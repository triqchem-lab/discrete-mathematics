#!/usr/bin/env python3
"""
DSPy 优化 Reasonix 系统提示词

与 TextGrad 对比:
  TextGrad: 优化单段文本 → LLM 反馈作为"梯度" → 改写
  DSPy:     优化整个模块 → 搜索最优 prompt 模板 + few-shot 示例 → 编译

DSPy 优势:
  - bootstrap 真实成功案例作为 few-shot 示例(不只是文本改写)
  - MIPROv2 自动搜索最优指令结构
  - 编译后的模块可直接提取 prompt 用于 Reasonix

用法:
  python3 optimize_dspy.py --compile  # 编译优化
  python3 optimize_dspy.py --eval     # 评测未优化版本
  python3 optimize_dspy.py --compare  # 对比优化前后
"""

import os, sys, json, argparse
sys.path.insert(0, '/data/work/discrete-mathematics/.reasonix/autoresearch/20260704-043019-builder-spec-silent-compliance-defect-builder-spec-archi/textgrad-opt')
import eval_tasks_v3_project

import dspy
import numpy as np


# ================================================================
# 1. 定义 Reasonix 编码代理的 DSPy 签名
# ================================================================

class CodingAgent(dspy.Signature):
    """You are a coding agent specialized in formal mathematics and proof engineering.
    
    Given a task description, produce a solution that:
    - Uses exact arithmetic (no floating point)
    - Handles errors explicitly
    - Verifies with real commands before claiming success
    - Follows the project's constitutional constraints
    """
    task: str = dspy.InputField(desc="The coding/proof task to solve")
    solution: str = dspy.OutputField(desc="The complete solution with code, proof, or analysis")


# ================================================================
# 2. 训练数据 — 从 v3 评估任务提取
# ================================================================

def load_training_data(max_examples=20):
    """将评估任务转换为 DSPy 训练样本."""
    trainset = []
    for task in eval_tasks_v3_project.EVAL_TASKS_V3[:max_examples]:
        example = dspy.Example(
            task=task["instruction"],
            difficulty=task["difficulty"],
            category=task["category"],
        ).with_inputs("task")
        trainset.append(example)
    return trainset


# ================================================================
# 3. 评分指标 — 用 LLM 评估输出质量
# ================================================================

EVAL_JUDGE_PROMPT = """Evaluate this coding agent response on a 0-100 scale.

TASK: {task}
AGENT RESPONSE: {solution}

Rate on:
- Correctness (40%): Is the solution mathematically/logically correct?
- Completeness (20%): Are all requirements addressed?
- Constitution (20%): No floating point, constructive, category separation?
- Verification (10%): Is there evidence of testing/verification?
- Clarity (10%): Is the solution clear and well-structured?

Respond with ONLY a number 0-100."""


def dspy_metric(example, pred, trace=None):
    """DSPy 评分函数 — 用 LLM-as-judge 评分."""
    # 简化评分: 用 LLM 评估
    judge = dspy.Predict("task, solution -> score: int")
    try:
        result = judge(
            task=example.task,
            solution=pred.solution,
        )
        score = int(result.score) if result.score else 50
        return max(0, min(100, score)) / 100.0
    except Exception:
        # Fallback: 基于输出长度的启发式评分
        if not pred.solution or len(pred.solution) < 50:
            return 0.0
        return min(0.8, len(pred.solution) / 500.0)


# ================================================================
# 4. 评测函数（不优化，仅测基线）
# ================================================================

def evaluate_baseline(trainset, lm):
    """评测未优化的 DSPy 模块."""
    dspy.configure(lm=lm)
    program = dspy.ChainOfThought(CodingAgent)
    
    scores = []
    for i, example in enumerate(trainset[:11]):  # 最多 11 个
        try:
            pred = program(task=example.task)
            score = dspy_metric(example, pred)
            scores.append(score)
            task = eval_tasks_v3_project.EVAL_TASKS_V3[i]
            print(f"  [{task['difficulty'][:1]}] {task['id'][:30]}: {score:.3f}")
        except Exception as e:
            print(f"  ERROR: {e}")
            scores.append(0.0)
    
    return np.mean(scores) if scores else 0.0


# ================================================================
# 5. 编译优化
# ================================================================

def compile_optimized(trainset, lm, output_path):
    """用 DSPy MIPROv2 编译优化."""
    dspy.configure(lm=lm)
    
    print(f"Training set: {len(trainset)} examples")
    print("Optimizer: MIPROv2 (auto prompt + bootstrap few-shot)")
    print()
    
    # 基线
    baseline = dspy.ChainOfThought(CodingAgent)
    print("Baseline (unoptimized):")
    base_score = evaluate_baseline(trainset, lm)
    print(f"  Mean score: {base_score:.3f}")
    
    # 编译
    print(f"\nCompiling with MIPROv2...")
    optimizer = dspy.MIPROv2(
        metric=dspy_metric,
        num_threads=4,
        auto="light",  # light/medium/full
    )
    
    optimized = optimizer.compile(
        baseline,
        trainset=trainset[:len(trainset)//2],  # 用一半训练
        valset=trainset[len(trainset)//2:],     # 另一半验证
        max_bootstrapped_demos=3,
        max_labeled_demos=4,
        requires_permission_to_run=False,
    )
    
    # 评测优化后
    print(f"\nOptimized:")
    opt_score = evaluate_baseline(trainset, lm)
    print(f"  Mean score: {opt_score:.3f}")
    print(f"  Improvement: {opt_score - base_score:+.3f}")
    
    # 保存
    optimized.save(output_path)
    print(f"\nSaved optimized program to: {output_path}")
    
    # 提取优化后的 prompt（如果可以）
    try:
        if hasattr(optimized, 'predictor') and hasattr(optimized.predictor, 'signature'):
            sig = optimized.predictor.signature
            print(f"\nOptimized signature instructions:")
            print(sig.instructions if hasattr(sig, 'instructions') else str(sig.__doc__)[:500])
    except Exception:
        pass
    
    return optimized


# ================================================================
# 6. 主函数
# ================================================================

def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--compile", action="store_true", help="Run DSPy optimization")
    parser.add_argument("--eval", action="store_true", help="Evaluate baseline only")
    parser.add_argument("--compare", action="store_true", help="Compare baseline vs optimized")
    parser.add_argument("--model", default="deepseek/deepseek-v4-flash")
    parser.add_argument("--output", default="optimized_dspy_program.json")
    args = parser.parse_args()
    
    # Setup LM
    lm = dspy.LM(args.model, api_key=os.environ.get("DEEPSEEK_API_KEY", ""))
    
    # Load data
    trainset = load_training_data()
    print(f"Training data: {len(trainset)} examples")
    print(f"Model: {args.model}")
    print()
    
    if args.eval:
        print("=== Baseline Evaluation ===")
        score = evaluate_baseline(trainset, lm)
        print(f"\nBaseline mean: {score:.3f}")
    
    elif args.compile:
        print("=== DSPy Optimization ===")
        optimized = compile_optimized(trainset, lm, args.output)
    
    elif args.compare:
        print("=== Baseline ===")
        base = evaluate_baseline(trainset, lm)
        print(f"Baseline: {base:.3f}")
        
        # Try to load optimized
        try:
            optimized = dspy.ChainOfThought(CodingAgent)
            optimized.load(args.output)
            dspy.configure(lm=lm)
            print(f"\n=== Optimized ===")
            opt = evaluate_baseline(trainset, lm)
            print(f"Optimized: {opt:.3f}")
            print(f"Delta: {opt - base:+.3f}")
        except FileNotFoundError:
            print(f"\nNo optimized program found at {args.output}")
            print("Run --compile first.")
    
    else:
        print("Usage: --eval | --compile | --compare")
        print("Recommended: --compile (takes ~5-10 minutes)")


if __name__ == "__main__":
    main()
