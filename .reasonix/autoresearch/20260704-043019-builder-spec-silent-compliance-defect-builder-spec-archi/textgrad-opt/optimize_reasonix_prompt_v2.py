#!/usr/bin/env python3
"""
TextGrad 优化 Reasonix 系统提示词 v2

改进:
- 种子提示词: 吸收 Fable5 9原则 + scholar-loop 4模式
- 评估任务: 覆盖多轮交互场景（文件操作/shell/重构/调试/项目级）
- 评分: LLM-as-judge + 结构化rubric (正确性/效率/安全性/证据)
- 约束: 保护 Fable5/scholar-loop 关键模式不被优化器丢弃
- 验证: 独立 v2 shell验证集做最终人工检查

用法:
  python3 optimize_reasonix_prompt_v2.py --epochs 5 --batch-size 2 --max-steps 4
"""

import os, json, random, argparse, re
from pathlib import Path
import textgrad as tg
import numpy as np


# ================================================================
# 种子提示词 (v1优化 + Fable5 + scholar-loop)
# ================================================================
SEED_PROMPT_PATH = Path(__file__).parent / "seed_v2_scholar_fable5.txt"
INITIAL_SYSTEM_PROMPT = SEED_PROMPT_PATH.read_text() if SEED_PROMPT_PATH.exists() else open(
    "/data/work/discrete-mathematics/.reasonix/autoresearch/20260704-043019-builder-spec-silent-compliance-defect-builder-spec-archi/textgrad-opt/seed_v2_scholar_fable5.txt"
).read()


# ================================================================
# 评估任务 (从 v2 提取, 适合 LLM-as-judge 评分)
# 每个任务设计为评估代理的多方面能力
# ================================================================
EVAL_TASKS = [
    # --- 文件操作 + 错误处理 ---
    {
        "id": "file_error_handling",
        "category": "file_ops",
        "difficulty": "easy",
        "instruction": "读 /tmp/missing_file.txt。文件不存在。给出清晰的错误信息，包括文件路径和失败原因。",
        "expected_traits": [
            "错误信息包含文件路径 /tmp/missing_file.txt",
            "说明了失败原因（文件不存在/权限等）",
            "没有崩溃或静默失败",
        ],
        "forbidden_traits": [
            "没有任何错误处理直接报错",
            "使用了裸 except: 而无视异常类型",
        ],
    },
    # --- 多文件协调 ---
    {
        "id": "multi_file_coordination",
        "category": "multi_file",
        "difficulty": "medium",
        "instruction": "在 /tmp/ 下，把 old_a.txt, old_b.txt, old_c.txt 重命名为 new_a.txt, new_b.txt, new_c.txt。先列出所有将要改的文件确认，再执行。",
        "expected_traits": [
            "先列出文件再操作（不盲目执行）",
            "每个重命名操作都有确认/日志",
            "没有使用删除命令",
        ],
        "forbidden_traits": [
            "不先列出就直接批量操作",
            "使用了 rm/mv --force 等危险标志",
        ],
    },
    # --- Shell 管道 ---
    {
        "id": "shell_pipeline",
        "category": "shell",
        "difficulty": "easy",
        "instruction": "从 /var/log/syslog（如不存在则用 dmesg）中找出含 'error' 的行，统计数量并输出前 3 行。用一行 shell 管道。",
        "expected_traits": [
            "使用了 grep 过滤",
            "统计了行数",
            "输出限制在前 3 行",
        ],
        "forbidden_traits": [
            "用了脚本语言替代 shell 一行",
            "没有错误处理（日志文件可能不存在）",
        ],
    },
    # --- 重构: 提取函数 ---
    {
        "id": "refactor_extract",
        "category": "refactor",
        "difficulty": "medium",
        "instruction": "以下代码有重复逻辑。提取公共部分为独立函数，消除重复，但保持行为不变。重构后验证结果相同。\n\ndef calc(a, b):\n    return a*1.1 + b*1.1\ndef report(x, y):\n    print(f'result: {x*1.1 + y*1.1}')",
        "expected_traits": [
            "提取了公共计算（1.1倍）为独立函数",
            "两个原函数都调用了新函数",
            "提到了验证步骤",
        ],
        "forbidden_traits": [
            "改变了原有行为",
            "删除了某个函数",
            "没有验证重构结果",
        ],
    },
    # --- 调试: off-by-one ---
    {
        "id": "debug_off_by_one",
        "category": "debug",
        "difficulty": "medium",
        "instruction": "下面的 binary_search 有 bug。找出 bug，只修复 bug 不改写函数，然后写测试验证。\n\ndef binary_search(arr, target):\n    left, right = 0, len(arr)\n    while left < right:\n        mid = (left + right) // 2\n        if arr[mid] == target: return mid\n        elif arr[mid] < target: left = mid + 1\n        else: right = mid\n    return -1",
        "expected_traits": [
            "找出了 bug（right 初始值应为 len(arr)-1 或循环条件修正）",
            "只修改了 bug 相关代码",
            "写了测试用例并运行",
        ],
        "forbidden_traits": [
            "重写了整个函数",
            "没有测试验证",
            "引入了新 bug",
        ],
    },
    # --- 约束遵守: 无浮点 ---
    {
        "id": "no_float_constraint",
        "category": "constraint",
        "difficulty": "easy",
        "instruction": "改写以下函数，用整数（单位: 分）替代浮点数计算，确保精确。\ndef apply_discount(price, percent):\n    return price * (1 - percent / 100.0)",
        "expected_traits": [
            "使用整数运算（非浮点）",
            "结果精确（如 10000 分, 15% 折扣 → 8500 分）",
            "解释了为何不用浮点",
        ],
        "forbidden_traits": [
            "仍使用浮点数",
            "结果不精确",
        ],
    },
    # --- 项目级: 添加模块 ---
    {
        "id": "project_add_module",
        "category": "project",
        "difficulty": "hard",
        "instruction": "现有项目结构: src/math_utils.py (含 add, multiply), src/__init__.py (导出它们), tests/test_math.py (测试)。新增 src/string_utils.py (capitalize_words)，更新 __init__.py 导出，加 tests/test_string.py 测试。确保已有测试不受影响。",
        "expected_traits": [
            "创建了新文件 string_utils.py",
            "更新了 __init__.py 的导出",
            "添加了测试文件",
            "提到了验证已有测试的步骤",
        ],
        "forbidden_traits": [
            "没有更新 __init__.py",
            "没有加测试",
            "破坏了已有模块",
        ],
    },
    # --- 上下文理解: 读已有代码再改 ---
    {
        "id": "context_aware_edit",
        "category": "context",
        "difficulty": "medium",
        "instruction": "在以下代码中添加一个 divide(a,b) 函数。先检查已有代码的风格和约定，遵循相同的模式。\n\n# math_utils.py\ndef add(a, b):\n    '''Return a + b.'''\n    if not isinstance(a, (int, float)) or not isinstance(b, (int, float)):\n        raise TypeError('Both arguments must be numbers')\n    return a + b",
        "expected_traits": [
            "添加了 divide 函数",
            "遵循了已有代码风格（docstring, 类型检查, TypeError）",
            "处理了除零错误",
        ],
        "forbidden_traits": [
            "风格不一致",
            "没有处理除零",
            "没有类型检查（而 add 有）",
        ],
    },
]

# 难度分布: easy=3, medium=4, hard=1


# ================================================================
# 评分 Rubric (LLM-as-judge, 但用结构化 rubric)
# ================================================================
EVAL_SYSTEM_PROMPT = """You are an expert evaluator of coding agent responses.
Rate the response on FOUR dimensions. Output ONLY a JSON object:

{
  "correctness": <0-100>,   // Does the solution work? Edge cases handled?
  "efficiency": <0-100>,     // Minimal changes? No unnecessary work?
  "safety": <0-100>,         // Error handling? No dangerous operations?
  "evidence": <0-100>,       // Verifiable output? Not just claims?
  "overall": <0-100>,        // Weighted average
  "reason": "<one sentence>",
  "met_traits": ["<list>"],
  "violated_traits": ["<list>"]
}

Weight: correctness*0.4 + efficiency*0.2 + safety*0.2 + evidence*0.2"""


def build_eval_prompt(task, response):
    return f"""TASK ({task['category']}, {task['difficulty']}):
{task['instruction']}

EXPECTED:
{chr(10).join(f'+ {t}' for t in task['expected_traits'])}

FORBIDDEN:
{chr(10).join(f'- {t}' for t in task['forbidden_traits'])}

AGENT RESPONSE:
{response[:1500]}

Rate on correctness/efficiency/safety/evidence. Output ONLY JSON."""


def parse_score(eval_text):
    try:
        m = re.search(r'\{[^}]*"overall"[^}]*\}', eval_text)
        if m:
            data = json.loads(m.group())
            return float(data.get("overall", 0)) / 100.0
    except: pass
    nums = re.findall(r'\b(\d+)\b', eval_text)
    return float(nums[-1]) / 100.0 if nums else 0.0


# ================================================================
# 主优化循环
# ================================================================
def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--epochs", type=int, default=5)
    parser.add_argument("--batch-size", type=int, default=2)
    parser.add_argument("--eval-engine", default="deepseek/deepseek-v4-flash")
    parser.add_argument("--backward-engine", default="deepseek/deepseek-v4-pro")
    parser.add_argument("--max-steps", type=int, default=4)
    parser.add_argument("--seed", type=int, default=42)
    parser.add_argument("--val-split", type=float, default=0.25)
    parser.add_argument("--output", default="optimized_prompt_v2.txt")
    parser.add_argument("--dry-run", action="store_true")
    args = parser.parse_args()

    np.random.seed(args.seed)
    random.seed(args.seed)

    print("=" * 60)
    print("TextGrad v2 — Fable5 + scholar-loop Seed")
    print("=" * 60)
    print(f"Eval engine:     {args.eval_engine}")
    print(f"Backward engine: {args.backward_engine}")
    print(f"Seed prompt:     {len(INITIAL_SYSTEM_PROMPT)} chars")
    print(f"Tasks:           {len(EVAL_TASKS)}")
    print(f"Epochs:          {args.epochs}")
    print()

    if args.dry_run:
        print("[DRY RUN] OK")
        return

    # --- Engines ---
    eval_engine = tg.get_engine(f"experimental:{args.eval_engine}")
    backward_engine = tg.get_engine(f"experimental:{args.backward_engine}")
    tg.set_backward_engine(backward_engine, override=True)

    # --- Train/Val split ---
    tasks_by_diff = {"easy": [], "medium": [], "hard": []}
    for i, t in enumerate(EVAL_TASKS):
        tasks_by_diff[t["difficulty"]].append(i)
    train_idx, val_idx = [], []
    for diff, indices in tasks_by_diff.items():
        arr = np.array(indices)
        np.random.shuffle(arr)
        n_val = max(1, int(len(arr) * args.val_split))
        val_idx.extend(arr[:n_val].tolist())
        train_idx.extend(arr[n_val:].tolist())
    print(f"Train: {len(train_idx)}  Val: {len(val_idx)}")

    # --- System prompt variable ---
    system_prompt = tg.Variable(
        INITIAL_SYSTEM_PROMPT, requires_grad=True,
        role_description="system prompt for a coding agent that reads/writes files, runs shell commands, produces clean correct code, follows Fable5 thinking principles"
    )
    model = tg.BlackboxLLM(eval_engine, system_prompt=system_prompt)

    # --- Optimizer with Fable5/scholar-loop protective constraints ---
    optimizer = tg.TextualGradientDescent(
        engine=backward_engine,
        parameters=[system_prompt],
        constraints=[
            "Preserve the numbered rules structure (1-9)",
            "Rule 2 must remain: scan before edit, check references (grep imports/callers)",
            "Rule 3 must remain: propose 2+ approaches for non-trivial decisions",
            "Rule 4 must remain: verify with real commands, report raw output",
            "Rule 5 must remain: keep changes minimal and reversible",
            "Working Discipline must include: predict-then-verify (state expectation before command)",
            "Working Discipline must include: challenge own assumptions before finalizing",
            "Working Discipline must include: every claim needs evidence (show output, not interpretation)",
            "Working Discipline must include: prefer small verifiable steps",
            "Working Discipline must include: record key decisions",
            "Must retain: never use floating point for exact arithmetic",
            "Must retain: handle errors explicitly, never empty catch",
            "Must retain: prefer standard library solutions",
            "Must be under 800 words",
        ],
        gradient_memory=3,
    )

    # --- Evaluator ---
    eval_model = tg.BlackboxLLM(eval_engine, system_prompt=tg.Variable(
        EVAL_SYSTEM_PROMPT, requires_grad=False,
        role_description="evaluation rubric for coding agent responses"
    ))

    def evaluate(task, response):
        inp = tg.Variable(build_eval_prompt(task, response.value), requires_grad=False,
                          role_description="evaluation request")
        out = eval_model(inp)
        return parse_score(out.value), out

    def eval_all(indices, label):
        scores = []
        for idx in indices:
            t = EVAL_TASKS[idx]
            r = model(tg.Variable(t["instruction"], requires_grad=False, role_description="task"))
            s, _ = evaluate(t, r)
            scores.append(s)
        avg = np.mean(scores) if scores else 0
        print(f"  {label}: {avg:.3f} (n={len(scores)})")
        return scores, avg

    # --- Baseline ---
    print("\n" + "=" * 60)
    print("Baseline evaluation...")
    print("=" * 60)
    _, train_baseline = eval_all(train_idx, "Train baseline")
    _, val_baseline = eval_all(val_idx, "Val baseline")
    results = {"best_score": val_baseline, "best_prompt": INITIAL_SYSTEM_PROMPT,
               "baseline": val_baseline}

    # --- Training ---
    print("\n" + "=" * 60)
    print("Starting optimization...")
    print("=" * 60)

    for epoch in range(args.epochs):
        indices = train_idx.copy()
        np.random.shuffle(indices)
        for step in range(min(args.max_steps, len(indices) // args.batch_size)):
            batch = indices[step * args.batch_size:(step + 1) * args.batch_size]
            optimizer.zero_grad()
            losses, scores = [], []
            for idx in batch:
                t = EVAL_TASKS[idx]
                inp = tg.Variable(t["instruction"], requires_grad=False, role_description="task")
                r = model(inp)
                s, ev = evaluate(t, r)
                scores.append(s)
                loss_text = (
                    f"TASK [{t['category']}]: {t['instruction'][:200]}\n"
                    f"SCORE: {s:.2f}/1.0\n"
                    f"DIAGNOSE: What in the system prompt caused this score? "
                    f"What exact wording change would improve correctness (40%), "
                    f"efficiency (20%), safety (20%), and evidence (20%)?"
                )
                loss = tg.Variable(loss_text, requires_grad=True,
                                   role_description=f"loss for {t['id']}")
                losses.append(ev)
                losses.append(r)
            if losses:
                try:
                    tg.sum(losses[:1]).backward()
                    optimizer.step()
                    avg_s = np.mean(scores)
                    _, val_avg = eval_all(val_idx, f"Val e{epoch+1}s{step+1}")
                    print(f"  E{epoch+1}S{step+1}: train={avg_s:.3f} val={val_avg:.3f} "
                          f"prompt={len(system_prompt.value)}c")
                    if val_avg > results["best_score"]:
                        results["best_score"] = val_avg
                        results["best_prompt"] = system_prompt.value
                        print(f"  >>> BEST val={val_avg:.3f}")
                except Exception as e:
                    print(f"  WARN: {e}")

    # --- Save ---
    out = Path(args.output)
    out.write_text(results["best_prompt"])
    print(f"\n{'=' * 60}")
    print(f"Done. Baseline={results['baseline']:.3f} → Best={results['best_score']:.3f}")
    print(f"Saved: {out} ({len(results['best_prompt'])} chars)")


if __name__ == "__main__":
    main()
