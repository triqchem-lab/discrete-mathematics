#!/usr/bin/env python3
"""
TextGrad 优化 Reasonix 系统提示词

使用 TextGrad 自动优化 Reasonix 的 system prompt：
- 训练数据：编码任务 + 预期行为
- 评分：DeepSeek 在任务上的表现
- 优化器：TextGrad TextualGradientDescent
- 输出：优化后的 system prompt → 可写入 config.toml

用法：
  python3 optimize_reasonix_prompt.py --epochs 3 --batch-size 2

依赖：
  pip install --break-system-packages textgrad litellm python-dotenv
"""

import os
import json
import random
import argparse
from pathlib import Path

import textgrad as tg
import numpy as np


# ========================
# 1. 编码评估任务集
# ========================

EVAL_TASKS = [
    {
        "instruction": "用 Python 实现一个函数 fibonacci(n) 返回第 n 个斐波那契数。要求处理 n=0 和 n=1 的边界情况。",
        "language": "Python",
        "difficulty": "easy",
        "expected_traits": [
            "函数名是 fibonacci",
            "处理 n=0 返回 0 或 1",
            "处理 n=1 返回 1",
            "不使用递归（或使用带缓存的递归）",
        ],
        "forbidden_traits": [
            "使用浮点数",
            "没有边界检查",
            "函数名错误",
        ],
    },
    {
        "instruction": "用 Python 读取文件 /etc/hostname 并打印其内容。如果没有权限则打印包含文件名的错误信息。",
        "language": "Python",
        "difficulty": "easy",
        "expected_traits": [
            "有 try-except 错误处理",
            "使用 with open() 语法",
            "错误信息包含文件名",
        ],
        "forbidden_traits": [
            "没有错误处理",
            "使用裸 except:",
            "输出 shell 命令而非 Python 代码",
        ],
    },
    {
        "instruction": "写一个 Bash 脚本，列出当前目录下所有超过 1MB 的文件并按大小排序。不使用 sudo 或删除命令。",
        "language": "Bash",
        "difficulty": "easy",
        "expected_traits": [
            "使用 find 命令",
            "有 -size 过滤",
            "按大小排序",
        ],
        "forbidden_traits": [
            "删除文件的命令（rm, shred 等）",
            "需要 sudo 的命令",
        ],
    },
    {
        "instruction": "用 JavaScript 写一个函数 debounce(fn, delay)，返回一个防抖版本的函数。保持 this 上下文和参数传递。",
        "language": "JavaScript",
        "difficulty": "medium",
        "expected_traits": [
            "使用 setTimeout 或等效机制",
            "使用 clearTimeout 取消前一个",
            "保持 this 上下文",
            "传递参数",
        ],
        "forbidden_traits": [
            "立即调用 fn",
            "没有清除机制",
        ],
    },
    {
        "instruction": "用 Python 写一段代码找出两个数组的交集（共同元素），要求 O(n) 时间复杂度。",
        "language": "Python",
        "difficulty": "medium",
        "expected_traits": [
            "使用 Set 或哈希表",
            "时间复杂度 O(n) 而非 O(n²)",
            "处理重复元素",
        ],
        "forbidden_traits": [
            "嵌套循环",
            "没有去重",
        ],
    },
    {
        "instruction": "用 Python 实现一个简单的 LRU 缓存类，支持 get(key) 和 put(key, value)，容量为 capacity。",
        "language": "Python",
        "difficulty": "hard",
        "expected_traits": [
            "使用 OrderedDict 或双向链表+哈希表",
            "get 更新访问顺序",
            "put 时容量满则淘汰最久未使用",
        ],
        "forbidden_traits": [
            "没有容量限制",
            "O(n) 淘汰",
        ],
    },
    {
        "instruction": "用 Python 写一个脚本解析 JSON 文件并验证其结构：必须包含 'name'(string) 和 'age'(integer) 字段。错误时给出清晰的提示指出哪个字段无效。",
        "language": "Python",
        "difficulty": "easy",
        "expected_traits": [
            "使用 json.load()",
            "使用 isinstance() 验证类型",
            "清晰的错误信息指出哪个字段无效",
        ],
        "forbidden_traits": [
            "使用 eval()",
            "没有类型验证",
            "崩溃而非报告错误",
        ],
    },
    {
        "instruction": "用 Rust 写一个函数读取文件所有行，返回 Vec<String>。用 Result 处理文件不存在的错误，不 panic。",
        "language": "Rust",
        "difficulty": "medium",
        "expected_traits": [
            "返回 Result 类型",
            "使用 ? 操作符传播错误",
            "使用 std::fs::read_to_string 或 BufReader",
        ],
        "forbidden_traits": [
            "使用 unwrap() 而不处理错误",
            "panic! 而非返回 Result",
        ],
    },
    {
        "instruction": "用 Python 写一个函数 parse_csv_line(line: str) -> list[str]，正确处理引号内的逗号。",
        "language": "Python",
        "difficulty": "medium",
        "expected_traits": [
            "处理双引号包裹的字段",
            "引号内逗号不被分割",
            "处理空字段",
        ],
        "forbidden_traits": [
            "简单用 line.split(',')",
            "忽略引号",
        ],
    },
    {
        "instruction": "用 Python 写一个上下文管理器 timer()，用 with timer() as t: 包裹代码块，退出时打印执行耗时（毫秒）。",
        "language": "Python",
        "difficulty": "medium",
        "expected_traits": [
            "使用 __enter__ 和 __exit__",
            "使用 time.perf_counter()",
            "在 __exit__ 中打印耗时",
        ],
        "forbidden_traits": [
            "使用 time.time()（精度不足）",
            "在 __enter__ 中打印",
        ],
    },
]


# ========================
# 2. 初始系统提示词（当前 Reasonix 内置提示词的精简提取）
# ========================

INITIAL_SYSTEM_PROMPT = """You are a coding agent focused on executing code tasks.
Use the provided tools to read and write files and run shell commands.
Principles: understand the request before acting; verify with tools instead of guessing; keep changes minimal and correct; briefly summarize what you did.

When writing code:
- Follow the user's language and framework conventions
- Handle errors explicitly, never use empty catch blocks
- Validate inputs at function boundaries
- Write clean, readable code with clear naming
- Include error handling for all I/O operations
- Prefer standard library solutions over external dependencies unless specified

When responding:
- Reply in the same language the user is using
- Be concise and direct
- Include code with proper syntax for the target language
- Verify your changes work before claiming success"""


# ========================
# 3. 评分函数
# ========================

SYSTEM_PROMPT_EVAL = """You are an expert code reviewer evaluating a coding agent's response.
Rate the response against the expected and forbidden traits.

Respond with ONLY a JSON object:
{
  "score": <0-100>,
  "reason": "<one sentence explaining the score>",
  "met_traits": ["<list of expected traits that were met>"],
  "violated_traits": ["<list of forbidden traits that were violated>"]
}

A score of 100 means ALL expected traits met and ZERO forbidden traits violated.
A score of 0 means NONE of the expected traits met or ALL forbidden traits violated.
Partial matches get proportional scores."""


def build_eval_prompt(instruction, expected_traits, forbidden_traits, agent_response):
    """Build the evaluation prompt for scoring an agent response."""
    return f"""Evaluate this coding agent response:

TASK: {instruction}

EXPECTED TRAITS:
{chr(10).join(f"- {t}" for t in expected_traits)}

FORBIDDEN TRAITS:
{chr(10).join(f"- {t}" for t in forbidden_traits)}

AGENT RESPONSE:
{agent_response}

Rate the response against the expected and forbidden traits. Output ONLY a JSON object."""


def parse_score(eval_text):
    """Parse the evaluation text to extract the numeric score."""
    try:
        # Try to find JSON in the response
        import re
        json_match = re.search(r'\{[^}]*"score"[^}]*\}', eval_text)
        if json_match:
            data = json.loads(json_match.group())
            return float(data.get("score", 0)) / 100.0
    except (json.JSONDecodeError, KeyError, ValueError):
        pass

    # Fallback: try to find a number
    import re
    nums = re.findall(r'\b(\d+)\b', eval_text)
    if nums:
        return float(nums[-1]) / 100.0
    return 0.0


# ========================
# 4. 主优化循环
# ========================

def main():
    parser = argparse.ArgumentParser(description="Optimize Reasonix system prompt with TextGrad")
    parser.add_argument("--epochs", type=int, default=3, help="Number of training epochs")
    parser.add_argument("--batch-size", type=int, default=2, help="Batch size per step")
    parser.add_argument("--eval-engine", default="deepseek/deepseek-v4-flash",
                        help="LLM to optimize (litellm format)")
    parser.add_argument("--backward-engine", default="deepseek/deepseek-v4-pro",
                        help="LLM for gradient computation (litellm format)")
    parser.add_argument("--max-steps", type=int, default=3, help="Max steps per epoch")
    parser.add_argument("--output", default="optimized_prompt.txt",
                        help="File to save the optimized prompt")
    parser.add_argument("--seed", type=int, default=42, help="Random seed for reproducibility")
    parser.add_argument("--val-split", type=float, default=0.25, help="Fraction of tasks for validation")
    parser.add_argument("--dry-run", action="store_true",
                        help="Test setup without running optimization")
    args = parser.parse_args()

    print("=" * 60)
    print("TextGrad System Prompt Optimizer for Reasonix")
    print("=" * 60)
    print(f"Eval engine:     {args.eval_engine}")
    print(f"Backward engine: {args.backward_engine}")
    print(f"Epochs:          {args.epochs}")
    print(f"Batch size:      {args.batch_size}")
    print(f"Tasks:           {len(EVAL_TASKS)}")
    print()

    if args.dry_run:
        print("[DRY RUN] Setup verified, exiting without optimization.")
        return

    # --- Bug 2 fix: reproducible seed ---
    np.random.seed(args.seed)
    random.seed(args.seed)
    print(f"Random seed:     {args.seed}")

    # --- Bug 2 fix: stratified train/val split by difficulty ---
    tasks_by_diff = {"easy": [], "medium": [], "hard": []}
    for i, t in enumerate(EVAL_TASKS):
        tasks_by_diff[t["difficulty"]].append(i)

    train_indices = []
    val_indices = []
    for diff, indices in tasks_by_diff.items():
        idx_arr = np.array(indices)
        np.random.shuffle(idx_arr)
        n_val = max(1, int(len(idx_arr) * args.val_split))
        val_indices.extend(idx_arr[:n_val].tolist())
        train_indices.extend(idx_arr[n_val:].tolist())

    print(f"Train tasks:     {len(train_indices)} ({[(EVAL_TASKS[i]['difficulty']) for i in train_indices]})")
    print(f"Val tasks:       {len(val_indices)} ({[(EVAL_TASKS[i]['difficulty']) for i in val_indices]})")
    print()

    # --- Setup TextGrad engines ---
    print("Setting up engines...")
    try:
        eval_engine = tg.get_engine(f"experimental:{args.eval_engine}")
        backward_engine = tg.get_engine(f"experimental:{args.backward_engine}")
        tg.set_backward_engine(backward_engine, override=True)
        print("  Engines OK")
    except Exception as e:
        print(f"  ERROR setting up engines: {e}")
        print("  Make sure DEEPSEEK_API_KEY is set in environment.")
        return

    # --- Setup system prompt variable and model ---
    print("Setting up system prompt variable...")
    system_prompt = tg.Variable(
        INITIAL_SYSTEM_PROMPT,
        requires_grad=True,
        role_description="system prompt for a coding agent that reads/writes files, runs shell commands, and produces clean correct code"
    )

    model = tg.BlackboxLLM(eval_engine, system_prompt=system_prompt)

    optimizer = tg.TextualGradientDescent(
        engine=backward_engine,
        parameters=[system_prompt],
        constraints=[
            "Must instruct the agent to understand before acting",
            "Must instruct the agent to verify with tools before claiming success",
            "Must instruct the agent to keep changes minimal and correct",
            "Must instruct the agent to handle errors explicitly — never use empty catch blocks or silent failures",
            "Must instruct the agent to validate inputs at function boundaries",
            "Must instruct the agent to prefer standard library solutions over external dependencies",
            "Must instruct the agent to reply in the user's language",
            "Must instruct the agent to never use floating point for exact arithmetic",
            "Must be under 600 words",
        ],
        gradient_memory=3,
    )
    print("  System prompt variable and optimizer OK")

    # --- Evaluation function ---
    eval_model = tg.BlackboxLLM(eval_engine, system_prompt=tg.Variable(
        SYSTEM_PROMPT_EVAL, requires_grad=False,
        role_description="system prompt for the code reviewer"
    ))

    def evaluate_response(instruction, expected_traits, forbidden_traits, agent_response):
        """Evaluate an agent response against expected/forbidden traits."""
        eval_input = build_eval_prompt(
            instruction, expected_traits, forbidden_traits, agent_response
        )
        eval_var = tg.Variable(
            eval_input, requires_grad=False,
            role_description="evaluation request for a coding agent response"
        )
        eval_output = eval_model(eval_var)
        score = parse_score(eval_output.value)
        return score, eval_output

    # --- Bug 2 fix: baseline evaluation before optimization ---
    print("=" * 60)
    print("Baseline evaluation (before optimization)...")
    print("=" * 60)

    def eval_all_tasks(indices, label):
        scores = []
        for idx in indices:
            task = EVAL_TASKS[idx]
            instruction = tg.Variable(
                task["instruction"], requires_grad=False,
                role_description="coding task instruction for the agent"
            )
            response = model(instruction)
            score, _ = evaluate_response(
                task["instruction"], task["expected_traits"],
                task["forbidden_traits"], response.value
            )
            scores.append(score)
        avg = np.mean(scores) if scores else 0
        print(f"  {label}: {avg:.3f} (n={len(scores)}, tasks={[EVAL_TASKS[i]['difficulty'][:3] for i in indices]})")
        return scores, avg

    train_baseline_scores, train_baseline = eval_all_tasks(train_indices, "Train baseline")
    val_baseline_scores, val_baseline = eval_all_tasks(val_indices, "Val baseline")
    results = {
        "train_scores": train_baseline_scores,
        "val_scores": val_baseline_scores,
        "best_score": val_baseline,
        "best_prompt": INITIAL_SYSTEM_PROMPT,
        "train_baseline": train_baseline,
        "val_baseline": val_baseline,
    }

    print("\n" + "=" * 60)
    print("Starting optimization...")
    print("=" * 60)

    for epoch in range(args.epochs):
        epoch_scores = []

        # Bug 2 fix: deterministic shuffle within epoch
        epoch_indices = train_indices.copy()
        np.random.shuffle(epoch_indices)

        for step in range(min(args.max_steps, len(epoch_indices) // args.batch_size)):
            batch_indices = epoch_indices[step * args.batch_size:(step + 1) * args.batch_size]

            optimizer.zero_grad()
            losses = []
            batch_scores = []

            for idx in batch_indices:
                task = EVAL_TASKS[idx]
                instruction = tg.Variable(
                    task["instruction"], requires_grad=False,
                    role_description="coding task instruction for the agent"
                )

                # Forward: agent responds with current system prompt
                response = model(instruction)

                # Evaluate the response
                score, eval_output = evaluate_response(
                    task["instruction"],
                    task["expected_traits"],
                    task["forbidden_traits"],
                    response.value,
                )
                batch_scores.append(score)

                # Loss: model's own critique of the response quality
                loss_text = (
                    f"TASK: {task['instruction']} (language: {task['language']})\n"
                    f"SCORE: {score:.2f}/1.0\n"
                    f"AGENT RESPONSE SUMMARY: {response.value[:300]}...\n"
                    f"\n"
                    f"DIAGNOSIS: The system prompt caused the agent to score {score:.2f} on this task.\n"
                    f"- If score is low: what EXACT wording in the system prompt misled the agent?\n"
                    f"- If score is high: what EXACT wording helped? Make sure it's preserved.\n"
                    f"- What specific line(s) should be added, removed, or changed?\n"
                    f"- Consider: language conventions ({task['language']}), error handling, input validation, code clarity."
                )
                loss = tg.Variable(
                    loss_text,
                    requires_grad=True,
                    role_description=f"loss for {task['language']} task: diagnose system prompt quality"
                )
                # Set the gradient manually - TextGrad uses backward engine
                # to critique and suggest improvements
                loss_grad = tg.Variable(
                    f"TASK: {task['instruction']}\n"
                    f"SCORE: {score:.2f}/1.0\n"
                    f"PROBLEMS: The response scored only {score:.2f}. "
                    f"Analyze WHY the system prompt led to this suboptimal response. "
                    f"What specific changes to the system prompt would improve the score? "
                    f"Consider: clarity, specificity, error handling guidance, "
                    f"language conventions, verification instructions.",
                    requires_grad=False,
                    role_description=f"gradient feedback for system prompt improvement"
                )

                # Link the loss to the response so backward can trace
                # In TextGrad, the loss.backward() computes textual gradients
                # that flow back through the computation graph to the system_prompt
                losses.append(eval_output)
                losses.append(response)  # Include response in loss computation

            if losses:
                total_loss = tg.sum(losses[:1])  # Use first loss as aggregate
                try:
                    total_loss.backward()
                    optimizer.step()

                    avg_score = np.mean(batch_scores) if batch_scores else 0
                    epoch_scores.extend(batch_scores)

                    print(f"  Epoch {epoch+1}/{args.epochs} Step {step+1}: "
                          f"train avg = {avg_score:.3f} (batch: {[f'{EVAL_TASKS[i]['difficulty'][:3]}' for i in batch_indices]}), "
                          f"prompt = {len(system_prompt.value)} chars")

                    # Bug 2 fix: validate on held-out set, not training batch
                    val_scores_epoch, val_avg = eval_all_tasks(val_indices, f"Val (epoch {epoch+1} step {step+1})")

                    if val_avg > results["best_score"]:
                        results["best_score"] = val_avg
                        results["best_prompt"] = system_prompt.value
                        results["val_scores"] = val_scores_epoch
                        print(f"  >>> New best prompt! Val score: {val_avg:.3f} (prev: {results['best_score']:.3f})")

                except Exception as e:
                    print(f"  WARNING: backward/step failed: {e}")
                    continue

        if epoch_scores:
            print(f"  Epoch {epoch+1} complete: mean score = {np.mean(epoch_scores):.3f}")

    # --- Save results ---
    output_path = Path(args.output)
    output_path.write_text(results["best_prompt"])
    print(f"\n{'=' * 60}")
    print(f"Optimization complete!")
    print(f"Train baseline:  {results['train_baseline']:.3f}")
    print(f"Val baseline:    {results['val_baseline']:.3f}")
    print(f"Best val score:  {results['best_score']:.3f}")
    print(f"Improvement:     {results['best_score'] - results['val_baseline']:+.3f}")
    print(f"Optimized prompt saved to: {output_path}")
    print(f"Prompt length:   {len(results['best_prompt'])} chars")
    print(f"\nTo use this prompt in Reasonix, add to ~/.reasonix/config.toml:")
    print(f'  [agent]')
    print(f'  system_prompt_file = "{output_path.absolute()}"')


if __name__ == "__main__":
    main()
