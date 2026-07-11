#!/usr/bin/env python3
"""
TextGrad v3 — 离散数学项目专属优化

种子: 项目宪法5条约束 + Fable5 Phase工作流 + scholar-loop verify-then-report
评测: 11个任务来自真实项目 (Python bug修复/Agda证明填充/跨语言验证/CI脚本)
约束: 保护宪法规则(no float/constructive proofs/category separation/π_H atomic/stdlib trust=0)

用法:
  python3 optimize_reasonix_prompt_v3.py --epochs 5 --batch-size 2 --max-steps 4
"""

import os, json, random, argparse, re
from pathlib import Path
import textgrad as tg
import numpy as np

# Import v3 tasks
import eval_tasks_v3_project
EVAL_TASKS = eval_tasks_v3_project.EVAL_TASKS_V3

# Seed prompt
SEED_PATH = Path(__file__).parent / "seed_v3_discrete_math.txt"
INITIAL_SYSTEM_PROMPT = SEED_PATH.read_text() if SEED_PATH.exists() else ""

# Evaluation rubric (tuned for proof/math tasks)
EVAL_SYSTEM_PROMPT = """You evaluate a coding agent working on formal mathematics and proof engineering.
Rate on 5 dimensions, each 0-100. Output ONLY JSON:

{
  "correctness": <0-100>,   // Is the solution mathematically correct?
  "completeness": <0-100>,   // Are all holes/postulates addressed?
  "constitution": <0-100>,   // Follows project rules (no float, constructive, category separation)?
  "verification": <0-100>,   // Did they verify with real commands?
  "precision": <0-100>,      // Exact values used (not approximations)?
  "overall": <0-100>,
  "reason": "<one sentence>"
}

Weights: correctness*0.35 + completeness*0.2 + constitution*0.2 + verification*0.15 + precision*0.1"""


def build_eval_prompt(task, response):
    return f"""TASK [{task['difficulty']}] {task['category']} — {task['source']}:
{task['instruction']}

AGENT RESPONSE:
{response.value[:2000]}

Rate on correctness/completeness/constitution/verification/precision. Output ONLY JSON."""


def parse_score(text):
    try:
        m = re.search(r'\{[^}]*"overall"[^}]*\}', text)
        if m: return float(json.loads(m.group()).get("overall", 0)) / 100.0
    except: pass
    nums = re.findall(r'\b(\d+)\b', text)
    return float(nums[-1]) / 100.0 if nums else 0.0


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--epochs", type=int, default=5)
    parser.add_argument("--batch-size", type=int, default=2)
    parser.add_argument("--eval-engine", default="deepseek/deepseek-v4-flash")
    parser.add_argument("--backward-engine", default="deepseek/deepseek-v4-pro")
    parser.add_argument("--max-steps", type=int, default=4)
    parser.add_argument("--seed", type=int, default=42)
    parser.add_argument("--val-split", type=float, default=0.25)
    parser.add_argument("--output", default="optimized_prompt_v3.txt")
    parser.add_argument("--dry-run", action="store_true")
    args = parser.parse_args()

    np.random.seed(args.seed); random.seed(args.seed)

    print("=" * 60)
    print("TextGrad v3 — Discrete Math Project (Agda + Python)")
    print("=" * 60)
    print(f"Seed: {len(INITIAL_SYSTEM_PROMPT)} chars")
    print(f"Tasks: {len(EVAL_TASKS)}")
    print(f"  easy={sum(1 for t in EVAL_TASKS if t['difficulty']=='easy')}")
    print(f"  medium={sum(1 for t in EVAL_TASKS if t['difficulty']=='medium')}")
    print(f"  hard={sum(1 for t in EVAL_TASKS if t['difficulty']=='hard')}")
    print()

    if args.dry_run:
        print("[DRY RUN] OK")
        return

    # Engines
    eval_engine = tg.get_engine(f"experimental:{args.eval_engine}")
    backward_engine = tg.get_engine(f"experimental:{args.backward_engine}")
    tg.set_backward_engine(backward_engine, override=True)

    # Stratified split
    tasks_by_diff = {"easy": [], "medium": [], "hard": []}
    for i, t in enumerate(EVAL_TASKS):
        tasks_by_diff[t["difficulty"]].append(i)
    train_idx, val_idx = [], []
    for diff, indices in tasks_by_diff.items():
        arr = np.array(indices); np.random.shuffle(arr)
        n_val = max(1, int(len(arr) * args.val_split))
        val_idx.extend(arr[:n_val].tolist())
        train_idx.extend(arr[n_val:].tolist())
    print(f"Train: {len(train_idx)}  Val: {len(val_idx)}")

    # System prompt
    sp = tg.Variable(INITIAL_SYSTEM_PROMPT, requires_grad=True,
                     role_description="system prompt for a formal-math coding agent working on Agda proofs and Python implementations")
    model = tg.BlackboxLLM(eval_engine, system_prompt=sp)

    # Optimizer — constitutional constraints are non-negotiable
    optimizer = tg.TextualGradientDescent(
        engine=backward_engine, parameters=[sp],
        constraints=[
            "Must retain: No floating point — use exact integer ratios (Fraction, rational)",
            "Must retain: Constructive proofs only — no postulate without elimination plan",
            "Must retain: Category separation — RootMath/Structology/Coupling/Density must not mix",
            "Must retain: π_H = 144/46 is atomic — never reduce this fraction",
            "Must retain: Standard library trust = 0 — self-prove all arithmetic",
            "Must retain: Twelve Lü lengths are static constants, never computed",
            "Must retain: Phase 0 (Understand), Phase 1 (Scan), Phase 2 (Verify), Phase 3 (Report)",
            "Must retain: Verify with real commands (agda <file>, pytest, bash scripts)",
            "Must retain: Report raw command output as evidence, never claim without proof",
            "Must be under 1000 words",
        ],
        gradient_memory=3,
    )

    # Evaluator
    eval_model = tg.BlackboxLLM(eval_engine, system_prompt=tg.Variable(
        EVAL_SYSTEM_PROMPT, requires_grad=False, role_description="evaluation rubric for math/proof tasks"))

    def evaluate(task, response):
        inp = tg.Variable(build_eval_prompt(task, response), requires_grad=False, role_description="eval")
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

    # Baseline
    print("\n" + "=" * 60)
    print("Baseline...")
    print("=" * 60)
    _, train_base = eval_all(train_idx, "Train baseline")
    _, val_base = eval_all(val_idx, "Val baseline")
    results = {"best_score": val_base, "best_prompt": INITIAL_SYSTEM_PROMPT, "baseline": val_base}

    # Training
    print("\n" + "=" * 60)
    print("Optimizing...")
    print("=" * 60)
    for epoch in range(args.epochs):
        indices = train_idx.copy(); np.random.shuffle(indices)
        for step in range(min(args.max_steps, len(indices) // args.batch_size)):
            batch = indices[step*args.batch_size:(step+1)*args.batch_size]
            optimizer.zero_grad()
            losses, scores = [], []
            for idx in batch:
                t = EVAL_TASKS[idx]
                inp = tg.Variable(t["instruction"], requires_grad=False, role_description="task")
                r = model(inp)
                s, ev = evaluate(t, r)
                scores.append(s)
                loss_text = (
                    f"TASK [{t['difficulty']}] {t['category']}: {t['instruction'][:300]}\n"
                    f"SCORE: {s:.2f}/1.0\n"
                    f"DIAGNOSE: What in the system prompt caused this score? "
                    f"Consider: correctness (35%), completeness (20%), "
                    f"constitutional compliance (20%), verification (15%), precision (10%). "
                    f"What exact wording change would improve the weakest dimension?"
                )
                loss = tg.Variable(loss_text, requires_grad=True, role_description=f"loss-{t['id']}")
                losses.append(ev); losses.append(r)
            if losses:
                try:
                    tg.sum(losses[:1]).backward()
                    optimizer.step()
                    avg_s = np.mean(scores)
                    _, val_avg = eval_all(val_idx, f"Val e{epoch+1}s{step+1}")
                    print(f"  E{epoch+1}S{step+1}: train={avg_s:.3f} val={val_avg:.3f} "
                          f"prompt={len(sp.value)}c")
                    if val_avg > results["best_score"]:
                        results["best_score"] = val_avg
                        results["best_prompt"] = sp.value
                        print(f"  >>> BEST val={val_avg:.3f}")
                except Exception as e:
                    print(f"  WARN: {e}")

    # Save
    out = Path(args.output)
    out.write_text(results["best_prompt"])
    print(f"\n{'=' * 60}")
    print(f"Done. Baseline={results['baseline']:.3f} → Best={results['best_score']:.3f}")
    print(f"Saved: {out} ({len(results['best_prompt'])} chars)")


if __name__ == "__main__":
    main()
