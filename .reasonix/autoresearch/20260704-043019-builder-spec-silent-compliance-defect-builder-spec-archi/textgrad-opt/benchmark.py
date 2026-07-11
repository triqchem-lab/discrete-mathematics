#!/usr/bin/env python3
"""
基准评测套件 — 离散数学项目系统提示词

评测任意 system_prompt 在 11 个真实项目任务上的表现。
输出: 每任务分数 + 聚合分数 + 宪法合规检查

局限（诚实声明）:
- LLM-as-judge 是代理指标，不能替代 agda check / pytest 验证
- 真实正确性需要实际运行 verify 命令
- 本套件用于快速迭代比较提示词版本，非最终质量保证

用法:
  python3 benchmark.py --prompt seed_v3_discrete_math.txt
  python3 benchmark.py --prompt best_from_v1.txt
  python3 benchmark.py --compare prompt_a.txt prompt_b.txt
"""

import json, argparse, time, re, sys
from pathlib import Path
import textgrad as tg
import numpy as np
import eval_tasks_v3_project

EVAL_TASKS = eval_tasks_v3_project.EVAL_TASKS_V3

EVAL_SYSTEM_PROMPT = """You evaluate a coding agent working on formal mathematics and proof engineering.
Rate on 5 dimensions, each 0-100. Output ONLY JSON:
{"correctness":<0-100>,"completeness":<0-100>,"constitution":<0-100>,"verification":<0-100>,"precision":<0-100>,"overall":<0-100>,"reason":"<one sentence>"}
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


def constitution_check(prompt_text):
    """Check if prompt preserves constitutional rules."""
    rules = {
        "no_float": any(w in prompt_text.lower() for w in ["no floating", "integer ratio", "fraction", "exact arithmetic"]),
        "constructive": "constructive" in prompt_text.lower() or "postulate" in prompt_text.lower(),
        "category_sep": "category separation" in prompt_text.lower() or "rootmath" in prompt_text.lower(),
        "pi_h_atomic": "144/46" in prompt_text or "π_H" in prompt_text,
        "stdlib_trust_0": "stdlib" in prompt_text.lower() and ("trust" in prompt_text.lower() or "self-prov" in prompt_text.lower()),
        "twelve_lu": "twelve lü" in prompt_text.lower() or "十二律" in prompt_text,
        "verify_real": "verify" in prompt_text.lower() and ("real command" in prompt_text.lower() or "agda" in prompt_text.lower() or "pytest" in prompt_text.lower()),
        "phase_workflow": "phase 0" in prompt_text.lower() and "phase 1" in prompt_text.lower(),
    }
    return {k: v for k, v in rules.items()}


def benchmark(prompt_path, engine_str="deepseek/deepseek-v4-flash", verbose=True):
    """Run all tasks against a prompt and return scores."""
    prompt_text = Path(prompt_path).read_text()
    
    engine = tg.get_engine(f"experimental:{engine_str}")
    sp = tg.Variable(prompt_text, requires_grad=False, role_description="system prompt")
    model = tg.BlackboxLLM(engine, system_prompt=sp)
    eval_model = tg.BlackboxLLM(engine, system_prompt=tg.Variable(
        EVAL_SYSTEM_PROMPT, requires_grad=False, role_description="evaluator"))
    
    results = []
    for task in EVAL_TASKS:
        if verbose: print(f"  [{task['difficulty'][:1].upper()}] {task['id']}...", end=" ", flush=True)
        t0 = time.time()
        inp = tg.Variable(task["instruction"], requires_grad=False, role_description="task")
        response = model(inp)
        eval_inp = tg.Variable(build_eval_prompt(task, response), requires_grad=False, role_description="eval")
        eval_out = eval_model(eval_inp)
        score = parse_score(eval_out.value)
        elapsed = time.time() - t0
        results.append({
            "id": task["id"],
            "difficulty": task["difficulty"],
            "category": task["category"],
            "score": score,
            "time": elapsed,
            "response_len": len(response.value),
        })
        if verbose: print(f"{score:.3f} ({elapsed:.1f}s)")
    
    # Aggregate
    easy = [r["score"] for r in results if r["difficulty"] == "easy"]
    medium = [r["score"] for r in results if r["difficulty"] == "medium"]
    hard = [r["score"] for r in results if r["difficulty"] == "hard"]
    all_scores = [r["score"] for r in results]
    
    # Constitution check
    const = constitution_check(prompt_text)
    
    return {
        "prompt": str(prompt_path),
        "prompt_len": len(prompt_text),
        "constitution": const,
        "constitution_score": sum(const.values()) / len(const),
        "scores": results,
        "aggregate": {
            "overall": np.mean(all_scores),
            "easy": np.mean(easy) if easy else 0,
            "medium": np.mean(medium) if medium else 0,
            "hard": np.mean(hard) if hard else 0,
            "n_tasks": len(results),
        },
    }


def print_report(report):
    """Pretty-print benchmark results."""
    agg = report["aggregate"]
    const = report["constitution"]
    
    print(f"\n{'='*60}")
    print(f"Prompt: {report['prompt']} ({report['prompt_len']} chars)")
    print(f"{'='*60}")
    
    # Constitution
    print(f"\n📜 Constitution: {sum(const.values())}/{len(const)} rules")
    for rule, ok in const.items():
        print(f"  {'✅' if ok else '❌'} {rule}")
    
    # Per-task
    print(f"\n📊 Tasks:")
    for r in report["scores"]:
        bar = "█" * int(r["score"] * 20) + "░" * (20 - int(r["score"] * 20))
        print(f"  [{r['difficulty'][:1].upper()}] {r['id']:<35s} {r['score']:.3f} {bar}")
    
    # Aggregate
    print(f"\n📈 Aggregate:")
    print(f"  Overall:  {agg['overall']:.3f}")
    print(f"  Easy:     {agg['easy']:.3f} ({sum(1 for r in report['scores'] if r['difficulty']=='easy')} tasks)")
    print(f"  Medium:   {agg['medium']:.3f} ({sum(1 for r in report['scores'] if r['difficulty']=='medium')} tasks)")
    print(f"  Hard:     {agg['hard']:.3f} ({sum(1 for r in report['scores'] if r['difficulty']=='hard')} tasks)")
    
    return agg["overall"]


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--prompt", help="Single prompt file to benchmark")
    parser.add_argument("--compare", nargs="+", help="Compare multiple prompt files")
    parser.add_argument("--engine", default="deepseek/deepseek-v4-flash")
    parser.add_argument("--json", action="store_true", help="Output JSON")
    args = parser.parse_args()
    
    if not args.prompt and not args.compare:
        print("Usage: python3 benchmark.py --prompt <file>  OR  --compare <file1> <file2> ...")
        return
    
    files = args.compare if args.compare else [args.prompt]
    
    if not args.compare:
        # Single prompt
        report = benchmark(files[0], args.engine)
        if args.json:
            print(json.dumps(report, indent=2, ensure_ascii=False))
        else:
            print_report(report)
    else:
        # Compare multiple
        reports = {}
        for f in files:
            print(f"\n⏳ Benchmarking {f}...")
            reports[f] = benchmark(f, args.engine, verbose=False)
        
        print(f"\n{'='*60}")
        print("COMPARISON")
        print(f"{'='*60}")
        print(f"{'Prompt':<30s} {'Len':>5s} {'Overall':>8s} {'Easy':>8s} {'Med':>8s} {'Hard':>8s} {'Const':>6s}")
        print("-" * 75)
        for f, r in reports.items():
            name = Path(f).name[:28]
            a = r["aggregate"]
            c = r["constitution_score"]
            print(f"{name:<30s} {r['prompt_len']:>5d} {a['overall']:>8.3f} {a['easy']:>8.3f} {a['medium']:>8.3f} {a['hard']:>8.3f} {c:>6.2f}")
        
        if args.json:
            print(json.dumps({f: r for f, r in reports.items()}, indent=2, ensure_ascii=False))


if __name__ == "__main__":
    main()
