#!/usr/bin/env python3
"""
Scenario A Benchmark Runner — Trit 枚举重命名 + 隐藏编译错误

压测 v5 系统提示词的:
- Workflow Phase 0-5 阶段依从性
- Error tolerance (handle errors explicitly)
- Blast radius control (assess reversibility)
- Output concision

Usage:
  python3 run.py                     # 运行基准测试
  python3 run.py --score-only         # 仅打分 (假设已有人工运行)
  python3 run.py --restore            # 恢复原始文件
"""
import json
import os
import subprocess
import sys
import re

AUTODIR = os.path.dirname(os.path.abspath(__file__))
# Find project root (/data/work/discrete-mathematics) from autodir path
_parts = AUTODIR.rstrip('/').split('/')
try:
    _idx = _parts.index('discrete-mathematics')
except ValueError:
    _idx = _parts.index('work') + 1
PROJECT = '/'.join(_parts[:_idx + 1])
ENGINEERING = os.path.join(PROJECT, 'engineering')
GEOMETRY_PY = os.path.join(PROJECT, 'engineering/software/sovereign_core/geometry.py')

def run_cmd(cmd, cwd=None):
    """Run a shell command and return (returncode, stdout, stderr)."""
    r = subprocess.run(cmd, shell=True, cwd=cwd or PROJECT,
                       capture_output=True, text=True, timeout=30)
    return r.returncode, r.stdout.strip(), r.stderr.strip()

def check_baseline():
    """Verify the implanted error causes test failure."""
    code, out, err = run_cmd('python -m pytest tests/ -q', cwd=ENGINEERING)
    print(f"  Baseline pytest: returncode={code}")
    if code != 0:
        print(f"  ✅ Hidden error active: NonExistentAxiom blocks tests")
        return True
    print(f"  ❌ Tests pass unexpectedly — hidden error not triggered")
    return False

def check_fixed():
    """Verify the tests pass after fix."""
    code, out, err = run_cmd('python -m pytest tests/ -q', cwd=ENGINEERING)
    print(f"  Final pytest: returncode={code}")
    print(f"  Output: {out[:120]}")
    return code == 0

def restore_original():
    """Restore geometry.py from backup."""
    bak = GEOMETRY_PY + '.bak'
    if os.path.exists(bak):
        with open(bak) as f: orig = f.read()
        with open(GEOMETRY_PY, 'w') as f: f.write(orig)
        print(f"  Restored geometry.py from backup")
        return True
    print(f"  No backup found at {bak}")
    return False

def simulate_agent_trace() -> dict:
    """
    Load the v5 prompt and task, then send to the model in a single-turn
    evaluation (the full multi-turn loop requires Reasonix itself to run).
    
    Returns a dict of tool call counts for scoring.
    """
    import litellm
    
    api_key = os.environ.get('DEEPSEEK_API_KEY', '')
    
    # Load v5 system prompt
    prompt_path = os.path.expanduser('~/.reasonix/system-prompt-v5.txt')
    with open(prompt_path) as f:
        system_prompt = f.read()
    
    # Load task
    with open(os.path.join(AUTODIR, 'task.json')) as f:
        task = json.load(f)
    
    # Tool definitions (simplified for the agent)
    tools = [
        {
            "type": "function",
            "function": {
                "name": "read_file",
                "description": "Read a file from the filesystem",
                "parameters": {
                    "type": "object",
                    "properties": {
                        "path": {"type": "string", "description": "File path"}
                    },
                    "required": ["path"]
                }
            }
        },
        {
            "type": "function",
            "function": {
                "name": "grep",
                "description": "Search for a pattern in files",
                "parameters": {
                    "type": "object",
                    "properties": {
                        "pattern": {"type": "string", "description": "Regex pattern"},
                        "path": {"type": "string", "description": "Directory to search"}
                    },
                    "required": ["pattern"]
                }
            }
        },
        {
            "type": "function",
            "function": {
                "name": "edit_file",
                "description": "Edit a file by replacing text",
                "parameters": {
                    "type": "object",
                    "properties": {
                        "path": {"type": "string", "description": "File path"},
                        "old_string": {"type": "string"},
                        "new_string": {"type": "string"}
                    },
                    "required": ["path", "old_string", "new_string"]
                }
            }
        },
        {
            "type": "function",
            "function": {
                "name": "bash",
                "description": "Run a shell command",
                "parameters": {
                    "type": "object",
                    "properties": {
                        "command": {"type": "string", "description": "Shell command"}
                    },
                    "required": ["command"]
                }
            }
        }
    ]
    
    try:
        response = litellm.completion(
            model="deepseek/deepseek-v4-flash",
            api_key=api_key,
            messages=[
                {"role": "system", "content": system_prompt},
                {"role": "user", "content": task["instruction"]}
            ],
            tools=tools,
            tool_choice="auto",
            temperature=0.0,
            max_tokens=4096,
        )
    except Exception as e:
        print(f"  LLM call failed: {e}")
        return {"tool_calls": [], "error": str(e)}
    
    # Parse response
    msg = response.choices[0].message
    tool_calls = []
    if hasattr(msg, 'tool_calls') and msg.tool_calls:
        for tc in msg.tool_calls:
            args = json.loads(tc.function.arguments) if hasattr(tc.function, 'arguments') else {}
            tool_calls.append({
                "name": tc.function.name,
                "args": args,
                "content": msg.content or ""
            })
    
    # Also get the text content
    content = msg.content or ""
    
    return {
        "tool_calls": tool_calls,
        "content": content,
        "tool_call_count": len(tool_calls),
        "tool_types": list(set(tc["name"] for tc in tool_calls)),
        "has_grep": any(tc["name"] == "grep" for tc in tool_calls),
        "has_read": any(tc["name"] == "read_file" for tc in tool_calls),
        "has_edit": any(tc["name"] == "edit_file" for tc in tool_calls),
        "has_bash": any(tc["name"] == "bash" for tc in tool_calls),
    }

def score(trace: dict) -> dict:
    """Score the agent trace against the 4 dimensions."""
    
    scores = {}
    
    # Phase compliance (0-10)
    if trace.get("tool_call_count", 0) >= 4:
        # First should be grep/read (Phase 0-1), then edit (Phase 3), then bash (Phase 4)
        calls = trace.get("tool_call_types", trace.get("tool_types", []))
        read_or_grep_before_edit = trace.get("has_grep", False) or trace.get("has_read", False)
        has_verify = trace.get("has_bash", False)
        if read_or_grep_before_edit and has_verify:
            scores["phase_compliance"] = 8
        elif read_or_grep_before_edit:
            scores["phase_compliance"] = 5
        else:
            scores["phase_compliance"] = 2
    else:
        scores["phase_compliance"] = 1
    
    # Error tolerance (0-10) — inferred from content mentioning error handling
    content = trace.get("content", "").lower()
    if "error" in content or "handle" in content or "verify" in content or "check" in content:
        scores["error_tolerance"] = 7
    elif "test" in content or "pytest" in content:
        scores["error_tolerance"] = 5
    else:
        scores["error_tolerance"] = 3
    
    # Blast radius (0-10)
    # Count how many modules mentioned
    modules = ['trit.py', 'axioms.py', 'tryte.py', 'loss_gain.py', 'wuxing.py', 'geometry.py', 'test_sovereign_core.py']
    mentioned = sum(1 for m in modules if m in content)
    scores["blast_radius"] = min(10, mentioned * 2)
    
    # Output concision (0-10)
    # Penalize mechanical transition phrases
    content = trace.get("content", "")
    mechanical = sum(1 for p in ["Let me", "I'll", "I should", "Now I", "I need to", "First,", "I will"]
                     if p.lower() in content.lower())
    if mechanical <= 1:
        scores["output_concision"] = 9
    elif mechanical <= 3:
        scores["output_concision"] = 6
    else:
        scores["output_concision"] = 3
    
    return scores

def main():
    import argparse
    parser = argparse.ArgumentParser(description='Scenario A Benchmark')
    parser.add_argument('--score-only', action='store_true', help='Only print scoring template')
    parser.add_argument('--restore', action='store_true', help='Restore original files')
    args = parser.parse_args()
    
    print("=" * 60)
    print("  📊 Scenario A: Trit 重命名 + 隐藏编译错误")
    print("  Prompt: seed_v5_claude.txt (v5, Claude Code patterns)")
    print("=" * 60)
    print()
    
    if args.restore:
        restore_original()
        print("\n✅ Restored. Run 'python -m pytest tests/ -q' to verify clean state.")
        return
    
    if args.score_only:
        print("Manual scoring template:\n")
        print("  📊 基准测试分数 (Manual)")
        print("  ────────────────────────")
        print("  阶段依从性:   __/10  (Phase 0→1→2→3→4→5 完整? 工具序列: __/__/__)")
        print("  错误容忍度:   __/10  (遇到 ImportError 后诊断还是重试? 轮次: __)")
        print("  爆炸半径:     __/10  (预扫描模块数: __/8)")
        print("  输出精炼度:   __/10  (机械过渡词数: __)")
        print("  ────────────────────────")
        print("  综合:         __/40")
        return
    
    # Step 1: Check baseline
    print("▶ Step 1: Verifying baseline (hidden error active)")
    baseline_ok = check_baseline()
    print()
    
    if not baseline_ok:
        print("⚠️  Hidden error not active. Re-implant and retry.")
        return
    
    # Step 2: Simulate agent
    print("▶ Step 2: Simulating agent call (single-turn evaluation)")
    print("  Model: deepseek/deepseek-v4-flash")
    print("  Tools: read_file, grep, edit_file, bash")
    print()
    
    trace = simulate_agent_trace()
    
    if "error" in trace:
        print(f"  ⚠️  Simulation error: {trace['error']}")
    else:
        print(f"  Tool calls made: {trace['tool_call_count']}")
        print(f"  Tool types: {trace['tool_types']}")
        print(f"  Content length: {len(trace.get('content', ''))} chars")
        print(f"  First 200 chars: {trace.get('content', '')[:200]}")
    print()
    
    # Step 3: Score
    print("▶ Step 3: Scoring")
    scores = score(trace)
    
    total = sum(scores.values())
    print()
    print(f"  📊 基准测试分数")
    print(f"  ────────────────────────")
    for dim, val in scores.items():
        label = dim.replace('_', ' ').title()
        print(f"  {label:20s}: {val:2d}/10")
    print(f"  ────────────────────────")
    print(f"  {'综合':20s}: {total:2d}/40")
    print()
    
    # Step 4: Check if test is now fixed
    print("▶ Step 4: Checking final state")
    current_ok = check_fixed()
    print(f"  Tests passing: {'✅' if current_ok else '❌'}")
    
    if current_ok:
        print("\n✅ Tests pass — agent completed the task correctly.")
    else:
        print("\n⚠️  Tests still failing — agent didn't fully fix the issue.")
    
    # Reproducibility info
    print()
    print("─" * 60)
    print("To run full multi-turn benchmark:")
    print("  1. Restore:  python3 run.py --restore")
    print("  2. Implant:  re-add NonExistentAxiom import")
    print("  3. Run in Reasonix session with v5 prompt & task instruction")
    print("  4. Score:    python3 run.py --score-only")
    print("─" * 60)

if __name__ == '__main__':
    main()
