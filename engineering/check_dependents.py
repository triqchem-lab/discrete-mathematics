#!/usr/bin/env python3
"""薄壳（2026-10-22 迁移）：真实现 → math-proof preset scripts/gates.mjs incremental

增量门禁：只编译「改动模块 + 传递下游」。命令面与旧版一致：
  python3 engineering/check_dependents.py <改动的.agda> ... [--jobs N] [--heap 6G] [--dry-run]
  python3 engineering/check_dependents.py --all
"""
import os
import sys

PRESET = os.environ.get("MATH_PROOF_PRESET", os.path.join(os.environ.get("DSH_HOME", os.path.expanduser("~/.dsh")), ".agent-presets", "math-proof"))
GATES = os.path.join(PRESET, "scripts", "gates.mjs")
if not os.path.isfile(GATES):
    sys.stderr.write("找不到系统门禁实现 %s（math-proof preset 未部署？）\n" % GATES)
    sys.exit(2)
os.chdir(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
os.execvp("node", ["node", GATES, "incremental"] + sys.argv[1:])
