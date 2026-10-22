#!/usr/bin/env bash
# 薄壳（2026-10-22 迁移）：真实现 → math-proof preset scripts/gates.mjs incremental --all
# 全库串行独立编译验证（资源受限 CI 用；HEAP/AGDA 环境变量兼容）。
# 用法: HEAP=6G ./engineering/check_all_modules.sh
set -uo pipefail
PRESET="${MATH_PROOF_PRESET:-${DSH_HOME:-$HOME/.dsh}/.agent-presets/math-proof}"
GATES="$PRESET/scripts/gates.mjs"
if [ ! -f "$GATES" ]; then
  echo "找不到系统门禁实现 $GATES（math-proof preset 未部署？）" >&2
  exit 2
fi
ROOT="$(cd "$(dirname "$0")/.." && pwd)" || exit 2
cd "$ROOT" || exit 2
exec node "$GATES" incremental --all --jobs 1 --heap "${HEAP:-6G}"
