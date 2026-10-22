#!/usr/bin/env bash
# 薄壳（2026-10-22 迁移）：真实现 → math-proof preset scripts/gates.mjs incremental --all
# 全库并行独立编译验证（等价旧版；并发=旧第一参数，默认 12；HEAP/AGDA 环境变量兼容）。
# 用法: ./engineering/check_all_modules_parallel.sh [并发数]（默认 12）
set -uo pipefail
PRESET="${MATH_PROOF_PRESET:-${DSH_HOME:-$HOME/.dsh}/.agent-presets/math-proof}"
GATES="$PRESET/scripts/gates.mjs"
if [ ! -f "$GATES" ]; then
  echo "找不到系统门禁实现 $GATES（math-proof preset 未部署？）" >&2
  exit 2
fi
ROOT="$(cd "$(dirname "$0")/.." && pwd)" || exit 2
cd "$ROOT" || exit 2
JOBS="${1:-12}"
exec node "$GATES" incremental --all --jobs "$JOBS" --heap "${HEAP:-6G}"
