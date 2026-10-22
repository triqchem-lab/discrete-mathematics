#!/usr/bin/env bash
# 薄壳（2026-10-22 迁移）：真实现 → math-proof preset scripts/gates.mjs structure-lint
# 参数兼容：旧 `ROOT`（默认 src）→ --scan-root ROOT
set -uo pipefail
PRESET="${MATH_PROOF_PRESET:-${DSH_HOME:-$HOME/.dsh}/.agent-presets/math-proof}"
GATES="$PRESET/scripts/gates.mjs"
if [ ! -f "$GATES" ]; then
  echo "找不到系统门禁实现 $GATES（math-proof preset 未部署？）" >&2
  exit 2
fi
ROOT="$(cd "$(dirname "$0")/.." && pwd)" || exit 2
cd "$ROOT" || exit 2
if [ -n "${1:-}" ]; then
  exec node "$GATES" structure-lint --scan-root "$1"
fi
exec node "$GATES" structure-lint
