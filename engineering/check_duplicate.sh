#!/usr/bin/env bash
# 薄壳（2026-10-22 迁移）：真实现已迁至 math-proof preset 的系统门禁层
#   ~/.dsh/.agent-presets/math-proof/scripts/gates.mjs duplicate
# 迁移理由：① bash 门禁每次起 bash+多次 grep -r 全库扫描（慢）；② 门禁属预设系统层，
#   不该由智能体在数据仓里自写（用户 2026-10-22 裁定）。命令面保持不变（--all/--warn 兼容）。
set -uo pipefail
PRESET="${MATH_PROOF_PRESET:-${DSH_HOME:-$HOME/.dsh}/.agent-presets/math-proof}"
GATES="$PRESET/scripts/gates.mjs"
if [ ! -f "$GATES" ]; then
  echo "找不到系统门禁实现 $GATES（math-proof preset 未部署？）" >&2
  exit 2
fi
ROOT="$(cd "$(dirname "$0")/.." && pwd)" || exit 2
cd "$ROOT" || exit 2
MODE="--staged"
WARN=""
for a in "$@"; do
  case "$a" in
    --all)  MODE="--head" ;;
    --warn) WARN="--warn" ;;
    *) echo "未知参数: $a" >&2; exit 2 ;;
  esac
done
exec node "$GATES" duplicate "$MODE" $WARN
