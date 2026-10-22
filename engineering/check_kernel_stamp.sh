#!/usr/bin/env bash
# 薄壳（2026-10-22 迁移）：真实现 → math-proof preset scripts/gates.mjs kernel-stamp
# 内核版本戳门禁（eb1251683f）：判据模块 PatchedTypeChecker.agda 在补丁内核上编译通过。
# 环境兼容：AGDA（正控制内核，默认 ~/.local/bin/agda）/ REF_AGDA（参考内核，设了就跑负控制）/ HEAP（默认 6G）
set -uo pipefail
PRESET="${MATH_PROOF_PRESET:-${DSH_HOME:-$HOME/.dsh}/.agent-presets/math-proof}"
GATES="$PRESET/scripts/gates.mjs"
if [ ! -f "$GATES" ]; then
  echo "找不到系统门禁实现 $GATES（math-proof preset 未部署？）" >&2
  exit 2
fi
ROOT="$(cd "$(dirname "$0")/.." && pwd)" || exit 2
cd "$ROOT" || exit 2
ARGS=(--heap "${HEAP:-6G}")
if [ -n "${REF_AGDA:-}" ]; then
  ARGS+=(--ref-agda "$REF_AGDA")
fi
if [ -n "${AGDA:-}" ]; then
  ARGS+=(--agda "$AGDA")
fi
exec node "$GATES" kernel-stamp "${ARGS[@]}"
