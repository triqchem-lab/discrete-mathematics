#!/bin/bash
# 垫片分块回归测试的构建 + 运行(对 SHIM_THREADS = 1..8 各跑一遍)。
# 用法: run.sh   (在本目录运行; 需要 clang++ 或 g++)
set -e
cd "$(dirname "$0")"
CXX="${CXX:-$(command -v clang++ || command -v g++)}"
OUT=$(mktemp -d)
trap 'rm -rf "$OUT"' EXIT
"$CXX" -std=c++17 -O2 -pthread -I../shim parallel_for_test.cc -o "$OUT/parallel_for_test"
# LOG_EVERY_T 的语义(首次立即输出, 之后按间隔限速; 2026-11-28 修过一次写反的判断)
"$CXX" -std=c++17 -O2 -pthread -I../shim log_every_t_test.cc -o "$OUT/log_every_t_test"
rc=0
if ! (cd "$OUT" && "$OUT/log_every_t_test"); then rc=1; fi
for n in 1 2 3 4 5 6 7 8; do
  if ! SHIM_THREADS=$n "$OUT/parallel_for_test"; then rc=1; fi
done
exit $rc
