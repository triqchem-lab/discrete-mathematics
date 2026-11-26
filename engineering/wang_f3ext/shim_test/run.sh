#!/bin/bash
# 垫片分块回归测试的构建 + 运行(对 SHIM_THREADS = 1..8 各跑一遍)。
# 用法: run.sh   (在本目录运行; 需要 clang++ 或 g++)
set -e
cd "$(dirname "$0")"
CXX="${CXX:-$(command -v clang++ || command -v g++)}"
OUT=$(mktemp -d)
trap 'rm -rf "$OUT"' EXIT
"$CXX" -std=c++17 -O2 -pthread -I../shim parallel_for_test.cc -o "$OUT/parallel_for_test"
rc=0
for n in 1 2 3 4 5 6 7 8; do
  if ! SHIM_THREADS=$n "$OUT/parallel_for_test"; then rc=1; fi
done
exit $rc
