#!/bin/bash
# 手工构建 Wang 框架(wcgbg/tensor-rank-lower-bound @ 9db3d21 + 本目录的 F₃ 扩展补丁),
# 不依赖 bazel / Xcode: clang++ 直编 + shim/ 目录下的垫片(ng-log, gflags, tbb, boost, protobuf)。
#
# 用法:
#   [WANG_REPO=<上游工作副本>] [CXX=<编译器>] [M=1 N0=3 N1=3 N2=3] \
#     build.sh <P> <verifier|enumerator|lower> <输出二进制>
#   P = 素域特征(2 或 3); M 扩张次数(矩阵族只支持 M=1); N0 N1 N2 = ⟨N0,N1,N2⟩ 格式。
#   WANG_REPO 缺省 /tmp/wang-tensor-rank —— 须是已应用 f3_extension.patch 并放入
#   fq_matrix.h / fq_matrix_tables.h 的上游副本(见 README.md「准备上游副本」)。
#   线程数由环境变量 SHIM_THREADS 控制(缺省 = 硬件并发数)。
#
# 例:
#   build.sh 3 verifier   /tmp/wang-f3/verifier_f3
#   build.sh 3 enumerator /tmp/wang-f3/enumerator_f3
#   build.sh 3 lower      /tmp/wang-f3/lower_f3
set -e
P=$1; WHAT=$2; OUT=$3
if [ -z "$P" ] || [ -z "$WHAT" ] || [ -z "$OUT" ]; then
  echo "usage: build.sh <P> <verifier|enumerator|lower> <output>" >&2
  exit 2
fi
REPO="${WANG_REPO:-/tmp/wang-tensor-rank}"
SHIM="$(cd "$(dirname "${BASH_SOURCE[0]}")/shim" && pwd)"
CXX="${CXX:-/opt/homebrew/opt/llvm/bin/clang++}"
M="${M:-1}" N0="${N0:-3}" N1="${N1:-3}" N2="${N2:-3}"
if [ ! -x "$CXX" ]; then CXX="$(command -v clang++ || command -v g++)"; fi
if [ ! -d "$REPO/problems/matrix" ]; then
  echo "WANG_REPO=$REPO 不是上游副本(缺 problems/matrix)" >&2
  exit 2
fi
case "$WHAT" in
  verifier)   MAIN=verifier/verifier_main.cc ;;
  enumerator) MAIN=search/orbit_enumerator_main.cc ;;
  lower)      MAIN=search/rank_lower_bound_main.cc ;;
  *) echo "unknown target $WHAT" >&2; exit 2 ;;
esac
# 用数组而不是字符串: zsh 不对未加引号的 $VAR 做分词, 字符串形式的 -D 列表会被当成一个参数。
DEFS=(-DCP_MATRIX "-DCP_P=$P" "-DCP_M=$M" "-DCP_N0=$N0" "-DCP_N1=$N1" "-DCP_N2=$N2")
"$CXX" -std=c++23 -O3 -march=native -DNDEBUG -w \
  -I"$SHIM" -I"$REPO" "${DEFS[@]}" \
  "$REPO/core/backtracking_proof.cc" "$REPO/core/dynamic_matrix.cc" "$REPO/$MAIN" \
  -o "$OUT" -lz -pthread
echo "built $OUT ($WHAT, P=$P, M=$M, n$N0$N1$N2)"
