#!/bin/bash
# run_window.sh <tag> <binary> <steps> <fanout> <证书.pb.txt> [lower 的其它参数...]
# 在一份证书的**副本**上跑一个窗口(续跑模式: 已有的界保留、只改进), 带内存哨兵(WANG_LIMIT_GB, 缺省 0 = 不限),
# 结束后用 cmpcert.py 与源证书逐轨道比较。证书副本在 $WANG_RUN/<tag>/, 日志与状态在 $WANG_RUN/<tag>.{log,status};
# 之后可以用 monitor_run.sh <tag> 盯同一个 tag。
# 示例(在 v3 上给 dim 3 开 2e7 步):
#   bash run_window.sh d3_2e7 ./lower_f3 20000000 4 certs/matrix_q03_n333_v3.pb.txt --dim_min=3 --dim_max=3
set -eu
TAG=$1; BIN=$2; STEPS=$3; FAN=$4; CERT=$5; shift 5
HERE=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)
RUN=${WANG_RUN:-./wang-run}
D="$RUN/$TAG"; rm -rf "$D"; mkdir -p "$D"
cp "$CERT" "$D/c.pb.txt"
cp "${CERT%.pb.txt}.btp" "$D/c.btp"
export SOVEREIGN_F3_FANOUT="$FAN"
bash "$HERE/guarded_run.sh" "${WANG_LIMIT_GB:-0}" "$TAG" "$BIN" "$D/c.pb.txt" "$@" \
    --backtracking_step_limit="$STEPS" --forced_product_max_iterations_log2=28 \
    --backtracking_max_map_size=2000000 || true
python3 "$HERE/cmpcert.py" "$CERT" "$D/c.pb.txt" | awk '/entries|differing|improved|^  idx|final/'
echo "log: $RUN/$TAG.log   status: $RUN/$TAG.status   certificate copy: $D/c.pb.txt"
