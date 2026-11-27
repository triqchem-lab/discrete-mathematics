#!/bin/bash
# guarded_run.sh <limit_gb> <tag> <binary> [args...]
# 跑一次下界搜索(在它自己唯一的子进程里), 日志 + 资源用量写到 $WANG_RUN/<tag>.log, 结束后写 <tag>.status。
# 内存哨兵: 进程占用(见 footprint.sh, 含被压缩 / 换出的部分) >= limit_gb(整数 GB; 0 = 不限)就杀掉,
# 并在 status 里记 MEMORY GUARD。
# 环境变量(SOVEREIGN_F3_FANOUT 等)原样传给二进制。WANG_RUN 缺省 ./wang-run。
#
# 注意: 证书只在整维做完时落盘 —— 被哨兵杀掉 = 正在跑的那一维白跑。所以请在证书的副本上跑, 预算先小后大。
# 用法示例(在 v3 证书的副本上给 dim 2-0 开 3e8 步, 扇出 4, 占用超过 40 GB 就杀):
#   SOVEREIGN_F3_FANOUT=4 bash guarded_run.sh 40 d210_3e8 ./lower_f3 c.pb.txt --dim_max=2 \
#       --backtracking_step_limit=300000000 --forced_product_max_iterations_log2=28 --backtracking_max_map_size=2000000
set -u
LIMIT_GB=$1; TAG=$2; shift 2
case "$LIMIT_GB" in
  ''|*[!0-9]*) echo "usage: guarded_run.sh <limit_gb 整数, 0 = 不限> <tag> <binary> [args...]" >&2; exit 2 ;;
esac
HERE=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)
# shellcheck source=footprint.sh
source "$HERE/footprint.sh"
RUN=${WANG_RUN:-./wang-run}
mkdir -p "$RUN"
LOG="$RUN/$TAG.log"
ST="$RUN/$TAG.status"
{
  echo "START $(date '+%F %T') HOST $(hostname)"
  echo "CMD: $*"
  echo "CWD: $(pwd)  SOVEREIGN_F3_FANOUT=${SOVEREIGN_F3_FANOUT:-unset}  SHIM_THREADS=${SHIM_THREADS:-unset}  limit=${LIMIT_GB}GB"
} > "$LOG"
"$@" >> "$LOG" 2>&1 &
PID=$!
echo "START $(date '+%F %T') pid=$PID limit=${LIMIT_GB}GB" > "$ST"
PEAK=0
while kill -0 "$PID" 2>/dev/null; do
  mb=$(footprint_mb "$PID")
  if [ -n "$mb" ] && [ "$mb" -gt "$PEAK" ]; then PEAK=$mb; fi
  if [ -n "$mb" ] && [ "$LIMIT_GB" -gt 0 ] && [ "$mb" -ge $((LIMIT_GB * 1024)) ]; then
    echo "MEMORY GUARD $(date '+%T'): footprint=${mb}MB >= $((LIMIT_GB * 1024))MB -> kill" >> "$ST"
    pkill -P "$PID" 2>/dev/null; kill "$PID" 2>/dev/null
  fi
  sleep 2
done
wait "$PID"; RC=$?
echo "exit=$RC END $(date '+%F %T') peak_footprint=${PEAK}MB" >> "$LOG"
echo "exit=$RC END $(date '+%F %T') peak_footprint=${PEAK}MB" >> "$ST"
exit $RC
