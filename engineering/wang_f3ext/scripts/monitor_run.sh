#!/bin/bash
# monitor_run.sh <tag> [间隔秒=300] —— 每隔一段时间打印一行: 时间 / 进度日志的最后一行 / 进程占用。
# 日志与 status 在 $WANG_RUN/<tag>.{log,status}。进程结束即退出。
TAG=$1; INTERVAL=${2:-300}
HERE=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)
source "$HERE/footprint.sh"
RUN=${WANG_RUN:-./wang-run}
LOG="$RUN/$TAG.log"
while true; do
  pid=$(awk '{for (i = 1; i <= NF; ++i) if ($i ~ /^pid=/) {sub("pid=", "", $i); print $i}}' "$RUN/$TAG.status" 2>/dev/null | head -1)
  if [ -z "$pid" ] || ! kill -0 "$pid" 2>/dev/null; then break; fi
  printf '%s footprint=%sMB  %s\n' "$(date '+%T')" "$(footprint_mb "$pid")" \
      "$(awk '/P1:|Processing dim=|duration=|Better LB/ {line=$0} END {print line}' "$LOG" | cut -c1-90)"
  sleep "$INTERVAL"
done
tail -1 "$RUN/$TAG.status" 2>/dev/null
