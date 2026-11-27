#!/bin/bash
# footprint.sh <pid> —— 打印一个进程的内存占用(MB), 整数。
# macOS: 用 top 的 MEM 列(含被系统压缩的部分)。不能量 RSS: 2026-11-28 D 段的进程 RSS 只有 3-4 GB,
#        占用却是 25 GB, 交换区快满时按 RSS 设的哨兵没响。
# Linux: /proc/<pid>/status 的 VmRSS + VmSwap。
footprint_mb() {
  local pid=$1
  if [ "$(uname)" = Darwin ]; then
    # top -l 1 输出: 表头 "PID   MEM" 之后每进程一行 "<pid> <大小><单位>"
    top -l 1 -pid "$pid" -stats pid,mem 2>/dev/null | awk -v p="$pid" '
      $1 == p { v=$2; u=substr(v, length(v)); n=substr(v, 1, length(v)-1) + 0;
                if (u == "G") printf "%d\n", n*1024; else if (u == "M") printf "%d\n", n;
                else if (u == "K") printf "%d\n", n/1024; else printf "%d\n", n/1048576; exit }'
  else
    awk '/^VmRSS:/ {r=$2} /^VmSwap:/ {s=$2} END {printf "%d\n", (r+s)/1024}' "/proc/$pid/status" 2>/dev/null
  fi
}
if [ "${BASH_SOURCE[0]}" = "$0" ]; then
  footprint_mb "$1"
fi
