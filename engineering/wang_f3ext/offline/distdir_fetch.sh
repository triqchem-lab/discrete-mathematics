#!/bin/bash
# 预下 distdir 档案: 8 路并行, 经用户 socks5 代理 127.0.0.1:10808
# 输入: /tmp/distdir_todo.txt (url<TAB>integrity 每行)
fetch_one() {
  url="$1"
  fname="${url##*/}"
  out="/tmp/distdir/$fname"
  [ -s "$out" ] && return 0
  for attempt in 1 2 3; do
    if curl -sfL --proxy socks5h://127.0.0.1:10808 --max-time 600 "$url" -o "$out.part"; then
      mv "$out.part" "$out"
      return 0
    fi
    sleep 3
  done
  echo "FAILED $url" >> /tmp/distdir_failures.txt
  rm -f "$out.part"
  return 1
}
export -f fetch_one
mkdir -p /tmp/distdir
: > /tmp/distdir_failures.txt
cut -f1 /tmp/distdir_todo.txt | xargs -P 8 -I{} bash -c 'fetch_one "$@"' _ {}
echo "done; failures: $(wc -l < /tmp/distdir_failures.txt)"
