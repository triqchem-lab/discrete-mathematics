#!/usr/bin/env bash
# Firefox 冒烟辅助 v3：禁内容沙箱（本机内核要求，同 Chrome --no-sandbox 的定位）。
url="$1"; out="$2"
export MOZ_DISABLE_CONTENT_SANDBOX=1
export MOZ_DISABLE_GPU_SANDBOX=1
export MOZ_DBUS_REMOTE=0
unset DBUS_SESSION_BUS_ADDRESS
firefox --new-window "$url" > /data/tmp/ff-debug.log 2>&1 &
fpid=$!
sleep 12
import -window root "$out" 2>/dev/null
kill $fpid 2>/dev/null; wait $fpid 2>/dev/null
echo "--- ff log tail ---"
tail -3 /data/tmp/ff-debug.log
