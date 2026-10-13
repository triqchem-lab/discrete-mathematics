#!/usr/bin/env bash
# 阶段 1a：依赖边 CSV（src_module -> dep_module）
set -u
ROOT="${1:-src/Sovereign}"
echo "src,dst"
find "$ROOT" -name "*.agda" | sort | while read -r f; do
  mod=$(grep -m1 "^module " "$f" | sed 's/^module \([^ ]*\).*/\1/'); [ -z "$mod" ] && continue
  grep -E "^(open )?import " "$f" | sed -E "s/^(open )?import[[:space:]]+([A-Za-z0-9._'-]+).*/\2/" | sort -u | while read -r d; do
    echo "$mod,$d"
  done
done
