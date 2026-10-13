#!/usr/bin/env bash
# 阶段 0：模块清单 CSV（module,path,lines,imports,postulates,holes,six_section）
set -u
ROOT="${1:-src/Sovereign}"
echo "module,path,lines,imports,postulates,holes,six_section"
find "$ROOT" -name "*.agda" | sort | while read -r f; do
  mod=$(grep -m1 "^module " "$f" | sed 's/^module \([^ ]*\).*/\1/')
  [ -z "$mod" ] && mod="(none)"
  lines=$(wc -l < "$f"); imports=$(grep -c "^open import" "$f")
  post=$(sed 's/--.*//' "$f" | grep -c "postulate"); holes=$(sed 's/--.*//' "$f" | grep -c "{!")
  six=$(grep -c "^-- | Sovereign" "$f"); [ "$six" -gt 0 ] && sixv=y || sixv=n
  echo "$mod,$f,$lines,$imports,$post,$holes,$sixv"
done
