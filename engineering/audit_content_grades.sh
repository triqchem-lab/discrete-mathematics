#!/usr/bin/env bash
# A/B/C 内容分级【静态初筛】——B/C 启发式；判 A 必须 proof_compile 回执 + 人工四问验收。
# 用法: engineering/audit_content_grades.sh [ROOT]   （默认 src）
set -u
ROOT="${1:-src}"
echo "# 内容分级初筛（静态，非权威——A 级以 proof_dag 内容闸门 + 回执为准）"
echo "# 文件 | 行 | 剥注释postulate | 洞 | 顶层签名 | 初筛 | 备注"
A_c=0; B_c=0; C_c=0
while IFS= read -r f; do
  [ -e "$f" ] || continue
  case "$f" in *_archive*|*_Probe*|*_PA*|*_P[A-Z]*|*/probes-tmp/*) continue;; esac
  lines=$(wc -l < "$f")
  code=$(sed 's/--.*//' "$f")
  post=$(printf '%s' "$code" | grep -c "postulate")
  holes=$(printf '%s' "$code" | grep -c "{!")
  thms=$(printf '%s' "$code" | grep -cE "^[[:alpha:]][[:alnum:]₀-₉ₐ-ₜ'₀-₉*-]* *:")
  if [ "$holes" -gt 0 ]; then grade=C; note="含洞——必删或补"; C_c=$((C_c+1))
  elif [ "$thms" -lt 3 ] && [ "$lines" -lt 30 ]; then grade=C; note="近空壳（签名/注释为主）"; C_c=$((C_c+1))
  elif [ "$post" -gt 0 ]; then grade=B; note="含 postulate——查 kind 登记"; B_c=$((B_c+1))
  else grade=B; note="静态通过——补回执+四问后方可判 A"; B_c=$((B_c+1)); fi
  printf '%s | %s | %s | %s | %s | %s | %s\n' "$f" "$lines" "$post" "$holes" "$thms" "$grade" "$note"
done < <(find "$ROOT" -name "*.agda" | sort)
echo "# 合计: C=$C_c B=$B_c A=$A_c（A 由 proof_dag 内容闸门判定，本脚本不签发 A）"
