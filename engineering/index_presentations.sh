#!/usr/bin/env bash
# 八要素 Presentation 索引工具 —— **索引，不是验证**
#
# ⚠ 定位（人类裁定 2026-10-14，见 docs/maps/八要素统一形状-2026-10-14.md）：
#   本脚本是**索引工具**，不是验证工具。它能查的只有**结构信号**：
#     · 谁实例化了 Presentation（record 类型标注）
#     · 各实例的八要素字段**齐 / 缺**
#     · 白名单（工具件/非展示群件）是否被正确排除
#   它**不能**校验数学内容 —— assoc 是否真成立、rigidity 是否真由 galoisConjugate
#   诱导、phase-cycle 的相位结构是否正确：**那是 Agda 类型检查器的责任**。
#   故本脚本只报「字段齐 / 缺」，**不判「通过 / 不通过」**，也不用「正确 / 错误」字样。
#   ⚠ 字段完整性 ≠ 数学正确性。勿把「索引结果」读作「数学结论」。
#
# 用法：engineering/index_presentations.sh [ROOT]     # 默认 ROOT=src
# 退出码：0 = 索引完成（**不代表任何数学结论**）；2 = 用法错误
set -uo pipefail
cd "$(dirname "$0")/.." || exit 2

ROOT="${1:-src}"
DEF="src/Sovereign/Algebra/Presentation.agda"

if [ ! -f "$DEF" ]; then
  echo "找不到 $DEF（工作目录 $(pwd) 是否正确？）" >&2
  exit 2
fi

# ── 八要素字段清单：从 Presentation.agda 的 record 定义**提取**（不硬编码，防漂移） ──
FIELDS=$(awk '/^record Presentation/,/^open Presentation/' "$DEF" \
         | grep -oE '^[[:space:]]+[a-zA-Z][A-Za-z0-9ˡʳ-]*[[:space:]]*:' \
         | sed 's/[[:space:]]*:.*//; s/^[[:space:]]*//' | sort -u)
N_FIELDS=$(echo "$FIELDS" | grep -c . || true)

# ── 白名单：工具件 / 非展示群件，不参与索引（DuodecClock 红线：A₄ 亦非十二进制） ──
WHITELIST_RE='Techniques/|/archive/'

echo "════ 八要素 Presentation 索引（root=$ROOT）════"
echo "字段模板（来自 $DEF，共 $N_FIELDS 字段）："
echo "$FIELDS" | tr '\n' ' ' | sed 's/^/  /'
echo

# ── 找实例：类型标注形式  `X : Presentation A` ──
# ⚠ 不排除 Presentation.agda —— 实例（dc-presentation）就写在那里；
#   类型类定义行 `record Presentation (A : Set) : Set₁` 不含 `: Presentation ` 故不会误匹配。
HITS=$(grep -rnE ':[[:space:]]*Presentation[[:space:]]' "$ROOT" --include=*.agda 2>/dev/null \
       | grep -vE "$WHITELIST_RE" || true)

N_HITS=$(echo "$HITS" | grep -c . || true)
echo "摘要：发现 $N_HITS 个 Presentation 实例。"
echo

if [ "$N_HITS" -eq 0 ]; then
  echo "  （无）"
else
  echo "$HITS" | while IFS= read -r line; do
    FILE="${line%%:*}"
    REST="${line#*:}"
    LN="${REST%%:*}"
    echo "── $FILE:$LN"
    # 该实例的 record 块：从标注行起取到首个以 `  }` 收尾处
    BLOCK=$(sed -n "${LN},$((LN+120))p" "$FILE" | sed '/^[[:space:]]*}/q')
    MISSING=""
    for f in $FIELDS; do
      # 字段出现在 `; f =` 或 `{ f =` 或 `; f  =` 形式
      if ! echo "$BLOCK" | grep -qE "(^|[;{][[:space:]]*)${f}[[:space:]]*="; then
        MISSING="$MISSING $f"
      fi
    done
    if [ -z "$MISSING" ]; then
      echo "   ✓ 字段齐全（$N_FIELDS/$N_FIELDS）"
    else
      echo "   ⚠ 缺字段:$MISSING"
    fi
  done
fi

echo
echo "════ 免责声明 ════"
echo "本输出是**结构索引**，不是数学裁定："
echo "  · 「字段齐全」⇒ 该实例在**形式**上提供了八要素字段；"
echo "  · 它**不**表示 assoc 成立、rigidity 确由 galoisConjugate 诱导、phase 结构正确；"
echo "  · 上述判定属 **Agda 类型检查器**（编译）与**台账**（proof_dag）的权威范围。"
echo "  · 白名单（$WHITELIST_RE）已排除工具件/归档件。"
echo "  权威顺序：类型检查器 > 台账 > 本文档索引。"

exit 0
