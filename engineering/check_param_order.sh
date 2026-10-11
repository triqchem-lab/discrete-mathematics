#!/bin/bash
# check_param_order.sh —— 附录 17 参数序陷阱前置门禁（WARN-only，只报不改）
# 元评采纳件①（2026-10-11 用户终评建议）：写证明前/CI 前跑本件，机械可查子集四型：
#   P1 *-distribʳ-+ 乘数首位（stdlib 口径 (d+e)*c = d*c+e*c——与 *-distribˡ-+ 相反）
#   P2 空格算符合并（`+ pos`/`+ negsuc` 解析为 +pos/+negsuc 连写——真二元 + 需括号形）
#   P3 _≡_ 首隐式是 Level（显式 `{…}` 位置隐式首槽 = ℓ 非类型——须命名 {A = …}）
#   P4 隐式钉参缺失（fzero/fsuc 在 check-* 尺寸不定语境——须 {A = Fin n}/显式尺寸）
# 用法: bash engineering/check_param_order.sh [ROOT]   （默认 src）
ROOT="${1:-src}"
cd "$(dirname "$0")/.." || exit 2
TOTAL=0
report() {
  local code="$1" name="$2" remedy="$3" pat="$4"
  local hits
  hits=$(grep -rnE "$pat" "$ROOT" --include="*.agda" 2>/dev/null)
  if [ -n "$hits" ]; then
    local n
    n=$(echo "$hits" | wc -l)
    TOTAL=$((TOTAL+n))
    echo "WARN [$code] $name — $n 处"
    head -20 <<< "$hits" | sed 's/^/    /'
    [ "$n" -gt 20 ] && echo "    …（共 $n 处）"
    echo "    规避: $remedy"
    echo
  fi
}
report "P1" "*-distribʳ-+ 乘数首位（参数序与 ⊣ 版相反）" \
  "核对参数序：*-distribʳ-+ c d e : (d+e)*c ≡ d*c+e*c——乘数 c 在首位；易误按 *-distribˡ-+ 的乘数次位写" \
  '\*-distribʳ-\+|\*-distribˡ-\+'
report "P2" "空格算符合并风险（+ pos 型）" \
  "真二元 + 后跟 pos/negsuc 须括号：写 + (pos n) 而非 + pos n（后者解析为 +pos 连写）" \
  '[^+]\+ pos |[^+]\+ negsuc |^pos |[^a-zA-Z_]\+ pos$'
report "P3" "_≡_ 位置隐式首槽是 Level 非类型" \
  "显式隐式用命名形 _≡_ {A = T}；位置形 _≡_ {x} 的首槽是 ℓ" \
  '_≡_ \{[^ }Aℓ_]|≡_ \{[^ }Aℓ_]'
report "P4" "fzero/fsuc 签名位尺寸不钉（隐式钉参风险）" \
  "类型签名里的 fzero/fsuc 需显式钉 {A = Fin n} 或尺寸实参（fzero : Fin (suc ?n) 不钉即 meta）——本项只查签名位" \
  '^[A-Za-z_][^:]*:.*\b(fzero|fsuc)\b'
echo "== 参数序门禁汇总: WARN $TOTAL 处（只报不改；逐处人工核参数序/括号/钉参）"
exit 0
