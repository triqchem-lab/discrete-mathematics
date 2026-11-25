#!/usr/bin/env bash
# RH (F₃ 全称化) 证明链验证闸门 (proof-chain gate)
#
# 对标 check_fermat_chain.sh 纪律: "单模块 exit=0 + 零 postulate/hole" 作整链健康信号。
#
# 链（import 拓扑序, 依赖先于被依赖者）:
#   NoNormT0Even → Mod3Core → NormClassify → NoNormT0General   (范数方程线: ∀② 全称分类)
#   Witness (范数见证)
#   CurveF3 → CountF3 → {CurveIsoF3, CountF9All → WeilRecurrenceAll → FrobF9 → FrobFix,
#                        HasseAllF3, TraceTableF3}  (计数线: F₃/F₉ + Frobenius σ)
#   FrobFix → GroupCls0..7 (E(F9) 群律表驱动: 8 同构类, 试点 cls6 含结合律)
#   SupersingularF3 → SupersingularDiv3 (p∣t 算术表述桥)
#   TraceTableF3 → SupersingularF3 → WaterhouseF3             (分类线)
#   Eisenstein → WeilRigidity → ZetaFrame → ZetaFunctional    (zeta 线)
#   ZetaAllF3 (汇合: CurveF3+CountF3+ZetaFrame+TraceTableF3+SupersingularF3+WeilRigidity)
#
# 用法:
#   ./engineering/check_rh_chain.sh            # 全部检查
#   ./engineering/check_rh_chain.sh NormClassify  # 单模块
#   RH_AGDA=agda ./engineering/check_rh_chain.sh  # 指定 agda
#
# 退出码: 0 = 全绿; 1 = 有模块编译失败; 2 = 有 postulate/hole 泄漏

set -u
cd "$(dirname "$0")/.."   # 仓库根

AGDA="${RH_AGDA:-$HOME/.local/bin/agda}"
RH_DIR="src/Sovereign/Application/Problems/RH"
CHAIN="NoNormT0Even Mod3Core NormClassify NoNormT0General Witness CurveF3 CountF3 CurveIsoF3 CountF9All WeilRecurrenceAll FrobF9 F9MultC8 FrobFix GroupCls0 GroupCls1 GroupCls2 GroupCls3 GroupCls4 GroupCls5 GroupCls6 GroupCls7 E3Tor HasseAllF3 TraceTableF3 SupersingularF3 SupersingularDiv3 WaterhouseF3 Eisenstein WeilRigidity ZetaFrame ZetaFunctional ZetaAllF3"

declare -a FILES
for m in $CHAIN; do
  f=""
  if [ -f "$RH_DIR/$m.agda" ]; then f="$RH_DIR/$m.agda"
  else f=$(find src/Sovereign -name "$m.agda" -not -path "*/archive/*" | head -1); fi
  if [ -z "$f" ]; then echo "FAIL: 链成员 $m 未找到（断链）"; exit 42; fi
  FILES+=("$f")
done

fail_compile=0
fail_post=0

# 剥离注释与字符串后扫描 (避免注释里的 "0 postulate" 误报)
strip_comments() {
  sed -e 's/{-[^}]*[^}]*}-//g' \
      -e 's/--.*$//' \
      "$1"
}

echo "=== RH (F₃ 全称化) 证明链验证闸门 ==="
echo "agda: $AGDA"
echo ""

only="${1:-}"
for m in $CHAIN; do
  if [ -n "$only" ] && [ "$m" != "$only" ]; then continue; fi
  f=""
  if [ -f "$RH_DIR/$m.agda" ]; then f="$RH_DIR/$m.agda"
  else f=$(find src/Sovereign -name "$m.agda" -not -path "*/archive/*" | head -1); fi
  if [ -z "$f" ]; then echo "❌ $m: 链成员未找到（断链）"; fail_compile=1; continue; fi
  # 1) 编译
  if $AGDA "$f" >/tmp/rh_chain_$$.log 2>&1; then
    echo "✅ $m: exit=0"
  else
    echo "❌ $m: exit=$? (见 /tmp/rh_chain_$$.log)"
    tail -5 /tmp/rh_chain_$$.log
    fail_compile=1
  fi
  # 2) postulate / hole 扫描 (词法, 剥注释)
  body="$(strip_comments "$f")"
  post=$(echo "$body" | grep -cE '^\s*postulate\b|\bpostulate\s+[A-Za-z_(]' || true)
  hole=$(echo "$body" | grep -c '{!' || true)
  sorry=$(echo "$body" | grep -cE '\bsorry\b|\btrustMe\b' || true)
  if [ "$post" -gt 0 ] || [ "$hole" -gt 0 ] || [ "$sorry" -gt 0 ]; then
    echo "  ⚠️  $m: postulate=$post hole=$hole sorry=$sorry"
    fail_post=1
  else
    echo "  ℹ️   $m: 0 postulate / 0 hole / 0 sorry"
  fi
done
rm -f /tmp/rh_chain_$$.log

echo ""
if [ "$fail_compile" -eq 0 ] && [ "$fail_post" -eq 0 ]; then
  echo "✅ 整链健康: 全部 exit=0, 零 postulate/hole"
  exit 0
elif [ "$fail_compile" -ne 0 ]; then
  echo "❌ 链断裂: 存在编译失败"
  exit 1
else
  echo "❌ 链污染: 存在 postulate/hole 泄漏"
  exit 2
fi
