#!/usr/bin/env bash
# Fermat 链验证闸门 (proof-chain gate)
#
# 对标 leanprover/fermats-last-theorem 的依赖纪律:
#   Claude 用 #print axioms 验"顶层定理公理集不扩散"; 我们以
#   "单模块 exit=0 + 零 postulate/hole" 作为整链健康信号.
#
# 链: FermatL0 (定义) → L1 (GF(3)× 周期2) → L2 (mod3 分类)
#                         └→ L3 (GF(9)× 周期8)   (L0+L1 为共同地基)
#      L4_NatLift (ℕ 提升: 偶次费马方程 ℤ 层无"三皆非3倍数"解) 依赖 L0+L1
#
# 用法:
#   ./engineering/check_fermat_chain.sh          # 全部检查
#   ./engineering/check_fermat_chain.sh L1       # 单模块
#   FERMAT_AGDA=agda ./engineering/check_fermat_chain.sh  # 指定 agda
#
# 退出码: 0 = 全绿; 1 = 有模块编译失败; 2 = 有 postulate/hole 泄漏

set -u
cd "$(dirname "$0")/.."   # 仓库根

AGDA="${FERMAT_AGDA:-$HOME/.local/bin/agda}"
FERMAT_DIR="src/Sovereign/Problem/Fermat"
# 拓扑序: 依赖先于被依赖者编译
CHAIN="FermatL0 FermatL1 FermatL2 FermatL3 FermatL4_NatLift FermatL4_Mod12Cycle"
# 词法 (非注释) 扫描对象: 真正的 postulate/hole 声明
declare -a FILES
for m in $CHAIN; do FILES+=("$FERMAT_DIR/$m.agda"); done

fail_compile=0
fail_post=0

# 剥离注释与字符串后扫描 (避免注释里的 "0 postulate" 误报)
strip_comments() {
  # 去掉 {- -} 块注释、-- 行注释、{! !} 之外的内容保留标记
  sed -e 's/{-[^}]*[^}]*}-//g' \
      -e 's/--.*$//' \
      "$1"
}

echo "=== Fermat 证明链验证闸门 ==="
echo "agda: $AGDA"
echo ""

for m in $CHAIN; do
  f="$FERMAT_DIR/$m.agda"
  # 1) 编译
  if $AGDA "$f" >/tmp/fermat_chain_$$.log 2>&1; then
    echo "✅ $m: exit=0"
  else
    echo "❌ $m: exit=$? (见 /tmp/fermat_chain_$$.log)"
    tail -5 /tmp/fermat_chain_$$.log
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
rm -f /tmp/fermat_chain_$$.log

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
