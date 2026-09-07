#!/usr/bin/env bash
# 群论链验证闸门 (group-theory proof-chain gate)
#
# 与 check_fermat_chain.sh 同一依赖纪律:
#   单模块 exit=0 + 零 postulate/hole 作为整链健康信号.
#
# 链 (拓扑序):
#   DuodecClock (DC 载体+群公理) → DuodecClockProperties (性质)
#     → DCGroup (DCAbelianGroup 实例)
#     → InformationStructure / NormExactSequence (L1: 非分裂正合列)
#     → NormHomomorphism (L2: 范数同态+核)
#     → CyclicGroupStructure (L3: 分量级联合周期)
#     → DayanCore (L4: 表现级记录 ⟨δ,φ|δ³=id,φ⁴=id,δφ=φδ⟩, 抽象导出 (δ∘φ)¹²=id)
#
# 用法:
#   ./engineering/check_group_chain.sh            # 全部检查
#   ./engineering/check_group_chain.sh DayanCore  # 单模块
#
# 退出码: 0 = 全绿; 1 = 编译失败; 2 = postulate/hole 泄漏

set -u
cd "$(dirname "$0")/.."   # 仓库根

AGDA="${GROUP_AGDA:-$HOME/.local/bin/agda}"
# 拓扑序: 路径相对仓库根 (InformationStructure 在 Algebra/ 下, 其余在 GroupTheory/ 下)
CHAIN="DuodecClock DuodecClockProperties DCGroup InformationStructure NormExactSequence NormHomomorphism CyclicGroupStructure DayanCore"

modpath() {
  case "$1" in
    InformationStructure) echo "src/Sovereign/Algebra/InformationStructure.agda" ;;
    *) echo "src/Sovereign/Algebra/GroupTheory/$1.agda" ;;
  esac
}

fail_compile=0
fail_post=0

strip_comments() {
  sed -e 's/{-[^}]*[^}]*}-//g' \
      -e 's/--.*$//' \
      "$1"
}

echo "=== 群论证明链验证闸门 ==="
echo "agda: $AGDA"
echo ""

for m in $CHAIN; do
  f="$(modpath "$m")"
  if $AGDA "$f" >/tmp/group_chain_$$.log 2>&1; then
    echo "✅ $m: exit=0"
  else
    echo "❌ $m: exit=$? (见 /tmp/group_chain_$$.log)"
    tail -5 /tmp/group_chain_$$.log
    fail_compile=1
  fi
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
rm -f /tmp/group_chain_$$.log

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
