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
# 拓扑序: 路径相对仓库根 (InformationStructure 在 Algebra/RingTheory/ 下, 其余在 Algebra/GroupTheory/ 下)
# ⚠ 2026-10-21 修复：目录重组（2026-10-19）后 InformationStructure 迁至 Algebra/RingTheory/，
#   本脚本仍指向旧路径 ⇒ 自重组起一直是**假失败**（Cannot read file / does not exist）。
CHAIN="DuodecClock DuodecClockProperties DCGroup InformationStructure NormExactSequence NormHomomorphism CyclicGroupStructure DayanCore"

# 路径解析：**首选已知位置，回退到全库 find** —— 避免目录重组再次把硬编码路径打断
# （2026-10-21 教训：InformationStructure 迁到 Algebra/RingTheory/ 后，本脚本仍指向旧路径，
#   于是「链断裂」实际是「读不到文件」，静默假失败了 2 天。）
modpath() {
  case "$1" in
    InformationStructure)
      if [ -f "src/Sovereign/Algebra/RingTheory/InformationStructure.agda" ]; then
        echo "src/Sovereign/Algebra/RingTheory/InformationStructure.agda"
      else
        find src/Sovereign -name "InformationStructure.agda" -not -path "*/archive/*" | head -1
      fi ;;
    *)
      if [ -f "src/Sovereign/Algebra/GroupTheory/$1.agda" ]; then
        echo "src/Sovereign/Algebra/GroupTheory/$1.agda"
      else
        find src/Sovereign -name "$1.agda" -not -path "*/archive/*" | head -1
      fi ;;
  esac
}

# 预检：链成员**路径存在性**（缺文件 ⇒ 路径失效，**不是**证明错误）
stale=0
for m in $CHAIN; do
  f="$(modpath "$m")"
  if [ -z "$f" ] || [ ! -f "$f" ]; then
    echo "❌ 路径失效: $m（找不到对应 .agda —— 目录重组后本脚本未同步？）"
    stale=1
  fi
done
if [ "$stale" -ne 0 ]; then
  echo ""
  echo "❌ 预检失败：链成员路径失效。这是**门禁脚本自身过期**，不是证明错误。"
  echo "   修法：核对 engineering/check_group_chain.sh 的 modpath()（它已有 find 回退，仍失败则模块确实不存在）。"
  exit 2
fi

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
