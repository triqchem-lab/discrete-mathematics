#!/usr/bin/env bash
# 内核版本戳门禁 — 本地 Agda 工具链是否带 eb1251683f
#
# 依据（类型论展示群，docs/duodecimal/11-type-theory-presentation.md）:
#   律算框架的群论是**类型论展示群**，不是集合论群：
#     载体用 record（Σ-类型）、生成元用 data（归纳类型）、关系用 record 字段、刚性从 GF9 诱导。
#   它反对传统数学的**信息截断** —— 集合论群把群截断成 {e, g₁, …, g₁₁} 加一张运算表，
#   丢失生成元来源 / 关系体系 / Frobenius 刚性 / 相位状态（C₄）/ 时钟读数（mixedOp¹² 的过程）。
#   同理，**相异展示本就是不同对象**（Bool vs Bool2、Trit vs Fin 3、R1 vs R2）：
#   它们的 ≡ **应当判为空**。这不是新语义，是展示群立场；传统数学的截断视角才把它抹平。
#
# 判据模块: src/Sovereign/Trust/PatchedTypeChecker.agda
#   在**带 eb1251683f** 的内核上编译通过；
#   在未打补丁的内核上报 UnsolvedConstraints: Is empty: R1 ≡ R2 (stuck)（exit 42）。
#
# 用法:
#   ./engineering/check_kernel_stamp.sh                                    # 正控制
#   REF_AGDA=/opt/agda/2.8.0.1/bin/agda ./engineering/check_kernel_stamp.sh  # 正 + 负控制
#   AGDA=/opt/agda/2.8.0.1/bin/agda ./engineering/check_kernel_stamp.sh      # 只跑负侧（应失败）
#
# 环境:
#   AGDA      正控制要验的内核（默认 $HOME/.local/bin/agda）
#   REF_AGDA  参考内核；设了就跑负控制（判据必须在其上失败）
#   HEAP      单进程堆上限（默认 6G）
#
# 退出码: 0 = 判据成立; 1 = 内核被换过 / 判据失效

set -u
cd "$(dirname "$0")/.."
AGDA="${AGDA:-$HOME/.local/bin/agda}"
REF_AGDA="${REF_AGDA:-}"
MODULE="src/Sovereign/Trust/PatchedTypeChecker.agda"
HEAP="${HEAP:-6G}"

echo "=== 内核版本戳门禁（eb1251683f）==="
echo "判据模块: $MODULE"
echo "本库依据: 类型论展示群 — 反对传统数学的信息截断"
echo ""

echo "--- 版本戳 ---"
echo "agda 路径 : $AGDA"
"$AGDA" --version 2>&1 | head -1 | sed 's/^/agda 版本 : /'
git log -1 --format='repo 提交 : %h %ad %s' --date=short 2>/dev/null
echo ""

rc=0

# 正控制：判据模块必须在 $AGDA 下编译通过
echo "--- 正控制（预期 exit 0）: 内核带 eb1251683f ---"
if timeout 300 "$AGDA" +RTS -M"$HEAP" -RTS --guardedness "$MODULE" >"/tmp/kernel_stamp_pos.$$" 2>&1; then
  echo "PASS  $MODULE 编译通过 ⇒ R1 ≡ R2 判为空 ⇒ 内核带 eb1251683f"
else
  echo "FAIL  $MODULE 未通过 ⇒ 内核**不含** eb1251683f"
  echo "      典型报错: UnsolvedConstraints: Is empty: R1 ≡ R2 (stuck)"
  tail -6 "/tmp/kernel_stamp_pos.$$"
  rc=1
fi
rm -f "/tmp/kernel_stamp_pos.$$"

# 负控制（可选）：判据模块在参考内核上必须失败
if [ -n "$REF_AGDA" ]; then
  echo ""
  echo "--- 负控制（预期失败）: 参考内核 $REF_AGDA ---"
  if timeout 300 "$REF_AGDA" +RTS -M"$HEAP" -RTS --guardedness "$MODULE" >"/tmp/kernel_stamp_neg.$$" 2>&1; then
    echo "FAIL  判据在参考内核上也通过 ⇒ 判据失去区分力（版本戳失效）"
    rc=1
  else
    echo "PASS  判据在参考内核上失败 ⇒ 区分力成立"
  fi
  rm -f "/tmp/kernel_stamp_neg.$$"
fi

echo ""
if [ "$rc" -eq 0 ]; then
  echo "=== 门禁通过: 工具链版本戳 = 带 eb1251683f ==="
else
  echo "=== 门禁失败: 内核被换过（或判据失效）==="
fi
exit "$rc"
