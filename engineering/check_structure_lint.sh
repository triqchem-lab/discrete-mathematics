#!/usr/bin/env bash
# 结构 lint 门禁：把 engineering/lint_agda_structure.py 纳入闸门。
#
# 为什么需要它：check_all_modules_parallel.sh:27 只扫 `src/Sovereign`，于是
# src/{01-electric-12d,02-magnetic-24d,03-neutral-144d} 这些目录里的草稿
# **从未被编译、也从未进门禁**（2026-09-13 实测；已归档到 archive/civlayers-2026-07/）。
# 本闸门只做**静态**检查（不编译），把「压根编不了的库内文件」在提交前暴露出来：
#   · module 声明名 ≠ 相对 include 根的路径（含目录分量带 `-` 的情形）
#   · 标识符 `_` 后接字面量（Agda 实测报 “the part 5 is not valid because it is a literal”）
#   · `where` 挂在 postulate/data/record/类型签名上（Agda 只允许函数子句带 where）
#   · `?` 洞（WARN，不拦门）
#
# 用法：engineering/check_structure_lint.sh [ROOT]   # 默认 ROOT=src
# 退出码：0 = 无 ERROR；1 = 有 ERROR；2 = 用法错误
set -uo pipefail
cd "$(dirname "$0")/.." || exit 2

ROOT="${1:-src}"
LINT="engineering/lint_agda_structure.py"

if [ ! -f "$LINT" ]; then
  echo "找不到 $LINT（工作目录 $(pwd) 是否正确？）" >&2
  exit 2
fi

echo "=== 结构 lint 门禁（root=$ROOT，不编译） ==="
python3 "$LINT" --root "$ROOT"
rc=$?

if [ "$rc" -ne 0 ]; then
  echo "❌ 结构 lint 失败（root=$ROOT）：存在 module 名≠路径 / 非法目录分量 / 非法标识符 / where 滥用。"
  echo "   修法：路径与 module 名对齐；where 只留给函数子句（其它声明把内部声明提到顶层）。"
  exit 1
fi
echo "✅ 结构 lint 通过（root=$ROOT 无 ERROR；? 洞仅警告）"
exit 0
