#!/usr/bin/env bash
# 提交前重复符号检测（2026-10-21，防「重复实现」类事故）
#
# ## 为什么存在
#
# 本会话实测三次重复实现，根因是「bash grep 只查局部文件」+「检索方言闸失效」：
#   1. `DCPresentation.agda`（119 行）—— 未发现 `Presentation.agda:131` 已有 `dc-presentation`
#   2. `dc-oblivion-trit/-phase/-joint` —— 未发现 `ZeroOblivion`（DuodecClock.agda:504）已有
#   3. 「全库第一个 Presentation」声明 —— 未查
#
# 本脚本是**验收层兜底**：提交前检查「新增的顶层签名」是否已在库内**其他模块**定义。
# 它**不依赖 hook 框架**（PreToolUse 闸门 2026-10-21 实测 106 次全放行 ✗）。
#
# ## 用法
#
#   bash engineering/check_duplicate.sh            # 检查 staged（pre-commit 用）
#   bash engineering/check_duplicate.sh --all      # 检查 HEAD vs HEAD~1
#   bash engineering/check_duplicate.sh --warn     # 只报告不失败（调试用）
#
# ## 退出码
#
#   0 = 通过 / 无可检项；1 = 发现重复符号；2 = 用法错误
#
# ## 边界（诚实声明）
#
#   · 只查**顶层签名**（行首 `name :`），不查 record 字段 / where 块 / 局部定义 ✗
#   · 白名单排除通用名（assoc/comm/unit/...）—— 它们跨模块重名是合法的 ✓
#   · 可用 `git commit --no-verify` 绕过 ✓ —— 但那样做的提交应在 journal 说明理由
#   · **同模块内**的定义不算重复（允许同文件更新）✓

set -uo pipefail
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
cd "$ROOT" || exit 2

MODE="staged"
for a in "$@"; do
  case "$a" in
    --all)  MODE="head" ;;
    --warn) WARN_ONLY=1 ;;
    *) echo "未知参数: $a" >&2; exit 2 ;;
  esac
done
WARN_ONLY="${WARN_ONLY:-0}"

# ── 白名单：通用名，跨模块重名合法 ──
IGNORE_RE='^(assoc|comm|refl|cong|id|zero|suc|unit|check|field|where|module|open|import|record|data|postulate|private|abstract|infix|infixl|infixr|eq|sym|trans|subst|map|foldr|iterate|proj₁|proj₂|carrier|step|phase|clock|rigidity)$'

# ── 取 diff ──
case "$MODE" in
  staged) DIFF="$(git diff --cached --diff-filter=AM -U0 2>/dev/null || true)"
          CHANGED="$(git diff --cached --name-only --diff-filter=AM 2>/dev/null | grep '\.agda$' || true)" ;;
  head)   DIFF="$(git diff HEAD~1 HEAD --diff-filter=AM -U0 2>/dev/null || true)"
          CHANGED="$(git diff HEAD~1 HEAD --name-only --diff-filter=AM 2>/dev/null | grep '\.agda$' || true)" ;;
esac

if [ -z "$DIFF" ]; then
  echo "✅ check_duplicate: 无 $MODE 变更（或不是 git 仓库）"
  exit 0
fi

# ── 提取新增的顶层签名（跳过注释行）──
SYMS="$(printf '%s\n' "$DIFF" \
  | grep '^+' \
  | sed 's/^+//' \
  | grep -vE '^[[:space:]]*--' \
  | grep -vE '^[[:space:]]*$' \
  | grep -oE '^[^[:space:]]+[[:space:]]*:' \
  | sed 's/[[:space:]]*:$//' \
  | sort -u)"

if [ -z "$SYMS" ]; then
  echo "✅ check_duplicate: 无新增顶层签名"
  exit 0
fi

FAIL=0
COUNT=0
while IFS= read -r sym; do
  [ -z "$sym" ] && continue
  # 跳过白名单 / 非标识符
  printf '%s\n' "$sym" | grep -qE "$IGNORE_RE" && continue
  printf '%s\n' "$sym" | grep -qE '^(module|open|import|data|record|where|postulate|private|abstract|infix)' && continue

  # 在库内查同名**定义**（行首同名 + 冒号），排除本次改动的文件
  if [ -n "$CHANGED" ]; then
    HIT="$(grep -rnE "^${sym}[[:space:]]*:" src/Sovereign --include=*.agda 2>/dev/null \
           | grep -vF -f <(printf '%s\n' "$CHANGED") || true)"
  else
    HIT="$(grep -rnE "^${sym}[[:space:]]*:" src/Sovereign --include=*.agda 2>/dev/null || true)"
  fi

  if [ -n "$HIT" ]; then
    COUNT=$((COUNT+1))
    echo "❌ 重复符号: $sym"
    printf '%s\n' "$HIT" | head -3 | sed 's/^/    已存在: /'
    FAIL=1
  fi
done <<< "$SYMS"

if [ "$FAIL" -eq 1 ]; then
  echo
  echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
  echo "🛑 check_duplicate: 发现 $COUNT 个重复符号（已在库内其他模块定义）"
  echo "   处置：复用已有定义（open import / 引用），或改名，或说明为何确需新建"
  echo "   绕过：git commit --no-verify（须在 proof_dag journal 说明理由）"
  echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
  [ "$WARN_ONLY" = "1" ] && { echo "（--warn 模式：不阻断）"; exit 0; }
  exit 1
fi

echo "✅ check_duplicate: 通过（$(( $(printf '%s\n' "$SYMS" | wc -l) )) 个新增签名，无重复）"
exit 0
