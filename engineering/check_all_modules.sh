#!/usr/bin/env bash
# 全库模块独立编译验证 (去聚合化后的健康检查) — 串行版
#
# 适用场景: 资源受限 CI (如 GitHub Actions 2 核 / 8GB) — 串行编译内存峰值低
#   (单进程 ≤ HEAP), 无 .agdai 并发写竞争, 行为可预测.
#   多核本地机全量验证请用 check_all_modules_parallel.sh (快 ~10 倍).
#
# 用法:
#   ./engineering/check_all_modules.sh                    # 默认堆上限 4G
#   HEAP=6G ./engineering/check_all_modules.sh            # 调堆上限 (≤ 容器内存)
#   AGDA=agda ./engineering/check_all_modules.sh
#
# 退出码: 0 = 全绿; 1 = 有失败
set -u
cd "$(dirname "$0")/.."
AGDA="${AGDA:-$HOME/.local/bin/agda}"
HEAP="${HEAP:-4G}"          # 每进程堆上限; CI 8GB 容器用 4G 安全
SRC="src/Sovereign"
pass=0
fail=0
fail_list=""
mapfile -t files < <(find "$SRC" -name "*.agda" | sort)
total=${#files[@]}
for f in "${files[@]}"; do
  if timeout 300 $AGDA +RTS -M"$HEAP" -RTS --guardedness "$f" >/dev/null 2>&1; then
    pass=$((pass+1))
  else
    fail=$((fail+1))
    fail_list="$fail_list $f"
  fi
  # 进度
  done_count=$((pass+fail))
  if [ $((done_count % 50)) -eq 0 ]; then
    echo "进度: $done_count/$total"
  fi
done
echo "=== 全库独立编译: $pass 通过 / $fail 失败 / 共 $total ==="
if [ -n "$fail_list" ]; then
  echo "--- 失败模块 ---"
  for f in $fail_list; do echo "$f"; done
  exit 1
fi
exit 0
