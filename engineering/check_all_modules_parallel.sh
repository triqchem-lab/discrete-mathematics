#!/usr/bin/env bash
# 全库模块并行独立编译验证 (去聚合化后的健康检查 — 并行版)
#
# 适用场景: 本地开发机/CI 多核环境快速全量验证.
#   对比 check_all_modules.sh (串行版): 本脚本用 xargs -P 并行编译,
#   36 核机器上 510 模块约 4 分钟 (串行需 30-40 分钟).
#
# ⚠️ 资源受限环境 (如 GitHub Actions 2 核 / 8GB) 请用串行版 check_all_modules.sh
#    — 并行版每进程 +RTS -M6G, 2 并发即需 ~12G 峰值, 不适合 8GB 容器.
#
# 用法:
#   ./engineering/check_all_modules_parallel.sh          # 默认并发 12
#   ./engineering/check_all_modules_parallel.sh 24       # 指定并发数
#   AGDA=agda ./engineering/check_all_modules_parallel.sh
#   HEAP=4G ./engineering/check_all_modules_parallel.sh  # 调低单进程堆上限
#
# 并发数建议: ≤ 物理核数, 且 并发数 × 堆上限 ≤ 可用内存 (每进程 +RTS -M6G,
# 峰值通常 <1G, 故 12 并发在 16G+ 机器安全; 61G 机器可到 24-32).
#
# 退出码: 0 = 全绿; 1 = 有失败

set -u
cd "$(dirname "$0")/.."
AGDA="${AGDA:-$HOME/.local/bin/agda}"
JOBS="${1:-12}"
HEAP="${HEAP:-6G}"          # 每进程堆上限 (+RTS -M), 防 REWRITE 无界展开吃满内存
SRC="src/Sovereign"
WORK="$(mktemp -d /tmp/check_all_par.XXXXXX)"
trap 'rm -rf "$WORK"' EXIT

echo "=== 全库并行独立编译 (并发 $JOBS, 堆上限 $HEAP) ==="
echo "agda: $AGDA"
echo ""

# 并行编译: 每个模块结果写独立文件 (md5 命名, 避免并发写冲突)
# AGDA/HEAP/WORK 经环境变量传入; xargs -I{} 把模块路径替换到 bash -c 的 $1
# (bash -c 后第一个参数是 $0=_, 第二个才是 $1)
export PAR_AGDA="$AGDA" PAR_HEAP="$HEAP" PAR_WORK="$WORK"
find "$SRC" -name "*.agda" | sort \
  | xargs -P "$JOBS" -I{} bash -c '
      f="$1"; agda="$PAR_AGDA"; heap="$PAR_HEAP"; work="$PAR_WORK"
      out="$work/$(printf "%s" "$f" | md5sum | cut -d" " -f1).result"
      if timeout 300 "$agda" +RTS -M"$heap" -RTS --guardedness "$f" >/dev/null 2>&1; then
        echo "PASS $f" > "$out"
      else
        echo "FAIL $f" > "$out"
      fi
    ' _ {}

# 汇总
pass=0; fail=0; fail_list=""
for r in "$WORK"/*.result; do
  if grep -q "^PASS" "$r"; then
    pass=$((pass+1))
  else
    fail=$((fail+1))
    fail_list="$fail_list $(sed 's/^FAIL //' "$r")"
  fi
done
total=$((pass+fail))

echo "=== 全库独立编译: $pass 通过 / $fail 失败 / 共 $total ==="
if [ "$fail" -gt 0 ]; then
  echo "--- 失败模块 ---"
  for f in $fail_list; do echo "$f"; done
  exit 1
fi
exit 0
