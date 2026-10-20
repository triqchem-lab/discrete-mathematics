#!/usr/bin/env bash
# 重新生成跨语言对账用 dump（sov-math 的 dump_tables 输出）
#
# 产物落到 **仓库内** engineering/artifacts/sovdump.csv（已 gitignore，不入库）。
# 用途：engineering/crosscheck_spec_anchor.py 的输入。
#
# 前置：sov-math 已构建（cargo build --bin dump_tables）。
# 用法：bash engineering/gen_sovdump.sh
set -euo pipefail
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
DUMP_BIN="${SOV_DUMP_BIN:-/home/yanli/work/math/rust/sov-math/target/debug/dump_tables}"
OUT="${1:-$ROOT/engineering/artifacts/sovdump.csv}"
if [ ! -x "$DUMP_BIN" ]; then
  echo "找不到 dump 二进制：$DUMP_BIN" >&2
  echo "先构建： (cd /home/yanli/work/math/rust/sov-math && cargo build --bin dump_tables)" >&2
  exit 2
fi
mkdir -p "$(dirname "$OUT")"
"$DUMP_BIN" > "$OUT"
echo "已生成 $OUT"
echo "行数: $(wc -l < "$OUT")"
echo "对账节: $(grep -cE '^(GF3ADD|GF3MUL|DCCRT|GF9MUL|DCSIGMA|DCMIX),' "$OUT" || true)"
