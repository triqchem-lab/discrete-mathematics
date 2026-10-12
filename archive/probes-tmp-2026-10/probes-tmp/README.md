# /data/tmp 探针与工具归档

本目录存放 /data/tmp 中的探针（Agda）、工具脚本（Python/Shell）——
用于 rearrange 方法论与 sum3-comm/rearrange9 迭代过程的产物，保留供后期排查。

## Agda 探针（16 个）

| 文件 | 用途 |
|------|------|
| ProbeA–ProbeJ, Probe9, ProbeAssoc | rearrange/bubble 逐步迭代探针 |
| BubbleLemmas.agda / bubble_lemmas.agda | bubble 交换链引理迭代 |
| comm_lines.agda | 交换律推导线 |
| f3_base.agda / fin3_final.agda | Fin3 sum3-comm 最终版 |

## Python 工具（12 个）

| 文件 | 用途 |
|------|------|
| burau_oracle.py | Burau 表示 oracle |
| gen_sum3.py / gen_swaps.py | 交换序列生成器 |
| f3_append.py / f3final.py | Fin3 证明生成 |
| ff-matrix.py / ff-bidi.py / ff-plan.py / ff-smoke.py / ff-shoot.sh | ff 系列 |
| verify_chain.py | 链验证 |
| zomega_ring_oracle.py | Z[ω] 环 oracle |
| fixv.py | 版本修复工具 |

## 来源

- 复制自 /data/tmp（28G 临时目录，含大量 Chrome 临时文件——不归档）
- 归档日期：2026-10-10
- 对应方法论：memory/rearrange-methodology.md + proof-engineer 附录 14
