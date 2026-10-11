# docs/plan —— 计划存档与追踪索引（2026-10-11 立）

> 目的：计划与核实状态同文档落盘，供后期追踪与核实。每份计划 = ①文件名申明 ②计划正文
> ③核实状态（对账表 + 回执）④与台账节点的映射。追踪方法：`proof_dag search <节点id>` +
> 文档内「核实状态」节 + `proof_compile` 回执对源码哈希核对。

## 计划清单

| 文件名 | 计划 | 状态 | 台账映射 | 回执 |
|---|---|---|---|---|
| `line1-N≡MM-bridge.md` | 线1 N≡MM Bridge（unique-root₃-same q≥2 分支闭合） | ✅ **已完成并核实**（2026-10-11） | `P3.2-hensel-uniqueness-pure` / `P3.2-hensel-uniqueness-qge2` | `7bad59be` / `efc5efdd` |
| `line2-norm-unique-dropZ.md` | 线2 norm-unique 修正版（dropZ B 主 + NoZero A 辅） | 🔄 批2 施工中 | `Laurent.norm-unique` | 待收 |
| （线3） | 串行模式未启动（线1 计划明文「本批只做线1」） | ⏸ 未展开 | — | — |

## 追踪约定
1. 计划变更不改史——修订追加「修订记录」节（同 journal 只增不改）；
2. 核实状态的「完成」判据 = proof_compile EXIT=0 回执 + 台账节点 proven（A/B/C 内容闸门过）；
3. 计划与台账冲突时**以台账为准**（机器权威），计划文档记录设计意图。
