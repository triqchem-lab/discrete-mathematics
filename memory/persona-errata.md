# persona/快照勘误（以源码实测为准）

> persona（系统提示）是快照，与库现状冲突时**以源码+台账为准**。逐条勘误：

| 快照断言 | 实况（源码证据） | 状态 |
|---|---|---|
| 「本库无通用 Lagrange / Sylow / 同构定理」 | **通用 Lagrange 已有**：`GroupTheory/Lagrange.agda`（|G|=|H|×[G:H] 构造性，头部自述补缺口）；`B.OrbitStabilizer.general` 通用轨道稳定子亦在；Sylow/同构定理仍缺 ✓ | 半过时 |
| 「个别模块含 hole（HighDimClosure、_rt）」 | `{!…!}` 式 3 文件 + `?` 式需判别（Doz/Closure 为 `<?` 运算符误报；FermatL2/4、DigitalRoot 待判） | 待判 |
| 「群论链 8 模块 0 postulate」 | ✓ 仍真（链门禁实测） | 有效 |
| 「全库 512 个 .agda」（AGENTS.md） | 591（2026-09-27） | 过时 |
| 「重构 329 模块/73k 行」（重构报告） | 591/132,494；已更正入报告 | 已修 |

维护规则：每次质量审计批次收口时复核本表。
