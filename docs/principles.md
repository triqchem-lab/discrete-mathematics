# 大衍证明原则与策略索引（docs/principles.md）

> 人类可读的**证明策略索引 + 可追溯三层账本**入口。机器权威账本 = `proof_dag` 台账（`~/.dsh/state/math-proof/`）；
> 本文件与 `docs/ledger/` 是**人类镜像**。方法论细则见技能 `proof-engineer`（SKILL.md + `references/` 三册）。
> 口径出处：`docs/声称边界精确审计-vFinal.md`（声称边界方法论）、`docs/maps/M9-quality-audit.md`（判型债/诚实边界）、`docs/decisions/数学严谨性路线选择-2026-10-10.md`（含 §⑤ 修订：List/函数两路线共存）。

## 一、证明策略索引（阻塞时按优先级下移：E > B > A > C > D）

| 策略 | 适用场景 | 技能位置 | 库内实例 |
|---|---|---|---|
| **E 未来态锁定 / CRT 正交分解**（首选） | Z/12Z 操作、有明确推导目标 | SKILL.md L2 + `proof-patterns.md` 附录 7 | makeTau 锚点、sum12 = sum3∘sum4 |
| **B 代数链**（命名引理 `∙`/`trans` 链，每项 ≤3） | 数论/域公理/卷积/重排 | L2 + 附录 14（rearrange） | `sum-ℤ-swap`、`rearrange9`、`t3-kill` |
| **A 穷举**（≤27 全用；27–81 需注释论证；>81 必符号化） | 有限论域 + 构造子穷尽 | L2 + 附录 11 | `⊕-comm` 9-case、`frobenius-is-cube` 半线性 |
| **C 否定**（`¬` + `λ ()`） | 构造子不匹配、反证件 | L2 | `tneg-goal-false`、`noReduction` |
| **D Postulate 三门槛**（最后手段） | 内核资源爆炸/编译器限制 | L0 + `compile-traps.md` 附录 1 | `div3k`/`mod3k`（8 条真 REWRITE） |
| **抽象化泛型引理**（爆点规避） | 「字面头+stuck 尾」比较 | 附录 15 B1 | `t3-kill`（M 抽象化 + 调用点字面实例化） |
| **半线性/线性基展开** | 有限域映射相等 | 附录 10/11 | `semilinear-ext3`、`linear-extN` |
| **单向注入 + 鸽巢** | 有限动力学轨道周期 | 附录 13 | `orbit-eventually-periodic-fin` |

## 二、可追溯性：三层账本

1. **命题层**：`docs/ledger/*.yaml`（人类镜像）↔ `proof_dag` 节点（机器权威，**id 同名对齐**）。
   每个顶层定理一条目：`statement / level / evidence / dependencies / proof_strategy / human_notes / git_witness`。
   **冲突时以 proof_dag 为准**（回执哈希绑定源码，改文件即失效）。
2. **策略层**：证明体注释标注 `-- 策略：… ｜ 来源：…`（人类友好化六条之三）。
3. **证据层**：`proves`（内核回执）＞ `weak`（oracle points≥domain / .agdai / 静态审计）＞ `unverified`（模型自报 = 未验证）。
   **A/B/C 内容分级以 proof_dag 内容闸门 + 人工四问验收为准**；
   `engineering/audit_content_grades.sh` 只是**静态初筛**（B/C 启发式），无回执一律不判 A。

## 三、人类友好化六条（详见 SKILL.md L3 节）

① 模块头数学背景优先 ② 命名反映数学内容（禁缩写/漂移）③ 每步证明数学注释 ④ where 有序无前向引用 ⑤ 条件符号分组 ⑥ 复杂证明结构可视化（ASCII 阶段图）。

## 四、目录架构：现行 vs 候选（⚠ 候选未裁决）

- **现行**（权威：AGENTS.md Architecture）：`RootMath → Base → Algebra → Arithmetic → Format → Structology → Constitution → Coupling → Density`（+ HoTT/Topology/Physics 侧链），模块独立编译。
- **候选**（2026-10-11 审查报告提案）：`00-foundation / 10-base / 20-algebra / 30-synthesis / 40-application / 90-infrastructure` 五层编号架构（依赖 `00 → 10 → 20 → 30 → 40` 单向）。
- **状态：候选、未裁决**——涉及 512 文件全量迁移 + 全量重编 + AGENTS.md/门禁脚本/台账 module 字段同步，须人类排期裁决后执行。**在此之前一切引用以现行架构为准。**

## 五、命名与示例的本地校准（防漂移）

- **List vs 函数**：按 `数学严谨性路线选择-2026-10-10.md` **§⑤ 修订**——两路线**共存互补**（构造主义 vs 定义严格性两维度），函数表示是**呈现选择**而非「唯一基础设施」，List 族在 `src/Sovereign/Algebra/`（不是 `_archive/`，更不是「投影」）。文档示例与此冲突时以裁决为准。
