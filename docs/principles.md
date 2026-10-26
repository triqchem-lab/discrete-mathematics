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

## 四、目录架构：现行 vs 候选（✅ 已裁决 2026-10-14）

- **现行（已裁决，权威）**：**纯名六层** —— `Foundation / Base / Algebra / Synthesis / Application / Infrastructure`（依赖单向 `Foundation → Base → Algebra → Synthesis → Application`，`Infrastructure` 横切）。**2026-10-14 人类裁决：追认「纯名六层」为裁决结果**（与已执行实况一致，零返工）；`F00/B10` 编号形式**不采纳**。
- **已执行实况（2026-10-14）**：移动面 **474 / 474 件全迁**、断链 0；非六层目录**已全部清空**（26 个源目录 + 顶层）；`layer-map.csv` 803 模块行 = 留驻件 309 + `_archive` 冻结 20 + 跨目录件 474。机读台账见 `docs/migration/progress.yaml`。
- **历史注**（不改史）：本条原记「候选（2026-10-11 审查报告提案）：`00-foundation / 10-base / …` 五层编号架构；状态：候选、未裁决」——该候选**未被采纳**，实际执行采用纯名六层。
- **A 类非层残留 9 件 —— 已处置（2026-10-14 人类裁决：按「拓扑侧链」定层）**：`Topology/Graphs/*` 8 件（GraphBasic/Connectivity/Trees/Matchings/Colorings/Flows/Cycles/RamseyFinite）→ **`Synthesis/Graphs/`**；`Arithmetic/LinearRecurrence.agda` → **`Algebra/`**。它们不属 `layer-map.csv` 803 行基线（故不计入 471/474 口径），而是 `docs/离散数学基础-缺面模块清单-2026-10-11.md` §二/§四的缺面新建研究件、`docs/plan/D1D3-watershed-general-dodziuk.md:36`「Graphs 面 8 件」的分水岭（Dodziuk）课题承载件。迁移实况：**零涟漪残留**、V1 **9/9 EXIT=0**。

## 五、命名与示例的本地校准（防漂移）

- **List vs 函数**：按 `数学严谨性路线选择-2026-10-10.md` **§⑤ 修订**——两路线**共存互补**（构造主义 vs 定义严格性两维度），函数表示是**呈现选择**而非「唯一基础设施」，List 族在 `src/Sovereign/Algebra/`（不是 `_archive/`，更不是「投影」）。文档示例与此冲突时以裁决为准。

## 六、数学优先纪律（2026-10-27 人类裁定）

**定位**：项目主体是**数学证明**，不是数值拟合。优先级 **① 数学证明 ② 严格性 ③ 强类型化**；工程便利排在其后。

### 6.1 禁止（红线）

- **用数值验证替代数学证明**：数值一致 ≠ 命题成立；有界实例（n=1..100）不证明含 `∀` 的命题。
- **用训练/拟合替代形式化**：神经网络拟合测量数据不是"验证模型"，只是"拟合参数"。
- **用"先跑通"替代"先证命题"**：Python/oracle 只允许用于**发现反例**，不允许充当结论。
- **类型不安全的表示**：用 `Int`/裸整数冒充 `Fin`/`BaseKey`；用静默默认值（`→ 0`、`→ eisZero`）吞掉不可达分支。
- **把 `refl` 暴力求值当证明**（`chern2Proof = refl` 类），以及**把 C 级报 A 级**。

### 6.2 允许（有明确边界）

- **oracle / Python / 数值探针**：仅用于「先算后证」中的**发现阶段**——找反例、定常数、选生成元；结论仍须回到内核证明。
- **工程工具**（张量网络、神经网络、物理模型）：作为**待形式化的对象**是合法的；作为**计算工具替代证明**不合法。
- **扩环/改基座**：只有在「数学上必要」时做（如酉 Schur 常数需 `√6`）；若存在基座内的正确表述（如 quaternionic 型的**双线性** Schur），则**不得**以"工程方便"为由扩环。

### 6.3 必须

- 每个数学命题：**内核回执 + 0 postulate + 0 hole**，且 A/B/C 分级与实际证据一致。
- 每个类型：强类型化到「非法值不可表达」（`Fin`、`BaseKey`、封闭构造子）；不可达分支一律 `constitutionalPanic`，**不许静默返回默认值**。
- 每个「工程工具」：在文档与提交信息里**明确标注"这是工具，不是证明"**。

### 6.4 判例（本纪律的来源）

- **2026-10-26**：`spinorValue` 按元素阶读数被判为"值对、理由不对"⇒ 改为由 `Z[ω]` 显式矩阵的**迹**导出（`Complex2A4`），`spinorValue` 降为推论。
- **2026-10-27**：Hermite 型 Schur 关系在非酉实现下**不成立**（`U†U ≠ I`）；酉化需 `√6`（`det H = 864`）。查 FS 指标 `Σχ(g²) = −24 ⇒ −1` ⇒ **quaternionic** ⇒ 正确表述是**双线性** Schur（`Σρᵢⱼρₖₗ = 12·εᵢₖεⱼₗ`），**在 `Z[ω]` 内精确成立**。⇒ **不扩环**；理由是数学，不是省事。
- **2026-10-27**：`Complex2A4` / `Carrier2A4` 中的静默默认值（`→ eisZero` / `→ eisOne` / `orderOfM → 0`）全部改为 `constitutionalPanic`——默认值会让错值伪装成正确。
