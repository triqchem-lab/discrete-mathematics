# A1c/π₂ᵈ 分水岭耦合状态表（2026-10-14 裁定修正面）

> 接续：`A1-pi-n-paths-abcd-research.md`（四路径报告）→ 进度报告两轮 → PIO 核勘轮（journal lesson #1127）→ 本轮三件收口（回执 `cb9240fe` / `8e9c0119` / `dd283822`）。
> 性质：**状态表文档**（阶段性快照），非证明——所有「已证」以回执为准，无回执一律标未证。

---

## 一、PIO 三判据（源码核勘修正后定形）

| # | 判据 | 陈述 | 状态 | 证据面 |
|---|---|---|---|---|
| **PIO-1** | 实例反例 | `∃G. π₁ᵈ(G) ≇ π₁(|N₁G|)`；实例 Gcmp：π₁ᵈ = 2 元幂等幺半群（**A 级**：`_PPI4f` loop-squash + `_PPI4e` gcmp-classify 恰两类 + `selfloop-quot-≠`）vs π₁(|N₁Gcmp|)=0（**外部事实** Barcelo-CK，库零命中） | **active（已入册 `PIO-1.card-divergence`）** | 库侧：分水岭 A 级回执；外部侧：待 `|N₁|` 旗复形构造件（(N1) 件在飞）→ Agda 化 |
| **PIO-2** | 关系分化（修正后真形） | AHomotopy 与 Barcelo A-同伦**对象层不同物**（走 vs 网格同态）；结构性分化点 = **AStep 两沿恒正长（`_PPI2:277` Q-AStep）⇒ 无回溯消去 ⇒ nil 类永不可及** | **库内已证面**（`selfloop-≁nil`/`_PPI4b:66`；`inv-law-false`/`_PPI2:301`） | ~~slide 论据~~ 作废（journal #1127：slide = 填充三角形直连捷径，连续同伦同样有） |
| **PIO-3** | 分水岭内在性 | 分水岭为 π₁ᵈ 内在性质（幂等幺半群在 AStep 关系下自洽，无需"经典呈现"排除） | **直接成立于分水岭 A 级** | `_PPI4f` 分水岭定稿 |

**内核注**：A1 报告（`A1-pi-n-ontology-research.md:106`）已立「πₙᵈ 本体论独立性 + 对应定理=桥非定义」立场——PIO 分析是**升级步**（印证+实例数据），**不是推翻**。44 行「经 McCord/M3 邻域=经典拷贝」指投影侧。

---

## 二、A1c 独立部分（E–H 弱形式）五件状态

| 件 | 陈述 | 状态 | 载体 |
|---|---|---|---|
| (e1) `∗₂` 商良定义（泛基） | `Ω3Walk (cons2 s (cons2 s̄ c)) c`（whisk 右延拓） | **引理级未证——主瓶颈** | 在飞：子代理 (c3) `src/_PEH4.agda`（商层 SetQuotients 路线；原族路线撞 K 死墙 #58） |
| (e2) `AStep-++w-comm` | 局部生成元 × 底走拼接交换 | **可达**（端点闭合自动；AStep 局部性=构造子展开） | 待 _
批注：e2 属引理级但形状简单 |
| (e3) Interchange law | 2×2 网格两种遍历同果 | 由 (e2) 导出（未开工） | — |
| (e4) 交换性 | 经典 E–H 推导（不用逆） | 条件成立（待 e3） | — |
| (e5) 幂等性 | π₁ᵈ 幂等逐层传导 | 结构确定（未单独证） | — |

---

## 三、π₂ᵈ(Gcmp) 基点分歧（已定型部分）

| 侧 | 陈述 | 状态 |
|---|---|---|
| **nil 侧（已定型）** | `π₂ᵈ(Gcmp, nil)` 载体平凡 | **A 级 proven**：`PEH0.nil-iso`（回执 `cb9240fe`）+ `c2.gcmp-selfloop-neighborhood`（回执 `8e9c0119`）的**通用否定面** `no-chain-into-nil : Pos (len w) → Ω2Walk G x w (nil x) → ⊥`（任意图） |
| **selfloop 侧（进行中）** | `π₂ᵈ(Gcmp, selfloop-walk)` 非平凡候选（whisk 邻区） | c2 邻域件已收：`selfloop 非孤立`（witness `selfloop-slide = slide nil nil e01 e10 loop-e`——反身自环源码确证）；类数列举待 (c3) 装配链 |
| **D1 verdict** | A1c↔A2 耦合裁决 | **未判**——两件前置：(c1) nil 侧 ✅、(c2) 邻域 ✅、(c3) 泛基同伦件在飞 |
| **A2 接口 (c6)** | add2⁺ 逆律 | = A2 域反射分层覆盖问题（未开） |

---

## 四、工具债登记（K 死墙——prover_limits #58）

- **`cubical-refl-eq-nil2-match`**（blocker，已入册）：同变元双索引构造子（`nil2 : ∀ w → Ω2Walk G x w w`）匹配 ⇒ 残余自反式需 K ⟹ `--cubical` 死墙；cons2 形（三独立索引）不受影响。
- **人类裁决 2026-10-14**：dype 内核补丁路线**作废**（dype=废弃项目/噪声）；执行路线 = **手写 Ω2Walk eliminator + PathP**（运件 = `congD-nil2`，`src/_PEH2.agda`）——在飞：子代理 `src/_PEH3.agda`（候选 A eliminator / B Σ-呈现桥 / C SetQuotients 商层 / D 死墙复现件）。
- 运件面（A 级 proven，回执 `dd283822`）：`congD-nil2 : (we : w ≡ w') → PathP (λ i → Ω2Walk G x (we i) (we i)) (nil2 w) (nil2 w')`；条件件 `Ω2-nil-singletonH`（零洞承载，非无条件）。

---

## 五、施工件索引（活清单）

| 代号 | 载体 | 状态 | 回执 |
|---|---|---|---|
| (c1)/PEH0 | nil-iso + pos-if-step（AStep 孤立点通用件） | **proven A 级** | `cb9240feda31bb5dc…` |
| (c2)/PEH1 | Gcmp selfloop 邻域枚举 + no-chain-into-nil 通用否定面 | **proven A 级（对象）** | `8e9c0119fd62e2d6…` |
| (f)/PEH2 | congD-nil2（依值版 cong 运件）+ 条件件 singletonH + 死墙注释实录 | **proven A 级**（f-a/f-c）｜f-b BLOCKED 立界 | `dd283822b68b886b…` |
| (N1)/PN1 | 旗复形/1-神经构造件（PIO-1 Agda 化前置） | **子代理在飞** | — |
| 路线B/PEH3 | eliminator+PathP 四候选逃逸 | **子代理在飞** | — |
| (c3)/PEH4 | 泛基 fill-tri-gen / Ω3Walk-suffix（含商层路线） | **子代理在飞** | — |

**明证边界**：本文档不含任何无回执的「已证」声明；三强化判定（PIO-*）与 D1 verdict 均为**研判定级**，最终以 Agda 商面收口为准。
