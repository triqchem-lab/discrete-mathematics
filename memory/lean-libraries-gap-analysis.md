# 两大 Lean 证明库对照：我们还没解决的理论（2026-09-09）

> 数据源：本地 `fermats-last-theorem`（60,475 模块 / 29,511 定理）、
> `NavierStokesAndEuler`（2,486 文件）、mathlib4 `docs/1000.yaml`（1,199 条，已形式化 244 / 未形式化 955）。
> 本文件只记录**可核对的清单与判据**，不记录立场。

## 1. 两个库各自证明了什么、明确没证什么

### 1.1 FLT（`/data/work/leanprover/fermats-last-theorem`）

**规模复核（子代理实测）**：60,478 个 `.lean` 文件 / **13,499,380 行**；`Theorems/` 29,511（仅陈述）
+ `P2M/Sol/` 29,513（证明）+ `Definitions/` 1,450。单 commit `aa2d8b34`，**本机未构建**
（无 `.lake`/`.olean`，`lake build` 需联网拉 mathlib，约 5.5 小时 / 153 GB 内存）。

**公理审计（独立 grep）**：`axiom`/`postulate`/`native_decide`/`unsafe`/`extern`/`implemented_by`/
`partial def`/`#eval` 全部 **0 匹配**；`sorry` 仅 3 处，全在包外的
`verification/comparator/Challenge.lean`（comparator 协议设计如此）。主定理路径 **0 sorry**。
`p2m_exact_reverting` 宏（`P2M/Util.lean:4-16`）= 带上下文回退的 `exact`，不绕过内核。

**⚠ 库自己承认的缺口（`README.md:99-102` 原文）**：
> "The Lean sources were produced by AI agents ... written to be checked rather than read:
> **names are machine-generated** ... and **where a name and a statement disagree the statement is what was proved.
> Comments were removed**"

以及 `README.md:52-54`：
> "**What no tool can check is that each intermediate theorem means what its name suggests**;
> that is for the reader to judge"

`formalization.yaml:107`：`review.status: self-assessed`，`reviewers: []`（无外部评审人）。
`ATTRIBUTION.md`：**106 个文件**取自 Imperial College FLT / flt-regular（54 在 `Definitions/`、52 在 `P2M/Sol/`）。

→ 这是「**信息截断**」在证明库层面的实例：内核检查通过 ≠ 语义可读。
与本项目「禁止信息截断」的红线同源，但它发生在**命名/注释层**而非代数结构层。

**证了**：`fermat_last_theorem (n : ℕ) (hn : 3 ≤ n) (a b c : ℕ) (0 < a,b,c) : a^n + b^n ≠ c^n`，
公理仅 `[propext, Classical.choice, Quot.sound]`，无 sorry/axiom/native_decide；
comparator + nanoda 双内核复核（`README.md`）。

**明确没证**（`PROOF-PATH.md` 末节「Exact strength of the named steps」原文）：
- 模性提升：只证了 semistable W 在 p=3 与 p∈{3,5} 的**带层条件**版本；无层条件版、非 semistable 曲线、其他 p **未证**
- Wiles：只证「每个 semistable 整 Weierstrass 模型（Δ≠0）在 a_ℓ 匹配意义下模性」；非 semistable 曲线、模参数化、L 函数**未提**
- Langlands–Tunnell：只证 octahedral 情形 + 显式提升；一般 odd 二维可解像表示的自守性**未证**
- Mazur：只证 Frey 曲线 E_P[p] 的不可约性；一般曲线的有理同源/挠**未证**
- Ribet：只证 Frey 表示在平方自由层上的层下降（作为迹同余）；一般模 p 表示**未证**

### 1.2 NSE（`/data/work/leanprover/NavierStokesAndEuler`）

**规模复核（子代理实测）**：2,486 个 `.lean` / **616,276 行** / 约 36,124 条定理声明。
`NavierStokes/` 643（顶层 579 + `R3/` 64）、`Euler/` 1,839、`ComparatorChallenges/` 2。
依赖 303 个 Mathlib 模块；主定理 import 闭包：NS 580 项目模块 / 209 mathlib，Euler 1,829 / 190；
**73 个模块不在任一主定理闭包内**。本机无 v4.34.0-rc2 工具链、无 `.lake/` → **未编译验证**。

**四条主定理（确切签名已抄录）**：

| 定理 | 文件:行 | 空间 | 外力 | 结论 |
|---|---|---|---|---|
| `navier_stokes_breakdown_R3` | `NavierStokes/ComparatorSolution.lean:16` | ℝ³ | **有**（decay） | 爆破 |
| `navier_stokes_breakdown_periodic` | `:23` | ℝ³/ℤ³ | **有**（周期+时间衰减） | 爆破 |
| `euler_breakdown_R3` | `Euler/Solution.lean:33` | ℝ³ | **无** | 爆破 |
| `exists_compact_smooth_euler_singularity` | `Euler/Solution.lean:43` | ℝ³ | **无** | 紧支初值 + C¹ limsup=⊤ + 涡量积分=⊤ |

**⚠ 关键限定（子代理查明）**：NS 定理前提**只有 `ν > 0`**，存在性由**构造**给出
（`u₀ = 0` + 紧时间支撑外力，`ComparatorTheorem.lean:20-21`）。
→ **这不是无外力 Clay 问题**：**外力是核心杠杆**。Euler 侧才是无外力、紧支光滑散度自由初值。

**公理审计**：`axiom`/`admit`/`native_decide` **0**；`sorry` 5 处，全在
`ComparatorChallenges/{NavierStokes,Euler}.lean`（参考陈述占位），**不在主定理 import 闭包内**。
`BlowupImplication.negative_power_tendsto_atTop`（`:24`）是**完整证明项，非 axiom**。

**未覆盖（grep 命中 0 文件）**：Leray–Hopf 弱解、自相似解、涡片（vortex sheet）、Boussinesq、
一般 BKM 定理陈述、全局正则性。→ **为特定构造定制的证明库，不是通用 PDE 理论库**。

**唯一可直接迁移到 Agda 的模块**：`Euler/PacketShiftArithmetic.lean` ——
整文件 **10 条定理**（`grep -c '^theorem'` 实测，2026-09-10），**无 ℝ**，纯 ℕ 线性算术
（`highShift p = 100*p-80` 等）。按证明方式拆：**1 条 `:= rfl`**（`primary_shift : highShift 1 = 20`，
定义自洽）+ **9 条 `omega`**（真正需要算术推理的那 9 条）。
例：`slow_high_high_room (i j p : ℕ) (1≤i) (1≤j) (i+j=p) : highShift i+highShift j+10 ≤ meanForceShift p`。
（口径注记：迁移节点 `A.PacketShift.lean-migration` 的「10 条」= 整文件口径，
Agda 侧 9 条拆 `-core` + 主定理 + 1 条 `primary_shift`；两口径不矛盾。）

## 2. 我们的覆盖度对照（grep 实测，2026-09-09）

| 理论 | 我们库模块数 |
|---|---|
| 模形式 / CuspForm / Hecke | 0 / 0 / 0 |
| 类域论 / 理想类群 | 0 / 0 |
| 模曲线 / Čerednik–Drinfeld / Néron | 0 / 0 / 0 |
| p 进 / Tate | 0 / 1 |
| Galois 表示 / 自守 / 形变 | 1 / 1 / 1 |
| Weierstrass / 椭圆曲线 | 1 / 8 |
| Sobolev / 弱解 / BKM | 0 / 0 / 0 |
| Leray / 爆破 / 能量估计 | 2 / 4 / 1 |
| 涡 / Navier | 33 / 9 |

**结论**：FLT 链的算术几何与 NSE 链的连续统分析，我们**基本没有**。
这不是「还没做」，而是**基座不适用**（本库构造主义、无 Choice、无连续统、无 funExt）。

## 3. 未解决理论清单（按可行性分三档）

数据源：mathlib4 `docs/1000.yaml` 中**无 decl/url** 的 955 条（即社区公认尚未形式化），
经关键词精确筛选后与本库能力交叉。

### 档 A：有限 / 离散 / 构造，本库基座可攻

| 定理 | 类型 | 为什么适合我们 | 已知障碍 |
|---|---|---|---|
| **Burnside p^a q^b 可解性** | 有限群 | 陈述纯有限；我们有 A₄/S₃/有限群实例 | 经典证明用 ℂ 特征标（代数整数）→ 需换无特征标证明或限定特征标域 |
| **Frobenius 互反** | 有限群表示 | 纯有限双线性配对 | 需先把表示论从「数值验证」升级为「结构定义」 |
| **Brauer 诱导特征标定理** | 有限群表示 | 有限生成元 + 整数系数 | 依赖代数整数环 |
| **Jordan–Schur / Schur 定理** | 有限群 | 陈述有限 | 指数界巨大（Jordan 界不可构造） |
| **Dilworth / Menger / König** | 有限组合 | 纯有限极值 | 需有限图/偏序基础设施 |
| **Brooks 定理** | 有限图染色 | 有限 | 需图论基础 |
| **Zsigmondy 定理** | 初等数论 | 有限、可计算 | 需分圆多项式与 Zsigmondy 对 |
| **Sophie Germain 定理（FLT 情形 I）** | 初等数论 | 我们已有 Fermat 链 L0–L4 | 需 p 次幂剩余与 mod p 论证 |
| **Maschke 定理（有限域版）** | 表示论 | 特征不整除群阶时平均法**构造性** | 需「平均映射」形式化 |
| **Ax–Grothendieck（有限集情形）** | 有限代数 | 有限集单射⇒满射，**一行** | 平凡，但可作结构引理 |
| **Poincaré–Birkhoff–Witt（有限维）** | 李代数 | 有限维、组合 | 需李代数基础 |

### 档 B：需换基座 / 需连续统或算术几何

- 完整模性定理（非 semistable）、无层条件的模性提升、一般 odd 二维表示自守性
- Kummer 正则素数 FLT 情形 I/II（需分圆域理想类群）
- Fermat 多边形数定理、Mihăilescu 定理、Thue–Siegel–Roth
- NS 正则性备选 (A)/(B)、BKM 判据、CKN 部分正则性、Leray–Hopf 弱解
- 一切需要 ε-δ / 极限 / 不可数覆盖 / Choice 的条目（1000 表中约 57 条分析类）

### 档 C：明确不做（基座不适用，做了也是投影）

- FLT 链的算术几何（模曲线 7,711 定理、形变理论、p 进 Hodge、局部 Langlands）
- NSE 链的 Sobolev / 测度 / 泛函分析
- Clay 千禧年问题本体（P vs NP / RH / YM 质量间隙 / NS 正则性 / BSD / Hodge）

## 4. 我们自己的缺口（不是「别人没做」，是「我们没做」）

| 缺口 | 现状 | 可攻性 |
|---|---|---|
| 通用 Lagrange / Sylow 定理 | 无（只有 A₄ 具体实例） | 高（有限、构造） |
| 通用 orbit-stabilizer 定理 | 只有 A₄ 具体 + T⁶ 的 Cubical 等价版 | 高 |
| Maschke / 半单表示论 | 无 | 高（有限域平均法） |
| 通用有限域理论（F_{p^n}） | 有 GF(9)/27/81/243/729 实例 | 中（泛化需大量重写） |
| 结构化的群特征标理论 | 有 GL₂(GF(9)) 数值验证 | 中（需升级为结构定义） |
| `funExt` | 无（非 cubical） | 需 `--cubical` 或 postulating |

## 5. 可引用锚点

- `fermats-last-theorem/README.md`（公理清单、双内核复核）
- `fermats-last-theorem/PROOF-PATH.md`（末节「Exact strength」= 未证清单原文）
- `NavierStokesAndEuler/README.md`（Clay 备选 (C)/(D) 定位）
- `NavierStokesAndEuler/formalization.yaml`（formalizes 关系）
- mathlib4 `docs/1000.yaml`（1,199 条形式化状态，244 已 / 955 未）
- 网页：[OpenAI NSE README](https://github.com/openai/NavierStokesAndEuler)、
  [mathlib4 1000.yaml](https://github.com/leanprover-community/mathlib4/blob/master/docs/1000.yaml)、
  [FLT 正则素数形式化论文](https://afm.episciences.org/16046)
