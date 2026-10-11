# discreteHurewicz 设计文档（任务书 2.5 缺口——设计先行）

> 建立：2026-10-11｜性质：**设计文档（纯研究，零源码改动）**｜依据：Gao-Yang 2024 原文（`docs/文献/pdf/Gao-Yang2024_discrete-homotopy-posets_2410.16948.pdf`，文本层已验）+ 本地机件对表
> ⚠ 作者组注记：文本层验为 **Gao, Jing-Wen & Yang, Xiao-Song 二作者**（INDEX.md 注「外供六人名单疑为另一篇，待人类裁决」——引用以二作者为准，冲突在案）

## 一、Phase 1-① 文献定义提取（页码/定理号带原文对照）

### 1.1 离散同伦群 πₙᴰ（Definition 3.1，p.4-5）
- **载体**：Z = 顶点为整数的 digraph，边 = **(2i, 2i+1) 与 (2j, 2j−1)**（锯齿双有向边形）；Zⁿ = n 重笛卡尔积；I_p = {0,…,p} 诱导子图；∂I_pⁿ = 有坐标 ∈{0,p} 的顶点子图；
- **映射**：f : (Zⁿ, ∂Zⁿ) → (X, x₀) = **有限半径映射**（∃r ≥ 0：f : (Zⁿ, Zⁿ_{[r,∞)}) → (X, x₀)，最小 r = radius）；
- **同伦**：H : (Zⁿ,∂Zⁿ) × I_p → X（基点保持；X×I^p 乘积偏序形——文中注与 Prop 2.3 的偏序等价关系一致）；
- **群结构**：f·g 沿 x₁ 拼接（x₁ ≤ r_f 走 f / x₁ > r_f 走平移 g）；单位 = 常值映射；**n ≥ 2 交换**（引 [5, Prop 3.6]——Barceló-Kramer-Laubenbacher-Weaver 2001，即 A-同伦奠基文）；
- **关键定理**：θ : πₙᴰ(X,x₀) ≅ πₙ(|K(X)|,x₀)（**Theorem 3.3**——离散与经典同伦群全维同构，经 McCord 弱等价 + 单纯逼近）。

### 1.2 离散立方体同调 Hₙ^Cube（Definition 4.1/4.2，p.13）
- n-立方体 σ : Qⁿ → X（Q¹ = 二点偏序 {0→1}）；Lₙ(X) = n-立方体生成的**自由阿贝尔群（ℤ 系数！）**；
- 面映射 fᵢ±（插 0/1）；退化立方体 Dₙ（某 i 上 fᵢ⁻=fᵢ⁺）；Cₙ(X) = Lₙ/Dₙ；
- ∂ₙ^Cube(σ) = Σᵢ(−1)ⁱ(fᵢ⁻σ − fᵢ⁺σ)；**Hₙ^Cube(X) = Ker ∂ₙ / Im ∂ₙ₊₁**；
- 关联定理：同伦等价 ⟹ Hₙ^Cube 相等（Theorem 4.3）；ψ : H^Cube → H^Simpl(K(X))（Thm 4.7：闭 m-流形情形 ψ_* 同构）。

### 1.3 离散 Hurewicz 映射 h_D（Definition 5.1，p.24）
- φ 构造：对 f : I_{p1}×…×I_{pn} → X，φ(f) = Σ_{x∈I_{p1−1}×…×I_{pn−1}} f_x（f_x : Qⁿ → X 为平移截断的 n-立方体）；某 pᵢ=0 时 φ=0；
- Tr f : (I_{4r}ⁿ, ∂I_{4r}ⁿ) → (X,x₀) = f′ 限制（f′(x)=f(x₁−2r,…,xₙ−2r)）；
- **h_D([f]) = [φ(Tr f)]**（p.24）；
- **Lemma 5.2**（p.24-25）：①扩张不变（f̃ 边界补 x₀ ⇒ φ 相等——退化立方体贡献为零）②φ(Tr f) ∈ Ker ∂ₙ^Cube（闭链）③同伦不变（homotopic f g ⟹ Hₙ^Cube 中类相等）；
- **Proposition 5.3**（p.26）：h_D 是群同态（φ(Tr(f·g)) − (φ(Tr f)+φ(Tr g)) 为退化立方体和 ⟹ 零）；
- **Theorem 5.4（p.26，一维离散 Hurewicz 定理）**：对任意有限偏序 X，h_D : π₁ᴰ(X,x₀) → H₁^Cube(X) **满**，且 **Ker h_D = [π₁ᴰ, π₁ᴰ]**（交换子子群）——证明策略引 [3, Thm 4.1]（Barceló-Capraro-White 2014）；
- **Theorem 5.5（p.26-27）**：交换图（h_D 经 θ/ψ/η_* 与经典 h 交换——「离散 Hurewicz 映射与经典重合」）。

### 1.4 谱系定位
h_D 原型 = **[11] B. Lutz《Higher discrete homotopy groups of graphs》(2021)**；群结构引 [5]（= A-同伦奠基，与本库 BarceloAHomotopy 同谱系）；dim-1 策略引 [3]；立方/路径同调背景 [4]。

## 二、Phase 1-② 本地机件对表（模块:行锚）

| 文献件 | 本地件 | 状态 |
|---|---|---|
| πₙᴰ（Zⁿ 映射类） | **定义形分岔**：本地 πₙᵈ := π₀(Ωⁿᵈ)（`_PPI5d:126` π0-Ω1 = π₁ᵈ 定义相等｜`_PPI5f` π₂ᵈ）——**迭代循环空间路线**（A-同伦谱系 [2][5][6]）；另 `Foundation/GaoYangRigidLock` 是**动力学核**（单射端映射有限步返回——非映射群） | ⚠ **桥断点 ①** |
| 同伦关系（X×I^p 乘积形） | `Topology/BarceloAHomotopy`（AHomotopy slide/expand）+ `_PPI5` DHomotopy——同谱系不同形 | 比较定理缺 |
| Hₙ^Cube（ℤ 立方链） | **无立方链复形**；同调面在：`Problem/Hodge/FreeAbHomology(.Group)/FreeAbH0/FreeAbHodgeVerdict` + `Application/KerImQuot` + `Synthesis/ChainQuotIso` + Morse ∂M（MorseBoundaryK3）——系数世界 = **FAb = Fin n → Trit（GF(3)）** | ⚠ **桥断点 ②③**（链面缺 + 系数差 ℤ vs GF(3)） |
| h_D | **无** | 断 |
| θ 同构（Thm 3.3） | McCord 面：P2.2-mccord-0-layer-core ✅ 但 P2.2-M5（全 n 弱等价）**blocked** | 半 |
| 边链数据（φ 的 dim-1 形） | `_PPI4i` walk4-classify 的 **npos/nneg 计数对恰是 walk 的边链内容**（two-chain 面全证）——**dim-1 的 φ 对应物已在库** | ✅ 意外强点 |

**三处桥断点**：①πₙᴰ（Zⁿ 映射）≠ πₙᵈ（Ωⁿ 迭代）；②立方链复形（Qⁿ 链）缺；③系数世界 ℤ vs FAb/GF(3)——Thm 5.4 的 Ker=[π₁,π₁] 是阿贝尔化陈述，GF(3) 系数下为**模 3 阿贝尔化**（陈述须改写）。

## 三、Phase 1-③ 方案对比

| 维 | A 忠实移植形 | B Ωⁿ 重述形 | **C 混合形（dim-1 先行双世界对照）** |
|---|---|---|---|
| 定义 | Zⁿ 映射 + φ/Tr + ℤ 立方链 + h_D 原样 | walk→边链 h₁ : π₁ᵈ → H₁^FAb + n≥2 面链 | B 的 dim-1 落地 + 文献形 dim-1 最小对照 |
| Thm 5.4 | 原样直取 | GF(3) 版需自证（改写 Ker 陈述） | 双版本对照（两世界各证/对照） |
| 复用 | 低（Z digraph/半径映射/立方链全新建 ~300-500 行） | **高**（π₁ᵈ/KerImQuot/FreeAb/npos-nneg 全现成 ~80-120 行） | 中（~150-250 行） |
| 与 A 级件衔接 | 弱（π₁ᴰ≠π₁ᵈ——连经典侧需 McCord M5=blocked） | **强**（分水岭/π₁ᵈ/FreeAb 全链） | 强 |
| 宪法契合 | ⚠ ℤ 世界与 GF(3) 基座脱节 | ✅ 框架锁定有限群语境内 | ✅ |
| 关键洞见 | — | walk→边链 = φ 的 dim-1 形 | **Z¹ = 锯齿双向 digraph ≅ Gskel 型图**——dim-1 的桥是组合同构候选（walk 族同形），**不必经 McCord 迂回** |

## 四、Phase 2-④ 实施路线（推荐 C）与验证点

| 批 | 内容 | 估 | 验证点 |
|---|---|---|---|
| **DH-1** | h₁ : π₁ᵈ → H₁^FAb（walk→边链映射 + 同态性——复用 KerImQuot/FreeAb 现件 + `_PPI4i` 边链数据） | 60-100 行 | 探针绿 + two-chain/G2s 实例核对 |
| **DH-2** | Thm 5.4 类比（GF(3) 版：h₁ 满 + **Ker = 交换子的模 3 像**——陈述改写如实；two-chain 全证 + 一般图按 [3, Thm 4.1] 策略立界） | 50-80 行 | 实例全证 + 泛型骨架 |
| **DH-3** | dim-1 对照件：Z¹-maps（锯齿 walk + 半径截断）↔ Gskel walk **组合桥最小件** | 40-60 行 | 对照实例 |
| **DH-4** | 设计批（n≥2 世界定案：立方链 vs Simplex/TriFace 面链 + 系数世界决定 + Thm 5.5 对照图骨架） | 设计文档 | 四问齐 |

**诚实边界**：①GF(3) 版 Thm 5.4 ≠ 文献 ℤ 版（系数差异如实标注，不冒充）；②n≥2 前 DH-4 世界定案未过不开工；③πₙᴰ↔πₙᵈ 一般维桥（经 θ 或组合形）属深件——DH-3 只做 dim-1。

## 五、结论（Phase 2 收口）
- **定义提取**：h_D = Def 5.1（p.24）+ Thm 5.4（p.26）——「映射类 → 闭链类」经 φ/Tr 构造；
- **桥断点三处**（定义形/链面/系数世界）——**dim-1 是唯一三断点都薄的地方**（npos/nneg 边链数据在库 + Z¹≅Gskel 型 + 陈述改写可控）；
- **推荐 C（dim-1 先行双世界对照）**：DH-1..3 ≈ 150-250 行达「离散 Hurewicz 一维定理的框架版 + 文献对照」，DH-4 再定 n≥2——**设计层缺口就此转为工时件**。
