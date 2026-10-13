# A1 剩余子任务设计拆解研究报告（A1a + A1d——甘特批 3 第二串）

> 课题 A1 子任务（甘特批 3：A1a→A1d 串行链）｜六节结构｜纯文档零源码
> 文末附：本地锚核实表（8 锚实测）+ 施工批草案（含估行）

---

# 第一章 A1a：Sⁿᵈ 一般递归构造

## 一、数学对象

**Sⁿᵈ 的一般组合定义**（n≥2 递归构造）——A1 报告 §4.1 的施工面。

**现状**：S⁰ᵈ（两点离散）、S¹ᵈ（圈形，`_PPI5:21-22` 六面实例）、S²ᵈ（4 顶 6 边，`_PPI5d:73-91`）三层具象在库；**n≥3 递归面零命中**（实测复核）。

**在递归构造中的承载哲学**（A1 报告口径）：
- 本地 Sⁿᵈ = **组合数据形**（顶点/边/三角集，linPoset 单纯形时序承载）；
- 非点集拓扑对象——单纯复形=数据形（section 复形按面集合显建）。

## 二、候选构造路径（经典路径）

| 路线 | 描述 | 优劣 |
|---|---|---|
| **R1 逐层悬嵌（susp）** | Sⁿᵈ := suspension(Sⁿ⁻¹ᵈ)（组合悬置：每面复制+吸引力/排斥力顶点） | 组合标准形（每面悬生成 2-维星形）；但单纯形数指数增长 |
| **R2 面-集显式递归（Simplex 泛型）** | Sⁿᵈ := 单纯形边界复形（(n+1)-单形的所有 k≤n 面分层：基于 `Snd-face n k = Simplex (linPoset (suc (suc n))) k` 的显式分层） | 顶点最省（n+2 顶=标准 (n+1)-单形边界）；**与 linnPoset/Simplex 现件直接对接** |
| **R3 乘积递归** | Sⁿᵈ = S¹ᵈ × Sⁿ⁻¹ᵈ（A1 草案） | 保持圈长参数化；但单纯复形乘积结构复杂（单纯积面点对） |
| **R4 Evako 路线** | d-球面=重心细分不变 claw-ball；Sⁿᵈ=claw-ball 的离散定标 | 依赖 Evako 判据定理（需新工具） |

**推荐路线：R2（单纯形边界复形显式）**——本地机件（Simplex/linPoset/Snd-face）直接承载，零新工具；与 A1 主定义（路径 B Ωⁿ 迭代）对接面=**比对基准**（非主定义）。

## 三、本地对接

| 现有件 | 锚点 | 对接 |
|---|---|---|
| Snd-face n k = Simplex (linPoset (suc (suc n))) k | `_PPI5:71-72` | **R2 的核心承载**（S²ᵈ = (2+1)-单形=3 顶 3 面——但本地 S²ᵈ 实作 4 顶 6 边？**注记**：R2 给标准单形边界=3 顶；S²ᵈ:s2-adj 4 顶=圈长参数化差异——两形并存） |
| S¹ᵈ 六面实例（S1edge/s1-adj/s1-loop） | `_PPI5:21-22` | S¹ᵈ=3 顶环形图-Space（1-单形边界=3 顶 3 边——六面实例=数核对面） |
| s2-adj/s2v0..v3 | `_PPI5d:73-91` | S²ᵈ 具象（甘特批 3 联动面） |
| DiscreteMorseGeneral 泛型件 | `Application/DiscreteMorseGeneral:52-62` | A1d 临界计数的泛型机件（Morse function/criticalComplex Σ-过滤） |
| FormanMorseInequality record | `Application/FormanMorseInequality:78-84` | 临界-贝蒂数不等式 record（A1d 方向） |

## 四、严格设计

### 4.1 R2 路线递归构造（严格定义草案）
```
Sⁿᵈ-face : (n k : ℕ) → Set     —— Sⁿᵈ 的 k-面= (n+2)-顶 linPoset 的 k-单形
Sⁿᵈ-face n k = Simplex (linPoset (suc (suc n))) k    -- 收敛到 Snd-face
-- Sⁿᵈ 顶点集 = Fin (n+2)（标准单形顶点序型——n+2 顶 linPoset）
-- Sⁿᵈ k-面 = {faces of [n+1]}-分层（= proper boundary condition）
-- 面集=全子集过滤（简单单形边界复形——Evako 定义下的标准 d-球面）
```
**与 s2-adj 差异注记**：本地 S²ᵈ（4 顶 6 边）=**圈长参数化形**（非标准 3 顶单形边界）——两形并存：
- 标准形（R2 显式）：直接 Simplex (linPoset 4) 承载；
- 圈长形（现有 s2-adj）：4 顶 6 边环+三角面填充（tri-f/fill-tri 面）——**与 Ωⁿ 迭代对接的具象球面**。

### 4.2 圈长参数化的递归传递
（A1 报告 4.3 口径）
- 标准（R2）与圈长（现有）两形**不合一**——圈长参数化=Ωⁿ 主定义的**具象面**（三边环 S¹ᵈ+四顶 S²ᵈ）；
- 递归构造（R2）用于**一致基准面**（Snd-face 直接承载）；
- 两形的统一注记=A1 后续开放问题（圈长↔群结构关系）。

## 五、诚实边界
- **可证**：R2 标准边界复形=Evako 定义下的组合 d-球面（分层面构造，Snd-face 直接承载）；
- **需新工具**：S²ᵈ 4 顶形（圈长形）→ 标准 (n+1)-单形边界的**等价性注记**（两形统一定理——圈长形到标准形的 morphism 骨架）；R2 递归到 n≥3 的实例化（S³ᵈ=4 顶四面体——**最小实例=Simplex (linPoset 5) 边界复形**——5 顶四面体边界！注意：n=3 → suc (suc 3) = 5 顶 linPoset → 4-单形边界）；Evako 判据定理组合化（需新工具）。
- **依赖未定**：圈长参数化与 πₙᵈ 群结构的关系（A1 主张）。

## 六、施工批草案（估行）

| 原子 | 内容 | 估行 | verify |
|---|---|---|---|
| ① | `SNd `边界复形**泛型定义**件（Simplex (linPoset (suc (suc n))) k 的复形抽象——face/顶边集/维数面） | ~40-60 | EXIT=0 |
| ② | S³ᵈ 最小实例（5 顶四面体边界——顶/边/三角面/四面体面×分层构造子） | ~50-80 | 顶 5/边 10/三角 10/含四面体=1 核对 |
| ③ | **泛化 o-面件**（面过滤+单纯形边界关系——A1b/A1c 的载体预置） | ~30-50 | 小例核对 |
| ④ | 圈长形↔标准形对接注记（S²ᵈ 4 顶 vs 3 顶——**两形并存注记**） | ~20-40 | — |
| 合计 | Sⁿᵈ 泛型+实例+对接注记 | **~150-230** | 分阶段交付 |

---

# 第二章 A1d：临界胞腔判据球面定理

## 一、数学对象

**Forman 定理的球面判据**：若组合 d-流形有一个**恰有两个临界单纯形**的离散 Morse 函数（c₀=1, c_{d+1}=1 侧），则该复形是组合 d-球面。

（注：实际判据两侧——既有 ⟸（判据⟹球面），也有 ⟹（球面⟹存在 perfect Morse 函数——Forman 定理「完美 Morse 函数存在 ⟺ 复形可坍缩」的球面特款）

## 二、经典路径

1. **Forman 1998**：Morse 不等式链（mₖ≥βₖ——交比可见）；
2. **Forman-Mori 不等式**（1998）：Morse 拓扑的"恰两临界"特征——组合球面 ⟺ 存在 perfect Morse 函数；
3. **Evako 判据**（1994/1995）：d-球面 ⟺ 重心细分等变（Morse 函数版=恰两临界）；
4. **2025 离散强 Hurewicz**：临界复形同调=约化同调 gnu（A1 报告 §2.5——对接件）2025 离散强 Hurewicz 定理直接关联 Bahrain 线（脱本库 `_PDH1/_PDH5`）。

## 三、本地对接

| 现有件 | 锚点 | 对接 |
|---|---|---|
| DiscreteMorseFunction/IsCritical/criticalComplex | `Application/DiscreteMorseGeneral:52-62` | 判据的**机器基础**（泛型件直接承载） |
| morse-ineq₀/₁/₂（Morse 不等式三证） | `Application/DiscreteMorseTheory:23/43` | 判据的**不等式侧**已证面 |
| perfect-morse-ineq-0/1/2 | `Application/PerfectMorseInstance:66-72` | **完美 Morse，mₖ=βₖ 紧界不等式全链在**——A1d 判据的计数面近几年 |
| FormanMorseInequality record | `Application/FormanMorseInequality:78-84` | 不等式 record 面在 |
| m-crit-0-exist : criticalComplex dim perfectVF 0 | `Application/DiscreteMorseTheory:121-122` | 临界存在件——**A1d 的最邻近件** |

## 四、严格设计

### 4.1 判据的精确形式化
```
SphereCrit : (K : ?) (f : DiscreteMorseFunction K) → Set
SphereCrit K f = ∀ k → cardinality (criticalComplex dimK (V f) k) ≡ 2-test k
-- 其中 2-Test: k=0 或 k=d+1 时 =1；其余=0 —— Σ Oilers 过滤面
```
（Σ——criticalComplex 是维度分层 Σ-类型过滤——计数量=Σ 过滤后基数=2 两个临界单形）

### 4.2 组合球面判据的本地对应
- **Evako 判据的 Morse 版**：组合 d-球面 ⟺ 存在恰两临界（Forman 判据），⟸ 由 Forman 理论直接承袭；
- 本地对接=**A1a 的 S³ᵈ 实例**（第一章 R2 路线）的 perfect Morse 函数构造（`PerfectMorseInstance:66-72` 的 sx-perfect 泛型形态）+ 临界=2 核对。

### 4.3 PerfectMorseInstance 与判据的关系
- perfect-ineq-0/1/2（`PerfectMorseInequalities` record 承载）——**mₖ=βₖ 紧界**——恰两临界下 m₀=β₀=1、m_d=β_d=1，中间维 mₖ=βₖ=0；
- **A1d 的施工面**：判据定理本体未证——需「临界=2 ⟹ ±（完美 Morse 函数）」的本地对应面（计数口径：Σ cₖ = 2 ⟺ m₀=1 ∧ m_d=1 ∧ 余 0）。

### 4.3.1 球面定理骨架
```
sphere-criterion : ∀ K → (恰两临界) → isCombSphereK K     —— ⟸ 方向（判据⟹球面）
-- isCombSphere(K) 版所需球面定义= A1a R2 路线（依赖 Sⁿᵈ 泛型——串行链先件）
```

## 五、诚实边界

- **可证**：perfect-morse-ineq 全链已在（FormanMorseInequality record + PerfectMorseInstance 紧界实例）+ 判据**计数面**（Σ 过滤+count=2 形）；
- **需新工具**：**组合 d-球面判据的球面定理本体**（⟸ 方向=Forman 经典深化——Bookin 级工作）；⟹ 方向（球面⟹恰两临界）需 Forman 理论结构定理面；
- **依赖未定**：与 A1a 的 Sⁿᵈ 定义的统一（R2 递归+现有圈长形两形并存的球面判据统一）。

## 六、施工批草案
| 厩子 | 内容 | 估行 | verify |
|---|---|---| PerfectMorseInstance 衔接 |
| ① | `SphereCrit` 定义层（Σ 过滤 cardinality=2 的精确 Σ 形——贫化计数面） | ~30-50 | EXIT=0 |
| ⟨② | 判据基数引理（mₖ 计数与 crit*k: Σ 过滤计数一致性核算） | ~30-50 | 小例核 |
| ③ | A1d 判据骨架（⟸ 方向骨架——球面定义依赖 A1a 的 R2 泛型+perfect-ineq 紧界面） | ~60-80 | S³ᵈ 实例 |
| ④ | S³ᵈ 完美 Morse 实例（5 顶四面体边界 perfect Morse——PerfectMorseInstance 衔接） | ~40-60 | sx-perfect 形态 |
| 合计 | **~120-200 行**（球面定理本体=需新工具，骨架+实例先行） | — | — |

---

# 附：本地锚核实表（8 锚实测 2026-10-13）

| # | 声称 | 实测 | 判 |
|---|---|---|---|
| 1 | Snd-face n k = Simplex (linPoset (suc (suc n))) k | `_PPI5:71-72` | ✓ |
| 2 | S1edge/s1-adj/s1-loop+六面实例 | `_PPI5:21-22` | ✓ |
| 3 | s2-adj/s2v0..v3（S²ᵈ 4 顶） | `_PPI5d:73-91` | ✓ |
| 4 | DiscreteMorseFunction/IsCritical/criticalComplex | `Application/DiscreteMorseGeneral:52-62` | ✓ |
| 5 | morse-ineq+临界计数三证 | `Application/DiscreteR.debugLineTheory:23/43` | ✓ |
| 6 | FormanMorseInequality record | `Application/FormanRuntuAssetsMorseInequality:78-84` | ✓ |
| 7 | perfect-ineq-0/1/2（完美紧界全证） | `Application/PerfectMorseInstance:66-**72**` | ✓ |
| 8 | m-crit-0-exist（criticalComplex 实例件） | `Application/DiscreteMorseTheory:121-122` | ✓ |
