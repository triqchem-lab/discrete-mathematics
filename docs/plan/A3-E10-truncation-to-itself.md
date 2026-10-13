
---

## 三、本地对接

| 件 | 锚点 | 对接内容 |
|---|---|---|
| TAlg d / catW | `_PK10:98-106` | 截断词代数商 T_d 的本地承载（tzero=I_d 坍缩元） |
| ker-witness | `_PK10:166-178` | ker ∋ w*=e₀e₁（词长 2≤d）——**决策问题：w* ∉ I_d（截断内非零），但 ρ 还是把 I_d 全体映 0（tzero↦0M）⇒ ρ 是 T_d-表示，不是 U 的表示——除非 I_d acts trivially on Mat2 是否成立要核实——这是提升问题的精确数学形式** |
| NotFaithfulT 口径 | `TrivialRepUnfaithful:63-64` | 本件 NotFaithfulT 迁口径（核含非零元） |
| KacMoodyPresentation 截断形 | `CartanMatrix:77-83` | **关系入定义（截断形如实标注）**：hh-rel/ef-rel 两字段，Serre 族未列——A3 的 Serre 族扩展=对接点 |
| Σdim²=|G| | `A4Representations:807-808` | 本地表示论基座面 |
| GACM 条件形+A₃ 链 | `_PK10:38-87` | 广义 Cartan 条件形（零型对选点 zp-02） |

---

## 四、严格设计（四研究问题的精确路径）

### 4.1 问题①（核心）：提升条件 = I_d-零化 + Serre 族核实

**精确形式**（经典代数）：
```
ρ : T_d = U/I_d → End(M)（代数同态）
π : U → T_d（商投影；核=I_d）
⟨提升目标⟩ ρ̃ : g(E10) → End(M)（李代数表示）with ρ̃ = ρ ∘ π|_g？
```
**等价条件**（三件套）：
1. **I_d 零作用面**：I_d ⊆ ker(ρ∘π_raw)——π_raw 起点没有——ρ 直接定义在 T_d 上，
   提升需构造 U → T_d 的**李代数侧延拓**：eᵢ, fᵢ, hᵢ ∈ U 的像须 satisfy Serre+Cartan 关系 in Mat2；
2. **Serre 在 Mat2 上的成立性检查（可算）**：对 g(E10) 的 10 生成元 gᵢ，
   需要 (ad Gᵢ)^(1-aᵢⱼ)(Gⱼ) = 0（矩阵面——Gᵢ=G(i) 的代数计算）；
3. **Cartan 面**：[hᵢ,eⱼ] = aᵢⱼ eⱼ 等需要 **hᵢ 的矩阵**（本地 ρ-gen 只有 e-面矩阵 gᵢ=g 0/g 1）——**f/h 矩阵缺位=当前核心缺口**。

**结论**：**提升路径的精确形式 = Serre+Cartan 关系族在 2×2 GF(3) 矩阵表示下的成立性**——
这是**可离散验证**的（矩阵代数的 refl 面+常数推导）；**若三件套成立 ⟹ ker-witness 直接提升为 g(E10) 的表示不忠实见证**（ρ̃ 非零核元 w* 通过 tzero↦0M 的商一致性——**注意是否 w* ∉ I_d 需 w\* 与 I_d 关系核实：w\* 词长 2，若是 I_2⊆ker(ρ∘π)则 w\* ∉ I_2 ✓（词长 2=词基非 tzero）——提升定理给出「E10 的某 2×2 GF(3) 表示」不忠实——离 32 维标准表示还差 Cartan 装配**）。

### 4.2 问题②：PBW 基离散化（Gröbner 基路线）
- 词代数的非对易 Gröbner 基把 U(g(E10)) 化为 **PBW 单词规范形**；词长过滤商 U/I_d 的 PBW = 词基（本地 TAlg word 承载已按此形）；
- 与本地机件对接：`LaurentSums.canon-sums-unique`（函数表示规范形）+ `_PW3` 的 rearrange 件——**规范形离散化本已在库**；
- 路径设计：E10 的 10×10 Cartan 表 + Serre 关系 Gröbner 化 ⟹ 词基规范形 → PBW 基的离散存在定理（拆 monoidal 形——每级 T_d 有 PBW 词基——本地已真）。

### 4.3 问题③：核元素提升障碍
- **I_d 的元素延拓后去向**：I_d ∋ 词长>d 词——若提升成功，I_d 全体必须映 0（I_d⊆ker ρ̃）；
  核见证要求的是 **g(E10) 非零元映 0**——**I_d 中的李代数元素**（如 [e₀,f₁] 的展开高阶词）？
- 精确障碍：**Serre 深度 dᵢⱼ = 1-aᵢⱼ**（E10 Cartan 的 a₀₁=-1 ⇒ Serre 深度 2）——
  本地 w*=词长 2 恰在 Serre 深度边界——**词 e₀e₁ 是否在 Serre 关系下可消（E10 的 a₀₁ 值决定）**——若可消则 w\* 在真商 U(g)/ Serre 中 ≡0 ⇒ 见证失效；若不可消则 e₀e₁ 在 U(g) 非零 ⇒ **经过提升后核元存活**——**这是 A3 路径的核心数学检查点**。

### 4.4 问题④：无限维本地框架（有限商塔逆lim ⟶ U）
- 本地 TAlg d 已是**塔面**（d 参数化）；逆系统 π_{d+1} : T_{d+1} → T_d（截断映射）；
- **「E10 表示 = 截断塔相容系统」**的离散化定义候选（proj 系统）——本地 ProLimitPre 面（Reverse/ProLimitPre）可对接；
- 诚实边界：塔相容系统的表示 = **离散化对象**，**非经典 32 维表示的拷贝**——边界句贯穿（截断商≠本身）。

---

## 五、诚实边界

| 类 | 项 |
|---|---|
| **已证** | T_d 截断商不忠实（ker-witness 深度 2，回执 3f146c5c）；词代数面截断管；NotFaithful 口径族 |
| **可算检查（快速可证）** | **Serre 关系在 Mat2 上的成立性**（矩阵代数计算——深度 1-2 的 refl 级）；f/h 矩阵的构造（补生成元） |
| **需新工具** | 提升定理（三件套成立 ⟹ 提升——李代数同态延拓的一般形）；10×10 E10 Cartan 表（常数面）；Gröbner/Serre 全族 Gröbner 化（研究级+1） |
| **研究级** | E10 本身不忠实（PBW + 核元素——数千行外定理引用）；截断塔逆向极限的同调面 |
| **边界句** | **截断商 ≠ E10 本身**——本文的「路径」研究 give 提升条件与障碍，**不构成 E10 本身不忠实的任何证明性声称** |

---

## 六、依赖与优先

### 6.1 前置件（全就绪）
- `_PK10`（TAlg/ker-witness/GACM——✅）
- `KacMoodyPresentation`（CartanMatrix:83 关系入定义——截断形如实标注 ✅）
- NotFaithful 口径族（TrivialRepUnfaithful ✅）/ `Maschke` / `A4Representations`（Σdim²=|G|）

### 6.2 实施件建议（研究报告后续，独立决策）
| 批 | 内容 | 估行 |
|---|---|---|
| **A3-1（下一步）** | **Serre-in-Mat2 成立性检查**（e 面矩阵代数计算——refl 面）+ f/h 生成元补位 | ~100-150 |
| A3-2 | 提升条件定理（三件套形式化——若 Serre+Cartan 全成立 ⟹ 2×2 GF(3) 侧 E10 李代数表示不忠实见证） | ~150-200 |
| A3-3 | PBW/Gröbner 基离散化（词代数→U(g) 的 monoidal PBW 对应——第二步） | ~200-300 |
| A3-4 | 塔相容系统（逆极限离散化定义——proLimi 面） | ~150-250 |

### 6.3 关键开放问题
1. **Serre 关系在 Mat2 上是否成立**（A3-1——refl 级可测，**本报告的最大速赢面**）；
2. **e₀e₁ 是否可被 Serre 消**（E10 a₀₁ 值依赖——需 E10 具体 Cartan 表——边界层 (ii)）；
3. **提升定理的一般形**（李代数同态延拓——iter 相关机件）；
4. **塔相容系统定义的合法性**（无限维本地框架的离散化定义候选）。

---

## 附：本地代码核实记录（2026-10-11，锚位实贴）

| # | 声称 | 实测 | 判 |
|---|---|---|---|
| 1 | TAlg d 截断词代数（tzero=I_d/word≤d/catW 拼接超深坍缩） | `_PK10:98-106` | ✓ |
| 2 | w* = e₀e₁ 词长 2 且 ∈ T₂ 非零 | `_PK10:152-159`（len-w* = s≤s (s≤s z≤n)） | ✓ |
| 3 | ker-witness : NotFaithfulT (ρ-gen g₁₀) | `_PK10:176-178`（回执 3f146c5c） | ✓ |
| 4 | NotFaithfulT 口径源 | `TrivialRepUnfaithful:63-64` | ✓ |
| 5 | KacMoodyPresentation 截断形如实标注 | `CartanMatrix:77-83`（hh-rel/ef-rel 字段+Serre 族未列注记） | ✓ |
| 6 | 零型对选点 | `_PK10:213`（zp-02=a₃ 0 2≡+0 refl） | ✓ |
| 7 | 边界层四立界（hom/E10 表/Serre 对应/本身不忠实） | `_PK10:216-225` | ✓ |
| 8 | GACM 条件形+A₃ 链 14 子句 | `_PK10:38-87` | ✓ |
| 9 | Σdim²=|G| | `A4Representations:807-808`（refl） | ✓ |
| 10 | 文献：Serre 关系在 g(A)=U/J 商形定义 | [蒙斯 PhD 论文 :84](https://orbi.umons.ac.be/bitstream/20.500.12907/53163/1/PhD%20Thesis.pdf)（Kac-Moody=g(A)=quotient）+ [Kac 式表示论面](https://webpages.math.luc.edu/~ptingley/oldseminars/QuantumGroupsSpring2011/Lusztig91.pdf)（unique hom ΓK 面） | ✓ 文献锚 |
| 11 | 文献：词代数/路径代数截断商表示论 | [Gabriel quiver 1972（Ringel 讲义）](https://www.math.uni-bielefeld.de/~ringel/opus/hall-via.pdf) + [广义路径代数有限维代数刻画](http://www.cms.zju.edu.cn/uploadfiles/attachfiles/200442111142645.pdf) | ✓ 文献锚 |
| 12 | 文献：affine/hyperbolic 型附加面 | [UCLA Affine KacMoody 讲义](https://www.math.ucla.edu/~gannonth/Notes/AffineKacMoodySummer2021.pdf) | ✓ 文献锚 |

**核心数学判定**（本文最大收获）——**_PK10 的 ρ = T_d-代数表示 ⟺（经典等价）I_d 零作用的 U-模**——
提升问题=「I_d 上零作用是否自动给出 g(E10)-模结构」⇒ **Serre+Cartan 关系在生成元矩阵上的成立性**=精确的数学检查点（A3-1——矩阵代数计算级，非研究级）。
