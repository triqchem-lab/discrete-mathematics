# 目录 `src/Sovereign/Algebra/Jacobian/` 逐模块审计记录

共 15 个模块。


## `src/Sovereign/Algebra/Jacobian/jac_AutT6.agda`

- **module**: `Sovereign.Algebra.Jacobian.jac_AutT6`
- **行数**: 140（代码 35 / 注释 82）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | jac_AutT6 — Aut(T⁶/GF(9)) 群论闭包
  - 半直积 GL₃(GF(9)) ⋊ Gal(GF(9)/GF(3)) 的结构定义
  - 0 postulate
- **导入 (9)**: `Data.Nat`, `Data.Fin`, `Data.Product`, `Relation.Binary.PropositionalEquality`, `Sovereign.Base.Trit`, `Sovereign.Algebra.GF9`, `Sovereign.Problem.Riemann.Galois`, `Sovereign.Structology.A4Group`, `Sovereign.Algebra.LieDiscrete`
- **record 类型**: `AutElement`
- **顶层签名 (7)**: `Mat3`, `I3`, `id-aut`, `frob-aut`, `aut-order`, `a4-order`, `a4-in-aut`
- **质量**: `refl`×1；无 postulate / 无 hole

## `src/Sovereign/Algebra/Jacobian/jac_CRTDet.agda`

- **module**: `Sovereign.Algebra.Jacobian.jac_CRTDet`
- **行数**: 113（代码 17 / 注释 80）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | jac_CRTDet — CRT 行列式分解定理 (拱顶石)
  - 定理: det(M) = crt12(det(M₃), det(M₄))
  - det(M) ≠ 0 ⟺ (det(M₃) ≠ 0) ∧ (det(M₄) ≠ 0)
  - 永久替代通用 N×N 行列式。0 postulate。
  - 元理论对齐: CRT 无损降维 ↔ Dvir 有限射影空间精确计数 —
  - Dvir: 𝔽_qⁿ 方向约束 → |ℙⁿ⁻¹(𝔽_q)| = (qⁿ-1)/(q-1) 精确有限计数;
  - 本模块: 高维可逆性 → CRT 同态投影至 3×3/4×4 局部分量判定。
  - 参见: docs/Kakeya-元诊断-连续统病态vs离散自愈.md §二
- **导入 (6)**: `Data.Nat`, `Data.Fin`, `Data.Product`, `Relation.Binary.PropositionalEquality`, `Sovereign.Base.Trit`, `Sovereign.Algebra.Duodecimal`
- **顶层签名 (4)**: `det2-gf3`, `crt-det-I₂`, `crt-det-nonzero`, `crt-equivalence`
- **质量**: `refl`×4；无 postulate / 无 hole

## `src/Sovereign/Algebra/Jacobian/jac_CRTSpectrum.agda`

- **module**: `Sovereign.Algebra.Jacobian.jac_CRTSpectrum`
- **行数**: 607（代码 251 / 注释 263）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | Sovereign.Algebra.Jacobian.jac_CRTSpectrum
  - CRT 正交分解与矩阵谱 (det/rank/双射性) 的连接
  - 核心原则：
  - 1. Z/12Z ≅ Z/3Z × Z/4Z (CRT, gcd(3,4)=1) 是结构学基石
  - 2. 映射双射性在 CRT 分量上独立判定——将 12! 搜索分解为 3!×4! 正交
  - 3. 行列式单位性: det 是 Z/12Z 单位 ⟺ det mod 3 ≠ 0 且 det mod 4 是奇数
  - 4. 零因子在 CRT 分量中可见——环的缺陷在正交投影中暴露
  - 5. CRT 加速: 729×729 矩阵分解为 27×27 的 CRT 分量
  - 包含：Duodec 双射 CRT 分解、零因子可见性、行列式单位性、
  - GF(3)² 谱分类、CRT 加速定理
- **导入 (9)**: `Relation.Binary.PropositionalEquality`, `Data.Product`, `Data.Sum`, `Data.Empty`, `Data.Fin`, `Sovereign.Base.Trit`, `Sovereign.Algebra.Duodecimal`, `Sovereign.Algebra.Jacobian.jac_Discrete`, `Sovereign.Algebra.Jacobian.jac_Matrix`
- **data 类型**: `IsNonZero`, `IsDuodecUnit`, `IsUnit`
- **顶层签名 (32)**: `π3-surjective`, `π4-surjective`, `Inj12`, `Surj12`, `Bij12`, `CRT-structural`, `crt-compose`, `Inj3`, `Surj3`, `Inj4`, `Surj4`, `crt-bijection-forward`, `crt-bijection-backward`, `crt-id-decompose`, `+1-mod3`, `+1-mod4`, `+1D`, `+1-crt-compat`, `d6-double-zero`, `Mat2-12`, `det2-12`, `unit-crt-d1`, `unit-crt-d5`, `unit-crt-d7`, `unit-crt-d11`, `det-unit-crt-condition`, `det-unit-table`, `det2-range-claim`, `π3-mat`, `π3-negate`, `det-commutes-π3`, `crt-acceleration-factor`
- **质量**: `refl`×78；无 postulate / 无 hole

## `src/Sovereign/Algebra/Jacobian/jac_Discrete.agda`

- **module**: `Sovereign.Algebra.Jacobian.jac_Discrete`
- **行数**: 123（代码 33 / 注释 63）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | Sovereign.Algebra.Jacobian.jac_Discrete
  - Phase 2: 形式导数 vs 差分算子 vs 函数表矩阵
  - 三种"雅可比"的区分:
  - 1. 形式导数 J_formal: 连续统的离散模拟, char p 下有 Frobenius 盲区
  - (注: Frobenius 盲区是 char p 经典事实, Adjamagbo 1995, Maubach)
  - 2. 差分算子 J_Δ = SF - F: 真正的离散雅可比, 无 Frobenius 盲区
  - 3. 函数表矩阵 M_F: 有限集线性代数, det ≠ 0 ⟺ 双射 (重言式)
  - 注意: 形式多项式环 GF(3)[x] 中 x³ ≠ x,
  - 多项式函数空间 GF(3)^{GF(3)} 中 x³ = x (Fermat)。
  - BCW 规约在形式多项式环上工作, Fermat 坍缩在函数空间上工作。
- **导入 (4)**: `Relation.Binary.PropositionalEquality`, `Data.Product`, `Data.Empty`, `Sovereign.Base.Trit`
- **顶层签名 (11)**: `Mat2`, `det2`, `I2`, `GF3²`, `FormalJacDet1`, `FunctionTableInj`, `F-blind`, `formal-jac-blind`, `formal-passes`, `table-fails`, `formal-not-table`
- **质量**: `refl`×3；无 postulate / 无 hole

## `src/Sovereign/Algebra/Jacobian/jac_DiscreteJC.agda`

- **module**: `Sovereign.Algebra.Jacobian.jac_DiscreteJC`
- **行数**: 325（代码 81 / 注释 194）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | Sovereign.Algebra.Jacobian.DiscreteJC
  - 离散雅可比猜想的精确 Agda 类型陈述
  - 核心原则:
  - 1. 离散是本质, 连续是投影 — 全局矩阵判据在有限环面上精确成立
  - 2. 逐点雅可比 (形式导数/差分算子) 有局部→全局鸿沟, 不蕴含双射性
  - 3. 函数表矩阵 det(M_F) ≠ 0 ⟺ F 双射 (有限集线性代数, 鸽巢原理)
  - 4. 三层雅可比强度: 形式导数 < 差分算子 < 函数表矩阵
  - 包含: 三层雅可比定义, 反例整合, 主定理陈述, 与连续统JC的关系, 强度总结
- **导入 (11)**: `Relation.Binary.PropositionalEquality`, `Data.Product`, `Data.Empty`, `Sovereign.Base.Trit`, `Sovereign.Algebra.Jacobian.jac_Discrete`, `Sovereign.Algebra.Jacobian.jac_GF3`, `Sovereign.Problem.Riemann.FrobeniusBlind`, `Sovereign.Algebra.Jacobian.jac_Pigeonhole`, `Sovereign.Algebra.Jacobian.jac_Injectivity`, `Sovereign.Algebra.Holographic.Conjecture`, `Sovereign.Algebra.Jacobian.jac_Matrix`
- **顶层签名 (7)**: `pointwise-insufficient-GF3`, `pointwise-insufficient-GF9`, `pointwise-insufficient`, `global-exact-GF3²`, `DiscreteJacobiTheorem-GF3²`, `DiscreteJacobiTheorem-GF3²-converse`, `DiscreteJacobiEquiv-GF3²`
- **质量**: `refl`×1；无 postulate / 无 hole

## `src/Sovereign/Algebra/Jacobian/jac_FunctionTable.agda`

- **module**: `Sovereign.Algebra.Jacobian.jac_FunctionTable`
- **行数**: 117（代码 38 / 注释 56）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | Sovereign.Algebra.Jacobian.jac_FunctionTable
  - 函数表矩阵 M_F: det ≠ 0 ⟺ F 双射 (利用列结构绕过 N×N 行列式)
  - 核心原则:
  - ① M_F 的列是标准基向量 (每列恰一个 1)
  - ② F 单射 ⟺ 列互异, F 满射 ⟺ 无全零行
  - ③ 列互异+无全零行 ⟺ 置换矩阵 ⟺ F 双射
  - ④ 因此 NonSingular(=Inj2) 等价于 det(M_F) ≠ 0 (形式化 gap 闭合)
  - 包含: 2×2 行列式实例, 抽象论证, 等价性定理, 低维验证
- **导入 (8)**: `Relation.Binary.PropositionalEquality`, `Data.Product`, `Data.Empty`, `Sovereign.Base.Trit`, `Sovereign.Algebra.Jacobian.jac_Discrete`, `Sovereign.Algebra.Jacobian.jac_GF3`, `Sovereign.Algebra.Jacobian.jac_Pigeonhole`, `Sovereign.Algebra.Jacobian.jac_Injectivity`
- **顶层签名 (4)**: `ColumnDistinct`, `RowFull`, `column-row-equiv`, `example-nonsingular-fails`
- **质量**: `refl`×1；无 postulate / 无 hole

## `src/Sovereign/Algebra/Jacobian/jac_GF3.agda`

- **module**: `Sovereign.Algebra.Jacobian.jac_GF3`
- **行数**: 325（代码 125 / 注释 137）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | Sovereign.Algebra.Jacobian.GF3
  - Phase 1: GF(3) 上的 BCW 坍缩
  - 费马小定理 x³=x 使三次多项式退化为线性,
  - 但 Frobenius 盲区 (∂(x³)/∂x=0) 仍然存在。
  - 逐点 JC 在 GF(3) 上为假; 全局 JC 平凡为真。
- **导入 (4)**: `Relation.Binary.PropositionalEquality`, `Data.Product`, `Data.Empty`, `Sovereign.Base.Trit`
- **顶层签名 (33)**: `cube`, `fermat3`, `GF3²`, `Mat2`, `det2`, `I2`, `det2-I2`, `deriv-cube-is-zero`, `deriv-id-is-one`, `deriv-scaled-cube`, `J-formal`, `J-formal≡I`, `det-J-formal`, `bcw-collapse`, `F-gf3`, `F-gf3-vals`, `gf3-collision`, `gf3-not-surj`, `shift`, `Sx`, `Sy`, `_⊖_`, `π₁`, `π₂`, `Δx-F1-counter`, `Δy-F1-counter`, `Δx-F2-counter`, `Δy-F2-counter`, `JΔ-counter`, `det-JΔ-counter`, `id-gf3`, `JΔ-id`, `det-JΔ-id`
- **质量**: `refl`×58；无 postulate / 无 hole

## `src/Sovereign/Algebra/Jacobian/jac_GF9Matrix.agda`

- **module**: `Sovereign.Algebra.Jacobian.jac_GF9Matrix`
- **行数**: 165（代码 79 / 注释 56）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | Sovereign.Algebra.Jacobian.jac_GF9Matrix
  - GF(9) 矩阵代数基础设施 — 解锁 BSD/Complexity/LatticeField 三个模块
  - 核心定义:
  - §1. GF9Vec, GF9Mat: GF(9) 向量与矩阵
  - §2. 2×2 行列式 (det2-gf9, 已验证 det(I)=1)
  - §3. 矩阵-向量乘法接口与秩计算接口
  - 0 postulate.
- **导入 (6)**: `Data.Nat`, `Data.Fin`, `Data.Product`, `Relation.Binary.PropositionalEquality`, `Sovereign.Base.Trit`, `Sovereign.Algebra.GF9`
- **顶层签名 (18)**: `0gf9`, `1gf9`, `GF9Vec`, `GF9Mat`, `neg-gf9`, `det2-gf9`, `det2-gf9-I`, `det2-gf9-nonzero`, `I2-gf9`, `rank2-gf9`, `det3-gf9`, `I3-gf9`, `det3-gf9-I`, `rank3-gf9`, `det4-gf9`, `I4-gf9`, `det4-gf9-I`, `rank4-gf9`
- **质量**: `refl`×7；无 postulate / 无 hole

## `src/Sovereign/Algebra/Jacobian/jac_Injectivity.agda`

- **module**: `Sovereign.Algebra.Jacobian.jac_Injectivity`
- **行数**: 203（代码 78 / 注释 87）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | Sovereign.Algebra.Jacobian.jac_Injectivity
  - 函数表矩阵非奇异 ⟹ F 单射 ⟹ F 双射 的完整证明链
  - 核心原则:
  - 1. 函数表矩阵 M_F: 每列是标准基向量，列唯一 ⟺ F 单射
  - 2. 碰撞 → 同列 → 行列式为零（2×2 实例 + 一般论证）
  - 3. 有限集上单射 ⟹ 满射（鸽巢原理，pigeonhole-2, 0 postulate）
  - 4. 综合: det(M_F) ≠ 0 ⟹ F 双射
  - 包含: 碰撞概念, 2×2同列→det=0, 核心证明链, 反例验证
- **导入 (7)**: `Relation.Binary.PropositionalEquality`, `Data.Product`, `Data.Empty`, `Sovereign.Base.Trit`, `Sovereign.Algebra.Jacobian.jac_Pigeonhole`, `Sovereign.Algebra.Jacobian.jac_Discrete`, `Sovereign.Algebra.Jacobian.jac_GF3`
- **顶层签名 (14)**: `_≢_`, `proj₁`, `proj₂`, `ne01`, `ne02`, `ne12`, `Collision`, `x⊕negx≡0`, `NonSingular`, `T₀T₀≢T₀T₁`, `F-gf3-collision`, `F-gf3-not-inj`, `F-gf3-not-surj`, `F-gf3-not-bij`
- **质量**: `refl`×4；无 postulate / 无 hole

## `src/Sovereign/Algebra/Jacobian/jac_LieGroup.agda`

- **module**: `Sovereign.Algebra.Jacobian.jac_LieGroup`
- **行数**: 330（代码 124 / 注释 155）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | Sovereign.Algebra.Jacobian.jac_LieGroup
  - 离散 Frobenius-Galois 群代数 — 从连续李群到有限自同构群
  - 核心定理:
  - §1. 离散指数映射: exp_D(t) = σ^t 替代 exp(tX), 周期 3
  - §2. Galois 自同构群: Aut(GF(9)/GF(3)) ≅ C₂, σ(z)=z³ 驱动
  - §3. T⁶ 自同构群: Aut(T⁶/GF(9)) ⊂ GL₆(GF(3))
  - §4. 表示论有限封顶: 所有不可约表示 ⊂ 有限特征标表
  - §5. 与 LieDiscrete 的对齐: SO(3)→A₄ 是 Aut(T⁶/GF(9)) 的子商
  - 0 postulate.
- **导入 (14)**: `Data.Nat`, `Data.Fin`, `Data.Product`, `Relation.Binary.PropositionalEquality`, `Sovereign.Base.Trit`, `Sovereign.Algebra.Jacobian.jac_Discrete`, `Sovereign.Algebra.Jacobian.jac_Matrix`, `Sovereign.Base.Trit`, `Relation.Binary.PropositionalEquality`, `Sovereign.Algebra.GF9`, `Sovereign.Algebra.Jacobian.jac_GF9Matrix`, `Sovereign.Structology.A4Representations`, `Sovereign.Algebra.LieDiscrete`, `Sovereign.Algebra.LieDiscrete`
- **data 类型**: `C2`
- **record 类型**: `FiniteAutGroup`
- **顶层签名 (20)**: `σ`, `expD`, `expD-id`, `c2-mul`, `c2-order`, `commutator`, `diag-commute`, `sigma-mat`, `sigma-mat-entry-involutive`, `sigma-I2`, `alphaI2`, `sigma-alpha`, `sigma-alphaI2`, `mat2-mul-gf9`, `neg2f`, `Mat2G`, `m2mul`, `sigm2`, `SDElem`, `a4-burnside`
- **质量**: `refl`×20；无 postulate / 无 hole

## `src/Sovereign/Algebra/Jacobian/jac_LinearAlgebra.agda`

- **module**: `Sovereign.Algebra.Jacobian.jac_LinearAlgebra`
- **行数**: 77（代码 51 / 注释 14）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | jac_LinearAlgebra — GF(3) 无零因子 + 行列式秩 + 线性无关
  - 0 postulate
- **导入 (5)**: `Data.Nat`, `Data.Sum`, `Data.Product`, `Relation.Binary.PropositionalEquality`, `Sovereign.Base.Trit`
- **顶层签名 (5)**: `no-zero-divisor`, `cancel-⊗`, `rank-by-det`, `rank2-ok`, `⊗-table`
- **质量**: `refl`×27；无 postulate / 无 hole

## `src/Sovereign/Algebra/Jacobian/jac_Matrix.agda`

- **module**: `Sovereign.Algebra.Jacobian.jac_Matrix`
- **行数**: 7216（代码 7091 / 注释 74）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | Sovereign.Algebra.Jacobian.jac_Matrix
  - GF(3) 上 2×2 矩阵的完整线性代数理论
  - 核心原则：
  - 1. GF(3)有限域上优先穷举法（策略A），利用代数引理压缩case数
  - 2. det(AB)=det(A)det(B) 是核心定理，连接矩阵乘法与行列式
  - 3. 逆矩阵通过伴随矩阵构造：M⁻¹ = (det M)⁻¹·adj(M)
  - 4. 可逆性 ⇔ det≠0（有限域上重言式）
  - 包含：乘法逆元、矩阵运算、行列式乘法性、伴随矩阵、逆矩阵、秩分类
- **导入 (5)**: `Relation.Binary.PropositionalEquality`, `Data.Product`, `Data.Empty`, `Sovereign.Base.Trit`, `Sovereign.Algebra.Jacobian.jac_Discrete`
- **data 类型**: `Rank`
- **顶层签名 (18)**: `inv`, `inv-correct`, `mat-add`, `mat-scale`, `mat-mul`, `mat-vec`, `det-I`, `det-scale`, `det-mul`, `transpose`, `transpose-det`, `adjugate`, `invertible`, `inverse`, `adj-mul-right`, `adj-mul`, `inverse-correct`, `rank`
- **质量**: `refl`×6918；无 postulate / 无 hole

## `src/Sovereign/Algebra/Jacobian/jac_NMatrix.agda`

- **module**: `Sovereign.Algebra.Jacobian.jac_NMatrix`
- **行数**: 174（代码 84 / 注释 60）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | Sovereign.Algebra.Jacobian.jac_NMatrix
  - 函数表矩阵 M_F: det(M_F) ≠ 0 ⟺ F 双射
  - 核心洞察: M_F 每列是标准基向量 (e_{F(j)}).
  - det ≠ 0  ⇔  无全零行  ∧  无相同列     (有限线性代数)
  - 无全零行  ⇔  F 满射                    (§2)
  - 无相同列  ⇔  F 单射                    (§2)
  - 因此 det ≠ 0 ⇔ F 双射                 (§3)
  - 不计算 9×9 行列式; 用 Fin 9 查找表定义矩阵.
  - 0 postulate.
- **导入 (10)**: `Relation.Binary.PropositionalEquality`, `Data.Product`, `Data.Empty`, `Data.Fin`, `Data.Fin.Properties`, `Relation.Nullary`, `Sovereign.Base.Trit`, `Sovereign.Algebra.Jacobian.jac_Discrete`, `Sovereign.Algebra.Jacobian.jac_Pigeonhole`, `Sovereign.Algebra.Jacobian.jac_Injectivity`
- **顶层签名 (7)**: `Mat9`, `toTrit`, `funcTable`, `⇐hit`, `NoZeroRow`, `ColDistinct`, `DetNonzero`
- **质量**: `refl`×5；无 postulate / 无 hole

## `src/Sovereign/Algebra/Jacobian/jac_Pigeonhole.agda`

- **module**: `Sovereign.Algebra.Jacobian.jac_Pigeonhole`
- **行数**: 332（代码 247 / 注释 38）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | Sovereign.Algebra.Jacobian.jac_Pigeonhole
  - 鸽巢原理: GF(3)¹ 上 单射 ⟹ 满射
  - 完全构造性证明, 0 postulate
  - 策略: 显式等式传递 + 9-case 碰撞穷举
  - 元理论对齐: 与 Dvir (2009) 有限域挂谷猜想证明同构 —
  - Dvir 将高维几何重叠还原为多项式空间维数与点集阶数的鸽巢矛盾;
  - 本模块将雅可比逐点条件还原为函数表矩阵的列互异与行列式非零。
  - 参见: docs/Kakeya-元诊断-连续统病态vs离散自愈.md §二
- **导入 (10)**: `Relation.Binary.PropositionalEquality`, `Data.Product`, `Data.Empty`, `Agda.Builtin.Equality.Rewrite`, `Sovereign.Base.Trit`, `Data.Nat`, `Data.Nat.Properties`, `Data.Fin`, `Data.Fin.Properties`, `Function`
- **data 类型**: `Dec`
- **顶层签名 (30)**: `_≢_`, `Inj1`, `Surj1`, `ne01`, `ne02`, `ne12`, `all-miss-T₀`, `all-miss-T₁`, `all-miss-T₂`, `⊥-elim`, `_≟T_`, `pigeonhole-1`, `GF3²`, `Inj2`, `Surj2`, `pair-eq`, `fst²`, `snd²`, `_≟²_`, `encode9`, `decode9`, `encode9-decode9`, `decode9-encode9`, `encode9-injective`, `decode9-injective`, `compress`, `expand`, `expand∘compress`, `nine-miss-⊥`, `pigeonhole-2`
- **REWRITE 规则**: `decode9`
- **质量**: `refl`×41；无 postulate / 无 hole

## `src/Sovereign/Algebra/Jacobian/jac_Topology.agda`

- **module**: `Sovereign.Algebra.Jacobian.jac_Topology`
- **行数**: 160（代码 51 / 注释 78）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | Sovereign.Algebra.Jacobian.jac_Topology
  - 离散代数拓扑 — 三角复形同调与欧拉恒等式 (解析证法, 0 postulate)
  - 核心定理:
  - §1. 三角复形边界算子 (循环置换的 3×3 GF(3) 矩阵)
  - §2. 核计算: 证明 ker ∂ = ((T₁,T₁,T₁)) — 一维子空间
  - §3. 秩-零度: rank ∂ = 2, nullity = 1, rank+nullity = dim = 3
  - §4. 同调: dim H₀ = 3−rank = 1, dim H₁ = nullity = 1
  - §5. 欧拉恒等式: χ = dim C₀−dim C₁ = 3−3 = 0 = dim H₀−dim H₁ = 1−1
  - §6. 桥接: 同调消失 ⟺ nullity=0 ∧ rank=3 ⟺ F双射 ⟺ det(M_F)≠0
  - 0 postulate. 全部解析证法, 不用穷举.
- **导入 (5)**: `Data.Nat`, `Data.Fin`, `Data.Product`, `Relation.Binary.PropositionalEquality`, `Sovereign.Base.Trit`
- **顶层签名 (22)**: `GF3Vec`, `0v`, `boundary3`, `⊗-verify`, `const1`, `const1-ker0`, `const1-ker1`, `const1-ker2`, `const1-in-kernel`, `rank-proof`, `rank∂-ge-2`, `rank∂`, `nullity∂`, `dimH0`, `dimH1`, `rank-nullity-ok`, `dimC0`, `dimC1`, `χ-complex`, `χ-homology`, `euler-identity`, `euler-zero`
- **质量**: `refl`×13；无 postulate / 无 hole
