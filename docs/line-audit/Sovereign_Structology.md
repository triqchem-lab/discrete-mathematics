# 目录 `src/Sovereign/Structology/` 逐模块审计记录

共 64 个模块。


## `src/Sovereign/Structology/A4Group.agda`

- **module**: `Sovereign.Structology.A4Group`
- **行数**: 662（代码 452 / 注释 150）
- **OPTIONS**: `--rewriting --cubical --guardedness`
- **头部注释（数学背景）**:
  - | Sovereign.Structology.A4Group
  - 结构学：A₄ 群（正四面体旋转对称群）
  - A₄ = 正四面体旋转群 = 交错群 Alt(4)，12 阶非交换，是三代费米子对称群。
  - 结构: A₄ ≅ V₄ ⋊ C₃（半直积，非直积）。
  - 它包含 12 个元素，对应正四面体的 12 个旋转操作，作用在 12 条有向边（十二律）上。
  - ⚠️ 概念澄清 (2026-08-19 定稿):
  - A₄ 是十二律的对称群（群作用），不是「十二进制」本体——本体是
  - DuodecClock.agda 的加乘联合周期 Z/3⊕⟨α⟩（交换）。
  - A₄ 与 Z/12 同为 12 阶但不同构（A₄ 非交换）。禁挂「A₄ ≅ Z/12」。
  - 群作用引理（正则表示/消去律/非交换）见 A4GroupAction.agda。
- **导入 (5)**: `Data.Fin`, `Data.Nat`, `Data.Vec`, `Data.Product.Base`, `Cubical.Foundations.Prelude`
- **data 类型**: `A4`
- **顶层签名 (16)**: `perm`, `_∘ₚ_`, `fromPerm`, `fromPerm-perm`, `_⊗_`, `perm-hom`, `assoc`, `identity`, `inverse`, `TwelveTones`, `labelToPair`, `pairToLabel`, `A4Action`, `actionIdentity`, `actionCompose`, `generatorC3`
- **质量**: `refl`×681；无 postulate / 无 hole

## `src/Sovereign/Structology/A4GroupAction.agda`

- **module**: `Sovereign.Structology.A4GroupAction`
- **行数**: 239（代码 133 / 注释 74）
- **OPTIONS**: `--rewriting --cubical --guardedness`
- **头部注释（数学背景）**:
  - | Sovereign.Structology.A4GroupAction
  - A₄ 群作用 — 正则表示、消去律、传递/自由、非交换（与十二进制严格分离）
  - A₄ = 正四面体旋转群 = 交错群 Alt(4)，12 阶非交换，是三代费米子对称群。
  - 结构: A₄ ≅ V₄ ⋊ C₃（半直积，非直积）
  - · V₄ = 克莱因四元群（3 个二重对换 Flip + 单位元 Id，A₄ 的正规子群）
  - · C₃ = 商群 A₄/V₄（三进制归零的三角循环）
  - ⚠️ 概念分离（防「传统污染」）:
  - 本模块只研究 A₄ 自身的群作用，不引用十二进制（Duodec/Z/12 的联合周期）。
  - A₄ 与 Z/12 同为 12 阶但不同构：A₄ 非交换，Z/12 交换。
  - 禁挂「A₄ ≅ Z/12」或「A₄ 是十二进制」，禁「对偶」一词——只说「不同构」。
  - 唯一的交叉是 §5 的「无单射同态」否定性引理（证明不能嵌入，而非建立同构）。
  - 核心定理（0 postulate，L2 符号证明 + 有限穷举兜底）:
  - §1  消去律（右/左）—— 由逆元 + 结合律导出，全称符号证明
  - §2  正则作用（左乘）自由 + 传递 —— Cayley 正则表示实例
  - §3  正则表示忠实（作用在单位元处决定群元）
  - §4  V₄ 子群注记（二重对换 Flip 均为 2 阶）—— V₄ ⋊ C₃ 的 V₄
  - §5  A₄ 非交换（两个 3-循环/对换不交换的逐点见证）
- **导入 (8)**: `Data.Nat`, `Data.Fin`, `Data.Empty`, `Data.Product.Base`, `Data.Unit`, `Cubical.Foundations.Prelude`, `Sovereign.Structology.A4Group`, `Sovereign.Algebra.Duodecimal`
- **顶层签名 (19)**: `a4-inv`, `a4-inv-right`, `a4-inv-left`, `right-cancel`, `left-cancel`, `regular-free`, `regular-transitive`, `orbit-stabilizer-identity`, `regular-faithful`, `flip-order-2`, `rot-not-id`, `rot-not-order-2`, `rot-flip-at-zero`, `flip-rot-at-zero`, `fin4-2≢1`, `non-abelian-witness`, `not-commutative`, `+12-commᶜ`, `no-injective-hom`
- **质量**: `refl`×178；无 postulate / 无 hole

## `src/Sovereign/Structology/A4OneDimHom.agda`

- **module**: `Sovereign.Structology.A4OneDimHom`
- **行数**: 265（代码 210 / 注释 34）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | Sovereign.Structology.A4OneDimHom
  - A₄ 一维表示的同态构造 — 从 abelianization 推导特征标 (0 postulate)
  - 深度证明 (第一步): A₄ 的三个一维表示 (ρ₁, ρ₁′, ρ₁″) 不是手写特征标,
  - 而是从 abelianization 映射 ab : A₄ → C₃ (Fin 3) 复合 ω 的幂得到:
  - ρ₁′(g) = ω^(ab g),  ρ₁″(g) = ω²^(ab g)
  - 同态性 ρ₁′(g⊗h) = ρ₁′(g)·ρ₁′(h) 由两个引理推出:
  - ab-hom:        ab(g⊗h) = ab g + ab h        (C₃ 同态, 12×12 穷举)
  - omega-pow-mul: ω^a · ω^b = ω^(a+b)          (9 情形 refl)
  - 本模块先落 omega-pow-mul (纯 Z[ω] 代数, 独立于群), ab-hom 穷举随后。
- **导入 (5)**: `Data.Fin`, `Relation.Binary.PropositionalEquality`, `Sovereign.Structology.A4Representation`, `Data.Fin`, `Sovereign.Structology.A4Group`
- **顶层签名 (6)**: `add3`, `powerω`, `omega-pow-mul`, `ab`, `ρ1`, `ab-hom`
- **质量**: `refl`×158；无 postulate / 无 hole

## `src/Sovereign/Structology/A4Orbits3.agda`

- **module**: `Sovereign.Structology.A4Orbits3`
- **行数**: 144（代码 85 / 注释 44）
- **OPTIONS**: `--rewriting`
- **头部注释（数学背景）**:
  - 本模块是 HFM 交叉验证测试向量, 不替代原形式化证明。
  - 主证明见: A4Representations.agda, BurnsideT6.agda
  - | Sovereign.Structology.A4Orbits3
  - A₄ 三维不可约表示在 GF(3)³ (=27 点) 上的 Burnside 轨道计数
  - HFM 交叉验证 (test/FinalVerify.hs):
  - A₄ 在 GF(3)³ 上: Burnside 和 = 60, 轨道 = 5
  - 不动点: 恒等 27, 双对换 3, 3-循环 3
  - 数学原理:
  - A₄ 的三维不可约表示 V₃ (A4Representations.agda) 的特征标:
  - χ₄ = (3, -1, 0, 0)
  - 这是在 ℂ 上的特征标值。在 GF(3) 上,
  - V₃ 等同于 GF(3)⁴ 中 v₀+v₁+v₂+v₃=0 子空间。
  - A₄ 在 GF(3)⁴ 上置换 4 个坐标, 限制到 sum=0 得 V₃。
  - 不动点计数 (在 GF(3)³ 上):
  - 恒等: 全部 27 = 3³ 点不动
  - 双对换 (如 (12)(34)): v₀=v₁=v₂=v₃ 在 sum=0 中
  - → 4v₀ ≡ 0 → v₀ 自由, 但要求 v₀=v₁=v₂=v₃
- **导入 (3)**: `Data.Nat`, `Relation.Binary.PropositionalEquality`, `Relation.Binary.PropositionalEquality`
- **顶层签名 (14)**: `fix-identity`, `fix-double-transposition`, `fix-3cycle`, `burnside-sum`, `burnside-sum-correct`, `orbit-count`, `orbit-count-correct`, `orbit-count-factor-check`, `small-orbit-size`, `small-orbit-count`, `large-orbit-size`, `large-orbit-count`, `orbit-decomposition-sum`, `total-points-verified`
- **质量**: `refl`×1；无 postulate / 无 hole

## `src/Sovereign/Structology/A4Representation.agda`

- **module**: `Sovereign.Structology.A4Representation`
- **行数**: 247（代码 150 / 注释 52）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | Sovereign.Structology.A4Representation
  - A₄ 表示论: 不可约表示 {1, 1′, 1″, 3} + 特征标正交性 (0 postulate, 全 refl)
  - 三代费米子的代数起源: A₄ 的三维不可约表示在 Z₃ 子群上分支为
  - 1 ⊕ 1′ ⊕ 1″ — 三代不是可调参数, 而是 A₄ 群结构的刚性预测。
  - 诚实边界 (必须记录): A₄ 的 ω 特征需要 3 阶元素 (ω³=1), 而 GF(9) 的
  - 非零元是 8 阶循环群 (3∤8), 无 3 阶元素。因此本模块工作在 Z[ω] 环
  - (特征 0) 上, 与 GF(9) 的 Frobenius 共轭 (4 阶) 各自服务不同目的:
  - GF(9) 负责 Frobenius 共轭 (4 阶, E⊥B 90°)
  - Z[ω]  负责 A₄ 的 3 阶对称 (三代费米子)
  - 两者不可互相替代。
- **导入 (5)**: `Data.Nat`, `Data.Integer.Base`, `Data.Fin`, `Data.Product`, `Relation.Binary.PropositionalEquality`
- **record 类型**: `Zω`
- **顶层签名 (28)**: `zeroZω`, `oneZω`, `ω`, `ω²`, `addZω`, `negZω`, `subZω`, `mulZω`, `conjZω`, `omega-sum-zero`, `omega-cubed`, `omega-squared-form`, `ConjClass`, `Irrep`, `classSize`, `chi1`, `chi3`, `chi`, `dim-squared-sum`, `colInnerProduct`, `column-orth-diag`, `column-orth-offdiag`, `rowInnerProduct`, `row-orth-diag`, `row-orth-offdiag`, `chi-perm`, `perm-decompose`, `branching-Z3`
- **质量**: `refl`×45；无 postulate / 无 hole

## `src/Sovereign/Structology/A4Representations.agda`

- **module**: `Sovereign.Structology.A4Representations`
- **行数**: 886（代码 700 / 注释 95）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | Sovereign.Structology.A4Representations
  - A₄ 群的不可约表示理论 (补强版, 2026-08, 0 postulate)
  - 核心结果:
  - 1. A₄ 有恰好 4 个共轭类: C₁(1), C₂(4), C₃(4), C₄(3)
  - 2. 四个特征标 {3, 1, 1′, 1″} 满足完整第一正交关系 (4×4 全 16 项):
  - ⟨χᵢ, χⱼ⟩ = Σ_C |C|·χᵢ(C)·conj(χⱼ(C)) = 12·δᵢⱼ — char-orthogonality
  - 3. 维数平方和: 3² + 1² + 1² + 1² = 12 = |A₄|
  - 4. V₃ = 置换表示去掉全对称分量: 三个基向量 sum=0 (basisSumZero),
  - 置换作用保持坐标和 (sumZero-invariant, 13 case 显式),
  - 特征标分解 χ_perm = χ₁ + χ₃ (perm-char-decomp)
  - 5. V₁, V₁′, V₁″ = 通过 Abel 化 A₄/V₄ ≅ C₃ 拉回的三个特征标,
  - 全部为群同态 (multiplicative, abelianize-hom 144 case) 且两两相异
  - 6. 三代费米子 = 三个一维特征标 (singlets) + 三维标准表示 (triplet)
  - 诚实边界:
  - (a) 经典定理 ⟨χ,χ⟩=|G| ⟺ 不可约 (第一正交关系 → 不可约) 是有限群
  - 特征标理论的引用结果, 不在本库内落链; 本模块验证的是该判据的
  - 计算侧: 全部四个 ⟨χᵢ,χᵢ⟩ ≡ 12 (irrep-norm-criterion)。
  - (b) "三代费米子是必然的"的物理对应 (A₄ 味对称 ↔ Altarelli-Feruglio)
- **导入 (9)**: `Data.Nat`, `Data.Integer`, `Data.Integer.Properties`, `Data.Fin`, `Data.Vec`, `Data.Product`, `Relation.Binary.PropositionalEquality`, `Sovereign.Structology.A4Group`, `Sovereign.RootMath.Eisenstein`
- **data 类型**: `ConjugacyClass`, `A4Irrep`, `C3Group`
- **record 类型**: `FermionGenerations`
- **顶层签名 (59)**: `encodeA4`, `classSize`, `classSizeSum`, `lookup-class`, `classify`, `dim`, `dimSqSum`, `charAt`, `character`, `eis12`, `classSizeᵉ`, `inner`, `kronecker12`, `char-orthogonality`, `irrep-norm-criterion`, `χ₃-values`, `χ₁-values`, `character-at-identity`, `chars-distinct`, `V3basis1`, `V3basis2`, `V3basis3`, `sumVec4`, `basisSumZero`, `act`, `swap34`, `swap01`, `rot3cw`, `rot3ccw`, `fix0-cw`, `fix0-ccw`, `fix1-cw`, `fix1-ccw`, `fix2-cw`, `fix2-ccw`, `fix3-cw`, `fix3-ccw`, `flip01`, `flip02`, `flip03`, `sumZero-invariant`, `act-preserves-L`, `fixCountC`, `fixChar`, `perm-char-decomp-c`, `perm-char-decomp`, `lookup-abel`, `abelianize`, `c3Char`, `c3Char-hom`, `abelianize-hom`, `a4inv`, `classify-conjugation-invariant`, `branching3`, `χ₁-multiplicative`, `theorem-dimension-sum-of-squares`, `theorem-class-count`, `theorem-dim-sum-eq-class-sum`, `standardFermionAssignment`
- **质量**: `refl`×355；无 postulate / 无 hole

## `src/Sovereign/Structology/A4ThreeDimRep.agda`

- **module**: `Sovereign.Structology.A4ThreeDimRep`
- **行数**: 267（代码 210 / 注释 36）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | Sovereign.Structology.A4ThreeDimRep
  - A₄ 三维不可约表示 ρ₃ 的构造 + 同态证明 (0 postulate)
  - 深度证明 (最后一步): 三代费米子的代数起源 = "3 维表示" 不再手写特征标,
  - 而是从置换表示 (4 顶点) 限制到 V₀ = {x | Σxᵢ = 0} 导出:
  - 基 b₁=(1,-1,0,0), b₂=(0,1,-1,0), b₃=(0,0,1,-1)
  - ρ₃(g) 的列 j = perm(g)·bⱼ 在 {b₁,b₂,b₃} 下的整数坐标
  - 矩阵元 ∈ {-1,0,1} ⊂ Z[ω], 迹 = χ₃ (3,0,0,-1), Python 已核验 144 同态。
  - 至此 A₄ 全部 4 个不可约表示的特征标均由构造导出:
  - ρ₁ (平凡)      — A4Representation / 显式
  - ρ₁′, ρ₁″ (1 维) — A4OneDimHom (ω 幂 ∘ abelianization)
  - ρ₃ (3 维)       — 本模块 (V₀ 限制, 迹即 χ₃)
- **导入 (8)**: `Data.Fin`, `Data.Integer`, `Data.Product`, `Data.Vec`, `Relation.Binary.PropositionalEquality`, `Sovereign.Structology.A4Group`, `Sovereign.Structology.A4Representation`, `Sovereign.Structology.MatrixZω`
- **顶层签名 (9)**: `rho3`, `rho3-hom`, `classOf`, `chi3FromRep`, `rho3-identity`, `chi3-id`, `chi3-3cycle`, `chi3-double-transposition`, `chi3-values`
- **质量**: `refl`×167；无 postulate / 无 hole

## `src/Sovereign/Structology/Aether.agda`

- **module**: `Sovereign.Structology.Aether`
- **行数**: 356（代码 185 / 注释 118）
- **OPTIONS**: `--guardedness --rewriting`
- **头部注释（数学背景）**:
  - | Sovereign.Structology.Aether
  - 结构学：以太——T⁶ 离散环面格点基底
  - 本质：主权 LCM 商空间的格点全集
  - 极向 144 与环向 46 的全息展开
  - 注意：以太本身不演化，演化的是主权状态机的缠绕数与虚实比
- **导入 (18)**: `Data.Nat`, `Data.Nat.DivMod`, `Data.Nat.Properties`, `Data.Fin`, `Data.Fin.Properties`, `Data.Vec`, `Data.Vec.Properties`, `Data.Integer`, `Data.List`, `Relation.Binary.PropositionalEquality`, `Relation.Binary.PropositionalEquality.Properties`, `Data.Product`, `Data.Unit`, `Data.Empty`, `Relation.Nullary`, `Sovereign.Structology.T6`, `Sovereign.Structology.Winding`, `Sovereign.Coupling.LossGain`
- **record 类型**: `Aether`, `MagicSquareContainer`, `DiscreteConnection`, `DiscreteGeodesic`, `ContinuousMedium`
- **顶层签名 (24)**: `allLatticePoints`, `standardAether`, `aetherLatticeSize`, `standardContainer`, `containerSumCorrect`, `containerIsAetherProjection`, `gf3`, `gf3-toℕ-id`, `latticeIndex`, `allLatticePointsComplete`, `parallelTransport`, `transportStaysInAether`, `geodesicLengthEqualsLatticeDiff`, `buildPathFromChain`, `trivialGeodesic`, `trivialGeodesicFromChain`, `geodesicDeterminedByLossGain`, `aetherChernNumber`, `aetherChernIs2`, `aetherEnergyGap`, `chernGapInvariant`, `AetherDefinition`, `T6DiscreteTorusLatticeBase`, `aetherLegal`
- **质量**: `refl`×15；⚠️ 2 postulate

## `src/Sovereign/Structology/ArthurMagicSquare.agda`

- **module**: `Sovereign.Structology.ArthurMagicSquare`
- **行数**: 153（代码 76 / 注释 39）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - 【术语边界】本模块「幻方」= 数学数字幻方（行列对角线和相等）。
  - 非卢先生「矢量方向/变量计数」幻方（阶数 = 同时在变的矢量方向个数）。
  - 辨析与知识库依据见 docs/cross-level/magic-square-terminology.md
- **导入 (6)**: `Data.Fin`, `Data.Product`, `Relation.Binary.PropositionalEquality`, `Sovereign.Base.Trit`, `Sovereign.Algebra.GF9`, `Sovereign.Structology.A4Group`
- **顶层签名 (24)**: `Matrix4`, `zeroMatrix`, `sum4`, `rowSum`, `colSum`, `diagSum`, `antiDiagSum`, `IsRowConstant`, `IsColConstant`, `DiagMatchesRow`, `IsClassicalMagicSquare`, `a4ActionOnMatrix`, `IsA4EquivariantRowSum`, `v₄f₂`, `v₄f₃`, `IsV4DiagInvariant`, `IsArthurMagicSquare`, `zeroMatrix-isRowConst`, `zeroMatrix-isColConst`, `zeroMatrix-diagMatches`, `zeroMatrix-isClassical`, `zeroMatrix-a4Equiv`, `zeroMatrix-v4Diag`, `zeroMatrix-isArthur`
- **质量**: `refl`×13；无 postulate / 无 hole

## `src/Sovereign/Structology/BinaryTetrahedral.agda`

- **module**: `Sovereign.Structology.BinaryTetrahedral`
- **行数**: 621（代码 384 / 注释 157）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | Sovereign.Structology.BinaryTetrahedral
  - 二元四面体群 2A₄ — A₄ 在 SU(2) 中的非平凡中心扩张
  - 核心结构:
  - 2A₄ ≅ Q₈ ⋊ C₃ (半直积, 非直积 A₄ × Z₂)
  - 1 → Z₂ → 2A₄ → A₄ → 1 (非平凡中心扩张)
  - 【本体衔接】上述「中心扩张 Z₂」是标准群论描述 (数学事实, 非诠释)。
  - 离散全息/斯瓦鲁本体读法: Z₂ ≅ Gal(GF(9)/GF(3)) ≅ ⟨σ⟩ (σ(x)=x³, σ(α)=-α),
  - 故「中心 −1」是 Frobenius 共轭 σ 对全群的投影, 2A₄ = 两个 A₄ 的共轭展开,
  - 非「外加中心/对偶/对称」。本模块代码是群论层的, 二者兼容 (同一 C₂ 两种读法)。
  - 关键定理:
  - 1. |2A₄| = 24 = |Q₈| × |C₃| = 8 × 3
  - 2. Z(2A₄) = {(1,c₀), (-1,c₀)} ≅ Z₂
  - 3. 2A₄/Z₂ ≅ A₄ (商映射核 = Z₂)
  - 4. 2A₄ ≢ A₄ × Z₂ (非平凡性: order-2 元素的提升有 order 4)
  - 5. 7 个不可约表示: dim ∈ {1,1,1,2,2,2,3}, Σdim² = 24
  - 证明策略: 穷举法 (Q₈ 8元素, C₃ 3元素, 2A₄ 24元素)
- **导入 (5)**: `Data.Nat`, `Data.Product`, `Data.Empty`, `Data.Sum`, `Relation.Binary.PropositionalEquality`
- **data 类型**: `Q8`, `C3G`, `V4El`, `BTIrrep`
- **record 类型**: `BT`
- **顶层签名 (57)**: `negQ`, `negQ-involutive`, `q8-i²`, `q8-j²`, `q8-k²`, `q8-ij≡k`, `q8-jk≡i`, `q8-ki≡j`, `q8-ji≡mk`, `q8-kj≡mi`, `q8-ik≡mj`, `q8-neg1-central`, `q8-neg1²`, `q8-i⁴`, `c3-identity`, `c3-identityʳ`, `c3-ω³≡1`, `c3-assoc`, `act`, `act-neg1`, `act-1`, `act-ω³`, `act-hom-ij`, `act-hom-jk`, `act-hom-ki`, `act-hom-i²`, `bt-id`, `c-inv`, `qInv`, `bt-inv`, `bt-card`, `bt-card≡24`, `q1-left-id`, `q-right-id`, `bt-id-left`, `bt-id-right`, `bt-right-inv`, `center-neg1-commutes`, `center-i-not`, `qk≠qmk`, `bt-i-sq`, `bt-neg1≠id`, `bt-i⁴`, `bt-i≠id`, `bt-i²≠id`, `projV4`, `quotient`, `kernel-id`, `kernel-neg1`, `projV4-kernel`, `quotient-neg`, `quotient-card`, `btDim`, `btDimSqSum`, `btIrrepCount`, `a4-irrep-count`, `bt-more-irreps`
- **质量**: `refl`×136；无 postulate / 无 hole

## `src/Sovereign/Structology/BinaryTetrahedralDefiningRep.agda`

- **module**: `Sovereign.Structology.BinaryTetrahedralDefiningRep`
- **行数**: 187（代码 135 / 注释 30）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | Sovereign.Structology.BinaryTetrahedralDefiningRep
  - 2·A₄ = SL(2,3) 定义表示: 从 GF(3) 矩阵导出 χ₂ (0 postulate)
  - 【重要更正】此前计划用 Z[ω,i] 上生成元 a=diag(ω,ω²)、b=[[0,1],[-1,0]] 生成 24 阶群:
  - Python 枚举证明 ⟨a,b⟩ 只有 12 阶, 且 ⟨a,b,c=diag(i,-i)⟩ 虽 24 阶却含 12 阶元素
  - (迹含 i), 不是 SL(2,3)。SL(2,3) 的 Z 值二维不可约表示 χ₂ 是 GF(3) 上的定义表示:
  - SL(2,3) = { 2×2 矩阵 over GF(3) | det = 1 }, 24 元素, 阶 ∈ {1,2,3,4,6}。
  - 深度推导: 特征标 χ₂ 由「阶数」(即特征值结构) 决定, 非手写:
  - 阶 1 → 2,  阶 2 → -2,  阶 3 → -1 (特征值 ω,ω²),
  - 阶 4 → 0 (特征值 i,-i),  阶 6 → 1 (特征值 -ω,-ω²)。
  - 这正是「从表示推导特征标」, 与 BinaryTetrahedralRepresentation 的手写表一致 (24 refl)。
- **导入 (6)**: `Data.Nat`, `Data.Fin`, `Data.Product`, `Relation.Binary.PropositionalEquality`, `Sovereign.Structology.A4Representation`, `Sovereign.Structology.BinaryTetrahedralRepresentation`
- **data 类型**: `SL23`
- **顶层签名 (11)**: `orderOf`, `classOf`, `lift`, `chi2FromRep`, `chi2-correct`, `chi2-order1`, `chi2-order2`, `chi2-order3`, `chi2-order4`, `chi2-order6`, `chi2-values`
- **质量**: `refl`×37；无 postulate / 无 hole

## `src/Sovereign/Structology/BinaryTetrahedralHFM.agda`

- **module**: `Sovereign.Structology.BinaryTetrahedralHFM`
- **行数**: 123（代码 72 / 注释 36）
- **OPTIONS**: `--rewriting`
- **头部注释（数学背景）**:
  - 本模块是 HFM 交叉验证测试向量, 不替代原形式化证明。
  - 主证明见: BinaryTetrahedral.agda
  - | Sovereign.Structology.BinaryTetrahedralHFM
  - Q₈ 置换群构造 + 2A₄ ≅ Q₈ ⋊ C₃ 的 HFM 交叉验证
  - HFM 验证 (test/Construct2A4.hs, test/Semidirect.hs):
  - Q₈ 通过左正则表示嵌入 S₈: |Q₈|=8, |Z(Q₈)|=2
  - 生成元: i=(1 2 3 4)(5 7 6 8), j=(1 5 3 6)(2 8 4 7)
  - dp Q₈ C₃ 生成 24 元素 (直积, 与半直积阶相同)
  - 数学原理:
  - Q₈ (四元数群, 8 元素):
  - 生成元 i, j, 满足 i⁴=1, i²=j²=k²=-1, ij=k
  - 中心 Z(Q₈) = {1, -1} ≅ Z₂
  - 2A₄ (二元四面体群, 24 元素):
  - Q₈ ⋊ C₃ 半直积, C₃ 通过外自同构 ω 作用在 Q₈ 上:
  - ω(i)=j, ω(j)=k, ω(k)=i
  - 2A₄/Z₂ ≅ A₄ (中心扩张)
- **导入 (3)**: `Data.Nat`, `Relation.Binary.PropositionalEquality`, `Relation.Binary.PropositionalEquality`
- **顶层签名 (13)**: `sizeQ8`, `sizeC3`, `sizeA4`, `size2A4`, `sizeCenter`, `irrepCount`, `sizeQ8-ok`, `size2A4-ok`, `sizeCenter-ok`, `sumDimSq2A4`, `sumDimSq2A4-ok`, `sumDimSqA4`, `sumDimSqA4-ok`
- **质量**: `refl`×1；无 postulate / 无 hole

## `src/Sovereign/Structology/BinaryTetrahedralIrreducibility.agda`

- **module**: `Sovereign.Structology.BinaryTetrahedralIrreducibility`
- **行数**: 84（代码 33 / 注释 34）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | Sovereign.Structology.BinaryTetrahedralIrreducibility
  - 2·A₄ = SL(2,3) 推导特征标不可约性重证: ⟨χ,χ⟩ = 1 (item 5, 0 postulate)
  - 核心原则:
  - ① 离散形式: ⟨χ,χ⟩ = (1/|G|) Σ_c |c|·χ(c)·χ̄(c) 不用有理数/浮点,
  - 证明层锁其整数恒等式 ⟨χ,χ⟩·|G| = Σ ≡ 24 = |G| (⟨χ,χ⟩=1 ⟺ Σ=|G|·1)
  - ② 对象是「推导特征标」: χ₂ 由阶数导出 (DefiningRep),
  - χ₂′ = χ₂⊗χ₁′, χ₂″ = χ₂⊗χ₁″ 由张量积导出 (TwoDimTensors.chi2'-tensor)
  - ③ 全 refl 归约穷举 (7 类 × 3 特征标), Zω 算术闭值归约
  - ④ 命名层: 除法 24/24=1 的表述留在注释, 不进证明链
  - 包含: scaleZω/term/inner-num 定义, classSizes-sum (Σ|c|=24),
  - chi2-irreducible / chi2'-irreducible / chi2''-irreducible
  - 数值预验证: sov-math/sov-validation/src/chi_inner.rs (cargo test 通过)
- **导入 (6)**: `Data.Nat`, `Data.Fin`, `Data.Integer`, `Relation.Binary.PropositionalEquality`, `Sovereign.Structology.A4Representation`, `Sovereign.Structology.BinaryTetrahedralRepresentation`
- **顶层签名 (6)**: `classSizes-sum`, `scaleZω`, `term`, `inner-num`, `group-order`, `chi2-irreducible`
- **质量**: `refl`×6；无 postulate / 无 hole

## `src/Sovereign/Structology/BinaryTetrahedralRepresentation.agda`

- **module**: `Sovereign.Structology.BinaryTetrahedralRepresentation`
- **行数**: 206（代码 103 / 注释 72）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | Sovereign.Structology.BinaryTetrahedralRepresentation
  - 二元四面体群 2·A₄ = SL(2,3) 表示论 — 三代(3阶)与 Frobenius(4阶)之桥 (0 postulate)
  - 【本体修正】2·A₄ 的物理图像 = 两个 A₄ 的 Frobenius 共轭展开, 非中心扩张/对偶/对称。
  - * 标准群论 (数学事实): A₄ 的二重复盖, 中心 Z₂ = {±1}。
  - * 离散全息/斯瓦鲁本体: 同一个手征旋转, 在两个旋向 (CW/CCW) 上的完整共轭实现。
  - 中心 Z₂ ≅ Gal(GF(9)/GF(3)) ≅ ⟨σ⟩ (σ(x)=x³, σ(α)=-α),
  - 故「中心 −1」是 Frobenius 共轭 σ 对全群的投影, 不是外加的实体。
  - 2·A₄ (24 阶) 同时拥有:
  - 3 阶元素 (三个循环, 三代 = 三个驻波构型, 来自 A₄)
  - 4 阶元素 (四元数单位 ±i,±j,±k = σ 共轭的周期/代数载体)
  - 手征 σ (Frobenius 共轭, 交换两个 A₄)
  - 7 个共轭类 (大小 1,1,4,4,4,4,6), 7 个不可约表示 (维度 1,1,1,2,2,2,3):
  - σ 不变 (σ 特征 +1, A₄ 的提升): χ₁,χ₁′,χ₁″,χ₃
  - σ 反变 (σ 特征 -1, 新的二维表示): χ₂,χ₂′,χ₂″
  - 共轭展开的物理读法 (不进入证明链, 证明只及特征标代数):
  - 类1(-1) 上的特征标分裂 {1,1,1,3} vs {-2,-2,-2} = 手征共轭的标志。
- **导入 (6)**: `Data.Nat`, `Data.Integer.Base`, `Data.Fin`, `Data.Product`, `Relation.Binary.PropositionalEquality`, `Sovereign.Structology.A4Representation`
- **顶层签名 (14)**: `ConjClass2A4`, `classSize2A4`, `central-minus-one`, `z-neg-one`, `z-two`, `z-neg-two`, `z-three`, `chi1-2A4`, `chi2-2A4`, `chi3-2A4`, `dim-squared-sum-2A4`, `central-decomposition`, `fourfold-structure`, `threefold-preserved`
- **质量**: `refl`×18；无 postulate / 无 hole

## `src/Sovereign/Structology/BinaryTetrahedralSpectrum.agda`

- **module**: `Sovereign.Structology.BinaryTetrahedralSpectrum`
- **行数**: 118（代码 68 / 注释 28）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | Sovereign.Structology.BinaryTetrahedralSpectrum
  - 谱的显式处理: 阶 → 特征值 → 迹 = 特征标 (0 postulate)
  - 填补表示论缺口「谱定理的有限域版」: 有限群表示的特征值由元素阶数决定,
  - 特征标 = 特征值之和。SL(2,3) 二维定义表示的特征值:
  - 阶 1 → {1,1},  阶 2 → {-1,-1},  阶 3 → {ω,ω²},
  - 阶 4 → {i,-i},  阶 6 → {-ω,-ω²}
  - 特征值之和 (迹) 落在 Z[ω] (i 分量相消), 即 χ₂。
  - 本模块把特征值显式写出 (在 Z[ω,i] 中), 证明其和 = 由阶数推导的 χ₂,
  - 使 Zωi 环落到其本来的用途 (4 阶元素的 ±i 特征值)。
- **导入 (7)**: `Data.Nat`, `Data.Integer.Base`, `Data.Product`, `Relation.Binary.PropositionalEquality`, `Sovereign.Structology.Zωi`, `Sovereign.Structology.A4Representation`, `Sovereign.Structology.BinaryTetrahedralDefiningRep`
- **顶层签名 (12)**: `ω²Zωi`, `spectrum`, `sumSpectrum`, `embed`, `omega-sum-neg-one`, `i-sum-zero`, `negomega-sum-one`, `spectrum-correct`, `omega-sum`, `i-sum`, `negomega-sum`, `spectrum-summary`
- **质量**: `refl`×34；无 postulate / 无 hole

## `src/Sovereign/Structology/BinaryTetrahedralTwoDimTensors.agda`

- **module**: `Sovereign.Structology.BinaryTetrahedralTwoDimTensors`
- **行数**: 69（代码 34 / 注释 23）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | Sovereign.Structology.BinaryTetrahedralTwoDimTensors
  - 2·A₄ 的另外两个二维不可约表示: χ₂′ 与 χ₂″ 的张量积推导 (0 postulate)
  - 深度证明 (与 BinaryTetrahedralDefiningRep 组成完整链):
  - χ₂  = 定义表示 (GF(3) 矩阵, 阶数 → 迹)     [BinaryTetrahedralDefiningRep]
  - χ₂′ = χ₂ ⊗ χ₁′  (定义表示 ⊗ ω 特征)       [本模块]
  - χ₂″ = χ₂ ⊗ χ₁″  (定义表示 ⊗ ω² 特征)      [本模块]
  - 其中 χ₁′、χ₁″ 是一维表示 (abelianization A₄→C₃ 的 ω、ω² 特征, 见 A4OneDimHom)。
  - 故三个二维不可约表示的特征标均由构造导出, 不再是手写表:
  - 二维表示 ≅ 定义表示 ⊗ {1, χ₁′, χ₁″} (三维张量积分解)。
  - Z[ω,i] 的 i 分量在迹中消去, 特征标落在 Z[ω]。
- **导入 (4)**: `Data.Fin`, `Relation.Binary.PropositionalEquality`, `Sovereign.Structology.A4Representation`, `Sovereign.Structology.BinaryTetrahedralRepresentation`
- **质量**: `refl`×22；无 postulate / 无 hole

## `src/Sovereign/Structology/BurnsideT6.agda`

- **module**: `Sovereign.Structology.BurnsideT6`
- **行数**: 201（代码 105 / 注释 43）
- **OPTIONS**: `--rewriting`
- **导入 (8)**: `Data.Nat`, `Relation.Binary.PropositionalEquality`, `Data.Product`, `Data.Empty`, `Sovereign.Base.Trit`, `Sovereign.Algebra.GF9`, `Sovereign.Structology.Winding`, `Sovereign.Structology.MagicSquare144`
- **顶层签名 (54)**: `c3-gf9`, `c3²-gf9`, `c2-gf9`, `c3-c2-commute`, `c3²-c2-commute`, `c3-gf9³`, `c2-gf9²`, `c3-cw-no-fix`, `c3-ccw-no-fix`, `c3-no-fixpoint`, `c3²-no-fixpoint`, `c2-fixpoint-char`, `c3sig-no-fixpoint`, `c3²sig-no-fixpoint`, `G-Order`, `gorder-verify`, `fix-id`, `fix-c3`, `fix-c3²`, `fix-sig`, `fix-c3sig`, `fix-c3²sig`, `burnside-sum-gf9`, `burnside-sum-gf9-verify`, `gf9-orbit-count`, `gf9-burnside-equation`, `gf9-orbit-value`, `burnside-orbit-t6`, `burnside-t6-equation`, `burnside-orbit-t6-value`, `burnside-sum-t6`, `burnside-sum-t6-verify`, `burnside-t6-full`, `Merkaba-24`, `Water-36`, `Wuxing-5`, `4320D-factor-decomposition`, `independent-info-from-yao`, `yao-4320`, `both-paths-to-4320`, `gf3³-size`, `gf3³-size-verify`, `complement-size`, `complement-size-verify`, `orbit-size-gf3³`, `orbit-size-free`, `orbit-count-gf3³`, `orbit-count-free`, `orbit-count-total`, `orbit-count-total-verify`, `orbit-sizes-sum-729`, `burnside-consistency`, `orbit-divides-group`, `group-closure-complete`
- **质量**: `refl`×28；无 postulate / 无 hole

## `src/Sovereign/Structology/Closure.agda`

- **module**: `Sovereign.Structology.Closure`
- **行数**: 129（代码 48 / 注释 56）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | Sovereign.Structology.Closure
  - 结构学：仲吕相位同步与高维拓扑同步 (Zhonglv PhaseSync & Topological Sync)
  - 核心原理：
  - 仲吕相位同步在二维工程中表现为算术修正 (acc * 3^11 >> 16)，
  - 但在高维几何拓扑中，它是主权状态机在 T⁶ 环面上，
  - 极向缠绕 (144) 与环向缠绕 (46) 因不可通约性而产生的**拓扑同步跃迁**。
  - 极限环面原理：
  - 局部观测到的“十二律循环”只是高维“144/46 极限环面”的一个投影切片。
  - 系统演化必然趋向于全息相位同步 (144/46 同步归零)。
- **导入 (12)**: `Data.Nat`, `Data.Nat.Base`, `Data.Nat.DivMod`, `Data.Integer`, `Data.Product`, `Data.Bool`, `Relation.Nullary`, `Data.Fin.Base`, `Relation.Binary.PropositionalEquality`, `Data.Bool.Base`, `Sovereign.Base.Invariants`, `Sovereign.Base.Axioms`
- **record 类型**: `State`
- **顶层签名 (10)**: `PolarPhase`, `ToroidalPhase`, `step`, `calculateGap`, `isZhonglvPoint`, `zhonglvPhaseSyncOp`, `stepN`, `iteratePhaseSync`, `isHolographicState`, `convergenceToHolographicState`
- **质量**: `refl`×3；⚠️ 1 TODO

## `src/Sovereign/Structology/DefectSum.agda`

- **module**: `Sovereign.Structology.DefectSum`
- **行数**: 39（代码 16 / 注释 13）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | Sovereign.Structology.DefectSum
  - 53 微分几何补强 — 离散 Gauss-Bonnet: 四面体顶角亏 (0 postulate)
  - 正四面体: 4 顶点, 每顶点 3 个三角形 → 亏角 = 2π − 3·(π/3) = π
  - 以 π 为单位: 每顶点亏 = 1, 总和 = 4
  - 离散 Gauss-Bonnet: Σ 亏角 = 2π·χ(S²) → 4 = 2·2 ✓
  - 与 12 胞腔 S² 陈数协议的关系 (ChernEulerLadder/DiscreteKTheory §6) 注释。
- **导入 (3)**: `Data.Nat`, `Data.Integer`, `Relation.Binary.PropositionalEquality`
- **顶层签名 (7)**: `tet-vertices`, `tet-faces`, `tet-edges`, `vertex-defect`, `total-defect`, `gauss-bonnet`, `tet-euler`
- **质量**: `refl`×5；无 postulate / 无 hole

## `src/Sovereign/Structology/DiscreteCalculus.agda`

- **module**: `Sovereign.Structology.DiscreteCalculus`
- **行数**: 120（代码 39 / 注释 55）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | Sovereign.Structology.DiscreteCalculus
  - 结构学：代数复数场与离散微分算子
  - 宪法更新：
  - 移除 Data.Complex (违反纯代数宪法)。
  - 使用 Sovereign.RootMath.AlgebraicComplex 替代。
- **导入 (7)**: `Sovereign.RootMath.AlgebraicComplex`, `Data.Rational`, `Data.Integer`, `Data.Fin`, `Data.Nat`, `Relation.Binary.PropositionalEquality`, `Sovereign.Structology.LuCellGrid`
- **顶层签名 (10)**: `StandingWaveField`, `zeroField`, `constantField`, `partialPolar`, `partialToroidal`, `mixedPartial`, `shiftPolarNeg`, `shiftToroidalNeg`, `DiscreteLaplacian`, `CurvatureTest`
- **质量**: `refl`×1；无 postulate / 无 hole

## `src/Sovereign/Structology/DynamicMagicSquare.agda`

- **module**: `Sovereign.Structology.DynamicMagicSquare`
- **行数**: 153（代码 69 / 注释 50）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | Sovereign.Structology.DynamicMagicSquare
  - 动态幻方: 矢量方向动态系统 (本体类型, 卢先生定义)
  - 幻方不是静态数字排列, 而是过程:
  - n 阶 = n 个矢量方向同时变化
  - 套环 = 每个方向在环上转 (基座环 GF(3), +1 归零周期 3)
  - 动态 = 所有方向在同一时间参数 t 下同步演化
  - 解   = 闭合约束下的全部轨线
  - 传统数字幻方 = 此动态过程在某一时刻的投影切片 (电影的一帧)。
  - 与既有模块的连接:
  - 基座层: SP2Ternary.agda (+1 归零周期 3 / ×2 乌比斯环周期 2 永不归零)
  - 观测层: GF4AffineMagicSquare.affine-trajectory / GF9AffineMagicSquare.trajectory-Lλ
  - (环同步转动经仿射投影为步长 (a+b)/(λ+1) 的平移)
  - 静态实例: OrthogonalLatinSquare.agda (M4 完全幻方 = 动态过程的一帧)
  - 包含:
  - §1 矢量方向与套环 (类型)
  - §2 动态解 = 轨道 (同步演化) + 静动区分定理
  - §3 两条基座轨道的周期/归零性质
- **导入 (6)**: `Data.Nat`, `Data.Fin`, `Data.Vec`, `Relation.Binary.PropositionalEquality`, `Sovereign.Base.Trit`, `Sovereign.Base.Invariants`
- **record 类型**: `DynamicMagicSquare`
- **顶层签名 (23)**: `VectorDirections`, `NestedRings`, `Orbit`, `snapshot`, `zero-reset-orbit`, `threes`, `zr-period3`, `zr-closes-3`, `zr-closes-6`, `mobius-orbit`, `twos`, `mobius-period2`, `mobius-never-zero`, `orbits-distinct`, `lu-orders`, `lu-fib-1`, `lu-fib-2`, `lu-fib-3`, `lu-fib-4`, `lu-fib-5`, `lu-fib-6`, `lu-fib-7`, `lu-144-polar`
- **质量**: `refl`×13；无 postulate / 无 hole

## `src/Sovereign/Structology/ElectricalTopology.agda`

- **module**: `Sovereign.Structology.ElectricalTopology`
- **行数**: 71（代码 26 / 注释 31）
- **OPTIONS**: `--rewriting --cubical --guardedness`
- **头部注释（数学背景）**:
  - | Sovereign.Structology.ElectricalTopology
  - ⚠️ 废弃：电性文明拓扑（连续统退化投影）
  - 宪法裁定：
  - 本模块使用 Data.Complex (连续统复数)，违反纯代数宪法。
  - 根据 ADR-004，外部连续统引用信用为 0。
  - 本模块仅作为历史对照组存在，禁止用于任何宪法级证明。
  - 替代方案：参见 Sovereign.Structology.DiscreteCalculus (代数复数版本)
- **导入 (5)**: `Data.Complex`, `Data.Fin`, `Data.Rational`, `Relation.Binary.PropositionalEquality`, `Sovereign.Structology.LuCellGrid`
- **顶层签名 (4)**: `Phase_Cont`, `Connection`, `computeCurvature`, `computeChernNumber`
- **质量**: `refl`×1；无 postulate / 无 hole

## `src/Sovereign/Structology/FiniteTopology.agda`

- **module**: `Sovereign.Structology.FiniteTopology`
- **行数**: 101（代码 71 / 注释 14）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | Sovereign.Structology.FiniteTopology
  - 54 点集拓扑补强 — GF(3) 三点的 Sierpiński 拓扑 (0 postulate)
  - X = Trit, τ = {∅, {T₀}, {T₀,T₁}, X} — 有限拓扑完整公理:
  - 并/交封闭 (16 项表), T₀ 分离 (见证 {T₀}),
  - 非 T₁ (含 T₁ 不含 T₀ 的开集不存在)
- **导入 (5)**: `Data.Bool`, `Data.Product`, `Relation.Binary.PropositionalEquality`, `Relation.Nullary`, `Sovereign.Base.Trit`
- **data 类型**: `OpenSet`
- **顶层签名 (9)**: `member`, `union`, `inter`, `union-closed-sample`, `inter-closed-sample`, `union-idem`, `inter-idem`, `t0-separated`, `not-t1`
- **质量**: `refl`×13；无 postulate / 无 hole

## `src/Sovereign/Structology/FrequencySpaceUnity.agda`

- **module**: `Sovereign.Structology.FrequencySpaceUnity`
- **行数**: 72（代码 25 / 注释 31）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | Sovereign.Structology.FrequencySpaceUnity
  - 频率-空间一体: 泛音结构 (Christoffel 螺旋 mod 3) 与格点平移的统一 (0 postulate)
  - 泛音公理 (信息论第一性): 频率的离散结构 ≅ 空间的格点结构。
  - 频率泛音 = ×2 mod 3 (Frobenius σ, 周期 2, 轨 {1,2}) — 乌比斯环
  - 空间平移 = +1 mod 3 (C₃ 旋转, 周期 3, 轨 {0,1,2})      — 三进制归零
  - 两者是同一个 GF(3) = Fin 3 的乘法面与加法面; 频率与空间不是两个对象,
  - 而是同一离散格点的两个自同构 (σ 与 C₃ 生成仿射群 S₃, 见 S3IsGL22)。
  - 本模块只证明算子轨道结构 (refl); 物理读法 (overtone=频率, spaceStep=空间)
  - 属命名层, 不进入证明链。
- **导入 (5)**: `Data.Fin`, `Data.Vec`, `Data.Product`, `Relation.Binary.PropositionalEquality`, `Sovereign.Structology.SP2Ternary`
- **顶层签名 (6)**: `overtone`, `spaceStep`, `christoffel`, `christoffel-is-overtone`, `overtone-period2`, `spaceStep-period3`
- **质量**: `refl`×6；无 postulate / 无 hole

## `src/Sovereign/Structology/GF4.agda`

- **module**: `Sovereign.Structology.GF4`
- **行数**: 492（代码 429 / 注释 28）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | Sovereign.Structology.GF4
  - GF(4) = GF(2)[α]/(α²+α+1): 四元域, 完整域公理 (0 postulate)
  - 元素 {0, 1, α, α+1}, 特征 2 (x+x=0), α²=α+1, α(α+1)=1, (α+1)²=α。
  - 用于 GF(4) → 正交拉丁方 → 幻方的域论生成链; 与 GF(3)/GF(9)/GF(27) 并列。
- **导入 (7)**: `Data.Nat`, `Data.Fin`, `Data.Product`, `Data.Sum`, `Data.Empty`, `Relation.Nullary.Negation`, `Relation.Binary.PropositionalEquality`
- **data 类型**: `GF4`
- **顶层签名 (24)**: `toFin`, `fromFin`, `toFin-fromFin`, `add4`, `neg4`, `mul4`, `add4-comm`, `add4-assoc`, `add4-unit`, `add4-inv`, `mul4-comm`, `mul4-assoc`, `mul4-unit`, `mul4-zero`, `distrib-left`, `distrib-right`, `mul4-inv`, `add4-identityˡ`, `mul4-identityˡ`, `add4-self`, `neg4-identity`, `gf4-no-zero-divisors`, `gf4-square-map`, `gf4-squared`
- **质量**: `refl`×336；无 postulate / 无 hole

## `src/Sovereign/Structology/GF4AffineMagicSquare.agda`

- **module**: `Sovereign.Structology.GF4AffineMagicSquare`
- **行数**: 270（代码 148 / 注释 83）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | Sovereign.Structology.GF4AffineMagicSquare
  - 完全幻方五定理: GF(4) 仿射正交拉丁方对 (0 postulate)
  - 【幻方定义: 一本体 + 两投影】(会话裁定 #11, 修正此前「三层并列」表述)
  - 本体: 幻方 = 矢量方向动态系统 (卢先生定义) — 环上 n 个矢量方向同时变化,
  - 套环同步演化, 解 = 闭合约束下的全部轨线。没有静态几何。
  - 投影 1 (本模块): 框架可证定义 = 本体在 GF(4) 基座上的显式实现, 仍是动态的:
  - L1 = 2i+3j+2, L2 = 3i+2j+2 是两个环的动态法则;
  - 正交性 = 两环同时转, 16 组合各出现一次; 完全闭合 = 十线等和不变量。
  - 投影 2: 传统数字幻方 = 动态过程的静态投影切片 (电影的一帧),
  - 只保留「十线和相等」不变量 — MagicSquareM4.agda 实例, 非并列层。
  - 【定理序列】(会话裁定 #9, 证明层/命名层严格分离)
  - T1    正交性: 16 对互异 (承 OrthogonalLatinSquare.orthogonal)
  - T2′   转置恒等式: L2 ≡ L1ᵀ (主对角反射 — 命名层挂 Slot 4↔5 手征交换)
  - T2″   系数 σ-像 (实例级): σ4(α)=α+1, σ4(α+1)=α — 命名层挂 Slot 6 内部规范相位
  - 诚实边界: 常数项 c=2 未共轭 (σ4(2)=3≠2), 不可声称 L2 = σ(L1)
  - T-sym 统一判据: det[[a,b],[b,a]] = a²⊕b² = (a⊕b)² (特征2), 非零 ⟺ a≠b
  - 正交性条件与对角 transversal 条件统一为同一判据
  - T3    完全幻方: M0 = 4·L1+L2 十线全 ≡ 30
- **导入 (9)**: `Data.Nat`, `Data.Fin`, `Data.Vec`, `Data.Bool`, `Data.Product`, `Data.Empty`, `Relation.Binary.PropositionalEquality`, `Sovereign.Structology.GF4`, `Sovereign.Structology.OrthogonalLatinSquare`
- **顶层签名 (23)**: `T1`, `transpose4`, `T2′`, `σ4`, `constant-not-conjugated`, `T-sym-square`, `add4-self`, `det-zero-eq`, `det-neq-zero`, `T-sym`, `det-instance-nonzero`, `M0`, `T3`, `add4-regroup`, `affine-trajectory`, `trajectory-L1`, `trajectory-L2`, `trajectory-step`, `trajectory-step-nonzero`, `diagonal-main-step`, `diagonal-main-nonzero`, `diagonal-anti-step`, `diagonal-anti-nonzero`
- **质量**: `refl`×43；无 postulate / 无 hole

## `src/Sovereign/Structology/GF9AffineMagicSquare.agda`

- **module**: `Sovereign.Structology.GF9AffineMagicSquare`
- **行数**: 213（代码 112 / 注释 63）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | Sovereign.Structology.GF9AffineMagicSquare
  - GF(9) 幻方链推广: a≠b 判据在特征 3 的形态 (0 postulate)
  - 【特征分离】(对照 GF4AffineMagicSquare 的特征 2 统一判据)
  - GF(4) 特征 2: a≠b 统一判据 ⟺ 正交 + 两对角闭合 (Freshman's Dream 合并)
  - GF(9) 特征 3: 判据分裂为三:
  - 正交   ⟺ λ₁ ≠ λ₂        (斜率差非零, 无零因子)
  - 主对角 ⟺ λ ≠ -1          (L_λ(i,i) = (λ+1)·i 为置换)
  - 副对角 ⟺ λ ≠ 1           (空间副对角 j=8-i ⟺ (2,2)⊖i,
  - 值 = (λ-1)·i + (2,2) 为置换)
  - 【完全幻方实例】λ₁=α, λ₂=2α (均 ∉ {1,-1}):
  - 正交 (81 对互异) + 叠加 M = 9·L₁+L₂+1 十线全 369 (1..81 完整)
  - 81 格表的十线数据由 Rust 锁定 (表过大不入证明层):
  - sov-math/sov-validation/src/gf9_diag.rs [3]/[6]
  - Agda 侧锁定: 判据代数核 (无零因子 orth-kernel)、对角 transversal
  - (显式置换表)、退化反例 (λ=1/λ=-1)、幻常数算术。
  - 【命名层锚点】三进制「矢量对称幻方」实例: L_α/L_2α 两环同步旋转,
  - 完全闭合是动态过程的不变量 (本体定义见 GF4AffineMagicSquare 头注释)。
- **导入 (7)**: `Data.Nat`, `Data.Vec`, `Data.Product`, `Data.Empty`, `Relation.Binary.PropositionalEquality`, `Sovereign.Base.Trit`, `Sovereign.Algebra.GF9`
- **顶层签名 (23)**: `twoAlpha`, `negGF9`, `subGF9`, `anti-c`, `onePlusAlpha`, `alphaMinusOne`, `orth-diff`, `orth-diff-val`, `orth-diff-nonzero`, `orth-kernel`, `diag-alpha`, `diag-alpha-perm`, `anti-alpha`, `anti-alpha-perm`, `anti-degen-1`, `main-degen-2`, `sep-diff`, `sep-diff-nonzero`, `idx-sum-36`, `magic-constant-369`, `+gf9-inner-swap`, `trajectory-Lλ`, `trajectory-step-alpha`
- **质量**: `refl`×10；无 postulate / 无 hole

## `src/Sovereign/Structology/GF9MagicSquare.agda`

- **module**: `Sovereign.Structology.GF9MagicSquare`
- **行数**: 193（代码 127 / 注释 29）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | Sovereign.Structology.GF9MagicSquare
  - GF(9) = GF(3)[α]/(α²+1) 正交拉丁方 → 9 阶幻方 (Euler 构造, 0 postulate)
  - 【术语边界】本模块「幻方」= 数学数字幻方（行列对角线和相等，幻常数 369）。
  - 非卢先生「矢量方向/变量计数」幻方（阶数 = 同时在变的矢量方向个数）。
  - 辨析与知识库依据见 docs/cross-level/magic-square-terminology.md
  - 深度证明: 三进制域 GF(3²) 上的正交拉丁方 L_λ[i,j] = idx(λ·el(i) + el(j))
  - 由域运算生成, 取 λ=α 与 λ=2α (Galois 共轭对 σ(α)=-α=2α, 即 C₂ 手征共轭),
  - Euler 叠加 M = 9·L₁ + L₂ + 1 得到 9 阶完全幻方 (幻常数 369)。
  - 拉丁性 ⟹ 行/列和 = 幻常数; 正交性 ⟹ 81 元互异 = {1..81} (正规幻方)。
  - 对应 Rust sov-validation/ternary_magic.rs 的数值核验。
- **导入 (9)**: `Data.Nat`, `Data.Fin`, `Data.Vec`, `Data.Bool`, `Data.Product`, `Relation.Binary.PropositionalEquality`, `Relation.Nullary.Decidable`, `Sovereign.Base.Trit`, `Sovereign.Algebra.GF9`
- **顶层签名 (29)**: `el`, `idx`, `L`, `lam1`, `lam2`, `L1`, `L2`, `count`, `isLatinRow9`, `column`, `isLatinSquare9`, `L1-latin`, `L2-latin`, `flatten9`, `super0`, `allDistinct`, `orthogonal`, `superpose`, `sum9`, `rowSum`, `colSum`, `diagSum`, `antidiagSum`, `magicConstant369`, `euler-row-magic`, `euler-col-magic`, `euler-diag-magic`, `sum0to8`, `euler-magic-formula`
- **质量**: `refl`×348；无 postulate / 无 hole

## `src/Sovereign/Structology/HoloInformation.agda`

- **module**: `Sovereign.Structology.HoloInformation`
- **行数**: 279（代码 108 / 注释 113）
- **OPTIONS**: `--rewriting --cubical --guardedness`
- **头部注释（数学背景）**:
  - | Sovereign.Structology.HoloInformation
  - 全息信息论：4320D 形式化
  - 核心命题：
  - 1. 4320D = 24(梅尔卡巴) x 36(水态) x 5(五行) == 2(手性) x 12(十二律) x 36(苞元) x 5(五行)
  - 2. 七阶段周期：5 元素 + 空生火 + 入空 = 7，火是唯一双端口元素
  - 3. 21 条热带 = 3(trit) x 7(七阶段) = H2O@C60 红外光谱锚定 (J. Chem. Phys. 2025)
  - 4. 1:3 光锥内外信息比 = 全息统一 : 光锥内三段火大投影
  - 5. 54 规范冗余 = |(C3)^3 x C2| = Burnside 轨道修正 (NSE.agda:112)
  - 证明策略分布：
  - 穷举(refl): 24 条 | 代数链: 0 | 否定: 0 | Postulate: 0
  - 全部构造性闭合 (0 postulate):
  - Burnside 轨道计数已由 BurnsideT6.agda 构造性闭合
  - LightCone 光锥边界已由 LightCone.agda 构造性闭合
  - 4320D 爻变维度已由 independent-info-is-4320D refl 闭合
  - 实验锚定来源：
  - H2O@C60 红外光谱 (21条热带/39条谱线) — J. Chem. Phys. 2025
- **导入 (6)**: `Data.Nat`, `Data.Product`, `Relation.Binary.PropositionalEquality`, `Sovereign.Structology.Winding`, `Sovereign.Structology.MagicSquare144`, `Sovereign.Physics.LightCone`
- **record 类型**: `FivePhaseFreq`, `ExperimentalAnchor`
- **顶层签名 (54)**: `M24x36x5`, `M2x12x36x5`, `merkaba-chiral-phase`, `4320D-decomposition-equivalent`, `4320D-merkaba-firewater`, `4320D-chiral-lv-harmonic-wuxing`, `FireMerkaba`, `WaterHarmonic36`, `WuxingCount`, `fire-water-wuxing-product`, `merkaba-is-dual-A4`, `water-harmonic-decomposition`, `seven-freq`, `seven-equals-five-plus-two`, `fire-double-port`, `earth-once`, `metal-once`, `water-once`, `wood-once`, `TropicalBands21`, `TritStates`, `SevenStagesN`, `FirePhaseCount`, `A4CellCount`, `ZhonglvSingularity`, `SpectralLines39`, `tropical-bands-equals-trit-times-seven`, `tropical-bands-equals-firecycles`, `spectral-lines-equals-trit-times-a4plus1`, `LightconeFullInfo`, `HolographicInfoUnit`, `info-conserved-across-lightcone`, `GaugeGroupOrder54`, `gauge-group-equals-27x2`, `TotalYaoSpace`, `IndependentInfo`, `independent-info-is-4320D`, `yao-to-gauge-ratio`, `anchor-tropical`, `anchor-spectral`, `anchor-c60`, `anchor-polar`, `anchor-merkaba24`, `anchor-five`, `anchor-4320`, `all-anchors-closed`, `dim-4320-structural`, `merkaba-structural`, `water-structural`, `seven-phase-structural`, `tropical-bands-structural`, `info-conservation-structural`, `gauge-group-structural`, `independent-info-structural`
- **质量**: `refl`×44；无 postulate / 无 hole

## `src/Sovereign/Structology/HolographicPi.agda`

- **module**: `Sovereign.Structology.HolographicPi`
- **行数**: 419（代码 231 / 注释 120）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | Sovereign.Structology.HolographicPi
  - 结构学：全息 π = 144/46
  - 本质：T⁶ 离散环面上极向缠绕 144 与环向缠绕 46 的原子配对
  - 主权状态机平行移动和乐归零的拓扑签名
  - 注意：非连续统 π ≈ 3.14159，禁止约分、禁止十进制展开
  - 范畴纪律：PolarRep/ToroidalRep 为不透明原子类型——"约分"在类型层不可表达
- **导入 (16)**: `Data.Nat`, `Data.Integer`, `Data.Rational`, `Data.Fin`, `Relation.Binary.PropositionalEquality`, `Data.Product`, `Data.Empty`, `Relation.Nullary`, `Data.Unit`, `Data.List`, `Data.Maybe`, `Data.Bool`, `Agda.Builtin.String`, `Sovereign.Structology.Winding`, `Sovereign.Coupling.ZhonglvPhaseSync`, `Sovereign.Coupling.LossGain`
- **data 类型**: `PolarRep`, `ToroidalRep`, `Density`, `EuclideanPi`
- **record 类型**: `HolographicPi`, `DensityPi`, `CuttingCircle`, `CuttingLossGainIsomorphism`, `ElectricComputation`, `GF3Lattice`, `SovereignLCMModulus`, `ZhonglvPhaseSyncDynamics`, `IntrinsicDiscreteCurvature`, `RationalApproximation`, `DecimalExpansion`, `ToroidalWindingRatioTopologicalCurvature`
- **顶层签名 (33)**: `HoloPiNumerator`, `holoPiNumeratorIs144`, `HoloPiDenominator`, `holoPiDenominatorIs46`, `polarRepValue`, `toroidalRepValue`, `polarRepIs144`, `toroidalRepIs46`, `standardHoloPi`, `holoPiStandard`, `pi12`, `pi24`, `pi144`, `allDensityPisExact`, `projectPi`, `cannotUpgradePi`, `holoPiDistinctFromOthers`, `zuChongzhiCutting`, `zuChongzhiReachesPi24`, `cuttingIsomorphismInstance`, `illegalPresumptions`, `holographicPiRequirements`, `holoPiIsTopologicalInvariant`, `intrinsicCurvature`, `c60Fundamental46`, `magicSquare144`, `nanlu432Hz`, `noRationalApproximation`, `noEuclideanPi`, `noDecimalExpansion`, `HolographicPiDefinition`, `holoPiLegal`, `holoPiRememberedNotComputed`
- **质量**: `refl`×19；无 postulate / 无 hole

## `src/Sovereign/Structology/HolographicSpace.agda`

- **module**: `Sovereign.Structology.HolographicSpace`
- **行数**: 151（代码 62 / 注释 60）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | Sovereign.Structology.HolographicSpace
  - 全息态与基模 — 信息论闭包的类型基础设施
  - 核心原则:
  - ① 类型定义保持 ∀ n 参数化, 不在类型中固定 4320 (避免 Fin 归一化展开)
  - ② 具体 4320 仅出现在 ℕ 级证明 (refl, 不涉及 Fin 递归)
  - ③ normSq-basisVec/basis-orthogonal 已迁移至 FiniteInnerProduct.agda (构造性证明)
  - ④ theorem-maximality-4320 由 BurnsideT6.orbit-sizes-sum-729 + refl 闭合
  - 包含: HolographicState, BasisMode, basisAt, basisAt-orthogonal,
  - theorem-maximality-4320, closure-complete
  - 0 postulate — 全部构造性证明
- **导入 (9)**: `Agda.Builtin.Equality`, `Data.Nat`, `Data.Fin`, `Data.Product`, `Relation.Nullary`, `Sovereign.Base.Trit`, `Sovereign.Algebra.GF9`, `Sovereign.Analysis.FiniteInnerProduct`, `Sovereign.Structology.BurnsideT6`
- **record 类型**: `HolographicState`, `BasisMode`
- **顶层签名 (14)**: `INFO-DIM`, `N-CELLS`, `N-ORBITS`, `G-ORDER`, `Orthogonal`, `basisAt`, `basisAt-self`, `basisAt-orthogonal`, `theorem-maximality-4320`, `combinatorial-closure`, `group-closure`, `burnside-consistency`, `closure-complete`, `info-dim≡yao`
- **质量**: `refl`×13；无 postulate / 无 hole

## `src/Sovereign/Structology/IhC60Vibration.agda`

- **module**: `Sovereign.Structology.IhC60Vibration`
- **行数**: 933（代码 683 / 注释 93）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | Sovereign.Structology.IhC60Vibration
  - I_h → 46 定理: C60 的 174 维振动表示在 I_h 下分解出恰好 46 个独立基频
  - 数学背景:
  - C60（足球烯）60 个顶点, 对称群 I_h（|I_h|=120, 10 个不可约表示）。
  - 顶点置换表示 Γ_perm 在各类上的不动点: 仅 E(60) 与 σ 镜面(4), 其余为 0。
  - ⟨χ_perm, χ_R⟩ = (60·χ_R(E) + 60·χ_R(σ))/120 = (d_R + σ_R)/2  ⟹
  - Γ_perm = A_g + T₁g + 2T₁u + T₂g + 2T₂u + 2G_g + 2G_u + 3H_g + 2H_u (60 维)
  - 振动表示 Γ_vib = Γ_perm ⊗ T₁u − T₁u(平移) − T₁g(转动), 维数 174 = 3·60−6:
  - Γ_vib = 2A_g + A_u + 3T₁g + 4T₁u + 4T₂g + 5T₂u + 6G_g + 6G_u + 8H_g + 7H_u
  - 独立基频数 = 各不可约支出现数之和 = 2+1+3+4+4+5+6+6+8+7 = 46。
  - 形式化内容（0 postulate, 全部 ℤ[τ] 精确算术 refl, τ=(1+√5)/2, τ²=τ+1）:
  - §1 Golden 环 ℤ[τ]（无浮点, 宪法兼容）
  - §2 I_h 特征标表（10 不可约表示 × 10 共轭类, 100 项）
  - §3 张量积行 T₁u-乘积表 + 特征标级验证（10 行 × 10 类 = 100 refl）
  - §4 Γ_perm 重数（内积公式 (d+σ)/2, 10 证书）
  - §5 Γ_vib 重数向量（2,1,3,4,4,5,6,6,8,7）与主定理: 46 个独立基频
  - §6 维数守恒: Σ m_R·d_R = 174
  - §7 特征标正交性全表: ⟨χᵢ,χⱼ⟩ = δᵢⱼ (10×10 = 100 项, 缩放 120 消分母)
- **导入 (6)**: `Data.Integer`, `Data.Nat`, `Data.Product`, `Data.List`, `Relation.Binary.PropositionalEquality`, `Relation.Nullary`
- **data 类型**: `Irrep`, `Class`
- **顶层签名 (149)**: `Golden`, `τ`, `g1`, `charTable`, `dim`, `chiPerm`, `tensorRow`, `chiSum`, `verify-tensor`, `sigmaChi`, `permMult`, `perm-cert-Ag`, `perm-cert-Au`, `perm-cert-T1g`, `perm-cert-T1u`, `perm-cert-T2g`, `perm-cert-T2u`, `perm-cert-Gg`, `perm-cert-Gu`, `perm-cert-Hg`, `perm-cert-Hu`, `times`, `permVibRaw`, `irrep-dec`, `removeOne`, `vibList`, `count`, `vibMult`, `vib-vector`, `freq-46`, `dim-174`, `dof-check`, `classSize`, `classSizeSum`, `scaleG`, `orthoTerm`, `ortho`, `orthoAgAg`, `orthoAgAu`, `orthoAgT1g`, `orthoAgT1u`, `orthoAgT2g`, `orthoAgT2u`, `orthoAgGg`, `orthoAgGu`, `orthoAgHg`, `orthoAgHu`, `orthoAuAg`, `orthoAuAu`, `orthoAuT1g`, `orthoAuT1u`, `orthoAuT2g`, `orthoAuT2u`, `orthoAuGg`, `orthoAuGu`, `orthoAuHg`, `orthoAuHu`, `orthoT1gAg`, `orthoT1gAu`, `orthoT1gT1g`
  - … 其余 89 项
- **质量**: `refl`×245；无 postulate / 无 hole

## `src/Sovereign/Structology/Lattice.agda`

- **module**: `Sovereign.Structology.Lattice`
- **行数**: 79（代码 39 / 注释 26）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | Sovereign.Structology.Lattice
  - 结构学：长度格点序列 (十二律)
  - 核心概念：
  - 律管长度格点序列是主权状态机在极向缠绕维度上的离散投影。
  - 十二律不仅仅是音律，更是时间/空间演化的 12 个关键相位节点。
  - 宪法依据：
  - "黄钟归一化长度格点 81" ... "仲吕长度格点 30"
  - "十二律 LCM 余数序列"
- **导入 (9)**: `Data.Nat`, `Data.Vec.Base`, `Data.Bool`, `Data.Fin.Base`, `Relation.Binary.PropositionalEquality`, `Sovereign.Base.Lü`, `Sovereign.Base.Invariants`, `Sovereign.Base.Axioms`, `Sovereign.Projection.Decimal.Axioms`
- **record 类型**: `Lü`
- **顶层签名 (3)**: `TwelveLu`, `huangZhongStable`, `zhongLuRemCorrect`
- **质量**: `refl`×3；无 postulate / 无 hole

## `src/Sovereign/Structology/LuCellGrid.agda`

- **module**: `Sovereign.Structology.LuCellGrid`
- **行数**: 137（代码 57 / 注释 47）
- **OPTIONS**: `--rewriting --cubical --guardedness`
- **头部注释（数学背景）**:
  - | Sovereign.Structology.LuCellGrid
  - 结构学：律胞腔网格（十二律相位的二维静态展开）
  - 此模块定义十二律胞腔在二维网格上的静态排列。
  - 网格总数 = 144，与极向缠绕数 144 数值相等，是全息同构的庄严签名。
  - ⚠️ 宪法宣誓：
  - 此 Fin 144 是【静态网格的格点索引】，≠ 极向缠绕数（PolarWinding）！
  - 禁止将此 Fin 144 与 PolarWinding 的 Fin 144 视为同一类型。
  - 禁止对 Fin 144 进行 Fin 12 × Fin 12 的模式匹配或代数分解。
  - 本模块属于结构学静态容器，禁止暴露给耦合域的状态机演化模块。
- **导入 (8)**: `Data.Fin`, `Data.Nat`, `Data.Product`, `Data.Vec`, `Relation.Binary.PropositionalEquality`, `Sovereign.Structology.A4Group`, `Data.Bool`, `Data.Nat`
- **顶层签名 (14)**: `LuGridPoint`, `gridRow`, `gridCol`, `mkGridPoint`, `shiftPolar`, `shiftToroidal`, `shiftDiagonal`, `actionOnGrid`, `gridActionIdentity`, `gridActionCompose`, `LCMGrid`, `isA4Symmetric`, `PhaseField`, `discreteCurvature`
- **质量**: `refl`×3；无 postulate / 无 hole

## `src/Sovereign/Structology/MagicSquare144.agda`

- **module**: `Sovereign.Structology.MagicSquare144`
- **行数**: 316（代码 104 / 注释 154）
- **OPTIONS**: `--cubical --guardedness --rewriting`
- **头部注释（数学背景）**:
  - | Sovereign.Structology.MagicSquare144
  - 结构学：144 阶幻方静态容器
  - 【术语边界】本模块「144 阶幻方」= 144 胞腔静态容器（120 + 24），
  - 非数学数字幻方（行列和对角线和相等），亦非卢先生「矢量方向/变量计数」幻方
  - （后者阶数 = 同时在变的矢量方向个数，144 = 12 维对称关系，排列数 144!）。
  - 辨析与知识库依据见 docs/cross-level/magic-square-terminology.md
  - 物质世界能量抽离后，主权状态机退化的静态胞腔容器：
  - 正十二面体 120 胞腔与梅尔卡巴 24 胞腔并集
  - 此静态组成 ≠ 缠绕数分解
- **导入 (13)**: `Data.Nat`, `Data.Nat.DivMod`, `Data.Nat.Properties`, `Data.Fin`, `Data.Product`, `Data.Vec`, `Relation.Binary.PropositionalEquality`, `Relation.Nullary`, `Sovereign.Structology.Winding`, `Sovereign.Structology.T6`, `Sovereign.Format.CRT`, `Sovereign.Arithmetic.CRTLemmas`, `Sovereign.Base.Invariants`
- **data 类型**: `CellType`
- **record 类型**: `MagicCell`
- **顶层签名 (34)**: `MagicOrder`, `magicOrderIs144`, `MagicTotal`, `magicTotalIs20736`, `DodecahedronCells`, `dodecahedronDerivation`, `MerkabaCells`, `merkabaDerivation`, `magicSquareComposition`, `noWindingFrom120`, `noWindingFrom24`, `crt-projection-equality`, `cell-sum-lt-M`, `winding-CRT-fiber`, `FULL_TOUR`, `fullTourCorrect`, `M-contains-tours`, `magicSquareSum`, `magicSumCorrect`, `magicToT6`, `magicPeriodic`, `dodecahedronEuler`, `dodecahedronEulerIs2`, `merkabaEuler`, `merkabaEulerIs0`, `totalEuler`, `totalEulerIs2`, `magic-order-structural`, `dodecahedron-structural`, `merkaba-structural`, `magic-total-structural`, `euler-characteristics`, `full-tour-structural`, `magic-sum-structural`
- **质量**: `refl`×16；无 postulate / 无 hole

## `src/Sovereign/Structology/MagicSquareHFM.agda`

- **module**: `Sovereign.Structology.MagicSquareHFM`
- **行数**: 63（代码 36 / 注释 11）
- **OPTIONS**: `--rewriting`
- **头部注释（数学背景）**:
  - 本模块是 HFM 交叉验证测试向量, 不替代原形式化证明。
  - 主证明见: ArthurMagicSquare.agda
  - 【术语边界】本模块「幻方」= 数学数字幻方（行列对角线和相等）。
  - 非卢先生「矢量方向/变量计数」幻方。辨析见 docs/cross-level/magic-square-terminology.md
  - | Sovereign.Structology.MagicSquareHFM
  - M4 幻方常数的 HFM 交叉验证
- **导入 (3)**: `Data.Nat`, `Relation.Binary.PropositionalEquality`, `Relation.Binary.PropositionalEquality`
- **顶层签名 (20)**: `row0`, `row0-ok`, `row1`, `row1-ok`, `row2`, `row2-ok`, `row3`, `row3-ok`, `col0`, `col0-ok`, `col1`, `col1-ok`, `col2`, `col2-ok`, `col3`, `col3-ok`, `diag1`, `diag1-ok`, `diag2`, `diag2-ok`
- **质量**: `refl`×1；无 postulate / 无 hole

## `src/Sovereign/Structology/MagicSquareM4.agda`

- **module**: `Sovereign.Structology.MagicSquareM4`
- **行数**: 461（代码 128 / 注释 266）
- **OPTIONS**: `--rewriting --cubical --guardedness`
- **头部注释（数学背景）**:
  - | Sovereign.Structology.MagicSquareM4
  - 瑟尔四阶幻方 M₄ 及其 CRT 谱投影
  - 【CRT 谱投影定理】
  - M₄ 矩阵在实数域 ℝ 上的真实本征值为：
  - Σ_ℝ = {34, 0, 2√10, -2√10}   （其中 2√10 ≈ 6.3246）
  - 在 CRT 模域中，取模数 M = 3¹¹·2¹⁶ = 11609505792。
  - 注意到 216 = 2³·3³ 是 M 的因子（216 | M）。
  - 在模 216 下，有同余关系：
  - (2√10)² = 40
  - 16² = 256
  - 256 ≡ 40  (mod 216)     因为 256 - 40 = 216 = 1 × 216
  - 因此 √40 ≡ 16 (mod 216)，进而 √40 ≡ 16 (mod M)。
  - 由此得到实数谱的 CRT-模投影：
- **导入 (7)**: `Data.Nat`, `Data.Nat.DivMod`, `Data.Integer`, `Data.Vec`, `Relation.Binary.PropositionalEquality`, `Data.Product`, `Sovereign.Structology.MagicSquare144`
- **data 类型**: `M4Orthogonality`, `Eigenvalue`
- **record 类型**: `CompilerM4Connection`
- **顶层签名 (35)**: `_≡_mod_`, `M4`, `magicConstant`, `row1Sum`, `col1Sum`, `row2Sum`, `row3Sum`, `row4Sum`, `col2Sum`, `col3Sum`, `col4Sum`, `diagSum`, `antidiagSum`, `evalEigenvalue`, `Σ-M4`, `traceM4`, `crtCongruence`, `crtEigenvalue`, `crtModProof`, `matVecMul`, `scalarMul`, `v34`, `v0`, `eigenvector34`, `eigenEq34`, `eigenvector0`, `eigenEq0`, `innerProduct`, `orth-v34-v0`, `Orth`, `orth-16-neg16`, `orth-v34-v0-verify`, `v34-norm`, `v0-norm`, `orthogonal-basis-complete`
- **质量**: `refl`×31；⚠️ 1 postulate

## `src/Sovereign/Structology/MatrixZω.agda`

- **module**: `Sovereign.Structology.MatrixZω`
- **行数**: 50（代码 22 / 注释 15）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | Sovereign.Structology.MatrixZω
  - Z[ω] 上的最小矩阵库 — A₄ 三维表示 ρ₃ 构造的基础设施 (0 postulate)
  - 矩阵用 Vec (Vec Zω m) n 表示 (n 行 m 列), 提供:
  - dot (向量内积), mulMat (矩阵乘法), trace (迹)。
  - 全部递归/定义展开, 无 postulate。
- **导入 (4)**: `Data.Nat`, `Data.Fin`, `Data.Vec`, `Sovereign.Structology.A4Representation`
- **顶层签名 (6)**: `Mat`, `dot`, `sumVec`, `column`, `mulMat`, `trace`
- **质量**: `refl`×0；无 postulate / 无 hole

## `src/Sovereign/Structology/MotorStableStates.agda`

- **module**: `Sovereign.Structology.MotorStableStates`
- **行数**: 113（代码 38 / 注释 49）
- **OPTIONS**: `--rewriting --guardedness`
- **导入 (9)**: `Data.Fin`, `Data.Nat`, `Data.Unit`, `Data.Product`, `Relation.Binary.PropositionalEquality`, `Sovereign.Algebra.GF9`, `Sovereign.Structology.A4Group`, `Sovereign.Algebra.TriCycGraph`, `Sovereign.Structology.ArthurMagicSquare`
- **顶层签名 (9)**: `IsA4Invariant`, `StableState`, `zeroMatrix-a4Invariant`, `zeroMatrix-stable`, `fourTCGtoMatrix`, `a4-order`, `FixPoint`, `BurnsideLemma`, `FixSize`
- **质量**: `refl`×2；无 postulate / 无 hole

## `src/Sovereign/Structology/OrderLattice.agda`

- **module**: `Sovereign.Structology.OrderLattice`
- **行数**: 61（代码 36 / 注释 13）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | OrderLattice — 离散序与格理论 (MSC 06)
  - GF(3) 上的偏序与格: 有限集上所有序关系可穷举.
  - 0 postulate.
- **导入 (5)**: `Data.Nat`, `Data.Product`, `Data.Empty`, `Relation.Binary.PropositionalEquality`, `Sovereign.Base.Trit`
- **data 类型**: `_`
- **顶层签名 (5)**: `¬T1≤T0`, `≤₃-trans`, `∨₃`, `∧₃`, `∨-absorbs-∧`
- **质量**: `refl`×14；无 postulate / 无 hole

## `src/Sovereign/Structology/OrthogonalLatinSquare.agda`

- **module**: `Sovereign.Structology.OrthogonalLatinSquare`
- **行数**: 197（代码 111 / 注释 51）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | Sovereign.Structology.OrthogonalLatinSquare
  - 正交拉丁方 → 幻方 (Euler 构造, 0 postulate)
  - 【术语边界】本模块「幻方」= 数学数字幻方（行列对角线和相等）。
  - 非卢先生「矢量方向/变量计数」幻方（阶数 = 同时在变的矢量方向个数）。
  - 辨析与知识库依据见 docs/cross-level/magic-square-terminology.md
  - 深度证明: M₄ 幻方不再手写给定, 而是从一对正交拉丁方 L₁, L₂ 叠加导出:
  - M₄[i,j] = 4·L₁[i,j] + L₂[i,j] + 1     (符号 0..3, 叠加值 1..16)
  - 拉丁性   ⟹ 每行/列含 {0,1,2,3} 各一次 ⟹ Σ = 6 ⟹ 行/列和 = 4·6 + 6 + 4 = 34
  - 正交性   ⟹ 16 个叠加值两两不同 ⟹ {1..16} 完整 (正规幻方)
  - 对角     ⟹ 具体 L₁, L₂ (断对角拉丁方) 额外使两条对角线和 = 34
  - 一般 Euler 定理 (任意奇数 n, 或 GF(q) 上的任意阶): 正交拉丁方对 (L₁,L₂)
  - 叠加 M = n·L₁ + L₂ + 1 自动给出半幻方 (行列和 = n(n²+1)/2); 正交性保证
  - 16 元互异。本模块在 n=4 逐 case 全证 (0 postulate, 全 refl)。
  - 与本体系连接: 此 M₄ 与 MagicSquareM4.agda 的 M₄ 逐元素一致 (euler-is-M4),
  - 后者经 M4CRTBridge.agda 投影到 CRT 模域 {34,0,16,-16}。故本模块把
- **导入 (7)**: `Data.Nat`, `Data.Fin`, `Data.Vec`, `Data.Bool`, `Data.Product`, `Relation.Binary.PropositionalEquality`, `Relation.Nullary.Decidable`
- **顶层签名 (24)**: `L1`, `L2`, `count`, `isLatinRow`, `column`, `isLatinSquare`, `L1-latin`, `L2-latin`, `super0`, `allDistinct`, `orthogonal`, `superpose`, `M4`, `euler-is-M4`, `sum4`, `rowSum`, `diagSum`, `antidiagSum`, `magicConstant`, `euler-row-magic`, `euler-col-magic`, `euler-diag-magic`, `sum0to3`, `euler-magic-formula`
- **质量**: `refl`×80；无 postulate / 无 hole

## `src/Sovereign/Structology/OrthogonalLatinSquareGF4.agda`

- **module**: `Sovereign.Structology.OrthogonalLatinSquareGF4`
- **行数**: 127（代码 73 / 注释 25）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | Sovereign.Structology.OrthogonalLatinSquareGF4
  - GF(4) 域公式 → 正交拉丁方 → 半幻方 (0 postulate)
  - 域生成: L1(i,j) = i + j,  L2(i,j) = α·i + j  (GF(4) 加法/乘法)
  - 两者拉丁且正交 (16 对互异), Euler 叠加 M = 4·L1 + L2 + 1 是半幻方
  - (行和=列和=34)。
  - 【重要更正】本模块的 genL1/genL2 与 OrthogonalLatinSquare.agda 的手写 L1/L2
  - (来自 Dürer M₄ 分解) 不是同一对: 域仿射公式给出半幻方 (对角 ≠ 34), 而 M₄ 分解
  - 给出完全幻方 (对角也 = 34)。故 genL1 ≢ L1, 之前「genL1-eq-L1 = refl」的假设错误。
  - 本模块证明 GF(4) 域论链「域 → 正交拉丁方 → 半幻方」, 与 M₄ 的完全幻方互补。
- **导入 (8)**: `Data.Nat`, `Data.Fin`, `Data.Vec`, `Data.Bool`, `Data.Product`, `Relation.Binary.PropositionalEquality`, `Relation.Nullary.Decidable`, `Sovereign.Structology.GF4`
- **顶层签名 (20)**: `genL1`, `genL2`, `count`, `isLatinRow`, `column`, `isLatinSquare`, `genL1-latin`, `genL2-latin`, `flatten4`, `super0`, `allDistinct`, `orthogonal`, `superpose`, `sum4`, `rowSum`, `colSum`, `semi-magic-rows`, `semi-magic-cols`, `sum0to3`, `euler-formula`
- **质量**: `refl`×77；无 postulate / 无 hole

## `src/Sovereign/Structology/PickTheorem.agda`

- **module**: `Sovereign.Structology.PickTheorem`
- **行数**: 34（代码 12 / 注释 13）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | Sovereign.Structology.PickTheorem
  - 52 离散几何补强 — Pick 定理的格三角形见证 (0 postulate)
  - 三角形 (0,0), (4,0), (0,4):
  - 面积 A = 8; 边界格点 B = 12; 内点 I = 3
  - Pick: A = I + B/2 − 1 = 3 + 6 − 1 = 8 ✓
  - 边界计数: 三边各 gcd(4,0)+1 = 5 / gcd(4,4)+1 = 5 / gcd(0,4)+1 = 5
  - (顶点计 2 次, 5+5+5−3 = 12)
- **导入 (2)**: `Data.Nat`, `Relation.Binary.PropositionalEquality`
- **顶层签名 (4)**: `boundary-points`, `interior-points`, `triangle-area`, `pick-identity`
- **质量**: `refl`×5；无 postulate / 无 hole

## `src/Sovereign/Structology/PlatonicTorusProjection.agda`

- **module**: `Sovereign.Structology.PlatonicTorusProjection`
- **行数**: 164（代码 87 / 注释 51）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | Sovereign.Structology.PlatonicTorusProjection
  - 柏拉图几何体 + 群信息论 → T⁶ 环面投影的等价映射 (类型级可证定理)
  - 物理锚定 (量子晶格 / 声子模型 / 神经网络训练验证):
  - 极向 144 = I_h 空间容器定义 = 子午线缠绕数
  - 环向 46  = I_H 时间分子振动分解 = 经度大圆缠绕数
  - 120 (十二面体胞腔) + 24 (梅尔卡巴/群信息论) = 柏拉图几何体与
  - 群信息论在环面上的投影 — 与缠绕容器 144 计数等价 (等价的映射),
  - 但分属不同范畴: 容器定义 vs 静态剖分。
  - 实验/训练证据: 石英声子等离子体 (Physics/QuartzPhonon.agda,
  - S2Sovereign 1.27B 训练验证), 螺旋测地线收敛到非平衡稳态极限环
  - (384K 步 LCM 环, dype wiki/06-experimental.md, C3 1500 步周期)。
  - 定理 (全部 0 postulate):
  - 1. polarContainerIsAtomic / toroidalTimeIsAtomic —
  - "不可拆解"的类型级可证形式: 原子表示恰一个构造子。
  - 2. 禁约分由原子类型承载 (PolarRep/ToroidalRep 上不存在任何
  - "k·72 / 72·23" 的合法表达式 — 约分不可表达, 见 HolographicPi)。
  - 3. platonicProjectionEquiv : Fin 144 ≃ (Fin 120 ⊎ Fin 24) —
  - 柏拉图剖分投影是 144 点容器上的等价映射 (计数等价,
- **导入 (10)**: `Data.Nat`, `Data.Nat.Properties`, `Data.Fin`, `Data.Fin.Properties`, `Data.Sum`, `Data.Product`, `Data.Empty`, `Relation.Nullary`, `Relation.Binary.PropositionalEquality`, `Sovereign.Structology.HolographicPi`
- **record 类型**: `_`, `WindingContainer`
- **顶层签名 (10)**: `polarContainerIsAtomic`, `toroidalTimeIsAtomic`, `platonic-to`, `platonic-from`, `platonic-to-from₁`, `platonic-to-from₂`, `platonic-to-from`, `platonic-from-to`, `platonicProjectionEquiv`, `standardContainer`
- **质量**: `refl`×3；无 postulate / 无 hole

## `src/Sovereign/Structology/Platonics.agda`

- **module**: `Sovereign.Structology.Platonics`
- **行数**: 491（代码 201 / 注释 224）
- **OPTIONS**: `--rewriting`
- **头部注释（数学背景）**:
  - | Sovereign.Structology.Platonics
  - 五正多面体 → 五行基数: 对称群特征模数的 CRT 投影形式化
  - 【证明路径】(v5.3, 2026-07-03)
  - 研究路径分为两个阶段:
  - 阶段一 (S²/S³ 建模):
  - 1. 五正多面体嵌入 S² 球面, 每个多面体的对称群 G 作用在球面上
  - 2. G 的阶数 |G| 通过 CRT 投影映射到环面 Z_144×Z_46 的余数空间
  - 3. 余数空间中非平凡同余类的最小代表 = 五行基数
  - 阶段二 (CRT + 幻方正交拓扑, 后期发展):
  - 4. M₄ 幻方 CRT 模 216 桥 (256≡40 mod 216) 提供了群体投影的统一框架
  - 5. P_CRT: |G| → 基数 是 P_CRT: ±2√10 → ±16 的泛化
  - 6. 幻方正交判据 ⟨v_λi, v_λj⟩=0 确保五个基数在 CRT 空间中正交
  - 【火/A₄ → 2 的完整证明链】(已在 ZeroGeometry + A4Group 中部分建立)
  - A₄ 群阶数=12, S²/A₄ 胞腔数=12, 陈数 C=2=χ(S²)
  - C₃ 生成元作用下, 12个胞腔分为 4 条 C₃ 轨道 (每条大小=3)
  - 每条 C₃ 轨道有两个非平凡方向 (CW/CCW), 因此基数=2
- **导入 (18)**: `Data.Nat`, `Data.Nat.DivMod`, `Data.Fin`, `Data.Integer`, `Data.Product`, `Relation.Binary.PropositionalEquality`, `Data.Empty`, `Data.Nat`, `Data.Nat.DivMod`, `Data.Unit`, `Relation.Nullary.Decidable`, `Sovereign.Structology.A4Group`, `Sovereign.Base.ZeroGeometry`, `Sovereign.Structology.Winding`, `Sovereign.Structology.MagicSquareM4`, `Data.Nat`, `Sovereign.Structology.T6`, `Data.Nat.Properties`
- **data 类型**: `SymmetryGroup`, `WuXingBase`
- **record 类型**: `PlatonicGroup`
- **顶层签名 (33)**: `groupOrder`, `groupOrderA4`, `platonicToGroup`, `groupOrderOfTetrahedron`, `baseToℕ`, `SOVEREIGN_LCM`, `POLAR`, `TOROIDAL`, `projectToTorus`, `projectA4`, `projectOh`, `projectIh`, `projectI`, `projectO`, `fireBaseDerived`, `earthBaseDerived`, `metalBaseDerived`, `waterBaseDerived`, `woodBaseDerived`, `basesProductNondegenerate`, `maxProduct`, `maxProductLtLCM`, `allProducts`, `allProductsLtLCM`, `basesMutuallyIrreducible`, `tetrahedronGroup`, `hexahedronGroup`, `dodecahedronGroup`, `icosahedronGroup`, `octahedronGroup`, `PolarCircle`, `ToroidalCircle`, `Torus2D`
- **质量**: `refl`×22；⚠️ 3 postulate

## `src/Sovereign/Structology/ProjPlane.agda`

- **module**: `Sovereign.Structology.ProjPlane`
- **行数**: 42（代码 14 / 注释 18）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | Sovereign.Structology.ProjPlane
  - 51 几何补强 — 射影平面 PG(2,3) (0 postulate)
  - PG(2,3) (GF(3) 上的射影平面): 13 点, 13 线, 每线 4 点, 每点过 4 线。
  - 点: 9 仿射点 (x,y) + 4 无穷远点 (斜率 0,1,2,∞)
  - 线: 12 仿射线 (y = mx+b 9 条 + 竖线 x = c 3 条) + 1 无穷远线
  - 对偶计数: 13×4 = 52 = 4×13 (自对偶)
- **导入 (2)**: `Data.Nat`, `Relation.Binary.PropositionalEquality`
- **顶层签名 (6)**: `pg-points`, `pg-lines`, `incidence-count`, `duality`, `total-incidence`, `line-at-infinity`
- **质量**: `refl`×5；无 postulate / 无 hole

## `src/Sovereign/Structology/QuantumBridge.agda`

- **module**: `Sovereign.Structology.QuantumBridge`
- **行数**: 1133（代码 385 / 注释 540）
- **OPTIONS**: `--cubical --guardedness --rewriting`
- **头部注释（数学背景）**:
  - | Sovereign.Structology.QuantumBridge
  - 量子数学桥：CRT域 ←→ 幻方正交 ←→ T⁶环面
  - 将已有证明串联为统一框架, 不引入新 postulate。
  - 全部使用 refl 验证代数关系。
- **导入 (33)**: `Data.Fin`, `Data.Nat`, `Data.Nat.Properties`, `Data.Sum`, `Data.Product`, `Relation.Nullary`, `Relation.Nullary.Decidable.Core`, `Data.Unit`, `Function`, `Relation.Binary.PropositionalEquality`, `Sovereign.MetaStructure.WuXing`, `Sovereign.Structology.Winding`, `Sovereign.Structology.MagicSquare144`, `Sovereign.Structology.MagicSquareM4`, `Sovereign.Arithmetic.CRTLemmas`, `Sovereign.RootMath.DigitalRoot`, `Data.List`, `Data.Bool`, `Data.Integer`, `Sovereign.Coupling.LCM`, `Sovereign.Format.CRT`, `Sovereign.Structology.T6`, `Sovereign.Structology.Platonics`, `Sovereign.Format.CRT`, `Sovereign.Structology.MagicSquareM4`, `Sovereign.Base.Trit`, `Data.Vec`, `Sovereign.Format.CRT`, `Sovereign.Algebra.GF9`, `Sovereign.Structology.A4Group`, `Sovereign.Structology.T6`, `Sovereign.Structology.T6`, `Sovereign.Base.Trit`
- **record 类型**: `Telescope`, `TorusLatticePoint`
- **顶层签名 (91)**: `wuXing-sum`, `wuXing-sum-25`, `magic-34-minus-wuxing-25`, `full-tour-6624`, `polar-is-A4-squared`, `toroidal-digital-root`, `toroidal-root-1`, `wuxing-times-12`, `m-mod-fulltour`, `tours-per-M`, `chiral-symmetry`, `toroidal-46-minus-16`, `chiral-16-mod3`, `chiral-neg16-mod3`, `piH-irreducible`, `alignment-vs-tour`, `spiral-period-6`, `spiral-steps`, `spirals-per-polar-winding`, `spirals-per-toroidal`, `truncation-ratio`, `truncation-remainder`, `tours-till-carry`, `polar-digital-root`, `toroidal-digital-root-1`, `one-not-stable`, `three-is-stable`, `seven-not-stable`, `wuxing-digital-roots`, `wuxing-roots`, `wuxing-dual-structure`, `T6-points`, `torus-points`, `zhonglv-crt`, `pow3-exponent-is-11`, `twelve-is-3-times-4`, `c3-order-3`, `chiral-conjugate-gf3`, `self-conjugate-gf3`, `chiral-square-is-identity`, `GF3⁶`, `c3-rotate`, `c3-rotate3-id`, `c3-conjugate`, `c3-conjugate3-id`, `rotate-T1-is-T2`, `conjugate-T2-is-T1`, `c3-table-00`, `c3-table-01`, `c3-table-02`, `c3-table-10`, `c3-table-11`, `c3-table-12`, `c3-table-20`, `c3-table-21`, `c3-table-22`, `c3-inverse`, `inverse-law-0`, `inverse-law-1`, `inverse-law-2`
  - … 其余 31 项
- **质量**: `refl`×125；无 postulate / 无 hole

## `src/Sovereign/Structology/S3IsGL22.agda`

- **module**: `Sovereign.Structology.S3IsGL22`
- **行数**: 171（代码 122 / 注释 26）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | Sovereign.Structology.S3IsGL22
  - S₃ ≅ GL(2,2): SP2 含反射全对称的 GF(2) 矩阵实现 (0 postulate)
  - GL(2,2) = GF(2) 上 det=1 的 2×2 可逆矩阵, 共 6 个, 与 S₃ 同构。
  - 阶分解: 1 个单位元 (阶 1) + 3 个对换 (阶 2) + 2 个三循环 (阶 3) = 6,
  - 非交换 (唯一 6 阶非交换群即 S₃)。这是 SP2 含反射对称的代数载体,
  - GF(2) 只服务于 SP2 的反射, 不进入 GF(3)/GF(9) 主基座。
- **导入 (5)**: `Data.Nat`, `Data.Fin`, `Data.Bool`, `Data.Product`, `Relation.Binary.PropositionalEquality`
- **record 类型**: `Mat2`
- **顶层签名 (12)**: `gadd`, `gmul`, `mulMat2`, `det2`, `mat`, `_⊗_`, `mul-hom`, `orderOf`, `order-identity`, `order-two-count`, `order-three-count`, `non-abelian`
- **质量**: `refl`×43；无 postulate / 无 hole

## `src/Sovereign/Structology/SL23Cayley.agda`

- **module**: `Sovereign.Structology.SL23Cayley`
- **行数**: 1376（代码 1310 / 注释 35）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | Sovereign.Structology.SL23Cayley
  - SL(2,3) 的 Cayley 表与 576 对封闭性 (GF(3) 定义表示, 0 postulate)
  - 深度证明 (补充 BinaryTetrahedralDefiningRep): SL(2,3) = {det=1 的 GF(3) 2×2 矩阵},
  - 24 元素在矩阵乘法下封闭。本模块以 24×24 = 576 对 Cayley 表穷举证明同态:
  - toMat (x ⊗ y) ≡ mulMat2 (toMat x) (toMat y)
  - 封闭性亦由 det 乘法性保证 (det(AB)=det(A)det(B)=1), 此处显式穷举与理论一致。
- **导入 (8)**: `Data.Nat`, `Data.Fin`, `Data.Bool`, `Data.Product`, `Data.Empty`, `Data.Unit`, `Relation.Binary.PropositionalEquality`, `Sovereign.Structology.BinaryTetrahedralDefiningRep`
- **record 类型**: `Mat2`
- **顶层签名 (16)**: `add3`, `mul3`, `mulMat2`, `toMat`, `_⊗_`, `toMat-hom`, `matI`, `powMat`, `order-pow`, `eq3`, `isI`, `isI-matI`, `true≢false`, `not-isI`, `min-checks`, `order-minimal`
- **质量**: `refl`×680；无 postulate / 无 hole

## `src/Sovereign/Structology/SL23Trace.agda`

- **module**: `Sovereign.Structology.SL23Trace`
- **行数**: 91（代码 52 / 注释 25）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | Sovereign.Structology.SL23Trace
  - 矩阵 → 迹 → 特征标: SL(2,3) 定义表示的显式迹 (0 postulate)
  - 表示论的源头是矩阵: 特征标是矩阵的迹。本模块显式证明:
  - 对每个 g ∈ SL(2,3), traceMat(toMat g) ≡ classTrace(classOf g)  (迹 mod 3)
  - 结合 BinaryTetrahedralDefiningRep 的 chi2FromRep (Brauer 提升 lift ∘ order),
  - 得到完整链: 矩阵 → 迹(mod3) + 阶(特征值结构) → χ₂。
  - 注意: SL(2,3) 的定义表示是 GF(3) 上的 det=1 矩阵 (无分母), 这是矩阵构造的源头;
  - 其在特征 0 的忠实二维表示需 1/2 (「半元素」), 故 Z[ω,i] 整环上无忠实二维矩阵表示,
  - 迹含 ω 的 χ₂′/χ₂″ 由张量积 χ₂ ⊗ {χ₁′,χ₁″} 导出 (见 BinaryTetrahedralTwoDimTensors)。
- **导入 (5)**: `Data.Fin`, `Data.Product`, `Relation.Binary.PropositionalEquality`, `Sovereign.Structology.BinaryTetrahedralDefiningRep`, `Sovereign.Structology.SL23Cayley`
- **顶层签名 (5)**: `traceMat`, `classTrace`, `trace-correct`, `trace-identity`, `trace-values-summary`
- **质量**: `refl`×32；无 postulate / 无 hole

## `src/Sovereign/Structology/SP2Ternary.agda`

- **module**: `Sovereign.Structology.SP2Ternary`
- **行数**: 88（代码 33 / 注释 32）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | Sovereign.Structology.SP2Ternary
  - SP2 三进制读法: 两条轨道岔口 (0 postulate, 纯 Z/3 计算)
  - SP2 = 磁→光的电磁场转化。它的三进制表示把三个方向/频率标成 Z/3 = {0,1,2},
  - 生成操作落在两条不同轨道上, 恰对应卢先生的两条原话:
  - * 倍频 ×2 (二进制读法): 轨 {1,2}, 周期 2, 永不归零 — 「2 SP 2 重金属」/乌比斯环
  - * 加一 +1 (三进制读法): 轨 {0,1,2}, 周期 3, 闭合归零 — 「任何的零都是三个的」
  - 本模块只证明算子的轨道结构 (refl / λ()); 物理/本体论解读见知识库, 不进入证明链。
- **导入 (3)**: `Data.Fin`, `Relation.Binary.PropositionalEquality`, `Relation.Nullary.Negation`
- **顶层签名 (12)**: `SP2Dir`, `double`, `succ3`, `double-1`, `double-2`, `double-1-not-zero`, `double-2-not-zero`, `succ3-0`, `succ3-1`, `succ3-2`, `double-0`, `succ3-closes`
- **质量**: `refl`×9；无 postulate / 无 hole

## `src/Sovereign/Structology/StandingWave.agda`

- **module**: `Sovereign.Structology.StandingWave`
- **行数**: 73（代码 28 / 注释 29）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | Sovereign.Structology.StandingWave
  - 三代 = 三个驻波构型 (波节 T₀ / 波峰 T₁ / 波谷 T₂), 0 postulate
  - 本体: 三代费米子不是三个独立粒子, 而是同一手征旋转 (CW/CCW 共轭) 的
  - 三个稳定驻波构型。A₄ 三维表示在 Z₃ 子群上分支 3 = 1 ⊕ 1′ ⊕ 1″,
  - 三个一维特征标恰好是三个驻波构型 (波节/波峰/波谷)。
  - 干涉规则 (GF(3) 加法 ⊕):
  - 同相     T₁ ⊕ T₁ = T₂   (波峰 + 波峰 → 波谷)
  - 反相     T₁ ⊕ T₂ = T₀   (波峰 + 波谷 → 波节)
  - 同相偏移 T₂ ⊕ T₂ = T₁   (波谷 + 波谷 → 波峰)
  - 三代循环 (⊕ T₁ 即 C₃ 生成元): T₀ → T₁ → T₂ → T₀ (生之序)
- **导入 (4)**: `Data.Product`, `Relation.Binary.PropositionalEquality`, `Sovereign.Base.Trit`, `Sovereign.Structology.A4Representation`
- **顶层签名 (10)**: `WaveMode`, `node`, `peak`, `trough`, `interfere`, `law-peak`, `law-node`, `law-trough`, `gen-cycle`, `generation`
- **质量**: `refl`×8；无 postulate / 无 hole

## `src/Sovereign/Structology/T6.agda`

- **module**: `Sovereign.Structology.T6`
- **行数**: 1500（代码 1076 / 注释 225）
- **OPTIONS**: `--cubical --guardedness --rewriting`
- **头部注释（数学背景）**:
  - | Sovereign.Structology.T6
  - T⁶ 离散商空间：复三维/实六维环面的内禀定义
  - 一句话定位: T⁶ = (GF(3))⁶ = 729 点有限离散空间, 4320D 基 3 归约引擎。
  - 核心原则:
  - ① 有限模型论 — ∀ over Fin 729 可判 (toℕ-sum-injective, leftInv/rightInv)
  - ② 4320D 剥离链 — sum%3-N/sum/3-N 纯模运算数字提取 (6层→0层)
  - ③ REWRITE 规则 — div3k/mod3k/gf3Toℕ-A4-inv 替代 mod-helper 表达式展开
  - 主定理: T6Lattice ≃ Fin 729 (t6ToFin/finToT6 双射, 左逆 toℕ-sum-injective 4320D 剥离链, 右逆 DivMod 代数)
- **导入 (45)**: `Agda.Builtin.Equality`, `Agda.Builtin.Nat`, `Agda.Builtin.Equality.Rewrite`, `Data.Nat`, `Data.Nat`, `Data.Nat.Properties`, `Data.Fin`, `Data.Fin`, `Data.Fin.Properties`, `Data.Vec`, `Data.Product`, `Data.Empty`, `Data.Integer`, `Cubical.Foundations.Prelude`, `Relation.Binary.PropositionalEquality`, `Relation.Binary.PropositionalEquality`, `Data.Nat.DivMod`, `Cubical.HITs.SetTruncation`, `Cubical.HITs.SetTruncation.Properties`, `Cubical.HITs.SetQuotients`, `Cubical.Foundations.Equiv`, `Cubical.Relation.Nullary`, `Cubical.Relation.Nullary.Properties`, `Cubical.Data.Equality.Conversion`, `Data.Vec.Properties`, `Data.Nat.DivMod`, `Data.Nat.Divisibility`, `Sovereign.Structology.A4Group`, `Data.Nat.Properties`, `Cubical.Foundations.Isomorphism`, `Cubical.Foundations.Univalence`, `Data.Fin.Properties`, `Relation.Nullary`, `Cubical.Foundations.Prelude`, `Cubical.HITs.SetQuotients.Properties`, `Cubical.HITs.SetTruncation.Properties`, `Cubical.Foundations.Isomorphism`, `Cubical.Data.Equality.Conversion`, `Cubical.Foundations.HLevels`, `Data.Vec`, `Data.Fin`, `Relation.Binary.PropositionalEquality`, `Data.Nat`, `Data.Nat.Properties`, `Data.Product`
- **data 类型**: `CellDimension`, `LüLabel`
- **record 类型**: `Cell`, `QuotientT6A4`, `HomologyGroup`, `HoloGCD`
- **顶层签名 (91)**: `GF3`, `T6Lattice`, `iterate`, `t6Cardinality`, `toℕ-sum`, `toℕ-sum-nested`, `right-assoc-6`, `finToT6`, `t6ToFin`, `right-assoc-3`, `right-assoc-4`, `right-assoc-5`, `factor-right-2`, `factor-right-3`, `factor-right-4`, `factor-right-5`, `factor3-2`, `factor3-3`, `factor3-4`, `factor3-5`, `mod3N`, `div3-gf3`, `div3-add`, `sum5`, `sum4`, `sum3`, `sum2`, `expand-chain`, `peel`, `rightInv`, `toℕ-sum-injective`, `leftInv`, `t6≃fin729`, `iterate-3n`, `iterate-id`, `iterate-cong`, `vertexCount`, `A4Element`, `_⊙_`, `applyPerm`, `a4Action`, `A4OrbitEquiv`, `Orbit`, `CosetEquiv`, `Stab`, `φ`, `discreteGF3`, `isSetGF3`, `discreteT6`, `isSetT6Lattice`, `isSetOrbit`, `orbitIso`, `orbitStabilizer-path`, `orbitStabilizer`, `zero-fixed`, `zeroOrbitSize1`, `only-id-fixes-v-star`, `step1`, `step2`, `step1-cubed-id`
  - … 其余 31 项
- **REWRITE 规则**: `div3k`, `mod3k`, `gf3Toℕ`
- **质量**: `refl`×101；⚠️ 3 postulate

## `src/Sovereign/Structology/T6A4Burnside.agda`

- **module**: `Sovereign.Structology.T6A4Burnside`
- **行数**: 295（代码 167 / 注释 88）
- **OPTIONS**: `--rewriting`
- **头部注释（数学背景）**:
  - 本模块是 HFM 交叉验证测试向量, 不替代原形式化证明。
  - 主证明见: T6.agda, BurnsideT6.agda
  - | Sovereign.Structology.T6A4Burnside
  - T⁶/A₄ Burnside 轨道计数：A₄ 置换 T⁶ 前 4 个坐标
  - HFM 交叉验证 (HaskellForMaths, 见 test/T6Burnside.hs)：
  - A₄ 在 GF(3)⁴ 上的 Burnside：180/12 = 15 个轨道
  - 在全 T⁶ (=GF(3)⁶) 上，后 2 坐标固定：15×9 = 135 个轨道
  - 不动点结构：
  - C₁ (恒等, |C|=1)：  所有 3⁴ = 81 点均不动
  - C₂ (双对换, |C|=3)：v₀=v₁, v₂=v₃ → 3² = 9 个不动点
  - C₃ (3-循环, |C|=4)：v₀=v₁=v₂, v₃ 自由 → 3² = 9 个不动点
  - C₄ (另一 3-循环, |C|=4)：同上 → 9 个不动点
  - Burnside 和 = 81 + 3·9 + 4·9 + 4·9 = 180
  - 轨道数 = 180 / 12 = 15
- **导入 (3)**: `Data.Nat`, `Relation.Binary.PropositionalEquality`, `Relation.Binary.PropositionalEquality`
- **顶层签名 (37)**: `fix-identity-GF3⁴`, `fix-identity-T6`, `fix-double-transposition-GF3⁴`, `fix-3cycle-GF3⁴`, `burnside-sum-GF3⁴`, `orbit-count-GF3⁴`, `orbit-count-T6`, `burnside-sum-correct`, `orbit-count-GF3⁴-correct`, `orbit-count-T6-correct`, `orbit-count-divisibility`, `orbit-count-chain`, `total-points-T6`, `burnside-sum-T6`, `burnside-sum-T6-correct`, `orbit-count-T6-full`, `orbit-count-T6-full-ok`, `cross-check-5x27`, `cross-check-5x27-ok`, `burnside-sum-G`, `orbit-count-G`, `orbit-size-G`, `burnside-sum-G-ok`, `orbit-count-G-ok`, `orbit-size-G-ok`, `orbit-count-stab12`, `orbit-size-stab12`, `orbit-count-stab3`, `orbit-size-stab3`, `orbit-count-stab2`, `orbit-size-stab2`, `orbit-count-stab1`, `orbit-size-stab1`, `total-orbits-csp`, `total-orbits-csp-ok`, `total-points-csp`, `total-points-csp-ok`
- **质量**: `refl`×1；无 postulate / 无 hole

## `src/Sovereign/Structology/T6FiveDimensionalProjection.agda`

- **module**: `Sovereign.Structology.T6FiveDimensionalProjection`
- **行数**: 150（代码 73 / 注释 40）
- **OPTIONS**: `--cubical --rewriting --guardedness`
- **头部注释（数学背景）**:
  - | Sovereign.Structology.T6FiveDimensionalProjection
  - T⁶ 五维物理投影: 六枚坐标的显式维度标注 (0 postulate, 无洞)
  - T⁶ = (x, y, z, cL, cR, g)
  - = 三个空间维 (Space3) × 两个手征维 (Chiral2) × 一个规范相位维 (Gauge1)
  - 五维物理投影 FiveD = Space3 × Chiral2 (3+2), 规范相位为纤维方向:
  - fiveOf 对相位不敏感 (fiveOf-gauge-independent), 相位承载 Z₃ 规范圈。
  - 语义标注 (dimTag, 6 例 refl):
  - 坐标 0,1,2 → Space (x, y, z); 坐标 3,4 → Chiral (cL, cR); 坐标 5 → Gauge (g)
  - 手征语义 (spinLabel, 3 例 refl, 与 ChiralInterference.cw/ccw/rest 对齐):
  - 0 → rest (静止), 1 → cw (右旋), 2 → ccw (左旋)  — 两列反向波叠加 → 驻波
  - 与 T6.agda 的 729 双射对接: project729 = decompose ∘ finToT6
  - 为后续物理模块提供维度框架 (本体层 PhysicalOntology: 5D 以太 = T⁶ + GF(9))。
- **导入 (5)**: `Data.Fin`, `Data.Product`, `Data.Vec`, `Relation.Binary.PropositionalEquality`, `Sovereign.Structology.T6`
- **data 类型**: `DimTag`, `Spin`
- **顶层签名 (23)**: `Space3`, `Chiral2`, `Gauge1`, `FiveD`, `dimTag`, `spinLabel`, `decompose`, `recompose`, `decompose∘recompose`, `recompose∘decompose`, `spaceOf`, `chiralOf`, `gaugeOf`, `fiveOf`, `recompose∘labels`, `setGauge`, `fiveOf-gauge-independent`, `gaugeOf-setGauge`, `chiralFlip`, `chiralFlip-involutive`, `chiralFlip-preserves-space`, `chiralFlip-preserves-gauge`, `project729`
- **质量**: `refl`×12；无 postulate / 无 hole

## `src/Sovereign/Structology/TetrahedralA4.agda`

- **module**: `Sovereign.Structology.TetrahedralA4`
- **行数**: 68（代码 24 / 注释 27）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | Sovereign.Structology.TetrahedralA4
  - 正四面体旋转群 = A₄: 元素阶分解 1 + 3×2 + 8×3 (0 postulate)
  - 卢先生原生锚: 正四面体 = 「两个周期」(180° 双对换, 阶 2) + 「三生三」(120° 三循环, 阶 3)。
  - A₄ 的元素阶结构 (1, 2,2,2, 3,3,3,3,3,3,3,3) 与之逐项对应:
  - 1 个单位元 (阶 1, 无旋转)
  - 3 个双对换 Flip (阶 2, 180° 绕对边中点轴, 「两个周期归零」)
  - 8 个三循环 Rot (阶 3, 120°/240° 绕顶点-面轴, 「三生三、三再乘三」)
  - 本模块把「阶结构」作为正四面体旋转群的代数指纹, 与 A4Group 的群结构桥接;
  - 物理/本体论解读 (sp3 四面体 = 频率+时间+空间) 属命名层, 不进入证明链。
- **导入 (4)**: `Data.Nat`, `Data.Fin`, `Relation.Binary.PropositionalEquality`, `Sovereign.Structology.A4Group`
- **顶层签名 (7)**: `orderOf`, `order-id`, `order-rot`, `order-flip`, `rot-count`, `order-decomposition`, `flip-self-inverse`
- **质量**: `refl`×9；无 postulate / 无 hole

## `src/Sovereign/Structology/TopologyLevels.agda`

- **module**: `Sovereign.Structology.TopologyLevels`
- **行数**: 167（代码 88 / 注释 49）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | Sovereign.Structology.TopologyLevels
  - 结构学：多层级拓扑定义（磁性、中性、全息）
  - 本模块旨在纠正以往使用“电性文明”（连续统/有理数/复数）定义拓扑的错误。
  - 我们在此严格依据《律算算经 v2.5》，分三个文明层级实现“联络与周天拓扑”。
  - 1. 磁性文明 (24 密度): 基于六十甲子的离散模运算
  - 2. 中性文明 (144 密度): 基于主权 LCM 模数的整数推演
  - 3. 全息文明 (4320 密度): 基于公理的瞬时同步
- **导入 (6)**: `Data.Fin`, `Data.Nat`, `Data.Integer`, `Relation.Binary.PropositionalEquality`, `Sovereign.Structology.LuCellGrid`, `Data.Integer`
- **record 类型**: `Curvature`, `HolographicTorus`
- **质量**: `refl`×2；无 postulate / 无 hole

## `src/Sovereign/Structology/TorusClosure.agda`

- **module**: `Sovereign.Structology.TorusClosure`
- **行数**: 34（代码 14 / 注释 14）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | Sovereign.Structology.TorusClosure
  - 定理三: T⁶ 离散环面的代数闭包与无无穷远定理
  - 在 T⁶ = (GF(3))⁶ (729 格点) 上, 原生 Frobenius σ(x)=x³ 下,
  - 映射空间同时满足:
  - ① 几何闭包 — 无射影无穷远, Fin 729 有限编码
  - ② 代数共轭 — σ 是域自同构, 盲区可见
  - ③ 描述完备 — 全局函数表矩阵 M_F 精确判定
  - 证明: jac_4320DClosure.agda (鸽子笼原理 T⁶ 推广, 0 postulate)
  - jac_EscapeAnalysis.agda (Alpöge 反例阻断分析)
  - Structology.T6 (t6ToFin/finToT6 双射, Fin 729 编码)
- **导入 (2)**: `Data.Fin`, `Data.Product`
- **record 类型**: `TorusClosure`, `TripleClosure`
- **质量**: `refl`×0；无 postulate / 无 hole

## `src/Sovereign/Structology/VectorDirection.agda`

- **module**: `Sovereign.Structology.VectorDirection`
- **行数**: 95（代码 36 / 注释 36）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | Sovereign.Structology.VectorDirection
  - 矢量方向计数: 卢先生「幻方」的矢量义 (0 postulate)
  - 术语边界 (docs/cross-level/magic-square-terminology.md):
  - 卢先生「幻方」的阶数 n = 同时在变的矢量方向(变量)个数, 与「行列对角线和」无关。
  - 本模块把这一矢量义形式化:  n 阶幻方 = n 个矢量方向 = Vec Trit n (Tⁿ 环面的 n 维)。
  - 对齐离散全息框架:
  - 一个矢量方向 = 一个 GF(3) 自由度 (Trit)
  - n 个矢量方向 = Vec Trit n  (GF(3)ⁿ, 共 3ⁿ 个格点)
  - T⁶ 环面 = 6 个矢量方向 = Vec (Fin 3) 6  (Trit ≅ Fin 3)
  - 4 阶  = 3 空间 + 1 时间 = 4 个矢量方向
  - 144 阶 = 12 维对称关系 = 12 × 12 = 144 个矢量方向/力学关系
  - 排列数 n! = 置换群 Sₙ 的大小 (144! ≈ 1.51×10⁹⁶, 组合爆炸非浮点精度)
- **导入 (5)**: `Data.Nat`, `Data.Fin`, `Data.Vec`, `Relation.Binary.PropositionalEquality`, `Sovereign.Base.Trit`
- **顶层签名 (13)**: `Direction`, `MagicSquareᵛ`, `order`, `tritToFin`, `fourDirections`, `sixDirections`, `order-four`, `order-six`, `twelve-squared`, `t6-points`, `fact`, `fact18`, `fact19`
- **质量**: `refl`×8；无 postulate / 无 hole

## `src/Sovereign/Structology/Winding.agda`

- **module**: `Sovereign.Structology.Winding`
- **行数**: 137（代码 43 / 注释 69）
- **OPTIONS**: `--guardedness`
- **头部注释（数学背景）**:
  - | Sovereign.Structology.Winding
  - 结构学：极向缠绕数 144、环向缠绕数 46
  - 核心原则：缠绕数是不可拆分的拓扑不变量，由实验锚定
- **导入 (4)**: `Data.Nat`, `Data.Vec`, `Relation.Binary.PropositionalEquality`, `Relation.Nullary`
- **record 类型**: `HolomorphicPi`
- **顶层签名 (12)**: `PolarWinding`, `polarWindingValue`, `PolarWindingPath`, `ToroidalWinding`, `toroidalWindingValue`, `ToroidalWindingPath`, `holoPi`, `noReductionNumerator`, `noReductionDenominator`, `WindingVector`, `polarWindingVec`, `toroidalWindingVec`
- **质量**: `refl`×13；无 postulate / 无 hole

## `src/Sovereign/Structology/WuXingEulerHFM.agda`

- **module**: `Sovereign.Structology.WuXingEulerHFM`
- **行数**: 45（代码 26 / 注释 10）
- **OPTIONS**: `--rewriting`
- **头部注释（数学背景）**:
  - 本模块是 HFM 交叉验证测试向量, 不替代原形式化证明。
  - 主证明见: WuXingTransition.agda
  - | Sovereign.Structology.WuXingEulerHFM
  - 柏拉图立体 Euler 示性数的 HFM 交叉验证
- **导入 (3)**: `Data.Integer`, `Relation.Binary.PropositionalEquality`, `Relation.Binary.PropositionalEquality`
- **顶层签名 (15)**: `tetV`, `tetChi`, `tetChi-ok`, `cubeV`, `cubeChi`, `cubeChi-ok`, `octV`, `octChi`, `octChi-ok`, `dodV`, `dodChi`, `dodChi-ok`, `icoV`, `icoChi`, `icoChi-ok`
- **质量**: `refl`×1；无 postulate / 无 hole

## `src/Sovereign/Structology/WuXingTransition.agda`

- **module**: `Sovereign.Structology.WuXingTransition`
- **行数**: 912（代码 491 / 注释 297）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | Sovereign.Structology.WuXingTransition
  - 五行对称群跃迁链：A₄ → O_h → I_h → I → O → A₄
  - v5.5 (2026-07-03): 手性 Z₂ 因子生命周期 + 环向缠绕幂次 a 序参量
  - v5.6 (2026-07-03): Christoffel 螺旋深层推导 —— a序列和Z₂因子从离散测地线导出
  - 本质：Z₂ × S⁵ 主丛上的手性离合器状态机
  - S⁵ 参数化五个五行态
  - Z₂ 参数化反射对称的有无
  - 环向缠绕幂次 a 是控制 Z₂ 因子的序参量
  - a 奇数 → 含反射 (Z₂=Present)
  - a 偶数 → 纯旋转 (Z₂=Absent)
  - v5.6 深层推导链：
  - Christoffel螺旋 (1→2→4→8→7→5, 周期6)
  - → 模3投影 [1,2,1,2,1,2] = 损益交替 (1=Sun损一, 2=Yi益一)
  - → scanl 累加 [0,1,3,4,6] = a序列
  - → a奇偶性 → Z₂因子 (奇=含反射, 偶=纯旋转)
- **导入 (11)**: `Data.Nat`, `Data.Bool`, `Data.Vec`, `Data.Product`, `Relation.Binary.PropositionalEquality`, `Data.List`, `Sovereign.RootMath.DigitalRoot`, `Data.Vec`, `Sovereign.Structology.A4Group`, `Data.Fin`, `Sovereign.Base.ZeroGeometry`
- **data 类型**: `ClutchState`, `WuXingPhase`, `Z2Factor`, `SymmetryGroup`, `LossGain`, `Z2`, `FacePolygon`, `VertexDegree`
- **record 类型**: `HasZ2Factor`
- **顶层签名 (90)**: `allPhases`, `numPhases`, `aValue`, `chiralCopies`, `groupOrder`, `symmetryGroup`, `z2Presence`, `clutchState`, `transition`, `spiralMod3`, `spiralMod3-sequence`, `mod3ToLossGain`, `lossGainPattern`, `lossGainPattern-sequence`, `lossGainStep`, `derivedASequence`, `derivedA-sequence`, `derivedA-matches-defined`, `deriveZ2`, `derivedZ2-matches-defined`, `christos-guarantees-closure`, `christoffel-derives-all`, `transition-cycle`, `a-sequence`, `chiralCopies-sequence`, `groupOrder-sequence`, `z2-lifecycle`, `clutch-a-correspondence`, `z2-a-parity`, `a-accumulation`, `groupGrowth-sequence`, `expansion-phase`, `contraction-phase`, `z2Order`, `ohZ2`, `ihZ2`, `noZ2Factor`, `oh-has-Z2`, `ih-has-Z2`, `noZ2-in-pure-rotations`, `z2-acquisition`, `z2-loss`, `z2-acquired-at-Earth`, `z2-maintained-at-Metal`, `z2-lost-at-Water`, `a1-implies-Z2`, `a3-implies-Z2`, `a0-no-Z2`, `a4-no-Z2`, `a6-no-Z2`, `theorem-z2-lifecycle-via-group-theory`, `allA4Elements`, `a4Cardinality`, `a4-matches-fire`, `a4-pure-rotation`, `a4-vertex-count`, `a4-cardinality-correct`, `a4-to-o-ratio`, `a4-to-i-ratio`, `group-chain-from-a4`
  - … 其余 30 项
- **质量**: `refl`×200；无 postulate / 无 hole

## `src/Sovereign/Structology/XuanwuAbsorption.agda`

- **module**: `Sovereign.Structology.XuanwuAbsorption`
- **行数**: 232（代码 177 / 注释 22）
- **OPTIONS**: `--guardedness --rewriting`
- **导入 (19)**: `Agda.Builtin.Equality`, `Agda.Builtin.Nat`, `Agda.Builtin.Equality.Rewrite`, `Data.Nat`, `Data.Nat.Properties`, `Data.Bool`, `Data.Product`, `Data.Fin.Base`, `Data.Fin.Properties`, `Data.Empty`, `Relation.Nullary`, `Relation.Binary.PropositionalEquality`, `Data.Nat.DivMod`, `Data.Vec`, `Sovereign.Structology.Closure`, `Sovereign.Structology.Winding`, `Sovereign.Structology.MagicSquare144`, `Data.Nat.DivMod`, `Data.Nat.Properties`
- **data 类型**: `StepNotEq`
- **顶层签名 (25)**: `step-changes-toroidal`, `stepN-adds`, `never-stops-abstract`, `step-not-fixed-lemma`, `never-stops`, `zhonglv-adds`, `cycle-adds-13`, `cycleN-adds`, `reaches-alignment-in-46`, `xuanwu-selfheal`, `after-heal-leaves-alignment`, `zhonglv-resets-polar`, `polar-after-sync`, `general-alignment`, `fullTourMod144`, `fullTourMod46`, `full-tour-identity`, `theorem-17-xuanwu`, `full-tour-division`, `syncs-per-polar-winding`, `syncs-per-toroidal-winding`, `local-steps-per-full-tour`, `full-tour-equals-local`, `bezout-13-46`, `mod-inverse-13`
- **REWRITE 规则**: `mod46k`, `div46k`, `mod`
- **质量**: `refl`×18；⚠️ 2 postulate / 1 TODO

## `src/Sovereign/Structology/Zωi.agda`

- **module**: `Sovereign.Structology.Zωi`
- **行数**: 113（代码 49 / 注释 38）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | Sovereign.Structology.Zωi
  - Z[ω,i] 环: 2·A₄ = SL(2,3) 二维不可约表示的忠实环 (0 postulate)
  - 为什么需要 i: Z[ω] 只有 3 阶元素 (ω³=1), 但 2·A₄ 的二维表示需要 4 阶元素
  - (四元数单位 i,j,k)。二元四面体群的二维矩阵元素含 i, 迹却消去 i 落在 Z[ω]。
  - 因此深度证明的基环必须扩展为 Z[ω,i], 其中 i²=-1, ωi=iω。
  - 元素: a + bω + ci + dωi  (a,b,c,d ∈ ℤ)
  - 关系: ω² = -1-ω,  i² = -1,  ωi = iω,  (ωi)² = 1+ω
  - 乘法系数 (手工展开 + Python 穷举验证: 恒等式全过, 结合律 20 万组通过):
  - (a+bω+ci+dωi)(a′+b′ω+c′i+d′ωi)
  - = (aa′−bb′−cc′+dd′)
  - + (ab′+ba′−bb′−cd′−dc′+dd′)ω
  - + (ac′+ca′−bd′−db′)i
  - + (ad′+da′+bc′+cb′−bd′−db′)ωi
  - 注意: 本模块定义前, 初稿公式有两处错误 (ω 系数漏 +dd′, i 系数符号反),
  - 已由穷举反例 (ωi)²≠1+ω 与结合律反例否决并修正。此为「先算后写」纪律。
- **导入 (3)**: `Data.Integer.Base`, `Data.Product`, `Relation.Binary.PropositionalEquality`
- **record 类型**: `Zωi`
- **顶层签名 (15)**: `zeroZωi`, `oneZωi`, `ωZωi`, `iZωi`, `ωiZωi`, `addZωi`, `negZωi`, `subZωi`, `mulZωi`, `omega-squared`, `omega-sum-zero`, `i-squared`, `i-squared-zero`, `omega-i-comm`, `omegai-squared`
- **质量**: `refl`×8；无 postulate / 无 hole
