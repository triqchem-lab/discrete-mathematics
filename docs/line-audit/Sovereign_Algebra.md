# 目录 `src/Sovereign/Algebra/` 逐模块审计记录

共 77 个模块。


## `src/Sovereign/Algebra/AdjacencyMatrix.agda`

- **module**: `Sovereign.Algebra.AdjacencyMatrix`
- **行数**: 164（代码 89 / 注释 47）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | Sovereign.Algebra.AdjacencyMatrix
  - GF(9) 邻接矩阵与图谱基础
  - 语料锚: "幻方本征谱 {34, 0, 16, -16}" (torus-geometry-and-magic-square)
  - "谱有限性" (几何闭包问题)
  - 定义:
  - §1 通用 n 阶邻接矩阵 (Fin n → Fin n → GF9)
  - §2 矩阵乘法 (4 阶)
  - §3 对角线/迹
  - §4 对称性检测
  - §5 基本性质
  - 0 postulate.
- **导入 (6)**: `Data.Nat`, `Data.Fin`, `Data.Product`, `Relation.Binary.PropositionalEquality`, `Sovereign.Base.Trit`, `Sovereign.Algebra.GF9`
- **顶层签名 (17)**: `AdjMatrix`, `zeroAdj`, `AdjMatrix4`, `matI4`, `mulMat4`, `powMat4`, `zero-mat4-mulˡ`, `zero-mat4-pow`, `diag4`, `trace4`, `trace-zero`, `adj-transpose`, `Symmetric4`, `zero-symmetric`, `identity-symmetric`, `zero-diag`, `identity-diag`
- **质量**: `refl`×26；无 postulate / 无 hole

## `src/Sovereign/Algebra/AlgGeomBridge.agda`

- **module**: `Sovereign.Algebra.AlgGeomBridge`
- **行数**: 194（代码 109 / 注释 49）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | Sovereign.Algebra.AlgGeomBridge
  - 14 代数几何对接 — GF(9) 范数 1 圆锥 (离散曲线起点, 0 postulate)
  - 对接 MSC 14 的离散桥梁: 圆锥曲线 x² + y² = 1 在 GF(3) 上的点集
  - = { (1,0), (0,1), (2,0), (0,2) } — 恰 4 = q+1 点 (亏格 0, Weil 界取等)
  - 与 GF(9) 的范数 1 单位子群 {1, α, −1, −α} ≅ C₄ 一一对应:
  - z = x + yα, N(z) = z·σ(z) = x² + y² = 1 ⟺ (x,y) 在圆锥上
  - 结构: §1 圆锥 4 点枚举 + 非点反证; §2 范数 1 单位 (4 元素 + 闭包 16 项);
  - §3 对应与 Weil 注释 (亏格 0: #点 = q+1 = 4)。
- **导入 (6)**: `Data.Product`, `Data.Nat`, `Relation.Binary.PropositionalEquality`, `Relation.Nullary`, `Sovereign.Base.Trit`, `Sovereign.Algebra.GF9`
- **data 类型**: `Norm1`, `EPoint`
- **顶层签名 (30)**: `conic-point-10`, `conic-point-01`, `conic-point-20`, `conic-point-02`, `conic-nonpoint-11`, `neg-gf9`, `norm1-one`, `norm1-alpha`, `norm1-mone`, `norm1-malpha`, `norm1Elem`, `norm1Mul`, `norm1-closed`, `norm1-cycle-2`, `norm1-cycle-4`, `onE`, `onE-01`, `onE-02`, `onE-10`, `¬onE-00`, `¬onE-11`, `¬onE-12`, `¬onE-20`, `¬onE-21`, `¬onE-22`, `eadd`, `e01-order2`, `e01-order3`, `e01-order4`, `hasse-bound`
- **质量**: `refl`×34；无 postulate / 无 hole

## `src/Sovereign/Algebra/AlgebraicPoleUnified.agda`

- **module**: `Sovereign.Algebra.AlgebraicPoleUnified`
- **行数**: 476（代码 232 / 注释 160）
- **OPTIONS**: `--rewriting`
- **导入 (9)**: `Data.Product`, `Data.Nat`, `Data.Fin`, `Relation.Binary.PropositionalEquality`, `Sovereign.Base.Trit`, `Sovereign.Algebra.GF9`, `Sovereign.Algebra.GF9AlgebraicChain`, `Sovereign.Algebra.Duodecimal`, `Data.Nat`
- **record 类型**: `AlgebraicPole`
- **顶层签名 (35)**: `algebraic-pole`, `π3-ring-homomorphism`, `π3-surjective`, `π3-not-injective-witness`, `norm-to-gf3`, `trace-to-gf3`, `gf9-to-duodec-via-norm`, `gf9-to-duodec-via-trace`, `norm-path-roundtrip`, `trace-path-roundtrip`, `gf3-embed-norm`, `gf3-embed-trace`, `duodec-π3-embed`, `crt-section-right-inverse`, `AlgebraicPoleCarrier`, `algebraic-pole-order`, `algebraic-pole-complete`, `quantum-superposition-carrier`, `quantum-superposition-states`, `quantum-entanglement-carrier`, `quantum-entanglement-generator`, `quantum-entanglement-irreducible`, `vortex-phase-carrier`, `vortex-phase-advance`, `vortex-periodicity`, `subgroup-embedding-chain`, `subgroup-embedding-chain-4`, `subgroup-chain-compatible`, `crt-decomposition`, `vortex-root-12`, `octave-base`, `octave-2nd`, `octave-4th`, `merkaba-wraparound`, `water-three-cycles`
- **质量**: `refl`×28；无 postulate / 无 hole

## `src/Sovereign/Algebra/BCWDegeneracy.agda`

- **module**: `Sovereign.Algebra.BCWDegeneracy`
- **行数**: 26（代码 15 / 注释 4）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | Sovereign.Algebra.BCWDegeneracy
  - 定理二: BCW 矩阵代数的离散离心定理
- **导入 (4)**: `Relation.Binary.PropositionalEquality`, `Data.Product`, `Sovereign.Base.Trit`, `Sovereign.Algebra.Jacobian.jac_GF3`
- **顶层签名 (3)**: `fermat-cubic`, `BCW-Decoupling`, `proof`
- **质量**: `refl`×4；无 postulate / 无 hole

## `src/Sovereign/Algebra/Base10Degeneration.agda`

- **module**: `Sovereign.Algebra.Base10Degeneration`
- **行数**: 435（代码 178 / 注释 188）
- **OPTIONS**: `--rewriting --guardedness`
- **导入 (12)**: `Data.Nat`, `Data.Nat.Base`, `Data.Nat.Divisibility.Core`, `Data.Nat.DivMod`, `Data.Nat.Properties`, `Data.Empty`, `Data.Product`, `Data.Unit`, `Relation.Nullary`, `Relation.Binary.PropositionalEquality`, `Sovereign.Algebra.Duodecimal`, `Sovereign.RootMath.DigitalRoot`
- **record 类型**: `Base10Degeneration`
- **顶层签名 (32)**: `2∣12`, `3∣12`, `4∣12`, `6∣12`, `12-divisors`, `verify-half₁₂`, `verify-third₁₂`, `verify-quarter₁₂`, `verify-sixth₁₂`, `base12-all-terminating`, `3∤10`, `dr12`, `dr39`, `vortex-closure`, `vortex-3-12-3`, `3∣12-vortex`, `dr10`, `dr10-not-stable`, `2∣10`, `5∣10`, `4∤10`, `6∤10`, `separation-witness`, `separation-witness-6`, `base12-terminating-count`, `base10-one-digit-count`, `base12-richer`, `mod3-info-preserved-base12`, `mod3-info-lost-base10`, `base12-stable-root`, `base10-unstable-root`, `base10-is-degenerate`
- **质量**: `refl`×30；无 postulate / 无 hole

## `src/Sovereign/Algebra/BranchingRules.agda`

- **module**: `Sovereign.Algebra.BranchingRules`
- **行数**: 390（代码 182 / 注释 140）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | Sovereign.Algebra.BranchingRules
  - SO(3) → A₄ 分支规则: 连续李群表示限制到离散子群的分解表
  - 核心结果:
  - SO(3) spin-l 不可约表示 (dim 2l+1) 限制到 A₄ 后分解为:
  - l=0: V1                             (dim 1)
  - l=1: V3                             (dim 3)
  - l=2: V3 ⊕ V1' ⊕ V1''               (dim 5)  ← 修正: 非 V3⊕V1⊕V1'
  - l=3: V3 ⊕ V3 ⊕ V1                  (dim 7)
  - l=4: V3 ⊕ V3 ⊕ V1 ⊕ V1' ⊕ V1''    (dim 9)
  - l=5: V3 ⊕ V3 ⊕ V3 ⊕ V1' ⊕ V1''    (dim 11)
  - 证明策略: 穷举法 (l=0..5 逐案 refl) + 周期 6 递推 (l≥6)
  - 数学依据: 特征标内积 m_i = (1/12) Σ_C |C| χ_l(C) conj(χ_i(C))
  - 宪法合规:
  - 0 postulate
  - 禁止浮点数, 特征标值 ∈ Z[ω] (Eisenstein 整数)
  - 所有验证通过穷举 refl
- **导入 (6)**: `Data.Nat`, `Data.Integer`, `Data.Product`, `Relation.Binary.PropositionalEquality`, `Sovereign.RootMath.Eisenstein`, `Sovereign.Structology.A4Representations`
- **顶层签名 (46)**: `2ᵉ`, `5ᵉ`, `7ᵉ`, `9ᵉ`, `11ᵉ`, `12ᵉ`, `so3χ-C1`, `so3χ-C23`, `so3χ-C4`, `so3χ`, `so3χ-C1-0`, `so3χ-C1-2`, `so3χ-C1-5`, `so3χ-C23-period`, `so3χ-C4-period`, `a4χ`, `branchMult`, `dimSum`, `dimSum≡1`, `dimSum≡3`, `dimSum≡5`, `dimSum≡7`, `dimSum≡9`, `dimSum≡11`, `dimSum≡13`, `l2-V1≡0`, `l2-V3≡1`, `innerNum`, `inner-l2-V1`, `inner-l2-V3`, `inner-l0-V1`, `inner-l1-V3`, `decomp-l0`, `decomp-l1`, `decomp-l2`, `decomp-l3`, `decomp-l4`, `decomp-l5`, `pairing-0`, `pairing-1`, `pairing-2`, `pairing-3`, `pairing-4`, `pairing-5`, `pairing-general`, `V3-mult-formula`
- **质量**: `refl`×71；无 postulate / 无 hole

## `src/Sovereign/Algebra/C3Orbit.agda`

- **module**: `Sovereign.Algebra.C3Orbit`
- **行数**: 45（代码 21 / 注释 13）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | Sovereign.Algebra.C3Orbit
  - C₃ 轨道定理: {1,3,5} 在 +2 (mod 6) 下构成 C₃ 群轨道。
  - 对应三分损益 Sun=+1, Yi=+2 在指数域中的生成元作用。
  - C₃ 作用: a_i → a_{(i+2) mod 6}
  - 轨道: 1 → 3 → 5 → 1 (周期 3)
  - 不动点: {0,2,4} (偶数项, C₃ 作用下不变 mod 6?)
- **导入 (4)**: `Data.Nat`, `Data.Vec`, `Data.Product`, `Relation.Binary.PropositionalEquality`
- **顶层签名 (6)**: `add2-mod6`, `orbit-step-1`, `orbit-step-3`, `orbit-step-5`, `C3-mult-table`, `orbit-size`
- **质量**: `refl`×8；无 postulate / 无 hole

## `src/Sovereign/Algebra/ChainComplex.agda`

- **module**: `Sovereign.Algebra.ChainComplex`
- **行数**: 136（代码 44 / 注释 67）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | ChainComplex — GF(3) 离散链复形与同调
  - 连续统病态: 连续空间的链复形涉及无穷维向量空间
  - 离散自愈: GF(3) 上链复形是有限维, 同调群可精确计算
  - 核心结构:
  - §1. 链群: C_n = GF(3) 上的有限生成自由模
  - §2. 边界算子: ∂_n : C_n → C_{n-1}
  - §3. 基本定理: ∂² = 0 (边界之边界为零)
  - §4. 同调群: H_n = ker(∂_n) / im(∂_{n+1})
  - 复用: Sovereign.Base.Trit (GF(3) 运算)
  - 0 postulate.
- **导入 (5)**: `Data.Nat`, `Data.Product`, `Data.Vec`, `Relation.Binary.PropositionalEquality`, `Sovereign.Base.Trit`
- **顶层签名 (16)**: `ChainGroup`, `C₀`, `C₁`, `C₂`, `_⊖_`, `∂₁`, `∂₂`, `∂²-zero`, `zero-chain₀`, `zero-chain₁`, `ker-∂₁-const`, `betti₀`, `betti₁`, `euler-char`, `euler-combinatorial`, `euler-agree`
- **质量**: `refl`×8；无 postulate / 无 hole

## `src/Sovereign/Algebra/ChainZ3toZ12.agda`

- **module**: `Sovereign.Algebra.ChainZ3toZ12`
- **行数**: 248（代码 116 / 注释 100）
- **OPTIONS**: `--rewriting --guardedness`
- **导入 (6)**: `Sovereign.Geometry.ProjectiveCore`, `Data.Nat`, `Data.Product`, `Relation.Binary.PropositionalEquality`, `Sovereign.Base.Trit`, `Sovereign.Algebra.Duodecimal`
- **顶层签名 (16)**: `embed-3-12`, `embed-hom`, `embed-inj`, `embed-zero`, `crt12-rt`, `VortexFunc`, `Δ₁₂`, `swap-middle`, `Δ₁₂-linear`, `Δ₁₂-const-zero`, `char3-triple`, `char3-Δ³`, `Δ₁₂³-is-3step`, `vortex-chain`, `vortex-4320`, `phase-align`
- **质量**: `refl`×110；无 postulate / 无 hole

## `src/Sovereign/Algebra/CharacteristicTower.agda`

- **module**: `Sovereign.Algebra.CharacteristicTower`
- **行数**: 273（代码 120 / 注释 94）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | Sovereign.Algebra.CharacteristicTower
  - 特征塔与进制层级 — 坍缩判据 + 余数判据 (0 postulate)
  - 全部深层证明 (穷举 refl):
  - §1 乘法群阶: GF(2)=1, GF(4)=3, GF(3)=2, GF(9)=8
  - §2 坍缩判据: GF(4)无4阶元, GF(9)无3阶元
  - §3 余数判据: GF(3)x²+1无根, GF(9)α是根
  - §4 进制层级表: 五列对比 + CRT 分解
- **导入 (9)**: `Data.Nat`, `Data.Fin`, `Data.Product`, `Data.Bool`, `Data.Empty`, `Relation.Binary.PropositionalEquality`, `Sovereign.Base.Trit`, `Sovereign.Algebra.GF9`, `Sovereign.Physics.DiscreteEMField3D`
- **data 类型**: `BaseLevel`
- **顶层签名 (38)**: `GF2-star`, `GF2-mul-group-order-is-1`, `GF3-star-order-2`, `one-order-1`, `two-order-2`, `two-alpha-squared`, `one-plus-alpha-squared`, `two-plus-alpha-squared`, `two-plus-two-alpha-squared`, `one-cubed`, `two-cubed`, `alpha-cubed`, `two-alpha-cubed`, `one-plus-alpha-cubed`, `one-plus-two-alpha-cubed`, `two-plus-alpha-cubed`, `two-plus-two-alpha-cubed`, `x2-plus-1-no-root-0`, `x2-plus-1-no-root-1`, `x2-plus-1-no-root-2`, `x2-plus-1-no-root-GF3`, `alpha-is-root`, `three-mod-four`, `nine-mod-four`, `char-of`, `mul-group-order`, `has-90-rotation`, `BL-GF9-has-90`, `BL-GF2-no-90`, `BL-GF4-no-90`, `BL-GF3-no-90`, `BL-Z12-no-90`, `twelve-is-three-times-four`, `gf9-90-rotation-witness`, `gf2-no-90-rotation`, `gf3-no-90-rotation`, `affine`, `affine-identity`
- **质量**: `refl`×33；无 postulate / 无 hole

## `src/Sovereign/Algebra/CommAlgBridge.agda`

- **module**: `Sovereign.Algebra.CommAlgBridge`
- **行数**: 143（代码 53 / 注释 56）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | Sovereign.Algebra.CommAlgBridge
  - 13H 交换代数对接 — 二次整数环的整除性/分歧结构 (0 postulate)
  - 对接 MSC 13 的离散桥梁: Z[i] 与 Z[ω] 的 Euclidean 性质
  - (范数除法) 以具体见证 refl 呈现:
  - Z[i]: 2 分歧 (2 = (1+i)(1−i)), 5 分裂 (5 = (2+i)(2−i))
  - Z[ω]: 3 分歧 (3 = (1−ω)(1−ω²)), 7 分裂 (7 = (3+ω)(2−ω))
  - 素数分类 (注释): Z[i]: p ≡ 1 mod 4 分裂 / p ≡ 3 mod 4 惰性 / 2 分歧;
  - Z[ω]: p ≡ 1 mod 3 分裂 / p ≡ 2 mod 3 惰性 / 3 分歧。
  - 结构路线 (Euclidean 算法全称版 / 主理想分解) 留待深化 — 未以 postulate 驻留。
- **导入 (5)**: `Data.Integer`, `Data.Product`, `Relation.Binary.PropositionalEquality`, `Sovereign.RootMath.Gaussian`, `Sovereign.RootMath.Eisenstein`
- **顶层签名 (18)**: `gauss-2-ramifies`, `gauss-2-norm`, `gauss-5-splits`, `gauss-5-norm`, `eis-3-ramifies`, `eis-3-norm`, `eis-7-splits`, `eis-7-norm`, `gauss-euclid-witness`, `gauss-euclid-remainder-norm`, `gauss-euclid-divisor-norm`, `quot-product`, `quot-residue-zero`, `quot-hom-sample`, `gauss-ramification-summary`, `gauss-splitting-summary`, `eis-ramification-summary`, `eis-splitting-summary`
- **质量**: `refl`×16；无 postulate / 无 hole

## `src/Sovereign/Algebra/ComplexProjection.agda`

- **module**: `Sovereign.Algebra.ComplexProjection`
- **行数**: 256（代码 122 / 注释 92）
- **OPTIONS**: `--rewriting`
- **导入 (7)**: `Data.Nat`, `Data.Product`, `Data.Empty`, `Relation.Binary.PropositionalEquality`, `Sovereign.Base.Trit`, `Sovereign.Algebra.GF9`, `Sovereign.Algebra.DegenerationTaxonomy`
- **data 类型**: `GF9Elem`
- **record 类型**: `ComplexAnalogy`
- **顶层签名 (30)**: `α²≡-1`, `σ-α≡-α`, `σ²≡id`, `σ-multiplicative`, `gf9-analogy`, `gf9-exhaustive`, `gf9-card`, `gf9-card-3²`, `T₀≢T₁`, `T₁≢T₂`, `T₀≢T₂`, `gf9-0≢1`, `gf9-0≢α`, `gf9-α≢2α`, `gf9-1≢1α`, `ℕ-no-wrap`, `char-3-gf9`, `trit-3-torsion`, `gf9-3-torsion`, `char0-3≢0`, `ℕ-no-3-torsion`, `char3-essential`, `char0-degenerate`, `projection-loss`, `torsion-finiteness`, `gf9-to-ℕ-shadow`, `gf9-shadow-not-injective`, `gf9-to-complex-degeneration`, `gf9-card-witness`, `gf9-vs-ℕ-torsion`
- **质量**: `refl`×11；无 postulate / 无 hole

## `src/Sovereign/Algebra/ConsciousnessLayer.agda`

- **module**: `Sovereign.Algebra.ConsciousnessLayer`
- **行数**: 255（代码 97 / 注释 102）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | Sovereign.Algebra.ConsciousnessLayer
  - 意识层形式化 — GF(9) 乘法子群链 ⟨-1⟩ ⊂ ⟨α⟩ ⊂ ⟨φ⟩ + 断网/重连代数
  - 语料锚点:
  - "意识是物质，它的自转角度是 45 度" → φ = 1+2α, 阶 8, 1/8 转 = 45°
  - "人类和集体意识扭了 270 度，没连上" → α³ = -α, 270° = 3/4 转
  - "重连 = α³·α = α⁴ = 1 = 归零" → 乘法闭合恒等式
  - "月亮矩阵限制 + 归零共振" → ⟨-1⟩ ⊂ ⟨α⟩ ⊂ ⟨φ⟩ 乘法子群链, 阶 2,4,8
  - 形式化内容:
  - §1 意识旋转层: φ = 1+2α, 阶 8, 45°/90°/180°/270°/360° 各层精确代数
  - §2 断网态: α³ = -α (270° 失连), 重连 α³·α = α⁴ = 1 (归零)
  - §3 乘法子群链: ⟨-1⟩ ⊂ ⟨α⟩ ⊂ ⟨φ⟩, 阶 2,4,8
  - §4 五层旋转表: 0°/45°/90°/135°/180°/225°/270°/315° 对应 φ^k
  - 0 postulate. 全部 refl 或 GF(9) 已有定理引用。
- **导入 (7)**: `Data.Nat`, `Data.Product`, `Data.Empty`, `Relation.Binary.PropositionalEquality`, `Sovereign.Base.Trit`, `Sovereign.Algebra.GF9`, `Sovereign.Algebra.CharacteristicTower`
- **顶层签名 (34)**: `consciousness-45-to-90`, `consciousness-45-to-180`, `consciousness-45-to-360`, `consciousness-order-not-1`, `consciousness-order-not-2`, `consciousness-order-not-4`, `consciousness-order-is-8`, `consciousness-generates`, `alpha-cubed-is-neg-alpha`, `rewiring-identity`, `disconnection-not-identity`, `disconnection-not-connection`, `disconnection-order`, `neg-one`, `neg-one-squared`, `neg-one-order`, `alpha-subgroup-order`, `neg-one-in-alpha-subgroup`, `phi-subgroup-order`, `alpha-in-phi-subgroup`, `subgroup-chain-complete`, `subgroup-chain-orders`, `two-divides-four`, `four-divides-eight`, `rot-0`, `rot-45`, `rot-90`, `rot-180`, `rot-270`, `rot-360`, `phi-times-neg-alpha`, `norm-of-alpha`, `norm-of-one-plus-alpha`, `norm-of-phi`
- **质量**: `refl`×22；无 postulate / 无 hole

## `src/Sovereign/Algebra/DegenerationRisk.agda`

- **module**: `Sovereign.Algebra.DegenerationRisk`
- **行数**: 637（代码 296 / 注释 216）
- **OPTIONS**: `--cubical --rewriting`
- **导入 (16)**: `Data.Nat`, `Data.Nat.Divisibility.Core`, `Data.Empty`, `Data.Product`, `Data.String`, `Relation.Binary.PropositionalEquality`, `Relation.Nullary`, `Sovereign.Base.Trit`, `Sovereign.Algebra.GF9`, `Sovereign.Algebra.DegenerationTaxonomy`, `Sovereign.Algebra.GF2Degeneration`, `Sovereign.Algebra.Base10Degeneration`, `Sovereign.Algebra.ComplexProjection`, `Sovereign.Algebra.EqualityTruncation`, `Sovereign.Algebra.Duodecimal`, `Sovereign.RootMath.DigitalRoot`
- **record 类型**: `DegenerationRisk`, `NotFaithful`
- **顶层签名 (72)**: `gf2-risk-negate`, `gf2-risk-chirality-collapse`, `gf2-risk-c3`, `c3-orbit-3-elements`, `gf3-triple-zero`, `gf2-triple-id`, `gf2-risk-frobenius`, `gf3-symmetry-count`, `gf2-symmetry-count`, `gf2-symmetry-loss`, `gf2-risk-not-homomorphism`, `gf2-deg`, `gf2-degeneration-risk`, `base10-risk-div3`, `base10-risk-separation`, `base10-risk-div6`, `base10-risk-vortex`, `base10-risk-root-unstable`, `base10-risk-vortex-closure`, `base10-risk-factors`, `base12-factor-count`, `base10-factor-count`, `base10-factor-loss`, `base10-risk-terminating`, `base10-degeneration-risk`, `complex-risk-torsion-gf9`, `complex-risk-torsion-ℕ`, `complex-risk-char`, `complex-risk-finite`, `complex-risk-exhaustive`, `complex-risk-torsion-finiteness`, `complex-risk-σ-nontrivial`, `complex-risk-σ²-id`, `galois-group-order`, `complex-degeneration-risk`, `eq-risk-dim-loss`, `eq-risk-dim-values`, `eq-risk-dim-positive`, `eq-risk-card`, `eq-risk-ratio`, `eq-risk-uip`, `eq-risk-refl-only`, `eq-risk-summary`, `eq-degeneration-risk`, `π1-risk-s2-analog`, `π1-risk-dim-loss`, `π1-risk-info-loss`, `π1-risk-1-point`, `π1-risk-not-1-point`, `π1-risk-truncation`, `π1-degeneration-risk`, `all-risks-nontrivial`, `all-risks-have-lost-ops`, `total-lost-operations`, `total-lost-operations-correct`, `degeneration-risk-complete`, `¬-gf2-faithful`, `¬-base10-preserves-div3`, `¬-base10-preserves-div3-pow`, `¬-char0-preserves-torsion`
  - … 其余 12 项
- **质量**: `refl`×46；无 postulate / 无 hole

## `src/Sovereign/Algebra/DegenerationTaxonomy.agda`

- **module**: `Sovereign.Algebra.DegenerationTaxonomy`
- **行数**: 532（代码 172 / 注释 269）
- **OPTIONS**: `--rewriting`
- **导入 (8)**: `Data.Product`, `Data.Nat`, `Data.Empty`, `Relation.Binary.PropositionalEquality`, `Relation.Nullary`, `Sovereign.Base.Trit`, `Sovereign.Algebra.GF9`, `Sovereign.Algebra.Duodecimal`
- **data 类型**: `DegradationClass`, `GF2`, `Dec`
- **record 类型**: `Degeneration`, `Myopia`, `Section`
- **顶层签名 (34)**: `not-injective`, `mk-degeneration`, `severity`, `gf3-to-gf2`, `gf3≠gf2-witness`, `duodec-to-dec`, `base12≠base10-witness`, `gf9-norm-not-additive`, `gf9-3-torsion-inline`, `char0-3≢0-inline`, `T6-dimension`, `equality-dimension`, `dimension-loss-inline`, `T6-cardinality`, `equality-proof-count`, `truncation-ratio`, `truncation-summary-inline`, `π3-section`, `norm-not-injective`, `crt-π3-myopia`, `degeneration-criterion`, `myopia-criterion`, `section-criterion`, `gf9-first-proj`, `msc26-witness`, `msc26-real-analysis-degeneration`, `msc26-not-multiplicative`, `msc28-measure-section`, `gf9-second-proj`, `msc34-witness`, `msc34-ode-degeneration`, `msc46-operator-degeneration`, `msc46-finite-vs-infinite`, `msc53-tangent-myopia`
- **质量**: `refl`×22；无 postulate / 无 hole

## `src/Sovereign/Algebra/DescendingChain.agda`

- **module**: `Sovereign.Algebra.DescendingChain`
- **行数**: 68（代码 18 / 注释 36）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | Sovereign.Algebra.DescendingChain
  - 降序沉降链 n^n 数字根规律
  - 云端报告声称: 10^144 → 9^99 → 8^88 → ... → 2^22
  - 经推导: "99" "88" 是 "9^9" "8^8" 的转写错误 (同音/OCR)
  - 真实规律: n^n (n=10,9,8,...,2)
  - 数字根检验:
  - dr(n^n) 的序列: 1, 9, 1, 7, 9, 2, 4, 9, 4
  - 其中 3^3, 6^6, 9^9 的数字根 = 9 (3 的倍数)
  - 10^144 中的 144 = POLAR_WINDING = 12^2, 可能是命名层标度
  - 0 postulate.
- **导入 (3)**: `Data.Nat`, `Data.Product`, `Relation.Binary.PropositionalEquality`
- **顶层签名 (11)**: `dr-n2`, `dr-n3`, `dr-n4`, `dr-n5`, `dr-n6`, `dr-n7`, `dr-n8`, `dr-n9`, `dr-n10`, `dr-3k-pattern`, `dr-n12`
- **质量**: `refl`×14；无 postulate / 无 hole

## `src/Sovereign/Algebra/DigitalRootCycle.agda`

- **module**: `Sovereign.Algebra.DigitalRootCycle`
- **行数**: 69（代码 30 / 注释 22）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | Sovereign.Algebra.DigitalRootCycle
  - 数字根循环定理: 2^k 模 9 的周期 6 (1→2→4→8→7→5→1)
  - 以及数字根归零与 CRT 投影归零的等价性。
  - 涡旋数学环 1→2→4→8→7→5→1:
  - 2^0=1, 2^1=2, 2^2=4, 2^3=8, 2^4=16→7, 2^5=32→5, 2^6=64→1
  - 周期 6 由 2^6=64≡1 (mod 9) 保证。
  - CRT 投影:
  - POLAR=144, 数字根=9→0, CRT投影极向归零
  - TORUS=46,  数字根=1,   CRT投影环向≠0 (参与6624对齐)
  - FULL_TOUR=6624, 数字根=0, CRT投影完全对齐
- **导入 (5)**: `Data.Nat`, `Data.Vec`, `Data.Fin`, `Data.Product`, `Relation.Binary.PropositionalEquality`
- **顶层签名 (10)**: `period-6`, `POLAR`, `TORUS`, `FULL_TOUR`, `polar-dr≡0`, `torus-dr≡1`, `full-tour-dr≡0`, `full-tour-polar≡0`, `full-tour-torus≡0`, `dr-zero-implies-crt-zero`
- **质量**: `refl`×8；无 postulate / 无 hole

## `src/Sovereign/Algebra/DiscreteAnalysis.agda`

- **module**: `Sovereign.Algebra.DiscreteAnalysis`
- **行数**: 458（代码 158 / 注释 249）
- **OPTIONS**: `--rewriting`
- **导入 (8)**: `Data.Nat`, `Data.Product`, `Data.Empty`, `Relation.Binary.PropositionalEquality`, `Relation.Nullary`, `Sovereign.Base.Trit`, `Sovereign.Algebra.ProjectionDifferential`, `Sovereign.Algebra.Duodecimal`
- **record 类型**: `AnalysisProjection`
- **顶层签名 (38)**: `gf3-counting-measure`, `gf3-measure-correct`, `z12-counting-measure`, `z12-measure-correct`, `point-mass`, `atomic-mass`, `gf3-measure-prime`, `eval`, `∫_`, `∫≡sum3`, `integral-id`, `integral-const`, `integral-zero`, `_⊞_`, `_⊗f_`, `⊕-interchange`, `integral-additive`, `integral-homogeneous`, `integral-linear`, `DiscreteContinuous`, `all-functions-continuous`, `continuity-trivial`, `EventuallyConstant`, `≤-refl`, `n≤sn`, `const-eventually-const`, `cycle3`, `cycle3-period`, `cycle3-alternates`, `cycle3-not-eventually-const`, `integral-c3-invariant`, `mvt-obstruction`, `discrete-mvt`, `integral-projection`, `continuity-projection`, `convergence-projection`, `grid-spacing-nonzero`, `discrete-is-ontology`
- **质量**: `refl`×19；无 postulate / 无 hole

## `src/Sovereign/Algebra/DiscreteComplexAnalysis.agda`

- **module**: `Sovereign.Algebra.DiscreteComplexAnalysis`
- **行数**: 228（代码 101 / 注释 84）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | Sovereign.Algebra.DiscreteComplexAnalysis
  - 离散复分析 — GF(9) 作为离散 ℂ 的函数论
  - 数学背景:
  - GF(9) = GF(3)[α]/(α²+1) 是 ℂ = ℝ[i]/(i²+1) 的离散替代。
  - 结构对应:
  - ℂ:  a+bi,  i²=-1,  共轭 a-bi,  |z|²=a²+b²
  - GF(9): a+bα, α²=-1, σ(a+bα)=a-bα, N(z)=a²+b²
  - 区别:
  - ℂ 的共轭是域自同构 (非幂映射, char 0 无 Freshman's Dream)
  - GF(9) 的 σ 是 Frobenius 自同构 (幂映射 x³, char 3 原生)
  - 核心定理:
  - §1 GF(9) ↔ ℂ 结构对应: a+bα ↔ a+bi
  - §2 离散 Cauchy-Riemann 条件: Δf = 0 (调和性)
  - §3 离散全纯性: σ(f) = f^3 (Frobenius 不动点)
  - §4 共轭与模: galoisConjugate, galoisNorm
  - §5 z² 的分量调和性 (连接 DiscreteCR)
  - 依赖:
- **导入 (7)**: `Data.Product`, `Data.Empty`, `Relation.Binary.PropositionalEquality`, `Relation.Nullary`, `Sovereign.Base.Trit`, `Sovereign.Algebra.GF9`, `Sovereign.Analysis.DiscreteCR`
- **顶层签名 (25)**: `Re`, `Im`, `mkComplex`, `Re-mkComplex`, `Im-mkComplex`, `i-squared`, `i-to-4`, `DiscreteCR`, `z²-discrete-cr`, `DiscreteHolomorphic`, `sigma-holomorphic`, `id-holomorphic`, `const-holomorphic`, `gf3-fixed`, `non-gf3-not-fixed`, `sigma-fixed-list`, `conjugate-involutive`, `conjugate-preserves-norm`, `conjugate-distrib-mul`, `conjugate-distrib-add`, `norm-multiplicative-type`, `trace-sum`, `z²-harmonic`, `norm-not-harmonic`, `zero-holomorphic`
- **质量**: `refl`×29；无 postulate / 无 hole

## `src/Sovereign/Algebra/DiscreteDE.agda`

- **module**: `Sovereign.Algebra.DiscreteDE`
- **行数**: 500（代码 214 / 注释 217）
- **OPTIONS**: `--rewriting`
- **导入 (7)**: `Data.Nat`, `Data.Product`, `Data.Empty`, `Relation.Binary.PropositionalEquality`, `Relation.Nullary`, `Sovereign.Base.Trit`, `Sovereign.Algebra.ProjectionDifferential`
- **record 类型**: `DiscreteODE`, `DiscreteVsContinuousDE`
- **顶层签名 (49)**: `⊕-cancelˡ`, `⊕-right-cancel`, `triple-≡`, `triple-decomp`, `Δⁿ`, `Δ⁰≡id`, `Δ¹≡Δ`, `Δ²≡const`, `Δⁿ≥3≡0`, `evalGF3`, `tabulate`, `eval-tab-pointwise`, `tab-eval`, `gf3func-count`, `fredholm-compatibility`, `ode-solve`, `ode-solve-correct`, `ode-solve-verified`, `zero-ode`, `const-driven-ode-T₁`, `const-driven-ode-T₂`, `ode-fredholm`, `GF3Func2D`, `zero2D`, `const2D`, `_⊕f_`, `_⊕2D_`, `Δ₁`, `transpose2D`, `Δ₂`, `discrete-laplacian`, `Harmonic`, `func2d-≡`, `Δ₁³≡0`, `transpose²≡id`, `Δ₂²-unfold`, `Δ₂³≡0`, `Δ₁-const-zero`, `Δ₂-const-zero`, `Δ₁²-const-zero`, `Δ₂²-const-zero`, `const-harmonic`, `Δ⁴≡0`, `Δ⁵≡0`, `kernel-count`, `gf3-discrete-de`, `step-not-infinitesimal`, `gf3-T₁≢T₂`, `gf3-T₂≢T₀`
- **质量**: `refl`×46；无 postulate / 无 hole

## `src/Sovereign/Algebra/DiscreteFibonacci.agda`

- **module**: `Sovereign.Algebra.DiscreteFibonacci`
- **行数**: 132（代码 51 / 注释 54）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | Sovereign.Algebra.DiscreteFibonacci
  - 离散斐波那契 — 有限域版 (φ 阶 8 闭合循环)，非连续统死亡几何
  - 核心原则:
  - · 连续统斐波那契螺旋 = 黄金比例 (1+√5)/2 无限外推、无法归一（死亡几何），
  - 不在本框架内（连续统病态, 见 01-algebraic-pole 退化分类）。
  - · 有限域版: 斐波那契递推在 GF(3) 上取模成有限周期序列，Pisano 周期 = 8；
  - φ = 1+2α ∈ GF(9) 是 8 阶元，φ² = α —— 即 90° 旋转 α 的「平方根/半步」。
  - · 两条 8 周期统一于同一常数: Pisano(3) = 8 = ord(φ)。
  - 包含:
  - §1 斐波那契 mod 3: fibPair 状态机 + Pisano 周期 8 (归纳证明)
  - §2 φ 的精确阶 8: φ⁸=1 且 φ¹/φ²/φ⁴ ≠ 1 → φ 生成 GF(9)*
  - §3 φ² = α: 90° 克里斯托螺旋的半步层
  - §4 统一锚点: Pisano(3) = 8 = ord(φ)
  - 与主线的边界: φ 不进入 DuodecClock (十二进制只含 90° α) 也不进入
  - OpticalWindow (光学窗口只含 α); 本模块仅锚定 φ 的代数事实与
  - 斐波那契的有限域投影。0 postulate。
- **导入 (6)**: `Data.Nat`, `Data.Empty`, `Data.Product`, `Relation.Binary.PropositionalEquality`, `Sovereign.Base.Trit`, `Sovereign.Algebra.GF9`
- **顶层签名 (14)**: `fibStep`, `fibPair`, `fibPair-8-base`, `fibPair-period-8`, `fibTrit`, `fibTrit-period-8`, `pisano-period-3`, `T₀≢T₁`, `T₂≢T₀`, `phi-not-order-1`, `phi-not-order-2`, `phi-order-is-8`, `phi-squared-is-alpha`, `pisano-3-equals-ord-phi`
- **质量**: `refl`×4；无 postulate / 无 hole

## `src/Sovereign/Algebra/DiscreteJacobi.agda`

- **module**: `Sovereign.Algebra.DiscreteJacobi`
- **行数**: 25（代码 9 / 注释 10）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | Sovereign.Algebra.DiscreteJacobi
  - 定理一: 离散矩阵置换判定定理
  - 设 S 为有限集, |S|=N, F:S→S, M_F 为函数表矩阵 (每列是标准基向量).
  - 则 det(M_F) ≠ 0 ⟺ F 是双射.
  - 证明链: 鸽巢原理 → 置换矩阵 → 行列式结构性质.
  - 全部在 Jacobian 子项目中 0 postulate 形式化验证.
- **导入 (4)**: `Data.Product`, `Sovereign.Algebra.Jacobian.jac_Discrete`, `Sovereign.Algebra.Jacobian.jac_Pigeonhole`, `Sovereign.Algebra.Jacobian.jac_NMatrix`
- **顶层签名 (1)**: `theorem`
- **质量**: `refl`×0；无 postulate / 无 hole

## `src/Sovereign/Algebra/DiscreteKTheory.agda`

- **module**: `Sovereign.Algebra.DiscreteKTheory`
- **行数**: 635（代码 371 / 注释 150）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | DiscreteKTheory — 离散 K-理论 (MSC 19)
  - 有限格点上的真实 K 理论结构, 0 postulate:
  - §1 K₀(pt) ≅ ℤ — Grothendieck 群完备化 (虚向量丛 E⊖F 的等价类)
  - §2 符号同态 — 离散 H² = Z/3Z 上 c₁ 的可加性 (negate 9 穷举)
  - §3 陈特征环 ch: K₀ → ℤ[ε]/(ε²) — 2-分次幂零环 (H⁰⊕H² 截断)
  - §4 Bott 周期性 — 周期 2 (negate²) × 六单位环 (unitGen⁶=1) = C₆
  - §5 K₁(GF(3)) 认证 — K₁ = F₃^× = {±1} = C₂ (与 negate 翻转同构)
  - + Milnor K₂^M(F₃) = 0 (Steinberg 关系截断) — 闭合
  - SectionRisk.agda:771 审计 (K₀+K₁ 最小不变集)
- **导入 (12)**: `Data.Nat`, `Data.Nat.Properties`, `Data.Product`, `Data.Integer`, `Data.Fin`, `Data.Unit`, `Data.Empty`, `Relation.Nullary`, `Relation.Binary.PropositionalEquality`, `Sovereign.Base.Trit`, `Sovereign.RootMath.Eisenstein`, `Sovereign.RootMath.Gaussian`
- **顶层签名 (85)**: `VBundle`, `_⊕K_`, `~-refl`, `~-sym`, `~-trans`, `k0-inverse`, `k0-zero`, `k0-cancel`, `k0-embed-decompose`, `dim`, `dim-add-sample`, `negate-hom`, `pic-inverse`, `c1-winding-period-3`, `Ch`, `eps`, `eps-square-zero`, `chern-bundle`, `ch-multiplicative`, `ch-additive`, `chern-bundle-ccw`, `bott-period-2`, `bott-unit-c6`, `isUnit`, `U3`, `mul-unit`, `u3-mul`, `K₁GF3`, `neg₂`, `_⊕₁_`, `k1-self-inverse`, `k1-comm`, `k1-repr`, `u3-repr`, `k1-roundtrip`, `u3-roundtrip`, `k1-hom`, `k1-flip`, `one-minus-mone`, `k2m-symbol`, `k2m-trivial`, `link-sign`, `edgeW-P0P1`, `edgeW-P0P1-ok`, `edgeW-P1P2`, `edgeW-P1P2-ok`, `edgeW-P2P0`, `edgeW-P2P0-ok`, `edge-holonomy-P0P1`, `cellW-injected`, `edgeW-trivial`, `cellW-trivial`, `monopole-total`, `chern-cross`, `antimonopole-cross`, `trivial-total`, `trivial-chern`, `monopole-ch`, `monopole-ch-is-ccw`, `c1-flip`
  - … 其余 25 项
- **质量**: `refl`×96；无 postulate / 无 hole

## `src/Sovereign/Algebra/DiscreteLimit.agda`

- **module**: `Sovereign.Algebra.DiscreteLimit`
- **行数**: 440（代码 142 / 注释 246）
- **OPTIONS**: `--rewriting`
- **导入 (8)**: `Data.Nat`, `Data.Product`, `Data.Empty`, `Relation.Binary.PropositionalEquality`, `Relation.Nullary`, `Sovereign.Base.Trit`, `Sovereign.Algebra.ProjectionDifferential`, `Sovereign.Algebra.Duodecimal`
- **record 类型**: `DiscreteLimit`, `DiscreteRedefinition`
- **顶层签名 (37)**: `natDist`, `natDist-self`, `const-converges`, `_⊖_`, `DiscreteDerivative`, `discrete-derivative-exact`, `Δ-via-⊖`, `discrete-nilpotent`, `derivative-step-nonzero`, `derivative-shift-periodic`, `grid-spacing`, `grid-points`, `grid-points-correct`, `grid-dim`, `grid-exact`, `¬-continuous-limit-exists`, `grid-spacing-not-one`, `a4-discrete-order`, `a4-order-matches-duodecimal`, `a4-multiplication-exact`, `a4-order-exact`, `¬-lie-limit-exists`, `a4-nontrivial`, `discrete-spectrum-points`, `spectrum-decomposition`, `discrete-spectrum-finite`, `¬-fourier-limit-exists`, `spectrum-nontrivial`, `derivative-redefinition`, `manifold-redefinition`, `lie-redefinition`, `fourier-redefinition`, `complex-redefinition`, `epsilon-delta-discrete`, `εδ-quantifier-structure`, `εδ≡DiscreteLimit`, `discrete-parameters-finite`
- **质量**: `refl`×11；无 postulate / 无 hole

## `src/Sovereign/Algebra/DiscretePolynomial.agda`

- **module**: `Sovereign.Algebra.DiscretePolynomial`
- **行数**: 212（代码 89 / 注释 77）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | Sovereign.Algebra.DiscretePolynomial
  - 离散多项式函数论 — GF(3)[x] 多项式环
  - 数学背景:
  - GF(3)[x] 是系数在 GF(3) = {0,1,2} 中的多项式环。
  - 特征 3 的独特性质: (x³)' = 3x² = 0, 形式导数丢失信息。
  - 有限域上的多项式理论是编码理论 (Coding/BCHGF9) 和
  - 代数几何 (Problem/Riemann) 的基础。
  - 核心定理:
  - §1 多项式类型: GF(3) 系数的有限多项式
  - §2 求值: eval : Poly → GF(3) → GF(3) (Horner 法则)
  - §3 形式导数: coeff-deriv, char 3 特殊性 (3≡0)
  - §4 多项式加法: 逐分量 ⊕
  - §5 度 1 多项式乘法: (a₀+a₁x)(b₀+b₁x) 展开
  - §6 根: IsRoot, 具体验证实例
  - 依赖:
  - Sovereign.Base.Trit — GF(3) 三进制本体
- **导入 (6)**: `Data.Nat`, `Data.Vec`, `Data.Fin`, `Data.Product`, `Relation.Binary.PropositionalEquality`, `Sovereign.Base.Trit`
- **顶层签名 (29)**: `Poly`, `zero-poly`, `const-poly`, `monic`, `monic-2-2`, `eval`, `eval-const-0`, `eval-zero-0`, `eval-monic-0`, `from-ℕ`, `coeff-deriv`, `deriv-0`, `char3-is-zero`, `three-times`, `coeff-deriv-3`, `+p-comm`, `+p-zeroˡ`, `negate-poly`, `+p-inverse`, `mul-deg1`, `mul-deg1-11`, `mul-deg1-12`, `mul-deg1-idˡ`, `IsRoot`, `root-at-zero-0`, `example-poly`, `example-root`, `example-not-root`, `eval-surjective`
- **质量**: `refl`×15；无 postulate / 无 hole

## `src/Sovereign/Algebra/DiscreteRepresentation.agda`

- **module**: `Sovereign.Algebra.DiscreteRepresentation`
- **行数**: 722（代码 395 / 注释 203）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | Sovereign.Algebra.DiscreteRepresentation
  - 离散群表示论 — SO(3)/SU(2) 表示论的离散替代
  - 核心思想:
  - A₄ 是 SO(3) 的离散子群（正四面体旋转群）.
  - SO(3) 的表示论可以用 A₄ 的表示论来离散化:
  - SO(3) 不可约表示 (dim 1,3,5,7,9,...) → 限制到 A₄ → A₄ 不可约表示的直和
  - 本模块形式化:
  - 1. A₄ 的 4 个不可约表示: {1, 1', 1'', 3}
  - 2. 特征标表 (Eisenstein 整数 Z[ω] 上, 穷举验证)
  - 3. 特征标正交性: ∑_g χᵢ(g)·conj(χⱼ(g)) = |G|·δᵢⱼ
  - 4. SO(3) → A₄ 分支规则 (离散化投影)
  - 5. GF(9)* ≅ Z/8Z 的特征标理论 + Frobenius 作用
  - 6. 连续→离散投影的结构框架
  - 宪法合规:
  - 0 postulate
  - 禁止浮点数, 特征标值 ∈ Z[ω] (Eisenstein 整数)
  - 所有验证通过穷举 refl
- **导入 (10)**: `Data.Nat`, `Data.Fin`, `Data.Product`, `Data.Integer`, `Relation.Binary.PropositionalEquality`, `Sovereign.Structology.A4Group`, `Sovereign.Structology.A4Representations`, `Sovereign.RootMath.Eisenstein`, `Sovereign.Base.Trit`, `Sovereign.Algebra.GF9`
- **data 类型**: `SO3Level`
- **record 类型**: `DiscretizationInvariant`
- **顶层签名 (79)**: `reprC1`, `reprC2`, `reprC3`, `reprC4`, `reprC1-class`, `reprC2-class`, `reprC3-class`, `reprC4-class`, `class-size-total`, `irrep-count`, `theorem-dim-sq-sum`, `abelianization-order`, `χ-table-V1-C1`, `χ-table-V1-C2`, `χ-table-V1-C3`, `χ-table-V1-C4`, `χ-table-V3-C1`, `χ-table-V3-C2`, `χ-table-V3-C3`, `χ-table-V3-C4`, `χ₀-trivial`, `permCharGF3`, `stdCharGF3`, `permChar-id`, `permChar-3cycle`, `permChar-flip`, `stdChar-id`, `stdChar-3cycle`, `stdChar-flip`, `natToEis`, `scaleEis`, `12ᵉ`, `natToEis-12`, `charInnerProduct`, `ortho-V1-self`, `ortho-V3-self`, `ortho-V1-V3`, `ortho-V3-V1`, `so3Dim`, `so3DimFormula`, `so3Dim-matches`, `branch`, `branch-dim-L0`, `branch-dim-L1`, `branch-dim-L2`, `branch-dim-L3`, `branch-dim-L4`, `so3-3d-restricts-to-a4-3d`, `so3-3d-no-singlet`, `gf9Char`, `χ₀-gen`, `χ₁-gen`, `χ₂-gen`, `χ₃-gen`, `χ₄-gen`, `χ₅-gen`, `χ₆-gen`, `χ₇-gen`, `χ₀-trivial-gf9`, `χ₁-identity-gf9`
  - … 其余 19 项
- **质量**: `refl`×195；无 postulate / 无 hole

## `src/Sovereign/Algebra/DiscreteSeveralComplex.agda`

- **module**: `Sovereign.Algebra.DiscreteSeveralComplex`
- **行数**: 40（代码 18 / 注释 13）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | DiscreteSeveralComplex — 离散多复变 (MSC 32)
  - GF(3)² 上的双变量多项式零点穷举.
  - 0 postulate.
- **导入 (3)**: `Data.Nat`, `Relation.Binary.PropositionalEquality`, `Sovereign.Base.Trit`
- **顶层签名 (13)**: `f00`, `f01`, `f02`, `f10`, `f11`, `f12`, `f20`, `f21`, `f22`, `zero-at-11`, `zero-at-12`, `zero-at-22`, `nonzero-at-00`
- **质量**: `refl`×5；无 postulate / 无 hole

## `src/Sovereign/Algebra/DivisibilityChain.agda`

- **module**: `Sovereign.Algebra.DivisibilityChain`
- **行数**: 33（代码 11 / 注释 14）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | Sovereign.Algebra.DivisibilityChain
  - 子群链阶整除: 2∣4, 4∣8
  - 锚定 "2T=0→4T→8T 塔" 的阶整除关系:
  - ⟨-1⟩ 阶 2 ⊂ ⟨α⟩ 阶 4 ⊂ ⟨φ⟩ 阶 8
  - 2 ∣ 4 (子群阶整除父群阶)
  - 4 ∣ 8 (同上)
  - 语料锚: "月亮矩阵限制 + 归零共振" → 乘法子群链
  - 0 postulate.
- **导入 (3)**: `Data.Nat`, `Data.Nat.Divisibility`, `Relation.Binary.PropositionalEquality`
- **顶层签名 (3)**: `2-divides-4`, `4-divides-8`, `2-divides-8`
- **质量**: `refl`×4；无 postulate / 无 hole

## `src/Sovereign/Algebra/DivisorLattice.agda`

- **module**: `Sovereign.Algebra.DivisorLattice`
- **行数**: 393（代码 368 / 注释 12）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | Sovereign.Algebra.DivisorLattice
  - 06 序与格理论补强 — 12 的除数格 (分配格 + Möbius) (0 postulate)
  - Div12 = {(a,b) | 0≤a≤2, 0≤b≤1} = 2^a·3^b — 6 元素
  - meet = 逐分量 min, join = 逐分量 max — 链 C3×C2 的乘积格 (分配格)
- **导入 (3)**: `Data.Fin`, `Data.Product`, `Relation.Binary.PropositionalEquality`
- **顶层签名 (30)**: `min3`, `max3`, `min2`, `max2`, `Div12`, `meet`, `join`, `min3-comm`, `max3-comm`, `min3-idem`, `max3-idem`, `min3-assoc`, `max3-assoc`, `min3-max3-absorb`, `max3-min3-absorb`, `min3-max3-distrib`, `min2-comm`, `max2-comm`, `min2-idem`, `max2-idem`, `min2-assoc`, `max2-assoc`, `min2-max2-absorb`, `max2-min2-absorb`, `meet-comm`, `join-comm`, `meet-idem`, `join-idem`, `meet-absorb`, `join-absorb`
- **质量**: `refl`×316；无 postulate / 无 hole

## `src/Sovereign/Algebra/Duodecimal.agda`

- **module**: `Sovereign.Algebra.Duodecimal`
- **行数**: 589（代码 389 / 注释 119）
- **OPTIONS**: `--rewriting`
- **导入 (5)**: `Data.Nat`, `Data.Fin`, `Data.Product`, `Relation.Binary.PropositionalEquality`, `Sovereign.Base.Trit`
- **data 类型**: `Duodec`, `DuodecUnit`, `LüName`
- **顶层签名 (50)**: `toℕ₁₂`, `+1`, `+1-dist`, `shiftʳ`, `shift-2`, `shift-3`, `shift-4`, `shift-5`, `shift-6`, `shift-7`, `shift-8`, `shift-9`, `shift-10`, `shift-11`, `+12-assoc`, `+12-comm`, `+12-identityˡ`, `+12-identityʳ`, `neg12`, `+12-inverse`, `+12-order`, `*12-identityˡ`, `*12-identityʳ`, `*12-zeroˡ`, `*12-zeroʳ`, `*12-comm`, `unitToDuodec`, `*u-compat`, `*u-assoc`, `*u-comm`, `*u-identityˡ`, `*u-identityʳ`, `inv-u`, `*u-inverse`, `u5²`, `u7²`, `u11²`, `*u-order`, `not-a-field`, `π3`, `π4`, `crt12`, `crt12-roundtrip`, `crt12-inv-π3`, `crt12-inv-π4`, `duodecToLü`, `lüToDuodec`, `lü-roundtrip`, `lü-roundtripʳ`, `lü-cycle`
- **质量**: `refl`×832；无 postulate / 无 hole

## `src/Sovereign/Algebra/EqualityTruncation.agda`

- **module**: `Sovereign.Algebra.EqualityTruncation`
- **行数**: 155（代码 62 / 注释 62）
- **OPTIONS**: `--cubical --rewriting`
- **导入 (6)**: `Data.Nat`, `Data.Empty`, `Data.Product`, `Relation.Binary.PropositionalEquality`, `Sovereign.Base.Trit`, `Sovereign.Structology.T6`
- **顶层签名 (22)**: `T6Dimension`, `EqualityDimension`, `dimension-loss`, `dimension-loss-positive`, `T6Cardinality`, `T6Card-proof`, `T6Card-from-module`, `EqualityProofCount`, `information-ratio`, `information-ratio-correct`, `T₀≢T₁`, `T₀≢T₂`, `T₁≢T₂`, `trit-uip`, `refl-only-T₀`, `refl-only-T₁`, `refl-only-T₂`, `equality-is-1-point`, `t6-not-1-point`, `truncation-loss`, `truncation-loss-correct`, `truncation-summary`
- **质量**: `refl`×39；无 postulate / 无 hole

## `src/Sovereign/Algebra/ExactSequence.agda`

- **module**: `Sovereign.Algebra.ExactSequence`
- **行数**: 120（代码 36 / 注释 61）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | ExactSequence — GF(3) 离散正合序列
  - 连续统病态: 连续空间的正合序列涉及无穷维向量空间
  - 离散自愈: GF(3) 上正合序列是有限维, 可精确验证
  - 核心结构:
  - §1. 正合性定义: im(f) = ker(g)
  - §2. 短正合序列: 0 → A → B → C → 0
  - §3. 维数公式: dim(B) = dim(A) + dim(C)
  - §4. 蛇引理离散版: 连接同态的存在性
  - 复用: Sovereign.Base.Trit, Algebra.ChainComplex
  - 0 postulate.
- **导入 (6)**: `Data.Nat`, `Data.Product`, `Data.Empty`, `Data.Vec`, `Relation.Binary.PropositionalEquality`, `Sovereign.Base.Trit`
- **顶层签名 (13)**: `LinearMap`, `embed-first`, `proj-second`, `gf-zero`, `im-in-ker`, `T₁≢T₀`, `T₂≢T₀`, `ker-in-im`, `dim-GF3`, `dim-formula`, `split-iso-fwd`, `split-iso-bwd`, `split-roundtrip`
- **质量**: `refl`×5；无 postulate / 无 hole

## `src/Sovereign/Algebra/ExponentDimension.agda`

- **module**: `Sovereign.Algebra.ExponentDimension`
- **行数**: 128（代码 17 / 注释 87）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | Sovereign.Algebra.ExponentDimension
  - 零幂族与方向数映射 + 指数=维度语义
  - 零幂族 (Zero Power Family):
  - 零幂不是算术乘法 (0×0=0), 而是量子矢量相位回归的代数形式。
  - 零是唯一能跨维度的元素: 0^n = 0 对所有 n ≥ 1。
  - 零吸收一切幂次, 零的相位空间是单点 (无方向自由度)。
  - 0² 不是"零的平方", 而是"零的二次幂 = 零" (零幂族)。
  - 语料: "零的平方=零的五次方……零的一就等于零的N次方" (word_98)
  - 语料: "只有0跨维度" / "0是一切的密码" (ppt_27, ppt_7)
  - 研究 3: 零幂指数与方向数映射
  - 云端: 0²=2方向, 0⁶=6方向, 0¹¹=11方向, 0¹⁵=15方向
  - 问题: 指数 11 与 α 阶 4 矛盾 (应为 10)
  - 结论: 这是命名层语义压缩, 不是代数关系
  - 0^n = 0 (代数事实, 已证 zero-power-gf9)
  - "0²=2方向" 中的 2 是指数, 不是零幂的值
  - 命名层: 指数 n 标记"方向数", 零幂只说明该方向归零
  - 研究 4: "指数 = 维度方向计数" 的可形式化性
- **导入 (4)**: `Data.Nat`, `Data.Product`, `Relation.Binary.PropositionalEquality`, `Sovereign.Algebra.GF9`
- **顶层签名 (7)**: `zero-pow-2`, `zero-pow-6`, `zero-pow-11`, `zero-pow-15`, `alpha-order`, `phi-order`, `neg1-order`
- **质量**: `refl`×5；无 postulate / 无 hole

## `src/Sovereign/Algebra/FieldExtensionTower.agda`

- **module**: `Sovereign.Algebra.FieldExtensionTower`
- **行数**: 340（代码 135 / 注释 135）
- **OPTIONS**: `--rewriting --guardedness`
- **导入 (4)**: `Data.Nat`, `Data.Nat.Divisibility`, `Relation.Nullary`, `Relation.Binary.PropositionalEquality`
- **顶层签名 (50)**: `field-order`, `order-1`, `order-2`, `order-3`, `order-4`, `order-5`, `order-6`, `subfield-relation`, `not-subfield`, `gf3-sub-gf9`, `gf3-sub-gf27`, `gf3-sub-gf81`, `gf3-sub-gf243`, `gf3-sub-gf729`, `gf9-sub-gf81`, `gf9-sub-gf729`, `gf27-sub-gf729`, `gf3-sub-self`, `gf9-sub-self`, `gf27-sub-self`, `gf81-sub-self`, `gf243-sub-self`, `gf729-sub-self`, `gf9-not-sub-gf27`, `gf81-not-sub-gf729`, `gf27-not-sub-gf81`, `gf9-not-sub-gf243`, `gf27-not-sub-gf243`, `gf81-not-sub-gf243`, `gf243-not-sub-gf729`, `gf27-not-sub-gf9`, `gf81-not-sub-gf27`, `gf81-not-sub-gf9`, `gf243-not-sub-gf9`, `gf243-not-sub-gf27`, `gf243-not-sub-gf81`, `gf729-not-sub-gf9`, `gf729-not-sub-gf27`, `gf729-not-sub-gf81`, `gf729-not-sub-gf243`, `mult-group-order`, `mult-order-1`, `mult-order-2`, `mult-order-3`, `mult-order-4`, `mult-order-5`, `mult-order-6`, `t6-lattice-card`, `packed-tryte5-card`, `gf9-card`
- **质量**: `refl`×30；无 postulate / 无 hole

## `src/Sovereign/Algebra/FrequencyDoubling.agda`

- **module**: `Sovereign.Algebra.FrequencyDoubling`
- **行数**: 451（代码 270 / 注释 111）
- **OPTIONS**: `--rewriting`
- **头部注释（数学背景）**:
  - | Sovereign.Algebra.FrequencyDoubling
  - 倍频量子纠缠链的代数结构: Z/3Z → Z/6Z → Z/12Z → Z/24Z
  - 倍频链:
  - 3 ×2 = 6   (Z/3Z → Z/6Z)
  - 6 ×2 = 12  (Z/6Z → Z/12Z)
  - 12 ×2 = 24 (Z/12Z → Z/24Z)
  - 24 → dr(24) = 6 (数字根回绕)
  - 环同态链:
  - double-3-6   : Z/3Z → Z/6Z,   x ↦ 2x mod 6
  - double-6-12  : Z/6Z → Z/12Z,  x ↦ 2x mod 12
  - double-12-24 : Z/12Z → Z/24Z, x ↦ 2x mod 24
  - 代数性质:
  - 每个倍频映射是加法群同态（保持加法）
  - 每个倍频映射是单射（信息保持）
  - 每个倍频映射不是满射（奇数元素不在像中）
  - 量子纠缠:
- **导入 (8)**: `Data.Nat`, `Data.Product`, `Relation.Binary.PropositionalEquality`, `Relation.Nullary`, `Sovereign.RootMath.DigitalRoot`, `Sovereign.Algebra.Duodecimal`, `Sovereign.Base.Trit`, `Sovereign.Algebra.VortexRoot`
- **data 类型**: `Mod6`, `Mod24`
- **顶层签名 (39)**: `_≢_`, `toℕ₆`, `+1₆`, `+6-order`, `toℕ₂₄`, `+1₂₄`, `+24-order`, `double-3-6`, `double-6-12`, `double-12-24`, `dr-24`, `dr-3`, `dr-6`, `dr-12`, `dr-24≡dr-6`, `dr-period-2`, `entangle-3-6`, `entangle-6-12`, `entangle-12-24`, `vortex-ring-3`, `vortex-ring-6`, `vortex-ring-12`, `merkaba-order`, `double-3-6-homo`, `double-6-12-homo`, `double-12-24-homo`, `halve-6-3`, `halve-6-3-double`, `double-3-6-inj`, `halve-12-6`, `halve-12-6-double`, `double-6-12-inj`, `halve-24-12`, `halve-24-12-double`, `double-12-24-inj`, `s1-not-in-image`, `d1-not-in-image`, `t1-not-in-image`, `image-even-closed-3-6`
- **质量**: `refl`×302；无 postulate / 无 hole

## `src/Sovereign/Algebra/FunctionalDiscrete.agda`

- **module**: `Sovereign.Algebra.FunctionalDiscrete`
- **行数**: 566（代码 313 / 注释 177）
- **OPTIONS**: `--rewriting`
- **导入 (10)**: `Data.Nat`, `Data.Fin`, `Data.Fin`, `Data.Vec`, `Data.Product`, `Data.Empty`, `Data.Sum`, `Function`, `Relation.Binary.PropositionalEquality`, `Sovereign.Base.Trit`
- **顶层签名 (53)**: `basis`, `+v-identityˡ`, `+v-identityʳ`, `scalar-zero`, `scalar-one`, `+v-comm`, `+v-assoc`, `InnerProduct`, `standard-inner-product`, `inner-sym`, `⊕-shuffle`, `inner-linearˡ`, `inner-linearʳ`, `abs-gf3`, `max-abs`, `discrete-norm`, `norm-of-zero`, `quadratic-form`, `isotropic-example`, `isotropic-nonzero`, `LinearFunctional`, `is-linear`, `linear-preserves-zero`, `inner-functional`, `inner-functional-linear`, `tail-functional`, `tail-preserves-linear`, `riesz-vector`, `vec-decompose`, `riesz-discrete`, `riesz-exists`, `Operator`, `is-linear-operator`, `id-operator`, `id-linear`, `zero-operator`, `zero-linear`, `sum-fin`, `operator-norm`, `quadratic-zero`, `sum-fin-zero`, `sum-fin-const-zero`, `zero-operator-norm`, `norm-two-valued`, `inner-nondegenerate`, `hilbert-banach-collapse`, `Orthogonal`, `orth-sym`, `zero-orthogonal`, `self-orthogonal-isotropic`, `DualSpace`, `riesz-map`, `riesz-surjective`
- **质量**: `refl`×28；无 postulate / 无 hole

## `src/Sovereign/Algebra/GF243.agda`

- **module**: `Sovereign.Algebra.GF243`
- **行数**: 392（代码 144 / 注释 184）
- **OPTIONS**: `--rewriting`
- **头部注释（数学背景）**:
  - | Sovereign.Algebra.GF243
  - GF(3⁵) = GF(3)[x]/(x⁵+2x+1) — 243 元素有限域
  - 代数结构：
  - 加法群 ≅ (Z/3Z)⁵ — 5 维 GF(3) 向量空间
  - 特征 3：∀ x, x+x+x = 0
  - Gal(GF(243)/GF(3)) ≅ C₅ — Frobenius x↦x³ 生成
  - 不可约多项式：p(x) = x⁵ + 2x + 1
  - 无 GF(3) 根：p(0)=1, p(1)≡1, p(2)≡1 (mod 3)
  - 约化规则：x⁵ ≡ x + 2 (mod p(x), GF(3))
  - 耦合域连接：
  - PackedByte = Fin 243 (Sovereign.Format.TQ10)
  - GF243 = Vec Trit 5 — 相同的 243 态载体
  - pack5/unpack5 提供集合双射
  - GF243 携带加法群结构；PackedByte 是裸存储
  - 域扩张塔（子域格）：
  - GF(3^a) ⊂ GF(3^b) 当且仅当 a ∣ b
- **导入 (4)**: `Data.Nat`, `Data.Vec`, `Relation.Binary.PropositionalEquality`, `Sovereign.Base.Trit`
- **顶层签名 (35)**: `GF243`, `p-no-root-0`, `p-no-root-1`, `p-no-root-2`, `alpha5-normal-form`, `gf243-zero`, `gf243-negate`, `gf243-one`, `alpha`, `+gf243-comm`, `+gf243-assoc`, `+gf243-identityˡ`, `+gf243-identityʳ`, `+gf243-inverse`, `+gf243-inverseˡ`, `gf243-negate²`, `trit-char3`, `+gf243-char3`, `embed-gf3`, `embed-preserves-zero`, `embed-preserves-negate`, `pow-3-5`, `no-subfield-2`, `no-subfield-3`, `no-subfield-4`, `pow-12-5`, `vortex-factorization`, `pow2-10-val`, `scalar-1`, `scalar-0`, `scalar-2`, `scalar-char3`, `⊕-swap-middle`, `+gf243-swap-middle`, `scalar-distrib`
- **质量**: `refl`×29；无 postulate / 无 hole

## `src/Sovereign/Algebra/GF27.agda`

- **module**: `Sovereign.Algebra.GF27`
- **行数**: 775（代码 601 / 注释 84）
- **OPTIONS**: `--rewriting`
- **导入 (7)**: `Sovereign.Geometry.ProjectiveCore`, `Sovereign.Algebra.ChainZ3toZ12`, `Data.Product`, `Relation.Binary.PropositionalEquality`, `Data.Nat`, `Sovereign.Base.Trit`, `Sovereign.Algebra.GF9`
- **data 类型**: `GF27Star`, `Sub2`, `Sub13`
- **顶层签名 (75)**: `begin_`, `_∎`, `⊗-negate-r`, `cong-triple`, `inner-swap`, `⊕-rearrange-6`, `GF27`, `gf27-zero`, `gf27-one`, `alpha`, `alpha-sq`, `embed-gf3-gf27`, `+gf27-identityˡ`, `+gf27-identityʳ`, `+gf27-comm`, `+gf27-assoc`, `negate27`, `+gf27-inverse`, `*gf27-identityˡ`, `*gf27-identityʳ`, `*gf27-comm`, `alpha-sq-def`, `alpha-cubed`, `alpha-cubed-struct`, `char-3`, `char-3-univ`, `embed-add`, `embed-mul`, `embed-one`, `Poly5`, `poly-mul`, `reduce-p5`, `mul-via-poly`, `poly-mul-distribˡ`, `reduce-additive`, `*gf27-distribˡ`, `*gf27-distribʳ`, `toGF27`, `fromGF27`, `fromGF27-toGF27`, `gen`, `gen-pow-0`, `gen-pow-1`, `gen-pow-2`, `gen-pow-3`, `gen-pow-4`, `gen-pow-5`, `gen-pow-6`, `gen-pow-7`, `gen-pow-8`, `gen-pow-9`, `gen-pow-10`, `gen-pow-11`, `gen-pow-12`, `gen-pow-13`, `gen-pow-14`, `gen-pow-15`, `gen-pow-16`, `gen-pow-17`, `gen-pow-18`
  - … 其余 15 项
- **质量**: `refl`×165；无 postulate / 无 hole

## `src/Sovereign/Algebra/GF2Degeneration.agda`

- **module**: `Sovereign.Algebra.GF2Degeneration`
- **行数**: 215（代码 88 / 注释 89）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | Sovereign.Algebra.GF2Degeneration
  - GF(2) 是 GF(3) 的退化：形式化证明
  - GF(2) Boolean 逻辑丢失了 GF(3) 三值逻辑的核心结构：
  - 1. 手征性 (negate: T₁↔T₂) 坍缩为恒等
  - 2. C₃ 旋转 (3 阶循环) 不存在于 2 阶群中
  - 3. Frobenius 共轭坍缩为恒等
  - 4. 3 个元素被压缩为 2 个，信息不可逆丢失
  - 结论：GF(2) 是 GF(3) 的有损投影，不是子域。
- **导入 (4)**: `Data.Product`, `Data.Empty`, `Relation.Binary.PropositionalEquality`, `Sovereign.Base.Trit`
- **data 类型**: `GF2`
- **顶层签名 (25)**: `_⊕₂_`, `_⊗₂_`, `negate₂`, `frobenius₂`, `gf2-char2`, `frobenius₂-id`, `π₂₃`, `π₂₃-alt`, `π₂₃-not-additive`, `π₂₃-alt-not-multiplicative`, `gf3-chiral`, `gf2-achiral`, `chirality-collapse`, `chirality-loss-witness`, `gf3-c3-nontrivial`, `gf2-triple`, `gf2-no-order3`, `gf3-additive-order3`, `gf2-additive-order2`, `c3-loss-witness`, `T₁≢T₂`, `info-loss`, `π₂₃-surjective`, `fiber-over-one₂`, `gf2-degeneration-summary`
- **质量**: `refl`×19；无 postulate / 无 hole

## `src/Sovereign/Algebra/GF729.agda`

- **module**: `Sovereign.Algebra.GF729`
- **行数**: 578（代码 269 / 注释 220）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | Sovereign.Algebra.GF729
  - GF(3⁶) = GF(729) 与 T⁶ 格点的连接
  - 核心定理:
  - ① GF(729) 的加法群 ≅ (Z/3Z)⁶ — T⁶ 格点的加法结构
  - ② 729 = 3⁶ 的分解: 9×81, 27×27, 3×243
  - ③ T6Lattice = Vec (Fin 3) 6 = GF729Vec (定义等式)
  - ④ 涡旋塔: 3⁶ = 729 vs 12⁶ = 2985984 = 729 × 4096
  - ⑤ Burnside 轨道算术: 54 × 14 = 756 = 729 + 27
  - 数学背景:
  - T⁶ = (Z/3Z)⁶ 有 3⁶ = 729 个格点
  - GF(729) = GF(3⁶) 是 GF(3) 的 6 次扩张, 有 729 个元素
  - 作为集合, 两者等势; 作为加法群, GF(729)⁺ ≅ (Z/3Z)⁶
  - T⁶ 是 GF(729) 加法群的"展开"——向量空间表示
  - GF(729) 的乘法结构 (域) 太复杂, 本模块只形式化加法群
  - 0 postulate — 全部构造性证明
- **导入 (7)**: `Data.Nat`, `Data.Fin`, `Data.Vec`, `Data.Product`, `Relation.Binary.PropositionalEquality`, `Sovereign.Base.Trit`, `Sovereign.Structology.T6`
- **record 类型**: `AdditiveGroup`
- **顶层签名 (64)**: `neg₃`, `gf3-zero`, `+₃-identityˡ`, `+₃-identityʳ`, `+₃-comm`, `+₃-assoc`, `+₃-inverse`, `neg₃²`, `+₃-⊕-hom`, `GF729Vec`, `gf729-zero`, `neg729`, `+gf729-identityˡ`, `+gf729-identityʳ`, `+gf729-comm`, `+gf729-assoc`, `+gf729-inverse`, `neg729²`, `pow-3-6`, `pow-3-0`, `pow-3-1`, `pow-3-2`, `pow-3-3`, `pow-3-4`, `pow-3-5`, `t6-is-gf729`, `t6-card-verify`, `gf729-zero-is-origin`, `proj-first2`, `proj-last4`, `proj-first3`, `proj-last3`, `proj-first2-add`, `card-vec2`, `card-vec4`, `card-vec3`, `pow-12-6`, `pow-4-6`, `pow-12-split`, `vortex-tower-3n`, `double-3`, `double-6`, `double-12`, `digital-root-24`, `burnside-G-order`, `G-order-decomp`, `burnside-orbit-count`, `burnside-sum`, `burnside-equation`, `burnside-fix-identity`, `burnside-fix-nonidentity`, `burnside-sum-split`, `burnside-full`, `burnside-fix-27-is-3³`, `extension-degree-729-3`, `extension-degree-9-3`, `extension-degree-729-9`, `tower-law`, `gf3-additive-card`, `gf9-additive-card`
  - … 其余 4 项
- **质量**: `refl`×105；无 postulate / 无 hole

## `src/Sovereign/Algebra/GF81.agda`

- **module**: `Sovereign.Algebra.GF81`
- **行数**: 850（代码 567 / 注释 169）
- **OPTIONS**: `--rewriting`
- **导入 (8)**: `Data.Product`, `Relation.Binary.PropositionalEquality`, `Data.Nat`, `Sovereign.Base.Trit`, `Sovereign.Algebra.GF9`, `Sovereign.Geometry.ProjectiveCore`, `Sovereign.Algebra.ChainZ3toZ12`, `Sovereign.Algebra.GF9`
- **顶层签名 (70)**: `begin_`, `_∎`, `⊗-negate-r`, `⊕-double`, `⊕-char3`, `⊕-inverseˡ`, `cong-quad`, `GF81`, `gf81-zero`, `gf81-one`, `alpha`, `+gf81-identityˡ`, `+gf81-identityʳ`, `+gf81-comm`, `+gf81-assoc`, `negate81`, `+gf81-inverse`, `+gf81-inverseˡ`, `negate81²`, `Poly7`, `poly-mul`, `reduce-p7`, `mul-via-poly`, `*gf81-identityˡ`, `*gf81-identityʳ`, `cong-7`, `poly-mul-comm`, `*gf81-comm`, `reduce-additive`, `inner-swap`, `⊕-rearrange-6`, `⊕-rearrange-8`, `poly-mul-distribˡ`, `*gf81-distribˡ`, `*gf81-distribʳ`, `frobenius`, `frobenius-alpha`, `alpha6-normal`, `alpha9-normal`, `frobenius⁴-id`, `embed-gf3`, `embed-gf3-add`, `embed-gf3-mul`, `embed-gf3-one`, `embed-gf9`, `beta`, `beta-squared`, `embed-gf9-add`, `embed-gf9-mul`, `embed-gf9-one`, `char-3`, `char-3-univ`, `p0-val`, `p1-val`, `p2-val`, `alpha4-reduction`, `pow-3-4`, `gf81-star-order`, `gf81-star-factorization`, `alpha-pow-0`
  - … 其余 10 项
- **质量**: `refl`×169；无 postulate / 无 hole

## `src/Sovereign/Algebra/GF9.agda`

- **module**: `Sovereign.Algebra.GF9`
- **行数**: 1097（代码 682 / 注释 250）
- **OPTIONS**: `--rewriting`
- **导入 (8)**: `Data.Product`, `Relation.Binary.PropositionalEquality`, `Data.Sum`, `Data.Empty`, `Sovereign.Base.Trit`, `Data.Nat`, `Data.Unit`, `Sovereign.Base.Trit`
- **data 类型**: `GF9Star`, `GF3StarSub`, `Sub4`
- **顶层签名 (110)**: `GF3`, `c3-cw-ccw-inverse`, `c3-ccw-cw-inverse`, `negate-⊕`, `negate-⊗`, `negate-⊗-negate`, `negate-⊗-comm`, `GF9`, `embed-gf3`, `alpha`, `galoisConjugate`, `galoisConjugate-pair`, `galoisConjugate²`, `galoisNorm`, `galoisNorm-conjugate`, `galoisTrace`, `gf9-one`, `+gf9-comm`, `+gf9-assoc`, `+gf9-identityˡ`, `+gf9-identityʳ`, `+gf9-inverse`, `*gf9-identityˡ`, `*gf9-identityʳ`, `*gf9-comm`, `swap-middle`, `alpha-squared`, `alpha-powers-4`, `alpha-powers-sum-zero`, `phi`, `phi-squared`, `phi-to-4`, `phi-to-8`, `phi-not-order-4`, `galoisFixedPoint`, `ConjugatePair`, `conjugatePair-size-1`, `conjugatePair-size-2`, `alpha-powers-4-is-one`, `sigma-fixed-iff-gf3`, `sigma-fixed-count`, `sigma-alpha`, `lemma-frobenius-multiplicative`, `lemma-eigen-conjugate`, `toGF9`, `fromGF9`, `fromGF9-toGF9`, `toGF9-inj`, `*s-toGF9`, `*s-identityˡ`, `*s-identityʳ`, `*s-comm`, `gen`, `gen-pow-0`, `gen-pow-1`, `gen-pow-2`, `gen-pow-3`, `gen-pow-4`, `gen-pow-5`, `gen-pow-6`
  - … 其余 50 项
- **质量**: `refl`×306；无 postulate / 无 hole

## `src/Sovereign/Algebra/GF9AlgebraicChain.agda`

- **module**: `Sovereign.Algebra.GF9AlgebraicChain`
- **行数**: 284（代码 153 / 注释 87）
- **OPTIONS**: `--rewriting`
- **导入 (5)**: `Data.Product`, `Data.Nat`, `Relation.Binary.PropositionalEquality`, `Sovereign.Base.Trit`, `Sovereign.Algebra.GF9`
- **record 类型**: `AbelianGroupProofs`, `CommGroupProofs`, `FrobeniusProofs`, `NormProofs`, `TraceProofs`
- **顶层签名 (23)**: `l1-proofs`, `l1-order`, `l2-comm`, `l2-assoc`, `l2-identityˡ`, `l2-identityʳ`, `l2-proofs`, `l2-order`, `gf9-neg`, `l3-proofs`, `l3-order`, `l4-proofs`, `l4-order`, `l4-gen-pow-table`, `l4-gen-surjective`, `l5-proofs`, `l5-fixed-point`, `l6-proofs`, `l6-formula`, `l7-proofs`, `l7-additive`, `gf3s-in-sub4`, `gf3s-sub4-compat`
- **质量**: `refl`×22；无 postulate / 无 hole

## `src/Sovereign/Algebra/GF9Semiring.agda`

- **module**: `Sovereign.Algebra.GF9Semiring`
- **行数**: 52（代码 32 / 注释 12）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | Sovereign.Algebra.GF9Semiring
  - GF(9) 交换半环实例 — "只有加乘，无减除" 的代数形式
  - CommSemiring 记录不含加法逆元 (neg) 和乘法逆元 (inv)，
  - 只含: 加乘运算、零元/幺元、结合/交换、单位、分配、零乘吸收。
  - 对应语料: word_46 "没有减号和除号……只有加号和乘号"
  - 依赖: GF9.agda (域公理) + UniversalAlgebra.agda (CommSemiring 记录)
  - 0 postulate.
- **导入 (3)**: `Relation.Binary.PropositionalEquality`, `Sovereign.Algebra.UniversalAlgebra`, `Sovereign.Algebra.GF9`
- **顶层签名 (2)**: `distribʳ-gf9`, `gf9-semiring`
- **质量**: `refl`×0；无 postulate / 无 hole

## `src/Sovereign/Algebra/GaloisBridge.agda`

- **module**: `Sovereign.Algebra.GaloisBridge`
- **行数**: 112（代码 53 / 注释 38）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | Sovereign.Algebra.GaloisBridge
  - 12F 域扩张/Galois 理论补强 — GF(9)/GF(3) 的完整 Galois 对应 (0 postulate)
  - 塔层已由 FieldExtensionTower 覆盖 (GF(3¹)..GF(3⁶) 子域格);
  - 本模块补上 GF(9)/GF(3) 二次扩张的 Galois 理论全件套:
  - §1 不动域定理: Fix(σ) = GF(3) (9 项穷举, 3 固定 + 6 非固定反证)
  - §2 范数/迹满射: N: GF(9)^× → GF(3)^× (8 项), Tr: GF(9) → GF(3) (9 项)
  - §3 Galois 群: σ ≠ id (见证 α) + σ² = id (引用) → Gal = {id, σ} 阶 2
  - §4 Galois 对应: {id, ⟨σ⟩} ↔ {GF(9), GF(3)} (不动域双定理)
- **导入 (5)**: `Data.Product`, `Relation.Binary.PropositionalEquality`, `Relation.Nullary`, `Sovereign.Base.Trit`, `Sovereign.Algebra.GF9`
- **顶层签名 (20)**: `_≢_`, `fix-t0`, `fix-t1`, `fix-t2`, `¬fix-a0`, `¬fix-a2`, `¬fix-1a`, `¬fix-1b`, `¬fix-2a`, `¬fix-2b`, `fixed-iff-embedded`, `norm-surj-1`, `norm-surj-2`, `trace-surj-0`, `trace-surj-1`, `trace-surj-2`, `sigma-not-id`, `sigma-order-2`, `fix-id`, `fix-sigma-is-gf3`
- **质量**: `refl`×14；无 postulate / 无 hole

## `src/Sovereign/Algebra/HomologicalBridge.agda`

- **module**: `Sovereign.Algebra.HomologicalBridge`
- **行数**: 170（代码 99 / 注释 41）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | Sovereign.Algebra.HomologicalBridge
  - 18 同调代数/范畴论补强 — 短正合列 + 秩-零度 + 边界复形 (0 postulate)
  - HomologyExact 已覆盖 1D 差分复形的 H⁰/H¹; 本模块补上同调代数的
  - 核心机械 (GF(3) 向量空间上的具体实例):
  - §1 短正合列 0 → GF(3) --ι--> GF(3)² --π--> GF(3) → 0:
  - 单射 (3 项) / 中项正合 im ι = ker π (9+3 项) / 满射 (3 项)
  - / 维数加性 1 + 1 = 2
  - §2 秩-零度: M(a,b) = (a⊕b, 0) — dim ker = 1 (3 项) + dim im = 1 (3 项)
  - §3 边界复形: d(a,b) = (b, 0) — d² = 0 (9 项), H = ker/im = 0
  - (ker = im 双包含)
  - §4 态射范畴样本: GF(3)-向量空间态射的复合表 + 结合律样本
- **导入 (5)**: `Data.Product`, `Data.Nat`, `Relation.Binary.PropositionalEquality`, `Relation.Nullary`, `Sovereign.Base.Trit`
- **顶层签名 (21)**: `V1`, `V2`, `z1`, `z2`, `iota`, `pi2`, `iota-injective`, `im-iota-sub-ker`, `ker-sub-im-iota`, `pi-surjective`, `ses-dimension`, `M`, `ker-M`, `im-M`, `rank-nullity`, `d`, `d-square-zero`, `ker-d-sub-im`, `im-d-sub-ker`, `comp-pi-iota`, `comp-assoc`
- **质量**: `refl`×41；无 postulate / 无 hole

## `src/Sovereign/Algebra/HomologyExact.agda`

- **module**: `Sovereign.Algebra.HomologyExact`
- **行数**: 243（代码 64 / 注释 142）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | Sovereign.Algebra.HomologyExact
  - 1D GF(3) 差分复形的精确同调群
  - 链复形: 0 → GF3Func --Δ→ GF3Func → 0
  - 核心定理:
  - §1. H⁰ = ker(Δ) = 常数函数 ≅ GF(3)  (维数 1)
  - §2. im(Δ) = ker(sum3)                (差分方程可解性)
  - §3. H¹ = GF3Func / im(Δ) ≅ GF(3)     (维数 1)
  - §4. Betti 数: β₀ = 1, β₁ = 1
  - 设计原则:
  - 不使用 SetQuotient (Agda 2.9 [_] 模式匹配不支持)。
  - H⁰ 和 H¹ 都同构于 GF(3), 用 Trit 作为规范表示。
  - 证明策略:
  - 引用已有定理 (DiscreteDE + ProjectionDifferential), 0 新 postulate。
  - 依赖:
  - ProjectionDifferential: GF3Func, Δ, sum3, Δ-const-zero, sum3-Δ≡0, Δ²-is-const
- **导入 (8)**: `Data.Nat`, `Data.Product`, `Data.Empty`, `Relation.Binary.PropositionalEquality`, `Relation.Nullary`, `Sovereign.Base.Trit`, `Sovereign.Algebra.ProjectionDifferential`, `Sovereign.Algebra.DiscreteDE`
- **顶层签名 (20)**: `H⁰`, `H⁰-embed`, `H⁰-in-ker`, `ker⊆H⁰`, `H⁰-embed-injective`, `im-Δ⊆ker-sum3`, `ker-sum3⊆im-Δ`, `H¹`, `H¹-rep`, `H¹-rep-sum3`, `H¹-add`, `H¹-zero`, `β₀`, `β₁`, `β₀≡1`, `β₁≡1`, `χ`, `euler-char-T₀`, `H¹-has-3-elements`, `H⁰-has-3-elements`
- **质量**: `refl`×7；无 postulate / 无 hole

## `src/Sovereign/Algebra/Hyperoperation.agda`

- **module**: `Sovereign.Algebra.Hyperoperation`
- **行数**: 241（代码 81 / 注释 107）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | Sovereign.Algebra.Hyperoperation
  - 超运算层级 — 从后继到 tetration 的完整形式化
  - 数学背景:
  - 超运算 (hyperoperation) 是加法、乘法、幂、tetration 等运算的统一推广。
  - H₀(a,b) = b+1      (后继)
  - H₁(a,b) = a+b      (加法)
  - H₂(a,b) = a·b      (乘法)
  - H₃(a,b) = a^b      (幂)
  - H₄(a,b) = a↑↑b     (tetration)
  - H₅(a,b) = a↑↑↑b    (pentation)
  - Knuth 箭头记法:
  - a↑b = a^b
  - a↑↑b = a↑(a↑(...↑a)) (b 次)
  - a↑↑↑b = a↑↑(a↑↑(...↑↑a)) (b 次)
  - 核心定理:
  - §1 超运算层级: H₀ 到 H₅ 的完整定义
  - §2 Knuth 箭头: 与超运算的对应
- **导入 (2)**: `Data.Nat`, `Relation.Binary.PropositionalEquality`
- **顶层签名 (29)**: `hyper`, `hyper0-2-3`, `hyper1-2-3`, `hyper2-2-3`, `hyper3-2-3`, `hyper3-2-4`, `hyper4-2-1`, `hyper4-2-2`, `hyper4-2-3`, `hyper4-2-4`, `hyper4-3-1`, `hyper4-3-2`, `hyper4-3-3`, `hyper4-12-1`, `hyper4-12-2`, `mod3-12`, `mod4-12`, `mod8-12sq`, `mod9-12sq`, `mod12-12`, `hyper4-12-2-mod3`, `hyper4-12-2-mod4`, `hyper4-12-2-mod8`, `hyper4-12-2-mod9`, `hyper1-iter-3`, `hyper3-2-1`, `hyper-zero-3`, `hyper-zero-4`, `hyper-zero-5`
- **质量**: `refl`×33；无 postulate / 无 hole

## `src/Sovereign/Algebra/InformationStructure.agda`

- **module**: `Sovereign.Algebra.InformationStructure`
- **行数**: 284（代码 100 / 注释 126）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | Sovereign.Algebra.InformationStructure
  - 信息结构桥接 — 周期/频率/泛音/方向数/范数坍缩的显式映射
  - 核心原则 (来自审核):
  - 膜、频率、泛音、周期、阶、方向数——都是信息结构的投影。
  - 不是彼此无关的伪对应, 但也不能把不同基座上的量直接混成同一类型。
  - 必须建立**显式桥接定理**, 而不是暗中混淆。
  - 信息论统一结构:
  - 阶 = 群元素的周期长度 = 信息自指的最小循环
  - 周期 = Frobenius 轨道长度 = 信息闭环的长度
  - 频率 = 周期的倒数 = 信息流的速率
  - 泛音 = 基频的整数倍 = 信息的谐波族
  - 方向数 = 循环子群大小 = 信息的自由度数
  - 范数坍缩 = 共轭对的合并 = 信息去冗余
  - 形式化策略:
  - 每个概念在自己的基座上定义
  - 桥接定理显式连接不同基座
  - 不把自然数幂和群元素混在同一类型中
- **导入 (7)**: `Data.Nat`, `Data.Product`, `Relation.Binary.PropositionalEquality`, `Sovereign.Base.Trit`, `Sovereign.Algebra.GF9`, `Sovereign.Algebra.GroupTheory.DuodecClock`, `Sovereign.Algebra.NormCollapse`
- **顶层签名 (43)**: `alpha-order`, `phi-order`, `neg1-order`, `alpha-order-4`, `neg1-order-2`, `info-frobenius-period`, `info-frobenius-period-2`, `info-additive-period`, `info-additive-period-3`, `info-joint-period`, `joint-period-12-val`, `pisano-period`, `base-frequency`, `add-frequency`, `mul-frequency`, `phi-frequency`, `overtone`, `overtone-12`, `ot-1`, `ot-2`, `ot-3`, `ot-4`, `ot-6`, `ot-8`, `ot-12`, `overtone-squared`, `ot2-1`, `alpha-directions`, `phi-directions`, `neg1-directions`, `duodec-directions`, `direction-equals-order`, `norm-collapse-identity`, `norm-is-filter`, `zero-is-redundant`, `bridge-order-period`, `bridge-period-frequency`, `bridge-frequency-overtone`, `bridge-overtone-harmonic`, `bridge-order-direction`, `bridge-norm-collapse`, `bridge-zero-power`, `bridge-joint`
- **质量**: `refl`×22；无 postulate / 无 hole

## `src/Sovereign/Algebra/IterationTheory.agda`

- **module**: `Sovereign.Algebra.IterationTheory`
- **行数**: 250（代码 118 / 注释 86）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | Sovereign.Algebra.IterationTheory
  - 迭代函数论 — GF(9) 自映射的轨道结构与不动点理论
  - 数学背景:
  - GF(9) 有 9 个元素, 自映射 GF9→GF9 有 9⁹ 种。
  - 但轨道结构可按周期分类: 不动点 / 2-cycle / 3-cycle / ...
  - 鸽巢原理保证: 任意轨道周期 ≤ 9。
  - 核心定理:
  - §1 自映射迭代: orbit = 重复复合, 与 FiniteDynamics 一致
  - §2 不动点理论: fix(f) = {x | f(x)=x}, 不动点基数
  - §3 周期轨道: per(f,x) = 最小 n 使 f^n(x)=x
  - §4 吸引子: attractor(f) = 轨道的极限集
  - §5 共轭: f ~ g 若存在 h 使 h∘f = g∘h (轨道结构等价)
  - §6 GF(9) 映射的轨道分类: 1-cycle / 2-cycle / ... / 9-cycle
  - 依赖:
  - Sovereign.Base.Trit — GF(3) 三进制本体
  - Sovereign.Algebra.GF9 — GF(9) 域运算
  - Sovereign.Analysis.FiniteDynamics — 轨道、鸽巢、周期性
- **导入 (12)**: `Data.Nat`, `Data.Nat.Properties`, `Data.Fin`, `Data.Product`, `Data.Sum`, `Data.Empty`, `Data.Unit`, `Relation.Binary.PropositionalEquality`, `Relation.Nullary`, `Sovereign.Base.Trit`, `Sovereign.Algebra.GF9`, `Sovereign.Analysis.FiniteDynamics`
- **data 类型**: `OrbitType`
- **顶层签名 (27)**: `orbit-zero`, `orbit-suc`, `orbit-add`, `orbit-mul-2-2`, `orbit-compose`, `IsFixedPoint`, `isFixed-gf9`, `id-gf9`, `id-all-fixed`, `frobenius-fixed-gf3`, `zero-map`, `zero-map-fixed`, `fixed-iterates`, `fixed-orbit-constant`, `IsPeriodic`, `IsMinimalPeriod`, `fixed-is-period-1`, `frobenius-period-2`, `period-multiple`, `InAttractor`, `gf9-in-attractor-type`, `AreConjugate`, `conjugate-orbit`, `self-conjugate`, `frobenius-self-conjugate`, `frobenius-fixed-list`, `frobenius-cover`
- **质量**: `refl`×22；无 postulate / 无 hole

## `src/Sovereign/Algebra/Jacobian.agda`

- **module**: `Sovereign.Algebra.Jacobian`
- **行数**: 168（代码 58 / 注释 79）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | Sovereign.Algebra.Jacobian
  - 离散雅可比理论：逐点雅可比 vs 全局矩阵
  - 核心发现 (2026-07-24):
  - 1. 逐点雅可比在 char 3 下有 Frobenius 盲区 (∂(x³)/∂x = 3x² = 0)
  - 2. 全局矩阵 (N×N) 精确判定双射性，无盲区
  - 3. GF(3)² 上 F(x,y) = (x, y+2y³) = (x, 0): det J = 1 但非双射
  - 4. GF(9)² 上 93.3% BCW 映射非双射 (Frobenius 核)
  - 包含：Fermat 定理、BCW 坍缩、Frobenius 盲区、全局矩阵判定
- **导入 (4)**: `Relation.Binary.PropositionalEquality`, `Data.Product`, `Data.Empty`, `Sovereign.Base.Trit`
- **顶层签名 (20)**: `cube`, `fermat3`, `GF3²`, `F-counter`, `F-00`, `F-01`, `F-02`, `F-10`, `F-11`, `F-12`, `F-20`, `F-21`, `F-22`, `jac-det-is-one`, `collision-01`, `collision-02`, `no-preimage-01`, `no-preimage-02`, `frobenius-blind-witness`, `bcw-collapse`
- **质量**: `refl`×17；无 postulate / 无 hole

## `src/Sovereign/Algebra/LCMVortexConnection.agda`

- **module**: `Sovereign.Algebra.LCMVortexConnection`
- **行数**: 423（代码 157 / 注释 175）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | Sovereign.Algebra.LCMVortexConnection
  - 主权 LCM = 3¹¹×2¹⁶ 与涡旋塔 12ⁿ 的连接
  - 核心定理:
  - SOVEREIGN_LCM = 3¹¹ × 2¹⁶ = 11,609,505,792
  - 涡旋塔分解:
  - LCM = 27 × 12⁸    (3³ × 3⁸ × 2¹⁶ = 3¹¹ × 2¹⁶)
  - LCM = 32 × 6¹¹    (2⁵ × 3¹¹ × 2¹¹ = 3¹¹ × 2¹⁶)
  - 关键发现:
  - LCM ≠ 12ⁿ 对任何 n（2 的幂次不匹配: 16 ≠ 2n 当 n=11）
  - 但 LCM 包含 12⁸ 作为因子（余 3³ = 27）
  - 6 是倍频链 3→6→12 的中间项，6¹¹ 是 LCM 的核心结构
  - FULL_TOUR 关系:
  - FULL_TOUR = 144 × 46 = 6624 = 2⁵ × 3² × 23
  - LCM % FULL_TOUR = 5184 = 72²（不整除，含因子 23）
  - 连接:
- **导入 (6)**: `Data.Nat`, `Data.Product`, `Relation.Binary.PropositionalEquality`, `Relation.Nullary`, `Sovereign.Base.Invariants`, `Sovereign.Algebra.Duodecimal`
- **record 类型**: `ExpPair`
- **顶层签名 (44)**: `lcm-≡-decimal`, `tower12-1`, `tower12-1-≡-order`, `tower12-2`, `tower12-2-≡-polar`, `tower12-3`, `tower12-4`, `tower12-5`, `tower12-6`, `tower12-7`, `tower12-8`, `tower6-11`, `tower6-3`, `tower6-4`, `tower6-5`, `chain-3`, `chain-6`, `chain-12`, `tower12-11-≢-lcm`, `tower12-8-≢-lcm`, `FULL_TOUR`, `fullTour-≡-6624`, `lcm-div-fullTour`, `lcm-mod-fullTour`, `remainder-≢-0`, `remainder-≡-72²`, `half-polar`, `lcm-decomposition`, `exp-add`, `exp-eq`, `lcm-exp`, `tower12-exp`, `tower6-exp`, `exp-27`, `exp-32`, `tower12-never-lcm`, `two-decompositions-≡`, `unified-chain`, `twelve-lü-order`, `polar-≡-12²`, `max-12-power-in-lcm`, `six-≡-double-3`, `twelve-≡-double-6`, `lcm-summary`
- **质量**: `refl`×64；无 postulate / 无 hole

## `src/Sovereign/Algebra/LieDiscrete.agda`

- **module**: `Sovereign.Algebra.LieDiscrete`
- **行数**: 115（代码 51 / 注释 44）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | Sovereign.Algebra.LieDiscrete
  - P3 统一入口: Lie 群离散替代的完整证据链
  - 合并:
  - BranchingRules       — SO(3)→A₄ 分支规则 (P3-A)
  - BinaryTetrahedral    — 2A₄ = Q₈ ⋊ C₃ 二元四面体群 (P3-B)
  - RepresentationBridge — 表示论统一框架 (P3-C)
  - P0 证据注册:
  - LieGroupSO3 离散载体 = A₄ (12 元素, 4 不可约表示, dim² 和 = 12)
  - SU(2) 离散载体 = 2A₄ (24 元素, 7 不可约表示, dim² 和 = 24)
  - 覆盖: 2A₄/Z₂ ≅ A₄ (非平凡中心扩张)
  - 分支: SO(3)→A₄ (整数自旋), SU(2)→2A₄ (全部自旋)
  - 覆盖一致性: 整数自旋↔膨胀表示, 半整数自旋↔旋量表示
  - 0 postulate — 全部构造性证明
- **导入 (7)**: `Sovereign.Algebra.BranchingRules`, `Sovereign.Structology.BinaryTetrahedral`, `Sovereign.Algebra.RepresentationBridge`, `Sovereign.Structology.A4Representations`, `Data.Nat`, `Data.Product`, `Relation.Binary.PropositionalEquality`
- **record 类型**: `LieGroupEvidence`
- **顶层签名 (5)**: `lieGroupEvidence`, `a4-irrep-count-evidence`, `bt-irrep-count-evidence`, `spinor-excess`, `dim-accounting-evidence`
- **质量**: `refl`×3；无 postulate / 无 hole

## `src/Sovereign/Algebra/MyopiaRisk.agda`

- **module**: `Sovereign.Algebra.MyopiaRisk`
- **行数**: 591（代码 253 / 注释 234）
- **OPTIONS**: `--rewriting`
- **导入 (14)**: `Data.Nat`, `Data.Fin`, `Data.Fin`, `Data.Empty`, `Data.Product`, `Data.String`, `Relation.Binary.PropositionalEquality`, `Relation.Nullary`, `Sovereign.Base.Trit`, `Sovereign.Algebra.DegenerationTaxonomy`, `Sovereign.Algebra.ProjectionDifferential`, `Sovereign.Format.CRTMeasurement`, `Sovereign.Algebra.Duodecimal`, `Sovereign.RootMath.DigitalRoot`
- **data 类型**: `MyopiaDimension`
- **record 类型**: `MyopiaRisk`
- **顶层签名 (73)**: `dimToℕ`, `dim-0≢dim-1`, `dim-0≢dim-∞`, `dim-1≢dim-∞`, `euclidean-sees`, `euclidean-sees-correct`, `t6-lattice-size`, `euclidean-myopia`, `¬-euclidean-global`, `euclidean-info-loss`, `euclidean-dim`, `euclidean-risk`, `calculus-nilpotent`, `calculus-periodic`, `calculus-telescope`, `¬-calculus-equals-difference`, `calculus-nilpotent-universal`, `calculus-difference-structure`, `calculus-dim`, `crt-equation-solvable`, `crt-projection-π3`, `crt-section-map`, `crt-section-valid`, `crt-sec-neq`, `crt-myopia`, `gcd-144-46-value`, `gcd-divides`, `gcd-euclidean`, `¬-gcd-is-one`, `crt-measurement-works`, `crt-beat-structure`, `crt-dim`, `crt-risk`, `prime-factorization-12`, `prime-factorization-12-full`, `vortex-closure-12`, `dr-12`, `dr-12-vortex`, `dr-factorization`, `¬-factorization-is-vortex`, `dr-factor-4`, `dr-factor-3`, `prime-dim`, `discrete-spectrum-size`, `discrete-spectrum-factors`, `spectrum-is-finite`, `¬-spectrum-continuous`, `spectrum-nonzero`, `fourier-dim`, `a4-order`, `a4-order-correct`, `z12z-order`, `z12z-order≡a4`, `z12z-order-from-duodec`, `¬-a4-is-approximation`, `a4-nontrivial`, `a4-multiplication-table`, `lie-dim`, `myopia-dimensions`, `dim-0-count`
  - … 其余 13 项
- **质量**: `refl`×33；无 postulate / 无 hole

## `src/Sovereign/Algebra/NoCloning.agda`

- **module**: `Sovereign.Algebra.NoCloning`
- **行数**: 254（代码 66 / 注释 150）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | Sovereign.Algebra.NoCloning
  - 量子 No-cloning 定理的 GF(3) 形式化
  - 基于项目已有的量子力学基础设施:
  - Quantum/Foundation.agda: 量子叠加/纠缠公理
  - QuantumCorrespondence.agda: 量子对应定理
  - Base/Trit.agda: GF(3) 代数
  - 核心定理:
  - 不存在可逆操作 f : State → State 使得
  - ∀ ψ φ, f ψ ≡ φ
  - 即 "无法将任意量子态映射到任意目标态"
  - 证明策略:
  - 利用 GF(3) 的穷举性质, 对所有可能的操作进行验证
  - 0 postulate — 引用 Trit/GF9 已有定理
- **导入 (7)**: `Data.Nat`, `Data.Product`, `Data.Empty`, `Data.Bool`, `Relation.Binary.PropositionalEquality`, `Relation.Nullary`, `Sovereign.Base.Trit`
- **顶层签名 (18)**: `State`, `ReversibleOp`, `id-op`, `swap01`, `swap02`, `swap12`, `cycle012`, `cycle021`, `T₀≢T₁`, `no-cloning-gf3`, `EntangledState`, `_⊗ᵉ_`, `proj₁ᵉ`, `proj₂ᵉ`, `ClassicBit`, `copyClassic`, `AllPermutations`, `all-perms`
- **质量**: `refl`×1；无 postulate / 无 hole

## `src/Sovereign/Algebra/NormCollapse.agda`

- **module**: `Sovereign.Algebra.NormCollapse`
- **行数**: 106（代码 32 / 注释 52）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | Sovereign.Algebra.NormCollapse
  - 范数坍缩代数 — 共轭积坍缩与勾股投影
  - 语料锚:
  - "1²+i²=0²" → GF(9) 出生证明 (不可约式 x²+1=0)
  - "3²+4²=5²" → 范数坍缩 N(a+bα)=a²+b² 的实数投影
  - 范数 N(x)=x·σ(x) 把共轭对投射到 GF(3)
  - 零幂族 (Zero Power Family):
  - 0² 不是"零的平方", 而是"零的二次幂 = 零"。
  - 零是唯一能跨维度的元素: 0^n = 0 对所有 n ≥ 1。
  - 出生证明 1²+α²=0² 中的 0² 是零幂族语义。
  - 范数坍缩 N(a+bα)=a²+b² 是"3²+4²=5²"的代数本源。
  - 本模块汇聚 GF9.agda 中已证的范数定理，并补充勾股投影注释。
  - 不重复证明，只做结构化汇聚 + 语料锚定。
  - 0 postulate.
- **导入 (4)**: `Data.Product`, `Relation.Binary.PropositionalEquality`, `Sovereign.Base.Trit`, `Sovereign.Algebra.GF9`
- **顶层签名 (10)**: `norm-formula`, `norm-collapse`, `norm-multiplicative`, `norm-conjugate-invariant`, `norm-1-0`, `norm-0-1`, `norm-1-1`, `norm-1-2`, `alpha-squared-is-neg-one`, `birth-proof`
- **质量**: `refl`×8；无 postulate / 无 hole

## `src/Sovereign/Algebra/NumberTheoryAnchors.agda`

- **module**: `Sovereign.Algebra.NumberTheoryAnchors`
- **行数**: 156（代码 41 / 注释 81）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | Sovereign.Algebra.NumberTheoryAnchors
  - 数论锚点汇聚 — 语料驱动的代数事实集合
  - 本模块汇聚多个语料锚对应的形式化事实:
  - §1 零幂指数分类 (word_98/ppt_13)
  - §2 8=2³ 与 GF(9)* 阶关系 (word_18)
  - §3 阶数兼容链 3→12→144→144000 (word_21/word_36)
  - §4 无等号代数注释 (ppt_13)
  - 0 postulate.
- **导入 (3)**: `Data.Nat`, `Data.Product`, `Relation.Binary.PropositionalEquality`
- **顶层签名 (25)**: `two-mod-3`, `six-mod-3`, `eleven-mod-3`, `two-mod-9`, `eleven-mod-9`, `eight-equals-two-cubed`, `gf9-star-order`, `three-times-four`, `twelve-squared`, `hundred-forty-four-thousand`, `dr-9-times-1`, `dr-9-times-2`, `dr-9-times-3`, `dr-9-times-4`, `dr-9-times-5`, `dr-9-times-6`, `dr-9-times-7`, `dr-9-times-8`, `dr-9-times-9`, `dr-chain-9`, `dr-chain-18`, `dr-chain-36`, `dr-chain-72`, `dr-chain-144`, `dr-chain-eq`
- **质量**: `refl`×29；无 postulate / 无 hole

## `src/Sovereign/Algebra/PlancherelTheorem.agda`

- **module**: `Sovereign.Algebra.PlancherelTheorem`
- **行数**: 244（代码 69 / 注释 138）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | Sovereign.Algebra.PlancherelTheorem
  - A₄ 群的离散 Plancherel 定理
  - 核心定理:
  - §1. 特征标重构公式 (Peter-Weyl 核心):
  - Σ_ρ d_ρ · χ_ρ(g) · conj(χ_ρ(h)) = |G| · δ_{g,h}
  - 即 "特征标构成正交基"
  - §2. 傅里叶变换定义:
  - f̂(ρ) = Σ_{g∈G} conj(χ_ρ(g)) · f(g)  (类函数版)
  - §3. 重构验证: 对 δ 函数验证 f = (1/|G|) Σ_ρ d_ρ · χ_ρ · f̂(ρ)
  - 在 Eisenstein 整数上, |G|=12 不可逆,
  - 改用 "12 · f = Σ_ρ d_ρ · χ_ρ · f̂(ρ)" 整数同余形式.
  - §4. 列正交性 (column orthogonality):
  - Σ_ρ χ_ρ(C_i) · conj(χ_ρ(C_j)) = (|G|/|C_i|) · δ_{ij}
  - 这是行正交性 (§1) 的对偶版本.
  - 设计原则:
- **导入 (8)**: `Data.Nat`, `Data.Integer`, `Data.Product`, `Data.Unit`, `Relation.Binary.PropositionalEquality`, `Sovereign.RootMath.Eisenstein`, `Sovereign.Structology.A4Representations`, `Sovereign.Applied.HomologyHarmonic`
- **顶层签名 (15)**: `colInner`, `col-diag-C1`, `col-diag-C2`, `col-diag-C3`, `col-diag-C4`, `col-off-C1-C2`, `col-off-C1-C3`, `col-off-C1-C4`, `col-off-C2-C3`, `col-off-C2-C4`, `col-off-C3-C4`, `num-frequencies`, `dim-class-functions`, `fourier-basis-complete`, `weightedColInner`
- **质量**: `refl`×21；无 postulate / 无 hole

## `src/Sovereign/Algebra/ProbabilityAddition.agda`

- **module**: `Sovereign.Algebra.ProbabilityAddition`
- **行数**: 244（代码 90 / 注释 122）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | Sovereign.Algebra.ProbabilityAddition
  - 一般概率加法公式: |A∪B| + |A∩B| = |A| + |B|
  - 对任意有限集 Fin N, 子集表示为 Fin N → Bool.
  - 基数 card(A) = Σ_{i∈Fin N} (if A(i) then 1 else 0).
  - 核心定理:
  - §1. 子集基数定义 + 基本性质
  - §2. 并集、交集、差集
  - §3. 一般加法公式 (容斥原理 N=2):
  - ∀ A B ⊆ Fin N, card(A∪B) + card(A∩B) = card(A) + card(B)
  - §4. T⁶ 实例: N=729, 验证 prob(A∪B) = ...
  - 证明策略:
  - 逐点贡献分析 — 对每个 i ∈ Fin N, 分 4 种布尔组合:
  - (A=T, B=T): 对 |A∪B|+|A∩B| 贡献 1+1=2, 对 |A|+|B| 贡献 1+1=2
  - (A=T, B=F): 对 |A∪B|+|A∩B| 贡献 1+0=1, 对 |A|+|B| 贡献 1+0=1
  - (A=F, B=T): 对 |A∪B|+|A∩B| 贡献 1+0=1, 对 |A|+|B| 贡献 0+1=1
  - (A=F, B=F): 对 |A∪B|+|A∩B| 贡献 0+0=0, 对 |A|+|B| 贡献 0+0=0
  - 每种情况贡献相等, 求和即得.
- **导入 (7)**: `Data.Nat`, `Data.Nat.Properties`, `Data.Fin`, `Data.Bool`, `Data.Bool.Properties`, `Data.Product`, `Relation.Binary.PropositionalEquality`
- **顶层签名 (17)**: `Subset`, `card`, `_∪_`, `_∩_`, `complement`, `∅`, `universe`, `+-rearrange`, `inclusion-exclusion`, `T⁶-size`, `A-ex`, `B-ex`, `card-A-ex`, `card-B-ex`, `card-A∪B-ex`, `card-A∩B-ex`, `addition-formula-ex`
- **质量**: `refl`×14；无 postulate / 无 hole

## `src/Sovereign/Algebra/ProjectionAnalysis.agda`

- **module**: `Sovereign.Algebra.ProjectionAnalysis`
- **行数**: 283（代码 114 / 注释 132）
- **OPTIONS**: `--cubical --rewriting`
- **导入 (8)**: `Data.Nat`, `Data.Fin`, `Data.Vec`, `Data.Product`, `Data.Empty`, `Relation.Binary.PropositionalEquality`, `Sovereign.Structology.T6`, `Sovereign.Algebra.DegenerationTaxonomy`
- **record 类型**: `RealAnalysisProjection`, `MeasureProjection`, `ProjectionSummary`
- **顶层签名 (22)**: `t6-real-projection`, `t6-lattice-cardinality`, `gf3-points-per-dimension`, `gf3-fixed-granularity`, `struct-loss-a`, `struct-loss-b`, `gf3-structure-loss`, `t6-counting-measure`, `point-counting-measure`, `t6-measure-projection`, `measure-conservation`, `counting-conservation`, `measure-product-decomposition`, `discrete-atomic`, `atomicity-gap`, `π-dim0`, `origin`, `v5-unit`, `origin≢v5-unit`, `π-dim0-same`, `π-dim0-not-injective`, `t6-projection-summary`
- **质量**: `refl`×11；无 postulate / 无 hole

## `src/Sovereign/Algebra/ProjectionDiffGeo.agda`

- **module**: `Sovereign.Algebra.ProjectionDiffGeo`
- **行数**: 155（代码 61 / 注释 71）
- **OPTIONS**: `--rewriting`
- **导入 (5)**: `Data.Nat`, `Data.Nat.Properties`, `Data.Empty`, `Relation.Binary.PropositionalEquality`, `Sovereign.Structology.T6`
- **record 类型**: `BoundedNeighborhood`, `DiscreteTorusFacts`
- **顶层签名 (13)**: `T6Card`, `T6Card-proof`, `T6Dim`, `T6Dim-proof`, `T6Neighbors`, `T6Neighbors-proof`, `t6-bounded`, `no-tangent-space`, `DiscreteCurvature`, `t6-curvature`, `t6-curvature-zero`, `t6-curvature-uniform`, `t6-facts`
- **质量**: `refl`×11；无 postulate / 无 hole

## `src/Sovereign/Algebra/ProjectionDifferential.agda`

- **module**: `Sovereign.Algebra.ProjectionDifferential`
- **行数**: 499（代码 251 / 注释 179）
- **OPTIONS**: `--rewriting`
- **导入 (7)**: `Data.Nat`, `Data.Product`, `Data.Empty`, `Relation.Binary.PropositionalEquality`, `Relation.Nullary`, `Sovereign.Base.Trit`, `Sovereign.Algebra.DegenerationTaxonomy`
- **record 类型**: `DifferenceVsDifferential`, `Mat2x2`, `FiniteVsInfinite`
- **顶层签名 (50)**: `GF3Func`, `sum3`, `shift`, `Δ`, `shift³≡id`, `shift≠id`, `Δ-const-zero`, `Δ²-is-const`, `Δ³≡0`, `sum3-Δ≡0`, `step-nonzero`, `gf3-difference`, `trace`, `det`, `mat2x2-count`, `mat2x2-dim`, `mat2x2-entries`, `mat2x2-entries-correct`, `charPoly`, `IsEigenvalue`, `Spectrum`, `charPoly-T₀`, `charPoly-T₁`, `charPoly-T₂`, `quad-not-all-roots`, `at-most-2-eigenvalues`, `spectrum-finite`, `gf3-finite-operators`, `eval₀`, `eval₀-x`, `eval₀-y`, `eval₀-witness-neq`, `eval₀-witness-eq`, `eval₀-not-injective`, `eval₀-degeneration`, `const-func`, `eval₀-const-valid`, `eval₀-sec-neq`, `eval₀-section`, `trace-x`, `trace-y`, `trace-witness-neq`, `trace-witness-eq`, `trace-not-injective`, `trace-degeneration`, `scalar-mat`, `trace-scalar-valid`, `trace-sec-t`, `trace-sec-neq`, `trace-section`
- **质量**: `refl`×97；无 postulate / 无 hole

## `src/Sovereign/Algebra/QuantumCorrespondence.agda`

- **module**: `Sovereign.Algebra.QuantumCorrespondence`
- **行数**: 198（代码 88 / 注释 73）
- **OPTIONS**: `--rewriting`
- **导入 (6)**: `Data.Product`, `Relation.Binary.PropositionalEquality`, `Data.Empty`, `Sovereign.Base.Trit`, `Sovereign.Algebra.GF9`, `Sovereign.Algebra.Duodecimal`
- **record 类型**: `QuantumStructure`
- **顶层签名 (25)**: `superposition-closure`, `superposition-01`, `superposition-11`, `superposition-02`, `superposition-12`, `superposition-22`, `superposition-assoc`, `superposition-comm`, `superposition-inverse`, `superposition-vacuumˡ`, `superposition-vacuumʳ`, `entanglement-pair`, `entanglement-involutive`, `entanglement-nonseparable`, `entanglement-multiplicative`, `entanglement-concrete`, `entanglement-trivial-on-real`, `vortex-phase-period`, `vortex-phase-assoc`, `vortex-phase-comm`, `vortex-phase-identityˡ`, `vortex-phase-identityʳ`, `vortex-phase-inverse`, `quantum-structure-witness`, `quantum-mul-assoc`
- **质量**: `refl`×9；无 postulate / 无 hole

## `src/Sovereign/Algebra/RepresentationBridge.agda`

- **module**: `Sovereign.Algebra.RepresentationBridge`
- **行数**: 298（代码 145 / 注释 112）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | Sovereign.Algebra.RepresentationBridge
  - P3-C: 表示论统一框架 — SO(3)→A₄ 与 SU(2)→2A₄ 分支规则的结构性连接
  - 核心定理:
  - 1. 膨胀 (Inflation): A₄ 的 4 个不可约表示 {V1,V1',V1'',V3}
  - 膨胀为 2A₄ 的 {W1,W1',W1'',W3}, 维数保持
  - 2. 旋量识别: 2A₄ 多出的 3 个不可约表示 {W2,W2',W2''} (dim=2)
  - 是 SU(2) 旋量结构的离散遗迹, -1 在其上作用为 -1
  - 3. SU(2)→2A₄ 分支表: j=0→W1, j=1/2→W2, j=1→W3,
  - j=3/2→W2'⊕W2'', j=2→W1'⊕W1''⊕W3
  - 4. 覆盖一致性: 整数自旋 → 仅膨胀表示 (无旋量);
  - 半整数自旋 → 仅旋量表示 (无膨胀)
  - 5. SO(3)↔SU(2) 匹配: 整数自旋的 SU(2)→2A₄ 分支
  - 与 SO(3)→A₄ 分支通过膨胀映射一致
  - 6. 维数会计: Σ(膨胀 dim²) = 12 = |A₄|,
  - Σ(旋量 dim²) = 12, 总计 24 = |2A₄|
  - 证明策略: 穷举法 (全 refl)
  - 宪法合规: 0 postulate, 禁止浮点
- **导入 (6)**: `Data.Nat`, `Data.Product`, `Relation.Binary.PropositionalEquality`, `Sovereign.Structology.A4Representations`, `Sovereign.Structology.BinaryTetrahedral`, `Sovereign.Algebra.BranchingRules`
- **data 类型**: `SU2Level`
- **顶层签名 (19)**: `inflate`, `inflate-dim`, `isSpinor`, `spinor-dim-W2`, `inflate-not-spinor`, `su2Dim`, `su2DimFormula`, `su2Dim-matches`, `su2Branch`, `su2-branch-dim`, `integer-no-spinor-0`, `integer-no-spinor-1`, `integer-no-spinor-2`, `match-0`, `match-1`, `match-2`, `inflate-dim-sq-sum`, `spinor-dim-sq-sum`, `dim-accounting`
- **质量**: `refl`×53；无 postulate / 无 hole

## `src/Sovereign/Algebra/SectionRisk.agda`

- **module**: `Sovereign.Algebra.SectionRisk`
- **行数**: 1017（代码 549 / 注释 300）
- **OPTIONS**: `--rewriting`
- **导入 (14)**: `Data.Nat`, `Data.Fin`, `Data.Fin`, `Data.Empty`, `Data.Product`, `Data.String`, `Relation.Binary.PropositionalEquality`, `Relation.Nullary`, `Sovereign.Base.Trit`, `Sovereign.Algebra.GF9`, `Sovereign.Algebra.Duodecimal`, `Sovereign.RootMath.DigitalRoot`, `Sovereign.Algebra.DegenerationTaxonomy`, `Sovereign.Algebra.DigitalRootCycle`
- **record 类型**: `SectionPair`, `SectionRisk`, `UnifiedProjection`
- **顶层签名 (138)**: `complex-proj`, `complex-sec₁`, `complex-sec₂`, `complex-sec₁-valid`, `complex-sec₂-valid`, `complex-secs-differ`, `complex-section`, `complex-pair`, `complex-frobenius-involutive`, `complex-frobenius-multiplicative`, `complex-fiber-size`, `complex-section-picks`, `¬-complex-complete`, `complex-gauge-info`, `complex-risk`, `diffgeo-proj`, `diffgeo-sec₁`, `diffgeo-sec₂`, `diffgeo-sec₁-valid`, `diffgeo-sec₂-valid`, `diffgeo-secs-differ`, `diffgeo-section`, `diffgeo-pair`, `diffgeo-tangent-dim`, `diffgeo-tangent-correct`, `diffgeo-lattice-size`, `diffgeo-lattice-correct`, `¬-tangent-sees-global`, `diffgeo-info-loss`, `diffgeo-full-tour`, `diffgeo-full-tour-value`, `¬-tangent-euclidean`, `diffgeo-gauge-info`, `diffgeo-risk`, `harmonic-sec₁`, `harmonic-sec₂`, `harmonic-sec₁-valid`, `harmonic-sec₂-valid`, `harmonic-secs-differ`, `harmonic-section`, `harmonic-pair`, `harmonic-total-freq`, `harmonic-base-freq`, `harmonic-fiber-per-base`, `harmonic-factorization`, `harmonic-crt-roundtrip`, `¬-spectrum-continuous`, `harmonic-polar`, `harmonic-torus`, `harmonic-gauge-info`, `harmonic-risk`, `linalg-proj`, `linalg-sec₁`, `linalg-sec₂`, `linalg-sec₁-valid`, `linalg-sec₂-valid`, `linalg-secs-differ`, `linalg-section`, `linalg-pair`, `linalg-gf3-mult`
  - … 其余 78 项
- **质量**: `refl`×44；无 postulate / 无 hole

## `src/Sovereign/Algebra/SpectralFunctionTheory.agda`

- **module**: `Sovereign.Algebra.SpectralFunctionTheory`
- **行数**: 171（代码 60 / 注释 77）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | Sovereign.Algebra.SpectralFunctionTheory
  - 谱函数论 — GF(9)* 特征标与离散 Fourier 分析
  - 数学背景:
  - GF(9)* 是 8 阶循环群, 生成元 φ = 1+α。
  - 特征标 χ : GF(9)* → GF(9)* 是乘性群的同态。
  - 离散 Fourier 变换: f̂(k) = Σₓ f(x) · χₖ(x)
  - Plancherel 定理: Σ|f(x)|² = Σ|f̂(k)|²
  - 核心定理:
  - §1 GF(9)* 特征标: 8 个特征标 (循环群的对偶)
  - §2 离散 Fourier 变换: 在 GF(9) 上的 DFT
  - §3 正交性: 特征标的正交关系
  - §4 Plancherel 定理: 能量守恒
  - 依赖:
  - Sovereign.Base.Trit — GF(3)
  - Sovereign.Algebra.GF9 — GF(9) 域
  - 0 postulate — 全部构造性证明
- **导入 (7)**: `Data.Nat`, `Data.Vec`, `Data.Fin`, `Data.Product`, `Relation.Binary.PropositionalEquality`, `Sovereign.Base.Trit`, `Sovereign.Algebra.GF9`
- **顶层签名 (15)**: `character`, `character-0`, `character-1`, `character-2-gen`, `character-4-gen`, `character-8-gen`, `GF9StarFunc`, `fromGF9-idx`, `eval-func`, `const-func`, `mul-accumulate`, `fourier-coeff`, `identity-fourier`, `identity-at-0`, `identity-at-4`
- **质量**: `refl`×7；无 postulate / 无 hole

## `src/Sovereign/Algebra/SpiralCycle.agda`

- **module**: `Sovereign.Algebra.SpiralCycle`
- **行数**: 156（代码 77 / 注释 41）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | Sovereign.Algebra.SpiralCycle
  - ⟨2⟩ 六环定理：Christoffel 螺旋 {1,2,4,8,7,5} 的代数闭合
  - 数学背景：
  - (ℤ/9ℤ)* = {1,2,4,5,7,8}，|(ℤ/9ℤ)*| = φ(9) = 6。
  - 倍频算子 x ↦ 2x mod 9 是单位群上的自同构（2 可逆 mod 9）。
  - 轨道 ⟨2⟩ = {1 → 2 → 4 → 8 → 7 → 5 → 1} 恰为全部单位：
  - 2¹ ≡ 2, 2² ≡ 4, 2³ ≡ 8, 2⁴ ≡ 16 ≡ 7, 2⁵ ≡ 32 ≡ 5, 2⁶ ≡ 64 ≡ 1 (mod 9)
  - 因此 2 生成 (ℤ/9ℤ)*，|⟨2⟩| = 6，轨道六步闭合——"124875" 螺旋。
  - 与循环数的联系：1/7 = 0.\overline{142857}，142857 是周期 6 的循环数；
  - 2×142857 = 285714、4×142857 = 571428——倍频 = 数字旋转，
  - 即 ⟨2⟩₉ ≅ ⟨10⟩₇ ≅ C₆ 的两个投影。
  - 0 postulate — 全部 refl 构造性证明（字面量计算归约）
- **导入 (4)**: `Data.Nat`, `Data.Product`, `Relation.Binary.PropositionalEquality`, `Relation.Nullary`
- **顶层签名 (30)**: `_≢_`, `double-mod9`, `spiral-step-1`, `spiral-step-2`, `spiral-step-4`, `spiral-step-8`, `spiral-step-7`, `spiral-step-5`, `spiral-order-6`, `spiral-minimal-1`, `spiral-minimal-2`, `spiral-minimal-3`, `spiral-minimal-4`, `spiral-minimal-5`, `six-steps-return`, `unit-hit-1`, `unit-hit-2`, `unit-hit-4`, `unit-hit-8`, `unit-hit-7`, `unit-hit-5`, `units-distinct`, `one-seventh-cycle`, `cyclic-rotate-2`, `cyclic-rotate-4`, `cyclic-rotate-3`, `cyclic-rotate-5`, `cyclic-rotate-6`, `fraction-doubling-rotates`, `dr-999999`
- **质量**: `refl`×24；无 postulate / 无 hole

## `src/Sovereign/Algebra/Tetration.agda`

- **module**: `Sovereign.Algebra.Tetration`
- **行数**: 177（代码 52 / 注释 85）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | Sovereign.Algebra.Tetration
  - 超运算 / 指数塔 — 递归数据类型定义
  - 语料: "12^12^12^12" (四层嵌套指数塔)
  - 数学: tetration (超-4 运算) ↑↑n
  - 定义:
  - §1 超运算层级: successor → addition → multiplication → exponentiation → tetration
  - §2 指数塔数据类型: 有限嵌套
  - §3 有限域中的指数塔坍缩 (模周期)
  - 0 postulate.
- **导入 (2)**: `Data.Nat`, `Relation.Binary.PropositionalEquality`
- **顶层签名 (23)**: `hyper0`, `hyper1`, `hyper2`, `hyper3`, `tetration`, `pentation`, `t-2-1`, `t-2-2`, `t-2-3`, `t-2-4`, `t-3-1`, `t-3-2`, `t-3-3`, `t-12-1`, `t-12-2`, `mod6-12`, `mod3-12`, `mod4-12`, `mod8-12sq`, `mod9-12sq`, `mod12-12`, `mod3-12sq`, `mod4-12sq`
- **质量**: `refl`×18；无 postulate / 无 hole

## `src/Sovereign/Algebra/TowerConnection.agda`

- **module**: `Sovereign.Algebra.TowerConnection`
- **行数**: 421（代码 203 / 注释 149）
- **OPTIONS**: `--rewriting`
- **头部注释（数学背景）**:
  - | Sovereign.Algebra.TowerConnection
  - 域扩张塔的连接定理 — 嵌入映射及其同态性质
  - 子域格 (Hasse 图):
  - GF(729) n=6
  - /         \
  - GF(27)       GF(9)
  - n=3           n=2
  - \         /
  - GF(3) n=1
  - GF(243) n=5
  - |
  - GF(3) n=1
  - 本模块形式化:
  - ① 嵌入映射: GF(3)→GF(9), GF(3)→GF(27), GF(3)→GF(243),
  - GF(3)→GF(729), GF(9)→GF(729), GF(27)→GF(729)
  - ② 嵌入保持加法 (所有嵌入) 和乘法 (GF(3)→GF(9))
- **导入 (11)**: `Data.Product`, `Data.Vec`, `Data.Fin`, `Relation.Binary.PropositionalEquality`, `Sovereign.Base.Trit`, `Sovereign.Algebra.GF9`, `Sovereign.Algebra.GF27`, `Sovereign.Algebra.GF243`, `Sovereign.Algebra.GF729`, `Sovereign.Algebra.FieldExtensionTower`, `Data.Nat`
- **record 类型**: `SubfieldEmbedding`
- **顶层签名 (47)**: `embed-3-9`, `embed-3-27`, `embed-3-243`, `embed-3-729`, `embed-9-729`, `embed-27-729`, `embed-3-9-add`, `embed-3-27-add`, `embed-3-243-add`, `embed-3-729-add`, `embed-9-729-add`, `embed-27-729-add`, `embed-3-9-mul`, `embed-3-9-one`, `embed-3-27-one`, `embed-3-9-inj`, `embed-3-27-inj`, `embed-3-243-inj`, `tritToFin3-inj`, `embed-3-729-inj`, `embed-9-729-inj`, `embed-27-729-inj`, `tower-3-9-729`, `tower-3-27-729`, `embed-3-9-zero`, `embed-3-27-zero`, `embed-3-729-zero`, `embed-9-729-zero`, `embed-27-729-zero`, `embed-3-9-neg`, `tritToFin3-negate`, `subfield-3-9`, `subfield-3-27`, `subfield-3-243`, `subfield-3-729`, `subfield-9-729`, `subfield-27-729`, `degree-3-9`, `degree-3-27`, `degree-3-243`, `degree-3-729`, `degree-9-729`, `degree-27-729`, `tower-law-9`, `tower-law-27`, `dim-729-over-9`, `dim-729-over-27`
- **质量**: `refl`×38；无 postulate / 无 hole

## `src/Sovereign/Algebra/TriCycGraph.agda`

- **module**: `Sovereign.Algebra.TriCycGraph`
- **行数**: 134（代码 66 / 注释 36）
- **OPTIONS**: `--rewriting --guardedness`
- **导入 (5)**: `Data.Fin`, `Data.Product`, `Relation.Binary.PropositionalEquality`, `Sovereign.Base.Trit`, `Sovereign.Algebra.GF9`
- **顶层签名 (20)**: `TriCycGraph`, `edge₀₁`, `edge₁₂`, `edge₂₀`, `fin3-shift`, `fin3-shift³`, `shift`, `zeroGraph`, `oneGraph`, `pureShift`, `pureShift³-id`, `shift²-pure`, `fin3-shift⁶`, `σ⁶-id`, `shift⁶-id`, `_⊗g_`, `_⊕g_`, `⊗g-comm`, `⊕g-comm`, `totalWeight`
- **质量**: `refl`×7；无 postulate / 无 hole

## `src/Sovereign/Algebra/TriadicHarmonic.agda`

- **module**: `Sovereign.Algebra.TriadicHarmonic`
- **行数**: 207（代码 120 / 注释 49）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | Sovereign.Algebra.TriadicHarmonic
  - 三合弦恒等式: i²+1²=0, i⁶+1⁶=0, i¹⁰+1¹⁰=0
  - 数学意义 (GF(3) 三元框架):
  - 在 GF(9) = GF(3)(α) 中, alpha = (T₀,T₁), 满足 α² = -1, α⁴ = 1。
  - 故 GF(9)ˣ ≅ C₈, α 是生成元。α² 生成 C₄ 子群。
  - 河图解释 (地数奇谐波):
  - 地数 {2,4,6,8,10} 中取奇数位 {第1,第3,第5} = {2,6,10}:
  - 地二生火 (2) = 存在公理 | 地六成水 (6) = 动态公理 | 地十成土 (10) = 闭合公理
  - 不是算术 2+4+4 的归纳序列, 是 C₃ 群轨道在河图地数上的三个独立投影。
  - 2×{1,3,5} = {2,6,10} 中 {1,3,5} 在 C₃ 下构成轨道 (1→3→5→1 mod 6)。
  - 同调等价性:
  - 0² 与 0⁶ 在 CRT 投影 (144,46) 下都归零。区别在迹映射层: Tr(i²)=Tr(i⁶)=-1。
  - 这是"两仪无区别, 三才分别之"的代数表达。
- **导入 (8)**: `Data.Nat`, `Data.Nat.Properties`, `Data.Product`, `Relation.Binary.PropositionalEquality`, `Data.Sum`, `Sovereign.Base.Trit`, `Sovereign.Algebra.GF9`, `Data.List`
- **顶层签名 (29)**: `𝟘`, `𝟙`, `-𝟙`, `α²`, `α²≡-𝟙`, `α⁴`, `α⁴≡𝟙`, `α⁶`, `α⁶≡α²`, `α¹⁰`, `α¹⁰≡α²`, `alpha-power`, `α⁰≡𝟙`, `α¹≡α`, `α³≢𝟙`, `involution-unique`, `dual-n`, `inv-dual-n`, `dual-closed`, `betti-match`, `alpha-power-add4-9case`, `alpha-power-add4`, `地数`, `奇谐波指数`, `奇谐波特性`, `生成对`, `成对`, `生成成对偶闭合`, `triadic-harmonic-theorem`
- **质量**: `refl`×49；无 postulate / 无 hole

## `src/Sovereign/Algebra/UniversalAlgebra.agda`

- **module**: `Sovereign.Algebra.UniversalAlgebra`
- **行数**: 340（代码 258 / 注释 45）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | Sovereign.Algebra.UniversalAlgebra
  - 08 一般代数系统 — 代数结构层级 + 实例 + 同态 + 分类 (0 postulate)
  - 泛代数的离散落位: 结构记录层级 (半群/幺半群/群/Abel 群/环/域)
  - 在律算合一三大载体 (GF(3) / Z/12Z / GF(9)) 上的实例,
  - 全称同态定理 (保幺元/保持求值) 与域分类 (零因子 ⟹ 非域)。
  - 结构: §1 结构记录层级; §2 三大载体实例; §3 同态定理;
  - §4 分类: IsField + 零因子否定定理 + GF(3) 是域 / Z/12Z 非域
- **导入 (7)**: `Data.Product`, `Data.Empty`, `Relation.Nullary`, `Relation.Binary.PropositionalEquality`, `Sovereign.Base.Trit`, `Sovereign.Algebra.Duodecimal`, `Sovereign.Algebra.GF9`
- **data 类型**: `Term2`
- **record 类型**: `Semigroup`, `CommSemiring`, `Monoid`, `Group`, `AbelianGroup`, `Ring`, `IsField`
- **顶层签名 (19)**: `_≢_`, `trit-add`, `trit-mul`, `trit-ring`, `trit-semiring`, `duodec-add`, `gf9-add`, `gf9-mul-comm`, `gf9-mul-identityˡ`, `gf9-mul-identityʳ`, `gf9-distribʳ`, `hom-preserves-zero`, `eval`, `hom-preserves-eval`, `negate-add-hom`, `negate-is-automorphism`, `zero-divisor-not-field`, `trit-field`, `duodec-not-field`
- **质量**: `refl`×17；无 postulate / 无 hole

## `src/Sovereign/Algebra/VortexConnections.agda`

- **module**: `Sovereign.Algebra.VortexConnections`
- **行数**: 372（代码 229 / 注释 81）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | Sovereign.Algebra.VortexConnections
  - Z/12Z 与 CRT/4320D/十二律的连接定理
  - 代数链扩展 (Duodecimal L8-L10, VortexTower L11-L13 之后):
  - C1: CRT₁₂ 往返恒等 — Z/12Z ≅ Z/3Z × Z/4Z (12 case 穷举)
  - C2: 涡旋塔嵌入 Z/12Z → Z/144Z — 加法同态
  - C3: 4320 = 12 × 360 — 全息维度与十二律基的连接
  - C4: 6624 mod 12 = 0 — 相位对齐
  - C5: 十二律 ↔ Z/12Z 双射
  - C6: 倍频链 3→6→12 — 涡旋根
  - C7: (Z/12Z)* 阶 = 4 — 单位群
  - C8: 零因子 — Z/12Z 不是域
  - 0 postulate — 全部构造性证明
- **导入 (12)**: `Data.Nat`, `Data.Nat.DivMod`, `Data.Nat.Properties`, `Data.Fin`, `Data.Fin.Properties`, `Data.Product`, `Relation.Binary.PropositionalEquality`, `Sovereign.Base.Trit`, `Sovereign.Algebra.Duodecimal`, `Sovereign.Algebra.VortexTower`, `Sovereign.Structology.HoloInformation`, `Sovereign.Coupling.LossGain`
- **顶层签名 (41)**: `crt12-roundtrip`, `crt12-inv-π3`, `crt12-inv-π4`, `embed-12-144`, `embed-d0`, `embed-val`, `embed-12-144-hom`, `vortex-4320-base`, `vortex-4320-decomp`, `holo-4320-≡`, `phase-align-12`, `fulltour-div-12`, `fulltour-factor-12`, `LüName`, `duodecToLü`, `lüToDuodec`, `lü-roundtrip`, `lü-roundtripʳ`, `huangzhong-is-d0`, `zhonglv-is-d5`, `lü-index-complete`, `vortex-root-chain`, `vortex-12-crt`, `vortex-144-sq`, `DuodecUnit`, `unit-group-order`, `unit-group-order-val`, `u5-self-inverse`, `u7-self-inverse`, `u11-self-inverse`, `unit-closure`, `not-a-field`, `huangzhong-length`, `sun-op-81`, `yi-op-81`, `sovereign-lcm-val`, `tower-level1-product`, `tower-level2-product`, `tower-level3-product`, `polar-winding-12sq`, `crt12-tower-consistency`
- **质量**: `refl`×237；无 postulate / 无 hole

## `src/Sovereign/Algebra/VortexDifferential.agda`

- **module**: `Sovereign.Algebra.VortexDifferential`
- **行数**: 502（代码 356 / 注释 86）
- **OPTIONS**: `--rewriting --guardedness`
- **导入 (7)**: `Function`, `Data.Nat`, `Data.Fin`, `Data.Product`, `Relation.Binary.PropositionalEquality`, `Sovereign.Base.Trit`, `Sovereign.Algebra.Duodecimal`
- **顶层签名 (33)**: `VortexFunc`, `_⊕f_`, `negatef`, `_≋_`, `shift₁₂`, `Δ₁₂`, `sum12`, `Σ₁₂`, `const₁₂`, `negate-⊗`, `negate-⊗ʳ`, `negate-double`, `negate-⊕`, `⊕-swap-mid`, `+1-⊖-dist`, `Δ₁₂-linear`, `Δ₁₂-scalar`, `shift₁₂-comm`, `Δ₁₂-const-zero`, `sum₁₂-annihilation`, `+1³`, `Δ₁₂²-expand`, `cancel-pair`, `inner-telescope`, `telescope-4`, `Δ₁₂³-is-3step`, `shift-conv`, `sum12-distrib`, `sum12-cong`, `negate-distrib`, `sum12-negate`, `⊗-negateʳ`, `Δ₁₂-leibniz`
- **质量**: `refl`×132；无 postulate / 无 hole

## `src/Sovereign/Algebra/VortexRoot.agda`

- **module**: `Sovereign.Algebra.VortexRoot`
- **行数**: 113（代码 46 / 注释 41）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | Sovereign.Algebra.VortexRoot
  - 涡旋根 "123" — 代数极本体的正式落位 (0 postulate)
  - AlgebraicPoleUnified 自述的第一缺口: VortexRoot.agda 尚未创建。
  - 本模块闭合该缺口: L0/L0U/L0C 的代数载体已由 Duodecial.agda 完整提供
  - (Z/12Z 环 + V₄ 单位群 + CRT 分解), 本模块补上本体论层:
  - §1 根命名 "123" (数字根 = 6 = 二次谐波)
  - §2 倍频量子纠缠链: 3(基频) → 6(二次谐波) → 12(四次谐波)
  - §3 Merkaba 回绕: 24 = 12×2 → dr(24) = 6; 水态 36 = 12×3
  - §4 本体论地位注释 (诚实): "12 是独立根 '123', 非 3×4 分解" 为
  - 命名学立场; 代数上 L0C 的 CRT 同构 Z/12Z ≅ Z/3Z × Z/4Z
  - 与之并存 — 本体根在命名上独立, 在代数上可分解。
- **导入 (4)**: `Data.Nat`, `Relation.Binary.PropositionalEquality`, `Sovereign.RootMath.DigitalRoot`, `Sovereign.Algebra.Duodecimal`
- **data 类型**: `VortexRoot`
- **顶层签名 (16)**: `root-123-digital-root`, `doubling-3-6`, `doubling-6-12`, `fourth-harmonic`, `doubling-chain`, `merkaba-double`, `merkaba-digital-root`, `water-state`, `vortexValue`, `next`, `vortex-value-3`, `vortex-value-6`, `vortex-value-12`, `vortex-next-3-6`, `vortex-next-6-12`, `vortex-next-12-6`
- **质量**: `refl`×15；无 postulate / 无 hole

## `src/Sovereign/Algebra/VortexTower.agda`

- **module**: `Sovereign.Algebra.VortexTower`
- **行数**: 441（代码 320 / 注释 53）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | Sovereign.Algebra.VortexTower
  - 涡旋塔扩张：Z/12ⁿZ 的 CRT 正交分解塔
  - 代数链扩展 (Duodecimal L8-L10 之后):
  - L11: Z/144Z 环 — 极向缠绕 144 = 12² 的代数结构
  - L12: CRT 分解 Z/144Z ≅ Z/9Z × Z/16Z — 3² × 2⁴ 正交分解
  - L13: 涡旋塔公式 Z/12ⁿZ ≅ Z/3ⁿZ × Z/2²ⁿZ
  - 核心定理:
  - 144 = 12² = 极向缠绕数 (PolarWinding)
  - 144 = 9 × 16 = 3² × 2⁴, gcd(9,16) = 1
  - Z/144Z ≅ Z/9Z × Z/16Z (CRT)
  - 1728 = 12³ = 27 × 64, gcd(27,64) = 1
  - 涡旋塔层级:
  - n=1: Z/12Z   ≅ Z/3Z  × Z/4Z   (Duodecimal.agda)
  - n=2: Z/144Z  ≅ Z/9Z  × Z/16Z  (本模块)
  - n=3: Z/1728Z ≅ Z/27Z × Z/64Z  (本模块)
  - 0 postulate — 全部构造性证明
- **导入 (16)**: `Data.Nat`, `Data.Nat.DivMod`, `Data.Nat.Properties`, `Data.Nat.GCD`, `Data.Nat.Coprimality`, `Data.Nat.Divisibility.Core`, `Data.Nat.Divisibility`, `Data.Fin`, `Data.Fin.Properties`, `Data.Product`, `Relation.Binary.PropositionalEquality`, `Data.Empty`, `Relation.Nullary`, `Sovereign.AlgebraWrapper`, `Sovereign.Structology.Winding`, `Sovereign.Algebra.Duodecimal`
- **data 类型**: `TowerLevel`
- **顶层签名 (59)**: `Z144`, `0₁₄₄`, `1₁₄₄`, `toℕ-0₁₄₄`, `toℕ-1₁₄₄`, `mod-absorbˡ`, `mod-absorbʳ`, `+₁₄₄-assoc`, `+₁₄₄-comm`, `+₁₄₄-identityˡ`, `+₁₄₄-identityʳ`, `*₁₄₄-comm`, `*₁₄₄-identityˡ`, `*₁₄₄-identityʳ`, `*₁₄₄-zeroˡ`, `π9`, `π16`, `toℕ-π9`, `toℕ-π16`, `crt144`, `crt-e₁-mod9`, `crt-e₁-mod16`, `crt-e₂-mod9`, `crt-e₂-mod16`, `coprime-9-16`, `crt-merge-9-16`, `arith-mod9`, `arith-mod16`, `crt144-mod9`, `crt144-mod16`, `crt144-roundtrip`, `crt144-inv-π9`, `crt144-inv-π16`, `tower-n1-product`, `tower-n1-gcd`, `tower-n1-roundtrip`, `tower-n2-product`, `tower-n2-gcd`, `tower-n2-roundtrip`, `tower-n3-product`, `tower-n3-gcd`, `π27`, `π64`, `crt1728`, `crt1728-e₁-mod27`, `crt1728-e₁-mod64`, `crt1728-e₂-mod27`, `crt1728-e₂-mod64`, `polar-is-12-sq`, `polar-decomposition`, `cube-12`, `polar-winding-value`, `crt144-product`, `crt1728-product`, `towerModulus`, `towerMod3`, `towerMod2`, `tower-product`, `tower-gcd`
- **质量**: `refl`×31；无 postulate / 无 hole

## `src/Sovereign/Algebra/ZeroCrossing.agda`

- **module**: `Sovereign.Algebra.ZeroCrossing`
- **行数**: 119（代码 34 / 注释 62）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | Sovereign.Algebra.ZeroCrossing
  - 零元跨维度归零 — 零幂族的代数形式
  - 零幂族 (Zero Power Family):
  - 零幂不是算术乘法 (0×0=0), 而是量子矢量相位回归的代数形式。
  - 零是唯一能跨维度的元素: 0^n = 0 对所有 n ≥ 1。
  - 零吸收一切幂次, 零的相位空间是单点 (无方向自由度)。
  - 0² 不是"零的平方", 而是"零的二次幂 = 零" (零幂族)。
  - 语料: "零的平方=零的五次方……零的一就等于零的N次方" (word_98, 七锚齐备)
  - 语料: "只有0跨维度" / "0是一切的密码" (ppt_27, ppt_7)
  - ⚠️ 深度澄清 (2026-08-19):
  - 在我们的框架中:
  - · 归零是量子矢量相位回归，是动态过程，不是静态状态
  - · 动态幻方中: 归零 = 矢量方向经过 3 步 (+1 归零轨道) 回到原点
  - · DuodecClock 中: 不是 Z/12 加法群 (模 12 环有零因子)，
  - 而是 Z/3_加 ⊕ ⟨α⟩_乘 的加乘联合周期
  - · 零幂的真正含义: 零矢量在任何方向上的相位演化都回归到零，
  - 因为零的相位空间是单点 (无方向自由度)
  - · "只有0跨维度" = 零是唯一能在所有维度方向上保持不变的矢量
- **导入 (5)**: `Data.Nat`, `Data.Product`, `Relation.Binary.PropositionalEquality`, `Sovereign.Base.Trit`, `Sovereign.Algebra.GF9`
- **顶层签名 (10)**: `additive-zero-crossing`, `char-3-zero`, `char-3-zero-2`, `mul-zero-left`, `mul-zero-right`, `pow-zero-stable`, `zero-squared`, `zero-cubed`, `zero-to-5`, `zero-to-11`
- **质量**: `refl`×8；无 postulate / 无 hole
