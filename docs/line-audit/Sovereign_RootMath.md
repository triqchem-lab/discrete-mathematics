# 目录 `src/Sovereign/RootMath/` 逐模块审计记录

共 8 个模块。


## `src/Sovereign/RootMath/AlgebraicComplex.agda`

- **module**: `Sovereign.RootMath.AlgebraicComplex`
- **行数**: 205（代码 81 / 注释 82）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | Sovereign.RootMath.AlgebraicComplex
  - 代数复数：避免连续统的复数表示
  - 宪法原则：
  - 1. 禁止使用 Data.Complex (连续统复数)。
  - 2. 复数表示为 (实部 : ℚ, 虚部系数 : ℚ)，对应 a + b√(-1)。
  - 3. 在律算中，虚部通常与能隙 Δ=√3 关联，因此使用 √3 系数更合适。
  - 本模块提供两种代数复数：
  - Gaussian: a + bi (i² = -1)
  - Sqrt3: a + b√3 (用于能隙相关计算)
- **导入 (3)**: `Data.Rational`, `Data.Integer`, `Relation.Binary.PropositionalEquality`
- **record 类型**: `Gaussian`, `Sqrt3`, `Sqrt2`
- **顶层签名 (17)**: `i`, `_-ᵍ_`, `conjᵍ`, `normSqᵍ`, `sqrt3`, `_-ˢ_`, `conjˢ`, `normˢ`, `sqrt2`, `_-²_`, `conj²`, `norm²`, `sqrt2Sq`, `sqrt2SqProof`, `EnergyGap`, `EnergyGapSq`, `EnergyGapIs3`
- **质量**: `refl`×5；无 postulate / 无 hole

## `src/Sovereign/RootMath/Arithmetic.agda`

- **module**: `Sovereign.RootMath.Arithmetic`
- **行数**: 118（代码 46 / 注释 53）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | Sovereign.RootMath.Arithmetic
  - 根数学:高维几何审查后的算术引理
  - 宪法原则:
  - 1. 所有算术引理必须基于 GF(3) 格点拓扑重新证明。
  - 2. 本模块通过引用标准库已证明引理，消除所有 postulate。
  - 3. 标准库引理视为"几何审查通过"的信任基座。
- **导入 (8)**: `Data.Nat`, `Data.Nat.Base`, `Data.Bool`, `Relation.Binary.PropositionalEquality`, `Data.Nat.DivMod`, `Data.Nat.Divisibility.Core`, `Data.Nat.Properties`, `Data.Product`
- **data 类型**: `ReviewStatus`
- **顶层签名 (7)**: `+-mod-verified`, `+-mod-trusted`, `div-mod-theorem`, `div-mod-uniqueness`, `gf3-periodicity`, `144-mod-3≡0`, `arithmetic_lemmas_status`
- **质量**: `refl`×4；无 postulate / 无 hole

## `src/Sovereign/RootMath/Base.agda`

- **module**: `Sovereign.RootMath.Base`
- **行数**: 111（代码 83 / 注释 6）
- **OPTIONS**: `--rewriting --guardedness`
- **导入 (10)**: `Data.Nat`, `Data.Nat.DivMod`, `Data.Nat.Properties`, `Data.Bool`, `Data.Integer`, `Data.Fin`, `Data.Vec`, `Data.Sum.Base`, `Data.Empty`, `Relation.Binary.PropositionalEquality`
- **data 类型**: `Trit`, `StableDigitalRoot`
- **顶层签名 (15)**: `tritToℕ`, `tritEncode`, `tritDecode`, `encodeDecodeInverse`, `tritEq`, `gf3Zero`, `gf3Neg`, `gf3NegCancel`, `Tryte`, `tryteToℕ⁶`, `zeroTryte`, `digitalRoot`, `digitalRoot≤9`, `isStableRoot`, `IsStable`
- **质量**: `refl`×7；⚠️ 1 postulate

## `src/Sovereign/RootMath/DigitalRoot.agda`

- **module**: `Sovereign.RootMath.DigitalRoot`
- **行数**: 222（代码 117 / 注释 68）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | Sovereign.RootMath.DigitalRoot
  - 根数学：数字根公理与稳定驻波判定
  - 公理：稳定驻波对应的长度比例数字根必须 ∈ {0, 3, 6}（模 9 意义下）
  - 0 代表传统数字根定义中的 9（9 ≡ 0 mod 9）。
  - 其余因干涉相消无法在 T⁶ 环面驻留
- **导入 (8)**: `Data.Nat`, `Data.Nat.DivMod`, `Data.Bool`, `Data.List`, `Data.Maybe`, `Relation.Nullary`, `Relation.Binary.PropositionalEquality`, `Data.Product`
- **data 类型**: `StableRoot`, `IsStableResonance`, `ChristosPhase`
- **record 类型**: `StableLengthRatio`
- **顶层签名 (20)**: `digitalRoot`, `digitalRootMod9`, `isStableRoot`, `mkStableRatio`, `tryStableRatio`, `twelvePitches`, `pitchDigitalRoots`, `stablePitches`, `digitalRootAdd`, `digitalRootMul`, `stableRootAddClosed`, `axiomDigitalRoot`, `unstableResonanceElim`, `christosSequence`, `christosStep`, `iterateChristos`, `christosClosure`, `phaseToValue`, `nextPhase`, `christosPeriod6`
- **质量**: `refl`×10；无 postulate / 无 hole

## `src/Sovereign/RootMath/Eisenstein.agda`

- **module**: `Sovereign.RootMath.Eisenstein`
- **行数**: 968（代码 810 / 注释 82）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | Sovereign.RootMath.Eisenstein
  - Eisenstein 整数环 Z[ω]:  a + b·ω, 其中 ω² + ω + 1 = 0, ω³ = 1
  - 宪法原则:
  - 1. 禁止使用浮点复数 (Data.Complex). 这是离散数学, 不能有连续统.
  - 2. Z[ω] 是 A₄ 特征标值的自然系数环:
  - 三维表示 χ₃: 值 ∈ {3, 0, -1} ⊂ ℤ ⊂ Z[ω]
  - 一维表示 χ₁': 值 ∈ {1, ω, ω²} ⊂ Z[ω]
  - 3. 乘法规则利用 ω² = -1 - ω, 避免任何 √3 或浮点.
  - 4. Z[ω] ≅ { (a,b) ∈ ℤ² | 乘法: (ac-bd) + (ad+bc-bd)ω }
  - 参考:
  - C++: /home/yanli/work/math/cpp/include/fixed_complex.h (Q16 Z[ω])
  - Agda: RootMath/AlgebraicComplex.agda (Gaussian / Sqrt3 pattern)
- **导入 (4)**: `Data.Integer`, `Data.Integer.Properties`, `Data.Nat`, `Relation.Binary.PropositionalEquality`
- **record 类型**: `Eisenstein`
- **顶层签名 (59)**: `0ᵉ`, `1ᵉ`, `ωᵉ`, `ω²ᵉ`, `-1ᵉ`, `3ᵉ`, `conjᵉ`, `ω³≡1`, `conj-ω≡ω²`, `conj-ω²≡ω`, `χ₃-1`, `χ₃-3cycle`, `χ₃-2trans`, `χ₁-val`, `0ℤ`, `-ᵉ_`, `+ᵉ-comm`, `+ᵉ-assoc`, `+ᵉ-identityˡ`, `+ᵉ-identityʳ`, `+ᵉ-inverseˡ`, `+ᵉ-inverseʳ`, `*ᵉ-comm`, `*ᵉ-assoc`, `*ᵉ-identityˡ`, `*ᵉ-identityʳ`, `*ᵉ-distribˡ`, `*ᵉ-distribʳ`, `normᵉ`, `norm-form`, `conjᵉ-mul`, `mul-real`, `norm-mul`, `unit1`, `unitm1`, `unitω`, `unitω2`, `unitmω`, `unitmω2`, `unit-inv-1`, `unit-inv-m1`, `unit-inv-ω`, `unit-inv-ω2`, `unit-inv-mω`, `unit-inv-mω2`, `unit-norm-1`, `unit-norm-m1`, `unit-norm-ω`, `unit-norm-ω2`, `unit-norm-mω`, `unit-norm-mω2`, `unitGen`, `unitGen-pow-0`, `unitGen-pow-1`, `unitGen-pow-2`, `unitGen-pow-3`, `unitGen-pow-4`, `unitGen-pow-5`, `unitGen-pow-6`
- **质量**: `refl`×28；无 postulate / 无 hole

## `src/Sovereign/RootMath/EnergyGap.agda`

- **module**: `Sovereign.RootMath.EnergyGap`
- **行数**: 305（代码 146 / 注释 101）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | Sovereign.RootMath.EnergyGap
  - 根数学：能隙 Δ=√3 与弦长 √3 的起源
  - 本质：T⁶ 复三维离散环面上 C3 循环群生成元作用下的复振幅跃迁
  - 相生 (+1) 与相克 (ω) 格点间的最小不可分间距
  - 注意：非连续统能量差、声学阻抗或量子涨落
  - 宪法合规：
  - 零 postulate
  - 能隙 Δ=√3 使用 Sovereign.RootMath.AlgebraicComplex.Sqrt3 代数定义
  - 所有物理相关参数标记为 EXPERIMENTAL_PARAMETER 记录（非 postulate）
- **导入 (8)**: `Relation.Binary.PropositionalEquality`, `Data.Empty`, `Data.Nat`, `Data.Integer`, `Data.Rational`, `Data.Product`, `Data.Bool`, `Sovereign.RootMath.AlgebraicComplex`
- **data 类型**: `C3Element`, `ContinuousEnergyDiff`, `AcousticImpedance`, `QuantumFluctuation`
- **record 类型**: `ChordLength`, `HomomorphismChain`, `ZhonglvPrepTrigger`, `ShouldTriggerZhonglvPrep`
- **顶层签名 (27)**: `_⊙_`, `omegaCubedIsId`, `c3ToSqrt3`, `phaseGenerate`, `phaseOvercome`, `energyGapJump`, `energyGapNorm`, `algebraicEnergyGap`, `halfEnergyGap`, `halfEnergyGapModSq`, `chordLengthSquared`, `standardChord`, `standardChordCorrect`, `homomorphismInstance`, `timeSpaceUnification`, `hermiteMetric`, `yaoTrapThreshold`, `halfGapExactSquared`, `ℤabs`, `zhonglvPrepInstance`, `shouldTriggerZhonglvPrep`, `EnergyGapDefinition`, `C3GeneratorComplexAmplitudeJump`, `notEnergyDifference`, `notAcousticImpedance`, `notQuantumFluctuation`, `energyGapLegal`
- **质量**: `refl`×10；⚠️ 7 postulate

## `src/Sovereign/RootMath/Gaussian.agda`

- **module**: `Sovereign.RootMath.Gaussian`
- **行数**: 189（代码 90 / 注释 56）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | Sovereign.RootMath.Gaussian
  - 高斯整数 Z[i] — 毕达哥拉斯复数线的判别式 −4 分支 (0 postulate)
  - 数学背景:
  - i² = −1, 元素 (a,b) = a+bi, a,b ∈ ℤ — 方格点阵 (90°)
  - 乘法: (a,b)(c,d) = (ac−bd, ad+bc)
  - 范数: N = a²+b² (毕达哥拉斯二次型 — 勾股数 = 范数平方)
  - 共轭: conj(a,b) = (a,−b)
  - 单位群 = {±1, ±i} ≅ C₄ (生成元 i)
  - 与 Eisenstein (Z[ω], 判别式 −3, 60°) 的对称:
  - Z[i] 判别式 −4 (90° 格) ↔ Z[ω] 判别式 −3 (60° 格)
  - 范数 a²+b² ↔ a²−ab+b² — 毕达哥拉斯二次型的两个分歧
  - 核心定理 (勾股三元组生成):
  - (m+ni)² = (m²−n²) + 2mn·i ⟹ 三元组 (m²−n², 2mn, m²+n²) 满足
  - (m²−n²)² + (2mn)² = (m²+n²)² — 全部本原勾股数的 Gauss 生成
  - 本模块: 具体对 (m,n) 的 ℤ 字面 refl (有限穷举风格);
  - 符号化范数乘性 N(xy)=N(x)N(y) 与 Brahmagupta–Fibonacci 恒等式的
- **导入 (4)**: `Data.Integer`, `Data.Nat`, `Data.Product`, `Relation.Binary.PropositionalEquality`
- **data 类型**: `Gaussian`
- **顶层签名 (42)**: `z0`, `z1`, `-ᵢ_`, `conjᵢ`, `normᵢ`, `0ᵢ`, `1ᵢ`, `iᵤ`, `i-square`, `i-fourth`, `unit1`, `uniti`, `unitm1`, `unitmi`, `unit-pow`, `unit-pow-0`, `unit-pow-1`, `unit-pow-2`, `unit-pow-3`, `unit-pow-4`, `unit-norm-1`, `unit-norm-i`, `unit-norm-m1`, `unit-norm-mi`, `unit-inv-i`, `unit-inv-mi`, `unit-inv-m1`, `pyth-3-4-5-square`, `pyth-3-4-5-norm`, `pyth-3-4-5-identity`, `pyth-5-12-13-square`, `pyth-5-12-13-identity`, `pyth-15-8-17-square`, `pyth-15-8-17-identity`, `pyth-21-20-29-square`, `pyth-21-20-29-identity`, `twelve-as-2mn`, `norm-mul-sample`, `norm-mul-factor`, `norm-mul-sample-eq`, `bf-identity-sample`, `conj-mul-sample`
- **质量**: `refl`×31；无 postulate / 无 hole

## `src/Sovereign/RootMath/LengthLattice.agda`

- **module**: `Sovereign.RootMath.LengthLattice`
- **行数**: 143（代码 79 / 注释 41）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | Sovereign.RootMath.LengthLattice
  - 根数学：十二律长度格点序列的完整定义
  - 基准：黄钟归一化长度格点 81（无量纲整数）
  - 损益操作唯一合法的长度比例演化方式
- **导入 (8)**: `Data.Nat`, `Data.Integer`, `Data.Product`, `Data.Vec`, `Data.Fin`, `Relation.Binary.PropositionalEquality`, `Sovereign.Coupling.LossGain`, `Sovereign.Base.Lü`
- **data 类型**: `LossGainStep`
- **顶层签名 (12)**: `lengthLattice`, `lüToLength`, `huangzhongBase`, `reachableFromBase`, `SOVEREIGN_LCM`, `POW3¹¹`, `POW2¹⁶`, `lcmRemainders`, `zhongluRemainderIs65536`, `huangzhongRemainderIs177147`, `zhonglvReset`, `zhonglvCorrect`
- **质量**: `refl`×5；无 postulate / 无 hole
