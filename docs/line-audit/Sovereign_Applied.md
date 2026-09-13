# 目录 `src/Sovereign/Applied/` 逐模块审计记录

共 40 个模块。


## `src/Sovereign/Applied/AcousticsDiscrete.agda`

- **module**: `Sovereign.Applied.AcousticsDiscrete`
- **行数**: 57（代码 16 / 注释 29）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | Sovereign.Applied.AcousticsDiscrete
  - 应用层：离散声学 (十二律与频率比)
  - 层级: 应用数学 (电性文明投影)
  - GF(3) 合法身份: 模 3 整数算术
  - 定理清单:
  - 1. 十二律: 12 个音律
  - 2. 频率比 3¹¹/2¹⁶: 数值验证 (仲吕闭合)
  - 0 postulate, 全部构造性证明, 穷举法优先
- **导入 (2)**: `Data.Nat`, `Relation.Binary.PropositionalEquality`
- **顶层签名 (6)**: `twelve-lu-count`, `twelve-lu-as-a4`, `san-shiyi`, `er-shiliu`, `zhonglv-product`, `huangzhong-length`
- **质量**: `refl`×7；无 postulate / 无 hole

## `src/Sovereign/Applied/AlgebraChainDeep.agda`

- **module**: `Sovereign.Applied.AlgebraChainDeep`
- **行数**: 331（代码 180 / 注释 106）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | Sovereign.Applied.AlgebraChainDeep
  - 代数链深层证明: GF(9) 域性质强化 + 4320 组合闭包
  - B16: GF(9) 乘法逆元完整验证 (8 case: x·x⁻¹=1)
  - B17: GF(9) Frobenius σ(xy)=σ(x)σ(y) 完整验证
  - B18: GF(9) 范数乘性 N(xy)=N(x)N(y) 完整 81-case
  - B25: 4320 = 729×6-54 组合闭包
  - B26: 4320 = 2×12×36×5 分解
  - 0 postulate — 全部构造性证明, 穷举法优先
- **导入 (5)**: `Data.Nat`, `Data.Product`, `Relation.Binary.PropositionalEquality`, `Sovereign.Base.Trit`, `Sovereign.Algebra.GF9`
- **record 类型**: `AlgebraChainDeepTheorems`
- **顶层签名 (26)**: `gf9-inv-complete`, `inv-s1`, `inv-s2`, `inv-sα`, `inv-s2α`, `inv-s1α`, `inv-s12α`, `inv-s21α`, `inv-s22α`, `gf9-inv-involutive`, `gf9-frobenius-mult`, `frobenius-α²-witness`, `norm-multiplicative`, `norm-nonzero-s1`, `norm-nonzero-s2`, `norm-nonzero-sα`, `norm-nonzero-s2α`, `norm-nonzero-s1α`, `norm-nonzero-s12α`, `norm-nonzero-s21α`, `norm-nonzero-s22α`, `verify-4374∸54`, `verify-54`, `verify-729`, `combo-4320-prime`, `algebra-chain-deep-complete`
- **质量**: `refl`×113；无 postulate / 无 hole

## `src/Sovereign/Applied/BiologyDiscrete.agda`

- **module**: `Sovereign.Applied.BiologyDiscrete`
- **行数**: 35（代码 18 / 注释 8）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | BiologyDiscrete — MSC 92 数理生物 · GF(3) 三态基因型
  - 连续统 TypeError: ContinuousPopulationWithoutFiniteFitness
  - 离散替代: Trit 基因型 + 离散复制动力学
- **导入 (2)**: `Relation.Binary.PropositionalEquality`, `Sovereign.Base.Trit`
- **顶层签名 (6)**: `Genotype`, `Population`, `fitness`, `extinction-equilibrium`, `neutral-equilibrium`, `selective-equilibrium`
- **质量**: `refl`×4；无 postulate / 无 hole

## `src/Sovereign/Applied/BlackHoleWhiteHole.agda`

- **module**: `Sovereign.Applied.BlackHoleWhiteHole`
- **行数**: 80（代码 26 / 注释 39）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | Sovereign.Applied.BlackHoleWhiteHole
  - C42: 离散黑洞/白洞 — CRT 对偶 + 信息守恒
  - 核心命题:
  - 1. CRT 对偶: crtReconstruct(crtProject x) ≡ x % M (引用 crtTheorem)
  - 黑洞=投影 (crtProject), 白洞=重构 (crtReconstruct)
  - 2. 信息守恒: 4320D 全息容量不变 (引用 yao-4320)
  - 0 postulate, 穷举法优先
- **导入 (5)**: `Data.Nat`, `Data.Product`, `Relation.Binary.PropositionalEquality`, `Sovereign.Format.CRT`, `Sovereign.Structology.BurnsideT6`
- **顶层签名 (8)**: `bh-wh-duality`, `bh-wh-reverse`, `bh-channel-capacity`, `info-conservation-4320`, `info-bare-space`, `info-gauge-order`, `info-physical`, `info-capacity-exact`
- **质量**: `refl`×5；无 postulate / 无 hole

## `src/Sovereign/Applied/CelestialExtended.agda`

- **module**: `Sovereign.Applied.CelestialExtended`
- **行数**: 65（代码 20 / 注释 31）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | Sovereign.Applied.CelestialExtended
  - C56: 离散天体力学 — LCM 共振周期 + 极向/环向同步
  - 核心命题:
  - 1. LCM 共振: SOVEREIGN_LCM = 3^11 × 2^16 = 11609505792 (refl)
  - 2. 极向/环向同步归零: 缠绕数 144/46 的公倍周期
  - 0 postulate, 穷举法优先
- **导入 (3)**: `Data.Nat`, `Relation.Binary.PropositionalEquality`, `Sovereign.Base.Invariants`
- **顶层签名 (7)**: `resonance-lcm`, `resonance-pow3`, `resonance-pow2`, `resonance-product`, `celestial-polar`, `celestial-toroidal`, `celestial-sync-period`
- **质量**: `refl`×8；无 postulate / 无 hole

## `src/Sovereign/Applied/CelestialGeneticsControl.agda`

- **module**: `Sovereign.Applied.CelestialGeneticsControl`
- **行数**: 195（代码 86 / 注释 73）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | Sovereign.Applied.CelestialGeneticsControl
  - 浅层应用定理：天体力学 (Christoffel 螺旋/轨道共振)、
  - 遗传学扩展 (密码子手征)、控制论 (状态转移周期/可控性)
  - 全部构造性证明，0 postulate，穷举法优先。
- **导入 (8)**: `Data.Nat`, `Data.Fin`, `Data.Product`, `Relation.Binary.PropositionalEquality`, `Sovereign.Base.Trit`, `Sovereign.RootMath.DigitalRoot`, `Sovereign.Format.CRTMeasurement`, `Sovereign.Analysis.FiniteDynamics`
- **顶层签名 (26)**: `spiral-elements`, `spiral-closure`, `spiral-phase-period6`, `christoffel-period-is-6`, `resonance-6-4`, `resonance-verify`, `resonance-div6`, `resonance-div4`, `resonance-minimal-evidence`, `resonance-is-12-lu`, `zero-codon-fixed`, `nonzero-codon-moves`, `nonzero-codon-moves-2`, `chiral-annihilation`, `codon-char3`, `codon-space-27`, `state-3-periodic`, `state-3-id-periodic`, `cyclic3`, `cyclic3-period3`, `a4-order`, `a4-order-12`, `a4-order-decomposition`, `a4-order-christoffel`, `a4-order-resonance`, `a4-covers-electric`
- **质量**: `refl`×39；无 postulate / 无 hole

## `src/Sovereign/Applied/CircuitExtended.agda`

- **module**: `Sovereign.Applied.CircuitExtended`
- **行数**: 343（代码 194 / 注释 91）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | Sovereign.Applied.CircuitExtended
  - 应用层：扩展电路理论 (三值逻辑门)
  - 层级: 应用数学 (电性文明投影)
  - GF(3) 合法身份: 模 3 整数算术 + 格运算
  - 定理清单:
  - 1. AND = min (_∧T_), OR = max (_∨T_): 引用 DomainProofs
  - 2. NOT: T₀→T₂, T₁→T₁, T₂→T₀ (3 case 穷举)
  - 3. De Morgan 定律: NOT(x∧y)≡NOT(x)∨NOT(y), NOT(x∨y)≡NOT(x)∧NOT(y)
  - 4. AND = GLB, OR = LUB: 格论刻画 (≤T 全序)
  - 5. 常数生成: T₀(AND零元), T₂(OR零元), T₁(门构造)
  - 6. 函数完备性: {∧T, ∨T, NOT, ⊕, 常数} 生成全部 3³=27 个单变量函数
  - 选择子分解: f(x) = ∨_a (Δ_a(x) ∧ f(a))
  - 0 postulate, 全部构造性证明, 穷举法优先
- **导入 (5)**: `Data.Nat`, `Data.Product`, `Relation.Binary.PropositionalEquality`, `Sovereign.Base.Trit`, `Sovereign.Applied.DomainProofs`
- **顶层签名 (43)**: `and-gate-example`, `or-gate-example`, `and-zero`, `or-identity`, `not-gate`, `not-T₀`, `not-T₁`, `not-T₂`, `not-involution`, `de-morgan-∧`, `de-morgan-∨`, `and-lowerˡ`, `and-lowerʳ`, `and-glb`, `or-upperˡ`, `or-upperʳ`, `or-lub`, `or-annihilator`, `const-T₁-via-gates`, `sel₀`, `sel₁`, `sel₂`, `sel₀-gate`, `sel₁-gate`, `sel₂-gate`, `Δ₀`, `Δ₁`, `Δ₂`, `Δ₀-select`, `Δ₀-reject₁`, `Δ₀-reject₂`, `Δ₁-reject₀`, `Δ₁-select`, `Δ₁-reject₂`, `Δ₂-reject₀`, `Δ₂-reject₁`, `Δ₂-select`, `TruthTable`, `tt-fun`, `decompose`, `completeness`, `function-count`, `function-count-27`
- **质量**: `refl`×68；无 postulate / 无 hole

## `src/Sovereign/Applied/CommunicationDiscrete.agda`

- **module**: `Sovereign.Applied.CommunicationDiscrete`
- **行数**: 57（代码 17 / 注释 29）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | Sovereign.Applied.CommunicationDiscrete
  - 应用层：离散通信理论 (信道容量与 CRT 编码)
  - 层级: 应用数学 (全息文明投影)
  - GF(3) 合法身份: 模 3 整数算术 + CRT 正交分解
  - 定理清单:
  - 1. 信道容量 = 4320: 引用 yao-4320
  - 2. CRT 编码无损: 引用 crtTheorem
  - 0 postulate, 全部构造性证明, 穷举法优先
- **导入 (5)**: `Data.Nat`, `Data.Product`, `Relation.Binary.PropositionalEquality`, `Sovereign.Structology.BurnsideT6`, `Sovereign.Format.CRT`
- **顶层签名 (4)**: `channel-capacity-4320`, `channel-capacity-arithmetic`, `crt-lossless`, `crt-modulus`
- **质量**: `refl`×3；无 postulate / 无 hole

## `src/Sovereign/Applied/CondensedMatter.agda`

- **module**: `Sovereign.Applied.CondensedMatter`
- **行数**: 66（代码 22 / 注释 29）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | Sovereign.Applied.CondensedMatter
  - 应用层：离散凝聚态物理 (T⁶ 晶格与 A₄ 对称性)
  - 层级: 应用数学 (磁性文明投影)
  - GF(3) 合法身份: 模 3 整数算术 + 群论
  - 定理清单:
  - 1. 晶格 = 729: T⁶ = GF(3)⁶ 的格点数
  - 2. 对称 = A₄: 正四面体旋转群 12 阶
  - 0 postulate, 全部构造性证明, 穷举法优先
- **导入 (4)**: `Data.Nat`, `Data.Fin`, `Relation.Binary.PropositionalEquality`, `Sovereign.Structology.A4Group`
- **顶层签名 (8)**: `lattice-dim`, `lattice-base`, `lattice-cardinality`, `lattice-expanded`, `a4-order`, `a4-identity-exists`, `a4-rotations-exist`, `a4-flips-exist`
- **质量**: `refl`×4；无 postulate / 无 hole

## `src/Sovereign/Applied/ControlTheory.agda`

- **module**: `Sovereign.Applied.ControlTheory`
- **行数**: 124（代码 49 / 注释 52）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | Sovereign.Applied.ControlTheory
  - C37: 离散控制论 — 有限状态系统的稳定性与周期上界
  - 核心命题:
  - 1. 稳定性: 有限状态机轨道最终周期 (引用 orbit-eventually-periodic)
  - 2. 周期上界: 轨道周期 ≤ N (引用 orbit-period-bound)
  - 0 postulate, 穷举法优先
- **导入 (5)**: `Data.Nat`, `Data.Fin`, `Data.Product`, `Relation.Binary.PropositionalEquality`, `Sovereign.Analysis.FiniteDynamics`
- **顶层签名 (15)**: `control-stability`, `control-3-state-stable`, `control-9-state-stable`, `control-period-bound`, `control-3-bound`, `control-9-bound`, `control-discrete-topological`, `cycle3`, `identity-period-1`, `cycle-3-step-1`, `cycle-3-step-2`, `cycle-3-period`, `cycle-3-period-6`, `const-3-converges-1`, `const-3-converges-2`
- **质量**: `refl`×9；无 postulate / 无 hole

## `src/Sovereign/Applied/CosmologyDiscrete.agda`

- **module**: `Sovereign.Applied.CosmologyDiscrete`
- **行数**: 119（代码 40 / 注释 55）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | Sovereign.Applied.CosmologyDiscrete
  - C41: 离散宇宙学 — 4320 容量 + 729 格点
  - 核心命题:
  - 1. 4320 全息容量: 729×6 - 54 = 4320 (引用 yao-4320)
  - 2. 729 格点: T⁶ = GF(3)⁶ 的基数 (引用 T6 相关)
  - 0 postulate, 穷举法优先
- **导入 (3)**: `Data.Nat`, `Relation.Binary.PropositionalEquality`, `Sovereign.Structology.BurnsideT6`
- **顶层签名 (16)**: `cosmology-capacity-4320`, `cosmology-factor-4320`, `cosmology-both-paths`, `cosmology-t6-cardinality`, `cosmology-729-product`, `cosmology-orbit-closure`, `cosmology-gauge-order`, `cosmology-bare-space`, `cosmology-physical-dof`, `factor-4320-2`, `factor-4320-3`, `factor-4320-5`, `factor-4320-full`, `factor-4320-prime`, `factor-2pow5`, `factor-3pow3`
- **质量**: `refl`×14；无 postulate / 无 hole

## `src/Sovereign/Applied/CrossDomainTheorems.agda`

- **module**: `Sovereign.Applied.CrossDomainTheorems`
- **行数**: 314（代码 114 / 注释 139）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | Sovereign.Applied.CrossDomainTheorems
  - 跨域定理 D61–D80: 代数链定理在不同领域的投影
  - 核心原则: 跨域定理 = 已有定理的领域语义包装。
  - 每个定理引用代数链中已证定理 + 简单 refl/引用，0 postulate。
  - 领域映射:
  - D61: CRT ↔ 信号处理       D71: σ ↔ 量子
  - D62: Burnside ↔ 热力学    D72: 14轨道 ↔ 数据库
  - D63: Δ³≡0 ↔ 微分方程     D73: 五行 ↔ 历法
  - D64: 鸽巢 ↔ 可计算性     D74: 十二律 ↔ 声学
  - D65: A₄ ↔ 粒子物理       D75: I_h ↔ 材料
  - D66: Christoffel ↔ 天体   D76: T⁶ ↔ 宇宙膜
  - D67: GF(3)³ ↔ 遗传       D77: 不动点 ↔ 经济
  - D68: 4320 ↔ 信息论       D78: 轨道 ↔ 神经
  - D69: 6624 ↔ 宇宙学       D79: 对称 ↔ 美学
  - D70: CRT ↔ 密码学        D80: 格点 ↔ 建筑
- **导入 (15)**: `Data.Nat`, `Data.Product`, `Data.Fin`, `Relation.Binary.PropositionalEquality`, `Sovereign.Format.CRT`, `Sovereign.Structology.BurnsideT6`, `Sovereign.Algebra.DiscreteDE`, `Sovereign.Algebra.ProjectionDifferential`, `Sovereign.Analysis.FiniteDynamics`, `Sovereign.Structology.A4Representations`, `Sovereign.RootMath.DigitalRoot`, `Sovereign.Algebra.GF9`, `Sovereign.Structology.Winding`, `Sovereign.MetaStructure.WuXing`, `Sovereign.Base.Trit`
- **顶层签名 (26)**: `d61-crt-signal-processing`, `d62-burnside-thermodynamics`, `d63-pde-truncation`, `d64-pigeonhole-computability`, `d65-a4-particle-physics`, `d66-christoffel-celestial`, `d67-gf3-genetics`, `d67-codon-space`, `d68-4320-information`, `d69-6624-cosmology`, `d69-winding-values`, `d70-crt-cryptography`, `d71-sigma-quantum`, `d72-orbits-database`, `d72-normal-forms`, `d73-generate5-id`, `d73-jiazi-60`, `d74-twelve-pitches`, `d74-pythagorean-ratio`, `d75-ih-materials`, `d76-t6-brane`, `d77-fixedpoint-economics`, `d78-orbit-neuroscience`, `d79-symmetry-aesthetics`, `d80-lattice-architecture`, `cross-domain-theorems-complete`
- **质量**: `refl`×20；无 postulate / 无 hole

## `src/Sovereign/Applied/DeepAlgebraProofs.agda`

- **module**: `Sovereign.Applied.DeepAlgebraProofs`
- **行数**: 186（代码 82 / 注释 87）
- **OPTIONS**: `--rewriting --cubical --guardedness`
- **头部注释（数学背景）**:
  - | Sovereign.Applied.DeepAlgebraProofs
  - 深层代数证明索引 (B16–B22)
  - 本模块是证明索引：汇总并重导出已在各源模块中完成的深层证明。
  - 所有定理均为构造性证明，0 postulate。
  - 任务清单:
  - B16: GF(9) 乘法逆元完整验证        ← GF9.inv-correct
  - B17: Frobenius σ(xy)=σ(x)σ(y)     ← GF9.lemma-frobenius-multiplicative
  - B18: 范数乘性 N(xy)=N(x)N(y)       ← NormDiscrete.galoisNorm-multiplicative
  - B19: A₄ 群结合律                   ← A4Group.assoc
  - B20: A₄ 共轭类分类 (1+4+4+3=12)    ← A4Representations.classSizeSum
  - B21: 2A₄ 群公理                    ← BinaryTetrahedral.bt-id-left/right/inv
  - B22: 2A₄ 非平凡性                  ← BinaryTetrahedral.bt-i-sq/bt-neg1≠id
- **导入 (7)**: `Sovereign.Algebra.GF9`, `Sovereign.Algebra.GF9`, `Sovereign.Analysis.NormDiscrete`, `Sovereign.Structology.A4Group`, `Sovereign.Structology.A4Representations`, `Sovereign.Structology.BinaryTetrahedral`, `Sovereign.Structology.BinaryTetrahedral`
- **质量**: `refl`×8；无 postulate / 无 hole

## `src/Sovereign/Applied/DeepStructureProofs.agda`

- **module**: `Sovereign.Applied.DeepStructureProofs`
- **行数**: 412（代码 189 / 注释 180）
- **OPTIONS**: `--rewriting --cubical --guardedness`
- **头部注释（数学背景）**:
  - | Sovereign.Applied.DeepStructureProofs
  - 深层结构证明索引 (B23–B35)
  - 本模块是证明索引：汇总并重导出已在各源模块中完成的深层证明，
  - 补充缺失的简单证明 (B34 五行 C₅ 闭合, B35 纳音 60=5×12)。
  - 所有定理均为构造性证明，0 postulate，穷举法优先。
  - 任务清单:
  - B23: CRT 重构唯一性              ← Format.CRT.crtTheorem
  - B24: Burnside 轨道大小 Σ=729     ← Structology.BurnsideT6.orbit-sizes-sum-729
  - B25: 4320 = 729×6−54            ← Structology.BurnsideT6.yao-4320
  - B26: 4320 = 2×12×36×5           ← Structology.HoloInformation
  - B27: 特征标正交性 (5 定理)       ← Structology.A4Representations
  - B28: 分支规则 l=0..5            ← Algebra.BranchingRules.decomp-l0..l5
  - B29: 分支规则周期 6             ← Algebra.BranchingRules (递推 + pairing-general)
  - B30: 域扩张塔 GF(3)⊂GF(9)⊂GF(729) ← Algebra.FieldExtensionTower
  - B31: Christoffel 6步闭合         ← RootMath.DigitalRoot.christosPeriod6
  - B32: 6624 = 144×46              ← 本地 refl (多源交叉验证)
  - B33: LCM(2¹⁶,3¹¹) = 11609505792 ← Base.Invariants.SOVEREIGN_LCM
  - B34: 五行 C₅ generate⁵=id       ← 本地穷举 (新增)
- **导入 (14)**: `Data.Nat`, `Data.Product`, `Relation.Binary.PropositionalEquality`, `Sovereign.Format.CRT`, `Sovereign.Structology.BurnsideT6`, `Sovereign.Structology.BurnsideT6`, `Sovereign.Structology.HoloInformation`, `Sovereign.Structology.A4Representations`, `Sovereign.Algebra.BranchingRules`, `Sovereign.Algebra.BranchingRules`, `Sovereign.Algebra.FieldExtensionTower`, `Sovereign.RootMath.DigitalRoot`, `Sovereign.Base.Invariants`, `Sovereign.MetaStructure.WuXing`
- **顶层签名 (14)**: `b23-crt-modulus-value`, `b32-full-tour`, `b32-holo-pi-num`, `b32-holo-pi-den`, `b33-lcm-value`, `b33-lcm-factors`, `generate⁵`, `b34-generate5-id`, `b34-generate1-not-id`, `b34-generate-images`, `b35-nayin-60`, `b35-jiazi-lcm`, `b35-60-decompositions`, `deep-structure-proofs-complete`
- **质量**: `refl`×41；无 postulate / 无 hole

## `src/Sovereign/Applied/DomainProofs.agda`

- **module**: `Sovereign.Applied.DomainProofs`
- **行数**: 256（代码 172 / 注释 50）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | Sovereign.Applied.DomainProofs
  - 浅层应用定理：KCL 电流守恒、密码子空间、Trit 全序与格运算
  - 全部构造性证明，0 postulate，穷举法优先。
- **导入 (4)**: `Data.Nat`, `Data.Sum`, `Relation.Binary.PropositionalEquality`, `Sovereign.Base.Trit`
- **data 类型**: `_`
- **顶层签名 (24)**: `kcl-example`, `kcl-general`, `kcl-complementary`, `codon-space-size`, `codon-27`, `codon-div3`, `codon-dim`, `trit-total`, `≤T-refl`, `≤T-trans`, `≤T-antisym`, `_∨T_`, `_∧T_`, `∨T-idem`, `∧T-idem`, `∨T-comm`, `∧T-comm`, `∨T-absorb`, `∧T-absorb`, `∧T-distrib-∨T`, `∨T-distrib-∧T`, `codon-orbit-div`, `codon-fixed-points`, `codon-char3`
- **质量**: `refl`×107；无 postulate / 无 hole

## `src/Sovereign/Applied/EMDiscrete.agda`

- **module**: `Sovereign.Applied.EMDiscrete`
- **行数**: 86（代码 32 / 注释 38）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | Sovereign.Applied.EMDiscrete
  - C45: 离散电磁学 — Maxwell 截断 + 干涉
  - 核心命题:
  - 1. Maxwell 截断: Δ³≡0 (三阶差分幂零 → 高阶 Maxwell 方程截断)
  - 2. 干涉: T₁⊕T₂≡T₀ (GF(3) 相消干涉)
  - 0 postulate, 穷举法优先
- **导入 (5)**: `Data.Nat`, `Data.Product`, `Relation.Binary.PropositionalEquality`, `Sovereign.Base.Trit`, `Sovereign.Algebra.ProjectionDifferential`
- **顶层签名 (9)**: `maxwell-cutoff`, `maxwell-second-order`, `maxwell-fourth-order`, `interference-destructive`, `interference-constructive`, `interference-wraparound`, `interference-vacuum`, `interference-char3`, `interference-conjugate`
- **质量**: `refl`×13；无 postulate / 无 hole

## `src/Sovereign/Applied/EconomicsDiscrete.agda`

- **module**: `Sovereign.Applied.EconomicsDiscrete`
- **行数**: 59（代码 21 / 注释 27）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | Sovereign.Applied.EconomicsDiscrete
  - C57: 离散经济学 — 有限资源分配均衡 + 729 格点鸽巢原理
  - 核心命题:
  - 1. 均衡存在: 729 格点上的确定性资源分配 → 轨道最终周期 (鸽巢原理)
  - 2. 分配归零: GF(3) 特征 3 → 三重分配回归均衡
  - 0 postulate, 穷举法优先
- **导入 (6)**: `Data.Nat`, `Data.Fin`, `Data.Product`, `Relation.Binary.PropositionalEquality`, `Sovereign.Base.Trit`, `Sovereign.Analysis.FiniteDynamics`
- **顶层签名 (4)**: `equilibrium-729`, `allocation-pigeonhole`, `triple-allocation-zero`, `supply-demand-cancel`
- **质量**: `refl`×5；无 postulate / 无 hole

## `src/Sovereign/Applied/FluidDiscrete.agda`

- **module**: `Sovereign.Applied.FluidDiscrete`
- **行数**: 59（代码 21 / 注释 27）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | Sovereign.Applied.FluidDiscrete
  - 应用层：离散流体力学 (GF(3) 周期性与无耗散)
  - 层级: 应用数学 (电性文明投影)
  - GF(3) 合法身份: 模 3 整数算术
  - 定理清单:
  - 1. GF(3) 周期 3: ∀x, (x⊕x)⊕x≡T₀ (特征 3)
  - 2. 无耗散: char 3 中能量不衰减
  - 0 postulate, 全部构造性证明, 穷举法优先
- **导入 (3)**: `Data.Nat`, `Relation.Binary.PropositionalEquality`, `Sovereign.Base.Trit`
- **顶层签名 (4)**: `char3-period`, `char3-period-alt`, `no-dissipation-inverse`, `no-dissipation-reversible`
- **质量**: `refl`×13；无 postulate / 无 hole

## `src/Sovereign/Applied/GRDiscrete.agda`

- **module**: `Sovereign.Applied.GRDiscrete`
- **行数**: 60（代码 21 / 注释 28）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | Sovereign.Applied.GRDiscrete
  - 应用层：离散广义相对论 (Christoffel 联络与曲率截断)
  - 层级: 应用数学 (中性文明投影)
  - GF(3) 合法身份: 模 3 整数算术 + 差分算子
  - 定理清单:
  - 1. Christoffel 联络周期 6: 引用 christosPeriod6
  - 2. 曲率截断: Δ³≡0 (三阶幂零 → 离散曲率自动截断)
  - 0 postulate, 全部构造性证明, 穷举法优先
- **导入 (6)**: `Data.Nat`, `Data.Product`, `Relation.Binary.PropositionalEquality`, `Sovereign.Base.Trit`, `Sovereign.RootMath.DigitalRoot`, `Sovereign.Algebra.ProjectionDifferential`
- **顶层签名 (4)**: `christoffel-period6`, `christoffel-closure-value`, `curvature-truncation`, `flat-connection`
- **质量**: `refl`×3；无 postulate / 无 hole

## `src/Sovereign/Applied/GameTheory.agda`

- **module**: `Sovereign.Applied.GameTheory`
- **行数**: 118（代码 42 / 注释 58）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | Sovereign.Applied.GameTheory
  - C38: 离散博弈论 — 鸽巢原理 → 周期轨道存在 + GF(3) 三值策略
  - 核心命题:
  - 1. 周期轨道存在: 有限策略空间 → 鸽巢原理 → 轨道最终周期
  - 2. 不动点实例: 恒等函数/常数函数有不动点 (具体构造)
  - 3. GF(3) 三值策略: T₀(合作)/T₁(中立)/T₂(对抗), 3 case 穷举
  - 重要区分:
  - 纯策略 Nash 均衡 (不动点) 不一定存在!
  - 例: f(0)=1, f(1)=0 在 Fin 2 上没有不动点。
  - 经典 Nash 存在性定理需要混合策略 (概率分布) + Brouwer 不动点定理。
  - 离散博弈论的正确替代: 所有有限博弈都有周期轨道 (鸽巢原理, 构造性)。
  - 0 postulate, 穷举法优先
- **导入 (6)**: `Data.Nat`, `Data.Fin`, `Data.Product`, `Relation.Binary.PropositionalEquality`, `Sovereign.Base.Trit`, `Sovereign.Analysis.FiniteDynamics`
- **顶层签名 (18)**: `orbit-periodic-exists`, `orbit-periodic-3-strategy`, `orbit-pigeonhole`, `nash-identity`, `nash-constant`, `nash-constant-general`, `Strategy`, `strategy-annihilation`, `strategy-sum-coop-coop`, `strategy-sum-coop-neut`, `strategy-sum-coop-agg`, `strategy-sum-neut-coop`, `strategy-sum-neut-neut`, `strategy-sum-neut-agg`, `strategy-sum-agg-coop`, `strategy-sum-agg-neut`, `strategy-sum-agg-agg`, `strategy-char3`
- **质量**: `refl`×18；无 postulate / 无 hole

## `src/Sovereign/Applied/GeneticsExtended.agda`

- **module**: `Sovereign.Applied.GeneticsExtended`
- **行数**: 78（代码 27 / 注释 35）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | Sovereign.Applied.GeneticsExtended
  - C39: 扩展遗传学 — 密码子 27 + GF(3) 特征 3
  - 核心命题:
  - 1. 密码子空间: 3³ = 27 (三个碱基位, 每位 3 态)
  - 2. 特征 3: ∀ x, (x⊕x)⊕x = T₀ (GF(3) 代数基本性质)
  - 0 postulate, 穷举法优先
- **导入 (4)**: `Data.Nat`, `Data.Product`, `Relation.Binary.PropositionalEquality`, `Sovereign.Base.Trit`
- **顶层签名 (11)**: `Codon`, `codon-space-size`, `codon-count-product`, `codon-completeness`, `char3-triple-zero`, `char3-T₀`, `char3-T₁`, `char3-T₂`, `double-T₀`, `double-T₁`, `double-T₂`
- **质量**: `refl`×13；无 postulate / 无 hole

## `src/Sovereign/Applied/HomologyHarmonic.agda`

- **module**: `Sovereign.Applied.HomologyHarmonic`
- **行数**: 811（代码 455 / 注释 273）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | Sovereign.Applied.HomologyHarmonic
  - 同调代数与调和分析的浅层定理
  - MSC 55: 同调截断 — Δ³≡0 意味着高阶同调消失
  - MSC 42: 调和分析 — Euler 示性数、Plancherel 定理、卷积定理
  - 核心结果:
  - §1. 同调截断: Δ³≡0 → H^n = 0 for n ≥ 3
  - §2. Euler 示性数: χ(T⁶) = Σ(-1)^k C(6,k) = 0
  - §3. Plancherel 定理 (A₄): 特征标正交性 → 完备正交基
  - §4. 卷积定理 (Z/3Z): sum3(f*g) = sum3(f) · sum3(g) [DC 分量]
  - §5. Leibniz 规则: Δ(f*g) = f*(Δg) = (Δf)*g [非 DC 分量]
  - 依赖:
  - ProjectionDifferential: Δ³≡0, GF3Func, sum3, shift
  - DiscreteDE: Δⁿ, Δⁿ≥3≡0, Δ≡0→const
  - A4Representations: A4Irrep, ConjugacyClass, dim
  - Eisenstein: Z[ω] 算术
  - 0 postulate — 全部构造性证明, 穷举法优先
- **导入 (10)**: `Data.Nat`, `Data.Product`, `Relation.Binary.PropositionalEquality`, `Sovereign.Base.Trit`, `Sovereign.Algebra.ProjectionDifferential`, `Sovereign.Algebra.DiscreteDE`, `Sovereign.Structology.A4Representations`, `Sovereign.RootMath.Eisenstein`, `Data.Integer`, `Sovereign.Geometry.ProjectiveCore`
- **顶层签名 (59)**: `homology-vanishes-3`, `homology-vanishes-higher`, `homology-vanishes-4`, `image-Δ³-trivial`, `ker-Δ-constants`, `chain-complex-d₀∘d₁`, `const-in-kernel`, `β₀`, `β₁`, `β₂`, `β₃`, `β₄`, `β₅`, `β₆`, `euler-even-sum`, `euler-odd-sum`, `euler-characteristic`, `binom-6-2`, `binom-6-3`, `betti-total`, `dim-sq-sum`, `charVal`, `classSizeE`, `12ᵉ`, `charInner`, `plancherel-V3`, `plancherel-V1`, `plancherel-V3-V1`, `plancherel-dim-formula`, `class-size-sum`, `_⊕f_`, `_⊗f_`, `conv`, `δ`, `zero-func`, `triple-≡`, `⊕-interchange`, `sum3-⊕f`, `sum3-⊗f`, `sum3-shift`, `sum3-shift²`, `conv-δ-left`, `conv-zero-left`, `conv-decomp`, `augment-conv`, `augment-δ`, `augment-zero`, `⊕-rotate₃`, `⊕-swap-inner`, `negate-≡-⊗₂`, `negate-⊗-scalar`, `Δ-linear`, `Δ-scalar-comm`, `Δ-shift-comm`, `shift-conv-left`, `conv-comm`, `Δ-conv-leibniz`, `Δ²-conv-leibniz`, `Δ³-conv-zero`
- **质量**: `refl`×33；无 postulate / 无 hole

## `src/Sovereign/Applied/ImageProcessing.agda`

- **module**: `Sovereign.Applied.ImageProcessing`
- **行数**: 65（代码 21 / 注释 32）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | Sovereign.Applied.ImageProcessing
  - C59: 离散图像处理 — Δ 边缘检测 + Δ² 平滑
  - 核心命题:
  - 1. Δ 边缘检测: Δf 是一阶差分, 非零处即"边缘"
  - 2. Δ² 平滑: Δ²f 是常数 (GF(3) 上), 二阶差分无局部结构
  - 0 postulate, 穷举法优先
- **导入 (5)**: `Data.Nat`, `Data.Product`, `Relation.Binary.PropositionalEquality`, `Sovereign.Base.Trit`, `Sovereign.Algebra.ProjectionDifferential`
- **顶层签名 (5)**: `edge-const-zero`, `edge-step-example`, `smooth-Δ²-const`, `smooth-Δ³-zero`, `smooth-const-invariant`
- **质量**: `refl`×2；无 postulate / 无 hole

## `src/Sovereign/Applied/InformationFrame.agda`

- **module**: `Sovereign.Applied.InformationFrame`
- **行数**: 79（代码 26 / 注释 36）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | Sovereign.Applied.InformationFrame
  - C43: 信息帧 — 格点快照 + 帧容量
  - 核心命题:
  - 1. 帧=格点快照: 729 = 3⁶ (T⁶ 全部格点的一帧)
  - 2. 帧容量=4320: 每帧承载 4320D 独立信息
  - 0 postulate, 穷举法优先
- **导入 (3)**: `Data.Nat`, `Relation.Binary.PropositionalEquality`, `Sovereign.Structology.BurnsideT6`
- **顶层签名 (10)**: `frame-size`, `frame-size-product`, `frame-completeness`, `frame-resolution-per-dim`, `frame-dimensions`, `frame-capacity-4320`, `frame-capacity-decomposition`, `frame-bare-space`, `frame-gauge-redundancy`, `frame-efficiency-loss`
- **质量**: `refl`×10；无 postulate / 无 hole

## `src/Sovereign/Applied/LeibnizGF9.agda`

- **module**: `Sovereign.Applied.LeibnizGF9`
- **行数**: 459（代码 337 / 注释 84）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | Sovereign.Applied.LeibnizGF9
  - Leibniz 规则从 GF(3) 3 点函数推广到 GF(9) 9 点函数
  - 核心结果:
  - §1. GF(9) 加法逆元的代数性质
  - §2. Z/9Z 循环索引 (9 点)
  - §3. GF(9) 9 点函数空间: shift9, Δ9
  - §4. Δ9 的线性与移位交换性
  - §5. 循环卷积 (移位叠加定义)
  - §6. Leibniz 规则: Δ9(f*g) = f*(Δ9 g)
  - 推广路径:
  - GF(3) 3 点: HomologyHarmonic §5 — Δ(f*g) = f*(Δg)
  - GF(9) 9 点: 本文件 — Δ9(f*g) = f*(Δ9 g)
  - 证明结构完全相同: 分解 → 线性 → 标量交换 → 移位交换 → 重组
  - 依赖:
  - GF9: GF(3²) 域运算, 域公理
  - Trit: GF(3) 底层类型, negate 代数性质
- **导入 (4)**: `Data.Product`, `Relation.Binary.PropositionalEquality`, `Sovereign.Base.Trit`, `Sovereign.Algebra.GF9`
- **data 类型**: `Fin9`
- **顶层签名 (28)**: `gf9-neg`, `gf9-neg-⊕`, `gf9-neg²`, `⊕-interchange`, `+gf9-interchange`, `suc9`, `GF9Func`, `shift9`, `gf9-neg-func`, `Δ9`, `shift9⁰`, `shift9¹`, `shift9²`, `shift9³`, `shift9⁴`, `shift9⁵`, `shift9⁶`, `shift9⁷`, `shift9⁸`, `Δ9-linear`, `Δ9-scalar`, `Δ9-shift-comm`, `Δ9-peel`, `conv9`, `zero9-func`, `δ9`, `Δ9-conv9-leibniz`, `Δ9²-conv9-leibniz`
- **质量**: `refl`×6；无 postulate / 无 hole

## `src/Sovereign/Applied/LeibnizT6.agda`

- **module**: `Sovereign.Applied.LeibnizT6`
- **行数**: 441（代码 230 / 注释 170）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | Sovereign.Applied.LeibnizT6
  - 多维 Leibniz 规则 — T⁶ = GF(3)⁶ 上的方向差分代数
  - 核心结果:
  - §3. 线性性: Δ₁, Δ₂ 保持逐点加法
  - §4. 标量交换: Δ₁, Δ₂ 与标量乘法交换
  - §5. 方向交换律: Δ₁Δ₂ = Δ₂Δ₁ (多维 Leibniz 的核心)
  - §6. 幂零性: Δ₁³ = Δ₂³ = 0 (char 3)
  - §7. 混合差分推论
  - 数学意义:
  - T⁶ = (Z/3Z)⁶ 上的 6 个方向差分算子 Δ₀,...,Δ₅ 满足:
  - (1) 每个 Δᵢ 是 GF(3)-线性的
  - (2) ΔᵢΔⱼ = ΔⱼΔᵢ (方向交换 / 可积条件)
  - (3) Δᵢ³ = 0 (char 3 幂零截断)
  - 这三条性质完全刻画了 T⁶ 上的离散微分结构。
  - 本模块在 2D 切片 (Z/3Z)² 上证明这些性质。
  - 6D 推广是直接的: 每个方向独立继承 1D 结构,
  - 方向交换律对任意方向对成立 (因为不同方向的移位作用于不同坐标)。
- **导入 (6)**: `Data.Product`, `Relation.Binary.PropositionalEquality`, `Sovereign.Base.Trit`, `Sovereign.Algebra.ProjectionDifferential`, `Sovereign.Algebra.DiscreteDE`, `Sovereign.Geometry.ProjectiveCore`
- **顶层签名 (27)**: `triple-≡`, `_⊗f_`, `_⊗2D_`, `negate-≡-⊗₂`, `⊕-interchange`, `neg-⊕-neg`, `negate-⊗-scalar`, `Δ-linear-1D`, `Δ₁-linear`, `transpose-⊕2D`, `Δ₂-linear`, `Δ-scalar-1D`, `Δ₁-scalar`, `transpose-⊗2D`, `Δ₂-scalar`, `Δ₂D-comm-component`, `Δ₁Δ₂-comm`, `Δ₁-nilpotent`, `Δ₂-nilpotent`, `Δ₁-kills-const`, `Δ₂-kills-const`, `Δ₁²Δ₂-comm`, `Δ₁Δ₂²-comm`, `Δ₁²Δ₂²-comm`, `Δ₁³Δ₂≡0`, `Δ₂³Δ₁≡0`, `Δ₁³Δ₂²≡0`
- **质量**: `refl`×11；无 postulate / 无 hole

## `src/Sovereign/Applied/LinguisticsDiscrete.agda`

- **module**: `Sovereign.Applied.LinguisticsDiscrete`
- **行数**: 67（代码 21 / 注释 34）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | Sovereign.Applied.LinguisticsDiscrete
  - C58: 离散语言学 — GF(3) 三值语法 + Δ³≡0 递归截断
  - 核心命题:
  - 1. 三值语法: 句法成分取 GF(3) 三态 (主语/谓语/宾语)
  - 2. Δ³≡0 递归截断: 嵌套深度最多 3 层 (幂零性)
  - 0 postulate, 穷举法优先
- **导入 (5)**: `Data.Nat`, `Data.Product`, `Relation.Binary.PropositionalEquality`, `Sovereign.Base.Trit`, `Sovereign.Algebra.ProjectionDifferential`
- **顶层签名 (5)**: `SyntaxRole`, `argument-closure`, `syntax-cycle`, `recursion-truncation`, `recursion-2-collapse`
- **质量**: `refl`×5；无 postulate / 无 hole

## `src/Sovereign/Applied/LogicCompleteness2Var.agda`

- **module**: `Sovereign.Applied.LogicCompleteness2Var`
- **行数**: 392（代码 228 / 注释 102）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | Sovereign.Applied.LogicCompleteness2Var
  - 应用层：双变量三值逻辑函数完备性
  - 层级: 应用数学 (电性文明投影)
  - GF(3) 合法身份: 模 3 整数算术 + 格运算
  - 推广 CircuitExtended.agda §5-§6 的单变量完备性 (3³=27 函数)
  - 到双变量完备性 (3⁹=19683 函数)。
  - 定理清单:
  - 1. 双变量选择子: Δ_{a,b}(x,y) = Δ_a(x) ∧T Δ_b(y)
  - 2. 选择子正交性: Δ_{a,b}(x,y) = T₂ 当 (x,y)=(a,b), T₀ 否则
  - 3. 分解定理: f(x,y) = ∨_{a,b} (Δ_{a,b}(x,y) ∧T f(a,b))
  - 4. 完备性: ∀ tt x y → decompose2 tt (x,y) ≡ eval2 tt (x,y)
  - 5. 计数: 3⁹ = 19683 个双变量函数
  - 0 postulate, 全部构造性证明, 穷举法优先
- **导入 (6)**: `Data.Nat`, `Data.Product`, `Relation.Binary.PropositionalEquality`, `Sovereign.Base.Trit`, `Sovereign.Applied.DomainProofs`, `Sovereign.Applied.CircuitExtended`
- **顶层签名 (44)**: `TruthTable2`, `eval2`, `Δ₀₀`, `Δ₀₁`, `Δ₀₂`, `Δ₁₀`, `Δ₁₁`, `Δ₁₂`, `Δ₂₀`, `Δ₂₁`, `Δ₂₂`, `Δ₀₀-select`, `Δ₀₀-reject₀₁`, `Δ₀₀-reject₀₂`, `Δ₀₀-reject₁₀`, `Δ₀₀-reject₁₁`, `Δ₀₀-reject₁₂`, `Δ₀₀-reject₂₀`, `Δ₀₀-reject₂₁`, `Δ₀₀-reject₂₂`, `Δ₁₁-select`, `Δ₁₁-reject₀₀`, `Δ₁₁-reject₂₂`, `Δ₂₂-select`, `Δ₂₂-reject₀₀`, `Δ₂₂-reject₁₁`, `decompose2`, `completeness2`, `function-count-2var`, `function-count-19683`, `input-pairs`, `input-pairs-9`, `const-T₁-tt`, `const-T₁-correct`, `proj₁-tt`, `proj₁-correct`, `proj₂-tt`, `proj₂-correct`, `xor-tt`, `xor-correct`, `mul-tt`, `mul-correct`, `decompose2-gf3`, `completeness2-gf3`
- **质量**: `refl`×117；无 postulate / 无 hole

## `src/Sovereign/Applied/MachineLearning.agda`

- **module**: `Sovereign.Applied.MachineLearning`
- **行数**: 114（代码 44 / 注释 48）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | Sovereign.Applied.MachineLearning
  - C60: 离散机器学习 — 三值网络收敛 + 4320 容量上限
  - 核心命题:
  - 1. 三值网络收敛: 有限状态 → 轨道最终周期 (鸽巢原理)
  - 2. 4320 容量上限: 独立信息维度 = 729×6 - 54 = 4320
  - 0 postulate, 穷举法优先
- **导入 (7)**: `Data.Nat`, `Data.Fin`, `Data.Product`, `Relation.Binary.PropositionalEquality`, `Sovereign.Base.Trit`, `Sovereign.Analysis.FiniteDynamics`, `Sovereign.Structology.HoloInformation`
- **顶层签名 (14)**: `network-converges`, `network-729-converges`, `capacity-4320`, `total-yao-space`, `gauge-order`, `gf3-successor`, `const-network-converges`, `const-network-from-1`, `const-network-from-2`, `identity-network-period`, `gf3-network-step-1`, `gf3-network-step-2`, `gf3-network-period-3`, `gf3-network-period-6`
- **质量**: `refl`×11；无 postulate / 无 hole

## `src/Sovereign/Applied/MetaTheorems.agda`

- **module**: `Sovereign.Applied.MetaTheorems`
- **行数**: 226（代码 60 / 注释 128）
- **OPTIONS**: `--rewriting --guardedness`
- **导入 (9)**: `Data.Nat`, `Data.Product`, `Data.Empty`, `Relation.Binary.PropositionalEquality`, `Relation.Nullary`, `Sovereign.Base.Trit`, `Sovereign.Completeness.CompletenessTheorem`, `Sovereign.Algebra.ProjectionDifferential`, `Sovereign.Algebra.GF9`
- **顶层签名 (14)**: `E82-P0-complete`, `E83-4320-triple-closure`, `E84-char3`, `E84-nontrivial`, `E85-Δ³-nilpotent`, `E86-frobenius-involution`, `E87-gf9star-cyclic`, `E88-4320-finite`, `E90-no-infinitesimal`, `E96-gauge-intrinsic`, `E97-vortex-root`, `E98-octave-entanglement`, `E99-holographic-closure`, `E100-大衍已立`
- **质量**: `refl`×29；无 postulate / 无 hole

## `src/Sovereign/Applied/MolecularSymmetry.agda`

- **module**: `Sovereign.Applied.MolecularSymmetry`
- **行数**: 58（代码 16 / 注释 30）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | Sovereign.Applied.MolecularSymmetry
  - 应用层：离散分子对称性 (C₆₀ 振动模与对称群)
  - 层级: 应用数学 (磁性文明投影)
  - GF(3) 合法身份: 模 3 整数算术 + 拓扑不变量
  - 定理清单:
  - 1. C₆₀ 振动模 = 46: 环向缠绕数
  - 2. 对称群阶: I_h 群与 A₄ 的关系
  - 0 postulate, 全部构造性证明, 穷举法优先
- **导入 (3)**: `Data.Nat`, `Relation.Binary.PropositionalEquality`, `Sovereign.Structology.Winding`
- **顶层签名 (5)**: `c60-vibrational-modes`, `polar-winding-144`, `ih-order`, `ih-a4-index`, `polar-as-a4-squared`
- **质量**: `refl`×4；无 postulate / 无 hole

## `src/Sovereign/Applied/NeuroscienceDiscrete.agda`

- **module**: `Sovereign.Applied.NeuroscienceDiscrete`
- **行数**: 171（代码 89 / 注释 58）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | Sovereign.Applied.NeuroscienceDiscrete
  - C40: 离散神经科学 — 轨道即记忆 + 三值神经元
  - 核心命题:
  - 1. 轨道=记忆: 有限神经网络的轨道最终周期 → 记忆是吸引子
  - 2. 三值神经元: GF(3) 状态 (抑制/静息/激发)
  - 0 postulate, 穷举法优先
- **导入 (6)**: `Data.Nat`, `Data.Fin`, `Data.Product`, `Relation.Binary.PropositionalEquality`, `Sovereign.Base.Trit`, `Sovereign.Analysis.FiniteDynamics`
- **顶层签名 (16)**: `memory-is-attractor`, `memory-3-neuron`, `memory-9-neuron`, `NeuronState`, `synapse-inhibit-excite`, `synapse-rest-excite-cancel`, `synapse-excite-excite`, `neuron-char3`, `neuron-conjugate`, `fixed-point-memory`, `fixed-point-period-1`, `orbit-collapse-3`, `neuron-char3-T₁-chain`, `neuron-char3-T₂-chain`, `synapse-full-chain`, `neuron-inverse-involution-chain`
- **质量**: `refl`×10；无 postulate / 无 hole

## `src/Sovereign/Applied/NumberOptComp.agda`

- **module**: `Sovereign.Applied.NumberOptComp`
- **行数**: 115（代码 40 / 注释 56）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | Sovereign.Applied.NumberOptComp
  - 浅层应用定理：数论、组合优化、可计算性
  - 数论: 2^n mod 9 完整周期表、CRT 互素条件
  - 组合优化: 穷举搜索终止 (鸽巢原理)、Burnside 轨道压缩
  - 可计算性: 有限即停机 (周期上界)、Δ³≡0 递归截断
  - 全部构造性证明，0 postulate，穷举法优先。
- **导入 (10)**: `Data.Nat`, `Data.Fin`, `Data.Product`, `Relation.Binary.PropositionalEquality`, `Relation.Nullary`, `Sovereign.Base.Trit`, `Sovereign.Algebra.DigitalRootCycle`, `Sovereign.Analysis.FiniteDynamics`, `Sovereign.Algebra.DiscreteDE`, `Sovereign.Algebra.ProjectionDifferential`
- **顶层签名 (8)**: `pow2-cycle`, `pow2-cycle-closes`, `coprime-2-3`, `pow2-16≢pow3-11`, `search-terminates`, `burnside-compression`, `halt-bound`, `recursion-truncated`
- **质量**: `refl`×8；无 postulate / 无 hole

## `src/Sovereign/Applied/OpticsDiscrete.agda`

- **module**: `Sovereign.Applied.OpticsDiscrete`
- **行数**: 141（代码 66 / 注释 52）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | Sovereign.Applied.OpticsDiscrete
  - 应用层：离散光学 (GF(3) 干涉与频率比)
  - 层级: 应用数学 (电性文明投影)
  - GF(3) 合法身份: 模 3 整数算术
  - 定理清单:
  - 1. 相消干涉: T₁⊕T₂≡T₀ (互补相位归零)
  - 2. 相长干涉: T₁⊕T₁≡T₂ (同相叠加)
  - 3. 频率比: 3¹¹ 和 2¹⁶ 的数值验证
  - 0 postulate, 全部构造性证明, 穷举法优先
- **导入 (3)**: `Data.Nat`, `Relation.Binary.PropositionalEquality`, `Sovereign.Base.Trit`
- **顶层签名 (14)**: `destructive-interference`, `destructive-interference-sym`, `constructive-interference`, `constructive-T₂`, `pow3-11`, `pow2-16`, `sovereign-lcm-value`, `triple-interference`, `quad-interference`, `double-destructive`, `interference-assoc-comm`, `triple-T₂`, `sovereign-lcm-chain`, `phase-conjugate-chain`
- **质量**: `refl`×8；无 postulate / 无 hole

## `src/Sovereign/Applied/OptimizationDiscrete.agda`

- **module**: `Sovereign.Applied.OptimizationDiscrete`
- **行数**: 10（代码 6 / 注释 1）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - MSC 90 · GF(3)有限全搜索
- **导入 (2)**: `Relation.Binary.PropositionalEquality`, `Sovereign.Base.Trit`
- **顶层签名 (1)**: `gradient-zero`
- **质量**: `refl`×2；无 postulate / 无 hole

## `src/Sovereign/Applied/ParticlePhysics.agda`

- **module**: `Sovereign.Applied.ParticlePhysics`
- **行数**: 60（代码 19 / 注释 29）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | Sovereign.Applied.ParticlePhysics
  - 应用层：离散粒子物理 (A₄ 表示与粒子代)
  - 层级: 应用数学 (中性文明投影)
  - GF(3) 合法身份: 模 3 整数算术 + 表示论
  - 定理清单:
  - 1. 4 不可约表示 = 粒子代: A₄ 有 4 个 irrep {3,1,1′,1″}
  - 2. 色荷 = GF(3): 3 种色荷对应 GF(3) 的 3 个元素
  - 0 postulate, 全部构造性证明, 穷举法优先
- **导入 (5)**: `Data.Nat`, `Data.Product`, `Relation.Binary.PropositionalEquality`, `Sovereign.Base.Trit`, `Sovereign.Structology.A4Representations`
- **顶层签名 (5)**: `irrep-count`, `dim-sq-sum-equals-order`, `irrep-dims`, `color-charge-count`, `color-confinement`
- **质量**: `refl`×8；无 postulate / 无 hole

## `src/Sovereign/Applied/PleiadianCosmology.agda`

- **module**: `Sovereign.Applied.PleiadianCosmology`
- **行数**: 76（代码 25 / 注释 35）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | Sovereign.Applied.PleiadianCosmology
  - C44: 昴宿星宇宙学 — 全息=CRT + 12 涡旋根
  - 核心命题:
  - 1. 全息=CRT: 全息投影等价于 CRT 正交分解 (引用 crtTheorem)
  - 2. 12 涡旋根: 12 ≡ 12 (涡旋数学的独立根)
  - 0 postulate, 穷举法优先
- **导入 (4)**: `Data.Nat`, `Data.Product`, `Relation.Binary.PropositionalEquality`, `Sovereign.Format.CRT`
- **顶层签名 (9)**: `holographic-crt`, `holographic-encoding`, `holographic-capacity`, `vortex-root-12`, `vortex-octave-3-6`, `vortex-octave-6-12`, `vortex-chain-3-12`, `vortex-12-factors`, `vortex-polar-144`
- **质量**: `refl`×10；无 postulate / 无 hole

## `src/Sovereign/Applied/ProbThermo.agda`

- **module**: `Sovereign.Applied.ProbThermo`
- **行数**: 177（代码 77 / 注释 70）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | Sovereign.Applied.ProbThermo
  - 应用层： 概率论与热力学的浅层定理 (GF(3) / Burnside 版)
  - 层级: 应用数学 (电性/磁性文明投影)
  - GF(3) 合法身份: 模 3 整数算术 + 轨道计数
  - 定理清单:
  - 1. 概率加法公式 (GF(3) 离散版)
  - 2. 全概率公式 (Burnside 轨道分解)
  - 3. 熵的离散界 (log₃(14) 的整数夹逼)
  - 4. 配分函数 (14 轨道等权和)
  - 5. 可逆性 (GF(3) 加法逆元 → 热力学第二定律不适用)
  - 0 postulate, 全部构造性证明, 穷举法优先
- **导入 (4)**: `Data.Nat`, `Data.Product`, `Relation.Binary.PropositionalEquality`, `Sovereign.Base.Trit`
- **顶层签名 (18)**: `prob-addition-example`, `prob-addition-general`, `total-probability`, `burnside-total-prob`, `entropy-lower`, `entropy-upper`, `entropy-bounds`, `partition-function`, `partition-is-14`, `partition-eq-orbits`, `gf3-reversible`, `gf3-reversible-comm`, `total-prob-chain`, `burnside-chain`, `gf3-reversible-chain`, `prob-normalization-chain`, `partition-algebra-chain`, `entropy-algebra-chain`
- **质量**: `refl`×16；无 postulate / 无 hole

## `src/Sovereign/Applied/SignalProcessing.agda`

- **module**: `Sovereign.Applied.SignalProcessing`
- **行数**: 106（代码 35 / 注释 49）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | Sovereign.Applied.SignalProcessing
  - C36: 离散信号处理 — CRT 无损采样 + 729 格点完备性
  - 核心命题:
  - 1. CRT 无损: crtReconstruct(crtProject x) ≡ x % M (引用 crtTheorem)
  - 2. 采样即全部: 729 = 3⁶ 格点 = T⁶ 全部信息 (refl)
  - 0 postulate, 穷举法优先
- **导入 (4)**: `Data.Nat`, `Data.Product`, `Relation.Binary.PropositionalEquality`, `Sovereign.Format.CRT`
- **顶层签名 (14)**: `signal-crt-lossless`, `signal-modulus`, `signal-domain-positive`, `t6-sample-count`, `sampling-completeness`, `per-dimension-states`, `dimension-product`, `crt-orthogonal-decomposition`, `crt-example-0`, `crt-example-1`, `crt-example-2`, `crt-example-728`, `crt-example-729`, `crt-reconstruct-zero`
- **质量**: `refl`×14；无 postulate / 无 hole

## `src/Sovereign/Applied/ThermoExtended.agda`

- **module**: `Sovereign.Applied.ThermoExtended`
- **行数**: 51（代码 14 / 注释 26）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | Sovereign.Applied.ThermoExtended
  - 应用层：扩展热力学 (配分函数与轨道分解)
  - 层级: 应用数学 (磁性文明投影)
  - GF(3) 合法身份: 模 3 整数算术 + 轨道计数
  - 定理清单:
  - 1. 配分函数 = 14: Burnside 轨道数
  - 2. 轨道分解: 1×27 + 13×54 ≡ 729
  - 0 postulate, 全部构造性证明, 穷举法优先
- **导入 (2)**: `Data.Nat`, `Relation.Binary.PropositionalEquality`
- **顶层签名 (5)**: `partition-function-14`, `partition-decomposition`, `orbit-decomposition-729`, `lattice-total`, `free-orbit-size`
- **质量**: `refl`×6；无 postulate / 无 hole
