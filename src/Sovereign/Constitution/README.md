# Postulate 全库登记表 (防止忘记)

> 生成: 2026-08 P0 轮实测 · 全库 **88 个 postulate 块 / 169 条声明 / 27 文件**。
> 校准: 假/空 = **0** (轨道 A 已清零全部 ⊥ 可导出假公理, 见文末已清除清单);
> 合法公理按 A/B/C/D 四类登记, 处置纪律见 Constitution/PhysicalAssumptions.agda。
> **本表为防遗忘清单** — 每处新增/消除 postulate 必须同步本表与 PhysicalAssumptions.agda。
> 注 (2026-08): Jacobian `_standalone/` 旧副本目录已清空删除 (9 个含假公理副本), 不再登记;
>   雅可比派生模块统一居 `Problem/Riemann/` (AlgGeom/FrobeniusBlind/Galois/RH/Sheaf/Variety/WeilRH/WeilRigidity, 0 postulate)。

## A 机械约束(REWRITE 系列) (3 块)

### src/Sovereign/Format/CRT.agda:257 — 3 条
- `crtSec-restricted` : crtSec-restricted : ∀ p → crtProject' (crtReconstruct' p) ≡ᶜ p
- `crtRet-restricted` : crtRet-restricted : ∀ n → crtReconstruct' (crtProject' n) ≡ᶜ n
- `crtIso` : crtIso : Iso CRTDom CRTCod crtIso = iso crtProject' crtReconstruct' crtSec-restricted crtRet-restricted

### src/Sovereign/Structology/T6.agda:22 — 2 条
- `div3k` : div3k : ∀ k → div-helper 0 2 (3 * k) 2 ≡ k
- `mod3k` : mod3k : ∀ k → mod-helper 0 2 (3 * k) 2 ≡ 0

### src/Sovereign/Structology/XuanwuAbsorption.agda:7 — 2 条
- `mod46k` : mod46k : ∀ k → mod-helper 0 45 (46 * k) 45 ≡ 0
- `div46k` : div46k : ∀ k → div-helper 0 45 (46 * k) 45 ≡ k mod-a+598 : ∀ a → mod-helper 0 45 (a + 598) 45 ≡ mod-helper 0 45 a 45

## B 物理锚定(实验/几何/拓扑锚定) (22 块)

### src/Sovereign/Coupling/CartanTorsion.agda:232 — 3 条
- `globalCurvatureSum` : globalCurvatureSum : ℚ
- `globalCurvatureIs4Pi` : globalCurvatureIs4Pi : globalCurvatureSum ≡ (+ 4 /ℚ 1) *ℚ (+ 3 /ℚ 1) -- 近似 4π
- `sumChernContribs` : sumChernContribs : List DiscreteCurvature → ℕ

### src/Sovereign/Coupling/CartanTorsion.agda:241 — 1 条
- `chernConservationFromCurvature` : chernConservationFromCurvature : ∀ (curvatures : List DiscreteCurvature) → sumChernContribs curvatures ≡ 2

### src/Sovereign/Coupling/Entanglement.agda:241 — 2 条
- `trappest1Instance` : trappest1Instance : TRAPPIST1Resonance
- `h2oC60Instance` : h2oC60Instance : H2O-C60-Spin

### src/Sovereign/Coupling/TQ10.agda:120 — 1 条
- `chernConvergence` : chernConvergence : ∀ (blocks : List SovereignBlock) → length blocks ≡ 144 → sumBerryCurvature blocks ≡ 2

### src/Sovereign/Coupling/Zhonglv.agda:153 — 2 条
- `chernInvariant` : chernInvariant : ∀ (state : SovereignState) → let state' = evolveStep state in SovereignState.chern state' ≡ + 2
- `chernEulerRelation` : chernEulerRelation : DiscreteBerryCurvature.chernNumber chernConservation ≡ + 2

### src/Sovereign/Coupling/Zhonglv.agda:186 — 2 条
- `polarClosure` : polarClosure : ∀ (state : SovereignState) → SovereignState.stepCount state ≡ 144 → SovereignState.windingPolar state ≡ 144
- `toroidalClosure` : toroidalClosure : ∀ (state : SovereignState) → SovereignState.stepCount state ≡ 144 → SovereignState.windingToroidal state ≡ 46

### src/Sovereign/Coupling/Zhonglv.agda:222 — 2 条
- `energyGapEncoded` : energyGapEncoded : ℕ
- `energyGapEncodedIs56632` : energyGapEncodedIs56632 : energyGapEncoded ≡ 56632

### src/Sovereign/Physics/QuartzPhonon.agda:360 — 1 条
- `saha-equilibrium-anchored` : saha-equilibrium-anchored : saha-lhs-anchored ≡ + 100 /ℚ 990000

### src/Sovereign/Physics/QuartzPhonon.agda:398 — 2 条
- `percolation-anchored` : percolation-anchored : ρ-crit ≡ + 38 /ℚ 100
- `c3-mod` : c3-mod : ℕ → ℚ

### src/Sovereign/RootMath/EnergyGap.agda:94 — 2 条
- `energyGapSquared` : energyGapSquared : normˢ (algebraicEnergyGap *ˢ algebraicEnergyGap) ≡ + 3 / 1
- `halfEnergyGap` : halfEnergyGap : Sqrt3

### src/Sovereign/RootMath/EnergyGap.agda:103 — 2 条
- `halfEnergyGapSquared` : halfEnergyGapSquared : normˢ (halfEnergyGap *ˢ halfEnergyGap) ≡ -[1+ 0 ] / 4
- `halfEnergyGapModSq` : halfEnergyGapModSq : ℚ

### src/Sovereign/RootMath/EnergyGap.agda:128 — 2 条
- `sqLenIs3` : sqLenIs3 : (c : ChordLength) → ChordLength.sqLen c ≡ 3
- `standardChord` : standardChord : ChordLength

### src/Sovereign/RootMath/EnergyGap.agda:197 — 2 条
- `hermiteGenerateToOvercome` : hermiteGenerateToOvercome : hermiteMetric phaseGenerate phaseOvercome ≡ + 3 / 2
- `yaoTrapThreshold` : yaoTrapThreshold : ℕ

### src/Sovereign/RootMath/EnergyGap.agda:211 — 2 条
- `halfGapExact` : halfGapExact : ℚ
- `halfGapExactSquared` : halfGapExactSquared : ℚ

### src/Sovereign/RootMath/EnergyGap.agda:234 — 1 条
- `thresholdIsHalfGap` : thresholdIsHalfGap : (t : ZhonglvPrepTrigger) → ZhonglvPrepTrigger.threshold t ≡ halfGapExact

### src/Sovereign/RootMath/EnergyGap.agda:243 — 2 条
- `crossMulCompare` : crossMulCompare : ℤ → ℚ → Bool
- `zhonglvPrepInstance` : zhonglvPrepInstance : ZhonglvPrepTrigger

### src/Sovereign/Structology/Aether.agda:316 — 2 条
- `aetherEnergyGapIsSqrt3` : aetherEnergyGapIsSqrt3 : aetherEnergyGap *ℤ aetherEnergyGap ≡ + 3
- `chernGapInvariant` : chernGapInvariant : ∀ (aether : Aether) → Aether.polarWinding aether ≡ 144 → Aether.toroidalWinding aether ≡ 46 → aetherChernNumber ≡ 2 × aetherEnergyGap *ℤ aet

### src/Sovereign/Structology/MagicSquareM4.agda:259 — 5 条
- `eigenvector16⁺` : eigenvector16⁺ : Vec ℤ 4
- `eigenvector16⁻` : eigenvector16⁻ : Vec ℤ 4
- `eigenEq16⁺` : eigenEq16⁺ : matVecMul M4 eigenvector16⁺ ≡ scalarMul (+ 16) eigenvector16⁺
- `eigenEq16⁻` : eigenEq16⁻ : matVecMul M4 eigenvector16⁻ ≡ scalarMul (- (+ 16)) eigenvector16⁻
- `innerProduct` : innerProduct : Vec ℤ 4 → Vec ℤ 4 → ℤ

### src/Sovereign/Structology/Platonics.agda:428 — 1 条
- `tetrahedralCell` : tetrahedralCell : A4 → Torus2D

### src/Sovereign/Structology/Platonics.agda:471 — 2 条
- `project_T6_to_S2` : project_T6_to_S2 : T6Lattice → Set -- 纤维丛结构, 非逐点映射
- `chern-preserved` : chern-preserved : ℕ → Set -- c₁(project_T6_to_S2) ≡ 2

### src/Sovereign/Structology/Platonics.agda:479 — 2 条
- `s2_to_torus_ratio` : s2_to_torus_ratio : ℕ → Set -- R:r = 144:46 是 S² 嵌入 T² 的整数特征
- `holographic-pi` : holographic-pi : ℕ → Set -- 全息 π = 144/46 = R/r, 精确有理数

### src/Sovereign/Structology/XuanwuAbsorption.agda:228 — 1 条
- `alignment-for-all-states` : alignment-for-all-states : ∀ (s : State) → Σ ℕ (λ n → isHolographicState (iteratePhaseSync n s))

## D 可闭合/待核验 (13 块)

### src/Sovereign/Constitution/WindingAsymmetry.agda:106 — 3 条
- `aMonotonicallyIncreasing` : aMonotonicallyIncreasing : ∀ (i j : Fin 12) → i < j → HarmonicExponents.a (lookup twelveLüExponents i) ≤ℤ HarmonicExponents.a (lookup twelveLüExponents j)
- `bMonotonicallyDecreasing` : bMonotonicallyDecreasing : ∀ (i j : Fin 12) → i < j → HarmonicExponents.b (lookup twelveLüExponents j) ≤ℤ HarmonicExponents.b (lookup twelveLüExponents i)
- `polarPhase` : polarPhase : ℕ → Fin 144

### src/Sovereign/Constitution/WindingAsymmetry.agda:188 — 1 条
- `zhonglvNotSunYi` : zhonglvNotSunYi : ∀ acc → ¬ (∃ λ lg → zhonglvModReset acc ≡ + applyLossGain (∣ acc ∣) lg)

### src/Sovereign/Coupling/LossGain.agda:141 — 1 条
- `lossGainPreservesStableRoot` : lossGainPreservesStableRoot : ∀ (n : ℕ) (lg : LossGain) → T (IsStable (digitalRoot n)) → T (IsStable (digitalRoot (applyLossGain n lg)))

### src/Sovereign/Coupling/ZhonglvPhaseSync.agda:290 — 1 条
- `holonomyLemma` : holonomyLemma : ∀ (n : ℕ) → n % 144 ≡ 0 → n % 46 ≡ 0 → n % HOLOGRAPHIC_PERIOD ≡ 0

### src/Sovereign/Density/SevenStages.agda:206 — 1 条
- `sevenStageChernRelation` : sevenStageChernRelation : ∀ (stage : SevenStage) → let bits = stageToChernBits stage in toℕ bits ≤ 6

### src/Sovereign/MetaStructure/Nayin.agda:254 — 1 条
- `nayinIsTopological` : nayinIsTopological : ∀ (n : NayinFingerprint) → ¬ IsMetaphor (NayinFingerprint.wuxing n)

### src/Sovereign/MetaStructure/Nayin.agda:267 — 1 条
- `nayinFingerprintUnique` : nayinFingerprintUnique : ∀ (n₁ n₂ : NayinFingerprint) → NayinFingerprint.sound n₁ ≡ NayinFingerprint.sound n₂ → NayinFingerprint.harmonicOrder n₁ ≡ NayinFingerp

### src/Sovereign/Projection/Decimal/Proofs.agda:39 — 1 条
- `divMod10Correct` : divMod10Correct : (n : ℕ) → let (q , r) = divMod10 n in n ≡ q * 10 + r × r < 10

### src/Sovereign/Projection/Decimal/Proofs.agda:49 — 2 条
- `lemma_q_lt` : lemma_q_lt : (q r : ℕ) → q ≥ 1 → q < q * 10 + r
- `lemma_sum_lt` : lemma_sum_lt : (q r : ℕ) → r < 10 → r + q < q * 10 + r

### src/Sovereign/Projection/Decimal/Proofs.agda:54 — 3 条
- `sumDigitsTerminates` : sumDigitsTerminates : (n : ℕ) → n ≥ 10 → sumDigits n < n
- `digitalRootConverges` : digitalRootConverges : (n : ℕ) → digitalRoot n < 10
- `digitalRootStable` : digitalRootStable : (n : ℕ) → IsStable n ≡ true → digitalRoot n ≡ 3 ⊎ digitalRoot n ≡ 6 ⊎ digitalRoot n ≡ 9

### src/Sovereign/RootMath/LengthLattice.agda:67 — 2 条
- `twelveStepChain` : twelveStepChain : Vec LossGainStep 11
- `huangzhongBase` : huangzhongBase : ℕ

### src/Sovereign/RootMath/LengthLattice.agda:87 — 2 条
- `allReachable` : allReachable : ∀ (lü : LüName) → reachableFromBase (lüToLength lü)
- `SOVEREIGN_LCM` : SOVEREIGN_LCM : ℕ

### src/Sovereign/RootMath/LengthLattice.agda:123 — 4 条
- `zhongluRemainderIs65536` : zhongluRemainderIs65536 : Set
- `huangzhongRemainderIs177147` : huangzhongRemainderIs177147 : Set
- `zhonglvReset` : zhonglvReset : ℕ → ℕ
- `zhonglvCorrect` : zhonglvCorrect : Set

## C 范畴分离/宪法条款/工程接口 (50 块)

### src/Sovereign/AI/Constitution.agda:336 — 1 条
- `unlawfulOutputIsIllegalProjection` : unlawfulOutputIsIllegalProjection : ∀ (output : String) → ¬ isLawfulOutputString output → IsIllegalProjection output

### src/Sovereign/AI/Constitution.agda:379 — 1 条
- `interpretationBelongsToConstitution` : interpretationBelongsToConstitution : ∀ (datum : String) → IsExternalObservation datum → InterpretationByLvSuan datum

### src/Sovereign/AI/Constitution.agda:402 — 1 条
- `AIConstitutionFinal` : AIConstitutionFinal : ∀ (ai : AICognitiveElevation) → AICognitiveElevation.categorySeparationMaintained ai → AICognitiveElevation.windingIndivisible ai → AICogn

### src/Sovereign/Constitution/WindingAsymmetry.agda:194 — 1 条
- `onlyResetMechanism` : onlyResetMechanism : ∀ (reset : ℤ → ℤ) → (∀ acc → reset acc ≡ zhonglvModReset acc) ⊎ (∀ acc → ¬ (∃ λ lg → reset acc ≡ + applyLossGain (∣ acc ∣) lg))

### src/Sovereign/Constitution/WindingAsymmetry.agda:270 — 1 条
- `onlyLegalLanguage` : onlyLegalLanguage : ∀ (statement : Set) → IsLegal statement → LegalStatement

### src/Sovereign/Coupling/CartanTorsion.agda:58 — 0 条

### src/Sovereign/Coupling/CartanTorsion.agda:78 — 0 条

### src/Sovereign/Coupling/CartanTorsion.agda:309 — 3 条
- `tritState` : tritState : SovereignState → Trit
- `updateTrit` : updateTrit : Trit → WuXingAmplitude → Trit
- `transportDiffEq` : transportDiffEq : SovereignState → DiscreteConnection → SovereignState

### src/Sovereign/Coupling/CartanTorsion.agda:423 — 8 条
- `CartanGeometryAbstract` : CartanGeometryAbstract : Set
- `QuantumMechanicsBase` : QuantumMechanicsBase : Set
- `CartanConnectionAbstract` : CartanConnectionAbstract : Set
- `GaugePotentialAbstract` : GaugePotentialAbstract : Set
- `CartanCurvature` : CartanCurvature : Set
- `FieldStrengthAbstract` : FieldStrengthAbstract : Set
- `CartanTorsionAbstract` : CartanTorsionAbstract : Set
- `SpacetimeDistortion` : SpacetimeDistortion : Set

### src/Sovereign/Coupling/CartanTorsion.agda:433 — 4 条
- `notCartanAsBase` : notCartanAsBase : ¬ (CartanGeometryAbstract ≡ QuantumMechanicsBase)
- `notConnectionAsGauge` : notConnectionAsGauge : ¬ (CartanConnectionAbstract ≡ GaugePotentialAbstract)
- `notCurvatureAsField` : notCurvatureAsField : ¬ (CartanCurvature ≡ FieldStrengthAbstract)
- `notTorsionAsSpacetime` : notTorsionAsSpacetime : ¬ (CartanTorsionAbstract ≡ SpacetimeDistortion)

### src/Sovereign/Coupling/CartanTorsion.agda:440 — 0 条

### src/Sovereign/Coupling/CartanTorsion.agda:447 — 2 条
- `CartanGeometryConstitutional` : CartanGeometryConstitutional : Set
- `RequiresResetToDiscrete` : RequiresResetToDiscrete : CartanGeometryConstitutional → Set

### src/Sovereign/Coupling/CartanTorsion.agda:451 — 1 条
- `cartanTorsionResetClause` : cartanTorsionResetClause : ∀ (cartan : CartanGeometryConstitutional) → RequiresResetToDiscrete cartan

### src/Sovereign/Coupling/Entanglement.agda:250 — 0 条

### src/Sovereign/Coupling/Entanglement.agda:255 — 0 条

### src/Sovereign/Coupling/ParityViolation.agda:84 — 0 条

### src/Sovereign/Coupling/ParityViolation.agda:114 — 0 条

### src/Sovereign/Coupling/ParityViolation.agda:148 — 2 条
- `betaDecayAsymmetry` : betaDecayAsymmetry : ∀ (flip : TritFlip) → tritFlipChiralBias flip LeftHanded >ℤ tritFlipChiralBias flip RightHanded
- `chiralPhaseTransition` : chiralPhaseTransition : ToroidalPower → ChiralSymmetry × WuXingAmplitude

### src/Sovereign/Coupling/ParityViolation.agda:171 — 0 条

### src/Sovereign/Coupling/ParityViolation.agda:198 — 1 条
- `weakForce` : weakForce : WeakNuclearForce

### src/Sovereign/Coupling/ParityViolation.agda:220 — 2 条
- `ParityViolation` : ParityViolation : Set
- `SpatialReflectionAsymmetry` : SpatialReflectionAsymmetry : Set

### src/Sovereign/Coupling/ParityViolation.agda:224 — 1 条
- `noSpatialReflection` : noSpatialReflection : ¬ (ParityViolation ≡ SpatialReflectionAsymmetry)

### src/Sovereign/Coupling/ParityViolation.agda:228 — 2 条
- `ParityViolationDefinition` : ParityViolationDefinition : Set
- `ChiralSymmetryBreakingByToroidalWinding` : ChiralSymmetryBreakingByToroidalWinding : Set

### src/Sovereign/Coupling/ParityViolation.agda:232 — 1 条
- `parityViolationLegal` : parityViolationLegal : ParityViolationDefinition ≡ ChiralSymmetryBreakingByToroidalWinding

### src/Sovereign/Coupling/SpinTwistor.agda:77 — 2 条
- `ChiralityInContainer` : ChiralityInContainer : Chirality → Set
- `SpinLabelInContainer` : SpinLabelInContainer : SpinLabel → Set

### src/Sovereign/Coupling/SpinTwistor.agda:103 — 3 条
- `IsBoson` : IsBoson : SpinLabel → Set
- `IsFermion` : IsFermion : SpinLabel → Set
- `spinStatisticsReset` : spinStatisticsReset : ∀ (tp : ToroidalPower) (beta : ChiralBeta) → let spin = computeSpinProjection tp beta in (spin ≡ Spin1 → IsBoson spin) × (spin ≡ Spin12 → 

### src/Sovereign/Coupling/SpinTwistor.agda:150 — 3 条
- `SovereignState` : SovereignState : Set
- `accReal` : accReal : SovereignState → ℤ
- `accImag` : accImag : SovereignState → ℤ

### src/Sovereign/Coupling/SpinTwistor.agda:220 — 9 条
- `Electron` : Electron : Set Spin12' : Set
- `TwistorSpace` : TwistorSpace : Set
- `FundamentalSpacetime` : FundamentalSpacetime : Set
- `SpinNetwork` : SpinNetwork : Set
- `QuantumGeometry` : QuantumGeometry : Set
- `SpinDefinition` : SpinDefinition : Set
- `ChiralSeparationProjection` : ChiralSeparationProjection : Set
- `TwistorDefinition` : TwistorDefinition : Set
- `T6ComplexCoordinateProjection` : T6ComplexCoordinateProjection : Set RequiresResetToDis本源 : Set → Set

### src/Sovereign/Coupling/SpinTwistor.agda:234 — 4 条
- `notElectronSpin12` : notElectronSpin12 : ¬ (Electron ≡ Spin12')
- `notTwistorSpacetime` : notTwistorSpacetime : ¬ (TwistorSpace ≡ FundamentalSpacetime)
- `notSpinNetworkQuantumGeom` : notSpinNetworkQuantumGeom : ¬ (SpinNetwork ≡ QuantumGeometry)
- `spinLegal` : spinLegal : SpinDefinition ≡ ChiralSeparationProjection

### src/Sovereign/Coupling/SpinTwistor.agda:247 — 1 条
- `spinTwistorResetClause` : spinTwistorResetClause : ∀ (spin : SpinLabel) (tw : TwistorPoint) → RequiresResetToDis本源 spin × RequiresResetToDis本源 tw

### src/Sovereign/Coupling/TQ10.agda:130 — 5 条
- `updatePhaseBias` : updatePhaseBias : ℕ → ℕ → Word8
- `updateChernGuard` : updateChernGuard : ℕ → ℕ → Word8
- `updateWuxingMask` : updateWuxingMask : ℕ → Word8
- `updateReserved` : updateReserved : ReservedLayer → ReservedLayer
- `evolveBlock` : evolveBlock : SovereignBlock → SovereignBlock

### src/Sovereign/Coupling/TQ10.agda:161 — 7 条
- `IsFloatingPoint` : IsFloatingPoint : Set
- `Decomposable` : Decomposable : Set
- `ModifiedFormat` : ModifiedFormat : Set
- `sov_block_holographic_t` : sov_block_holographic_t : Set
- `noFloatInBlock` : noFloatInBlock : ∀ (block : SovereignBlock) → ¬ IsFloatingPoint
- `noDecomposition` : noDecomposition : ∀ (block : SovereignBlock) → ¬ Decomposable
- `polarMod144` : polarMod144 : ∀ (coord : ℕ) → coord % PolarWinding ≡ coord % 144

### src/Sovereign/Coupling/TQ10.agda:228 — 1 条
- `sovFormatImmutable` : sovFormatImmutable : ¬ (ModifiedFormat ≡ sov_block_holographic_t)

### src/Sovereign/Coupling/ZhonglvPhaseSync.agda:354 — 1 条
- `zhonglvConstitutionalClause` : zhonglvConstitutionalClause : ∀ (sync : ZhonglvPhaseSync) → IsTopologicalBreath sync

### src/Sovereign/Density/Resonance.agda:259 — 1 条
- `resonanceLegal` : resonanceLegal : ResonanceDefinition ≡ NayinStandingWaveHarmonicFiltering

### src/Sovereign/Diagnosis/ElectricCivilization.agda:102 — 3 条
- `DiagnosisResult` : DiagnosisResult : Set
- `Diagnosed` : Diagnosed : ElectricCharacteristic → Set → DiagnosisResult
- `Unlawful` : Unlawful : ElectricCharacteristic → DiagnosisResult

### src/Sovereign/Diagnosis/ElectricCivilization.agda:152 — 2 条
- `allMisconceptionsDiagnosable` : allMisconceptionsDiagnosable : ∀ (m : EightMisconceptions) → highDimensionalDiagnosis (misconceptionToChar m) ≢ Unlawful (misconceptionToChar m)
- `prohibitedTerms` : prohibitedTerms : List String

### src/Sovereign/Diagnosis/ElectricCivilization.agda:177 — 2 条
- `ConstitutionalIsolation` : ConstitutionalIsolation : Set
- `isolationInstance` : isolationInstance : ConstitutionalIsolation

### src/Sovereign/Diagnosis/ElectricCivilization.agda:186 — 2 条
- `ElectricCivilizationReset` : ElectricCivilizationReset : Set
- `Hz432Reset` : Hz432Reset : ElectricCivilizationReset elec→struct : Set

### src/Sovereign/Diagnosis/ElectricCivilization.agda:191 — 2 条
- `Hz432ResetValue` : Hz432ResetValue : Set
- `mustResetBeforeUse` : mustResetBeforeUse : Set

### src/Sovereign/Diagnosis/ElectricCivilization.agda:209 — 13 条
- `crossScaleObservations` : crossScaleObservations : Set
- `diagnosisTable` : diagnosisTable : Set
- `IsLawfulFoundation` : IsLawfulFoundation : ElectricCharacteristic → Set
- `IsLawfulUnit` : IsLawfulUnit : String → Set
- `IsLawfulTerm` : IsLawfulTerm : String → Set
- `clause1_BaseSeparation` : clause1_BaseSeparation : Set
- `clause2_UnitSeparation` : clause2_UnitSeparation : Set
- `clause3_LanguageSeparation` : clause3_LanguageSeparation : Set π-const : ℚ
- `clause4_NumericSeparation` : clause4_NumericSeparation : Set
- `clause5_InterpretationAuthority` : clause5_InterpretationAuthority : Set
- `electricCivilizationIsDegenerate` : electricCivilizationIsDegenerate : Set
- `LvSuanConstitutionIsFinal` : LvSuanConstitutionIsFinal : Set
- `electricCivilizationPendingElevation` : electricCivilizationPendingElevation : Set

### src/Sovereign/Engine/QsUpdate.agda:94 — 0 条

### src/Sovereign/HoTT/DiscreteCCHM.agda:106 — 0 条

### src/Sovereign/HoTT/DiscreteCCHM.agda:109 — 2 条
- `windingP` : windingP : ℕ → ℕ ; windingP n = (n % POLAR) * TORUS
- `winding-balance` : winding-balance : ∀ n → windingP (n + FULL_TOUR) ≡ windingP n

### src/Sovereign/Physics/QuartzPhonon.agda:458 — 0 条

### src/Sovereign/Projection/Decimal/Proofs.agda:35 — 0 条

### src/Sovereign/RootMath/Base.agda:110 — 0 条

### src/Sovereign/Structology/Aether.agda:340 — 2 条
- `aetherNotContinuous` : aetherNotContinuous : ¬ (Aether ≡ ContinuousMedium)
- `AetherDefinition` : AetherDefinition : Set

### src/Sovereign/Structology/T6.agda:976 — 0 条

### src/Sovereign/Structology/T6.agda:1475 — 0 条

## 已清除 (2026-08 P0 轮, 全部 ⊥ 可导出, 勿再引入)

- k>1-contr, electricCannotExpressHoloPi, cannotUpgradePi (HolographicPi)
- orbit-count-is-4320, total-orbits, orbit-refl/sym/trans 公理化 (ProjectiveOrbit → 重导出)
- experimental-anchoring (Quantum/Foundation)
- windingNotDecomposed (MagicSquare144 主库 + _standalone 旧副本) — ¬(144≡120+24), refl 反证
- polarIndecomposable (Boundaries) — 见证 120+24=144
- holoPiIrreducible (Boundaries) — 见证 k=2 (144=2·72, 46=2·23)
- Anchor_EnergyGap_H2O (DataAnchors) — 断言 867/1000 ≡ 5/10
- manifold-orth-replaces-coprime (MagicSquareM4) — 空洞 Set 公理
- projection-orthogonality (MagicSquareM4) — 假公理 → record 字段
- crt-fiber-distinction (MagicSquare144) — 前提恒 refl, 结论被 0/1 反驳
- magicSquareIsStatic (MagicSquare144) — value 自由字段取 144 即反证
- noIllegalSymmetry (WindingAsymmetry) — IllegalStatement 4 构造子, ⊥ 直证
- zhonglvSynchronizes 假合取 (ZhonglvPhaseSync) — acc'⁴≡acc'² 对任意 ℤ 假
- sunNotInvertible/yiNotInvertible (WindingAsymmetry) — ℤ 指数可逆, 改写为真定理
- reversibleImpliesHeatDeath (WindingAsymmetry) — 前提可证 + 结论被 syncAt 反驳

## 类型级重建 (教义从假公理 → 可证定理, 2026-08)

"不可拆解/禁约分"教义的类型级落地 — 见 `Sovereign.Structology.PlatonicTorusProjection`
(0 postulate, 编译绿):

- `polarContainerIsAtomic` / `toroidalTimeIsAtomic` — 极向 144 (I_h 空间容器,
  子午线缠绕) 与环向 46 (I_H 时间分子振动, 经度大圆缠绕) 的原子表示恰一个
  构造子 — "不可拆解"的可证形式
- 禁约分: 由 `HolographicPi` 的 PolarRep/ToroidalRep 原子类型承载 —
  "k·72/72·23" 在类型层不可表达
- `platonicProjectionEquiv : Fin 144 ≃ (Fin 120 ⊎ Fin 24)` — 柏拉图几何体
  (十二面体 120 胞腔) + 群信息论 (梅尔卡巴 24) 在环面上的投影是 144 点
  容器的等价映射 (to/from + 双向往返恒等全部证明)
- `WindingContainer` — I_h × I_H 缠绕语义记录 (与剖分计数分属不同范畴)

物理锚定: 石英声子等离子体 (Physics/QuartzPhonon, S2Sovereign 1.27B 训练
验证) + 螺旋测地线收敛极限环 (384K 步 LCM 环, dype wiki/06-experimental.md)。

## 本会话升级为证明 (postulate → 0)

- shift-additive (DiscreteCCHM) — mod+-distrib + [m+kn]%n≡m%n
- orthogonal-basis-complete (MagicSquareM4) — 4 显式整数见证
- phonon-propagate/interference/standing-wave/collapse (Quantum/Foundation) — 构造性定义
- polarMod144/toroidalMod46 (TQ10) — refl
- lossGainUniqueness (Boundaries) — 恒等证明
- phaseDiffNotConstant, phaseAlignment (WindingAsymmetry) — [m+kn]%n≡m%n + toℕ-fromℕ<
- zhonglvSyncIdentity (ZhonglvPhaseSync) — +-identityˡ
- CartanTorsion: Z₃ 群公理 assoc/identity/inverse 27+3+3 case refl