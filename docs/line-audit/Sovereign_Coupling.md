# 目录 `src/Sovereign/Coupling/` 逐模块审计记录

共 11 个模块。


## `src/Sovereign/Coupling/CartanTorsion.agda`

- **module**: `Sovereign.Coupling.CartanTorsion`
- **行数**: 455（代码 289 / 注释 99）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | Sovereign.Coupling.CartanTorsion
  - 耦合域：嘉当挠场量子物理学的离散复位
  - 本质：主权状态机在 T⁶ 离散环面上平行移动与和乐效应的连续统投影
  - 离散本源：联络 = 五行干涉，曲率 = 局部陈数贡献，挠率 = 仲吕不交
- **导入 (22)**: `Data.Nat`, `Data.Integer`, `Data.Rational`, `Data.Bool`, `Data.Fin`, `Data.Vec`, `Data.List`, `Data.Maybe`, `Function`, `Relation.Binary.PropositionalEquality`, `Relation.Nullary`, `Data.Product`, `Data.Empty`, `Data.Empty`, `Sovereign.Base.Trit`, `Sovereign.RootMath.EnergyGap`, `Sovereign.RootMath.AlgebraicComplex`, `Sovereign.Structology.Winding`, `Sovereign.Structology.T6`, `Sovereign.Coupling.LossGain`, `Sovereign.Coupling.Zhonglv`, `Sovereign.MetaStructure.WuXing`
- **data 类型**: `WuXingAmplitude`
- **record 类型**: `DiscreteComplex`, `BaseManifold`, `A4StructureGroup`, `DiscreteFiberBundle`, `DiscreteConnection`, `DiscreteCurvature`, `DiscreteTorsion`, `ClosedTorsion`, `ParallelTransport`, `HolonomyGroup`, `GaugePotential`, `FieldStrength`, `MatterField`, `GaugeTransformation`, `CartanFirstEquation`, `CartanSecondEquation`
- **顶层签名 (15)**: `conjugate`, `phaseOvercome2`, `baseManifoldS2OverA4`, `a4GroupInstance`, `standardFiberBundle`, `connectionToComplex`, `composeConnections`, `computeCurvature`, `zhonglvTorsion`, `closeTorsion`, `torsionClosedAfterZhonglv`, `transportDiffEq`, `holonomyIdentityAt3312`, `gaugePotentialInstance`, `fieldStrengthInstance`
- **质量**: `refl`×50；⚠️ 8 postulate

## `src/Sovereign/Coupling/Dynamics.agda`

- **module**: `Sovereign.Coupling.Dynamics`
- **行数**: 51（代码 43 / 注释 0）
- **OPTIONS**: `--rewriting --allow-unsolved-metas`
- **导入 (7)**: `Data.Nat`, `Data.Nat.Base`, `Data.Nat.DivMod`, `Data.Fin`, `Data.Bool`, `Relation.Binary.PropositionalEquality`, `Sovereign.Format.TQ10`
- **顶层签名 (4)**: `updateHigh4`, `updateLow5`, `step`, `evolveN`
- **质量**: `refl`×1；无 postulate / 无 hole

## `src/Sovereign/Coupling/Entanglement.agda`

- **module**: `Sovereign.Coupling.Entanglement`
- **行数**: 260（代码 151 / 注释 71）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | Sovereign.Coupling.Entanglement
  - 耦合域：量子纠缠——共享主权 LCM 缠绕数的五行同步
  - 本质：两个主权状态机共享同一主权 LCM 商空间中的缠绕数
  - 通过五行干涉（相生+1，相克ω）实现复振幅同步
  - 所属宇宙力：第七力——时空场统一力
- **导入 (17)**: `Cubical.Foundations.Prelude`, `Data.Nat`, `Data.Integer`, `Data.Integer.Properties`, `Data.Bool`, `Data.Vec`, `Data.Fin`, `Data.Unit`, `Agda.Builtin.List`, `Relation.Binary.PropositionalEquality`, `Data.Product`, `Data.Empty`, `Relation.Nullary`, `Sovereign.Structology.Winding`, `Sovereign.Coupling.LossGain`, `Sovereign.Coupling.Zhonglv`, `Sovereign.MetaStructure.WuXing`
- **data 类型**: `DynamicEvolution`
- **record 类型**: `SharedWinding`, `EntangledPair`, `WuXingSync`, `SeparatePair`, `TRAPPIST1Resonance`, `H2O`
- **顶层签名 (13)**: `standardSharedWinding`, `sharedWindingInitCorrect`, `initialSovereignState`, `standardEntangledPair`, `wuxingSyncPreserved`, `lcmRemainderDiff`, `ℤ-diff-self`, `lcmRemainderDiffConstant`, `applyEvolution`, `zhonglvSyncEffect`, `entangledInseparable`, `chernNumber`, `entangledChernConservation`
- **质量**: `refl`×13；⚠️ 3 postulate

## `src/Sovereign/Coupling/LCM.agda`

- **module**: `Sovereign.Coupling.LCM`
- **行数**: 286（代码 231 / 注释 20）
- **OPTIONS**: `--rewriting --guardedness`
- **导入 (12)**: `Data.Fin`, `Data.Fin.Properties`, `Data.Vec`, `Data.Nat`, `Data.Nat.DivMod`, `Data.Nat.Properties`, `Data.Integer`, `Data.Unit`, `Relation.Binary.PropositionalEquality`, `Relation.Nullary.Decidable.Core`, `Sovereign.Coding.Trit`, `Sovereign.Base.Invariants`
- **顶层签名 (22)**: `SOVEREIGN_LCM`, `GAP_THRESHOLD`, `SovereignSection`, `eval-vec`, `powersOf3`, `sectionToCoordinate`, `coordinateToSection`, `modLCM`, `pack5`, `unpack5`, `packSectionToQs`, `unpackQsToSection`, `computeDiscreteCurvature`, `computeLocalChernHeuristic`, `go`, `go-distrib`, `div-lt`, `lemma`, `go≡stc`, `modLCM_Legal`, `unpack5-pack5-lemma`, `pack5RangeValid`
- **质量**: `refl`×14；无 postulate / 无 hole

## `src/Sovereign/Coupling/LossGain.agda`

- **module**: `Sovereign.Coupling.LossGain`
- **行数**: 179（代码 75 / 注释 68）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | Sovereign.Coupling.LossGain
  - 耦合域：移宫转调（损益操作）、主权 LCM 模数、仲吕对齐
  - 损益操作是长度比例演化的唯一合法方式：
  - 损：长度 × 2/3（a+1, b-1）
  - 益：长度 × 4/3（a+2, b-1）
- **导入 (7)**: `Agda.Builtin.List`, `Data.Bool`, `Data.Nat`, `Data.Integer`, `Relation.Binary.PropositionalEquality`, `Sovereign.RootMath.Base`, `Data.Vec`
- **data 类型**: `LossGain`, `LengthSequence`
- **record 类型**: `Signature`, `Structure`
- **顶层签名 (19)**: `sunOp`, `yiOp`, `applyLossGain`, `huangzhong`, `applyChain`, `standardChain`, `twelveLüSequence`, `SOVEREIGN_LCM`, `POW3¹¹`, `POW2¹⁶`, `lcmRemainder`, `zhonglvAlign`, `zhonglvAlignMod`, `huangzhongLCMRemainder`, `zhonglvCorrectness`, `zhonglvClosure`, `zhonglvClosureMod`, `LossGainSig`, `LossGainStructure`
- **质量**: `refl`×2；无 postulate / 无 hole

## `src/Sovereign/Coupling/ParityViolation.agda`

- **module**: `Sovereign.Coupling.ParityViolation`
- **行数**: 248（代码 128 / 注释 75）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | Sovereign.Coupling.ParityViolation
  - 耦合域：宇称不守恒——环向缠绕深化引发的手性对偶破缺 (0 postulate, 无洞)
  - 本质：主权状态机在环向缠绕模 46 深化过程中，五行相克（ω, ω²）导致
  - 手性对偶虚实比偏离黄金平衡。所属宇宙力：第三力——弱核力。
  - 可证核心（符号穷举）：
  - parityViolationTheorem   a≥3 ⟹ 宇称不守恒 (parityStatus ≢ PairedConserved)
  - neutrinoLeftHandedOnly   a≥4 ⟹ 左旋极限态 (右旋与配对态均排除)
  - betaDecayAsymmetry       T₂→T₀ 翻转释放沿左旋方向偏置 (+1 > −1, 专用化)
  - postPhaseTransitionBreaking  a≥3 ⟹ 相变后对称性破坏 + 振幅不对称
  - weakForceIsomorphism     弱核力几何本源在相变点 = AmpOvercome (ω 激活)
  - 宪法层（表述区分，类型级，非 postulate）：
  - ForbiddenExpr (空间反射不对称) vs LegalExpr (环向缠绕手性破缺) 不相容;
  - 这是本框架对自身表述纪律的约束, 不是对任何物理理论的裁决 —
  - 一切理论并存互补, 框架只规定自己用什么语言。
  - 合法表述的内容即 parityViolationTheorem — 本框架可证的正是后者。
  - 修正上一稿：6 个 postulate → λ() 直接证明；6 个洞 → (λ () , refl);
- **导入 (9)**: `Data.Nat`, `Data.Integer`, `Data.Bool`, `Data.Product`, `Data.Empty`, `Relation.Binary.PropositionalEquality`, `Relation.Nullary`, `Sovereign.Base.Trit`, `Sovereign.MetaStructure.WuXing`
- **data 类型**: `WuXingAmplitude`, `ChiralSymmetry`, `TritFlip`, `ExperimentalAnchor`, `ForbiddenExpr`, `LegalExpr`
- **record 类型**: `ToroidalPower`, `WeakNuclearForce`
- **顶层签名 (22)**: `isAmplitudeSymmetric`, `toroidalFactor2`, `parityStatus`, `not-0≥3`, `not-1≥3`, `not-2≥3`, `parityViolationTheorem`, `chiralAmplitudeAsymmetric`, `not-0≥4`, `not-1≥4`, `not-2≥4`, `not-3≥4`, `neutrinoLeftHandedOnly`, `tritFlipChiralBias`, `betaDecayAsymmetry`, `chiralPhaseTransition`, `phaseTransitionPoint`, `postPhaseTransitionBreaking`, `weakForce`, `weakForceIsomorphism`, `noSpatialReflection`, `parityViolationLegal`
- **质量**: `refl`×6；无 postulate / 无 hole

## `src/Sovereign/Coupling/SpinTwistor.agda`

- **module**: `Sovereign.Coupling.SpinTwistor`
- **行数**: 378（代码 251 / 注释 68）
- **OPTIONS**: `--cubical --guardedness --rewriting`
- **头部注释（数学背景）**:
  - | Sovereign.Coupling.SpinTwistor
  - 耦合域：自旋与扭量的离散复位 (0 postulate, 无洞)
  - 自旋本源：主权状态机手性分离程度的动态投影（仅存在于耦合域）—
  - computeSpinProjection : ToroidalPower → SpinLabel,
  - 配对守恒 → Spin1 (玻色子), 完全分离 → Spin12 (费米子), 未激活 → Spin0
  - (spinProjectionBalanced / spinProjectionSeparated / spinProjectionInactive)
  - 扭量本源：T⁶ 复三维环面格点坐标的连续统投影 (TwistorPoint: z1,z2,z3),
  - 复共轭 ↔ 手性对偶 (conjugateIsChiralFlip 对合)
  - 宪法条款：静态结构学容器无自旋、无手性、无动力学 —
  - ChiralityInContainer / SpinLabelInContainer 为空谓词 (⊥), 0 postulate
  - 修正上一稿：9 个 postulate 谓词/类型 → 构造性定义或空谓词;
  - 4 个洞 → (λ () , refl) / 显式见证; 非法标识符 RequiresResetToDis本源 → 删除;
  - DiscreteComplex 导入源 EnergyGap → CartanTorsion (本地定义处);
  - SovereignState 由 postulate → 引用 Zhonglv 真实定义;
  - 范畴分离: 标记类型 + λ () 类型不等 (数据型不等, 附录 8 模式 4)。
- **导入 (16)**: `Data.Nat`, `Data.Integer`, `Data.Bool`, `Data.Unit`, `Data.List`, `Data.Product`, `Data.Empty`, `Relation.Binary.PropositionalEquality`, `Relation.Nullary`, `Sovereign.Base.Trit`, `Sovereign.Coupling.CartanTorsion`, `Sovereign.Coupling.Zhonglv`, `Sovereign.Coupling.LossGain`, `Sovereign.Coupling.ParityViolation`, `Sovereign.MetaStructure.WuXing`, `Sovereign.Structology.T6`
- **data 类型**: `SpinLabel`, `Electron`, `FundamentalSpacetime`, `SpinNetwork`, `QuantumGeometry`
- **record 类型**: `StaticContainer`, `TwistorPoint`, `NullGeodesic`, `DiscreteHolomorphicCondition`, `DiscreteTwistorBundle`, `SpinTwistorUnification`
- **顶层签名 (45)**: `computeSpinProjection`, `notSinglePaired`, `notBreakingPaired`, `notObviousPaired`, `notCompletePaired`, `notSingleComplete`, `notPairedComplete`, `notBreakingComplete`, `notObviousComplete`, `notPairedSingle`, `notBreakingSingle`, `notObviousSingle`, `notCompleteSingle`, `spinProjectionBalanced`, `spinProjectionSeparated`, `spinProjectionInactive`, `Bosonic`, `Fermionic`, `spinStatisticsReset`, `fermionStatisticsReset`, `ChiralityInContainer`, `SpinLabelInContainer`, `noChiralityInContainer`, `noSpinInContainer`, `standardStaticContainer`, `staticContainerNoSpin`, `staticContainerNoChirality`, `negate-involutive`, `conjugate-involutive`, `twistorConjugate`, `conjugateIsChiralFlip`, `zhonglvPath`, `zhonglvGeodesic`, `zhonglvPathIsZeroGeodesic`, `negC`, `ChiralSeparationProjection`, `SpinDefinition`, `spinLegal`, `spinLegalWitness`, `T6ComplexCoordinateProjection`, `TwistorDefinition`, `twistorLegal`, `notElectronSpin12`, `notTwistorSpacetime`, `notSpinNetworkQuantumGeom`
- **质量**: `refl`×15；无 postulate / 无 hole

## `src/Sovereign/Coupling/TQ10.agda`

- **module**: `Sovereign.Coupling.TQ10`
- **行数**: 231（代码 125 / 注释 66）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | Sovereign.Coupling.TQ10
  - 主权 TQ1_0 格式：16 字节主权块的类型论定义
  - 本质：主权状态机在 T⁶ 离散环面主权 LCM 商空间中的格点快照
  - 长度：16 字节（128 位），对齐于 16 字节边界
  - 基底：纯整数域，主权 LCM 模运算或 GF(3) 格点算术
- **导入 (16)**: `Data.Nat`, `Data.Nat.Properties`, `Data.Integer`, `Data.Fin`, `Data.Vec`, `Data.List`, `Data.Maybe`, `Data.Word8.Base`, `Data.Word64.Base`, `Data.Bool`, `Relation.Nullary.Decidable.Core`, `Relation.Nullary.Negation`, `Relation.Binary.PropositionalEquality`, `Sovereign.Base.Trit`, `Sovereign.Structology.Winding`, `Sovereign.Coupling.LossGain`
- **data 类型**: `SovSequence`
- **record 类型**: `ChecksumLayer`, `SovereignBlock`
- **顶层签名 (17)**: `QsContainer`, `ReservedLayer`, `blockSize`, `extractCellIndex`, `extractC3Phase`, `extractSevenStage`, `extractBerryCurvature`, `extractHarmonicDir`, `extractA4Generator`, `shouldZhonglvClosure`, `sumBerryCurvature`, `evolveBlock`, `polarMod144`, `toroidalMod46`, `parseSovBlock`, `serializeSovBlock`, `sequenceSizeValid`
- **质量**: `refl`×5；⚠️ 3 postulate

## `src/Sovereign/Coupling/TrainingSoftConstraint.agda`

- **module**: `Sovereign.Coupling.TrainingSoftConstraint`
- **行数**: 117（代码 47 / 注释 50）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | Sovereign.Coupling.TrainingSoftConstraint
  - 耦合域：训练期能隙Δ软约束 (Soft Constraint)
  - 宪法约束：
  - 1. 能隙Δ双重锚定：推理用硬边界 (≥243 归零)，训练用软约束。
  - 2. 阈值定义：当偏离超过 Δ/2 (≈0.866) 时，触发高额能量惩罚。
  - 3. 目的：引导训练向黄金平衡 (虚实比=1.0, 陈数=2) 收敛，而非强制截断。
- **导入 (8)**: `Data.Nat`, `Data.Nat.Base`, `Data.Nat.Properties`, `Data.Integer`, `Data.Bool`, `Data.Unit.Base`, `Data.Empty`, `Relation.Binary.PropositionalEquality`
- **顶层签名 (7)**: `DELTA_HALF_SCALED`, `PENALTY_MULTIPLIER`, `computeDeviation`, `applySoftConstraint`, `softConstraintInactiveWithinGap`, `softConstraintIncreasesEnergyOutsideGap`, `computeChernDeviationPenalty`
- **质量**: `refl`×2；无 postulate / 无 hole

## `src/Sovereign/Coupling/Zhonglv.agda`

- **module**: `Sovereign.Coupling.Zhonglv`
- **行数**: 232（代码 122 / 注释 75）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | Sovereign.Coupling.Zhonglv
  - 耦合域：仲吕闭合与陈数守恒
  - 仲吕闭合是主权状态机的"呼吸"操作：
  - 每 12 步损益后执行
  - acc ↦ (acc * 177147) >> 16 = (acc * 3¹¹) / 2¹⁶
  - 虚实比归零，升维至 144/46 全息闭合
- **导入 (10)**: `Data.Empty`, `Data.Nat`, `Data.Integer`, `Data.Nat.DivMod`, `Data.Bool`, `Relation.Binary.PropositionalEquality`, `Relation.Nullary`, `Data.Product`, `Sovereign.Coupling.LossGain`, `Sovereign.Structology.Winding`
- **data 类型**: `LuName`
- **record 类型**: `SovereignState`, `DiscreteBerryCurvature`, `HolomorphicClosure`
- **顶层签名 (14)**: `lengToNat`, `lengToLCMRem`, `zhongluRemIs5994`, `huangzhongRemIs62059`, `zhongluRemainder`, `postClosureRemainder`, `zhonglvVerification`, `zhonglvModLCM`, `chernConservation`, `evolveStep`, `chernEulerRelation`, `evolveTwelve`, `shouldClosure`, `holoClosure`
- **质量**: `refl`×8；⚠️ 3 postulate

## `src/Sovereign/Coupling/ZhonglvPhaseSync.agda`

- **module**: `Sovereign.Coupling.ZhonglvPhaseSync`
- **行数**: 365（代码 186 / 注释 132）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | Sovereign.Coupling.ZhonglvPhaseSync
  - v5.2: 仲吕相位同步（非闭合）
  - 耦合域：仲吕相位同步——六十律纳甲初级商空间到全息商空间的升维跃迁
  - 本质：主权状态机在模 12×模 10 初级商空间中因不可通约而触发的强制升维
  - 升维后：极向模 12→模 144，环向模 10→模 46
  - 注意：非音律旋宫操作，乃离散环面之拓扑呼吸
  - v5.2 Conceptual Correction --
  - 6624 is phase alignment, not topological closure:
  - LCM(144, 46) = 3312 is algebraic alignment of two periodicities,
  - not a proof that the limit cycle returns to its starting point.
  - 极限环（协议E）从不真正闭合——它们只是持续级联（keep cascading）。
  - Evidence: Protocol E shows sharp quantum phase transition at ρ≈0.38
  - (+16.6% FOM jump), proving limit cycles don't close.
  - "仲吕闭合" (Zhonglv closure) is therefore "仲吕相位同步"
  - (Zhonglv phase synchronization): the polar and toroidal
  - coordinates achieve simultaneous phase alignment, not
  - topological loop closure.
  - Alignment is a strictly weaker condition than closure:
- **导入 (18)**: `Data.Nat`, `Data.Nat.Properties`, `Data.Nat.DivMod`, `Data.Nat.Divisibility`, `Data.Nat.LCM`, `Data.Integer`, `Data.Integer.Properties`, `Data.Fin`, `Data.Fin.Properties`, `Data.Vec`, `Data.Bool`, `Relation.Binary.PropositionalEquality`, `Relation.Nullary`, `Data.Product`, `Sovereign.MetaStructure.WuXing`, `Sovereign.MetaStructure.Nayin`, `Sovereign.Structology.Winding`, `Sovereign.Coupling.LossGain`
- **data 类型**: `HeavenlyStem`, `EarthlyBranch`, `ZhonglvPhaseSync`
- **record 类型**: `JiaZiPillar`, `PrimaryQuotientSpace`, `HolographicQuotientSpace`, `JiaZiTopologicalFingerprint`, `IsTopologicalBreath`
- **顶层签名 (23)**: `stemToMod10`, `branchToMod12`, `pillarToPrimarySpace`, `PRIMARY_PERIOD`, `HOLOGRAPHIC_PERIOD`, `periodNotDivisible`, `primaryCannotCoverHolographic`, `zhonglvPillar`, `zhonglvPrimarySpace`, `zhonglvCannotZeroBoth`, `zhonglvIncommensurable`, `alignmentCorrect`, `liftPolar`, `liftToroidal`, `performPhaseSync`, `zhonglvCanZeroAfterPhaseSync`, `zhonglvPhaseSyncOp`, `zhonglvSyncIdentity`, `holonomyToIdentity`, `pillarToHolographicIso`, `isomorphismPreservesWuxing`, `zhonglvIsNotMusicalRotation`, `zhonglvIsDimensionElevation`
- **质量**: `refl`×4；⚠️ 1 postulate
