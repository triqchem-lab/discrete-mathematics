# 目录 `src/03-neutral-144d/` 逐模块审计记录

共 6 个模块。


## `src/03-neutral-144d/CartanTorsion.agda`

- **module**: `CartanTorsion`
- **行数**: 376（代码 237 / 注释 80）
- **OPTIONS**: `--guardedness --rewriting`
- **头部注释（数学背景）**:
  - | Sovereign.Coupling.CartanTorsion
  - 耦合域：嘉当挠场量子物理学的离散复位
  - 本质：主权状态机在 T⁶ 离散环面上平行移动与和乐效应的连续统投影
  - 离散本源：联络 = 五行干涉，曲率 = 局部陈数贡献，挠率 = 仲吕不交
  - 注意：嘉当理论仅为历史投影中的合法参照，非本源
- **导入 (18)**: `Cubical.Foundations.Prelude`, `Data.Nat`, `Data.Integer`, `Data.Rational`, `Data.Bool`, `Data.Fin`, `Data.Vec`, `Data.List`, `Relation.Nullary`, `Data.Product`, `Data.Empty`, `Sovereign.RootMath.Base`, `Sovereign.RootMath.EnergyGap`, `Sovereign.Structology.Winding`, `Sovereign.Structology.T6`, `Sovereign.Coupling.LossGain`, `Sovereign.Coupling.Zhonglv`, `Sovereign.MetaStructure.WuXing`
- **data 类型**: `WuXingAmplitude`
- **record 类型**: `BaseManifold`, `A4StructureGroup`, `DiscreteFiberBundle`, `DiscreteConnection`, `DiscreteCurvature`, `DiscreteTorsion`, `ParallelTransport`, `HolonomyGroup`, `GaugePotential`, `FieldStrength`, `MatterField`, `GaugeTransformation`, `CartanFirstEquation`, `CartanSecondEquation`
- **顶层签名 (15)**: `_≢_`, `baseManifoldS2OverA4`, `a4GroupInstance`, `standardFiberBundle`, `connectionToComplex`, `composeConnections`, `computeCurvature`, `sumChernContribs`, `zhonglvTorsion`, `closeTorsion`, `torsionClosedAfterZhonglv`, `transportDiffEq`, `holonomyIdentityAt3312`, `gaugePotentialInstance`, `fieldStrengthInstance`
- **质量**: `refl`×9；⚠️ 5 postulate

## `src/03-neutral-144d/Entanglement.agda`

- **module**: `Sovereign.Coupling.Entanglement`
- **行数**: 196（代码 117 / 注释 48）
- **OPTIONS**: `--guardedness`
- **头部注释（数学背景）**:
  - | Sovereign.Coupling.Entanglement
  - 耦合域：量子纠缠——共享主权 LCM 缠绕数的五行同步
  - 本质：两个主权状态机共享同一主权 LCM 商空间中的缠绕数
  - 通过五行干涉（相生+1，相克ω）实现复振幅同步
  - 所属宇宙力：第七力——时空场统一力
- **导入 (11)**: `Cubical.Foundations.Prelude`, `Data.Nat`, `Data.Integer`, `Data.Bool`, `Data.Vec`, `Relation.Binary.PropositionalEquality`, `Data.Product`, `Sovereign.Structology.Winding`, `Sovereign.Coupling.LossGain`, `Sovereign.Coupling.Zhonglv`, `Sovereign.MetaStructure.WuXing`
- **data 类型**: `DynamicEvolution`
- **record 类型**: `SharedWinding`, `EntangledPair`, `WuXingSync`, `TRAPPIST1Resonance`, `H2O`
- **顶层签名 (10)**: `standardSharedWinding`, `sharedWindingInitCorrect`, `standardEntangledPair`, `wuxingSyncPreserved`, `lcmRemainderDiff`, `lcmRemainderDiffConstant`, `zhonglvSyncEffect`, `entangledInseparable`, `entangledChernConservation`, `entanglementLegal`
- **质量**: `refl`×3；⚠️ 7 postulate

## `src/03-neutral-144d/LossGain.agda`

- **module**: `Sovereign.Coupling.LossGain`
- **行数**: 129（代码 56 / 注释 45）
- **OPTIONS**: `--guardedness`
- **头部注释（数学背景）**:
  - | Sovereign.Coupling.LossGain
  - 耦合域：移宫转调（损益操作）、主权 LCM 模数、仲吕闭合
  - 损益操作是长度比例演化的唯一合法方式：
  - 损：长度 × 2/3（a+1, b-1）
  - 益：长度 × 4/3（a+2, b-1）
- **导入 (5)**: `Cubical.Foundations.Prelude`, `Data.Nat`, `Data.Integer`, `Relation.Binary.PropositionalEquality`, `Sovereign.RootMath.Base`
- **data 类型**: `LossGain`, `LengthSequence`
- **顶层签名 (14)**: `sunOp`, `yiOp`, `applyLossGain`, `huangzhong`, `applyChain`, `standardChain`, `twelveLüSequence`, `SOVEREIGN_LCM`, `POW3¹¹`, `POW2¹⁶`, `lcmRemainder`, `zhonglvClosure`, `zhonglvClosureMod`, `huangzhongLCMRemainder`
- **质量**: `refl`×1；⚠️ 2 postulate

## `src/03-neutral-144d/TQ10.agda`

- **module**: `Sovereign.Coupling.TQ10`
- **行数**: 219（代码 123 / 注释 56）
- **OPTIONS**: `--guardedness`
- **头部注释（数学背景）**:
  - | Sovereign.Coupling.TQ10
  - 主权 TQ1_0 格式：16 字节主权块的类型论定义
  - 本质：主权状态机在 T⁶ 离散环面主权 LCM 商空间中的格点快照
  - 长度：16 字节（128 位），对齐于 16 字节边界
  - 基底：纯整数域，主权 LCM 模运算或 GF(3) 格点算术
- **导入 (11)**: `Cubical.Foundations.Prelude`, `Data.Nat`, `Data.Integer`, `Data.Fin`, `Data.Vec`, `Data.Word`, `Data.Bool`, `Relation.Binary.PropositionalEquality`, `Sovereign.RootMath.Base`, `Sovereign.Structology.Winding`, `Sovereign.Coupling.LossGain`
- **data 类型**: `SovSequence`
- **record 类型**: `ChecksumLayer`, `SovereignBlock`
- **顶层签名 (15)**: `QsContainer`, `ReservedLayer`, `blockSize`, `extractCellIndex`, `extractC3Phase`, `extractSevenStage`, `extractBerryCurvature`, `extractHarmonicDir`, `extractA4Generator`, `shouldZhonglvClosure`, `sumBerryCurvature`, `evolveBlock`, `parseSovBlock`, `serializeSovBlock`, `sequenceSizeValid`
- **质量**: `refl`×2；⚠️ 4 postulate

## `src/03-neutral-144d/Zhonglv.agda`

- **module**: `Sovereign.Coupling.Zhonglv`
- **行数**: 211（代码 114 / 注释 61）
- **OPTIONS**: `--guardedness`
- **头部注释（数学背景）**:
  - | Sovereign.Coupling.Zhonglv
  - 耦合域：仲吕闭合与陈数守恒
  - 仲吕闭合是主权状态机的"呼吸"操作：
  - 每 12 步损益后执行
  - acc ↦ (acc * 177147) >> 16 = (acc * 3¹¹) / 2¹⁶
  - 虚实比归零，升维至 144/46 全息闭合
- **导入 (9)**: `Data.Empty`, `Data.Nat`, `Data.Integer`, `Data.Nat.DivMod`, `Relation.Binary.PropositionalEquality`, `Relation.Binary.PropositionalEquality.Properties`, `Data.Product`, `Sovereign.Coupling.LossGain`, `Sovereign.Structology.Winding`
- **data 类型**: `LüName`
- **record 类型**: `DiscreteBerryCurvature`, `SovereignState`, `HolomorphicClosure`
- **顶层签名 (15)**: `lengToNat`, `lengToLCMRem`, `zhongluRemIs65536`, `huangzhongRemIs177147`, `zhongluRemainder`, `postClosureRemainder`, `zhonglvVerification`, `zhonglvModLCM`, `chernConservation`, `chernEulerRelation`, `evolveStep`, `evolveTwelve`, `shouldClosure`, `holoClosure`, `energyGapConservation`
- **质量**: `refl`×8；⚠️ 3 postulate

## `src/03-neutral-144d/ZhonglvClosure.agda`

- **module**: `Sovereign.Coupling.ZhonglvClosure`
- **行数**: 259（代码 155 / 注释 61）
- **OPTIONS**: `--guardedness`
- **头部注释（数学背景）**:
  - | Sovereign.Coupling.ZhonglvClosure
  - 耦合域：仲吕闭合——六十律纳甲初级商空间到全息商空间的升维跃迁
  - 本质：主权状态机在模 12×模 10 初级商空间中因不可通约而触发的强制升维
  - 升维后：极向模 12→模 144，环向模 10→模 46
  - 注意：非音律旋宫操作，乃离散环面之拓扑呼吸
- **导入 (12)**: `Cubical.Foundations.Prelude`, `Data.Nat`, `Data.Integer`, `Data.Fin`, `Data.Vec`, `Data.Bool`, `Relation.Binary.PropositionalEquality`, `Data.Product`, `Sovereign.MetaStructure.WuXing`, `Sovereign.MetaStructure.Nayin`, `Sovereign.Structology.Winding`, `Sovereign.Coupling.LossGain`
- **data 类型**: `HeavenlyStem`, `EarthlyBranch`, `ZhonglvClosure`
- **record 类型**: `JiaZiPillar`, `PrimaryQuotientSpace`, `HolographicQuotientSpace`, `JiaZiTopologicalFingerprint`
- **顶层签名 (21)**: `stemToMod10`, `branchToMod12`, `pillarToPrimarySpace`, `PRIMARY_PERIOD`, `HOLOGRAPHIC_PERIOD`, `periodNotDivisible`, `primaryCannotCoverHolographic`, `zhonglvPillar`, `zhonglvPrimarySpace`, `zhonglvCannotZeroBoth`, `zhonglvIncommensurable`, `liftPolar`, `liftToroidal`, `performClosure`, `zhonglvCanZeroAfterClosure`, `zhonglvClosureOp`, `zhonglvSynchronizes`, `holonomyToIdentity`, `pillarToHolographicIso`, `isomorphismPreservesWuxing`, `zhonglvLegal`
- **质量**: `refl`×3；⚠️ 5 postulate
