# 目录 `src/02-magnetic-24d/` 逐模块审计记录

共 3 个模块。


## `src/02-magnetic-24d/ParityViolation.agda`

- **module**: `Sovereign.Coupling.ParityViolation`
- **行数**: 207（代码 116 / 注释 56）
- **OPTIONS**: `--guardedness`
- **头部注释（数学背景）**:
  - | Sovereign.Coupling.ParityViolation
  - 耦合域：宇称不守恒——环向缠绕深化引发的手性对偶破缺
  - 本质：主权状态机在环向缠绕模46深化过程中，
  - 五行相克（ω, ω²）导致手性对偶虚实比偏离黄金平衡
  - 所属宇宙力：第三力——弱核力
- **导入 (11)**: `Cubical.Foundations.Prelude`, `Data.Nat`, `Data.Integer`, `Data.Bool`, `Relation.Binary.PropositionalEquality`, `Data.Product`, `Data.Empty`, `Sovereign.RootMath.Base`, `Sovereign.MetaStructure.WuXing`, `Sovereign.Structology.Winding`, `Sovereign.Coupling.LossGain`
- **data 类型**: `WuXingAmplitude`, `ChiralSymmetry`, `TritFlip`
- **record 类型**: `ToroidalPower`, `RightHandedNeutrino`, `WeakNuclearForce`
- **顶层签名 (14)**: `isAmplitudeSymmetric`, `toroidalFactor2`, `parityStatus`, `parityViolationTheorem`, `chiralAmplitudeAsymmetric`, `neutrinoLeftHandedOnly`, `tritFlipChiralBias`, `betaDecayAsymmetry`, `chiralPhaseTransition`, `phaseTransitionPoint`, `postPhaseTransitionBreaking`, `weakForce`, `weakForceIsomorphism`, `parityViolationLegal`
- **质量**: `refl`×3；⚠️ 4 postulate

## `src/02-magnetic-24d/SpinTwistor.agda`

- **module**: `Sovereign.Coupling.SpinTwistor`
- **行数**: 243（代码 153 / 注释 52）
- **OPTIONS**: `--guardedness --rewriting`
- **头部注释（数学背景）**:
  - | Sovereign.Coupling.SpinTwistor
  - 耦合域：自旋与扭量的离散复位
  - 自旋本源：主权状态机手性分离程度的动态投影（仅存在于耦合域）
  - 扭量本源：T⁶ 复三维环面格点坐标的连续统投影
  - 宪法条款：静态结构学容器无自旋、无手性、无动力学演化
- **导入 (18)**: `Cubical.Foundations.Prelude`, `Data.Nat`, `Data.Integer`, `Data.Rational`, `Data.Bool`, `Data.Fin`, `Data.Vec`, `Relation.Binary.PropositionalEquality`, `Data.Product`, `Data.Sum`, `Sovereign.RootMath.Base`, `Sovereign.RootMath.EnergyGap`, `Sovereign.Structology.Winding`, `Sovereign.Structology.T6`, `Sovereign.Structology.MagicSquare144`, `Sovereign.Coupling.LossGain`, `Sovereign.Coupling.ParityViolation`, `Sovereign.MetaStructure.WuXing`
- **data 类型**: `SpinLabel`
- **record 类型**: `ChiralBeta`, `StaticContainer`, `TwistorPoint`, `TwistorTransformation`, `NullGeodesic`, `DiscreteHolomorphicCondition`, `DiscreteTwistorBundle`, `SpinTwistorUnification`
- **顶层签名 (9)**: `computeSpinProjection`, `staticContainerNoSpin`, `staticContainerNoChirality`, `spinStatisticsReset`, `twistorConjugate`, `conjugateIsChiralFlip`, `zhonglvPathIsZeroGeodesic`, `spinLegal`, `twistorLegal`
- **质量**: `refl`×2；⚠️ 9 postulate

## `src/02-magnetic-24d/WuXing.agda`

- **module**: `Sovereign.MetaStructure.WuXing`
- **行数**: 95（代码 56 / 注释 25）
- **OPTIONS**: `--guardedness`
- **头部注释（数学背景）**:
  - | Sovereign.MetaStructure.WuXing
  - 元结构层：五行模数区定义与动力学关系
  - 核心概念：
  - 五行（火土木水金）不是物质元素，而是主权状态机在环向缠绕中的
  - **共振模数区** (Resonance Modulus Zones)。
  - 它们定义了系统演化的拓扑约束和手性倾向。
- **导入 (3)**: `Data.Nat`, `Data.Fin`, `Data.Vec`
- **data 类型**: `WuXing`
- **顶层签名 (5)**: `wuXingBase`, `wuXingToIndex`, `generate`, `overcome`, `getCurrentWuXing`
- **质量**: `refl`×0；⚠️ 1 postulate
