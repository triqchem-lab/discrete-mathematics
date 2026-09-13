# 目录 `src/Sovereign/Completeness/` 逐模块审计记录

共 3 个模块。


## `src/Sovereign/Completeness/CompletenessTheorem.agda`

- **module**: `Sovereign.Completeness.CompletenessTheorem`
- **行数**: 209（代码 104 / 注释 74）
- **OPTIONS**: `--cubical --guardedness --rewriting`
- **导入 (14)**: `Data.Nat`, `Data.Product`, `Data.Unit`, `Data.Fin`, `Relation.Binary.PropositionalEquality`, `Sovereign.Completeness.Layer`, `Sovereign.Base.Trit`, `Sovereign.Algebra.ProjectionDifferential`, `Sovereign.Structology.T6`, `Sovereign.Structology.A4Group`, `Sovereign.Algebra.GF9`, `Sovereign.Algebra.Holographic.4320D`, `Sovereign.Algebra.DiscreteLimit`, `Sovereign.Algebra.LieDiscrete`
- **data 类型**: `CompletionStatus`
- **record 类型**: `CompletenessEvidence`
- **顶层签名 (14)**: `ContinuousUniverse`, `universeSize`, `DiscreteCarrier`, `carrierWitness`, `carrierLayer`, `projectionProof`, `completeness-theorem`, `completionStatus`, `completedCount`, `incompleteCount`, `derivative-nilpotent`, `fourier-decomposition`, `discrete-nonzero`, `lieGroup-rep-evidence`
- **质量**: `refl`×1；无 postulate / 无 hole

## `src/Sovereign/Completeness/FunctorProof.agda`

- **module**: `Sovereign.Completeness.FunctorProof`
- **行数**: 156（代码 52 / 注释 84）
- **OPTIONS**: `--cubical --rewriting --guardedness`
- **导入 (5)**: `Cubical.Foundations.Prelude`, `Cubical.WildCat.Base`, `Cubical.WildCat.Functor`, `Data.Unit`, `Sovereign.Completeness.Layer`
- **顶层签名 (10)**: `ContinuousCat`, `DiscreteCat`, `sim`, `sim-Bridge`, `sim-Proj-Manifold`, `sim-Proj-SO3`, `sim-Proj-Fourier`, `sim-Proj-Complex`, `sim-preserves-id`, `sim-preserves-comp`
- **质量**: `refl`×17；无 postulate / 无 hole

## `src/Sovereign/Completeness/Layer.agda`

- **module**: `Sovereign.Completeness.Layer`
- **行数**: 138（代码 73 / 注释 43）
- **OPTIONS**: `--rewriting --guardedness`
- **导入 (4)**: `Data.Nat`, `Data.Nat.Properties`, `Data.Unit`, `Data.Product`
- **data 类型**: `Layer`, `ContinuousConcept`
- **record 类型**: `LayerInfo`, `ProjectionMark`, `HasDiscreteAnalog`
- **顶层签名 (9)**: `layerRank`, `_≤layer_`, `≤layer-refl`, `≤layer-trans`, `≤layer-min`, `≤layer-max`, `layerInfo`, `conceptLayer`, `projectionMark`
- **质量**: `refl`×4；无 postulate / 无 hole
