# 目录 `src/Sovereign/PDE/` 逐模块审计记录

共 4 个模块。


## `src/Sovereign/PDE/ConvergenceAlignment.agda`

- **module**: `Sovereign.PDE.ConvergenceAlignment`
- **行数**: 392（代码 200 / 注释 157）
- **OPTIONS**: `--rewriting`
- **导入 (9)**: `Data.Nat`, `Data.Nat.Properties`, `Data.Fin`, `Data.Fin.Properties`, `Data.Product`, `Relation.Binary.PropositionalEquality`, `Sovereign.Base.Trit`, `Sovereign.Algebra.ProjectionDifferential`, `Sovereign.Algebra.DiscreteDE`
- **record 类型**: `LimitCycleConvergence`, `ExactAlignment`
- **顶层签名 (20)**: `DiscreteStateSeq`, `iterate`, `evolution-seq`, `iterate-plus`, `gf3func-encode`, `gf3func-decode`, `decode∘encode≡id`, `encode-injective`, `gf3func-cardinality`, `gf3func-count`, `pigeonhole-GF3Func`, `theorem-finite-cycle`, `theorem-exact-alignment`, `alignment-is-identity`, `shift-period-3`, `Δ-nilpotent-3`, `Δ-nilpotent-higher`, `Δ-convergence`, `shift-convergence`, `nilpotency-tighter-than-pigeonhole`
- **质量**: `refl`×33；无 postulate / 无 hole

## `src/Sovereign/PDE/HeatEquationDiscrete.agda`

- **module**: `Sovereign.PDE.HeatEquationDiscrete`
- **行数**: 388（代码 201 / 注释 149）
- **OPTIONS**: `--rewriting`
- **导入 (9)**: `Data.Nat`, `Data.Fin`, `Data.Empty`, `Data.Product`, `Relation.Binary.PropositionalEquality`, `Relation.Nullary`, `Sovereign.Base.Trit`, `Sovereign.Algebra.ProjectionDifferential`, `Sovereign.Algebra.DiscreteDE`
- **data 类型**: `_`
- **顶层签名 (24)**: `Grid1D`, `grid1d3-to-gf3func`, `gf3func-to-grid1d3`, `_⊕g_`, `sq`, `laplacian`, `laplacian≡Δ²`, `laplacian-const-zero`, `heatStep`, `heatStep≡id⊕Δ`, `energy`, `sq-zero`, `sq-one`, `sq-two`, `sq-negate`, `heat-const-steady`, `energy-step-identity`, `energy-conservation-balanced`, `heatStep³≡id`, `sum3-heatStep-invariant`, `≤₃-refl`, `⊕T₂-decreases`, `dissipation-core`, `heat-dissipation`
- **质量**: `refl`×129；无 postulate / 无 hole

## `src/Sovereign/PDE/PDEDiscrete.agda`

- **module**: `Sovereign.PDE.PDEDiscrete`
- **行数**: 240（代码 102 / 注释 110）
- **OPTIONS**: `--rewriting`
- **导入 (8)**: `Sovereign.Algebra.DiscreteDE`, `Data.Nat`, `Data.Product`, `Data.Unit`, `Relation.Binary.PropositionalEquality`, `Sovereign.Base.Trit`, `Sovereign.Algebra.ProjectionDifferential`, `Sovereign.Completeness.Layer`
- **record 类型**: `PDEDiscreteFramework`, `ODEPDECompletenessBridge`
- **顶层签名 (10)**: `pde-framework`, `ODEPDEDiscreteCarrier`, `odepde-witness`, `odepde-completeness-bridge`, `pde-fredholm`, `pde-ode-exists`, `pde-const-harmonic`, `pde-nilpotent`, `pde-Δ₁³`, `pde-Δ₂³`
- **质量**: `refl`×3；无 postulate / 无 hole

## `src/Sovereign/PDE/WaveEquationDiscrete.agda`

- **module**: `Sovereign.PDE.WaveEquationDiscrete`
- **行数**: 304（代码 146 / 注释 131）
- **OPTIONS**: `--rewriting`
- **导入 (6)**: `Data.Nat`, `Data.Product`, `Relation.Binary.PropositionalEquality`, `Sovereign.Base.Trit`, `Sovereign.Algebra.ProjectionDifferential`, `Sovereign.Algebra.DiscreteDE`
- **顶层签名 (17)**: `WaveState`, `sq`, `waveStep`, `kineticEnergy`, `potentialEnergy`, `totalEnergy`, `wave-const-component`, `wave-const-steady`, `wave-inverse-component`, `waveStepInverse`, `wave-left-inverse`, `wave-inverse-component₂`, `wave-right-inverse`, `kinetic-const-zero`, `potential-const-zero`, `energy-const-zero`, `wave-energy-const-conservation`
- **质量**: `refl`×75；无 postulate / 无 hole
