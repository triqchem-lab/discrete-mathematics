# 目录 `src/Sovereign/Engine/` 逐模块审计记录

共 2 个模块。


## `src/Sovereign/Engine/QsUpdate.agda`

- **module**: `Sovereign.Engine.QsUpdate`
- **行数**: 162（代码 92 / 注释 46）
- **OPTIONS**: `--rewriting --cubical --guardedness`
- **头部注释（数学背景）**:
  - | Sovereign.Engine.QsUpdate
  - 引擎层：主权块权重 (qs) 的物理更新逻辑
  - 核心原理：
  - 将损益操作 (Loss/Gain) 映射为 30 个 Trit 的相位旋转。
  - 通过解包 -> 旋转 -> 打包 的循环，确保主权块的物理状态
  - 严格遵循律算公理的离散拓扑演化。
  - 安全性：
  - 由于 Trit 的旋转是模 3 循环 (0-1-2-0...)，
  - 任何 5 个 Trit 的组合打包后必然在 0-242 范围内。
  - 因此，更新后的 qs 永远不会落入“能隙奇点捕获区” (243-255)。
- **导入 (7)**: `Data.Vec`, `Data.Fin`, `Relation.Binary.PropositionalEquality`, `Relation.Binary.PropositionalEquality.Properties`, `Sovereign.Format.TQ10`, `Sovereign.Base.TritOps`, `Sovereign.Base.Trit`
- **顶层签名 (3)**: `updateByte`, `updateQs`, `qsCycleProperty`
- **质量**: `refl`×9；⚠️ 1 postulate

## `src/Sovereign/Engine/StateMachine.agda`

- **module**: `Sovereign.Engine.StateMachine`
- **行数**: 54（代码 42 / 注释 3）
- **OPTIONS**: `--rewriting --guardedness`
- **导入 (11)**: `Data.Nat`, `Data.Nat.Base`, `Data.Nat.DivMod`, `Data.Fin`, `Data.Vec`, `Data.Bool`, `Relation.Binary.PropositionalEquality`, `Sovereign.Coupling.LCM`, `Sovereign.Coding.Trit`, `Sovereign.Base.Axioms`, `Sovereign.Base.Invariants`
- **record 类型**: `SovereignState`
- **顶层签名 (8)**: `stepPhase`, `stepSection`, `evolve`, `stateToTQ10`, `tq10ToState`, `zhonglvTriggeredAfter12`, `gapSingularityIncreasesOnInvalidInput`, `evolvePreservesLCM`
- **质量**: `refl`×1；无 postulate / 无 hole
