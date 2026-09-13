# 目录 `src/Sovereign/Density/` 逐模块审计记录

共 2 个模块。


## `src/Sovereign/Density/Resonance.agda`

- **module**: `Sovereign.Density.Resonance`
- **行数**: 262（代码 161 / 注释 56）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | Sovereign.Density.Resonance
  - 密度：量子共振——纳音驻波主峰的谐波筛选
  - 本质：纳音驻波主峰在地气声子谱（基频 144Hz）中的谐波筛选与拓扑相变
  - 工程锚定：候气管有效长度统一调谐至 19.271cm
- **导入 (13)**: `Cubical.Foundations.Prelude`, `Data.Nat`, `Data.Integer`, `Data.Rational`, `Data.Bool`, `Data.Unit`, `Data.Vec`, `Relation.Binary.PropositionalEquality`, `Data.Product`, `Sovereign.MetaStructure.Nayin`, `Sovereign.Density.SevenStages`, `Sovereign.RootMath.EnergyGap`, `Sovereign.Coupling.Zhonglv`
- **data 类型**: `ResonanceTriggered`, `Resonance`, `EnergyLevelTransition`, `EnergyTransfer`, `ResonanceDefinition`, `NayinStandingWaveHarmonicFiltering`
- **record 类型**: `HouQiTube`, `NayinHarmonicIsomorphism`, `ResonanceEffect`, `H2O`, `C60`, `ZengHouYiNanLu`
- **顶层签名 (19)**: `DIQI_PHONON_BASE`, `diqiPhononSpectrum`, `diqiPhononHarmonics`, `standardHouQiTube`, `tubeMatches3rdHarmonic`, `wuxingFromHarmonic`, `NanLuNayin`, `nanluIso`, `resonanceTriggersAsh`, `alpha`, `resonanceWidth`, `widthProportionalToBase`, `decoherenceTime`, `zhonglvCausesDecoherence`, `h2oC60Instance`, `c60Instance`, `zengHouYiInstance`, `noEnergyLevelTransition`, `noEnergyTransfer`
- **质量**: `refl`×13；⚠️ 1 postulate

## `src/Sovereign/Density/SevenStages.agda`

- **module**: `Sovereign.Density.SevenStages`
- **行数**: 217（代码 138 / 注释 47）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | Sovereign.Density.SevenStages
  - 密度：七阶段周期、爻变窗口、地气声子谱基频 144 Hz
  - 七阶段：空生火→火生土→土生金→金生水→水生木→木生火→入空
  - 爻变窗口：主权状态机在特定阶段的相位变化窗口
- **导入 (10)**: `Data.Nat`, `Data.Nat.Properties`, `Data.Fin`, `Data.Vec`, `Data.Integer`, `Data.Rational`, `Relation.Binary.PropositionalEquality`, `Data.Bool`, `Relation.Nullary.Decidable.Core`, `Sovereign.Coupling.Zhonglv`
- **data 类型**: `SevenStage`, `HeavenlyStem`, `EarthlyBranch`
- **record 类型**: `YaoWindow`, `JiaZi`
- **顶层签名 (17)**: `stageToNat`, `natToStage`, `nextStage`, `iterate`, `sevenStageCycle`, `isYaoWindowActive`, `yaoWindowsInCycle`, `DIQI_BASE_FREQ`, `diqiHarmonic`, `diqiHarmonics`, `alpha`, `branchPhaseToFreqMod`, `annualDiqiFreq`, `dingmaoFreq`, `guiyouFreq`, `stageToChernBits`, `sevenStageChernRelation`
- **质量**: `refl`×9；无 postulate / 无 hole
