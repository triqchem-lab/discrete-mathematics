# 目录 `src/Sovereign/MetaStructure/` 逐模块审计记录

共 2 个模块。


## `src/Sovereign/MetaStructure/Nayin.agda`

- **module**: `Sovereign.MetaStructure.Nayin`
- **行数**: 281（代码 200 / 注释 53）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | Sovereign.MetaStructure.Nayin
  - 元结构层：六十甲子纳音拓扑指纹
  - 纳音是主权状态机在特定天干地支下的驻波谐波主峰拓扑指纹
  - 禁止将纳音解释为五行比喻或音律象征
- **导入 (8)**: `Data.Nat`, `Data.Fin`, `Data.Fin.Properties`, `Data.Vec`, `Relation.Binary.PropositionalEquality`, `Relation.Nullary`, `Sovereign.MetaStructure.WuXing`, `Sovereign.RootMath.DigitalRoot`
- **data 类型**: `HeavenlyStem`, `EarthlyBranch`, `NayinSound`
- **record 类型**: `JiaZi`, `NayinFingerprint`, `IsMetaphor`
- **顶层签名 (10)**: `stemToIndex`, `branchToIndex`, `allJiaZi`, `nayinToWuxing`, `mkNayinFingerprint`, `nayinPreferredHarmonic`, `DIQI_BASE`, `nayinResonanceFreq`, `stableProofIrrelevant`, `nayinFingerprintUnique`
- **质量**: `refl`×7；无 postulate / 无 hole

## `src/Sovereign/MetaStructure/WuXing.agda`

- **module**: `Sovereign.MetaStructure.WuXing`
- **行数**: 150（代码 72 / 注释 59）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | Sovereign.MetaStructure.WuXing
  - 元结构层：五行模数区定义与动力学关系
  - 核心概念：
  - 五行（火土木水金）不是物质元素，而是主权状态机在环向缠绕中的
  - **共振模数区** (Resonance Modulus Zones)。
  - 它们定义了系统演化的拓扑约束和手性倾向。
  - 【基数推导档案 — v5.3 (2026-07-03)】
  - 五行基数 (2,5,4,6,8) 非任意赋值, 有三条独立推导链:
  - 来源一: 群论 — 五种正多面体对称群 (KNOWLEDGE-DISTILLATION §1.3)
  - 火=2 → 正四面体 A₄ (order 12, C₃轨道最小模数)
  - 土=5 → 正六面体 Oₕ (order 48, 立方体对角周期)
  - 金=4 → 正十二面体 Iₕ (order 120, 五重对称基数)
  - 水=6 → 正二十面体 I (order 60, 三角面模数)
  - 木=8 → 正八面体 O (order 24, 对偶极点周期)
  - 来源二: 光谱数据锚定 (Physics/DataAnchors.agda)
  - Anchor_WuXing_TrapPist1: 木/土 = 8/5 ≡ TRAPPIST-1 行星轨道共振 (refl)
- **导入 (6)**: `Data.Nat`, `Data.Nat.DivMod`, `Data.Fin`, `Data.Vec`, `Data.Product`, `Relation.Binary.PropositionalEquality`
- **data 类型**: `WuXing`, `Chirality`
- **record 类型**: `ChiralWuXing`
- **顶层签名 (8)**: `wuXingBase`, `wuXingToIndex`, `generate`, `overcome`, `getCurrentWuXing`, `wuXingBasesCorrect`, `chiralDual`, `chiralDualInvolutive`
- **质量**: `refl`×11；无 postulate / 无 hole
