# 目录 `src/Sovereign/Constitution/` 逐模块审计记录

共 4 个模块。


## `src/Sovereign/Constitution/Boundaries.agda`

- **module**: `Sovereign.Constitution.Boundaries`
- **行数**: 167（代码 78 / 注释 63）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | Sovereign.Constitution.Boundaries
  - 宪法：范畴边界、合法转换、非法封禁
  - 核心原则：
  - 1. 范畴不可通约：五大范畴各自独立
  - 2. 缠绕数不可拆分
  - 3. 紧化非法
  - 4. 移宫转调唯一合法
  - 5. 律管与编钟隔离
  - 6. 纳音为驻波拓扑指纹
- **导入 (13)**: `Data.Empty`, `Data.Sum`, `Level`, `Data.Nat`, `Data.Integer`, `Data.List`, `Data.Product`, `Relation.Nullary`, `Relation.Binary.PropositionalEquality`, `Sovereign.Base.Trit`, `Sovereign.Structology.Winding`, `Sovereign.Coupling.LossGain`, `Sovereign.MetaStructure.WuXing`
- **data 类型**: `Category`, `DependsOn`
- **record 类型**: `IsConvertible`
- **顶层签名 (7)**: `polarToStep`, `toroidalToPhase`, `lengthToLossGain`, `wuXingToWinding`, `IsLegalTransform`, `lossGainUniqueness`, `dependsTransitive`
- **质量**: `refl`×3；无 postulate / 无 hole

## `src/Sovereign/Constitution/GroupTheoryRedLight.agda`

- **module**: `Sovereign.Constitution.GroupTheoryRedLight`
- **行数**: 168（代码 77 / 注释 55）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | Sovereign.Constitution.GroupTheoryRedLight
  - 群论红灯审查 — 六大连续统缺陷的离散修复形式化 (0 postulate)
  - 对应 docs/群论红灯审查-离散全息修复.md 的修正版映射表。
  - 六节 = 六缺陷修复; 全部引用已有定理 + 本轮补齐的 GL₂ 代表内积。
  - 诚实边界 (与审查文档一致):
  - GL₂(GF(9)) 全特征标表 (80 类 × 80 不可约, 28 主序列 + 36 尖点参数族)
  - 未完成 — 尖点不可约在 4 类代表上的取值是单位根组合 (非整数, 脚本证实),
  - 不进 ℤ-标度正交层; AutomorphicRep ≃ GaloisRep 全函子对应 = 开放命题,
  - 本模块仅承载数据级对应 (Langlands 双表), 不以断言代替证明。
- **导入 (9)**: `Data.Nat`, `Data.Product`, `Data.Integer`, `Relation.Binary.PropositionalEquality`, `Relation.Nullary`, `Data.Empty`, `Sovereign.Base.Trit`, `Sovereign.Algebra.GF9`, `Sovereign.Analysis.FiniteDynamics`
- **顶层签名 (24)**: `a4-order`, `binTet-order`, `ih-order`, `d4-order`, `gl2-order`, `finite-carriers`, `neg-gf9`, `sigma-alpha`, `sigma-not-id`, `sigma-order-2`, `frobenius-multiplicative`, `conjugation-involutive`, `_⊞_`, `_⊠_`, `orth-1-1`, `orth-1-st`, `orth-st-st`, `ps-values`, `orth-ps-ps`, `reducibility-witness`, `frobenius-period`, `frobenius-lock`, `class-structure`, `burnside-total`
- **质量**: `refl`×15；无 postulate / 无 hole

## `src/Sovereign/Constitution/PhysicalAssumptions.agda`

- **module**: `Sovereign.Constitution.PhysicalAssumptions`
- **行数**: 90（代码 7 / 注释 73）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | Sovereign.Constitution.PhysicalAssumptions
  - 物理锚定登记处（轨道 B）— 全库 postulate 三分类的集中登记
  - 依据: docs/Postulate审计报告.md 三分类 + 2026-08-14 编译器实测
  - 权威层级: Agda 编译器 > 本登记 > 各模块注释
  - 原则: 零宣称必须带范围; 物理输入是合法公理, 但必须显式登记, 不得冒充定理。
  - 三分类定义:
  - ① 机械约束: 可证但因 Agda REWRITE/跨模块路径机制无法替换 — 保留
  - ② 物理锚定: 实验常数的离散编码, 不可代数推导 — genuine bridge, 登记
  - ③ 可闭合:   数学上可证, 证明未实现 — 优先歼灭目标
  - 本模块不 import 任何物理模块（避免耦合与编译链膨胀）,
  - 仅作 grep-able 的集中登记。每个站点都必须能回答: 属于哪类? 依据是什么?
- **data 类型**: `PostulateClass`
- **质量**: `refl`×3；无 postulate / 无 hole

## `src/Sovereign/Constitution/WindingAsymmetry.agda`

- **module**: `Sovereign.Constitution.WindingAsymmetry`
- **行数**: 401（代码 270 / 注释 90）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | Sovereign.Constitution.WindingAsymmetry
  - 宪法：宇宙非对称性——源于缠绕数与泛音列公理
  - 核心论断：
  - 极向缠绕 144：不可拆分
  - 环向缠绕 46：不可约化
  - 泛音列公理：损益操作方向性不可逆
  - 对称性讨论脱离缠绕数与泛音列均属违宪
- **导入 (20)**: `Data.Nat`, `Data.Nat.DivMod`, `Data.Nat.Properties`, `Data.Integer`, `Data.Integer.Properties`, `Relation.Nullary`, `Data.Bool`, `Data.String`, `Data.Fin`, `Data.Fin.Properties`, `Relation.Binary.PropositionalEquality`, `Relation.Nullary`, `Data.Vec`, `Relation.Binary.PropositionalEquality`, `Data.Product`, `Data.Sum`, `Sovereign.Structology.Winding`, `Sovereign.Base.Lü`, `Sovereign.RootMath.LengthLattice`, `Sovereign.Coupling.LossGain`
- **data 类型**: `LegalStatement`, `IllegalStatement`
- **record 类型**: `HarmonicExponents`, `Asymmetry`, `ZhonglvPhaseSyncTriggered`, `IsLegal`
- **顶层签名 (19)**: `powNZ`, `harmonicLaw`, `applySun`, `applyYi`, `twelveLüExponents`, `sunInvertible`, `yiInvertible`, `aMonotonicallyIncreasing`, `bMonotonicallyDecreasing`, `polarPhase`, `toroidalPhase`, `phaseDifference`, `polarNotEqualToroidal`, `phaseDiffNotConstant`, `FULL_TOUR_VALUE`, `phaseAlignment`, `zhonglvModReset`, `asymmetryEvidence`, `universeAsymmetric`
- **质量**: `refl`×5；⚠️ 1 postulate
