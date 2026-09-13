# 全库逐模块逐行审计记录 (Line Audit)

> 自动遍历 `src/` 下全部 `.agda` 模块（排除 `_build/`），逐行读取并提取结构化信息。

- 模块总数: **507**
- 总行数: **120505**（代码 68089 / 注释 35409）
- 全库 `refl` 出现: **27100**
- 全库 `postulate`: **90**（分布在 30 个模块）
- 全库 hole `{!!}`: **3**（分布在 3 个模块）

## 目录索引

- `src/01-electric-12d/` (2 模块, 272 行) → [01-electric-12d.md](01-electric-12d.md)
- `src/02-magnetic-24d/` (3 模块, 545 行) → [02-magnetic-24d.md](02-magnetic-24d.md)
- `src/03-neutral-144d/` (6 模块, 1390 行) → [03-neutral-144d.md](03-neutral-144d.md)
- `src/Generated/` (2 模块, 36 行) → [Generated.md](Generated.md)
- `src/Sovereign/AI/` (1 模块, 412 行) → [Sovereign_AI.md](Sovereign_AI.md)
- `src/Sovereign/Algebra/` (77 模块, 23961 行) → [Sovereign_Algebra.md](Sovereign_Algebra.md)
- `src/Sovereign/Algebra/GroupTheory/` (5 模块, 1120 行) → [Sovereign_Algebra_GroupTheory.md](Sovereign_Algebra_GroupTheory.md)
- `src/Sovereign/Algebra/Holographic/` (12 模块, 1915 行) → [Sovereign_Algebra_Holographic.md](Sovereign_Algebra_Holographic.md)
- `src/Sovereign/Algebra/Jacobian/` (15 模块, 10407 行) → [Sovereign_Algebra_Jacobian.md](Sovereign_Algebra_Jacobian.md)
- `src/Sovereign/Algebra/Lie/` (2 模块, 2159 行) → [Sovereign_Algebra_Lie.md](Sovereign_Algebra_Lie.md)
- `src/Sovereign/` (5 模块, 1544 行) → [Sovereign.md](Sovereign.md)
- `src/Sovereign/Analysis/` (34 模块, 6019 行) → [Sovereign_Analysis.md](Sovereign_Analysis.md)
- `src/Sovereign/Applied/` (40 模块, 6719 行) → [Sovereign_Applied.md](Sovereign_Applied.md)
- `src/Sovereign/Arithmetic/` (3 模块, 190 行) → [Sovereign_Arithmetic.md](Sovereign_Arithmetic.md)
- `src/Sovereign/Base/` (7 模块, 745 行) → [Sovereign_Base.md](Sovereign_Base.md)
- `src/Sovereign/Coding/` (8 模块, 6989 行) → [Sovereign_Coding.md](Sovereign_Coding.md)
- `src/Sovereign/Completeness/` (3 模块, 503 行) → [Sovereign_Completeness.md](Sovereign_Completeness.md)
- `src/Sovereign/Constitution/` (4 模块, 826 行) → [Sovereign_Constitution.md](Sovereign_Constitution.md)
- `src/Sovereign/Coupling/` (11 模块, 2802 行) → [Sovereign_Coupling.md](Sovereign_Coupling.md)
- `src/Sovereign/Density/` (2 模块, 479 行) → [Sovereign_Density.md](Sovereign_Density.md)
- `src/Sovereign/Diagnosis/` (1 模块, 259 行) → [Sovereign_Diagnosis.md](Sovereign_Diagnosis.md)
- `src/Sovereign/Engine/` (2 模块, 216 行) → [Sovereign_Engine.md](Sovereign_Engine.md)
- `src/Sovereign/Format/` (4 模块, 1067 行) → [Sovereign_Format.md](Sovereign_Format.md)
- `src/Sovereign/Geometry/` (13 模块, 1986 行) → [Sovereign_Geometry.md](Sovereign_Geometry.md)
- `src/Sovereign/HoTT/` (23 模块, 3636 行) → [Sovereign_HoTT.md](Sovereign_HoTT.md)
- `src/Sovereign/HoTT/DiscreteCubical/` (1 模块, 145 行) → [Sovereign_HoTT_DiscreteCubical.md](Sovereign_HoTT_DiscreteCubical.md)
- `src/Sovereign/MetaStructure/` (2 模块, 431 行) → [Sovereign_MetaStructure.md](Sovereign_MetaStructure.md)
- `src/Sovereign/PDE/` (4 模块, 1324 行) → [Sovereign_PDE.md](Sovereign_PDE.md)
- `src/Sovereign/Physics/` (63 模块, 13825 行) → [Sovereign_Physics.md](Sovereign_Physics.md)
- `src/Sovereign/Problem/BSD/` (11 模块, 693 行) → [Sovereign_Problem_BSD.md](Sovereign_Problem_BSD.md)
- `src/Sovereign/Problem/Hodge/` (8 模块, 353 行) → [Sovereign_Problem_Hodge.md](Sovereign_Problem_Hodge.md)
- `src/Sovereign/Problem/Kakeya/` (4 模块, 914 行) → [Sovereign_Problem_Kakeya.md](Sovereign_Problem_Kakeya.md)
- `src/Sovereign/Problem/Langlands/` (6 模块, 395 行) → [Sovereign_Problem_Langlands.md](Sovereign_Problem_Langlands.md)
- `src/Sovereign/Problem/NavierStokes/` (3 模块, 600 行) → [Sovereign_Problem_NavierStokes.md](Sovereign_Problem_NavierStokes.md)
- `src/Sovereign/Problem/PvsNP/` (11 模块, 955 行) → [Sovereign_Problem_PvsNP.md](Sovereign_Problem_PvsNP.md)
- `src/Sovereign/Problem/Riemann/` (9 模块, 1437 行) → [Sovereign_Problem_Riemann.md](Sovereign_Problem_Riemann.md)
- `src/Sovereign/Problem/YangMills/` (11 模块, 989 行) → [Sovereign_Problem_YangMills.md](Sovereign_Problem_YangMills.md)
- `src/Sovereign/Projection/` (2 模块, 198 行) → [Sovereign_Projection.md](Sovereign_Projection.md)
- `src/Sovereign/Projection/Decimal/` (2 模块, 268 行) → [Sovereign_Projection_Decimal.md](Sovereign_Projection_Decimal.md)
- `src/Sovereign/Quantum/` (5 模块, 1356 行) → [Sovereign_Quantum.md](Sovereign_Quantum.md)
- `src/Sovereign/RootMath/` (8 模块, 2261 行) → [Sovereign_RootMath.md](Sovereign_RootMath.md)
- `src/Sovereign/Structology/` (64 模块, 17478 行) → [Sovereign_Structology.md](Sovereign_Structology.md)
- `src/Sovereign/Topology/` (4 模块, 489 行) → [Sovereign_Topology.md](Sovereign_Topology.md)
- `src/Sovereign/Trust/` (1 模块, 132 行) → [Sovereign_Trust.md](Sovereign_Trust.md)
- `src/` (3 模块, 65 行) → [src.md](src.md)

## 含 postulate 的模块（与零 postulate 目标冲突，需关注）

- `src/01-electric-12d/Base.agda` → 1 postulate
- `src/01-electric-12d/DigitalRoot.agda` → 2 postulate
- `src/02-magnetic-24d/ParityViolation.agda` → 4 postulate
- `src/02-magnetic-24d/SpinTwistor.agda` → 9 postulate
- `src/02-magnetic-24d/WuXing.agda` → 1 postulate
- `src/03-neutral-144d/CartanTorsion.agda` → 5 postulate
- `src/03-neutral-144d/Entanglement.agda` → 7 postulate
- `src/03-neutral-144d/LossGain.agda` → 2 postulate
- `src/03-neutral-144d/TQ10.agda` → 4 postulate
- `src/03-neutral-144d/Zhonglv.agda` → 3 postulate
- `src/03-neutral-144d/ZhonglvClosure.agda` → 5 postulate
- `src/Generated/T6Verification.agda` → 1 postulate
- `src/Sovereign/Constitution/WindingAsymmetry.agda` → 1 postulate
- `src/Sovereign/Coupling/CartanTorsion.agda` → 8 postulate
- `src/Sovereign/Coupling/Entanglement.agda` → 3 postulate
- `src/Sovereign/Coupling/TQ10.agda` → 3 postulate
- `src/Sovereign/Coupling/Zhonglv.agda` → 3 postulate
- `src/Sovereign/Coupling/ZhonglvPhaseSync.agda` → 1 postulate
- `src/Sovereign/Density/Resonance.agda` → 1 postulate
- `src/Sovereign/Engine/QsUpdate.agda` → 1 postulate
- `src/Sovereign/Format/CRT.agda` → 1 postulate
- `src/Sovereign/HoTT/DiscreteCCHM.agda` → 2 postulate
- `src/Sovereign/Physics/QuartzPhonon.agda` → 3 postulate
- `src/Sovereign/RootMath/Base.agda` → 1 postulate
- `src/Sovereign/RootMath/EnergyGap.agda` → 7 postulate
- `src/Sovereign/Structology/Aether.agda` → 2 postulate
- `src/Sovereign/Structology/MagicSquareM4.agda` → 1 postulate
- `src/Sovereign/Structology/Platonics.agda` → 3 postulate
- `src/Sovereign/Structology/T6.agda` → 3 postulate
- `src/Sovereign/Structology/XuanwuAbsorption.agda` → 2 postulate

## 含 hole 的模块（未完成证明）

- `src/Sovereign/HoTT/CRTHarmonics.agda` → 1 hole
- `src/Sovereign/Topology/HighDimClosure.agda` → 1 hole
- `src/_rt.agda` → 1 hole
