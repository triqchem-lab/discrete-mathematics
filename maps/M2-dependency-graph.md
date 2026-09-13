# M2: 全域依赖关系图 (Dependency Graph)

> **自动生成** — 基于 `src/` 下 493 个 `Sovereign.*` 模块的 `import` 声明提取。
> 更新时间: 2026-08-20 (北京时间)

---

## 1. 全库依赖统计

| 指标 | 数值 |
|------|------|
| 模块总数 | **493** |
| 依赖边总数 | **1317** |
| 叶子模块（无 Sovereign 导入） | 99 |
| 根模块（不被其他模块导入） | 138 |
| 最大拓扑深度 | **7 层** |
| 平均依赖数 | 2.7 / 模块 |

## 2. 拓扑分层

> Layer 0 = 无 Sovereign 导入的叶子 → Layer 7 = 最深层依赖链

### Layer 0（99 个模块）

- **Algebra/** (10 个): `C3Orbit`, `DescendingChain`, `DigitalRootCycle`, `DivisibilityChain`, `DivisorLattice` …
- **AlgebraWrapper/**: `AlgebraWrapper`
- **Analysis/** (6 个): `ApproxBounds`, `DiscreteSpecialFunctions`, `DiscreteVariational`, `GoodnessOfFitGF3`, `RandomMatrixMoments` …
- **Applied/**: `AcousticsDiscrete`, `ThermoExtended`
- **Arithmetic/**: `MobiusPhi`, `Untrusted`
- **Base/**: `FunctionTheory`, `Invariants`, `Lü`, `Trit`
- **Coding/**: `HammingMetric`, `PigeonholeStandard`, `Trit`
- **Completeness/**: `Layer`
- **Constitution/**: `PhysicalAssumptions`
- **Coupling/**: `TrainingSoftConstraint`
- **DaYan/**: `DaYan`
- **Geometry/**: `ConformalInvariants`, `ProjectiveTransformHFM`
- **HoTT/** (8 个): `DiscreteCCHM`, `DiscreteCubical`, `Path`, `Geometry`, `M4CRTBridge` …
- **MetaStructure/**: `WuXing`
- **Physics/** (6 个): `AlphaRelation`, `DiscreteEMField`, `DiscreteEMField3D`, `EntropySpin`, `ObservabilityAngle` …
- **Problem/** (19 个): `BSDTrace`, `BSD_GF243`, `BSD_GF27`, `BSD_GF81`, `BSD_General` …
- **Projection/**: `Projection`, `Axioms`
- **RootMath/** (6 个): `AlgebraicComplex`, `Arithmetic`, `Base`, `DigitalRoot`, `Eisenstein` …
- **Structology/** (19 个): `A4Group`, `A4Orbits3`, `A4Representation`, `BinaryTetrahedral`, `BinaryTetrahedralHFM` …
- **Trust/**: `External`
- **_root/**: `_rt`, `_test_irrelevant`, `test_chiral`

### Layer 1（110 个模块）

- **Algebra/** (21 个): `ChainComplex`, `CommAlgBridge`, `DiscreteKTheory`, `DiscreteSeveralComplex`, `Duodecimal` …
- **Analysis/** (11 个): `DifferenceEq`, `DiscreteApprox`, `DiscreteCR`, `DiscreteIntegralEq`, `DiscreteMorseTheory` …
- **Applied/** (10 个): `BiologyDiscrete`, `CelestialExtended`, `CondensedMatter`, `DomainProofs`, `FluidDiscrete` …
- **Arithmetic/**: `CRTLemmas`
- **Base/**: `Axioms`, `TritOps`, `ZeroGeometry`
- **Coding/**: `FFIProtocol`, `NumericalSpec`
- **Completeness/**: `FunctorProof`
- **Coupling/**: `LCM`, `LossGain`, `ParityViolation`
- **Geometry/**: `DiscreteManifold`, `Tryte`
- **HoTT/** (7 个): `Bundle`, `CanonicityAlignment`, `ChernClass`, `EnergyGap`, `Fibration` …
- **MetaStructure/**: `Nayin`
- **Physics/** (13 个): `ChiralInterference`, `DataAnchors`, `DiscreteDiffOps`, `DiscreteEMCore`, `DiscreteLightcone` …
- **Problem/** (15 个): `BSD`, `EllipticComplex`, `KakeyaGF3`, `NSE`, `NSVortex` …
- **Projection/**: `Binary`, `Proofs`
- **Quantum/**: `Entanglement`
- **RootMath/**: `EnergyGap`
- **Structology/** (15 个): `A4OneDimHom`, `A4Representations`, `BinaryTetrahedralRepresentation`, `DynamicMagicSquare`, `FiniteTopology` …
- **Topology/**: `HighDimClosure`

### Layer 2（127 个模块）

- **Algebra/** (35 个): `AdjacencyMatrix`, `AlgGeomBridge`, `BCWDegeneracy`, `Base10Degeneration`, `BranchingRules` …
- **Analysis/** (12 个): `CauchySchwarz`, `DiscreteFourier`, `FiniteDynamics`, `FiniteInnerProduct`, `FunctionalAnalysisDiscrete` …
- **Applied/**: `AlgebraChainDeep`, `CircuitExtended`, `LeibnizGF9`, `ParticlePhysics`
- **Coding/**: `BCHGF9`, `CyclicGF27`, `ExpSquaring`
- **Constitution/**: `Boundaries`
- **Coupling/**: `TQ10`, `Zhonglv`, `ZhonglvClosure`, `ZhonglvPhaseSync`
- **Engine/**: `StateMachine`
- **Format/**: `CRT`, `TQ10`
- **Geometry/**: `ConformalCore`, `ProjectiveCore`, `TorusAlgebra`, `TorusGeometry`
- **HoTT/** (7 个): `CRTFiberWinding`, `ChernConservation`, `ChernEulerLadder`, `Connection`, `HopfConstruction` …
- **Physics/** (18 个): `DNAEncoding`, `DiscreteActionPrinciple`, `DiscreteLagrangian`, `DiscreteMaxwellTime`, `EntropySpinVerification` …
- **Problem/** (13 个): `BSD9`, `SelmerDiscrete`, `ZetaDiscrete`, `Hodge`, `KakeyaGF9` …
- **Projection/**: `Decimal`
- **Quantum/**: `Measurement`, `NoCloning`
- **RootMath/**: `LengthLattice`
- **Structology/** (16 个): `A4GroupAction`, `A4ThreeDimRep`, `Aether`, `ArthurMagicSquare`, `BinaryTetrahedralDefiningRep` …
- **T6Verification/**: `T6Verification`
- **Topology/**: `DeRhamComplex`, `HomologicalAlgebra`

### Layer 3（77 个模块）

- **Algebra/** (19 个): `AlgebraicPoleUnified`, `ChainZ3toZ12`, `ComplexProjection`, `ConsciousnessLayer`, `FrequencyDoubling` …
- **Analysis/**: `CalculusOfVariations`, `NormDiscrete`, `VertexAlgebraDiscrete`
- **Applied/** (7 个): `ControlTheory`, `EconomicsDiscrete`, `GameTheory`, `LogicCompleteness2Var`, `NeuroscienceDiscrete` …
- **Constitution/**: `GroupTheoryRedLight`, `WindingAsymmetry`
- **Coupling/**: `CartanTorsion`, `Dynamics`, `Entanglement`
- **Density/**: `SevenStages`
- **Engine/**: `QsUpdate`
- **Examples/**: `Examples`
- **HoTT/**: `CRTHarmonics`, `Equivalence`
- **Physics/** (16 个): `AtomicStandingWave`, `ClimateDynamics`, `DiscreteLagrangian3D`, `DiscreteMaxwellConservation`, `DiscreteMaxwellGF9` …
- **Problem/** (14 个): `DeligneHodge`, `KakeyaMF`, `Complexity`, `DetMul`, `Sheaf` …
- **Quantum/**: `ZeroPowerQuantum`
- **Structology/**: `BinaryTetrahedralSpectrum`, `HolographicPi`, `MagicSquare144`, `MotorStableStates`, `SL23Cayley`
- **Topology/**: `CharacteristicClasses`
- **_root/**: `CartanTorsion`

### Layer 4（38 个模块）

- **Algebra/** (9 个): `DegenerationRisk`, `DiscreteAnalysis`, `DiscreteDE`, `DiscreteJacobi`, `DiscreteLimit` …
- **Analysis/**: `HilbertDiscrete`, `NoetherTheorem`
- **Applied/**: `DeepAlgebraProofs`, `EMDiscrete`, `GRDiscrete`, `ImageProcessing`, `LinguisticsDiscrete`
- **Coupling/**: `SpinTwistor`
- **Density/**: `Resonance`
- **Diagnosis/**: `ElectricCivilization`
- **Format/**: `CRTMeasurement`
- **Geometry/**: `ProjectiveInvariants`, `TorusFourier`, `TorusGeodesic`
- **Integration/**: `Integration`
- **Physics/** (7 个): `ElectromagneticUnitBridge`, `EntropySpinBalance`, `EntropySpinQuantize`, `QuantumFieldAstrophysics`, `QuantumMotor` …
- **Problem/**: `CharPoly3`, `PvsNP_L15`
- **Structology/**: `BurnsideT6`, `MagicSquareM4`, `PlatonicTorusProjection`, `SL23Trace`, `XuanwuAbsorption`

### Layer 5（29 个模块）

- **AI/**: `Constitution`
- **Algebra/** (7 个): `RepresentationTheory`, `ClassicAnalysis`, `HomologyExact`, `jac_AutT6`, `jac_LieGroup` …
- **Applied/** (9 个): `BlackHoleWhiteHole`, `CelestialGeneticsControl`, `CommunicationDiscrete`, `CosmologyDiscrete`, `CrossDomainTheorems` …
- **Completeness/**: `CompletenessTheorem`
- **Format/**: `ModulusGeneration`
- **Geometry/**: `ProjectiveOrbit`, `ProjectiveTransform`
- **PDE/**: `ConvergenceAlignment`, `HeatEquationDiscrete`, `PDEDiscrete`, `WaveEquationDiscrete`
- **Physics/**: `LightCone`, `VectorFieldGeometricPhase`
- **Structology/**: `HolographicSpace`, `Platonics`

### Layer 6（8 个模块）

- **Algebra/**: `Master`, `PhysicalOntology`, `PlancherelTheorem`
- **Applied/**: `MetaTheorems`
- **Physics/**: `LightConeMatrix`
- **Quantum/**: `Foundation`
- **Structology/**: `HoloInformation`, `QuantumBridge`

### Layer 7（5 个模块）

- **Algebra/**: `FinalAudit`, `VortexConnections`
- **All/**: `All`
- **Applied/**: `DeepStructureProofs`, `MachineLearning`

## 3. 核心枢纽模块（被依赖最多的 20 个）

| # | 模块 | 被依赖数 | 占比 | 角色 |
|---|------|----------|------|------|
| 1 | `Sovereign.Base.Trit` | 248 | 50% | GF(3) 公理地基 |
| 2 | `Sovereign.Algebra.GF9` | 98 | 20% | GF(3²) 域 |
| 3 | `Sovereign.Structology.T6` | 38 | 8% | T⁶ 离散环面 |
| 4 | `Sovereign.Structology.Winding` | 29 | 6% | 缠绕数 |
| 5 | `Sovereign.Base.Invariants` | 28 | 6% | 拓扑不变量 |
| 6 | `Sovereign.Physics.DiscreteEMField3D` | 25 | 5% | 电磁场 3D |
| 7 | `Sovereign.Algebra.Duodecimal` | 24 | 5% | Z/12 环 |
| 8 | `Sovereign.Structology.A4Group` | 23 | 5% | A₄ 群 |
| 9 | `Sovereign.Algebra.ProjectionDifferential` | 19 | 4% | 投影微分 |
| 10 | `Sovereign.Coupling.LossGain` | 16 | 3% | 损益链 |
| 11 | `Sovereign.Algebra.Jacobian.jac_GF9Matrix` | 16 | 3% | Jacobian 矩阵 |
| 12 | `Sovereign.RootMath.DigitalRoot` | 15 | 3% | 数字根 |
| 13 | `Sovereign.RootMath.Eisenstein` | 15 | 3% | Eisenstein 整数 |
| 14 | `Sovereign.Structology.A4Representations` | 15 | 3% | A₄ 表示论 |
| 15 | `Sovereign.MetaStructure.WuXing` | 14 | 3% | 五行 |
| 16 | `Sovereign.Algebra.Jacobian.jac_Discrete` | 13 | 3% | 离散 Jacobian |
| 17 | `Sovereign.Format.CRT` | 12 | 2% | CRT 格式 |
| 18 | `Sovereign.Geometry.TorusGeometry` | 12 | 2% | 环面几何 |
| 19 | `Sovereign.Algebra.Jacobian.jac_Pigeonhole` | 11 | 2% | 鸽巢 |
| 20 | `Sovereign.Analysis.FiniteDynamics` | 11 | 2% | 有限动力学 |

## 4. 目录间依赖关系

> A → B 表示目录 A 中有模块导入目录 B 中的模块

| 源目录 | 导入的目录 |
|--------|------------|
| **AI/** | Coupling/, Diagnosis/, Projection/, RootMath/, Structology/ |
| **Algebra/** | AlgebraWrapper/, Analysis/, Applied/, Base/, Coding/, Coupling/, Format/, Geometry/, Physics/, Problem/, RootMath/, Structology/ |
| **All/** | AI/, Algebra/, Analysis/, Applied/, Arithmetic/, Base/, Coding/, Constitution/, Coupling/, Engine/, Examples/, Format/, Geometry/, HoTT/, Integration/, MetaStructure/, Physics/, Projection/, Quantum/, Structology/, Topology/ |
| **Analysis/** | Algebra/, Base/, Completeness/, Physics/, RootMath/, Structology/ |
| **Applied/** | Algebra/, Analysis/, Base/, Completeness/, Format/, Geometry/, MetaStructure/, RootMath/, Structology/ |
| **Arithmetic/** | AlgebraWrapper/ |
| **Coding/** | Algebra/, Base/, Problem/ |
| **Completeness/** | Algebra/, Base/, Structology/ |
| **Constitution/** | Algebra/, Analysis/, Base/, Coupling/, MetaStructure/, RootMath/, Structology/ |
| **Coupling/** | Base/, Coding/, Format/, MetaStructure/, RootMath/, Structology/ |
| **Density/** | Coupling/, MetaStructure/, RootMath/ |
| **Diagnosis/** | Base/, Coupling/, Projection/, Structology/ |
| **Engine/** | Base/, Coding/, Coupling/, Format/ |
| **Examples/** | Base/, Engine/, Format/ |
| **Format/** | Arithmetic/, Base/, Geometry/, RootMath/, Structology/ |
| **Geometry/** | Base/, Format/, Structology/ |
| **HoTT/** | Arithmetic/, Base/, Coding/, Coupling/, Engine/, RootMath/, Structology/ |
| **Integration/** | Base/, Coupling/, Engine/, Format/, MetaStructure/, Structology/ |
| **MetaStructure/** | RootMath/ |
| **PDE/** | Algebra/, Base/, Completeness/ |
| **Physics/** | Algebra/, Base/, Geometry/, HoTT/, Quantum/, Structology/ |
| **Problem/** | Algebra/, Base/, RootMath/, Structology/ |
| **Projection/** | Coding/ |
| **Quantum/** | Algebra/, Base/, Format/, Geometry/, RootMath/, Structology/ |
| **RootMath/** | Base/, Coupling/ |
| **Structology/** | Algebra/, Analysis/, Arithmetic/, Base/, Coupling/, Format/, MetaStructure/, Physics/, Projection/, RootMath/ |
| **T6Verification/** | Structology/ |
| **Topology/** | Base/, HoTT/, Physics/ |
| **_root/** | Coupling/, MetaStructure/, RootMath/, Structology/ |

## 5. 关键依赖链路

### 5.1 全局核心链

```
Base/Trit (GF3, Layer 0)
  ├→ Algebra/GF9 (GF3², Layer 1)  ← 被 98 个模块依赖
  │    ├→ Algebra/Duodecimal (Z/12, Layer 2)  ← 被 24 个模块依赖
  │    │    └→ GroupTheory/DuodecClock (12-clock, Layer 3)
  │    └→ Algebra/Jacobian/* (Jacobian, Layer 2-3)
  ├→ Structology/T6 (T⁶ 环面, Layer 2)  ← 被 38 个模块依赖
  │    └→ Structology/Winding (缠绕, Layer 3)  ← 被 29 个模块依赖
  │         └→ HoTT/* (同伦, Layer 4-7)
  └→ Base/Invariants (不变量, Layer 1)  ← 被 28 个模块依赖
       └→ Coupling/LossGain (损益, Layer 2)  ← 被 16 个模块依赖
            └→ Coupling/* (耦合, Layer 3-4)
```

### 5.2 Problem/ 千禧年问题依赖链

```
Algebra/GF9 + Algebra/Jacobian/* → Problem/BSD|PvsNP|Hodge|...
Structology/A4Representations → Problem/Langlands/GL2TestVectors
Structology/IhC60Vibration → Problem/YangMills/*
Algebra/GF9 + Problem/Kakeya/* → KakeyaGF3|KakeyaGF9|KakeyaPathology|KakeyaMF
```

## 6. 风险评估

### 6.1 单点故障（影响 >20 模块的节点）

| 模块 | 影响范围 | 风险等级 |
|------|----------|----------|
| `Base/Trit` | 248 模块 (50%) | 🔴 极高 — 修改需全量回归 |
| `Algebra/GF9` | 98 模块 (20%) | 🔴 高 — 证明链核心 |
| `Structology/T6` | 38 模块 (8%) | 🟡 中 — 含 REWRITE 规则 |
| `Structology/Winding` | 29 模块 (6%) | 🟡 中 |
| `Base/Invariants` | 28 模块 (6%) | 🟡 中 — 常量定义 |
| `Physics/DiscreteEMField3D` | 25 模块 (5%) | 🟡 中 |
| `Algebra/Duodecimal` | 24 模块 (5%) | 🟡 中 |
| `Structology/A4Group` | 23 模块 (5%) | 🟡 中 |

### 6.2 孤立顶节点分布（不被任何模块依赖）

| 目录 | 顶节点数 | 说明 |
|------|----------|------|
| Algebra/ | 29 | 深层代数定理 |
| Problem/ | 23 | 千禧年问题终态证明 |
| Structology/ | 18 | 结构学定理 |
| Applied/ | 15 | 应用层模块 |
| HoTT/ | 12 | 同伦类型论 |
| Analysis/ | 9 | 分析学定理 |
| Physics/ | 6 | 物理实证 |
| _root/ | 4 | — |
| Coupling/ | 4 | — |
| PDE/ | 4 | — |
| Constitution/ | 3 | — |
| Topology/ | 2 | — |
| DaYan/ | 1 | — |
| T6Verification/ | 1 | — |
| All/ | 1 | — |
| Coding/ | 1 | — |
| Completeness/ | 1 | — |
| Density/ | 1 | — |
| Projection/ | 1 | — |
| RootMath/ | 1 | — |
| Trust/ | 1 | — |

---

> 此文件由 `gen_m2.py` 自动生成，勿手动编辑。
