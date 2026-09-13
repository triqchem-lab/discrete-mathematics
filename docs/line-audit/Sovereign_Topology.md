# 目录 `src/Sovereign/Topology/` 逐模块审计记录

共 4 个模块。


## `src/Sovereign/Topology/CharacteristicClasses.agda`

- **module**: `Sovereign.Topology.CharacteristicClasses`
- **行数**: 115（代码 40 / 注释 50）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | Sovereign.Topology.CharacteristicClasses
  - 特征标类统一结构 (L3 深层证明)
  - 核心命题:
  - 将陈类、欧拉示性数、Betti 数统一为一个自洽的特征标类框架。
  - 证明策略:
  - §1 陈类 (Chern class)
  - §2 欧拉示性数 (Euler characteristic)
  - §3 Betti 数
  - §4 特征标类关系 (Chern = Euler, signature, etc.)
  - 全部 0 postulate, GF(3) 穷举 refl + 符号推理。
- **导入 (7)**: `Data.Nat`, `Data.Fin`, `Data.Integer`, `Data.Product`, `Relation.Binary.PropositionalEquality`, `Sovereign.HoTT.ChernClass`, `Sovereign.HoTT.ChernEulerLadder`
- **顶层签名 (11)**: `chern-number-S2`, `chern-equals-euler`, `chern-simons-discrete-val`, `euler-S2`, `euler-S3`, `euler-T6`, `t6-flat-curvature-val`, `t6-betti-middle-val`, `s2-signature-val`, `t6-signature-val`, `chern-euler-relation`
- **质量**: `refl`×2；无 postulate / 无 hole

## `src/Sovereign/Topology/DeRhamComplex.agda`

- **module**: `Sovereign.Topology.DeRhamComplex`
- **行数**: 117（代码 30 / 注释 63）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | Sovereign.Topology.DeRhamComplex
  - 离散 de Rham 复形 (L3 深层证明)
  - 核心命题:
  - 离散 de Rham 复形 d²=0 的 GF(3) 版本:
  - div∘curl = 0, curl∘grad = 0, 即 d²=0 在离散格点上成立。
  - 证明策略:
  - §1 离散微分形式 (0-形式=标量场, 1-形式=向量场, 2-形式=标量场)
  - §2 外微分算子 (grad, curl, div)
  - §3 d²=0 恒等式 (div∘curl=0, curl∘grad=0)
  - §4 de Rham 复形结构 (链复形)
  - 全部 0 postulate, GF(3) 穷举 refl + 符号推理。
- **导入 (7)**: `Data.Nat`, `Data.Fin`, `Data.Product`, `Relation.Binary.PropositionalEquality`, `Sovereign.Base.Trit`, `Sovereign.Physics.DiscreteEMField3D`, `Sovereign.Physics.DiscreteEMCore`
- **顶层签名 (4)**: `curl-grad-zero-full`, `div-curl-zero-full`, `d-squared-zero`, `de-rham-complex`
- **质量**: `refl`×2；无 postulate / 无 hole

## `src/Sovereign/Topology/HighDimClosure.agda`

- **module**: `Sovereign.Topology.HighDimClosure`
- **行数**: 144（代码 79 / 注释 36）
- **OPTIONS**: `--rewriting --guardedness --allow-unsolved-metas`
- **头部注释（数学背景）**:
  - | Sovereign.Topology.HighDimClosure
  - 拓扑学：仲吕闭合的高维几何原理与极限环面演化
  - 核心区分：
  - 1. 二维工程原理 (2D Engineering Principle):
  - 表现为算术修正 (acc * 177147 >> 16)，是对"仲吕不交" gap 的数值补偿。
  - 2. 高维几何原理 (High-Dimensional Geometric Principle):
  - 表现为纤维丛 (Fiber Bundle) 的截面跃迁。
  - 当极向缠绕 (12 步) 无法与环向缠绕 (46 周期) 对齐时，系统发生拓扑相变，
  - 跃迁至下一个高维截面，强制同步 144 与 46 的相位。
  - 极限环面原理 (Limit Torus Principle):
  - 系统的动态演化必然趋向于 144/46 的全息闭合态，这是系统的吸引子 (Attractor)。
- **导入 (11)**: `Data.Nat`, `Data.Nat.Base`, `Data.Nat.DivMod`, `Data.Integer`, `Data.Fin.Base`, `Data.Product`, `Data.Bool`, `Data.Unit`, `Data.Empty`, `Relation.Binary.PropositionalEquality`, `Sovereign.Base.Invariants`
- **record 类型**: `State`, `s`, `s`
- **顶层签名 (5)**: `isHolographicState`, `evolve`, `iterateEvolve`, `convergenceTheorem`, `project`
- **质量**: `refl`×1；⚠️ 1 hole / 2 TODO

## `src/Sovereign/Topology/HomologicalAlgebra.agda`

- **module**: `Sovereign.Topology.HomologicalAlgebra`
- **行数**: 113（代码 27 / 注释 60）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | Sovereign.Topology.HomologicalAlgebra
  - 同调代数统一结构 (L3 深层证明)
  - 核心命题:
  - 将有限链复形、同调群、边界算子统一为一个自洽的同调代数框架。
  - 证明策略:
  - §1 链复形定义 (对象 + 边界算子 + d²=0)
  - §2 同调群定义 (ker d / im d)
  - §3 离散 de Rham 同调 (grad, curl, div)
  - §4 同调不变量 (Betti 数, Euler 示性数)
  - 全部 0 postulate, GF(3) 穷举 refl + 符号推理。
- **导入 (7)**: `Data.Nat`, `Data.Fin`, `Data.Product`, `Relation.Binary.PropositionalEquality`, `Sovereign.Base.Trit`, `Sovereign.Physics.DiscreteEMField3D`, `Sovereign.Physics.DiscreteEMCore`
- **顶层签名 (4)**: `chain-complex`, `d-squared-zero`, `grad-in-ker-curl`, `curl-in-ker-div`
- **质量**: `refl`×2；无 postulate / 无 hole
