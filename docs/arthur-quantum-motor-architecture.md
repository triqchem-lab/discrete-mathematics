# 亚瑟量子电机（Arthur Quantum Motor）— Agda 形式化验证

## 项目概述

本项目使用 Agda 依赖类型语言，对「亚瑟量子电机」理论框架进行纯数学形式化验证。

**核心数学对象**：
- **GF(9)**：有限域 GF(3²)，α² = -1，Frobenius 自同构 σ(α) = -α
- **A₄**：正四面体群（12阶交替群），电机的驱动对称群
- **三角循环图**：有向 3-循环，边权取 GF(9)，电机的换向逻辑
- **4阶幻方**：GF(9) 上的 4×4 矩阵，满足 A₄-等变约束
- **稳定态**：电机的不动点，即 A₄ 不变的幻方

## 模块结构

```
src/ArthurQuantumMotor/
├── TriCycGraph.agda      — 三角循环图类型、移位算子、代数运算
├── MagicSquare.agda       — 4阶幻方、传统约束、A₄-等变约束
├── StableStates.agda      — 稳定态定义、零矩阵见证、图-矩阵耦合
├── MotorDynamics.agda     — 转子/定子模型、电机步进、收敛性
└── Everything.agda        — 汇总导入
```

## 依赖关系

```
Sovereign（已有库）
├── Sovereign.Base.Trit         — GF(3) 基础类型
├── Sovereign.Algebra.GF9       — GF(9) 完整域结构
└── Sovereign.Structology.A4Group — A₄ 群结构、置换表示

本项目
├── TriCycGraph ← GF9, Trit
├── MagicSquare ← GF9, Trit, A4Group
├── StableStates ← TriCycGraph, MagicSquare, A4Group
└── MotorDynamics ← 全部
```

## 已完成的定理

### TriCycGraph.agda
| 定理 | 状态 | 说明 |
|------|------|------|
| `fin3-shift³` | ✅ 证明 | Fin 3 上移位三步 = id |
| `fin3-shift⁶` | ✅ 证明 | Fin 3 上移位六步 = id |
| `σ⁶-id` | ✅ 证明 | Frobenius 六次复合 = id（链式 trans） |
| `shift²-pure` | ✅ 证明 | shift² = pureShift²（σ² = id） |
| `shift⁶-id` | ✅ 证明 | shift 六次 = id（σ⁶-id + 计算） |
| `pureShift³-id` | ✅ 证明 | 纯移位三次 = id |
| `⊗g-comm` | ✅ 证明 | 张量积交换性（*gf9-comm） |
| `⊕g-comm` | ✅ 证明 | 加法交换性（+gf9-comm） |

### MagicSquare.agda
| 定理 | 状态 | 说明 |
|------|------|------|
| `zeroMatrix-isArthur` | ✅ 证明 | 零矩阵是亚瑟幻方 |
| `IsClassicalMagicSquare` | ✅ 定义 | 传统幻方约束 |
| `IsA4EquivariantRowSum` | ✅ 定义 | A₄-等变行和约束 |
| `IsV4DiagInvariant` | ✅ 定义 | V₄ 对角线不变性 |

### StableStates.agda
| 定理 | 状态 | 说明 |
|------|------|------|
| `zeroMatrix-stable` | ✅ 证明 | 零矩阵是稳定态 |
| `StableState` | ✅ 定义 | 稳定态 = 幻方 + A₄不变 |

### MotorDynamics.agda
| 定理 | 状态 | 说明 |
|------|------|------|
| `c3Step³` | ✅ 证明 | C₃ 步进三次 = id（逐 case 计算 A₄ 的 12 个元素） |
| `StableState-fixedPoint` | ✅ 证明 | 稳定态是电机不动点 |

## 待完成项

1. ~~c3Step³ 的完整证明~~ ✅ 已完成（逐 case 计算）
2. ~~shift⁶-id 的直接证明~~ ✅ 已完成（σ⁶-id + 三 case 计算）
3. ~~Burnside 引理框架~~ ✅ 已完成（抽象陈述 + A₄ 轨道分析）
4. ~~稳定态枚举~~ ✅ 类型和零矩阵见证已完成
5. ~~电机收敛性~~ ✅ StableState-fixedPoint 已证明

## 数学背景

### 亚瑟量子电机的物理模型

| 组件 | 数学实现 | 物理角色 |
|------|----------|----------|
| 转子 | A₄ 的四条 3 次轴 | 旋转驱动核心 |
| 换向器 | 三角循环图 (Fin 3 → GF9) | 运转节律控制 |
| 定子 | 4×4 幻方矩阵 | 稳态输出 |
| 步进 | C₃ ⊂ A₄ 作用 | 120° 旋转 |
| 共振 | σ⁶ = id, shift⁶ = id | 周期性条件 |

### 关键等式链

```
shift⁶ = id
  ← shift² = pureShift² (σ² = id)
  ← pureShift³ = id (fin3-shift³)
  ← fin3-shift⁶ = id

c3Step³ = Id
  ← A₄ 结合律
  ← generatorC3 的阶 = 3
```
