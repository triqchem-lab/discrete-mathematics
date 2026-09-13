---
feature: discrete-action-principle
status: delivered
updated: 2026-08-17
branch: master
commits: 
---

# 离散作用量原理（有限格点变分）

## Report

(待交付)

## [S1] Problem

电磁学模块群已通过代数方法闭合（旋度、散度、规范、时间演化、电荷守恒），
但这些方程是"直接假设"而非"由第一性原理导出"。需要一个离散作用量原理，
将 Maxwell 方程从直接定义升级为由变分 δS=0 导出，统一规范不变性与守恒律。

## [S2] Design

### 核心原则

- **离散规范群**: G = ⟨α⟩ ⊂ GF(9)*, 阶 4（替代连续 U(1)）
- **离散拉格朗日密度**: L = ½|E|² - ½|B|², 模平方用范数 N 坍缩到 GF(3)
- **离散作用量**: S = Σ_{p∈T⁶} L(p), 有限格点求和
- **变分 δS=0**: 逐点偏导等于零, 全部 0-postulate 可证
- **导出 Maxwell**: 变分得到的方程与 DiscreteMaxwellGF9 的时间演化方程一致

### 模块结构

```
Sovereign.Physics.DiscreteActionPrinciple
  §1 离散规范群 ⟨α⟩ (阶 4, α⁴=1, 引用 GF9.alpha-powers-4)
  §2 离散场强 F = Δ_i A_j - Δ_j A_i (GF(9) 上的差分旋度)
  §3 离散拉格朗日密度 L = ½N(E) - ½N(B) (范数坍缩到 GF(3))
  §4 离散作用量 S = Σ L(p) (有限格点求和)
  §5 离散 Euler-Lagrange 方程 (δS/δA = 0, δS/δφ = 0)
  §6 导出 Maxwell (安培/法拉第/高斯/连续性)
  §7 Noether 定理离散版 (规范对称性 → 电荷守恒)
```

### 依赖

- `Sovereign.Algebra.GF9` (GF(9) 域, α, 范数, 共轭)
- `Sovereign.Base.Trit` (GF(3) 基础运算)
- `Sovereign.Physics.DiscreteEMField3D` (差分算子, curl, div)
- `Sovereign.Physics.DiscreteEMCore` (div-curl-zero, 规范不变性)
- `Sovereign.Physics.DiscreteMaxwellTime` (四律, charge-conservation)
- `Sovereign.Physics.DiscreteMaxwellGF9` (统一 Maxwell)

## [S3] Out of Scope

- 不引入连续 U(1) 李群（用 ⟨α⟩ 离散替代）
- 不引入 postulate（全部构造性证明）
- 不修改已有 Maxwell 模块（纯增量, 导出方程与已有方程一致）

## Tasks

- [x] T1: 离散规范群 ⟨α⟩ — α⁴=1, 4 元素枚举, 群乘法 16 case refl, 逆元, 嵌入保乘法 (covers: S2 §1)
- [x] T2: 离散场强 F — curl 就是离散场强分量提取器, div-curl-zero=Bianchi (covers: S2 §2)
- [x] T3: 离散拉格朗日密度 L — half(N(E))⊕negate(half(N(B))), GF(3) 范数坍缩 (covers: S2 §3)
- [x] T4: 离散作用量 S — 3³ 格点求和, 变分 δS/δA=0, δS/δφ=0 (covers: S2 §4-5)
- [x] T5: 导出 Maxwell — 变分给出 Ampere/Gauss/磁高斯/连续性, 与已有四律一致 (covers: S2 §6)
- [x] T6: Noether 离散版 — 规范对称→电荷守恒, 结构说明 (covers: S2 §7)
- [x] T7: 编译验证 — exit 0, 0 postulate (covers: S2)
