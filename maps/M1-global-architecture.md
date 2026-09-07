# M1: 全域架构图 (Global Architecture)

> **更新** — 基于 502 模块 / 119,086 行的当前状态。
> 更新时间: 2026-08-20 (北京时间)

---

## 1. 项目总览

| 指标 | 数值 |
|------|------|
| Agda 模块 | **502** |
| 代码行数 | **119,086**（代码 67,358 / 注释 34,955）|
| `refl` 证明 | **26,994** |
| 零 postulate 模块 | **472 (94%)** |
| Python 测试 | 29 passed |
| 编译入口 | ~~`src/Sovereign/All.agda`~~ 已取消 (2026-09-07 去聚合化, 模块独立编译) |

---

## 2. 分层架构

```
┌─────────────────────────────────────────────────────────┐
│ Problem/ (63 模块)                                       │
│   BSD / Hodge / PvsNP / Riemann / YangMills /           │
│   Langlands / NavierStokes / Kakeya / Hilbert           │
├─────────────────────────────────────────────────────────┤
│ Applied/ (40) + Physics/ (63) + PDE/ (4)                │
│   物理实证 / 电磁 / 量子化学 / 宇宙学 / 流体           │
├─────────────────────────────────────────────────────────┤
│ Analysis/ (34) + Quantum/ (5)                            │
│   泛函 / 调和 / 变分 / 概率 / 顶点代数                 │
├─────────────────────────────────────────────────────────┤
│ HoTT/ (24) + Topology/ (4)                               │
│   同伦类型论 / 陈类 / 纤维化 / 特征类                   │
├─────────────────────────────────────────────────────────┤
│ Geometry/ (13) + Coupling/ (12)                           │
│   射影 / 共形 / 环面 / 仲吕 / 损益链                   │
├─────────────────────────────────────────────────────────┤
│ Structology/ (64) + Format/ (4)                           │
│   T⁶ 环面 / 幻方 / A₄ / Burnside / CRT               │
├─────────────────────────────────────────────────────────┤
│ Algebra/ (106) — 核心代数                                │
│   GF(9)/GF(27)/GF(81)/GF(243)/GF(729)                  │
│   Jacobian(15) / Holographic(12) / Lie(2) / GroupTheory │
├─────────────────────────────────────────────────────────┤
│ RootMath/ (8) + Coding/ (8) + MetaStructure/ (2)         │
│   数字根 / Eisenstein / Hamming / 五行                   │
├─────────────────────────────────────────────────────────┤
│ Base/ (7) — 公理地基                                     │
│   Trit(GF3) / Invariants / Axioms / FunctionTheory       │
│   TritOps / Lü(十二律) / ZeroGeometry                   │
└─────────────────────────────────────────────────────────┘
```

---

## 3. 核心常量（宪法锁定）

| 常量 | 值 | 来源模块 | 语义 |
|------|----|----------|------|
| POLAR_WINDING | 144 | Base/Invariants | 极向缠绕数（不可拆分）|
| TOROIDAL_WINDING | 46 | Base/Invariants | 环向缠绕数（不可约分）|
| CHERN_NUMBER | 2 | Base/Invariants | 陈数（全局拓扑荷）|
| SOVEREIGN_LCM | 3¹¹·2¹⁶ | Base/Invariants | 主权 LCM 周期 |
| 全息 π | 144/46 | Base/Invariants | 禁止约分 |

---

## 4. ~~All.agda~~ 注册状态 (已取消)

| 状态 | 数量 | 说明 |
|------|------|------|
| 已注册 | **230** | 通过 `All.agda` 的 `open import public` |
| 未注册 | **272** | 存在于 `src/` 但未在 `All.agda` 中 |
| 历史遗留 | **11** | `01/02/03-*/` 目录下的旧版快照 |

> 未注册 ≠ 有错误。许多模块编译通过（exit=0）但尚未注册到 All.agda。

---

## 5. 命名空间结构

```
Sovereign/
├── Base/          — GF(3) 公理 + 拓扑不变量
├── Algebra/       — 有限域 + 群论 + 全息 + Jacobian + Lie
├── Structology/   — 环面 + 幻方 + A₄ + Burnside
├── Coupling/      — 仲吕 + 损益 + 宇称 + 自旋
├── Geometry/      — 射影 + 共形 + 环面几何
├── HoTT/          — 同伦 + 陈类 + 纤维 + CRT
├── Analysis/      — 泛函 + 调和 + 变分 + 概率
├── Physics/       — 电磁 + 量子 + 热力学 + 宇宙学
├── Applied/       — 工程 + 生物 + 经济 + 语言学
├── Problem/       — 七大千禧年问题 + Kakeya + Hilbert
├── Quantum/       — 量子公理 + 不可克隆 + 测量
├── PDE/           — 离散偏微分方程
├── Format/        — CRT + TQ10 格式
├── Coding/        — 编码理论 + Hamming
├── RootMath/      — 数字根 + Eisenstein + 能隙
├── MetaStructure/ — 五行 + 纳音
├── Engine/        — 主权状态机
├── Constitution/  — 宪法约束
├── Trust/         — 外部信任
├── Completeness/  — 完备性
├── Density/       — 密度
├── Diagnosis/     — 诊断
├── Projection/    — 十进制投影
├── AI/            — AI 宪法
└── Arithmetic/    — 算术引理
```

---

> 此文件手动维护，反映项目架构全景。
