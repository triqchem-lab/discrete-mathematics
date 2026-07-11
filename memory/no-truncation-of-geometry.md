---
name: no-truncation-of-geometry
description: Orbit 必须保留几何编码（T6Lattice 格点集），不能坍缩为代数商——这是 HoTT 拒绝截断的核心原则
type: project
---

## Orbit 双表示原则

`T6Lattice` 是 GF(3)⁶ 的 729 个格点，实 6 维离散环面。轨道 `Orbit x` 必须保留其**几何嵌入**——作为格点集的高维结构，不能被坍缩为纯代数商。

**两种表示，不可相互替代：**

| 定义 | 编码 | 含义 |
|------|------|------|
| `Orbit x`（几何） | `Σ T6Lattice (λ y → ∥ A4OrbitEquiv x y ∥₁)` | 可达格点的**集合**（命题截断——"是否在轨道中"是命题，不是数据） |
| `A4/Stab x`（代数） | `A4Element / CosetEquiv x` | 群元按作用结果划分的**商空间**（群论视角） |

**命题截断 `∥_∥₁` 是正确选择**——"格点 y 是否在 x 的轨道中"是命题（是/否），不是数据（以哪个群元到达）。这不是"丢信息"，是"识别类型层级"（集合 vs 命题）。

**orbit-stabilizer 定理**：`Orbit x ≃ A4/Stab x`。这是一条**待证定理**，不能通过把 Orbit 定义为 A4/Stab 来"简化"掉——那是把同构变成了定义相等，把数学定理变成了 triviality，砍掉了高维几何嵌入。

**构造性阻塞**：`∥_∥₁.rec` 需要 `isProp` 目标，但 `A4/Stab` 是 `Set`（商类型，h-level 2）。从几何轨道提取群元给代数商的正向构造（`Orbit → A4/Stab`）在构造性 Agda 中不可行——这是 PT 消除 vs Set 目标的经典张力，应标记为 postulate，不是砍掉几何定义的理由。

**Why:** 用户指出"经典代数拓扑的本质是有损压缩（截断），π₁ 把同伦类型砍到一维，同调群再丢掉非交换结构。HoTT/Cubical 的整个出发点就是拒绝这种截断。"把 `Orbit` 定义为 `A4/Stab` 将 729 个 GF(3) 格点的高维结构压扁成了符号 `[g]`——这正是项目始终反对的截断。

**How to apply:** Orbit 永远保留 `Σ T6Lattice (λ y → ∥ A4OrbitEquiv x y ∥₁)` 的几何编码。`A4/Stab` 保留独立商编码。`orbitStabilizer : Orbit x ≃ A4/Stab x` 是标记为 postulate 的待证定理——它的不可构造性来自 PT/SQ 的类型层级张力，不是数学缺口。
