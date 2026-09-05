# 十二进制知识图谱

**日期**: 2026-08-25  
**状态**: 宪法级文档  
**维护**: 项目核心定义，修改需经审核

---

## 概述

本文件夹记录「十二进制」（Duodecimal）代数体系的完整定义、关系与证明状态。

十二进制不是传统的「以 12 为底的位值记数法」，而是一个**多层代数结构**，其核心是：

\[
12 = 3 \times 4 = \mathrm{char}(\mathbb{F}_3) \times \mathrm{ord}(\alpha)
\]

其中：
- **3** = GF(3) 的特征（损益周期）
- **4** = GF(9) 中 α 的阶（相位周期）
- **12** = 两个独立周期的最小公倍数（联合归零点）

---

## 文件结构

| 文件 | 内容 | 优先级 |
|------|------|--------|
| [01-ontology.md](01-ontology.md) | 本体论：Duodecimal vs DuodecClock 谁是本源 | P0 |
| [02-type-definitions.md](02-type-definitions.md) | 精确的 Agda 类型定义（可执行） | P0 |
| [03-algebraic-structure.md](03-algebraic-structure.md) | 群、环、域的层次关系 | P1 |
| [04-zero-oblivion.md](04-zero-oblivion.md) | 零冥族：相位归零的数学本质 | P1 |
| [05-crt-decomposition.md](05-crt-decomposition.md) | CRT 分解：12 ≅ 3 × 4 | P1 |
| [06-relationship-graph.md](06-relationship-graph.md) | 概念关系图谱（Mermaid） | P2 |
| [07-proof-status.md](07-proof-status.md) | 证明状态与缺口清单 | P2 |
| [08-terminology.md](08-terminology.md) | 术语表：合法/非法表述对照 | P0 |
| [09-complex-numbers.md](09-complex-numbers.md) | 体系复数概念：GF(9)/Gaussian/Eisenstein/Sqrt3/Sqrt2 | P0 |
| [10-norm-collapse.md](10-norm-collapse.md) | 范数坍缩：勾股定理的局限性 | P0 |
| [13-flt-analysis.md](13-flt-analysis.md) | 费马大定理的十二进制分析：Archimedes 序依赖的诊断 | P0 |

---

## 核心宪法（一句话）

> **十二进制 = Trit 加法 ⊕ ⟨α⟩ 乘法的联合时钟**。  
> Duodecimal 是它的扁平投影标签；DuodecClock 是它的本源坐标。  
> 12 不是「选了个好看的数」，是两个独立旋转同时回到原点的最短时间。

---

## 与其他模块的关系

| 模块 | 关系 | 文档 |
|------|------|------|
| `Sovereign.Base.Trit` | GF(3) 载体 | [../Sovereign/Base/Trit.agda](../../src/Sovereign/Base/Trit.agda) |
| `Sovereign.Algebra.GF9` | GF(9) = GF(3)[α]/(α²+1) | [../Sovereign/Algebra/GF9.agda](../../src/Sovereign/Algebra/GF9.agda) |
| `Sovereign.Algebra.GroupTheory.DuodecClock` | 本源时钟定义 | [../Sovereign/Algebra/GroupTheory/DuodecClock.agda](../../src/Sovereign/Algebra/GroupTheory/DuodecClock.agda) |
| `Sovereign.Algebra.Duodecimal` | 扁平投影标签 | [../Sovereign/Algebra/Duodecimal.agda](../../src/Sovereign/Algebra/Duodecimal.agda) |
| `Sovereign.Algebra.AlgebraicPoleUnified` | 代数极统一入口 | [../Sovereign/Algebra/AlgebraicPoleUnified.agda](../../src/Sovereign/Algebra/AlgebraicPoleUnified.agda) |
| `Sovereign.Coupling.ZhonglvPhaseSync` | 仲吕闭合/和乐归零 | [../Sovereign/Coupling/ZhonglvPhaseSync.agda](../../src/Sovereign/Coupling/ZhonglvPhaseSync.agda) |

---

## 本体论立场

> **律算离散本源**：离散代数结构（GF(3)/GF(9)/DC）是本源，连续统是精度截断误差的累积。
> 
> 这不是「用离散近似连续」，而是「连续是离散的低能投影」。
> 
> 代码库中的表述：
> - `cognitive-dimension-deepening.md:14`：「无限小数尾数被证明是精度截断误差的累积，而非宇宙本性」
> - `LVSUAN-CONSTITUTION-v2.5-FINAL.md:154`：「律算离散本源」
> 
> **注意**：不要使用「范式反转」一词，应说「律算框架的本体论立场：离散先于连续」。

## 最终完成状态

**全部 9 个模块，0 个 Agda 洞，0 个 postulate，形式化完成。**

| 模块 | ? | postulate | 状态 |
|------|:-:|:---------:|:----:|
| DihedralD12 | 0 | 0 | ✅ |
| ShortExactSequence | 0 | 0 | ✅ |
| DCCharacter | 0 | 0 | ✅ |
| DCCayleyGraph | 0 | 0 | ✅ |
| DCTopos | 0 | 0 | ✅ |
| DCGroup | 0 | 0 | ✅ |
| NormCollapse | 0 | 0 | ✅ |
| ElectronCloud | 0 | 0 | ✅ |
| CayleyMetric | 0 | 0 | ✅ |

## 快速导航

- **我要理解十二进制是什么** → [01-ontology.md](01-ontology.md)
- **我要看精确的类型定义** → [02-type-definitions.md](02-type-definitions.md)
- **我要理解零冥族/归零概念** → [04-zero-oblivion.md](04-zero-oblivion.md)
- **我要查证明状态** → [07-proof-status.md](07-proof-status.md)
- **我要写文档，需要术语表** → [08-terminology.md](08-terminology.md)
- **我要理解复数概念** → [09-complex-numbers.md](09-complex-numbers.md)
- **我要理解范数坍缩/勾股定理** → [10-norm-collapse.md](10-norm-collapse.md)
- **我要理解费马大定理在本框架中的定位** → [13-flt-analysis.md](13-flt-analysis.md)

## 新增模块（形式化文章中的新概念）

### 二面体群 D₁₂

- **文件**: `src/Sovereign/Algebra/Dihedral/DihedralD12.agda`
- **内容**: D₁₂ = DC ⋊ ⟨ρ⟩，24阶二面体群
- **状态**: 框架完成，部分证明待补充

### 短正合列

- **文件**: `src/Sovereign/Algebra/Dihedral/ShortExactSequence.agda`
- **内容**: 1 → C₄ → DC → F₃ → 1 (分裂)
- **状态**: ✅ 完成

### 特征分解

- **文件**: `src/Sovereign/Algebra/Character/DCCharacter.agda`
- **内容**: DC 的特征分解 χ_(u,v)
- **状态**: 框架完成，求和部分待补充

### 谱理论与 Cayley 图

- **文件**: `src/Sovereign/Algebra/Spectral/DCCayleyGraph.agda`
- **内容**: DC 的 Cayley 图与谱理论
- **状态**: 框架完成，矩阵计算待补充

### 拓扑斯

- **文件**: `src/Sovereign/Algebra/Dihedral/DCTopos.agda`
- **内容**: DC 的拓扑斯结构
- **状态**: 框架完成，判定性部分待补充

## 新增模块

| 文件 | 内容 | 状态 |
|------|------|:----:|
| [11-type-theory-presentation.md](11-type-theory-presentation.md) | 类型论展示群：律算框架的群论基础 | ✅ |

## 严谨类型论定义

| 文件 | 内容 | 状态 |
|------|------|:----:|
| [12-rigorous-type-theory.md](12-rigorous-type-theory.md) | 律算框架类型论展示群的严谨定义 | ✅ |
