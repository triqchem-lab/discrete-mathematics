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
| [14-fermat-proof-path.md](14-fermat-proof-path.md) | Fermat 离散投影链：依赖路线图 + 验证闸门（工程方法） | P1 |
| [15-flt-mathematical-position.md](15-flt-mathematical-position.md) | 离散基座上的 FLT：精确声明/已证定理/边界（致数学界立场文件） | P0 |
| [16-dc12-layer-adjudication.md](16-dc12-layer-adjudication.md) | DC12 论文 L0-L7 逐层裁定：哪些已证/哪些不可证 | P1 |
| [17-dc-fourier-analysis.md](17-dc-fourier-analysis.md) | DC 傅里叶分析层：特征→正交→对偶完备→Parseval 完整形式化 | P0 |
| [18-dihedral-d12-analysis.md](18-dihedral-d12-analysis.md) | D₁₂ 二面体群模块分析：数学内容/错误定位/复用绿库的修复路径 | P1 |

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

> ⚠️ 修正 (2026-09-07): 下表早期把 Dihedral/ 下 7 个未编译草稿误标 ✅。
> 真实状态: DCCharacter/DCGroup/DCCayleyGraph/NormCollapse 的绿版分别在
> Algebra/Character、Algebra/GroupTheory、Algebra/Spectral、Algebra/ 下; 
> Dihedral/ 目录的 7 个文件全部编译失败、从未进 git、无下游引用 (见 §附: Dihedral 草稿审计)。

| 模块 (绿版路径) | ? | postulate | 状态 |
|------|:-:|:---------:|:----:|
| DCCharacter (`Algebra/Character/`) | 0 | 0 | ✅ |
| DCGroup (`Algebra/GroupTheory/`) | 0 | 0 | ✅ |
| DCCayleyGraph (`Algebra/Spectral/`) | 0 | 0 | ✅ |
| NormCollapse (`Algebra/`) | 0 | 0 | ✅ |
| DihedralD12 (`Algebra/Dihedral/`) | 0 | 0 | ✅ (2026-09-07 修复入库) |
| DCTopos / ElectronCloud (`Algebra/Dihedral/`) | 0 | 0 | ✅ (2026-09-07 修复入库) |
| DiscreteMetric (`Algebra/Dihedral/`) | 0 | 0 | ✅ 重建 (损益投影真性质, 2026-09-07) |
| CayleyMetric (`Algebra/Dihedral/`) | 0 | 0 | ✅ 重建 (真字度量三公理穷举, 2026-09-07) |

## 快速导航

- **我要理解十二进制是什么** → [01-ontology.md](01-ontology.md)
- **我要看精确的类型定义** → [02-type-definitions.md](02-type-definitions.md)
- **我要理解零冥族/归零概念** → [04-zero-oblivion.md](04-zero-oblivion.md)
- **我要查证明状态** → [07-proof-status.md](07-proof-status.md)
- **我要写文档，需要术语表** → [08-terminology.md](08-terminology.md)
- **我要理解复数概念** → [09-complex-numbers.md](09-complex-numbers.md)
- **我要理解范数坍缩/勾股定理** → [10-norm-collapse.md](10-norm-collapse.md)
- **我要理解费马大定理在本框架中的定位** → [13-flt-analysis.md](13-flt-analysis.md)
- **我要看 Fermat 证明链的依赖图/验证闸门** → [14-fermat-proof-path.md](14-fermat-proof-path.md)
- **我要看致数学界的 FLT 立场声明** → [15-flt-mathematical-position.md](15-flt-mathematical-position.md)

## 新增模块（形式化文章中的新概念）

### 二面体群 D₁₂

- **文件**: `src/Sovereign/Algebra/Dihedral/DihedralD12.agda`
- **内容**: D₁₂ = DC ⋊ ⟨ρ⟩，24阶二面体群（库中首个非交换群）
- **状态**: ✅ 完成 (2026-09-07 修复入库, 0 postulate 0 hole)
  群公理归约 DC / srs=r⁻¹ 验证 / 非交换构造反例 / DC 嵌入单射
  分析见 [18-dihedral-d12-analysis.md](18-dihedral-d12-analysis.md)

### 短正合列

- **文件**: `src/Sovereign/Algebra/Dihedral/ShortExactSequence.agda`
- **内容**: 1 → C₄ → DC → F₃ → 1 (分裂)
- **状态**: ❌ 未编译草稿 (UnequalTypes GF9Star; 分裂性已有绿版
  DCGroup/群论链覆盖)

### 特征分解

- **文件**: `src/Sovereign/Algebra/Character/DCCharacter.agda`
- **内容**: DC 的特征分解 χ_(u,v)（载体 Z12Sys = ℚ(ζ₁₂)）
- **状态**: ✅ 完成 — 特征同态性(1728 refl)、正交性(156)、自内积(=12)、
  对偶完备性 Σ_k χ_k(x)·conj χ_k(y) = 12·δ_xy、conj 引理族、
  **Parseval/Plancherel**：Σ_x|f(x)|² = (1/12)·Σ_k|f̂(k)|²（0 postulate 0 hole）
  详见 [17-dc-fourier-analysis.md](17-dc-fourier-analysis.md)

### 谱理论与 Cayley 图

- **文件**: `src/Sovereign/Algebra/Spectral/DCCayleyGraph.agda`
- **内容**: DC 的 Cayley 图与谱理论
- **状态**: ⚠️ 部分编译 (ρ 自同构/邻接对称已证; 谱定理判定删除见文件裁定注释)

### 拓扑斯

- **文件**: `src/Sovereign/Algebra/Dihedral/DCTopos.agda`
- **内容**: DC 的拓扑斯结构
- **状态**: ❌ 未编译草稿 (NotInScope@74, 无下游引用)

## 新增模块

| 文件 | 内容 | 状态 |
|------|------|:----:|
| [11-type-theory-presentation.md](11-type-theory-presentation.md) | 类型论展示群：律算框架的群论基础 | ✅ |

## 严谨类型论定义

| 文件 | 内容 | 状态 |
|------|------|:----:|
| [12-rigorous-type-theory.md](12-rigorous-type-theory.md) | 律算框架类型论展示群的严谨定义 | ✅ |
| [20-dc-type-theory-positioning.md](20-dc-type-theory-positioning.md) | 杜德克时钟理论定位：守卫类型论模型 + 几何拓扑动力学 | ✅ |
