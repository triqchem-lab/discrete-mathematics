# 领域知识库 — 共形几何

> **创建**: 2026-07-18
> **项目**: discrete-mathematics (Sovereign)
> **框架**: T⁶ 离散环面 + GF(3) 三进制

## 来源

| 来源 | 类型 | 说明 |
|------|------|------|
| Cartan, É. (1922). "Leçons sur la géométrie des espaces de Riemann" | 理论 | 活动标架法（repère mobile）的精神起源 |
| Cartan, É. (1937). "La théorie des groupes finis et continus et la géométrie différentielle" | 理论 | 群论与几何的深层联系 |
| Klein, F. (1872). "Erlanger Programm" | 理论 | 用变换群分类几何——射影/仿射/共形/欧氏层级 |
| Schottenloher, M. (1997). "Geometrie und Symmetrie in der Physik" | 理论 | 共形群在物理中的角色 |
| `src/Sovereign/Geometry/ProjectiveCore.agda` (2026) | 代码 | 射影几何的 T⁶ 离散化模式（本项目的模板） |
| `src/Sovereign/Geometry/ConformalCore.agda` (2026) | 代码 | 共形几何的 T⁶ 离散化实现 |
| `src/Sovereign/Base/Trit.agda` (2026) | 代码 | GF(3) 三进制基础设施 |

## 关键认知点

1. **共形 ≠ 射影**：射影保持共线性，共形保持角度（内积比例）。在 GF(3) 中，由于 λ²≡1，共形变换直接保持内积不变。
2. **离散化的优势**：在 ℝ 上共形保持内积比例；在 GF(3) 上共形保持内积本身——这是有限域特有的"紧致化"。
3. **自对偶性**：GF(3) 中唯一的非平凡缩放因子 2 满足 2²≡1，因此 scale2 是 C₂（对合）。
4. **嵌入关系**：射影群 G = (C₃)³ ⋊ C₂ ⊂ Conf = (C₃)⁶ ⋊ C₂。
