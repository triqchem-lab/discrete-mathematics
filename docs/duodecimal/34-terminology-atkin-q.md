# Atkin Q-analysis 术语体系——q-连通 · 正交数组 · 层级单调性

> **日期**: 2026-10-04
> **性质**: Atkin Q-analysis 术语提取——7 模块全部 100% 闭合的术语沉淀
> **来源**: Atkin (1972) "From cohomology in physics to q-connectivity" + 本库 7 模块

---

## 一、Q-analysis 基础

| 术语 | 定义 | 代码 | 来源模块 |
|---|---|---|---|
| **Q-analysis** | 单纯复形上基于共享 q-面的连通性分析 | — | Atkin (1972) |
| **p-单形** | p 维单纯形（顶点集 [v₀,...,vₚ]） | — | Atkin (1972) |
| **q-连通** | 两个 p-单形共享一个 q-面（q ≤ min(p₁,p₂)） | — | Atkin (1972) |
| **q=0 连通** | 两个单形共享一个顶点 | `QAnalysisRecord.QPathG` | AtkinQAnalysis |
| **q=1 连通** | 两个单形共享一条边 | `QAnalysisFacesInstance` | AtkinQ1, QAnalysisTwoTriangles |
| **正交数组 OA(n²,n,n+1,2)** | 拉丁方的等价物 | — | Atkin (1972) 理论 |

## 二、泛型 QAnalysis record（展示群风格）

| 术语 | 定义 | 代码 | 来源模块 |
|---|---|---|---|
| **QAnalysis** | 泛型 Q-analysis record | `record QAnalysis` | QAnalysisRecord |
| **Carrier A** | 底层对象集合 | `A : Set` | — |
| **Shared** | 共享关系（生成元用 data） | `Shared : A → A → Set` | — |
| **QPathG** | 泛型连通路径（自反传递闭包） | `data QPathG (A : Set) (Shared : ...) : A → A → Set` | QAnalysisRecord |
| **qpath-refl** | 路径自反 | `qpath-refl : ∀ a → QPathG A Shared a a` | — |
| **qpath-step** | 路径传递步 | `qpath-step : Shared a b → QPathG ... b c → QPathG ... a c` | — |

## 三、星形连通

| 术语 | 定义 | 代码 | 来源模块 |
|---|---|---|---|
| **QStarAnalysis** | 星形扩展 record（全员共享中心） | `record QStarAnalysis` | QAnalysisStar |
| **center** | 星形中心（锥顶） | `center : A` | — |
| **star** | 全员共享中心 | `star : ∀ x → Shared x center` | — |
| **McCordCore 定理 A** | 有全局最小元 ⊥ 的偏序集比较图直径 ≤ 2 | x → ⊥ → y | McCordCore |

## 四、层级单调性

| 术语 | 定义 | 代码 | 来源模块 |
|---|---|---|---|
| **qpath-mono** | 层级单调性定理：S₁ ⊆ S₀ ⟹ QPath S₁ → QPath S₀ | `qpath-mono` | QPathMonotone |
| **关系包含** | ∀ a b → S₁ a b → S₀ a b（强关系蕴含弱关系） | 函数参数 | — |
| **连通性单调递增** | 关系越强、路径越多（q=1 ⟹ q=0） | 泛型定理 | — |

## 五、实例层

| 实例 | q 层 | 载体 | 共享关系 | 状态 |
|---|---|---|---|---|
| AtkinQAnalysis | q=0 | K₃ 顶点 {v₀,v₁,v₂} | 边关系自反传递闭包 | ✅ |
| AtkinQ1 | q=1 | K₃ 边 {e₀₁,e₁₂,e₂₀} | 共享顶点 | ✅ 单类全连通 |
| QAnalysisFacesInstance | q=0 | Face3 = {F₀,F₁,F₂} | 三对共享顶点 | ✅ |
| QAnalysisTwoTriangles | q=1 | 双三角 {ΔL=[0,1,2], ΔR=[1,2,3]} | 共享边 [1,2] | ✅ 最小 q=1 |
| QAnalysisStar | 泛型 | 任意 A | 全员共享中心 | ✅ |
| QPathMonotone | 泛型 | 任意 A + 两关系 S₁⊆S₀ | 层级单调 | ✅ |

---

## 六、术语映射

| Atkin 术语 | 本框架对应 | 代码 | 本体 |
|---|---|---|---|
| q-连通 | 共享 q-面的连通路径 | `QPathG` | 投影（Atkin 1972 → 本框架） |
| 星形连通 | 锥形连通核泛化 | `QStarAnalysis` | 投影 |
| 单调性 | 关系蕴含→路径翻译 | `qpath-mono` | 投影 |
| 正交数组 | 拉丁方/试验设计 | — | — |

Atkin Q-analysis 在本框架中属于 **L4 应用投影层**——它将同伦直觉（Atkin 的原始表述）移植到单纯复形，由本框架的 GF(3) 系数代数提供基础。
