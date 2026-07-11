# 待办清单 — 律算合一 (Sovereign) v5.5

**Date**: 2026-07-05  
**知识图谱**: `docs/cross-level/knowledge-graph-v5.5.md`  
**顶层构架**: `docs/造物法则-CREATION-LAWS.md` (= `docs/creation-law-from-gf3.md`)  
**状态**: 持续更新

---

## 优先级说明

| 标记 | 含义 | 时间框 |
|:---|:---|:---|
| 🔴 P0 | 阻断性缺口——后续工作依赖此项 | 1-2 周 |
| 🟡 P1 | 重要增强——非阻断但显著提升完整性 | 2-4 周 |
| 🟢 P2 | 优化完善——文档、交叉引用、清理 | 持续 |
| ⚪ M | 里程碑——独立研究项目 | 视资源 |

---

## P0: 阻断性缺口 (2 项)

### P0-1: A₄ 不可约表示的形式化

**文件**:  +   
**状态**: ✅ 完成  
**Agda路径A修复**: digestUnifyLog DInjectivity + buildLeftInverse open context + buildEquiv nctel=1 正确实现 + nctel>1 文档化回退  
**效果**: --cubical 下 281 警告消除, 0 warnings, 0 errors  
**剩余**: 多字段构造子 nctel>1 (Sovereign 未触发, 低优先级)

### P0-2: Platonics.agda 基数推导的构造性证明

**文件**: `src/Sovereign/Structology/Platonics.agda`  
**状态**: ⚠️ 火=2 已证明 (refl)，其余四个基数有 refl 但推导链被标记为"待形式化"  
**描述**: 当前四个基数（土=5, 金=4, 水=6, 木=8）通过 `refl` 连接到几何不变量，但从"对称群作用 → 模数 → 基数"的完整构造性推导链尚未闭合。

**需要完成**:
1. 土/O_h→5: Liouville 不可积轨道数 ← 从 O_h 群在 Z_144×Z_46 上的轨道分解导出
2. 金/I_h→4: C₅ 非平凡旋转数 ← 从 I_h 群的 C₅ 子群作用导出
3. 水/I→6: C₅ 轴数 ← 从 I 群和二十面体几何的 Orbit-Stabilizer 导出
4. 木/O→8: 面数/对偶极点周期 ← 从 O 群和八面体面结构导出  
5. 五行 a-序列 ↔ 群跃迁链的跨文件连接定理（`WuXingTransition.agda` ↔ `Platonics.agda`）

**阻断**: 造物法则第三法则（五行=手征耦合模式）缺少完整群论根基

---

## P1: 重要增强 (3 项)

### P1-1: FineStructureMapping.agda 实质性证明

**文件**: `src/Sovereign/Physics/FineStructureMapping.agda`  
**状态**: ⚠️ `NoContinuousConstants` 证明为占位符 (`allRational ≡ true`)  
**描述**: α_电 = α_律算 × (π_欧/π_全息) × 1/8 的映射关系已定义，但"所有物理量可表示为律算不变量的有理函数"的全局定理缺少实质性证明。

---

### P1-2: WuXingTransition.agda ↔ Platonics.agda 跨文件连接

**文件**: `src/Sovereign/Structology/WuXingTransition.agda`, `Platonics.agda`  
**状态**: 🔄 各自独立完整，但缺少跨文件 `refl` 桥接  
**描述**: 
- `WuXingTransition.agda` 已有 Christoffel 螺旋→a 序列的 scanl 推导 ✅
- `Platonics.agda` 已有 a 值与群阶的对应关系 ✅
- 但两者之间缺少显式的连接定理: `derivedASequence ↔ PlatonicGroup.crtProj`

---

### P1-3: LCM.agda I/O 桩恢复

**文件**: `src/Sovereign/Coupling/LCM.agda`  
**状态**: ⚠️ `packSectionToQs`/`unpackQsToSection`/`computeDiscreteCurvature`/`computeLocalChernHeuristic` 为桩实现  
**描述**: `.bak` 文件中有完整实现，仅需合并。P0 级简单度，P1 级重要性（影响数据流完整性）。

---

## P2: 优化完善 (3 项)

### P2-1: 参考文献整合
- [x] Altarelli & Feruglio (2005, 2010) 已补入造物法则文档
- [ ] 补充 SO(3) 有限子群分类的标准参考文献
- [ ] 补充 Planck 2018 CMB 数据的引用

### P2-2: 文档 INDEX 更新
- [ ] `docs/INDEX.md` 加入 v5.5 知识图谱 + 造物法则 + CMB 协议
- [ ] 每个 Agda 模块头注释标注其在 v5.5 知识图谱中的节点位置

### P2-3: M₄ CRT 桥接的 postulate 闭合
- [ ] `HoTT/M4CRTBridge.agda`: 4 个本征向量正交性 postulate 闭合
- [ ] `HoTT/T6Homotopy.agda`: toroidalHolonomy postulate 闭合

---

## 里程碑 (2 项)

### M1: π_H 与 CMB 低多极矩交叉验证 ⬜

**协议文档**: `docs/cross-level/cmb-piH-validation-protocol.md`  
**状态**: 框架已建立，待执行  
**协议**: CM-1 (46 周期), CM-2 (四极矩抑制), CM-3 (周期-6), CM-4 (偶奇不对称)  
**数据**: Planck 2018 PR3/PR4  
**意义**: 若显著 → 框架获得宇宙学独立确认；若不显著 → 框架在超视界尺度需修正

### M2: 造物法则理论白皮书独立发布 ⬜

**文档**: `docs/造物法则-CREATION-LAWS.md`  
**状态**: 内容已成熟，待格式化  
**目标**: 作为 Sovereign 框架的独立理论白皮书发布

---

## 完成记录

| 日期 | 项目 | 详情 |
|:---|:---|:---|
| 2026-07-05 | 造物法则文档 | 完整撰写，含 9 章 + 8 参考文献 |
| 2026-07-05 | 知识图谱 v5.5 | 五层依赖矩阵 + 待办清单 |
| 2026-07-05 | CMB 交叉验证协议 | 4 个协议 + 3 种结论场景 |
| 2026-07-05 | WuXingTransition 审计 | Christoffel→a-序列 scanl 推导已确认完整 |
| 2026-07-05 | 外部引用更新 | Altarelli-Feruglio (2005,2010) 已补入 |
| 2026-07-05 | creation-law-from-gf3.md | symlink 已创建 |

---

*本文件是 v5.5 知识图谱的待办追踪器。优先级和状态随工作进展持续更新。*
