# A2 研究报告：修正案 A（backtrack 生成元）与分水岭定理 v2

> 课题 A2（P0，依赖分水岭定理 ✅）｜六节结构｜2026-10-11 落盘
> 文末附「本地代码核实记录」——零源码改动（纯研究文档）

> ⚠ **2026-10-17 追记（判据层）**
> 本文档 §7.1 已在**叙述层**更正「逆律全域普适 / 分水岭整体消解」的越界措辞；
> 本轮把「分层传导」提升为**可陈述判据**：见
> `docs/plan/A2-重定位-判据层-2026-10-17.md`（A2' 内逆存在性判据、`Face` 参数、
> 三条要件 (a)分层 / (b)传导 / (c)ρ¹ 层作用、依赖序、风险 R-a..R-d）。
> 另：**π₁bt 的投影层地位**已入册 `docs/decisions/本源-投影分层-A1线-2026-10-17.md`。
> 本文档正文（§1–§7）**原样保留**，不改写历史。

> ⛔ **2026-10-19 终局裁决（台账已 `resolve`）：采 (B) 拒绝 `AStep-bt`——修正案 A 作废。**
> 依据（四条，均实测）：① 已证 `Q-AStep`（`probes/_PPI2.agda:276-280`）——AStep 两沿恒同正长
> ⇒ 正长闭走永远到不了 `nil`；backtrack 是唯一能把长度 2 减到 0 的规则，只要 `Flip G` 就存在相邻逆对
> ⇒ Q 不变量必被摧毁。② oracle 闸门（回执 `700bf9fe…`，domain=points=65 完整枚举）：`Gcmp`（自反）
> 2 类 → +backtrack 1 类；`Gskel`（无自反边）3 类 → +backtrack 1 类 ⇒ **本文档 §7.2 提出的 (C) 条件
> （「只在 `¬ Reflexive G` 上开 backtrack」）实测不成立**。③ 动机不成立：A 级定理 `Watershed.no-pi1-iso`
> （`probes/_PPI4f`，回执 `3b58a988…`）证 π₁ᵈ(Gcmp) 是 2 元幂等幺半群、`[loop]` **无逆**
> ⇒ 「补逆律」这个驱动 (A)/(C) 的前提在此 face 上数学上就是错的。④ 代码现状：`AStep-bt` 从未进入
> `src/`（DSH grep 带正对照复验）⇒ 裁定与现状一致，**零代码改动**。
> 决定性文书：`docs/decisions/无截断本源的精确陈述-2026-10-18.md` §八；台账裁决流水 `2026-10-17T18:08:00.190Z`。
> **后续路线**：逆律只能换表述（载体收窄 / 带标签移动而非消去 / 弱化为 E–H 型），倾向 (γ) 弱化
> （与 A1c2 既有结论同源）。本文档 §7.2 的「协同合并批」不再执行。

---

## 一、数学对象

### 1.1 问题陈述
**backtrack 生成元入定义后，分水岭定理如何重述？**

| 维度 | v1（现行） | v2（修正案 A 后） |
|---|---|---|
| AStep 生成集 | {slide, expand} | {slide, expand, **backtrack**} |
| Gskel 侧 π₁ᵈ | ≅ (ℕ,+)（gskel-classify 双证） | **≅ (ℤ,+)?（假设 H1，待施工）** |
| Gcmp 侧 π₁ᵈ | 2 元幂等幺半群 | 幂等障碍何在？（假设 H2） |
| 定理形 | ¬MonoidIso（双侧不同构） | **幸存性待证**（v2 两侧都变——定理内容移位） |

### 1.2 backtrack 的定义件（本地锚）
`_PPI2:229-236` 修正案立界原文：
```
(1) 逆律需 AStep 增回溯消去生成元 backtrack：
    AStep'(p ++ cons e (cons (flip e) b)) (p ++ b) —— 生成元入定义
    （豁免精化判据正解②；本体论：「带反转 A-homotopy」的标准生成集）
(2) 涟漪清单：AHomotopy 合同族（disp2-respects 等）补 backtrack 案；
    disp2 新前提「flip 权重互逆」wt x y *A wt (flip e) ≡ oneA
(3) 修补后逆律骨架（~20-40 行）：cons e p 归纳 + rev-resp 搬运 + backtrack 收口
```

---

## 二、经典路径（文献 + web 检索实证）

### 2.1 Barcelo A-理论对 backtrack 的处理（检索结论）
文献锚：
- [Babson-Barcelo-de Longueville-Laubenbacher《Homotopy theory of graphs》(zbmath 1108.05030)](https://zbmath.org/pdf/1108.05030.pdf)
- [Barcelo-Laubenbacher《Perspectives on A-theory》](https://zbmath.org/pdf/02207449.pdf)
- [离散同伦论综述（Smith 博士论文）](http://faculty.gvsu.edu/smithshe/files/MainDissertationFile.pdf)
- [几何群论笔记（对称边集在反转下封闭的实证段）](https://www.math.uni-sb.de/ag/weitze/images/Geometric_Group_TheoryI.pdf)

**核心事实**：经典 A-理论在**对称图**（digraph 每边自带反转边）上展开——回溯 = 「沿 e 走后沿 flip e 走回来」，反转边**在图中存在** ⇒ 回溯消去是 homotopy 关系的一部分 ⇒ 经典 A-群天然是群。

### 2.2 与本地 v1 的对照（本体论读法）
**v1 的幺半群现象 = 生成集缺失，非理论差异**：
- 我们现行 AStep = {slide, expand} **漏了回溯消去关系**（Barcelo 对称图中自动具备的部分）；
- 修正案 A = **补齐缺失关系回到经典生成集**（「带反转 A-homotopy」标准形——_PPI2:231 原文）；
- **因此 v1 分水岭的定理内容不失效而是移位**：它刻画的其实是「{slide,expand} 表征下的不变量」——修正后 Gskel 侧预期从 (ℕ,+) 升 (ℤ,+)（负环=反向走圈）。

---

## 三、本地对接

| 件 | 锚点 | 用途 |
|---|---|---|
| AStep' backtrack 立界 | `_PPI2:229-236` | 定义件（生成元入定义正解②） |
| π₁ᵈ/π₁ᵈ-rec/商面三律 | `_PPI2:31/38` | 商面级施工载体 |
| Gskel/Gcmp 定义 | `_PPI4:41-45` | 两案图的定义面 |
| **Flip 前提=定义级零代价**（Gskel-flip/Gcmp-flip 构造可证） | `_PPI4:49-58` | backtrack 的 flip e 有源（前提代价为零的实证） |
| MonoidIso record（presentation 最小自检） | `_PPI4:71-73` | v2 同构重述的载体 |
| 分水岭定理 v1+回执 | `_PPI4b/c`（回执 e3c0b2c0） | v2 的对照基线 |
| AStep-sk-empty（无三角判据）+ 一般化注记 | `_PPI4h:13/41` | backtrack 案的 AStep 空性对照（backtrack 后 AStep 非空！） |
| FreeAbQuotient 群律 transport-of-structure（f₀ 拉回 Trit 结构） | `Application/FreeAbQuotient:111/127/213` | **商面级逆元承载范式**（⊞ᵈ-inv 的施工范式） |

---

## 四、严格设计（研究问题四件）

### 4.1 Q① backtrack 的数学定义
**判定（基于 _PPI2:230 + 2.1 检索）**：backtrack **不是独立图生成元**——是 **AStep 关系集的新构造子**（消去关系），其合法性前提 = 图对称性（flip e 存在）。定义形：
```
AStep-back : ∀ {u} (p q : Walk G u u) (e : edge u v) →
             AHomotopy-rel (p ++w cons e (cons (flip e) q)) (p ++w q)
```
本体论：展示群「关系入定义」正解②（_PPI2 原文）——关系是同伦生成集的组成部分，非外来公理。

### 4.2 Q② 分水岭 v2 的移位（假设，待施工验证）
- **H1（Gskel 侧）**：backtrack 给出逆元素——`[loopK m]⁻¹ = [rev (loopK m)]`（反向走圈；backtrack 逐边消去）⇒ 预期 π₁ᵈ ≅ **(ℤ,+)**（v1 的 ℕ→ℤ）；
- **H2（Gcmp 侧）**：2 元幂等幺半群的幂等类 **无逆可给**（群论硬事实：群中唯一幂等元=单位元）——backtrack 只能（a）保持幂等类存在 ⇒ 幺半群依旧 ⇒ 分水岭幸存；(b) 把幂等类**坍缩**到平凡 ⇒ 平凡群 ≇ ℤ ⇒ 分水岭幸存；两支皆幸存 ⇒ **v2 定理 = ¬MonoidIso（内容升级版）**——预期形式；
- **施工件**：v2 two-chain 案（修正案 A 生成集下的两侧重新分类——~100-150 行）+ 幂等障碍的一般引理（幂等类在 backtrack 消去下的行为）。

### 4.3 Q③ 与 McCord 经典 iso 的一致性
**预期结果（张力面，A1 报告 §五同源）**：two-chain 偏序的序复形=1-单纯形（可缩）⇒ 经典 π₁(|K(X)|) = **平凡群**——McCord/Gao-Yang 侧给出**平凡**；本项目 v2 预期 **ℤ**——**两者必然不同构**。这不是矛盾而是**本体论分层**：Gao-Yang=经典拷贝（投影侧）；本项目 πₙᵈ=组合本源（v2 的 ℤ 是组合不变量）。A2 的论证义务：把「一致性」重新表述为「**对应定理**（组合本源 → 经典拷贝的投影映射及其核）」而非「同构」——与 A1 §五张力结论同向传导。

### 4.4 Q④ 涟漪传导清单（_PPI2:232-236 原文 + 补全）
| 面 | 涟漪 | 前提 |
|---|---|---|
| AHomotopy 合同族 | disp2-respects 等补 backtrack 案 | — |
| disp2（带权同伦） | 新前提「flip 权重互逆」`wt x y *A wt (flip e) ≡ oneA` | 权重系需配逆（ℕ 权重→ℤ/A 群权重——**结构性升级**） |
| 逆律 | cons e p 归纳+rev-resp+backtrack 收口；⊞ᵈ-inv = elimProp/q + cong [_] 一步 | ~20-40 行 |
| 商面级 | ⊞ᵈ-inv 良定义性 | FreeAbQuotient 范式（:111-213） |
| 下游 | πₙ-B1..B5/rec-elim 族（n≥2 商面同样补 backtrack）| 全 Ωⁿ 系涟漪 |

---

## 五、诚实边界

| 类 | 项 |
|---|---|
| **可证（已锚定）** | backtrack 定义件（_PPI2 原文）；Flip 前提零代价（_PPI4:49-58 构造可证）；涟漪清单完整 |
| **可证待施工** | 逆律骨架 ~20-40 行；H1（ℤ 分类）two-chain 案 ~100-150 行；幂等障碍一般引理 |
| **不可证/开放** | v2 定理的双侧精确分类（H2 两支谁发生=待计算）；无对称前提的一般图的 backtrack 部分消去（半对称图——新地形）；Gao-Yang 对应定理的核刻画 |
| **需新工具** | ℤ/A 群权重系（disp2 权重升级）；反向走 rev 的构造性件（rev 函数+rev-resp） |

---

## 六、依赖与优先
- **前置**：分水岭定理 v1 ✅（_PPI4b/c e3c0b2c0）；FreeAbQuotient 范式 ✅；
- **后续**：分水岭 v2 施工批（~150-250 行）→ D1 一般化（v2 后的分类面）；修正案 A 的 T1/T2/T3 触发评估（T1=对外交付需 McCord iso——v2 后的 iso 目标变 ℤ——**触发条件内容更新**）；涟漪批（disp2 权重系升级=大件独立批）；
- **推进**：施工批 = (a) backtrack AStep 定义 + 合同族涟漪 → (b) 逆律 → (c) v2 分类（H1/H2 判定）——三段。

---

## 附：本地代码核实记录（2026-10-11）
| # | 锚 | 实测 | 判 |
|---|---|---|---|
| 1 | backtrack 立界原文（AStep'/涟漪/逆律骨架） | `_PPI2:229-236` | ✓ |
| 2 | π₁ᵈ/rec 商面件 | `_PPI2:31/38` | ✓ |
| 3 | Gskel/Gcmp 定义 | `_PPI4:41-45` | ✓ |
| 4 | Flip 前提+两 flip 构造可证（零代价实证） | `_PPI4:49-58` | ✓ |
| 5 | MonoidIso record+presentation 自检 | `_PPI4:71+` | ✓ |
| 6 | AStep-sk-empty+一般化注记 | `_PPI4h:13/41` | ✓ |
| 7 | FreeAbQuotient 群律 transport 先例 | `Application/FreeAbQuotient:111/127/213` | ✓ |
| 8 | Barcelo 对称图回溯自动存在（经典 A-群=群的结构根源） | web 检索（zbmath 1108.05030/Perspectives/Smith 综述） | ✓ 检索结论 |
| 9 | 修正案 A 三触发台账 | 台账在案（T1 对外交付需 McCord iso/T2/T3） | ✓ |


---

## 七、校订注记与跨批协同（2026-10-13 晚，主台追记）

### 7.1 校订：本文档**无需修正**（错记在叙述层，不在此文档）
本报告 §1.1 表格已把 v2 写作「**幸存性待证**（H1/H2）」、§4.2 明列「两支皆幸存 ⇒ v2 定理 = ¬MonoidIso」——**从未声称**「逆律全域普适、分水岭整体消解」。该措辞出现在**会话叙述层**（进度报告/汇总），属**叙述层越界**，现予更正：
- **准确表述**：backtrack 是**新增的展示生成集 face**（关系入定义，_PPI2:229-236 正解②）；v1（无回溯 face）的分水岭定理**原样成立**（`_PPI2:301 inv-law-false` 仍是该 face 的合法否证件）；v2 是**另一 face**，其分类（H1 ℤ 侧 / H2 幂等侧）**待施工**。
- **不得混读**：v1 结论 ≠ v2 结论；两 face 的定理各自成立，互不推翻。这就是「分层传导」的准确含义（**不是**「分水岭整体消解」）。

### 7.2 协同：A2 §4.1 的 `AStep-back` 与桥件设计甲1 的 `AStep-bt` = **同一对象**
| 面 | 出处 | 定义形 |
|---|---|---|
| A2 修正案 A | 本报告 §4.1（源自 `_PPI2:230`） | `AStep-back : (p q) (e : edge u v) → AHomotopy-rel (p ++w cons e (cons (flip e) q)) (p ++w q)` |
| N₁-Pi1-PTS 桥件（甲1） | `docs/plan/N1-Pi1-PTS-bridge-design-2026-10-13.md` §二 | `bt : p ++w (cons e (cons (flip e) b)) → p ++w b`（flip 走 `SymEdge-sym`，零公理） |

**结论（避免双重定义）**：二者**逐字同形** ⇒ 应**合并为一批工**——先落 `AStep-bt`（新 face data，零改现件）→ 同批产出（a）A2 的逆律骨架（~20-40 行，`_PPI2:232` 原文锚）、（b）桥件的 `bt-collapse`（`w ++w rev w ~ᵇᵗ nil`）、（c）A2 H1/H2 分类的**两个 face 对照表**。**合并理由**：同一生成集若在两处各自定义，会立即产生「相异刚性头」式的双定义污染（dype 审计案同族）。
