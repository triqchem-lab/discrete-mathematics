# A1b 瓶颈专项研究报告：Ω⁴+ 机件设计路径

> 甘特图指认：A1b = 总工期唯一瓶颈（Ω⁴+ 零命中需新工具设计——关键路径 A1→A1b→A1c 终点）
> 课题 A1 子任务（A1b→A1c 串行链）｜六节结构｜纯文档零源码｜2026-10-13
> 文末附：本地锚核实（14 锚实测）+ A1b 施工批原子分解草案（估 ~150-250 行）

---

## 一、数学对象

### 1.1 问题陈述
离散高阶同伦 π₃ᵈ（及 πₙᵈ n≥3）的**定义载体**：Ω⁴+ 迭代机件。当前迭代模式止于 3 阶：
```
Ω¹ᵈ = Walk(V,edge)(x,x)        _PPI5d:40 —— 定义相等
Ω²ᵈ = Walk(Walk,AStep)(nil,nil)  _PPI5d:52 —— 2-腔=AStep 链
Ω³ᵈ = Walk(Ω2Walk,Ω3Step)(nil2,nil2)  _PPI5f:58 —— 3-腔=填充同伦链
Ω⁴ᵈ = ???                       —— 全库零命中（实测）
```

### 1.2 迭代模式的**不变量**（从 1→2→3 阶实测提炼）
| 阶 | 载体（k 阶数据=上阶闭走） | 步关系（k+1 阶生成元） | 基点 |
|---|---|---|---|
| 1 | V G × V G（顶点） | edge | x |
| 2 | Walk G x x（闭走=数据） | AStep（slide/expand——带方向对 invAStep） | nil x |
| 3 | Ω2Walk G x w w（2-腔=数据） | Ω3Step（fill-tri 单构造子：s∘s⁻¹ 2-腔 3-可缩） | nil2 (nil x) |
| **4** | **Ω3Walk G x c c'（3-腔=数据）** | **Ω4Step（fill-tet：往返 3-腔 4-可缩）** | **refl3 (nil2 (nil x))** |

**关键不对称（设计难点定位）**：Ω2Walk 是**数据类型**（cons2 链），而 Ω3Walk 是**等价闭包**（refl3/symm3/trans3 内建）——4 阶的载体必须把「3-腔当数据」处理：3-腔的复合=trans3、3-腔的逆=symm3（**等价闭包自带逆**——这与 2 阶需显式 invAStep 不同，是 4 阶设计的**简化点**）。

---

## 二、经典路径

- **连续 Ωⁿ**：ΩⁿX = Mapₓ(Sⁿ, X)——n 阶环路空间；πₙ = π₀(ΩⁿX)；Eckmann-Hilton：Ω²X 的两个复合一致 ⟹ πₙ n≥2 阿贝尔；
- **sSet Kan**：Kan 复形的单纯同伦群——**本项目已排除**（presentation 超定红线）；
- **Barcelo A-同伦**：双分级序列（A1 报告 §2.2）——高阶 A-群 n≥2 阿贝尔（2025 猜想证明的核心结论）；
- **离散 EH**：本报告 §四的阿贝尔性预设计走 **whisk 对称化路线**（whiskL×whiskR 交换律=离散 EH 交换律）——Barcelo 双分级为对照面。

---

## 三、本地对接（代码实测锚——14 锚全验证）

| 本地件 | 锚点 | 对接 |
|---|---|---|
| 迭代模式注记（Ω^{k+1}=上阶闭走+上阶同伦生成元） | `_PPI5d:54-57` | **设计的模式依据**（本报告即其落地设计） |
| Ω2Walk 数据形（nil2/cons2 : AStep→） | `_PPI5d:44-46` | 2→3 阶的「数据」范式 |
| Ω3Step 单构造子 fill-tri（s∘s⁻¹ 3-可缩） | `_PPI5f:45-47` | **3→4 阶的 fill-tet 模板** |
| Ω3Walk 等价闭包（refl3/symm3/trans3/gen3） | `_PPI5f:50-54` | 4 阶闭包构造子形模板 |
| invAStep（slide↔expand 方向对） | `_PPI5f:40` | 2 阶显式逆 vs 3 阶 symm3 内置的对比锚 |
| Ω3Walk⁺/bub3/whisk3（扩展生成集） | `_PPI5g:55-64` | Ω4Step⁺ 的扩展范式（bub4 候选） |
| bubble-complete（气泡完备） | `_PPI5h:32` | 4 阶完备性的 3 阶基准 |
| rec₂ᵈ/elim₂ᵈ/elim2₂ᵈ（商面消去族） | `_PPI5j:57-66` | π₃ᵈ 商面的 rec/elim 模板 |
| whiskR（后缀缘饰——尊重性两变元） | `_PPI5j`（whiskR 主件） | **阿贝尔性路线的半边** |
| addL⁺/addR⁺（前/后缀作用） | `_PPI5j`（运算面） | whisk 对称化的两半 |
| TrivΩ2/TrivΩ3⁺ 判据 | `_PPT6:36-47` | at4 案的判据模板 |
| TruncAbove record（at2/at3） | `_PPT6:52-56` | **at4 字段扩展点** |
| tower-gskel/trunc-above-gskel 实例 | `_PPT6:64-69` | 4 阶实例的实例模板 |
| Ω⁴ 全库零命中 | grep 实测（'Ω4'零命中） | 瓶颈确认（立界如实） |

---

## 四、严格设计（核心——Ω⁴ 数据形四件）

### 4.1 Ω4Step（4 阶步生成元——fill-tet）
```agda
-- 3-腔之间的 4-步生成元（四面体填充）。
-- fill-tet：3-腔「h ∘ h⁻¹」（往返）4-可缩至平凡 3-腔 refl3 c。
-- 与 fill-tri 的对偶：2-圈的 3-消去 ⟶ 3-圈（往返 3-腔）的 4-消去。
data Ω4Step (G : DiGraph) (x : DiGraph.V G) :
       {w1 w2 : Walk G x x} {c c' : Ω2Walk G x w1 w2} →
       Ω3Walk G x c c' → Ω3Walk G x c c' → Set where
  fill-tet : {w1 w2 : Walk G x x} {c c' : Ω2Walk G x w1 w2}
             (h : Ω3Walk G x c c') →
             Ω4Step G x (trans3 h (symm3 h)) (refl3 c)
```
**设计要点**：①签名形状与 fill-tri 逐字对偶（指标层 +1：{w1 w2} 下再抬 {c c'}）；②「h⁻¹」由 **symm3 承载**（等价闭包自带逆——比 2 阶 invAStep 构造少一件）；③「往返 3-腔」= trans3 h (symm3 h)（**3-腔的复合是 trans3 非新构造子**——零新机件）。

### 4.2 Ω4Walk + Ω4ᵈ（等价闭包 + 闭 4-走）
```agda
data Ω4Walk (G : DiGraph) (x : DiGraph.V G) :
       {w1 w2 : Walk G x x} {c c' : Ω2Walk G x w1 w2} →
       Ω3Walk G x c c' → Ω3Walk G x c c' → Set where
  refl4  : (h : Ω3Walk G x c c') → Ω4Walk G x h h
  symm4  : Ω4Walk G x h h' → Ω4Walk G x h' h
  trans4 : Ω4Walk G x h1 h2 → Ω4Walk G x h2 h3 → Ω4Walk G x h1 h3
  gen4   : Ω4Step G x h h' → Ω4Walk G x h h'

Ω4ᵈ G x = Ω4Walk G x (refl3 (nil2 (nil x))) (refl3 (nil2 (nil x)))
```

### 4.3 π₃ᵈ 定义（商面——SetQuotient）
```agda
π₃ᵈ G x = Ω3ᵈ G x / Ω4Walkᵇ G x      -- 闭 3-腔经 4-腔同伦的商（_/_ HIT，EqRel4 包装）
```
配 rec₃ᵈ/elim₃ᵈ（rec/elim 模板照 `_PPI5j` 抄——EqRel4 包装件同 EqRel3 范式）。

### 4.4 Ω4Step⁺ 扩展（完备性候选——A1b 的完备面）
```agda
-- bub4：任意位置 3-气泡消去（bub3 的 4 阶对应——Ω4Step⁺ 三构造子族）
--   base4+ : fill-tet 基案
--   whisk4 : 前后缀缘饰保持（++2/whisk 面提升）
--   bub4   : 边界 3-圈收缩（fill-tet 的一般形）
```
**完备性候选命题（立界→施工）**：Ω4Walk⁺ 生成一切 3-腔同伦（bubble-complete 的 4 阶对应——`bubble4-complete`）。

### 4.5 阿贝尔性预设计（A1c 依赖——Eckmann-Hilton 离散形）
**路线：whisk 对称化**（Barcelo 双分级为对照）：
1. **交换律件**（核心）：`whisk-swap : whiskR (addL⁺ a b) ≡ addL⁺ b (whiskR …)`——前后缀作用交换（++2-assoc + 具体构造子分派——**可证面**，2-腔数据形直承）；
2. EH 推导骨架：π₂ᵈ 的两复合（whiskR 型/whiskL 型）经 whisk-swap 一致 ⟹ **π₂ᵈ ≅ π₃ᵈ 且阿贝尔**（连续 EH 的离散形——每步 2-3 个具名引理）；
3. **依赖链**：whisk-swap（~40-60 行）→ EH-骨架（~40 行）→ πₙᵈ n≥2 阿贝尔定理（一般形经 Ωⁿ 迭代模式泛化——A1b+ 推广面）。

### 4.6 TruncAbove 对接（at4 全形化）
```agda
TrivΩ3 G x = (p q : Ω3ᵈ G x) → Ω4Walk G x p q      -- at4 判据（全形，非 bubble 代理）
record TruncAbove … field at2/at3/**at4**           -- 字段扩展（record 加字段=下游实例补件——Gskel 侧有全证预期：Ω3ᵈ 在 Gskel two-chain 处近平凡）
```

---

## 五、诚实边界

| 类 | 项 |
|---|---|
| **可证（设计已闭合）** | Ω4Step/Ω4Walk/Ω4ᵈ 定义层（对偶模板齐）；π₃ᵈ 商面+rec/elim（模板在）；Gskel two-chain 的 4 阶实例（预期近平凡——Ω3ᵈ 面已近平凡（nil 孤立点同根），4 阶更平凡——**有把握面**）；TrivΩ3 全形判据 |
| **需新数据形** | fill-tet 的**一般位置**版（whisk4/bub4 扩展集——仿 _PPI5g 三构造）；Ω⁵+ 迭代（同模式递推——**模式已闭合，纯复制**）；whisk-swap 的完整证明（前后缀作用交换——中件面） |
| **依赖未定** | 圈长参数化↔4 阶群结构（A1 开放问题①延续）；**阿贝尔性的 EH 路线 vs Barcelo 双分级路线**孰为正解（本报告推荐 whisk 路线——机件全在+离散直承；双分级作对照）；无 uip 的 HIT 顶点型情形（_PPI4o 立界同源——Ω4Walk 是 data 非 HIT，预期无此面——注记） |

**瓶颈定性结论**：A1b 的「零命中」**不是理论空洞，是模式未展开**——迭代模式注记（_PPI5d:54-57）已给出全部结构信息，4 阶=对偶复制 + symm3/ trans3 复用（比 2→3 阶**少两件**：无 invAStep 构造、无复合新件）。**A1b 施工批 ~150-250 行可清**——甘特图的 10d 估计偏保守，实测预期 1-2 批。

---

## 六、依赖与优先

### 6.1 前置件
**全在**（零阻塞）：Ω1-3 阶全链（B1-B5 回执族）+ rec/elim 族（_PPI5j）+ EqRel3 范式（_PPI5g）+ TruncAbove 骨架（_PPT6）。

### 6.2 后续件
| 件 | 依赖 |
|---|---|
| **A1c 阿贝尔性** | **A1b 硬依赖**（whisk-swap 需 Ω4 面的 π₃ 结构）——串行链 |
| A1d 临界胞腔判据 | A1a（Sⁿᵈ 递归）——另一串 |
| πₙ 立界件（i≥4 全形/一般图对齐） | A1b |
| C1 Trakhtenbrot（TM 面） | 无关——平行 |

### 6.3 A1b 施工批原子分解草案（~150-250 行——ready）
| 原子 | 内容 | verify | 估行 |
|---|---|---|---|
| ① | Ω4Step（fill-tet）+ Ω4Walk + Ω4ᵈ 定义层 | 编译绿+构造子分派核对 | ~50 |
| ② | π₃ᵈ := Ω3ᵈ/Ω4Walkᵇ + EqRel4 + rec₃ᵈ/elim₃ᵈ | 模板对账（EqRel3 范式） | ~40 |
| ③ | Gskel two-chain 4 阶实例（预期平凡——nil 孤立点同根）+ TrivΩ3 gskel 全形 | refl 级核对 | ~40 |
| ④ | S²ᵈ 4 阶面（omega2-wit 的 4-可缩性核对——fund2 面衔接） | 与 _PPT4 k2-face-s2 对账 | ~40 |
| ⑤ | at4 字段扩展 + trunc-above-gskel 升 4 阶 | trunc₂/₃/₄ 三阶对账 | ~30 |
| ⑥（A1c 前件） | whisk-swap（前后缀交换律） | trans 链 ≤3 | ~40-60 |

**验证点**：①每原子 EXIT=0 ②Gskel/S²ᵈ 双实例核对 ③零洞零 postulate。

---

## 七、一句话

**A1b 瓶颈=模式未展开非理论空洞**——迭代模式注记（_PPI5d:54-57）已含全部结构：Ω⁴ = 对偶复制（fill-tet 单构造子 + 等价闭包四构造子），且**比 2→3 阶简化**（symm3 承载逆/trans3 承载复合——零新机件）；阿贝尔性（A1c）走 whisk 对称化路线（机件全在）；A1b 施工批 ~150-250 行、6 原子、无阻塞——**甘特 10d 估计可压缩至 1-2 批**，总工期关键路径随之缩短。

---

## 附：本地锚核实记录（14 锚实测——bash 原生 grep，零降档）
（§三表即锚定实录——Ω⁴ 零命中经 bash 原生 grep 复核；本报告零源码改动）
