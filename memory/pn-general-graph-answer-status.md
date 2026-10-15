# 「一般图答案」线 —— 状态与接手简报

> 更新：2026-10-14（本会话第 160–223 轮）｜权威仍在 `proof_dag` 台账（本文件是**人可读**投影）
> 规则戳：`r15/5c21a729`｜五模块 `_PN4`/`_PN12`/`_PN14`/`_PN15`/`_PN16` **全部 exit=0，0 洞 0 postulate**

---

## 一、这条线在证什么

**命题**：对任意图 `G`（连通、`flip` 无不动点），

```
π₁bt(G) ≅ F_{E₀ − V + 1}        （E₀ = **无向**边数）
```

**数学内容**：bt 面（backtrack 等价）的闭走类，作为群，同构于「**非树边环生成的自由群**」。

**四层作用**（人类 2026-10-14 定）：
1. 把 π₁ᵈ 特例提升为一般图统一刻画；
2. **与分水岭定理对照** ⇒ 证明 **bt 面 = 经典 π₁ 的重现**，AHomotopy 面 = 新对象 ⇒ **πₙᵈ 独立性的精确形式是 `π₁ᵈ ≠ π₁bt`**；
3. 给出显式自由基（非树边环）；
4. 作为 πₙᵈ 系列的基座。

---

## 二、依赖链与完成度

```
(T1) red-unique                [已证 _PN11]
(T3) nf-exists                 [已证 _PN12]
(T4) nontree-invariant/reflect [已证 _PN12]
SpanningTree 接口              [已证 _PN14]
字载体 word-setoid-group       [已证 _PN15]  ← 12 件，六条群定律全过
最终装配 SetoidGroupIso 8 字段 [进行中 _PN16]
```

### `SetoidGroupIso` 的 8 字段现状

| 字段 | 状态 | 备注 |
| --- | --- | --- |
| `to` / `from` | ✅ 已定义 | `from` 按裁决 Ⅳ 改为「先归约再取字」 |
| `to-cong` | ✅ **已证** | 一行 `cong`（第 185 轮） |
| `from-cong` | ✅ **已证** | 一行（第 214 轮，`setV⊤` 解锁后） |
| `from-to` | 🟡 **`from-to-A` 已按新 `to` 重推（一行）；差桥** | `from-to-A` ✅（`reduceG-cong-bt (go-orient …)`）+ `from-to-B` ✅（用 `filterE`），**但定向化与 `filterE` 不可兼容** ⇒ 待裁决 **Ⅸ** |
| `to-from` | ⬜ 未做 | 步骤 7；**新 `to` 的 `bwd` 支设计已使该支正确** ✓（不依赖 Ⅸ） |
| `to-mul` / `from-mul` | ⬜ 未做 | 需 Ⅶ 的修法 |

### 第 225–236 轮的新进展（**关键**）

| 件 | 内容 |
| --- | --- |
| **Ⅴ 完整实施** | `to` 改为**按方向映射**（`toEdgesO`）：代表 ⇒ `fwd`；**非代表 ⇒ `bwd (nontree-rep …)`** —— 我此前只做了「过滤」，漏了方向映射 ⇒ `to-from` 的 `bwd` 支才真正成立 |
| **`loop-flip`** | `loop (flip e) ≡ rev (loop e)`（3 轮 12 次；关键是**全路径** `PN12.GroupC.<name> G flip flip-invol _≟E_ setV classify`） |
| **`loop-flipE`** | 抬到 `Elem` 层（一行） |
| **`go-orient`** | 广义 `go` 引理：`go acc es ~ prodA acc (map fB es)`，`fB (fwd g)=g`、`fB (bwd g)=flipE g`；`bwd` 支用 `subst` 沿 `loop-flip` |
| **`from-to-A`（新版）** | **一行**：`reduceG-cong-bt (go-orient (nil a) …)`（旧版需四件，现已不需要） |
| **对抗验证** | `go-orient-nil` + `from-to-A-nil`（空点，定义层闭合 ✓） |
| **`from-to-cond`** | `from-to` 的**条件装配**：把 Ⅸ 压缩为**一条具名义务**（`bridge`） |
| **`step-canon`** | 桥的**逐项件**（一行 `cong`），条件于 `canon` |
| **`bridge-canon`** | 桥的**对表归纳**（`with` 三分支），条件于 `canon` ⇒ **Ⅸ (a) 证明层已完备** |

### ★★ 完整的**条件链**（Ⅸ 的字段一旦加入即全部落地）

```
Ⅸ 的字段 canon : (e) (h) → ¬ (nontree-rep st e h ≡ e) → e ≡ flipE (nontree-rep st e h)
  ⇒ step-canon    （逐项相等）                    ✅ 已证
  ⇒ bridge-canon  （对表归纳）                    ✅ 已证
  ⇒ from-to-cond 的前提填上 ⇒ 无条件 from-to      ✓
```

**⇒ 唯一遗留小缺口（已定位 + 三块工具已备齐）**：
```
`from-to-cond` 的桥用 `toEdges (reduceG (to x))`，而 `bridge-canon` 给 `toEdgesO l`
  ⇒ 需 `go (nil a) (toEdges (reduceG (to x))) ~ go (nil a) (toEdges (to x))`

★ 三块工具**已全部证成**（第 237–240 轮）：
  ① rev-append-inv : (p) → AHbt (rev p ++w p) (nil a)                  —— 一行
  ② go-cancel-rev  : (acc) (g) (es) → AHbt (go acc (bwd g ∷ fwd g ∷ es)) (go acc es)
  ③ cancel-pair    : (acc) (g) (es) → prodA acc (map fB (bwd g ∷ fwd g ∷ es)) ≈π2 prodA acc (map fB es)
     （= ② + go-orient 直接组合）

★ 剩余 crux（**唯一难点**）：把「走的 `AHbt`」转成「`go` 像的 `AHbt`」
  —— 即 `reduceG-sound : p ~ reduceG p`（`_PN12:163`）**蕴含**
     `go (nil a) (toEdges (reduceG p)) ~ go (nil a) (toEdges p)`
  —— 需对 `AHbt` 的生成方式归纳（回溯对的插入/删除），每一步用 ②/③ 消去。
  ⇒ 或用 `_PN4` 的 `bt-collapse-general`（需查其确切陈述）
```

### ★★★ 完整的证明骨架（**全部已证，只差一个字段**）

```
Ⅸ 的字段 canon : (e) (h) → ¬ (nontree-rep st e h ≡ e) → e ≡ flipE (nontree-rep st e h)
   （语义：非代表的边**恰是**其代表的 flip ⇒ flip-类恰有 2 个元素）
  ⇒ step-canon        ✅ 第 234 轮（一行 cong）
  ⇒ bridge-canon      ✅ 第 235 轮（对表归纳，with 三分支）
  ⇒ bridge-connect    ✅ 第 246 轮（缺口闭合）
  ⇒ bridge            ✅ 第 246 轮
  ⇒ from-to-canon     ✅ 第 246 轮  ⇒ **from-to ✅**（`SetoidGroupIso` 的字段之一）

缺口（toEdges∘reduceG vs toEdgesO）—— **全部已证**：
  rev-append-inv ✅（237）· go-cancel-rev ✅（239）· cancel-pair ✅（240）
  · toEdges-++ ✅（242）· go-++ ✅（242）· gen-case ✅（243）
  · go-toEdges-AHbt ✅（245，crux）· go-toEdges-reduce ✅（246）
  · bridge-connect ✅（246）· from-to-B' ✅（246）
```

### ★★ 「加字段」的精确补丁方案（4 个构造点，逐条）

```
文件 `src/_PN14.agda`：
① record `SpanningTree` 加字段：
     nontree-rep-canon : (e : PN11.Elem G)
                       → (h : ¬ IsTree (edg e))
                       → ¬ (nontree-rep e h ≡ e)
                       → e ≡ PN11.Elems.flipE G flip flip-invol (nontree-rep e h)
② `g2f-spanning`（IsTree = ⊤）⇒ `nontree-rep-canon e h _ = ⊥-elim (h tt)`
③ `spanning-from` ⇒ 新增参数 `(nrep-canon : …)` 并传给 record
④ `tree-spanning` ⇒ 新增参数 `(nrep-canon : …)` 并传给 record
⑤ `BA-spanning`（IsTree = ⊥）⇒ `⊥-elim`（非树证明不存在；h 的类型是 ⊥）
   注：`BA` 的 `IsTree = ⊥` ⇒ `nontree-rep e h` 中的 `h` 不可达 ⇒ 该字段可用
       `⊥-elim`（与 `BA-spanning` 现有的 `nontree-rep`/`nontree-rep-flips` 同款）
   ⇒ 之后 `_PN16` 里 `from-to-canon` 的前提可直接填（或用 `from-to-B'` + `bridge` 重述）
   ⇒ **from-to 无条件成立** ✓
```

**⇒ BFS 侧（`spanning-from`）该字段的来源**：`BFSConnected` 里应有「非树边的两条方向互为 flip」的信息
（或可从 `LastEdge` 的唯一性推出）；若不易，可**先按参数传入**（与 `nontree-rep-flips` 同样处理），
把 BFS 侧的证明作为**后续任务**（该字段在三处是退化的，只有 BFS 一处需实质证明）。

---

## 三、本会话已证（51 件，按类）

| 类别 | 代表 |
| --- | --- |
| **P2 核心** | `_PN4.tree-loop-uncond`、`_PN14.tree-loop-of-tree`、**`tree-spanning`（树支收口）** |
| **P2 辅助** | `toElems-snoc`、`no-edges-nil`、`∈-++ˡ`/`∈-++⁻`/`∈-singleton`、`BFSConnected` 加强、`all-edges-last` |
| **(c) 字载体** | **`word-setoid-group`**（十二件） |
| **(c) 映射** | `to-cong`、`fromW-cong`、`from-cong-word`、`go-cong`、`inv-core2`、`inv-core-bt`、**`go-cancel`**、**`go-fwd-only`** |
| **步骤 4–6** | `setV⊤`（**关键突破**）、`FG3`、**`from-cong`**、`toGen` 代表过滤（`repB`+`filterᵇ`）、`toGen=filterE`、`gen-elem-map`、`reduceG-cong-bt`、`reduceG-idem2`、**`gen-nontree-nil`**、**`from-to-B`**、`reduceG-red-id`、`fromEdges-fwd-red`、**`from-to-A`**+`from-to-A-eq` |
| **Ⅶ 基础** | `prodA-++`、`prodA-cong` |
| **oracle** | 533,418 棵 BFS 树（0 反例）；3,184,821 例两支互斥 |

---

## 四、本会话的六条**关键设计发现**（都属蓝图演进，均经人类裁决）

| # | 问题 | 裁决 | 执行 |
| --- | --- | --- | --- |
| **Ⅰ** | `SpanningTree.flip-tree` 对 BFS 树**过强**（oracle：两支严格互斥） | ✅ 删字段 | ✅ 删 + 导出定理 `SpanningTree-flip-tree` |
| Ⅱ | ~~`_·w_` 往返不可归约~~ | — | ✅ **已撤回**（我的误诊） |
| Ⅲ | ~~`Gen` 证明分量 ⇒ `decGen` 不可证~~ | — | ✅ **已解除**（改过滤式） |
| **Ⅳ** | `from-cong` 接口与可证性不匹配（曾判「需 K」） | ✅ 采纳 (C) | ✅ **`setV⊤` 可证**（匹配**证明** = 标准 J，非 K）⇒ 一行 |
| **Ⅴ** | `to-from` 在 `bwd` 支为假（`Gen` 有向 ⇒ 生成元多一倍） | ✅ 采纳 (a) | ✅ `nontree-rep`（**偏函数**）+ `toGen` 代表过滤 |
| **Ⅵ** | `from-to-B` 需 `ret a ≡ nil a` | ✅ 加字段 | ✅ `ret-base` |
| **Ⅶ** | `to-mul` 不成立（`reduceG` 是**全局**的） | ⏳ 未裁决 | 建议：`to` 改用 `prodA`（`prodA-++` 已证） |
| **Ⅷ** | ~~Ⅴ 的代表过滤与 `_PN12.filterE` 不可互换~~ | ✅ **已消解** | **Ⅴ 完整实施后自动消解**（新 `to` 用**全部**非树边 ⇒ 与 `filterE` 对齐） |
| **Ⅸ** | **定向化与 `filterE` 不可兼容**：非代表项上 `fwd x`（保 `filterE`）与 `bwd (rep x)`（保 `to-from`）**不可兼得** | ⏳ **待裁决** | 建议 (a)+(b)：加字段 `nontree-rep-canon : ¬ (nontree-rep e h ≡ e) → e ≡ flipE (nontree-rep e h)`（=「flip-类恰有 2 个元素」）+ 两半改定向版 |

---

## 五、⚠ 本会话的两条工程教训（已入册）

1. **WIP 切片不得用 `s[:i] + new`**（会丢弃其后全部内容）；且**两个边界都必须紧贴待删内容** —— 本会话**两次**因此静默丢失已证代码（编译绿灯掩盖，因未被引用）。**防御**：每轮收尾跑**符号计数核查**。
2. **`proof_dag journal resolve` 必须传具体 ts**，`last` 会命中非预期条目 —— 本会话已因此**误写 2 条**记录（更正已留档）。
3. **「某引理不可证」的结论必须用正确的写法验证过才能下** —— `setV⊤` 的「需 K」误判（匹配元素 vs 匹配证明）耽误了 20+ 轮。

---

## 六、下一步（按依赖排序）

| # | 动作 | 依赖 |
| --- | --- | --- |
| 1 | **Ⅸ 加字段**（4 个构造点，代价极小）⇒ `bridge-canon` 填上 ⇒ **无条件 `from-to`** | **Ⅸ 裁决（一句话）** |
| 1b | 遗留小缺口：`toEdges (reduceG (to x))` vs `toEdgesO l` ⇒ 需「`reduceG` 消去 vs `prodA`」引理（见上） | 1 之后 |
| 2 | `to-from`（步骤 7；新 `to` 的 `bwd` 支设计已正确 ✓，但需 `reduceG` 的深层性质 ⇒ 较难） | 无 |
| 3 | `to-mul`/`from-mul` | Ⅶ 裁决 |
| 4 | WIP 收尾：`toGen-rep`/`repB-sound`/`∈-filterᵇ`（**同一个 `with`-抽象陷阱**，统一绕法：把定义体改成无 `with` 形式） | 无（辅助件） |

## 六点五、★ 本会话（第 160–269 轮）成果与交接坐标

### 已无条件证成（`SetoidGroupIso` 8 字段中的 5 项）
```
· `to` / `from`            已定义（`from` 按裁决 Ⅳ 改为「先归约再取字」）
· `to-cong` / `from-cong`  ✅（各一行）
· `from-to`                ✅ **无条件**（裁决 Ⅸ 的字段落地后，`from-to-canon` 的前提被填上）
```

### 已落地的接口字段（`_PN14.SpanningTree`）
```
· `nontree-rep-canon`（裁决 Ⅸ）：非代表的边恰是其代表的 flip —— 四构造点全接
· `tree-flip`（与 Ⅸ 同款）：IsTree e → IsTree (flip e) —— 四构造点全接（**待人类确认**）
```

### 新增工具件（六件，全部已证）
```
· `tree-loop-flip-elem`（`_PN16`）：IsTree (flip (edg x)) → loop (edg x) ~ nil
· `filterE-ret-st`     ：ret 的边全为树 ⇒ filterE 丢空
· `++w-nil-right'`     ：本地全泛化版 `++w` 右单位（避开名字遮蔽）
· `step-nil`           ：累加器绕一圈不改变类（AHbt (step acc x) acc）
· `to-go-reduce`       ：to (go (nil a) es) ≡ to (prodA (nil a) (map fB es))
· `toEdgesO-++`        ：toEdgesO (l₁ ++ l₂) ≡ toEdgesO l₁ ++ toEdgesO l₂
```

### 已消解的四个障碍（含两个深坑）
```
① 过滤器与 from-to 的矛盾 —— 解法：被丢的项 `loop (flip e)` 由 `tree-loop-flip-elem` 证平凡
② `tree-flip` 字段缺失    —— 解法：补字段（裁决 Ⅰ 当年按 `spanning-from` 视角降为定理）
③ `++w` 右单位「隐式推不出」—— **真因是名字遮蔽**（`∀ {a b}` 遮蔽了模块的 `a`）⇒ 本地全泛化版
④ `bridge-canon` 累加器差 —— 解法：`step-nil` + `prodA-cong` + `symm-b`
```

### ★ 剩余两个字段的精确结论
```
`to-from` 与 `to-mul`/`from-mul` **是同一个结**，都需 Ⅶ（reduceG 对拼接的全局行为）。
关卡 = `toElems-toEdgesO-AHbt`（过滤器尊重 AHbt），拆为三段：
  ① `toEdgesO-++`          ✅ **已证**（一次通过）
  ② `pair-cancel`          ⬜ 三情形已析（见下）
  ③ 字级消对               ⬜（`cancel-pair` 是 prodA 层，需一次转换）

② 的三情形（rep x 与 {x, flipE x} 的关系）：
  · x 树边        ⇒ 两者同丢（`tree-flip` 字段）⇒ 两边都是 reduceG nil ✓
  · rep x = x     ⇒ 输出 fwd x , bwd x         ⇒ 相邻逆对 ✓
  · rep x = flip x ⇒ 输出 bwd(flip x), fwd(flip x) ⇒ 相邻逆对 ✓
  · rep x ∉ {x, flip x} ⇒ 被 **裁决 Ⅸ 的 `nontree-rep-canon`** 排除 ✓
★ 结论：**Ⅸ 的字段不仅服务 `from-to`，也正好是 `to-mul`/`to-from` 的关键** —— 两条线接口设计一致。
```

---

## 七、可复用的工程事实（本会话实测，避免重复踩坑）

0. **台账回执刷新**（本会话第 250–253 轮，共 **103 个节点**）：改源码 ⇒ 回执失效（预期机制）⇒ 用
   `proof_compile` 取该模块**当前**回执 → `proof_dag import` 批量 `update`（每条须带 `id` + `state` +
   `statement` + `receipt`；**若节点登记的模块与所给回执的模块不同，必须显式带 `module` 字段**，
   否则报「回执与当前源码不符」）。已刷新：`PN14` 12 / `PN16` 16 / `PN15` 22 / `PN12` 28 /
   `PN4` 9 / `PN11` 2 / `PN13` 6 / `PN10` 6 / `PN5` 2。
1. **`GC.<name>` 会命中重导出同名件** —— `GroupC` 内有 `open PN4.GenFace G flip` ⇒ 引用时用**全路径** `PN12.GroupC.<name> G flip flip-invol _≟E_ setV classify`（症状：首参被当成 `flip`，报 `Walk … 不是 edge → edge`）。**`++w-assoc` 亦然**（`PN4.GenFace.++w-assoc G flip …`）。
2. **替换必须限定行范围** —— 全局 `replace` 会误伤同名位置（本会话 3 次）。
3. **`inspect`（stdlib 2.4）**：返回**记录** `Reveal_·_is_`（非 `Σ`）；字段全名 `…Reveal_·_is_.eq`；惯用模式 `[ eq ]` **不解析**。
4. **`with`-抽象陷阱**：嵌套 `with` 使 `mem` 的类型不随 goal 归约（本会话 3 次同型）⇒ 绕法：**把定义体改成无 `with` 形式**（`if`/`filterᵇ`/先证展开引理）。
5. **`⊤` 的证明层 proof-irrelevance 可构造性证明**：匹配**证明**（`setV⊤ {tt} {tt} refl refl = refl`）是标准 J，**不是 K**；匹配**元素**才失败。
6. **定义顺序**：`go-orient` 必须在 `loop-flip` 之后；`gen-case`/`go-toEdges-AHbt` 必须在 `go-cancel`/`go-cancel-rev` 之后（否则 `NotInScope`）。
7. **★ 不用 `where` 绑定中间量** —— `where` 的绑定**不展开** ⇒ 隐式参数推不出（`gen-b` 支连碰三次的根因）；改**顶层具名引理 + 全部显式**即一次通过。
8. **嵌套 `subst` 超过 2 层时，先拆成具名中间引理再合成** —— 本会话两层（`from-to-A`）一次成功，四层（`gen-b`）连碰三次。
9. **★ 嵌套 `with` 会改写上下文里变量的类型** —— 症状：报 `UnequalTerms`，说「`t` 被期望为 `IsTree (flip (edg x))`」而实际是 `IsTree (edg x)`；试过显式端点、先捕获、`with … in eq`、隐式边参数**全无效**。
   **正解**：**每层只用一个 `with`，把内层拆成独立 helper 函数**（`toEdgesO-single-tree` 一次通过、`toEdgesO-tree-pair` 拆掉嵌套后一次通过）。
10. **`⊥-elim` 可吸收任何目标类型** —— 在不可达分支里用它收尾，**不受 `with` 抽象影响**；这是单元素版一次通过的关键。
11. **回退脚本必须用精确行范围，且回退后立即编译验证** —— 本会话有一次回退脚本锚点失效导致文件短暂红灯（已即时修复）。**判据：任何 `edit`/脚本写入后，立刻 `agda` 一次**。

---

## 八、第 160–319 轮（本会话）成果与接手坐标

### 8.1 最大成果
- **`from-to` 无条件**（`SetoidGroupIso` 字段之七）—— 从「条件版」升级为无条件。

### 8.2 两次结构性重构（均**零下游错误**）
1. **`toEdgesO`**：三层 `with` 定义 → `toEdgeO? : Elem → Maybe BEdge` + `toEdgesO = mapMaybe toEdgeO?`
   - 代价实测：全库 52 处引用中**核心消费者仅 3 处**（`to`/`to-cong`/`bridge-canon`），重构后零错误。
   - 红利：`toEdgesO-++` 从 8 行归纳 → **1 行**（`mapMaybe-++ toEdgeO?`）。
2. **`toEdgeO?` 第三层**：`with … ≟E …` → `if Dec.does (… ≟E …)`
   - 理由：`with` 形式**不可归约**（`proof_goals context` 实测给出 `with-1198 … | …` 形式）⇒ 结构性不可证。
   - 效果：逐点引理**一次通过**（此前同类引理 8 次失败）。

### 8.3 Ⅶ 第二段：20 件（全部一次通过）
- **逐点 4**：`toEdgeO?-tree` · `-tree-flip` · `-rep` · `-nonrep`
- **单元素 5**：`toEdgesO-single-tree` · `-rep` · `-nonrep` · `-nothing` · `toEdgesO-tree-pair₂`
- **分配律 1**：`toEdgesO-++`（一行版）
- **非树两元素 3**：`-pair-rep` · `-pair-nonrep` · `-pair`（统一 ⊎ 陈述）
- **前提 4**：`nontree-flipE` · `nontree-flipE'` · `rep-flipE` · `rep-flipE-nonrep`
- **中段 1**：`toEdgesO-middle-both-dropped`
- **逆对消去 2**：`pair-cancel-word-fwd` · `-bwd`（用 `FG3.one-loop` + `FG3.reduceG-cong`）
- 另：`reduceG-++`（reduceG 的拼接律）· `fromEdges-++`（2 行归纳）

### 8.4 `to-mul` 的六件齐备（仅差第一步形式）
```
reduceG-++ · toElems-++w(_PN11:61) · toEdgesO-++ · fromEdges-++ · catMaybes-++(stdlib:775) · map-++-commute(stdlib)
```
**证明链**：
```
to (p ++w q) =‹reduceG-++› fromEdges (toEdgesO (toElems (reduceG p ++w reduceG q)))
             =‹toElems-++w› …
             =‹toEdgesO-++› …
             =‹fromEdges-++› to p ++w to q
```
**⚠ 唯一缺口**：第一步 `cong` 的动机落在 `reduceG` 的**展开形式**上
（`Folded.res (reduceV p)` vs `reduceG p`）⇒ 改用 `subst`/`rewrite`。

### 8.5 12 条可复用经验（新增 4 条硬经验）
- ⑨ 嵌套 `with` 会改写上下文变量类型（`UnequalTerms` 的常见根因）
- ⑩ `⊥-elim` 可吸收任意目标（不可达分支）
- ⑪ 回退脚本须用**精确行范围**，改完立即编译
- ⑫ **`subst` 跨 `IsTree` 的动机必须显式写端点**（`{src x} {tgt x}`），否则报「端点不符」
- 另：`mapMaybe p = catMaybes ∘ map p`（stdlib 定义层）· `PN12.GroupC.<name> G flip flip-invol _≟E_ setV classify`（全参数路径）· `GC2.F.<name>`（Fold 层）· `cong-++w-left/right` 已在 `_PN16:49` 用 `G flip` 打开（裸名可用）· `reduceG-cong`/`reduceG-eq→AHbt` 是双向桥

### 8.6 接手第一条指令建议
> 接手 PN 线：读 `memory/pn-general-graph-answer-status.md` §八 与 `proof_dag brief`。
> 用 `subst`/`rewrite` 写 `to-mul`（六件齐备，链见 §8.4），然后 `to-from` → `iso-assembly`。

### 8.7 会话末段补充（第 320–331 轮）

**新增资产（保留）**：
- `to-aux` / `to-aux2`（函数抽取，零错误，定义层等值 ⇒ 消费者无感）：
  `to-aux2 l = fromEdges (toEdgesO l)`；`to-aux u = to-aux2 (toElems u)`；`to p = to-aux (reduceG p)`
- `to-aux2-++ : (l₁ l₂) → to-aux2 (l₁ ++ l₂) ≡ to-aux2 l₁ ++w to-aux2 l₂`（**一次通过**）
- `fromEdges-++ : (l₁ l₂) → fromEdges (l₁ ++ l₂) ≡ fromEdges l₁ ++w fromEdges l₂`（2 行归纳，一次通过）
- `reduceG-++ : (p q) → reduceG (p ++w q) ≡ reduceG (reduceG p ++w reduceG q)`
  （证法：`reduceG-idem` + `reduceG-cong` + `reduceG-sound` + `cong-++w-right/left` 组合）

**`to-mul` 的全部件（8 件，齐备）**：
`reduceG-++` · `toElems-++w`(_PN11:61) · `toEdgesO-++` · `fromEdges-++` · `catMaybes-++`(stdlib:775)
· `map-++-commute`(stdlib) · `to-aux2-++` · `to-cong`(_PN16:392) · `reduceG-idem`(PN12.GroupC)

**唯一障碍（纯技术）**：把 `reduceG-++ p q` 作为 `≈π2` 参数传给 `to-cong` 时，
`reduceG (reduceG p ++w reduceG q)` 的**展开不对称**（`Folded.res (reduceV p)` 出现在一边）⇒ UnequalTerms。
**建议做法**：用 `subst` 把该等式造好再传；或把 `to-cong` 逐点展开
（`to-cong u v h = cong (λ z → toEdgesO (toElems z)) h`）后手工构造链。

**关键路径记录**：
- `to-cong` 的精确签名（`_PN16:392`）：`(u v : Walk G a a) → u ≈π2 v → toEdgesO (toElems (reduceG u)) ≡ toEdgesO (toElems (reduceG v))`
  ⇒ 即 **`to` 对 `≈π2` 相容** —— 这正是 `to-mul` 的核心。
- `PN12.GroupC.<name> G flip flip-invol _≟E_ setV classify`（全参数路径）；`GC2.F.<name>`（Fold 层）；
  `cong-++w-left/right` 已在 `_PN16:49` 用 `G flip` 打开（裸名可用）。

**本会话新增第 13 条经验**：**抽具名纯函数治「展开不对称」——但只治最外层一层**
（`to-aux`/`to-aux2` 使 `to-mul` 第一步通过，第二步仍失败）。

### 8.8 两条战线的最终坐标（第 337–342 轮）

**战线 A：`to-mul`（8 件齐备）**
- 陈述：`to (p ++w q) ≡ to p ++w to q`（`Walk (BA Gen)` 的群运算就是 `++w`）
- 件：`reduceG-++` · `toElems-++w` · `toEdgesO-++` · `fromEdges-++` · `catMaybes-++` · `map-++-commute` · `to-aux2-++` · `to-cong`(_PN16:392)
- **障碍（纯技术）**：把 `reduceG-++ p q` 作为 `≈π2` 参数传给 `to-cong` 时，`reduceG (reduceG p ++w reduceG q)` 的展开不对称（`Folded.res (reduceV p)` 只在一侧）⇒ `UnequalTerms`。
- 建议：用 `subst` 把该等式造好再传；或把 `to-cong` 逐点展开（`to-cong u v h = cong (λ z → toEdgesO (toElems z)) h`）后手工构造链。

**战线 B：`from-mul`（四件就位 + 三步已定）**
- 陈述：`from (x ++w y) ≈π2 (from x) ⊛ (from y)`（`⊛` = `_PN12` 的 `reduceG (p ++w q)`）
- 件：`FG3-reduceG-++`（**本轮新增，一次通过**）· `toEdges-++`(_PN16:919，已有) · `go-++`(_PN16:924，已有) · `go-cong`(_PN16:368，已有)
- 三步已定（试写验证）：
  `cong (λ z → reduceG (go (nil a) (toEdges z))) (FG3-reduceG-++ x y)`
  `cong (λ z → reduceG (go (nil a) z)) (toEdges-++ …)`
  `cong reduceG (go-++ (nil a) …)`
- **末步工具（已确认）**：`go-orient acc es : AHbt (go acc es) (prodA acc (map fB es))` + `prodA-hom`（_PN16 已有）
- **位置**：`from-mul` 必须放在 `toEdges-++`(:919) **之后**
- **已排除的错路**：`go-fromEdges : AHbt (go acc es) (acc ++w fromEdges es)` —— **图不匹配**
  （`fromEdges` 属 `BA Gen`，顶点 `⊤`；`go` 属 `G`，顶点 `G.V`）

**关键 API（本会话试出）**：
- `PN12.GroupC.<name> G flip flip-invol _≟E_ setV classify`（全参数路径）
- `FG3.F.<name>` / `GC2.F.<name>`（Fold 层）；`FG3.reduceG-cong` / `FG3.one-loop`（裸名可用）
- `cong-++w-left/right` 已在 `_PN16:49` 用 `G flip` 打开（裸名可用）；用 `(PN15.BA Gen) PN15.flip-BA` 形式可作用于 `BA Gen`
- `reduceG-cong` / `reduceG-eq→AHbt`（`_PN12` 的双向桥）；`reduceG-idem`（`PN12.GroupC`）

### 8.9 `to-mul` 的根本障碍与解法（第 345–351 轮，**最重要的一条**）

**根本障碍**：`reduceG` 的展开**贯穿多层**（`reduceG` → `PN12.Fold.Folded.res` → `reduceV`），
导致任何 `cong` / `subst` / `rewrite` 施加 `reduceG-++` 时都报 `UnequalTerms`
（典型报错项：`PN12.Fold.Folded.res (GC2.F.reduceV p) ++w GC2.F.reduceG q`）。
**已穷尽的形式方案（全部失败）**：`cong`（正/反向）· `subst` · `rewrite` · 两次 `to-cong` ·
抽具名纯函数（`to-aux`/`to-aux2`，只治最外层一层）· 包装 `reduceG-++` · generalize · 改陈述形式。

**根本解法（两条，均为纪律段已记载的成熟手段）**：
1. **`abstract` 封体**（纪律段 §4.5「把界与所有相关定义连同它们的体封进同一个 `abstract` 块」）：
   把 `reduceG` 及相关定义连体封进 `abstract`，只对外暴露类型 ⇒ 展开被阻断 ⇒ `cong` 稳定。
2. **全程走 AHbt 层**：用 `_PN12` 的双向桥 `reduceG-cong : AHbt X Y → reduceG X ≡ reduceG Y` 与
   `reduceG-eq→AHbt : reduceG x ≡ reduceG y → AHbt x y`，把全部推理放在 **AHbt（命题层）**，
   只在**一次** `reduceG-cong` 处接触 ≡ 层。（**倾向此法**：不动既有定义、风险更低。）

**完整路线（件已齐备）**：`reduceG-++` · `toElems-++w` · `filterE-++`(_PN12:1360) ·
`bridge-canon`(_PN16:834，G 侧，参数 `l : List (Elem G)`) · `reduceG-cong` · `reduceG-eq→AHbt`。

**教训（第 16 条）**：**「形式方案全败」时，往定义层找（`abstract`/`opaque`/换层），而不是继续调形式。**
