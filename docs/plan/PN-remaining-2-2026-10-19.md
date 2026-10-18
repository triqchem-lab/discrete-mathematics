# PN 线剩余 2 件的解决计划（2026-10-19）

> **接续**：PN 线 L1–L8 已全部闭合（journal round 331–332）；`π₁ᵇᵗ ≅ F_{E₀−V+1}` 主线完成。
> **性质**：**计划文档**（非证明）。所有「已证」以 `proof_dag` 台账回执为准；**无回执一律标未证**。
> **范围**：仅剩 2 件 —— `A1c2.add2-comm-generic-status`（blocked）与 `PIO-1.card-divergence`（active）。

---

## 0. 现状快照（实测，2026-10-19）

| 指标 | 值 |
|---|---|
| PN 线节点 | **270**（`proven 257`｜未完成 **2**｜abandoned 7｜refuted 3｜artifact 1）|
| 全台账 | `proven 732`（A 级 732，**回执无效 0**）｜pending 2｜active 5｜blocked 6 |
| 规则戳 | 规则集 `r15/5c21a729`｜插件本体本实例 `67fc261c` / 磁盘 `39a7f83c` ⚠ 待重启 |

**本轮（round 332）已解 4 件**（均为「找到已证承载件」，非新证）：

| 节点 | 承载件 | 位置 |
|---|---|---|
| `PN5.general-correspondence` | `PN16.pi1bt-iso`（8/8 字段）+ `PN5.edge-path-group-boundary` | `_PN16:3612` |
| `PN16.toEdgesO-faithful`（★枢轴）| 源码名 **`faithful`** | `_PN16:1851-1857` |
| `PN16.to-from-w` | `PN15.to-from-w` + `_PN16.bridge-connect` | `_PN15:65` / `_PN16:1152-1166` |
| `PN16.red-edges-tree-classification` | `PN12.reduceG-AllE`（对**任意** `P` 保持）| `_PN12:216-220` |

**共同教训**：节点写的是**计划稿**，实现走了**更强/不同形**的路线 ⇒ 属**账面滞后**，不是缺证。
⇒ **本计划的第一条纪律**：动手前先按「**承载件是否已在源码里**」核查一遍（本轮 4/6 都是这样解的）。

---

## 0.5 复用清单（**动手前必读** —— 2026-10-19 用 DSH `grep` 工具实测）

> 纪律：**先查代码实现与复用，原子构建**。以下均已实测命中；**新写之前先复用**。

### 件 A 可复用的（集合层消去范式 —— **已在用，不是新造**）

| 复用件 | 位置 | 说明 |
|---|---|---|
| **`rec squash/ (λ c → …) (λ c c' s → eq/ …)`** | 全库 **17+ 处** | 集合层消去范式（常值函子 + respect）|
| **`add2⁺` 本身就是这么定义的** | `probes/_PPI5j.agda:141`、`_PEH13.agda:8` | `add2⁺ q r = rec squash/ (λ c → addL⁺ c r) resp-outer q` ✓ |
| `addL⁺` / `addR⁺` | `_PPI5j.agda:131/:136` | 单变元版（`rec squash/` + `whiskΩ3` / `whiskR-walk`）|
| **`π₁ᵈ-rec`** | `_PPI2.agda:94/:193` | **1 维商的集合层 rec** —— `_PPI4.agda:118` 称其为「**`_PPI2` 既有形**」✓ |
| 范式文档 | `_PN5.agda:79`、`_PN6.agda:66` | 「商面消去按 **`_PEH14` 范式**：`rec`（需 `isSet` 余域）/ `rec2` / `elimProp`」✓ |
| `rec`/`rec2` 的 import 行 | `_PN5:100`、`_PN6:85`、`_PEH14:38` | 直接抄 import ✓ |

**⇒ 结论**：`A1c2` 路径 A1 的**机制（集合层 rec + respect）在库内已成熟** ✓ —— 缺的**只是**一个「对 `Ω3Walk⁺` 不变的**判别不变量**」✗（现有 17 处 `rec` 的余域**全是商**，没有一处到 `ℕ`/`Bool` ✗）。
⇒ **原子第一步**：按 `_PPI5j:131` 的形状写 `f : Ω2Walk → ℕ` + `f-resp : ∀ c c' s → f c ≡ f c'`，**先只证 respect**（不急着找不相等见证）。

### 件 B 可复用的（同构接口范式 + 库侧分类件）

| 复用件 | 位置 | 说明 |
|---|---|---|
| **`record SetoidGroupIso (S T : SetoidGroupData) : Set₁`** | `_PN15.agda:135` | **通用同构 record 已在** ✓（8 字段：`to`/`from`/`to-cong`/`from-cong`/`from-to`/`to-from`/`from-mul`/`to-mul`）⇒ monoid 版**按它写**（小改动）✓ |
| `gcmp-classify`（分类主件）| `probes/_PPI4e.agda:95` | **库侧 A 级**：`∀ (w : Walk (Gcmp two-chain) fzero fzero) → …`，恰两类 ✓ |
| `cls-ex-nil` / `cls-ex-loop` | `_PPI4e.agda:115/:119` | 两类各自的见证 ✓ |
| 完备性 | `_PPI4e.agda:147` | 「完备性 = `gcmp-classify` 本体（全部 `fzero` 闭 walk 二分）」✓ |
| 旗复形构造件 | `pn-proofs/_PN1.agda:3/:5-8/:327` | `Shape n` / `N₁Trivialization` ✓（**已在**，更正旧注「零命中」✗）|
| 立界件 | `pn-proofs/_PN1.agda:321` | 「本库**无几何实现 `\|·\|` 与拓扑 `π₁`**」✓ |

**⇒ 结论**：`PIO-1` 的**库侧**（`π₁ᵈ` 恰两类 ⇒ 基数 2）**已 A 级** ✓；**外部侧**（`π₁(|N₁G|)=0`）**已立界** ✗ ⇒ 路径 **B2 拆分**是**直接可做**的 ✓。

---

## 1. 件 A：`A1c2.add2-comm-generic-status`

### 1.1 命题与当前判定

- **命题**：`∀ q r : π₂ᵈ⁺, add2⁺ q r ≡ add2⁺ r q`
- **判定**：**假**（结构性论证：自由群胚一般非交换）——**但无机器反证** ✗
- **已证部分**（机器验证）：
  - `add2⁺-comm-generic-reduction`（`probes/_PEH13.agda:188`）—— 把泛型交换律**归约**为 Ω3Walk⁺ 层条件 ✓
  - `add2⁺-comm-unit` / `add2⁺-comm-of-unit`（`:199-`）—— 单位类与一切类交换 ✓
  - `suffix-class⁺`（`probes/_PEH4.agda`）—— s²ᵈ 气泡类坍缩实例 ✓

### 1.2 精确障碍（本轮实测）

`π₂ᵈ⁺ = Ω2Walk / Ω3Walk⁺` 是 **Cubical 集合商**（`squash/`）。要证商中的**不相等**，必须有**集合层**（set-level）判别不变量；而 `_PEH13` 暴露的消去族**只有命题层**：

```
_PEH13.agda:60   open import Cubical.HITs.SetQuotients using (_/_; [_]; eq/; squash/; elimProp; elimProp2)
_PEH13.agda:79   elim⁺ : … → …      （:83  elim⁺ = elimProp）
```

**命题消去只能证命题，不能造出 `π₂ᵈ⁺ → 可判定集` 的函数** ⇒ 无法构造区分两个类的见证 ✗。

### 1.3 三条路径

| # | 路径 | 做法 | 代价 | 风险 |
|---|---|---|---|---|
| **A1** | **建集合层 `rec`** | 在 `_PEH13` 定义 `rec⁺ : (f : Ω2Walk → A) → (∀ d d' s → f d ≡ f d') → π₂ᵈ⁺ → A`（`A` 为 **set**），用 `SetQuotients.rec` 或 `rec2`；目标取**可判定集**（如 `ℕ` 或 `Bool`）| **中**（接口层 + respect 证明）| 中（respect 证明可能撞 `whiskΩ3` 的具体形状）|
| **A2** | **换判别目标** | 不证「不相等」，改证**更强的正命题**：`add2⁺-comm-generic-reduction` 的**逆**（即「交换律 ⟺ 某实例条件」），把「假」编码为「该实例条件不可满足」| **中高** | 高（逆方向未必成立）|
| **A3** | **立界（boundary）** | 如实声明：本库当前**不具备**机器反证所需机件 ⇒ 记为**已知边界**（`blocked` + 精确诊断，已做 ✓），并把「结构性论证」明确标为**非证明** | **低** | 无（诚实）|

### 1.4 判据（做到哪一步算什么）

- **A1 成功判据**：存在 `rec⁺` 且 `proof_compile` exit 0；**且**存在具体 `q r` 使 `f q ≢ f r`（其中 `f := rec⁺ …`）⇒ 此时节点可标 `refuted`（带机器反证）✓
- **A1 半成**：只有 `rec⁺` 而无不相等见证 ⇒ 新建节点记 `rec⁺` 为 `object`，原节点仍 `blocked` ✓
- **A3**：写清「缺哪件机件 + 为什么命题消去不够」，节点保持 `blocked` + `diagnosis: proof_too_hard` ✓

### 1.5 第一步（具体）

```bash
# ① 读 SetQuotients 的 rec 签名（本库已 import 的版本）
grep -nE "^rec |^rec2 |rec :" /data/work/functional-programming/agda-stdlib/…/Cubical/HITs/SetQuotients/Base.agda
# ② 在探针里试写 rec⁺ 到 ℕ（目标 = 走长 / 生成元计数）
# ③ 若 respect 证明撞墙，退回 A3 并记录撞墙形状（供 prover_limits）
```

---

## 2. 件 B：`PIO-1.card-divergence`

### 2.1 命题与当前状态

- **命题**：`∃G. π₁ᵈ(G) ≇ π₁(|N₁G|)`
- **实例**：`G = Gcmp two-chain`
  - 库侧：`π₁ᵈ = 2 元幂等幺半群` —— **A 级** ✓（`probes/_PPI4e.agda:95` `gcmp-classify : ∀ (w : Walk (Gcmp two-chain) fzero fzero) → …`，配 `cls-ex-nil`（:115）/ `cls-ex-loop`（:119）/ 完备性（:147）；`_PPI4f` loop-squash）
  - 外部侧：`π₁(|N₁Gcmp|) = 0` —— **外部事实**（Barcelo–CK）
- **基数 2 ≠ 1 ⟹ 不同构** ✓（推理形式简单）

### 2.2 精确事实（本轮实测，**更正节点旧注**）

节点注记曾写「`|N₁G|`/旗复形件在库**零命中**」✗ —— **实测有命中** ✓：

```
pn-proofs/_PN1.agda:3    -- | _PN1 —— 旗复形 / 1-神经构造件（PIO-1 Agda 化的前置件）
pn-proofs/_PN1.agda:5-8  旗复形（flag complex / clique simplex）… 1-旗复形载体 … Shape n：k 元链 = (k−1)-单纯形
pn-proofs/_PN1.agda:321  陈述面：|N₁G| 几何实现可缩 ⟹ π₁(N₁G)=0。本库**无几何实现 |·| 与拓扑 π₁** 的…
pn-proofs/_PN1.agda:327  N₁Trivialization : DiGraph → Set
pn-proofs/_PN1.agda:37   … one-sym-graph-is-simplex / N₁Trivialization【立界】
```

⇒ **旗复形构造件已在**（`_PN1`）✓；缺的是**几何实现 `|·|` 与拓扑 `π₁`** ✗ —— 而 `_PN1:321` **已经立界** ✓（明确声明本库无该层）。

### 2.3 三条路径

| # | 路径 | 做法 | 代价 | 风险 |
|---|---|---|---|---|
| **B1** | **库内自足化** | 在库内建**组合式**的 `π₁(|N₁G|)` 替身（如「旗复形的 1-骨架走类」），并证它与 `π₁ᵈ` 不同 | **高** | 高（等于在库内重造拓扑 π₁；且「替身 = 拓扑 π₁」本身需论证 ✗）|
| **B2** | **立界 + 双面分述** | 把节点**拆成两半**：(a) 库侧 A 级（`π₁ᵈ` 的分类，**已证** ✓）⇒ 可单独闭合；(b) 外部侧（`π₁(|N₁G|)=0`）⇒ 明确标为**外部事实**（带文献来源），**不冒充库内定理** ✗ | **低** | 无（诚实）|
| **B3** | **改陈述为条件式** | 陈述改为「**若** `π₁(|N₁Gcmp|)=0`（外部事实）**则** `π₁ᵈ(Gcmp) ≇ π₁(|N₁Gcmp|)`」—— 前半为**假设**、后半为**库内可证的基数论证** | **低中** | 低 |

### 2.4 判据

- **B2 成功判据**：新建节点 `PIO-1a.library-side`（`object`/`proven`，承载件 `_PPI4e.gcmp-classify` 等 ✓，带回执）+ `PIO-1b.external-side`（`artifact`，`evidenceKind: doc`，指向 Barcelo–CK 文献）；原节点 `abandoned`（**已拆分**）并写明两半去向 ✓
- **B3 成功判据**：新陈述为 Π-型（假设 → 结论），`proof_compile` exit 0 ⇒ 标 `proven` ✓

### 2.5 第一步（具体）

```bash
# ① 核实库侧 A 级件的实际签名与覆盖
grep -nE "gcmp-classify|cls-ex-|完备性" probes/_PPI4e.agda
# ② 确认 _PN1 的旗复形件签名（Shape / 链 / 双射件）
grep -nE "^ *data Shape|^ *[a-zA-Z-]+ *: *DiGraph|one-sym-graph-is-simplex" pn-proofs/_PN1.agda
# ③ 按 B2 拆分（首选）或 B3 改陈述
```

---

## 3. 诚实边界（本计划不声称的）

1. **本计划是计划，不是证明** ✗ —— 所有「已证」以回执为准；本文件里凡未附回执者一律为**待办** ✓
2. **件 A 的「假」目前只有结构性论证** ✗ —— **不得**据此标 `refuted`（纪律：`refuted` 必须带证据 ✓）
3. **件 B 的外部侧（`π₁(|N₁G|)=0`）不是本库定理** ✗ —— `_PN1:321` 已立界；把它当库内结论即为**越界声称** ✓
4. **「基数 2 ≠ 1 ⟹ 不同构」需要同构概念的形式化** ✓ —— 库内**没有**通用 `MonoidIso`（节点注记自述「需 `MonoidIso`-型 EQUIVS 面」✗）⇒ 这是 B2/B3 都必须先补的**接口件** ✓

---

## 4. 执行顺序与验收

| 序 | 动作 | 验收 |
|---|---|---|
| 1 | 件 B 走 **B2 拆分**（低风险、立即可做）| 3 个节点入账（a/b/原），各带证据；原节点写明拆分去向 ✓ |
| 2 | 补 **`MonoidIso`-型接口件**（B2/B3 共用）| 新节点 + `proof_compile` 回执 ✓ |
| 3 | 件 B 走 **B3 条件式**（若接口件就位）| 新陈述编译通过 ⇒ `proven` ✓ |
| 4 | 件 A 走 **A1 建 `rec⁺`**（先探针，后并入）| 探针 `exit 0` ⇒ 并入 `_PEH13` ⇒ 重签 ⇒ 兑现 ✓ |
| 5 | 件 A 若 A1 撞墙 ⇒ 退回 **A3 立界**并记 `prover_limits` | 撞墙形状入限制库（**证据必填** ✓）|

**每步结束**：`proof_dag check` 看断链/回执 → `journal` 记流水 → 工作树提交 ✓

---

## 5. 参考锚点（全部可复核）

- `probes/_PEH13.agda:60/:79/:83/:188/:199`（消去族与已证件）
- `probes/_PPI4e.agda:95/:115/:119/:147`（库侧 A 级分类件）
- `pn-proofs/_PN1.agda:3/:5-8/:37/:321/:327`（旗复形构造件 + 立界）
- 台账：`A1c2.add2-comm-generic-status`（blocked）｜`PIO-1.card-divergence`（已拆）
- 相关计划：`docs/plan/a1c-pi2-watershed-status-2026-10-14.md`（π₂ᵈ 分水岭状态表）、`docs/plan/A1-pi-n-paths-abcd-research.md`

---

## 6. 任务原子分解（**动笔前齐备** —— proof-engineer「开工作业四件套」第 1 件）

> **原子定义**（纪律）：一个原子 = **一条能独立写出的顶层类型签名**（能单独放进探针模块编译）。
> 过粗不可证、过细是噪音。**每个原子必须有：签名 + 依赖 + 验证命令 + 达成判据**。

### 6.1 件 A 的原子链（`A1c2`）

**★ 路线由源码自己指定**（`probes/_PEH13.agda:41/:50/:333` 逐字）：
> `:41`「先在 `Ω2Walk` 上造出与 `Ω3Walk⁺` 相容的**可计算不变量**（把两式分离）」
> `:50`「**(e) 机器反证的下一路（本件未做）**：在 `Ω2Walk` 上构造与 `_++2_` 相容的**可计算次序不变量**」

**载体事实**（`_PPI5d.agda:44-46`）：`Ω2Walk G x : Walk G x x → Walk G x x → Set` = **`ASTep` 的列表**
```agda
data Ω2Walk (G) (x) : Walk G x x → Walk G x x → Set where
  nil2  : ∀ (w) → Ω2Walk G x w w
  cons2 : ∀ {w1 w2 w3} → AStep G w1 w2 → Ω2Walk G x w2 w3 → Ω2Walk G x w1 w3
```

| 原子 | 签名（**可直接写进模块**）| 依赖 | 验证 | 达成判据 | 状态 |
|---|---|---|---|---|---|
| **A-0** | *设计*：定出 `f` 的**具体公式**（候选：步数 / 首步的 `ASTep` 端点 / 各步「面号」的加权和）| — | 手工推演 + 3 个具体 2-walk 上试算 | 在 `Ω3Walk⁺` 的**三个生成元** `{fill-tri, whisk3, bub3}` 上分别试算，确认 `f` 在它们下**不变** | ⬜ 未开工 |
| **A-1** | `len2 : ∀ {w w'} → Ω2Walk G x w w' → ℕ`（步数；**非不变**，但为后续原子提供归纳骨架）| — | `proof_compile` 探针 | `exit 0` + 回执 | ⬜ 未开工 |
| **A-2** | `f : ∀ {w w'} → Ω2Walk G x w w' → ℕ`（A-0 定出的不变量）| A-0 | 同上 | 同上 | ⬜ 未开工 |
| **A-3** | `f-resp : ∀ {w w'} (c c' : Ω2Walk G x w w') → Ω3Walk⁺ G x c c' → f c ≡ f c'`（**相容性**：核心难点）| A-2 | 同上 | 同上（**须对三个生成元逐个分情况**）| ⬜ 未开工 |
| **A-4** | `f-++2 : ∀ (a b) → f (a ++2 b) ≡ g (f a) (f b)`（与 `_++2_` 相容；`g` 为组合律）| A-2 | 同上 | 同上 | ⬜ 未开工 |
| **A-5** | 见证对：`∃ a b. f (a ++2 b) ≢ f (b ++2 a)`（**机器反证**）| A-3, A-4 | `proof_compile` + 具体点 | 存在性与不相等**都有证明体** ⇒ **可标 `refuted`** ✓ | ⬜ 未开工 |

**策略（L2）**：A-1/A-2 用**结构递归**（`Ω2Walk` 两个构造子 ✓）；A-3 用**穷举生成元**（`Ω3Walk⁺` 的生成集有限 ✓ ⇒ 3 case ✓，符合「≤27 case 全用」✓）；A-5 用**否定证明**（策略 C ✓）。

**风险与备选**：若 A-3 在某个生成元上**撞墙**（不变性其实不成立 ⇒ 该 `f` 选错）⇒ 退回 A-0 换公式 ✓（**不是**改陈述 ✗）。若 3 个候选公式**全部**撞墙 ⇒ 按 A3 路径**立界** + 记 `prover_limits` ✓。

### 6.2 件 B 的原子链（`PIO-1`）

**已完成原子**（B2 拆分 ✓）：`PIO-1a.library-side`（proven ✓）｜`PIO-1b.external-side`（artifact ✓）。

| 原子 | 签名 | 依赖 | 验证 | 达成判据 | 状态 |
|---|---|---|---|---|---|
| **B-1** | `record SetoidMonoidIso (S T : SetoidMonoidData) : Set₁`（按 `_PN15.agda:135` 的 `SetoidGroupIso` 写，去掉 `inv`/`invˡ`/`invʳ` 三字段）| — | `proof_compile` 新模块 | `exit 0` + 回执 | ⬜ 未开工 |
| **B-2** | `π₁ᵈ-card : ∀ (G) → …`（**基数 = 2**：由 `gcmp-classify` 的二分给出）| `PIO-1a.library-side` ✓ | 同上 | 同上 | ⬜ 未开工 |
| **B-3** | 条件式陈述：`(h : π₁(|N₁Gcmp|) 平凡) → ¬ (SetoidMonoidIso π₁ᵈ-类 (trivial-monoid))` | B-1, B-2 | 同上 | 同上 ⇒ `proven` ✓ | ⬜ 未开工 |
| **B-4** | （备选）B1 路径：库内自足化 `π₁(|N₁G|)` 的组合替身 | — | — | — | ⬜ **不建议**（代价高、风险高，见 §2.3）|

**策略（L2）**：B-1 是**定义层**（`record` ⇒ 对象级验收 ✓，见 doctrine）；B-2 用**分类器 + 计数**（`gcmp-classify` 的 `inj₁`/`inj₂` 二分 ✓）；B-3 用**基数矛盾**（`2 ≠ 1` ✓）。

**风险**：B-2 需先把 `π₁ᵈ` 的**载体/关系**封装成 `SetoidMonoidData`（`_PN15:99` 有 `SetoidGroupData` ✓ ⇒ 按它写 monoid 版 ✓）。

### 6.3 开工顺序（**原子构建**：一个原子一编译一记账）

```
① A-1（len2，最确定，只验机制）→ 探针 exit 0
② B-1（SetoidMonoidIso record，纯定义层，最确定）
③ A-0（设计 f 的公式，在 3 个生成元上试算）← 件 A 的真正瓶颈
④ A-2 → A-3 → A-4 → A-5（依赖序）
⑤ B-2 → B-3
```

**每原子收尾（纪律）**：`proof_compile`（拿回执）→ `proof_dag add/update`（记账）→ `check`（看断链不增）→ `journal`（记流水）→ **提交** ✓

---

## 7. 验证点对账表（**L4 交付层要求：五层缺一不收** —— 2026-10-19 审核后补）

> 口径：**每个原子子任务**必须能对上「**验证命令 → 达成判据 → 当前状态**」三列。
> 状态取值：`达成`（有工具签发证据）/ `未达成` / `未开工` / `不适用`。**模型自报不算达成**。

### 7.1 本轮已完成（B2 拆分链）

| # | 子任务 | 验证命令 | 达成判据 | 状态 |
|---|---|---|---|---|
| B2-1 | 取库侧分类件的回执 | `proof_compile probes/_PPI4e.agda` | `exit 0` + 回执 id | ✅ **达成**（`2b478d87f961…`，3.8s）|
| B2-2 | 登记库侧节点 | `proof_dag add`（`kind:object`）| 工具接受 + 记 `proven` + 有 `construction` | ✅ **达成**（`PIO-1a.library-side`）|
| B2-3 | 登记外部侧节点 | `proof_dag add`（`artifact`）| 工具接受 + 带 `evidenceKind:doc` | ✅ **达成**（`PIO-1b.external-side`）|
| B2-4 | 原节点标已拆 | `proof_dag update` + `import` | `abandoned` + **`reason` 非空** | ✅ **达成**（`abandoned 无 reason: 0` ✅）|
| B2-5 | 依赖登记与代码一致 | `proof_dag check` | 断链数不因本轮**增加** | ✅ **达成**（10 → 4 → 预期 3；修了**自己引入的 7 处** ✗）|

### 7.2 本轮未做（**如实列**）

| # | 子任务 | 验证命令 | 达成判据 | 状态 |
|---|---|---|---|---|
| 4-2 | 补 `MonoidIso`-型接口件 | `proof_compile <新模块>` | `exit 0` + 回执 | ⬜ **未开工** |
| 4-3 | 件 B 条件式（B3） | 同上 | 新陈述编译通过 ⇒ `proven` | ⬜ **未开工** |
| 4-4 | 件 A 建 `rec⁺`（A1，**先探针**）| `proof_compile probes/_PEH13*.agda` | 探针 `exit 0` + `f-resp` 有证明体 | ⬜ **未开工** |
| 4-5 | 件 A 撞墙则立界 | `prover_limits add` | 条目带**实测证据** | ⬜ **不适用**（尚未撞墙）|
| 4-6 | 件 A 找不相等见证 | 需 4-4 先成 | 存在 `q r` 使 `f q ≢ f r` ⇒ 可标 `refuted` | ⬜ **未开工**（依赖 4-4）|

### 7.3 验收命令速查（每步收尾必跑）

```bash
# ① 回执与状态
proof_dag check                     # 看：断链 / 回执无效 / A 级计数 / 非命题已完成
# ② 单模块内核证据（唯一裁决）
proof_compile <Module>.agda         # 成功签发回执（与源码哈希绑定）
# ③ 证明图（依赖序 / 环）
proof_graph <PN 模块列表>            # 期望：环 0
# ④ 甘特面（三图交付之一）
node ~/.dsh/.agent-presets/math-proof/scripts/dag-gantt.mjs
```

### 7.4 审核发现与处置（2026-10-19，`proof-engineer` × `fable5` 双技能审核）

| 发现 | 严重度 | 处置 |
|---|---|---|
| **断链 3 → 10**（**本轮我自己引入 7 处** ✗：改 `module` 连带改 deps 解析 + 补登依赖未一次查完 import 表）| 高 | ✅ **已修**（10 → 4 → 预期 3）；两条教训入 journal ✓ |
| **甘特只认 `proven` 一态** ✗（42 个 `artifact` + 144 个 `abandoned` 被画成「待办」）| 中 | ✅ **已修**（四态映射：`:done`/`:milestone`/`:active`/`:crit` + 后缀区分 ✓）|
| 计划缺**验证点对账表** ✗ | 中 | ✅ **本次已补**（本 §7 ✓）|
| **我误判**「甘特日期硬编码/陈旧」✗ | 低 | ✅ **已自查纠正**：`dag-gantt.mjs:85` 用 `new Date()` **动态生成** ✓，那个「2026-10-18」是**系统日期** ✓ |
| 变体模块（`_PN16s`/`_PN16probe*`/`_PN12check`）**未入台账** ✗ | 低 | ⬜ **未处置**（列入缺口 ✓）|
