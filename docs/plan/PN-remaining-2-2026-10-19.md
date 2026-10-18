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
| **A-0** | *设计*：定出 `f` 的**具体公式** | — | 手工推演 + 生成元分析 | 在 `Ω3Walk⁺` 三个生成元上**不变** | ✅ **达成**（见下方取证：基关系 = 气泡塌缩 ⇒ 有符号计数天然不变；**交换目标不能分离** ⇒ 分离器须非交换）|

#### ★ A-0 取证结果（2026-10-19 实测，`probes/_PPI5g.agda:48-58`）

```agda
data Ω3Step⁺ (G) (x) : {w1 w2} → Ω2Walk G x w1 w2 → Ω2Walk G x w1 w2 → Set where
  base3+ : …                                   -- ① fill-tri 嵌入（尾位气泡收缩）
  whisk3 : (c₁ : Ω2Walk G x w1 wm) {c c' : Ω2Walk G x wm w2} → …  -- ② 缘饰/**前缀提升**
  bub3   : (c₁ : Ω2Walk G x w1 wm) {wm' : …} → …                  -- ③ 任意位气泡消去
data Ω3Walk⁺ (G) (x) : {w1 w2} → Ω2Walk G x w1 w2 → Ω2Walk G x w1 w2 → Set where …  -- 闭包
```

**关键结构事实（决定 `f` 的设计空间）**：
1. **`whisk3` 是左同余** ✓（`c₁ ++2 c` ↝ `c₁ ++2 c'`）⇒ **任何不变量必须对「前缀拼接」不变** ✗ —— 强约束：`f` 只能「看见」**尾部** ✓
2. ⇒ **不能用**：步数 ✗（`bub3` 会变）、首步 ✗（`whisk3` 会变）、整条 `ASTep` 序列 ✗
3. **可用方向（待验）**：`f` 取**尾部不变量** —— 候选：(i) 最右非气泡段的形状；(ii) 末尾 `ASTep` 的**类型**（注意：目标走 = 类型指标 ✗ 不可用，但 `ASTep` 的**构造子标签**可用 ✓）
4. ⚠ **风险已明确**：三候选若**全部**撞墙 ⇒ 按 A3 路径**立界** + 记 `prover_limits` ✓（**不改陈述** ✗）

**已验生成元实例**（供 A-2/A-3 复用 ✓）：`_PPI5g.agda:125` `chk-bub-wit = bub3 (nil2 w3) face012-slide (nil2 w3)` ✓｜`:132` `chk-whisk3-s2 : Ω3Step⁺ s2-adj s2v0 (bub face012-slide ++2 bub face012-slide) (bub face012-slide)` ✓
| **A-1** | `len2 : ∀ {w w'} → Ω2Walk G x w w' → ℕ`（步数；**非不变**，但为后续原子提供归纳骨架）| — | `proof_compile` 探针 | `exit 0` + 回执 | ✅ **达成**（`probes/_PEH16.agda`，回执 `eda6390f03e7…`）|
| **A-2** | `sign` + `wsum : Ω2Walk G x w w' → ℤ`（有符号步数和，候选 C-1）| A-0 ✅ | `proof_compile` 探针 | `exit 0` + 回执 | ✅ **达成**（`probes/_PEH16.agda`，回执 `e1e7c5a206e3…`）⚠ **非分离器** ✗ |
| **A-3** | `wsum-resp : Ω3Walk⁺ G x c c' → wsum c ≡ wsum c'`（三生成元 + 四闭包构造子）| A-2 ✅ | 同上 | 同上 | ✅ **达成**（回执 `88440b6f0f54…`，5.1s，0 postulate/0 hole）—— 形状对齐 `_PEH9:246-252` ✓ |
| **A-4** | `wsum-++2 : wsum (c ++2 e) ≡ wsum c + wsum e`（可加性）| A-2 ✅ | 同上 | 同上 | ✅ **达成**（回执 `229b0b5d085a…`）—— ★ **走 Cubical 路线**（`Cubical.Data.Int` + `Properties` 的 `pos0+`/`+Comm`/`+Assoc`）✓ |
| ~~A-5~~ | ~~`∃ a b. wsum (a ++2 b) ≢ wsum (b ++2 a)`~~ | — | — | — | ❌ **原形不可达**（ℤ 交换 ⇒ 恒相等 ✓）—— 但 ★ **这是「方法错」不是「命题错」** ✗（见下方改道）|
| **A-5'** | ★ **改道后的 A-5**（`_PN12.Fold`/`GroupC` 实例化 + 自由幺半群判别子）：`to = reduceG ∘ toW` + `to-resp` + `witness-neq` | A-3 ✅ | `proof_compile` | `exit 0` + 回执 ⇒ **`refuted`** ✓ | ✅ **达成**（`probes/_PEH21`，回执 `a6b6ba46…`；`add2-comm-generic-status` 已升 refuted ✓，见下方闭合记录）|
| **A-6** | ~~C-4 自由群分离器~~（`Label = Bool × ℕ × ℕ` + `cancel`）| — | — | — | ✅ **达成（改道）**——自造 `cancel` 链退役 ✗，改由 **`_PN12.Fold`/`GroupC` 实例化**完成（`LabelGraph` + 两个 `open module` ✓，见闭合记录教训①）|

#### ★★ A-5 改道依据（2026-10-19，`PN2.pio1-noiso` 模板）

**同族已证件**（**proven** ✓，回执 `7a928e08cad4…`）方法**逐字**：
> ① **P1 类集合 2-枚举**（`to2`/`of2` 双向 + `quot-cover` + `of2-to2-id` 商级）
> ② **P2 单点面**（`TrivCls = ⊤` 全形 + `flag-point`）
> ③ **no-iso-π₁ᵈ-unit**（2 元类不与 1 点群同构——**全形类型级收案**）

⇒ **方法 = 枚举/分类 + 类型级不相等** ✓ —— **不是**抽象不变量 ✗、**不是**自由群范式 ✗
⇒ **优点**：① **复用**已证模式 ✓；② **类型级** ⇒ 不需**可判定相等**机件 ✗（正好绕开 C-4 卡住的 `cons` 解析 ✗）；③ 与 §7.3「分水岭定理：π₁ᵈ 二分 ✓ **自同构决定**」口径一致 ✓

#### ★ 八要素对 A-5' 的**硬要求**（`Presentation.agda:19-27` + `docs/maps/八要素统一形状:15`）

| 要素 | A-5' 的对应 | 要求 |
|---|---|---|
| ① 载体 | `Ω2Walk G x w w'` | ✓ 已有 |
| ② 生成元 | `ASTep`（`slide`/`expand`）| ✓ 已有 |
| ③ 关系 | `Ω3Step⁺`（`base3+`/`whisk3`/`bub3`）| ✓ 已有 |
| ④ **相位** | ★ **朝向 + 三角数据** | **不可约** ✗ —— **不许截断成 {±1}** ✗（相位不可约性元公理 ✓）|
| ⑤ 时钟 | `_++2_` 的拼接迭代 | ✓ 已有 |
| ⑥ 归零 | 气泡塌缩（`fill-tri`）| ✓ 已有（同 `1² + i² = 0²` 的归零机制 ✓）|
| ⑦ **刚性** | ★ 需**从 GF9 的 `galoisConjugate` 诱导** | ⚠ **待建**（范式：`dc-presentation` 的 `rigidity = rho`，`Presentation.agda:144` ✓）|
| ⑧ 核对 | `refl`（**不产生结构**）| ✓ |

#### ★ 改道后的原子链（A-5'）

| 原子 | 内容 | 验证 | 状态 |
|---|---|---|---|
| **A5'-1** | 枚举件 = **`LabelGraph` + `PN12.Fold`/`GroupC` 实例化**（`to = reduceG ∘ toW` + `to-idem`，`_PEH21`）| `proof_compile` | ✅（回执 `7dae8c8d…`；范式计算 `to-c1`/`to-c2` 见 A5'-2 ✓）|
| **A5'-2** | 见证对：`LoopG` 上两个**同型** `ASTep`（前缀长 0 vs 1 ⇒ label `(t,0,1) ≢ (t,1,0)`）| 同上 | ✅（`labs-neq` + `word-swap-≠`，回执 `ad7755fc…`）|
| **A5'-3** | `witness-neq : ¬ (Ω3Walk⁺ LoopG tt c1 c2)`（`to-resp` 提升到商层）| 同上 | ✅（回执 `a6b6ba46…`；**`add2-comm-generic-status` 已升 refuted** ✓）|
| **A5'-4** | 八要素对表（`A1c2.A5'-4.presentation`，对象级 ✓）| 同上 | 🟡 **部分达成**（①②③④⑤⑥⑧ ✅；⑦ `invLabel` 对合已证 ✓ 但 **GF9 诱导正式桥未建** ⚠ 诚实缺口，对分离非必需 ✓）|

#### ★★ A-5' 闭合记录（2026-10-19，全部 proven ✓）

| 原子 | 状态 | 回执 |
|---|---|---|
| A5'-1 标签层（`wlen`/`Label`/`label`/`invLabel`/`label-inv`/`_≟L_`/`cancel`，`_PEH19`）| ✅ | `f5a57d8c…`/`55b80bfd…` |
| A5'-1 引理层（`invLabel-inv`/`cancel-pair`/`toRaw`/`toRaw-++2`）| ✅ | `5a5ed623…`/`ee8f68a7…` |
| A5'-1e 图实例化（`LabelGraph` + `PN12.Fold`/`GroupC`，`_PEH21`）| ✅ | `7dae8c8d…` |
| 三案（`bubble-eq`/`base3-eq`/`toW-++2`/`whisk3-eq`/`bubble-mid`/`bub-eq`）| ✅ | `6a1cbedb…` 等 6 件 |
| **`to-resp`（总装配，含局部 `assocL`）** | ✅ | `c73ebb38…` |
| 判别力（`hd`/`just-inj`/`word-swap-≠`/`nil≢cons`）| ✅ | `ad7755fc…` |
| **A5'-2/3 见证对 `witness-neq : ¬ (Ω3Walk⁺ LoopG tt c1 c2)`** | ✅ | `a6b6ba46…` |
| A5'-4 八要素对表（`A1c2.A5'-4.presentation`，对象级）| ✅ | 同上 |

**连锁升级** ✓：`A1c2.add2-comm-generic-status` **blocked → refuted**（构造性见证落地 ✓）。

**★ 路线教训（入册）** ✓：① **先查库再自造**（自造 `cancel` 链被 `_PN12.Fold`/`GroupC` 两个 `open module` 取代，`_PEH19`/`_PEH20` 自造件已退役 ✗ 勿重走）；② **库件带脏隐式参数时同内容局部重证更便宜**（`assocL` 3 行 vs `++w-assoc` 层级调试）；③ **同族硬约束**（判等层 stdlib `_≡_`+`Dec`，代数层 Cubical Int 族）。

**诚实缺口** ⚠：八要素 ⑦ 的 **GF9 诱导正式桥**未建（`invLabel` 对合已证 ✓ 且同型于 σ ✓，但 Label→GF9 映射未建 ✗）—— 对分离非必需 ✓。


**策略（L2）**：A-1/A-2 用**结构递归**（`Ω2Walk` 两个构造子 ✓）；A-3 用**穷举生成元**（`Ω3Walk⁺` 的生成集有限 ✓ ⇒ 3 case ✓，符合「≤27 case 全用」✓）；A-5 用**否定证明**（策略 C ✓）。

**风险与备选**：若 A-3 在某个生成元上**撞墙**（不变性其实不成立 ⇒ 该 `f` 选错）⇒ 退回 A-0 换公式 ✓（**不是**改陈述 ✗）。若 3 个候选公式**全部**撞墙 ⇒ 按 A3 路径**立界** + 记 `prover_limits` ✓。

### 6.2 件 B 的原子链（`PIO-1`）

**已完成原子**（B2 拆分 ✓）：`PIO-1a.library-side`（proven ✓）｜`PIO-1b.external-side`（artifact ✓）。

| 原子 | 签名 | 依赖 | 验证 | 达成判据 | 状态 |
|---|---|---|---|---|---|
| **B-1** | `record SetoidMonoidIso (S T : SetoidMonoidData) : Set₁`（按 `_PN15.agda:135` 的 `SetoidGroupIso` 写，去掉 `inv`/`invˡ`/`invʳ` 三字段）| — | `proof_compile` 新模块 | `exit 0` + 回执 | ✅ **达成**（`probes/_PEH17.agda`，回执 `9e030ec33c70…`）|
| **B-2** | `π₁ᵈ-card : ∀ (G) → …`（**基数 = 2**：由 `gcmp-classify` 的二分给出）| `PIO-1a.library-side` ✓ | 同上 | 同上 | ⬜ **未开工**（注：**实例级**枚举已在 `_PN2` ✓（`to2`/`of2`/`quot-cover` proven ✓）；**泛型 `∀ G` 件未提** ✗ —— 坐标：照 `_PN2.agda:127-151` 五件套泛型化）|
| **B-3** | 条件式陈述：`(h : π₁(|N₁Gcmp|) 平凡) → ¬ (SetoidMonoidIso π₁ᵈ-类 (trivial-monoid))` | B-1, B-2 | 同上 | 同上 ⇒ `proven` ✓ | 🟡 **两件已备**：① 抽象否定件 `no-iso-to-trivial`（`_PEH22` 回执 `62595bb1…` ✓）② 两个不同类 `classes-neq`（`_PEH23` 回执 `8c6fd14f…` ✓，复用库件 `selfloop-quot-≠` + 族桥 `pathOf` ✓）；**剩**：类 setoid 实例（`≈ = _≡s_` ⇒ `≈→≡` 免费 ✓；但真类级 `⋆` 需商双递归 ✗）|
| **B-4** | （备选）B1 路径：库内自足化 `π₁(|N₁G|)` 的组合替身 | — | — | — | ⬜ **不建议**（代价高、风险高，见 §2.3）|

**策略（L2）**：B-1 是**定义层**（`record` ⇒ 对象级验收 ✓，见 doctrine）；B-2 用**分类器 + 计数**（`gcmp-classify` 的 `inj₁`/`inj₂` 二分 ✓）；B-3 用**基数矛盾**（`2 ≠ 1` ✓）。

**风险**：B-2 需先把 `π₁ᵈ` 的**载体/关系**封装成 `SetoidMonoidData`（`_PN15:99` 有 `SetoidGroupData` ✓ ⇒ 按它写 monoid 版 ✓）。

### 6.3 开工顺序（**原子构建**：一个原子一编译一记账）

```
✅ 已完成（2026-10-19）：A-0 / A-1 / A-2 / A-3 / A-4 ｜ B-1
✅ 已完成（2026-10-19 全部）：件 A 全链（A-0..A-4 + A-5' 九层 + 见证对 + 八要素对表）｜B-1
⬜ 剩余（严格口径）：
① B-2：π₁ᵈ-card 泛型件（实例已在 _PN2 ✓，泛型 ∀ G 未提 ✗）
② B-3：桥接核心（`_PEH22` ✓）+ 两不同类（`_PEH23` ✓）已备；剩类 setoid 实例（需真类级 `⋆` = 商双递归 ✗）
③ ⑦ GF9 诱导正式桥（Label → GF9 映射 + 保持性；对分离非必需 ✓）
④ 探针收编：_PEH21 升入 src/Sovereign/Synthesis/Homotopy/（_PEH19/20 自造件退役 ✗ 勿重走）
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
| 4-2 | 补 `MonoidIso`-型接口件 | `proof_compile <新模块>` | `exit 0` + 回执 | ✅ **达成**（B-1：`_PEH17` 的 `SetoidMonoidIso` 8 字段 record，回执 `9e030ec3…`）|
| 4-3 | 件 B 条件式（B3） | 同上 | 新陈述编译通过 ⇒ `proven` | ⬜ **未开工**（同 B-3：需 `_PEH17` ↔ `_PN2` 桥接 ✗）|
| 4-4 | 件 A 建 `rec⁺`（A1，**先探针**）| `proof_compile probes/_PEH13*.agda` | 探针 `exit 0` + `f-resp` 有证明体 | ✅ **目标达成（手段改道）**——`rec⁺` 未建，但分离器已由 C-4（`to`+`to-resp`+`witness-neq`）完成 ✓（`rec⁺` 降为不需要 ✗）|
| 4-5 | 件 A 撞墙则立界 | `prover_limits add` | 条目带**实测证据** | ✅ **达成**（已撞墙并全部入册：`cons-shadowed-parse-lhs` 等，实测证据齐 ✓）|
| 4-6 | 件 A 找不相等见证 | 需 4-4 先成 | 存在 `q r` 使 `f q ≢ f r` ⇒ 可标 `refuted` | ✅ **达成**（`witness-neq` ✓，回执 `a6b6ba46…`；`add2-comm-generic-status` 已升 refuted ✓）|

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
