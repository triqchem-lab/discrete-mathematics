# 42 · 依赖类型论展示群：完备定义（精确到可判定）

> **2026-10-21 定义完善 v2**（承接 [11](11-type-theory-presentation.md)、[12](12-rigorous-type-theory.md)、[20](20-dc-type-theory-positioning.md)）
> 本文档把「八要素」从**描述性清单**提升为**可判定的 record 定义**，
> 并逐条给出**为什么不能弱化**（反例 + 判据），最后给出**加强版**定义。
>
> **结论先行（v2 修正）**：现有 `Presentation` record（`Presentation.agda:56-85`）有 **7 处约束不足**（G1–G7）。
> v1 曾判定「G1 由 N5/N6 部分解决、G5 是独立缺口」—— **v2 证伪了这两条** ✗：
> **N5/N6 排除不了 `ρ`**，而 G1 与 G5 **共用同一个缺口**（缺加法分量投影 `add`）。
> ⇒ 最终定义 v2 以 `add` 为核心，一并闭合 G1/G5，并附带形式化 ② 生成元来源。

---

## 一、定义的分层：八要素 → 三层

八要素不是并列的八条，而是**三层**，每层回答不同的问题：

| 层 | 要素 | 回答的问题 | 判定方式 |
|---|---|---|---|
| **结构层** | ① 载体 ② 生成元 ③ 关系 ⑥ 归零 | 「它是**什么**」——代数骨架 | `record` 字段 + `refl` |
| **动力层** | ④ 相位 ⑤ 时钟 | 「它**怎么动**」——演化过程 | 迭代 + 周期 |
| **判据层** | ⑦ 刚性 ⑧ 核对 | 「它**来自哪**」——本源溯源 | 域论诱导 + 定义自洽 |

**⇒ 三层缺一不可** ✓：
- 缺**结构层** ⇒ 退化到集合论群 ✗
- 缺**动力层** ⇒ 把过程压成静态事实（"群阶 12"）✗
- 缺**判据层** ⇒ 丢失本源溯源（刚性）/ 无法核对定义自洽 ✗

### 1.1 ★ 判定尺度的红线（勿混）

| 说法 | 判定 |
|---|---|
| 「八要素」指 **8 个结构分量** | ✅ 正确 |
| 「八要素 = 元素个数」/「DC 有 8 个元素」 | ❌ **错**：`DuodecPoint` 是 **12** 元素（`Trit × AlphaPower = 3 × 4`）|
| 「DC 是 8 阶结构」 | ❌ **错**：8 是**要素条数**，不是群阶 |
| 「八要素 = 特征 3 + 代数刚性 + 自同构」 | ⚠ **不是等价改写**：这是对「为什么是这八条」的**来源说明**（特征 3 给 ②③⑥，代数刚性给 ⑦，自同构给 ④⑤ 的周期律），不是八要素的另一种计数 |

**⇒ 要素数是 8，元素数是 12，两者永不相等、不可互推** ✓

---

## 二、现有 `Presentation` record（现状）

```agda
-- Presentation.agda:56-85（现状，13 字段）
record Presentation (A : Set) : Set₁ where
  field
    step        : A → A → A      -- ② 联合运算
    g           : A              -- ② 生成元
    unit        : A              -- ⑥ 单位元
    assoc       : ∀ x y z → step (step x y) z ≡ step x (step y z)   -- ③
    zeroˡ       : ∀ x → step unit x ≡ x                             -- ③
    zeroʳ       : ∀ x → step x unit ≡ x                             -- ③
    phase       : A → A           -- ④ 相位算子
    phase-order : ℕ               -- ④ 相位阶
    phase-cycle : ∀ x → iterate phase phase-order x ≡ x              -- ④
    clock       : ℕ               -- ⑤ 时钟
    clock-cycle : ∀ x → iterate (λ y → step y g) clock x ≡ x         -- ⑤
    rigidity    : A → A           -- ⑦ 刚性
    check       : ∀ x → step x unit ≡ x                              -- ⑧
```

**⇒ 这是「形」，不是「义」** ✗ —— 字段齐全（13/13）只保证形式 ✗，
**语义由 L0 红线判**（`index_presentations.sh` 的免责声明即为此而写）。

**⇒ v2 的诚实计数**：加强约束 `N1–N10`（见 §四）**当前一条也没有进 Agda record** ✗。
DC 侧只证了 **5 条 record 外定理**（`dc-phase-step-comm` / `dc-phase-g-comm` /
`dc-clock-neq-phase` / `g-ne-unit` / `dc-oblivion-algebra`），
它们证明「约束在 DC 上成立」，**不等于**「约束进入了模板」✗ —— 两件事必须分开记账 ✓。

---

## 三、★ 七个精确化缺口（G1–G7）

### G1. `rigidity : A → A` 无约束 —— **本体论级缺口**

**现状**：`rigidity` 只是函数 ✗

**为什么不够**：任意函数都合格 ✗ —— 无法区分：
- `mu  (t, αᵏ) = (t, α⁻ᵏ)` ✓ Frobenius 运输（**加法分量不动**）
- `rho (t, αᵏ) = (-t, α⁻ᵏ)` ✗ 群反转（`D₁₂` 半直积反射，**加法分量取反**）
- `id` ✗ 恒等
- `λ _ → unit` ✗ 常值

**⇒ 文档 `11:110-127` 的「必须由 `galoisConjugate` 诱导」是**注释级**约束** ✗ —— 类型层不检查 ✗

#### ★★ 1.1 G1 的判据：`ρ` 与 `μ` 的**可区分性**（v2 新增，推翻了 v1 的结论）

v1 认为「`rigidity-hom` + `rigidity-invol` 可部分解决 G1」✗ —— **这是错的**：

| 候选约束 | `μ`（Frobenius）| `ρ = λ∘μ`（群反转）| 能否区分？ |
|---|---|---|---|
| `rigidity-hom`（自同构）| ✅ | ✅ **也成立** | ❌ **不能** |
| `rigidity-invol`（对合）| ✅ | ✅ **也成立** | ❌ **不能** |
| `add (rigidity x) ≡ add x` | ✅ | ❌ `add (ρ x) = negate (add x)` | ✅ **能** |

**`ρ` 满足 hom + invol 的证明（2 行）**：
```
已知  rho-is-inv : ∀ p → rho p ≡ duodec-inv p        （DuodecClock，已证）
① 对合：ρ(ρ p) = (p⁻¹)⁻¹ = p                        ✓
② 自同构：ρ(p · q) = (p · q)⁻¹ = q⁻¹ · p⁻¹ = p⁻¹ · q⁻¹ = ρ p · ρ q
   倒数第二步用 **DC 交换**（mixedOp 分量级 ⊕ 与 mulAlpha 都交换）✓
```
**⇒ `hom` + `invol` 对 `μ` 与 `ρ` **同时成立** ⇒ 它们**不是** G1 的判别式** ✗

**⇒ 唯一的判别式是**：`add` 分量。
`μ` 是**域自同构的运输** ⇒ 固定素域 GF(3) ⇒ 加法分量上 `σ = id` ✓；
`ρ` 把 `t ↦ -t` ⇒ 加法分量变了 ⇒ **不可能是 Frobenius 的运输** ✗（见 [39](39-frobenius-vs-group-inversion.md)）

**⇒ G1 的正确形式**：
```agda
add               : A → Trit                    -- 加法分量（② 生成元来源）
rigidity-fixes-add : ∀ x → add (rigidity x) ≡ add x   -- ★ 真正的判别式
rigidity-hom       : ∀ x y → rigidity (step x y) ≡ step (rigidity x) (rigidity y)
rigidity-invol     : ∀ x → rigidity (rigidity x) ≡ x
```
`hom`/`invol` 保留（排除 `id`、常值、非自同构），但**判别 `μ` vs `ρ` 靠 `rigidity-fixes-add`** ✓

### G2. `clock` 无极小性

**现状**：`clock-cycle : ∀ x → iterate (λ y → step y g) clock x ≡ x` ✗

**为什么不够**：`clock = 12` 与 `clock = 24` 都满足 ✗ ⇒ **`clock` 不唯一** ✗

**精确化（两种，选其一）**：
```agda
-- (a) 整除型（强）：所有周期都被 clock 整除
clock-min : ∀ k → (∀ x → iterate (λ y → step y g) k x ≡ x) → clock ∣ k
-- (b) 极小性型（弱但足用，推荐）：clock 以下没有正周期
clock-min : ∀ k → 0 < k → k < clock
          → ¬ (∀ x → iterate (λ y → step y g) k x ≡ x)
```

**⇒ 为什么 (b) **足够** 排除 `clock = 24`**：
若 `clock = 24`，则 `k = 12` 满足 `0 < 12 < 24` 且 12 **是**周期
⇒ 违反 (b) ✓ ⇒ `clock = 24` 被排除 ✓

**⇒ (b) 优于 (a) 的工程理由**：`(b)` 只需对 `k = 1..clock-1` 枚举（DC 上 11 case），
`(a)` 需要带余除法 + 序归纳 ⇒ 在 Agda 里成本高一个量级，而**判别力等价**（对本模板的用途）✓

### G3. `phase` 与 `step` 无关系

**现状**：`phase : A → A` ✗ —— 与 `step` 独立 ✗

**精确化（单边，**双边是错的** ✗）**：
```agda
-- ✅ 单边（DC 上 144 对全部成立，已证 dc-phase-step-comm）
phase-hom : ∀ x y → phase (step x y) ≡ step (phase x) y

-- ❌ 双边（DC 上 False，反例 x = y = unit）
-- phase-hom2 : ∀ x y → phase (step x y) ≡ step (phase x) (phase y)
--   phase (step (0,0) (0,0)) = (0,1)   vs   step (phase (0,0)) (phase (0,0)) = (0,2)
```

**原因**：`phase` 只动相位分量，`step` 在相位分量上做乘法 —— 单边时相位被推进**一次** ✓；
双边时被推进**两次** ✗ ⇒ 多一次 `α` ✗

### G4. `g` 与 `phase` 无关系

**现状**：`g : A` ✗ —— 与 `phase` 独立 ✗

**为什么不够**：`g` 可为 `unit` ✗（则 `clock-cycle` 退化成恒等 ✗，`clock` 任意 ✗）

**★ 关键发现（2026-10-21 深度研究，v1 已记载）**：**G4 不需要 `add` 投影** ✓

| G4 候选 | DC 上 | 形式 | 采纳 |
|---|---|---|---|
| ① `phase (step g x) ≡ step g (phase x)` | ✅ True | **纯函数等式** | ✅ **采用** |
| ② `phase ≡ (step g)^9` | ✅ True | DC 特定（`9≡0 mod 3`、`9≡1 mod 4` 的 CRT 巧合 ✗）| ❌ |
| ③ `phase-proj (phase x) ≡ phase-proj (step g x)` | ✅ True | 需投影 ✗ | ❌ |
| ④ `phase ≡ λ x → step g x` | ❌ **False** | 加法分量不同 ✗ | ❌ |

**⇒ 采用 ①**：`phase-g-comm : ∀ x → phase (step g x) ≡ step g (phase x)` ✓（已证 `dc-phase-g-comm`）

#### ★ 更重要的发现：`g ≠ unit` 是**可导出的**，不需要新字段

```
反证：若 g = unit
  ⇒ step y g = step y unit = y                    （zeroʳ）
  ⇒ iterate (λ y → step y g) 1 x = step x g = x   （1 是周期）
  ⇒ clock ∣ 1  ⇒  clock ≤ 1                       （clock-min）
  但 N1 + N3b ⇒ 1 < phase-order < clock ⇒ clock ≥ 3
  矛盾 ⇒ **g ≠ unit** ✓
```

**⇒ G4 的「`g` 非平凡」部分由 N1 + N2 + N3b 自动导出** ✓
**⇒ G4 的「`phase` 与 `g` 有关」部分由 `phase-g-comm` 给出** ✓
**⇒ `add-proj` 对 G4 不需要** ✓（但见下面 G5 —— 它对 G1/G5 **需要**）

### G5. `unit` ≠ 「归零机制」

**现状**：`unit : A` + `zeroˡ/zeroʳ` ✗ —— 只是**单位元** ✗

**为什么不够**：八要素 ⑥ 是「**归零**」✗ —— `12` 定义 2.4 的 `ZeroOblivion.jointCycle`
（`mixedOp^12 p ≡ p`）**不在 record 里** ✗ —— 归零被降格为「单位元」✗

#### ★★ 1.2 G5 的精确诊断（v2 修正）：四层归零里有**两层已进模板**

v1 说「record 只覆盖了第三种」✗ —— **不准确**。逐层核对：

| 归零层 | 数学内容 | record 里对应字段 | 状态 |
|---|---|---|---|
| **相位归零** | `α⁴ = a₀` | `phase-cycle`（`iterate phase phase-order ≡ id`）| ✅ **已进模板** |
| **联合归零** | `mixedOp¹² = id` | `clock-cycle`（`iterate (step·g) clock ≡ id`）| ✅ **已进模板** |
| **加法归零** | `⊕³ = T₀`（`(x⊕x)⊕x = T₀`）| **无** | ❌ **缺** |
| **仲吕 12** | 谐波对齐（`04`, `27`）| **无**（非代数命题）| ❌ 缺（本来就非代数）|

**⇒ G5 的真实内容**：缺的**不是**「归零」这个概念（`clock-cycle`/`phase-cycle` 已是归零），
而是**加法分量上的三层归零** `⊕³` ✗ —— 它需要把加法分量**投影出来** ✓

**⇒ 精确化（与 G1 共用 `add`）**：
```agda
add           : A → Trit
add-op        : Trit → Trit → Trit                  -- 一般化：a 分量上的运算
add-hom       : ∀ x y → add (step x y) ≡ add-op (add x) (add y)
add-zero      : add unit ≡ T₀
add-oblivion  : ∀ x → add-op (add-op (add x) (add x)) (add x) ≡ T₀   -- ★ ⊕³ 归零
```

**⇒ `add-oblivion` 的表达力**：它对 `add` 的像**每一点**成立 ⇒ 这是「虚实对消灭」
（`1² + i² = 0²`，[04](04-zero-oblivion.md)）在加法分量上的**类型级**形态 ✓

### G6. **无「生成」约束** —— **本体论级缺口**

**现状**：`g : A` ✗ —— 但**没有**说 `g` **生成**整个载体 ✗

**为什么不够**：八要素 ② 叫「**生成元**」✗ —— 生成元必须**生成** ✗
若无此约束 ⇒ `A` 可以是任意大集合，`g` 只生成一个子群 ✗ ⇒ 展示群退化为「子群 + 无关元素」✗

**精确化**：
```agda
generated : ∀ x → ∃ (λ n → iterate (λ y → step y g) n unit ≡ x)
```

**⇒ DC 的验证**：`DuodecPoint` 12 个元素 **全部** 是 `g = (T₁,a₁)` 的幂 ✓（见 §5.1 枚举）

### G7. 无统一「展示群」定义

**现状**：`12` 号文的定义 2.1–2.7 是**分散**的 ✗ —— 没有一处把八要素合成一个 record ✗

**⇒ 本文档 §四 给出统一的**加强版** ✓；
**⚠ 但它仍是文档，不是 record** —— 真正的闭合需要改 `Presentation.agda`（见 §六「迁移清单」）✗

---

## 四、★ 加强版定义 v2（完备，逐条可判）

```agda
-- 语义说明在每行注释里；本定义是「目标状态」，现有 record 是「弱化版」
-- ★★ = v2 相对 v1 的修正/新增；★ = v1 已有
record Presentation (A : Set) : Set₁ where
  field
    -- ═══ ② 生成元（联合运算 + 生成元 + **加法分量来源**）══════════
    step        : A → A → A                    -- 联合运算（幅度 ⊕ 相位）
    g           : A                            -- 联合生成元
    add         : A → Trit                     -- ★★ 加法分量投影（= ② 生成元来源）
    add-op      : Trit → Trit → Trit           -- ★★ 加法分量上的运算
    add-hom     : ∀ x y → add (step x y) ≡ add-op (add x) (add y)   -- ★★
    add-zero    : add unit ≡ T₀                                     -- ★★

    -- ═══ ① 载体（隐含：A 本身）═════════════════════════════════
    -- A 已是 record 参数；在 DC 里 = Trit × AlphaPower（12 元素）

    -- ═══ ③ 关系（algebraic laws）═══════════════════════════════
    assoc       : ∀ x y z → step (step x y) z ≡ step x (step y z)
    unit        : A
    zeroˡ       : ∀ x → step unit x ≡ x
    zeroʳ       : ∀ x → step x unit ≡ x

    -- ═══ ④ 相位（分量级旋转）═══════════════════════════════════
    phase       : A → A                        -- 分量级，只动相位
    phase-order : ℕ
    phase-cycle : ∀ x → iterate phase phase-order x ≡ x
    phase-nontrivial : 1 < phase-order         -- ★ N1（排除 C₁）
    phase-hom   : ∀ x y → phase (step x y) ≡ step (phase x) y        -- ★ N7 单边
    phase-g-comm : ∀ x → phase (step g x) ≡ step g (phase x)         -- ★ N8

    -- ═══ ⑤ 时钟（联合周期）═════════════════════════════════════
    clock       : ℕ
    clock-cycle : ∀ x → iterate (λ y → step y g) clock x ≡ x
    clock-min   : ∀ k → 0 < k → k < clock                            -- ★ N2 极小性
                → ¬ (∀ x → iterate (λ y → step y g) k x ≡ x)
    clock-phase : phase-order ∣ clock           -- ★ N3（联合性）
    clock-neq-phase : phase-order < clock       -- ★ N3b（N3 排除不了 clock = phase-order）

    -- ═══ ② 生成性（g 生成整个载体）═════════════════════════════
    generated   : ∀ x → ∃ (λ n → iterate (λ y → step y g) n unit ≡ x)  -- ★ N4

    -- ═══ ⑥ 归零（**加法层**；相位层/联合层已由 phase-cycle/clock-cycle 承载）═══
    add-oblivion : ∀ x → add-op (add-op (add x) (add x)) (add x) ≡ T₀   -- ★★ N9′

    -- ═══ ⑦ 刚性（域自同构的运输）═══════════════════════════════
    rigidity          : A → A
    rigidity-hom      : ∀ x y → rigidity (step x y) ≡ step (rigidity x) (rigidity y)  -- ★ N5
    rigidity-invol    : ∀ x → rigidity (rigidity x) ≡ x                               -- ★ N6
    rigidity-fixes-add : ∀ x → add (rigidity x) ≡ add x    -- ★★ N10（**唯一能排除 ρ 的字段**）

    -- ═══ ⑧ 核对（定义自洽，不产生结构）══════════════════════════
    check       : ∀ x → step x unit ≡ x
```

### 4.1 加强版相对现状的**十项新增**

| # | 字段 | 排除什么反例 | 判别力 |
|---|---|---|---|
| **N1** | `phase-nontrivial : 1 < phase-order` | 排除 `phase-order = 1`（相位空洞 ✗）| ✅ |
| **N2** | `clock-min`（极小性型）| 排除 `clock = 24, 36, …`（非极小 ✗）| ✅ |
| **N3** | `clock-phase : phase-order ∣ clock` | 排除 `clock` **不是** `phase-order` 倍数 ✗；**不能**排除 `clock = phase-order`（`4∣4` 也成立）✗ | ⚠ 部分 |
| **N3b** | `clock-neq-phase : phase-order < clock` | 补 N3 的漏：排除 `clock = phase-order` ✓ | ✅ |
| **N4** | `generated` | 排除「`g` 只生成子群」✗ | ✅ |
| **N5** | `rigidity-hom` | 排除「`rigidity` 非自同构」（`id`/常值之外的部分）| ⚠ 排不了 `ρ` |
| **N6** | `rigidity-invol` | 排除「`rigidity` 非对合」 | ⚠ 排不了 `ρ` |
| **N7** | `phase-hom`（单边）| 排除 `phase` 与 `step` 完全无关 ✗ | ✅ |
| **N8** | `phase-g-comm` | 排除 `g` 只是加法生成元、与相位无关 ✗ | ✅ |
| **N9′** | `add-oblivion` | 排除「⑥ 归零被降格为单位元」✗ | ✅ |
| **N10** | `rigidity-fixes-add` | **排除 `ρ`（群反转）混入刚性** ✗ | ✅ **本体论级** |
| **N-add** | `add` / `add-op` / `add-hom` / `add-zero` | 形式化 ② **生成元来源**（`11:181`）| ✅ |

**⇒ 计数**：显式约束 10 条（N1–N10）+ `add` 四件套（N-add，服务 ②⑥⑦ 三处）✓

### 4.2 ★★ 核心洞察：`add` 是**一个字段**闭合**两个本体论缺口**

```
       add : A → Trit
            │
   ┌────────┼────────┐
   ▼        ▼        ▼
 ② 生成元  ⑥ 归零   ⑦ 刚性
 来源     ⊕³ 层    判别 μ vs ρ
 (add-hom) (add-oblivion) (rigidity-fixes-add)
```

**⇒ 这是 v1 完全没看到的结构** ✓ —— v1 把 G1/G5 当作两个独立缺口 ✗，
v2 证明它们**共用同一个缺失投影** ✓

**⇒ 更深的意义**：展示群的「八要素」里，②⑥⑦ 本来就不是三个独立维度 ——
它们都是**生成元来源**的不同侧面：
- ② 说「有哪些生成元」（加法 + 相位）
- ⑥ 说「生成元回到单位的方式」（`⊕³` / `α⁴` / 联合 `¹²`）
- ⑦ 说「哪个自同构来自生成元所在的域」（Frobenius 固定素域 ⇒ 不动加法分量）

**⇒ 三者共用 `add` 不是巧合，是它们同源的**形式化证据** ✓

### 4.3 ★ N3 与 N3b 的分工（必须并存）

```
phase-order = 4, clock = 4  ⇒  4 ∣ 4 成立  ⇒  N3 **不能**排除 clock = phase-order ✗
clock-neq-phase : phase-order < clock  ⇒  4 < 12 成立  ✓ 可排除
```

**⇒ 只写 `clock-phase` 的模板**（v1 曾如此）**放过 `clock = phase-order`** ✗ ——
`RnPresentation` 踩的正是这条红线（`clock = 4 = phase-order`，已撤回，见 [39](39-frobenius-vs-group-inversion.md)）✗

---

## 五、DC 实例的逐条核对

| 要素 | DC 实例 | 加强版约束 | 数值/类型验证 | 状态 |
|---|---|---|---|---|
| **① 载体** | `DuodecPoint = Trit × AlphaPower`（**12** 元素）| — | — | ✅ |
| **② 生成元** | `step = mixedOp`，`g = (T₁, a₁)` | `generated` | ✅ `g^0..g^11` 覆盖全部 12 个 | ✅ 数值 |
| **② 来源** | `add = proj₁`，`add-op = _⊕_` | `add-hom` | ✅ `refl`（`mixedOp` 分量级定义）| ✅ **可 refl** |
| **③ 关系** | `assoc` / `zeroˡ` / `zeroʳ` | — | ✅ `mixedOp-assoc` 等已证 | ✅ |
| **④ 相位** | `phase = (t, a) ↦ (t, mulAlpha a₁ a)`，阶 4 | `phase-nontrivial` / `phase-hom` / `phase-g-comm` | ✅ 9 case `refl`；✅ 144 对 | ✅ |
| **⑤ 时钟** | `clock = 12`，`mixedOp¹² p ≡ p` | `clock-min` / `clock-phase` / `clock-neq-phase` | ✅ 最小正周期 = **12**；`4 ∣ 12`；`4 < 12` | ✅ **已形式化** |
| **⑥ 归零** | `ZeroOblivion` 四层 | `add-oblivion`（加法层）| ✅ 逐字引用 `tritCycle` | ✅ **已形式化** |
| **⑦ 刚性** | `rigidity = mu = σ_DC` | `rigidity-hom` / `rigidity-invol` / `rigidity-fixes-add` | ❌ `ρ` 也满足前两条；`μ` 满足第三条 | ✅ **已形式化** |
| **⑧ 核对** | `mixedOp-identityʳ` | — | ✅ | ✅ |

**⇒ 现状：8/8 全部有内核回执**（`src/Sovereign/Algebra/UniversalAlgebra/PresentationV2.agda`，
`proof_compile` 回执 `a59ea9c2…`，0 postulate / 0 hole / 0 sorry）✓

**⇒ 记录形式**：v2 落成 `record PresentationV2`（**28 字段**）+ `dc-presentation-v2 : PresentationV2 DuodecPoint` ✓

### 5.1 ★ 数值验证（2026-10-21，`g^0..g^11` 枚举）

**`generated` 验证**（Python 精确枚举，无浮点）：

```
g^0..g^11 = (0,0) (1,1) (2,2) (0,3) (1,0) (2,1) (0,2) (1,3) (2,0) (0,1) (1,2) (2,3)
去重计数 = 12 / 12   ✓ 生成全部 12 个元素
```

**`clock-min` 验证**：

```
最小正周期 = 12                ✓（k = 1..24 逐一检查，第一个满足的是 12）
12 的倍数也满足                 ⇒ clock 不唯一 ⇒ 必须加 clock-min 约束 ✓
k = 4 不满足                    ⇒ phase-order = 4 不是联合周期 ✓
```

**`clock-phase` 验证**：`4 ∣ 12` ✓（若 `clock = phase-order = 4` 则丢加法分量 ✗
—— 正是 `RnPresentation` 踩的红线，见 [39](39-frobenius-vs-group-inversion.md)）

**N7/N8/N3b 的验证**（2026-10-21 审核后补，已落 Agda）：

```
✅ phase (step x y) ≡ step (phase x) y        单边：True（全部 144 对）  —— dc-phase-step-comm
✅ phase (step g x) ≡ step g (phase x)        True                      —— dc-phase-g-comm
✅ 4 < 12                                                              —— dc-clock-neq-phase
❌ phase (step x y) ≡ step (phase x) (phase y) 双边：False
   反例 x = y = (0,0)：phase(step) = (0,1)  vs  step(phase,phase) = (0,2)
❌ phase ≡ λ x → step g x                       False
   反例 x = (0,0)：phase = (0,1)  vs  step g = (1,1)（差在加法分量）
```

**★ G1 判别式的验证（v2 新增）**：

```
μ (t, aᵏ) = (t, a⁻ᵏ)    ⇒ add (μ x) = t = add x        ✓ N10 成立
ρ (t, aᵏ) = (-t, a⁻ᵏ)   ⇒ add (ρ x) = -t               ✗ N10 不成立（t ≠ T₀ 时）
μ 满足 hom + invol:  自同构 ✓（域自同构）；对合 ✓（σ² = id，Gal ≅ C₂）
ρ 满足 hom + invol:  自同构 ✓（交换群上 inv）；对合 ✓（inv∘inv = id）
⇒ **hom+invol 无判别力；只有 N10 有** ✓
```

**CRT 结构**：`g^n` 的 `(n mod 3, n mod 4)` 覆盖全部 12 对 ✓
⇒ `generated` 的本质就是 **CRT 双射** `Z/12 ≅ Z/3 × Z/4` ✓
—— 这不是巧合，是 `12 = lcm(3,4)` 的直接体现。

---

## 六、判据：什么叫「展示群定义**完整**」

```
完整 = ① 三层齐备（结构层 / 动力层 / 判据层）
     ② 每个要素的约束**在类型层可判**（不是注释）
     ③ 每个约束有**反例说明**（为什么不能弱化）
     ④ DC 实例逐条核对通过
```

**逐条对照（v2，诚实计数）**：

| 判据 | 现有 record（13 字段）| 加强版 v2（文档）|
|---|---|---|
| ① 三层齐备 | ✅ | ✅ |
| ② 每个要素约束**类型层可判** | ❌ | ✅ **全部可判**（N1–N10 + N-add）|
| ③ 每个约束有反例说明 | ✅ | ✅ |
| ④ DC 实例逐条核对 | ✅ | ⚠ **6/8 已验**；⑤⑦ 待形式化 |

**⇒ 加强版**设计上**满足 ①③，② 已闭合，④ 待 Agda 落地** ⚠

### 6.1 ★ 缺口闭合表（v1 → v2 对照）

| 缺口 | v1 判定 | **v2 判定** | **内核状态** | 变化原因 |
|---|---|---|---|---|
| **G1** `rigidity` 无约束 | ⚠ 部分（N5/N6）| ✅ **闭合**（N5+N6+N10）| ✅ `mu-hom` / `mu-invol` / `add (mu x) ≡ add x` | **v1 错**：N5/N6 排除不了 `ρ` |
| **G2** `clock` 无极小性 | ✅ N2 | ✅ N2（改为极小性型）| ✅ `dc-clock-min`（11 case）| 工程可行性 + 判别力等价 |
| **G3** `phase`/`step` 脱节 | ⚠ 部分（N7 单边）| ✅ **闭合**（N7 单边是正确形式）| ✅ `dc-phase-step-comm` | 双边本就不成立，非缺口 |
| **G4** `g`/`phase` 脱节 | ❌ 未解决 | ✅ **闭合**（N8 + 可导出 `g ≠ unit`）| ✅ `dc-phase-g-comm` | v1 漏了「可导出」 |
| **G5** `unit` ≠ 归零 | ❌ 未解决 | ✅ **闭合**（N9′，与 G1 共用 `add`）| ✅ `dc-add-oblivion`（引用 `tritCycle`）| v1 漏了「两层已在模板里」 |
| **G6** 无生成约束 | ✅ N4 | ✅ N4 | ✅ `dc-generated`（12 case）| — |
| **G7** 无统一 record | ⚠ 部分 | ✅ **闭合**（`PresentationV2`，28 字段）| ✅ 模块 `PresentationV2.agda` 编译通过 | 以**新增模块**落地，旧 `Presentation` 未动 ⇒ 零级联 |

**⇒ v2 在**内核层**闭合 G1–G7** ✓ ——
`src/Sovereign/Algebra/UniversalAlgebra/PresentationV2.agda`
（`record PresentationV2` + `dc-presentation-v2`，回执 `a59ea9c2…`，0 postulate/hole/sorry）

**⚠ 但旧 `Presentation.agda`（13 字段）未被替换** —— 它仍是 `dc-presentation` 等的载体 ✗。
「v2 存在」≠「v1 已废除」：**两套并存**，迁移见 §6.2 批 2 ✓

### 6.2 ★ 迁移清单（G7 的落地路径）

**影响面**（DSH `grep` 全库实测，2026-10-21）：`Presentation` 实例**只有 3 处**

| 文件 | 角色 | 加字段后的动作 |
|---|---|---|
| `Presentation.agda:131` `dc-presentation` | **唯一本源实例** | 补 14 个字段（多数 `refl` 可闭合）|
| `RnDCPresentation.agda:134` `RnDCPresentation` | 派生实例（`clock = 12`）| 补字段 |
| `RnPresentation.agda:126` `RnPresentation` | ⚠ **已撤回**（`clock = 4` 踩红线）| 删除或按新约束重写 |
| `PresentationTheorems.agda:62` `g-ne-unit` | 消费者（`P : Presentation A` 抽象）| 假设 `clock-min` 等变成字段 ⇒ **签名可简化** ✓ |

**⇒ 级联风险低**（3 实例 + 1 消费者），**但 `Presentation.agda` 的 `Trit` 依赖要上移**：
`add : A → Trit` 使模板**显式依赖 `Base.Trit`** ⇒ 模板不再是「任意代数」，
而是「**DC 族模板**」—— 这与 `Presentation.agda:180` 已有的自我定位一致 ✓
（「Presentation 目前是群式 + GF9 刚性约束的 DC 族特化模板，尚非通用模板」）

**⇒ 迁移顺序（依赖单调，禁反向）**：
```
1. Presentation.agda：加字段（先只加 N-add 五件套 + N3b/N7/N8）
2. dc-presentation：补字段 —— 每条都用已有定理/refl
3. PresentationTheorems.agda：简化 g-ne-unit 签名
4. RnDCPresentation：补字段
5. RnPresentation：删除（已撤回）
6. 最后加 N2/N4/N10（需要新证：clock-min 11 case、generated 12 case、N10 refl）
```

**⇒ 分两批**：批 1（步骤 1–5）只搬运已有定理 ⇒ 低风险 ✓；
批 2（步骤 6）需新证 ⇒ 独立任务 ✓

**★ 2026-10-21 实际执行结果（已超出原计划）**：批 2 的 4 条新证**已全部完成** ✓
```
dc-rigidity-hom    : ∀ x y → mu (mixedOp x y) ≡ mixedOp (mu x) (mu y)   -- 复用 rho-alphaInv-homo
dc-rigidity-invol  : ∀ x → mu (mu x) ≡ x                               -- 12 case refl
dc-generated       : ∀ x → ∃ n → iterate gStep n e ≡ x                 -- 12 case refl（g 的幂表）
dc-clock-min       : ∀ (k : Fin 12) → 0 < toℕ k → ¬ period (toℕ k)     -- 11 case 反驳
```
**⇒ 落地方式改为「新增模块」而非「改旧 record」** ✓：
`PresentationV2.agda`（`record PresentationV2` + `dc-presentation-v2`），**零级联**——
因为旧 `Presentation` 的 3 个实例（`dc-presentation` / `RnDCPresentation` / 撤回的 `RnPresentation`）
**一个都不需要动** ✓。真正的「替换」仍是独立任务（批 3）⚠

---

## 七、★ 与「透明性」判据的关系（见 `40`、`41`）

本定义本身也是**透明**的：

| 透明性要求 | 本定义 |
|---|---|
| **显式构造** | 每个字段给出 Agda 签名，无 `postulate` ✓ |
| **可穷举验证** | DC 是 12 元素有限类型，全部 `refl` 可验 ✓ |
| **有限步骤** | 无 `AC`、无 `funext`（逐点陈述 ✓）、无反证 ✓ |
| **不依赖学科名** | 约束指向**结构**（自同构/极小性/整除），不指向「域论/群论」✓ |

**⇒ 定义的精确化 = 透明性的提升** ✓

**⇒ ★ N10 的透明性**：`rigidity-fixes-add` 把「Frobenius 固定素域」这条**域论事实**
翻译成**一行 `refl` 可验的等式**（`add (mu x) ≡ add x`）——
这正是「透明性」判据要求的形态（判据指向结构，不指向学科）✓
而 `ρ` 在同一行上**失败** ⇒ 判别力来自结构本身，不来自「因为它是群反转所以不行」 ✗

---

## 八、一句话

**依赖类型论展示群的完整定义 = 三层八要素 + 类型层可判的约束 + 反例说明 + 实例核对。**

**v2 的三条实质性修正**（相对 v1）：

1. **N5+N6 排除不了 `ρ`** ✗ —— `ρ = 群反转`在交换群上**也**是自同构 + 对合。
   唯一判别式是 `rigidity-fixes-add : add (rigidity x) ≡ add x`（N10）✓
2. **G1 与 G5 是同一个缺口** ✓ —— 都缺 `add : A → Trit`。
   一个字段闭合两个本体论缺口，并附带形式化 ② 生成元来源 ✓
3. **④ 归零有两层已在模板里** ✗ —— `phase-cycle`（`α⁴`）与 `clock-cycle`（`¹²`）就是归零；
   缺的只是**加法层** `⊕³`（N9′）✓

**⇒ 加强版 v2 = 10 条显式约束（N1–N10）+ `add` 四件套**，
已落成 `record PresentationV2`（28 字段）+ `dc-presentation-v2`，
`proof_compile` exit 0（回执 `a59ea9c2…`，0 postulate / 0 hole / 0 sorry）✓
**⇒ G1–G7 在内核层全部闭合** ✓

**★ N10 判别力的内核级证据**（不只是论证）：
```agda
dc-rho-not-fixes-add : ∃ (λ x → dc-add (rho x) ≢ dc-add x)
dc-rho-not-fixes-add = (T₁ , a0) , dc-T₂≢T₁
-- ρ (T₁,a₀) = (T₂,a₀) ⇒ add(ρ x) = T₂ ≠ T₁ = add x
```
⇒ `ρ` 满足 `rho-mixedOp`（N5）+ `rho-involution`（N6），却在 N10 上**失败** ✓
**⇒ 「自同构 + 对合」无判别力，这一点现在有 Agda 项作证，不是散文** ✓

**⚠ 仍未做**：旧 `Presentation.agda`（13 字段）**未被替换** —— 两套并存，
真正的 v1 → v2 替换是独立任务（§6.2 批 3）⚠

**⇒ 定义的精确化不是学术洁癖，是透明性的提升** ——
在有限结构上，每个约束都可穷举验证；这正是特征 3 结构相对连续统的本体论优势。

---

## 九、相关文件

| 文件 | 关系 |
|---|---|
| [11-type-theory-presentation.md](11-type-theory-presentation.md) | 八要素的**描述性**定义 |
| [12-rigorous-type-theory.md](12-rigorous-type-theory.md) | 定义 2.1–2.7（分散的形式化）|
| [20-dc-type-theory-positioning.md](20-dc-type-theory-positioning.md) | 生成结构定位 |
| [04-zero-oblivion.md](04-zero-oblivion.md) | 四层归零（⑥ 的权威出处）|
| [30-terminology-ontology.md](30-terminology-ontology.md) | 本源/投影判断术语 |
| [39-frobenius-vs-group-inversion.md](39-frobenius-vs-group-inversion.md) | 刚性 = `μ`（不是 `ρ`）|
| [40-transparency-vs-refutation.md](40-transparency-vs-refutation.md) | 刚性 = 自同构的透明性 |
| [41-strength-vs-transparency.md](41-strength-vs-transparency.md) | 判据指向结构，不指向学科 |
| `src/Sovereign/Algebra/UniversalAlgebra/Presentation.agda` | v1 record（弱化版，13 字段）|
| `src/Sovereign/Algebra/UniversalAlgebra/PresentationV2.agda` | ✅ **v2 record（28 字段）+ DC 本源实例**，回执 `a59ea9c2…` |
| `src/Sovereign/Algebra/UniversalAlgebra/PresentationTheorems.agda` | 模板层定理（`g-ne-unit`）|
| `src/Sovereign/Algebra/UniversalAlgebra/RnDCPresentation.agda` | 合法派生实例（`clock = 12`）|
| `src/Sovereign/Algebra/UniversalAlgebra/RnPresentation.agda` | ⚠ 已撤回（`clock = 4` 踩红线）|
