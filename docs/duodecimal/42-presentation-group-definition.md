# 42 · 依赖类型论展示群：完备定义（精确到可判定）

> **2026-10-21 定义完善**（承接 [11](11-type-theory-presentation.md)、[12](12-rigorous-type-theory.md)、[20](20-dc-type-theory-positioning.md)）
> 本文档把「八要素」从**描述性清单**提升为**可判定的 record 定义**，
> 并逐条给出**为什么不能弱化**（反例 + 判据），最后给出**加强版**定义。
>
> **结论先行**：现有 `Presentation` record（`Presentation.agda:52-85`）有 **7 处约束不足**（G1–G7），
> 其中 **G1（`rigidity` 无约束）** 与 **G6（无生成约束）** 是**本体论级**的缺口。

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

---

## 二、现有 `Presentation` record（现状）

```agda
-- Presentation.agda:52-85（现状）
record Presentation (A : Set) : Set₁ where
  field
    step        : A → A → A      -- ② 联合运算
    g           : A               -- ② 生成元元
    unit        : A               -- ⑥ 单位元
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

---

## 三、★ 七个精确化缺口（G1–G7）

### G1. `rigidity : A → A` 无约束 —— **本体论级缺口**

**现状**：`rigidity` 只是函数 ✗

**为什么不够**：任意函数都合格 ✗ —— 无法区分：
- `mu  (t, αᵏ) = (t, α⁻ᵏ)` ✓ Frobenius 运输
- `rho (t, αᵏ) = (-t, α⁻ᵏ)` ✗ 群反转（`D₁₂` 半直积反射）
- `id` ✗ 恒等
- `λ _ → unit` ✗ 常值

**⇒ 文档 `11:104` 的「必须由 `galoisConjugate` 诱导」是**注释级**约束** ✗ —— 类型层不检查 ✗

**精确化需要**（三选一或组合）：
```agda
-- (a) 刚性是自同构
rigidity-hom : ∀ x y → rigidity (step x y) ≡ step (rigidity x) (rigidity y)
-- (b) 刚性对合
rigidity-invol : ∀ x → rigidity (rigidity x) ≡ x
-- (c) 刚性固定「加法分量」的证据（需要分量投影才可表达）
--     ⇒ 需要 carrier 上有 `add-part : A → Trit` 与 `rigidity-add : ∀ x → add-part (rigidity x) ≡ add-part x`
```

**⇒ 语义判据**：`rigidity` 必须是**域自同构的运输**（`σ` 固定素域 ⇒ 加法分量 `id`）
—— 这是**本源层**判据 ✓，不能用投影层的群论事实 ✗（见 `39` §六、`08 §7.1b`）。

### G2. `clock` 无极小性

**现状**：`clock-cycle : ∀ x → iterate (λ y → step y g) clock x ≡ x` ✗

**为什么不够**：`clock = 12` 与 `clock = 24` 都满足 ✗ ⇒ **`clock` 不唯一** ✗

**精确化**：
```agda
clock-min : ∀ k → (∀ x → iterate (λ y → step y g) k x ≡ x) → clock ∣ k
-- 或：∀ k → 0 < k → k < clock → ¬ (∀ x → iterate (λ y → step y g) k x ≡ x)
```

**⇒ DC 的 `clock = 12` 必须是 `lcm(3,4)` 这个**最小**周期** ✓（不是「12 的倍数」）✗

### G3. `phase` 与 `step` 无关系

**现状**：`phase : A → A` ✗ —— 与 `step` 独立 ✗

**为什么不够**：文档说相位是**分量级**旋转 ✗，但 record 无法表达「`phase` 只动一个分量」✗

**精确化需要**分量投影：
```agda
-- 载体上有相位分量
phase-proj  : A → AlphaPower
phase-lift  : AlphaPower → A → A     -- 只改相位分量
-- 约束
phase-eq    : ∀ x → phase x ≡ phase-lift (mulAlpha (phase-proj x) a1) x
-- 且 step 的第二分量就是相位乘法
step-phase  : ∀ x y → phase-proj (step x y) ≡ mulAlpha (phase-proj x) (phase-proj y)
```

### G4. `g` 与 `phase` 无关系

**现状**：`g : A` ✗ —— 与 `phase` 独立 ✗

**为什么不够**：文档说 `g = (T₁, a₁)` 是**联合**生成元（含相位分量）✗，
但 record 无法保证 ✗ —— `g` 可为 `unit` ✗（则 `clock-cycle` 变成恒等 ✗，`clock` 任意 ✗）

**精确化**：
```agda
g-phase : phase-proj g ≢ phase-proj unit       -- g 的相位分量非平凡
clock-phase : phase-order ∣ clock               -- 相位阶整除时钟
```

**⇒ `clock-phase` 是「联合」的形式化**：`clock = lcm(3,4)` ⇒ `4 ∣ 12` ✓
（若 `clock = phase-order` ✗，则只是相位迭代 ✗ —— **正是 `RnPresentation` 踩的红线** ✗）

### G5. `unit` ≠ 「归零机制」

**现状**：`unit : A` + `zeroˡ/zeroʳ` ✗ —— 只是**单位元** ✗

**为什么不够**：八要素 ⑥ 是「**归零**」✗ —— `12` 定义 2.4 的 `ZeroOblivion.jointCycle`
（`mixedOp^12 p ≡ p`）**不在 record 里** ✗ —— 归零被降格为「单位元」✗

**精确化**：
```agda
-- 归零 = 周期闭合机制，不是单位元
oblivion : ℕ → A           -- 归零阶（如 3 / 4 / 12）
oblivion-cycle : ∀ x → iterate (λ y → step y g) (clock) x ≡ x   -- 联合归零 = clock-cycle
-- 更强：多个归零层
oblivion-layers : ∀ x → step (step x g) g ≡ ...                 -- 三层归零
```

**⇒ DC 的四种归零**（`04-zero-oblivion.md`）：
`⊕³ = id` / `α⁴ = a₀` / `mixedOp¹² = id` / 仲吕 12 ✗ —— record 只覆盖了**第三种** ✗

### G6. **无「生成」约束** —— **本体论级缺口**

**现状**：`g : A` ✗ —— 但**没有**说 `g` **生成**整个载体 ✗

**为什么不够**：八要素 ② 叫「**生成元**」✗ —— 生成元必须**生成** ✗
若无此约束 ⇒ `A` 可以是任意大集合，`g` 只生成一个子群 ✗ ⇒ 展示群退化为「子群 + 无关元素」✗

**精确化**：
```agda
generated : ∀ x → ∃ (λ n → iterate (λ y → step y g) n unit ≡ x)
-- 或：∀ x → ∃ n → （x 可由 g 的 n 次幂到达）
```

**⇒ DC 的验证**：`DuodecPoint` 12 个元素 **全部** 是 `g = (T₁,a₁)` 的幂 ✓
⇒ `iterate (λ p → mixedOp p g) n e` 遍历 12 个元素 ✓

### G7. 无统一「展示群」定义

**现状**：`12` 号文的定义 2.1–2.7 是**分散**的 ✗ —— 没有一处把八要素合成一个 record ✗

**⇒ 本文档 §四 给出统一的**加强版** ✓

---

## 四、★ 加强版定义（完备，逐条可判）

```agda
-- 语义说明在每行注释里；本定义是「目标状态」，现有 record 是「弱化版」
record Presentation (A : Set) : Set₁ where
  field
    -- ═══ ② 生成元（联合运算 + 生成元）══════════════════════════
    step        : A → A → A                    -- 联合运算（幅度 ⊕ 相位）
    g           : A                            -- 联合生成元

    -- ═══ ① 载体（隐含：A 本身）═════════════════════════════════
    -- A 已是 record 参数；在 DC 里 = Trit × AlphaPower

    -- ═══ ③ 关系（algebraic laws）═══════════════════════════════
    assoc       : ∀ x y z → step (step x y) z ≡ step x (step y z)
    unit        : A
    zeroˡ       : ∀ x → step unit x ≡ x
    zeroʳ       : ∀ x → step x unit ≡ x

    -- ═══ ④ 相位（分量级旋转）═══════════════════════════════════
    phase       : A → A                        -- 分量级，只动相位
    phase-order : ℕ
    phase-cycle : ∀ x → iterate phase phase-order x ≡ x
    phase-nontrivial : 1 < phase-order         -- 相位非平凡（排除 C₁）★新增

    -- ═══ ⑤ 时钟（联合周期）═════════════════════════════════════
    clock       : ℕ
    clock-cycle : ∀ x → iterate (λ y → step y g) clock x ≡ x
    clock-min   : ∀ k → (∀ x → iterate (λ y → step y g) k x ≡ x) → clock ∣ k   -- ★新增（极小性）
    clock-phase : phase-order ∣ clock           -- ★新增（联合性：相位阶整除时钟）

    -- ═══ ② 生成性（g 生成整个载体）═════════════════════════════
    generated   : ∀ x → ∃ (λ n → iterate (λ y → step y g) n unit ≡ x)          -- ★新增

    -- ═══ ④/⑤ 动力层耦合（N7–N9，2026-10-21 补）══════════════════
    phase-hom   : ∀ x y → phase (step x y) ≡ step (phase x) y        -- N7 ✓ 单边（双边不成立）
    clock-neq   : phase-order < clock                                 -- N3b ✓ 排除 clock = phase-order
    phase-g-comm : ∀ x → phase (step g x) ≡ step g (phase x)         -- N8 ✓（纯函数等式）
    -- g ≠ unit 由 N1+N2+N3b 自动导出，**不需新字段** ✓
    -- N9：归零机制（G5，本体论级 —— 仍为草案）
    -- oblivion : A → A → A ;  oblivion-cycle : ∀ x → ...

    -- ═══ ⑦ 刚性（域自同构的运输）═══════════════════════════════
    rigidity          : A → A
    rigidity-hom      : ∀ x y → rigidity (step x y) ≡ step (rigidity x) (rigidity y)  -- ★新增（自同构）
    rigidity-invol    : ∀ x → rigidity (rigidity x) ≡ x                               -- ★新增（对合）
    -- ⚠ 关键：rigidity 必须来自 galoisConjugate，且**固定幅度分量**
    --   在 DC 里：sigmaDC (t , a) = (t , alphaInv a)  ✓（幅度不变）
    --   反例 rho (t , a) = (negate t , alphaInv a)    ✗（幅度变了 ⇒ 不是 σ）

    -- ═══ ⑧ 核对（定义自洽，不产生结构）══════════════════════════
    check       : ∀ x → step x unit ≡ x
```

### 4.1 加强版相对现状的**六项新增**

| # | 字段 | 排除什么反例 |
|---|---|---|
| **N1** | `phase-nontrivial : 1 < phase-order` | 排除 `phase-order = 1`（相位空洞 ✗）|
| **N2** | `clock-min` | 排除 `clock = 24, 36, …`（非极小 ✗）|
| **N3** | `clock-phase : phase-order ∣ clock` | 排除 `clock` **不是** `phase-order` 倍数（如 `clock=5, phase-order=4`）✗；**不能**排除 `clock = phase-order`（`4∣4` 也成立）✗ |
| **N4** | `generated` | 排除「`g` 只生成子群」✗ |
| **N5** | `rigidity-hom` | 排除「`rigidity` 非自同构」✗ |
| **N6** | `rigidity-invol` | 排除「`rigidity` 非对合」✗ |

**⇒ N3 表达的是「`clock` 是 `phase-order` 的倍数」，**不是**「`clock ≠ phase-order」** ✗
（`phase-order = 4, clock = 4` 时 `4 ∣ 4` 成立 ✗ —— **不能**排除）

### 4.2 ★ 补充约束 N7–N9（2026-10-21 审核后补，解决 G3/G4/G5）

| # | 字段 | 解决 | 在 DC 上成立？ |
|---|---|---|---|
| **N7** | `phase-hom : ∀ x y → phase (step x y) ≡ step (phase x) y` | **G3 部分**（相位是运算的**左参数自同态**）| ✅ **已验证 True** |
| **N8** | `phase-g-comm : ∀ x → phase (step g x) ≡ step g (phase x)` | **G4**（`phase` 与 `g` 交换）| ✅ **已验证 True**（纯函数等式，**不需投影**）|
| **N9** | `oblivion : A → A → A` + 四层归零约束 | **G5**（归零机制）| ⚠ 需设计 |
| **N3b** | `clock-neq-phase : phase-order < clock` | **N3 不能排除的 `clock = phase-order`** | ✅ `4 < 12` |

#### N7 的正确形式（双边是**错的** ✗）

```agda
-- ❌ 双边（DC 上 False，反例 x = y = unit）
phase-hom2 : ∀ x y → phase (step x y) ≡ step (phase x) (phase y)   -- ✗ 不成立
--   反例：phase (step (0,0) (0,0)) = (0,1)   vs   step (phase (0,0)) (phase (0,0)) = (0,2)

-- ✅ 单边（DC 上 True，已验证）
phase-hom  : ∀ x y → phase (step x y) ≡ step (phase x) y            -- ✓ 成立
```

**原因**：`phase` 只动相位分量，`step` 在相位分量上做乘法 —— 两者**交换** ✓；
但若两边都 `phase`，相位被推进**两次** ✗ ⇒ 双边多了一次 `α` ✗

#### N8 修订（2026-10-21 深度研究后）：G4 **不需要 `add-proj`**

**原方案（需投影）✗** —— 深度研究后发现可简化：

| G4 候选 | DC 上 | 形式 |
|---|---|---|
| ① `phase (step g x) ≡ step g (phase x)` | ✅ **True** | **纯函数等式** ✓ 无需投影 |
| ② `phase ≡ (step g)^9` | ✅ True | DC 特定（`9≡0 mod 3`、`9≡1 mod 4` 的 CRT 巧合 ✗）|
| ③ `phase-proj (phase x) ≡ phase-proj (step g x)` | ✅ True | 需投影 ✗ |
| ④ `phase ≡ λ x → step g x` | ❌ **False** | 加法分量不同 ✗ |

**⇒ 采用候选 ①** ✓ —— `phase-g-comm : ∀ x → phase (step g x) ≡ step g (phase x)` ✓

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
**⇒ `add-proj` 不需要** ✓（原方案作废）

---

#### N8 原方案（已作废，保留供对照）

```agda
-- ❌ 纯函数等式（DC 上 False）
phase-eq-g : phase ≡ λ x → step g x                                -- ✗ 不成立
--   反例：phase (0,0) = (0,1)  vs  step g (0,0) = (1,1)（差在加法分量）

-- ✅ 需要加法分量投影（把「加法分量」显式化）
add-proj   : A → Trit
g-add      : add-proj g ≢ add-proj unit          -- g 的加法分量非平凡
g-phase    : ∀ x → phase x ≡ —— 由 step g 与 add-proj 复合 ——    -- 需设计
```

**⇒ G4 的本质**：`g` 的**加法分量**必须非平凡 ✗ —— 否则 `g` 只是相位生成元 ✗

#### N9：G5 归零机制（本体论级）

```agda
-- 归零不是「单位元」，是「周期闭合机制」
oblivion        : A → A → A                    -- 对消灭操作（如 ⊕ 的合成）
oblivion-cycle  : ∀ x → step x unit ≡ x         -- 单位元层（现有 zeroʳ）
-- 四层归零（04-zero-oblivion.md）
oblivion-add    : ∀ x → step (step x g) g ≡ ...  -- ⊕³ 层
oblivion-phase  : ∀ x → iterate phase 4 x ≡ x    -- α⁴ 层（= phase-cycle）
oblivion-joint  : ∀ x → iterate (λ y → step y g) clock x ≡ x  -- mixedOp¹² 层（= clock-cycle）
```

**⇒ G5 的根源**：`unit : A` 满足 `step unit x ≡ x` ✗，但**不表达**「虚实对消灭」✗
（`1² + i² = 0²` 的机制 ✗）—— 需要 `oblivion` 字段 ✓

---

**⇒ N5/N6 让 `G1` 从注释级变为类型级** ✓

---

## 五、DC 实例的逐条核对

| 要素 | DC 实例 | 加强版约束 | 数值验证 | 状态 |
|---|---|---|---|---|
| **① 载体** | `DuodecPoint = Trit × AlphaPower` | — | — | ✅ |
| **② 生成元** | `step = mixedOp`，`g = (T₁, a₁)` | `generated` | ✅ `g^0..g^11` 覆盖全部 12 个 | ✅ |
| **③ 关系** | `assoc` / `zeroˡ` / `zeroʳ` | — | — | ✅ |
| **④ 相位** | `phase = (t, a) ↦ (t, mulAlpha a1 a)`，阶 4 | `phase-nontrivial` | ✅ 9 case `refl` | ✅ |
| **⑤ 时钟** | `clock = 12`，`mixedOp¹² p ≡ p` | `clock-min`、`clock-phase` | ✅ 最小正周期 = **12**；`4 ∤ 12` 满足性 | ✅ |
| **⑥ 归零** | `ZeroOblivion.jointCycle` | （未纳入 record）| — | ⚠ **G5** |
| **⑦ 刚性** | `rigidity = mu = sigmaDC` | `rigidity-hom`、`rigidity-invol` | — | ⚠ 待形式化 |
| **⑧ 核对** | `mixedOp-identityʳ` | — | — | ✅ |

**⇒ 现状：6/8 已验证（② ⑤ 本轮数值确认），2/8 待形式化（⑥ G5、⑦ 自同构性质）** ✓

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
k = 4 不满足                   ⇒ phase-order = 4 不是联合周期 ✓
```

**`clock-phase` 验证**：`4 ∣ 12` ✓（若 `clock = phase-order = 4` 则丢加法分量 ✗
—— 正是 `RnPresentation` 踩的红线，见 [39](39-frobenius-vs-group-inversion.md)）

**G3/G4 候选约束的验证**（2026-10-21 审核后补）：

```
✅ phase (step x y) ≡ step (phase x) y        单边：True（全部 144 对）
❌ phase (step x y) ≡ step (phase x) (phase y) 双边：False
   反例 x = y = (0,0)：phase(step) = (0,1)  vs  step(phase,phase) = (0,2)
❌ phase ≡ λ x → step g x                       False
   反例 x = (0,0)：phase = (0,1)  vs  step g = (1,1)（差在加法分量）
⇒ G3 需**单边**形式；G4 需**分量投影**（纯函数等式不可表达）
```

**N3 的精确性验证**：

```
phase-order = 4, clock = 4  ⇒  4 ∣ 4 成立  ⇒  N3 **不能**排除 clock = phase-order ✗
clock-neq-phase : phase-order < clock  ⇒  4 < 12 成立  ✓ 可排除
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

**逐条对照（2026-10-21 审核后修正）**：

| 判据 | 现有 record | 加强版（N1–N9）|
|---|---|---|
| ① 三层齐备 | ✅ | ✅ |
| ② 每个要素约束**类型层可判** | ❌ | ⚠ **部分**：G1/G2/G3/G6 已可判；**G4/G5 仍不可判** ✗ |
| ③ 每个约束有反例说明 | ✅ | ✅ |
| ④ DC 实例逐条核对 | ✅ | ✅（6/8 数值验证，2/8 待形式化）|

**⇒ 加强版满足 ①③④，② **部分**满足** ✗

**⚠ 三个缺口**：

| 缺口 | 被 N1–N9 解决？ | 说明 |
|---|---|---|
| **G1** `rigidity` 无约束 | ✅ **部分**（N5/N6）| 「由 `galoisConjugate` 诱导」仍需更精确字段 |
| **G2** `clock` 无极小性 | ✅ N2 | `clock-min` |
| **G3** `phase` 与 `step` 无关系 | ⚠ **部分**（N7）| 单边 `phase-hom` ✓；**双边不成立** ✗（DC 反例）|
| **G4** `g` 与 `phase` 无关系 | ❌ **未解决** | 需 `add-proj` 投影，**纯函数等式不可表达** ✗ |
| **G5** `unit` ≠ 归零机制 | ❌ **未解决**（N9 仅草案）| `oblivion` 字段需设计 ✗ |
| **G6** 无「生成」约束 | ✅ N4 | `generated` |
| **G7** 无统一 record | ⚠ 部分 | 本文档是文档，不是 record 本身 |

**⇒ 「加强版满足全部四条」这个判断**需修正**：G3 部分、G4 与 G5 仍存在** ✗
**⇒ 其中 G5（归零公理被降格为 `unit`）是**本体论级**缺口** ✗

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

---

## 八、一句话

**依赖类型论展示群的完整定义 = 三层八要素 + 类型层可判的约束 + 反例说明 + 实例核对。**
现有 `Presentation` record 是**弱化版**（7 处约束不足，G1/G5/G6 为本体论级缺口）；
加强版新增 **9 项约束**（N1–N9），**但仍未解决 G4（`g`/`phase` 脱节）与 G5（归零机制）** ✗：

- **N3 不能排除 `clock = phase-order`** ✗（`4 ∣ 4` 成立）⇒ 需单独的 `clock-neq-phase : phase-order < clock` ✓
- **N7 只能单边**（`phase (step x y) ≡ step (phase x) y` ✓；**双边不成立** ✗，DC 反例 `x=y=(0,0)`）
- **N8 已简化**（2026-10-21 深度研究）：`phase-g-comm : phase (step g x) ≡ step g (phase x)` ✓ 纯函数等式（无需投影）；`g ≠ unit` 由 N1+N2+N3b 自动导出 ✓
- **N9（G5）仍为草案** ✗ —— `unit : A` 不表达「虚实对消灭」✗**定义的精确化不是学术洁癖，是透明性的提升** ——
在有限结构上，每个约束都可穷举验证；这正是特征 3 结构相对连续统的本体论优势。

---

## 九、相关文件

| 文件 | 关系 |
|---|---|
| [11-type-theory-presentation.md](11-type-theory-presentation.md) | 八要素的**描述性**定义 |
| [12-rigorous-type-theory.md](12-rigorous-type-theory.md) | 定义 2.1–2.7（分散的形式化）|
| [20-dc-type-theory-positioning.md](20-dc-type-theory-positioning.md) | 生成结构定位 |
| [30-terminology-ontology.md](30-terminology-ontology.md) | 本源/投影判断术语 |
| [39-frobenius-vs-group-inversion.md](39-frobenius-vs-group-inversion.md) | 刚性 = `μ`（不是 `ρ`）|
| [40-transparency-vs-refutation.md](40-transparency-vs-refutation.md) | 刚性 = 自同构的透明性 |
| [41-strength-vs-transparency.md](41-strength-vs-transparency.md) | 判据指向结构，不指向学科 |
| `src/Sovereign/Algebra/UniversalAlgebra/Presentation.agda` | 现有 record（弱化版）|
| `src/Sovereign/Algebra/UniversalAlgebra/RnDCPresentation.agda` | 合法实例（`clock = 12`）|
| `src/Sovereign/Algebra/UniversalAlgebra/RnPresentation.agda` | ⚠ 已撤回（`clock = 4` 踩红线）|
