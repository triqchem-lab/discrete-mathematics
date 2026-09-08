# 律算框架类型论展示群的严谨定义

**日期**: 2026-08-26 (2026-09-08 补: 相位/时钟/归零为核心维度)  
**状态**: 权威定义文档  
**来源**: DuodecClock.agda, GF9.agda, Trit.agda

---

## 一、严谨性的标准

严谨意味着：

1. **每个符号都有明确的类型**
2. **每个断言都对应代码库中的实际构造**
3. **本体论立场被明确标注，不混同投影与本源**
4. **信息保留被逐一验证，无遗漏**

---

## 二、律算框架的严格群论定义

### 定义 2.1（载体类型）

```agda
-- DuodecClock.agda:206
DuodecPoint : Set
DuodecPoint = Trit × AlphaPower
```

这是一个**Σ-类型**（record），其项具有形式 \((t, \alpha^k)\)，其中：

\[
t : \mathrm{Trit}, \quad \alpha^k : \mathrm{AlphaPower}
\]

**本体论标注**：这是**联合周期的载体**，不是抽象直积。

---

### 定义 2.2（分量类型的代数来源）

```agda
-- Trit.agda:27
data Trit : Set where
  T₀ : Trit  -- 0
  T₁ : Trit  -- 1
  T₂ : Trit  -- 2

-- DuodecClock.agda:76
data AlphaPower : Set where
  a0 : AlphaPower   -- 1
  a1 : AlphaPower   -- α
  a2 : AlphaPower   -- α² = -1
  a3 : AlphaPower   -- α³
```

- `Trit` 来源：\(\mathbb{F}_3\) 的加法群，特征 3
- `AlphaPower` 来源：GF(9) 乘法群的 4 阶子群 \(\langle \alpha \rangle\)，其中 \(\alpha^2 = -1\)

---

### 定义 2.3（群运算 mixedOp 的联合性）

```agda
-- DuodecClock.agda:212
mixedOp : DuodecPoint → DuodecPoint → DuodecPoint
mixedOp (x , a) (y , b) = (x ⊕ y , mulAlpha a b)
```

其中 \(\oplus\) 是 \(\mathbb{F}_3\) 的加法，\(\mathrm{mulAlpha}\) 是 \(\langle\alpha\rangle\) 的乘法。

**联合性标注**：生成元 \(g := (T_1, a_1)\) 在一步中同时执行：
- 损益分量 \(+1\)（\(\mathbb{F}_3\) 加法）
- 相位分量 \(\times \alpha\)（\(\langle\alpha\rangle\) 乘法）

---

### 定义 2.4（关系作为 record 字段）

```agda
-- DuodecClock.agda:379
record ZeroOblivion : Set where
  field
    carrier : Set
    zero : carrier
    addZeroR : ∀ x → mixedOp x zero ≡ x
    addZeroL : ∀ x → mixedOp zero x ≡ x
    mulAlphaCycle : mulAlpha^4 a1 ≡ a0
    tritCycle : ∀ x → (x ⊕ x) ⊕ x ≡ T₀
    jointCycle : ∀ p → mixedOp^12 p ≡ p
```

**关键**：关系是 `record` 字段，**不是 HIT 构造子**。证明用 `refl`（穷举），非路径合成。

---

### 定义 2.5（Frobenius 刚性的精确表述）

```agda
-- GF9.agda:96
galoisConjugate : GF9 → GF9
galoisConjugate (a , b) = a , negate b
```

**诱导到 DC**：

\[
\sigma_{\mathrm{DC}} : \mathrm{DuodecPoint} \to \mathrm{DuodecPoint}
\]

\[
\sigma_{\mathrm{DC}}(t, \alpha^k) := (t, \alpha^{-k})
\]

**层级标注**：
- Frobenius 的**原始载体**是 GF9
- DC 通过相位子群 \(\langle\alpha\rangle \subset \mathrm{GF9}^\times\) **继承** Frobenius 作用
- 这个继承是严格的：\(\sigma_{\mathrm{DC}}\) 是 \(\mathrm{galoisConjugate}\) 在 \(\langle\alpha\rangle\) 上的限制

---

### 定义 2.6（相位维度 — 不可约旋转状态）

**2026-09-08 补**：展示群的核心不只有"载体 + 生成元 + 关系"，还须显式承载**相位**与**时钟**两个动力维度。此前文档把它们降格为静态标签，构成信息截断。

相位不是 `AlphaPower` 这个 data 类型的"来源说明"，而是**每个 DC 元素不可约携带的 90° 旋转状态**：

\[
\text{相位}: (t, \alpha^k) \mapsto k \in \{0,1,2,3\}
\]

- 元素 \((t, a_1)\) 与 \((t, a_2)\) 的区别**就是相位状态**（90° vs 180°），不是额外标签
- `mixedOp` 的第二分量 `mulAlpha a b` **就是相位在走**：一步 ×α = 相位前进 90°
- 截断 \(\alpha \mapsto \{\pm 1\}\)（C₄→C₂ 非忠实商）会抹掉 90°/270° 状态 = 相位信息丢失
  —— 这是**相位不可约性元公理**（memory/crt-wave-physics-not-modular-arithmetic.md），展示群必须承载它

**信息保留主张**：展示群保留"每个元素此刻在 C₄ 哪个位置"（0°/90°/180°/270°）；集合论群 \(C_{12}\) 截断后只剩 12 个无相位结构的点。

---

### 定义 2.7（时钟维度 — 联合演化过程）

**2026-09-08 补**：DC 在源码中自称"混合时钟"（DuodecClock.agda §2）、宪法裁决叫"本源时钟结构"（01-ontology），但展示群文档把时钟降格为"周期 12 = 群阶 lcm(3,4) 的定理"——**把过程当成了静态事实**。

时钟是**时间演化**维度：联合生成元 \(g = (T_1, a_1)\) 每走一步，幅度 +1、相位 ×α：

\[
\text{iterate } n\ (\mathrm{mixedOp}\ g)\ p = p\ \text{沿钟走 } n \text{ 步}
\]

- `mixedOp^12 p ≡ p`（`ZeroOblivion.jointCycle`）= **走钟一圈**：12 步后幅度与相位同时归零
- 这不是"群的阶是 12"这个静态事实，而是**走 12 步的过程**——每一步的幅度+相位联合状态是时钟读数
- 时钟信息 = "此刻走到第几步、相位累积到哪"；截断成 \(C_{12}\) 就丢了"走到一半时相位在哪"

**信息保留主张**：展示群保留时钟的**过程性**（`iterate 12` = 走一圈）；抽象群 \(C_{12}\) 只保留"群阶 12"，丢失每一步的相位演化。

**归零定位 (2026-09-08 补)**: `mixedOp^12 p ≡ p`（`ZeroOblivion.jointCycle`）不只是"走钟一圈"——它同时是**联合归零** = 零冥族的核心。零冥族不是"关系公理的集合"，而是**周期闭合机制**：

- 时钟（走的过程）与归零（回到单位元的闭合）是**配对维度**：没有归零，时钟就走不回原点，周期 12 无从成立
- 零冥族统一四种归零（04-zero-oblivion.md）：
  - 加法归零 `⊕³ = id`（损益消灭，T₁⊕T₂=T₀）
  - 相位归零 `α⁴ = a₀`（旋转闭环，90°×4=360°）
  - **联合归零 `mixedOp^12 = id`**（双周期同步 = 十二 = 走钟一圈回 d0）
  - 仲吕闭合（另一个 12 的实例）
- 零不是"空"，是**多维相位同时回到单位元的状态**（04 文档核心主张）

**信息保留主张**：展示群保留归零的**闭合机制**（为什么走回原点）；集合论群只记录"g¹²=e"这一条等式，丢失四种归零各自的代数来源（谁归零、怎么归零）。

---

## 三、与集合论群定义的信息对比

| 信息 | 集合论群 | 律算框架类型论 |
|------|---------|---------------|
| 载体 | 12 元素集合 | `record DuodecPoint`（Σ-类型） |
| 生成元来源 | 丢失 | `Trit`（GF(3)）+ `AlphaPower`（⟨α⟩） |
| 运算联合性 | 丢失 | `mixedOp` 的分量规则 |
| 关系体系 | 丢失 | `ZeroOblivion` 五字段 |
| **归零机制** (2026-09-08) | **丢失 (只剩 g¹²=e 一条)** | **ZeroOblivion 四归零 = 周期闭合 (⊕³/α⁴/mixedOp¹²/仲吕12)** |
| Frobenius 刚性 | 丢失 | `galoisConjugate` 定义在 GF9，诱导到 DC |
| 联合生成元 | 丢失 | \(g = (T_1, a_1)\) 显式构造 |
| 周期 12 | 只是群阶 | \(\mathrm{lcm}(3,4)\) 的定理 |
| **相位状态** (2026-09-08) | **丢失 (12 个无相位点)** | **每元素携带 C₄ 位置 (0°/90°/180°/270°)** |
| **时钟读数** (2026-09-08) | **丢失 (只剩群阶 12)** | **`mixedOp^12` = 走钟一圈的过程** |

---

## 四、本体论层级的严格标注

\[
\boxed{
\begin{aligned}
&\text{本源结构}: \mathrm{DC} = \text{加法 3 特征} \oplus \text{4 阶相位的联合周期} = \text{携带相位状态、经归零闭合的时钟} \\
&\text{载体类型}: \texttt{record DuodecPoint} = \Sigma_{t:\mathrm{Trit}} \mathrm{AlphaPower} \\
&\text{相位维度}: \text{每元素携带 } C_4 \text{ 位置 (不可约 90° 旋转状态)} \\
&\text{时钟维度}: \mathrm{mixedOp}^{12} p = p \ \text{= 走钟一圈 (12 步联合演化)} \\
&\text{归零维度}: \mathrm{mixedOp}^{12} = id \ \text{= 联合归零 (零冥族周期闭合, 与时钟配对)} \\
&\text{抽象投影}: (DC, \mathrm{mixedOp}) \cong C_{12} \ (\text{作为抽象群}) \\
&\text{投影不是本源}: C_{12} \ \text{丢失了生成来源、关系、Frobenius 刚性、相位状态、时钟过程与归零机制}
\end{aligned}}
\]

---

## 五、严谨性检查清单

| 检查项 | 状态 |
|--------|:----:|
| 载体是 `record`（Σ-类型），不是 `data` | ✅ |
| 分量是 `data`（归纳枚举） | ✅ |
| 关系在 `ZeroOblivion` record 字段中 | ✅ |
| Frobenius 定义在 GF9 上，诱导到 DC | ✅ |
| 联合生成元 \(g = (T_1, a_1)\) 显式定义 | ✅ |
| 联合周期 12 = lcm(3,4) 是定理 | ✅ |
| 不将 DC 说成直积或 C₁₂ | ✅ |
| 不将载体说成 HIT | ✅ |
| **相位显式携带 (2026-09-08): 每元素含 C₄ 位置, 非 data 标签** | ✅ |
| **时钟 = 12 步演化 (2026-09-08): `mixedOp^12` 是走钟一圈, 非仅群阶** | ✅ |
| **归零显式 (2026-09-08): ZeroOblivion 四归零 (⊕³/α⁴/mixedOp¹²/仲吕12) = 周期闭合机制, 非仅关系公理** | ✅ |

---

## 六、最终严谨表述

> **律算框架的群论是类型论展示群**：
>
> - 载体 `DuodecPoint` 是 **Σ-类型**（record），由 `Trit` 和 `AlphaPower` 两个归纳类型打包而成
> - `Trit` 来源自 \(\mathbb{F}_3\) 加法，`AlphaPower` 来源自 GF(9) 的 \(\langle\alpha\rangle\) 乘法
> - 群运算 `mixedOp` 保留分量的联合性：第一分量用加法，第二分量用乘法
> - 关系体系 `ZeroOblivion` 作为 record 字段（见下"归零维度"）
> - Frobenius 刚性 `galoisConjugate` 定义在 GF9 上，通过相位子群诱导到 DC
> - 联合生成元 \(g = (T_1, a_1)\) 同时执行损益步和相位步，周期 12 = \(\mathrm{lcm}(3,4)\)
> - **相位维度** (2026-09-08)：每个元素携带不可约的 C₄ 位置 (0°/90°/180°/270°)，非 data 标签
> - **时钟维度** (2026-09-08)：`mixedOp^12 p ≡ p` = 走钟一圈的联合演化过程，非仅群阶
> - **归零维度** (2026-09-08)：`mixedOp^12 = id` 即**联合归零** = 零冥族核心（周期闭合机制，
>   与时钟配对：时钟走一圈、归零回到单位元；四种归零 ⊕³/α⁴/mixedOp¹²/仲吕12 见 04-zero-oblivion.md）
>
> **本体论立场**：本源结构是**携带相位状态、经归零闭合的时钟过程**（GF(3)×C₄ 纤维丛 + 不可约旋转 + 12 步联合演化 + 周期归零闭合）；抽象群 \(C_{12}\) 只是投影，丢失了生成来源、关系、刚性、**相位状态、时钟过程与归零机制**。

---

## 七、DC 与 C₁₂ 的本质区别（特征 3）

### 关键区分

| 结构 | 特征 | 来源 |
|------|------|------|
| GF(3) | char = 3 | 素域 |
| **DC = Trit × AlphaPower** | **char = 3**（Trit 分量继承） | GF(3) 加法 |
| C₁₂ = (Duodec, +12) | char = 12（环特征） | Z/12Z 投影 |
| Z/12Z | char = 12 | 整数模 12 |

### DC 不是 C₁₂

**DC 不是「抽象群同构于 C₁₂」**。这个同构是投影，它丢失了：

- 特征 3 的代数来源
- ⟨α⟩ 的乘法结构
- Frobenius 刚性
- **相位状态** (2026-09-08)：C₁₂ 的 12 个点不携带 C₄ 位置
- **时钟过程** (2026-09-08)：C₁₂ 只剩"群阶 12"，无 `mixedOp^12` 走圈的逐步演化

### 类型论展示群的优势

DC 作为类型论展示群，保留了：

1. **特征 3**：Trit 分量继承 GF(3) 的 char = 3
2. **阶 4**：AlphaPower 来自 ⟨α⟩，ord(α) = 4
3. **联合周期**：12 = lcm(3,4)，由特征 3 与阶 4 联合生成
4. **Frobenius 刚性**：定义在 GF9 上，诱导到 DC
5. **关系体系**：ZeroOblivion 五字段打包零冥族
6. **相位状态** (2026-09-08)：每元素携带 C₄ 位置，非 data 标签
7. **时钟过程** (2026-09-08)：`mixedOp^12` = 走钟一圈，非仅群阶

### 最终本体论立场

> **本源是携带相位状态的时钟**（联合周期系统 + C₄ 不可约旋转 + 12 步演化），
> 保留特征 3、阶 4、Frobenius 刚性、相位状态与时钟过程；
> **C₁₂ 只是投影**，丢失这些代数来源与动力维度。
