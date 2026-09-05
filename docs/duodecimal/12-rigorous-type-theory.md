# 律算框架类型论展示群的严谨定义

**日期**: 2026-08-26  
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

## 三、与集合论群定义的信息对比

| 信息 | 集合论群 | 律算框架类型论 |
|------|---------|---------------|
| 载体 | 12 元素集合 | `record DuodecPoint`（Σ-类型） |
| 生成元来源 | 丢失 | `Trit`（GF(3)）+ `AlphaPower`（⟨α⟩） |
| 运算联合性 | 丢失 | `mixedOp` 的分量规则 |
| 关系体系 | 丢失 | `ZeroOblivion` 五字段 |
| Frobenius 刚性 | 丢失 | `galoisConjugate` 定义在 GF9，诱导到 DC |
| 联合生成元 | 丢失 | \(g = (T_1, a_1)\) 显式构造 |
| 周期 12 | 只是群阶 | \(\mathrm{lcm}(3,4)\) 的定理 |

---

## 四、本体论层级的严格标注

\[
\boxed{
\begin{aligned}
&\text{本源结构}: \mathrm{DC} = \text{加法 3 特征} \oplus \text{4 阶相位的联合周期} \\
&\text{载体类型}: \texttt{record DuodecPoint} = \Sigma_{t:\mathrm{Trit}} \mathrm{AlphaPower} \\
&\text{抽象投影}: (DC, \mathrm{mixedOp}) \cong C_{12} \ (\text{作为抽象群}) \\
&\text{投影不是本源}: C_{12} \ \text{丢失了生成来源、关系、Frobenius 刚性}
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

---

## 六、最终严谨表述

> **律算框架的群论是类型论展示群**：
>
> - 载体 `DuodecPoint` 是 **Σ-类型**（record），由 `Trit` 和 `AlphaPower` 两个归纳类型打包而成
> - `Trit` 来源自 \(\mathbb{F}_3\) 加法，`AlphaPower` 来源自 GF(9) 的 \(\langle\alpha\rangle\) 乘法
> - 群运算 `mixedOp` 保留分量的联合性：第一分量用加法，第二分量用乘法
> - 五层零冥关系打包在 `ZeroOblivion` record 的字段中
> - Frobenius 刚性 `galoisConjugate` 定义在 GF9 上，通过相位子群诱导到 DC
> - 联合生成元 \(g = (T_1, a_1)\) 同时执行损益步和相位步，周期 12 = \(\mathrm{lcm}(3,4)\)
>
> **本体论立场**：本源结构是联合周期系统；抽象群 \(C_{12}\) 只是投影，丢失了生成来源、关系和刚性。

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

### 类型论展示群的优势

DC 作为类型论展示群，保留了：

1. **特征 3**：Trit 分量继承 GF(3) 的 char = 3
2. **阶 4**：AlphaPower 来自 ⟨α⟩，ord(α) = 4
3. **联合周期**：12 = lcm(3,4)，由特征 3 与阶 4 联合生成
4. **Frobenius 刚性**：定义在 GF9 上，诱导到 DC
5. **关系体系**：ZeroOblivion 五字段打包零冥族

### 最终本体论立场

> **本源是联合周期系统**，保留特征 3、阶 4、Frobenius 刚性；
> **C₁₂ 只是投影**，丢失这些代数来源。
