# 类型论展示群：律算框架的群论基础

**日期**: 2026-08-26 (2026-09-08 补: 相位与时钟为核心维度)  
**状态**: 审核结论  
**来源**: DuodecClock.agda, GF9.agda, CRT.agda

---

## 核心结论

> **律算框架的群论是类型论展示群，不是集合论群。**
> 
> 载体用 `record`（Σ-类型），生成元用 `data`（归纳类型），关系用 `record` 字段，刚性从 GF9 诱导。
> 
> **核心 = 载体 + 相位 + 时钟**：展示群不只保留代数结构，还须承载每元素的 C₄ 相位状态
> 与 `mixedOp^12` 走钟一圈的时钟过程（2026-09-08 补，详见 12-rigorous-type-theory.md 定义 2.6/2.7）。
> 
> 类型论基础 = Cubical Agda（代码库已用 `--cubical`）。

---

## 一、集合论群的病根

传统群论定义：

> 群是集合 G 配二元运算，满足结合律、单位元、逆元。

这个定义把群截断为：

\[
G = \{e, g_1, g_2, \ldots, g_{11}\}
\]

丢失的信息：

| 丢失的信息 | 具体内容 |
|-----------|---------|
| 生成元来源 | 损益循环来自 F₃ 加法，相位循环来自 GF(9) 乘法 |
| 关系体系 | ⊕³ = T₀，α⁴ = a₀，α² = -1 |
| Frobenius 刚性 | σ: x ↦ x³ 的 Galois 来源 |
| 联合周期 | g = (1,α) 同时走两步的联合生成 |
| 零冥族 | 五层零结构的嵌套关系 |
| **相位状态** (2026-09-08) | 每元素在 C₄ 哪个位置 (0°/90°/180°/270°)，非 data 标签 |
| **时钟读数** (2026-09-08) | `mixedOp^12` 走钟一圈的逐步演化，非仅"群阶 12" |

---

## 二、代码库中的实际类型定义

### 2.1 生成元类型（data）

```agda
-- Sovereign.Base.Trit
data Trit : Set where
  T₀ T₁ T₂ : Trit

-- Sovereign.Algebra.GroupTheory.DuodecClock
data AlphaPower : Set where
  a0 a1 a2 a3 : AlphaPower
```

- `Trit` 来自 GF(3)（特征 3 加法）
- `AlphaPower` 来自 ⟨α⟩（α 乘法相位）

### 2.2 载体类型（类型别名 = 乘积类型）

```agda
-- Sovereign.Algebra.GroupTheory.DuodecClock
DuodecPoint : Set
DuodecPoint = Trit × AlphaPower
```

- **不是**归纳类型（data），是**类型别名**（乘积类型）
- 每个项是 `(t, a)` 对，由两个分量构造
- 与 `record` 的区别：类型别名是直接的乘积，record 可以有额外结构

### 2.3 关系类型（record 字段）

```agda
-- Sovereign.Algebra.GroupTheory.DuodecClock
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

- 关系在 **record** 中，不是 HIT 构造子
- 证明是 **refl**（穷举），不是路径合成

### 2.4 Frobenius 刚性（从 GF9 诱导）

```agda
-- Sovereign.Algebra.GF9
galoisConjugate : GF9 → GF9
galoisConjugate (a , b) = (a , negate b)
```

- Frobenius 定义在 **GF9** 上，不是 DC 的生成元
- 通过 `galoisConjugate` 诱导到 DC 的相位反射 μ

---

## 三、与传统群论的对照

| 传统群论 | 类型论展示群 |
|---------|-------------|
| 集合 G 加上二元运算 | 载体类型由生成元构造 |
| 元素是集合成员 x ∈ G | 项由构造子 `Trit`, `AlphaPower`, `_,_` 生成 |
| 关系是逻辑公理 | 关系是 record 字段，证明是 refl |
| 自同构是任意双射 | 自同构由生成元上的作用递归定义 |
| 同构抹杀结构 | 生成元和关系是结构的一部分 |
| 信息截断（12 点 + 运算表） | 信息保留（生成来源、关系、Frobenius 刚性） |

---

## 四、律算框架的群论公理

\[
\boxed{
\begin{aligned}
\text{Group} := &\ \text{载体类型 (record)} \\
&\ + \text{生成元族 (data, 带代数来源标记)} \\
&\ + \text{关系族 (record 字段)} \\
&\ + \text{刚性作用 (Frobenius 从 GF9 诱导)} \\
&\ + \text{结构证明 (refl, 0 postulate)}
\end{aligned}}
\]

DC 不再是 C₁₂ 的抽象，而是：

\[
\mathrm{DC} = \left(
\begin{array}{l}
\text{载体: DuodecPoint = Trit × AlphaPower (类型别名)} \\
\text{生成元: } g_3 = (T_1, a_0)_{\mathbb{F}_3\text{-加法}},\ g_4 = (T_0, a_1)_{\alpha\text{-相位}} \\
\text{关系: } \oplus^3 = T_0,\ \alpha^4 = a_0,\ g^{12} = e \\
\text{刚性: } \sigma(t, \alpha^k) = (t, \alpha^{-k})_{\text{Frobenius}} \\
\text{相位: } \text{每元素携带 } C_4 \text{ 位置 (0°/90°/180°/270°, 不可约) (2026-09-08)} \\
\text{时钟: } \mathrm{mixedOp}^{12} p = p = \text{走钟一圈 (12 步联合演化) (2026-09-08)} \\
\text{证明: 全部为 refl (穷举)}
\end{array}
\right)
\]

---

## 五、信息保留的证明

在类型论展示群中，以下信息**全部保留**：

1. **生成元来源**：`Trit` 标记为 GF(3) 加法，`AlphaPower` 标记为 α 相位乘法
2. **关系体系**：`ZeroOblivion` record 的 5 层零冥关系
3. **联合周期**：由 `tritCycle` 和 `mulAlphaCycle` 推导的 `jointCycle`
4. **Frobenius 刚性**：`galoisConjugate` 定义在 GF9 上，诱导到 DC
5. **零冥族**：`zero` 的五层零结构作为 record 字段

这些在集合论群定义中**全部被截断**。

---

## 六、类型论基础：Cubical Agda

代码库**已经在使用 Cubical Agda**：

```agda
-- CRT.agda
{-# OPTIONS --rewriting --cubical --guardedness #-}
open import Cubical.Foundations.Prelude using () renaming (_≡_ to _≡ᶜ_)
open import Cubical.Foundations.Isomorphism using (Iso; iso)

-- SpinTwistor.agda
{-# OPTIONS --cubical --guardedness --rewriting #-}
```

Cubical Agda 提供：
- 路径类型（离散拓扑的基础）
- 高阶归纳类型（GF(9) 商结构）
- 计算规则（证明可执行）

---

## 七、修正后的表述

| 文章说的 | 代码库实际 | 修正 |
|---------|-----------|------|
| 「载体由 HIT 构造」 | 代码用 `record` + `data` | 应说「可用 HIT 但当前未用」 |
| 「DC 用归纳类型定义」 | DC 用 `DuodecPoint = Trit × AlphaPower` | 应说「DC 用 record（Σ-类型）」 |
| 「关系构造子 rel₃, rel₄」 | 代码用 `ZeroOblivion` record 字段 | 应说「关系在 record 中」 |
| 「Frobenius 在生成元层面定义」 | Frobenius 定义在 GF9 上 | 应说「Frobenius 从 GF9 诱导到 DC」 |

---

## 八、总结

> **律算框架的群论是类型论展示群**：
> - 载体 = `DuodecPoint = Trit × AlphaPower`（类型别名，乘积类型）
> - 生成元 = `Trit`（GF(3)）+ `AlphaPower`（⟨α⟩）
> - 关系 = `ZeroOblivion` record 的字段（5 层零冥）
> - 刚性 = `galoisConjugate`（Frobenius，从 GF9 诱导）
> - **相位** (2026-09-08) = 每元素携带 C₄ 位置 (0°/90°/180°/270°)
> - **时钟** (2026-09-08) = `mixedOp^12` 走钟一圈的联合演化
> - 证明 = `refl`（穷举，非 HIT）
> 
> **类型论基础 = Cubical Agda**（代码库已用 `--cubical`）
