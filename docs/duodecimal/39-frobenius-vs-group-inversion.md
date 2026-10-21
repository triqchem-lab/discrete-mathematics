# 39 · 域刚性 vs 群反转：两个「共轭」必须分开

> **2026-10-21 理论精确化**（触发：`dc-presentation.rigidity = rho` 的审核发现）
> 本文档把「八要素 ⑦ 刚性」的定义精确到可判定的程度，并揭示一个**概念混淆**：
> 群论意义的「共轭」（反转 `g ↦ g⁻¹`）≠ 域论意义的「共轭」（Frobenius `x ↦ xᵖ`）。
>
> **▶ 第二层**：[40-transparency-vs-refutation.md](40-transparency-vs-refutation.md) 把判据再推进一层——
> 刚性不仅是「Frobenius **存在**」，更是「Frobenius **透明**」（可显式构造 + 可穷举验证）。

---

## 一、数学严格性维度

### 1.1 三个映射，都是合法自同构，但身份不同

`DC = DuodecPoint = Trit × AlphaPower = C₃ × C₄`（12 元阿贝尔群）。

| 映射 | 定义 | 数学身份 | 合法自同构 | Agda 实现 |
|---|---|---|---|---|
| **`μ`** | `(t, αᵏ) ↦ (t, α⁻ᵏ)` | **域自同构**（Frobenius 的运输） | ✅ | `mu` / `sigmaDC` |
| **`λ`** | `(t, αᵏ) ↦ (-t, αᵏ)` | **群自同构**（加法取反） | ✅ | `lambda` |
| **`ρ = λ ∘ μ`** | `(t, αᵏ) ↦ (-t, α⁻ᵏ)` | **群反转** `p ↦ p⁻¹` | ✅ | `rho` |

三者都是 `DC` 的合法自同构（阿贝尔群 ⇒ 反转也是自同构 ✓），
**但只有 `μ` 是「域自同构」**，`ρ` 是**复合**，不是「恰好等于 Frobenius 在 DC 上的诱导作用」。

### 1.2 ★ 严格的代数论证：`ρ` 不可能是 Frobenius

```
设 σ 是域 GF(9) 的 Frobenius 自同构（x ↦ x³）
  ① σ 是域同态 ⇒ σ(a + b) = σ(a) + σ(b)          （加法保持）
  ② σ(1) = 1³ = 1
  ③ ⇒ σ(n·1) = n·σ(1) = n·1  对 n = 0, 1, 2
     ⇒ σ 固定素域 GF(3) ⇒ 在加法分量上 σ = id      （★ 关键）
  ④ 而 ρ 把 t ↦ -t ✗ ⇒ 只有 t = 0 时才与 σ 一致
  ⇒ ρ 不可能是 Frobenius 的运输 ✗
```

**这是数学上的硬事实 —— `ρ` 不是 Frobenius，`μ` 才是。**
若 `rigidity` 的定义要求「由 `galoisConjugate` 诱导」，则 `rigidity = ρ` 在数学上就是错的。

### 1.3 ★ Agda 探针实证（2026-10-21）

```agda
-- ① ρ 就是群反转：mixedOp p (ρ p) ≡ e（12 个构造子全部 refl ✓）
rho-is-inverse : ∀ (p : DuodecPoint) → mixedOp p (rho p) ≡ duodec-e

-- ② ρ ≠ μ（ρ 动加法分量，μ 不动）
rho-is-not-mu : rho (T₁ , a1) ≢ mu (T₁ , a1)     -- ✓ (λ ())
mu-keeps-add  : mu  (T₁ , a1) ≡ (T₁ , a3)        -- ✓ refl
rho-flips-add : rho (T₁ , a1) ≡ (T₂ , a3)        -- ✓ refl
```

### 1.4 `DC` 的两个分量：Frobenius 的作用**不同**

| 分量 | 群 | Frobenius `σ(x) = x³` 的作用 | 理由 |
|---|---|---|---|
| **加法** `Trit` | `C₃` | **恒等** | σ 固定素域（`1³ = 1`，GF(3)-线性） |
| **相位** `⟨α⟩` | `C₄` | **取逆** | `α³ = α⁻¹`（`3 ≡ -1 mod 4`） |

**`μ` 是唯一同时满足两个分量的映射** —— 加法恒等、相位取逆。
`ρ` 在加法分量上取反，**不符合 Frobenius 固定素域的性质**。

---

## 二、理论完备性维度

### 2.1 八要素 ⑦ 的定义要求（精确化）

**原文**（`11-type-theory-presentation.md:104`）：

> 通过 `galoisConjugate` 诱导到 DC 的相位反射 `μ`

**精确陈述**（`11:143`）：

> `σ(t, α^k) = (t, α^{-k})`

**「诱导」的精确含义是「恰好等于 `μ`」，不是「可以由 `μ` 加上其他对称性复合得到」。**

### 2.2 ★★ 本体论论证：刚性为什么能区分连续统

```
char 0（ℂ, ℝ, ℚ）**也有**群反转 x ↦ -x  ✓
⇒ 若刚性 = 群反转，则连续统也有刚性 ✗
⇒ 三重完备性的「原生共轭 = 0」判据失效 ✗
⇒ 刚性必须用**连续统没有**的东西
⇒ Frobenius（char p 独有）✓
```

**刚性之所以能区分连续统，唯一的原因是 Frobenius 在 char 0 不存在。**

如果刚性用群反转，那连续统也有刚性 —— 三重完备性的判据就失效了。

### 2.3 概念混淆的根源

| 语境 | 「共轭」的含义 | 例子 | char 0 有吗？ |
|---|---|---|---|
| **群论** | 反转 `g ↦ g⁻¹` | `ρ` | ✅ 有（`x ↦ -x`）✗ 不区分 char |
| **域论** | Frobenius `x ↦ xᵖ` | `μ` | ❌ 无 ✓ 区分 char |

**八要素要的「原生共轭」是域论意义的** —— 因为它判的是 `char p` 是否有 Frobenius。
把群论意义的共轭（`ρ`）当成域论意义的共轭（`μ`），是**概念混淆**。

---

## 三、建议（对代码与文档）

### 3.1 理论完备性：`rigidity` 必须是 `μ`

```agda
-- 修正
dc-presentation.rigidity = mu    -- 即 sigmaDC
```

**理由**：八要素 ⑦ 要求「由 `galoisConjugate` 诱导」，而 `μ` 是唯一同时满足
**加法恒等**和**相位取逆**的映射。`ρ` 在加法分量上取反，不符合 Frobenius 固定素域的性质。

### 3.2 数学严格性：`ρ` 保留，但作为独立概念

```agda
-- 保留 ρ 作为独立定义
rho : DuodecPoint → DuodecPoint
rho = λ ∘ μ

-- 它在台账中记为「群反转」，不是「刚性」
```

**理由**：`ρ` 本身是合法的 2 阶自同构（群反转），有独立地位（阿贝尔群的一般自同构）。
它不应被删除，但也不应作为 `rigidity`。

### 3.3 理论上区分两个概念

| 概念 | 定义 | 例子 | 判据 |
|---|---|---|---|
| **域刚性** | 由 Frobenius 诱导的域自同构 | `μ` | char p（p 为素域特征）|
| **群反转** | `p ↦ p⁻¹` | `ρ` | 任意阿贝尔群 |

**八要素 ⑦ 要的是域刚性，不是群反转。**

### 3.4 修正的影响范围（执行清单）

| 步 | 内容 |
|---|---|
| **1** | 检查 `dc-presentation.rigidity` 的消费者 —— 若只在 `dc-presentation` 中用，修正安全 |
| **2** | 若 `ρ` 在其他地方被使用，保留 `ρ` 作为独立定义，但重命名（如 `group-inversion`）|
| **3** | 台账记录：`dc-presentation.rigidity` 从 `ρ` 修正为 `μ`，原因是八要素 ⑦ 要求刚性由 `galoisConjugate` 诱导 |
| **4** | 文档明确「诱导」的精确含义 —— 是「恰好等于 `μ`」，不是「可以由 `μ` 加上其他对称性复合得到」|

---

## 四、更深层的理论建议

### 4.1 八要素 ⑦ 的陈述精确化

**原陈述**：

> 刚性必须由 GF9 的 `galoisConjugate` 诱导

**精确化陈述**：

```
⑦ 刚性：rigidity 必须**恰好等于** galoisConjugate 在 DC 上的诱导作用 μ，
        不能是 μ 与其他对称性的复合。
        理由：八要素 ⑦ 要求刚性反映 GF9 的 Frobenius 自同构，
        μ 是 Frobenius 在相位分量上的精确诱导，
        复合其他对称性会引入非 Frobenius 的分量。
```

### 4.2 三重完备性的判据精确化

`25-liouville-goldbach-vs-abc-barrier.md:84` 的「原生共轭」行应加注：

```
原生共轭：F_p 素域 Gal 平凡、char 0 无 Frobenius
         ⇒ 只有 char p 的 GF(p^k)（k ≥ 2）有非平凡 Frobenius
         ⇒ 刚性 = Frobenius 的存在性，**不是群反转**
```

**这个注记可以防止未来的混淆** —— 把「共轭」的域论意义和群论意义分开。

### 4.3 ★ `R_n = Functions((Z/3)^n, GF9)` 的正面含义

T4 的正确环是 `Functions((Z/3)^n, GF9)`，它：

- **特征 3** ✓（GF9 是 char 3 域）
- **Frobenius 存在** ✓（`σ(f)(x) = σ(f(x))`，逐点）
- **⇒ 代数刚性成立** ✓

**这正是相对连续统病态（char 0 无 Frobenius）的正面判据。**
T4 的正确环选择不仅使计算简化（对角算子、Hamming 计数），
而且**在理论上满足八要素的 ⑦** —— 这是环选择的理论依据，不只是计算便利。

---

## 五、一句话

**从理论完备性看，`rigidity` 必须是 `μ`** —— 八要素 ⑦ 要求「由 `galoisConjugate` 诱导」，
而 `μ` 是唯一同时满足加法恒等和相位取逆的映射；`ρ` 在加法分量上取反，不符合 Frobenius 固定素域的性质。

**从数学严格性看，`ρ` 是合法的群反转，但不是 Frobenius 的运输** ——
严格的代数论证（σ 固定素域 ⇒ 加法分量上 σ = id）证明 `ρ` 不可能是 Frobenius。

**本体论上，刚性之所以能区分连续统，唯一的原因是 Frobenius 在 char 0 不存在** ——
如果刚性用群反转，连续统也有刚性，三重完备性的判据就失效了。

**修正建议**：`rigidity = μ`，`ρ` 保留作为独立概念（群反转），
文档中明确「诱导」的精确含义（恰好等于 `μ`，不是复合），
三重完备性表加注「刚性 = Frobenius 的存在性，不是群反转」。

**T4 的正确环 `Functions((Z/3)^n, GF9)` 同时满足计算简化和理论刚性 —— 这是环选择的理论依据，不只是计算便利。**

---

## 六、相关文件

| 文件 | 关系 |
|---|---|
| `11-type-theory-presentation.md:95-104` | §2.4 Frobenius 刚性（本源定义）|
| `11-type-theory-presentation.md:143` | 八要素的 σ 精确陈述 |
| `12-rigorous-type-theory.md:104-130` | 定义 2.5（Frobenius 刚性的精确表述）|
| `25-liouville-goldbach-vs-abc-barrier.md:84` | 三重完备性的「原生共轭」行 |
| `src/Sovereign/Algebra/GroupTheory/DuodecClock.agda:683-700` | `lambda` / `mu` / `rho` 的定义 |
| `src/Sovereign/Algebra/GroupTheory/DCGroup.agda:100` | `sigmaDC`（= `mu`）|
| `src/Sovereign/Algebra/UniversalAlgebra/Presentation.agda:82` | 八要素 ⑦ 的约定 |
| `memory/research-2026-10-21-slice-decomposition.md` §50-§51 | 本轮查证与分析的完整记录 |
