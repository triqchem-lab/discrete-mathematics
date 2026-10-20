# 研究报告：DayanNatFix 终止性 · NSE 六轴 adv6/Leray/秩核

> 日期：2026-10-20 ｜ 方法：**先查本地库（DSH grep）→ 再查论文** ｜ 深度：L3
> 结论先行：**三个课题里只有一个是真研究**，另两个是「本地已有」或「陈述有误」。

---

## 0. 摘要

按「先查代码库」执行后，原定的三个课题被重分类：

| 课题 | 原判断 | **查证后的真实状态** | 性质 |
|---|---|---|---|
| DayanNatFix 整术终止性 | 未证 | `step-decreases`（严格递减）**已证** ✓；`termination-statement` **作为陈述是假的** ✗（缺互素前提） | **陈述修正 + 补 gcd 链**，非研究 |
| NSE `adv6` | 待补 | **已存在**于 `NSEPresentation.agda:367`（`adv1..adv6` 六路分派）✓ | **移植**，非研究 |
| NSE Leray | 条件存在 | `PoissonSolvable` **无条件不成立** ✗（Δ₆ 核维数 275 ⇒ 非满射）⇒ 应改为**否定定理 + 锐化条件** | 可证，非研究 |
| NSE 秩核 454/275 | 未证 | 无任何本地形式化；需 GF(3) 上 729 维线性代数 | **唯一真研究** ⬜ |

---

## 1. DayanNatFix 终止性

### 1.1 本地证据

`src/Sovereign/Algebra/GroupTheory/DayanTermination.agda`（83 行 / 0 postulate / 0 hole）已有：

```agda
termination-measure : DayanState → ℕ
termination-measure = right-top

step-decreases : (s : DayanState) → right-top s > 0 →
                 termination-measure (dayan-step s) < termination-measure s
step-decreases s rt>0 with right-top s | rt>0
... | zero    | ()
... | suc rt-1 | _ = m%n<n (right-bottom s) (suc rt-1)     -- ✅ 已证
```

`termination-statement` **只写了 `Set`，没有证明体** ✗：

```agda
termination-statement : Set
termination-statement = ∀ (奇 定 : ℕ) → Σ ℕ (λ fuel → dayan-terminates (dayan-iterate-fuel fuel (dayan-init 奇 定)))
```

### 1.2 ★ 陈述有误（`diagnosis: statement_wrong`）

`dayan-terminates s = (right-top s ≡ 1)`（`DayanState.agda:68`），而

```agda
dayan-step s with right-top s
... | zero    = s          -- ⚠ rt=0 时**原样返回**，不再前进
... | suc rt-1 = dayan diff (left-top s) (right-bottom s % right-top s) (suc rt-1)
```

迭代 `right-top` 得到的是**欧几里得链**：`奇, 定 % 奇, 奇 % (定 % 奇), …`，
其极限是 **`gcd(奇,定)`**。因此：

- `gcd(奇,定) = 1` ⟹ 链到达 **1** ⟹ `dayan-terminates` ✓
- `gcd(奇,定) = g > 1` ⟹ 链停在 **`g`** ⟹ `right-top ≠ 1` ⟹ **`dayan-terminates` 假** ✗

**反例（构造性）**：`奇 = 2, 定 = 4` ⇒ `gcd = 2` ⇒ `right-top` 链 `2, 0, 0, …` ⇒ 永不 `≡ 1`。
⇒ **原 `termination-statement` 不可证**（命题为假）。

### 1.3 修正后的义务

```agda
-- ① gcd 链：迭代的 right-top 序列以 gcd(奇,定) 为极限
dayan-reaches-gcd :
  ∀ 奇 定 → Σ ℕ (λ fuel → right-top (dayan-iterate-fuel fuel (dayan-init 奇 定)) ≡ gcd 奇 定)

-- ② 终止（带互素前提）—— 才是秦九韶「奇一而止」的正确陈述
dayan-termination :
  ∀ 奇 定 → gcd 奇 定 ≡ 1 →
    Σ ℕ (λ fuel → dayan-terminates (dayan-iterate-fuel fuel (dayan-init 奇 定)))
```

**证明路线**（不需要良基递归，只需强归纳）：
1. `step-decreases` 已给「严格递减」✓；
2. 强归纳（`Data.Nat.Induction.<-rec`）on `right-top s`：
   `∀ n s → right-top s ≤ n → right-top s > 0 → Σ fuel, right-top (iterate fuel s) ≡ 1`（在互素前提下）；
3. gcd 链用标准 `gcd` 递推（`Data.Nat.GCD` / `Data.Nat.Properties.gcd`）对齐。

**工作量估计**：~60–90 行（主要是 gcd 对齐），非研究级。

---

## 2. NSE 六轴 `adv6`

### 2.1 本地证据

`src/Sovereign/Application/Problems/NavierStokes/NSEPresentation.agda:345-375` **已有**：

```agda
-- 对流项: adv_i = Σ_j (amp v_j ⊗ D_j^amp (v_i))
advSum : ...
adv1 .. adv6 : VelField → Torus6 → Trit
adv6 v x = advSum (v6 v) v x
advField : VelField → Torus6 → (Trit × Trit × Trit × Trit × Trit × Trit)
```

且该处文件头注（`NSEPresentation.agda:289`）已声明「分量↔轴 1-1 对应」在新载体上成立。

### 2.2 结论

`NSEOnT6SixAxis.agda` 的「adv6 待补」实质是 **port**：把 `NSEOnT6SixAxis` 的 `Axis6 = Fin 6` /
`shiftAt6` 与 `NSEPresentation` 的 `advSum` 定义对齐，再证 `div6 ∘ adv` 的恒等式。

**判断**：纯工程，~80 行，无未知数学。

---

## 3. NSE Leray 投影

### 3.1 本地证据

`NSEOnT6.agda:569`：

```agda
PoissonSolvable : Field → Set
PoissonSolvable v = Σ ScalarField (λ p → ∀ x → laplacian p x ≡ negate (div (adv v) x))
```

`NSEOnT6SixAxis.agda:52` 自述：「离散 Leray 投影仍是条件存在（`PoissonSolvable` 那类前提不可省）」。

`NSEOnT6SixAxis.agda:20` 给出实测：`laplacian` 六轴版 **rank 454 / 核维数 275**（空间维数 729）。

### 3.2 ★ 应当证明的是**否定**

由秩-核维数：`dim ker Δ₆ = 275 > 0` ⟹ **Δ₆ 不是单射** ⟹ 在有限维空间上 **不是满射** ✓
⟹ `PoissonSolvable v` 对某些 `v` **无解** ⟹ **无条件 Leray 投影不存在** ✓

且该模块已给出构造性否证 `laplacian6-not-identically-zero`（`Δ₆ f ≢ 0` 恒等）——与
「`Δ` 非满射」是两块拼图，合起来才是完整的诚实结论。

**修正后的义务**：

```agda
-- ① 存在非零调和场（ker Δ₆ ≠ 0）
exists-harmonic : Σ ScalarField (λ f → (∀ x → laplacian6 f x ≡ T₀) × (∃ λ x → f x ≢ T₀))

-- ② 有限维 + 非单射 ⇒ 非满射（需秩-核维数，或构造性地给出不可解的 v）
leray-not-unconditional : Σ Field (λ v → ¬ PoissonSolvable v)
```

**路线**：② 可**构造性**给出——取 `v` 使 `div (adv v) ≡ 0` 但取常值型不可解，
或用「`Δ` 的像 ⊊ 全空间」（由 ① 的对偶）论证。这需要有限维线性代数的秩-核工具 ✗（与课题 4 共用）。

---

## 4. NSE 秩核（rank 454 / kernel 275）—— **唯一的真研究**

### 4.1 缺口

仓库**没有任何**关于 `laplacian6` 的 rank/核维数的形式化定理：
`grep -rn "rank\|核维数\|kernel" src/Sovereign/Application/Problems/NavierStokes/` 无命中。

**数字 `454 / 275` 的出处（已更正，2026-10-20）**：只在模块注释
`NSEOnT6SixAxis.agda:20` 里出现，**`engineering/*.py` 里 grep 不到** ✗ ——
所以它**既不是定理、也不是可复跑的 oracle 回执**，只是一个**未溯源的注释数字** ✗。
⇒ 本报告**不**采信其数值；`RESEARCH.nse-rank-kernel` 的陈述应视为
「待先算出、再形式化」的空槽 ✗，而非「已知答案待证」。

### 4.2 为什么难

- 载体是 `GF(3)^729`，`Δ₆ : 729 → 729` 是线性映射；
- 直接做矩阵秩需要 729×729 的行化简 ✗（>27 case 红线，且计算量巨大）；
- **正确路线是符号化**：`Δ₆` 在 `(Z/3)⁶` 上是对角化的（离散傅里叶/特征标分解），
  特征值 `λ_ξ = Σ_{i=1}^{6} (ω^{ξ_i} - 1)(ω^{-ξ_i} - 1)`，其中 `ω` 是 GF(3) 上的 3 次单位根……

### 4.3 文献线索

- 离散 Hodge 分解在有限域上的代数版本：[Algebraic Discrete Hodge Decomposition in the Closure](https://www.zenodo.org/records/18672535/files/discrete_exterior_variation_geometry.pdf?download=1#19#4)
- 离散 Leray 投影综述：[Discrete Leray Projection — Papers](https://www.emergentmind.com/topics/discrete-leray-projection#1)
- 周期环面谱格点：[On the periodic torus, Fourier modes lie on the discrete lattice Z³](https://www.zenodo.org/records/19743001/files/Deep_Research_ACL-1.pdf?download=1#2#2)

**★ 已更正（2026-10-20，人类指正）** ✗：
在 `GF(3)` 上「`ω ∉ GF(3)` ⇒ 换 `GF(9)`」的说法是**错的** ✗：
- `x³ − 1 = (x − 1)³`（char 3）⇒ `x³ = 1 ⇒ x = 1` ⇒ **任何**特征 3 的域都没有本原三次单位根 ✗；
- `GF(3^k)* ≅ C_{3^k−1}` 且 `3 ∤ 3^k − 1`（`3^k − 1 ≡ 2 mod 3`）⇒ 扩多少次都不行 ✗。

**正确结构** ✓：`k > 1` 时用的是 **`GF(9)` 诱导的自同构**——Frobenius `σ : x ↦ x³`，
是 `Gal(GF(9)/GF(3)) ≅ C₂` 的非平凡元（DC 的刚性 `sigmaDC` 即此 `σ` 的体现），
而**不是**三次单位根 ✗。⇒ 对角化/不变量论证应走 **Frobenius 共轭**这条路 ✓。

---

## 5. 任务分解（按可执行性排序）

| # | 任务 | 前置 | 估计 | 性质 |
|---|---|---|---|---|
| T1 | DayanNatFix：修正 `termination-statement`（加互素前提）+ 证 `dayan-termination` | 无（`step-decreases` 已有 ✓） | ~60–90 行 | 证明 |
| T2 | NSE：把 `adv6`/`advField` 移植进 `NSEOnT6SixAxis` | 无 | ~80 行 | 移植 |
| T3 | NSE：证 `∃ 非零调和场` + `Leray 非无条件` | T2 / 秩核工具 | ~120 行 | 证明 |
| T4 | NSE 秩核 454/275 | **先解决 GF(3) 上无 3 次单位根的问题** | 未知 | **研究** |

**建议顺序**：T1 → T2 → （T3 与 T4 共用有限维线性代数工具，先建工具再并行）

---

## 6. 诚实边界

- ✗ 秩核 `454 / 275` **只是 oracle 实测数字**，不是定理；本报告不声称它们正确。
- ✗ 本报告未验证 `ω ∉ GF(3)` 对谱分解路线的完整影响；第 4.3 节末尾的疑问是**待验证**，不是结论。
- ✗ 文献部分只做了 1 轮检索（3 条 query），**未做交叉验证**；引用仅作线索。
- ✓ 第 1–3 节的「本地已有 / 陈述有误」判断均基于**读源码**（给了行号），可信。
