# Agda `with` 纪律（2026-10-20 人类工程建议入册）

> **核心判据**：`with` 的危险不在于它是 `with`，而在于它的 **scrutinee 是否与
> goal / 索引 / 参数类型耦合**。

## 1. 决策表

| 场景 | 用 `with`？ | 替代 |
|---|---|---|
| 简单分支（scrutinee 不出现在 goal 或参数类型中）| ✅ 可以用 | — |
| scrutinee 出现在 goal 类型中 | ❌ 避免 | 顶层辅助函数（显式签名）|
| 多层嵌套 `with`（≥3 层）| ❌ 避免 | 拆成「每层一个函数」|
| scrutinee 是索引类型（`Fin n`、`Walk G a a`）| ❌ 避免 | 泛端点 + 显式等式 |
| 需要在后续 goal 引用原表达式 | ⚠️ `inspect` | `eq : f x ≡ result` ⇒ `rewrite` |
| 递归结构递减依赖 with 抽象 | ❌ 避免 | 提取辅助函数 + 显式递减 |
| `Dec` 判定分支（`with x ≟ y`）| ⚠️ | `case_of_` 或 `Dec` 消去器 |

## 2. 替代方案优先级

1. **顶层辅助函数**（显式签名）—— 最彻底，完全绕开翻译
2. **`case_of_`** —— 表达式内分支，作用域局部
3. **`inspect` + `rewrite`** —— 需要保留等式证据
4. **`Dec` 消去器**（`Dec-elim` / `⊥-elim`）
5. **直接在函数子句上匹配**（不用 `with`）

## 3. 卡点信号（一出现立即换，不试探）

| 信号 | 含义 |
|---|---|
| `CannotEliminateWithPattern` | with 抽象后的模式无法消去 |
| `UnequalTerms` 且报错位置在 `with-XXXX` | 内部抽象函数与预期目标不匹配 |
| `C-c C-,` 看到 goal 里出现 `with-XXXX` | goal 已被改写 |
| `subst` motive 端点报「`a` vs `a + b`」 | 端点被 with 抽象污染 |
| 同一处 `assoc` 方向反复报错 | 上下文被改写，方向推断失效 |

**「再看一次」是 whack-a-mole 的开始** —— 第三次不成功就换方案。

## 4. 止损协议

```
with-stop-loss :
  ① 单处 with 相关改动，3 次编译不通过 → 立即提取辅助函数
  ② 同一类 with 错误（同信号）出现 2 次 → 记入 prover_limits
  ③ 修改核心定义（Walk / AStep / reduceG 等）时 → 预先审视下游 with 的使用
```

## 5. 反向提醒：不要过度避免

纯局部计算（`with n` 后对 `ℕ` 构造子分支，无 goal 耦合）用 `with` 比提取辅助函数更简洁 ✓。
**判据始终是「scrutinee 是否与类型耦合」，不是「是否用了 with」。**

## 6. 本会话实例（证据）

**`GF3Rank.agda` 的 `elimBelow-heads`**（2026-10-20）✗：
```agda
elimBelow p ((x ∷ xs) ∷ rs) with isZeroT x
... | true  = elimBelow-heads p rs
```
报错：`UnequalTerms` —— goal 是 `allHeads (elimBelow p rs)`，但期望
`if isZeroT x then allHeads (...) else false` ✗ —— **正是信号 ②**：
`allHeads` 内部还有一次 `if isZeroT x`，`with` 只抽象了**外层**那一次 ✗。

**按本纪律的正解**：把 `allHeads` 改成显式接收首项的参数化版本（方案 1）：
```agda
allHeadsWith : ∀ (x : Trit) → Row → Matrix → Bool
```
消掉内层 `if` 之后，`with` 的抽象就与外层一致 ✓。

## 相关

- `memory/search-discipline.md`（跨库检索纪律）
- `prover_limits` 条目：`agda-with-goal-rewrite`、`agda-with-inner-if-nested`、
  `agda-assoc-direction-cubical-vs-stdlib`

---

## 7. ★ 真命题一律不得删（2026-10-20 人类纠正，最严重的一条）

**事故**：`GF3LaplacianN.agda` 的 `lapN-zero : lapN (λ _ → T₀) x ≡ T₀` 一次编译失败（`sumFin` 未归约），
我**把它整个删掉** ✗，并自称「可选 sanity 件」✗。

**人类质疑后**：补上 `sumFin-cong` / `sumFin-zero` / `diffAt-zero` 三个辅助引理，
`lapN-zero` 一次通过 ✓（回执 `7305a258`）。

### 关键区分

| 止损**授权**的 ✓ | 止损**不授权**的 ✗ |
|---|---|
| 放弃一个证明**尝试** | 把**命题**从文件里抹掉 |
| 记录正解，留给下轮 | 删掉后 grep 不到、台账不报、评审看不到 |
| 留下**待办** | **销毁需求** |

**为什么删除最坏** ✗：`{!!}` 至少**诚实** ✓（编译不过、台账报洞 ✓）；
删掉则让缺口**不可见** ✗ —— 下一个人（或自己下一轮）**不知道那里曾有一条真命题** ✗。

### 规矩

真命题编译不过时，三条动作按优先：
1. **补它依赖的辅助引理**（本例：`sumFin-cong`）✓
2. 标 `{!!}` + 台账 `blocked` + 记录正解 ✓
3. 注释里写「待补 + 障碍定位」✓

**唯一禁止：删除** ✗。

**并且**：不许用「可选 / sanity / nice-to-have / 非核心」给自己的无能开脱 ✗ —— 真命题没有可选项 ✗。

已入 `prover_limits`：`agda-deleting-true-props-not-allowed`（severity: **blocker**）

---

## 8. ★ 下判断前先算一遍（2026-10-20，单会话 3 次实证）

**同一病根出现 3 次** ✗：

| 轮 | 我的判断 | 实际 | 是否算过 |
|---|---|---|---|
| 1 | T4「不可达」✗ | 有结构公式 `3^{n−1}+2^{n−1}` | **没算** |
| 2 | 族 B = `0↔2` 交换二项式 ✗ | n=3 起证伪 | 从 RREF 基反推（伪模式）|
| 3 | T-D「需值分类/refactor」✗ | 只需 `sumFin {1}` 展开 + `⊕-idʳ` | **没展开** |

**对照实验**：同一位置的「先猜」耗时 3 轮且失败 ✗；「先算」**1 轮通过** ✓（`66dae0ee`）。

### 协议

凡要说「**难 / 需 refactor / 不可达**」，必须先做过下列**至少一件**并写出结果：

1. **纸笔展开**定义一到两层（例：`sumFin {1} g = g fzero ⊕ T₀`）
2. 跑 `proof_oracle` 算小样本（n=1,2,3）
3. `proof_goals action:"normalize"` 看范式
4. `proof_goals action:"infer"` 看项的类型

### 区分「真 refactor」与「我没算」

| 真 refactor ✓ | 我没算 ✗ |
|---|---|
| 阻碍是**符号签名级**的（例：`Torus6` 是固定六元组，不做 `Torus : ℕ → Set` 就无法对 n 归纳）| 只是**定义没展开** |
| 换写法也绕不开 | 展开一下就有 |

**判据**：**能不能当场算出一个范式/反例来推进？** 能 ⇒ 先算，不要说难 ✓。

已入 `prover_limits`：`judgment-without-computing-first`

---

## 9. ★ 「说卡点」之前必须把两侧形状写出来（2026-10-20，第 4 次同类误判）

**事故**：`NSEOnT6Bridge` 的 `diffAt2-correspond'` 连续 4 次失败 ✗，
我判断为「`cong₂` 两臂**形状不同步**」✗ —— 听起来像**结构性困难** ✗。

**写出来之后**：
```
左 ≡ [diffF6 i f (vecToTuple (LN.shiftAt i v))] ⊕ negate [diffF6 i f (vecToTuple v)]
右   [diffF6 i f (NS.shiftAt6 i (vecToTuple v))] ⊕ negate [diffF6 i f (vecToTuple v)]
                        ↑ 只差这一处 ↑                    ↑ 两边完全相同 ⇒ refl ↑
```
⇒ **只有第一臂不同** ✓ —— 一个 `cong` 就补上 ✓，**一次通过** ✓（`978d2875`）。

### 判据（加进 `judgment-without-computing-first` 的延伸）

**说「卡点」之前，必须把两侧/两臂的**具体形状**逐字写出来对照** ✓。
写不出来 ⇒ 你看到的是「我不会拼」✗，不是「它结构上不行」✗。

| 说法 | 何时才允许 |
|---|---|
| 「两臂形状不同步」✗ | **只在**写出两臂形状、并指出**各自**差在哪里之后 |
| 「需要 refactor」✗ | **只在**写出阻碍是符号签名级的之后 |
| 「不可达」✗ | **只在**算过小样本、看过范式之后 |

**共同结构**：把「我的信息不足」包装成「对象的困难」✗。

---

## 10. ★ `with` 的**正确切分**（2026-10-20，替换此前"一律提取辅助函数"的笼统规则）

### 10.1 两类场景，工具不同

| 场景 | `with` 的状态 | 工具 |
|---|---|---|
| **证明函数自己的递归**（如 `mulX2-twoAt`）| **挡路** ✗ | **`rewrite`** ✓ |
| **用函数的定义做分支**（如 `barrier` 三支）| **正确工具** ✓ | `with` ✓ |

### 10.2 实证

```agda
-- ✗ 场景 1：with 挡住递归引理
mulX2 i p b with lookupAt i b
...
mulX2-twoAt {n = suc n} (fsuc i) p (a ∷ as) = mulX2-twoAt i (p ∘ (a ∷_)) as
-- → [UnequalTerms]：with 抽象后两式不再定义相等

-- ✓ 解法：改写为 rewrite
mulX2-twoAt i p a rewrite lookupAt-twoAt i a = refl
```

```agda
-- ✓ 场景 2：with 是正确工具（用定义本身分支）
mulX2-other i j ne p a avoid with lookupAt j (twoAt i a)
... | fzero            = refl     -- 定义直接归约 ✓
... | fsuc fzero       = refl
... | fsuc (fsuc fzero) = ...      -- 定义直接归约到 p (zeroAt j ...) ✓
```

### 10.3 ⚠ 仍有一个 `with` 会挡路的子情形

**内层 `with` 不替换子项**：
```agda
... | fsuc (fsuc fzero) with p (zeroAt j (twoAt i a))   -- ✗
...     | T₁ = ⊥-elim (contra T₁≢T₀)   -- contra 要 p (...) ≢ T₀，但得到 T₁ ≢ T₀
```
因为 `p (zeroAt j ...)` 出现在 `contra` 的**假设类型**里，`with` 不替换 ✗。

**解法**：改用**三值消去函数** ✓（不做 with ✓）：
```agda
trit-zero : (v : Trit) → (v ≢ T₀ → ⊥) → v ≡ T₀
trit-zero T₀ h = refl
trit-zero T₁ h = ⊥-elim (h T₁≢T₀)
trit-zero T₂ h = ⊥-elim (h T₂≢T₀)
```

### 10.4 判据（一句话）

**问：「我在证这个函数自己的性质，还是在用它的定义分支？」**
- 前者 ⇒ `rewrite`（或改定义去掉 `with`）
- 后者 ⇒ `with` 正确；但若要**把分支值当等式用** ⇒ 用 `trit-zero` 类消去函数

---

## §11. `with` 的**抽象陷阱**（2026-10-20，本会话撞 6 次后定稿）

### 11.1 症状

```agda
sumFin-nonzero : (f : Fin n → Trit) → sumFin f ≢ T₀ → Σ (Fin n) (λ i → f i ≢ T₀)
sumFin-nonzero {suc m} f ne with f fzero in eq
... | T₀ = ...
```

报错：`sumFin (λ j → f (fsuc j)) ≡ f fzero ⊕ sumFin (…)` **不再成立** ✗
—— 因为 `with f fzero` 把 `f fzero` **抽象成变量** ✗，`sumFin f` 的定义展开被**打断** ✗。

### 11.2 三条纪律

| 写法 | 是否抽象掉 `f x` | 能否用它证明 |
|---|---|---|
| `with f x` | ✅ 抽象 | ❌ `f x` 不再归约 |
| `with f x in eq` | ✅ **照样抽象** ✗ | ⚠️ 多一条等式，但归约仍断 |
| **不提 `f x`（改陈述）** | ❌ 不抽象 | ✅ **推荐** |

### 11.3 四个可行解法（按优先级）

**① 改写成逆向陈述** ✓（最推荐）
```agda
-- 想要： A → B
-- 改写： ¬B → ¬A          （构造性逻辑中两者等价）
sum2-zero-off-slice : wt2 b ≠ suc k → sum2 p b ≡ T₀
```
原理：**逆向陈述避开「从结论里抽取某一项」** ✗✓ —— 本轮 §58 一次通过 ✓

**② 把被 `with` 的值提到顶层** ✓
```agda
-- 不在 proof 内部 with，而是先定义一个顶层函数
mulX2-slice : ... → mulX2 (fsuc i) p (k ∷ rest) ≡ mulX2 i (splitAt p k) rest
```

**③ 用消去函数**（`trit-zero` 类）✓
```agda
trit-zero : (v : Trit) → (v ≢ T₀ → ⊥) → v ≡ T₀
```

**④ 用可判定等式 + `⊥-elim`** ✓
```agda
sum2-slice p k sp b nz with wt2 b ≟ suc k
... | yes eq = eq
... | no neq = ⊥-elim (nz (sum2-zero-off-slice p k sp b neq))
```

### 11.4 本会话的 6 次实例

| # | 场景 | 解法 |
|---|---|---|
| 1 | `mulX2-twoAt`（递归卡住）| `rewrite lookupAt-twoAt i a = refl` |
| 2 | `mulX2-slice`（两支同一式）| 显式分三支（`fzero`/`fsuc fzero`/`fsuc (fsuc fzero)`）|
| 3 | `ker-block-fwd` 的 `where` 里 `n` 不在域 | 提顶层 |
| 4 | `Vac-tail-1` 的 `Fin (suc n)` 索引 | 具名常量 + 显式 `{n = 2}` |
| 5 | `sumFin-nonzero`（`with ... in` 抽象）| **改逆向陈述** |
| 6 | `sum2-zero-off-slice` 的 `lookupAt` | `with ... in eqL` + 逆向陈述 |

### 11.5 一句话

**`with` 是「用函数的定义做分支」，不是「拿到分支的值当等式」** ✗
—— 要值当等式，用消去函数或可判定等式 ✓
—— 要从非零结论抽项，改**逆向陈述** ✓

---

## §12. **先 grep 再写**——stdlib 名字不是猜的（2026-10-21，人类批评后定稿）

### 12.1 人类的批评（原话）

> 「本地的大量 agda, lean4, rocq 的代码库，你每次都是一 base grep 检索不出来，
>   让你使用 dsh grep 你不听，每次大量已经完成的代码不使用，反复的推理。」

### 12.2 实例：`3^`-单射

**猜名字的代价** ✗：
```
3^-grow / 3^-mono-<  —— 自己证，4 次类型错误
（"3^a ≤ 3^(suc b)" 的 n≤1+n 用法错了、*-monoʳ-< 的参数方向错了……）
```

**grep 的代价** ✓：
```agda
-- DSH grep `^\^-mono` in agda-stdlib/src/Data/Nat/Properties.agda
-- ⇒ 一行命中：
^-monoʳ-< : ∀ m → 1 < m → Monotonic₁ _<_ _<_ (m ^_)     -- Properties.agda:1128

3^-mono-< = ^-monoʳ-< 3 1<3      -- 一行完成 ✓
```

### 12.3 检索清单（本库常用）

| 想找 | grep 模式 | 位置 |
|---|---|---|
| ℕ 单调性 | `^\^-mono` `^\*-mono` `^\+-mono` | `Data/Nat/Properties.agda` |
| ℕ 等式引理 | `^m∸n` `^\*\-identity` `^m\*n≡0` | 同上 |
| `Fin` 的双射 | `↔` / `remQuot` / `combine` / `\*↔×` | `Data/Fin/Properties.agda` |
| 有限幂等 | `^\^-` | 同上 |
| 本库的 Span/Comb/基 | `IsBasis` / `Comb` / `Span` | `src/Sovereign/Algebra/LinearAlgebra/` |
| 秩/行化简 | `rankOfReduced` / `elimBelow` | `GF3Rank.agda` |

### 12.4 铁律

1. **写任何 `ℕ` 算术引理前，先 grep `Data/Nat/Properties.agda`** ✗✓
2. **写任何 `Fin`/`Vec` 双射前，先 grep `Data/Fin/Properties.agda`** ✗✓
3. **写任何「基/张成/维数」前，先 grep `src/Sovereign/Algebra/LinearAlgebra/`** ✗✓
4. **跨库（Lean/Rocq/Agda）检索**用 DSH `grep` 工具（不是 bash grep）✓
5. 猜名字 = 浪费 3–4 轮；grep = 1 轮 ✓

---

## §13. **Ring solver 替代手写重排**（2026-10-21，人类指点）

### 13.1 症状

`total : (C0 n + C1 n) + C2 n ≡ 3 ^ n` 的归纳步需要 ℕ 重排：
```
((a + 2c) + (b + 2a)) + (c + 2b) ≡ 3·((a+b)+c)
```
手写要 ~80 行 `+-assoc`/`+-comm`/`*-distrib` 链 ✗ —— 而且极易错（`2 * x ≡ x + x` **不是** `refl` ✗）。

### 13.2 ★ 解法：stdlib 的 Ring solver（**一行**）

```agda
open import Data.Nat.Properties using (+-*-commutativeSemiring)
open import Algebra.Solver.Ring.NaturalCoefficients.Default +-*-commutativeSemiring

shuffle = solve 3
  (λ a b c → ((a :+ con 2 :* c) :+ (b :+ con 2 :* a)) :+ (c :+ con 2 :* b)
             := con 3 :* ((a :+ b) :+ c))
  refl
```

### 13.3 关键细节（踩过的坑）

| 坑 | 说明 |
|---|---|
| **`+` 是左结合** ✗ | `a + b + c` = `(a+b)+c` ✓；写成 `a + (b+c)` 形状 ✗ 不匹配 |
| **`con` 写常数** ✓ | `con 2`、`con 3`（不是 `2`、`3`）|
| **变量用 `:+_ :*_`** ✓ | solver 的 `Polynomial` 运算 |
| **`solve n (λ v₁..vₙ → LHS := RHS) refl`** ✓ | `n` = 自由变量个数；末尾 `refl` 是系数相等证明 |
| 互递归定义不自动展开 ✗ | 需显式 `C0-step n` / `C1-step n` / `C2-step n` 重写 |

### 13.4 模块路径

| 用途 | 模块 |
|---|---|
| **ℕ 的预实例化**（最常用）| `Algebra.Solver.Ring.NaturalCoefficients.Default` |
| 一般 `CommutativeSemiring` | `Algebra.Solver.Ring.NaturalCoefficients` |
| 一般 `AlmostCommutativeRing` | `Algebra.Solver.Ring.Simple` |
| 核心 | `Algebra.Solver.Ring`（导出 `prove`/`solve`，`_⊜_` 重命名为 `_:=_`）|

### 13.5 铁律

**写任何 ℕ 重排引理前，先试 Ring solver** ✓ ——
80 行手写 vs 1 行 solver ✓；且 solver 不会出错 ✓。

---

## §14. **消去引理的参数顺序**（2026-10-21，`★C0-odd` 的 5 次失败教训）

### 14.1 症状

`★C0-odd : C0 (2m+1) ≡ 9^m` 的归纳步卡了 **5 次** ✗，错误永远是：
```
The terms  C0 (n + 1 * n + 1)  and  9 ^ n  are not equal
```
看起来像「目标形状不对」✗，实际是 **`cancel` 的第三个参数传错了** ✗。

### 14.2 根因：两处

**① `cancel` 的 `k` 传错**

链条给的是
```
C0(2·suc n+1) + 3·C0(2n+1)  ≡  9^(suc n) + 3·C0(2n+1)
```
而被消去的项我传了 `3 * 9 ^ n` ✗ ——
**`k` 必须是 `3 * C0 (2 * n + 1)`**（链条里出现的那一项）✓

**② `+-cancelʳ-≡` 的参数顺序**

`Algebra/Definitions.agda:154`：
```agda
RightCancellative _•_ = ∀ x y z → (y • x) ≈ (z • x) → y ≈ z
```
⇒ **`x` 是被消去的那一项**，`y z` 是留下的 ✓
⇒ 正确调用：`+-cancelʳ-≡ k a b`（不是 `a b k` ✗）

### 14.3 铁律

1. **`+-cancelʳ-≡` 的第一个参数 = 被消去的项** ✓
2. **写 `cancel` 前，先把等式的两端逐字写出来**，确认 `+ k` 的 `k` 是哪一项 ✓
3. 错误信息里的 `C0 (n + 1 * n + 1)` 是 `C0 (2 * suc n + 1)` 的**规范形式**（`_*_` 展开）✓ —— 不要被它迷惑 ✓

### 14.4 另一个前置：`x ^ suc n = x * x ^ n` 是**定义**

`Data/Nat/Base.agda:296`：
```agda
x ^ suc n = x * x ^ n
```
⇒ `9 ^ suc m ≡ 9 * 9 ^ m` 和 `3 ^ (2m+1) ≡ 3 * 3^(2m)` **都是 `refl`** ✓
⇒ **不要**绕道 `^-distribˡ-+-*`（会在 `m + 1` 上卡住 ✗，因为 ℕ 的 `_+_` 递归在第一个参数）✓

---

## §15. ★★ **`solve` 生成的引理不能应用到复合参数**（2026-10-21，`★E-even`/`★E-odd` 的根因）

### 15.1 症状（卡了 4 轮）

```agda
lin-3B : ∀ B → 9 * B ≡ 3 * (3 * B)
lin-3B = solve 1 (λ B → con 9 :* B := con 3 :* (con 3 :* B)) refl
```
把它应用到 `C0 (2 * (2 * k))`（含 `2 * k`）时：
```
The terms  k  and  k + 1 * k  are not equal at type ℕ
```

### 15.2 根因

`solve` 是 **reflection 宏** ✗ —— 它的证明项内部对表达式做了**规范化**（reify）✓。
当引理应用到**复合参数**（如 `2 * k`）时，Agda 要 unification 目标与该规范化形式 ✗，
而 `_*_` 的定义是 `suc m * n = n + (m * n)` ⇒ `2 * k` 展成 `k + (1 * k)` ✗
⇒ 与目标准形式不匹配 ✗。

### 15.3 ✅ 正确的分层（这是方向）

| 引理的用途 | 该怎么证 |
|---|---|
| **只在裸变量上做线性重排**（如 `3(a+3b) ≡ 3a+9b`）| **`solve` 可以** ✓ |
| **需要应用到复合参数**（如 `9 * C0 (2*(2k))`）| **必须用 `*-assoc`/`*-distrib`** ✓（透明，unification 正常）✗ 不能用 `solve` |
| **抽象代数引理**（裸变量，如 `A + 3B ≡ 4N → ...`）| `solve` + `cancel` ✓ |

### 15.4 已验证的探针结果

```agda
test  : 9 ≡ 3 * 3              -- refl ✓
test2 : ∀ B → 9 * B ≡ (3 * 3) * B   -- refl ✓
```
⇒ `9` 与 `3 * 3` **是** definitional 相等 ✓ —— 所以 `*-assoc 3 3 B` 可以直接用 ✓。

### 15.5 该问题的正确解法（下一步，~40 行）

1. `abstract-odd` / `abstract-even` —— **已证** ✓（纯裸变量线性代数）
2. `lin-3A`/`lin-3B`/`lin-34N` 改用 `*-assoc`/`*-distribˡ-+` 证 ✓（不用 `solve`）
3. 代入：`★E-odd k = abstract-odd (3·A) (3·B) (9^(2k)) (3^(2k)) ...`
4. `★E-even (suc k) = abstract-even A B (9^(2k+1)) (3^(2k+1)) ...`

**WIP 文件**：`engineering/artifacts/GF3HammingCount-WIP-2026-10-21.agda.txt`
（含 `abstract-odd`/`abstract-even` 的完整证明 ✓，只差代入部分）

---

## §16. ★★★ **`2 * k` 是 Agda ℕ 证明的雷区**（2026-10-21，`★E-even`/`★E-odd` 的最终诊断）

### 16.1 现象（卡了 10+ 轮）

任何形如
```agda
f (2 * k)            -- 或 E (2 * k) 其中 E m = C0 (2 * m)
```
的项参与 unification 时，都报
```
The terms  k  and  k + 1 * k  are not equal at type ℕ
```

### 16.2 根因（终于定位）

```agda
-- Data/Nat/Base.agda
suc m * n = n + (m * n)
zero  * n = zero
```

⇒ `2 * k` = `suc (suc zero) * k` = `k + (1 * k)` = `k + (k + (0 * k))` ✗
⇒ 它**不是**任何 `2 * k` 字面形状 ✓，而是一个**嵌套 `+`** ✓

⇒ Agda 在 **unification**（不是 reduction）时，不会把目标里的 `2 * k` 与 `k + (1*k)` 视为同一 ✗

### 16.3 ❌ **无效的尝试**（不要重走）

| 尝试 | 为什么失败 |
|---|---|
| `E m = C0 (2 * m)` 抽象 | **Agda 会 β-展开 `E`** ⇒ 又变回 `C0 (2 * k)` ✗ |
| 把 `solve` 引理改成 `*-assoc` 证 | 引理**本身**透明了 ✓，但**参数里的 `2*k`** 仍然炸 ✗ |
| `subst` 转换索引 | 能转**一处** ✓，但每处都要转，组合爆炸 ✗ |
| 把 `9*B` 写成 `3*(3*B)` | 只是换了个位置 ✗ |

### 16.4 ✅ 唯一可靠的出路

**归纳变量里绝不出现 `2 * k`** ✓ —— 奇偶只在**结论**处拆，不在**索引**处：

```agda
-- ✅ 正确：索引是 m
★C0-even-step : C0 (2 * m + 2) + 3 * C0 (2 * m) ≡ 4 * 9 ^ m

-- ❌ 错误：索引是 2 * k
★E-even : 3 * C0 (2 * (2 * k)) ≡ ...
```

⇒ 要做的是**强归纳/双步归纳**（`m` 上的 `m → m+2` 型递推）✗，
而不是把 `2 * k` 塞进索引里 ✗。

### 16.5 附：这个坑不该出现的原因

如果 `_*_` 定义成 `zero * n = zero; suc m * n = n + m * n` ✓，
那 `2 * k` 仍然是 `k + (k + 0)` ✗ —— **同样的问题** ✗。
真正的解法只有「不写 `2 * k`」✓ —— 或者用 `Vec`/`Fin` 的**结构化**奇偶 ✗。

### 16.6 铁律

> **在 ℕ 上做归纳时，如果索引里出现 `2 * k` / `3 * k` / 任何 `_*_`，
> 立刻停下来改成「索引是 `m`」的形式。** ✓
