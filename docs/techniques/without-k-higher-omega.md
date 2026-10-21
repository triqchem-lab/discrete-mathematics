# `--without-K` 的 K 墙与 `Ωⁿ` 的破法（2026-10-21，本会话三实例实测）

> **为什么写这份**：人类 2026-10-21 的诊断指出「高阶同伦（`π₂ᵈ` 以上）基本空白，
> `Ωⁿ` 一般递归卡 K 墙」。本会话在**一阶**上恰好两次撞到同一堵墙并绕过去了。
> 把绕法固化下来，是让高阶线**可重新开工**的最便宜一步 —— 不是新定理，是**可复用技法**。

---

## 一、墙是什么

库的 `agda-lib` 里开了 `--cubical`，因此 `--without-K` 生效。后果：

```agda
w : Walk G v v          -- `v` 在 Walk 的两个索引位置**同时**出现
-- 想对它做构造子 split（nil / cons）⇒
--   SplitError.UnificationStuck: Cannot eliminate reflexive equation v = v
```

`Walk G : V → V → Set` 是索引族，两个索引**相等时** Agda 拒绝消去
（`--without-K` 禁止把 `refl` 式方程当构造子方程用）。

**这堵墙正好卡在 `Ωⁿ` 上**：`Ωⁿ⁺¹ X c` 的定义就是 `Walk (Ωⁿ-graph X) c c`
—— 同一个 `c` 在两个索引位置 ⇒ 想「归纳一个 2-走」就撞墙。

---

## 二、破法（**同一个手法，三种形态**）

### 破法 A：把陈述写成**一般端点**，split 留在构造层

`Walk G u v` 里 `u`、`v` 是**不同变量**时 split **完全合法** ✓

```agda
-- ✗ 撞墙：对 `Walk G v v` 归纳
-- ✓ 合法：对一般端点归纳
canon : IsComplete G → (a : V) (e : edge v a) (p : Walk a v)
      → AHomotopy G (cons e p) (cons (c v v) (nil v))
canon c a e (nil .a)    = ...
canon c a e (cons e' p) = ... canon c _ e' p
```

- **实例**：`Sovereign.Synthesis.Homotopy.Pi1dCompleteIdempotent.canon`
- 要点：**不用** `walk-len`、**不用** well-founded recursion —— 直接对**尾部走**结构递归。

### 破法 B：把 split **移到调用点**（把走已经分解好地传进来）

```agda
-- ✗ 主语是 `Walk G v v`，要 split ⇒ 撞墙
-- ✓ 主语是「已分解的走」，split 由调用者完成
complete-idempotent-cons :
    (c : IsComplete G) (e : edge G v a) (rest : Walk G a v)
  → AHomotopy G (cons e rest ++w cons e rest) (cons e rest)
complete-idempotent-cons c e rest =
  AH-trans (canon c _ e (rest ++w cons e rest))
           (AH-symm (canon c _ e rest))
```

- **实例**：`Pi1dCompleteIdempotent.complete-idempotent-cons` / `complete-idempotent-nil`
- 效果：「完全 ⇒ 幂等」的**两个实质情形全部证出**，只剩「按 `Walk` 构造子合并成
  `∀ w`」这一步被禁 —— **这一步是编译器限制，不是数学缺口**（已在台账写明）。
- 代价：**定理形态变了**（多一个分解参数）。这是**诚实的形状改变**，不是把命题改弱：
  两个情形合起来蕴含原命题，只是合并步骤无法在本库内表达。

### 破法 C：**换载体**，让等式成为真等式而不是需要 `funext` 的等式

函数载体上 `f (f (f x)) ≡ x` 需要 `funext`（库无）⇒ 卡死；
`Vec` 载体上同一条是**真等式** ✓

```agda
updAt-cubed : ∀ j (v : T6Vec n) → updAt j (updAt j (updAt j v)) ≡ v
```

- **实例**：`T6CayleyVec.updAt-cubed`（Vec 载体）vs `T6CayleyGraph.stepGen-cubed`（函数载体，**放弃**）
- 判据：**凡是需要「三个生成元回到原点」这类等式的地方，选 Vec，不选函数**。

---

## 三、反模式（**别再试**）

| 反模式 | 为什么不行 | 实测 |
|---|---|---|
| `with walk-len w` 再分 case | 想从长度 0 推出 `w ≡ nil v` 仍需 split ⇒ 同样撞墙 | 见 `Pi1dCardinality.walk-len-zero` 的绕法（用显式端点等式 + `refl` 特化） |
| 用 well-founded recursion | 不是墙的成因；`canon` 用**普通结构递归**就够 | 一次就过 |
| 靠 `subst` 把 `Walk G a a` 变成 `Walk G a b` 再 split | `subst` 只改**类型**，不改**已抽象的项**；split 仍然被拒 | — |
| 把端点 `refl` 化后再 split | `--without-K` 正是禁止这个 | 墙的原话：`Cannot eliminate reflexive equation v = v` |

---

## 四、对高阶线的直接含义（`π₂ᵈ` 以上）

1. **幺半群部分是免费的**：`++w-assoc` / 单位律对**任意** `DiGraph` 成立
   （`Pi1dMonoid` 就是这种一般陈述）⇒ 每一层的 `Ωⁿ` 只要构成 `DiGraph`，
   结合律立刻到手，**不需要重证** ✓
2. **卡住的是「消去 / 归纳」**：凡是「对 `Ωⁿ` 的一个元素做构造子 split」的证明，
   都必须按破法 A/B 重写成**一般端点 + 分解参数**的形状。
3. **`πₙ` 的定义本身要设计成可消去的形状** —— 这是 `Ωⁿ` 一般递归的先决条件，
   比「写更多定义」更优先。

---

## 五、诚实边界

- 本节**不是**高阶同伦的推进，是**技法记录**；`π₂ᵈ` 的计算层仍为空。
- 三实例都只在一阶（+ `Ω¹` 的 Cayley 载体）上验证过，**未在 `Ω²` 及以上实测**。
- 破法 B 的代价（定理多一个参数）在实际做 `π₂ᵈ` 时可能累积成很重的签名 —— 未量化。
