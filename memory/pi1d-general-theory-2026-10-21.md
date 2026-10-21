# π₁ᵈ 一般理论：三模块汇总（2026-10-21）

**触发**：台账节点 `PIO-1.card-general-theory`（对任意图 G 刻画并计算 π₁ᵈ(G) 的基数）。
**结果**：主定理 + 两条判据已证；**基数计算部分仍未做**（缺计数机件），如实挂账。

---

## 一、一句话结论

**π₁ᵈ(G) 是幺半群；它何时塌缩、何时是群，完全由 G 的「有向三角形」决定。**

---

## 二、三模块与它们各自的位置

| 模块 | 内容 | 回执 |
|---|---|---|
| `Homotopy/Pi1dMonoid.agda` | `_++w_` 的左右单位律、结合律；关于 `AHomotopy` 的左/右同余；合并乘法同余 | `3fe1ad43` |
| `Homotopy/Pi1dCardinality.agda` | **塌缩判据**（主定理）+ 长度事实 + **群性判据** | `d59f914f` |
| `Homotopy/BarceloAHomotopy.agda`（既有） | `DiGraph` / `Walk` / `AStep` / `AHomotopy` 定义层 | — |

---

## 三、主定理：塌缩 ⟺ 有向三角形

```agda
no-collapse-iff-triangle-free : ∀ {G : DiGraph} → (NoCollapse G) ↔ᵈ (TriangleFree G)
-- NoCollapse G   = ∀ {p q} → AHomotopy G p q → p ≡ q
-- TriangleFree G = ∀ {x y z} → edge x y → edge y z → ¬ (edge x z)
```

| 方向 | 机制 |
|---|---|
| ⇐ | `AStep` 的 `slide` / `expand` **都**要求一组三角形 `e1:x→y, e2:y→z, e3:x→z` ⇒ 无三角形时 `AStep` 空 ⇒ `AHomotopy` 只剩 `refl'/symm/trans'` ⇒ 就是命题相等 |
| ⇒ | 给定三角形，取 `p = cons e1 (cons e2 nil)`（长 2）、`q = cons e3 nil`（长 1）；`slide (nil x) (nil z) e1 e2 e3 : AStep G p q` ⇒ `gen` 给 `AHomotopy`；而 `p ≢ q`（`walk-len` 区分 2≠1）|

**⇒ 每个有向三角形至少粘合一对不同的走**；没有三角形则**一个也不粘合**。

---

## 四、两条判据

### 4.1 长度

- **一般事实**：`AStep-changes-len` —— 任何 AStep 都改变走长
  （`slide`：`|p| + (2 + |b|) → |p| + (1 + |b|)`）
- **无三角形时**：`ahomotopy-preserves-len`（保长）、`differing-len-not-AH`（逆否）

### 4.2 群性

```agda
no-inverse-for-pos : AHomotopy G (w ++w w') (nil v) → ¬ (0 < walk-len w)
group-trivial-when-triangle-free :
    无三角形 + π₁ᵈ 是群  ⇒  所有闭走长度为零（π₁ᵈ 平凡）
```

**⇒ 无三角形时，只要存在正长闭走，`π₁ᵈ(G)` 就不是群** ✓

### 4.3 幂等

```agda
idempotent-len-zero : AHomotopy G (w ++w w) w → walk-len w ≡ zero
no-pos-idempotent   : AHomotopy G (w ++w w) w → ¬ (0 < walk-len w)
```

---

## 五、诚实边界（三条，都未闭合）

| 缺口 | 状态 | 原因 |
|---|---|---|
| **基数计算** | ❌ 未做 | 需要 `V` 有限 + 可判定相等 + 枚举，才能定义 `(A^n)_{vv}` 计数；本库无此机件 |
| **`walk-len w ≡ 0 → w ≡ nil u`** | ❌ 不可证 | 库开 `--cubical` ⇒ without-K；闭走形态卡在消除自反方程 `u = u`（见 prover_limits `agda-without-k-reflexive-index-split`）|
| **`PIO-1.conj.*` 幂等判据** | 已 refuted ×2 | 「π₁ᵈ 幂等 ⟺ G 含三角形」→ refuted；「每条边属于三角形」→ refuted。与**本线**的「塌缩」不是同一命题，勿混 |

**「基数相等」的可形式化内容**确实已有：`pi1d-class-is-point` / `class-singleton`
—— 无三角形时每个 `AHomotopy`-类**恰是单点**，故商与闭走等基数 ✓。
但那不给出**数值**；要数值必须建计数机件。

---

## 六、可引用锚点

| 内容 | 锚点 |
|---|---|
| 幺半群律 | `Pi1dMonoid.agda:++w-identityʳ/ˡ`, `++w-assoc`, `AH-++w`, `AH-++wˡ`, `++w-cong` |
| 塌缩主定理 | `Pi1dCardinality.agda:no-collapse-iff-triangle-free` |
| 三角形见证 | `Pi1dCardinality.agda:triangle-collapses` |
| 长度事实 | `Pi1dCardinality.agda:AStep-changes-len`, `walk-len-++w` |
| 群性判据 | `Pi1dCardinality.agda:no-inverse-for-pos`, `group-trivial-when-triangle-free` |
| 塌缩实例（既有） | 台账 `PIO-1a.library-side`（`gcmp-classify`，`Gcmp two-chain` 商只有 2 元）|

---

## 七、下一步（按依赖序）

1. **计数机件**：有限 `V` + 邻接计数 `ECount : V → V → ℕ` + `WCount n u v` 的矩阵幂恒等式
   → 才能陈述「无三角形时 |π₁ᵈ| = Σ_n WCount n v v」
2. 有了它，`PIO-1.card-general-theory` 才能真正结案
3. **不要**去证「`w ≡ nil`」形态 —— without-K 阻断，已入限制库
