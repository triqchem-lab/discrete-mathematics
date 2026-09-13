# Burnside 块 5：项链计数（招牌应用）

**状态**：proven（0 postulate / 0 hole），2026-09-10
**台账节点**：`B.necklace.rot4` / `B.burnside.app-necklace` / `B.necklace.decomposition`
**回执**：`0c6ed442…`（BurnsideNecklace.agda，**一次通过**）
**oracle 回执**：`686bbf90…`（domain = points = **1488721**，即 n=1..10 × c=2..4 的全部着色）

---

## 一、结论

```
2 色 4 珠的项链数 = (1/4)·(2⁴ + 2¹ + 2² + 2¹) = 24/4 = 6
```

形式化为：

```
rot : Fin 16 → Fin 16                          -- 4-bit 串循环右移
rot n = f16 (toℕ n % 2 * 8 + toℕ n / 2)        -- f16 k = fromℕ< (k % 16 < 16)
rot⁴ : ∀ x → rot (rot (rot (rot x))) ≡ x       -- 16 case refl

C4-necklace : Action C4 (Fin 16)               -- 项链 = 轨道

necklace-numOrbits  : numOrbitsOf C4 C4-necklace ≡ 6      -- refl
necklace-fixCount   : fixCount C4 C4-necklace ≡ 24        -- refl
necklace-stabCount  : stabCount C4 C4-necklace ≡ 24       -- refl
necklace-classical  : fixCount C4 C4-necklace ≡ 4 * 6     -- burnside-classical
```

不动点分布与纸面一致：`|Fix id| = 16`、`|Fix rot| = |Fix rot³| = 2`、`|Fix rot²| = 4`，和 = 24。

## 二、为什么这是块 3/4 之后的正确一步

块 3 的实例是 C₄ 正则 / 奇偶 / 平凡（`#orbits ∈ {1,3}`），块 4 加了非传递非自由（`#orbits = 2`）——
**都是群论内部造出来的玩具作用**。块 5 换成一个**真实的组合计数问题**：项链是数学家会去数的东西，
`6` 这个数字可以被任何一本组合数学书独立核对。至此「Lagrange → orbit-stabilizer → Burnside 三块 → 判据无关 → 应用」
这条链第一次产出一个**外部可验证的数**。

## 三、工程要点

### 3.1 `act-⊙` 不穷举 256 case

`act-⊙ : ∀ g h x → act (g +4 h) x ≡ act g (act h x)`，字面穷举是 `4 × 4 × 16 = 256` 个 case（**远超 27 上限**）。

改为按 `(g, h)` 分 **16 个 case**，每个 case 对 `x` 保持符号化：

| 类型 | 个数 | 依据 |
|---|---|---|
| `refl` | 8 | `act` 与 `_+4_` 都定义性地归约 |
| `sym (rot⁴ _)` | 8 | 归约到「rot 是 4 阶置换」，作用在 `x` 的某次迭代上 |

例如 `(g,h) = (3,3)`：`3 +4 3 = 2`，目标是 `rot² x ≡ rot⁶ x`，正是 `rot⁴ (rot² x)` 的 `sym`。
每个 case 都是**具名事实的直接应用**，不是暴力计算。

### 3.2 `rot` 的建值：`fromℕ<` 的归约不依赖界证明

stdlib 2.4 把 `fromℕ` 改成了「取 `Fin (suc n)` 的顶元素」——**不再是 `ℕ → Fin n` 的函数**。
正确的建值途径是 `fromℕ< : .(m ℕ.< n) → Fin n`，且它的定义

```agda
fromℕ< {zero}  {suc _} _   = zero
fromℕ< {suc m} {suc _} m<n = suc (fromℕ< (ℕ.s<s⁻¹ m<n))
```

递归在**隐式索引 `m`** 上，不在证明上；界是不可约的 `.`，`ℕ.s<s⁻¹` 即便卡住也不阻碍 `suc` 逐层产出。
所以 `f16 k = fromℕ< {k % 16} {16} (m%n<n k 16)` 对具体 `k` 会归约到第 `(k mod 16)` 个元素 ✅，
而界证明用 `Data.Nat.DivMod.m%n<n` 一次给出，不必手写 `s≤s` 嵌套。

### 3.3 对抗验证：不只核对「一个数」

只核对 `#orbits = 6` 可能是巧合。`§4` 把 16 个着色按轨道划分逐条列出：

| 轨道 | 大小 |
|---|---|
| {0000} | 1 |
| {1111} | 1 |
| {0001, 0010, 0100, 1000} | 4 |
| {0011, 0110, 1100, 1001} | 4 |
| {0101, 1010} | 2 |
| {0111, 1011, 1101, 1110} | 4 |

六个大小全部用 `SubEnum.size (orbEnum …)` **独立 refl** 算出，`partition-sum 1+1+4+4+2+4 ≡ 16`，
并与 oracle 逐条打印的轨道分解**逐字对齐**。

### 3.4 踩坑：Agda 的 LHS 模式必须加最外层括号

生成器先产出 `rot⁴ fsuc (fzero) = refl`，Agda 报
`WrongNumberOfConstructorArguments: The constructor fsuc expects 2 arguments ... but has been given 1`。

根因：Agda 的**左端按项解析**，`rot⁴ fsuc (fzero)` 被解析成「`rot⁴` 应用于两个模式 `fsuc` 与 `fzero`」，
因为 `fsuc` 单独就是合法项、应用左结合。修法：`rot⁴ (fsuc fzero) = refl`。
（已沉淀 `prover_limits: agda-lhs-pattern-outer-parens`；对**生成代码**尤其容易踩。）

## 四、oracle（先算后验证）

`engineering/tests/oracle_necklace_block5.py`，回执 `686bbf90…`，**1488721 个着色**完备穷举（非抽样）：

- n = 1..10、c = 2..4 的**全部** `cⁿ` 着色，逐点算轨道（旋转群 C_n）：
  ① 轨道划分完整且不重不漏；② Burnside 定义式 `Σ_x|Stab x| == n·#orbits`；
  ③ 与闭式 `Σ_{d|n} φ(d)·c^(n/d) / n` 一致。三者互相独立。
- 4 珠 2 色：恰 6 条项链、轨道大小 `[1,1,2,4,4,4]`。

**计数单位修正**：初版 `domain` 只数 `(n,c)` 三元组（33），掩盖了真实枚举量；
改成以**单个着色**为计数单位后 `domain = points = 1488721`。
这正是块 4 那条教训（「断言要按段拆开各给 domain，且量级要有预期」）的延续。

## 五、诚实边界

- 只算 **2 色 4 珠**这一具体实例；一般 `n` 的项链计数**未形式化**（oracle 覆盖到 n≤10，但那不是证明）。
- `rot` 的「颜色语义」是本模块选定的一种编码（低位 = 第 0 珠）；换编码得同构的作用，本模块不证编码无关性。
- 作用于有限集 `Fin 16`；不声称无限或连续情形。
- 编译通过 ≠ 物理正确。
