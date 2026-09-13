# Burnside 引理（块 3）：轨道划分 + 通用纤维分解

**状态**：proven（0 postulate / 0 hole），2026-09-10
**台账节点**：`B.sum.const` / `B.sum.single` / `B.sum.fiber` / `B.orb.partition` / `B.orb.rep` /
`B.orb.fiber-orbit` / `B.orb.stab-const` / `B.burnside.main` / `B.burnside.classical`

## 1. 结论

```
burnside-lemma     : n * numOrbitsOf G A ≡ stabCount G A        -- 乘法形式
burnside-classical : fixCount G A      ≡ n * numOrbitsOf G A    -- 经典形式
```

三条等式合起来就是 Cauchy–Frobenius 引理：`Σ_g |Fix g| ≡ n · #orbits`。

## 2. 为什么必须是乘法形式（**不是**因为「除法截断」）

常见误答：「ℕ 除法是 floor 所以不能用」。那不是承重理由。真理由是：

**整除性 `n ∣ Σ_x |Stab x|` 是 Burnside 的结论，不是前提。**
写成 `#orbits = Σ_x |Stab x| / n`，Agda 要求先交出整除见证 → **循环依赖**。
且 ℕ 的 `_/_` 无见证时无法回推成乘法形式，证明链断在第一步。

而三条已有接口天然是乘法/等式形状：
- 块 2 `stabSize-conj` 给等式 `|Stab (g·x)| ≡ |Stab x|`
- `orbit-stabilizer-auto` 给乘式 `|Orbit a| · |Stab a| ≡ |G|`
- 通用纤维分解给乘式 `Σ_x f (L x) ≡ Σ_y |fiber_y| · f y`

不截断的除法只有 ℚ 除法与分数对子；把 ℕ 计数提升到 ℚ 是过度建模（后续计数论证全部重做），
连分数是把 floor 藏进展开过程且场景错配。**计数场景下「避免截断」= 不用除法，改用乘式。**

## 3. 模块结构（三个新模块，无环；均不修改既有文件）

| 模块 | 行数 | 内容 | 回执前缀 |
| --- | --- | --- | --- |
| `GroupTheory/BurnsideFiber.agda` | 128 | 通用纤维分解 `sumFin-fiber` + `sumFin-const` / `sumFin-single` | `018503dd` |
| `GroupTheory/OrbitPartition.agda` | 266 | 轨道等价关系 + 最小代表元 + 标签纤维=轨道 | `6d704d64` |
| `GroupTheory/BurnsideMain.agda` | 192 | 组装 + 对抗验证 | `b79cfe29` |

依赖方向（无环）：`Burnside` → `BurnsideFiber` → `OrbitPartition` → `BurnsideMain`。
**不往 `Burnside.agda` 追加 §** —— 追加会让块 1/块 2 的回执失效。

## 4. 四步证明链（每步一个具名引理）

```
Σ_x |Stab x|
  ≡ Σ_x |Stab (orbRep x)|                     块 2 拉平（stabSize-orbRep）
  ≡ Σ_x |Stab (toFin RepEnum (orbLabel x))|   orbLabel-ok（定义性）
  ≡ Σ_y |fiber_y| · |Stab (toFin RepEnum y)|  通用纤维分解（sumFin-fiber）
  ≡ Σ_y n ≡ #orbits · n                       纤维=轨道 + orbit-stabilizer-auto
```

## 5. 复用账（真新增只有两处）

| 需要 | 用了谁的 | 重造？ |
| --- | --- | --- |
| 群代数（结合/逆/双重逆/左消去） | `FinGroup` record 字段 | ❌ |
| 双射 ⇒ 基数相等 | stdlib `cantor-schröder-bernstein` | ❌ |
| 子类型枚举 `SubEnum` / `index-ok` | `CosetAuto` | ❌ |
| 结构性最小搜索 `firstIn` | `CosetConstruction` §3 | ❌ |
| 求和的秤 `sumFin` / `size-as-count` | `Burnside` §1–§2 | ❌ |
| orbit-stabilizer（自动版） | `OrbitStabilizerAuto.orbit-stabilizer-auto` | ❌ |
| **共轭把 |Stab| 沿轨道拉平** | 块 2 | ❌（只是接线） |
| **通用纤维分解** | 本块新写 | ✅ |
| **纤维 = 轨道（CSB 双向单射）** | 本块新写 | ✅ |

## 6. 两个真实教训（编译现场，非事后审查）

### 6.1 `1 * n` 展开成 `n + 0`，而 `n + 0` **不**定义性归约

- **症状**：`sumFin-single` 报 `UnequalTerms`：`f fzero` 与 `f fzero + 0 * f fzero` 不等。
- **判据**：写 10 行探针 `ProbeReduce.agda` 逐条打归约表 ——
  `0 * n`、`1 * n`、`bit (fzero ≟ fzero)`、`bit (fsuc y ≟ fzero)`、`0 + n` **都归约**；
  **唯 `n + 0` 卡住**（`_+_` 匹配第一参数，变量头不归约）。
- **做法**：显式接 `+-identityʳ`，不指望 `refl`。
- **教训**：「`1 * n` 展开成 `n + 0 * n`」是**乘法定义形式**的直接后果，不是证明策略问题。
  先查被调函数的定义形式。

### 6.2 定义函数不可反演 ⇒ 隐式参数反解会留元变量

- **症状**：`fiberSizeEqOrbit` 报 `UnsolvedConstraints`，约束里出现未解元变量 `_y_708`
  （本应是 `SubEnum.toFin RepEnum y`）。
- **判据**：Agda 要从 `orbRep ? ≡ orbRep ?` 反解 `orbLabel-cong` 的隐式参数，
  但 `orbRep` 是**定义**而非构造子，Agda 不反演。
- **做法**：① `orbLabel-cong` 改走 `SubEnum.toFin-inj`（避开 `index-cong`）；
  ② 显式标注 `{x}{r}` / `{r}{x}`；③ 顺带修正 `orbRep-eq-of-eq` 的插入方向（原方向插反）。
- **教训**：从定义函数的等式反解隐式参数 = 必然留元变量。**显式标注比换策略有效。**

## 7. 对抗验证（§4，全 refl 通过）

| 作用 | #orbits（独立 refl） | Σ_x |Stab x|（独立 refl） | 定理实例 |
| --- | --- | --- | --- | --- |
| C₄ 正则（传递） | 1 | 4 | `4 * 1 ≡ 4` ✓ |
| C₄ 奇偶（传递） | 1 | 2 + 2 = 4 | `4 * 1 ≡ 4` ✓ |
| C₄ 平凡作用 Fin 3（**非传递**） | 3 | 3 × 4 = 12 | `4 * 3 ≡ 12` ✓ |

非传递实例是关键：它是唯一能测出 `numOrbits ≠ 1` 的情形，防止「传递作用碰巧对上」。
经典形式另给一条独立路径：`fixCount C4 C4-trivial ≡ 12`。

## 8. oracle（先算后验证闸门）

`engineering/tests/oracle_burnside_block3.py`，回执 `661a09c3…`，**120998/120998 完备穷举**（非抽样）：

- 阶 ≤ 6 的**全部**群（C1/C2/C3/C4/V4/C5/C6/S3，群论分类穷尽）× `Fin p (p≤5)` 的**全部**作用
  （生成元映到 Sym(p) 的全部满足定义关系者；群同态由生成元唯一决定，von Dyck ⇒ 完备）：
  核对 `n·#orbits == Σ_x|Stab x|`、扁平化重排、同轨道 `|Stab|` 相等、`|Orbit|·|Stab| == n`；
- `p≤5, m≤4` 的**全部** `(L, f)`：核对 `Σ_x f(L x) == Σ_y |fiber_y|·f y`。

## 9. 诚实边界

- 作用是**有限集 `Fin p`** 上的（`#orbits` 才有限）；不声称无限作用或拓扑群的 Burnside。
- `#orbits` 的定义取「轨道内 `toℕ` 最小元」作**判据**——换判据结论不变，本模块不证这一点。
- oracle 覆盖阶 ≤ 6 的群；更高阶未穷举（Agda 证明本身对任意 `n` 成立，不依赖 oracle）。
- 编译通过 ≠ 物理正确。
