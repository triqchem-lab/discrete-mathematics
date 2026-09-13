# Burnside 块 6：作用同构不变性（并补上块 5 的编码无关性边界）

**状态**：proven（0 postulate / 0 hole），2026-09-10
**台账节点**：`B.action.iso-invariant` / `B.necklace.direction-free`
**回执**：`bc6af800…`（ActionIsomorphism，5.2s）｜`8f4515d3…`（NecklaceInvariance，**冷编译 171s**）
**oracle 回执**：`6beff5e9…`（domain = points = 68096）

---

## 一、结论

**主定理（作用同构不变性）**

```
action-iso-invariant :
  给出互相的等变单射 f : Fin p → Fin q 与 fb : Fin q → Fin p
     f  (g ·_A x) ≡ g ·_B (f  x)
     fb (g ·_B y) ≡ g ·_A (fb y)
  ⟹ numOrbitsOf G A ≡ numOrbitsOf G B
```

**应用（块 5 的编码无关性）**

```
bit-reversal rev 把旋转共轭到反向旋转：rev (rot x) ≡ rot⁻¹ (rev x)
⟹ C4-necklace ≅ C4-necklace-inv（反向旋转作用）
⟹ numOrbitsOf C4 C4-necklace-inv ≡ numOrbitsOf C4 C4-necklace
```
两个编码**各自独立 refl** 算出 **6**。

块 5 模块头明写：「rot 的『颜色语义』是本模块选定的一种编码（低位 = 第 0 珠）；换编码得同构的作用，**本模块不证编码无关性**。」——本块把它补上。

## 二、证明骨架

等变映射把轨道送到轨道 ⟹ 两个代表元系统等势。落成两个有限枚举之间的双射：

```
Φ  : {A 的不动代表元} → {B 的不动代表元},  x ↦ orbRep_B (f x)
Ψ  : {B 的不动代表元} → {A 的不动代表元},  y ↦ orbRep_A (fb y)
```
`Φ` 单射的关键链（**这是本块的全部数学内容**）：
`f a`、`f b` 在 B 同轨道 ⟹ `∃g, g ·_B (f a) ≡ f b` ⟹ 等变性给 `f (g ·_A a) ≡ f b`
⟹ `f` 单射给 `g ·_A a ≡ b` ⟹ `a`、`b` 在 A 同轨道 ⟹ 两者皆 A 的不动代表元 ⟹ `a ≡ b`。

交给 stdlib `cantor-schröder-bernstein`（`f`/`g` 是隐式参数）收口，未自写基数搬运。

**结论强于「基数相等」**：只断言 `numOrbits` 相等，**不**要求 `p ≡ q`。

## 三、工程要点

### 3.1 `·-⊙` 只按 `g` 分 4 个 case

反向旋转作用的 `act-⊙` 本可展开成 4×4×16 个 case。做法：
`inv₄-hom : ∀ g h → inv₄ (g +4 h) ≡ inv₄ g +4 inv₄ h`（16 case refl，≤27 合规）承担**全部**内容；
因 **C₄ 交换**，`(g+h)⁻¹ = g⁻¹ + h⁻¹` 无需反序引理（`(gh)⁻¹ = h⁻¹g⁻¹`），`·-⊙` 退化成
`trans (cong (λ z → act z x) (inv₄-hom g h)) (·-⊙ C4-necklace (inv₄ g) (inv₄ h) x)` 一行。

### 3.2 `rev-act` / `back-act` 各 4 个 case

`rev (act g x) ≡ act (inv₄ g) (rev x)`：对 `g = 0,1,2,3` 分别是 `refl` / `rev-rot` /
（两段 `rev-rot` 复合 + `rot⁴`）/ `rev-roti`。两个 16-case 引理 `rev-rot`、`rev-roti`
是全部素材，**不出现 256 个 case**。

### 3.3 踩坑：又栽在「生成代码的模式括号」上

`inv₄-hom` 有 **2 个参数**，生成器产出 `inv₄-hom fsuc fzero fzero = refl`，
被解析成 3 个参数 → `WrongNumberOfConstructorArguments`。修法：`inv₄-hom (fsuc fzero) (fzero) = refl`。
**这正是块 5 刚沉淀的 `prover_limits: agda-lhs-pattern-outer-parens` 立刻复发** ——
生成代码时对**每一个**参数都包括号，不要只包带嵌套的那个。

## 四、已知性能代价（诚实记录）

`NecklaceInvariance.agda` 冷编译 **171s**，是本库实测最慢模块。定位实验：

| 版本 | 冷编译 |
|---|---|
| §1–§4 全量 | 169s |
| §1–§3（去掉 §4 的两个具体数 refl） | 165s |
| `ActionIsomorphism`（通用定理，无 Fin 16 实例） | 5.2s |

**结论：成本在「通用定理于 Fin 16 的实例化」，不在 §4 的 refl。**
根因：`Φ : … → Fin (SubEnum.size PA.RepEnum) → Fin (SubEnum.size PB.RepEnum)` ——
`SubEnum.index` / `toFin` 的**类型下标**是 `SubEnum.size RepEnum` 这类具体计算，
每次出现 Agda 都要展开 16 层 `enum` 连同每层的 `orbRep` 最小元搜索（`firstIn` + `searchFin`）。
这是**实例规模问题**，不是设计缺陷。缓解方向（未做）：用 `abstract` 把 `RepEnum` 的尺寸计算封成不透明常量，
或在更小的实例（如 2 珠 2 色 = Fin 4）上验证编码无关性。

已删除一处**重复命题**：`necklace-both-six` 与 `necklace-inv-numOrbits` 是同一陈述，删掉前者。

## 五、oracle（先算后验证）

`engineering/tests/oracle_action_iso_block6.py`，回执 `6beff5e9…`，**68096** 完备穷举（非抽样）：
阶 ≤ 6 的**全部**群 × `Fin p (p≤5)` 的**全部**作用 × `Sym(p)` 的**每一个**置换 σ，核对：
① 共轭作用 `A^σ` 仍是作用；② σ 在 `A` 与 `A^σ` 之间等变；③ 轨道大小多重集不变（⇒ `#orbits` 不变）。

### ⚠ 自审：我写的第一版「否定控制」是空转的

初版设置了 `changed_somewhere` 来衡量「非等变置换是否会改变轨道结构」，但它是**由那个永不失败的比较**
（③）设置的 —— 逻辑上必然恒假，输出 `0 个` 看起来像「找到了反例基线」，实际什么都没测。

改成真正有内容的见证：对每个**非平凡**作用，检查是否存在置换 τ 使 `τ (g·x) ≠ g·(τ x)`
（即 τ 不是自等变的，说明「随便一个双射」不够、等变性是必要条件）。结果 **693/700**。
余下 7 个是 p=2 的情形：作用像 = Sym(2) 且 Sym(2) 交换 ⟹ 所有置换自等变 —— **这是真事实，不是缺陷**，
故把该检查从失败判据降为报告项。

**教训**：「否定控制」必须独立于被验证的比较；若它由同一个比较驱动，它测的是空气。
这与块 4 那条「断言要按段拆开、量级要有预期」是同一族问题：**让指标可见，才能发现它是空的。**

## 六、诚实边界

- 结论只是 `#orbits` 相等，**不**断言 `p ≡ q`，也**不**断言两个作用作为 G-集同构。
- 只证了「正向旋转作用 ≅ 反向旋转作用」这一对编码；一般「任意编码」的无关性需要先把
  「编码」形式化成 G-集同构类，本模块不做。
- oracle 的完备性是**共轭不变性**意义下的（同一载体上的重标号天然带等变 σ）；
  本脚本不构成「跨不同载体」的独立见证。
- 编译通过 ≠ 物理正确。
