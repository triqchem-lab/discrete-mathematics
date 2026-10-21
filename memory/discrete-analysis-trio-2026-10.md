# 离散分析五件套（2026-10-21 会话交付）

> 文件名保留 `trio` 以稳定索引链接；实际覆盖 **5** 个模块。

> 对应台账节点：`DISC.measure.count-additive` / `DISC.ode.kernel-const` /
> `DISC.hilbert.indefinite` / `DISC.functional.separating` /
> `DISC.ode.fredholm-alternative`
> 全库门禁实测 **915 通过 / 0 失败 / 共 915**（本会话新增 5 个模块；其余增量为并行协作者所加）。

## 背景：`Foundation/CompletenessTheorem` 点名的 4 个缺口

该模块把 10 个连续数学概念映射到离散载体，其中 4 个（HilbertSpace / ODEPDE / MeasureTheory /
FunctionalAnalysis）原先标注为「Unit 占位」。**实际载体早已具体化**（这是第 ⑨ 处过期标注，已更正），
真正缺的是**概念特有的结构定律**。本会话处置了其中 3 个。

## 1. `Synthesis/Analysis/DiscreteMeasure.agda` —— 计数测度可加

```agda
Count n = Fin n → Bool            -- 有限集 = 特征函数
count P = #(P)                    -- 计数测度
count-∪ : Disjoint P Q → count (P ∪ Q) ≡ count P + count Q
```
**不相交前提不可省**（否则右侧重复计数）。

**技术要点（通用）**：不要在 `count-∪` 里 `with P zero` —— `with` 会把 `P zero` 抽象成变量，
于是「它就是 `true`」只能**命题地**拿到，`refl` 闭合不了（实测卡两轮）。
正解：把布尔量提成**参数**的 `step-lemma`，四情形全闭合（`true/true` 由互不相交排除）。

## 2. `Synthesis/Analysis/DiscreteODE.agda` —— 齐次解唯一到常数

```agda
Δ-kernel-const : Δ f ≡ (T₀,T₀,T₀) → Σ Trit (λ s → f ≡ (s,s,s))
```
`ker Δ` 恰是 3 个常函数（维数 1）——连续统里是「`u' = 0 ⇒ u` 常数」，这里是 27 情形纯组合。

## 3. `Synthesis/Analysis/DiscreteHilbert.agda` —— ★ GF(3) 配对**不正定**

```agda
⟨ (a,b,c) , (x,y,z) ⟩ = (a⊗x) ⊕ ((b⊗y) ⊕ (c⊗z))
⟨,⟩-sym          : ⟨ f , g ⟩ ≡ ⟨ g , f ⟩          -- ✓ 成立
⟨,⟩-isotropic    : ⟨ isotropic , isotropic ⟩ ≡ T₀   -- isotropic = (T₁,T₁,T₁)
⟨,⟩-not-definite : (∀ f → ⟨ f , f ⟩ ≡ T₀ → f ≡ zero3) → ⊥
```
特征 3 下 `1+1+1 = 0` ⇒ **各向同性向量存在** ⇒ 「离散 Hilbert 空间」只能是**正交空间**，
不能是内积空间：正定性这条公理**在特征 3 下为假**，属**改陈述**而非补证明。

**双线性也已证**（`⟨,⟩-bilinearˡ/ʳ`）：经 `swap`（2×2 转置）两次拼出 2×3 转置 `transpose`，再套 `⊗-distribʳ-⊕`。

## 4. `Synthesis/Analysis/DiscreteFunctional.agda` —— 对偶空间分离点

```agda
Dual = GF3Func → Trit                  -- 不限于线性（更大 ⇒ 分离性更强）
coord₀ coord₁ coord₂ : Dual            -- 三个坐标泛函
separating : (∀ φ → φ f ≡ φ g) → f ≡ g
```
三次投影的 `with` 细化 ⇒ `refl`。Hahn–Banach「对偶分离点」的离散弱化形态。

**一个坑**：`separating-∃ f .f refl φ` 报 `SortOfSplitVarError`——不能在积类型
（`GF3Func = Trit³`）上以 `.f` **点模式**细分。该引理本为同义反复，删掉即可。

**四缺口定案**：MeasureTheory ✅补定律 · ODEPDE ✅补定律 ·
HilbertSpace ❌否证（不正定）· FunctionalAnalysis ✅补分离性。

## 5. 同会话的文档清扫（9 处「文档与代码不符」）

分四类，均为「误导后续会话」型：

| 类 | 例 |
|---|---|
| A 做完未更新 | Pi2dFunctionLayer 右逆 / Omega3Suffix `suffix-resp` / AStepStdGroup 一般走层逆 / Ring3pow11 `modp-add-carry3` |
| B **模块头把完成品说成未完成** | **GF3Barrier**（壁垒定理被藏；已补登 `QUAD.GF3Barrier.thm`） |
| C **命题为假却写成「未做」** | T6AStepCode 的忠实性（正确形态见 `T6AStepFaithful`） |
| D **文档低估代码** | CompletenessTheorem「Unit 占位」（实际已具体化） |

**判据**：函数是否已全定义（构造子逐条有子句）+ 模块编译绿 ⇒ 它就已经存在。
筛查器：`python3 engineering/check_stale_claims.py`（`--markers` 为高精度模式）。

## 5. `Synthesis/Analysis/DiscreteODESolvable.agda` —— 离散 Fredholm 替代

```agda
sum3-Δ     : ∀ f → sum3 (Δ f) ≡ T₀                              -- 必要性（望远镜求和）
Δ-solvable : ∀ v → sum3 v ≡ T₀ → Σ GF3Func (λ f → Δ f ≡ v)      -- 充分性（构造）
```
**可解 ⟺ 全和为 0**：必要侧 27 情形全 `refl`；充分侧给**常数为 0 的积分**
`f = (T₀ , v₀ , v₀ ⊕ v₁)`，9 个可解情形 `refl`、其余 18 个 `()`
⇒ 与 `DiscreteODE.Δ-kernel-const`（核 = 常数）合起来完整刻画 `Δ` 的线性代数。

**流程教训**：自动生成的 Agda 文件**必须**带显式 `module ... where`——否则报
`ModuleNameDoesntMatchFileName`，而**报错行号指向第 1 行的 OPTIONS**，不指向真正缺声明处。

## 6. 补记：`DiscreteMeasure` 的两条公理与命名变化

- **可加性**（§4 `countᵐ-∪`，互不相交）+ **单调性**（§6 `countᵐ-mono`，`P ⊆ Q`）⇒ 计数测度是测度 ✓
- 两处都靠「**对布尔变量分情形的 step 引理**」，不用 `with`（`with` 的抽象会让
  「`P zero` 就是 `true`」只能命题地拿到，`refl` 与矛盾都闭合不了）——本模块两次因此得救
- ⚠ 该模块内 `count` / `_∪_` 已被改名为 **`countᵐ` / `_∪ᵐ_`**（下游引用需同步）

## 7. 补记（后续续作）：对偶维数定理与「链长 ≠ 难度」

`DiscreteFunctional.linear-determined`：**线性泛函由三个基值决定**（对偶维数 = 3）。
三层结构：`φ-eval`（求值公式）+ `decomp`（`⊕-identityʳ`）+ 三条 `•eᵢ≡` 桥引理（`⊗-identityʳ`/`⊗-zeroʳ`）。

**一条自我修正**：此事我曾两批判断「风险高、边际收益低」而不做，实际只花 **3 轮**迭代。
⇒ **链长 ≠ 难度**：只要每一步都有现成引理，长链也能一次写成。**下次遇到同类，先花 2 轮试，再决定是否放弃。**

## 8. 补记：离散上同调 H¹ = 0（闭 = 恰当）

```agda
closed-sum-zero : Δ (Δ v) ≡ zero3 → sum3 v ≡ T₀
h1-vanishes     : ∀ v → Δ (Δ v) ≡ zero3 → Σ GF3Func (λ f → Δ f ≡ Δ v)
```
两步各用一条已有定理：`Δ²-is-const`（库内）给「闭 ⇒ 全和为 0」，`Δ-solvable`（§3）给「全和为 0 ⇒ 有原像」。
⇒ 与 `DiscreteODE.Δ-kernel-const`（H⁰ = 常数）合起来，`0 → 函数 --Δ--> 函数 --Δ--> 函数 → 0` 的**上同调只有 H⁰**。

## 9. 后续补强（同一会话后段）

| 模块 | 新增 | 手法 |
|---|---|---|
| `DiscreteMeasure` | **点质量** `countᵐ (singleton i) ≡ 1` | `singleton i j = if does (i ≟ j) then true else false`；辅助 `fzero≢fsuc` / `singleton-zero-suc` / `countᵐ-zero-tail` / **`suc-dec`（两分支都 `refl`）** |
| `DiscreteODESolvable` | **正合性 `im Δ = ker Δ²`（双向）** | 正向用 `Δ³≡0`；反向用 `closed-sum-zero` + `Δ-solvable` |
| `DiscreteFunctional` | **满射侧** `realize`（三元组 → 线性泛函） | `realize-add` **复用 `DiscreteHilbert.transpose2x3`**；`realize-hom` 用 `⊗-assoc`+`⊗-distribˡ-⊕` |

⇒ ODE 线的正合列与对偶的 `≅ Trit³` 都已完整：
```
0 → 函数 --Δ--> 函数 --Δ--> 函数 → 0     （ker Δ = 常数, im Δ = ker Δ², H¹ = 0）
线性泛函 ≅ Trit³                        （单射 = 维数定理, 满射 = realize）
```

**新增教训**：`suc-dec : does (suc k ≟ suc j) ≡ does (k ≟ j)` **两分支都只需 `refl`**——
`Fin._≟_` 在 `suc/suc` 上递归到内层判定再映射，`with k ≟ j` 之后两侧定义性一致。
⇒ 这类「判定器在构造子上的相容性」通常**不用真证**，写 `with` 试一次 `refl` 即可。
