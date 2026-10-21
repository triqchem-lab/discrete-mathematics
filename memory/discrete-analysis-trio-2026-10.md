# 离散分析四件套（2026-10-21 会话交付）

> 文件名保留 `trio` 以稳定索引链接；实际覆盖 **4** 个模块。

> 对应台账节点：`DISC.measure.count-additive` / `DISC.ode.kernel-const` /
> `DISC.hilbert.indefinite` / `DISC.functional.separating`
> 全库门禁实测 **914 通过 / 0 失败 / 共 914**（本会话新增 4 个模块；其余增量为并行协作者所加）。

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

**未做（如实标注）**：`⟨,⟩` 的双线性（需六元 `⊕` 重排；最省路线是先证 3 元旋转
`a⊕(b⊕c) ≡ b⊕(c⊕a)` 再套两次）。模块头已明写「本模块未证」。

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
