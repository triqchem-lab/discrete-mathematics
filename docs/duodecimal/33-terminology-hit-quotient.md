# HIT 商群术语体系——FreeAbQuotient · FreeAbImEquiv

> **日期**: 2026-10-04
> **性质**: Hodge K3 同调商群术语——cubical HIT SetQuotients + Σ 商等价 + transport-of-structure
> **来源**: FreeAbQuotient (6 件闭合) + FreeAbImEquiv + HomologyLES

---

## 一、HIT 商类型（cubical SetQuotients）

| 术语 | 定义 | 代码 | 来源 |
|---|---|---|---|
| **商类型** | A / R：集合 A 模等价关系 R 的商 | `H₀ = C₀ / R₀` | Cubical.HITs.SetQuotients |
| **[_]** | 商类注入器：x ↦ [x] | `[_] : A → A / R` | eq/ 构造 |
| **eq/** | 商等价构造：R a b → [a] ≡ [b] | `eq/ x y h : [x] ≡ [y]` | — |
| **squash/** | 商类型的 isProp：[a]≡[b] 是命题 | `squash/ : isProp([a]≡[b])` | H₀ 是 Set |
| **elim** | 商类型消去器（一般形式） | `elim : ... → A/R → P` | — |
| **elimProp** | 消去器（P 是 Prop 时简化版） | `elimProp : ...` | — |
| **elimProp2** | 二元消去器 | `elimProp2 : ...` | — |

## 二、等价关系

| 术语 | 定义 | 代码 | 值 |
|---|---|---|---|
| **R₀** | C₀ 上等价关系：aug 判据 | `R₀ x y = aug x ≡ aug y` | 27-case aug-∂₁-zero |
| **R₁** | C₁ 上等价关系 | `R₁ x y = ...` | — |
| **R₂** | C₂ 上等价关系 | `R₂ x y = ...` | — |
| **aug** | 增广映射（链群→GF(3)） | `aug : C₀ → Trit` | — |

## 三、商群 H₀ = C₀/R₀ ≅ GF(3)

| 术语 | 定义 | 代码 | 值 |
|---|---|---|---|
| **H₀** | 0 阶同调群（HIT 商） | `H₀ = C₀ / R₀` | ≅ GF(3) |
| **H₁** | 1 阶同调群 | `H₁ = C₁ / R₁` | = 0（K₃ 实例） |
| **H₂** | 2 阶同调群 | `H₂ = C₂ / R₂` | = 0（K₃ 实例） |
| **f₀** | H₀ → Trit 同构 | `f₀ = elim (λ_→isSetTrit) aug (λ a b r → r)` | — |
| **h₀-inj** | f₀ 单射性（链级） | `h₀-inj x y h = eq/ x y h` | — |
| **h₀-injQ** | f₀ 单射性（商级，elimProp2） | `h₀-injQ = elimProp2 prop (λ x y h → eq/ x y h)` | — |
| **h₀-surj** | f₀ 满射性 | `h₀-surj c = h₀-fwd-bwd c` | — |

## 四、H₀ 群律（transport-of-structure）

| 术语 | 定义 | 代码 | 迁移路径 |
|---|---|---|---|
| **+H₀** | 商上加法 | `+H₀ q₁ q₂ = [h₀-bwd (f₀ q₁ ⊕ f₀ q₂)]` | transport-of-structure |
| **+H₀-respect** | +H₀ 良定义性 | `h₀-fwd-bwd ∙ cong₂ ∙ sym` | f₀ 常值性直给 |
| **+H₀-comm** | 交换律 | `h₀-injQ _ _ (f₀-comm _ _)` | h₀-injQ + f₀-comm |
| **+H₀-assoc** | 结合律 | `h₀-injQ _ _ (f₀-assoc _ _ _)` | h₀-injQ + f₀-assoc（5步∙链） |
| **+H₀-unit-l** | 左单位元 | `h₀-injQ _ _ (h₀-fwd+H₀ _ _ ∙ identityˡ-cub)` | ⊕-identityˡ-cub |
| **+H₀-unit-r** | 右单位元 | `h₀-injQ _ _ (h₀-fwd+H₀ _ _ ∙ identityʳ-cub)` | ⊕-identityʳ-cub |
| **+H₀-unit** | 单位元 | `[h₀-bwd T₀]` | — |

**H₀ 成群**：comm/assoc/unit-l/unit-r 四律全经 h₀-injQ + f₀ 迁移闭合。

## 五、Σ 商等价（FreeAbImEquiv）

| 术语 | 定义 | 代码 |
|---|---|---|
| **Im∂₁** | ∂₁ 的像谓词 | `Im∂₁ y = Σ C₁ (λ b → ∀ i → y i ≡ ∂₁ b i)` |
| **~₁** | 商等价 x ~ y := x − y ∈ im∂₁ | `~₁ x y = Im∂₁ (x ⊕ negᵠ y)` |
| **~₁-refl** | 自反性 | `zeroC₁ , λ i → neg-flip-r(x i)` |
| **~₁-sym** | 对称性 | negᶠ-b + neg-distrib + neg-self + comm |
| **~₁-trans** | 传递性 | cancel-pointwise + cong₂ + ∂₁-add |
| **cancel-pointwise** | 逐点相消 | `(x⊕neg y)⊕(y⊕neg z) ≡ x⊕neg z` |

## 六、cubical 技术术语

| 术语 | 含义 | 注意 |
|---|---|---|
| **transport 惯用法** | λ() 对 Path 相等不自动判空 → 用 transport | cubical 特有 |
| **cubical Dec** | Discrete 类型用 cubical 自有版本 | 非 stdlib Dec |
| **双 ≡ 不混** | PropEq ≡ vs cubical ≡——模块内选一种 | cubical 模块需本地 ⊕-comm-cub |
| **eq/ {R = ...}** | 显式传 R 消 meta | cubical SetQuotients |
| **elimProp2** | 二元消去（isPropΠ + squash/ 组合） | 一次通过关键 |
| **未来态锚定** | 类型声明 ≡ 右端锚定最终目标形态 | 非 中间态（f₀-assoc 教训） |

## 七、六件闭合清单

| 件 | 内容 | 回执 |
|---|---|---|
| S1a fab-laws | FAb 群律 + ∂₁ 线性三条 | SunyiBase |
| S1a im-equiv | Σ 商等价 isEquivRel | FreeAbImEquiv |
| generic-hit | HIT 商 + f₀ 同构 + +H₀ 交换律 + 归零 | FreeAbQuotient |
| homology-quotient | 实例层 aug-setoid | FreeAbHomologyGroup |
| plusH0 | +H₀ transport + 交换律 | FreeAbQuotient |
| injQ | 商层单射 + 结合律/单位元 | FreeAbQuotient |
