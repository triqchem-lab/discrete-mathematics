> **Flat 模态** · `flat`
>
> @♭（flat）模态与 #（sharp）模态，以及 @♭ 上的模式匹配，用于控时不假设（guarded/时态）分解。
>
> 🔗 原文：<https://agda.readthedocs.io/en/latest/language/flat.html>
>
> **本项目相关性**：高维纤维丛分层（本体/投影）可用模态隔离，避免不同层级类型混用——契合范畴分离原则。

---
# Flat Modality[](#flat-modality "Link to this heading")

The flat/crisp attribute `@♭/@flat` is an idempotent comonadic modality modeled after [Spatial Type Theory](https://arxiv.org/abs/1509.07584/) and [Crisp Type Theory](https://arxiv.org/abs/1801.07664/). It is similar to a necessity modality.

This attribute is enabled using the infective flag [\--cohesion](https://agda.readthedocs.io/en/latest/tools/command-line-options.html#cmdoption-cohesion).

We can define `♭ A` as a type for any `(@♭ A : Set l)` via an inductive definition:

data ♭ {@♭ l : Level} (@♭ A : Set l) : Set l where
  con : (@♭ x : A) → ♭ A

counit : {@♭ l : Level} {@♭ A : Set l} → ♭ A → A
counit (con x) = x

When trying to provide a `@♭` arguments only other `@♭`variables will be available, the others will be marked as `@⊤` in the context. For example the following will not typecheck:

unit : {@♭ l : Level} {@♭ A : Set l} → A → ♭ A
unit x = con x

## Pattern Matching on `@♭`[](#pattern-matching-on "Link to this heading")

By default matching on arguments marked with `@♭` is disallowed, but it can be enabled using the option [\--flat-split](https://agda.readthedocs.io/en/latest/tools/command-line-options.html#cmdoption-flat-split). When matching on a `@♭` argument the flat status gets propagated to the arguments of the constructor

data _⊎_ (A B : Set) : Set where
  inl : A → A ⊎ B
  inr : B → A ⊎ B

flat-sum : {@♭ A B : Set} → (@♭ x : A ⊎ B) → ♭ A ⊎ ♭ B
flat-sum (inl x) = inl (con x)
flat-sum (inr x) = inr (con x)

When refining `@♭` variables the equality also needs to be provided as `@♭`

flat-subst : {@♭ A : Set} {P : A → Set} (@♭ x y : A) (@♭ eq : x ≡ y) → P x → P y
flat-subst x .x refl p = p

if we simply had `(eq : x ≡ y)` the code would be rejected.

Note that in Cubical Agda functions that match on an argument marked with `@♭` trigger the `UnsupportedIndexedMatch` warning (see [Indexed inductive types](cubical.md#indexed-inductive-types)), and the code might not compute properly.

## The Sharp Modality[](#the-sharp-modality "Link to this heading")

The [\--cohesion](https://agda.readthedocs.io/en/latest/tools/command-line-options.html#cmdoption-cohesion) flag also enables the sharp modality as presented in [Cohesive Homotopy Type Theory](https://arxiv.org/abs/1509.07584). The annotation `@♯/@sharp` is an idempotent monadic modality, which is right adjoint to the `@♭` modality.

We can define `♯` as the following record type:

record ♯ {l} (@♯ A : Set l) : Set l where
  constructor conSharp
  field
    @♯ ε : A

open ♯

_ : ∀ {@♭ l} {@♭ A : Set l} → @♭ ♯ A → A
_ = ε

When providing a `@♯` argument, every non `@⊤` variable becomes `@♭` annotated. As a record, we can define elements of `♯` by copattern matching. After copattern matching with `ε`, all variables in the context become crisp, for example, in the following, we can use `a` in the constuctor of `♭`.

unit : ∀ {@♭ A : Set} → A → ♯ (♭ A)
unit a .ε = con a