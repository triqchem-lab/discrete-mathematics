> **Prop 命题宇宙** · `prop`
>
> 命题宇宙 Prop、predicative 层级、propositional squash 类型 ∥_∥、使用限制。
>
> 🔗 原文：<https://agda.readthedocs.io/en/latest/language/prop.html>
>
> **本项目相关性**：命题截断 ∥_∥₁/∥_∥₂ 在 HoTT 证明中表达「存在性」；注意本项目偏好高维全息，慎用过度截断。

---
# Prop[](#prop "Link to this heading")

`Prop` is Agda’s built-in sort of _definitionally proof-irrelevant propositions_. It is similar to the sort `Set`, but all elements of a type in `Prop` are considered to be (definitionally) equal.

The implementation of `Prop` is based on the POPL 2019 paper [Definitional Proof-Irrelevance without K](https://hal.inria.fr/hal-01859964/) by Gaëtan Gilbert, Jesper Cockx, Matthieu Sozeau, and Nicolas Tabareau.

This is an experimental extension of Agda guarded by option [\--prop](https://agda.readthedocs.io/en/latest/tools/command-line-options.html#cmdoption-prop).

## Usage[](#usage "Link to this heading")

Just as for `Set`, we can define new types in `Prop`’s as data or record types:

data ⊥ : Prop where

record ⊤ : Prop where
  constructor tt

When defining a function from a data type in `Prop` to a type in `Set`, pattern matching is restricted to the [absurd pattern](function-definitions.md#absurd-patterns) `()`:

absurd : (A : Set) → ⊥ → A
absurd A ()

Unlike for `Set`, all elements of a type in `Prop` are definitionally equal. This implies all applications of `absurd` are the same:

only-one-absurdity : {A : Set} → (p q : ⊥) → absurd A p ≡ absurd A q
only-one-absurdity p q = refl

Since pattern matching on datatypes in `Prop` is limited, it is recommended to define types in `Prop` as recursive functions rather than inductive datatypes. For example, the relation `_≤_` on natural numbers can be defined as follows:

_≤_ : Nat → Nat → Prop
zero  ≤ y     = ⊤
suc x ≤ zero  = ⊥
suc x ≤ suc y = x ≤ y

The induction principle for `_≤_` can then be defined by matching on the arguments of type `Nat`:

module _ (P : (m n : Nat) → Set)
  (pzy : (y : Nat) → P zero y)
  (pss : (x y : Nat) → P x y → P (suc x) (suc y)) where

  ≤-ind : (m n : Nat) → m ≤ n → P m n
  ≤-ind zero    y       pf = pzy y
  ≤-ind (suc x) (suc y) pf = pss x y (≤-ind x y pf)
  ≤-ind (suc _) zero    ()

Note that while it is also possible to define `_≤_` as a datatype in `Prop`, it is hard to use that version because of the limitations to matching.

When defining a record type in `Set`, the types of the fields can be both in `Set` and `Prop`. For example:

record Fin (n : Nat) : Set where
  constructor _[_]
  field
    ⟦_⟧   : Nat
    proof : suc ⟦_⟧ ≤ n
open Fin

Fin-≡ : ∀ {n} (x y : Fin n) → ⟦ x ⟧ ≡ ⟦ y ⟧ → x ≡ y
Fin-≡ x y refl = refl

## The predicative hierarchy of `Prop`[](#the-predicative-hierarchy-of-prop "Link to this heading")

Just as for `Set`, Agda has a predicative hierarchy of sorts `Prop₀` (= `Prop`), `Prop₁`, `Prop₂`, …, `Propω₀` (= `Propω`), `Propω₁`, `Propω₂`, …, where `Prop₀ : Set₁`, `Prop₁ : Set₂`, `Prop₂ : Set₃`, …, `Propω₀ : Setω₁`, `Propω₁ : Setω₂`, `Propω₂ : Setω₃`, etc. Like `Set`, `Prop` also supports universe polymorphism (see [universe levels](universe-levels.md#universe-levels)), so for each `ℓ : Level` we have the sort `Prop ℓ`. For example:

True : ∀ {ℓ} → Prop (lsuc ℓ)
True {ℓ} = ∀ (P : Prop ℓ) → P → P

Note that `∀ {ℓ} → Prop (lsuc ℓ)` (and likewise any `∀ {ℓ} → Prop (t ℓ)`) lives in `Setω`, not `Propω`.

## The propositional squash type[](#the-propositional-squash-type "Link to this heading")

When defining a datatype in `Prop ℓ`, it is allowed to have constructors that take arguments in `Set ℓ′` for any `ℓ′ ≤ ℓ`. For example, this allows us to define the propositional squash type and its eliminator:

data Squash {ℓ} (A : Set ℓ) : Prop ℓ where
  squash : A → Squash A

squash-elim : ∀ {ℓ₁ ℓ₂} (A : Set ℓ₁) (P : Prop ℓ₂) → (A → P) → Squash A → P
squash-elim A P f (squash x) = f x

This type allows us to simulate Agda’s existing irrelevant arguments (see [irrelevance](irrelevance.md#irrelevance)) by replacing `.A` with `Squash A`.

## Limitations[](#limitations "Link to this heading")

It is possible to define an equality type in Prop as follows:

data _≐_ {ℓ} {A : Set ℓ} (x : A) : A → Prop ℓ where
  refl : x ≐ x

However, the corresponding eliminator cannot be defined because of the limitations on pattern matching. As a consequence, this equality type is only useful for refuting impossible equations:

0≢1 : 0 ≐ 1 → ⊥
0≢1 ()