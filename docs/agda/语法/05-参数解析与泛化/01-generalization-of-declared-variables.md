> **声明变量泛化** · `generalization-of-declared-variables`
>
> variable 块声明的变量自动泛化为顶层签名参数，含嵌套泛化、实例/无关变量、导入导出规则。
>
> 🔗 原文：<https://agda.readthedocs.io/en/latest/language/generalization-of-declared-variables.html>
>
> **本项目相关性**：减少 Sovereign 库中重复的 telescope 书写；注意泛化变量不要破坏范畴分离（如把耦合域变量泄漏到根数学）。

---
# Generalization of Declared Variables[](#generalization-of-declared-variables "Link to this heading")

## [Overview](#id3)[](#overview "Link to this heading")

Since version 2.6.0, Agda supports implicit generalization over variables in types. Variables to be generalized over must be declared with their types in a `variable`block. For example:

variable
  ℓ : Level
  n m : Nat

data Vec (A : Set ℓ) : Nat → Set ℓ where
  []  : Vec A 0
  _∷_ : A → Vec A n → Vec A (suc n)

Here the parameter `ℓ` and the `n` in the type of `_∷_` are not bound explicitly, but since they are declared as generalizable variables, bindings for them are inserted automatically. The level `ℓ` is added as a parameter to the datatype and `n` is added as an argument to `_∷_`. The resulting declaration is

data Vec {ℓ : Level} (A : Set ℓ) : Nat → Set ℓ where
  []  : Vec A 0
  _∷_ : {n : Nat} → A → Vec A n → Vec A (suc n)

See [Placement of generalized bindings](#placement-of-generalized-bindings) below for more details on where bindings are inserted.

Variables are generalized in top-level type signatures, [module](module-system.md#module-system) [telescopes](telescopes.md#telescopes), and [record](record-types.md#record-types)and [datatype](data-types.md#data-types) parameter telescopes.

Issues related to this feature are marked with [generalize](https://github.com/agda/agda/labels/generalize) in the issue tracker.

## [Nested generalization](#id4)[](#nested-generalization "Link to this heading")

When generalizing a variable, any generalizable variables in its type are also generalized over. For instance, you can declare `A` to be a type at some level `ℓ` as

variable
  A : Set ℓ

Now if `A` is mentioned in a type, the level `ℓ` will also be generalized over:

-- id : {A.ℓ : Level} {A : Set ℓ} → A → A
id : A → A
id x = x

The nesting can be arbitrarily deep, so

variable
  x : A

refl′ : x ≡ x
refl′ = refl

expands to

refl′ : {x.A.ℓ : Level} {x.A : Set x.A.ℓ} {x : x.A} → x ≡ x

See [Naming of nested variables](#id2) below for how the names are chosen.

Nested variables are not necessarily generalized over. In this example, if the universe level of `A` is fixed there is nothing to generalize:

postulate
  -- pure : {A : Set} {F : Set → Set} → A → F A
  pure : {F : Set → Set} → A → F A

See [Generalization over unsolved metavariables](#generalization-over-unsolved-metavariables) for more details.

Note

Nested generalized variables are local to each variable, so if you declare

variable
  B : Set ℓ

then `A` and `B` can still be generalized at different levels. For instance,

-- _$_ : {A.ℓ : Level} {A : Set A.ℓ} {B.ℓ : Level} {B : Set B.ℓ} → (A → B) → A → B
_$_ : (A → B) → A → B
f $ x = f x

### Generalization over unsolved metavariables[](#generalization-over-unsolved-metavariables "Link to this heading")

Generalization over nested variables is implemented by creating a metavariable for each nested variable and generalize over any such meta that is still unsolved after type checking. This is what makes the `pure` example from the previous section work: the metavariable created for `ℓ` is solved to level 0 and is thus not generalized over.

A typical case where this happens is when you have dependencies between different nested variables. For instance:

postulate
  Con : Set

variable
  Γ Δ Θ : Con

postulate
  Sub : Con → Con → Set

  idS : Sub Γ Γ
  _∘_ : Sub Γ Δ → Sub Δ Θ → Sub Γ Θ

variable
  δ σ γ : Sub Γ Δ

postulate
  assoc : δ ∘ (σ ∘ γ) ≡ (δ ∘ σ) ∘ γ

In the type of `assoc` each substitution gets two nested variable metas for their contexts, but the type of `_∘_` requires the contexts of its arguments to match up, so some of these metavariables are solved. The resulting type is

assoc : {δ.Γ δ.Δ : Con} {δ : Sub δ.Γ δ.Δ} {σ.Δ : Con} {σ : Sub δ.Δ σ.Δ}
        {γ.Δ : Con} {γ : Sub σ.Δ γ.Δ} → (δ ∘ (σ ∘ γ)) ≡ ((δ ∘ σ) ∘ γ)

where we can see from the names that `σ.Γ` was unified with `δ.Δ` and `γ.Γ` with `σ.Δ`. In general, when unifying two metavariables the “youngest” one is eliminated which is why `δ.Δ` and `σ.Δ` are the ones that remain in the type.

If a metavariable for a nested generalizable variable is partially solved, the left-over metas are generalized over. For instance,

variable
  xs : Vec A n

head : Vec A (suc n) → A
head (x ∷ _) = x

-- lemma : {xs.n.1 : Nat} {xs : Vec Nat (suc xs.n.1)} → head xs ≡ 1 → (0 < sum xs) ≡ true
lemma : head xs ≡ 1 → (0 < sum xs) ≡ true

In the type of `lemma` a metavariable is created for the length of `xs`, which the application `head xs` refines to `suc _n`, for some new metavariable `_n`. Since there are no further constraints on `_n`, it’s generalized over, creating the type given in the comment. See [Naming of nested variables](#naming-of-nested-variables) below for how the name `xs.n.1` is chosen.

Note

Only metavariables originating from nested variables are generalized over. An exception to this is in `variable` blocks where all unsolved metas are turned into nested variables. This means writing

variable
  A : Set _

is equivalent to `A : Set ℓ` up to naming of the nested variable (see below).

### Naming of nested variables[](#naming-of-nested-variables "Link to this heading")

The general naming scheme for nested generalized variables is `parentVar.nestedVar`. So, in the case of the identity function `id : A → A` expanding to

id : {A.ℓ : Level} {A : Set ℓ} → A → A

the name of the level variable is `A.ℓ` since the name of the nested variable is `ℓ` and its parent is the named variable `A`. For multiple levels of nesting the parent can be another nested variable as in the `refl′` case above

refl′ : {x.A.ℓ : Level} {x.A : Set x.A.ℓ} {x : x.A} → x ≡ x

If a nested generalizable variable is solved with a term containing further metas, these are generalized over as explained in the `lemma` example above. The names of the new variables are of the form `parentName.i` where `parentName` is the name of the solved variable and `i` numbers the metas, starting from 1, in the order they appear in the solution.

If a variable comes from a free unsolved metavariable in a `variable` block (see [this note](#note-free-metas)), its name is chosen as follows:

* If it is a labelled argument to a function, the label is used as the name,
* otherwise the name is its left-to-right index (starting at 1) in the list of unnamed variables in the type.

It is then given a hierarchical name based on the named variable whose type it occurs in. For example,

postulate
  V : (A : Set) → Nat → Set
  P : V A n → Set

variable
  v : V _ _

postulate
  thm : P v

Here there are two unnamed variables in the type of `v`, namely the two arguments to `V`. The first argument has the label `A` in the definition of `V`, so this variable gets the name `v.A`. The second argument has no label and thus gets the name `v.2` since it is the second unnamed variable in the type of `v`.

If the variable comes from a partially instantiated nested variable the name of the metavariable is used unqualified.

Note

Currently it is not allowed to use hierarchical names when giving parameters to functions, see [Issue #3208](https://github.com/agda/agda/issues/3280).

## [Placement of generalized bindings](#id5)[](#placement-of-generalized-bindings "Link to this heading")

The following rules are used to place generalized variables:

* Generalized variables are placed at the front of the type signature or [telescope](telescopes.md#telescopes).
* Type signatures appearing inside other type signatures, for instance in [let bindings](let-and-where.md#let-expressions) or dependent function arguments are not generalized. Instead any generalizable variables in such types are generalized over in the parent signature.
* Variables mentioned earlier are placed before variables mentioned later, where nested variables count as being mentioned together with their parent.

Note

This means that an implicitly quantified variable cannot depend on an explicitly quantified one. See [Issue #3352](https://github.com/agda/agda/issues/3352) for the feature request to lift this restriction.

### Indexed datatypes[](#indexed-datatypes "Link to this heading")

When generalizing datatype parameters and indices a variable is turned into an index if it is only mentioned in indices and into a parameter otherwise. For instance,

data All (P : A → Set) : Vec A n → Set where
  []  : All P []
  _∷_ : P x → All P xs → All P (x ∷ xs)

Here `A` is generalized as a parameter and `n` as an index. That is, the resulting signature is

data All {A : Set} (P : A → Set) : {n : Nat} → Vec A n → Set where

## [Instance and irrelevant variables](#id6)[](#instance-and-irrelevant-variables "Link to this heading")

Generalized variables are introduced as implicit arguments by default, but this can be changed to [instance arguments](instance-arguments.md#instance-arguments) or [irrelevant arguments](irrelevance.md#irrelevance) by annotating the declaration of the variable

record Eq (A : Set) : Set where
  field eq : A → A → Bool

variable
  {{EqA}} : Eq A   -- generalized as an instance argument
  .ignore : A      -- generalized as an irrelevant (implicit) argument

Variables are never generalized as explicit arguments.

## [Importing and exporting variables](#id7)[](#importing-and-exporting-variables "Link to this heading")

Generalizable variables are treated in the same way as other declared symbols (functions, datatypes, etc) and use the same mechanisms for importing and exporting between modules. This means that unless marked `private` they are exported from a module.

## [Interaction](#id8)[](#interaction "Link to this heading")

When developing types interactively, generalizable variables can be used in holes if they have already been generalized, but it is not possible to introduce newgeneralizations interactively. For instance,

works : (A → B) → Vec A n → Vec B {!n!}
fails : (A → B) → Vec A {!n!} → Vec B {!n!}

In `works` you can give `n` in the hole, since a binding for `n` has been introduced by its occurrence in the argument vector. In `fails` on the other hand, there is no reference to `n` so neither hole can be filled interactively.

## [Modalities](#id9)[](#modalities "Link to this heading")

One can give a modality when declaring a generalizable variable:

variable
  @0 o : Nat

In the generalization process generalizable variables get the modality that they are declared with, whereas other variables always get the default modality.