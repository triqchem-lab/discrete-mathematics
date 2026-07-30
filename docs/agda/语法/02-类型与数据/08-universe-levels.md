> **宇宙层级** · `universe-levels`
>
> Level 类型与运算（ℓ⊔ℓ/ℓ+1）、intrinsic 属性、forall 记法、Setω、相关 pragma。
>
> 🔗 原文：<https://agda.readthedocs.io/en/latest/language/universe-levels.html>
>
> **本项目相关性**：多态证明库的基础；GF(3) 运算与 HoTT 路径跨层级时需正确管理 Level。

---
# Universe Levels[](#universe-levels "Link to this heading")

Agda’s type system includes an infinite hierarchy of universes `Setᵢ : Setᵢ₊₁`. This hierarchy enables quantification over arbitrary types without running into the inconsistency that follows from `Set : Set`. These universes are further detailed on the page on [Agda’s sort system](sort-system.md#sort-system).

However, when working with this hierarchy it can quickly get tiresome to repeat the same definition at different universe levels. For example, we might be forced to define new datatypes `data List (A : Set) : Set`, `data List₁ (A : Set₁) : Set₁`, etc. Also every function on lists (such as `append`) must be re-defined, and every theorem about such functions must be re-proved, for every possible level.

The solution to this problem is universe polymorphism. Agda provides a special primitive type `Level`, whose elements are possible levels of universes. In fact, the notation for the `n` th universe, `Setₙ`, is just an abbreviation for `Set n`, where `n : Level`is a level. We can use this to write a polymorphic `List` operator that works at any level. The library `Agda.Primitive` must be imported to access the `Level` type. The definition then looks like this:

open import Agda.Primitive

data List {n : Level} (A : Set n) : Set n where
  []   : List A
  _::_ : A → List A → List A

This new operator works at all levels; for example, we have

List Nat : Set
List Set : Set₁
List Set₁ : Set₂

## Level arithmetic[](#level-arithmetic "Link to this heading")

Even though we don’t have the number of levels specified, we know that there is a lowest level `lzero`, and for each level `n`, there exists some higher level `lsuc n`; therefore, the set of levels is infinite. In addition, we can also take the least upper bound `n ⊔ m` of two levels. In summary, the following (and only the following) operations on levels are provided:

lzero : Level
lsuc  : (n : Level) → Level
_⊔_   : (n m : Level) → Level

This is sufficient for most purposes; for example, we can define the Cartesian product of two types of arbitrary (and not necessarily equal) levels like this:

data _×_ {n m : Level} (A : Set n) (B : Set m) : Set (n ⊔ m) where
   _,_ : A → B → A × B

With this definition, we have, for example:

Nat × Nat : Set
Nat x Set : Set₁
Set × Set : Set₁

## Intrinsic level properties[](#intrinsic-level-properties "Link to this heading")

Levels and their associated operations have some properties which are internally and automatically solved by the compiler. This means that we can replace some expressions with others, without worrying about the expressions for their corresponding levels matching exactly.

For example, we can write:

_ : {F : (l : Level) → Set l} {l1 l2 : Level} → F (l1 ⊔ l2) → F (l2 ⊔ l1)
_ = λ x → x

and Agda does the conversion from `F (l1 ⊔ l2)` to `F (l2 ⊔ l1)` automatically.

Here is a list of the level properties:

* Idempotence: `a ⊔ a` is the same as `a`.
* Associativity: `(a ⊔ b) ⊔ c` is the same as `a ⊔ (b ⊔ c)`.
* Commutativity: `a ⊔ b` is the same as `b ⊔ a`.
* Distributivity of `lsuc` over `⊔`: `lsuc (a ⊔ b)` is the same as `lsuc a ⊔ lsuc b`.
* Neutrality of `lzero`: `a ⊔ lzero` is the same as `a`.
* Subsumption: `a ⊔ lsuc a` is the same as `lsuc a`. Notably, this also holds for arbitrarily many `lsuc` usages: `a ⊔ lsuc (lsuc a)` is also the same as `lsuc (lsuc a)`.

## `forall` notation[](#forall-notation "Link to this heading")

From the fact that we write `Set n`, it can always be inferred that `n` is a level. Therefore, when defining universe-polymorphic functions, it is common to use the ∀ (or forall) notation. For example, the type of the universe-polymorphic `map` operator on lists can be written

map : ∀ {n m} {A : Set n} {B : Set m} → (A → B) → List A → List B

which is equivalent to

map : {n m : Level} {A : Set n} {B : Set m} → (A → B) → List A → List B

## Expressions of sort `Setω`[](#expressions-of-sort-set "Link to this heading")

In a sense, universes were introduced to ensure that every Agda expression has a type, including expressions such as `Set`, `Set₁`, etc. However, the introduction of universe polymorphism inevitably breaks this property again, by creating some new terms that have no type. Consider the polymorphic singleton set `Unit n : Setₙ`, defined by

data Unit (n : Level) : Set n where
  <> : Unit n

It is well-typed, and has type

Unit : (n : Level) → Set n

However, the type `(n : Level) → Set n`, which is a valid Agda expression, does not belong to any universe in the `Set` hierarchy. Indeed, the expression denotes a function mapping levels to sorts, so if it had a type, it should be something like `Level → Sort`, where `Sort` is the collection of all sorts. But if Agda were to support a sort `Sort` of all sorts, it would be a sort itself, so in particular we would have `Sort : Sort`. Just like `Type : Type`, this would leads to circularity and inconsistency.

Instead, Agda introduces a new sort `Setω` that stands above all sorts `Set ℓ`, but is not itself part of the hierarchy. For example, Agda assigns the expression `(n : Level) → Set n` to be of type `Setω`.

`Setω` is itself the first step in another infinite hierarchy `Setωᵢ : Setωᵢ₊₁`. However, this hierarchy does not support universe polymorphism, i.e. there are no sorts `Setω ℓ` for `ℓ : Level`. Allowing this would require a new universe `Set2ω`, which would then naturally lead to `Set2ω₁`, and so on. Disallowing universe polymorphism for `Setωᵢ` avoids the need for such even larger sorts. This is an intentional design decision.

## Pragmas and options[](#pragmas-and-options "Link to this heading")

* The option [\--type-in-type](https://agda.readthedocs.io/en/latest/tools/command-line-options.html#cmdoption-type-in-type) disables the checking of universe level consistency for the whole file.
* The option [\--omega-in-omega](https://agda.readthedocs.io/en/latest/tools/command-line-options.html#cmdoption-omega-in-omega) enables the typing rule `Setω : Setω` (thus making Agda inconsistent) but otherwise leaves universe checks intact.
* The option [\--level-universe](https://agda.readthedocs.io/en/latest/tools/command-line-options.html#cmdoption-level-universe) makes `Level` live in its own universe `LevelUniv` and disallows having levels depend on terms that are not levels themselves. When this option is turned off, `LevelUniv` still exists, but reduces to `Set`.  
Note: While compatible with the [\--cubical](https://agda.readthedocs.io/en/latest/tools/command-line-options.html#cmdoption-cubical) option, this option is currently not compatible with cubical builtin files, and an error will be raised when trying to import them in a file using [\--level-universe](https://agda.readthedocs.io/en/latest/tools/command-line-options.html#cmdoption-level-universe).  
{-# OPTIONS --level-universe #-}  
open import Agda.Primitive  
open import Agda.Builtin.Nat  
toLevel : Nat → Level  
toLevel _ = lzero  
funSort Set LevelUniv is not a valid sort  
when checking that the expression Nat → Level is a type
* The pragma `{-# NO_UNIVERSE_CHECK #-}` can be put in front of a data or record type to disable universe consistency checking locally. Example:  
{-# NO_UNIVERSE_CHECK #-}  
data U : Set where  
  el : Set → U  
This pragma applies only to the check that the universe level of the type of each constructor argument is less than or equal to the universe level of the datatype, not to any other checks.  
Added in version 2.6.0.

The options [\--type-in-type](https://agda.readthedocs.io/en/latest/tools/command-line-options.html#cmdoption-type-in-type) and [\--omega-in-omega](https://agda.readthedocs.io/en/latest/tools/command-line-options.html#cmdoption-omega-in-omega) and the pragma `{-# NO_UNIVERSE_CHECK #-}` cannot be used with –safe.