> **正定性检查** · `positivity-checking`
>
>  occurrence 分析确保数据类型严格正定，禁止非正定出现。
>
> 🔗 原文：<https://agda.readthedocs.io/en/latest/language/positivity-checking.html>
>
> **本项目相关性**：HIT 与归纳类型定义必须通过正定性检查；纤维丛自引用结构需注意。

---
# Positivity Checking[](#positivity-checking "Link to this heading")

Note

This is a stub.

## Occurrence analysis[](#occurrence-analysis "Link to this heading")

By default Agda analyses how functions use their arguments. For instance, Agda can tell that `D` in the following code is strictly positive, because `Vec` uses its `Set` argument in a strictly positive way:

data _×_ (A B : Set) : Set where
  _,_ : A → B → A × B

Vec : Set → Nat → Set
Vec A zero    = ⊤
Vec A (suc n) = A × Vec A n

data D : Set where
  c : ∀ n → Vec D n → D

However, this analysis can be slow, especially for big mutual blocks. It can be turned off with the [\--no-occurrence-analysis](https://agda.readthedocs.io/en/latest/tools/command-line-options.html#cmdoption-occurrence-analysis) flag.

The analysis is also used to detect unused function arguments. For instance, Agda by default notices that the last argument of `F` in the following code is unused, and accepts the use of reflexivity:

F : Bool → Set → Set
F true  _ = Bool
F false _ = ⊤

_ : {b : Bool} → F b Bool ≡ F b ⊤
_ = refl

An alternative to the occurrence analysis is to use [polarities](polarity.md#polarity):

data _×_ (@++ A B : Set) : Set where
  _,_ : A → B → A × B

Vec : @++ Set → Nat → Set
Vec A zero    = ⊤
Vec A (suc n) = A × Vec A n

data D : Set where
  c : ∀ n → Vec D n → D

F : Bool → @unused Set → Set
F true  _ = Bool
F false _ = ⊤

_ : {b : Bool} → F b Bool ≡ F b ⊤
_ = refl

### The `NO_POSITIVITY_CHECK` pragma[](#the-no-positivity-check-pragma "Link to this heading")

The pragma switches off the positivity checker for data/record definitions and mutual blocks. This pragma was added in Agda 2.5.1

The pragma must precede a data/record definition or a mutual block. The pragma cannot be used in [\--safe](https://agda.readthedocs.io/en/latest/tools/command-line-options.html#cmdoption-safe) mode.

Examples:

* Skipping a single data definition:  
{-# NO_POSITIVITY_CHECK #-}  
data D : Set where  
  lam : (D → D) → D
* Skipping a single record definition:  
{-# NO_POSITIVITY_CHECK #-}  
record U : Set where  
  inductive; no-eta-equality  
  field ap : U → U
* Skipping an old-style mutual block. Somewhere within a mutual block before a data/record definition:  
mutual  
  data D : Set where  
    lam : (D → D) → D  
  {-# NO_POSITIVITY_CHECK #-}  
  record U : Set where  
    inductive; no-eta-equality  
    field ap : U → U
* Skipping an old-style mutual block. Before the `mutual` keyword:  
{-# NO_POSITIVITY_CHECK #-}  
mutual  
  data D : Set where  
    lam : (D → D) → D  
  record U : Set where  
    inductive; no-eta-equality  
    field ap : U → U
* Skipping a new-style mutual block. Anywhere before the declaration or the definition of a data/record in the block:  
record U : Set  
data D   : Set  
record U where  
  inductive; no-eta-equality  
  field ap : U → U  
{-# NO_POSITIVITY_CHECK #-}  
data D where  
  lam : (D → D) → D

### POLARITY pragmas[](#polarity-pragmas "Link to this heading")

Polarity pragmas can be attached to postulates. The polarities express how the postulate’s arguments are used. The following polarities are available:

* `_`: Unused.
* `++`: Strictly positive.
* `+`: Positive.
* `-`: Negative.
* `*`: Unknown/mixed.

Polarity pragmas have the form `{-# POLARITY name <zero or more polarities> #-}`, and can be given wherever fixity declarations can be given. The listed polarities apply to the given postulate’s arguments (explicit/implicit/instance), from left to right. Polarities currently cannot be given for module parameters. If the postulate takes n arguments (excluding module parameters), then the number of polarities given must be between 0 and n (inclusive).

Polarity pragmas make it possible to use postulated type formers in recursive types in the following way:

postulate
  ∥_∥ : Set → Set

{-# POLARITY ∥_∥ ++ #-}

data D : Set where
  c : ∥ D ∥ → D

Note that one can use postulates that may seem benign, together with polarity pragmas, to prove that the empty type is inhabited:

postulate
  _⇒_    : Set → Set → Set
  lambda : {A B : Set} → (A → B) → A ⇒ B
  apply  : {A B : Set} → A ⇒ B → A → B

{-# POLARITY _⇒_ ++ #-}

data ⊥ : Set where

data D : Set where
  c : D ⇒ ⊥ → D

not-inhabited : D → ⊥
not-inhabited (c f) = apply f (c f)

d : D
d = c (lambda not-inhabited)

bad : ⊥
bad = not-inhabited d

Polarity pragmas are not allowed in safe mode.