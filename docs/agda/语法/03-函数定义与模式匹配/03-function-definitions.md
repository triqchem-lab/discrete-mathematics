> **函数定义** · `function-definitions`
>
> 函数签名与子句定义、特殊模式（absurd/dot/record）、case tree 展开机制。
>
> 🔗 原文：<https://agda.readthedocs.io/en/latest/language/function-definitions.html>
>
> **本项目相关性**：损益链、LCM 运算、Trit GF(3) 加法乘法均以函数定义；理解 case tree 有助于诊断归约性能。

---
# Function Definitions[](#function-definitions "Link to this heading")

## Introduction[](#introduction "Link to this heading")

A function is defined by first declaring its type followed by a number of equations called _clauses_. Each clause consists of the function being defined applied to a number of _patterns_, followed by `=` and a term called the _right-hand side_. For example:

not : Bool → Bool
not true  = false
not false = true

Functions are allowed to call themselves recursively, for example:

twice : Nat → Nat
twice zero    = zero
twice (suc n) = suc (suc (twice n))

## General form[](#general-form "Link to this heading")

The general form for defining a function is

f : (x₁ : A₁) → … → (xₙ : Aₙ) → B
f p₁ … pₙ = d
…
f q₁ … qₙ = e

where `f` is a new identifier, `pᵢ` and `qᵢ` are patterns of type `Aᵢ`, and `d` and `e` are expressions.

The declaration above gives the identifier `f` the type `(x₁ : A₁) → … → (xₙ : Aₙ) → B` and `f` is defined by the defining equations. Patterns are matched from top to bottom, i.e., the first pattern that matches the actual parameters is the one that is used.

By default, Agda checks the following properties of a function definition:

* The patterns in the left-hand side of each clause should consist only of constructors and variables.
* No variable should occur more than once on the left-hand side of a single clause.
* The patterns of all clauses should together cover all possible inputs of the function, see [Coverage Checking](coverage-checking.md#coverage-checking).
* The function should be terminating on all possible inputs, see [Termination Checking](termination-checking.md#termination-checking).

## Special patterns[](#special-patterns "Link to this heading")

In addition to constructors consisting of constructors and variables, Agda supports two special kinds of patterns: dot patterns and absurd patterns.

### Dot patterns[](#dot-patterns "Link to this heading")

A dot pattern (also called _inaccessible pattern_) can be used when the only type-correct value of the argument is determined by the patterns given for the other arguments. A dot pattern is not matched against to determine the result of a function call. Instead it serves as checked documentation of the only possible value at the respective position, as determined by the other patterns. The syntax for a dot pattern is `.t`.

As an example, consider the datatype `Square` defined as follows

data Square : Nat → Set where
  sq : (m : Nat) → Square (m * m)

Suppose we want to define a function `root : (n : Nat) → Square n → Nat` that takes as its arguments a number `n` and a proof that it is a square, and returns the square root of that number. We can do so as follows:

root : (n : Nat) → Square n → Nat
root .(m * m) (sq m) = m

Notice that by matching on the argument of type `Square n` with the constructor `sq : (m : Nat) → Square (m * m)`, `n` is forced to be equal to `m * m`.

In general, when matching on an argument of type `D i₁ … iₙ` with a constructor `c : (x₁ : A₁) → … → (xₘ : Aₘ) → D j₁ … jₙ`, Agda will attempt to unify `i₁ … iₙ` with `j₁ … jₙ`. When the unification algorithm instantiates a variable `x` with value `t`, the corresponding argument of the function can be replaced by a dot pattern `.t`.

Using a dot pattern can help readability, but is not necessary; a dot pattern can always be replaced by an underscore or a fresh pattern variable without changing the function definition. The following are also legal definitions of `root`:

Since Agda 2.4.2.4:

root₁ : (n : Nat) → Square n → Nat
root₁ _ (sq m) = m

Since Agda 2.5.2:

root₂ : (n : Nat) → Square n → Nat
root₂ n (sq m) = m

In the case of `root₂`, `n` evaluates to `m * m` in the body of the function and is thus equivalent to

root₃ : (n : Nat) → Square n → Nat
root₃ _ (sq m) = let n = m * m in m

A dot pattern need not be a valid ordinary pattern at all (as in the case of `m * m` above). If it happens to be a valid ordinary pattern, then sometimes the dot can be removed without changing the function definition.

Other times, removing the dot yields a valid definition but with different definitional behavior. For instance, in the following definition:

data Fin : Nat → Set where
  fzero : {n : Nat} → Fin (suc n)
  fsuc : {n : Nat} → Fin n → Fin (suc n)

foo : (n : Nat) (k : Fin n) → Nat
foo .(suc zero) (fzero {zero})     = zero
foo .(suc (suc n)) (fzero {suc n}) = zero
foo .(suc _) (fsuc k)              = zero

removing the dots in `foo` changes the case tree so that it splits on the first argument first. This results in the third equation not holding definitionally (and thus the definition being flagged under the option [–exact-split](#catchall-pragma)).

### Absurd patterns[](#absurd-patterns "Link to this heading")

Absurd patterns can be used when none of the constructors for a particular argument would be valid. The syntax for an absurd pattern is `()`.

As an example, if we have a datatype `Even` defined as follows

data Even : Nat → Set where
  even-zero  : Even zero
  even-plus2 : {n : Nat} → Even n → Even (suc (suc n))

then we can define a function `one-not-even : Even 1 → ⊥` by using an absurd pattern:

one-not-even : Even 1 → ⊥
one-not-even ()

Note that if the left-hand side of a clause contains an absurd pattern, its right-hand side must be omitted.

In general, when matching on an argument of type `D i₁ … iₙ` with an absurd pattern, Agda will attempt for each constructor `c : (x₁ : A₁) → … → (xₘ : Aₘ) → D j₁ … jₙ` of the datatype `D` to unify `i₁ … iₙ` with `j₁ … jₙ`. The absurd pattern will only be accepted if all of these unifications end in a conflict.

### As-patterns[](#as-patterns "Link to this heading")

As-patterns (or `@-patterns`) can be used to name a pattern. The name has the same scope as normal pattern variables (i.e. the right-hand side, where clause, and dot patterns). The name reduces to the value of the named pattern. For example:

module _ {A : Set} (_<_ : A → A → Bool) where
  merge : List A → List A → List A
  merge xs [] = xs
  merge [] ys = ys
  merge xs@(x ∷ xs₁) ys@(y ∷ ys₁) =
    if x < y then x ∷ merge xs₁ ys
             else y ∷ merge xs ys₁

As-patterns are properly supported since Agda 2.5.2.

## Case trees[](#case-trees "Link to this heading")

Internally, Agda represents function definitions as _case trees_. For example, a function definition

max : Nat → Nat → Nat
max zero    n       = n
max m       zero    = m
max (suc m) (suc n) = suc (max m n)

will be represented internally as a case tree that looks like this:

max m n = case m of
  zero   → n
  suc m' → case n of
    zero   → suc m'
    suc n' → suc (max m' n')

Note that because Agda uses this representation of the function `max`, the clause `max m zero = m` does not hold definitionally (i.e. as a reduction rule). If you would try to prove that this equation holds, you would not be able to write `refl`:

data _≡_ {A : Set} (x : A) : A → Set where
  refl : x ≡ x

-- Does not work!
lemma : (m : Nat) → max m zero ≡ m
lemma = refl

Clauses which do not hold definitionally are usually (but not always) the result of writing clauses by hand instead of using Agda’s case split tactic. These clauses are [highlighted](https://agda.readthedocs.io/en/latest/tools/emacs-mode.html#highlight) by Emacs.

The [\--exact-split](https://agda.readthedocs.io/en/latest/tools/command-line-options.html#cmdoption-exact-split) flag causes Agda to raise a warning whenever a clause in a definition by pattern matching cannot be made to hold definitionally. Specific clauses can be excluded from this check by means of the `{-# CATCHALL #-}` pragma.

For instance, the above definition of `max` will be flagged when using the [\--exact-split](https://agda.readthedocs.io/en/latest/tools/command-line-options.html#cmdoption-exact-split) flag because its second clause does not to hold definitionally.

When using the [\--exact-split](https://agda.readthedocs.io/en/latest/tools/command-line-options.html#cmdoption-exact-split) flag, catch-all clauses have to be marked as such, for instance:

eq : Nat → Nat → Bool
eq zero    zero    = true
eq (suc m) (suc n) = eq m n
{-# CATCHALL #-}
eq _       _       = false

The [\--no-exact-split](https://agda.readthedocs.io/en/latest/tools/command-line-options.html#cmdoption-exact-split) flag can be used to override a global [\--exact-split](https://agda.readthedocs.io/en/latest/tools/command-line-options.html#cmdoption-exact-split) in a file, by adding a pragma `{-# OPTIONS --no-exact-split #-}`. This option is enabled by default.

Since version 2.8.0, Agda warns about superfluous CATCHALL pragmas, flagging a [UselessPragma](https://agda.readthedocs.io/en/latest/tools/command-line-options.html#cmdoption-arg-UselessPragma).