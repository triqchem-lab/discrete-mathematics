> **Lambda 抽象** · `lambda-abstraction`
>
> λ 表达式、pattern lambda、absurd lambda。
>
> 🔗 原文：<https://agda.readthedocs.io/en/latest/language/lambda-abstraction.html>
>
> **本项目相关性**：定义路径/transport 等高阶函数时常用 λ；pattern lambda 简化局部模式匹配。

---
# Lambda Abstraction[](#lambda-abstraction "Link to this heading")

## Lambda expressions[](#lambda-expressions "Link to this heading")

Anonymous functions can be defined using a lambda expression `\x → u`:

myFun = \ x → x + x -- equivalent: `myFun x = x + x`

You can also use the Unicode symbol `λ` (type “\\lambda” or “\\Gl” in the Emacs Agda mode) instead of `\` (type “\\\\” in the Emacs Agda mode).

Lambda expressions can take several arguments and arguments can optionally be annotated with a type. For instance, both expressions below have type `(A : Set) → A → A` (the second expression checks against other types as well):

example₁ = \ (A : Set)(x : A) → x
example₂ = \ A x → x

A functions taking `n` (> 1) arguments is equivalent to a function that takes a single argument and returns another function with `n-1` arguments, i.e. functions are curried.

curry : (λ x y → x + y) ≡ (λ x → (λ y → x + y))
curry = refl

All functions in Agda satisfy η-equality: `f` is (definitionally) equal to `λ x → f x`.

etaFun : myFun ≡ λ x → myFun x
etaFun = refl

In particular, two lambda expressions with the same body up to renaming of the argument(s) are considered equal.

alpha : (λ x → x + 1) ≡ (λ y → y + 1)
alpha = refl

Lambda expressions can take [Implicit Arguments](implicit-arguments.md#implicit-arguments) and [Instance Arguments](instance-arguments.md#instance-arguments) by adding curly braces (resp. double curly braces) around the argument.

implicit-lambda = λ {A : Set} (x : A) → x

instance-lambda = λ (A : Set) {{monoid-A : Monoid A}} → mempty

Arguments to lambda expressions can also be annotated with any [modality](modalities.md#modalities), for instance with [erasure status](runtime-irrelevance.md#erased-lambda).

Note that in Cubical Agda (see [\--cubical](https://agda.readthedocs.io/en/latest/tools/command-line-options.html#cmdoption-cubical)), many of the examples above do not pass because there the types of lambda expressions are not _inferred_ in general; lambdas are only _checked_ against given types. Thus, type signatures are needed for `myFun` etc.

## Pattern lambda[](#pattern-lambda "Link to this heading")

Anonymous pattern matching functions can be defined by a _pattern lambda_ using one of the two following syntaxes:

\ { p11 .. p1n -> e1 ; … ; pm1 .. pmn -> em }

\ where
  p11 .. p1n -> e1
  …
  pm1 .. pmn -> em

(where, as usual, `\` and `->` can be replaced by `λ` and `→`). Note that the `where` keyword introduces an _indented_ block of clauses; if there is only one clause then it may be used inline.

Examples of pattern lambdas:

and : Bool → Bool → Bool
and = λ { true x → x ; false _ → false }

xor : Bool → Bool → Bool
xor = λ { true  true  → false
        ; false false → false
        ; _     _     → true
        }

eq : Bool → Bool → Bool
eq = λ where
  true  true  → true
  false false → true
  _ _ → false

myFst : {A : Set} {B : A → Set} → Σ A B → A
myFst = λ { (a , b) → a }

mySnd : {A : Set} {B : A → Set} (p : Σ A B) → B (fst p)
mySnd = λ { (a , b) → b }

swap : {A B : Set} → A × B → B × A
swap = λ where (a , b) → (b , a)

Pattern lambdas can also use [Copatterns](copatterns.md#copatterns) by using projections in [postfix notation](record-types.md#record-types).

swap' : {A B : Set} → A × B → B × A
swap' = λ where
  (a , b) .fst → b
  (a , b) .snd → a

It is not allowed to use `where` and `with` constructions in pattern lambdas.

### Internal representation of pattern lambdas[](#internal-representation-of-pattern-lambdas "Link to this heading")

Internally pattern lambdas are translated into a function definition of the following form:

extlam p11 .. p1n = e1
…
extlam pm1 .. pmn = em

where extlam is a fresh name. In other words, pattern lambdas are _generative_. In particular, two pattern lambdas with the same body are not considered equal by Agda (in contrast to regular lambda expressions).

(λ { true → true ; false → false }) ==
(λ { true → true ; false → false })

This type is equivalent to `extlam1 ≡ extlam2` for some distinct fresh names `extlam1` and `extlam2`, hence cannot be proven with `refl`.

## Absurd lambda[](#absurd-lambda "Link to this heading")

An _absurd lambda_ is a lambda expression that uses an [absurd pattern](function-definitions.md#absurd-patterns) `()`.

absurd-lambda : 0 ≡ 1 → ⊥
absurd-lambda = λ ()

Unlike general pattern lambdas, absurd lambdas do not require curly braces or the `where` keyword, although using them is still allowed.

absurd-lambda-curly : 0 ≡ 1 → ⊥
absurd-lambda-curly = λ { () }

absurd-lambda-where : 0 ≡ 1 → ⊥
absurd-lambda-where = λ where ()

It is also allowed to have regular arguments before or after the absurd pattern.

absurd-lambda-list : {A : Set} (x : A) (xs : List A) → x ∷ xs ≡ [] → ⊥
absurd-lambda-list = λ x xs ()