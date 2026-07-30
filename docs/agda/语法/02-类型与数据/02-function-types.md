> **函数类型** · `function-types`
>
> 依赖函数空间 (x : A) → B 的记法约定与箭头方向。
>
> 🔗 原文：<https://agda.readthedocs.io/en/latest/language/function-types.html>
>
> **本项目相关性**：纤维丛截面、holonomy 算子均为依赖函数类型；理解隐式/显式参数位置是基础。

---
# Function Types[](#function-types "Link to this heading")

Function types are written `(x : A) → B`, or in the case of non-dependent functions simply `A → B`. For instance, the type of the addition function for natural numbers is:

Nat → Nat → Nat

and the type of the addition function for vectors is:

(A : Set) → (n : Nat) → (u : Vec A n) → (v : Vec A n) → Vec A n

where `Set` is the type of sets and `Vec A n` is the type of vectors with `n` elements of type `A`. Arrows between consecutive hypotheses of the form `(x : A)` may also be omitted, and `(x : A) (y : A)` may be shortened to `(x y : A)` (see also [telescopes](telescopes.md#telescopes)):

(A : Set) (n : Nat)(u v : Vec A n) → Vec A n

Functions are constructed by [lambda expressions](lambda-abstraction.md#lambda-abstraction) or [Function Definitions](function-definitions.md#function-definitions).

The application of a function `f : (x : A) → B` to an argument `a : A` is written `f a` and the type of this is `B[x := a]`.

## Notational conventions[](#notational-conventions "Link to this heading")

Function types:

prop₁ : ((x : A) (y : B) → C) is-the-same-as   ((x : A) → (y : B) → C)
prop₂ : ((x y : A) → C)       is-the-same-as   ((x : A)(y : A) → C)
prop₃ : (forall (x : A) → C)  is-the-same-as   ((x : A) → C)
prop₄ : (forall x → C)        is-the-same-as   ((x : _) → C)
prop₅ : (forall x y → C)      is-the-same-as   (forall x → forall y → C)

You can also use the Unicode symbol `∀` (type “\\all” in the Emacs Agda mode) instead of `forall`.

Functional abstraction:

(\x y → e)                    is-the-same-as   (\x → (\y → e))

Functional application:

(f a b)                       is-the-same-as    ((f a) b)