> **编译指令（Pragmas）** · `pragmas`
>
> 全部 pragma 索引：OPTIONS/INLINE/REWRITE/BUILTIN/ETC，控制编译器行为。
>
> 🔗 原文：<https://agda.readthedocs.io/en/latest/language/pragmas.html>
>
> **本项目相关性**：库配置 --guardedness -WnoUnsupportedIndexedMatch 等选项；理解 pragma 是调优前提。

---
# Pragmas[](#pragmas "Link to this heading")

Pragmas are special declarations that pass extra information to Agda about how regular declarations are to be interpreted. They are written similar to block comments so that users may easily skip them in a first reading of an Agda document. The general format is:

{-# <PRAGMA_NAME> <arguments> #-}

## Index of pragmas[](#index-of-pragmas "Link to this heading")

* [BUILTIN](built-ins.md#built-ins)
* [CATCHALL](function-definitions.md#catchall-pragma)
* [COMPILE](foreign-function-interface.md#foreign-function-interface)
* [DISPLAY](#display-pragma)
* [ETA\_EQUALITY](coinduction.md#eta-pragma)
* [FOREIGN](foreign-function-interface.md#foreign-function-interface)
* [INJECTIVE](#injective-pragma)
* [INJECTIVE\_FOR\_INFERENCE](#injective-for-inference-pragma)
* [INLINE](#inline-pragma)
* [NO\_POSITIVITY\_CHECK](positivity-checking.md#no-positivity-check-pragma)
* [NO\_TERMINATION\_CHECK](termination-checking.md#terminating-pragma)
* [NO\_UNIVERSE\_CHECK](universe-levels.md#no-universe-check-pragma)
* [NOINLINE](#inline-pragma)
* [NON\_COVERING](#non-covering-pragma)
* [NON\_TERMINATING](termination-checking.md#non-terminating-pragma)
* [OPTIONS](#options-pragma)
* [POLARITY](positivity-checking.md#polarity-pragma)
* [REWRITE](rewriting.md#rewriting)
* [STATIC](built-ins.md#built-ins)
* [TERMINATING](termination-checking.md#terminating-pragma)
* [WARNING\_ON\_USAGE](#warning-pragma)
* [WARNING\_ON\_IMPORT](#warning-pragma)

See also [Command-line and pragma options](https://agda.readthedocs.io/en/latest/tools/command-line-options.html#command-line-pragmas).

### The `DISPLAY` pragma[](#the-display-pragma "Link to this heading")

Users can declare a display form via the `DISPLAY` pragma:

{-# DISPLAY f e1 .. en = e #-}

This causes `f e1 .. en` to be printed in the same way as `e`, where `ei` can bind variables used in `e`. The expressions `ei` and `e`are scope checked, but not type checked.

For example this can be used to print overloaded (instance) functions with the overloaded name:

instance
  NumNat : Num Nat
  NumNat = record { ..; _+_ = natPlus }

{-# DISPLAY natPlus a b = a + b #-}

Limitations:

> * Left-hand sides of the display form are restricted to variables, constructors, defined functions or types, and literals. In particular, lambdas are not allowed in left-hand sides.
> * Since display forms are not type checked, implicit argument insertion may not work properly if the type of f computes to an implicit function space after pattern matching.
> * An ill-typed display form can make Agda crash with an internal error when Agda tries to use it (issue #6476 <https://github.com/agda/agda/issues/6476>).

### The `INJECTIVE` pragma[](#the-injective-pragma "Link to this heading")

Injective pragmas can be used to mark a definition as injective for the pattern matching unifier. This can be used as a version of [\--injective-type-constructors](https://agda.readthedocs.io/en/latest/tools/command-line-options.html#cmdoption-injective-type-constructors) that only applies to specific datatypes.

Example:

open import Agda.Builtin.Equality
open import Agda.Builtin.Nat

data Fin : Nat → Set where
  zero : {n : Nat} → Fin (suc n)
  suc  : {n : Nat} → Fin n → Fin (suc n)

{-# INJECTIVE Fin #-}

Fin-injective : {m n : Nat} → Fin m ≡ Fin n → m ≡ n
Fin-injective refl = refl

Aside from datatypes, this pragma can also be used to mark other definitions as being injective (for example postulates).

At the moment it only gives you propositional injectivity, so you can pattern match on a proof of Fin x ≡ Fin y in example above, but does not give you definitional injectivity, so the constraint solver does not know how to solve the constraint Fin x = Fin \_. Relevant issue: <https://github.com/agda/agda/issues/4106#issuecomment-534904561>

### The `INJECTIVE_FOR_INFERENCE` pragma[](#the-injective-for-inference-pragma "Link to this heading")

Treats functions as injective for type inference. This behaves like a local version of [\--lossy-unification](https://agda.readthedocs.io/en/latest/tools/command-line-options.html#cmdoption-lossy-unification) and has the same potential issues. Since Agda can not always infer whether a function is injective it can be used to get stronger unification for those functions.

The option [\--no-require-unique-meta-solutions](https://agda.readthedocs.io/en/latest/tools/command-line-options.html#cmdoption-require-unique-meta-solutions) needs to be active in the file where the function is used, but not necessarily in the file it is defined. When solving a constraint involving the function in a file where [\--require-unique-meta-solutions](https://agda.readthedocs.io/en/latest/tools/command-line-options.html#cmdoption-require-unique-meta-solutions) is in effect, the pragma is ignored.

Example:

open import Agda.Builtin.Equality
open import Agda.Builtin.List

module _ {A : Set} where
  _++_ : List A → List A → List A
  []       ++ ys = ys
  (x ∷ xs) ++ ys = x ∷ (xs ++ ys)

  reverse : List A → List A
  reverse []      = []
  reverse (x ∷ l) = reverse l ++ (x ∷ [])

  {-# INJECTIVE_FOR_INFERENCE reverse #-}

  reverse-≡ : {l l' : List A} → reverse l ≡ reverse l' → reverse l ≡ reverse l'
  reverse-≡ h = h

  []≡[] : {l l' : List A} → [] ≡ []
  []≡[] = reverse-≡ (refl {x = reverse []})

### The `INLINE` and `NOINLINE` pragmas[](#the-inline-and-noinline-pragmas "Link to this heading")

A function definition marked with an `INLINE` pragma is inlined during compilation. If it is a simple function definition that does no pattern matching, it is also inlined in function bodies at type-checking time.

When the [\--auto-inline](https://agda.readthedocs.io/en/latest/tools/command-line-options.html#cmdoption-auto-inline) [command-line option](https://agda.readthedocs.io/en/latest/tools/command-line-options.html#command-line-options) is enabled, function definitions are automatically marked `INLINE` if they satisfy the following criteria:

* No pattern matching.
* Uses each argument at most once.
* Does not use all its arguments.

Automatic inlining can be prevented using the `NOINLINE` pragma.

Example:

-- Would be auto-inlined since it doesn't use the type arguments.
_∘_ : {A B C : Set} → (B → C) → (A → B) → A → C
(f ∘ g) x = f (g x)

{-# NOINLINE _∘_ #-} -- prevents auto-inlining

-- Would not be auto-inlined since it's using all its arguments
_o_ : (Set → Set) → (Set → Set) → Set → Set
(F o G) X = F (G X)

{-# INLINE _o_ #-} -- force inlining

#### Inlining constructor right-hand sides[](#inlining-constructor-right-hand-sides "Link to this heading")

Added in version 2.6.4.

Constructors can also be marked `INLINE` (for types supporting copattern matching):

record Stream (A : Set) : Set where
  coinductive; constructor _∷_
  field head : A
        tail : Stream A
open Stream
{-# INLINE _∷_ #-}

Functions definitions using these constructors will be translated to use copattern matching instead, e.g.:

nats : Nat → Stream Nat
nats n = n ∷ nats (1 + n)

is translated to:

nats' : Nat → Stream Nat
nats' n .head = n
nats' n .tail = nats (n + 1)

which passes termination-checking.

This translation only works for fully-applied constructors at the root of a function definition’s right-hand side.

If [\--exact-split](https://agda.readthedocs.io/en/latest/tools/command-line-options.html#cmdoption-exact-split) is on, the inlining will trigger a [InlineNoExactSplit](https://agda.readthedocs.io/en/latest/tools/command-line-options.html#cmdoption-arg-InlineNoExactSplit) warning for `nats`.

### The `NON_COVERING` pragma[](#the-non-covering-pragma "Link to this heading")

Added in version 2.6.1.

The `NON_COVERING` pragma can be placed before a function (or a block of mutually defined functions) which the user knows to be partial. To be used as a version of [\--allow-incomplete-matches](https://agda.readthedocs.io/en/latest/tools/command-line-options.html#cmdoption-allow-incomplete-matches) that only applies to specific functions.

### The `NOT_PROJECTION_LIKE` pragma[](#the-not-projection-like-pragma "Link to this heading")

Added in version 2.6.3.

The `NOT_PROJECTION_LIKE` pragma disables projection-likeness analysis for a particular function, which must be defined before it can be affected by the pragma. To be used as a version of [\--no-projection-like](https://agda.readthedocs.io/en/latest/tools/command-line-options.html#cmdoption-no-projection-like) that only applies to specific functions.

For example, suppose you have a function which projects a field from an instance argument, and instance selection depends on a visible argument. If an application of this function is generated by metaprogramming, and inserted in the source code by `elaborate-and-give` (C\-c C\-m in Emacs), the visible argument would instead be printed as \_, because it was erased!

Example:

open import Agda.Builtin.Bool

record P (n : Nat) : Set where
  field the-bool : Bool
open P

-- Agda would normally mark this projection-like, so it would have its
-- (n : Nat) argument erased when printing, including by e.g.
-- elaborate-and-give
get-bool-from-p : (n : Nat) ⦃ has-p : P n ⦄ → Bool
get-bool-from-p _ ⦃ p ⦄ = p .the-bool
{-# NOT_PROJECTION_LIKE get-bool-from-p #-}

-- With the pragma, it gets treated as a regular function.

### The `OPTIONS` pragma[](#the-options-pragma "Link to this heading")

Some options can be given at the top of .agda files in the form

`{-# OPTIONS --{opt₁} --{opt₂} ... #-}`

The possible options are listed in [Command-line and pragma options](https://agda.readthedocs.io/en/latest/tools/command-line-options.html#command-line-pragmas).

### The `WARNING_ON_` pragmas[](#the-warning-on-pragmas "Link to this heading")

A library author can use a `WARNING_ON_USAGE` pragma to attach to a defined name a warning to be raised whenever this name is used (since Agda 2.5.4).

Similarly they can use a `WARNING_ON_IMPORT` pragma to attach to a module a warning to be raised whenever this module is imported (since Agda 2.6.1).

This would typically be used to declare a name or a module ‘DEPRECATED’ and advise the end-user to port their code before the feature is dropped.

Users can turn these warnings off by using the `--warn=noUserWarning` option. For more information about the warning machinery, see [Warnings](https://agda.readthedocs.io/en/latest/tools/command-line-options.html#warnings).

Example:

-- The new name for the identity
id : {A : Set} → A → A
id x = x

-- The deprecated name
λx→x = id

-- The warning
{-# WARNING_ON_USAGE λx→x "DEPRECATED: Use `id` instead of `λx→x`" #-}
{-# WARNING_ON_IMPORT "DEPRECATED: Use module `Function.Identity` rather than `Identity`" #-}