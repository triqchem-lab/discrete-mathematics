> **隐式参数** · `implicit-arguments`
>
> 花括号隐式参数、tactic 参数、元变量与统一化（unification）机制。
>
> 🔗 原文：<https://agda.readthedocs.io/en/latest/language/implicit-arguments.html>
>
> **本项目相关性**：理解统一化对诊断 PR #8611 的 CRT 正交分解何时触发、以及 UnsupportedIndexedMatch 根因至关重要。

---
# Implicit Arguments[](#implicit-arguments "Link to this heading")

It is possible to omit terms that the type checker can figure out for itself, replacing them by an underscore (`_`). If the type checker cannot infer the value of an `_` it will report an error. For instance, for the polymorphic identity function

id : (A : Set) → A → A

the first argument can be inferred from the type of the second argument, so we might write `id _ zero` for the application of the identity function to `zero`.

We can even write this function application without the first argument. In that case we declare an implicit function space:

id : {A : Set} → A → A

and then we can use the notation `id zero`.

Another example:

_==_  : {A : Set} → A → A → Set
subst : {A : Set} (C : A → Set) {x y : A} → x == y → C x → C y

Note how the first argument to `_==_` is left implicit. Similarly, we may leave out the implicit arguments `A`, `x`, and `y` in an application of `subst`. To give an implicit argument explicitly, enclose it in curly braces. The following two expressions are equivalent:

x1 = subst C eq cx
x2 = subst {_} C {_} {_} eq cx

It is worth noting that implicit arguments are also inserted at the end of an application, if it is required by the type. For example, in the following, `y1` and `y2` are equivalent.

y1 : a == b → C a → C b
y1 = subst C

y2 : a == b → C a → C b
y2 = subst C {_} {_}

Implicit arguments are inserted eagerly in left-hand sides so `y3` and `y4`are equivalent. An exception is when no type signature is given, in which case no implicit argument insertion takes place. Thus in the definition of `y5`the only implicit is the `A` argument of `subst`.

y3 : {x y : A} → x == y → C x → C y
y3 = subst C

y4 : {x y : A} → x == y → C x → C y
y4 {x} {y} = subst C {_} {_}

y5 = subst C

It is also possible to write lambda abstractions with implicit arguments. For example, given `id : (A : Set) → A → A`, we can define the identity function with implicit type argument as

id’ = λ {A} → id A

Implicit arguments can also be referred to by name, so if we want to give the expression `e` explicitly for `y`without giving a value for `x` we can write

subst C {y = e} eq cx

In rare circumstances it can be useful to separate the name used to give an argument by name from the name of the bound variable, for instance if the desired name shadows an existing name. To do this you write

id₂ : {A = X : Set} → X → X  -- name of bound variable is X
id₂ x = x

use-id₂ : (Y : Set) → Y → Y
use-id₂ Y = id₂ {A = Y}      -- but the label is A

Labeled bindings must appear by themselves when typed, so the type `Set` needs to be repeated in this example:

const : {A = X : Set} {B = Y : Set} → A → B → A
const x y = x

When constructing implicit function spaces the implicit argument can be omitted, so both expressions below are valid expressions of type `{A : Set} → A → A`:

z1 = λ {A} x → x
z2 = λ x → x

The `∀` (or `forall`) syntax for function types also has implicit variants:

① : (∀ {x : A} → B)    is-the-same-as  ({x : A} → B)
② : (∀ {x} → B)        is-the-same-as  ({x : _} → B)
③ : (∀ {x y} → B)      is-the-same-as  (∀ {x} → ∀ {y} → B)

In very special situations it makes sense to declare _unnamed_ hidden arguments `{A} → B`. In the following `example`, the hidden argument to `scons` of type `zero ≤ zero` can be solved by η-expansion, since this type reduces to `⊤`.

data ⊥ : Set where

_≤_ : Nat → Nat → Set
zero ≤ _      = ⊤
suc m ≤ zero  = ⊥
suc m ≤ suc n = m ≤ n

data SList (bound : Nat) : Set where
  []    : SList bound
  scons : (head : Nat) → {head ≤ bound} → (tail : SList head) → SList bound

example : SList zero
example = scons zero []

There are no restrictions on when a function space can be implicit. Internally, explicit and implicit function spaces are treated in the same way. This means that there are no guarantees that implicit arguments will be solved. When there are unsolved implicit arguments the type checker will give an error message indicating which application contains the unsolved arguments. The reason for this liberal approach to implicit arguments is that limiting the use of implicit argument to the cases where we guarantee that they are solved rules out many useful cases in practice.

## Tactic arguments[](#tactic-arguments "Link to this heading")

You can declare [tactics](reflection.md#reflection) to be used to solve a particular implicit argument using the `@(tactic t)` attribute, where `t : Term → TC ⊤`. For instance:

clever-search : Term → TC ⊤
clever-search hole = unify hole (lit (nat 17))

the-best-number : {@(tactic clever-search) n : Nat} → Nat
the-best-number {n} = n

check : the-best-number ≡ 17
check = refl

The tactic can be an arbitrary term of the right type and may depend on previous arguments to the function:

default : {A : Set} → A → Term → TC ⊤
default x hole = bindTC (quoteTC x) (unify hole)

search : (depth : Nat) → Term → TC ⊤

example : {@(tactic default 10)   depth : Nat}
          {@(tactic search depth) proof : Proof} →
          Goal

## Metavariables[](#metavariables "Link to this heading")

## Unification[](#unification "Link to this heading")