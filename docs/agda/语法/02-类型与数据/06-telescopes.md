> **望远镜** · `telescopes`
>
> telescope（多绑定上下文）记法、binding 位置上的 irrefutable pattern、telescope 内 let。
>
> 🔗 原文：<https://agda.readthedocs.io/en/latest/language/telescopes.html>
>
> **本项目相关性**：★ 依赖类型核心载体；PR #8611 的 makeTau Γ→Δ 即在 telescope 层操作，telescope 理解是关键。

---
# Telescopes[](#telescopes "Link to this heading")

A telescope is a non-empty sequence of variable bindings annotated by their types, with each variable surrounded by parentheses. For example, `(x : Nat) (y : Bool) (z : Bool)` is a telescope. Adjacent variables that have the same type can share a type annotation. For example, the same telescope can be written equivalently as `(x : Nat) (y z : Bool)`. The type of each variable can depend on the previous variables in the telescope, for example `(A : Set) (n : Nat) (v : Vec A n)`.

Note

The terminology is due to de Bruijn [\[1\]](#telescopes-refs): “The word was inspired, of course, by the old-fashioned instrument consisting of segments that slide one into another.” Each variable binding corresponds to a segment of the telescope, which can slide into (i.e. depend on) the previous ones.

Telescopes appear in the following parts of the Agda syntax:

* [Function types](function-types.md#function-types)
* Declarations of [data types](data-types.md#data-types) and [record types](record-types.md#record-types)
* Declarations of [parameterised modules](module-system.md#parameterised-modules)

postulate
  f : (A : Set) (n : Nat) (v : Vec A n) → Nat

data D (A : Set) (n : Nat) (v : Vec A n) : Set where
  -- ...

module M (A : Set) (n : Nat) (v : Vec A n) where
  -- ...

In telescopes of data and record types as well as parameterised modules, it is allowed to omit the type of a variable binding. This is equivalent to giving the variable the type `_` (see [implicit arguments](implicit-arguments.md#implicit-arguments)).

data D' A n (v : Vec A n) : Set where
  -- ...

module M' A n (v : Vec A n) where
  -- ...

In function types, the type of a variable binding can be omitted if the module telescope starts with `forall` or `∀`.

postulate
  f' : ∀ A n (v : Vec A n) → Nat

When binding a variable of a [record type](record-types.md#record-types) (but not a data type), it is possible to deconstruct the bound variable by [pattern matching](record-types.md#decomposing-records):

module N ((x , y) : Nat × Bool) where
  -- ...

Variable bindings in a telescope can be [implicit](implicit-arguments.md#implicit-arguments) or [instance](instance-arguments.md#instance-arguments) arguments. For example:

postulate
  mconcat : {A : Set} {{monoidA : Monoid A}} → List A → A

They can also be [irrelevant](irrelevance.md#irrelevance) or carry another [modality](modalities.md#modalities). For example:

postulate
  div : (m n : Nat) .(nz : NonZero n) → Nat

## Irrefutable Patterns in Binding Positions[](#irrefutable-patterns-in-binding-positions "Link to this heading")

Since Agda 2.6.1, irrefutable patterns can be used at every binding site in a telescope to take the bound value of record type apart. The type of the second projection out of a dependent pair will for instance naturally mention the value of the first projection. Its type can be defined directly using an irrefutable pattern as follows:

proj₂ : ((a , _) : Σ A B) → B a

And this second projection can be implemented with a lamba-abstraction using one of these irrefutable patterns taking the pair apart:

proj₂ = λ (_ , b) → b

Using an as-pattern makes it possible to name the argument and to take it apart at the same time. We can for instance prove that any pair is equal to the pairing of its first and second projections, a property commonly called eta-equality:

eta : (p@(a , b) : Σ A B) → p ≡ (a , b)
eta p = refl

Since Agda 2.9.0, irrefutable patterns require that the deconstructed record has eta-equality. This is the case for `Σ`, but e.g. not for `coinductive` records or records declared with `no-eta-equality`. In the absence of eta-equality, irrefutable patterns trigger the warning [ShouldBeEtaRecordPattern](https://agda.readthedocs.io/en/latest/tools/command-line-options.html#cmdoption-arg-ShouldBeEtaRecordPattern).

## Let Bindings in Telescopes[](#let-bindings-in-telescopes "Link to this heading")

Telescopes of function types and parameterised modules (but not of data and record types) can also contain [let bindings](let-and-where.md#let-expressions). When used in this manner, the let-binding should be surrounded by parentheses and the `in` part of the syntax is omitted. For example:

postulate
  g : (x : Nat) (let y = x + x) (v : Vec Nat y) → Nat

Let-bound variables in a module telescope are available in the whole module. For example:

module O (X : Set) (let LX = List X) (l : LX) where

  extend : LX → LX
  extend m = l ++ m

In general, any valid let-binding can also be used in a telescope. For example, it is possible to pattern match on a record type with a let-binding:

postulate
  h : (f : Nat → (Bool × Bool)) (let (x0 , y0) = f 0) (tx : IsTrue x0) → IsTrue y0

Another notable example is opening a [module](module-system.md#module-system) in a telescope:

module M1 (X : Set) (let open M X) where

This can also be written more compactly with just `open` (without the `let`):

module M2 (X : Set) (open M X) where

### References[](#references "Link to this heading")

\[1\] N.G. de Bruijn. “[Telescopic mappings in typed lambda calculus.](https://doi.org/10.1016/0890-5401%2891%2990066-B)” Information and Computation, Volume 91, Issue 2, 1991.