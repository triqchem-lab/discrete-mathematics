> **数据类型** · `data-types`
>
> 简单/参数化/索引数据类型定义，strict positivity 约束。
>
> 🔗 原文：<https://agda.readthedocs.io/en/latest/language/data-types.html>
>
> **本项目相关性**：GF(3) Trit、Tryte、A4Group、十二律格点均为 data/record；索引类型用于 fiber-dependent 编码。

---
# Data Types[](#data-types "Link to this heading")

## Simple datatypes[](#simple-datatypes "Link to this heading")

### Example datatypes[](#example-datatypes "Link to this heading")

In the introduction we already showed the definition of the data type of natural numbers (in unary notation):

data Nat : Set where
    zero : Nat
    suc  : Nat → Nat

We give a few more examples. First the data type of truth values:

data Bool : Set where
  true  : Bool
  false : Bool

The `True` set represents the trivially true proposition:

data True : Set where
    tt : True

The `False` set has no constructor and hence no elements. It represents the trivially false proposition:

data False : Set where

Another example is the data type of non-empty binary trees with natural numbers in the leaves:

data BinTree : Set where
  leaf   : Nat → BinTree
  branch : BinTree → BinTree → BinTree

Finally, the data type of Brouwer ordinals:

data Ord : Set where
  zeroOrd : Ord
  sucOrd  : Ord → Ord
  limOrd  : (Nat → Ord) → Ord

### General form[](#general-form "Link to this heading")

The general form of the definition of a simple datatype `D` is the following

data D : Setᵢ where
  c₁ : A₁
  ...
  cₙ : Aₙ

The name `D` of the data type and the names `c₁`, …, `cₙ` of the constructors must be new w.r.t. the current signature and context, and the types `A₁`, …, `Aₙ` must be function types ending in `D`, i.e. they must be of the form

(y₁ : B₁) → ... → (yₘ : Bₘ) → D

## Parametrized datatypes[](#parametrized-datatypes "Link to this heading")

Datatypes can have _parameters_. They are declared after the name of the datatype but before the colon, for example:

data List (A : Set) : Set where
  []  : List A
  _∷_ : A → List A → List A

## Indexed datatypes[](#indexed-datatypes "Link to this heading")

In addition to parameters, datatypes can also have _indices_. In contrast to parameters which are required to be the same for all constructors, indices can vary from constructor to constructor. They are declared after the colon as function arguments to `Set`. For example, fixed-length vectors can be defined by indexing them over their length of type `Nat`:

data Vector (A : Set) : Nat → Set where
  []  : Vector A zero
  _∷_ : {n : Nat} → A → Vector A n → Vector A (suc n)

Notice that the parameter `A` is bound once for all constructors, while the index `{n : Nat}` must be bound locally in the constructor `_∷_`.

Indexed datatypes can also be used to describe predicates, for example the predicate `Even : Nat → Set` can be defined as follows:

data Even : Nat → Set where
  even-zero  : Even zero
  even-plus2 : {n : Nat} → Even n → Even (suc (suc n))

### General form[](#id4 "Link to this heading")

The general form of the definition of a (parametrized, indexed) datatype `D` is the following

data D (x₁ : P₁) ... (xₖ : Pₖ) : (y₁ : Q₁) → ... → (yₗ : Qₗ) → Set ℓ where
  c₁ : A₁
  ...
  cₙ : Aₙ

where the types `A₁`, …, `Aₙ` are function types of the form

(z₁ : B₁) → ... → (zₘ : Bₘ) → D x₁ ... xₖ t₁ ... tₗ

## Strict positivity[](#strict-positivity "Link to this heading")

When defining a datatype `D`, Agda poses an additional requirement on the types of the constructors of `D`, namely that `D` may only occur **strictly positively** in the types of their arguments.

Concretely, for a datatype with constructors `c₁ : A₁`, …, `cₙ : Aₙ`, Agda checks that each Aᵢ has the form

(y₁ : B₁) → ... → (yₘ : Bₘ) → D

where an argument types Bᵢ of the constructors is either

* _non-inductive_ (a _side condition_) and does not mention `D` at all,
* or _inductive_ and has the form  
(z₁ : C₁) → ... → (zₖ : Cₖ) → D  
where `D` must not occur in any Cⱼ.

The strict positivity condition rules out declarations such as

data Bad : Set where
    bad : (Bad → Bad) → Bad
    --     A     B      C
    -- A is in a negative position, B and C are OK

since there is a negative occurrence of `Bad` in the type of the argument of the constructor. (Note that the corresponding data type declaration of `Bad` is allowed in standard functional languages such as Haskell and ML.).

Non strictly-positive declarations are rejected because they admit non-terminating functions.

If the positivity check is disabled, so that a similar declaration of `Bad` is allowed, it is possible to construct a term of the empty type, even without recursion.

{-# OPTIONS --no-positivity-check #-}

data ⊥ : Set where

data Bad : Set where
  bad : (Bad → ⊥) → Bad

self-app : Bad → ⊥
self-app (bad f) = f (bad f)

absurd : ⊥
absurd = self-app (bad self-app)

For more general information on termination see [Termination Checking](termination-checking.md#termination-checking).