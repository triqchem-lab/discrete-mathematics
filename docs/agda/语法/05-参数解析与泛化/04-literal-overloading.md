> **字面量重载** · `literal-overloading`
>
> ℕ/String/Negative 字面量通过 Number/IsString/IsNegativeNumber 实例重载的机制与限制。
>
> 🔗 原文：<https://agda.readthedocs.io/en/latest/language/literal-overloading.html>
>
> **本项目相关性**：项目宪法禁用字面量（规避 Agda #8540 ring solver bug），但理解重载机制有助于诊断隐式字面量泄漏。

---
# Literal Overloading[](#literal-overloading "Link to this heading")

## Natural numbers[](#natural-numbers "Link to this heading")

By default [natural number literals](lexical-structure.md#lexical-structure-int-literals) are mapped to the [built-in natural number type](built-ins.md#built-in-nat). This can be changed with the `FROMNAT` built-in, which binds to a function accepting a natural number:

{-# BUILTIN FROMNAT fromNat #-}

This causes natural number literals `n` to be desugared to `fromNat n`, whenever `fromNat` is in scope _unqualified_ (renamed or not). Note that the desugaring happens before [implicit argument](implicit-arguments.md#implicit-arguments) are inserted so `fromNat` can have any number of implicit or [instance arguments](instance-arguments.md#instance-arguments). This can be exploited to support overloaded literals by defining a [type class](instance-arguments.md#instance-arguments) containing `fromNat`:

module number-simple where

  record Number {a} (A : Set a) : Set a where
    field fromNat : Nat → A

  open Number {{...}} public

{-# BUILTIN FROMNAT fromNat #-}

This definition requires that any natural number can be mapped into the given type, so it won’t work for types like `Fin n`. This can be solved by refining the `Number` class with an additional constraint:

record Number {a} (A : Set a) : Set (lsuc a) where
  field
    Constraint : Nat → Set a
    fromNat : (n : Nat) {{_ : Constraint n}} → A

open Number {{...}} public using (fromNat)

{-# BUILTIN FROMNAT fromNat #-}

This is the definition used in `Agda.Builtin.FromNat`. A `Number` instance for `Nat` is simply this:

instance
  NumNat : Number Nat
  NumNat .Number.Constraint _ = ⊤
  NumNat .Number.fromNat    m = m

A `Number` instance for `Fin n` can be defined as follows:

_≤_ : (m n : Nat) → Set
zero  ≤ n     = ⊤
suc m ≤ zero  = ⊥
suc m ≤ suc n = m ≤ n

fromN≤ : ∀ m n → m ≤ n → Fin (suc n)
fromN≤ zero    _       _  = zero
fromN≤ (suc _) zero    ()
fromN≤ (suc m) (suc n) p  = suc (fromN≤ m n p)

instance
  NumFin : ∀ {n} → Number (Fin (suc n))
  NumFin {n} .Number.Constraint m         = m ≤ n
  NumFin {n} .Number.fromNat    m {{m≤n}} = fromN≤ m n m≤n

test : Fin 5
test = 3

It is important that the constraint for literals is trivial. Here, `3 ≤ 5` evaluates to `⊤` whose inhabitant is found by unification.

Using predefined function from the standard library and instance `NumNat`, the `NumFin` instance can be simply:

open import Data.Fin using (Fin; #_)
open import Data.Nat using (suc; _≤?_)
open import Relation.Nullary.Decidable using (True)

instance
  NumFin : ∀ {n} → Number (Fin n)
  NumFin {n} .Number.Constraint m         = True (suc m ≤? n)
  NumFin {n} .Number.fromNat    m {{m<n}} = #_ m {m<n = m<n}

Note

Overloading numeric literals only works in expressions, not in patterns. The following is rejected:

isZero : ∀ {n} → Fin n → Bool
isZero 0 = true   -- error: zero is not a constructor of the datatype Fin
isZero _ = false

## Negative numbers[](#negative-numbers "Link to this heading")

Negative integer literals have no default mapping and can only be used through the `FROMNEG` built-in. Binding this to a function `fromNeg` causes negative integer literals `-n` to be desugared to `fromNeg n`, where `n`is a [built-in natural number](built-ins.md#built-in-nat). From `Agda.Builtin.FromNeg`:

record Negative {a} (A : Set a) : Set (lsuc a) where
  field
    Constraint : Nat → Set a
    fromNeg : (n : Nat) {{_ : Constraint n}} → A

open Negative {{...}} public using (fromNeg)
{-# BUILTIN FROMNEG fromNeg #-}

## Strings[](#strings "Link to this heading")

[String literals](lexical-structure.md#lexical-structure-string-literals) are overloaded with the `FROMSTRING` built-in, which works just like `FROMNAT`. If it is not bound string literals map to [built-in strings](built-ins.md#built-in-string). From `Agda.Builtin.FromString`:

record IsString {a} (A : Set a) : Set (lsuc a) where
  field
    Constraint : String → Set a
    fromString : (s : String) {{_ : Constraint s}} → A

open IsString {{...}} public using (fromString)
{-# BUILTIN FROMSTRING fromString #-}

## Restrictions[](#restrictions "Link to this heading")

Currently only integer and string literals can be overloaded.

Overloading does not work in patterns yet.