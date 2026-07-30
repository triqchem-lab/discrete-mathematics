> **大小类型** · `sized-types`
>
> Size 索引类型用于保证（余）归纳的 productivity 与终止性。
>
> 🔗 原文：<https://agda.readthedocs.io/en/latest/language/sized-types.html>
>
> **本项目相关性**：余归纳共振链、自相似 T⁶ 结构的终止性证明可用 sized types 替代手动 termination 度量。

---
# Sized Types[](#sized-types "Link to this heading")

Note

This is a stub.

Sizes help the termination checker by tracking the depth of data structures across definition boundaries.

The built-in combinators for sizes are described in [Sized types](built-ins.md#builtin-sized-types).

## Example for coinduction: finite languages[](#example-for-coinduction-finite-languages "Link to this heading")

See [Abel 2017](#abel-2017) and [Traytel 2017](#traytel-2017).

Decidable languages can be represented as infinite trees. Each node has as many children as the number of characters in the alphabet `A`. Each path from the root of the tree to a node determines a possible word in the language. Each node has a boolean label, which is `true` if and only if the word corresponding to that node is in the language. In particular, the root node of the tree is labelled `true` if and only if the word `ε` belongs to the language.

These infinite trees can be represented as the following coinductive data-type:

record Lang (i : Size) (A : Set) : Set where
  coinductive
  field
    ν : Bool
    δ : ∀{j : Size< i} → A → Lang j A

open Lang

As we said before, given a language `a : Lang A`, `ν a ≡ true` iff `ε ∈ a`. On the other hand, the language `δ a x : Lang A` is the [Brzozowski derivative](https://en.wikipedia.org/wiki/Brzozowski%5Fderivative) of `a` with respect to the character `x`, that is, `w ∈ δ a x` iff `xw ∈ a`.

With this data type, we can define some regular languages. The first one, the empty language, contains no words; so all the nodes are labelled `false`:

∅ : ∀ {i A}  → Lang i A
ν ∅   = false
δ ∅ _ = ∅

The second one is the language containing a single word; the empty word. The root node is labelled `true`, and all the others are labelled `false`:

ε : ∀ {i A} → Lang i A
ν ε   = true
δ ε _ = ∅

To compute the union (or sum) of two languages, we do a point-wise `or`operation on the labels of their nodes:

_+_ : ∀ {i A} → Lang i A → Lang i A → Lang i A
ν (a + b)   = ν a   ∨ ν b
δ (a + b) x = δ a x + δ b x

infixl 10 _+_

Now, lets define concatenation. The base case (`ν`) is straightforward: `ε ∈ a · b` iff `ε ∈ a` and `ε ∈ b`.

For the derivative (`δ`), assume that we have a word `w`, `w ∈ δ (a · b) x`. This means that `xw = αβ`, with `α ∈ a` and `β ∈ b`.

We have to consider two cases:

> 1. `ε ∈ a`. Then, either:
> 
>  * `α = ε`, and `β = xw`, where `w ∈ δ b x`.
>  * `α = xα’`, with `α’ ∈ δ a x`, and `w = α’β ∈ δ a x · b`.
> 2. `ε ∉ a`. Then, only the second case above is possible:
> 
>  * `α = xα’`, with `α’ ∈ δ a x`, and `w = α’β ∈ δ a x · b`.

_·_ : ∀ {i A} → Lang i A → Lang i A → Lang i A
ν (a · b)   = ν a ∧ ν b
δ (a · b) x = if ν a then δ a x · b + δ b x else δ a x · b

infixl 20 _·_

Here is where sized types really shine. Without sized types, the termination checker would not be able to recognize that `_+_` or `if_then_else` are not inspecting the tree, which could render the definition non-productive. By contrast, with sized types, we know that the `a + b` is defined to the same depth as `a` and `b` are.

In a similar spirit, we can define the Kleene star:

_* : ∀ {i A} → Lang i A → Lang i A
ν (a *)   = true
δ (a *) x = δ a x · a *

infixl 30 _*

Again, because the types tell us that \_·\_ preserves the size of its inputs, we can have the recursive call to `a *` under a function call to `_·_`.

### Testing[](#testing "Link to this heading")

First, we want to give a precise notion of membership in a language. We consider a word as a `List` of characters.

_∈_ : ∀ {i} {A} → List i A → Lang i A → Bool
[]      ∈ a = ν a
(x ∷ w) ∈ a = w ∈ δ a x

Note how the size of the word we test for membership cannot be larger than the depth to which the language tree is defined.

If we want to use regular, non-sized lists, we need to ask for the language to have size `∞`.

_∈_ : ∀ {A} → List A → Lang ∞ A → Bool
[]      ∈ a = ν a
(x ∷ w) ∈ a = w ∈ δ a x

Intuitively, `∞` is a `Size` larger than the size of any term than one could possibly define in Agda.

Now, let’s consider binary strings as words. First, we define the languages `⟦ x ⟧` containing the single word “x” of length 1, for alphabet `A = Bool`:

⟦_⟧ : ∀ {i} → Bool → Lang i Bool
ν ⟦ _     ⟧       = false

δ ⟦ false ⟧ false = ε
δ ⟦ true  ⟧ true  = ε
δ ⟦ false ⟧ true  = ∅
δ ⟦ true  ⟧ false = ∅

Now we can define the bip-bop language, consisting of strings of even length alternating letters “true” and “false”.

bip-bop = (⟦ true ⟧ · ⟦ false ⟧)*

Let’s test a few words for membership in the language `bip-bop`!

test₁ : (true ∷ false ∷ true ∷ false ∷ true ∷ false ∷ []) ∈ bip-bop ≡ true
test₁ = refl

test₂ : (true ∷ false ∷ true ∷ false ∷ true ∷ []) ∈ bip-bop ≡ false
test₂ = refl

test₃ : (true ∷ true ∷ false ∷ []) ∈ bip-bop ≡ false
test₃ = refl

## References[](#references "Link to this heading")

> [Equational Reasoning about Formal Languages in Coalgebraic Style, Andreas Abel](http://www.cse.chalmers.se/~abela/jlamp17.pdf).

> [Formal Languages, Formally and Coinductively, Dmitriy Traytel, LMCS Vol. 13(3:28)2017, pp. 1–22 (2017)](http://doi.org/10.23638/LMCS-13%283:28%292017).