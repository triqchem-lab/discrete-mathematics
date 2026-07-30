> **模态系统** · `modalities`
>
> 通用模态框架：位置模态系统与纯模态系统，统一描述 irrelevance/flat/...
>
> 🔗 原文：<https://agda.readthedocs.io/en/latest/language/modalities.html>
>
> **本项目相关性**：范畴分离原则可视为模态分层；理解通用框架有助于为不同文明层级设计隔离机制。

---
# Modalities[](#modalities "Link to this heading")

Agda uses the machinery of modalities to implement a couple of features. While they all generally have similar structure, these modality systems don’t all have the same behavior and obey the same typing rules, especially regarding definitions and modules. They can be grouped into two styles: [Positional modality systems](#positional-modalities) and [Pure modality systems](#pure-modalities). Here is the list of the modality systems in Agda:

* [Irrelevance](irrelevance.md#irrelevance), which is positional, using dot prefixes or annotations `@irr`/`@irrelevant`, `@shirr`/`@shape-irrelevant` and `@relevant`;
* [Run-time Irrelevance](runtime-irrelevance.md#runtime-irrelevance), positional, using `@0` and `@ω`;
* [Flat Modality](flat.md#flat), pure, using `@♭` and `@⊤`, although the latter can never be written explicitely by the user;
* [Polarity Annotations](polarity.md#polarity), pure, using `@++`, `@+`, `@-`, `@mixed` and `@unused`.

## General modalities[](#general-modalities "Link to this heading")

Modality systems let you add modality annotations to the domain of arrow types, and also to definitions (this includes local definitions, such as in where and let blocks).

For example, a function of type `@μ A → B` means that it uses its argument `μ`\-modally, for `μ=irr`, that means that the argument is irrelevant for the function! Annotations on a definition are a bit more complicated (and behave differently depending on the modality system), but as a first approximation, you can think of a definition `@μ f : A` to be usable only `μ`\-modally.

When a variable is bound by e.g. pattern matching, Agda remembers under which modality it is available, and checks that the variable is only used under compatible modalities: as an example, you can use a relevant variable irrelevantly, but you can’t use an irrelevant variable relevantly.

More formally, a modality system is given by:

* an ordered set of modalities, which govern how variables of different modalities can be used;
* a way to compose modalities, with a binary operation `*` that is monotone in both arguments, along with an identity modality `id` for that operation;
* a way to left-divide modalities, with an operation `\`, such that `μ ≤ δ*ν` if and only if `δ \ μ ≤ ν`.

When no annotation is specified by the user, a default modality (not always the identity) is assigned.

A variable `@μ x : A` in the context is usable if `μ ≤ id`, and for `f` a term of type `(@ν x : A) → B`, the subterm `s` in `f s` is checked with all modalities in the context left-divided by `ν`.

## Positional modality systems[](#positional-modality-systems "Link to this heading")

For positional modality systems, a definition of the form

module M Γ where
  @μ f : A

can only be used if the context has been divided by `ν` so that `ν \ μ ≤ id`, and their types would appear to the Agda user as `@μ f : Γ → A`.

Having a “boxed unboxing” for a modal system is the ability to derive `@μ unbox : @μ A → A` with `unbox x = x`. The erasure system has boxed unboxings, as well as irrelevance if [\--irrelevant-projections](https://agda.readthedocs.io/en/latest/tools/command-line-options.html#cmdoption-irrelevant-projections) is enabled.

If a positional modal system has “boxed unboxings”, then a definition such as `@μ f : A` is checked by first left-dividing the context by `μ`. This is why the following only type-checks with [\--irrelevant-projections](https://agda.readthedocs.io/en/latest/tools/command-line-options.html#cmdoption-irrelevant-projections):

module M (@irr A : Set) where
  @irr B : Set
  B = A

These modality systems are called positional because the type-checker “remembers” in what modality the current position is.

## Pure modality systems[](#pure-modality-systems "Link to this heading")

As opposed to the previous systems, in pure modality systems, a definition of the form

module M Γ where
  @μ f : A

is actually equivalent to a top-level definition of type `μ \ Γ → A`. This is why the following

module M (@unused A : Set) where
  @unused B : Set
  B = A

gives a top level definition `M.B : @mixed Set → Set`.

A top-level definition `@μ f : A` is checked by always first left-dividing the context by the modality `μ`.

Definitions can then only be used if all the implicitely applied arguments coming from the context telescope are actually available at the proper modalities. The following doesn’t type-check

module M (@++ A : Set) where
  @unused B : Set
  B = A → ⊤

  @++ C : Set
  C = B

because at the point of use of `B`, it implicitely tries to apply it to the `@++ A` present in the context, but since `B` has top-level type `@mixed Set → Set`, this doesn’t work.