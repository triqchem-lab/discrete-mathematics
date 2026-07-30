> **公设** · `postulates`
>
> postulate 声明外部假设的项/类型，含 postulated built-ins 与局部 postulate 用法。
>
> 🔗 原文：<https://agda.readthedocs.io/en/latest/language/postulates.html>
>
> **本项目相关性**：本项目目标 0 postulate，但宪法承认 postulate 是声明「外部已知事实」的合法过渡手段（如 fromℕ 隐式绑定问题），最终需在消除计划中。

---
# Postulates[](#postulates "Link to this heading")

A postulate is a declaration of an element of some type without an accompanying definition. With postulates we can introduce elements in a type without actually giving the definition of the element itself.

The general form of a postulate declaration is as follows:

postulate
    c11 ... c1i : <Type>
    ...
    cn1 ... cnj : <Type>

Postulate blocks can include `instance` and `private` declarations.

Example for a basic postulate block:

postulate
  A B    : Set
  a      : A
  b      : B
  _=AB=_ : A → B → Set
  a==b   : a =AB= b

Introducing postulates is in general not recommended. Once postulates are introduced the consistency of the whole development is at risk, because there is nothing that prevents us from introducing an element in the empty set.

data False : Set where

postulate bottom : False

Postulates are forbidden in [Safe Agda](safe-agda.md#safe-agda) (option [\--safe](https://agda.readthedocs.io/en/latest/tools/command-line-options.html#cmdoption-safe)) to prevent accidential inconsistencies.

A preferable way to work with assumptions is to define a module parametrised by the elements we need:

module Absurd (bt : False) where

  -- ...

module M (A B : Set) (a : A) (b : B)
         (_=AB=_ : A → B → Set) (a==b : a =AB= b) where

  -- ...

## Postulated built-ins[](#postulated-built-ins "Link to this heading")

Some [built-ins](built-ins.md#built-ins) such as Float and Char are introduced as a postulate and then given a meaning by the corresponding `{-# BUILTIN ... #-}` pragma.

## Local uses of `postulate`[](#local-uses-of-postulate "Link to this heading")

Postulates are declarations and can appear in positions where arbitrary declarations are allowed, e.g., in `where` blocks:

module PostulateInWhere where

  my-theorem : (A : Set) → A
  my-theorem A = I-prove-this-later
    where
      postulate I-prove-this-later : _