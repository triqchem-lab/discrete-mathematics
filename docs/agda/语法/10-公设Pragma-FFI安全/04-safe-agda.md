> **Safe Agda** · `safe-agda`
>
> --safe 选项禁用不安全特性（postulate 未信任、unquote 等），保证可信赖基础。
>
> 🔗 原文：<https://agda.readthedocs.io/en/latest/language/safe-agda.html>
>
> **本项目相关性**：形式化证明库应追求 --safe，但本项目临时依赖 postulate 时无法完全 safe，需记录消除计划。

---
# Safe Agda[](#safe-agda "Link to this heading")

By using the option [\--safe](https://agda.readthedocs.io/en/latest/tools/command-line-options.html#cmdoption-safe) (as a pragma option, or on the command-line), a user can specify that Agda should ensure that features leading to possible inconsistencies should be disabled.

Here is a list of the features [\--safe](https://agda.readthedocs.io/en/latest/tools/command-line-options.html#cmdoption-safe) is incompatible with:

* `postulate`; can be used to assume any axiom.
* [\--allow-unsolved-metas](https://agda.readthedocs.io/en/latest/tools/command-line-options.html#cmdoption-allow-unsolved-metas); forces Agda to accept unfinished proofs.
* [\--allow-incomplete-matches](https://agda.readthedocs.io/en/latest/tools/command-line-options.html#cmdoption-allow-incomplete-matches)and pragma [NON\_COVERING](pragmas.md#non-covering-pragma); allows to prove false using a partial function or through a partial proof.
* [\--no-positivity-check](https://agda.readthedocs.io/en/latest/tools/command-line-options.html#cmdoption-no-positivity-check)and pragmas [NO\_POSITIVITY\_CHECK](positivity-checking.md#no-positivity-check-pragma)and [POLARITY](positivity-checking.md#polarity-pragma); make it possible to write non-terminating programs via datatypes that are not strictly positive.
* [\--no-termination-check](https://agda.readthedocs.io/en/latest/tools/command-line-options.html#cmdoption-no-termination-check)and pragmas [TERMINATING](termination-checking.md#terminating-pragma)and [NON\_TERMINATING](termination-checking.md#non-terminating-pragma); give loopy programs any type.
* [\--type-in-type](https://agda.readthedocs.io/en/latest/tools/command-line-options.html#cmdoption-type-in-type) and [\--omega-in-omega](https://agda.readthedocs.io/en/latest/tools/command-line-options.html#cmdoption-omega-in-omega)and pragma [NO\_UNIVERSE\_CHECK](universe-levels.md#no-universe-check-pragma); allow the user to encode the Girard-Hurken paradox.
* pragma [INJECTIVE](pragmas.md#injective-pragma); allows to prove false by declaring a non-injective function as injective.
* [\--injective-type-constructors](https://agda.readthedocs.io/en/latest/tools/command-line-options.html#cmdoption-injective-type-constructors); together with excluded middle leads to an inconsistency via Chung-Kil Hur’s construction.
* [\--sized-types](https://agda.readthedocs.io/en/latest/tools/command-line-options.html#cmdoption-sized-types); lacks some checks that rule out improper, inconsistent uses of sizes.
* [\--experimental-irrelevance](https://agda.readthedocs.io/en/latest/tools/command-line-options.html#cmdoption-experimental-irrelevance) and [\--irrelevant-projections](https://agda.readthedocs.io/en/latest/tools/command-line-options.html#cmdoption-irrelevant-projections); enables potentially unsound irrelevance features (irrelevant levels, irrelevant data matching, and projection of irrelevant record fields, respectively).
* [\--rewriting](https://agda.readthedocs.io/en/latest/tools/command-line-options.html#cmdoption-rewriting); turns any equation into one that holds definitionally. It can at the very least break convergence.
* [\--cubical=compatible](https://agda.readthedocs.io/en/latest/tools/command-line-options.html#cmdoption-cubical) together with [\--with-K](https://agda.readthedocs.io/en/latest/tools/command-line-options.html#cmdoption-with-K); the univalence axiom is provable using cubical constructions, which falsifies the K axiom.
* [\--without-K](https://agda.readthedocs.io/en/latest/tools/command-line-options.html#cmdoption-without-K) together with [\--flat-split](https://agda.readthedocs.io/en/latest/tools/command-line-options.html#cmdoption-flat-split)
* The `primEraseEquality` primitive together with [\--without-K](https://agda.readthedocs.io/en/latest/tools/command-line-options.html#cmdoption-without-K); using `primEraseEquality`, one can derive the K axiom.
* [\--allow-exec](https://agda.readthedocs.io/en/latest/tools/command-line-options.html#cmdoption-allow-exec); allows system calls during type checking.
* [\--no-load-primitives](https://agda.readthedocs.io/en/latest/tools/command-line-options.html#cmdoption-no-load-primitives); allows the user to bind the sort and level primitives manually.
* [\--cumulativity](https://agda.readthedocs.io/en/latest/tools/command-line-options.html#cmdoption-cumulativity); due to its poor heuristic for solving universe levels.
* [\--large-indices](https://agda.readthedocs.io/en/latest/tools/command-line-options.html#cmdoption-large-indices) together with [\--without-K](https://agda.readthedocs.io/en/latest/tools/command-line-options.html#cmdoption-without-K) or [\--forced-argument-recursion](https://agda.readthedocs.io/en/latest/tools/command-line-options.html#cmdoption-forced-argument-recursion); both of these combinations are known to be inconsistent.
* pragma [COMPILE](foreign-function-interface.md#foreign-function-interface); allows to change the meaning of code during compilation.

The option [\--safe](https://agda.readthedocs.io/en/latest/tools/command-line-options.html#cmdoption-safe) is coinfective (see [Checking options for consistency](https://agda.readthedocs.io/en/latest/tools/command-line-options.html#consistency-checking-options)); if a module is declared safe, then all its imported modules must also be declared safe.