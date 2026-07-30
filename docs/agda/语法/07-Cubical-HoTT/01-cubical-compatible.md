> **Cubical 兼容模式** · `cubical-compatible`
>
> --cubical-compatible（即 --without-K 的增强）使普通模式匹配代码可被 Cubical 理论解释，保留 univalence 语义。
>
> 🔗 原文：<https://agda.readthedocs.io/en/latest/language/cubical-compatible.html>
>
> **本项目相关性**：本项目混合使用 Cubical 与普通归纳类型时，应确保关键模块可兼容，避免 K 公理破坏 univalence。

---
# Cubical compatible[](#cubical-compatible "Link to this heading")

The option [\--cubical=compatible](https://agda.readthedocs.io/en/latest/tools/command-line-options.html#cmdoption-cubical) specifies whether the module being type-checked is compatible with Cubical Agda: modules without this flag can not be imported from [\--cubical](https://agda.readthedocs.io/en/latest/tools/command-line-options.html#cmdoption-cubical) modules.

Note

Prior to Agda 2.6.3, the [\--cubical=compatible](https://agda.readthedocs.io/en/latest/tools/command-line-options.html#cmdoption-cubical) flag did not exist, and [\--without-K](https://agda.readthedocs.io/en/latest/tools/command-line-options.html#cmdoption-without-K) also implied the (internal) generation of Cubical Agda-specific code. See [Agda issue #5843](https://github.com/agda/agda/issues/5843) for the rationale behind this change.

Compatibility with Cubical Agda consists of:

* No reasoning principles incompatible with univalent type theory may be used. This behaviour is controlled by the [Without K](without-k.md#without-k)flag ([\--without-K](https://agda.readthedocs.io/en/latest/tools/command-line-options.html#cmdoption-without-K)), which [\--cubical=compatible](https://agda.readthedocs.io/en/latest/tools/command-line-options.html#cmdoption-cubical) implies.
* Due to specifics of the Cubical Agda implementation, several kinds of Agda definition need internal support code to be generated during their elaboration.

Occasionally, elaborator bugs can result in errors surfacing from these internal definitions, despite the code being type-correct. To avoid showing errors mentioning cubical definitions when the user-written code is independent of Cubical Agda, these internal definitions are now gated behind [\--cubical=compatible](https://agda.readthedocs.io/en/latest/tools/command-line-options.html#cmdoption-cubical).

Note that code that uses (only) [\--without-K](https://agda.readthedocs.io/en/latest/tools/command-line-options.html#cmdoption-without-K) can not be imported from code that uses [\--cubical](https://agda.readthedocs.io/en/latest/tools/command-line-options.html#cmdoption-cubical). Thus library developers are encouraged to use [\--cubical=compatible](https://agda.readthedocs.io/en/latest/tools/command-line-options.html#cmdoption-cubical) instead of [\--without-K](https://agda.readthedocs.io/en/latest/tools/command-line-options.html#cmdoption-without-K), if possible.

Note also that Agda tends to be quite a bit faster if [\--without-K](https://agda.readthedocs.io/en/latest/tools/command-line-options.html#cmdoption-without-K)is used instead of [\--cubical=compatible](https://agda.readthedocs.io/en/latest/tools/command-line-options.html#cmdoption-cubical).

The [\--cubical=compatible](https://agda.readthedocs.io/en/latest/tools/command-line-options.html#cmdoption-cubical) option is coinfective (see [Checking options for consistency](https://agda.readthedocs.io/en/latest/tools/command-line-options.html#consistency-checking-options)): the generated support code for functions may depend on those of importing modules.