> **词法结构** · `lexical-structure`
>
> token 分类、关键字、layout（缩进）规则、literate Agda（.lagda）支持。
>
> 🔗 原文：<https://agda.readthedocs.io/en/latest/language/lexical-structure.html>
>
> **本项目相关性**：理解 layout 规则可排查缩进导致的解析错误；本项目 .lagda.rst 文档与证明混排时需注意。

---
# Lexical Structure[](#lexical-structure "Link to this heading")

Agda code is written in UTF-8 encoded plain text files with the extension `.agda`; more file extensions are supported for [Literate Programming](https://agda.readthedocs.io/en/latest/tools/literate-programming.html#literate-programming). A UTF-8 byte order mark (BOM) is ignored at the beginning of a file.

Most unicode characters can be used in identifiers, see section [Names](#names). Whitespace is important, see section [Layout](#lexical-structure-layout).

## Tokens[](#tokens "Link to this heading")

### Keywords and special symbols[](#keywords-and-special-symbols "Link to this heading")

Most non-whitespace unicode can be used as part of an Agda name, but there are two kinds of exceptions:

special symbols

Characters with special meaning that cannot appear at all in a name. These are `.;{}()@"`.

keywords

Reserved words that cannot appear as a [name part](#names), but can appear in a name together with other characters.

`=` `|` `->` `→` `:` `?` `\` `λ` [∀](function-types.md#notational-conventions) `..` `...` `abstract` `coinductive` `constructor` `data` [do](syntactic-sugar.md#do-notation) `eta-equality` `field` [forall](function-types.md#notational-conventions) `hiding` `import` `in` `inductive` `infix` `infixl` `infixr` `instance` `interleaved` `let` [macro](reflection.md#macros) `module` `mutual` `no-eta-equality` `opaque` `open` [overlap](record-types.md#instance-fields) `pattern` `postulate` `primitive` `private` `public` [quote](reflection.md#reflection) [quoteTerm](reflection.md#macros) `record` `renaming` `rewrite` `syntax` `tactic` `unfolding` [unquote](reflection.md#macros) [unquoteDecl](reflection.md#unquoting-declarations) [unquoteDef](reflection.md#unquoting-declarations) `using` [variable](generalization-of-declared-variables.md#generalization-of-declared-variables) `where` `with`

keywords in `renaming` directives

The word `to` is only reserved in `renaming` directives.

keywords in `import` statements

The word `as` has a special meaning in `import` statements, although it is not reserved.

### Names[](#names "Link to this heading")

A qualified name is a non-empty sequence of names separated by dots (`.`). A name is an alternating sequence of name parts and underscores (`_`), containing at least one name part. A name partis a non-empty sequence of unicode characters, excluding whitespace, `_`, and [special symbols](#keywords-and-special-symbols). A name part cannot be one of the [keywords](#keywords-and-special-symbols) above, and cannot start with a single quote, `'` (which are used for character literals, see [Literals](#literals) below).

Examples

* Valid: `data?`, `::`, `if_then_else_`, `0b`, `_⊢_∈_`, `x=y`
* Invalid: `data_?`, `foo__bar`, `_`, `a;b`, `[_.._]`

The underscores in a name indicate where the arguments go when the name is used as an operator. For instance, the application `_+_ 1 2` can be written as `1 + 2`. See [Mixfix Operators](mixfix-operators.md#mixfix-operators) for more information. Since most sequences of characters are valid names, whitespace is more important than in other languages. In the example above the whitespace around `+` is required, since `1+2` is a valid name.

Qualified names are used to refer to entities defined in other modules. For instance `Prelude.Bool.true` refers to the name `true` defined in the module `Prelude.Bool`. See [Module System](module-system.md#module-system) for more information.

### Literals[](#literals "Link to this heading")

There are four types of literal values: integers, floats, characters, and strings. See [Built-ins](built-ins.md#built-ins) for the corresponding types, and [Literal Overloading](literal-overloading.md#literal-overloading) for how to support literals for user-defined types.

Integers

Integer values in decimal, hexadecimal (prefixed by `0x`), or binary (prefixed by `0b`) notation. The character \_ can be used to separate groups of digits. Non-negative numbers map by default to [built-in natural numbers](built-ins.md#built-in-nat), but can be overloaded. Negative numbers have no default interpretation and can only be used through [overloading](literal-overloading.md#literal-overloading).

Examples: `123`, `0xF0F080`, `-42`, `-0xF`, `0b11001001`, `1_000_000_000`, `0b01001000_01001001`.

Floats

Floating point numbers in the standard notation (with square brackets denoting optional parts):

float    ::= [-] decimal . decimal [exponent]
           | [-] decimal exponent
exponent ::= (e | E) [+ | -] decimal

These map to [built-in floats](built-ins.md#built-in-float) and cannot be overloaded.

Examples: `1.0`, `-5.0e+12`, `1.01e-16`, `4.2E9`, `50e3`.

Characters

Character literals are enclosed in single quotes (`'`). They can be a single (unicode) character, other than `'` or `\`, or an escaped character. Escaped characters start with a backslash `\` followed by an escape code. Escape codes are natural numbers in decimal or hexadecimal (prefixed by `x`) between `0` and `0x10ffff` (`1114111`), or one of the following special escape codes:

| Code | ASCII | Code | ASCII | Code | ASCII | Code | ASCII |
| ---- | ----- | ---- | ----- | ---- | ----- | ---- | ----- |
| a    | 7     | b    | 8     | t    | 9     | n    | 10    |
| v    | 11    | f    | 12    | \\   | \\    | '    | '     |
| "    | "     | NUL  | 0     | SOH  | 1     | STX  | 2     |
| ETX  | 3     | EOT  | 4     | ENQ  | 5     | ACK  | 6     |
| BEL  | 7     | BS   | 8     | HT   | 9     | LF   | 10    |
| VT   | 11    | FF   | 12    | CR   | 13    | SO   | 14    |
| SI   | 15    | DLE  | 16    | DC1  | 17    | DC2  | 18    |
| DC3  | 19    | DC4  | 20    | NAK  | 21    | SYN  | 22    |
| ETB  | 23    | CAN  | 24    | EM   | 25    | SUB  | 26    |
| ESC  | 27    | FS   | 28    | GS   | 29    | RS   | 30    |
| US   | 31    | SP   | 32    | DEL  | 127   |      |       |

Character literals map to the [built-in character type](built-ins.md#built-in-char) and cannot be overloaded.

Examples: `'A'`, `'∀'`, `'\x2200'`, `'\ESC'`, `'\32'`, `'\n'`, `'\''`, `'"'`.

Strings

String literals are sequences of, possibly escaped, characters enclosed in double quotes `"`. They follow the same rules as [character literals](#characters) except that double quotes `"` need to be escaped rather than single quotes `'`. String literals map to the [built-in string type](built-ins.md#built-in-string) by default, but can be [overloaded](literal-overloading.md#overloaded-strings).

Example: `"Привет \"мир\"\n"`.

### Holes[](#holes "Link to this heading")

Holes are an integral part of the interactive development supported by the [Emacs mode](https://agda.readthedocs.io/en/latest/tools/emacs-mode.html#emacs-mode). Any text enclosed in `{!` and `!}` is a hole and may contain nested holes. A hole with no contents can be written `?`. There are a number of Emacs commands that operate on the contents of a hole. The type checker ignores the contents of a hole and treats it as an unknown (see [Implicit Arguments](implicit-arguments.md#implicit-arguments)).

Example: `{! f {!x!} 5 !}`

### Comments[](#comments "Link to this heading")

Single-line comments are written with a double dash `--` followed by arbitrary text. Multi-line comments are enclosed in `{-` and `-}`and can be nested. Comments cannot appear in [string literals](#lexical-structure-string-literals).

Example:

{- Here is a {- nested -}
   comment -}
s : String --line comment {-
s = "{- not a comment -}"

### Pragmas[](#pragmas "Link to this heading")

Pragmas are special comments enclosed in `{-#` and `#-}` that have special meaning to the system. See [Pragmas](pragmas.md#pragmas) for a full list of pragmas.

## Layout[](#layout "Link to this heading")

Agda is layout sensitive using similar rules as Haskell, with the exception that layout is mandatory: you cannot use explicit `{`, `}` and `;` to avoid it.

A layout block contains a sequence of statements and is started by one of the layout keywords:

abstract
constructor
do
field
instance
let
macro
mutual
opaque
postulate
primitive
private
variable
where

The first token after the layout keyword decides the indentation of the block. Any token indented more than this is part of the previous statement, a token at the same level starts a new statement, and a token indented less lies outside the block.

data Nat : Set where -- starts a layout block
    -- comments are not tokens
  zero : Nat      -- statement 1
  suc  : Nat →    -- statement 2
         Nat      -- also statement 2

one : Nat -- outside the layout block
one = suc zero

Note that the indentation of the layout keyword does not matter.

If several layout blocks are started by layout keywords without line break in between (where line breaks inside block comments do not count), then those blocks indented _more_ than the last block go passive, meaning they cannot be further extended by new statements:

private module M where postulate
          A : Set                 -- module-block goes passive
          B : Set                 -- postulate-block can still be extended
        module N where            -- private-block can still be extended

An Agda file contains one top-level layout block, with the special rule that the contents of the top-level module need not be indented.

module Example where
NotIndented : Set₁
NotIndented = Set

## Literate Agda[](#literate-agda "Link to this heading")

Agda supports [literate programming](https://en.wikipedia.org/wiki/Literate%5Fprogramming) with multiple typesetting tools like LaTeX, Markdown and reStructuredText. For instance, with LaTeX, everything in a file is a comment unless enclosed in `\begin{code}`, `\end{code}`. Literate Agda files have special file extensions, like `.lagda` and `.lagda.tex` for LaTeX, `.lagda.md` for Markdown, `.lagda.rst` for reStructuredText instead of `.agda`. One use case for literate Agda files is to generate documents including Agda code. See [Generating HTML](https://agda.readthedocs.io/en/latest/tools/generating-html.html#generating-html) and [Generating LaTeX](https://agda.readthedocs.io/en/latest/tools/generating-latex.html#generating-latex) for more information.

\documentclass{article}
% some preamble stuff
\begin{document}
Introduction usually goes here
\begin{code}
module MyPaper where
  open import Prelude
  five : Nat
  five = 2 + 3
\end{code}
Now, conclusions!
\end{document}