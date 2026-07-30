> **语法声明** · `syntax-declarations`
>
> 为 mixfix 运算符绑定 notation（stub 文档）。
>
> 🔗 原文：<https://agda.readthedocs.io/en/latest/language/syntax-declarations.html>
>
> **本项目相关性**：自定义证明语法的辅助；与 mixfix-operators 配合。

---
# Syntax Declarations[](#syntax-declarations "Link to this heading")

Note

This is a stub

It is now possible to declare user-defined syntax that binds identifiers. Example:

record Σ (A : Set) (B : A → Set) : Set where
  constructor _,_
  field fst : A
        snd : B fst

syntax Σ A (λ x → B) = [ x ∈ A ] × B

witness : ∀ {A B} → [ x ∈ A ] × B → A
witness (x , _) = x

The syntax declaration for `Σ` implies that `x` is in scope in `B`, but not in `A`.

You can give fixity declarations along with syntax declarations:

infix 5 Σ
syntax Σ A (λ x → B) = [ x ∈ A ] × B

The fixity applies to the syntax, not the name; syntax declarations are also restricted to ordinary, non-operator names. The following declaration is disallowed:

syntax _==_ x y = x === y

Syntax declarations must also be linear; the following declaration is disallowed:

syntax wrong x = x + x

Syntax declarations can have implicit arguments. For example:

id : ∀ {a}{A : Set a} -> A -> A
id x = x

syntax id {A} x = x ∈ A

Unlike [mixfix operators](mixfix-operators.md#mixfix-operators) that can be used unapplied using the name including all the underscores, or partially applied by replacing only some of the underscores by arguments, syntax must be fully applied.