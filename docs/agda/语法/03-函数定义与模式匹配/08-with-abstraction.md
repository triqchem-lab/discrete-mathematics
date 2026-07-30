> **with 抽象** · `with-abstraction`
>
> with 对中间值分类讨论、多 with、技术细节（隐藏、重写）。
>
> 🔗 原文：<https://agda.readthedocs.io/en/latest/language/with-abstraction.html>
>
> **本项目相关性**：★ 构造性证明主力工具；损益链分类、CRT 分支、不变量 case 分析大量使用 with。

---
# With-Abstraction[](#with-abstraction "Link to this heading")

With-abstraction was first introduced by Conor McBride [\[McBride2004\]](#mcbride2004) and lets you pattern match on the result of an intermediate computation by effectively adding an extra argument to the left-hand side of your function.

## [Usage](#id8)[](#usage "Link to this heading")

In the simplest case the `with` construct can be used just to discriminate on the result of an intermediate computation. For instance

filter : {A : Set} → (A → Bool) → List A → List A
filter p [] = []
filter p (x ∷ xs) with p x
filter p (x ∷ xs)    | true  = x ∷ filter p xs
filter p (x ∷ xs)    | false = filter p xs

The clause containing the with-abstraction has no right-hand side. Instead it is followed by a number of clauses with an extra argument on the left, separated from the original arguments by a vertical bar (`|`).

When the original arguments are the same in the new clauses you can use the `...` syntax:

filter : {A : Set} → (A → Bool) → List A → List A
filter p [] = []
filter p (x ∷ xs) with p x
...                  | true  = x ∷ filter p xs
...                  | false = filter p xs

In this case `...` expands to `filter p (x ∷ xs)`. There are three cases where you have to spell out the left-hand side:

* If you want to do further pattern matching on the original arguments.
* When the pattern matching on the intermediate result refines some of the other arguments (see [Dot patterns](function-definitions.md#dot-patterns)).
* To disambiguate the clauses of nested with-abstractions (see [Nested with-abstractions](#nested-with-abstractions) below).

### [Generalisation](#id9)[](#generalisation "Link to this heading")

The power of with-abstraction comes from the fact that the goal type and the type of the original arguments are generalised over the value of the scrutinee. See [Technical details](#technical-details) below for the details. This generalisation is important when you have to prove properties about functions defined using `with`. For instance, suppose we want to prove that the `filter` function above satisfies some property `P`. Starting out by pattern matching of the list we get the following (with the goal types shown in the holes)

postulate P : ∀ {A} → List A → Set
postulate p-nil : ∀ {A} → P {A} []
postulate Q : Set
postulate q-nil : Q

proof : {A : Set} (p : A → Bool) (xs : List A) → P (filter p xs)
proof p []       = {! P [] !}
proof p (x ∷ xs) = {! P (filter p (x ∷ xs) | p x) !}

In the cons case we have to prove that `P` holds for `filter p (x ∷ xs) | p x`. This is the syntax for a stuck with-abstraction—`filter` cannot reduce since we don’t know the value of `p x`. This syntax is used for printing, but is not accepted as valid Agda code. Now if we with-abstract over `p x`, but don’t pattern match on the result we get:

proof : {A : Set} (p : A → Bool) (xs : List A) → P (filter p xs)
proof p [] = p-nil
proof p (x ∷ xs) with p x
...                 | r   = {! P (filter p (x ∷ xs) | r) !}

Here the `p x` in the goal type has been replaced by the variable `r`introduced for the result of `p x`. If we pattern match on `r` the with-clauses can reduce, giving us:

proof : {A : Set} (p : A → Bool) (xs : List A) → P (filter p xs)
proof p [] = p-nil
proof p (x ∷ xs) with p x
...                 | true  = {! P (x ∷ filter p xs) !}
...                 | false = {! P (filter p xs) !}

Both the goal type and the types of the other arguments are generalised, so it works just as well if we have an argument whose type contains `filter p xs`.

proof₂ : {A : Set} (p : A → Bool) (xs : List A) → P (filter p xs) → Q
proof₂ p [] _ = q-nil
proof₂ p (x ∷ xs) H with p x
...                    | true  = {! H : P (x ∷ filter p xs) !}
...                    | false = {! H : P (filter p xs) !}

The generalisation is not limited to scrutinees in other with-abstractions. All occurrences of the term in the goal type and argument types will be generalised.

Note that this generalisation is not always type correct and may result in a (sometimes cryptic) type error. See [Ill-typed with-abstractions](#ill-typed-with-abstractions) below for more details.

### [Nested with-abstractions](#id10)[](#nested-with-abstractions "Link to this heading")

With-abstractions can be nested arbitrarily. The only thing to keep in mind in this case is that the `...` syntax applies to the closest with-abstraction. For example, suppose you want to use `...` in the definition below.

compare : Nat → Nat → Comparison
compare x y with x < y
compare x y    | false with y < x
compare x y    | false    | false = equal
compare x y    | false    | true  = greater
compare x y    | true = less

You might be tempted to replace `compare x y` with `...` in all the with-clauses as follows.

compare : Nat → Nat → Comparison
compare x y with x < y
...            | false with y < x
...                       | false = equal
...                       | true  = greater
...            | true = less    -- WRONG

This, however, would be wrong. In the last clause the `...` is interpreted as belonging to the inner with-abstraction (the whitespace is not taken into account) and thus expands to `compare x y | false | true`. In this case you have to spell out the left-hand side and write

compare : Nat → Nat → Comparison
compare x y with x < y
...            | false with y < x
...                       | false = equal
...                       | true  = greater
compare x y    | true = less

### [Simultaneous abstraction](#id11)[](#simultaneous-abstraction "Link to this heading")

You can abstract over multiple terms in a single with-abstraction. To do this you separate the terms with vertical bars (`|`).

compare : Nat → Nat → Comparison
compare x y with x < y | y < x
...            | true  | _     = less
...            | _     | true  = greater
...            | false | false = equal

In this example the order of abstracted terms does not matter, but in general it does. Specifically, the types of later terms are generalised over the values of earlier terms. For instance

postulate plus-commute : (a b : Nat) → a + b ≡ b + a
postulate P : Nat → Set

thm : (a b : Nat) → P (a + b) → P (b + a)
thm a b t with a + b | plus-commute a b
thm a b t    | ab    | eq = {! t : P ab, eq : ab ≡ b + a !}

Note that both the type of `t` and the type of the result `eq` of `plus-commute a b` have been generalised over `a + b`. If the terms in the with-abstraction were flipped around, this would not be the case. If we now pattern match on `eq` we get

thm : (a b : Nat) → P (a + b) → P (b + a)
thm a b t with   a + b  | plus-commute a b
thm a b t    | .(b + a) | refl = {! t : P (b + a) !}

and can thus fill the hole with `t`. In effect we used the commutativity proof to rewrite `a + b` to `b + a` in the type of `t`. This is such a useful thing to do that there is special syntax for it. See [Rewrite](#with-rewrite) below.

A limitation of generalisation is that only occurrences of the term that are visible at the time of the abstraction are generalised over, but more instances of the term may appear once you start filling in the right-hand side or do further matching on the left. For instance, consider the following contrived example where we need to match on the value of `f n` for the type of `q` to reduce, but we then want to apply `q` to a lemma that talks about `f n`:

postulate
  R     : Set
  P     : Nat → Set
  f     : Nat → Nat
  lemma : ∀ n → P (f n) → R

Q : Nat → Set
Q zero    = ⊥
Q (suc n) = P (suc n)

proof : (n : Nat) → Q (f n) → R
proof n q with f n
proof n ()   | zero
proof n q    | suc fn = {! q : P (suc fn) !}

Once we have generalised over `f n` we can no longer apply the lemma, which needs an argument of type `P (f n)`. To solve this problem we can add the lemma to the with-abstraction:

proof : (n : Nat) → Q (f n) → R
proof n q with f n    | lemma n
proof n ()   | zero   | _
proof n q    | suc fn | lem = lem q

In this case the type of `lemma n` (`P (f n) → R`) is generalised over `f n` so in the right-hand side of the last clause we have `q : P (suc fn)` and `lem : P (suc fn) → R`.

See [With-abstraction equality](#the-inspect-idiom) below for an alternative approach.

### [Making with-abstractions hidden and/or irrelevant](#id12)[](#making-with-abstractions-hidden-and-or-irrelevant "Link to this heading")

It is possible to add hiding and relevance annotations to withexpressions. For example:

module _ (A B : Set) (recompute : .B → .{{A}} → B) where

  _$_ : .(A → B) → .A → B
  f $ x with .{f} | .(f x) | .{{x}}
  ... | y = recompute y

This can be useful for hiding with-abstractions that you do not need to match on but that need to be abstracted over for the result to be well-typed. It can also be used to abstract over the fields of a record type with irrelevant fields, for example:

record EqualBools : Set₁ where
  field
    bool1  : Bool
    bool2  : Bool
    .same : bool1 ≡ bool2
open EqualBools

example : EqualBools → EqualBools
example x with bool1 x | bool2 x | .(same x)
...     | true  | y′ | eq′ = record { bool1 = true;  bool2 = y′; same = eq′ }
...     | false | y′ | eq′ = record { bool1 = false; bool2 = y′; same = eq′ }

### [Using underscores and variables in pattern repetition](#id13)[](#using-underscores-and-variables-in-pattern-repetition "Link to this heading")

If an ellipsis … cannot be used, the with-clause has to repeat (or refine) the patterns of the parent clause. Since Agda 2.5.3, such patterns can be replaced by underscores \_ if the variables they bind are not needed. Here is a (slightly contrived) example:

record R : Set where
  coinductive -- disallows matching
  field  f  :  Bool
         n  :  Nat

data P (r : R) : Nat → Set where
  fTrue  :  R.f r ≡ true  →  P r zero
  nSuc   :                   P r (suc (R.n r))

data Q : (b : Bool) (n : Nat) →  Set where
  true!  :             Q true zero
  suc!   :  ∀{b n}  →  Q b (suc n)

test : (r : R) {n : Nat} (p : P r n) → Q (R.f r) n
test  r  nSuc       = suc!
test  r  (fTrue p)  with  R.f r
test  _  (fTrue ())    |  false
test  _  _             |  true  = true!  -- underscore instead of (isTrue _)

Since Agda 2.5.4, patterns can also be replaced by a variable:

f : List Nat → List Nat
f [] = []
f (x ∷ xs) with f xs
f xs0 | r = ?

The variable xs0 is treated as a let-bound variable with value .x ∷ .xs (where .x : Nat and .xs : List Nat are out of scope). Since with-abstraction may change the type of variables, the instantiation of such let-bound variables are type checked again after with-abstraction.

### [Irrefutable With](#id14)[](#irrefutable-with "Link to this heading")

When a pattern is irrefutable, we can use a pattern matching `with`instead of a traditional `with` block. This gives us a lightweight syntax to make a lot of observations before using a “proper” `with`block. For a basic example of such an irrefutable pattern, see this unfolding lemma for `pred`

pred : Nat → Nat
pred zero    = zero
pred (suc n) = n

NotNull : Nat → Set
NotNull zero    = ⊥ -- false
NotNull (suc n) = ⊤ -- trivially true

pred-correct : ∀ n (pr : NotNull n) → suc (pred n) ≡ n
pred-correct n pr with suc p ← n = refl

In the above code snippet we do not need to entertain the idea that `n`could be equal to `zero`: Agda detects that the proof `pr` allows us to dismiss such a case entirely.

The patterns used in such an inversion clause can be arbitrary. We can for instance have deep patterns, e.g. projecting out the second element of a vector whose length is neither 0 nor 1:

infixr 5 _∷_
data Vec {a} (A : Set a) : Nat → Set a where
  []  : Vec A zero
  _∷_ : ∀ {n} → A → Vec A n → Vec A (suc n)

second : ∀ {n} {pr : NotNull (pred n)} → Vec A n → A
second vs with (_ ∷ v ∷ _) ← vs = v

Remember the example of [simultaneous abstraction](#simultaneous-abstraction) from above. A simultaneous rewrite / pattern matching `with` is to be understood as being nested. That is to say that the type refinements introduced by the first case analysis may be necessary to type the following ones.

In the following example, in `focusAt` we are only able to perform the `splitAt` we are interested in because we have massaged the type of the vector argument using `suc-+` first.

suc-+ : ∀ m n → suc m + n ≡ m + suc n
suc-+ zero    n                   = refl
suc-+ (suc m) n rewrite suc-+ m n = refl

infixr 1 _×_
_×_ : ∀ {a b} (A : Set a) (B : Set b) → Set _
A × B = Σ A (λ _ → B)

splitAt : ∀ m {n} → Vec A (m + n) → Vec A m × Vec A n
splitAt zero    xs       = ([] , xs)
splitAt (suc m) (x ∷ xs) with (ys , zs) ← splitAt m xs = (x ∷ ys , zs)

-- focusAt m (x₀ ∷ ⋯ ∷ xₘ₋₁ ∷ xₘ ∷ xₘ₊₁ ∷ ⋯ ∷ xₘ₊ₙ)
-- returns ((x₀ ∷ ⋯ ∷ xₘ₋₁) , xₘ , (xₘ₊₁ ∷ ⋯ ∷ xₘ₊ₙ))
focusAt : ∀ m {n} → Vec A (suc (m + n)) → Vec A m × A × Vec A n
focusAt m {n} vs rewrite suc-+ m n
                 with (before , focus ∷ after) ← splitAt m vs
                 = (before , focus , after)

You can alternate arbitrarily many `rewrite` and pattern matching `with` clauses and still perform a `with` abstraction afterwards if necessary.

### [Left-hand side let-bindings](#id15)[](#left-hand-side-let-bindings "Link to this heading")

An alternative to an irrefutable `with`, when you just need to bind a variable or do simple unpacking of record values, is to use a `using`\-binding. This is the left-hand side counterpart of a [let-binding](let-and-where.md#let-expressions) and supports the same limited form of pattern matching.

For instance, the irrefutable `with` used in `splitAt` in the section above can be changed to `using`:

splitAt : ∀ m {n} → Vec A (m + n) → Vec A m × Vec A n
splitAt zero    xs       = ([] , xs)
splitAt (suc m) (x ∷ xs) using (ys , zs) ← splitAt m xs = (x ∷ ys , zs)

Variables bound with `using` are in scope in following `with`clauses, allowing you to reuse bindings across multiple nested `with` s:

contrived : ∀ m {n} → Vec A (m + n) → (Vec A m → Bool) → (Vec A n → Bool) → Bool
contrived m xs p q using (ys , zs) ← splitAt m xs
                   with p ys
... | true = true
... | false with q zs
...   | true  = false
...   | false = true

For convenience, multiple bindings can be separated by `|`, and this has the same meaning as repeating the `using` keyword: bindings to the left are in scope to the right.

Contrary to `with` and `rewrite`, `using` does not perform any abstraction over the bound terms, but simply introduces a local binding. This can make it much cheaper to use than an irrefutable `with` in situations where the goal type and context are big and expensive to normalise, and the abstraction isn’t required.

### [Rewrite](#id16)[](#rewrite "Link to this heading")

Remember example of [simultaneous abstraction](#simultaneous-abstraction) from above.

postulate plus-commute : (a b : Nat) → a + b ≡ b + a

thm : (a b : Nat) → P (a + b) → P (b + a)
thm a b t with   a + b  | plus-commute a b
thm a b t    | .(b + a) | refl = t

This pattern of rewriting by an equation by with-abstracting over it and its left-hand side is common enough that there is special syntax for it:

thm : (a b : Nat) → P (a + b) → P (b + a)
thm a b t rewrite plus-commute a b = t

The `rewrite` construction takes a term `eq` of type `lhs ≡ rhs`, where `_≡_`is the [built-in equality type](built-ins.md#built-in-equality), and expands to a with-abstraction of `lhs` and `eq` followed by a match of the result of `eq` against `refl`:

f ps rewrite eq = v

  -->

f ps with lhs | eq
...    | .rhs | refl = v

One limitation of the `rewrite` construction is that you cannot do further pattern matching on the arguments _after_ the rewrite, since everything happens in a single clause. You can however do with-abstractions after the rewrite. For instance,

postulate T : Nat → Set

isEven : Nat → Bool
isEven zero = true
isEven (suc zero) = false
isEven (suc (suc n)) = isEven n

thm₁ : (a b : Nat) → T (a + b) → T (b + a)
thm₁ a b t rewrite plus-commute a b with isEven a
thm₁ a b t | true  = t
thm₁ a b t | false = t

Note that the with-abstracted arguments introduced by the rewrite (`lhs` and `eq`) are not visible in the code.

### [With-abstraction equality](#id17)[](#with-abstraction-equality "Link to this heading")

When you with-abstract a term `t` you lose the connection between `t` and the new argument representing its value. That’s fine as long as all instances of `t` that you care about get generalised by the abstraction, but as we saw [above](#with-on-lemma) this is not always the case. In that example we used simultaneous abstraction to make sure that we did capture all the instances we needed.

An alternative to that is to get Agda to remember in an equality proof that the patterns in the with clauses come from the expression you abstracted over. This is possible using the `in` keyword.

In the following artificial example, we try to prove that there exists two numbers such that one equals the double of the other. We start by computing the double of our input `m` and call it `n`. We can then return the nested pair containing `m`, `n`, and we now need a proof that `m + m ≡ n`. Luckily we used `in eq` when computing `n` as `m + m` and this `eq`is exactly the proof we need.

double : Nat → Σ Nat (λ m → Σ Nat (λ n → m + m ≡ n))
double m with n ← m + m in eq = m , n , eq

For a more natural example, we prove that `filter` (defined at the top of this page) is idempotent. That is to say that applying it twice to an input list is the same as only applying it once.

In the `filter-filter p (x ∷ xs)` case, abstracting over and then matching on the result of `p x` allows the first call to `filter p (x ∷ xs)` to reduce.

In case the element `x` is kept (i.e. `p x` is `true`), the second call to `filter` on the LHS goes on to performs the same `p x` test. Because we have retained the proof that `p x ≡ true` in `eq`, we are able to rewrite by this equality and get it to reduce too.

This leads to just enough computation that we can finish the proof with an appeal to congruence and the induction hypothesis.

filter-filter : ∀ {A} p (xs : List A) → filter p (filter p xs) ≡ filter p xs
filter-filter p []       = refl
filter-filter p (x ∷ xs) with p x in eq
... | false = filter-filter p xs -- easy
... | true -- second filter stuck on `p x`: rewrite by `eq`!
  rewrite eq = cong (x ∷_) (filter-filter p xs)

### [Alternatives to with-abstraction](#id18)[](#alternatives-to-with-abstraction "Link to this heading")

Although with-abstraction is very powerful there are cases where you cannot or don’t want to use it. For instance, you cannot use with-abstraction if you are inside an expression in a right-hand side. In that case there are a couple of alternatives.

#### Pattern lambdas[](#pattern-lambdas "Link to this heading")

Agda does not have a primitive `case` construct, but one can be emulated using [pattern lambdas](lambda-abstraction.md#pattern-lambda). First you define a function `case_of_` as follows:

case_of_ : ∀ {a b} {A : Set a} {B : Set b} → A → (A → B) → B
case x of f = f x

You can then use this function with a pattern lambda as the second argument to get a Haskell-style case expression:

filter : {A : Set} → (A → Bool) → List A → List A
filter p [] = []
filter p (x ∷ xs) =
  case p x of
  λ { true  → x ∷ filter p xs
    ; false → filter p xs
    }

This version of `case_of_` only works for non-dependent functions. For dependent functions the target type will in most cases not be inferrable, but you can use a variant with an explicit `B` for this case:

case_returning_of_ : ∀ {a b} {A : Set a} (x : A) (B : A → Set b) → (∀ x → B x) → B x
case x returning B of f = f x

The dependent version will let you generalise over the scrutinee, just like a with-abstraction, but you have to do it manually. Two things that it will not let you do is

* further pattern matching on arguments on the left-hand side, and
* refine arguments on the left by the patterns in the case expression. For instance if you matched on a `Vec A n` the `n` would be refined by the nil and cons patterns.

#### Helper functions[](#helper-functions "Link to this heading")

Internally with-abstractions are translated to auxiliary functions (see [Technical details](#technical-details) below) and you can always write these functions manually. The downside is that the type signature for the helper function needs to be written out explicitly, but fortunately the [Emacs Mode](https://agda.readthedocs.io/en/latest/tools/emacs-mode.html#emacs-mode) has a command (`C-c C-h`) to generate it using the same algorithm that generates the type of a with-function.

### [Termination checking](#id19)[](#termination-checking "Link to this heading")

The termination checker runs on the translated auxiliary functions, which means that some code that looks like it should pass termination checking does not. Specifically this happens in call chains like `c₁ (c₂ x) ⟶ c₁ x`where the recursive call is under a with-abstraction. The reason is that the auxiliary function only gets passed `x`, so the call chain is actually `c₁ (c₂ x) ⟶ x ⟶ c₁ x`, and the termination checker cannot see that this is terminating. For example:

data D : Set where
  [_] : Nat → D

fails : D → Nat
fails [ zero  ] = zero
fails [ suc n ] with some-stuff
... | _ = fails [ n ]

The easiest way to work around this problem is to perform a with-abstraction on the recursive call up front:

fixed : D → Nat
fixed [ zero  ] = zero
fixed [ suc n ] with fixed [ n ] | some-stuff
... | rec | _ = rec

If the function takes more arguments you might need to abstract over a partial application to just the structurally recursive argument. For instance,

fails : Nat → D → Nat
fails _ [ zero  ] = zero
fails _ [ suc n ] with some-stuff
... | m = fails m [ n ]

fixed : Nat → D → Nat
fixed _ [ zero  ] = zero
fixed _ [ suc n ] with (λ m → fixed m [ n ]) | some-stuff
... | rec | m = rec m

A possible complication is that later with-abstractions might change the type of the abstracted recursive call:

T      : D → Set
suc-T  : ∀ {n} → T [ n ] → T [ suc n ]
zero-T : T [ zero ]

fails : (d : D) → T d
fails [ zero  ] = zero-T
fails [ suc n ] with some-stuff
... | _ with [ n ]
...   | z = suc-T (fails [ n ])

Trying to abstract over the recursive call as before does not work in this case.

still-fails : (d : D) → T d
still-fails [ zero ] = zero-T
still-fails [ suc n ] with still-fails [ n ] | some-stuff
... | rec | _ with [ n ]
...   | z = suc-T rec -- Type error because rec : T z

To solve the problem you can add `rec` to the with-abstraction messing up its type. This will prevent it from having its type changed:

fixed : (d : D) → T d
fixed [ zero ] = zero-T
fixed [ suc n ] with fixed [ n ] | some-stuff
... | rec | _ with rec | [ n ]
...   | _ | z = suc-T rec

### [Performance considerations](#id20)[](#performance-considerations "Link to this heading")

The [generalisation step](#generalisation) of a with-abstraction needs to normalise the scrutinee and the goal and argument types to make sure that all instances of the scrutinee are generalised. The generalisation also needs to be type checked to make sure that it’s not [ill-typed](#ill-typed-with-abstractions). This makes it expensive to type check a with-abstraction if

* the normalisation is expensive,
* the normalised form of the goal and argument types are big, making finding the instances of the scrutinee expensive,
* type checking the generalisation is expensive, because the types are big, or because checking them involves heavy computation.

In these cases it is worth looking at the [alternatives to with-abstraction](#alternatives-to-with-abstraction)from above.

## [Technical details](#id21)[](#technical-details "Link to this heading")

Internally with-abstractions are translated to auxiliary functions—there are no with-abstractions in the [Core language](core-language.md#core-language). This translation proceeds as follows. Given a with-abstraction

![\\[\arraycolsep=1.4pt
\begin{array}{lrllcll}
  \multicolumn{3}{l}{f : \Gamma \to B} \\
  f ~ ps   & \mathbf{with} ~ & t_1 & | & \ldots & | ~ t_m \\
  f ~ ps_1 & | ~ & q_{11} & | & \ldots & | ~ q_{1m} &= v_1 \\
  \vdots \\
  f ~ ps_n & | ~ & q_{n1} & | & \ldots & | ~ q_{nm} &= v_n
\end{array}\\]](https://agda.readthedocs.io/en/latest/_images/math/674e0869e7573d55b601ba28cd9949f42655c51a.svg)

where ![\Delta \vdash ps : \Gamma](https://agda.readthedocs.io/en/latest/_images/math/c59afc4c6c8fae096d80b35d223ca17cc340f317.svg) (i.e. ![\Delta](https://agda.readthedocs.io/en/latest/_images/math/b007cd743e515e029a9bccbec37f13098326f061.svg) types the variables bound in ![ps](https://agda.readthedocs.io/en/latest/_images/math/604fb293595704a19bf6e90cb42d433504e7b062.svg)), we

* Infer the types of the scrutinees ![t_1 : A_1, \ldots, t_m : A_m](https://agda.readthedocs.io/en/latest/_images/math/f7fbfe136d6e0b47a4c11c8e6d324065b9d2baaf.svg).
* Partition the context ![\Delta](https://agda.readthedocs.io/en/latest/_images/math/b007cd743e515e029a9bccbec37f13098326f061.svg) into ![\Delta_1](https://agda.readthedocs.io/en/latest/_images/math/108826fc9a53c73c7d34e6ec621d8c4570e85138.svg) and ![\Delta_2](https://agda.readthedocs.io/en/latest/_images/math/bbca464a6bc96a775d1b41cdc7ba02f2385f9b17.svg) such that ![\Delta_1](https://agda.readthedocs.io/en/latest/_images/math/108826fc9a53c73c7d34e6ec621d8c4570e85138.svg) is the smallest context where ![\Delta_1 \vdash t_i : A_i](https://agda.readthedocs.io/en/latest/_images/math/a5da76ff792362dd544a6bbb06974947ca806cef.svg) for all ![i](https://agda.readthedocs.io/en/latest/_images/math/50e4c984ef907297b5f137fecc546c291d6d5e0f.svg), i.e., where the scrutinees are well-typed. Note that the partitioning is not required to be a split, ![\Delta_1\Delta_2](https://agda.readthedocs.io/en/latest/_images/math/dfbf7a9bb36729dd345b9d460fcbb5798a3d97be.svg) can be a (well-formed) reordering of ![\Delta](https://agda.readthedocs.io/en/latest/_images/math/b007cd743e515e029a9bccbec37f13098326f061.svg).
* Generalise over the ![t_i](https://agda.readthedocs.io/en/latest/_images/math/87de661ff5b040fa8493a5a0446648af764a98ba.svg) s, by computing  
![C = \(w_1 : A_1\)\(w_1 : A_2'\)\ldots\(w_m : A_m'\) \to \Delta_2' \to B'](https://agda.readthedocs.io/en/latest/_images/math/7e381a316fc4f86cf449c4e243846f06b9973bca.svg)  
such that the normal form of ![C](https://agda.readthedocs.io/en/latest/_images/math/4aef100b84bb52960c8fe11100fcebafa376cfa7.svg) does not contain any ![t_i](https://agda.readthedocs.io/en/latest/_images/math/87de661ff5b040fa8493a5a0446648af764a98ba.svg) and  
![A_i'\[w_1 := t_1 \ldots w_{i - 1} := t_{i - 1}\] \simeq A_i  
\(\Delta_2' \to B'\)\[w_1 := t_1 \ldots w_m := t_m\] \simeq \Delta_2 \to B](https://agda.readthedocs.io/en/latest/_images/math/5933b1446c390d5e73fe92815c2e36ebd01af92c.svg)  
where ![X \simeq Y](https://agda.readthedocs.io/en/latest/_images/math/44f6163e9f4504cb582f4ebc75a27dbafc9c7e90.svg) is equality of the normal forms of ![X](https://agda.readthedocs.io/en/latest/_images/math/22e1fc3098bd1f202213ea85675382731ce18466.svg) and ![Y](https://agda.readthedocs.io/en/latest/_images/math/c0b145d6c047be575a7e6011810c62556a6b295c.svg). The type of the auxiliary function is then ![\Delta_1 \to C](https://agda.readthedocs.io/en/latest/_images/math/c92e203a756189cff931a3a5526171fac719cbf7.svg).
* Check that ![\Delta_1 \to C](https://agda.readthedocs.io/en/latest/_images/math/c92e203a756189cff931a3a5526171fac719cbf7.svg) is type correct, which is not guaranteed (see [below](#ill-typed-with-abstractions)).
* Add a function ![f_{aux}](https://agda.readthedocs.io/en/latest/_images/math/be162c3695f0d55a788425389ebab4ef2762afd9.svg), mutually recursive with ![f](https://agda.readthedocs.io/en/latest/_images/math/62672234b9d2ac6958f5cc7d65bf2f2672bad684.svg), with the definition  
![\\[\arraycolsep=1.4pt  
\begin{array}{llll}  
  \multicolumn{4}{l}{f_{aux} : \Delta_1 \to C} \\  
  f_{aux} ~ ps_{11} & \mathit{qs}_1 & ps_{21} &= v_1 \\  
  \vdots \\  
  f_{aux} ~ ps_{1n} & \mathit{qs}_n & ps_{2n} &= v_n \\  
\end{array}\\]](https://agda.readthedocs.io/en/latest/_images/math/af1b9ea9bf7e4fb12cbf5bfed1703a96de622087.svg)  
where ![\mathit{qs}_i = q_{i1} \ldots q_{im}](https://agda.readthedocs.io/en/latest/_images/math/15570c0a8f24f431e61a655afcd94d829335f9c4.svg), and ![ps_{1i} : \Delta_1](https://agda.readthedocs.io/en/latest/_images/math/4997e15ed4d9fd319133c477a41e26ef4acac64a.svg) and ![ps_{2i} : \Delta_2](https://agda.readthedocs.io/en/latest/_images/math/4d51306b1ae01d5fcbabc9d62a311147ac5c4822.svg) are the patterns from ![ps_i](https://agda.readthedocs.io/en/latest/_images/math/3ffdd394f674e4110c9f73334b272522b92dda38.svg) corresponding to the variables of ![ps](https://agda.readthedocs.io/en/latest/_images/math/604fb293595704a19bf6e90cb42d433504e7b062.svg). Note that due to the possible reordering of the partitioning of ![\Delta](https://agda.readthedocs.io/en/latest/_images/math/b007cd743e515e029a9bccbec37f13098326f061.svg) into ![\Delta_1](https://agda.readthedocs.io/en/latest/_images/math/108826fc9a53c73c7d34e6ec621d8c4570e85138.svg) and ![\Delta_2](https://agda.readthedocs.io/en/latest/_images/math/bbca464a6bc96a775d1b41cdc7ba02f2385f9b17.svg), the patterns ![ps_{1i}](https://agda.readthedocs.io/en/latest/_images/math/ff849966a4f8e1292f7a5023df64296825d3fd6a.svg) and ![ps_{2i}](https://agda.readthedocs.io/en/latest/_images/math/ee583c6ef588a2cf0c1f52f9d868f94ca3c1bcc0.svg) can be in a different order from how they appear ![ps_i](https://agda.readthedocs.io/en/latest/_images/math/3ffdd394f674e4110c9f73334b272522b92dda38.svg).
* Replace the with-abstraction by a call to ![f_{aux}](https://agda.readthedocs.io/en/latest/_images/math/be162c3695f0d55a788425389ebab4ef2762afd9.svg) resulting in the final definition  
![\\[\arraycolsep=1.4pt  
\begin{array}{l}  
  f : \Gamma \to B \\  
  f ~ ps = f_{aux} ~ \mathit{xs}_1 ~ ts ~ \mathit{xs}_2  
\end{array}\\]](https://agda.readthedocs.io/en/latest/_images/math/cfa2494582bfb4babe29183fabba4b04955483a2.svg)  
where ![ts = t_1 \ldots t_m](https://agda.readthedocs.io/en/latest/_images/math/89182dfe36b3102144d84848503e588027eb7e68.svg) and ![\mathit{xs}_1](https://agda.readthedocs.io/en/latest/_images/math/34570bb493948d82a5756cd29c653eb57676fda4.svg) and ![\mathit{xs}_2](https://agda.readthedocs.io/en/latest/_images/math/575fe978de6d484aeb246314452238de03904e1b.svg) are the variables from ![\Delta](https://agda.readthedocs.io/en/latest/_images/math/b007cd743e515e029a9bccbec37f13098326f061.svg) corresponding to ![\Delta_1](https://agda.readthedocs.io/en/latest/_images/math/108826fc9a53c73c7d34e6ec621d8c4570e85138.svg) and ![\Delta_2](https://agda.readthedocs.io/en/latest/_images/math/bbca464a6bc96a775d1b41cdc7ba02f2385f9b17.svg) respectively.

### [Examples](#id22)[](#examples "Link to this heading")

Below are some examples of with-abstractions and their translations.

postulate
   A     : Set
   _+_   : A → A → A
   T     : A → Set
   mkT   : ∀ x → T x
   P     : ∀ x → T x → Set

-- the type A of the with argument has no free variables, so the with
-- argument will come first
f₁ : (x y : A) (t : T (x + y)) → T (x + y)
f₁ x y t with x + y
f₁ x y t    | w = {!!}

-- Generated with function
f-aux₁ : (w : A) (x y : A) (t : T w) → T w
f-aux₁ w x y t = {!!}

-- x and p are not needed to type the with argument, so the context
-- is reordered with only y before the with argument
f₂ : (x y : A) (p : P y (mkT y)) → P y (mkT y)
f₂ x y p with mkT y
f₂ x y p    | w = {!!}

f-aux₂ : (y : A) (w : T y) (x : A) (p : P y w) → P y w
f-aux₂ y w x p = {!!}

postulate
  H : ∀ x y → T (x + y) → Set

-- Multiple with arguments are always inserted together, so in this case
-- t ends up on the left since it’s needed to type h and thus x + y isn’t
-- abstracted from the type of t
f₃ : (x y : A) (t : T (x + y)) (h : H x y t) → T (x + y)
f₃ x y t h with x + y | h
f₃ x y t h    | w₁    | w₂ = {! t : T (x + y), goal : T w₁ !}

f-aux₃ : (x y : A) (t : T (x + y)) (h : H x y t) (w₁ : A) (w₂ : H x y t) → T w₁
f-aux₃ x y t h w₁ w₂ = {!!}

-- But earlier with arguments are abstracted from the types of later ones
f₄ : (x y : A) (t : T (x + y)) → T (x + y)
f₄ x y t with x + y | t
f₄ x y t    | w₁    | w₂ = {! t : T (x + y), w₂ : T w₁, goal : T w₁ !}

f-aux₄ : (x y : A) (t : T (x + y)) (w₁ : A) (w₂ : T w₁) → T w₁
f-aux₄ x y t w₁ w₂ = {!!}

-- With-abstraction equality
g : (x : A) → T x
g x with mkT x in eq
g x | w = {!!}

g-aux : (x : A) (w : T x) → mkT x ≡ w → T x
g-aux x w eq = {!!}

-- The equality argument is generalised over by further with-abstractions
g₁ : (x : A) → P x (g x)
g₁ x with mkT x in eq
g₁ x | w = {!!}

g-aux₁ : (x : A) (w : T x) (eq : mkT x ≡ w) → P x (g-aux x w eq)
g-aux₁ x w eq = {!!}

### [Ill-typed with-abstractions](#id23)[](#ill-typed-with-abstractions "Link to this heading")

As mentioned above, generalisation does not always produce well-typed results. This happens when you abstract over a term that appears in the _type_ of a subterm of the goal or argument types. The simplest example is abstracting over the first component of a dependent pair. For instance,

postulate
  A : Set
  B : A → Set
  H : (x : A) → B x → Set

bad-with : (p : Σ A B) → H (fst p) (snd p)
bad-with p with fst p
...           | _ = {!!}

Here, generalising over `fst p` results in an ill-typed application `H w (snd p)` and you get the following type error:

fst p != w of type A
when checking that the type (p : Σ A B) (w : A) → H w (snd p) of
the generated with function is well-formed

This message can be a little difficult to interpret since it only prints the immediate problem (`fst p != w`) and the full type of the with-function. To get a more informative error, pointing to the location in the type where the error is, you can copy and paste the with-function type from the error message and try to type check it separately.

\[[McBride2004](#id2)\] 

C. McBride and J. McKinna. **The view from the left**. Journal of Functional Programming, 2004\. <http://strictlypositive.org/vfl.pdf>.