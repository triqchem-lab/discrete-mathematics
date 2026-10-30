{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Algebra.Complexity.CNF-Tseitin
-- Tseitin 拆分：长子句 ⟹ 等可满足的 ≤3-子句组 —— Cook–Levin 前置 M1b
--
-- 【要解决的问题】tableau 会产生 4–7 文字的子句（见 CNF.agda 头注），而目标族是
-- 3-CNF。一个 n 文字的子句 `l₁ ∨ … ∨ lₙ` 用 n−3 个**辅助变元**拆成 n−2 条 3-子句：
--
--     (l₁ ∨ l₂ ∨ ¬x₁) ∧ (x₁ ∨ l₃ ∨ ¬x₂) ∧ … ∧ (x_{n−3} ∨ l_{n−1} ∨ lₙ)
--
-- 双向都成立（§4 回向、§5 前向），子句数 ≤ 辅助数 + 1（§3 计数）。
--
-- 【关键设计：在**同一池**内拆分】辅助变元不新开池位，而由调用方以数据给出
-- （`xs : List (Fin (suc m))`），配两条假设：
--   · `FreshAll xs cl` —— 每个辅助变元都不出现在 `cl` 里；
--   · `Distinct xs`     —— 辅助变元两两不同。
-- 于是「池扩张」（Fin 号 ⟹ 更大的 suc m、赋值前缀一致）**整块消失**：等可满足性
-- 在同一 `Asg m` 上陈述，证明里没有一处池/长度算术。池扩张留给调用方（M3/M4 构造
-- tableau 时一次性选定池）——这是「布局 ≠ 接口」的同一条口径。
--
-- 【语义提醒】本库赋值是 {T₀,T₁,T₂} 三值：`T₁ = +1`、`T₂ = −1`、`T₀ = 0/未定`；
-- 文字 `(σ₊,v)` 真 ⟺ `a[v] = T₁`、`(σ₋,v)` 真 ⟺ `a[v] = T₂`（`negate` 是符号翻转）。
-- 所以辅助变元的「真/假」都能表达（T₁/T₂），而 T₀ 使 `x` 与 `¬x` **同时不真**——
-- 回向的第三案正是这一情形（§4）。
--
-- 分级约定：〔结构定义〕/〔结构证明〕/〔refl 枚举〕/〔立界注记〕（同 TimeBound）。
-- 0 postulate / 0 hole。

module Sovereign.Algebra.Complexity.CNF-Tseitin where

open import Data.Nat using (ℕ; zero; suc; _+_; _≤_; s≤s; z≤n)
open import Data.Bool using (Bool; true; false; _∨_; _∧_)
open import Data.Bool.Properties using (∨-identityʳ)
open import Data.List using (List; []; _∷_; length; map)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.Vec using (lookup; updateAt) renaming ([] to vNil; _∷_ to _v∷_)
open import Data.Vec.Properties using (lookup∘updateAt; lookup∘updateAt′)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂)

open import Sovereign.Base.Trit using (Trit; T₀; T₁; T₂; negate)
open import Sovereign.Algebra.Complexity.SATMember
  using (Sign; σ₊; σ₋; Lit; Asg; evalLit; isT₁)
open import Sovereign.Algebra.Complexity.CNF
  using (Clause'; Formula'; satLit'; satClause'; satFormula')

-- ────────────────────────────────────────────────────────────────────
-- §0 Bool 小工具〔refl 枚举 + 2 案〕
-- ────────────────────────────────────────────────────────────────────

∨-trueʳ : ∀ (b : Bool) → (b ∨ true) ≡ true
∨-trueʳ true  = refl
∨-trueʳ false = refl

-- 前两文字已够真 ⟹ 再补文字仍真
∨-extend : ∀ (b c d : Bool) → (b ∨ c) ≡ true → (b ∨ (c ∨ d)) ≡ true
∨-extend true  c d h = refl
∨-extend false c d h = trans (cong (_∨ d) h) refl

Bool-⊥ : false ≡ true → ⊥
Bool-⊥ ()

∧-trueˡ : ∀ {b₁ b₂ : Bool} → (b₁ ∧ b₂) ≡ true → b₁ ≡ true
∧-trueˡ {true}  h = refl
∧-trueˡ {false} h = ⊥-elim (Bool-⊥ h)

∧-trueʳ : ∀ {b₁ b₂ : Bool} → (b₁ ∧ b₂) ≡ true → b₂ ≡ true
∧-trueʳ {true}  h = h
∧-trueʳ {false} h = ⊥-elim (Bool-⊥ h)

-- ────────────────────────────────────────────────────────────────────
-- §1 变元集、新鲜性、互异性〔结构定义 + 投影引理〕
-- ────────────────────────────────────────────────────────────────────

_∈ᶠ_ : ∀ {n} → Fin n → List (Fin n) → Set
x ∈ᶠ []       = ⊥
x ∈ᶠ (y ∷ ys) = (x ≡ y) ⊎ (x ∈ᶠ ys)

-- 子句里出现的变元号（正负文字同属一个变元）
vars : ∀ {m} → Clause' m → List (Fin (suc m))
vars = map proj₂

Fresh : ∀ {m} (x : Fin (suc m)) (cl : Clause' m) → Set
Fresh x cl = (x ∈ᶠ vars cl) → ⊥

FreshAll : ∀ {m} → List (Fin (suc m)) → Clause' m → Set
FreshAll xs cl = ∀ x → x ∈ᶠ xs → Fresh x cl

Distinct : ∀ {n} → List (Fin n) → Set
Distinct []       = ⊤
Distinct (x ∷ xs) = ((x ∈ᶠ xs) → ⊥) × Distinct xs

∈ᶠ-here : ∀ {n} {x y : Fin n} {ys} → x ≡ y → x ∈ᶠ (y ∷ ys)
∈ᶠ-here = inj₁

∈ᶠ-there : ∀ {n} {x y : Fin n} {ys} → x ∈ᶠ ys → x ∈ᶠ (y ∷ ys)
∈ᶠ-there = inj₂

subst-mem : ∀ {n} {a b : Fin n} {xs : List (Fin n)} → a ≡ b → (a ∈ᶠ xs) → (b ∈ᶠ xs)
subst-mem refl p = p

Fresh-head≢ : ∀ {m} {x : Fin (suc m)} {l : Lit m} {rest : Clause' m}
            → Fresh x (l ∷ rest) → (x ≡ proj₂ l) → ⊥
Fresh-head≢ {l = l} h q = h (∈ᶠ-here q)

Fresh-tail : ∀ {m} {x : Fin (suc m)} {l : Lit m} {rest : Clause' m}
           → Fresh x (l ∷ rest) → Fresh x rest
Fresh-tail h = λ p → h (∈ᶠ-there p)

FreshAll-head : ∀ {m} {x : Fin (suc m)} {xs} {cl : Clause' m}
              → FreshAll (x ∷ xs) cl → Fresh x cl
FreshAll-head h = h _ (∈ᶠ-here refl)

FreshAll-tail : ∀ {m} {x : Fin (suc m)} {xs} {cl : Clause' m}
              → FreshAll (x ∷ xs) cl → FreshAll xs cl
FreshAll-tail h = λ y p → h y (∈ᶠ-there p)

Distinct-head : ∀ {n} {x : Fin n} {xs} → Distinct (x ∷ xs) → (x ∈ᶠ xs) → ⊥
Distinct-head = proj₁

Distinct-tail : ∀ {n} {x : Fin n} {xs} → Distinct (x ∷ xs) → Distinct xs
Distinct-tail = proj₂

-- 新鲜性搬移（一）：去掉子句的首两个文字
freshAll-rest : ∀ {m} {xs} {l₁ l₂ : Lit m} {rest : Clause' m}
              → FreshAll xs (l₁ ∷ l₂ ∷ rest) → FreshAll xs rest
freshAll-rest h y p = λ q → h y p (∈ᶠ-there (∈ᶠ-there q))

-- 新鲜性搬移（二）：续跑子句 `(σ₊,x) ∷ rest`（x 本身从互异性拿到，不靠新鲜性）
freshAll-extend : ∀ {m} {xs : List (Fin (suc m))} {x : Fin (suc m)} {rest : Clause' m}
                → FreshAll xs rest → Distinct (x ∷ xs)
                → FreshAll xs ((σ₊ , x) ∷ rest)
freshAll-extend {xs = xs} hF hD y y∈xs (inj₁ q) = Distinct-head hD (subst-mem q y∈xs)
freshAll-extend {x = x}  hF hD y y∈xs (inj₂ p) = hF y y∈xs p

-- ────────────────────────────────────────────────────────────────────
-- §2 赋值一致性
-- ────────────────────────────────────────────────────────────────────

-- 只改一个不出现的变元：单文字真值不变（两种符号各一条）
satLit'-agree : ∀ {m} (a : Asg m) (x : Fin (suc m)) (u : Trit) (l : Lit m)
              → ((x ≡ proj₂ l) → ⊥)
              → satLit' (updateAt a x (λ _ → u)) l ≡ satLit' a l
satLit'-agree a x u (σ₊ , v) h = cong isT₁ (lookup∘updateAt′ v x (λ p → h (sym p)) a)
satLit'-agree a x u (σ₋ , v) h =
  cong (λ z → isT₁ (negate z)) (lookup∘updateAt′ v x (λ p → h (sym p)) a)

satClause'-agree1 : ∀ {m} (cl : Clause' m) (a : Asg m) (x : Fin (suc m)) (u : Trit)
                  → Fresh x cl
                  → satClause' (updateAt a x (λ _ → u)) cl ≡ satClause' a cl
satClause'-agree1 []         a x u h = refl
satClause'-agree1 (l ∷ rest) a x u h =
  cong₂ _∨_ (satLit'-agree a x u l (Fresh-head≢ {l = l} {rest = rest} h))
            (satClause'-agree1 rest a x u (λ q → h (∈ᶠ-there q)))

-- 两个赋值在某文字的变元上取值相同 ⟹ 该文字真值相同
satLit'-cong : ∀ {m} (a a′ : Asg m) (l : Lit m)
             → lookup a′ (proj₂ l) ≡ lookup a (proj₂ l)
             → satLit' a′ l ≡ satLit' a l
satLit'-cong a a′ (σ₊ , v) h = cong isT₁ h
satLit'-cong a a′ (σ₋ , v) h = cong (λ z → isT₁ (negate z)) h

-- 子句级：在子句全部变元上取值一致 ⟹ 真值相同
satClause'-cong : ∀ {m} (cl : Clause' m) (a a′ : Asg m)
                → (∀ v → (v ∈ᶠ vars cl) → lookup a′ v ≡ lookup a v)
                → satClause' a′ cl ≡ satClause' a cl
satClause'-cong []         a a′ h = refl
satClause'-cong (l ∷ rest) a a′ h =
  cong₂ _∨_ (satLit'-cong a a′ l (h (proj₂ l) (∈ᶠ-here refl)))
            (satClause'-cong rest a a′ (λ v p → h v (∈ᶠ-there p)))

-- ────────────────────────────────────────────────────────────────────
-- §3 拆分函数、计数、子句真值形
-- ────────────────────────────────────────────────────────────────────
-- 每步吃掉前两个文字、把辅助变元放到续跑子句最前面：
--   (l₁ ∨ l₂ ∨ ¬x)  ∥  x ∷ rest
-- xs 用尽时剩下的子句原样作为最后一条（恰好 3 文字时正是标准 Tseitin）。

tseitin-split : ∀ {m} → List (Fin (suc m)) → Clause' m → Formula' m
tseitin-split []       cl               = cl ∷ []
tseitin-split (x ∷ xs) []               = [] ∷ []
tseitin-split (x ∷ xs) (l ∷ [])        = (l ∷ []) ∷ []
tseitin-split (x ∷ xs) (l₁ ∷ l₂ ∷ rest) =
  (l₁ ∷ l₂ ∷ (σ₋ , x) ∷ []) ∷ tseitin-split xs ((σ₊ , x) ∷ rest)

-- 子句数 ≤ 辅助数 + 1（线性上界，不依赖子句长的精确形态）
tseitin-split-len : ∀ {m} (xs : List (Fin (suc m))) (cl : Clause' m)
           → length (tseitin-split xs cl) ≤ (length xs + 1)
tseitin-split-len []       cl               = s≤s z≤n
tseitin-split-len (x ∷ xs) (l₁ ∷ l₂ ∷ rest) = s≤s (tseitin-split-len xs ((σ₊ , x) ∷ rest))
tseitin-split-len (x ∷ xs) []               = s≤s z≤n
tseitin-split-len (x ∷ xs) (l ∷ [])         = s≤s z≤n

-- 抹掉尾端 `∨ false`
satClause'-2lit : ∀ {m} (a : Asg m) (l₁ l₂ : Lit m)
                → satClause' a (l₁ ∷ l₂ ∷ []) ≡ (satLit' a l₁ ∨ satLit' a l₂)
satClause'-2lit a l₁ l₂ = cong (satLit' a l₁ ∨_) (∨-identityʳ (satLit' a l₂))

satClause'-3lit : ∀ {m} (a : Asg m) (l₁ l₂ l₃ : Lit m)
                → satClause' a (l₁ ∷ l₂ ∷ l₃ ∷ [])
                  ≡ (satLit' a l₁ ∨ (satLit' a l₂ ∨ satLit' a l₃))
satClause'-3lit a l₁ l₂ l₃ =
  cong (satLit' a l₁ ∨_) (cong (satLit' a l₂ ∨_) (∨-identityʳ (satLit' a l₃)))

-- ────────────────────────────────────────────────────────────────────
-- §4 回向：拆分式可满足 ⟹ 原句可满足（**同一赋值**，不需要新鲜性）
-- ────────────────────────────────────────────────────────────────────
-- 合取两半皆真 + 对辅助取值 3 案（Trit 固有的 3 案，不是穷举）：
--   T₁ ⟹ x 真（用「前两文字」那半）；T₂ ⟹ ¬x 真（用续跑那半）；
--   T₀ ⟹ x 与 ¬x 同时不真 ⟹ 同样只能靠「前两文字」。

tseitin-split-step-sound : ∀ (bx : Trit) (b₁ b₂ R : Bool)
                  → (b₁ ∨ (b₂ ∨ isT₁ (negate bx))) ≡ true
                  → (isT₁ bx ∨ R) ≡ true
                  → (b₁ ∨ (b₂ ∨ R)) ≡ true
tseitin-split-step-sound T₁ b₁ b₂ R h₁ h₂ =
  ∨-extend b₁ b₂ R (trans (cong (b₁ ∨_) (sym (∨-identityʳ b₂))) h₁)
tseitin-split-step-sound T₂ b₁ b₂ R h₁ h₂ =
  trans (cong (b₁ ∨_) (trans (cong (b₂ ∨_) h₂) (∨-trueʳ b₂))) (∨-trueʳ b₁)
tseitin-split-step-sound T₀ b₁ b₂ R h₁ h₂ =
  ∨-extend b₁ b₂ R (trans (cong (b₁ ∨_) (sym (∨-identityʳ b₂))) h₁)

tseitin-split-sound : ∀ {m} (xs : List (Fin (suc m))) (cl : Clause' m) (a : Asg m)
             → satFormula' a (tseitin-split xs cl) ≡ true
             → satClause' a cl ≡ true
tseitin-split-sound []       cl a h = ∧-trueˡ h
tseitin-split-sound (x ∷ xs) (l₁ ∷ l₂ ∷ rest) a h =
  tseitin-split-step-sound (lookup a x) (satLit' a l₁) (satLit' a l₂) (satClause' a rest)
    (trans (sym (satClause'-3lit a l₁ l₂ (σ₋ , x))) (∧-trueˡ h))
    (tseitin-split-sound xs ((σ₊ , x) ∷ rest) a (∧-trueʳ h))
tseitin-split-sound (x ∷ xs) []       a h = ⊥-elim (Bool-⊥ h)
tseitin-split-sound (x ∷ xs) (l ∷ []) a h = ∧-trueˡ h

-- ────────────────────────────────────────────────────────────────────
-- §5 前向：原句可满足 ⟹ 拆分式可满足（构造辅助取值）
-- ────────────────────────────────────────────────────────────────────

-- 纯 Bool/Trit：给定 `b₁ ∨ (b₂ ∨ R)`，选 u 使两半皆真
-- （`false false` 支：`h` 已归约为 `R ≡ true`，取 u = T₂ 使 ¬x 真、x 假）
split-choice : ∀ (b₁ b₂ R : Bool) → (b₁ ∨ (b₂ ∨ R)) ≡ true
             → Σ Trit (λ u → ((b₁ ∨ (b₂ ∨ isT₁ (negate u))) ≡ true)
                              × ((isT₁ u ∨ R) ≡ true))
split-choice true  b₂ R h = T₁ , refl , refl
split-choice false true  R h = T₁ , refl , refl
split-choice false false R h = T₂ , refl , h

-- `cl3` 的三个变元都不在辅助表里：v₁/v₂ 靠新鲜性、x 靠互异性
clause3-vars-not-in :
    ∀ {m} {xs : List (Fin (suc m))} {l₁ l₂ : Lit m} {x : Fin (suc m)} {rest : Clause' m}
    → FreshAll xs (l₁ ∷ l₂ ∷ rest) → Distinct (x ∷ xs)
    → ∀ v → (v ∈ᶠ vars (l₁ ∷ l₂ ∷ (σ₋ , x) ∷ [])) → (v ∈ᶠ xs) → ⊥
clause3-vars-not-in {l₁ = l₁} hF hD v (inj₁ q) inXs =
  hF (proj₂ l₁) (subst-mem q inXs) (∈ᶠ-here refl)
clause3-vars-not-in {l₂ = l₂} hF hD v (inj₂ (inj₁ q)) inXs =
  hF (proj₂ l₂) (subst-mem q inXs) (∈ᶠ-there (∈ᶠ-here refl))
clause3-vars-not-in {x = x} hF hD v (inj₂ (inj₂ (inj₁ q))) inXs =
  Distinct-head hD (subst-mem q inXs)
clause3-vars-not-in hF hD v (inj₂ (inj₂ (inj₂ p))) inXs = ⊥-elim p

-- ★ 前向主引理：只动 xs 里的变元，就能把「满足 cl」改造成「满足 tseitin-split xs cl」；
--   并且新赋值与旧赋值**只在 xs 上可能不同**（这条让外层子句不受内层改动影响）。
tseitin-split-complete : ∀ {m} (xs : List (Fin (suc m))) (cl : Clause' m) (a : Asg m)
                → Distinct xs → FreshAll xs cl
                → satClause' a cl ≡ true
                → Σ (Asg m) (λ a′ → (satFormula' a′ (tseitin-split xs cl) ≡ true)
                                  × (∀ v → ((v ∈ᶠ xs) → ⊥) → lookup a′ v ≡ lookup a v))
tseitin-split-complete [] cl a hD hF h =
  a , (trans (cong (_∧ true) h) refl) , (λ v nv → refl)
tseitin-split-complete {m} (x ∷ xs) (l₁ ∷ l₂ ∷ rest) a hD hF h = a₂ , assembled , agree
  where
  sc : Σ Trit (λ u → ((satLit' a l₁ ∨ (satLit' a l₂ ∨ isT₁ (negate u))) ≡ true)
                     × ((isT₁ u ∨ satClause' a rest) ≡ true))
  sc = split-choice (satLit' a l₁) (satLit' a l₂) (satClause' a rest) h

  u : Trit
  u = proj₁ sc

  hu₁ : (satLit' a l₁ ∨ (satLit' a l₂ ∨ isT₁ (negate u))) ≡ true
  hu₁ = proj₁ (proj₂ sc)

  hu₂ : (isT₁ u ∨ satClause' a rest) ≡ true
  hu₂ = proj₂ (proj₂ sc)

  a₁ : Asg m
  a₁ = updateAt a x (λ _ → u)

  hDx : Distinct (x ∷ xs)
  hDx = hD

  hFt : FreshAll xs (l₁ ∷ l₂ ∷ rest)
  hFt = FreshAll-tail {xs = xs} {cl = l₁ ∷ l₂ ∷ rest} hF

  fx : Fresh x (l₁ ∷ l₂ ∷ rest)
  fx = FreshAll-head {xs = xs} {cl = l₁ ∷ l₂ ∷ rest} hF

  lu : lookup a₁ x ≡ u
  lu = lookup∘updateAt x a

  fx2 : Fresh x rest
  fx2 = λ q → fx (∈ᶠ-there (∈ᶠ-there q))

  ag : satClause' a₁ rest ≡ satClause' a rest
  ag = satClause'-agree1 rest a x u fx2

  -- 续跑子句在 a₁ 下成立（x 取 u、rest 不受影响）
  h₁ : satClause' a₁ ((σ₊ , x) ∷ rest) ≡ true
  h₁ = trans (cong₂ (λ p q → isT₁ p ∨ q) lu ag) hu₂

  a₁l₁ : satLit' a₁ l₁ ≡ satLit' a l₁
  a₁l₁ = satLit'-agree a x u l₁ (Fresh-head≢ {l = l₁} {rest = l₂ ∷ rest} fx)

  a₁l₂ : satLit' a₁ l₂ ≡ satLit' a l₂
  a₁l₂ = satLit'-agree a x u l₂ (λ q → fx (∈ᶠ-there (∈ᶠ-here q)))

  a₁x : satLit' a₁ (σ₋ , x) ≡ isT₁ (negate u)
  a₁x = cong (λ z → isT₁ (negate z)) lu

  -- 首条子句 (l₁ ∨ l₂ ∨ ¬x) 在 a₁ 下成立
  h₂ : satClause' a₁ (l₁ ∷ l₂ ∷ (σ₋ , x) ∷ []) ≡ true
  h₂ = trans (satClause'-3lit a₁ l₁ l₂ (σ₋ , x))
             (trans (cong₂ (λ p q → p ∨ q) a₁l₁
                           (cong₂ (λ p q → p ∨ q) a₁l₂ a₁x))
                    hu₁)

  ih : Σ (Asg m) (λ a′ → (satFormula' a′ (tseitin-split xs ((σ₊ , x) ∷ rest)) ≡ true)
                          × (∀ v → ((v ∈ᶠ xs) → ⊥) → lookup a′ v ≡ lookup a₁ v))
  ih = tseitin-split-complete xs ((σ₊ , x) ∷ rest) a₁
         (Distinct-tail hD)
         (freshAll-extend {xs = xs} {x = x} {rest = rest}
            (freshAll-rest {xs = xs} {l₁ = l₁} {l₂ = l₂} {rest = rest} hFt) hDx)
         h₁

  a₂ : Asg m
  a₂ = proj₁ ih

  hSat : satFormula' a₂ (tseitin-split xs ((σ₊ , x) ∷ rest)) ≡ true
  hSat = proj₁ (proj₂ ih)

  hAg : ∀ v → ((v ∈ᶠ xs) → ⊥) → lookup a₂ v ≡ lookup a₁ v
  hAg = proj₂ (proj₂ ih)

  cl3 : Clause' m
  cl3 = l₁ ∷ l₂ ∷ (σ₋ , x) ∷ []

  -- 内层改动不触及 cl3 的变元 ⟹ 首条子句仍成立
  h₂′ : satClause' a₂ cl3 ≡ true
  h₂′ = trans (satClause'-cong cl3 a₁ a₂
                 (λ v inV → hAg v (clause3-vars-not-in {xs = xs} {l₁ = l₁} {l₂ = l₂}
                                        {x = x} {rest = rest} hFt hDx v inV)))
              h₂

  assembled : satFormula' a₂ (tseitin-split (x ∷ xs) (l₁ ∷ l₂ ∷ rest)) ≡ true
  assembled = cong₂ _∧_ h₂′ hSat

  agree : ∀ v → ((v ∈ᶠ (x ∷ xs)) → ⊥) → lookup a₂ v ≡ lookup a v
  agree v nv =
    trans (hAg v (λ p → nv (∈ᶠ-there p)))
          (lookup∘updateAt′ v x (λ p → nv (∈ᶠ-here p)) a)
tseitin-split-complete (x ∷ xs) [] a hD hF h = ⊥-elim (Bool-⊥ h)
tseitin-split-complete (x ∷ xs) (l ∷ []) a hD hF h =
  a , (trans (cong (_∧ true) h) refl) , (λ v nv → refl)

-- ────────────────────────────────────────────────────────────────────
-- §6 等可满足性（∃ 形式与不可满足形式）〔结构证明〕
-- ────────────────────────────────────────────────────────────────────

tseitin-split-sat-elim : ∀ {m} (xs : List (Fin (suc m))) (cl : Clause' m)
                → Σ (Asg m) (λ a → satFormula' a (tseitin-split xs cl) ≡ true)
                → Σ (Asg m) (λ a → satClause' a cl ≡ true)
tseitin-split-sat-elim xs cl (a , h) = a , tseitin-split-sound xs cl a h

tseitin-split-sat-intro : ∀ {m} (xs : List (Fin (suc m))) (cl : Clause' m)
                 → Distinct xs → FreshAll xs cl
                 → Σ (Asg m) (λ a → satClause' a cl ≡ true)
                 → Σ (Asg m) (λ a → satFormula' a (tseitin-split xs cl) ≡ true)
tseitin-split-sat-intro xs cl hD hF (a , h) =
  proj₁ (tseitin-split-complete xs cl a hD hF h)
    , proj₁ (proj₂ (tseitin-split-complete xs cl a hD hF h))

tseitin-split-unsat : ∀ {m} (xs : List (Fin (suc m))) (cl : Clause' m)
             → (Σ (Asg m) (λ a → satClause' a cl ≡ true) → ⊥)
             → (Σ (Asg m) (λ a → satFormula' a (tseitin-split xs cl) ≡ true) → ⊥)
tseitin-split-unsat xs cl noSat (a , h) = noSat (a , tseitin-split-sound xs cl a h)

-- ────────────────────────────────────────────────────────────────────
-- §7 核对层〔refl 枚举〕（m = 1：变元 fzero / fsuc fzero）
-- ────────────────────────────────────────────────────────────────────

Cnf-check-cl4 : Clause' 1
Cnf-check-cl4 =
  (σ₊ , fzero) ∷ (σ₋ , fzero) ∷ (σ₊ , fsuc fzero) ∷ (σ₋ , fsuc fzero) ∷ []

Cnf-check-cl5 : Clause' 1
Cnf-check-cl5 =
  (σ₊ , fzero) ∷ (σ₋ , fzero) ∷ (σ₊ , fsuc fzero)
    ∷ (σ₋ , fsuc fzero) ∷ (σ₊ , fzero) ∷ []

-- 4 长 + 1 辅助 ⟹ 2 条 3-子句（第二条恰 3 文字）
Cnf-check-split4 :
  tseitin-split (fzero ∷ []) Cnf-check-cl4
  ≡ ((σ₊ , fzero) ∷ (σ₋ , fzero) ∷ (σ₋ , fzero) ∷ [])
      ∷ ((σ₊ , fzero) ∷ (σ₊ , fsuc fzero) ∷ (σ₋ , fsuc fzero) ∷ []) ∷ []
Cnf-check-split4 = refl

-- 5 长 + 2 辅助 ⟹ 3 条（链式，第二条首文字是 x₁ 的正出现）
Cnf-check-split5 :
  tseitin-split (fzero ∷ (fsuc fzero ∷ [])) Cnf-check-cl5
  ≡ ((σ₊ , fzero) ∷ (σ₋ , fzero) ∷ (σ₋ , fzero) ∷ [])
      ∷ ((σ₊ , fzero) ∷ (σ₊ , fsuc fzero) ∷ (σ₋ , fsuc fzero) ∷ [])
        ∷ ((σ₊ , fsuc fzero) ∷ (σ₋ , fsuc fzero) ∷ (σ₊ , fzero) ∷ []) ∷ []
Cnf-check-split5 = refl

-- 计数：2 条 ≤ 1 + 1
Cnf-check-len4 : length (tseitin-split (fzero ∷ []) Cnf-check-cl4) ≤ 2
Cnf-check-len4 = s≤s (s≤s z≤n)

-- 全假赋值：原子句假、拆分式亦假（回向的两半一致）
Cnf-check-sound-false :
  satFormula' (T₀ v∷ T₀ v∷ vNil) (tseitin-split (fzero ∷ []) Cnf-check-cl4) ≡ false
Cnf-check-sound-false = refl

-- ────────────────────────────────────────────────────────────────────
-- §8 尾注立界（诚实边界——不设空壳签名）
-- ────────────────────────────────────────────────────────────────────
-- (i)   辅助变元由调用方给出（同一池）；「池扩张」（Fin 号 ⟹ 更大的 suc m、
--       赋值前缀一致）不在本件范围——那是调用方构造 tableau 时一次性选定的
--       布局问题（同 SATLook §6(iii) 的「布局 ≠ 接口」）。
-- (ii)  计数只给上界 `length (tseitin-split xs cl) ≤ length xs + 1`：`tseitin-split` 的末条
--       子句在 `cl` 剩余不足 2 文字时原样保留（长度 ≤ 3，仍是合法 ≤3-CNF），
--       故精确等式依赖「辅助数 = 子句长 − 3」这一调用方条件，本件不假设它。
-- (iii) 与 `SATMember.Formula`（固定 3-CNF）的对接在 CNF.agda §4
--       （`formulaOf3-sat`）；若末条不足 3 文字需补位——那是 M3 落族时的接缝。
-- (iv)  未给「子句数精确 = n − 2」与「辅助数 = n − 3」的算术对接（M3 用）。

-- 0 postulate / 0 hole。
