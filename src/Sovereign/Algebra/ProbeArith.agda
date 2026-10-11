{-# OPTIONS --cubical --guardedness #-}
module Sovereign.Algebra.ProbeArith where

open import Cubical.Data.Nat using (ℕ; zero; suc; _∸_) renaming (_+_ to _+ℕ_)
open import Cubical.Data.Nat using (predℕ)
open import Cubical.Data.Empty using (⊥; rec)
open import Cubical.Data.Nat.Properties using (+-zero; +-suc) renaming (+-comm to +ℕ-comm)
open import Cubical.Data.Int using (ℤ; _+_; _-_; pos; negsuc; sucℤ; _+pos_; neg)
open import Cubical.Data.Int.Order using (_<_; _≤_; ≤-+o; ≤-o+; ≤-+o-cancel; isTrans≤; isRefl≤)
open import Cubical.Data.Int.Properties using (+Comm; +Assoc; +sucℤ; minusPlus; plusMinus; -Cancel; pos0+; -pos; -Cancel'; sucℤ+pos; negsuc+) renaming (sucℤ+ to sucInt)
open import Cubical.Foundations.Prelude using (_≡_; refl; sym; cong; cong₂; subst; Σ; _,_; fst; snd; _∙_; funExt)

-- 核心消去引理（参照 mathlib4 le.elim）：
-- a ≤ b 可以消去为「存在 ℕ 见证 k 使得 a +pos k ≡ b」
-- 这正是 Cubical 的 < / ≤ 的定义形式，现在把它封装为可直接用的工具

-- 序到等式消去：< 的见证是 Σ ℕ，直接取分量
<-witness : {a b : ℤ} → a < b → ℕ
<-witness (k , _) = k

<-eq : {a b : ℤ} → (h : a < b) → sucℤ a +pos <-witness h ≡ b
<-eq (_ , p) = p

-- ≤ 的见证
≤-witness : {a b : ℤ} → a ≤ b → ℕ
≤-witness (k , _) = k

≤-eq : {a b : ℤ} → (h : a ≤ b) → a +pos ≤-witness h ≡ b
≤-eq (_ , p) = p

-- 关键引理：n < Lf + Lg → Lf ≤ k → n - k < Lg
-- 用 ≤-eq 消去为算术等式后用 cong/transport 组合
-- sucIntPlus: sucℤ (x + y) ≡ sucℤ x + y（纯字母名避开解析冲突）
sucPush : ∀ x y → sucℤ (x + y) ≡ sucℤ x + y
sucPush x y = sucInt x y

pos-+pos : ∀ (a b : ℕ) → _+pos_ (pos a) b ≡ pos (a +ℕ b)
pos-+pos a zero = cong pos (sym (+-zero a))
pos-+pos a (suc b) = cong sucℤ (pos-+pos a b) ∙ cong pos (sym (+-suc a b))

probe : (n Lf Lg k : ℤ) → n < Lf + Lg → Lf ≤ k → n - k < Lg
probe n Lf Lg k (a , p₁) (b , p₂) = (a +ℕ b) , lem
  where
  lem : sucℤ (n - k) +pos (a +ℕ b) ≡ Lg
  lem = subst (λ x → sucℤ (n - x) +pos (a +ℕ b) ≡ Lg) p₂ lem'
    where
    lem' : sucℤ (n - (Lf +pos b)) +pos (a +ℕ b) ≡ Lg
    lem' = subst (λ x → sucℤ (n - (Lf +pos b)) +pos (a +ℕ b) ≡ x - Lf) p₁ lem'' ∙ cong (_- Lf) (+Comm Lf Lg) ∙ plusMinus Lf Lg
      where
      -- Lf +pos b 减去 Lf 回到 pos b（w - Lf ≡ pos b）
      wMinusLf : (Lf +pos b) + (Cubical.Data.Int.-_ Lf) ≡ pos b
      wMinusLf =
        cong (λ z → z + (Cubical.Data.Int.-_ Lf)) (+Comm Lf (pos b))
        ∙ sym (+Assoc (pos b) Lf (Cubical.Data.Int.-_ Lf))
        ∙ cong (pos b +_) (-Cancel Lf)

      -- -(w) + pos b ≡ - Lf（w = Lf +pos b）：minusPlus 消去
      negw+posb : Cubical.Data.Int.-_ (Lf +pos b) + pos b ≡ Cubical.Data.Int.-_ Lf
      negw+posb =
        cong (Cubical.Data.Int.-_ (Lf +pos b) +_) (sym wMinusLf)
        ∙ +Assoc (Cubical.Data.Int.-_ (Lf +pos b)) (Lf +pos b) (Cubical.Data.Int.-_ Lf)
        ∙ cong (λ z → z + (Cubical.Data.Int.-_ Lf))
            (cong (λ z → z + (Lf +pos b))
              (pos0+ (Cubical.Data.Int.-_ (Lf +pos b)))
              ∙ minusPlus (Lf +pos b) (pos 0))
        ∙ sym (pos0+ (Cubical.Data.Int.-_ Lf))

      -- -(Lf+pos b) + pos(a+b) ≡ pos a - Lf（重排中心引理）
      inner : Cubical.Data.Int.-_ (Lf +pos b) + pos (a +ℕ b) ≡ pos a + (Cubical.Data.Int.-_ Lf)
      inner =
        cong (Cubical.Data.Int.-_ (Lf +pos b) +_) (sym (pos-+pos a b))
        ∙ cong (Cubical.Data.Int.-_ (Lf +pos b) +_) (+Comm (pos a) (pos b))
        ∙ +Assoc (Cubical.Data.Int.-_ (Lf +pos b)) (pos b) (pos a)
        ∙ cong (_+ (pos a)) negw+posb
        ∙ +Comm (Cubical.Data.Int.-_ Lf) (pos a)

      lem'' : sucℤ (n - (Lf +pos b)) +pos (a +ℕ b) ≡ (sucℤ n +pos a) - Lf
      lem'' =
        cong (λ z → z + pos (a +ℕ b)) (sucPush n (Cubical.Data.Int.-_ (Lf +pos b)))
        ∙ sym (+Assoc (sucℤ n) (Cubical.Data.Int.-_ (Lf +pos b)) (pos (a +ℕ b)))
        ∙ cong (sucℤ n +_) inner
        ∙ +Assoc (sucℤ n) (pos a) (Cubical.Data.Int.-_ Lf)


-- ────────────────────────────────────────────────────────────────────
-- 上界对偶：Uf + Ug < n → k ≤ Uf → Ug < n - k
-- 见证 e := c +ℕ d；核心：sucℤ k - k ≡ pos 1（k + pos 1 ≡ sucℤ k 定义性）
-- ────────────────────────────────────────────────────────────────────

probe-dual : (n Uf Ug k : ℤ) → Uf + Ug < n → k ≤ Uf → Ug < n - k
probe-dual n Uf Ug k (c , q₁) (d , q₂) = (c +ℕ d) , lem
  where
  -- pos 1 + x ≡ sucℤ x（x + pos 1 ≡ sucℤ x 定义性 + +Comm）
  pos1+sucℤ : ∀ x → pos 1 + x ≡ sucℤ x
  pos1+sucℤ x = sym (+Comm x (pos 1))

  -- minus-shift 内联：(x - y) + z ≡ (x + z) - y
  mshift : ∀ x y z → (x - y) + z ≡ (x + z) - y
  mshift x y z = sym (+Assoc x (Cubical.Data.Int.-_ y) z)
                 ∙ cong (x +_) (+Comm (Cubical.Data.Int.-_ y) z)
                 ∙ +Assoc x z (Cubical.Data.Int.-_ y)

  -- sucℤ k - k ≡ pos 1
  sucℤk-k : sucℤ k - k ≡ pos 1
  sucℤk-k =
    cong (λ z → z + (Cubical.Data.Int.-_ k)) (+Comm k (pos 1))
    ∙ sym (+Assoc (pos 1) k (Cubical.Data.Int.-_ k))
    ∙ cong (pos 1 +_) (-Cancel k)

  LHS-chain' : sucℤ Ug +pos (c +ℕ d) ≡ (sucℤ Ug + pos c) + pos d
  LHS-chain' =
    cong (sucℤ Ug +_) (sym (pos-+pos c d))
    ∙ +Assoc (sucℤ Ug) (pos c) (pos d)

  RHS-chain : (sucℤ ((k +pos d) + Ug) +pos c) - k ≡ (sucℤ Ug + pos c) + pos d
  RHS-chain =
    cong (λ z → (z + pos c) - k)
      (sucPush (k +pos d) Ug ∙ cong (_+ Ug) (sucPush k (pos d)))
    ∙ cong (λ z → z - k) (sym (+Assoc ((sucℤ k + pos d)) Ug (pos c)))
    ∙ sym (mshift (sucℤ k + pos d) k (Ug + pos c))
    ∙ cong (_+ (Ug + pos c)) (sym (mshift (sucℤ k) k (pos d)))
    ∙ cong (λ z → (z + pos d) + (Ug + pos c)) sucℤk-k
    ∙ sym (+Assoc (pos 1) (pos d) (Ug + pos c))
    ∙ cong (pos 1 +_) (+Comm (pos d) (Ug + pos c))
    ∙ +Assoc (pos 1) (Ug + pos c) (pos d)
    ∙ cong (_+ pos d) (+Assoc (pos 1) Ug (pos c))
    ∙ cong (λ z → (z + pos c) + pos d) (pos1+sucℤ Ug)

  lem : sucℤ Ug +pos (c +ℕ d) ≡ n - k
  lem = subst (λ x → sucℤ Ug +pos (c +ℕ d) ≡ x - k) q₁ lem'
    where
    lem' : sucℤ Ug +pos (c +ℕ d) ≡ (sucℤ (Uf + Ug) +pos c) - k
    lem' = subst (λ x → sucℤ Ug +pos (c +ℕ d) ≡ (sucℤ (x + Ug) +pos c) - k) q₂ lem''
      where
      lem'' : sucℤ Ug +pos (c +ℕ d) ≡ (sucℤ ((k +pos d) + Ug) +pos c) - k
      lem'' = LHS-chain' ∙ sym RHS-chain


-- ────────────────────────────────────────────────────────────────────
-- 全称三分律：∀ m n → Trichotomy m n（界提取前置）
-- ────────────────────────────────────────────────────────────────────

open import Cubical.Data.Int.Order using (Trichotomy; lt; eq; gt; Trichotomy-suc; isIrrefl<) public
open import Cubical.Data.Nat.Order using () renaming (_<_ to _<'_; Trichotomy to Trichotomyℕ; lt to ltℕ; eq to eqℕ; gt to gtℕ; _≟'_ to _≟ℕ_)
open import Cubical.Data.Int.Properties using (posNotnegsuc; negsucNotpos) public

-- 基例：pos 0 与任意 n
tri0 : ∀ n → Trichotomy (pos 0) n
tri0 (pos zero) = eq refl
tri0 (pos (suc n)) = lt (n , pos-+pos 1 n)
tri0 (negsuc zero) = gt (zero , refl)
tri0 (negsuc (suc n)) = gt (suc n , lem)
  where
  lem : sucℤ (negsuc (suc n)) +pos (suc n) ≡ pos 0
  lem = cong (_+ pos (suc n)) (sym (-pos (suc n))) ∙ -Cancel' (pos (suc n))

-- 对称：lt/gt 对调（eq 保持）
tri-sym : ∀ m n → Trichotomy m n → Trichotomy n m
tri-sym m n (lt x) = gt x
tri-sym m n (eq x) = eq (sym x)
tri-sym m n (gt x) = lt x

-- 全称三分律主体。
-- 策略（下一批实现）：ℤ 符号分解 4 case 归约到 ℕ 比较——
--   pos a, pos b → ℕ 比较 a b；negsuc a, negsuc b → ℕ 反向比较；
--   pos/negsuc → 恒 lt；negsuc/pos → 恒 gt。
--   ℕ 二分 triℕ : ∀ a b → (a < b) ⊎ (a ≡ b) ⊎ (a > b) 对 a 归纳自证。
--   Trichotomy-suc 双边归约不成立（suc 同时作用两参数），弃用原策略。
-- ℕ < 见证转 pos < pos 见证（ℕ witness 前置 k+suc a≡b / ℤ 后置）
pos<pos : ∀ a b → a <' b → pos a < pos b
pos<pos a b (k , p) =
  k , pos-+pos (suc a) k ∙ cong pos (+ℕ-comm (suc a) k ∙ p)

-- z +pos (k +ℕ a) ≡ (z +pos k) +pos a（对 k 归纳，全定义性）
pos-split : ∀ z k a → z +pos (k +ℕ a) ≡ (z +pos k) +pos a
pos-split z zero a = refl
pos-split z (suc k) a = cong sucℤ (pos-split z k a) ∙ sucℤ+pos a (z +pos k)

-- x < pos 0 → x < pos a（witness 平移）
<-pos0→posa : ∀ x a → x < pos 0 → x < pos a
<-pos0→posa x a (k , p) =
  (k +ℕ a) , pos-split (sucℤ x) k a ∙ cong (_+pos a) p ∙ pos-+pos zero a

-- -(n+1) + (n+1) ≡ 0（-pos 桥 + -Cancel'）
negsucS+ : ∀ n → sucℤ (negsuc (suc n)) +pos (suc n) ≡ pos 0
negsucS+ n = -Cancel' (pos (suc n))

-- negsuc b < pos a 恒真（经 < pos 0 平移）
negsuc<pos : ∀ b a → negsuc b < pos a
negsuc<pos zero a = <-pos0→posa (negsuc zero) a (zero , refl)
negsuc<pos (suc b) a = <-pos0→posa (negsuc (suc b)) a (suc b , negsucS+ b)

-- ℕ 反序提升：p <' q ⇒ negsuc q < negsuc p（更负更小）
negsuc-anti : ∀ p q → p <' q → negsuc q < negsuc p
negsuc-anti p q (k , pk) =
  subst (λ z → negsuc z < negsuc p) (sym (+-suc k p) ∙ pk) core
  where
  -- 核：negsuc (suc (k+ℕ p)) < negsuc p（minusPlus 链）
  core : negsuc (suc (k +ℕ p)) < negsuc p
  core = k ,
    cong (λ z → negsuc z +pos k) (+ℕ-comm k p)
    ∙ cong (_+pos k) (negsuc+ p k)
    ∙ minusPlus (pos k) (negsuc p)

-- 全称三分律（符号分解 4 case + ℕ ≟）
triℤ : ∀ m n → Trichotomy m n
triℤ (pos a) (pos b) with a ≟ℕ b
... | ltℕ x = lt (pos<pos a b x)
... | eqℕ x = eq (cong pos x)
... | gtℕ x = gt (pos<pos b a x)
triℤ (pos a) (negsuc b) = gt (negsuc<pos b a)
triℤ (negsuc a) (pos b) = lt (negsuc<pos a b)
triℤ (negsuc a) (negsuc b) with a ≟ℕ b
... | ltℕ x = gt (negsuc-anti a b x)
... | eqℕ x = eq (cong negsuc x)
... | gtℕ x = lt (negsuc-anti b a x)

-- ─── 2026-10-11 补件 ───
-- lem-dpp : probe 的核心重排引理提层（原 probe.where 的 lem'' 链：
--   sucℤ (n - (Lf +pos b)) +pos (a +ℕ b) ≡ (sucℤ n +pos a) - Lf）

-- 小桥 1：(Lf +pos b) - Lf ≡ pos b（回到见证 b 的原点）
wMinusLf-dpp : ∀ (Lf : ℤ) (b : ℕ) → (Lf +pos b) + Cubical.Data.Int.-_ Lf ≡ pos b
wMinusLf-dpp Lf b =
      cong (λ z → z + (Cubical.Data.Int.-_ Lf)) (+Comm Lf (pos b))
      ∙ sym (+Assoc (pos b) Lf (Cubical.Data.Int.-_ Lf))
      ∙ cong (pos b +_) (-Cancel Lf)

-- 小桥 2：-(Lf+pos b) + pos b ≡ - Lf（minusPlus 消去）
negw+posb-dpp : ∀ (Lf : ℤ) (b : ℕ) → Cubical.Data.Int.-_ (Lf +pos b) + pos b ≡ Cubical.Data.Int.-_ Lf
negw+posb-dpp Lf b =
      cong (Cubical.Data.Int.-_ (Lf +pos b) +_) (sym (wMinusLf-dpp Lf b))
      ∙ +Assoc (Cubical.Data.Int.-_ (Lf +pos b)) (Lf +pos b) (Cubical.Data.Int.-_ Lf)
      ∙ cong (λ z → z + (Cubical.Data.Int.-_ Lf))
          (cong (λ z → z + (Lf +pos b)) (pos0+ (Cubical.Data.Int.-_ (Lf +pos b)))
           ∙ minusPlus (Lf +pos b) (pos 0))
      ∙ sym (pos0+ (Cubical.Data.Int.-_ Lf))

-- 重排中心：-(Lf+pos b) + pos (a+b) ≡ pos a - Lf
dpp-inner : ∀ (Lf : ℤ) (a b : ℕ) → Cubical.Data.Int.-_ (Lf +pos b) + pos (a +ℕ b) ≡ pos a + Cubical.Data.Int.-_ Lf
dpp-inner Lf a b =
      cong (Cubical.Data.Int.-_ (Lf +pos b) +_) (sym (pos-+pos a b))
      ∙ cong (Cubical.Data.Int.-_ (Lf +pos b) +_) (+Comm (pos a) (pos b))
      ∙ +Assoc (Cubical.Data.Int.-_ (Lf +pos b)) (pos b) (pos a)
      ∙ cong (_+ (pos a)) (negw+posb-dpp Lf b)
      ∙ +Comm (Cubical.Data.Int.-_ Lf) (pos a)

lem-dpp : ∀ (n Lf : ℤ) (a b : ℕ) → sucℤ (n - (Lf +pos b)) +pos (a +ℕ b) ≡ (sucℤ n +pos a) - Lf
lem-dpp n Lf a b =
      cong (λ z → z + pos (a +ℕ b)) (sucPush n (Cubical.Data.Int.-_ (Lf +pos b)))
      ∙ sym (+Assoc (sucℤ n) (Cubical.Data.Int.-_ (Lf +pos b)) (pos (a +ℕ b)))
      ∙ cong (sucℤ n +_) (dpp-inner Lf a b)
      ∙ +Assoc (sucℤ n) (pos a) (Cubical.Data.Int.-_ Lf)

