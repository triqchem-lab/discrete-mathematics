{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Algebra.LaurentCanon
-- Laurent 项列表的规范形唯一性：sort-unique 的核心前置。
--
-- 数学背景：Z[t,t⁻¹] 项列表的规范形 = 指数【严格】降序的列表
-- （严格降序 = 有序 + 指数互异，合为一个归纳谓词 Canon）。
-- 规范形唯一性：两个 Canon 列表若含相同的项集合（逐项成员双向），
-- 则列表逐点相等。
--
-- 为什么绕开 cons 消去引理：从 (x∷xs) ↭ (x∷ys) 剥出 xs ↭ ys
-- 的证明在 trans 分支会构造【新推导】，结构归纳失效
-- （Agda stdlib 至今没有此引理）。本模块用成员式论证替代：
--   头元素相等 = 成员双向转移 + Canon 严格界（canon-<-head）+ <-irrefl；
--   尾部成员等价 = 全体成员等价 + 严格界排除「尾元素 ≡ 对方头」。
--
-- 设计决策（2026-10）：成员谓词用自建结构化 InT（构造子即字面相等），
-- 不用 stdlib 的 Any 版 _∈_——后者在推断模式下隐参（setoid 层级/P）
-- 反复解不出（本会话实测多次 UnsolvedMetaVariables）。
--
-- 0 postulate / 0 hole。
module Sovereign.Algebra.LaurentCanon where

open import Data.Integer using (ℤ; _<_)
open import Data.Integer.Properties using (<-trans; <-irrefl)
open import Data.List using (List; []; _∷_)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Sovereign.Algebra.LaurentBase using (LaurentTerm; Laurent) public
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; subst; sym; trans)
open import Relation.Nullary using (¬_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List.Relation.Binary.Permutation.Propositional
  using (_↭_; refl; ↭-sym; prep; swap; trans)

-- ────────────────────────────────────────────────────────────────────
-- 结构化成员谓词（构造子即字面相等）
-- ────────────────────────────────────────────────────────────────────

data InT : LaurentTerm → Laurent → Set where
  here  : ∀ t ts → InT t (t ∷ ts)
  there : ∀ t u ts → InT t ts → InT t (u ∷ ts)

∈[]-absurd : ∀ {t : LaurentTerm} → InT t [] → ⊥
∈[]-absurd ()

∈-here : ∀ (t : LaurentTerm) (ts : Laurent) → InT t (t ∷ ts)
∈-here t ts = here t ts

-- 成员经置换双向转移（构造子级归纳，全部 case 封闭）
In-resp-↭ : ∀ {xs ys} → xs ↭ ys → ∀ t → InT t xs → InT t ys
In-resp-↭ refl t wit = wit
In-resp-↭ {_} {z ∷ ys} (prep z p) t (here t ts) = here t ys
In-resp-↭ {_} {z ∷ ys} (prep z p) t (there t z ts wit) = there t z ys (In-resp-↭ p t wit)
In-resp-↭ {_} {w ∷ z ∷ ys} (swap z w p) t (here t (w ∷ ts)) =
    there t w (z ∷ ys) (here t ys)
In-resp-↭ {_} {w ∷ z ∷ ys} (swap z w p) t (there t z (w ∷ ts) (here t ts')) =
    here t (z ∷ ys)
In-resp-↭ {_} {w ∷ z ∷ ys} (swap z w p) t (there t z (w ∷ ts) (there t w ts' wit)) =
  there t w (z ∷ ys) (there t z ys (In-resp-↭ p t wit))
In-resp-↭ (trans p q) t wit = In-resp-↭ q t (In-resp-↭ p t wit)

-- ────────────────────────────────────────────────────────────────────
-- Canon：指数严格降序（有序 + 指数互异，合一归纳谓词）
-- ────────────────────────────────────────────────────────────────────

data Canon : Laurent → Set where
  canon-nil  : Canon []
  canon-one  : ∀ t → Canon (t ∷ [])
  canon-cons : ∀ t₁ t₂ ts →
               proj₂ t₂ < proj₂ t₁ →      -- 严格降序
               Canon (t₂ ∷ ts) →
               Canon (t₁ ∷ t₂ ∷ ts)

-- 非空 Canon 的尾部仍是 Canon
canon-tail : ∀ {t ts} → Canon (t ∷ ts) → Canon ts
canon-tail (canon-one t) = canon-nil
canon-tail (canon-cons t₁ t₂ ts p s) = s

-- 严格界：Canon 列表尾中任意项的指数 < 头的指数
canon-<-head : ∀ {x xs} → Canon (x ∷ xs) → ∀ y → InT y xs → proj₂ y < proj₂ x
canon-<-head (canon-one x) y ()
canon-<-head (canon-cons x x₂ ts p s) y (here .y .ts) = p
canon-<-head (canon-cons x x₂ ts p s) y (there .y .x₂ .ts wit) =
  <-trans (canon-<-head s y wit) p

-- 严格矛盾：exp t < exp x，x ≡ y，t ≡ y ⟹ ⊥
strict-contradiction : ∀ (x y t : LaurentTerm) →
  proj₂ t < proj₂ x → x ≡ y → t ≡ y → ⊥
strict-contradiction x y t lt x≡y t≡y =
  <-irrefl refl (subst (λ e → proj₂ t < e) (sym (cong proj₂ t≡y)) lt')
  where
  lt' : proj₂ t < proj₂ y
  lt' = subst (λ e → proj₂ t < e) (cong proj₂ x≡y) lt

-- ────────────────────────────────────────────────────────────────────
-- 尾部成员等价（头相等的情形下，严格界排除「尾元素 ≡ 对方头」）
-- ────────────────────────────────────────────────────────────────────

tail-iff→ : ∀ x xs' y ys' → x ≡ y → Canon (x ∷ xs') →
  (∀ t → InT t (x ∷ xs') → InT t (y ∷ ys')) →
  ∀ t → InT t xs' → InT t ys'
tail-iff→ x xs' y ys' x≡y cx f t wit with f t (there t x xs' wit)
... | here .t .ys' =
  ⊥-elim (strict-contradiction x y t (canon-<-head cx t wit) x≡y refl)
... | there .t .y .ys' wit' = wit'

tail-iff← : ∀ x xs' y ys' → x ≡ y → Canon (y ∷ ys') →
  (∀ t → InT t (y ∷ ys') → InT t (x ∷ xs')) →
  ∀ t → InT t ys' → InT t xs'
tail-iff← x xs' y ys' x≡y cy g t wit with g t (there t y ys' wit)
... | here .t .xs' =
  ⊥-elim (strict-contradiction y x t (canon-<-head cy t wit) (sym x≡y) refl)
... | there .t .x .xs' wit' = wit'

-- ────────────────────────────────────────────────────────────────────
-- 规范形唯一性（核心）：canon-cons-unique 与 canon-unique 互调，
-- 递归沿 canon-tail 结构下降。
-- ────────────────────────────────────────────────────────────────────

mutual
  canon-cons-unique : ∀ x xs' y ys' →
    Canon (x ∷ xs') → Canon (y ∷ ys') →
    (∀ t → InT t (x ∷ xs') → InT t (y ∷ ys')) →
    (∀ t → InT t (y ∷ ys') → InT t (x ∷ xs')) →
    (x ∷ xs') ≡ (y ∷ ys')
  canon-cons-unique x xs' y ys' cx cy f g = loop (f x (∈-here x xs'))
    where
    loop : InT x (y ∷ ys') → (x ∷ xs') ≡ (y ∷ ys')
    loop (here .x .ys') =
      -- here 分支：成员构造子即字面相等，y := x
      cong (x ∷_) (canon-unique xs' ys' (canon-tail cx) (canon-tail cy)
        (tail-iff→ x xs' x ys' refl cx f) (tail-iff← x xs' x ys' refl cy g))
    loop (there .x .y .ys' x∈ys') = ⊥-elim y<x-absurd
      where
      -- y 也在 xs' 中 ⟹ 双向严格界矛盾
      y<x-absurd : ⊥
      y<x-absurd with g y (∈-here y ys')
      ... | here .y .xs' =
        -- here 分支：y 即 x，⟹ exp y < exp y，矛盾
        <-irrefl refl (canon-<-head cy y x∈ys')
      ... | there .y .x .xs' y∈xs' =
        <-irrefl refl
          (<-trans (canon-<-head cy x x∈ys') (canon-<-head cx y y∈xs'))

  canon-unique : ∀ xs ys → Canon xs → Canon ys
    → (∀ t → InT t xs → InT t ys) → (∀ t → InT t ys → InT t xs) → xs ≡ ys
  canon-unique [] [] c₁ c₂ f g = refl
  canon-unique [] (y ∷ ys) c₁ c₂ f g = ⊥-elim (∈[]-absurd (g y (∈-here y ys)))
  canon-unique (x ∷ xs) [] c₁ c₂ f g = ⊥-elim (∈[]-absurd (f x (∈-here x xs)))
  canon-unique (x ∷ xs) (y ∷ ys) c₁ c₂ f g =
    canon-cons-unique x xs y ys c₁ c₂ f g
