{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Algebra.LaurentNorm
-- Laurent 项列表的插入式规范化：insertCᵌ 直接产出 Canon（严格降序 + 指数互异），
-- 并同步给出「结果 = h ∷ r」的方程与首项来源刻画（refinement 风格）。
--
-- 数学背景：Z[t,t⁻¹] 项列表的规范形。与 sort+merge 双轨（LaurentSort）不同，
-- insertCᵌ 在插入点就地处理三种情形：
--   1. 指数相等：系数相加；和为零则整项丢弃（消去）
--   2. 指数更小：后插
--   3. 指数更大：前插
-- foldr insertCᵌ [] p 直接是 Canon——不需要 Sorted 中间态、All≤、
-- merge 头保持、成员保持三套归纳（拓扑扫描后选定此路径，备选 sort+merge 留案）。
--
-- 设计要点（本轮踩坑后定型）：
--   ① 插入的分支决策以 Cmp3 归纳类型显式传递（eq3 携带指数等式证据）；
--   ② 递归沿 Canon 证据本身结构下降，分支决策对 cmp3 做 with 精炼，
--      每个分支的方程按定义归约为 refl——避免「stuck cmp3」
--      （cmp3 作用于变量时不可归约，命题式假设无法精炼 stuck 项，
--      spec 必须与计算同步定义）。
--
-- 复用：Canon/InT/canon-<-head 全部来自 LaurentCanon（回执 c03e22f3）。
--
-- 0 postulate / 0 hole。
module Sovereign.Algebra.LaurentNorm where

open import Data.Integer using (ℤ; _≤_; _<_; +_; _+_)
open import Data.Integer.Properties
  using (_≟_; _<?_; _≤?_; ≤-antisym; <-trans; <-irrefl; ≰⇒>)
open import Data.List using (List; []; _∷_)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; cong; sym; trans; subst)
open import Relation.Nullary using (yes; no; ¬_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Sovereign.Algebra.LaurentCanon
  using (LaurentTerm; Laurent; Canon; canon-nil; canon-one; canon-cons;
         canon-tail; canon-<-head; InT; here; there)

-- ────────────────────────────────────────────────────────────────────
-- 序工具
-- ────────────────────────────────────────────────────────────────────

-- ¬(a < b) ⟹ b ≤ a
¬<⇒≤ : ∀ a b → ¬ (a < b) → b ≤ a
¬<⇒≤ a b h with b ≤? a
... | yes q = q
... | no  q = ⊥-elim (h (≰⇒> q))

-- 非严格 + 不等 ⟹ 严格
≤∧≢⇒< : ∀ n n' → n' ≤ n → n ≢ n' → n' < n
≤∧≢⇒< n n' p neq with n ≤? n'
... | yes q = ⊥-elim (neq (sym (≤-antisym p q)))
... | no  q = ≰⇒> q

-- ────────────────────────────────────────────────────────────────────
-- 三歧比较（eq3 携带等式证据）
-- ────────────────────────────────────────────────────────────────────

data Cmp3 : ℤ → ℤ → Set where
  lt3 : ∀ n n' → n < n' → Cmp3 n n'
  eq3 : ∀ n n' → n ≡ n' → Cmp3 n n'
  gt3 : ∀ n n' → n' < n → Cmp3 n n'

cmp3 : ∀ n n' → Cmp3 n n'
cmp3 n n' with n <? n'
... | yes p = lt3 n n' p
... | no nlt with n ≟ n'
...   | yes e = eq3 n n' e
...   | no ne = gt3 n n' (≤∧≢⇒< n n' (¬<⇒≤ n n' nlt) ne)

-- ────────────────────────────────────────────────────────────────────
-- insertCᵌ：计算并证明同步的规范化插入（对 Canon 证据结构归纳）
-- ────────────────────────────────────────────────────────────────────

insertCᵌ : ∀ (t : LaurentTerm) ts → Canon ts →
  Σ LaurentTerm (λ h → Σ Laurent (λ r →
     Canon (h ∷ r)
     × ((h ≡ t) ⊎ InT h ts ⊎ (proj₂ h ≡ proj₂ t))))
insertCᵌ t [] c = (t , [] , canon-one t , inj₁ refl)

insertCᵌ t (x ∷ []) (canon-one .x)
  with cmp3 (proj₂ t) (proj₂ x)
... | gt3 _ _ g =
  (t , (x ∷ []) , canon-cons t x [] g (canon-one x) , inj₁ refl)
... | eq3 _ _ e with (proj₁ t + proj₁ x) ≟ + 0
...   | yes _ = (x , [] , canon-one x , inj₂ (inj₁ (here x [])))
...   | no _  = ((proj₁ t + proj₁ x , proj₂ t) , [] , canon-one _ , inj₂ (inj₂ refl))
insertCᵌ t (x ∷ []) (canon-one .x)
  | lt3 _ _ l =
  (x , (t ∷ []) , canon-cons x t [] l (canon-one t) , inj₂ (inj₁ (here x [])))

insertCᵌ t (x ∷ x₂ ∷ xs) (canon-cons .x .x₂ .xs p s)
  with cmp3 (proj₂ t) (proj₂ x)
... | gt3 _ _ g =
  (t , (x ∷ x₂ ∷ xs)
  , canon-cons t x (x₂ ∷ xs) g (canon-cons x x₂ xs p s)
  , inj₁ refl)
... | eq3 _ _ e with (proj₁ t + proj₁ x) ≟ + 0
...   | yes _ =
    (x , (x₂ ∷ xs)
    , canon-cons x x₂ xs p s
    , inj₂ (inj₁ (here x (x₂ ∷ xs))))
...   | no _ with insertCᵌ (proj₁ t + proj₁ x , proj₂ t) (x₂ ∷ xs) s
...   | (h , r , cw , inj₁ h≡m) =
    (h , r , cw , inj₂ (inj₂ (cong proj₂ h≡m)))
...   | (h , r , cw , inj₂ (inj₁ wit)) =
    (h , r , cw , inj₂ (inj₁ (there h x (x₂ ∷ xs) wit)))
...   | (h , r , cw , inj₂ (inj₂ eh≡em)) =
    (h , r , cw , inj₂ (inj₂ eh≡em))
insertCᵌ t (x ∷ x₂ ∷ xs) (canon-cons .x .x₂ .xs p s)
  | lt3 _ _ l with insertCᵌ t (x₂ ∷ xs) s
...   | (h , r , cw , inj₁ h≡t) =
    (x , (h ∷ r)
    , canon-cons x h r (subst (λ e → e < proj₂ x) (sym (cong proj₂ h≡t)) l) cw
    , inj₂ (inj₁ (here x (x₂ ∷ xs))))
...   | (h , r , cw , inj₂ (inj₁ wit)) =
    (x , (h ∷ r)
    , canon-cons x h r bound cw
    , inj₂ (inj₁ (here x (x₂ ∷ xs))))
    where
    bound-fun : ∀ (h : LaurentTerm) → InT h (x₂ ∷ xs) → proj₂ h < proj₂ x
    bound-fun h wit' with wit'
    ... | here .x₂ .xs = p
    ... | there .h .x₂ .xs wit'' = <-trans (canon-<-head s h wit'') p
    bound : proj₂ h < proj₂ x
    bound = bound-fun h wit
...   | (h , r , cw , inj₂ (inj₂ eh≡et)) =
    (x , (h ∷ r)
    , canon-cons x h r (subst (λ e → e < proj₂ x) (sym eh≡et) l) cw
    , inj₂ (inj₁ (here x (x₂ ∷ xs))))
