{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Algebra.LaurentNorm
-- Laurent 项列表的插入式规范化：insertCᵌ 直接产出 Canon（严格降序 + 指数互异）。
--
-- 数学背景：Z[t,t⁻¹] 项列表的规范形。与 sort+merge 双轨（LaurentSort）不同，
-- insertCᵌ 在插入点就地处理三种情形：
--   1. 指数相等：系数相加；和为零则整项丢弃（消去，结果可能为空表）
--   2. 指数更小：后插
--   3. 指数更大：前插
-- foldr insertCᵌ [] p 直接是 Canon——不需要 Sorted 中间态、All≤、
-- merge 头保持、成员保持三套归纳（拓扑扫描后选定此路径，备选 sort+merge 留案）。
--
-- 设计要点（本轮踩坑后定型）：
--   ① 插入的分支决策以 Cmp3 归纳类型显式传递（eq3 携带指数等式证据）；
--   ② 递归沿 Canon 证据本身结构下降，分支决策对 cmp3 做 with 精炼
--      ——避免「stuck cmp3」（cmp3 作用于变量时不可归约，
--      命题式假设无法精炼 stuck 项，spec 必须与计算同步定义）；
--   ③ 规格用 w-形式 Σ Laurent (λ w → Canon w × …)：等指数相消时
--      结果 = ts 原样（可能为空表），cons 形状 Σ h r 无法表达空表
--      （曾在 eq-zero 分支错误地返回 x ∷ []——数学错误，已修正）。
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
-- 规格类型（w-形式）：结果 w 为 Canon，且
--   w ≡ ts（等指数相消，整项消失），或
--   w = h ∷ r 且首项来源：h ≡ t，或 h ∈ ts，或 exp h ≡ exp t（合并项）
-- ────────────────────────────────────────────────────────────────────

-- 三路：① w = ts（无变化）；② ts = x' ∷ xs' 且 w = xs'（头被消去）；
-- ③ w = h ∷ r 且首项来源：h ≡ t，或 h ∈ ts，或 exp h ≡ exp t（合并项）
SpecT : LaurentTerm → Laurent → Set
SpecT t ts =
  Σ Laurent (λ w →
    Canon w
    × ((((w ≡ ts)
         ⊎ (Σ LaurentTerm (λ x' → Σ Laurent (λ xs' →
              (ts ≡ x' ∷ xs') × (w ≡ xs')))))
        ⊎ (Σ LaurentTerm (λ h → Σ Laurent (λ r →
             (w ≡ h ∷ r)
             × ((h ≡ t) ⊎ InT h ts ⊎ (proj₂ h ≡ proj₂ t))))))))

-- ────────────────────────────────────────────────────────────────────
-- 首项来源重定向：合并项 m 的指数 = exp t
--   h ≡ m ⟹ exp h ≡ exp t；h ∈ 尾 ⟹ 外层成员（多一个 there）
dj-redirect : ∀ (t x x₂ : LaurentTerm) (xs : Laurent) (m h : LaurentTerm) →
  proj₂ m ≡ proj₂ t →
  ((h ≡ m) ⊎ InT h (x₂ ∷ xs) ⊎ (proj₂ h ≡ proj₂ m))
  → ((h ≡ t) ⊎ InT h (x ∷ x₂ ∷ xs) ⊎ (proj₂ h ≡ proj₂ t))
dj-redirect t x x₂ xs m h me≡te (inj₁ h≡m) =
  inj₂ (inj₂ (trans (cong proj₂ h≡m) me≡te))
dj-redirect t x x₂ xs m h me≡te (inj₂ (inj₁ wit)) =
  inj₂ (inj₁ (there h x (x₂ ∷ xs) wit))
dj-redirect t x x₂ xs m h me≡te (inj₂ (inj₂ eh≡em)) =
  inj₂ (inj₂ (trans eh≡em me≡te))

-- 单元素插入分支（独立函数，避免嵌套 with 的解析/覆盖问题）
-- ────────────────────────────────────────────────────────────────────

one-eq-redirect : ∀ (t x m h : LaurentTerm) → proj₂ t ≡ proj₂ x →
  proj₂ m ≡ proj₂ t →
  ((h ≡ m) ⊎ InT h (x ∷ []) ⊎ (proj₂ h ≡ proj₂ m))
  → ((h ≡ t) ⊎ InT h (x ∷ []) ⊎ (proj₂ h ≡ proj₂ t))
one-eq-redirect t x m h e me≡te (inj₁ h≡m) =
  inj₂ (inj₂ (trans (cong proj₂ h≡m) me≡te))
one-eq-redirect t x m h e me≡te (inj₂ (inj₁ wit)) = inj₂ (inj₁ wit)
one-eq-redirect t x m h e me≡te (inj₂ (inj₂ eh≡em)) =
  inj₂ (inj₂ (trans eh≡em me≡te))

insertCᵌ-spec-one : ∀ t x → Canon (x ∷ []) → SpecT t (x ∷ [])
insertCᵌ-spec-one t x c
  with cmp3 (proj₂ t) (proj₂ x)
... | gt3 _ _ g =
  let H : Σ LaurentTerm (λ h → Σ Laurent (λ r →
            t ∷ (x ∷ []) ≡ h ∷ r
            × ((h ≡ t) ⊎ InT h (x ∷ []) ⊎ (proj₂ h ≡ proj₂ t))))
      H = (t , (x ∷ []) , refl , inj₁ refl)
  in (t ∷ (x ∷ []) , canon-cons t x [] g (canon-one x) , inj₂ H)
... | eq3 _ _ e with (proj₁ t + proj₁ x) ≟ + 0
...   | yes _ = ([] , canon-nil , inj₁ (inj₂ (x , [] , refl , refl)))
...   | no _ =
  let m = (proj₁ t + proj₁ x , proj₂ t)
      H : Σ LaurentTerm (λ h → Σ Laurent (λ r →
            m ∷ [] ≡ h ∷ r
            × ((h ≡ t) ⊎ InT h (x ∷ []) ⊎ (proj₂ h ≡ proj₂ t))))
      H = (m , [] , refl , one-eq-redirect t x m m e refl (inj₁ refl))
  in (m ∷ [] , canon-one _ , inj₂ H)
insertCᵌ-spec-one t x c
  | lt3 _ _ l =
  let H : Σ LaurentTerm (λ h → Σ Laurent (λ r →
            x ∷ (t ∷ []) ≡ h ∷ r
            × ((h ≡ t) ⊎ InT h (x ∷ []) ⊎ (proj₂ h ≡ proj₂ t))))
      H = (x , (t ∷ []) , refl , inj₂ (inj₁ (here x [])))
  in (x ∷ (t ∷ []) , canon-cons x t [] l (canon-one t) , inj₂ H)

-- ────────────────────────────────────────────────────────────────────
-- 主定理
-- ────────────────────────────────────────────────────────────────────

-- InT 成员的界：h ∈ x₂ ∷ xs ⟹ exp h < exp x
--   （x₂ 的界由调用方以 p 提供：here 时 h = x₂）
inT-bound : ∀ (x : LaurentTerm) (x₂ : LaurentTerm) (xs : Laurent) →
  proj₂ x₂ < proj₂ x → Canon (x₂ ∷ xs) →
  ∀ (h : LaurentTerm) → InT h (x₂ ∷ xs) → proj₂ h < proj₂ x
inT-bound x x₂ xs p s h (here .x₂ .xs) = p
inT-bound x x₂ xs p s h (there .h .x₂ .xs wit'') =
  <-trans (canon-<-head s h wit'') p

-- 后插分支组装：内层 w-规格的两路来源 ⟹ 外层（结果头为 x）
lt3-cons : ∀ (t x x₂ : LaurentTerm) (xs : Laurent) →
  proj₂ x₂ < proj₂ x → proj₂ t < proj₂ x → Canon (x₂ ∷ xs) →
  (w' : Laurent) → Canon w' →
  ((w' ≡ x₂ ∷ xs)
   ⊎ (Σ LaurentTerm (λ h → Σ Laurent (λ r →
        w' ≡ h ∷ r × ((h ≡ t) ⊎ InT h (x₂ ∷ xs) ⊎ (proj₂ h ≡ proj₂ t))))))
  → SpecT t (x ∷ x₂ ∷ xs)
lt3-cons t x x₂ xs p l s w' cw' dj' with dj'
... | inj₁ weq =
  (x ∷ (x₂ ∷ xs) , canon-cons x x₂ xs p s
  , inj₁ (inj₁ refl))
... | inj₂ (h , r , eq , src) =
  let Cn : Canon (x ∷ (h ∷ r))
      Cn = canon-cons x h r (bound-fun h src) (subst (λ v → Canon v) eq cw')
      H : Σ LaurentTerm (λ h₀ → Σ Laurent (λ r₀ →
            x ∷ (h ∷ r) ≡ h₀ ∷ r₀
            × ((h₀ ≡ t) ⊎ InT h₀ (x ∷ x₂ ∷ xs) ⊎ (proj₂ h₀ ≡ proj₂ t))))
      H = (x , (h ∷ r) , refl , inj₂ (inj₁ (here x (x₂ ∷ xs))))
  in (x ∷ (h ∷ r) , Cn , inj₂ H)
  where
  bound-fun : ∀ (h : LaurentTerm) →
    ((h ≡ t) ⊎ InT h (x₂ ∷ xs) ⊎ (proj₂ h ≡ proj₂ t)) → proj₂ h < proj₂ x
  bound-fun h (inj₁ h≡t) = subst (λ e → e < proj₂ x) (sym (cong proj₂ h≡t)) l
  bound-fun h (inj₂ (inj₁ wit)) = inT-bound x x₂ xs p s h wit
  bound-fun h (inj₂ (inj₂ eh≡et)) = subst (λ e → e < proj₂ x) (sym eh≡et) l

