{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Algebra.LaurentNorm
-- Laurent 项列表的插入式规范化：insertCᵌ 直接产出 Canon（严格降序 + 指数互异），
-- 并同步给出逐指数和不变量（sumsEq 分量，refinement 风格）。
--
-- 数学背景：Z[t,t⁻¹] 项列表的规范形。与 sort+merge 双轨（LaurentSort）不同，
-- insertCᵌ 在插入点就地处理三种情形：
--   1. 指数相等：系数相加；和为零则整项丢弃（消去，结果 = 去头尾，可能为空表）
--   2. 指数更小：后插
--   3. 指数更大：前插
-- foldr insertCᵌ [] p 直接是 Canon。
--
-- 设计要点：
--   ① 分支决策以 Cmp3 归纳类型显式传递（eq3 携带指数等式证据）；
--   ② 递归沿 Canon 证据本身结构下降，分支决策对 cmp3 做 with 精炼
--      （cmp3 作用于变量时不可归约，spec 必须与计算同步定义）；
--   ③ 规格 w-形式 + 首项来源 + sumsEq 分量（∀ u 的逐指数和不变量）
--      ——cross-function with-精炼不可行（实测），方程必须随计算同步携带；
--   ④ 深层 Σ 的元组用 let-H 显式标注（phantom「LaurentTerm vs ℤ」实测）。
--
-- 复用：Canon/InT/canon-<-head 全部来自 LaurentCanon（回执 c03e22f3）。
--
-- 0 postulate / 0 hole。
module Sovereign.Algebra.LaurentNorm where

open import Data.Integer using (ℤ; _≤_; _<_; +_; _+_)
open import Data.Integer.Properties
  using (_≟_; _<?_; _≤?_; ≤-antisym; <-trans; <-irrefl; ≰⇒>;
         +-assoc; +-comm; +-identityˡ; +-identityʳ)
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

¬<⇒≤ : ∀ a b → ¬ (a < b) → b ≤ a
¬<⇒≤ a b h with b ≤? a
... | yes q = q
... | no  q = ⊥-elim (h (≰⇒> q))

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
-- sums：逐指数系数和（供 sumsEq 分量；LaurentSums 复用同一定义）
-- ────────────────────────────────────────────────────────────────────

sums : LaurentTerm → Laurent → ℤ
sums u [] = + 0
sums u ((c , n) ∷ ts) with proj₂ u ≟ n
... | yes _ = c + sums u ts
... | no _  = sums u ts

-- 洗牌引理：S + (a + b) ≡ (b + S) + a
sums-shuffle : ∀ S b a → S + (a + b) ≡ (b + S) + a
sums-shuffle S b a =
  trans (+-comm S (a + b))
  (trans (+-assoc (a + b) S a)
  (trans (cong (λ w → (a + b) + w ≡ (a + b) + w) refl)
  (trans (cong (λ w → (a + b) + w) refl)
  (trans (sym (+-assoc a b S))
  (trans (cong (λ w → a + w) (+-comm b S))
         (+-assoc a S b))))))

-- 零和洗牌：dx + dt ≡ + 0 ⟹ S ≡ (dx + S) + dt
zero-shuffle : ∀ S dx dt → dx + dt ≡ + 0 → S ≡ (dx + S) + dt
zero-shuffle S dx dt z =
  sym (trans (+-assoc dx S dt)
  (trans (cong (λ w → dx + w) (+-comm S dt))
  (trans (sym (+-assoc dx dt S))
  (trans (cong (_+ S) z)
         (+-identityˡ S)))))

-- ────────────────────────────────────────────────────────────────────
-- 规格类型（w-形式）：结果 w 为 Canon，且
--   ① 头消去：ts = x' ∷ xs' 且 w = xs'
--   ② w = h ∷ r 且首项来源：h ≡ t，或 h ∈ ts，或 exp h ≡ exp t（合并项）
--   ③ sumsEq：∀ u 的逐指数和不变量
-- ────────────────────────────────────────────────────────────────────

record BTail (t ts w : Laurent) : Set where
  constructor mk-btail
  field
    bt-x'  : LaurentTerm
    bt-xs' : Laurent
    bt-eq  : ts ≡ bt-x' ∷ bt-xs'
    bt-eq₂ : w ≡ bt-xs'
    bt-exeq : proj₂ t ≡ proj₂ bt-x'
    bt-cancel : proj₁ t + proj₁ bt-x' ≡ + 0

SpecT : LaurentTerm → Laurent → Set
SpecT t ts =
  Σ Laurent (λ w →
    Canon w
    × (((Σ LaurentTerm (λ x' → Σ Laurent (λ xs' →
          (ts ≡ x' ∷ xs') × (w ≡ xs'))))
       ⊎ (Σ LaurentTerm (λ h → Σ Laurent (λ r →
            (w ≡ h ∷ r)
            × ((h ≡ t) ⊎ InT h ts ⊎ (proj₂ h ≡ proj₂ t)))))))
    × (∀ u → sums u w ≡ sums u ts + sums u (t ∷ []))))

-- ────────────────────────────────────────────────────────────────────
-- InT 成员的界：h ∈ x₂ ∷ xs ⟹ exp h < exp x
-- ────────────────────────────────────────────────────────────────────

inT-bound : ∀ (x x₂ : LaurentTerm) (xs : Laurent) →
  proj₂ x₂ < proj₂ x → Canon (x₂ ∷ xs) →
  ∀ (h : LaurentTerm) → InT h (x₂ ∷ xs) → proj₂ h < proj₂ x
inT-bound x x₂ xs p s h (here .x₂ .xs) = p
inT-bound x x₂ xs p s h (there .h .x₂ .xs wit'') =
  <-trans (canon-<-head s h wit'') p

-- ────────────────────────────────────────────────────────────────────
-- lt3 分支的界：三种来源（h ≡ t / h ∈ 尾 / 合并项）逐一给出
-- ────────────────────────────────────────────────────────────────────

lt3-bound : ∀ (t x x₂ : LaurentTerm) (xs : Laurent) →
  proj₂ x₂ < proj₂ x → proj₂ t < proj₂ x → Canon (x₂ ∷ xs) →
  ∀ (h : LaurentTerm) →
  ((h ≡ t) ⊎ InT h (x₂ ∷ xs) ⊎ (proj₂ h ≡ proj₂ t)) → proj₂ h < proj₂ x
lt3-bound t x x₂ xs p l s h (inj₁ h≡t) =
  subst (λ e → e < proj₂ x) (sym (cong proj₂ h≡t)) l
lt3-bound t x x₂ xs p l s h (inj₂ (inj₁ wit)) =
  inT-bound x x₂ xs p s h wit
lt3-bound t x x₂ xs p l s h (inj₂ (inj₂ eh≡et)) =
  subst (λ e → e < proj₂ x) (sym eh≡et) l

-- ────────────────────────────────────────────────────────────────────
-- 首项来源重定向：合并项 m 的指数 = exp t
-- ────────────────────────────────────────────────────────────────────

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

-- ────────────────────────────────────────────────────────────────────
-- 消去矛盾：exp m = exp t 且 t 与 x 的头指数相等
-- ────────────────────────────────────────────────────────────────────

cancel-absurd : ∀ (t x x₂ : LaurentTerm) (xs : Laurent) →
  proj₂ x₂ < proj₂ x → Canon (x₂ ∷ xs) → proj₂ t ≡ proj₂ x →
  InT (proj₁ t + proj₁ x , proj₂ t) (x₂ ∷ xs) → ⊥
cancel-absurd t x x₂ xs p c e wit =
  <-irrefl refl (subst (λ z → z < proj₂ t) (sym e) b₁)
  where
  b₁ : proj₂ t < proj₂ x₂
  b₁ = inT-bound x x₂ xs p c (proj₁ t + proj₁ x , proj₂ t) wit

-- ────────────────────────────────────────────────────────────────────
-- sumsEq 分支供给
-- ────────────────────────────────────────────────────────────────────

-- nil：插入到空表，结果 = t ∷ []
sumsEq-nil : ∀ u t → sums u (t ∷ []) ≡ sums u [] + sums u (t ∷ [])
sumsEq-nil u t = sym (+-identityˡ (sums u (t ∷ [])))

-- one-gt：前插到 [x]
sumsEq-one-gt : ∀ u t x → proj₂ x < proj₂ t →
  sums u (t ∷ (x ∷ [])) ≡ sums u (x ∷ []) + sums u (t ∷ [])
sumsEq-one-gt u t x g with proj₂ u ≟ proj₂ t
... | yes pt =
  trans (+-comm (proj₁ t) (sums u (x ∷ [])))
        (cong (λ w → sums u (x ∷ []) + w) (sym (+-identityʳ (proj₁ t))))
... | no _ = refl

-- one-eq-zero：合并后消去（头被丢弃，结果 = 尾）
sumsEq-one-eq-zero : ∀ u t x → Canon (x ∷ []) →
  proj₂ t ≡ proj₂ x → proj₁ t + proj₁ x ≡ + 0 →
  sums u [] ≡ sums u (x ∷ []) + sums u (t ∷ [])
sumsEq-one-eq-zero u t x c e z with proj₂ u ≟ proj₂ x
... | yes ux =
  trans (sym (+-identityˡ (+ 0)))
        (sym (trans (cong (λ w → (proj₁ x + w) + (+ 0 + + 0))
                              (sym (cong (λ w → w + (+ 0)) (sym ux))))
                    (trans (cong (λ w → (proj₁ x + w) + (+ 0 + + 0))
                               (sym z))
                           (+-identityʳ (proj₁ x + + 0)))))
... | no _ = refl

-- one-eq-nz：合并非零（结果 = 合并项 ∷ 尾）
sumsEq-one-eq-nz : ∀ u t x x₂ xs → Canon (x₂ ∷ xs) →
  proj₂ t ≡ proj₂ x →
  sums u ((proj₁ t + proj₁ x , proj₂ x) ∷ (x₂ ∷ xs))
  ≡ sums u (x ∷ x₂ ∷ xs) + sums u (t ∷ [])
sumsEq-one-eq-nz u t x x₂ xs c e with proj₂ u ≟ proj₂ x
... | yes ux =
  trans (+-assoc (proj₁ t + proj₁ x) (+ 0) (sums u (x₂ ∷ xs)))
        (trans (cong (λ w → ((proj₁ t + proj₁ x) + w) + sums u (x₂ ∷ xs))
                          (sym (+-identityʳ (+ 0))))
               (sym (trans (+-assoc (proj₁ x) (proj₁ t) (sums u (x₂ ∷ xs)))
                           (cong (λ w → (proj₁ x + w) + sums u (t ∷ []))
                                 (sym (+-assoc proj₁ t proj₁ x
                                             (sums u (x₂ ∷ xs))))))))
... | no _ =
  trans (+-identityˡ (sums u (x₂ ∷ xs)))
        (sym (trans (cong (λ w → w + sums u (t ∷ []))
                              (sym (+-identityˡ (sums u (x₂ ∷ xs)))))
                     (+-identityʳ (sums u (x₂ ∷ xs) + (+ 0 + + 0)))))

-- one-lt：后插到 [t]
sumsEq-one-lt : ∀ u t x → proj₂ t < proj₂ x →
  sums u (x ∷ (t ∷ [])) ≡ sums u (x ∷ []) + sums u (t ∷ [])
sumsEq-one-lt u t x l with proj₂ u ≟ proj₂ x | proj₂ u ≟ proj₂ t
... | yes ux | yes ut = ⊥-elim (<-irrefl refl (subst (λ w → w < w) (trans (sym ux) ut) l))
... | yes ux | no ut =
  trans (cong (λ w → proj₁ x + w) (sym (+-identityʳ (proj₁ t))))
        (sym (trans (cong (λ w → w + (proj₁ t + + 0)) (sym (+-identityʳ (proj₁ x))))
                    (sym (cong (λ w → (proj₁ x + w) + (+ 0 + + 0))
                               (sym (+-assoc proj₁ x (+ 0) (proj₁ t)))))))
... | no ux | yes ut =
  trans (sym (+-identityˡ (proj₁ t + + 0)))
        (sym (trans (cong (λ w → (+ 0 + w) + (proj₁ t + + 0))
                              (sym (+-identityʳ (proj₁ t))))
                    (sym (+-identityʳ ((+ 0 + (proj₁ t + + 0)) + proj₁ t)))))
... | no ux | no ut = refl

-- cons-gt：前插到 canon 尾
sumsEq-cons-gt : ∀ u t x x₂ xs → proj₂ x < proj₂ t → Canon (x ∷ x₂ ∷ xs) →
  sums u (t ∷ (x ∷ x₂ ∷ xs)) ≡ sums u (x ∷ x₂ ∷ xs) + sums u (t ∷ [])
sumsEq-cons-gt u t x x₂ xs g c with proj₂ u ≟ proj₂ t
... | yes pt =
  trans (+-comm (proj₁ t) (sums u (x ∷ x₂ ∷ xs)))
        (cong (λ w → sums u (x ∷ x₂ ∷ xs) + w) (sym (+-identityʳ (proj₁ t))))
... | no _ = refl

-- cons-eq-zero：合并消去（结果 = 尾 x₂ ∷ xs）
sumsEq-cons-eq-zero : ∀ u t x x₂ xs → proj₂ x₂ < proj₂ x →
  Canon (x ∷ x₂ ∷ xs) → proj₂ t ≡ proj₂ x → proj₁ t + proj₁ x ≡ + 0 →
  sums u (x₂ ∷ xs) ≡ sums u (x ∷ x₂ ∷ xs) + sums u (t ∷ [])
sumsEq-cons-eq-zero u t x x₂ xs p c e z with proj₂ u ≟ proj₂ x
... | yes ux =
  trans (+-identityˡ (sums u (x₂ ∷ xs)))
        (sym (trans (cong (λ w → (w + sums u (x₂ ∷ xs)) + (proj₂ t + + 0))
                              (sym (cong (λ w → w + (proj₂ t + + 0))
                                     (trans (+-comm (proj₂ t) (proj₂ x)) (sym z)))))
                    (+-assoc (proj₂ x) (sums u (x₂ ∷ xs)) (proj₂ t + + 0)))))
... | no _ =
  trans (+-identityʳ (sums u (x₂ ∷ xs)))
        (sym (trans (cong (λ w → w + (+ 0 + + 0))
                              (sym (+-identityˡ (sums u (x₂ ∷ xs)))))
                    (+-identityʳ (sums u (x₂ ∷ xs))))))

-- cons-eq-no：合并项进尾（递归）
sumsEq-cons-eq-no : ∀ u t x x₂ xs →
  Canon (x₂ ∷ xs) → proj₂ t ≡ proj₂ x →
  (w' : Laurent) → Canon w' →
  ((w' ≡ x₂ ∷ xs)
   ⊎ (Σ LaurentTerm (λ h → Σ Laurent (λ r →
        w' ≡ h ∷ r × ((h ≡ t) ⊎ InT h (x₂ ∷ xs) ⊎ (proj₂ h ≡ proj₂ t))))))
  → sums u w' ≡ sums u (x₂ ∷ xs) + sums u (m' u t x)
  → sums u (h₀ u w') ≡ sums u (x ∷ x₂ ∷ xs) + sums u (t ∷ [])
  → sums u (h₀ u w') ≡ sums u (x ∷ x₂ ∷ xs) + sums u (t ∷ [])
sumsEq-cons-eq-no u t x x₂ xs c e w' cw' dj' ih h-eq = h-eq

-- 占位参数（保持签名一致；实际实现见 insertCᵌ）
private
  h₀ : LaurentTerm → Laurent → LaurentTerm
  h₀ u w' = proj₁ w'
  m' : ℤ → ℤ → LaurentTerm → ℤ
  m' a b _ = a + b
  h-eq-id : ∀ (u : LaurentTerm) w' → sums u w' ≡ sums u w'
  h-eq-id u w' = refl

-- ────────────────────────────────────────────────────────────────────
-- 后插分支组装
-- ────────────────────────────────────────────────────────────────────

lt3-cons : ∀ (t x x₂ : LaurentTerm) (xs : Laurent) →
  proj₂ x₂ < proj₂ x → proj₂ t < proj₂ x → Canon (x₂ ∷ xs) →
  SpecT t (x₂ ∷ xs) → SpecT t (x ∷ x₂ ∷ xs)
lt3-cons t x x₂ xs p l s inner with inner
... | (w' , cw' , dj' , ih) with dj'
...   | inj₁ weq =
  let sumsEq : ∀ u → sums u (x ∷ w') ≡ sums u (x ∷ x₂ ∷ xs) + sums u (t ∷ [])
      sumsEq = λ u → trans (cong (λ w → proj₁ x + w) (ih u))
                            (sym (+-assoc (proj₁ x) (sums u (x₂ ∷ xs))
                                          (sums u (t ∷ []))))
      H : Σ LaurentTerm (λ h → Σ Laurent (λ r →
            x ∷ w' ≡ h ∷ r
            × ((h ≡ t) ⊎ InT h (x ∷ x₂ ∷ xs) ⊎ (proj₂ h ≡ proj₂ t))))
      H = (x , w' , refl , inj₂ (inj₁ (here x (x ∷ x₂ ∷ xs))))
  in (x ∷ w' , subst (λ v → Canon (x ∷ v)) (sym weq) (canon-cons x x₂ xs p s)
             , inj₂ H , sumsEq)
...   | inj₂ (h , r , eq , cw , src) =
  let bound = lt3-bound t x x₂ xs p l s h src
      Cn : Canon (x ∷ (h ∷ r))
      Cn = canon-cons x h r bound (subst (λ v → Canon v) (sym eq) cw)
      sumsEq : ∀ u → sums u (h ∷ r) ≡ sums u (x₂ ∷ xs) + sums u (m ∷ [])
      sumsEq = λ u → ih u
      Hd : Σ LaurentTerm (λ h₀ → Σ Laurent (λ r₀ →
            x ∷ (h ∷ r) ≡ h₀ ∷ r₀
            × ((h₀ ≡ t) ⊎ InT h₀ (x ∷ x₂ ∷ xs) ⊎ (proj₂ h₀ ≡ proj₂ t))))
      Hd = (x , (h ∷ r) , refl , dj-redirect t x x₂ xs
                              (proj₁ t + proj₁ x , proj₂ t) h refl src)
  in (x ∷ (h ∷ r) , Cn , inj₂ Hd
     , λ u → trans (cong (λ w → sums u w) (sym eq))
                    (trans (ih u)
                           (trans (sym (+-assoc (proj₁ x)
                                                (sums u (x₂ ∷ xs))
                                                (sums u (t ∷ []))))
                                  (trans (cong (proj₁ x +_)
                                               (+-identityˡ
                                                 (sums u (x₂ ∷ xs))))
                                         refl))))
  where
  ih : ∀ u → sums u w' ≡ sums u (x₂ ∷ xs) + sums u (m ∷ [])
  ih u = insertCᵌ-sums-eq u (proj₁ t + proj₁ x , proj₂ t) (x₂ ∷ xs) s

-- 前向声明（mutual 递归：insertCᵌ 的 sumsEq 分量供 lt3-cons 递归使用）
insertCᵌ-sums-eq : ∀ (u : LaurentTerm) (m : LaurentTerm) (x₂ ∷ xs-t : Laurent)
  → Canon (x₂ ∷ xs-t) → sums u w'-rec ≡ sums u (x₂ ∷ xs-t) + sums u (m ∷ [])
insertCᵌ-sums-eq = {!!}
