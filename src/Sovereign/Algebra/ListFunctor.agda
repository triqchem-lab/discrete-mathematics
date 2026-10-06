{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Algebra.ListFunctor
-- List 泛型 map 定理完整清单（续）——自由 monoid 律 + 函子层 + 自然变换
--
-- 承接 ListLaws（map 基本律 + foldr 融合律），本模块闭合清单剩余项：
--   §1 自由 monoid 律：++-assoc / ++-identityˡ / ++-identityʳ
--   §2 reverse 交互：map-reverse（自然变换实例的核心等式）
--   §3 filter 交互：map-filter 条件交换
--   §4 Functor record + ListFunctor 实例（泛型代数函子层接口）
--   §5 NaturalTransformation record + reverse 实例 + negate 同态（数论连接）
--
-- 全结构归纳，逐点纪律（无 funext），0 postulate / 0 hole。
module Sovereign.Algebra.ListFunctor where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Function.Base using (_∘_)
open import Data.List using (List; _∷_; [])
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; cong₂; trans; sym)
open import Relation.Nullary using (¬_)
open import Data.Empty using (⊥)

--------------------------------------------------------------------------------
-- §0. 基础定义（自包含，与 ListLaws 同形）
--------------------------------------------------------------------------------

map : ∀ {A B : Set} → (A → B) → List A → List B
map f []       = []
map f (x ∷ xs) = f x ∷ map f xs

_++_ : ∀ {A : Set} → List A → List A → List A
[]       ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

reverse : ∀ {A : Set} → List A → List A
reverse []       = []
reverse (x ∷ xs) = reverse xs ++ (x ∷ [])

filter : ∀ {A : Set} → (A → Bool) → List A → List A
filter p []       = []
filter p (x ∷ xs) = if p x then x ∷ filter p xs else filter p xs

--------------------------------------------------------------------------------
-- §1. 自由 monoid 律——List A 是 A 生成的自由 monoid
--------------------------------------------------------------------------------

++-assoc : ∀ {A : Set} (xs ys zs : List A) →
           (xs ++ ys) ++ zs ≡ xs ++ (ys ++ zs)
++-assoc []       ys zs = refl
++-assoc (x ∷ xs) ys zs = cong (x ∷_) (++-assoc xs ys zs)

++-identityˡ : ∀ {A : Set} (xs : List A) → [] ++ xs ≡ xs
++-identityˡ xs = refl

++-identityʳ : ∀ {A : Set} (xs : List A) → xs ++ [] ≡ xs
++-identityʳ []       = refl
++-identityʳ (x ∷ xs) = cong (x ∷_) (++-identityʳ xs)

--------------------------------------------------------------------------------
-- §2. reverse 交互——map-reverse
--
--   归纳步需要 ++-assoc 重排：
--   map f (reverse (x∷xs)) = map f (reverse xs ++ [x])
--     = map f (reverse xs) ++ [f x]          (map-++)
--     = reverse (map f xs) ++ [f x]          (IH)
--     = reverse (f x ∷ map f xs)             (reverse 定义)
--------------------------------------------------------------------------------

map-++ : ∀ {A B : Set} (f : A → B) (xs ys : List A) →
         map f (xs ++ ys) ≡ map f xs ++ map f ys
map-++ f []       ys = refl
map-++ f (x ∷ xs) ys = cong (f x ∷_) (map-++ f xs ys)

map-reverse : ∀ {A B : Set} (f : A → B) (xs : List A) →
              map f (reverse xs) ≡ reverse (map f xs)
map-reverse f []       = refl
map-reverse f (x ∷ xs) = trans (map-++ f (reverse xs) (x ∷ []))
                               (cong (_++ (f x ∷ [])) (map-reverse f xs))
-- map f (reverse xs ++ [x]) = map f (reverse xs) ++ [f x]   (map-++)
--                           = reverse (map f xs) ++ [f x]   (IH + cong)
--                           = reverse (f x ∷ map f xs)      (定义性)

--------------------------------------------------------------------------------
-- §3. filter 交互——map-filter 条件交换
--
--   filter p (map f xs) ≡ map f (filter (p ∘ f) xs)
--   对每元素按 p (f x) 分情况，两 case 各 cong 归纳。
--------------------------------------------------------------------------------

map-filter : ∀ {A B : Set} (f : A → B) (p : B → Bool) (xs : List A) →
             filter p (map f xs) ≡ map f (filter (λ x → p (f x)) xs)
map-filter f p []       = refl
map-filter f p (x ∷ xs) with p (f x)
... | true  = cong (f x ∷_) (map-filter f p xs)
... | false = map-filter f p xs

--------------------------------------------------------------------------------
-- §4. Functor record——泛型代数的函子层接口
--------------------------------------------------------------------------------

record Functor (F : Set → Set) : Set₁ where
  field
    fmap     : ∀ {A B} → (A → B) → F A → F B
    fmap-id  : ∀ {A} (x : F A) → fmap (λ a → a) x ≡ x
    fmap-∘   : ∀ {A B C} (f : B → C) (g : A → B) (x : F A) →
               fmap (f ∘ g) x ≡ fmap f (fmap g x)

-- map-∘ 引理（ListFunctor 需要）
map-∘ : ∀ {A B C : Set} (f : B → C) (g : A → B) (xs : List A) →
        map (λ x → f (g x)) xs ≡ map f (map g xs)
map-∘ f g []       = refl
map-∘ f g (x ∷ xs) = cong (f (g x) ∷_) (map-∘ f g xs)

ListFunctor : Functor List
ListFunctor = record
  { fmap    = map
  ; fmap-id = map-id′
  ; fmap-∘  = map-∘-alt
  }
  where
    map-id′ : ∀ {A : Set} (xs : List A) → map (λ a → a) xs ≡ xs
    map-id′ []       = refl
    map-id′ (x ∷ xs) = cong (x ∷_) (map-id′ xs)

    map-∘-alt : ∀ {A B C : Set} (f : B → C) (g : A → B) (xs : List A) →
                map (λ x → f (g x)) xs ≡ map f (map g xs)
    map-∘-alt = map-∘

--------------------------------------------------------------------------------
-- §5. NaturalTransformation record + 实例
--------------------------------------------------------------------------------

record NaturalTransformation (F G : Set → Set)
         (𝔽 : Functor F) (𝔾 : Functor G) : Set₁ where
  field
    η          : ∀ {A} → F A → G A
    naturality : ∀ {A B} (f : A → B) (x : F A) →
                 η (Functor.fmap 𝔽 f x) ≡ Functor.fmap 𝔾 f (η x)

-- 实例：reverse 是 List→List 的自然变换
-- naturality 即 map-reverse 的直接重述
ReverseNT : NaturalTransformation List List ListFunctor ListFunctor
ReverseNT = record
  { η          = reverse
  ; naturality = λ f xs → sym (map-reverse f xs)
  }

--------------------------------------------------------------------------------
-- §5b. 数论连接——GF(3) negate 是 ⊕-群同态（自由模系数重排基础）
--
--   negate (x ⊕ y) ≡ negate x ⊕ negate y（9 case refl，<27 ✓）
--   这是「系数取负与求和交换」——FAb 系数重排的数论根基。
--------------------------------------------------------------------------------

open import Sovereign.Base.Trit using (Trit; T₀; T₁; T₂; _⊕_; negate)

negate-hom : ∀ (x y : Trit) → negate (x ⊕ y) ≡ negate x ⊕ negate y
negate-hom T₀ T₀ = refl
negate-hom T₀ T₁ = refl
negate-hom T₀ T₂ = refl
negate-hom T₁ T₀ = refl
negate-hom T₁ T₁ = refl
negate-hom T₁ T₂ = refl
negate-hom T₂ T₀ = refl
negate-hom T₂ T₁ = refl
negate-hom T₂ T₂ = refl

-- negate 与 map 交换（逐元素同态提升到列表）
map-negate : ∀ (xs : List Trit) →
             map negate (map negate xs) ≡ xs
map-negate []       = refl
map-negate (x ∷ xs) =
  cong₂ _∷_ (neg-selfinv-loc x) (map-negate xs)
  where
    neg-selfinv-loc : (x : Trit) → negate (negate x) ≡ x
    neg-selfinv-loc T₀ = refl
    neg-selfinv-loc T₁ = refl
    neg-selfinv-loc T₂ = refl

--------------------------------------------------------------------------------
-- §6. 完成度——泛型 map 定理完整清单闭合
--
--   ✅ 自由 monoid 律 ×3：++-assoc / ++-identityˡ / ++-identityʳ
--   ✅ map-reverse（自然变换核心等式，++-assoc + map-++ + IH 三步链）
--   ✅ map-filter（条件交换，Bool 分情况）
--   ✅ Functor record + ListFunctor 实例（fmap-id / fmap-∘）
--   ✅ NaturalTransformation record + ReverseNT 实例
--   ✅ 数论连接：negate-hom（GF(3) 加法同态，9 case）+ map-negate（对合）
--
--   对泛型代数的理论价值：
--   - Functor/NT record = 泛型代数的抽象接口层（FAb/链群可实例化）
--   - negate-hom = 系数重排（FAb 系数取负与求和交换）的数论根基
--   - reverse NT = M5-M7 链同伦的范畴语言预演
--
--   清单状态：核心 9 项全部闭合（ListLaws 6 项 + 本模块 6 项）；
--   map-foldr 另方向融合（B=List C 时）留 roadmap（当前无消费者）。
--------------------------------------------------------------------------------
