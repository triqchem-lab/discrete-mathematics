{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Algebra.ListLaws
-- List 泛型律——M4 链映射的底层操作基座（逐点纪律，无 funext）
--
-- 数学内容（结构归纳对应 List 两构造子 [] / _∷_）：
--   map-id / map-cong / map-length / map-++  —— map 基本律
--   foldr-map 融合律 —— foldr g e ∘ map f ≡ foldr (g ∘ f) e
--   Morse 连接：sum⊕ ≡ foldr (λ x acc → x ⊕ acc) T₀ 的融合对账
--
-- 所有定理构造性闭合（refl + cong/cong₂ + 归纳假设），0 postulate。
module Sovereign.Algebra.ListLaws where

open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; _∷_; [])
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; cong₂)

--------------------------------------------------------------------------------
-- §1. 基础定义（自包含——不依赖 Data.List 的 map/foldr，避免签名纠缠）
--------------------------------------------------------------------------------

map : ∀ {A B : Set} → (A → B) → List A → List B
map f []       = []
map f (x ∷ xs) = f x ∷ map f xs

_++_ : ∀ {A : Set} → List A → List A → List A
[]       ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

length : ∀ {A : Set} → List A → ℕ
length []       = zero
length (x ∷ xs) = suc (length xs)

foldr : ∀ {A B : Set} → (A → B → B) → B → List A → B
foldr f e []       = e
foldr f e (x ∷ xs) = f x (foldr f e xs)

--------------------------------------------------------------------------------
-- §2. map 基本律（结构归纳——每定理两分支）
--------------------------------------------------------------------------------

-- 2.1 恒等律
map-id : ∀ {A : Set} (xs : List A) → map (λ x → x) xs ≡ xs
map-id []       = refl
map-id (x ∷ xs) = cong (x ∷_) (map-id xs)

-- 2.2 同余律（逐点版——无 funext）
map-cong : ∀ {A B : Set} {f g : A → B} (h : ∀ x → f x ≡ g x) (xs : List A) →
           map f xs ≡ map g xs
map-cong h []       = refl
map-cong h (x ∷ xs) = cong₂ _∷_ (h x) (map-cong h xs)

-- 2.3 长度保持
map-length : ∀ {A B : Set} (f : A → B) (xs : List A) →
             length (map f xs) ≡ length xs
map-length f []       = refl
map-length f (x ∷ xs) = cong suc (map-length f xs)

-- 2.4 与 append 的交互（map 是自由 monoid 同态）
map-++ : ∀ {A B : Set} (f : A → B) (xs ys : List A) →
         map f (xs ++ ys) ≡ map f xs ++ map f ys
map-++ f []       ys = refl
map-++ f (x ∷ xs) ys = cong (f x ∷_) (map-++ f xs ys)

--------------------------------------------------------------------------------
-- §3. foldr 融合律——map 与 foldr 的交换
--
--   foldr-map：foldr g e (map f xs) ≡ foldr (λ x acc → g (f x) acc) e xs
--   即 foldr g e ∘ map f ≡ foldr (g ∘ f) e（用户修正版：尾递归 cong）
--------------------------------------------------------------------------------

foldr-map : ∀ {A B C : Set} (f : A → B) (g : B → C → C) (e : C) (xs : List A) →
            foldr g e (map f xs) ≡ foldr (λ x acc → g (f x) acc) e xs
foldr-map f g e []       = refl
foldr-map f g e (x ∷ xs) =
  cong (g (f x)) (foldr-map f g e xs)

--------------------------------------------------------------------------------
-- §4. Morse 连接——sum⊕ 是 foldr 的实例
--
--   MorseRouteListG/MorseSqZeroFull 的系数求和（⊕ 折叠）满足融合律：
--   对 Trit 列表，sum⊕ ≡ foldr _⊕_ T₀（定义性一致），
--   于是 foldr-map 给出「先 map 后求和 = 先融合后求和」的泛型形式。
--------------------------------------------------------------------------------

open import Sovereign.Base.Trit using (Trit; T₀; _⊕_)

sum⊕ : List Trit → Trit
sum⊕ = foldr _⊕_ T₀

-- 融合实例：先 negate 再求和 ≡ 融合后求和（map-neg ⊕ sum 融合）
-- 对应 M4 链映射场景：链映射作用在链上（map Ψ）后取边界（sum⊕）
-- 与「边界逐项作用后再求和」一致——链映射的自然性基础。
map-sum-fusion :
  ∀ (f : Trit → Trit) (xs : List Trit) →
  sum⊕ (map f xs) ≡ foldr (λ x acc → f x ⊕ acc) T₀ xs
map-sum-fusion f xs = foldr-map f _⊕_ T₀ xs

--------------------------------------------------------------------------------
-- §5. 完成度
--
--   ✅ 基础定义：map / _++_ / length / foldr（自包含）
--   ✅ map 基本律 ×4：map-id / map-cong（逐点）/ map-length / map-++
--   ✅ foldr 融合律：foldr-map（用户修正版）
--   ✅ Morse 连接：sum⊕ = foldr _⊕_ T₀ + map-sum-fusion
--      （M4 链映射的自然性基础——链映射∘求和 = 融合求和）
--
--   复用指引：
--   - M4 ChainHom 的 naturality 直接用 map-sum-fusion 实例化
--   - MorseSqZeroFull.sumFull 的融合版可由 map-sum-fusion 推导（roadmap）
--
--   未做（清单剩余项）：map-reverse / map-filter / Functor record /
--   NaturalTransformation record——按需启动（当前无消费者）。
--------------------------------------------------------------------------------
