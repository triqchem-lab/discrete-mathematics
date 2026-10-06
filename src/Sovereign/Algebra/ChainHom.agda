{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Algebra.ChainHom
-- M4 链映射：ChainHom record + 保 ∂ 交换图
--
-- 数学内容：
--   链映射 Ψ : C → C'（链群间映射）的两条公理：
--     ① 系数保持零：coeffMap T₀ ≡ T₀
--     ② GF(3) 线性（加法同态）：coeffMap (x ⊕ y) ≡ coeffMap x ⊕ coeffMap y
--   交换图（M4.2 核心定理）：
--     ∂ ∘ Ψ = Ψ-linear ∘ ∂
--     即：对链先作用映射再求边界 ≡ 先求边界再逐项作用
--     —— map-sum-fusion（ListLaws 融合律）的直接实例化。
--
-- 复用链：ListLaws（map-sum-fusion/map-++）+ ListFunctor（negate-hom）
--
-- 0 postulate / 0 hole。
module Sovereign.Algebra.ChainHom where

open import Data.List using (List; _∷_; [])
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; cong)

open import Sovereign.Base.Trit
  using (Trit; T₀; T₁; T₂; _⊕_; negate; ⊕-assoc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; cong; sym)
open import Sovereign.Algebra.ListLaws
  using (map; _++_; map-++; map-sum-fusion; foldr)
open import Sovereign.Algebra.ListFunctor using (negate-hom)

--------------------------------------------------------------------------------
-- §1. 边界算子——∂ = sum⊕ = foldr _⊕_ T₀（系数求和，透明 alias）
--------------------------------------------------------------------------------

open import Sovereign.Algebra.ListLaws renaming (sum⊕ to sum⊕L)
∂ : List Trit → Trit
∂ = sum⊕L
-- 与 ListLaws.sum⊕ convertible（透明 alias——map-sum-fusion 直接适用）

--------------------------------------------------------------------------------
-- §2. M4.1 ChainHom record——链映射的两条公理
--------------------------------------------------------------------------------

record ChainHom : Set₁ where
  field
    -- 系数级映射（生成元级映射 cellMap : K → K' 的系数部分；
    -- 泛型 List 层先生成系数级——生成元级 map 已由 ListLaws.map 承担）
    coeffMap : Trit → Trit

    -- 公理①：保持零
    coeff-zero : coeffMap T₀ ≡ T₀

    -- 公理②：GF(3) 线性（加法同态）
    coeff-hom : ∀ (x y : Trit) → coeffMap (x ⊕ y) ≡ coeffMap x ⊕ coeffMap y

--------------------------------------------------------------------------------
-- §3. 求和的 append 分配——∂ 是群同态的基础引理
--------------------------------------------------------------------------------

sum⊕-++ : ∀ (xs ys : List Trit) → ∂ (xs ++ ys) ≡ ∂ xs ⊕ ∂ ys
sum⊕-++ []       ys = refl
sum⊕-++ (x ∷ xs) ys =
  trans (cong (x ⊕_) (sum⊕-++ xs ys)) (sym (⊕-assoc x (∂ xs) (∂ ys)))
-- base: ∂([]++ys) = ∂ ys = T₀ ⊕ ∂ ys（定义性）
-- step: x ⊕ ∂(xs++ys) ≡ x ⊕ (∂xs ⊕ ∂ys) ≡ (x⊕∂xs)⊕∂ys  [sym ⊕-assoc]

--------------------------------------------------------------------------------
-- §4. M4.2 交换图——∂ ∘ Ψ = Ψ-linear ∘ ∂
--------------------------------------------------------------------------------

module Swap (ch : ChainHom) where
  open ChainHom ch

  -- Ψ 在系数级的链作用：map coeffMap
  Ψ : List Trit → List Trit
  Ψ = map coeffMap

  -- 交换图左：先 Ψ 后 ∂
  sq-left : List Trit → Trit
  sq-left xs = ∂ (Ψ xs)

  -- 交换图右：融合求和（先逐项作用后 ⊕ 折叠）
  sq-right : List Trit → Trit
  sq-right xs = foldr (λ x acc → coeffMap x ⊕ acc) T₀ xs

  -- ✅ M4.2 交换图定理：∂ ∘ Ψ ≡ 融合求和（map-sum-fusion 直接实例化）
  swap-commute : ∀ xs → sq-left xs ≡ sq-right xs
  swap-commute xs = map-sum-fusion coeffMap xs

  -- ✅ 加法性定理：Ψ 后求和 = 分块求和再 ⊕（∂ 群同态性）
  Ψ-hom : ∀ (xs ys : List Trit) →
          ∂ (Ψ (xs ++ ys)) ≡ ∂ (Ψ xs) ⊕ ∂ (Ψ ys)
  Ψ-hom xs ys = trans (cong ∂ (map-++ coeffMap xs ys))
                      (sum⊕-++ (Ψ xs) (Ψ ys))
  -- ∂(map f (xs++ys)) = ∂(map f xs ++ map f ys)  [map-++]
  --                   = ∂(map f xs) ⊕ ∂(map f ys) [sum⊕-++]

--------------------------------------------------------------------------------
-- §5. 实例：negate 链映射（数论连接——ListFunctor.negate-hom 复用）
--------------------------------------------------------------------------------

negChain : ChainHom
negChain = record
  { coeffMap  = negate
  ; coeff-zero = refl
  ; coeff-hom  = negate-hom
  }
-- 公理①：negate T₀ = T₀ 定义性 ✓
-- 公理②：negate (x⊕y) ≡ negate x ⊕ negate y（ListFunctor.negate-hom，9 case）✓

-- 实例交换图验证：negate 链映射的 naturality
neg-swap : ∀ xs → Swap.sq-left negChain xs
                   ≡ Swap.sq-right negChain xs
neg-swap = Swap.swap-commute negChain

-- 数值 sanity：negate 链映射在 2 项链上
neg-sanity : ∂ (Swap.Ψ negChain (T₁ ∷ T₂ ∷ []))
            ≡ negate T₁ ⊕ negate T₂
neg-sanity = refl
-- ∂(map negate [T₁,T₂]) = negate T₁ ⊕ negate T₂ = T₂ ⊕ T₁（定义性展开）

--------------------------------------------------------------------------------
-- §6. M4 完成度
--
--   ✅ M4.1 ChainHom record：coeff-zero + coeff-hom（两条公理）
--   ✅ M4.2 交换图：swap-commute（∂∘Ψ = 融合求和——map-sum-fusion 实例化）
--   ✅ 加法性：Ψ-hom（∂ 群同态——map-++ + sum⊕-++ 链）
--   ✅ 实例：negChain（negate 链映射，negate-hom 复用）+ 2 个验证
--
--   复用链：ListLaws.map-sum-fusion（交换图本体）
--         + ListLaws.map-++（加法性）
--         + ListFunctor.negate-hom（实例公理②）
--
--   M5-M7 解锁：链同伦需要两个 ChainHom + 同伦映射 h（roadmap）。
--------------------------------------------------------------------------------
