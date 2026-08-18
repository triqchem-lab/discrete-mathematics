{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Structology.GF4
-- GF(4) = GF(2)[α]/(α²+α+1): 四元域, 完整域公理 (0 postulate)
--
-- 元素 {0, 1, α, α+1}, 特征 2 (x+x=0), α²=α+1, α(α+1)=1, (α+1)²=α。
-- 用于 GF(4) → 正交拉丁方 → 幻方的域论生成链; 与 GF(3)/GF(9)/GF(27) 并列。

module Sovereign.Structology.GF4 where

open import Data.Nat using (ℕ)
open import Data.Fin using (Fin; zero; suc)
open import Data.Product using (Σ; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥-elim)
open import Relation.Nullary.Negation using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

--------------------------------------------------------------------------------
-- §1. GF(4) 元素
--------------------------------------------------------------------------------

data GF4 : Set where
  g0 : GF4   -- 0
  g1 : GF4   -- 1
  ga : GF4   -- α
  gb : GF4   -- α+1

-- 到 Fin 4 的索引
toFin : GF4 → Fin 4
toFin g0 = zero
toFin g1 = suc zero
toFin ga = suc (suc zero)
toFin gb = suc (suc (suc zero))

fromFin : Fin 4 → GF4
fromFin zero = g0
fromFin (suc zero) = g1
fromFin (suc (suc zero)) = ga
fromFin (suc (suc (suc zero))) = gb

toFin-fromFin : (x : GF4) → fromFin (toFin x) ≡ x
toFin-fromFin g0 = refl
toFin-fromFin g1 = refl
toFin-fromFin ga = refl
toFin-fromFin gb = refl

--------------------------------------------------------------------------------
-- §2. 加法 (特征 2)
--------------------------------------------------------------------------------

add4 : GF4 → GF4 → GF4
add4 g0 g0 = g0
add4 g0 g1 = g1
add4 g0 ga = ga
add4 g0 gb = gb
add4 g1 g0 = g1
add4 g1 g1 = g0
add4 g1 ga = gb
add4 g1 gb = ga
add4 ga g0 = ga
add4 ga g1 = gb
add4 ga ga = g0
add4 ga gb = g1
add4 gb g0 = gb
add4 gb g1 = ga
add4 gb ga = g1
add4 gb gb = g0

neg4 : GF4 → GF4   -- 特征 2: -x = x
neg4 g0 = g0
neg4 g1 = g1
neg4 ga = ga
neg4 gb = gb

--------------------------------------------------------------------------------
-- §3. 乘法 (α² = α+1)
--------------------------------------------------------------------------------

mul4 : GF4 → GF4 → GF4
mul4 g0 g0 = g0
mul4 g0 g1 = g0
mul4 g0 ga = g0
mul4 g0 gb = g0
mul4 g1 g0 = g0
mul4 g1 g1 = g1
mul4 g1 ga = ga
mul4 g1 gb = gb
mul4 ga g0 = g0
mul4 ga g1 = ga
mul4 ga ga = gb
mul4 ga gb = g1
mul4 gb g0 = g0
mul4 gb g1 = gb
mul4 gb ga = g1
mul4 gb gb = ga

--------------------------------------------------------------------------------
-- §4. 域公理 (全 refl 穷举)
--------------------------------------------------------------------------------

add4-comm : (x y : GF4) → add4 x y ≡ add4 y x
add4-comm g0 g0 = refl
add4-comm g0 g1 = refl
add4-comm g0 ga = refl
add4-comm g0 gb = refl
add4-comm g1 g0 = refl
add4-comm g1 g1 = refl
add4-comm g1 ga = refl
add4-comm g1 gb = refl
add4-comm ga g0 = refl
add4-comm ga g1 = refl
add4-comm ga ga = refl
add4-comm ga gb = refl
add4-comm gb g0 = refl
add4-comm gb g1 = refl
add4-comm gb ga = refl
add4-comm gb gb = refl

add4-assoc : (x y z : GF4) → add4 (add4 x y) z ≡ add4 x (add4 y z)
add4-assoc g0 g0 g0 = refl
add4-assoc g0 g0 g1 = refl
add4-assoc g0 g0 ga = refl
add4-assoc g0 g0 gb = refl
add4-assoc g0 g1 g0 = refl
add4-assoc g0 g1 g1 = refl
add4-assoc g0 g1 ga = refl
add4-assoc g0 g1 gb = refl
add4-assoc g0 ga g0 = refl
add4-assoc g0 ga g1 = refl
add4-assoc g0 ga ga = refl
add4-assoc g0 ga gb = refl
add4-assoc g0 gb g0 = refl
add4-assoc g0 gb g1 = refl
add4-assoc g0 gb ga = refl
add4-assoc g0 gb gb = refl
add4-assoc g1 g0 g0 = refl
add4-assoc g1 g0 g1 = refl
add4-assoc g1 g0 ga = refl
add4-assoc g1 g0 gb = refl
add4-assoc g1 g1 g0 = refl
add4-assoc g1 g1 g1 = refl
add4-assoc g1 g1 ga = refl
add4-assoc g1 g1 gb = refl
add4-assoc g1 ga g0 = refl
add4-assoc g1 ga g1 = refl
add4-assoc g1 ga ga = refl
add4-assoc g1 ga gb = refl
add4-assoc g1 gb g0 = refl
add4-assoc g1 gb g1 = refl
add4-assoc g1 gb ga = refl
add4-assoc g1 gb gb = refl
add4-assoc ga g0 g0 = refl
add4-assoc ga g0 g1 = refl
add4-assoc ga g0 ga = refl
add4-assoc ga g0 gb = refl
add4-assoc ga g1 g0 = refl
add4-assoc ga g1 g1 = refl
add4-assoc ga g1 ga = refl
add4-assoc ga g1 gb = refl
add4-assoc ga ga g0 = refl
add4-assoc ga ga g1 = refl
add4-assoc ga ga ga = refl
add4-assoc ga ga gb = refl
add4-assoc ga gb g0 = refl
add4-assoc ga gb g1 = refl
add4-assoc ga gb ga = refl
add4-assoc ga gb gb = refl
add4-assoc gb g0 g0 = refl
add4-assoc gb g0 g1 = refl
add4-assoc gb g0 ga = refl
add4-assoc gb g0 gb = refl
add4-assoc gb g1 g0 = refl
add4-assoc gb g1 g1 = refl
add4-assoc gb g1 ga = refl
add4-assoc gb g1 gb = refl
add4-assoc gb ga g0 = refl
add4-assoc gb ga g1 = refl
add4-assoc gb ga ga = refl
add4-assoc gb ga gb = refl
add4-assoc gb gb g0 = refl
add4-assoc gb gb g1 = refl
add4-assoc gb gb ga = refl
add4-assoc gb gb gb = refl

add4-unit : (x : GF4) → add4 x g0 ≡ x
add4-unit g0 = refl
add4-unit g1 = refl
add4-unit ga = refl
add4-unit gb = refl

add4-inv : (x : GF4) → add4 x (neg4 x) ≡ g0
add4-inv g0 = refl
add4-inv g1 = refl
add4-inv ga = refl
add4-inv gb = refl

mul4-comm : (x y : GF4) → mul4 x y ≡ mul4 y x
mul4-comm g0 g0 = refl
mul4-comm g0 g1 = refl
mul4-comm g0 ga = refl
mul4-comm g0 gb = refl
mul4-comm g1 g0 = refl
mul4-comm g1 g1 = refl
mul4-comm g1 ga = refl
mul4-comm g1 gb = refl
mul4-comm ga g0 = refl
mul4-comm ga g1 = refl
mul4-comm ga ga = refl
mul4-comm ga gb = refl
mul4-comm gb g0 = refl
mul4-comm gb g1 = refl
mul4-comm gb ga = refl
mul4-comm gb gb = refl

mul4-assoc : (x y z : GF4) → mul4 (mul4 x y) z ≡ mul4 x (mul4 y z)
mul4-assoc g0 g0 g0 = refl
mul4-assoc g0 g0 g1 = refl
mul4-assoc g0 g0 ga = refl
mul4-assoc g0 g0 gb = refl
mul4-assoc g0 g1 g0 = refl
mul4-assoc g0 g1 g1 = refl
mul4-assoc g0 g1 ga = refl
mul4-assoc g0 g1 gb = refl
mul4-assoc g0 ga g0 = refl
mul4-assoc g0 ga g1 = refl
mul4-assoc g0 ga ga = refl
mul4-assoc g0 ga gb = refl
mul4-assoc g0 gb g0 = refl
mul4-assoc g0 gb g1 = refl
mul4-assoc g0 gb ga = refl
mul4-assoc g0 gb gb = refl
mul4-assoc g1 g0 g0 = refl
mul4-assoc g1 g0 g1 = refl
mul4-assoc g1 g0 ga = refl
mul4-assoc g1 g0 gb = refl
mul4-assoc g1 g1 g0 = refl
mul4-assoc g1 g1 g1 = refl
mul4-assoc g1 g1 ga = refl
mul4-assoc g1 g1 gb = refl
mul4-assoc g1 ga g0 = refl
mul4-assoc g1 ga g1 = refl
mul4-assoc g1 ga ga = refl
mul4-assoc g1 ga gb = refl
mul4-assoc g1 gb g0 = refl
mul4-assoc g1 gb g1 = refl
mul4-assoc g1 gb ga = refl
mul4-assoc g1 gb gb = refl
mul4-assoc ga g0 g0 = refl
mul4-assoc ga g0 g1 = refl
mul4-assoc ga g0 ga = refl
mul4-assoc ga g0 gb = refl
mul4-assoc ga g1 g0 = refl
mul4-assoc ga g1 g1 = refl
mul4-assoc ga g1 ga = refl
mul4-assoc ga g1 gb = refl
mul4-assoc ga ga g0 = refl
mul4-assoc ga ga g1 = refl
mul4-assoc ga ga ga = refl
mul4-assoc ga ga gb = refl
mul4-assoc ga gb g0 = refl
mul4-assoc ga gb g1 = refl
mul4-assoc ga gb ga = refl
mul4-assoc ga gb gb = refl
mul4-assoc gb g0 g0 = refl
mul4-assoc gb g0 g1 = refl
mul4-assoc gb g0 ga = refl
mul4-assoc gb g0 gb = refl
mul4-assoc gb g1 g0 = refl
mul4-assoc gb g1 g1 = refl
mul4-assoc gb g1 ga = refl
mul4-assoc gb g1 gb = refl
mul4-assoc gb ga g0 = refl
mul4-assoc gb ga g1 = refl
mul4-assoc gb ga ga = refl
mul4-assoc gb ga gb = refl
mul4-assoc gb gb g0 = refl
mul4-assoc gb gb g1 = refl
mul4-assoc gb gb ga = refl
mul4-assoc gb gb gb = refl

mul4-unit : (x : GF4) → mul4 x g1 ≡ x
mul4-unit g0 = refl
mul4-unit g1 = refl
mul4-unit ga = refl
mul4-unit gb = refl

mul4-zero : (x : GF4) → mul4 x g0 ≡ g0
mul4-zero g0 = refl
mul4-zero g1 = refl
mul4-zero ga = refl
mul4-zero gb = refl

distrib-left : (x y z : GF4) → mul4 x (add4 y z) ≡ add4 (mul4 x y) (mul4 x z)
distrib-left g0 g0 g0 = refl
distrib-left g0 g0 g1 = refl
distrib-left g0 g0 ga = refl
distrib-left g0 g0 gb = refl
distrib-left g0 g1 g0 = refl
distrib-left g0 g1 g1 = refl
distrib-left g0 g1 ga = refl
distrib-left g0 g1 gb = refl
distrib-left g0 ga g0 = refl
distrib-left g0 ga g1 = refl
distrib-left g0 ga ga = refl
distrib-left g0 ga gb = refl
distrib-left g0 gb g0 = refl
distrib-left g0 gb g1 = refl
distrib-left g0 gb ga = refl
distrib-left g0 gb gb = refl
distrib-left g1 g0 g0 = refl
distrib-left g1 g0 g1 = refl
distrib-left g1 g0 ga = refl
distrib-left g1 g0 gb = refl
distrib-left g1 g1 g0 = refl
distrib-left g1 g1 g1 = refl
distrib-left g1 g1 ga = refl
distrib-left g1 g1 gb = refl
distrib-left g1 ga g0 = refl
distrib-left g1 ga g1 = refl
distrib-left g1 ga ga = refl
distrib-left g1 ga gb = refl
distrib-left g1 gb g0 = refl
distrib-left g1 gb g1 = refl
distrib-left g1 gb ga = refl
distrib-left g1 gb gb = refl
distrib-left ga g0 g0 = refl
distrib-left ga g0 g1 = refl
distrib-left ga g0 ga = refl
distrib-left ga g0 gb = refl
distrib-left ga g1 g0 = refl
distrib-left ga g1 g1 = refl
distrib-left ga g1 ga = refl
distrib-left ga g1 gb = refl
distrib-left ga ga g0 = refl
distrib-left ga ga g1 = refl
distrib-left ga ga ga = refl
distrib-left ga ga gb = refl
distrib-left ga gb g0 = refl
distrib-left ga gb g1 = refl
distrib-left ga gb ga = refl
distrib-left ga gb gb = refl
distrib-left gb g0 g0 = refl
distrib-left gb g0 g1 = refl
distrib-left gb g0 ga = refl
distrib-left gb g0 gb = refl
distrib-left gb g1 g0 = refl
distrib-left gb g1 g1 = refl
distrib-left gb g1 ga = refl
distrib-left gb g1 gb = refl
distrib-left gb ga g0 = refl
distrib-left gb ga g1 = refl
distrib-left gb ga ga = refl
distrib-left gb ga gb = refl
distrib-left gb gb g0 = refl
distrib-left gb gb g1 = refl
distrib-left gb gb ga = refl
distrib-left gb gb gb = refl

distrib-right : (x y z : GF4) → mul4 (add4 x y) z ≡ add4 (mul4 x z) (mul4 y z)
distrib-right g0 g0 g0 = refl
distrib-right g0 g0 g1 = refl
distrib-right g0 g0 ga = refl
distrib-right g0 g0 gb = refl
distrib-right g0 g1 g0 = refl
distrib-right g0 g1 g1 = refl
distrib-right g0 g1 ga = refl
distrib-right g0 g1 gb = refl
distrib-right g0 ga g0 = refl
distrib-right g0 ga g1 = refl
distrib-right g0 ga ga = refl
distrib-right g0 ga gb = refl
distrib-right g0 gb g0 = refl
distrib-right g0 gb g1 = refl
distrib-right g0 gb ga = refl
distrib-right g0 gb gb = refl
distrib-right g1 g0 g0 = refl
distrib-right g1 g0 g1 = refl
distrib-right g1 g0 ga = refl
distrib-right g1 g0 gb = refl
distrib-right g1 g1 g0 = refl
distrib-right g1 g1 g1 = refl
distrib-right g1 g1 ga = refl
distrib-right g1 g1 gb = refl
distrib-right g1 ga g0 = refl
distrib-right g1 ga g1 = refl
distrib-right g1 ga ga = refl
distrib-right g1 ga gb = refl
distrib-right g1 gb g0 = refl
distrib-right g1 gb g1 = refl
distrib-right g1 gb ga = refl
distrib-right g1 gb gb = refl
distrib-right ga g0 g0 = refl
distrib-right ga g0 g1 = refl
distrib-right ga g0 ga = refl
distrib-right ga g0 gb = refl
distrib-right ga g1 g0 = refl
distrib-right ga g1 g1 = refl
distrib-right ga g1 ga = refl
distrib-right ga g1 gb = refl
distrib-right ga ga g0 = refl
distrib-right ga ga g1 = refl
distrib-right ga ga ga = refl
distrib-right ga ga gb = refl
distrib-right ga gb g0 = refl
distrib-right ga gb g1 = refl
distrib-right ga gb ga = refl
distrib-right ga gb gb = refl
distrib-right gb g0 g0 = refl
distrib-right gb g0 g1 = refl
distrib-right gb g0 ga = refl
distrib-right gb g0 gb = refl
distrib-right gb g1 g0 = refl
distrib-right gb g1 g1 = refl
distrib-right gb g1 ga = refl
distrib-right gb g1 gb = refl
distrib-right gb ga g0 = refl
distrib-right gb ga g1 = refl
distrib-right gb ga ga = refl
distrib-right gb ga gb = refl
distrib-right gb gb g0 = refl
distrib-right gb gb g1 = refl
distrib-right gb gb ga = refl
distrib-right gb gb gb = refl

mul4-inv : (x : GF4) → ¬ (x ≡ g0) → Σ GF4 (λ y → mul4 x y ≡ g1)
mul4-inv g0 ne = ⊥-elim (ne refl)
mul4-inv g1 ne = g1 , refl
mul4-inv ga ne = gb , refl   -- α·(α+1) = 1
mul4-inv gb ne = ga , refl   -- (α+1)·α = 1

--------------------------------------------------------------------------------
-- §5. 补充 L2 定理 (全称量化)
--------------------------------------------------------------------------------

-- 加法左单位元: 0 + x = x
add4-identityˡ : (x : GF4) → add4 g0 x ≡ x
add4-identityˡ g0 = refl
add4-identityˡ g1 = refl
add4-identityˡ ga = refl
add4-identityˡ gb = refl

-- 乘法左单位元: 1 * x = x
mul4-identityˡ : (x : GF4) → mul4 g1 x ≡ x
mul4-identityˡ g0 = refl
mul4-identityˡ g1 = refl
mul4-identityˡ ga = refl
mul4-identityˡ gb = refl

-- 特征 2: x + x = 0 (自逆)
add4-self : (x : GF4) → add4 x x ≡ g0
add4-self g0 = refl
add4-self g1 = refl
add4-self ga = refl
add4-self gb = refl

-- 否定恒等: -x = x (特征 2)
neg4-identity : (x : GF4) → neg4 x ≡ x
neg4-identity g0 = refl
neg4-identity g1 = refl
neg4-identity ga = refl
neg4-identity gb = refl

-- 零因子不存在: x*y=0 → x=0 ∨ y=0
gf4-no-zero-divisors : (x y : GF4) → mul4 x y ≡ g0 → (x ≡ g0) ⊎ (y ≡ g0)
gf4-no-zero-divisors g0 _ _ = Data.Sum.inj₁ refl
gf4-no-zero-divisors _ g0 _ = Data.Sum.inj₂ refl
gf4-no-zero-divisors g1 g1 ()
gf4-no-zero-divisors g1 ga ()
gf4-no-zero-divisors g1 gb ()
gf4-no-zero-divisors ga g1 ()
gf4-no-zero-divisors ga ga ()
gf4-no-zero-divisors ga gb ()
gf4-no-zero-divisors gb g1 ()
gf4-no-zero-divisors gb ga ()
gf4-no-zero-divisors gb gb ()

-- 平方映射: x² 的值 (α²=α+1, (α+1)²=α)
gf4-square-map : GF4 → GF4
gf4-square-map g0 = g0
gf4-square-map g1 = g1
gf4-square-map ga = gb  -- α² = α+1
gf4-square-map gb = ga  -- (α+1)² = α

gf4-squared : (x : GF4) → mul4 x x ≡ gf4-square-map x
gf4-squared g0 = refl
gf4-squared g1 = refl
gf4-squared ga = refl
gf4-squared gb = refl

-- 0 postulate.
