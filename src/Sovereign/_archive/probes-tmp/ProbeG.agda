{-# OPTIONS --cubical --guardedness #-}
module ProbeG where

open import Cubical.Data.Int using (ℤ; _+_; pos; negsuc)
open import Cubical.Foundations.Prelude using (_≡_; refl; sym; cong; cong₂; _∙_)
open import Cubical.Data.Int.Properties using (+Assoc; +Comm)

-- 最小复现 u1b：cong (a+_) (+Assoc b c X) 其中 X 复合
probeG : ∀ a b c x y → (a + ((b + c) + (x + y))) ≡ (a + (b + (c + (x + y))))
probeG a b c x y = cong (a +_) (sym (+Assoc b c ((x + y))))

-- 对照：u1a 形（sym Assoc 裸）
probeH : ∀ a b c x y → (a + (b + (c + (x + y)))) ≡ (a + ((b + c) + (x + y)))
probeH a b c x y = +Assoc a (b + c) ((x + y))
