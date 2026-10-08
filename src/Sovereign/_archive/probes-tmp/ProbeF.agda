{-# OPTIONS --cubical --guardedness #-}
module ProbeF where

open import Cubical.Data.Int using (ℤ; _+_; pos; negsuc)
open import Cubical.Foundations.Prelude using (_≡_; refl; sym; cong; cong₂; _∙_)
open import Cubical.Data.Int.Properties using (+Assoc; +Comm)

-- 最小复现 t4 结构：sym (+Assoc 卡) 于 cong 嵌套 2
-- t4 同构：cong (a+_) (cong ((b+c)+_) (sym (+Assoc b c d)))
probeA : ∀ a b c d → (a + ((b + c) + d)) ≡ (a + ((b + (c + d))))
probeA a b c d = cong (a +_) (cong ((b + c) +_) (sym (+Assoc b c d)))

-- 对照：正向 +Assoc（bubble 模式——已验证绿的行为）
probeB : ∀ a b c d → (a + (b + (c + d))) ≡ (a + ((b + c) + d))
probeB a b c d = cong (a +_) (cong ((b + c) +_) (+Assoc b c d))
