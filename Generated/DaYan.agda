{-# OPTIONS --rewriting #-}
module Generated.DaYan where

open import Sovereign.Structology.T6
-- Type-level 同构
postulate
  t6≃fin729 : T6Lattice≃Fin729
-- 6层剥离模具
postulate
  toℕ-sum-injective : (x : T6Lattice) → (y : T6Lattice) → toℕ-sum x ≡ toℕ-sum y → x ≡ y
-- CRT 查表
crt-0 : lookupCrt 0 ≡ (0 , 0)
crt-0  = refl
crt-1 : lookupCrt 1 ≡ (1 , 1)
crt-1  = refl
crt-2 : lookupCrt 2 ≡ (2 , 2)
crt-2  = refl
crt-3 : lookupCrt 3 ≡ (3 , 3)
crt-3  = refl
crt-4 : lookupCrt 4 ≡ (4 , 4)
crt-4  = refl
crt-5 : lookupCrt 5 ≡ (5 , 5)
crt-5  = refl
crt-6 : lookupCrt 6 ≡ (6 , 6)
crt-6  = refl
crt-7 : lookupCrt 7 ≡ (7 , 7)
crt-7  = refl
crt-8 : lookupCrt 8 ≡ (8 , 8)
crt-8  = refl
crt-9 : lookupCrt 9 ≡ (9 , 9)
crt-9  = refl
-- 全息对齐
align-6624 : toroidal stepN 6624 huangzhong ≡ 0
align-6624  = trans stepN-adds 6624 huangzhong trans +-assoc 0 6624 0 refl
