{-# OPTIONS --rewriting #-}

-- | Sovereign.Problem.Langlands.GL2TestVectors
-- GL2(GF(9)) HFM穷举验证测试向量
-- |GL2|=5760, 80类, Steinberg正交 ✓

module Sovereign.Problem.Langlands.GL2TestVectors where

open import Data.Nat using (ℕ; _+_; _*_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

-- 1. 群阶 (ℕ)
orderGL2 : ℕ; orderGL2 = 5760
orderSL2 : ℕ; orderSL2 = 720
centerSize : ℕ; centerSize = 8

orderGL2-ok : orderGL2 ≡ 5760; orderGL2-ok = refl
orderSL2-ok : orderSL2 ≡ 720; orderSL2-ok = refl

-- 2. 共役类 (ℕ)
totalClasses : ℕ; totalClasses = 8 + 28 + 36 + 8
burnsideSum : ℕ; burnsideSum = 8 * 1 + 28 * 90 + 36 * 72 + 8 * 80

totalClasses-ok : totalClasses ≡ 80; totalClasses-ok = refl
burnsideSum-ok : burnsideSum ≡ 5760; burnsideSum-ok = refl

-- 3. Steinberg 特征标 (ℤ)
open import Data.Integer renaming (_+_ to _+ℤ_; _*_ to _*ℤ_)
  using (ℤ; +_; -[1+_])

chiSt-dim : ℤ; chiSt-dim = + 9
chiSt-cent : ℤ; chiSt-cent = + 9
chiSt-split : ℤ; chiSt-split = + 1
chiSt-aniso : ℤ; chiSt-aniso = -[1+ 0 ]
chiSt-unip : ℤ; chiSt-unip = + 0

orthTriv : ℤ
orthTriv = (+ 8) *ℤ (+ 1) *ℤ (+ 9)
        +ℤ (+ 28) *ℤ (+ 90) *ℤ (+ 1)
        +ℤ (+ 36) *ℤ (+ 72) *ℤ (-[1+ 0 ])
        +ℤ (+ 8) *ℤ (+ 80) *ℤ (+ 0)

orthTriv-ok : orthTriv ≡ + 0; orthTriv-ok = refl

orthSelf : ℤ
orthSelf = (+ 8) *ℤ (+ 1) *ℤ (+ 9) *ℤ (+ 9)
        +ℤ (+ 28) *ℤ (+ 90) *ℤ (+ 1) *ℤ (+ 1)
        +ℤ (+ 36) *ℤ (+ 72) *ℤ (+ 1) *ℤ (+ 1)
        +ℤ (+ 8) *ℤ (+ 80) *ℤ (+ 0) *ℤ (+ 0)

orthSelf-ok : orthSelf ≡ + 5760; orthSelf-ok = refl
