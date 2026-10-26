{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Synthesis.Physics.NoSplitJ1
-- 「A₄ 不变的**对角**微扰不能劈裂 J=1 三重态」的有限形式化
--
-- 物理背景（与 IhC60Vibration / PolyhedralReps 配套）：
--   J=1 的三维表示在 A₄ 下是单一不可约表示（T₁）。若一个微扰算符与群作用交换，
--   它在该三维空间上只能是标量 ⇒ 三个能级同等平移 ⇒ 不产生分裂。
--
-- 本模块只证**对角情形**（物理上即「三个能级各自平移」的那类微扰），
-- 用 A₄ 中的 3-循环 P 作为检验元素：X 与 P 交换 ⇒ x₀ = x₁ = x₂。
--
-- 为什么只做对角：一般（含非对角）情形需要「2x ≡ 0 ⇒ x ≡ 0」的整环无挠性，
--   本模块不引入该引理，把一般情形留作后续（roadmap），不虚报。
--
-- 0 postulate / 0 hole。
module Sovereign.Synthesis.Physics.NoSplitJ1 where

open import Data.Fin using (Fin; zero; suc)
open import Data.Integer using (ℤ; +_; +0; _*_)
open import Data.Integer.Properties using (*-identityʳ)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)

--------------------------------------------------------------------------------
-- §1. 三维复向量空间 NS1V = Fin 3 → ℤ 与基向量
--------------------------------------------------------------------------------
NS1V : Set
NS1V = Fin 3 → ℤ

NS1e0 : NS1V
NS1e0 zero = + 1
NS1e0 (suc zero) = +0
NS1e0 (suc (suc zero)) = +0

NS1e2 : NS1V
NS1e2 zero = +0
NS1e2 (suc zero) = +0
NS1e2 (suc (suc zero)) = + 1

--------------------------------------------------------------------------------
-- §2. 3-循环 P 与对角算符 D(a,b,c)
--------------------------------------------------------------------------------
-- P 作用： (v₀,v₁,v₂) ↦ (v₂,v₀,v₁)
NS1shift : NS1V → NS1V
NS1shift v zero = v (suc (suc zero))
NS1shift v (suc zero) = v zero
NS1shift v (suc (suc zero)) = v (suc zero)

-- 对角算符 D(a,b,c)：第 i 个分量乘以对应系数
NS1diag : ℤ → ℤ → ℤ → NS1V → NS1V
NS1diag a b c v zero = a * v zero
NS1diag a b c v (suc zero) = b * v (suc zero)
NS1diag a b c v (suc (suc zero)) = c * v (suc (suc zero))

-- 与 P 交换
NS1Commutes : ℤ → ℤ → ℤ → Set
NS1Commutes a b c = (v : NS1V) → NS1diag a b c (NS1shift v) ≡ NS1shift (NS1diag a b c v)

--------------------------------------------------------------------------------
-- §3. 主定理：对角微扰与 3-循环交换 ⇒ 三个对角元相等
--------------------------------------------------------------------------------
-- 在 NS1e0 上取值：左边第 1 分量 = b * 1，右边第 1 分量 = a * 1
-- 在 NS1e2 上取值：左边第 0 分量 = a * 1，右边第 0 分量 = c * 1
no-split-diag : (a b c : ℤ) → NS1Commutes a b c → (a ≡ b) × (a ≡ c)
no-split-diag a b c comm = a≡b , a≡c
  where
    -- comm NS1e0 的第 1 分量： b * 1 ≡ a * 1
    eq1 : b * (+ 1) ≡ a * (+ 1)
    eq1 = cong (λ v → v (suc zero)) (comm NS1e0)

    -- comm NS1e2 的第 0 分量： a * 1 ≡ c * 1
    eq2 : a * (+ 1) ≡ c * (+ 1)
    eq2 = cong (λ v → v zero) (comm NS1e2)

    a≡b : a ≡ b
    a≡b = trans (sym (*-identityʳ a)) (trans (sym eq1) (*-identityʳ b))

    a≡c : a ≡ c
    a≡c = trans (sym (*-identityʳ a)) (trans eq2 (*-identityʳ c))
