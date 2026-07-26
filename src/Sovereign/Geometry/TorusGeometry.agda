{-# OPTIONS --rewriting #-}

-- | Sovereign.Geometry.TorusGeometry
-- T⁶ 环面几何：加法群结构 + 群公理 + 基本群 + 测地线
--
-- T⁶ = (GF3)⁶, 729 个格点的 6 维离散环面
-- 加法群: (C₃)⁶, 逐分量 +₃ mod 3
-- π₁(T⁶) ≅ (C₃)⁶ ≅ T6Lattice (离散环面的基本群同构于加法群本身)

module Sovereign.Geometry.TorusGeometry where

open import Data.Fin using (Fin; zero; suc)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Vec using (Vec; []; _∷_; map)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂)

open import Sovereign.Base.Trit
  using (Trit; T₀; T₁; T₂; _⊕_; negate)
open import Sovereign.Structology.T6
  using (T6Lattice; GF3; finToT6; t6ToFin)

--------------------------------------------------------------------------------
-- 1. T⁶ 加法群结构
--------------------------------------------------------------------------------

tritOf : Fin 3 → Trit
tritOf zero = T₀
tritOf (suc zero) = T₁
tritOf (suc (suc zero)) = T₂

finOf : Trit → Fin 3
finOf T₀ = zero
finOf T₁ = suc zero
finOf T₂ = suc (suc zero)

-- Fin 3 上的加法 (mod 3)
_+₃_ : Fin 3 → Fin 3 → Fin 3
x +₃ y = finOf (tritOf x ⊕ tritOf y)

-- Fin 3 上的相反数
neg3 : Fin 3 → Fin 3
neg3 zero = zero
neg3 (suc zero) = suc (suc zero)  -- -1 ≡ 2 mod 3
neg3 (suc (suc zero)) = suc zero  -- -2 ≡ 1 mod 3

-- T⁶ 加法: 逐分量 +₃
t6Add : T6Lattice → T6Lattice → T6Lattice
t6Add (x₀ ∷ x₁ ∷ x₂ ∷ x₃ ∷ x₄ ∷ x₅ ∷ [])
     (y₀ ∷ y₁ ∷ y₂ ∷ y₃ ∷ y₄ ∷ y₅ ∷ []) =
  (x₀ +₃ y₀) ∷ (x₁ +₃ y₁) ∷ (x₂ +₃ y₂) ∷ (x₃ +₃ y₃) ∷ (x₄ +₃ y₄) ∷ (x₅ +₃ y₅) ∷ []

-- T⁶ 零元
z3 : Fin 3 ; z3 = Data.Fin.zero

t6Zero : T6Lattice
t6Zero = z3 ∷ z3 ∷ z3 ∷ z3 ∷ z3 ∷ z3 ∷ []

-- T⁶ 逆元 (逐分量相反)
t6Neg : T6Lattice → T6Lattice
t6Neg (x₀ ∷ x₁ ∷ x₂ ∷ x₃ ∷ x₄ ∷ x₅ ∷ []) =
  (neg3 x₀) ∷ (neg3 x₁) ∷ (neg3 x₂) ∷ (neg3 x₃) ∷ (neg3 x₄) ∷ (neg3 x₅) ∷ []

-- 6 个坐标生成元 (π₁ 生成元)
g1 : T6Lattice ; g1 = (suc zero) ∷ zero ∷ zero ∷ zero ∷ zero ∷ zero ∷ []
g2 : T6Lattice ; g2 = zero ∷ (suc zero) ∷ zero ∷ zero ∷ zero ∷ zero ∷ []
g3 : T6Lattice ; g3 = zero ∷ zero ∷ (suc zero) ∷ zero ∷ zero ∷ zero ∷ []
g4 : T6Lattice ; g4 = zero ∷ zero ∷ zero ∷ (suc zero) ∷ zero ∷ zero ∷ []
g5 : T6Lattice ; g5 = zero ∷ zero ∷ zero ∷ zero ∷ (suc zero) ∷ zero ∷ []
g6 : T6Lattice ; g6 = zero ∷ zero ∷ zero ∷ zero ∷ zero ∷ (suc zero) ∷ []

--------------------------------------------------------------------------------
-- 2. 群公理 (逐分量 + Fin 3 引理)
--------------------------------------------------------------------------------

-- Fin 3 结合律 (穷举 3³=27 case)
+₃-assoc : ∀ (x y z : Fin 3) → (x +₃ y) +₃ z ≡ x +₃ (y +₃ z)
+₃-assoc zero zero zero = refl ; +₃-assoc zero zero (suc zero) = refl
+₃-assoc zero zero (suc (suc zero)) = refl
+₃-assoc zero (suc zero) zero = refl ; +₃-assoc zero (suc zero) (suc zero) = refl
+₃-assoc zero (suc zero) (suc (suc zero)) = refl
+₃-assoc zero (suc (suc zero)) zero = refl
+₃-assoc zero (suc (suc zero)) (suc zero) = refl
+₃-assoc zero (suc (suc zero)) (suc (suc zero)) = refl
+₃-assoc (suc zero) zero zero = refl ; +₃-assoc (suc zero) zero (suc zero) = refl
+₃-assoc (suc zero) zero (suc (suc zero)) = refl
+₃-assoc (suc zero) (suc zero) zero = refl
+₃-assoc (suc zero) (suc zero) (suc zero) = refl
+₃-assoc (suc zero) (suc zero) (suc (suc zero)) = refl
+₃-assoc (suc zero) (suc (suc zero)) zero = refl
+₃-assoc (suc zero) (suc (suc zero)) (suc zero) = refl
+₃-assoc (suc zero) (suc (suc zero)) (suc (suc zero)) = refl
+₃-assoc (suc (suc zero)) zero zero = refl
+₃-assoc (suc (suc zero)) zero (suc zero) = refl
+₃-assoc (suc (suc zero)) zero (suc (suc zero)) = refl
+₃-assoc (suc (suc zero)) (suc zero) zero = refl
+₃-assoc (suc (suc zero)) (suc zero) (suc zero) = refl
+₃-assoc (suc (suc zero)) (suc zero) (suc (suc zero)) = refl
+₃-assoc (suc (suc zero)) (suc (suc zero)) zero = refl
+₃-assoc (suc (suc zero)) (suc (suc zero)) (suc zero) = refl
+₃-assoc (suc (suc zero)) (suc (suc zero)) (suc (suc zero)) = refl

-- Fin 3 交换律 (穷举 3²=9 case)
+₃-comm : ∀ (x y : Fin 3) → x +₃ y ≡ y +₃ x
+₃-comm zero zero = refl ; +₃-comm zero (suc zero) = refl
+₃-comm zero (suc (suc zero)) = refl ; +₃-comm (suc zero) zero = refl
+₃-comm (suc zero) (suc zero) = refl ; +₃-comm (suc zero) (suc (suc zero)) = refl
+₃-comm (suc (suc zero)) zero = refl ; +₃-comm (suc (suc zero)) (suc zero) = refl
+₃-comm (suc (suc zero)) (suc (suc zero)) = refl

-- 零元
+₃-identityˡ : ∀ (x : Fin 3) → z3 +₃ x ≡ x
+₃-identityˡ zero = refl ; +₃-identityˡ (suc zero) = refl
+₃-identityˡ (suc (suc zero)) = refl

+₃-identityʳ : ∀ (x : Fin 3) → x +₃ z3 ≡ x
+₃-identityʳ zero = refl ; +₃-identityʳ (suc zero) = refl
+₃-identityʳ (suc (suc zero)) = refl

-- 逆元
+₃-inverseˡ : ∀ (x : Fin 3) → (neg3 x) +₃ x ≡ zero
+₃-inverseˡ zero = refl
+₃-inverseˡ (suc zero) = refl
+₃-inverseˡ (suc (suc zero)) = refl

+₃-inverseʳ : ∀ (x : Fin 3) → x +₃ (neg3 x) ≡ zero
+₃-inverseʳ zero = refl
+₃-inverseʳ (suc zero) = refl
+₃-inverseʳ (suc (suc zero)) = refl

-- T⁶ 群公理 (通过逐分量 +₃-assoc/comm 验证)
t6Add-assoc : ∀ (x y z : T6Lattice) → t6Add (t6Add x y) z ≡ t6Add x (t6Add y z)
t6Add-assoc (x₀ ∷ x₁ ∷ x₂ ∷ x₃ ∷ x₄ ∷ x₅ ∷ [])
            (y₀ ∷ y₁ ∷ y₂ ∷ y₃ ∷ y₄ ∷ y₅ ∷ [])
            (z₀ ∷ z₁ ∷ z₂ ∷ z₃ ∷ z₄ ∷ z₅ ∷ []) =
  cong₂ (λ h t → h ∷ t) (+₃-assoc x₀ y₀ z₀)
        (cong₂ (λ h t → h ∷ t) (+₃-assoc x₁ y₁ z₁)
        (cong₂ (λ h t → h ∷ t) (+₃-assoc x₂ y₂ z₂)
        (cong₂ (λ h t → h ∷ t) (+₃-assoc x₃ y₃ z₃)
        (cong₂ (λ h t → h ∷ t) (+₃-assoc x₄ y₄ z₄)
        (cong₂ (λ h t → h ∷ t) (+₃-assoc x₅ y₅ z₅) refl)))))

t6Add-comm : ∀ (x y : T6Lattice) → t6Add x y ≡ t6Add y x
t6Add-comm (x₀ ∷ x₁ ∷ x₂ ∷ x₃ ∷ x₄ ∷ x₅ ∷ [])
           (y₀ ∷ y₁ ∷ y₂ ∷ y₃ ∷ y₄ ∷ y₅ ∷ []) =
  cong₂ (λ h t → h ∷ t) (+₃-comm x₀ y₀)
        (cong₂ (λ h t → h ∷ t) (+₃-comm x₁ y₁)
        (cong₂ (λ h t → h ∷ t) (+₃-comm x₂ y₂)
        (cong₂ (λ h t → h ∷ t) (+₃-comm x₃ y₃)
        (cong₂ (λ h t → h ∷ t) (+₃-comm x₄ y₄)
        (cong₂ (λ h t → h ∷ t) (+₃-comm x₅ y₅) refl)))))

t6Add-identityˡ : ∀ (x : T6Lattice) → t6Add t6Zero x ≡ x
t6Add-identityˡ (x₀ ∷ x₁ ∷ x₂ ∷ x₃ ∷ x₄ ∷ x₅ ∷ []) =
  cong₂ (λ h t → h ∷ t) (+₃-identityˡ x₀)
        (cong₂ (λ h t → h ∷ t) (+₃-identityˡ x₁)
        (cong₂ (λ h t → h ∷ t) (+₃-identityˡ x₂)
        (cong₂ (λ h t → h ∷ t) (+₃-identityˡ x₃)
        (cong₂ (λ h t → h ∷ t) (+₃-identityˡ x₄)
        (cong₂ (λ h t → h ∷ t) (+₃-identityˡ x₅) refl)))))

t6Add-identityʳ : ∀ (x : T6Lattice) → t6Add x t6Zero ≡ x
t6Add-identityʳ (x₀ ∷ x₁ ∷ x₂ ∷ x₃ ∷ x₄ ∷ x₅ ∷ []) =
  cong₂ (λ h t → h ∷ t) (+₃-identityʳ x₀)
        (cong₂ (λ h t → h ∷ t) (+₃-identityʳ x₁)
        (cong₂ (λ h t → h ∷ t) (+₃-identityʳ x₂)
        (cong₂ (λ h t → h ∷ t) (+₃-identityʳ x₃)
        (cong₂ (λ h t → h ∷ t) (+₃-identityʳ x₄)
        (cong₂ (λ h t → h ∷ t) (+₃-identityʳ x₅) refl)))))

t6Add-inverseˡ : ∀ (x : T6Lattice) → t6Add (t6Neg x) x ≡ t6Zero
t6Add-inverseˡ (x₀ ∷ x₁ ∷ x₂ ∷ x₃ ∷ x₄ ∷ x₅ ∷ []) =
  cong₂ (λ h t → h ∷ t) (+₃-inverseˡ x₀)
        (cong₂ (λ h t → h ∷ t) (+₃-inverseˡ x₁)
        (cong₂ (λ h t → h ∷ t) (+₃-inverseˡ x₂)
        (cong₂ (λ h t → h ∷ t) (+₃-inverseˡ x₃)
        (cong₂ (λ h t → h ∷ t) (+₃-inverseˡ x₄)
        (cong₂ (λ h t → h ∷ t) (+₃-inverseˡ x₅) refl)))))

t6Add-inverseʳ : ∀ (x : T6Lattice) → t6Add x (t6Neg x) ≡ t6Zero
t6Add-inverseʳ (x₀ ∷ x₁ ∷ x₂ ∷ x₃ ∷ x₄ ∷ x₅ ∷ []) =
  cong₂ (λ h t → h ∷ t) (+₃-inverseʳ x₀)
        (cong₂ (λ h t → h ∷ t) (+₃-inverseʳ x₁)
        (cong₂ (λ h t → h ∷ t) (+₃-inverseʳ x₂)
        (cong₂ (λ h t → h ∷ t) (+₃-inverseʳ x₃)
        (cong₂ (λ h t → h ∷ t) (+₃-inverseʳ x₄)
        (cong₂ (λ h t → h ∷ t) (+₃-inverseʳ x₅) refl)))))

-- 生成元列表
genL : Fin 6 → T6Lattice
genL zero = g1 ; genL (suc zero) = g2
genL (suc (suc zero)) = g3
genL (suc (suc (suc zero))) = g4
genL (suc (suc (suc (suc zero)))) = g5
genL (suc (suc (suc (suc (suc zero))))) = g6

-- π₁(T⁶) ≅ (C₃)⁶: 生成元的 3 阶性质
generator-order3 : ∀ (i : Fin 6) → t6Add (genL i) (t6Add (genL i) (genL i)) ≡ t6Zero
generator-order3 zero = refl
generator-order3 (suc zero) = refl
generator-order3 (suc (suc zero)) = refl
generator-order3 (suc (suc (suc zero))) = refl
generator-order3 (suc (suc (suc (suc zero)))) = refl
generator-order3 (suc (suc (suc (suc (suc zero))))) = refl

-- 生成元交换 (穷举 6×6=36 case)
generator-comm : ∀ (i j : Fin 6) → t6Add (genL i) (genL j) ≡ t6Add (genL j) (genL i)
generator-comm zero zero = refl ; generator-comm zero (suc zero) = refl
generator-comm zero (suc (suc zero)) = refl
generator-comm zero (suc (suc (suc zero))) = refl
generator-comm zero (suc (suc (suc (suc zero)))) = refl
generator-comm zero (suc (suc (suc (suc (suc zero))))) = refl
generator-comm (suc zero) zero = refl
generator-comm (suc zero) (suc zero) = refl
generator-comm (suc zero) (suc (suc zero)) = refl
generator-comm (suc zero) (suc (suc (suc zero))) = refl
generator-comm (suc zero) (suc (suc (suc (suc zero)))) = refl
generator-comm (suc zero) (suc (suc (suc (suc (suc zero))))) = refl
generator-comm (suc (suc zero)) zero = refl
generator-comm (suc (suc zero)) (suc zero) = refl
generator-comm (suc (suc zero)) (suc (suc zero)) = refl
generator-comm (suc (suc zero)) (suc (suc (suc zero))) = refl
generator-comm (suc (suc zero)) (suc (suc (suc (suc zero)))) = refl
generator-comm (suc (suc zero)) (suc (suc (suc (suc (suc zero))))) = refl
generator-comm (suc (suc (suc zero))) zero = refl
generator-comm (suc (suc (suc zero))) (suc zero) = refl
generator-comm (suc (suc (suc zero))) (suc (suc zero)) = refl
generator-comm (suc (suc (suc zero))) (suc (suc (suc zero))) = refl
generator-comm (suc (suc (suc zero))) (suc (suc (suc (suc zero)))) = refl
generator-comm (suc (suc (suc zero))) (suc (suc (suc (suc (suc zero))))) = refl
generator-comm (suc (suc (suc (suc zero)))) zero = refl
generator-comm (suc (suc (suc (suc zero)))) (suc zero) = refl
generator-comm (suc (suc (suc (suc zero)))) (suc (suc zero)) = refl
generator-comm (suc (suc (suc (suc zero)))) (suc (suc (suc zero))) = refl
generator-comm (suc (suc (suc (suc zero)))) (suc (suc (suc (suc zero)))) = refl
generator-comm (suc (suc (suc (suc zero)))) (suc (suc (suc (suc (suc zero))))) = refl
generator-comm (suc (suc (suc (suc (suc zero))))) zero = refl
generator-comm (suc (suc (suc (suc (suc zero))))) (suc zero) = refl
generator-comm (suc (suc (suc (suc (suc zero))))) (suc (suc zero)) = refl
generator-comm (suc (suc (suc (suc (suc zero))))) (suc (suc (suc zero))) = refl
generator-comm (suc (suc (suc (suc (suc zero))))) (suc (suc (suc (suc zero)))) = refl
generator-comm (suc (suc (suc (suc (suc zero))))) (suc (suc (suc (suc (suc zero))))) = refl

--------------------------------------------------------------------------------
-- 3. 测地线: 沿指定方向平移
--------------------------------------------------------------------------------

-- 沿向量 v 的测地线: geodesic(v, n) = n·v (T⁶ 上加法 n 次)
t6Scale : ℕ → T6Lattice → T6Lattice
t6Scale zero    v = t6Zero
t6Scale (suc n) v = t6Add v (t6Scale n v)

t6GeodesicN : T6Lattice → T6Lattice → ℕ → T6Lattice
t6GeodesicN start dir n = t6Add start (t6Scale n dir)

-- 沿 g1 的测地线 3 步回归
geodesic-g1-3 : t6GeodesicN t6Zero g1 3 ≡ t6Zero
geodesic-g1-3 = refl

-- 沿 g1 的测地线 6624 步回归 (极向*环向倍数步)
geodesic-g1-6624 : t6GeodesicN t6Zero g1 6624 ≡ t6Zero
geodesic-g1-6624 = refl
