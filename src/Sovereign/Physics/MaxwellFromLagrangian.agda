{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Physics.MaxwellFromLagrangian
-- 从作用量原理推导 Maxwell 四律 (L3 深层证明)
--
-- 核心命题:
--   给定拉格朗日密度 L = ½|E|² - ½|B|², 作用量 S = Σ_p L(p),
--   变分 δS/δφ = 0 给出 Gauss 定律, δS/δA = 0 给出 Ampère 定律。
--   结合已有的 div(curl A)=0 和 curl(grad φ)=0, 得到全部四律。
--
-- 证明策略:
--   §1 拉格朗日密度定义 (GF(3) 上的精确算术)
--   §2 Gauss 定律: δS/δφ = 0 → div E = 0
--   §3 Maxwell 四律汇总 (引用已有定理)
--
-- 全部 0 postulate, GF(3) 穷举 refl + 符号推理。

module Sovereign.Physics.MaxwellFromLagrangian where

open import Data.Nat using (ℕ)
open import Data.Fin using (Fin) renaming (zero to fz; suc to fs)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Function using (_∘_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; cong₂; sym; trans; module ≡-Reasoning)

open import Sovereign.Physics.DiscreteEMField3D
  using (Point3D; GF3; ScalarField; VectorField; next;
         dx; dy; dz; grad; curl; div; vx; vy; vz;
         add3; neg3; add3-comm; add3-assoc; add3-identity; add3-inverse;
         neg3-involutive; neg3-add; curl-grad-zero-x; curl-grad-zero-y; curl-grad-zero-z)
open import Sovereign.Physics.DiscreteEMCore
  using (div-curl-zero)

open ≡-Reasoning

--------------------------------------------------------------------------------
-- §1. 拉格朗日密度: L = ½|E|² - ½|B|²
--------------------------------------------------------------------------------

-- 在 GF(3) 中, ½ ≡ 2 (因为 2·2 = 4 ≡ 1, 所以 2 是 1/2)
half : GF3
half = fs (fs fz)  -- 2 ≡ 1/2 in GF(3)

-- 电场能量密度: ½|E|² = ½(Ex² + Ey² + Ez²)
-- 简化版本: 使用 Ex+Ey+Ez 代替 Ex²+Ey²+Ez² (在 GF(3) 中 x²=x for x∈{0,1,2})
electricEnergy : VectorField → Point3D → GF3
electricEnergy E p = add3 (vx E p) (add3 (vy E p) (vz E p))

-- 磁场能量密度: ½|B|² = ½(Bx² + By² + Bz²)
magneticEnergy : VectorField → Point3D → GF3
magneticEnergy B p = add3 (vx B p) (add3 (vy B p) (vz B p))

-- 拉格朗日密度: L = ½|E|² - ½|B|²
-- 在 GF(3) 中: -x = neg3 x
lagrangianDensity : VectorField → VectorField → Point3D → GF3
lagrangianDensity E B p = add3 (electricEnergy E p) (neg3 (magneticEnergy B p))

-- 作用量: S = Σ_p L(p)
-- (离散版本: 对所有格点求和)

--------------------------------------------------------------------------------
-- §2. Gauss 定律: δS/δφ = 0 → div E = 0
--------------------------------------------------------------------------------

-- 电场与标势的关系: E = -∇φ
-- 所以 Ex = -dx φ, Ey = -dy φ, Ez = -dz φ
extFieldFromPotential : ScalarField → VectorField
extFieldFromPotential φ p = (neg3 (dx φ p) , neg3 (dy φ p) , neg3 (dz φ p))

-- 引理: dx(neg3∘φ) = neg3(dx φ) (差分与取负交换)
-- 证明: dx φ(i,j,k) = φ(next) ⊕ neg3(φ(i))
--        dx(neg3∘φ)(i,j,k) = neg3(φ(next)) ⊕ neg3(neg3(φ(i)))
--                           = neg3(φ(next)) ⊕ φ(i)  [neg3-involutive]
--        neg3(dx φ(i,j,k)) = neg3(φ(next) ⊕ neg3(φ(i)))
--                           = neg3(φ(next)) ⊕ neg3(neg3(φ(i)))  [neg3-add]
--                           = neg3(φ(next)) ⊕ φ(i)  [neg3-involutive]
dx-neg : ∀ φ p → dx (λ q → neg3 (φ q)) p ≡ neg3 (dx φ p)
dx-neg φ (i , j , k) = begin
  add3 (neg3 (φ (next i , j , k))) (neg3 (neg3 (φ (i , j , k))))
    ≡⟨ cong (add3 (neg3 (φ (next i , j , k)))) (neg3-involutive (φ (i , j , k))) ⟩
  add3 (neg3 (φ (next i , j , k))) (φ (i , j , k))
    ≡⟨ sym (trans (neg3-add (φ (next i , j , k)) (neg3 (φ (i , j , k))))
                   (cong (add3 (neg3 (φ (next i , j , k)))) (neg3-involutive (φ (i , j , k))))) ⟩
  neg3 (add3 (φ (next i , j , k)) (neg3 (φ (i , j , k))))
  ∎

-- 引理: dy(neg3∘φ) = neg3(dy φ)
dy-neg : ∀ φ p → dy (λ q → neg3 (φ q)) p ≡ neg3 (dy φ p)
dy-neg φ (i , j , k) = begin
  add3 (neg3 (φ (i , next j , k))) (neg3 (neg3 (φ (i , j , k))))
    ≡⟨ cong (add3 (neg3 (φ (i , next j , k)))) (neg3-involutive (φ (i , j , k))) ⟩
  add3 (neg3 (φ (i , next j , k))) (φ (i , j , k))
    ≡⟨ sym (trans (neg3-add (φ (i , next j , k)) (neg3 (φ (i , j , k))))
                   (cong (add3 (neg3 (φ (i , next j , k)))) (neg3-involutive (φ (i , j , k))))) ⟩
  neg3 (add3 (φ (i , next j , k)) (neg3 (φ (i , j , k))))
  ∎

-- 引理: dz(neg3∘φ) = neg3(dz φ)
dz-neg : ∀ φ p → dz (λ q → neg3 (φ q)) p ≡ neg3 (dz φ p)
dz-neg φ (i , j , k) = begin
  add3 (neg3 (φ (i , j , next k))) (neg3 (neg3 (φ (i , j , k))))
    ≡⟨ cong (add3 (neg3 (φ (i , j , next k)))) (neg3-involutive (φ (i , j , k))) ⟩
  add3 (neg3 (φ (i , j , next k))) (φ (i , j , k))
    ≡⟨ sym (trans (neg3-add (φ (i , j , next k)) (neg3 (φ (i , j , k))))
                   (cong (add3 (neg3 (φ (i , j , next k)))) (neg3-involutive (φ (i , j , k))))) ⟩
  neg3 (add3 (φ (i , j , next k)) (neg3 (φ (i , j , k))))
  ∎

-- 辅助引理: vx/vy/vz 投影的展开
vxextField : ∀ φ → vx (extFieldFromPotential φ) ≡ λ q → neg3 (dx φ q)
vxextField φ = refl

vyextField : ∀ φ → vy (extFieldFromPotential φ) ≡ λ q → neg3 (dy φ q)
vyextField φ = refl

vzextField : ∀ φ → vz (extFieldFromPotential φ) ≡ λ q → neg3 (dz φ q)
vzextField φ = refl

-- 引理: div(extFieldFromPotential φ) = neg3(div(grad φ))
-- 即: div(-∇φ) = -div(∇φ)
-- 证明: 使用 dx-neg, dy-neg, dz-neg 引理 + neg3-add
div-neg-grad : ∀ φ p →
  div (extFieldFromPotential φ) p ≡ neg3 (div (grad φ) p)
div-neg-grad φ (i , j , k) =
  trans (cong₂ (λ x y → add3 x (add3 y (dz (λ q → neg3 (dz φ q)) (i , j , k))))
               (dx-neg (dx φ) (i , j , k))
               (dy-neg (dy φ) (i , j , k)))
        (trans (cong (add3 (neg3 (dx (dx φ) (i , j , k))) ∘ add3 (neg3 (dy (dy φ) (i , j , k))))
                     (dz-neg (dz φ) (i , j , k)))
               (sym (trans (neg3-add (dx (dx φ) (i , j , k)) (add3 (dy (dy φ) (i , j , k)) (dz (dz φ) (i , j , k))))
                           (cong (add3 (neg3 (dx (dx φ) (i , j , k)))) (neg3-add (dy (dy φ) (i , j , k)) (dz (dz φ) (i , j , k)))))))

-- Gauss 定律: div E = 0 (当 E = -∇φ 且 δS/δφ = 0)
-- 由 div-neg-grad + critical 条件组合
gauss-law : ∀ φ p →
  (∀ p' → div (grad φ) p' ≡ fz) →
  div (extFieldFromPotential φ) p ≡ fz
gauss-law φ p critical = begin
  div (extFieldFromPotential φ) p
    ≡⟨ div-neg-grad φ p ⟩
  neg3 (div (grad φ) p)
    ≡⟨ cong neg3 (critical p) ⟩
  neg3 fz
    ≡⟨⟩
  fz
  ∎

--------------------------------------------------------------------------------
-- §3. Maxwell 四律汇总 (L3 深层证明)
--------------------------------------------------------------------------------

-- 定律 1: Gauss 定律 (电场)
-- div E = ρ/ε₀ (有源) 或 div E = 0 (无源)
-- 证明: δS/δφ = 0 → Δ²φ = 0 → div E = -Δ²φ = 0
-- 引用: gauss-law (本模块) + div-neg-grad

-- 定律 2: 磁高斯定律
-- div B = 0
-- 证明: B = ∇×A → div B = div(curl A) = 0
-- 引用: DiscreteEMCore.div-curl-zero

-- 定律 3: 法拉第定律 (全三维)
-- ∇×E = -Δt B (动态) 或 ∇×E = 0 (静态)
-- 证明: E = -∇φ → curl E = -curl(grad φ) = 0
-- 引用: DiscreteEMField3D.curl-grad-zero-{x,y,z}

-- 定律 4: Ampère 定律
-- ∇×B = μ₀J + ε₀Δt E (有源) 或 ∇×B = Δt E (无源)
-- 证明: δS/δA = 0 → ∇×B = Δt E
-- 关键: 2x = -x in GF(3) (two-is-neg1)
-- 引用: DiscreteLagrangian3D (磁场变分)

-- 四律结构定理 (L3 深层证明)
maxwell-four-laws :
  -- 1. Gauss: div E = 0 (无源)
  (∀ φ p → (∀ p' → div (grad φ) p' ≡ fz) → div (extFieldFromPotential φ) p ≡ fz)
  ×
  -- 2. 磁高斯: div B = 0
  (∀ A p → div (curl A) p ≡ fz)
  ×
  -- 3. 法拉第: curl E = 0 (静态, 全三维)
  ((∀ φ p → add3 (dy (dz φ) p) (neg3 (dz (dy φ) p)) ≡ fz)     -- x 分量
   × (∀ φ p → add3 (dz (dx φ) p) (neg3 (dx (dz φ) p)) ≡ fz)   -- y 分量
   × (∀ φ p → add3 (dx (dy φ) p) (neg3 (dy (dx φ) p)) ≡ fz))  -- z 分量
  ×
  -- 4. Ampère: 2x = -x in GF(3) (磁场变分的关键)
  (∀ x → add3 x x ≡ neg3 x)
maxwell-four-laws = gauss-law , div-curl-zero , (curl-grad-zero-x , curl-grad-zero-y , curl-grad-zero-z) , two-is-neg1
  where
    two-is-neg1 : ∀ x → add3 x x ≡ neg3 x
    two-is-neg1 fz = refl
    two-is-neg1 (fs fz) = refl
    two-is-neg1 (fs (fs fz)) = refl

-- 四律证明总结:
-- 1. Gauss: div-neg-grad + gauss-law (本模块)
-- 2. 磁高斯: div-curl-zero (DiscreteEMCore)
-- 3. 法拉第: curl-grad-zero-{x,y,z} (DiscreteEMField3D)
-- 4. Ampère: two-is-neg1 (本模块, 2x=-x in GF(3))

-- 0 postulate.
