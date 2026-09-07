{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Algebra.Dihedral.DihedralD12
-- 二面体群 D₁₂ (24阶) 的形式化
--
-- 核心原则:
--   1. D₁₂ = DC ⋊_ρ C₂，其中 DC = DuodecPoint，ρ 是取逆自同构
--   2. 半直积乘法: (x,ε)·(y,δ) = (x·ρ^ε(y), ε+δ)
--   3. ρ 必须作用在第二个分量（被乘的元素），不是第一个
--   4. D₁₂ 是非交换的，但包含 DC 作为正规子群
--
-- 包含: 反射定义、半直积构造、群公理证明、非交换性、rho-共轭验证

module Sovereign.Algebra.Dihedral.DihedralD12 where

open import Data.Product using (_×_; _,_; Σ; proj₁; proj₂)
open import Data.Nat using (ℕ)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong; cong₂; sym; trans)
open import Sovereign.Base.Trit using (Trit; T₀; T₁; T₂; _⊕_; negate)
open import Sovereign.Algebra.GroupTheory.DuodecClock using
  (DuodecPoint; AlphaPower; a0; a1; a2; a3; mixedOp; duodec-e; duodec-inv;
   mixedOp-assoc; mixedOp-comm; mixedOp-identityˡ; mixedOp-identityʳ; mixedOp-inverse;
   mulAlpha; rho; rho-involution; rho-is-inv; rho-mixedOp; mixedOp-comm)

--------------------------------------------------------------------------------
-- §1. 反射的定义
--------------------------------------------------------------------------------

-- 损益反射 λ: (t, αᵏ) ↦ (-t, αᵏ)
lambda : DuodecPoint → DuodecPoint
lambda (t , a) = (negate t , a)

-- 相位反射 μ: (t, αᵏ) ↦ (t, α⁻ᵏ)
mu : DuodecPoint → DuodecPoint
mu (t , a0) = (t , a0)
mu (t , a1) = (t , a3)
mu (t , a2) = (t , a2)
mu (t , a3) = (t , a1)

-- λ 是对合
lambda-involution : ∀ p → lambda (lambda p) ≡ p
lambda-involution (T₀ , a) = refl
lambda-involution (T₁ , a) = refl
lambda-involution (T₂ , a) = refl

-- μ 是对合
mu-involution : ∀ p → mu (mu p) ≡ p
mu-involution (T₀ , a0) = refl
mu-involution (T₀ , a1) = refl
mu-involution (T₀ , a2) = refl
mu-involution (T₀ , a3) = refl
mu-involution (T₁ , a0) = refl
mu-involution (T₁ , a1) = refl
mu-involution (T₁ , a2) = refl
mu-involution (T₁ , a3) = refl
mu-involution (T₂ , a0) = refl
mu-involution (T₂ , a1) = refl
mu-involution (T₂ , a2) = refl
mu-involution (T₂ , a3) = refl

-- ρ² = id（已在 DuodecClock 中证明, 此处 import rho-involution）

--------------------------------------------------------------------------------
-- §2. 二面体群 D₁₂ = DC ⋊_ρ C₂
--------------------------------------------------------------------------------

-- D₁₂ 的元素: 旋转 (DC 本体) 或 反射 (ρ · DC)
data DihedralElement : Set where
  rotate  : DuodecPoint → DihedralElement    -- 旋转分量 (x, 0)
  reflect : DuodecPoint → DihedralElement    -- 反射分量 (x, 1)

-- D₁₂ 的乘法（修正版: ρ 作用在第二个分量）
-- 标准半直积: (x,ε)·(y,δ) = (x·ρ^ε(y), ε+δ)
_⋆_ : DihedralElement → DihedralElement → DihedralElement
rotate  p ⋆ rotate  q = rotate  (mixedOp p q)            -- ε=0, δ=0: x·y
rotate  p ⋆ reflect q = reflect (mixedOp p q)            -- ε=0, δ=1: x·y
reflect p ⋆ rotate  q = reflect (mixedOp p (rho q))      -- ε=1, δ=0: x·ρ(y)
reflect p ⋆ reflect q = rotate  (mixedOp p (rho q))      -- ε=1, δ=1: x·ρ(y)

-- D₁₂ 的单位元
d12-e : DihedralElement
d12-e = rotate duodec-e

-- D₁₂ 的逆元
d12-inv : DihedralElement → DihedralElement
d12-inv (rotate p)  = rotate (duodec-inv p)
d12-inv (reflect p) = reflect p  -- 反射的逆是自身

-- D₁₂ 的阶
d12-order : ℕ
d12-order = 24

--------------------------------------------------------------------------------
-- §3. 群公理
--------------------------------------------------------------------------------

-- 结合律辅助 1: (ρq)·(ρr) 重排到 ρ(q·r) 的中间态 (供反射×旋转×情形)
-- 需要: mixedOp (mixedOp p (rho q)) (rho r) ≡ mixedOp p (rho (mixedOp q r))
d12-rho-twist : ∀ p q r →
  mixedOp (mixedOp p (rho q)) (rho r) ≡ mixedOp p (rho (mixedOp q r))
d12-rho-twist p q r =
  trans (mixedOp-assoc p (rho q) (rho r))
        (cong (mixedOp p) (sym (rho-mixedOp q r)))

-- 结合律辅助 2: (ρq)·r 重排到 ρ(q·ρr) 的中间态 (供反射×反射×情形)
-- 需要: mixedOp (mixedOp p (rho q)) r ≡ mixedOp p (rho (mixedOp q (rho r)))
d12-rho-twist2 : ∀ p q r →
  mixedOp (mixedOp p (rho q)) r ≡ mixedOp p (rho (mixedOp q (rho r)))
d12-rho-twist2 p q r =
  trans (mixedOp-assoc p (rho q) r)
        (cong (mixedOp p)
              (trans (sym (cong (mixedOp (rho q)) (rho-involution r)))
                     (sym (rho-mixedOp q (rho r)))))

-- 结合律
d12-assoc : ∀ x y z → (x ⋆ y) ⋆ z ≡ x ⋆ (y ⋆ z)
d12-assoc (rotate p) (rotate q) (rotate r) =
  cong rotate (mixedOp-assoc p q r)
d12-assoc (rotate p) (rotate q) (reflect r) =
  cong reflect (mixedOp-assoc p q r)
d12-assoc (rotate p) (reflect q) (rotate r) =
  cong reflect (mixedOp-assoc p q (rho r))
d12-assoc (rotate p) (reflect q) (reflect r) =
  cong rotate (mixedOp-assoc p q (rho r))
d12-assoc (reflect p) (rotate q) (rotate r) =
  cong reflect (d12-rho-twist p q r)
d12-assoc (reflect p) (rotate q) (reflect r) =
  cong rotate (d12-rho-twist p q r)
d12-assoc (reflect p) (reflect q) (rotate r) =
  cong rotate (d12-rho-twist2 p q r)
d12-assoc (reflect p) (reflect q) (reflect r) =
  cong reflect (d12-rho-twist2 p q r)

-- 左单位元
d12-identityˡ : ∀ x → d12-e ⋆ x ≡ x
d12-identityˡ (rotate p)  = cong rotate (mixedOp-identityˡ p)
d12-identityˡ (reflect p) = cong reflect (mixedOp-identityˡ p)

-- 右单位元
d12-identityʳ : ∀ x → x ⋆ d12-e ≡ x
d12-identityʳ (rotate p)  = cong rotate (mixedOp-identityʳ p)
d12-identityʳ (reflect p) = cong reflect (mixedOp-identityʳ p)

-- 左逆元
d12-inverseˡ : ∀ x → x ⋆ d12-inv x ≡ d12-e
d12-inverseˡ (rotate p)  = cong rotate (mixedOp-inverse p)
d12-inverseˡ (reflect p) =
  cong rotate (trans (cong (mixedOp p) (rho-is-inv p)) (mixedOp-inverse p))

-- 右逆元
d12-inverseʳ : ∀ x → d12-inv x ⋆ x ≡ d12-e
d12-inverseʳ (rotate p)  =
  cong rotate (trans (mixedOp-comm (duodec-inv p) p) (mixedOp-inverse p))
d12-inverseʳ (reflect p) =
  cong rotate (trans (cong (mixedOp p) (rho-is-inv p)) (mixedOp-inverse p))

--------------------------------------------------------------------------------
-- §4. 定义关系验证: ρ-共轭
--------------------------------------------------------------------------------

-- 关键验证: reflect · rotate g · reflect = rotate (ρ(g)) = rotate (g⁻¹)
-- 这是 D₁₂ 的定义关系
rho-conjugation : ∀ g →
  (reflect duodec-e ⋆ rotate g) ⋆ reflect duodec-e ≡ rotate (rho g)
rho-conjugation g =
  let
    step1 : reflect duodec-e ⋆ rotate g ≡ reflect (mixedOp duodec-e (rho g))
    step1 = refl

    step2 : reflect (mixedOp duodec-e (rho g)) ≡ reflect (rho g)
    step2 = cong reflect (mixedOp-identityˡ (rho g))

    step3 : reflect (rho g) ⋆ reflect duodec-e ≡ rotate (mixedOp (rho g) (rho duodec-e))
    step3 = refl

    step4 : rotate (mixedOp (rho g) (rho duodec-e)) ≡ rotate (rho g)
    step4 = cong rotate (mixedOp-identityʳ (rho g))
  in
    trans (cong (λ x → x ⋆ reflect duodec-e) step2) step4

-- 推论: reflect · rotate g · reflect = rotate (g⁻¹)
rho-conjugation-inverse : ∀ g →
  (reflect duodec-e ⋆ rotate g) ⋆ reflect duodec-e ≡ rotate (duodec-inv g)
rho-conjugation-inverse g =
  trans (rho-conjugation g) (cong rotate (rho-is-inv g))

--------------------------------------------------------------------------------
-- §5. 非交换性证明
--------------------------------------------------------------------------------

-- ρ(T₁,a0) = (T₂,a0)
rho-T₁-a0 : rho (T₁ , a0) ≡ (T₂ , a0)
rho-T₁-a0 = refl

-- reflect(T₁,a1) ≠ reflect(T₂,a1)
reflect-T₁a1-not-T₂a1 : reflect (T₁ , a1) ≢ reflect (T₂ , a1)
reflect-T₁a1-not-T₂a1 ()

-- 非交换性: rotate(T₁,a0) ⋆ reflect(T₀,a1) ≠ reflect(T₀,a1) ⋆ rotate(T₁,a0)
d12-non-commutative :
  Σ (DihedralElement × DihedralElement)
    (λ (p , q) → p ⋆ q ≢ q ⋆ p)
d12-non-commutative =
  (rotate (T₁ , a0) , reflect (T₀ , a1)) ,
  (λ eq →
    let
      -- LHS: rotate(T₁,a0) ⋆ reflect(T₀,a1) = reflect(mixedOp(T₁,a0)(T₀,a1)) = reflect(T₁,a1)
      lhs : rotate (T₁ , a0) ⋆ reflect (T₀ , a1) ≡ reflect (T₁ , a1)
      lhs = refl

      -- RHS: reflect(T₀,a1) ⋆ rotate(T₁,a0) = reflect(mixedOp(T₀,a1)(ρ(T₁,a0)))
      --     = reflect(mixedOp(T₀,a1)(T₂,a0)) = reflect(T₂,a1)
      rhs : reflect (T₀ , a1) ⋆ rotate (T₁ , a0) ≡ reflect (T₂ , a1)
      rhs = cong reflect (cong (λ x → mixedOp (T₀ , a1) x) rho-T₁-a0)
    in
      reflect-T₁a1-not-T₂a1 (trans (sym lhs) (trans eq rhs))
  )

--------------------------------------------------------------------------------
-- §6. DC 嵌入 D₁₂
--------------------------------------------------------------------------------

embed-dc : DuodecPoint → DihedralElement
embed-dc = rotate

embed-dc-hom : ∀ p q → embed-dc (mixedOp p q) ≡ embed-dc p ⋆ embed-dc q
embed-dc-hom p q = refl

embed-dc-injective : ∀ p q → embed-dc p ≡ embed-dc q → p ≡ q
embed-dc-injective p q refl = refl

--------------------------------------------------------------------------------
-- §7. 反射子群
--------------------------------------------------------------------------------

reflect-subgroup : DihedralElement
reflect-subgroup = reflect duodec-e

rho-order-2 : reflect-subgroup ⋆ reflect-subgroup ≡ d12-e
rho-order-2 = cong rotate (mixedOp-inverse duodec-e)

-- 短正合列: 1 → DC → D₁₂ → C₂ → 1
data C2 : Set where
  c2-0 : C2  -- 旋转
  c2-1 : C2  -- 反射

d12-sign : DihedralElement → C2
d12-sign (rotate _)  = c2-0
d12-sign (reflect _) = c2-1

sign-surjective : ∀ t → Σ DihedralElement (λ x → d12-sign x ≡ t)
sign-surjective c2-0 = rotate duodec-e , refl
sign-surjective c2-1 = reflect duodec-e , refl

--------------------------------------------------------------------------------
-- §8. 结论
--------------------------------------------------------------------------------

-- D₁₂ = DC ⋊_ρ C₂ 是 24 阶二面体群
-- DC 是 12 阶交换子群（旋转）
-- ⟨ρ⟩ 是 2 阶反射子群
-- D₁₂ 是非交换的，但包含 DC 作为正规子群
-- 定义关系: ρ·g·ρ = g⁻¹ 已验证

-- 0 postulate.
