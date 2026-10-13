{-# OPTIONS --rewriting --guardedness #-}

-- | _PM56e
-- M5/M6 级联形链同伦批：多步级联形 H₀+H₁∘H₀ 复合（cascading homotopy）——
--   原「单步纯 H 形」不可能性（_PM56d 反核三基项）的正解路线。
-- 数学背景：纯 H-col（v→e 单级）在 e01/t 基项失配（LHS 搬走 vs ι 保留）。
--   级联形 = 复合同伦三项式 Htot = H₀ + H₁ + H₁∘∂∘H₀（经典复合公式——
--   H₀ : v→e 坍缩级，H₁ : e→f 级联级，交互项 H₁∘∂∘H₀ 吸收级间缺陷）。
--   **K₃ 等肩障碍（新发现）**：∂₁ˢ t 三肩全 T₁ ⇒ 纯 t 形修复给等肩型 (a,a,a)——
--   e01 基项需 (T₁,T₀,T₀) 非对称肩型 ⇒ 单 t 形不可达，需肩差分件（routed 世界）。
-- 核心原则：
-- 1. record 前提范式（零 postulate）｜形式和/lookup 口径（hom-id₁-∀ 同款）
-- 2. 反核法如实（route-hom-naive 同款——残余项 refl 算定 + 见证件）
-- 包含：§1 设计注记｜§2 级联件（H₁/Htot）｜§3 K₃ 级联实例｜§4 等肩障碍｜§5 立界

module _PM56e where

open import Data.List using (List; []; _∷_; _++_)
open import Data.Product using (_,_; _×_)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)

open import Sovereign.Base.Trit using (Trit; T₀; T₁; T₂; _⊕_; _⊗_)
open import Sovereign.Application.FormanMinimal using (Sx; v0; v1; v2; e01; e12; e20; t)
open import _PM56 using (Chain)
open import _PM56b using (negT; negChain; ∂₁ˢ; scl; ∂C)
open import _PM56c using (lookup; π-col)
open import _PM56d using (H-col)

-------------------------------------------------------------------------
-- §1 设计注记（级联骨架——先陈述后施工）
--   同伦方程（_PM56d 同形）：∂C(Htot x) ++ Htot(∂C x) ≡ ι(x) ++ negChain(π-col x)
--   级联三项式：Htot x = H-col x ++ H₁ x ++ H₁ (∂C (H-col x))
--     · H-col（H₀）：v→e 级（顶点面 3×7 全格已绿——_PM56d §2）
--     · H₁：e→f 级联级（边内容送入面 t——坍缩对 e01↔t 的级联消解）
--     · H₁∘∂C∘H-col：交互项（级间缺陷吸收——经典复合公式的第三项）
--   纯 H 形不可能性根源（_PM56d §3）：H₀ 搬走 e01 ⇒ LHS(e01)=T₀ vs ι 面 T₁。
-------------------------------------------------------------------------

-------------------------------------------------------------------------
-- §2 级联件（H₁ 单入口最小形：e01 ↦ t·T₁；Htot 三项式）
-------------------------------------------------------------------------

H₁ : Chain Sx → Chain Sx
H₁ ((e01 , a) ∷ xs) = (t , a ⊗ T₁) ∷ H₁ xs
H₁ (_ ∷ xs)         = H₁ xs
H₁ []               = []

Htot : Chain Sx → Chain Sx
Htot x = H-col x ++ H₁ x ++ H₁ (∂C (H-col x))

-------------------------------------------------------------------------
-- §3 K₃ 级联实例（反核三基项的级联修复形）
-------------------------------------------------------------------------

-- t 基项（原反核 t-hom-id-false）：级联修复 ✓
check-casc-t : lookup (∂C (Htot ((t , T₁) ∷ [])) ++ Htot (∂C ((t , T₁) ∷ []))) t
  ≡ lookup (((t , T₁) ∷ []) ++ negChain (π-col ((t , T₁) ∷ []))) t
check-casc-t = refl

-- e01 基项：e01 肩修复 ✓ + e12 肩修复 ✓（c⊕T₂ = T₁⊕T₂ = T₀ 与 RHS 合）
check-casc-e01 : lookup (∂C (Htot ((e01 , T₁) ∷ [])) ++ Htot (∂C ((e01 , T₁) ∷ []))) e01
  ≡ lookup (((e01 , T₁) ∷ []) ++ negChain (π-col ((e01 , T₁) ∷ []))) e01
check-casc-e01 = refl

check-casc-e01-e12 : lookup (∂C (Htot ((e01 , T₁) ∷ [])) ++ Htot (∂C ((e01 , T₁) ∷ []))) e12
  ≡ lookup (((e01 , T₁) ∷ []) ++ negChain (π-col ((e01 , T₁) ∷ []))) e12
check-casc-e01-e12 = refl

-- 顶点回归（H₁ 仅 e01 入口 ⇒ 顶点面与纯 H 全同——_PM56d §2 三件保持绿）
check-casc-v1 : (c : Sx) →
  lookup (∂C (Htot ((v1 , T₁) ∷ [])) ++ Htot (∂C ((v1 , T₁) ∷ []))) c
    ≡ lookup (((v1 , T₁) ∷ []) ++ negChain (π-col ((v1 , T₁) ∷ []))) c
check-casc-v1 v0 = refl
check-casc-v1 v1 = refl
check-casc-v1 v2 = refl
check-casc-v1 e01 = refl
check-casc-v1 e12 = refl
check-casc-v1 e20 = refl
check-casc-v1 t = refl

check-casc-v2 : (c : Sx) →
  lookup (∂C (Htot ((v2 , T₁) ∷ [])) ++ Htot (∂C ((v2 , T₁) ∷ []))) c
    ≡ lookup (((v2 , T₁) ∷ []) ++ negChain (π-col ((v2 , T₁) ∷ []))) c
check-casc-v2 v0 = refl
check-casc-v2 v1 = refl
check-casc-v2 v2 = refl
check-casc-v2 e01 = refl
check-casc-v2 e12 = refl
check-casc-v2 e20 = refl
check-casc-v2 t = refl

check-casc-v0 : (c : Sx) →
  lookup (∂C (Htot ((v0 , T₁) ∷ [])) ++ Htot (∂C ((v0 , T₁) ∷ []))) c
    ≡ lookup (((v0 , T₁) ∷ []) ++ negChain (π-col ((v0 , T₁) ∷ []))) c
check-casc-v0 v0 = refl
check-casc-v0 v1 = refl
check-casc-v0 v2 = refl
check-casc-v0 e01 = refl
check-casc-v0 e12 = refl
check-casc-v0 e20 = refl
check-casc-v0 t = refl

-------------------------------------------------------------------------
-- §4 等肩障碍（残余项反核——e01 基项的 e20 肩）
--   e20 肩：LHS(e20) = T₁（∂₁ˢ t 等肩型搬入）vs RHS(e20) = T₀（ι 面无 e20）
--   失配见证 + 等肩不可能性注记：∂₁ˢ t = e01·T₁ ⊕ e12·T₁ ⊕ e20·T₁（三肩全 T₁）
--   ⇒ 任意纯 t·a 形修复的肩型为 (a,a,a)——非对称肩型 (T₁,T₀,T₀) 不可达。
-------------------------------------------------------------------------

e20-resid-LHS : lookup (∂C (Htot ((e01 , T₁) ∷ [])) ++ Htot (∂C ((e01 , T₁) ∷ []))) e20
  ≡ T₁
e20-resid-LHS = refl

e20-resid-RHS : lookup (((e01 , T₁) ∷ []) ++ negChain (π-col ((e01 , T₁) ∷ []))) e20
  ≡ T₀
e20-resid-RHS = refl

t₁≢t₀ : T₁ ≡ T₀ → ⊥
t₁≢t₀ ()

e20-shoulder-resid : lookup (∂C (Htot ((e01 , T₁) ∷ [])) ++ Htot (∂C ((e01 , T₁) ∷ []))) e20
  ≡ lookup (((e01 , T₁) ∷ []) ++ negChain (π-col ((e01 , T₁) ∷ []))) e20 → ⊥
e20-shoulder-resid h = t₁≢t₀ (trans (sym e20-resid-LHS) (trans h e20-resid-RHS))

-- 等肩形算定（∂₁ˢ t 三肩系数全 T₁——纯 t 形肩型恒等引理的计算面）
equal-shoulder-t : (a : Trit) →
  (lookup (scl a (∂₁ˢ t)) e01 ≡ lookup (scl a (∂₁ˢ t)) e12)
  × (lookup (scl a (∂₁ˢ t)) e12 ≡ lookup (scl a (∂₁ˢ t)) e20)
equal-shoulder-t T₀ = refl , refl
equal-shoulder-t T₁ = refl , refl
equal-shoulder-t T₂ = refl , refl

-------------------------------------------------------------------------
-- §5 立界（GAP 收窄）
--   (i) e20 肩差分件：需肩差分元素（routed/商面世界——route-hom 立界同族）或
--       H₁ 顶点入口联合求解（级联代数机件全形 ~40-80 行）；
--   (ii) e12/t 基项级联验证（本件 e01 面已闭 + t 面已闭）；
--   (iii) 一般 X 级联复合公式（H₀+H₁+H₁∂H₀ 的交换图）。
