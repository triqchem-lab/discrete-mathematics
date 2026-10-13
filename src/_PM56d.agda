{-# OPTIONS --rewriting --guardedness #-}

-- | _PM56d
-- M5/M6 四小件清偿：④ H-col + 顶点全格实例 + 边面反核（级联障碍量化）
--                ② e01 肩定位桥 ①③ 骨架与精确立界
-- 数学背景：CollapseToMorse 的 K₃ 坍缩（collapseVF：v1↔e12 / v2↔e20 / e01↔t，临界 {v0}，
--   β = (1,0,0) 完美）——π-col 撤回到临界 v0；H-col 为其链同伦。
--   hom-id 形（_PM56b 三对件同款）：∂C(H x) ++ H(∂C x) ≡ ι(x) ++ negChain(π-col x)。
-- 核心原则：
-- 1. 形式和/lookup 口径（hom-id₁-∀ 同款——字面序形随 FreeAb 商面批）
-- 2. 顶点全格 3×7 实例全证；边/面基项**失配如实反核**（route-hom-naive 先例——
--    e01↔t 配对的坍缩级联在纯 H 形下不可达，量化为 T₀≢T₁/T₂≢T₀ 见证件）
-- 3. record 前提范式；零洞零 postulate
-- 包含：§1 H-col｜§2 顶点全格实例（3×7）｜§3 边面反核（级联障碍）｜§4 e01 肩定位桥｜§5 骨架+立界

module _PM56d where

open import Data.List using (List; []; _∷_; _++_)
open import Data.Product using (_,_)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)

open import Sovereign.Base.Trit using (Trit; T₀; T₁; T₂; _⊕_; _⊗_)
open import Sovereign.Topology.FormanMinimal using (Sx; v0; v1; v2; e01; e12; e20; t)
open import _PM56 using (Chain)
open import _PM56b using (negT; negChain; ∂₁ˢ; scl; ∂C)
open import _PM56c using (lookup; π-col)
open import Sovereign.Application.MorseBoundaryK3 using (∂M-e₂₀-v₁; ∂M-e₂₀-v₂)

-------------------------------------------------------------------------
-- §1 H-col（坍缩同伦——顶点面系数设计）
--   顶点基项的 hom-id 恒等式定系数：H(v1) = e12·T₂（∂(e12·T₂) 的 v1 肩 T₂⊗T₂ = T₁
--   恰为 ι⊖π 的 v1 侧系数）；H(v2) = e20·T₂ 同型；临界 v0 与边/t 不搬（H = 0）。
-------------------------------------------------------------------------

H-col : Chain Sx → Chain Sx
H-col ((v0 , a) ∷ xs)  = H-col xs
H-col ((v1 , a) ∷ xs)  = (e12 , a ⊗ T₂) ∷ H-col xs
H-col ((v2 , a) ∷ xs)  = (e20 , a ⊗ T₂) ∷ H-col xs
H-col ((e01 , a) ∷ xs) = H-col xs
H-col ((e12 , a) ∷ xs) = H-col xs
H-col ((e20 , a) ∷ xs) = H-col xs
H-col ((t , a) ∷ xs)   = H-col xs
H-col []               = []

-------------------------------------------------------------------------
-- §2 顶点全格实例（3 基项 × 7 格点 = 21 面全 refl 过内核）
-------------------------------------------------------------------------

check-hc-v0 : (c : Sx) →
  lookup (∂C (H-col ((v0 , T₁) ∷ [])) ++ H-col (∂C ((v0 , T₁) ∷ []))) c
    ≡ lookup (((v0 , T₁) ∷ []) ++ negChain (π-col ((v0 , T₁) ∷ []))) c
check-hc-v0 v0 = refl
check-hc-v0 v1 = refl
check-hc-v0 v2 = refl
check-hc-v0 e01 = refl
check-hc-v0 e12 = refl
check-hc-v0 e20 = refl
check-hc-v0 t = refl

check-hc-v1 : (c : Sx) →
  lookup (∂C (H-col ((v1 , T₁) ∷ [])) ++ H-col (∂C ((v1 , T₁) ∷ []))) c
    ≡ lookup (((v1 , T₁) ∷ []) ++ negChain (π-col ((v1 , T₁) ∷ []))) c
check-hc-v1 v0 = refl
check-hc-v1 v1 = refl
check-hc-v1 v2 = refl
check-hc-v1 e01 = refl
check-hc-v1 e12 = refl
check-hc-v1 e20 = refl
check-hc-v1 t = refl

check-hc-v2 : (c : Sx) →
  lookup (∂C (H-col ((v2 , T₁) ∷ [])) ++ H-col (∂C ((v2 , T₁) ∷ []))) c
    ≡ lookup (((v2 , T₁) ∷ []) ++ negChain (π-col ((v2 , T₁) ∷ []))) c
check-hc-v2 v0 = refl
check-hc-v2 v1 = refl
check-hc-v2 v2 = refl
check-hc-v2 e01 = refl
check-hc-v2 e12 = refl
check-hc-v2 e20 = refl
check-hc-v2 t = refl

-------------------------------------------------------------------------
-- §3 边面反核（坍缩级联障碍量化——e01↔t 配对的纯 H 形不可达）
--   反核法（route-hom-naive 同款）：两侧 lookup 各 refl 算定 + 构造子相异见证。
-------------------------------------------------------------------------

-- e01 基项：LHS(e01) = T₀（H 搬走 e01）vs RHS(e01) = T₁（ι 面）——失配
e01-LHS : lookup (∂C (H-col ((e01 , T₁) ∷ [])) ++ H-col (∂C ((e01 , T₁) ∷ []))) e01 ≡ T₀
e01-LHS = refl
e01-RHS : lookup (((e01 , T₁) ∷ []) ++ negChain (π-col ((e01 , T₁) ∷ []))) e01 ≡ T₁
e01-RHS = refl

t₀≢t₁ : T₀ ≡ T₁ → ⊥
t₀≢t₁ ()

e01-hom-id-false : lookup (∂C (H-col ((e01 , T₁) ∷ [])) ++ H-col (∂C ((e01 , T₁) ∷ []))) e01
                 ≡ lookup (((e01 , T₁) ∷ []) ++ negChain (π-col ((e01 , T₁) ∷ []))) e01 → ⊥
e01-hom-id-false p = t₀≢t₁ (trans (sym e01-LHS) (trans p e01-RHS))

-- t 基项：LHS(t) = T₀ vs RHS(t) = T₁——失配（t 为 e01 的坍缩目标，同症）
t-LHS : lookup (∂C (H-col ((t , T₁) ∷ [])) ++ H-col (∂C ((t , T₁) ∷ []))) t ≡ T₀
t-LHS = refl
t-RHS : lookup (((t , T₁) ∷ []) ++ negChain (π-col ((t , T₁) ∷ []))) t ≡ T₁
t-RHS = refl

t-hom-id-false : lookup (∂C (H-col ((t , T₁) ∷ [])) ++ H-col (∂C ((t , T₁) ∷ []))) t
               ≡ lookup (((t , T₁) ∷ []) ++ negChain (π-col ((t , T₁) ∷ []))) t → ⊥
t-hom-id-false p = t₀≢t₁ (trans (sym t-LHS) (trans p t-RHS))

-- e12 基项的 e20 肩溢出：H(∂C e12) 搬出 e20·T₂ 而 ι⊖π 侧无 e20 项——失配
e12-e20-LHS : lookup (∂C (H-col ((e12 , T₁) ∷ [])) ++ H-col (∂C ((e12 , T₁) ∷ []))) e20 ≡ T₂
e12-e20-LHS = refl
e12-e20-RHS : lookup (((e12 , T₁) ∷ []) ++ negChain (π-col ((e12 , T₁) ∷ []))) e20 ≡ T₀
e12-e20-RHS = refl

t₂≢t₀ : T₂ ≡ T₀ → ⊥
t₂≢t₀ ()

e12-face-false : lookup (∂C (H-col ((e12 , T₁) ∷ [])) ++ H-col (∂C ((e12 , T₁) ∷ []))) e20
               ≡ lookup (((e12 , T₁) ∷ []) ++ negChain (π-col ((e12 , T₁) ∷ []))) e20 → ⊥
e12-face-false p = t₂≢t₀ (trans (sym e12-e20-LHS) (trans p e12-e20-RHS))

-- 级联障碍定性注记：坍缩对 e01↔t 与 v1↔e12/v2↔e20 的**级联复合**（e01 的内容经 t
--   下行、e12/e20 的肩上行）在单步纯 H 形下不可同时满足——真同伦需**多步级联形**
--   （H = H₀ + H₁∘H₀ + … 复合或 cascading homotopy），精确残余见 §5。

-------------------------------------------------------------------------
-- §4 e01 肩定位桥（pair② 吸收项的路由理论定位——系数面指认）
-------------------------------------------------------------------------

-- ρ₂ᵃ 的 e01 补偿肩系数（check-ρ2a-e12 的 (e01 , T₁)/(e20 , T₁)）与 MorseBoundaryK3
--   的 ∂M-e₂₀ 分量对齐（pair③ 的 b/e' = ∂M-e₂₀-v₁/v₂）——指认桥：
shoulder-locate-v₁ : T₁ ≡ ∂M-e₂₀-v₁
shoulder-locate-v₁ = refl

shoulder-locate-v₂ : T₂ ≡ ∂M-e₂₀-v₂
shoulder-locate-v₂ = refl

-- 定位注记：ρ₂ᵃ 的补偿肩即 ∂M-e₂₀ 路由系数的同伦面像——CoefRoute 侧的
--   cr-via 系数形（_PM3b via-propagate 同族）为其理论定位（witness 面在
--   _PM3c entryOf 桥）；本件完成「系数值 = ∂M 分量」的指认，路由同伦项
--   的完整形随 routed/商面批（§5 (iii)）。

-------------------------------------------------------------------------
-- §5 骨架与精确立界（收窄注记）
-------------------------------------------------------------------------
--   (i) hom-id₁-∀ 全格字面形：随 FreeAb 商面批（形式和口径已闭——_PM56c §1）；
--   (ii) 路由定位：✅ 本件 §4 指认桥完成（系数面 = ∂M 分量 refl 对齐）；
--       残余 = CoefRoute cr-via 侧同伦项 witness（_PM3c entryOf 面衔接——~10-20 行）；
--   (iii) pair③ 路由 H 链同伦：点态已反核（_PM56c route-hom-naive-*）——真同伦
--       须 routed/商面世界（∂M/∂₁ˢ 双边界桥 + DirectExit 前提具体化）——立界照旧；
--   (iv) Collapse 全对接：✅ 顶点全格 3×7 实例（§2）+ 边面反核量化（§3）——
--       **纯 H 形不可能性已定理化**（e01-hom-id-false/t-hom-id-false/e12-face-false）；
--       残余 = 多步级联同伦形（cascading homotopy H₀+H₁∘H₀ 复合——需级联代数
--       机件 ~40-80 行，构造性路线明确）。
-- 共同前提口径：零洞零 postulate；record 前提范式；lookup = _PM56c 形式和口径。
