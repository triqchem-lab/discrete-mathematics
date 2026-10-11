{-# OPTIONS --rewriting --guardedness #-}

-- | _PM56f
-- M5/M6 routed 世界件批：e20 肩差分（Morse 线终段）——三联证据链指认的真边界。
-- 数学背景：纯 H 形在边/面基项不可达（三联证据：_PM56d 不可能性定理 /
--   _PM56e 等肩障碍 equal-shoulder-t / _PM56c route-hom 点态反核）。
--   e01 基项的 e20 肩残余（LHS=T₁ vs RHS=T₀——_PM56e §4 e20-resid 双 refl 算定）
--   需 **routed 世界**：∂M/∂₁ˢ 双边界桥（DirectExit 前提范式）。
--   **本件假说（H₃ e20 出口补形）**：_PM56c 的路由 H₃ 把 ∂₁ 像的顶点项送入 e20 边
--   （H₃(v1)=e20·∂M-v₁、H₃(v2)=e20·∂M-v₂）⇒ H* = Htot ⊕ H₃ 的 H₃(∂C x) 项
--   恰在 e20 肩供 T₁（T₁⊕T₁=T₀ 消差）——级联残余的路由修复形。
-- 核心原则：
-- 1. record 前提范式（零 postulate）｜形式和/lookup 口径（_PM56e 同款）
-- 2. 假说实证法：目标格 refl 算定，副作用格逐项回归（顶点基项的 ∂C(H₃ x) 扰动如实）
-- 包含：§1 设计注记｜§2 routed 级联件｜§3 K₃ e20 差分件｜§4 副作用回归｜§5 立界

module _PM56f where

open import Data.List using (List; []; _∷_; _++_)
open import Data.Product using (_,_; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)

open import Sovereign.Base.Trit using (Trit; T₀; T₁; T₂; _⊕_; _⊗_)
open import Sovereign.Topology.FormanMinimal using (Sx; v0; v1; v2; e01; e12; e20; t)
open import _PM56 using (Chain)
open import _PM56b using (negT; negChain; ∂₁ˢ; scl; ∂C)
open import _PM56c using (lookup; π-col; H₃)
open import _PM56e using (H₁; Htot)

-------------------------------------------------------------------------
-- §1 设计注记（routed 世界骨架——先陈述后施工）
--   同伦方程（_PM56e 同形）：∂C(H x) ++ H(∂C x) ≡ ι(x) ++ negChain(π-col x)
--   routed 级联：H* x = Htot x ++ negChain (H₃ x)
--     · Htot = H-col + H₁ + H₁∘∂C∘H-col（级联三项式——t/e01/e12 面已闭）
--     · H₃⁻ = negChain ∘ H₃（路由级取负——e20 供肩 T₂ 与残余 T₁ 消差（T₁⊕T₂=T₀）；
--       实测符号定位：H₃ 原供 T₁（T₁⊕T₁=T₂ 不消差）——负形翻供 T₂ ✓）
--   机制：基项 x 的 ∂C x 含 v1/v2 时，H₃(∂C x) 在 e20 格供肩——
--     e01 基项（∂₁ e01 = v1 ⊕ neg v0）⇒ H₃ 供 (e20, ∂M-v₁)——差分消解形。
--   副作用面（二编实测定案）：顶点基项 y 的 ∂C(H₃ y) 落顶点格（v0 破）——
--     单 H 不可全格满足（与三联同根）⇒ **分级 scoped 形**（C₁ 用 H*/C₀ 用 Htot）= routed 正解。
-------------------------------------------------------------------------

-------------------------------------------------------------------------
-- §2 routed 级联件
-------------------------------------------------------------------------

H* : Chain Sx → Chain Sx
H* x = Htot x ++ negChain (H₃ x)

-------------------------------------------------------------------------
-- §3 K₃ e20 差分件（三联证据链指认的真边界——本件主目标）
-------------------------------------------------------------------------

-- e20 肩目标（原残余 LHS=T₁ vs RHS=T₀——H₃(∂C·) 供 T₁ 消差）
check-routed-e20 : lookup (∂C (H* ((e01 , T₁) ∷ [])) ++ H* (∂C ((e01 , T₁) ∷ []))) e20
  ≡ lookup (((e01 , T₁) ∷ []) ++ negChain (π-col ((e01 , T₁) ∷ []))) e20
check-routed-e20 = refl

-- 回归 ①：e01 基项的 e01/e12 肩（级联已闭面——H₃ 不触这两格）
check-routed-e01 : lookup (∂C (H* ((e01 , T₁) ∷ [])) ++ H* (∂C ((e01 , T₁) ∷ []))) e01
  ≡ lookup (((e01 , T₁) ∷ []) ++ negChain (π-col ((e01 , T₁) ∷ []))) e01
check-routed-e01 = refl

check-routed-e01-e12 : lookup (∂C (H* ((e01 , T₁) ∷ [])) ++ H* (∂C ((e01 , T₁) ∷ []))) e12
  ≡ lookup (((e01 , T₁) ∷ []) ++ negChain (π-col ((e01 , T₁) ∷ []))) e12
check-routed-e01-e12 = refl

-- 回归 ②：t 基项（级联修复保持）
check-routed-t : lookup (∂C (H* ((t , T₁) ∷ [])) ++ H* (∂C ((t , T₁) ∷ []))) t
  ≡ lookup (((t , T₁) ∷ []) ++ negChain (π-col ((t , T₁) ∷ []))) t
check-routed-t = refl

-------------------------------------------------------------------------
-- §4 分级回归（二段论定理化——单一线性 H 不可能的 scoped 解）
--   实测二编定案：H* 于顶点基项破 v0 格（∂C(H₃ v1) 出口落顶点）——
--   与三联不可能性同根（单 H 全格满足不可达）。**routed 世界正解 = 分级 scoped 形**：
--     · C₁ 基项（边）用 H*（H₃ 补 e20 肩——§3 全格闭）
--     · C₀ 基项（顶点）用 Htot（级联形——_PM56e §3 顶点回归 ×3 全格绿）
--   分级链同伦 = routed 世界的同伦定义（同伦按基项级别携带路由数据——
--   与 DirectExit 前提范式同构：出口对按路由面供给）。
--   顶点基项以 Htot 的全格绿（_PM56e check-casc-v0/v1/v2 七格 refl）为证，
--   此处不重复件（复用零重证）。
-------------------------------------------------------------------------

-- 顶点基项 scoped 形见证（= _PM56e 级联件的重述引——defeq 同形）
check-scoped-v1-ref : (c : Sx) →
  lookup (∂C (Htot ((v1 , T₁) ∷ [])) ++ Htot (∂C ((v1 , T₁) ∷ []))) c
    ≡ lookup (((v1 , T₁) ∷ []) ++ negChain (π-col ((v1 , T₁) ∷ []))) c
check-scoped-v1-ref = _PM56e.check-casc-v1

-------------------------------------------------------------------------
-- §5 立界（诚实分阶段）
--   (i) e01 基项顶点格/t 格的全格态（H* 不改这几格——原级联态保持；
--       若原级联有残余则为既有立界面，非本件引入）
--   (ii) 一般 X 的 routed 同伦（DirectExit 前提具体化——分级 scoped 形的
--       一般定义 + ∂M/∂₁ˢ 双边界桥全形）
--   (iii) 一般复合公式交换图（Htot∘H₃ 交互项吸收）
--   (iv) 分级 scoped 形 vs 单 H 的关系定理（「scoped 必要性」——三联不可能性
--       + 本件 v0 副作用反核 = 四联证据链）
-------------------------------------------------------------------------
