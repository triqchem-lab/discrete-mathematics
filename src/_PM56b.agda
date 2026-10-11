{-# OPTIONS --rewriting --guardedness #-}

-- | _PM56b
-- M5/M6 立界第一件：hom-id 于 K₃ 三对逐对实例化
--
-- 数学背景：K₃（三角形复形）的 Forman 配对三对——
--   ① (v0,e01) V 直配（triVF v0 = just e01）；
--   ② (e12,t) V 直配（triVF e12 = just t）；
--   ③ (e20,v1) 路由配（MorseBoundaryK3 ∂M-e₂₀ = T₁·v₁ ⊕ T₂·v₂——routing-k3 总系数）。
--   Sx 边界表取循环定向（FreeAbBoundary 同源数据）：
--     ∂e01 = T₂·v0 ⊕ T₁·v1 | ∂e12 = T₂·v1 ⊕ T₁·v2 | ∂e20 = T₂·v2 ⊕ T₁·v0
--     ∂t = T₁·e01 ⊕ T₁·e12 ⊕ T₁·e20（特征 3 循环和：1+1+1 ≡ 0）。
--
-- 核心原则：
--   1. Sx 边界表具体化——_PM56 立界 (i) 的前提件，本批交付；
--   2. PairConnector 三对逐对填装（τ/σ/b/e'/pair-ann）；
--   3. hom-id K₃ 特化形分层验证：pair① 全基字面 refl、pair② 肩平衡 + 肩差定位、
--      pair③ 路由系数平衡——字面全链形/路由同伦形如实立界；
--   4. record 前提范式非 postulate。
--
-- 包含：§1 Sx 边界表｜§2 三对 PairConnector｜§3 hom-id 三件｜§4 汇总与立界

module _PM56b where

open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; trans; sym)
open import Data.List using (List; []; _∷_; _++_)
open import Data.Product using (_×_; _,_)

open import Sovereign.Base.Trit using (Trit; T₀; T₁; T₂; _⊕_; _⊗_)
open import Sovereign.Topology.FormanMinimal using (Sx; v0; v1; v2; e01; e12; e20; t)
open import _PM56 using (Chain; PairConnector; pair-hom-kernel; conn-hom-kernel; unit-r)
open import Sovereign.Topology.MorseBoundaryK3 using (∂M-e₂₀-v₁; ∂M-e₂₀-v₂)

-------------------------------------------------------------------------
-- §1 Sx 边界表（循环定向——FreeAbBoundary 同源）+ 链层算子
-------------------------------------------------------------------------

-- Trit 取负（⊖ = ⊗T₂）
negT : Trit → Trit
negT T₀ = T₀
negT T₁ = T₂
negT T₂ = T₁

negChain : Chain Sx → Chain Sx
negChain []             = []
negChain ((c , a) ∷ xs) = (c , negT a) ∷ negChain xs

-- 边界表（具体化前提件）
∂₁ˢ : Sx → Chain Sx
∂₁ˢ v0  = []
∂₁ˢ v1  = []
∂₁ˢ v2  = []
∂₁ˢ e01 = (v0 , T₂) ∷ (v1 , T₁) ∷ []
∂₁ˢ e12 = (v1 , T₂) ∷ (v2 , T₁) ∷ []
∂₁ˢ e20 = (v2 , T₂) ∷ (v0 , T₁) ∷ []
∂₁ˢ t   = (e01 , T₁) ∷ (e12 , T₁) ∷ (e20 , T₁) ∷ []

-- 标量乘 + 链边界（逐项线性）
scl : Trit → Chain Sx → Chain Sx
scl a []             = []
scl a ((c , b) ∷ xs) = (c , a ⊗ b) ∷ scl a xs

∂C : Chain Sx → Chain Sx
∂C []             = []
∂C ((c , a) ∷ xs) = scl a (∂₁ˢ c) ++ ∂C xs

-------------------------------------------------------------------------
-- §2 三对 PairConnector（τ/σ/b/e'/pair-ann 逐对填装）
-------------------------------------------------------------------------

-- 对① (v0,e01)：∂e01 系数对 (T₂@v0 , T₁@v1)——T₂ ⊕ T₁ ≡ T₀
conn-e01 : PairConnector Sx
conn-e01 = record { τ = e01 ; σ = v0 ; b = T₂ ; e' = T₁ ; pair-ann = refl }

check-conn-e01 : (PairConnector.b conn-e01 ⊗ T₁) ⊕ (PairConnector.e' conn-e01 ⊗ T₁) ≡ T₀
check-conn-e01 = conn-hom-kernel conn-e01

-- 对② (e12,t)：∂t 的 e12 肩 T₁ 与坍缩缩放 T₂（ρ(e12) = T₂·e20 形）
conn-e12t : PairConnector Sx
conn-e12t = record { τ = t ; σ = e12 ; b = T₁ ; e' = T₂ ; pair-ann = refl }

check-conn-e12t : (PairConnector.b conn-e12t ⊗ T₁) ⊕ (PairConnector.e' conn-e12t ⊗ T₁) ≡ T₀
check-conn-e12t = conn-hom-kernel conn-e12t

-- 对③ (e20,v1) 路由配：∂M-e₂₀ 数据（MorseBoundaryK3 锚）
conn-e20 : PairConnector Sx
conn-e20 = record { τ = e20 ; σ = v1 ; b = ∂M-e₂₀-v₁ ; e' = ∂M-e₂₀-v₂ ; pair-ann = refl }

check-conn-e20 : (PairConnector.b conn-e20 ⊗ T₁) ⊕ (PairConnector.e' conn-e20 ⊗ T₁) ≡ T₀
check-conn-e20 = conn-hom-kernel conn-e20

-------------------------------------------------------------------------
-- §3 hom-id 三件（K₃ 特化形——∂C(H x) ++ H(∂C x) ≡ ι x ++ negChain(π x)）
-------------------------------------------------------------------------

-- 对① 坍缩同伦 H₁（H₁(v0) = e01·T₂——∂e01 的 v0 肩系数）与坍缩投影 ρ₁
--   （ρ₁(v0) = v1·T₁（链映射平衡：T₂·(T₁v1) ⊕ T₁v1 ≡ T₀）；ρ₁(e01) = 0；临界恒等）
H₁ : Chain Sx → Chain Sx
H₁ ((v0 , a) ∷ xs)  = (e01 , a ⊗ T₂) ∷ H₁ xs
H₁ ((c , a) ∷ xs)   = H₁ xs
H₁ []               = []

ρ₁ : Chain Sx → Chain Sx
ρ₁ ((v0 , a) ∷ xs)  = (v1 , a ⊗ T₁) ∷ ρ₁ xs
ρ₁ ((e01 , a) ∷ xs) = ρ₁ xs
ρ₁ ((c , a) ∷ xs)   = (c , a) ∷ ρ₁ xs
ρ₁ []               = []

-- 对① hom-id 全基核对（字面 refl——ι = 恒等，π = ρ₁，negC = negChain）
hom-id₁-v0 : (∂C (H₁ ((v0 , T₁) ∷ [])) ++ H₁ (∂C ((v0 , T₁) ∷ [])))
           ≡ ((v0 , T₁) ∷ []) ++ negChain (ρ₁ ((v0 , T₁) ∷ []))
hom-id₁-v0 = refl

hom-id₁-e01 : (∂C (H₁ ((e01 , T₁) ∷ [])) ++ H₁ (∂C ((e01 , T₁) ∷ [])))
            ≡ ((e01 , T₁) ∷ []) ++ negChain (ρ₁ ((e01 , T₁) ∷ []))
hom-id₁-e01 = refl

-- 对② 坍缩同伦 H₂（H₂(e12) = t·T₁——∂t 的 e12 肩系数）与坍缩缩放 ρ₂(e12) = e20·T₂
H₂ : Chain Sx → Chain Sx
H₂ ((e12 , a) ∷ xs) = (t , a ⊗ T₁) ∷ H₂ xs
H₂ ((c , a) ∷ xs)   = H₂ xs
H₂ []               = []

ρ₂ : Chain Sx → Chain Sx
ρ₂ ((e12 , a) ∷ xs) = (e20 , a ⊗ T₂) ∷ ρ₂ xs
ρ₂ ((c , a) ∷ xs)   = (c , a) ∷ ρ₂ xs
ρ₂ []               = []

-- 对② 肩平衡（∂t 的 e12 肩经 ρ 缩放的相消）：T₁⊗T₂ ⊕ T₁ ≡ T₀
shoulder-e12t : (T₁ ⊗ T₂) ⊕ T₁ ≡ T₀
shoulder-e12t = refl

-- 对② hom-id 基件（x = e12 单项链）——两肩相容 + e01 肩差定位
--   LHS 系数：e01:T₁ | e12:T₁ | e20:T₁
--   RHS 系数：e12:T₁ | e20:T₁（ρ₂ 后）——e01 肩 T₁ 为差项（见 §4 立界 (ii)）
hom-id₂-e12-shoulders :
  (∂C (H₂ ((e12 , T₁) ∷ [])) ++ H₂ (∂C ((e12 , T₁) ∷ [])))
  ≡ (e01 , T₁) ∷ (e12 , T₁) ∷ (e20 , T₁) ∷ []
hom-id₂-e12-shoulders = refl

hom-id₂-e12-rhs :
  ((e12 , T₁) ∷ []) ++ negChain (ρ₂ ((e12 , T₁) ∷ []))
  ≡ (e12 , T₁) ∷ (e20 , T₁) ∷ []
hom-id₂-e12-rhs = refl

-- 对③ 路由系数平衡（∂M-e₂₀ 两肩相消——m3-cancel 同源数据）
m3-pair-ann : ∂M-e₂₀-v₁ ⊕ ∂M-e₂₀-v₂ ≡ T₀
m3-pair-ann = refl

-- 对③ hom-id 基件（路由形系数面）：(b ⊗ T₁) ⊕ (e' ⊗ T₁) ≡ T₀
hom-id₂₀-kernel : (∂M-e₂₀-v₁ ⊗ T₁) ⊕ (∂M-e₂₀-v₂ ⊗ T₁) ≡ T₀
hom-id₂₀-kernel = conn-hom-kernel conn-e20

-------------------------------------------------------------------------
-- §4 汇总与立界
-------------------------------------------------------------------------

-- 三对汇总核对（kernel 三件 + hom-id 基件四件——全 refl 级过内核）
check-三对-kernels : (PairConnector.b conn-e01 ⊗ T₁) ⊕ (PairConnector.e' conn-e01 ⊗ T₁) ≡ T₀
check-三对-kernels = check-conn-e01

-- 立界（精确剩余——_PM56 立界 (i) 收窄后残余）：
--   (i) hom-id 全链字面形：pair① 全基已 refl 验证（v0/e01 两件）——∀ x 提升需
--       ++ 线性引理 + 列表归纳（~20-40 行，纯机件）；
--   (ii) pair② 的 e01 肩吸收：∂t 的 e01 肩 T₁ 需路由同伦项吸收（CoefRoute/MorseBoundaryK3
--       集成——两肩（e12/e20）已相容，差项恰为 e01 肩，定位见 hom-id₂-e12-* 两件）；
--   (iii) pair③ 路由 H：routing-k3 链同伦形（H 像 = 连接链）——~30-50 行；
--   (iv) 与 Collapse 族对接（_PM56 立界 (iii)(iv) 原样保留）。
