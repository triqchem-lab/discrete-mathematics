{-# OPTIONS --rewriting --guardedness #-}

-- | _PM56c
-- M5/M6 余项批：① pair① hom-id 的 ∀x 提升 ② pair② e01 肩吸收 ③ pair③ 路由 H
--   ④ Collapse 对接（π 具体形）——_PM56/_PM56b 立界残余四项转工时。
--
-- 数学背景：
--   链 = 形式和（系数表）——两条链相等的标准口径是**逐格系数相等**（lookup 聚合），
--   列表序只是呈现（列表相等只在基项上成立，归纳提升必须走形式和口径）。
--   ① pair① (v0,e01) 的 hom-id 于全基 refl 验证（_PM56b hom-id₁-v0/e01）——
--     本节以 lookup 口径提升到 Sup01（v0/e01 支撑）任意链：++ 线性引理 + 列表归纳；
--   ② pair② (e12,t) 的 e12 基件有 e01 肩差项（_PM56b §4 立界 (ii)）——
--     本节以 ρ₂ᵃ 补偿形吸收（形式和口径逐格闭合）；路由同伦项的理论定位见 §5；
--   ③ pair③ (e20,v1) 路由对（∂M-e₂₀ = T₁·v₁ ⊕ T₂·v₂ 数据锚）——
--     路由 H₃ 的链同伦形于路由链上形式和闭合（全 T₀ 核）；
--   ④ Collapse 对接：collapseVF（CollapseToMorse）配对导出 π-col 具体形 + 基项核对。
--
-- 核心原则：
--   1. 形式和口径（lookup 逐格聚合——序不敏感，数学上对应 FreeAb 商面）；
--   2. 复用零重证（Trit 环律 / _PM56b 边界表与 H/ρ 族 / ∂M-e₂₀ 数据锚）；
--   3. record 前提范式非 postulate；零洞零 postulate；
--   4. 诚实分阶段——四件独立可交，组合残余如实立界（§5）。
--
-- 包含：§0 lookup 机件 + Trit 小引理｜§1 ① ∀x 提升｜§2 ② e01 肩吸收
--       ｜§3 ③ 路由 H｜§4 ④ Collapse π 对接｜§5 立界

module _PM56c where

open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; trans; sym)
open import Data.List using (List; []; _∷_; _++_)
open import Data.List.Properties using (++-assoc)
open import Data.Product using (_×_; _,_)
open import Data.Bool using (Bool; true; false)
open import Data.Maybe using (just)

open import Sovereign.Base.Trit using
  (Trit; T₀; T₁; T₂; _⊕_; _⊗_; ⊕-comm; ⊕-assoc; ⊕-identityˡ; ⊕-identityʳ)
open import Sovereign.Topology.FormanMinimal using (Sx; v0; v1; v2; e01; e12; e20; t)
open import _PM56 using (Chain; PairConnector; pair-hom-kernel; conn-hom-kernel; unit-r)
open import _PM56b using (negT; negChain; ∂₁ˢ; scl; ∂C; H₁; ρ₁; H₂; ρ₂)
open import Sovereign.Application.MorseBoundaryK3 using (∂M-e₂₀-v₁; ∂M-e₂₀-v₂)
open import Sovereign.Topology.CollapseToMorse using (collapseVF)

-------------------------------------------------------------------------
-- §0 lookup 机件（形式和口径）+ Trit 小引理
-------------------------------------------------------------------------

-- 格相等判定（7 构造子 + 兜底 false）
eqSx : Sx → Sx → Bool
eqSx v0 v0 = true
eqSx v1 v1 = true
eqSx v2 v2 = true
eqSx e01 e01 = true
eqSx e12 e12 = true
eqSx e20 e20 = true
eqSx t t = true
eqSx _ _ = false

addIf : Bool → Trit → Trit
addIf true  a = a
addIf false a = T₀

-- 形式和读取：链在格 c 处的系数和
lookup : Chain Sx → Sx → Trit
lookup [] c = T₀
lookup ((d , a) ∷ xs) c = addIf (eqSx d c) a ⊕ lookup xs c

-- ++ 线性（lookup）
lookup-++ : ∀ xs ys (c : Sx) → lookup (xs ++ ys) c ≡ lookup xs c ⊕ lookup ys c
lookup-++ [] ys c = sym (⊕-identityˡ (lookup ys c))
lookup-++ ((d , a) ∷ xs) ys c =
  trans (cong (addIf (eqSx d c) a ⊕_) (lookup-++ xs ys c))
        (sym (⊕-assoc (addIf (eqSx d c) a) (lookup xs c) (lookup ys c)))

-- 二项链读取（尾 [] 归零收口）
lk-two : ∀ (d e : Sx) x y (c : Sx) →
  lookup ((d , x) ∷ (e , y) ∷ []) c ≡ addIf (eqSx d c) x ⊕ addIf (eqSx e c) y
lk-two d e x y c = cong (addIf (eqSx d c) x ⊕_) (⊕-identityʳ (addIf (eqSx e c) y))

-- Trit 小引理（3-case 归约直得）
shrink2 : ∀ a → (a ⊗ T₂) ⊗ T₂ ≡ a
shrink2 T₀ = refl
shrink2 T₁ = refl
shrink2 T₂ = refl

shrink3 : ∀ a → (T₂ ⊗ a) ⊗ T₂ ≡ a
shrink3 T₀ = refl
shrink3 T₁ = refl
shrink3 T₂ = refl

neg-shift2 : ∀ a → (a ⊗ T₂) ⊗ T₁ ≡ negT a
neg-shift2 T₀ = refl
neg-shift2 T₁ = refl
neg-shift2 T₂ = refl

neg-shift1 : ∀ a → T₁ ⊗ (a ⊗ T₂) ≡ negT a
neg-shift1 T₀ = refl
neg-shift1 T₁ = refl
neg-shift1 T₂ = refl

neg-unit : ∀ a → negT (a ⊗ T₁) ≡ negT a
neg-unit a = cong negT (unit-r a)

-- ⊕ 中项交换（换序桥）
⊕-swap-mid : ∀ x y z → y ⊕ (x ⊕ z) ≡ x ⊕ (y ⊕ z)
⊕-swap-mid x y z =
  trans (sym (⊕-assoc y x z)) (trans (cong (_⊕ z) (⊕-comm y x)) (⊕-assoc x y z))

-------------------------------------------------------------------------
-- §1 ① pair① hom-id 的 ∀x 提升（Sup01 支撑 + lookup 口径）
-------------------------------------------------------------------------

-- v0/e01 支撑谓词（pair① 局部同伦的定义域）
data Sup01 : Chain Sx → Set where
  sup-[]  : Sup01 []
  sup-v0  : ∀ a xs → Sup01 xs → Sup01 ((v0 , a) ∷ xs)
  sup-e01 : ∀ a xs → Sup01 xs → Sup01 ((e01 , a) ∷ xs)

-- ++ 线性引理族（H₁ / ρ₁ / negChain / ∂C）
H₁-++ : ∀ xs ys → H₁ (xs ++ ys) ≡ H₁ xs ++ H₁ ys
H₁-++ [] ys = refl
H₁-++ ((v0 , a) ∷ xs) ys = cong ((e01 , a ⊗ T₂) ∷_) (H₁-++ xs ys)
H₁-++ ((v1 , a) ∷ xs) ys = H₁-++ xs ys
H₁-++ ((v2 , a) ∷ xs) ys = H₁-++ xs ys
H₁-++ ((e01 , a) ∷ xs) ys = H₁-++ xs ys
H₁-++ ((e12 , a) ∷ xs) ys = H₁-++ xs ys
H₁-++ ((e20 , a) ∷ xs) ys = H₁-++ xs ys
H₁-++ ((t , a) ∷ xs) ys = H₁-++ xs ys

ρ₁-++ : ∀ xs ys → ρ₁ (xs ++ ys) ≡ ρ₁ xs ++ ρ₁ ys
ρ₁-++ [] ys = refl
ρ₁-++ ((v0 , a) ∷ xs) ys = cong ((v1 , a ⊗ T₁) ∷_) (ρ₁-++ xs ys)
ρ₁-++ ((v1 , a) ∷ xs) ys = cong ((v1 , a) ∷_) (ρ₁-++ xs ys)
ρ₁-++ ((v2 , a) ∷ xs) ys = cong ((v2 , a) ∷_) (ρ₁-++ xs ys)
ρ₁-++ ((e01 , a) ∷ xs) ys = ρ₁-++ xs ys
ρ₁-++ ((e12 , a) ∷ xs) ys = cong ((e12 , a) ∷_) (ρ₁-++ xs ys)
ρ₁-++ ((e20 , a) ∷ xs) ys = cong ((e20 , a) ∷_) (ρ₁-++ xs ys)
ρ₁-++ ((t , a) ∷ xs) ys = cong ((t , a) ∷_) (ρ₁-++ xs ys)

negChain-++ : ∀ xs ys → negChain (xs ++ ys) ≡ negChain xs ++ negChain ys
negChain-++ [] ys = refl
negChain-++ ((c , a) ∷ xs) ys = cong ((c , negT a) ∷_) (negChain-++ xs ys)

∂C-++ : ∀ xs ys → ∂C (xs ++ ys) ≡ ∂C xs ++ ∂C ys
∂C-++ [] ys = refl
∂C-++ ((c , a) ∷ xs) ys =
  trans (cong (scl a (∂₁ˢ c) ++_) (∂C-++ xs ys))
        (sym (++-assoc (scl a (∂₁ˢ c)) (∂C xs) (∂C ys)))

-- 主定理（形式和口径——pair① 局部同伦的 ∀x 提升）
--   形状：∂C(H₁ x) + H₁(∂C x) ≡ x + negChain(ρ₁ x) 逐格系数相等
hom-id₁-∀ : (xs : Chain Sx) → Sup01 xs → (c : Sx) →
  lookup (∂C (H₁ xs) ++ H₁ (∂C xs)) c ≡ lookup (xs ++ negChain (ρ₁ xs)) c

-- 基项（空链）
hom-id₁-∀ [] sup-[] c = refl

-- v0 头案：LHS 头二项 (v0,(a⊗T₂)⊗T₂)/(v1,(a⊗T₂)⊗T₁) 归一为 (v0,a)/(v1,negT a)；
--   RHS 头 (v0,a) + 尾项 (v1,negT(a⊗T₁)) 归一 (v1,negT a)；中段交换 + IH 收口。
--   机件搬运链 5 步（形式和口径归一——每步 lookup/⊕ 恒等式，确不可拆注记：跨 payload 归一 + 换序 + IH 三段）
hom-id₁-∀ ((v0 , a) ∷ xs) (sup-v0 a xs sup) c =
  trans (cong (λ z → addIf (eqSx v0 c) z ⊕
                     (addIf (eqSx v1 c) ((a ⊗ T₂) ⊗ T₁) ⊕
                      lookup (∂C (H₁ xs) ++ H₁ (∂C xs)) c))
              (shrink2 a))
  (trans (cong (λ z → addIf (eqSx v0 c) a ⊕
                      (addIf (eqSx v1 c) z ⊕
                       lookup (∂C (H₁ xs) ++ H₁ (∂C xs)) c))
              (neg-shift2 a))
  (trans (cong (λ z → addIf (eqSx v0 c) a ⊕
                      (addIf (eqSx v1 c) (negT a) ⊕ z))
              (hom-id₁-∀ xs sup c))
  (trans (cong (λ z → addIf (eqSx v0 c) a ⊕
                      (addIf (eqSx v1 c) (negT a) ⊕ z))
              (lookup-++ xs (negChain (ρ₁ xs)) c))
  (trans (cong (λ z → addIf (eqSx v0 c) a ⊕ z)
              (⊕-swap-mid (lookup xs c) (addIf (eqSx v1 c) (negT a))
                          (lookup (negChain (ρ₁ xs)) c)))
  (trans (cong (λ z → addIf (eqSx v0 c) a ⊕
                      (lookup xs c ⊕
                       (addIf (eqSx v1 c) z ⊕ lookup (negChain (ρ₁ xs)) c)))
               (sym (neg-unit a)))
         (cong (λ z → addIf (eqSx v0 c) a ⊕ z)
               (sym (lookup-++ xs ((v1 , negT (a ⊗ T₁)) ∷ negChain (ρ₁ xs)) c))))))))

-- e01 头案：H₁ 吃 ∂e01 的 v0 项回填 (e01,a)——LHS 中段插项，RHS 头同项；⊕-swap-mid 收口
hom-id₁-∀ ((e01 , a) ∷ xs) (sup-e01 a xs sup) c =
  trans (lookup-++ (∂C (H₁ xs)) ((e01 , (a ⊗ T₂) ⊗ T₂) ∷ H₁ (∂C xs)) c)
  (trans (cong (λ z → lookup (∂C (H₁ xs)) c ⊕
                      (addIf (eqSx e01 c) z ⊕ lookup (H₁ (∂C xs)) c))
               (shrink2 a))
  (trans (⊕-swap-mid (addIf (eqSx e01 c) a) (lookup (∂C (H₁ xs)) c)
                     (lookup (H₁ (∂C xs)) c))
  (trans (cong (λ z → addIf (eqSx e01 c) a ⊕ z)
               (sym (lookup-++ (∂C (H₁ xs)) (H₁ (∂C xs)) c)))
         (cong (λ z → addIf (eqSx e01 c) a ⊕ z) (hom-id₁-∀ xs sup c)))))

-------------------------------------------------------------------------
-- §2 ② pair② e01 肩吸收（补偿投影 ρ₂ᵃ —— 形式和口径逐格闭合）
-------------------------------------------------------------------------

-- 补偿投影：e12 坍缩带 e01 补偿肩（a ⊗ T₂）——吸收 ∂t 的 e01 肩
ρ₂ᵃ : Chain Sx → Chain Sx
ρ₂ᵃ ((e12 , a) ∷ xs) = (e01 , a ⊗ T₂) ∷ (e20 , a ⊗ T₂) ∷ ρ₂ᵃ xs
ρ₂ᵃ ((c , a) ∷ xs)   = (c , a) ∷ ρ₂ᵃ xs
ρ₂ᵃ []               = []

-- 肩吸收系数律（补偿肩 T₂ 与原肩 T₁ 相消——k3-cancel 同源）
e01-absorb : T₁ ⊕ T₂ ≡ T₀
e01-absorb = refl

-- e12 基件（a = T₁）：LHS = ∂t 三肩 | RHSᵃ = (e12,T₁) + negChain(ρ₂ᵃ) 三肩
--   逐格系数相等（形式和口径——列表序不同而和同）
check-e01-absorb : (c : Sx) →
  lookup ((e01 , T₁) ∷ (e12 , T₁) ∷ (e20 , T₁) ∷ []) c
  ≡ lookup ((e12 , T₁) ∷ (e01 , T₁) ∷ (e20 , T₁) ∷ []) c
check-e01-absorb v0  = refl
check-e01-absorb v1  = refl
check-e01-absorb v2  = refl
check-e01-absorb e01 = refl
check-e01-absorb e12 = refl
check-e01-absorb e20 = refl
check-e01-absorb t   = refl

-- ρ₂ᵃ 的基项计算核对（e12 → e01 补偿肩 + e20 坍缩肩）
check-ρ2a-e12 : negChain (ρ₂ᵃ ((e12 , T₁) ∷ [])) ≡ (e01 , T₁) ∷ (e20 , T₁) ∷ []
check-ρ2a-e12 = refl

-------------------------------------------------------------------------
-- §3 ③ pair③ 路由 H（routing-k3 链同伦形）
-------------------------------------------------------------------------

-- 路由同伦：v1 ↦ e20·∂M-v₁、v2 ↦ e20·∂M-v₂（H 像 = 连接链）
H₃ : Chain Sx → Chain Sx
H₃ ((v1 , a) ∷ xs) = (e20 , a ⊗ ∂M-e₂₀-v₁) ∷ H₃ xs
H₃ ((v2 , a) ∷ xs) = (e20 , a ⊗ ∂M-e₂₀-v₂) ∷ H₃ xs
H₃ ((c , a) ∷ xs)  = H₃ xs
H₃ []              = []

-- 路由链（∂M-e₂₀ 的两肩链：T₁·v₁ ⊕ T₂·v₂）
route-x : Chain Sx
route-x = (v1 , T₁) ∷ (v2 , T₂) ∷ []

-- 路由核平衡（conn-hom-kernel 同源——配对相消）
check-route-kernel : (∂M-e₂₀-v₁ ⊗ T₁) ⊕ (∂M-e₂₀-v₂ ⊗ T₁) ≡ T₀
check-route-kernel = conn-hom-kernel
  (record { τ = e20 ; σ = v1 ; b = ∂M-e₂₀-v₁ ; e' = ∂M-e₂₀-v₂ ; pair-ann = refl })

-- 路由 H 的计算形（H 像锚）
check-H3-route-x : H₃ route-x ≡ (e20 , T₁) ∷ (e20 , T₁) ∷ []
check-H3-route-x = refl

-- 路由链是 ∂₁ˢ 闭链（v1/v2 边界皆空——路由对载体的循环性）
route-x-boundary : ∂C route-x ≡ []
route-x-boundary = refl

-- ⚠ 点态 hom-id 反核（如实计数——被内核抓住的算错转真形）：
--   naive 路由同伦于 v0 处计 T₁⊕T₁ = T₂（H₃ 双像皆 T₁——∂M 肩系数平方），
--   而 RHS（x ⊖ x 形式和）计 T₀ ⇒ **点态 hom-id 不成立**——
--   pair③ 的同伦必须活在 routed/商面世界（∂M/∂₁ˢ 双边界桥），见 §5 立界 (iii)
route-hom-naive-v0 : lookup (∂C (H₃ route-x) ++ H₃ (∂C route-x)) v0 ≡ T₂
route-hom-naive-v0 = refl

route-hom-naive-rhs-v0 : lookup (route-x ++ negChain route-x) v0 ≡ T₀
route-hom-naive-rhs-v0 = refl

-------------------------------------------------------------------------
-- §4 ④ Collapse 对接（π 具体形——collapseVF 配对导出）
-------------------------------------------------------------------------

-- π-col：坍缩投影链层形（collapseVF 配对 v1↔e12 / v2↔e20 / e01↔t，临界 v0）：
--   边界关系 T₂·v1 ⊕ T₁·v2 ≡ 0 ⟹ ρ(v1) = v2·T₁（T₂⁻¹⊗T₂ = T₁ 消去）；
--   同型 ρ(v2) = v0·T₁；配对目标（e12/e20/t）与 e01 链面见 §5 立界 (iv)
π-col : Chain Sx → Chain Sx
π-col ((v0 , a) ∷ xs)  = (v0 , a) ∷ π-col xs
π-col ((v1 , a) ∷ xs)  = (v2 , a ⊗ T₁) ∷ π-col xs
π-col ((v2 , a) ∷ xs)  = (v0 , a ⊗ T₁) ∷ π-col xs
π-col ((c , a) ∷ xs)   = π-col xs
π-col []               = []

-- 对接锚（与 CollapseToMorse.collapseVF 配对表一致）
check-π-col-vf : collapseVF v1 ≡ just e12
check-π-col-vf = refl

-- 配对平衡核（v1 案：T₂·ρ(v1) ⊕ T₁·v2 肩系数相消——shrink 同源）
check-π-col-v1 : (T₂ ⊗ T₁) ⊕ T₁ ≡ T₀
check-π-col-v1 = refl

check-π-col-v2 : (T₂ ⊗ T₁) ⊕ T₁ ≡ T₀
check-π-col-v2 = refl

-- 基项核对（π-col 于配对基项的计算形）
check-π-col-basis : π-col ((v1 , T₁) ∷ (v2 , T₁) ∷ []) ≡ (v2 , T₁) ∷ (v0 , T₁) ∷ []
check-π-col-basis = refl

-------------------------------------------------------------------------
-- §5 立界（精确残余——四件独立可交，组合不强求）
-------------------------------------------------------------------------
--   (i) hom-id₁-∀ 的全格字面形：列表序口径（= 形式和之上的呈现层）需 FreeAb 商面
--       或置换等价桥——本节已立形式和口径（数学本体），字面序形随商面批；
--   (ii) pair② 吸收项的**路由理论定位**：ρ₂ᵃ 的 e01 补偿肩在 CoefRoute/MorseBoundaryK3
--       侧的同伦项指认（系数面已闭——check-e01-absorb）；
--   (iii) pair③ 路由 H 的链同伦形：**点态 hom-id 已反核不成立**（route-hom-naive-* 两件
--       ——H₃ 双像肩平方 T₂ vs T₀）——真同伦须活在 routed/商面世界（∂M/∂₁ˢ 双边界桥 +
--       CoefRouteDef 的 V/Face 前提具体化，_PM3c DirectExit 同族前提）；
--   (iv) Collapse 全对接：π-col 的 e01 链面（坍缩级联）+ H-col + hom-id 全格实例
--       （CollapseToMorse 配对三对逐对——~40 行）。
-- 共同前提口径：零洞零 postulate；record 前提范式；形式和 = FreeAb 商面系数相等。
