{-# OPTIONS --rewriting --guardedness #-}
-- ══════════════════════════════════════════════════════════════════════════════
-- | _PPI4h
-- Gskel 完全推广（一般图）研究 · Phase 2 最小件：
--   **AStep 空判据（三角形无关 ⟺ AStep 全空）** + **AHomotopy=对角一般形**
--
-- 核心原则：
--   1. 判据两方向全证：三角形无关 ⟹ AStep 强空（任意两 walk）；
--      AStep 项 ⟹ 三角形见证（slide/expand 直读三边）；
--   2. 一般图 G 形（DiGraph 参数化）——**非 two-chain 特化**；
--      two-chain 应用 = 三角形无关 ⟺ P 无 3 元链（ht(P) ≤ 2）的推论；
--   3. gen 案不可达 ⟹ AHomotopy 退化为对角（最小等价闭包）——
--      AStep-sk-empty/ah-diag-sk（_PPI4c，two-chain）的一般化。
--
-- 包含：NoTriangle（三角形无关）｜AStep-empty←（方向一）｜Triangle/△-from-AStep（方向二）
--       ｜symE/transE（Builtin ≡ 辅件）｜ah-diag-gen（对角化）
-- ══════════════════════════════════════════════════════════════════════════════
module _PPI4h where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (Σ; _×_; _,_)
open import Agda.Builtin.Equality using () renaming (refl to reflᴱ; _≡_ to _≡ᴱ_)
open import Sovereign.Synthesis.BarceloAHomotopy
  using (DiGraph; Walk; AStep; AHomotopy; slide; expand; refl'; symm; trans'; gen)

private
  module DG = DiGraph

--------------------------------------------------------------------------------
-- §1 三角形无关谓词（一般图 G 的局部条件——含退化形亦禁，判据取严格形）
--------------------------------------------------------------------------------

NoTriangle : (G : DiGraph) → Set
NoTriangle G = ∀ x y z → DG.edge G x y → DG.edge G y z → DG.edge G x z → ⊥

--------------------------------------------------------------------------------
-- §2 判据方向一：三角形无关 ⟹ AStep 全空（强空——任意 u v w1 w2）
--------------------------------------------------------------------------------

-- 证明：slide/expand 两构造子各携带 (x→y)(y→z)(x→z) 三边 ⇒ NoTriangle 矛盾。
-- （与 _PPI4c 的 AStep-sk-empty 同构——但本件不依赖 two-chain/Fin 2 结构；
--   two-chain 侧的 tri-dist-impossible（Fin 2 无三元相异组）在此被
--   「无三角」的图论条件替换。）
AStep-empty← : {G : DiGraph} → NoTriangle G
  → {u v : DG.V G} {w1 w2 : Walk G u v} → AStep G w1 w2 → ⊥
AStep-empty← nt (slide {x = x} {y} {z} _ _ e1 e2 e3) = nt x y z e1 e2 e3
AStep-empty← nt (expand {x = x} {y} {z} _ _ e1 e2 e3) = nt x y z e1 e2 e3

--------------------------------------------------------------------------------
-- §3 判据方向二：AStep 项 ⟹ 三角形见证（构造子直读——逆否即方向一的紧化）
--------------------------------------------------------------------------------

-- 三角形见证：三顶点 + 三边打包（Σ 形）
Triangle : (G : DiGraph) → Set
Triangle G = Σ (DG.V G) λ x → Σ (DG.V G) λ y → Σ (DG.V G) λ z
           → (DG.edge G x y × DG.edge G y z × DG.edge G x z)

-- slide 构造子即携带三边——见证由 AStep 项直读
△-from-AStep : {G : DiGraph} {u v : DG.V G} {w1 w2 : Walk G u v}
  → (s : AStep G w1 w2) → Triangle G
△-from-AStep (slide {x = x} {y} {z} _ _ e1 e2 e3) = x , y , z , (e1 , e2 , e3)
△-from-AStep (expand {x = x} {y} {z} _ _ e1 e2 e3) = x , y , z , (e1 , e2 , e3)

-- 合取判据（等价形注记）：AStep 非空 ⟺ 三角形存在
--   （→ 由 △-from-AStep；← 由 slide 构造子对任意三边/任意 p b 直接入项）

--------------------------------------------------------------------------------
-- §4 AHomotopy = 对角（gen 案不可达的推论——最小等价闭包）
--------------------------------------------------------------------------------

-- Builtin ≡ 辅件（顶层命名件——免匹配纪律）
symE : {A : Set} {x y : A} → x ≡ᴱ y → y ≡ᴱ x
symE reflᴱ = reflᴱ

transE : {A : Set} {x y z : A} → x ≡ᴱ y → y ≡ᴱ z → x ≡ᴱ z
transE reflᴱ q = q

-- 对角化一般形：NoTriangle G ⟹ AHomotopy G w w' ⟹ w ≡ᴱ w'
-- （归约：refl'/symm/trans' 三案为最小等价闭包的构造；gen 案被 §2 消解）
ah-diag-gen : {G : DiGraph} → NoTriangle G
  → {u v : DG.V G} {w w' : Walk G u v} → AHomotopy G w w' → w ≡ᴱ w'
ah-diag-gen nt (refl' _) = reflᴱ
ah-diag-gen nt (symm h) = symE (ah-diag-gen nt h)
ah-diag-gen nt (trans' h1 h2) = transE (ah-diag-gen nt h1) (ah-diag-gen nt h2)
ah-diag-gen nt (gen s) = ⊥-elim (AStep-empty← nt s)
