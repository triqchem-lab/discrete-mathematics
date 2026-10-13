{-# OPTIONS --cubical --rewriting --guardedness #-}

-- | _PPT5
-- 任务书 6.1 PT-5：T⁶/(Z/3Z)⁶ 有限实例化 + 塔终止性判据
-- 数学背景：经典 Postnikov 塔处理无限同伦群（EM 空间逐层逼近）；框架锁定有限群 (Z/3Z)⁶——
--   有限型空间的塔在有限步稳定（终止性）。本件给三件：
--   ① TowerStable 判据（组合形：塔在 h 步后恒稳）+ **1-型终止性定理**（NoTriangle ⟹ h=1 恒稳）
--   ② G729 离散实例（729 点零边图 = T⁶ 点数面的离散形）——**真截断见证**（对角化定理）
--   ③ 分界注记：任务书 6.1 框架关系（有限生成 vs 无限同伦群）的组合对应落定
-- 核心原则：
-- 1. 复用零重证（_PPT2 PostnikovTower/tower-gskel、_PPI4h NoTriangle/ah-diag-gen、_PPI2 π₁ᵈ）
-- 2. 真截断见证（trunc-wit = 对角化定理——非裸 ⊤ 断言，ZeroHomology 教训防线）
-- 3. 诚实标注：G729 是 T⁶ 的**离散形代理**（点数面 729）；T⁶ 步进图面（4320D 步算子）另线
-- 包含：TowerStable/stab-const ｜ tower-1type/stab-1type（1-型终止性定理）｜ stab-gskel
--       ｜ G729/noTriangle729/tower-729/stab-729 ｜ 分界与收口注记

module _PPT5 where

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Fin using (Fin)
open import Data.Empty using (⊥)
open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; _,_)
open import Agda.Builtin.Equality using (_≡_; refl)

open import Sovereign.Synthesis.BarceloAHomotopy using (DiGraph; Walk; AHomotopy; nil)
open import _PPI2 using (π₁ᵈ)
open import _PPT2 using (PostnikovTower; tower-gskel)
open import _PPI4h using (NoTriangle; ah-diag-gen)

--------------------------------------------------------------------------------
-- §1 TowerStable 判据 + 1-型终止性定理
--------------------------------------------------------------------------------

-- 塔在 h 步后恒稳：Xₙ(h+n) ≡ Xₙ(h) 对所有 n
TowerStable : {G : DiGraph} {x : DiGraph.V G} → PostnikovTower G x → Set₁
TowerStable t =
  Σ ℕ (λ h → (n : ℕ) → PostnikovTower.Xₙ t (h + n) ≡ PostnikovTower.Xₙ t h)

-- 打包件（常值于 h 以上 ⟹ 稳定——判据的构造形）
stab-const : {G : DiGraph} {x : DiGraph.V G} (t : PostnikovTower G x) (h : ℕ)
           → ((n : ℕ) → PostnikovTower.Xₙ t (h + n) ≡ PostnikovTower.Xₙ t h)
           → TowerStable t
stab-const t h p = h , p

-- 1-型塔（组合形）：Xₙ = ⊤/π₁ᵈ 两阶；trunc-wit = **对角化定理**（NoTriangle 前提——真内容）
tower-1type : (G : DiGraph) (x : DiGraph.V G) → NoTriangle G → PostnikovTower G x
tower-1type G x nt = record
  { Xₙ        = λ { zero → ⊤ ; (suc _) → π₁ᵈ G x }
  ; stage-map = λ { zero _ → tt ; (suc _) → λ z → z }
  ; trunc₂    = λ _ → ∀ {u v} {w1 w2 : Walk G u v}
                    → AHomotopy G w1 w2 → w1 ≡ w2
  ; trunc-wit = λ _ {u v} {w1 w2} h → ah-diag-gen nt h
  }

-- **1-型终止性定理**：无三角图 ⟹ 塔在 h=1 恒稳（defeq 收口——Xₙ (suc _) 恒 π₁ᵈ）
stab-1type : (G : DiGraph) (x : DiGraph.V G) (nt : NoTriangle G)
           → TowerStable (tower-1type G x nt)
stab-1type G x nt = 1 , λ n → refl

-- 实例①：Gskel two-chain 塔在 h=1 稳定（tower-gskel 自带真截断见证 Ω2-triv-gskel）
stab-gskel : TowerStable tower-gskel
stab-gskel = 1 , λ n → refl

--------------------------------------------------------------------------------
-- §2 G729 离散实例（T⁶ 点数面 729 的离散形代理）
--------------------------------------------------------------------------------

-- 729 点零边图：edge 恒 ⊥
G729 : DiGraph
G729 = record { V = Fin 729 ; edge = λ _ _ → ⊥ }

-- 零边 ⟹ 无三角（任何三边前提含 ⊥——直接取首前提）
noTriangle729 : NoTriangle G729
noTriangle729 x y z e1 e2 e3 = e1

-- 729 点塔 = 1-型塔实例（真截断见证 = 对角化定理）
tower-729 : (x : Fin 729) → PostnikovTower G729 x
tower-729 x = tower-1type G729 x noTriangle729

-- 实例②：729 点塔在 h=1 稳定（stab-1type 直引）
stab-729 : (x : Fin 729) → TowerStable (tower-729 x)
stab-729 x = stab-1type G729 x noTriangle729

--------------------------------------------------------------------------------
-- §3 分界注记 + PT-1..5 收口对账
--------------------------------------------------------------------------------

-- 【分界注记（任务书 6.1 框架关系落定）】
--   经典 Postnikov 塔：无限同伦群（K(πₙ,n) 逐层逼近——EM 空间重机件，未开线）；
--   本框架：有限群 (Z/3Z)⁶ 锁定——有限型空间的 π 群全有限 ⟹ 不变量（kₙ）值域有限
--   ⟹ 塔数据序列在有限数据域中稳定（G729 实例：h=1 恒稳，trunc-wit 为真定理）。
--   任务书「Postnikov 处理无限同伦群 vs 框架锁定有限群」= 本件 TowerStable 的两形：
--   无限形一般不稳（EM 塔逐层非平凡）；有限形恒稳（stab-1type/G729）。

-- 【一般有限复形终止性（立界）】
--   高度 h 的有限单纯复形：Ω^{h+1} 全平凡 ⟹ 塔在 h 稳定——需 PT-2 一般截断迭代形
--   （Ωⁿ 高阶平凡性归纳）。本件已证 1-型面全形（NoTriangle ⟹ h=1）；一般高度版立界。

-- 【PT-1..5 收口对账（docs/plan/postnikov-tower-line.md 对照）】
--   PT-1 基础对账 ✅（清单交付）｜PT-2 塔结构 ✅（tower-gskel 真实例）｜
--   PT-3 同构（在途）｜PT-4 kₙ（在途）｜PT-5 本件 ✅（判据+实例+分界）。
--   T⁶ 格点锚：Synthesis/T6 的 T6Lattice ≃ Fin 729 主定理（只读引用——本件 G729 = 离散形代理，
--   4320D 步进图面另线）。
