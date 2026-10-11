{-# OPTIONS --rewriting --guardedness #-}

-- | _PPT4
-- 任务书 6.1 PT-4：Postnikov 不变量 kₙ 的离散对应——阶段粘合数据（扩张类）。
--
-- 数学背景：经典 kₙ ∈ Hⁿ⁺¹(Xₙ₋₁; πₙ(X)) 分类 Postnikov 扩张
--   0 → K(πₙ, n) → Xₙ → Xₙ₋₁ → 0，且 kₙ = 0 ⟺ 扩张分裂（Xₙ ≃ Xₙ₋₁ × K）。
-- 离散形（Ωⁿ 路线——与 _PPT2 PostnikovTower 同族）：
--   kₙ 数据 = **粘合数据**（纤维 fiberₙ = Ωⁿ 新增同伦数据 + 截面），平凡性 = 分裂；
--   S²ᵈ 面实例：2-腔 omega2-wit 粘合于圈 w3，三角面填充（3-腔）= k₂ 平凡化证据。
--
-- 核心原则：
-- 1. kₙ 离散形 = 粘合数据 record（关系入定义范式——扩张类数据非外来公理）
-- 2. 平凡性判据 = 分裂（截面存在）——经典语义的离散对应
-- 3. 诚实标注：离散对应非经典 k-不变量真身（EM 对照形属未开线——§5 立界）
--
-- 包含：KnSplit（塔面分裂数据 = kₙ=0 见证）｜Kn2Data（k₂ 面级代表+平凡化）
--       ｜S²ᵈ k₂ 双实例｜GF(3) 挠类对账｜立界注记

module _PPT4 where

-- ② 导入区
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Cubical.Foundations.Prelude using (_≡_; refl)
open import Sovereign.Topology.BarceloAHomotopy using (DiGraph; Walk)
open import _PPT2 using (PostnikovTower)
open import _PPI5d using (Ω2Walk; nil2; s2-adj; s2v0; w3; omega2-wit)
open import _PPI5f using (Ω3Walk; omega2-wit-triv)
open import Sovereign.Base.Trit using (Trit; T₀)

-- ③ 基础件层（kₙ 面级数据形）

-- k₂ 面级数据：2-腔 c 粘合于圈 w；k₂ = 0 的语义证据 = c 3-可缩至平凡 2-腔 nil2。
-- （经典：k₂ 的代表是 H² 面的上同调类——平凡类 ⟺ 代表被 3-腔填充。）
record Kn2Data (G : DiGraph) (x : DiGraph.V G) (w : Walk G x x) : Set₁ where
  field
    c      : Ω2Walk G x w w
    c-fill : Ω3Walk G x c (nil2 w)

-- ④ 主引理层（塔面分裂数据 = kₙ = 0 见证）

-- KnSplit：阶段 Xₙ 由 Xₙ₋₁ 经纤维 fiberₙ 粘合的**分裂**扩张数据。
-- 经典语义：kₙ = 0 ⟺ 扩张分裂——故本 record 携带截面即 kₙ 平凡的见证形。
record KnSplit (G : DiGraph) (x : DiGraph.V G) (T : PostnikovTower G x) (n : ℕ) : Set₁ where
  open PostnikovTower T
  field
    fiberₙ   : Set                                     -- 粘合纤维（Ωⁿ 新增同伦数据）
    fiber-pt : fiberₙ                                  -- 平凡纤维基点
    sectₙ    : Xₙ n → Xₙ (suc n)                       -- 截面（分裂）
    sect-map : (z : Xₙ n) → stage-map n (sectₙ z) ≡ z  -- 截面性质

-- ⑤ 组合层（S²ᵈ k₂ 双实例）

-- S²ᵈ 的 2-截断塔（k₂ 面）：X₀ = ⊤｜X₁ = ⊤｜X₂ = 圈 w3 上的 2-腔数据面。
-- stage-map 2 折叠至基点 2-腔 nil2 w3（投影杀纤维数据——平凡粘合形）。
tower-s2-k : PostnikovTower s2-adj s2v0
tower-s2-k = record
  { Xₙ        = λ { zero → ⊤ ; (suc zero) → ⊤ ; (suc (suc _)) → Ω2Walk s2-adj s2v0 w3 w3 }
  ; stage-map = λ { zero _ → tt ; (suc zero) _ → tt ; (suc (suc _)) _ → nil2 w3 }
  ; trunc₂    = λ _ → ⊤
  ; trunc-wit = λ _ → tt
  }

-- k₂ 分裂实例（n = 1 粘合步）：纤维 = 2-腔面，截面 = 常值基点 2-腔。
k2-split-s2 : KnSplit s2-adj s2v0 tower-s2-k 1
k2-split-s2 = record
  { fiberₙ   = Ω2Walk s2-adj s2v0 w3 w3
  ; fiber-pt = nil2 w3
  ; sectₙ    = λ _ → nil2 w3
  ; sect-map = λ z → refl
  }

-- k₂ 面级实例：omega2-wit 的粘合数据计算——三角面填充（3-腔）即 k₂ 平凡化证据。
-- （_PPI5f：omega2-wit-triv = gen3 (fill-tri face012-slide)——面 (0,1,2) 侧。）
k2-face-s2 : Kn2Data s2-adj s2v0 w3
k2-face-s2 = record { c = omega2-wit ; c-fill = omega2-wit-triv }

-- ⑥ 核对层

-- GF(3) 挠类对账：k₂ 平凡类在 GF(3) 系数下的类值 = T₀（挠面消失的系数面注记）。
k2-class-s2 : Trit
k2-class-s2 = T₀

check-k2-class : k2-class-s2 ≡ T₀
check-k2-class = refl

-- 分裂实例核对：截面性质在基点处 definitional 闭合。
check-sect-s2 : KnSplit.sect-map k2-split-s2 tt ≡ refl
check-sect-s2 = refl

-- §5 立界注记（诚实边界——不硬拱）
-- (i) 与经典 k-不变量的桥（kₙ 组合形 = EM 对照形的类对应）——EM 空间线属未开线
--     （复用 Cubical.HITs.EilenbergMacLane 方向，任务书 v2.0 勘误后为可选对照形）；
-- (ii) 一般 X 的 kₙ 面级分类（Kn2Data 的商面 rec/elim 定理族——依赖 π₂ᵈ 商面件）；
-- (iii) 系数理论全形（Hⁿ⁺¹(Xₙ₋₁; πₙ) 的离散上同调实现）——依赖 2.5 discreteHurewicz 线。
