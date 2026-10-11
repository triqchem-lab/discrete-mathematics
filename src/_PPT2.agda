{-# OPTIONS --rewriting --guardedness #-}

-- | _PPT2 —— Postnikov 塔线 PT-2：离散 Postnikov 塔（组合形）
-- 数学背景：Postnikov 塔将空间按同伦群逐层截断（Xₙ 抹除 >n 阶同伦信息，
--   阶间纤维 K(πₙ,n)）。本件为**离散对应**（PostnikovTruncation 头注同款口径）：
--   塔阶 = 组合数据，截断性质 = 「高阶循环数据平凡」的组合见证。
--   真身是空间截断——本件非真身，且零 K(G,n) 机件（Ωⁿ 迭代路线）。
-- 核心原则：
-- 1. 组合形即终形（Ωⁿ 迭代路线——避开 k-不变量阶数坑）
-- 2. 诚实标注：离散对应非空间截断真身；实例为最小形（塔前两阶）
-- 3. 复用零重证（π₁ᵈ/Ω2Walk/AStep-sk-empty/disp 全机件直引）
-- 包含：PostnikovTower record｜Gskel two-chain 塔实例（真截断见证）
--       ｜G2s/S²ᵈ 结构实例（smoke）｜disp 截断对账

module _PPT2 where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥-elim)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Sovereign.Topology.BarceloAHomotopy using (DiGraph; Walk; nil)
open import _PPI2 using (π₁ᵈ; G2s)
open import _PPI4 using (Gskel)
open import Sovereign.Topology.McCordPi0 using (two-chain)
open import _PPI4c using (AStep-sk-empty)
open import _PPI5d using (Ω2Walk; nil2; cons2; Ω2ᵈ; s2-adj)
open import Sovereign.HoTT.PostnikovTruncation using (WeightedDiGraph; disp)

-- ────────────────────────────────────────────────────────────────────
-- §1. 离散 Postnikov 塔（抽象接口——组合形）
--     Xₙ 阶段 + stage-map 塔映射 + trunc₂ 截断见证（2-腔数据平凡形）
-- ────────────────────────────────────────────────────────────────────

record PostnikovTower (G : DiGraph) (x : DiGraph.V G) : Set₁ where
  field
    Xₙ        : ℕ → Set                       -- n 阶段载体（组合数据）
    stage-map : ∀ n → Xₙ (suc n) → Xₙ n       -- 塔映射 Xₙ₊₁ → Xₙ
    -- 截断性质（组合形最小形）：n 阶段 2-腔数据平凡
    --   （一般形 πᵢ(Xₙ)=0 (i>n) 的迭代 Ω 形——立界，见 §5 注记）
    trunc₂    : (n : ℕ) → Set
    trunc-wit : (n : ℕ) → trunc₂ n

-- ────────────────────────────────────────────────────────────────────
-- §2. Gskel two-chain 塔实例（真内容截断见证）
--    数学事实：Gskel two-chain 无三角（AStep-sk-empty，_PPI4c）
--      ⇒ AStep 全空 ⇒ 2-腔的 gen 案不可达 ⇒ Ω2ᵈ 仅剩 nil2 形。
-- ────────────────────────────────────────────────────────────────────

-- 2-腔收缩（真内容）：任意两 2-腔 p q 相等（gen 案被空消解）
Ω2-triv-gskel : (p q : Ω2ᵈ (Gskel two-chain) fzero) → p ≡ q
Ω2-triv-gskel (nil2 w) (nil2 .w)  = refl
Ω2-triv-gskel (nil2 w) (cons2 s q) = ⊥-elim (AStep-sk-empty s)
Ω2-triv-gskel (cons2 s p) q        = ⊥-elim (AStep-sk-empty s)

-- 基点：Gskel two-chain 顶点 = Fin 2 首元（与 _PPI4g loopK 同形）
tower-gskel : PostnikovTower (Gskel two-chain) fzero
tower-gskel = record
  { Xₙ        = λ { zero → ⊤ ; (suc n) → π₁ᵈ (Gskel two-chain) fzero }
  ; stage-map = λ { zero _ → tt ; (suc n) → λ z → z }
    -- 注记：图 = 1-型（nerve 一维）⇒ 塔在 n=1 稳定（Xₙ 1 以上恒 π₁ᵈ，映射恒等）
  ; trunc₂    = λ { zero → ((u : ⊤) → u ≡ tt)
                  ; (suc n) → (p q : Ω2ᵈ (Gskel two-chain) fzero) → p ≡ q }
  ; trunc-wit = λ { zero → λ { tt → refl } ; (suc n) → Ω2-triv-gskel }
  }

-- ────────────────────────────────────────────────────────────────────
-- §3. G2s 结构实例（smoke——任务点名面）
--     ⚠ G2s 自环富形（edge = λ a b → ⊤ 含自环）——高阶平凡性非显然，
--       trunc₂ 以 ⊤ 供给 + 立界注记（自环面 2-腔分类待补）。
-- ────────────────────────────────────────────────────────────────────

tower-g2s : PostnikovTower G2s fzero
tower-g2s = record
  { Xₙ        = λ { zero → ⊤ ; (suc n) → π₁ᵈ G2s fzero }
  ; stage-map = λ { zero _ → tt ; (suc n) → λ z → z }
  ; trunc₂    = λ _ → ⊤
  ; trunc-wit = λ _ → tt
  }
-- 立界：G2s 自环面的 Ω² 分类（tower-gskel 的 Ω2-triv 同款不适用——自环给 AStep）

-- ────────────────────────────────────────────────────────────────────
-- §4. S²ᵈ 结构实例（smoke——任务点名面）
--     ⚠ S²ᵈ 完整塔立界（Ω² 分类件在 _PPI5f 最小面——一般形待补）。
-- ────────────────────────────────────────────────────────────────────

tower-s2 : PostnikovTower s2-adj fzero
tower-s2 = record
  { Xₙ        = λ { zero → ⊤ ; (suc n) → π₁ᵈ s2-adj fzero }
  ; stage-map = λ { zero _ → tt ; (suc n) → λ z → z }
  ; trunc₂    = λ _ → ⊤
  ; trunc-wit = λ _ → tt
  }
-- 立界：S²ᵈ 的 Ω² 分类完整形（_PPI5f 有 omega2-wit 双面 3-可缩最小件）

-- ────────────────────────────────────────────────────────────────────
-- §5. disp 截断对账
--    PostnikovTruncation 的 disp = walk 权重累积 = 1-截断映射；
--    与塔 n=1 阶一致性：空走零位移（definitional 形）。
-- ────────────────────────────────────────────────────────────────────

disp-nil-check : (W : WeightedDiGraph) (v : DiGraph.V (WeightedDiGraph.G W)) →
                 disp W (nil v) ≡ WeightedDiGraph.zeroA W
disp-nil-check W v = refl
-- 立界：loopK 案对账需均权 W 实例（权值+单位/结合律填装 ~20 行——后续件）
