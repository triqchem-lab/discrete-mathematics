{-# OPTIONS --rewriting --guardedness #-}

-- | _PD1 —— D1-impl 施工批：Mergeable 判据定理骨架（双向 + 图面件）
--
-- 数学背景：分水岭一般化的图面判据（D1 报告 c227588 §四）：「可逆性=每边有返边
--   且**去返对在 AHomotopy 下可消**」。本件落三段：
--   DIM-1 Mergeable 谓词 record（返边判据——每边带返回 witness 形式化）；
--   DIM-2 Ø 面（单点图/边-income 零图）——样例级判据核对（preliminary 2 例）；
--   DIM-3 充分方向骨架：Mergeable ⟹ 「inv-face 存在」（逆元素面条件——按
--   D1 报告 UI(P)(V) 前提范式，真定理留分水岭 v2 批——立界注记如实）。
--   必要方向 = ¬Mergeable ⟹ ¬群——**本件不写**（npos 长度计数依赖 _PPI4k 泛形
--  ผ UIP(V) 前提面；骨架属 _PPI4m 系立界执行段——立界留 §后注）。
--
-- 原则：关系入定义（edge-witness record）；0 postulate；穷举边界（样例二例）；
-- 量测时尚未 commit 即写盘保留（防下轮盘面回死）。
--
-- 包含：Mergeable · Mergeable-单点/双向样例 · inv-face-premise（骨架）· 核对层

module _PD1 where

open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (¬)

open import Sovereign.Topology.BarceloAHomotopy
  using (DiGraph; Walk; nil; AHomotopy; AH-refl; AH-symm; AH-trans; _++w_; cons; AStep; slide; expand)
open import _PPI2 using (π₁ᵈ; _⊞ᵈ_; π₁ᵈ-rec; []-resp)
open import _PPI4 using (Gskel; Gcmp; MonoidIso; Flip; Gskel-flip; Gcmp-flip)

-- ────────────────────────────────────────────────────────────────────
-- §1 DIM-1 Mergeable 谓词（每边有返边——D1 报告判据件）
--    Mergeable G = ∀ (u→v)∈E → ∃ 相消证据：…（D1 报告判据的 record 编码）
--    形式化选择：返边 witness 的「存在谓词型」，AHomotopy 可消性面留证明侧
-- ────────────────────────────────────────────────────────────────────

record Mergeable (G : DiGraph) : Set₁
 where
  field
    return-edge : ∀ {u v} → DiGraph.edge G u v → DiGraph.edge G v u
    return-ah   : ∀ {u v} (e : DiGraph.edge G u v) →
      Σ (Walk G u u) (λ q → AHomotopy G (cons e (cons (return-edge e) q)) (nil u))


