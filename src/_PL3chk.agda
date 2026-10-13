{-# OPTIONS --rewriting --guardedness #-}
-- | _PL3chk —— 线3 disp2-respects 小例核对（2 步 walk 的 slide 案）
--   ① refl 级：两步 walk 与滑步 walk 的 disp2 计算值相等（wt≡1 实例）
--   ② 定理调用：gen (slide …) 经 disp2-respects 出等式
module _PL3chk where

open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
open import Data.Nat.Properties using (+-assoc; +-comm; +-identityˡ; +-identityʳ; *-assoc; *-identityˡ; *-identityʳ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Sovereign.Topology.BarceloAHomotopy using (DiGraph; Walk; nil; cons; AStep; slide; AHomotopy; gen)
open import Sovereign.Synthesis.PostnikovTruncation
open WeightedDiGraph

-- 具体图：三点三边（x→y, y→z, x→z）
data V3 : Set where vx vy vz : V3
data E3 : V3 → V3 → Set where
  e1 : E3 vx vy
  e2 : E3 vy vz
  e3 : E3 vx vz

G3 : DiGraph
G3 = record { V = V3 ; edge = E3 }

-- 具体权重图：wt ≡ 1（harm 退化为 1*1 ≡ 1 = refl）
W3 : WeightedDiGraph
W3 = record
  { G = G3 ; A = ℕ ; _+A_ = _+_ ; zeroA = 0 ; _*A_ = _*_ ; oneA = 1
  ; wt = λ _ _ → 1
  ; +A-assoc = +-assoc ; +A-comm = +-comm ; +A-idˡ = +-identityˡ
  ; *A-assoc = *-assoc ; *A-idʳ = *-identityʳ ; *A-idˡ = *-identityˡ }

harm3 : ∀ a b c → (_*A_ W3 (wt W3 a b) (wt W3 b c)) ≡ wt W3 a c
harm3 a b c = refl

-- 2 步 walk vs 滑步 walk
w-left w-right : Walk G3 vx vz
w-left  = cons e1 (cons e2 (nil vz))
w-right = cons e3 (nil vz)

-- ① refl 级核对（计算值相等）
chk-left  : disp2 W3 w-left  ≡ 1
chk-left  = refl
chk-right : disp2 W3 w-right ≡ 1
chk-right = refl

-- ② 定理调用（gen (slide …) → disp2-respects）
chk-slide : disp2 W3 w-left ≡ disp2 W3 w-right
chk-slide = disp2-respects W3 (gen (slide (nil vx) (nil vz) e1 e2 e3)) harm3

chk-step : disp2 W3 w-left ≡ disp2 W3 w-right
chk-step = step-respects W3 (slide (nil vx) (nil vz) e1 e2 e3) harm3
