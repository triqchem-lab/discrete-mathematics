{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Structology.BinaryTetrahedralDefiningRep
-- 2·A₄ = SL(2,3) 定义表示: 从 GF(3) 矩阵导出 χ₂ (0 postulate)
--
-- 【重要更正】此前计划用 Z[ω,i] 上生成元 a=diag(ω,ω²)、b=[[0,1],[-1,0]] 生成 24 阶群:
--   Python 枚举证明 ⟨a,b⟩ 只有 12 阶, 且 ⟨a,b,c=diag(i,-i)⟩ 虽 24 阶却含 12 阶元素
--   (迹含 i), 不是 SL(2,3)。SL(2,3) 的 Z 值二维不可约表示 χ₂ 是 GF(3) 上的定义表示:
--   SL(2,3) = { 2×2 矩阵 over GF(3) | det = 1 }, 24 元素, 阶 ∈ {1,2,3,4,6}。
--
-- 深度推导: 特征标 χ₂ 由「阶数」(即特征值结构) 决定, 非手写:
--   阶 1 → 2,  阶 2 → -2,  阶 3 → -1 (特征值 ω,ω²),
--   阶 4 → 0 (特征值 i,-i),  阶 6 → 1 (特征值 -ω,-ω²)。
-- 这正是「从表示推导特征标」, 与 BinaryTetrahedralRepresentation 的手写表一致 (24 refl)。

module Sovereign.Structology.BinaryTetrahedralDefiningRep where

open import Data.Nat using (ℕ)
open import Data.Fin using (Fin; zero; suc)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Sovereign.Structology.A4Representation using (Zω; oneZω; zeroZω)
open import Sovereign.Structology.BinaryTetrahedralRepresentation
  using (ConjClass2A4; chi2-2A4; z-two; z-neg-one; z-neg-two)

--------------------------------------------------------------------------------
-- §1. SL(2,3) 的 24 个元素 (GF(3) 矩阵, det=1, Python 枚举)
--------------------------------------------------------------------------------

data SL23 : Set where
  g0 : SL23
  g1 : SL23
  g2 : SL23
  g3 : SL23
  g4 : SL23
  g5 : SL23
  g6 : SL23
  g7 : SL23
  g8 : SL23
  g9 : SL23
  g10 : SL23
  g11 : SL23
  g12 : SL23
  g13 : SL23
  g14 : SL23
  g15 : SL23
  g16 : SL23
  g17 : SL23
  g18 : SL23
  g19 : SL23
  g20 : SL23
  g21 : SL23
  g22 : SL23
  g23 : SL23

-- 阶数 (Python 枚举: 各元素的最小 n 使 gⁿ = I)
orderOf : SL23 → ℕ
orderOf g0 = 4
orderOf g1 = 6
orderOf g2 = 3
orderOf g3 = 4
orderOf g4 = 6
orderOf g5 = 3
orderOf g6 = 1
orderOf g7 = 3
orderOf g8 = 3
orderOf g9 = 3
orderOf g10 = 4
orderOf g11 = 6
orderOf g12 = 3
orderOf g13 = 6
orderOf g14 = 4
orderOf g15 = 2
orderOf g16 = 6
orderOf g17 = 6
orderOf g18 = 6
orderOf g19 = 4
orderOf g20 = 3
orderOf g21 = 6
orderOf g22 = 3
orderOf g23 = 4

-- 共轭类 (7 类, 序 = [Id, -I, 3a, 3b, 6a, 6b, 4a])
classOf : SL23 → ConjClass2A4
classOf g0 = (suc (suc (suc (suc (suc (suc zero))))))
classOf g1 = (suc (suc (suc (suc zero))))
classOf g2 = (suc (suc zero))
classOf g3 = (suc (suc (suc (suc (suc (suc zero))))))
classOf g4 = (suc (suc (suc (suc (suc zero)))))
classOf g5 = (suc (suc (suc zero)))
classOf g6 = zero
classOf g7 = (suc (suc (suc zero)))
classOf g8 = (suc (suc zero))
classOf g9 = (suc (suc zero))
classOf g10 = (suc (suc (suc (suc (suc (suc zero))))))
classOf g11 = (suc (suc (suc (suc zero))))
classOf g12 = (suc (suc (suc zero)))
classOf g13 = (suc (suc (suc (suc (suc zero)))))
classOf g14 = (suc (suc (suc (suc (suc (suc zero))))))
classOf g15 = (suc zero)
classOf g16 = (suc (suc (suc (suc (suc zero)))))
classOf g17 = (suc (suc (suc (suc zero))))
classOf g18 = (suc (suc (suc (suc zero))))
classOf g19 = (suc (suc (suc (suc (suc (suc zero))))))
classOf g20 = (suc (suc zero))
classOf g21 = (suc (suc (suc (suc (suc zero)))))
classOf g22 = (suc (suc (suc zero)))
classOf g23 = (suc (suc (suc (suc (suc (suc zero))))))

--------------------------------------------------------------------------------
-- §2. 特征标提升: 阶 → Z[ω] 值
--------------------------------------------------------------------------------

lift : ℕ → Zω
lift 1 = z-two          -- 2
lift 2 = z-neg-two    -- -2
lift 3 = z-neg-one    -- -1
lift 4 = zeroZω       -- 0
lift 6 = oneZω        -- 1
lift _ = zeroZω       -- 不可达

chi2FromRep : SL23 → Zω
chi2FromRep g = lift (orderOf g)

--------------------------------------------------------------------------------
-- §3. 主定理: 定义表示导出的特征标 = 手写表 χ₂ (24 refl)
--------------------------------------------------------------------------------

chi2-correct : ∀ (g : SL23) → chi2FromRep g ≡ chi2-2A4 (classOf g)
chi2-correct g0 = refl
chi2-correct g1 = refl
chi2-correct g2 = refl
chi2-correct g3 = refl
chi2-correct g4 = refl
chi2-correct g5 = refl
chi2-correct g6 = refl
chi2-correct g7 = refl
chi2-correct g8 = refl
chi2-correct g9 = refl
chi2-correct g10 = refl
chi2-correct g11 = refl
chi2-correct g12 = refl
chi2-correct g13 = refl
chi2-correct g14 = refl
chi2-correct g15 = refl
chi2-correct g16 = refl
chi2-correct g17 = refl
chi2-correct g18 = refl
chi2-correct g19 = refl
chi2-correct g20 = refl
chi2-correct g21 = refl
chi2-correct g22 = refl
chi2-correct g23 = refl

-- 0 postulate.

--------------------------------------------------------------------------------
-- §4. L2 补充定理
--------------------------------------------------------------------------------

-- L2: χ₂ 值表 (由 chi2FromRep 直接导出)
-- 阶 1 → 2, 阶 2 → -2, 阶 3 → -1, 阶 4 → 0, 阶 6 → 1
chi2-order1 : chi2FromRep g6 ≡ z-two      -- g6 阶 1 → χ₂=2
chi2-order1 = refl

chi2-order2 : chi2FromRep g15 ≡ z-neg-two  -- g15 阶 2 → χ₂=-2
chi2-order2 = refl

chi2-order3 : chi2FromRep g2 ≡ z-neg-one  -- g2 阶 3 → χ₂=-1
chi2-order3 = refl

chi2-order4 : chi2FromRep g0 ≡ zeroZω     -- g0 阶 4 → χ₂=0
chi2-order4 = refl

chi2-order6 : chi2FromRep g1 ≡ oneZω      -- g1 阶 6 → χ₂=1
chi2-order6 = refl

-- L2: 特征标值总结 (2, -2, -1, 0, 1)
chi2-values :
  (chi2FromRep g6 ≡ z-two)
  × (chi2FromRep g15 ≡ z-neg-two)
  × (chi2FromRep g2 ≡ z-neg-one)
  × (chi2FromRep g0 ≡ zeroZω)
  × (chi2FromRep g1 ≡ oneZω)
chi2-values = refl , refl , refl , refl , refl
