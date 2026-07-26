{-# OPTIONS --rewriting --guardedness #-}

module Sovereign.Algebra.TriCycGraph where

open import Data.Fin using (Fin; zero; suc)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans)

open import Sovereign.Base.Trit using (T₀)
open import Sovereign.Algebra.GF9
  using (GF9; _+gf9_; _*gf9_; galoisConjugate;
         gf9-one; galoisConjugate²; +gf9-comm; *gf9-comm)

-- ══════════════════════════════════════════════════════════════
-- §1 三角循环图（Triangular Cyclic Graph）
-- ══════════════════════════════════════════════════════════════
--
-- 数学定义：
--   三角循环图是有向图，顶点集 {0, 1, 2}，
--   边构成3-循环 0→1→2→0。
--   每条边赋权一个 GF(9) 元素（相位权重）。
--
-- 在亚瑟量子电机中的角色：
--   替代传统换向器，决定电机的运转节律。

TriCycGraph : Set
TriCycGraph = Fin 3 → GF9

edge₀₁ : Fin 3
edge₀₁ = zero

edge₁₂ : Fin 3
edge₁₂ = suc zero

edge₂₀ : Fin 3
edge₂₀ = suc (suc zero)

-- ── Fin 3 上的循环移位 ──

fin3-shift : Fin 3 → Fin 3
fin3-shift zero          = suc zero
fin3-shift (suc zero)    = suc (suc zero)
fin3-shift (suc (suc _)) = zero

-- 移位三次 = id
fin3-shift³ : ∀ (i : Fin 3) → fin3-shift (fin3-shift (fin3-shift i)) ≡ i
fin3-shift³ zero          = refl
fin3-shift³ (suc zero)    = refl
fin3-shift³ (suc (suc zero)) = refl

-- ── 移位算子 ──

shift : TriCycGraph → TriCycGraph
shift w i = galoisConjugate (w (fin3-shift i))

-- ── 特殊图 ──

zeroGraph : TriCycGraph
zeroGraph _ = (T₀ , T₀)

oneGraph : TriCycGraph
oneGraph _ = gf9-one

-- ══════════════════════════════════════════════════════════════
-- §2 pureShift³ = id（C₃ 生成元）
-- ══════════════════════════════════════════════════════════════

pureShift : TriCycGraph → TriCycGraph
pureShift w i = w (fin3-shift i)

pureShift³-id : ∀ (w : TriCycGraph) (i : Fin 3)
  → pureShift (pureShift (pureShift w)) i ≡ w i
pureShift³-id w i = cong w (fin3-shift³ i)

-- ══════════════════════════════════════════════════════════════
-- §3 Frobenius 移位的六阶性质
-- ══════════════════════════════════════════════════════════════
--
-- shift²(w)(i) = σ(σ(w(i+2))) = w(i+2)  （σ² = id）
-- shift⁶(w)(i) = w(i+6) = w(i)           （6 ≡ 0 mod 3）

-- shift⁶ 的核心引理：shift² = pureShift²（σ² 消去）
shift²-pure : ∀ (w : TriCycGraph) (i : Fin 3)
  → shift (shift w) i ≡ w (fin3-shift (fin3-shift i))
shift²-pure w i = galoisConjugate² (w (fin3-shift (fin3-shift i)))

-- fin3-shift⁶ = id（逐 case 计算）
fin3-shift⁶ : ∀ (i : Fin 3)
  → fin3-shift (fin3-shift (fin3-shift (fin3-shift (fin3-shift (fin3-shift i))))) ≡ i
fin3-shift⁶ zero          = refl
fin3-shift⁶ (suc zero)    = refl
fin3-shift⁶ (suc (suc zero)) = refl

-- σ⁶ = id（Frobenius 六次复合 = 恒等）
-- 链式：σ⁶(x) ≡ σ⁴(x) ≡ σ²(x) ≡ x
σ⁶-id : ∀ (x : GF9)
  → galoisConjugate (galoisConjugate (galoisConjugate (galoisConjugate (galoisConjugate (galoisConjugate x))))) ≡ x
σ⁶-id x = trans (galoisConjugate² (galoisConjugate (galoisConjugate (galoisConjugate (galoisConjugate x)))))
                 (trans (galoisConjugate² (galoisConjugate (galoisConjugate x)))
                        (galoisConjugate² x))

-- shift⁶ = id（电机六阶周期定理）
-- 对每个 i，shift⁶(w)(i) 通过计算化简为 σ⁶(w(i)) = w(i)
shift⁶-id : ∀ (w : TriCycGraph) (i : Fin 3)
  → shift (shift (shift (shift (shift (shift w))))) i ≡ w i
shift⁶-id w zero          = σ⁶-id (w zero)
shift⁶-id w (suc zero)    = σ⁶-id (w (suc zero))
shift⁶-id w (suc (suc zero)) = σ⁶-id (w (suc (suc zero)))

-- ══════════════════════════════════════════════════════════════
-- §4 图的代数运算
-- ══════════════════════════════════════════════════════════════

_⊗g_ : TriCycGraph → TriCycGraph → TriCycGraph
(w₁ ⊗g w₂) i = w₁ i *gf9 w₂ i

_⊕g_ : TriCycGraph → TriCycGraph → TriCycGraph
(w₁ ⊕g w₂) i = w₁ i +gf9 w₂ i

⊗g-comm : ∀ (w₁ w₂ : TriCycGraph) (i : Fin 3)
  → (w₁ ⊗g w₂) i ≡ (w₂ ⊗g w₁) i
⊗g-comm w₁ w₂ i = *gf9-comm (w₁ i) (w₂ i)

⊕g-comm : ∀ (w₁ w₂ : TriCycGraph) (i : Fin 3)
  → (w₁ ⊕g w₂) i ≡ (w₂ ⊕g w₁) i
⊕g-comm w₁ w₂ i = +gf9-comm (w₁ i) (w₂ i)

-- ══════════════════════════════════════════════════════════════
-- §5 图的总权重
-- ══════════════════════════════════════════════════════════════

totalWeight : TriCycGraph → GF9
totalWeight w = w edge₀₁ +gf9 (w edge₁₂ +gf9 w edge₂₀)
