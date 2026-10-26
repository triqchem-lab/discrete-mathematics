{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Synthesis.A4.BilinearSchur2A4
--
-- **双线性 Schur 正交关系**（Z[ω] 内精确，不扩环）：
--
--     Σ_{g∈2A₄} ρᵢⱼ(g)·ρₖₗ(g) = 12·εᵢₖ·εⱼₗ ,     ε = [[0,1],[−1,0]]
--
-- 为什么是**双线性**而不是 Hermite 型（`Σ ρᵢⱼ·conj ρₖₗ = (|G|/d)·δδ`）：
--   · Hermite 型 Schur 只对**酉**表示成立；本模型是 Z[ω] 上的非酉实现
--     （U†U = [[1,−1],[−1,2]] ≠ I），酉化要 H = Σ ρ†ρ 的平方根，
--     det H = 864 = 144·6 ⇒ 需 √6 ⇒ **出 Z[ω]**，代价过大。
--   · 实测反例（本模块 §7，非断言而是定理）：Σ_g ρ₀₀·conj ρ₀₀ = **18**，
--     而 Hermite 型 Schur 要求 |G|/d = 24/2 = 12。差 6 ≠ 0 ⇒ 该型确不成立。
--   · 双线性型成立的**原因**是 Frobenius–Schur 指标为 −1（quaternionic）：
--     Σ_g χ(g²) = −24 = −|G| ⇒ 指标 = −1 ⇒ 不变双线性形式**反对称** ⇒ ε⊗ε。
--     本模块 §6 把这条算成定理。
--
-- 模型（= sov-math `Sov.Math.Complex2A4` 的 24 个 Z[ω] 矩阵）：
--   i = [[−ω,−1],[−ω,ω]] ,  j = [[0,ω],[1+ω,0]] ,  U = [[0,−1],[1,−1]]
--   的闭包（阶 24）。本模块以 `toME : SL23 → M2E` 给出 24 个矩阵，并证：
--     · §8 `redM-toME`：逐项模 (1−ω) 归约回 GF(3) 定义表示 `toMat`
--     · §9 `toME-hom`：**24 行 × 24 案**，对 SL23 的 Cayley 表逐条核对
--   两条合起来才叫"这 24 个矩阵是 2A₄（= SL(2,F₃)）的忠实 2 维 Z[ω] 实现"。
--
-- 口径：有限集全枚举（24 元素 / 24² 对 / 4×4 系数对），非数值字面量暴力求值；
--   零浮点、零 partial。0 postulate / 0 hole。
module Sovereign.Synthesis.A4.BilinearSchur2A4 where

open import Data.Fin using (Fin; zero; suc)
open import Data.Integer using (ℤ; +_; -[1+_])
open import Data.List using (List; _∷_; []; foldr)
open import Data.Nat using (ℕ)
open import Data.Nat as NatP using (suc; _*_)
open import Data.Nat.DivMod using (_mod_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong; cong₂)

open import Sovereign.Synthesis.Representation.SL23Cayley
  using (Mat2; add3; toMat; _⊗_)
open import Sovereign.Algebra.LinearAlgebra.Matrix2 using (mkMat2)
open import Sovereign.Synthesis.A4.A4Representation
  using (Zω; mkZω; zeroZω; oneZω; ω; ω²; addZω; negZω; mulZω; conjZω)
open import Sovereign.Synthesis.A4.BinaryTetrahedralDefiningRep
  using (SL23; g0; g1; g2; g3; g4; g5; g6; g7; g8; g9; g10; g11
        ; g12; g13; g14; g15; g16; g17; g18; g19; g20; g21; g22; g23)

--------------------------------------------------------------------------------
-- §1 Z[ω] 上的 2×2 矩阵（sov-math `M2E` 的 Agda 版）
--------------------------------------------------------------------------------

record M2E : Set where
  constructor m2e
  field
    u00 u01 u10 u11 : Zω

open M2E

mulME : M2E → M2E → M2E
mulME (m2e a b c d) (m2e e f g h) =
  m2e (addZω (mulZω a e) (mulZω b g))
      (addZω (mulZω a f) (mulZω b h))
      (addZω (mulZω c e) (mulZω d g))
      (addZω (mulZω c f) (mulZω d h))

traceME : M2E → Zω
traceME (m2e a _ _ d) = addZω a d

-- 数据中出现的 7 个 Z[ω] 值（全枚举数据里只有这 7 个，别处不出现）
c0 c1 cm1 cw cw2 c1w cmw : Zω
c0  = zeroZω                   -- 0
c1  = oneZω                    -- 1
cm1 = negZω oneZω              -- −1
cw  = ω                        -- ω
cw2 = ω²                       -- ω² = −1−ω
c1w = negZω ω²                 -- 1+ω
cmw = negZω ω                  -- −ω

--------------------------------------------------------------------------------
-- §2 24 个矩阵：2A₄ 的 2 维 Z[ω] 表示（生成元 i, j, U 的闭包）
--
-- 索引与 SL23 的 24 个构造子一一对应：对应关系由 §8 的 `redM-toME` 钉住
-- （逐项模 (1−ω) 归约回 GF(3) 定义表示），乘法一致性由 §9 `toME-hom` 钉住。
--------------------------------------------------------------------------------

toME : SL23 → M2E
toME g0  = m2e c0  cw  c1w c0
toME g1  = m2e c0  c1  cm1 c1
toME g2  = m2e c0  cw2 cmw cm1
toME g3  = m2e c0  cmw cw2 c0
toME g4  = m2e c0  c1w cw  c1
toME g5  = m2e c0  cm1 c1  cm1
toME g6  = m2e c1  c0  c0  c1
toME g7  = m2e cw2 c0  cw2 cw
toME g8  = m2e cw  c0  c1w cw2
toME g9  = m2e cw2 cw  c0  cw
toME g10 = m2e cw  c1  cw  cmw
toME g11 = m2e c1  cw2 cmw c0
toME g12 = m2e cw  cmw c0  cw2
toME g13 = m2e c1  cm1 c1  c0
toME g14 = m2e cw2 c1w cm1 c1w
toME g15 = m2e cm1 c0  c0  cm1
toME g16 = m2e cmw c0  cw2 c1w
toME g17 = m2e c1w c0  c1w cmw
toME g18 = m2e cmw cw  c0  c1w
toME g19 = m2e c1w cw2 c1  cw2
toME g20 = m2e cm1 c1  cm1 c0
toME g21 = m2e c1w cmw c0  cmw
toME g22 = m2e cm1 c1w cw  c0
toME g23 = m2e cmw cm1 cmw cw

--------------------------------------------------------------------------------
-- §3 群上求和（24 项，无权重：2A₄ 有限离散，Haar 全 1）
--------------------------------------------------------------------------------

allSL23 : List SL23
allSL23 = g0 ∷ g1 ∷ g2 ∷ g3 ∷ g4 ∷ g5 ∷ g6 ∷ g7 ∷ g8 ∷ g9 ∷ g10 ∷ g11
        ∷ g12 ∷ g13 ∷ g14 ∷ g15 ∷ g16 ∷ g17 ∷ g18 ∷ g19 ∷ g20 ∷ g21
        ∷ g22 ∷ g23 ∷ []

sumSL23 : (SL23 → Zω) → Zω
sumSL23 f = foldr (λ x acc → addZω (f x) acc) zeroZω allSL23

card-SL23 : ℕ
card-SL23 = 24

--------------------------------------------------------------------------------
-- §4 矩阵系数与 ε
--------------------------------------------------------------------------------

entry : Fin 2 → Fin 2 → M2E → Zω
entry zero    zero    (m2e x _ _ _) = x
entry zero    (suc _) (m2e _ y _ _) = y
entry (suc _) zero    (m2e _ _ z _) = z
entry (suc _) (suc _) (m2e _ _ _ w) = w

-- ε = [[0,1],[−1,0]]（反对称不变形式；quaternionic 型的标志）
εZ : Fin 2 → Fin 2 → Zω
εZ zero    (suc _) = oneZω
εZ (suc _) zero    = negZω oneZω
εZ _       _       = zeroZω

twelveZ twentyFourZ : Zω
twelveZ     = mkZω (+ 12) (+ 0)
twentyFourZ = mkZω (+ 24) (+ 0)

--------------------------------------------------------------------------------
-- §5 主定理：双线性 Schur（16 = 4×4 个系数对，每对 24 项求和）
--------------------------------------------------------------------------------

schurLHS : Fin 2 → Fin 2 → Fin 2 → Fin 2 → Zω
schurLHS i j k l = sumSL23 (λ x → mulZω (entry i j (toME x)) (entry k l (toME x)))

bilinearSchur : ∀ (i j k l : Fin 2)
              → schurLHS i j k l ≡ mulZω twelveZ (mulZω (εZ i k) (εZ j l))
bilinearSchur zero    zero    zero    zero    = refl
bilinearSchur zero    zero    zero    (suc _) = refl
bilinearSchur zero    zero    (suc _) zero    = refl
bilinearSchur zero    zero    (suc _) (suc _) = refl
bilinearSchur zero    (suc _) zero    zero    = refl
bilinearSchur zero    (suc _) zero    (suc _) = refl
bilinearSchur zero    (suc _) (suc _) zero    = refl
bilinearSchur zero    (suc _) (suc _) (suc _) = refl
bilinearSchur (suc _) zero    zero    zero    = refl
bilinearSchur (suc _) zero    zero    (suc _) = refl
bilinearSchur (suc _) zero    (suc _) zero    = refl
bilinearSchur (suc _) zero    (suc _) (suc _) = refl
bilinearSchur (suc _) (suc _) zero    zero    = refl
bilinearSchur (suc _) (suc _) zero    (suc _) = refl
bilinearSchur (suc _) (suc _) (suc _) zero    = refl
bilinearSchur (suc _) (suc _) (suc _) (suc _) = refl

--------------------------------------------------------------------------------
-- §6 Frobenius–Schur 指标 = −1（双线性型的**理由**）
--
--   Σ_g χ(g²) = Σ_g tr(ρ(g)²) = −24 = −|G|  ⇒  指标 = −24/24 = −1 ⇒ quaternionic
--   ⇒ 不变双线性形式反对称 ⇒ ε⊗ε（而不是 δ⊗δ）。
--------------------------------------------------------------------------------

fsNum : Zω
fsNum = sumSL23 (λ x → traceME (mulME (toME x) (toME x)))

frobeniusSchur : fsNum ≡ negZω twentyFourZ
frobeniusSchur = refl

--------------------------------------------------------------------------------
-- §7 边界（定理，不是断言）：Hermite 型 Schur 在本模型**不成立**
--
--   酉型 Schur 会要求 Σ_g ρᵢⱼ·conj ρᵢⱼ = |G|/d = 24/2 = 12。
--   实测：Σ_g ρ₀₀·conj ρ₀₀ = **18** ≠ 12。
--------------------------------------------------------------------------------

hermitianSum00 : Zω
hermitianSum00 = sumSL23 (λ x → mulZω (entry zero zero (toME x))
                                        (conjZω (entry zero zero (toME x))))

hermitianValue : hermitianSum00 ≡ mkZω (+ 18) (+ 0)
hermitianValue = refl

hermitianNotSchur : hermitianSum00 ≢ twelveZ
hermitianNotSchur e = int-18≢12 (cong Zω.a (trans hermitianValue e))
  where
    int-18≢12 : (+ 18) ≢ (+ 12)
    int-18≢12 = λ ()

--------------------------------------------------------------------------------
-- §8 归约回 GF(3)：toME 是定义表示 toMat 的提升
--
--   Z[ω] → Z[ω]/(1−ω) ≅ F₃ ,  ω ↦ 1  ⇒  a + bω ↦ a + b (mod 3)。
--   逐项核对：redM (toME x) ≡ toMat x（24 案）。
--------------------------------------------------------------------------------

redInt : ℤ → Fin 3
redInt (+ n)      = n mod 3
redInt (-[1+ n ]) = (NatP._*_ 2 (NatP.suc n)) mod 3

redZ : Zω → Fin 3
redZ (mkZω x y) = add3 (redInt x) (redInt y)

redM : M2E → Mat2
redM (m2e x y z w) = mkMat2 (redZ x) (redZ y) (redZ z) (redZ w)

redM-toME : ∀ (x : SL23) → redM (toME x) ≡ toMat x
redM-toME g0  = refl
redM-toME g1  = refl
redM-toME g2  = refl
redM-toME g3  = refl
redM-toME g4  = refl
redM-toME g5  = refl
redM-toME g6  = refl
redM-toME g7  = refl
redM-toME g8  = refl
redM-toME g9  = refl
redM-toME g10 = refl
redM-toME g11 = refl
redM-toME g12 = refl
redM-toME g13 = refl
redM-toME g14 = refl
redM-toME g15 = refl
redM-toME g16 = refl
redM-toME g17 = refl
redM-toME g18 = refl
redM-toME g19 = refl
redM-toME g20 = refl
redM-toME g21 = refl
redM-toME g22 = refl
redM-toME g23 = refl

--------------------------------------------------------------------------------
-- §9 乘法一致：toME 是群同态（24 行 × 24 案 = 576 对，与 SL23 的 Cayley 表逐条核对）
--
-- 【为何是穷举】SL23 是不透明 24 构造子 data，`_⊗_` 是 576 条查找表，无生成元/字
-- 表示可归纳；`toME` 也是 24 条显式矩阵。本定理的命题内容正是「表数据与 Z[ω] 矩阵
-- 乘法一致」的 576 条独立事实（与 SL23Cayley 的 `toMat-hom` 同构），逐条归约不可约。
-- 按「单引理 ≤27 案」纪律，按第一参数分解成 24 个行引理（每个 ∀ y，24 案）再组装。
--------------------------------------------------------------------------------

toME-hom-g0 : ∀ (y : SL23) → toME (g0 ⊗ y) ≡ mulME (toME g0) (toME y)
toME-hom-g0 g0  = refl
toME-hom-g0 g1  = refl
toME-hom-g0 g2  = refl
toME-hom-g0 g3  = refl
toME-hom-g0 g4  = refl
toME-hom-g0 g5  = refl
toME-hom-g0 g6  = refl
toME-hom-g0 g7  = refl
toME-hom-g0 g8  = refl
toME-hom-g0 g9  = refl
toME-hom-g0 g10 = refl
toME-hom-g0 g11 = refl
toME-hom-g0 g12 = refl
toME-hom-g0 g13 = refl
toME-hom-g0 g14 = refl
toME-hom-g0 g15 = refl
toME-hom-g0 g16 = refl
toME-hom-g0 g17 = refl
toME-hom-g0 g18 = refl
toME-hom-g0 g19 = refl
toME-hom-g0 g20 = refl
toME-hom-g0 g21 = refl
toME-hom-g0 g22 = refl
toME-hom-g0 g23 = refl

toME-hom-g1 : ∀ (y : SL23) → toME (g1 ⊗ y) ≡ mulME (toME g1) (toME y)
toME-hom-g1 g0  = refl
toME-hom-g1 g1  = refl
toME-hom-g1 g2  = refl
toME-hom-g1 g3  = refl
toME-hom-g1 g4  = refl
toME-hom-g1 g5  = refl
toME-hom-g1 g6  = refl
toME-hom-g1 g7  = refl
toME-hom-g1 g8  = refl
toME-hom-g1 g9  = refl
toME-hom-g1 g10 = refl
toME-hom-g1 g11 = refl
toME-hom-g1 g12 = refl
toME-hom-g1 g13 = refl
toME-hom-g1 g14 = refl
toME-hom-g1 g15 = refl
toME-hom-g1 g16 = refl
toME-hom-g1 g17 = refl
toME-hom-g1 g18 = refl
toME-hom-g1 g19 = refl
toME-hom-g1 g20 = refl
toME-hom-g1 g21 = refl
toME-hom-g1 g22 = refl
toME-hom-g1 g23 = refl

toME-hom-g2 : ∀ (y : SL23) → toME (g2 ⊗ y) ≡ mulME (toME g2) (toME y)
toME-hom-g2 g0  = refl
toME-hom-g2 g1  = refl
toME-hom-g2 g2  = refl
toME-hom-g2 g3  = refl
toME-hom-g2 g4  = refl
toME-hom-g2 g5  = refl
toME-hom-g2 g6  = refl
toME-hom-g2 g7  = refl
toME-hom-g2 g8  = refl
toME-hom-g2 g9  = refl
toME-hom-g2 g10 = refl
toME-hom-g2 g11 = refl
toME-hom-g2 g12 = refl
toME-hom-g2 g13 = refl
toME-hom-g2 g14 = refl
toME-hom-g2 g15 = refl
toME-hom-g2 g16 = refl
toME-hom-g2 g17 = refl
toME-hom-g2 g18 = refl
toME-hom-g2 g19 = refl
toME-hom-g2 g20 = refl
toME-hom-g2 g21 = refl
toME-hom-g2 g22 = refl
toME-hom-g2 g23 = refl

toME-hom-g3 : ∀ (y : SL23) → toME (g3 ⊗ y) ≡ mulME (toME g3) (toME y)
toME-hom-g3 g0  = refl
toME-hom-g3 g1  = refl
toME-hom-g3 g2  = refl
toME-hom-g3 g3  = refl
toME-hom-g3 g4  = refl
toME-hom-g3 g5  = refl
toME-hom-g3 g6  = refl
toME-hom-g3 g7  = refl
toME-hom-g3 g8  = refl
toME-hom-g3 g9  = refl
toME-hom-g3 g10 = refl
toME-hom-g3 g11 = refl
toME-hom-g3 g12 = refl
toME-hom-g3 g13 = refl
toME-hom-g3 g14 = refl
toME-hom-g3 g15 = refl
toME-hom-g3 g16 = refl
toME-hom-g3 g17 = refl
toME-hom-g3 g18 = refl
toME-hom-g3 g19 = refl
toME-hom-g3 g20 = refl
toME-hom-g3 g21 = refl
toME-hom-g3 g22 = refl
toME-hom-g3 g23 = refl

toME-hom-g4 : ∀ (y : SL23) → toME (g4 ⊗ y) ≡ mulME (toME g4) (toME y)
toME-hom-g4 g0  = refl
toME-hom-g4 g1  = refl
toME-hom-g4 g2  = refl
toME-hom-g4 g3  = refl
toME-hom-g4 g4  = refl
toME-hom-g4 g5  = refl
toME-hom-g4 g6  = refl
toME-hom-g4 g7  = refl
toME-hom-g4 g8  = refl
toME-hom-g4 g9  = refl
toME-hom-g4 g10 = refl
toME-hom-g4 g11 = refl
toME-hom-g4 g12 = refl
toME-hom-g4 g13 = refl
toME-hom-g4 g14 = refl
toME-hom-g4 g15 = refl
toME-hom-g4 g16 = refl
toME-hom-g4 g17 = refl
toME-hom-g4 g18 = refl
toME-hom-g4 g19 = refl
toME-hom-g4 g20 = refl
toME-hom-g4 g21 = refl
toME-hom-g4 g22 = refl
toME-hom-g4 g23 = refl

toME-hom-g5 : ∀ (y : SL23) → toME (g5 ⊗ y) ≡ mulME (toME g5) (toME y)
toME-hom-g5 g0  = refl
toME-hom-g5 g1  = refl
toME-hom-g5 g2  = refl
toME-hom-g5 g3  = refl
toME-hom-g5 g4  = refl
toME-hom-g5 g5  = refl
toME-hom-g5 g6  = refl
toME-hom-g5 g7  = refl
toME-hom-g5 g8  = refl
toME-hom-g5 g9  = refl
toME-hom-g5 g10 = refl
toME-hom-g5 g11 = refl
toME-hom-g5 g12 = refl
toME-hom-g5 g13 = refl
toME-hom-g5 g14 = refl
toME-hom-g5 g15 = refl
toME-hom-g5 g16 = refl
toME-hom-g5 g17 = refl
toME-hom-g5 g18 = refl
toME-hom-g5 g19 = refl
toME-hom-g5 g20 = refl
toME-hom-g5 g21 = refl
toME-hom-g5 g22 = refl
toME-hom-g5 g23 = refl

toME-hom-g6 : ∀ (y : SL23) → toME (g6 ⊗ y) ≡ mulME (toME g6) (toME y)
toME-hom-g6 g0  = refl
toME-hom-g6 g1  = refl
toME-hom-g6 g2  = refl
toME-hom-g6 g3  = refl
toME-hom-g6 g4  = refl
toME-hom-g6 g5  = refl
toME-hom-g6 g6  = refl
toME-hom-g6 g7  = refl
toME-hom-g6 g8  = refl
toME-hom-g6 g9  = refl
toME-hom-g6 g10 = refl
toME-hom-g6 g11 = refl
toME-hom-g6 g12 = refl
toME-hom-g6 g13 = refl
toME-hom-g6 g14 = refl
toME-hom-g6 g15 = refl
toME-hom-g6 g16 = refl
toME-hom-g6 g17 = refl
toME-hom-g6 g18 = refl
toME-hom-g6 g19 = refl
toME-hom-g6 g20 = refl
toME-hom-g6 g21 = refl
toME-hom-g6 g22 = refl
toME-hom-g6 g23 = refl

toME-hom-g7 : ∀ (y : SL23) → toME (g7 ⊗ y) ≡ mulME (toME g7) (toME y)
toME-hom-g7 g0  = refl
toME-hom-g7 g1  = refl
toME-hom-g7 g2  = refl
toME-hom-g7 g3  = refl
toME-hom-g7 g4  = refl
toME-hom-g7 g5  = refl
toME-hom-g7 g6  = refl
toME-hom-g7 g7  = refl
toME-hom-g7 g8  = refl
toME-hom-g7 g9  = refl
toME-hom-g7 g10 = refl
toME-hom-g7 g11 = refl
toME-hom-g7 g12 = refl
toME-hom-g7 g13 = refl
toME-hom-g7 g14 = refl
toME-hom-g7 g15 = refl
toME-hom-g7 g16 = refl
toME-hom-g7 g17 = refl
toME-hom-g7 g18 = refl
toME-hom-g7 g19 = refl
toME-hom-g7 g20 = refl
toME-hom-g7 g21 = refl
toME-hom-g7 g22 = refl
toME-hom-g7 g23 = refl

toME-hom-g8 : ∀ (y : SL23) → toME (g8 ⊗ y) ≡ mulME (toME g8) (toME y)
toME-hom-g8 g0  = refl
toME-hom-g8 g1  = refl
toME-hom-g8 g2  = refl
toME-hom-g8 g3  = refl
toME-hom-g8 g4  = refl
toME-hom-g8 g5  = refl
toME-hom-g8 g6  = refl
toME-hom-g8 g7  = refl
toME-hom-g8 g8  = refl
toME-hom-g8 g9  = refl
toME-hom-g8 g10 = refl
toME-hom-g8 g11 = refl
toME-hom-g8 g12 = refl
toME-hom-g8 g13 = refl
toME-hom-g8 g14 = refl
toME-hom-g8 g15 = refl
toME-hom-g8 g16 = refl
toME-hom-g8 g17 = refl
toME-hom-g8 g18 = refl
toME-hom-g8 g19 = refl
toME-hom-g8 g20 = refl
toME-hom-g8 g21 = refl
toME-hom-g8 g22 = refl
toME-hom-g8 g23 = refl

toME-hom-g9 : ∀ (y : SL23) → toME (g9 ⊗ y) ≡ mulME (toME g9) (toME y)
toME-hom-g9 g0  = refl
toME-hom-g9 g1  = refl
toME-hom-g9 g2  = refl
toME-hom-g9 g3  = refl
toME-hom-g9 g4  = refl
toME-hom-g9 g5  = refl
toME-hom-g9 g6  = refl
toME-hom-g9 g7  = refl
toME-hom-g9 g8  = refl
toME-hom-g9 g9  = refl
toME-hom-g9 g10 = refl
toME-hom-g9 g11 = refl
toME-hom-g9 g12 = refl
toME-hom-g9 g13 = refl
toME-hom-g9 g14 = refl
toME-hom-g9 g15 = refl
toME-hom-g9 g16 = refl
toME-hom-g9 g17 = refl
toME-hom-g9 g18 = refl
toME-hom-g9 g19 = refl
toME-hom-g9 g20 = refl
toME-hom-g9 g21 = refl
toME-hom-g9 g22 = refl
toME-hom-g9 g23 = refl

toME-hom-g10 : ∀ (y : SL23) → toME (g10 ⊗ y) ≡ mulME (toME g10) (toME y)
toME-hom-g10 g0  = refl
toME-hom-g10 g1  = refl
toME-hom-g10 g2  = refl
toME-hom-g10 g3  = refl
toME-hom-g10 g4  = refl
toME-hom-g10 g5  = refl
toME-hom-g10 g6  = refl
toME-hom-g10 g7  = refl
toME-hom-g10 g8  = refl
toME-hom-g10 g9  = refl
toME-hom-g10 g10 = refl
toME-hom-g10 g11 = refl
toME-hom-g10 g12 = refl
toME-hom-g10 g13 = refl
toME-hom-g10 g14 = refl
toME-hom-g10 g15 = refl
toME-hom-g10 g16 = refl
toME-hom-g10 g17 = refl
toME-hom-g10 g18 = refl
toME-hom-g10 g19 = refl
toME-hom-g10 g20 = refl
toME-hom-g10 g21 = refl
toME-hom-g10 g22 = refl
toME-hom-g10 g23 = refl

toME-hom-g11 : ∀ (y : SL23) → toME (g11 ⊗ y) ≡ mulME (toME g11) (toME y)
toME-hom-g11 g0  = refl
toME-hom-g11 g1  = refl
toME-hom-g11 g2  = refl
toME-hom-g11 g3  = refl
toME-hom-g11 g4  = refl
toME-hom-g11 g5  = refl
toME-hom-g11 g6  = refl
toME-hom-g11 g7  = refl
toME-hom-g11 g8  = refl
toME-hom-g11 g9  = refl
toME-hom-g11 g10 = refl
toME-hom-g11 g11 = refl
toME-hom-g11 g12 = refl
toME-hom-g11 g13 = refl
toME-hom-g11 g14 = refl
toME-hom-g11 g15 = refl
toME-hom-g11 g16 = refl
toME-hom-g11 g17 = refl
toME-hom-g11 g18 = refl
toME-hom-g11 g19 = refl
toME-hom-g11 g20 = refl
toME-hom-g11 g21 = refl
toME-hom-g11 g22 = refl
toME-hom-g11 g23 = refl

toME-hom-g12 : ∀ (y : SL23) → toME (g12 ⊗ y) ≡ mulME (toME g12) (toME y)
toME-hom-g12 g0  = refl
toME-hom-g12 g1  = refl
toME-hom-g12 g2  = refl
toME-hom-g12 g3  = refl
toME-hom-g12 g4  = refl
toME-hom-g12 g5  = refl
toME-hom-g12 g6  = refl
toME-hom-g12 g7  = refl
toME-hom-g12 g8  = refl
toME-hom-g12 g9  = refl
toME-hom-g12 g10 = refl
toME-hom-g12 g11 = refl
toME-hom-g12 g12 = refl
toME-hom-g12 g13 = refl
toME-hom-g12 g14 = refl
toME-hom-g12 g15 = refl
toME-hom-g12 g16 = refl
toME-hom-g12 g17 = refl
toME-hom-g12 g18 = refl
toME-hom-g12 g19 = refl
toME-hom-g12 g20 = refl
toME-hom-g12 g21 = refl
toME-hom-g12 g22 = refl
toME-hom-g12 g23 = refl

toME-hom-g13 : ∀ (y : SL23) → toME (g13 ⊗ y) ≡ mulME (toME g13) (toME y)
toME-hom-g13 g0  = refl
toME-hom-g13 g1  = refl
toME-hom-g13 g2  = refl
toME-hom-g13 g3  = refl
toME-hom-g13 g4  = refl
toME-hom-g13 g5  = refl
toME-hom-g13 g6  = refl
toME-hom-g13 g7  = refl
toME-hom-g13 g8  = refl
toME-hom-g13 g9  = refl
toME-hom-g13 g10 = refl
toME-hom-g13 g11 = refl
toME-hom-g13 g12 = refl
toME-hom-g13 g13 = refl
toME-hom-g13 g14 = refl
toME-hom-g13 g15 = refl
toME-hom-g13 g16 = refl
toME-hom-g13 g17 = refl
toME-hom-g13 g18 = refl
toME-hom-g13 g19 = refl
toME-hom-g13 g20 = refl
toME-hom-g13 g21 = refl
toME-hom-g13 g22 = refl
toME-hom-g13 g23 = refl

toME-hom-g14 : ∀ (y : SL23) → toME (g14 ⊗ y) ≡ mulME (toME g14) (toME y)
toME-hom-g14 g0  = refl
toME-hom-g14 g1  = refl
toME-hom-g14 g2  = refl
toME-hom-g14 g3  = refl
toME-hom-g14 g4  = refl
toME-hom-g14 g5  = refl
toME-hom-g14 g6  = refl
toME-hom-g14 g7  = refl
toME-hom-g14 g8  = refl
toME-hom-g14 g9  = refl
toME-hom-g14 g10 = refl
toME-hom-g14 g11 = refl
toME-hom-g14 g12 = refl
toME-hom-g14 g13 = refl
toME-hom-g14 g14 = refl
toME-hom-g14 g15 = refl
toME-hom-g14 g16 = refl
toME-hom-g14 g17 = refl
toME-hom-g14 g18 = refl
toME-hom-g14 g19 = refl
toME-hom-g14 g20 = refl
toME-hom-g14 g21 = refl
toME-hom-g14 g22 = refl
toME-hom-g14 g23 = refl

toME-hom-g15 : ∀ (y : SL23) → toME (g15 ⊗ y) ≡ mulME (toME g15) (toME y)
toME-hom-g15 g0  = refl
toME-hom-g15 g1  = refl
toME-hom-g15 g2  = refl
toME-hom-g15 g3  = refl
toME-hom-g15 g4  = refl
toME-hom-g15 g5  = refl
toME-hom-g15 g6  = refl
toME-hom-g15 g7  = refl
toME-hom-g15 g8  = refl
toME-hom-g15 g9  = refl
toME-hom-g15 g10 = refl
toME-hom-g15 g11 = refl
toME-hom-g15 g12 = refl
toME-hom-g15 g13 = refl
toME-hom-g15 g14 = refl
toME-hom-g15 g15 = refl
toME-hom-g15 g16 = refl
toME-hom-g15 g17 = refl
toME-hom-g15 g18 = refl
toME-hom-g15 g19 = refl
toME-hom-g15 g20 = refl
toME-hom-g15 g21 = refl
toME-hom-g15 g22 = refl
toME-hom-g15 g23 = refl

toME-hom-g16 : ∀ (y : SL23) → toME (g16 ⊗ y) ≡ mulME (toME g16) (toME y)
toME-hom-g16 g0  = refl
toME-hom-g16 g1  = refl
toME-hom-g16 g2  = refl
toME-hom-g16 g3  = refl
toME-hom-g16 g4  = refl
toME-hom-g16 g5  = refl
toME-hom-g16 g6  = refl
toME-hom-g16 g7  = refl
toME-hom-g16 g8  = refl
toME-hom-g16 g9  = refl
toME-hom-g16 g10 = refl
toME-hom-g16 g11 = refl
toME-hom-g16 g12 = refl
toME-hom-g16 g13 = refl
toME-hom-g16 g14 = refl
toME-hom-g16 g15 = refl
toME-hom-g16 g16 = refl
toME-hom-g16 g17 = refl
toME-hom-g16 g18 = refl
toME-hom-g16 g19 = refl
toME-hom-g16 g20 = refl
toME-hom-g16 g21 = refl
toME-hom-g16 g22 = refl
toME-hom-g16 g23 = refl

toME-hom-g17 : ∀ (y : SL23) → toME (g17 ⊗ y) ≡ mulME (toME g17) (toME y)
toME-hom-g17 g0  = refl
toME-hom-g17 g1  = refl
toME-hom-g17 g2  = refl
toME-hom-g17 g3  = refl
toME-hom-g17 g4  = refl
toME-hom-g17 g5  = refl
toME-hom-g17 g6  = refl
toME-hom-g17 g7  = refl
toME-hom-g17 g8  = refl
toME-hom-g17 g9  = refl
toME-hom-g17 g10 = refl
toME-hom-g17 g11 = refl
toME-hom-g17 g12 = refl
toME-hom-g17 g13 = refl
toME-hom-g17 g14 = refl
toME-hom-g17 g15 = refl
toME-hom-g17 g16 = refl
toME-hom-g17 g17 = refl
toME-hom-g17 g18 = refl
toME-hom-g17 g19 = refl
toME-hom-g17 g20 = refl
toME-hom-g17 g21 = refl
toME-hom-g17 g22 = refl
toME-hom-g17 g23 = refl

toME-hom-g18 : ∀ (y : SL23) → toME (g18 ⊗ y) ≡ mulME (toME g18) (toME y)
toME-hom-g18 g0  = refl
toME-hom-g18 g1  = refl
toME-hom-g18 g2  = refl
toME-hom-g18 g3  = refl
toME-hom-g18 g4  = refl
toME-hom-g18 g5  = refl
toME-hom-g18 g6  = refl
toME-hom-g18 g7  = refl
toME-hom-g18 g8  = refl
toME-hom-g18 g9  = refl
toME-hom-g18 g10 = refl
toME-hom-g18 g11 = refl
toME-hom-g18 g12 = refl
toME-hom-g18 g13 = refl
toME-hom-g18 g14 = refl
toME-hom-g18 g15 = refl
toME-hom-g18 g16 = refl
toME-hom-g18 g17 = refl
toME-hom-g18 g18 = refl
toME-hom-g18 g19 = refl
toME-hom-g18 g20 = refl
toME-hom-g18 g21 = refl
toME-hom-g18 g22 = refl
toME-hom-g18 g23 = refl

toME-hom-g19 : ∀ (y : SL23) → toME (g19 ⊗ y) ≡ mulME (toME g19) (toME y)
toME-hom-g19 g0  = refl
toME-hom-g19 g1  = refl
toME-hom-g19 g2  = refl
toME-hom-g19 g3  = refl
toME-hom-g19 g4  = refl
toME-hom-g19 g5  = refl
toME-hom-g19 g6  = refl
toME-hom-g19 g7  = refl
toME-hom-g19 g8  = refl
toME-hom-g19 g9  = refl
toME-hom-g19 g10 = refl
toME-hom-g19 g11 = refl
toME-hom-g19 g12 = refl
toME-hom-g19 g13 = refl
toME-hom-g19 g14 = refl
toME-hom-g19 g15 = refl
toME-hom-g19 g16 = refl
toME-hom-g19 g17 = refl
toME-hom-g19 g18 = refl
toME-hom-g19 g19 = refl
toME-hom-g19 g20 = refl
toME-hom-g19 g21 = refl
toME-hom-g19 g22 = refl
toME-hom-g19 g23 = refl

toME-hom-g20 : ∀ (y : SL23) → toME (g20 ⊗ y) ≡ mulME (toME g20) (toME y)
toME-hom-g20 g0  = refl
toME-hom-g20 g1  = refl
toME-hom-g20 g2  = refl
toME-hom-g20 g3  = refl
toME-hom-g20 g4  = refl
toME-hom-g20 g5  = refl
toME-hom-g20 g6  = refl
toME-hom-g20 g7  = refl
toME-hom-g20 g8  = refl
toME-hom-g20 g9  = refl
toME-hom-g20 g10 = refl
toME-hom-g20 g11 = refl
toME-hom-g20 g12 = refl
toME-hom-g20 g13 = refl
toME-hom-g20 g14 = refl
toME-hom-g20 g15 = refl
toME-hom-g20 g16 = refl
toME-hom-g20 g17 = refl
toME-hom-g20 g18 = refl
toME-hom-g20 g19 = refl
toME-hom-g20 g20 = refl
toME-hom-g20 g21 = refl
toME-hom-g20 g22 = refl
toME-hom-g20 g23 = refl

toME-hom-g21 : ∀ (y : SL23) → toME (g21 ⊗ y) ≡ mulME (toME g21) (toME y)
toME-hom-g21 g0  = refl
toME-hom-g21 g1  = refl
toME-hom-g21 g2  = refl
toME-hom-g21 g3  = refl
toME-hom-g21 g4  = refl
toME-hom-g21 g5  = refl
toME-hom-g21 g6  = refl
toME-hom-g21 g7  = refl
toME-hom-g21 g8  = refl
toME-hom-g21 g9  = refl
toME-hom-g21 g10 = refl
toME-hom-g21 g11 = refl
toME-hom-g21 g12 = refl
toME-hom-g21 g13 = refl
toME-hom-g21 g14 = refl
toME-hom-g21 g15 = refl
toME-hom-g21 g16 = refl
toME-hom-g21 g17 = refl
toME-hom-g21 g18 = refl
toME-hom-g21 g19 = refl
toME-hom-g21 g20 = refl
toME-hom-g21 g21 = refl
toME-hom-g21 g22 = refl
toME-hom-g21 g23 = refl

toME-hom-g22 : ∀ (y : SL23) → toME (g22 ⊗ y) ≡ mulME (toME g22) (toME y)
toME-hom-g22 g0  = refl
toME-hom-g22 g1  = refl
toME-hom-g22 g2  = refl
toME-hom-g22 g3  = refl
toME-hom-g22 g4  = refl
toME-hom-g22 g5  = refl
toME-hom-g22 g6  = refl
toME-hom-g22 g7  = refl
toME-hom-g22 g8  = refl
toME-hom-g22 g9  = refl
toME-hom-g22 g10 = refl
toME-hom-g22 g11 = refl
toME-hom-g22 g12 = refl
toME-hom-g22 g13 = refl
toME-hom-g22 g14 = refl
toME-hom-g22 g15 = refl
toME-hom-g22 g16 = refl
toME-hom-g22 g17 = refl
toME-hom-g22 g18 = refl
toME-hom-g22 g19 = refl
toME-hom-g22 g20 = refl
toME-hom-g22 g21 = refl
toME-hom-g22 g22 = refl
toME-hom-g22 g23 = refl

toME-hom-g23 : ∀ (y : SL23) → toME (g23 ⊗ y) ≡ mulME (toME g23) (toME y)
toME-hom-g23 g0  = refl
toME-hom-g23 g1  = refl
toME-hom-g23 g2  = refl
toME-hom-g23 g3  = refl
toME-hom-g23 g4  = refl
toME-hom-g23 g5  = refl
toME-hom-g23 g6  = refl
toME-hom-g23 g7  = refl
toME-hom-g23 g8  = refl
toME-hom-g23 g9  = refl
toME-hom-g23 g10 = refl
toME-hom-g23 g11 = refl
toME-hom-g23 g12 = refl
toME-hom-g23 g13 = refl
toME-hom-g23 g14 = refl
toME-hom-g23 g15 = refl
toME-hom-g23 g16 = refl
toME-hom-g23 g17 = refl
toME-hom-g23 g18 = refl
toME-hom-g23 g19 = refl
toME-hom-g23 g20 = refl
toME-hom-g23 g21 = refl
toME-hom-g23 g22 = refl
toME-hom-g23 g23 = refl

toME-hom : ∀ (x y : SL23) → toME (x ⊗ y) ≡ mulME (toME x) (toME y)
toME-hom g0  y = toME-hom-g0 y
toME-hom g1  y = toME-hom-g1 y
toME-hom g2  y = toME-hom-g2 y
toME-hom g3  y = toME-hom-g3 y
toME-hom g4  y = toME-hom-g4 y
toME-hom g5  y = toME-hom-g5 y
toME-hom g6  y = toME-hom-g6 y
toME-hom g7  y = toME-hom-g7 y
toME-hom g8  y = toME-hom-g8 y
toME-hom g9  y = toME-hom-g9 y
toME-hom g10 y = toME-hom-g10 y
toME-hom g11 y = toME-hom-g11 y
toME-hom g12 y = toME-hom-g12 y
toME-hom g13 y = toME-hom-g13 y
toME-hom g14 y = toME-hom-g14 y
toME-hom g15 y = toME-hom-g15 y
toME-hom g16 y = toME-hom-g16 y
toME-hom g17 y = toME-hom-g17 y
toME-hom g18 y = toME-hom-g18 y
toME-hom g19 y = toME-hom-g19 y
toME-hom g20 y = toME-hom-g20 y
toME-hom g21 y = toME-hom-g21 y
toME-hom g22 y = toME-hom-g22 y
toME-hom g23 y = toME-hom-g23 y

--------------------------------------------------------------------------------
-- §10 结论：双线性 Schur 四件套
--------------------------------------------------------------------------------

record BilinearSchur2A4 : Set where
  field
    card            : ℕ
    card-ok         : card ≡ 24
    representation  : ∀ (x y : SL23) → toME (x ⊗ y) ≡ mulME (toME x) (toME y)
    reduction       : ∀ (x : SL23) → redM (toME x) ≡ toMat x
    schur           : ∀ (i j k l : Fin 2)
                    → schurLHS i j k l ≡ mulZω twelveZ (mulZω (εZ i k) (εZ j l))
    frobenius       : fsNum ≡ negZω twentyFourZ
    hermitian-break : hermitianSum00 ≢ twelveZ

bilinearSchur2A4 : BilinearSchur2A4
bilinearSchur2A4 = record
  { card            = card-SL23
  ; card-ok         = refl
  ; representation  = toME-hom
  ; reduction       = redM-toME
  ; schur           = bilinearSchur
  ; frobenius       = frobeniusSchur
  ; hermitian-break = hermitianNotSchur
  }
