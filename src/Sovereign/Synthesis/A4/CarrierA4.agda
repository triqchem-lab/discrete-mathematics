{-# OPTIONS --cubical --guardedness --rewriting #-}

-- | Sovereign.Synthesis.A4.CarrierA4
-- 内核载体 = C[A₄]（A₄ 上的函数空间，12 维）+ **Plancherel 内积**
--
-- 定位（2026-10-26 人类裁定）：载体是**函数空间**，不是点集，也不是点积几何。
--
--   载体      Carrier = A₄ → Z[ω]                      —— 12 维（= |A₄|）
--   内积      dot f g = Σ_{x∈A₄} f x · conj(g x)        —— Plancherel（未归一，×12）
--   分解      C[A₄] = ⊕_ρ ρ^{⊕ d_ρ}，Plancherel 恒等式 Σ_ρ d_ρ² = |A₄| = 12
--   忠实性    正则表示含**全部**不可约表示（各 d_ρ 次）⇒ 最小忠实载体
--
-- 为什么必须是 C[A₄] 而不是 Z/12：
--   · Z/12 交换 ⇒ 只有 1 维不可约表示 ⇒ **矢量表示不存在**（"矢量"退化成一堆标量）；
--   · C[A₄] 的正则表示含 1, 1′, 1″, 3 四者 ⇒ 其中 3 维的 R3 是 A₄ 唯一的忠实不可约
--     （三个 1 维表示都经 A₄/V₄ ≅ C₃ 分解，非忠实 —— 见 A4OneDimHom）。
--
-- 归一化约定（与 PlancherelTheorem 一致）：
--   12 在 Z[ω] 中不可逆，故本模块只给**未归一**配对 dot（= 12·⟨f,g⟩），
--   整数形式的 Parseval 写作 12·⟨f,g⟩ 的等式，不引入分母。
--
-- 0 postulate / 0 hole。全部为定义 + 结构恒等式。

module Sovereign.Synthesis.A4.CarrierA4 where

open import Data.List using (List; _∷_; []; foldr; map)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
open import Data.Fin using (Fin; zero; suc)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂)

open import Sovereign.Synthesis.A4.A4Group using (A4; Id; Rot; Flip)
open import Sovereign.Synthesis.A4.A4Representation
  using (Zω; zeroZω; oneZω; addZω; mulZω; conjZω)

--------------------------------------------------------------------------------
-- 1. 载体：A₄ 上的函数空间（12 维自由 Z[ω]-模）
--------------------------------------------------------------------------------

Carrier : Set
Carrier = A4 → Zω

-- |A₄| = 1（Id）+ 4×2（绕四顶点的 ±120°）+ 3（绕对边中点的 180°）= 12
-- 形状写成 1 + 4*2 + 3 而不是裸 12：三个加数分别是三类共轭类，结构在表达式里。
card-A4 : ℕ
card-A4 = 1 + 4 * 2 + 3

card-A4-correct : card-A4 ≡ 12
card-A4-correct = refl

-- 函数空间维数 = 群阶（自由模的秩）
dim-carrier : ℕ
dim-carrier = card-A4

--------------------------------------------------------------------------------
-- 2. Plancherel 内积（未归一）：dot f g = Σ_x f x · conj (g x)
--
-- sumA4 逐构造子展开 = 群上的 Haar 求和（12 项，无权重：A₄ 有限、离散 Haar 全 1）
--------------------------------------------------------------------------------

sumA4 : Carrier → Zω
sumA4 f = foldr addZω zeroZω (map f allA4List)
  where
    allA4List : List A4
    allA4List =
      Id ∷ Rot zero zero ∷ Rot zero (suc zero) ∷
      Rot (suc zero) zero ∷ Rot (suc zero) (suc zero) ∷
      Rot (suc (suc zero)) zero ∷ Rot (suc (suc zero)) (suc zero) ∷
      Rot (suc (suc (suc zero))) zero ∷ Rot (suc (suc (suc zero))) (suc zero) ∷
      Flip zero ∷ Flip (suc zero) ∷ Flip (suc (suc zero)) ∷ []

dot : Carrier → Carrier → Zω
dot f g = sumA4 (λ x → mulZω (f x) (conjZω (g x)))

-- 归一化配对（符号层面记录，不实现）：ip f g = (1/12) · dot f g
-- 12 ∤ Z[ω] ⇒ 不引入分母；需要归一化的定理一律写成 12 · ip ≡ dot。

--------------------------------------------------------------------------------
-- 3. 分解：C[A₄] = ⊕_ρ ρ^{⊕ d_ρ}，Σ_ρ d_ρ² = |A₄|
--------------------------------------------------------------------------------

data Irrep : Set where
  R1  : Irrep   -- 平凡（1 维，非忠实）
  R1' : Irrep   -- ω 特征（1 维，非忠实）
  R1'' : Irrep  -- ω² 特征（1 维，非忠实）
  R3  : Irrep   -- 三维标准表示（**唯一忠实不可约**）

dimI : Irrep → ℕ
dimI R1   = 1
dimI R1'  = 1
dimI R1'' = 1
dimI R3   = 3

square : ℕ → ℕ
square n = n * n

-- Plancherel 恒等式：Σ_ρ d_ρ² = |A₄|
-- 这是"正则表示含每个不可约表示 d_ρ 次"的维数形式，
-- 也是"12 维函数空间正好被 4 个不可约表示用满"的判据。
plancherel : square (dimI R1) + square (dimI R1') + square (dimI R1'') + square (dimI R3)
           ≡ card-A4
plancherel = refl

-- 不可约表示数 = 共轭类数 = 4（A4Representation 的特征标表按 4 类给出）
irrep-count : ℕ
irrep-count = 4

-- 唯一的忠实不可约是 R3：其余三个维度为 1，且全部经 A₄/V₄ ≅ C₃ 分解
-- （A4OneDimHom 已证：三个 1 维表示由 abelianization A₄ → C₃ 的 ω 幂导出）。
vector-irrep : Irrep
vector-irrep = R3

vector-irrep-dim : dimI vector-irrep ≡ 3
vector-irrep-dim = refl
