{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Synthesis.A4.CharTable2A4
--
-- **2A₄ = SL(2,F₃) 的 7 个不可约特征标表 + 49 对正交性**（Z[ω] 精确）
--
-- 类序 = **计算序**（与 sov-math `Sov.Math.Rep2A4` 同一序）：由 24 个元素做
-- 矩阵共轭算出 7 类，类的编号 = 在 g0..g23 中首次出现的次序：
--     κ0 = {6 元, 阶 4}    κ1 = {4 元, 阶 6}    κ2 = {4 元, 阶 3}
--     κ3 = {4 元, 阶 6}    κ4 = {4 元, 阶 3}    κ5 = {I}    κ6 = {−I}
--   6+4+4+4+4+1+1 = 24 ✓（`classSizes-total`）
--
-- 表的 7 行（与 sov-math `Rep2A4.allChars` 同一张表，本文件重算并定理化）：
--     i1 / i1' / i1''   三个 1 维（经 A₄ ≅ SL23/{±I} 分解 ⇒ 非忠实）
--     i2 / i2' / i2''   三个 2 维旋量型（在 −I 上取 −2 ⇒ **忠实**）
--     i3                A₄ 的 3 维（非忠实）
--   维数 1+1+1+4+4+4+9 = 24 = |2A₄| ✓（`irrDimSqSum`）
--
-- 正交性（未归一：Z[ω] 中 24 不可逆，故写 Σ_g chi2A4ᵢ(g)·conj chi2A4ⱼ(g) = 24·δᵢⱼ）：
--     charSum-diag : ∀ r → charSum r r ≡ 24          （7 条）
--     charSum-off  : ∀ r s → r ≢ s → charSum r s ≡ 0 （42 条）
--
-- ⚠ 边界（必读，§10 详列）：本文件证的是**函数层面**的完整正交性 + 维数恒等式 +
--   正则多重度。它**不**单独构成「7 个不可约表示」：i2 的表示论来源已证
--   （`BilinearSchur2A4.toME-hom`），i1/i1'/i1''/i3 与 i2'/i2'' 的来源分别是
--   "toA4 是同态"（576 案）与"张量积"，类函数性质还差 SL23 的逆——都未做。
--
-- 0 postulate / 0 hole；全枚举，零浮点。
module Sovereign.Synthesis.A4.CharTable2A4 where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Integer using (ℤ; +_; -[1+_])
open import Data.List using (List; _∷_; []; foldr)
open import Data.Nat using (ℕ; _+_; _*_)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong; cong₂)

open import Sovereign.Synthesis.A4.A4Representation
  using (Zω; mkZω; zeroZω; addZω; mulZω; conjZω)
open import Sovereign.Synthesis.A4.BilinearSchur2A4
  using (toME; traceME; allSL23; sumSL23; twentyFourZ)
open import Sovereign.Synthesis.A4.BinaryTetrahedralDefiningRep
  using (SL23; g0; g1; g2; g3; g4; g5; g6; g7; g8; g9; g10; g11
        ; g12; g13; g14; g15; g16; g17; g18; g19; g20; g21; g22; g23)

--------------------------------------------------------------------------------
-- §1 类与不可约表示的索引类型（具名构造子，避免 Fin 数字索引的错配风险）
--------------------------------------------------------------------------------

data Cls : Set where
  κ0 κ1 κ2 κ3 κ4 κ5 κ6 : Cls

data Irr : Set where
  i1 i1' i1'' i2 i2' i2'' i3 : Irr

-- 表里出现的 10 个 Z[ω] 值
ez0 ez1 ezm1 ez2 ezm2 ez3 ezw ezw2 ezmw ez1w : Zω
ez0  = mkZω (+ 0) (+ 0)              -- 0
ez1  = mkZω (+ 1) (+ 0)              -- 1
ezm1 = mkZω (-[1+ 0 ]) (+ 0)         -- −1
ez2  = mkZω (+ 2) (+ 0)              -- 2
ezm2 = mkZω (-[1+ 1 ]) (+ 0)         -- −2
ez3  = mkZω (+ 3) (+ 0)              -- 3
ezw  = mkZω (+ 0) (+ 1)              -- ω
ezw2 = mkZω (-[1+ 0 ]) (-[1+ 0 ])    -- ω² = −1−ω
ezmw = mkZω (+ 0) (-[1+ 0 ])         -- −ω
ez1w = mkZω (+ 1) (+ 1)              -- 1+ω

-- twentyFourZ（= |G|）与 allSL23 / sumSL23 直接复用 BilinearSchur2A4（不重复定义）

--------------------------------------------------------------------------------
-- §2 元素 → 类（24 案）与类的大小 / 元素阶
--------------------------------------------------------------------------------

classOf2A4 : SL23 → Cls
classOf2A4 g0  = κ0
classOf2A4 g1  = κ1
classOf2A4 g2  = κ2
classOf2A4 g3  = κ0
classOf2A4 g4  = κ3
classOf2A4 g5  = κ4
classOf2A4 g6  = κ5
classOf2A4 g7  = κ4
classOf2A4 g8  = κ2
classOf2A4 g9  = κ2
classOf2A4 g10 = κ0
classOf2A4 g11 = κ1
classOf2A4 g12 = κ4
classOf2A4 g13 = κ3
classOf2A4 g14 = κ0
classOf2A4 g15 = κ6
classOf2A4 g16 = κ3
classOf2A4 g17 = κ1
classOf2A4 g18 = κ1
classOf2A4 g19 = κ0
classOf2A4 g20 = κ2
classOf2A4 g21 = κ3
classOf2A4 g22 = κ4
classOf2A4 g23 = κ0

classSizes : Cls → ℕ
classSizes κ0 = 6
classSizes κ1 = 4
classSizes κ2 = 4
classSizes κ3 = 4
classSizes κ4 = 4
classSizes κ5 = 1
classSizes κ6 = 1

classOrders : Cls → ℕ
classOrders κ0 = 4
classOrders κ1 = 6
classOrders κ2 = 3
classOrders κ3 = 6
classOrders κ4 = 3
classOrders κ5 = 1
classOrders κ6 = 2

classSizes-total : classSizes κ0 + classSizes κ1 + classSizes κ2 + classSizes κ3
                 + classSizes κ4 + classSizes κ5 + classSizes κ6 ≡ 24
classSizes-total = refl

-- 类的 (大小, 元素阶) 签名 = sov-math `classInfoC`
classSig : Cls → ℕ × ℕ
classSig κ0 = (6 , 4)
classSig κ1 = (4 , 6)
classSig κ2 = (4 , 3)
classSig κ3 = (4 , 6)
classSig κ4 = (4 , 3)
classSig κ5 = (1 , 1)
classSig κ6 = (1 , 2)

classSignatureOk : (classSig κ0 ≡ (6 , 4)) × (classSig κ1 ≡ (4 , 6))
                 × (classSig κ2 ≡ (4 , 3)) × (classSig κ3 ≡ (4 , 6))
                 × (classSig κ4 ≡ (4 , 3)) × (classSig κ5 ≡ (1 , 1))
                 × (classSig κ6 ≡ (1 , 2))
classSignatureOk = refl , refl , refl , refl , refl , refl , refl

--------------------------------------------------------------------------------
-- §3 特征标表（7 行 × 7 列）
--
-- 每行 = 一个不可约特征标在 7 个类上的取值（同 sov-math `allChars`）。
-- i2 的取值不是抄表：它是 §4 的显式 Z[ω] 矩阵模型 `toME` 的迹
-- （阶 1↦2, 2↦−2, 4↦0, 3↦−1, 6↦1 —— 见 BilinearSchur2A4 §2）。
-- i1'/i1''/i3 的取值按 A₄ 的 1 维/3 维经 toA4 拉回；i2'/i2'' = i2 ⊗ i1'/i1''。
--------------------------------------------------------------------------------

charOf : Irr → Cls → Zω

-- i1：平凡
charOf i1 κ0 = ez1
charOf i1 κ1 = ez1
charOf i1 κ2 = ez1
charOf i1 κ3 = ez1
charOf i1 κ4 = ez1
charOf i1 κ5 = ez1
charOf i1 κ6 = ez1

-- i1′：在第一个 3 阶类 κ2 上取 ω（钉死标签，与 sov-math `nontrivialHomsSorted` 一致）
charOf i1' κ0 = ez1
charOf i1' κ1 = ezw2
charOf i1' κ2 = ezw
charOf i1' κ3 = ezw
charOf i1' κ4 = ezw2
charOf i1' κ5 = ez1
charOf i1' κ6 = ez1

-- i1″
charOf i1'' κ0 = ez1
charOf i1'' κ1 = ezw
charOf i1'' κ2 = ezw2
charOf i1'' κ3 = ezw2
charOf i1'' κ4 = ezw
charOf i1'' κ5 = ez1
charOf i1'' κ6 = ez1

-- i2：旋量定义表示（24 个元素的迹）
charOf i2 κ0 = ez0
charOf i2 κ1 = ez1
charOf i2 κ2 = ezm1
charOf i2 κ3 = ez1
charOf i2 κ4 = ezm1
charOf i2 κ5 = ez2
charOf i2 κ6 = ezm2

-- i2′ = i2 ⊗ i1′
charOf i2' κ0 = ez0
charOf i2' κ1 = ezw2
charOf i2' κ2 = ezmw
charOf i2' κ3 = ezw
charOf i2' κ4 = ez1w
charOf i2' κ5 = ez2
charOf i2' κ6 = ezm2

-- i2″ = i2 ⊗ i1″
charOf i2'' κ0 = ez0
charOf i2'' κ1 = ezw
charOf i2'' κ2 = ez1w
charOf i2'' κ3 = ezw2
charOf i2'' κ4 = ezmw
charOf i2'' κ5 = ez2
charOf i2'' κ6 = ezm2

-- i3：A₄ 的 3 维拉回（阶 1,2 ↦ 3；4 ↦ −1；3,6 ↦ 0）
charOf i3 κ0 = ezm1
charOf i3 κ1 = ez0
charOf i3 κ2 = ez0
charOf i3 κ3 = ez0
charOf i3 κ4 = ez0
charOf i3 κ5 = ez3
charOf i3 κ6 = ez3

--------------------------------------------------------------------------------
-- §4 群上的特征标与未归一内积
--------------------------------------------------------------------------------

chi2A4 : Irr → SL23 → Zω
chi2A4 r g = charOf r (classOf2A4 g)

-- | 未归一内积：24·⟨chi2A4ᵢ,chi2A4ⱼ⟩ = Σ_g chi2A4ᵢ(g)·conj chi2A4ⱼ(g)
charSum : Irr → Irr → Zω
charSum r s = sumSL23 (λ g → mulZω (chi2A4 r g) (conjZω (chi2A4 s g)))

--------------------------------------------------------------------------------
-- §4.5 i2 的表示论来源：它就是显式 Z[ω] 矩阵模型的迹
--
--   表里 i2 那一行**不是抄来的数据**：逐元素核对
--     charOf i2 (classOf2A4 x) ≡ traceME (toME x)
--   （24 案）。右侧来自 `BilinearSchur2A4` 的 24 个 Z[ω] 矩阵，其乘法同态性
--   已由 `toME-hom`（576 对）证明 ⇒ i2 是真正 2 维表示的迹。
--   其余 6 行的表示论来源仍未证（见 §10）。
--------------------------------------------------------------------------------

spinorFromModel : ∀ (x : SL23) → charOf i2 (classOf2A4 x) ≡ traceME (toME x)
spinorFromModel g0  = refl
spinorFromModel g1  = refl
spinorFromModel g2  = refl
spinorFromModel g3  = refl
spinorFromModel g4  = refl
spinorFromModel g5  = refl
spinorFromModel g6  = refl
spinorFromModel g7  = refl
spinorFromModel g8  = refl
spinorFromModel g9  = refl
spinorFromModel g10 = refl
spinorFromModel g11 = refl
spinorFromModel g12 = refl
spinorFromModel g13 = refl
spinorFromModel g14 = refl
spinorFromModel g15 = refl
spinorFromModel g16 = refl
spinorFromModel g17 = refl
spinorFromModel g18 = refl
spinorFromModel g19 = refl
spinorFromModel g20 = refl
spinorFromModel g21 = refl
spinorFromModel g22 = refl
spinorFromModel g23 = refl

--------------------------------------------------------------------------------
-- §5 正交性：49 = 7（对角）+ 42（非对角）
--------------------------------------------------------------------------------

charSum-diag : ∀ (r : Irr) → charSum r r ≡ twentyFourZ
charSum-diag i1   = refl
charSum-diag i1'  = refl
charSum-diag i1'' = refl
charSum-diag i2   = refl
charSum-diag i2'  = refl
charSum-diag i2'' = refl
charSum-diag i3   = refl

charSum-off-i1 : ∀ (s : Irr) → i1 ≢ s → charSum i1 s ≡ zeroZω
charSum-off-i1 i1  h = ⊥-elim (h refl)
charSum-off-i1 i1' h = refl
charSum-off-i1 i1'' h = refl
charSum-off-i1 i2  h = refl
charSum-off-i1 i2' h = refl
charSum-off-i1 i2'' h = refl
charSum-off-i1 i3  h = refl

charSum-off-i1' : ∀ (s : Irr) → i1' ≢ s → charSum i1' s ≡ zeroZω
charSum-off-i1' i1  h = refl
charSum-off-i1' i1' h = ⊥-elim (h refl)
charSum-off-i1' i1'' h = refl
charSum-off-i1' i2  h = refl
charSum-off-i1' i2' h = refl
charSum-off-i1' i2'' h = refl
charSum-off-i1' i3  h = refl

charSum-off-i1'' : ∀ (s : Irr) → i1'' ≢ s → charSum i1'' s ≡ zeroZω
charSum-off-i1'' i1  h = refl
charSum-off-i1'' i1' h = refl
charSum-off-i1'' i1'' h = ⊥-elim (h refl)
charSum-off-i1'' i2  h = refl
charSum-off-i1'' i2' h = refl
charSum-off-i1'' i2'' h = refl
charSum-off-i1'' i3  h = refl

charSum-off-i2 : ∀ (s : Irr) → i2 ≢ s → charSum i2 s ≡ zeroZω
charSum-off-i2 i1  h = refl
charSum-off-i2 i1' h = refl
charSum-off-i2 i1'' h = refl
charSum-off-i2 i2  h = ⊥-elim (h refl)
charSum-off-i2 i2' h = refl
charSum-off-i2 i2'' h = refl
charSum-off-i2 i3  h = refl

charSum-off-i2' : ∀ (s : Irr) → i2' ≢ s → charSum i2' s ≡ zeroZω
charSum-off-i2' i1  h = refl
charSum-off-i2' i1' h = refl
charSum-off-i2' i1'' h = refl
charSum-off-i2' i2  h = refl
charSum-off-i2' i2' h = ⊥-elim (h refl)
charSum-off-i2' i2'' h = refl
charSum-off-i2' i3  h = refl

charSum-off-i2'' : ∀ (s : Irr) → i2'' ≢ s → charSum i2'' s ≡ zeroZω
charSum-off-i2'' i1  h = refl
charSum-off-i2'' i1' h = refl
charSum-off-i2'' i1'' h = refl
charSum-off-i2'' i2  h = refl
charSum-off-i2'' i2' h = refl
charSum-off-i2'' i2'' h = ⊥-elim (h refl)
charSum-off-i2'' i3  h = refl

charSum-off-i3 : ∀ (s : Irr) → i3 ≢ s → charSum i3 s ≡ zeroZω
charSum-off-i3 i1  h = refl
charSum-off-i3 i1' h = refl
charSum-off-i3 i1'' h = refl
charSum-off-i3 i2  h = refl
charSum-off-i3 i2' h = refl
charSum-off-i3 i2'' h = refl
charSum-off-i3 i3  h = ⊥-elim (h refl)

charSum-off : ∀ (r s : Irr) → r ≢ s → charSum r s ≡ zeroZω
charSum-off i1   = charSum-off-i1
charSum-off i1'  = charSum-off-i1'
charSum-off i1'' = charSum-off-i1''
charSum-off i2   = charSum-off-i2
charSum-off i2'  = charSum-off-i2'
charSum-off i2'' = charSum-off-i2''
charSum-off i3   = charSum-off-i3

--------------------------------------------------------------------------------
-- §6 维数与 Σ d_ρ² = |G|
--------------------------------------------------------------------------------

irrDim : Irr → ℕ
irrDim i1   = 1
irrDim i1'  = 1
irrDim i1'' = 1
irrDim i2   = 2
irrDim i2'  = 2
irrDim i2'' = 2
irrDim i3   = 3

-- 维数 = 单位元类 κ5 上的取值（不是另设数据，而是表的一列）
irrDim-agrees : ∀ (r : Irr) → charOf r κ5 ≡ mkZω (+ irrDim r) (+ 0)
irrDim-agrees i1   = refl
irrDim-agrees i1'  = refl
irrDim-agrees i1'' = refl
irrDim-agrees i2   = refl
irrDim-agrees i2'  = refl
irrDim-agrees i2'' = refl
irrDim-agrees i3   = refl

irrDimSqSum : irrDim i1 * irrDim i1 + irrDim i1' * irrDim i1' + irrDim i1'' * irrDim i1''
         + irrDim i2 * irrDim i2 + irrDim i2' * irrDim i2' + irrDim i2'' * irrDim i2''
         + irrDim i3 * irrDim i3 ≡ 24
irrDimSqSum = refl

--------------------------------------------------------------------------------
-- §7 正则表示：chi2A4_reg = 24·δ_I ⇒ 每个不可约表示出现 d_ρ 次
--
--   Σ_g chi2A4_reg(g)·conj chi2A4_ρ(g) = 24·conj chi2A4_ρ(I) = 24·d_ρ（chi2A4 在 I 上取实值）
--------------------------------------------------------------------------------

regChar : SL23 → Zω
regChar g0  = zeroZω
regChar g1  = zeroZω
regChar g2  = zeroZω
regChar g3  = zeroZω
regChar g4  = zeroZω
regChar g5  = zeroZω
regChar g6  = twentyFourZ
regChar g7  = zeroZω
regChar g8  = zeroZω
regChar g9  = zeroZω
regChar g10 = zeroZω
regChar g11 = zeroZω
regChar g12 = zeroZω
regChar g13 = zeroZω
regChar g14 = zeroZω
regChar g15 = zeroZω
regChar g16 = zeroZω
regChar g17 = zeroZω
regChar g18 = zeroZω
regChar g19 = zeroZω
regChar g20 = zeroZω
regChar g21 = zeroZω
regChar g22 = zeroZω
regChar g23 = zeroZω

regMult : Irr → Zω
regMult r = sumSL23 (λ g → mulZω (regChar g) (conjZω (chi2A4 r g)))

regMult-spec : ∀ (r : Irr) → regMult r ≡ mkZω (+ (24 * irrDim r)) (+ 0)
regMult-spec i1   = refl
regMult-spec i1'  = refl
regMult-spec i1'' = refl
regMult-spec i2   = refl
regMult-spec i2'  = refl
regMult-spec i2'' = refl
regMult-spec i3   = refl

--------------------------------------------------------------------------------
-- §8 结论记录
--------------------------------------------------------------------------------

record CharTable2A4 : Set where
  field
    classes          : SL23 → Cls
    class-sizes      : Cls → ℕ
    class-sizes-sum  : classSizes κ0 + classSizes κ1 + classSizes κ2 + classSizes κ3
                     + classSizes κ4 + classSizes κ5 + classSizes κ6 ≡ 24
    class-signature  : (classSig κ0 ≡ (6 , 4)) × (classSig κ1 ≡ (4 , 6))
                     × (classSig κ2 ≡ (4 , 3)) × (classSig κ3 ≡ (4 , 6))
                     × (classSig κ4 ≡ (4 , 3)) × (classSig κ5 ≡ (1 , 1))
                     × (classSig κ6 ≡ (1 , 2))
    orthonormal-diag : ∀ (r : Irr) → charSum r r ≡ twentyFourZ
    orthonormal-off  : ∀ (r s : Irr) → r ≢ s → charSum r s ≡ zeroZω
    dims-agree       : ∀ (r : Irr) → charOf r κ5 ≡ mkZω (+ irrDim r) (+ 0)
    irrDim-sq-sum       : irrDim i1 * irrDim i1 + irrDim i1' * irrDim i1' + irrDim i1'' * irrDim i1''
                     + irrDim i2 * irrDim i2 + irrDim i2' * irrDim i2' + irrDim i2'' * irrDim i2''
                     + irrDim i3 * irrDim i3 ≡ 24
    regular-mult     : ∀ (r : Irr) → regMult r ≡ mkZω (+ (24 * irrDim r)) (+ 0)

charTable2A4 : CharTable2A4
charTable2A4 = record
  { classes          = classOf2A4
  ; class-sizes      = classSizes
  ; class-sizes-sum  = classSizes-total
  ; class-signature  = classSignatureOk
  ; orthonormal-diag = charSum-diag
  ; orthonormal-off  = charSum-off
  ; dims-agree       = irrDim-agrees
  ; irrDim-sq-sum       = irrDimSqSum
  ; regular-mult     = regMult-spec
  }

--------------------------------------------------------------------------------
-- §9 与 sov-math 的对照
--
--   sov-math `Rep2A4.classInfoC` = [(6,4),(4,6),(4,3),(4,6),(4,3),(1,1),(1,2)]
--   ⇒ 本文件 classSig 逐项相同（同一计算序）。
--   sov-math `allCharsOrthogonal`（Bool，24 元上穷举）是本文件 §5 的非形式对应物；
--   本文件把它变成 49 条定理，并把 `regularMultiplicityOk` 变成 regMult-spec。
--
-- §10 未做（不要当成已证）
--   (a) ✅ 已闭合（2026-10-27）：`ToA4Hom.toA4-hom`（576 对）+ `CharProvenance`
--       把 i1/i1'/i1''/i3 与 i2'/i2'' 全部落地为**已证表示的迹**。
--   (b) ✅ 已闭合：i2'/i2'' = 1 维表示与旋量的标量乘（`CharProvenance.ρ2a/ρ2b`），
--       乘法性用 Z[ω] 环律证明，不是枚举。
--   (c) 类函数性质 chi2A4(hgh⁻¹) = chi2A4(g)：**未做**——库里没有 SL23 的逆 ⇒
--       需 invSL（24 案）+ 双侧逆律（各 24 案）+ 共轭不变（576 案）。
--   (d) 不可约性的**内部判据**：⟨chi2A4,chi2A4⟩ = 24（= |G|）是必要且（配合 (a)(b)
--       的表示来源）充分；若要从表示内部直接判（不自称判据），仍需子系统/内积结构。
--------------------------------------------------------------------------------
