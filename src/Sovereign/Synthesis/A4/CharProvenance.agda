{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Synthesis.A4.CharProvenance
--
-- **7 行特征标表全部落地为"某表示的迹"**（2A₄ = SL(2,F₃)）
--
-- `CharTable2A4` 给的是表 + 49 对正交性；当时只有 i2 有表示论来源。
-- 本文件把剩下的 6 行补齐，于是"7 个不可约表示"不再是命名约定：
--
--   行     表示                                    来源
--   ────  ──────────────────────────────────────  ─────────────────────────────
--   i1    平凡 1 维  ψ1  ≡ ρ1                     A4OneDimHom.ρ1（常数 1）
--   i1''  ψ_a = ρ1' = powerω ∘ ab                 A4OneDimHom.rho1'-hom（已证）
--   i1'   ψ_b = powerω ∘ neg3 ∘ ab                §3 现证（neg3 对 add3 的分配 + ab-hom）
--   i2    ρ2 = toME（2 维旋量）                    BilinearSchur2A4.toME-hom（576 对）
--   i2'   ρ2b = (ψ_b ∘ toA4) • ρ2                  §5 标量乘：scaleM-hom + 迹线性
--   i2''  ρ2a = (ψ_a ∘ toA4) • ρ2                  §5 同上
--   i3    ρ3（A₄ 的 3 维，V₀ 限制）                 A4ThreeDimRep.rho3-hom（12 行引理）
--
-- 表行与表示的逐点一致 = §6 的 6 组 24 案 refl（i2 已由 CharTable2A4.spinorFromModel 给出）。
-- 于是每行的"是某表示的迹"都成立，且 1 维那三行还各自是**乘法特征标**。
--
-- 命名对照（⚠ 与直觉相反，实测确认）：
--   表中标 i1′ 的，是 ψ_b（ρ1′ 的共轭/逆）；标 i1″ 的才是 A4OneDimHom.ρ1′。
--   CharTable2A4 的标签是按"第一个 3 阶类上取 ω"钉死的，与 A4OneDimHom 的 ab 表不同源。
--
-- 0 postulate / 0 hole；全枚举 + 环律（Zomega 已有 add/mul 结合、交换、分配、单位律）。
module Sovereign.Synthesis.A4.CharProvenance where

open import Data.Fin using (Fin; zero; suc)
open import Data.Integer using (ℤ)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂; module ≡-Reasoning)
open import Relation.Nullary using (¬_)

open ≡-Reasoning

open import Sovereign.Synthesis.Representation.Fin3Semiring using (neg3)
open import Sovereign.Synthesis.Representation.SL23Cayley using (_⊗_)
open import Sovereign.Synthesis.FieldTower.MatrixZω using (Mat; mulMat; trace)

open import Sovereign.Synthesis.A4.A4Representation
  using (Zω; oneZω; addZω; mulZω)
open import Sovereign.Algebra.FieldTower.Zomega
  using ( addZω-assoc; addZω-comm
        ; mulZω-assoc; mulZω-comm; mulZω-identityˡ
        ; mulZω-distribˡ )

open import Sovereign.Synthesis.A4.BinaryTetrahedralDefiningRep
  using (SL23; g0; g1; g2; g3; g4; g5; g6; g7; g8; g9; g10; g11
        ; g12; g13; g14; g15; g16; g17; g18; g19; g20; g21; g22; g23)
import Sovereign.Synthesis.A4.A4Group as A4G
open A4G using (A4; Rot)

open import Sovereign.Synthesis.A4.CoverA4 using (toA4)
open import Sovereign.Synthesis.A4.ToA4Hom using (_⊗A_; toA4-hom)
open import Sovereign.Synthesis.A4.BilinearSchur2A4
  using (M2E; m2e; mulME; traceME; toME; toME-hom)
open import Sovereign.Synthesis.A4.CharTable2A4
  using (Irr; Cls; i1; i1'; i1''; i2; i2'; i2''; i3; charOf; classOf2A4)
open import Sovereign.Synthesis.A4.A4OneDimHom
  using (ρ1; ρ1'; ρ1''; ab; powerω; add3; omega-pow-mul; ab-hom; rho1'-hom)
open import Sovereign.Synthesis.A4.A4ThreeDimRep using (rho3; rho3-hom)

--------------------------------------------------------------------------------
-- §1 平凡的 1 维表示：常数 1
--------------------------------------------------------------------------------

ψ1 : A4 → Zω
ψ1 = ρ1

psi1-hom : ∀ (a b : A4) → ψ1 (a ⊗A b) ≡ mulZω (ψ1 a) (ψ1 b)
psi1-hom a b = sym (mulZω-identityˡ oneZω)

--------------------------------------------------------------------------------
-- §2 非平凡的 1 维表示（直接来自 A4OneDimHom）
--------------------------------------------------------------------------------

-- ψ_a = ρ1′ = powerω ∘ ab（A4OneDimHom 已证乘法性）
ψa : A4 → Zω
ψa = ρ1'

psiA-hom : ∀ (a b : A4) → ψa (a ⊗A b) ≡ mulZω (ψa a) (ψa b)
psiA-hom a b = sym (rho1'-hom a b)

--------------------------------------------------------------------------------
-- §3 另一个非平凡 1 维表示：ψ_b = powerω ∘ neg3 ∘ ab
--
--   C₃ 的两个非平凡乘法特征标互为逆；ρ1′ 只给出了其中一个。
--   乘法性靠三件事实：neg3 对 add3 的分配（9 案）、ab-hom、omega-pow-mul。
--   ⚠ `A4OneDimHom.ρ1''` 不是这个（其 ab2 表甚至不是同态，见模块注释），
--     故此处重新定义 ψ_b，而不是复用 ρ1''。
--------------------------------------------------------------------------------

ψb : A4 → Zω
ψb g = powerω (neg3 (ab g))

-- 反证：`A4OneDimHom.ρ1''` 的 ab2 表**不是同态**（下列等式在一个点上不成立），
-- 所以它不能当 1 维表示用；ψb 是重新定义的真表示。
ρ1''-not-multiplicative :
    ¬ (ρ1'' (Rot zero zero A4G.⊗ Rot (suc zero) zero)
       ≡ mulZω (ρ1'' (Rot zero zero)) (ρ1'' (Rot (suc zero) zero)))
ρ1''-not-multiplicative = λ ()

neg3-add3 : ∀ (x y : Fin 3) → add3 (neg3 x) (neg3 y) ≡ neg3 (add3 x y)
neg3-add3 zero                   zero                   = refl
neg3-add3 zero                   (suc zero)             = refl
neg3-add3 zero                   (suc (suc zero))       = refl
neg3-add3 (suc zero)             zero                   = refl
neg3-add3 (suc zero)             (suc zero)             = refl
neg3-add3 (suc zero)             (suc (suc zero))       = refl
neg3-add3 (suc (suc zero))       zero                   = refl
neg3-add3 (suc (suc zero))       (suc zero)             = refl
neg3-add3 (suc (suc zero))       (suc (suc zero))       = refl

psiB-hom : ∀ (a b : A4) → ψb (a ⊗A b) ≡ mulZω (ψb a) (ψb b)
psiB-hom a b = begin
    powerω (neg3 (ab (a ⊗A b)))
  ≡⟨ cong (λ t → powerω (neg3 t)) (ab-hom a b) ⟩
    powerω (neg3 (add3 (ab a) (ab b)))
  ≡⟨ cong powerω (sym (neg3-add3 (ab a) (ab b))) ⟩
    powerω (add3 (neg3 (ab a)) (neg3 (ab b)))
  ≡⟨ sym (omega-pow-mul (neg3 (ab a)) (neg3 (ab b))) ⟩
    mulZω (powerω (neg3 (ab a))) (powerω (neg3 (ab b)))
  ∎

--------------------------------------------------------------------------------
-- §4 3 维表示（A₄ 的 V₀ 限制，rho3 已证乘法性）
--------------------------------------------------------------------------------

trace3 : A4 → Zω
trace3 g = trace (rho3 g)

char3 : SL23 → Zω
char3 x = trace3 (toA4 x)

rep3-hom : ∀ (a b : A4) → mulMat (rho3 a) (rho3 b) ≡ rho3 (a ⊗A b)
rep3-hom = rho3-hom

-- 同态拉回：ρ₃ ∘ toA4 也是 SL23 上的矩阵表示
rep3-pull : ∀ (x y : SL23) → mulMat (rho3 (toA4 x)) (rho3 (toA4 y))
                         ≡ rho3 (toA4 (x ⊗ y))
rep3-pull x y = trans (rho3-hom (toA4 x) (toA4 y))
                      (cong rho3 (sym (toA4-hom x y)))

--------------------------------------------------------------------------------
-- §5 标量乘：ρ2′ = (ψ_b ∘ toA4) • ρ2 、ρ2″ = (ψ_a ∘ toA4) • ρ2
--
--   2 维旋量表示与 1 维表示张量 = 标量乘。乘法性只用 Z[ω] 的结合/交换/分配律
--   （`Zomega` 已有），不需要 576 案枚举。
--------------------------------------------------------------------------------

scaleM : Zω → M2E → M2E
scaleM c (m2e a b d e) = m2e (mulZω c a) (mulZω c b) (mulZω c d) (mulZω c e)

m2e-cong : ∀ {a b c d a' b' c' d'} → a ≡ a' → b ≡ b' → c ≡ c' → d ≡ d'
         → m2e a b c d ≡ m2e a' b' c' d'
m2e-cong refl refl refl refl = refl

-- (c·x)·(d·y) ≡ (c·d)·(x·y)
pullScale : ∀ (c d x y : Zω)
          → mulZω (mulZω c x) (mulZω d y) ≡ mulZω (mulZω c d) (mulZω x y)
pullScale c d x y = begin
    mulZω (mulZω c x) (mulZω d y)
  ≡⟨ mulZω-assoc c x (mulZω d y) ⟩
    mulZω c (mulZω x (mulZω d y))
  ≡⟨ cong (mulZω c) (sym (mulZω-assoc x d y)) ⟩
    mulZω c (mulZω (mulZω x d) y)
  ≡⟨ cong (λ t → mulZω c (mulZω t y)) (mulZω-comm x d) ⟩
    mulZω c (mulZω (mulZω d x) y)
  ≡⟨ cong (mulZω c) (mulZω-assoc d x y) ⟩
    mulZω c (mulZω d (mulZω x y))
  ≡⟨ sym (mulZω-assoc c d (mulZω x y)) ⟩
    mulZω (mulZω c d) (mulZω x y)
  ∎

-- 一个矩阵元的换序：(c x)(d y) + (c u)(d v) ≡ (cd)(xy + uv)
row-mix : ∀ (c d x y u v : Zω)
        → addZω (mulZω (mulZω c x) (mulZω d y)) (mulZω (mulZω c u) (mulZω d v))
        ≡ mulZω (mulZω c d) (addZω (mulZω x y) (mulZω u v))
row-mix c d x y u v =
  trans (cong₂ addZω (pullScale c d x y) (pullScale c d u v))
        (sym (mulZω-distribˡ (mulZω c d) (mulZω x y) (mulZω u v)))

-- 标量乘与矩阵乘交换：(c·A)(d·B) ≡ (cd)·(AB)
scaleM-hom : ∀ (c d : Zω) (A B : M2E)
           → mulME (scaleM c A) (scaleM d B) ≡ scaleM (mulZω c d) (mulME A B)
scaleM-hom c d (m2e a₁ a₂ a₃ a₄) (m2e b₁ b₂ b₃ b₄) = m2e-cong
  (row-mix c d a₁ b₁ a₂ b₃)
  (row-mix c d a₁ b₂ a₂ b₄)
  (row-mix c d a₃ b₁ a₄ b₃)
  (row-mix c d a₃ b₂ a₄ b₄)

-- 迹对标量线性
traceM-scale : ∀ (c : Zω) (A : M2E) → traceME (scaleM c A) ≡ mulZω c (traceME A)
traceM-scale c (m2e a b d e) = sym (mulZω-distribˡ c a e)

-- 两个"旋量 × 1 维"表示
ρ2a : SL23 → M2E
ρ2a x = scaleM (ψa (toA4 x)) (toME x)

ρ2b : SL23 → M2E
ρ2b x = scaleM (ψb (toA4 x)) (toME x)

ρ2a-hom : ∀ (x y : SL23) → ρ2a (x ⊗ y) ≡ mulME (ρ2a x) (ρ2a y)
ρ2a-hom x y = begin
    scaleM (ψa (toA4 (x ⊗ y))) (toME (x ⊗ y))
  ≡⟨ cong₂ scaleM (cong ψa (toA4-hom x y)) (toME-hom x y) ⟩
    scaleM (ψa (toA4 x ⊗A toA4 y)) (mulME (toME x) (toME y))
  ≡⟨ cong₂ scaleM (psiA-hom (toA4 x) (toA4 y)) refl ⟩
    scaleM (mulZω (ψa (toA4 x)) (ψa (toA4 y))) (mulME (toME x) (toME y))
  ≡⟨ sym (scaleM-hom (ψa (toA4 x)) (ψa (toA4 y)) (toME x) (toME y)) ⟩
    mulME (ρ2a x) (ρ2a y)
  ∎

ρ2b-hom : ∀ (x y : SL23) → ρ2b (x ⊗ y) ≡ mulME (ρ2b x) (ρ2b y)
ρ2b-hom x y = begin
    scaleM (ψb (toA4 (x ⊗ y))) (toME (x ⊗ y))
  ≡⟨ cong₂ scaleM (cong ψb (toA4-hom x y)) (toME-hom x y) ⟩
    scaleM (ψb (toA4 x ⊗A toA4 y)) (mulME (toME x) (toME y))
  ≡⟨ cong₂ scaleM (psiB-hom (toA4 x) (toA4 y)) refl ⟩
    scaleM (mulZω (ψb (toA4 x)) (ψb (toA4 y))) (mulME (toME x) (toME y))
  ≡⟨ sym (scaleM-hom (ψb (toA4 x)) (ψb (toA4 y)) (toME x) (toME y)) ⟩
    mulME (ρ2b x) (ρ2b y)
  ∎

-- 迹分解：χ_{2′} = χ_{1′}·χ_{2}，χ_{2″} = χ_{1″}·χ_{2}
char2b-factor : ∀ (x : SL23) → traceME (ρ2b x) ≡ mulZω (ψb (toA4 x)) (traceME (toME x))
char2b-factor x = traceM-scale (ψb (toA4 x)) (toME x)

char2a-factor : ∀ (x : SL23) → traceME (ρ2a x) ≡ mulZω (ψa (toA4 x)) (traceME (toME x))
char2a-factor x = traceM-scale (ψa (toA4 x)) (toME x)

--------------------------------------------------------------------------------
-- §6 表行 ↔ 表示：逐点一致（6 组 × 24 案 refl）
--------------------------------------------------------------------------------

row-i1 : ∀ (x : SL23) → charOf i1 (classOf2A4 x) ≡ ψ1 (toA4 x)
row-i1 g0  = refl
row-i1 g1  = refl
row-i1 g2  = refl
row-i1 g3  = refl
row-i1 g4  = refl
row-i1 g5  = refl
row-i1 g6  = refl
row-i1 g7  = refl
row-i1 g8  = refl
row-i1 g9  = refl
row-i1 g10 = refl
row-i1 g11 = refl
row-i1 g12 = refl
row-i1 g13 = refl
row-i1 g14 = refl
row-i1 g15 = refl
row-i1 g16 = refl
row-i1 g17 = refl
row-i1 g18 = refl
row-i1 g19 = refl
row-i1 g20 = refl
row-i1 g21 = refl
row-i1 g22 = refl
row-i1 g23 = refl

row-i1' : ∀ (x : SL23) → charOf i1' (classOf2A4 x) ≡ ψb (toA4 x)
row-i1' g0  = refl
row-i1' g1  = refl
row-i1' g2  = refl
row-i1' g3  = refl
row-i1' g4  = refl
row-i1' g5  = refl
row-i1' g6  = refl
row-i1' g7  = refl
row-i1' g8  = refl
row-i1' g9  = refl
row-i1' g10 = refl
row-i1' g11 = refl
row-i1' g12 = refl
row-i1' g13 = refl
row-i1' g14 = refl
row-i1' g15 = refl
row-i1' g16 = refl
row-i1' g17 = refl
row-i1' g18 = refl
row-i1' g19 = refl
row-i1' g20 = refl
row-i1' g21 = refl
row-i1' g22 = refl
row-i1' g23 = refl

row-i1'' : ∀ (x : SL23) → charOf i1'' (classOf2A4 x) ≡ ψa (toA4 x)
row-i1'' g0  = refl
row-i1'' g1  = refl
row-i1'' g2  = refl
row-i1'' g3  = refl
row-i1'' g4  = refl
row-i1'' g5  = refl
row-i1'' g6  = refl
row-i1'' g7  = refl
row-i1'' g8  = refl
row-i1'' g9  = refl
row-i1'' g10 = refl
row-i1'' g11 = refl
row-i1'' g12 = refl
row-i1'' g13 = refl
row-i1'' g14 = refl
row-i1'' g15 = refl
row-i1'' g16 = refl
row-i1'' g17 = refl
row-i1'' g18 = refl
row-i1'' g19 = refl
row-i1'' g20 = refl
row-i1'' g21 = refl
row-i1'' g22 = refl
row-i1'' g23 = refl

row-i2' : ∀ (x : SL23) → charOf i2' (classOf2A4 x) ≡ traceME (ρ2b x)
row-i2' g0  = refl
row-i2' g1  = refl
row-i2' g2  = refl
row-i2' g3  = refl
row-i2' g4  = refl
row-i2' g5  = refl
row-i2' g6  = refl
row-i2' g7  = refl
row-i2' g8  = refl
row-i2' g9  = refl
row-i2' g10 = refl
row-i2' g11 = refl
row-i2' g12 = refl
row-i2' g13 = refl
row-i2' g14 = refl
row-i2' g15 = refl
row-i2' g16 = refl
row-i2' g17 = refl
row-i2' g18 = refl
row-i2' g19 = refl
row-i2' g20 = refl
row-i2' g21 = refl
row-i2' g22 = refl
row-i2' g23 = refl

row-i2'' : ∀ (x : SL23) → charOf i2'' (classOf2A4 x) ≡ traceME (ρ2a x)
row-i2'' g0  = refl
row-i2'' g1  = refl
row-i2'' g2  = refl
row-i2'' g3  = refl
row-i2'' g4  = refl
row-i2'' g5  = refl
row-i2'' g6  = refl
row-i2'' g7  = refl
row-i2'' g8  = refl
row-i2'' g9  = refl
row-i2'' g10 = refl
row-i2'' g11 = refl
row-i2'' g12 = refl
row-i2'' g13 = refl
row-i2'' g14 = refl
row-i2'' g15 = refl
row-i2'' g16 = refl
row-i2'' g17 = refl
row-i2'' g18 = refl
row-i2'' g19 = refl
row-i2'' g20 = refl
row-i2'' g21 = refl
row-i2'' g22 = refl
row-i2'' g23 = refl

row-i3 : ∀ (x : SL23) → charOf i3 (classOf2A4 x) ≡ char3 x
row-i3 g0  = refl
row-i3 g1  = refl
row-i3 g2  = refl
row-i3 g3  = refl
row-i3 g4  = refl
row-i3 g5  = refl
row-i3 g6  = refl
row-i3 g7  = refl
row-i3 g8  = refl
row-i3 g9  = refl
row-i3 g10 = refl
row-i3 g11 = refl
row-i3 g12 = refl
row-i3 g13 = refl
row-i3 g14 = refl
row-i3 g15 = refl
row-i3 g16 = refl
row-i3 g17 = refl
row-i3 g18 = refl
row-i3 g19 = refl
row-i3 g20 = refl
row-i3 g21 = refl
row-i3 g22 = refl
row-i3 g23 = refl

--------------------------------------------------------------------------------
-- §7 结论记录：每行都是某（已证乘法性的）表示的迹
--------------------------------------------------------------------------------

record CharProvenance : Set where
  field
    -- 1 维：三行各自是乘法特征标
    rep-1        : ∀ (a b : A4) → ψ1 (a ⊗A b) ≡ mulZω (ψ1 a) (ψ1 b)
    rep-1a       : ∀ (a b : A4) → ψa (a ⊗A b) ≡ mulZω (ψa a) (ψa b)
    rep-1b       : ∀ (a b : A4) → ψb (a ⊗A b) ≡ mulZω (ψb a) (ψb b)
    -- 2 维：三个矩阵表示
    rep-2        : ∀ (x y : SL23) → toME (x ⊗ y) ≡ mulME (toME x) (toME y)
    rep-2a       : ∀ (x y : SL23) → ρ2a (x ⊗ y) ≡ mulME (ρ2a x) (ρ2a y)
    rep-2b       : ∀ (x y : SL23) → ρ2b (x ⊗ y) ≡ mulME (ρ2b x) (ρ2b y)
    -- 3 维
    rep-3        : ∀ (a b : A4) → mulMat (rho3 a) (rho3 b) ≡ rho3 (a ⊗A b)
    rep-3-pull   : ∀ (x y : SL23) → mulMat (rho3 (toA4 x)) (rho3 (toA4 y))
                                   ≡ rho3 (toA4 (x ⊗ y))
    -- 表行 = 迹
    row-1        : ∀ (x : SL23) → charOf i1 (classOf2A4 x) ≡ ψ1 (toA4 x)
    row-1'       : ∀ (x : SL23) → charOf i1' (classOf2A4 x) ≡ ψb (toA4 x)
    row-1''      : ∀ (x : SL23) → charOf i1'' (classOf2A4 x) ≡ ψa (toA4 x)
    row-2'       : ∀ (x : SL23) → charOf i2' (classOf2A4 x) ≡ traceME (ρ2b x)
    row-2''      : ∀ (x : SL23) → charOf i2'' (classOf2A4 x) ≡ traceME (ρ2a x)
    row-3        : ∀ (x : SL23) → charOf i3 (classOf2A4 x) ≡ char3 x
    -- 迹的乘法分解（张量积特征标 = 特征标之积）
    trace-2a     : ∀ (x : SL23) → traceME (ρ2a x) ≡ mulZω (ψa (toA4 x)) (traceME (toME x))
    trace-2b     : ∀ (x : SL23) → traceME (ρ2b x) ≡ mulZω (ψb (toA4 x)) (traceME (toME x))

charProvenance : CharProvenance
charProvenance = record
  { rep-1      = psi1-hom
  ; rep-1a     = psiA-hom
  ; rep-1b     = psiB-hom
  ; rep-2      = toME-hom
  ; rep-2a     = ρ2a-hom
  ; rep-2b     = ρ2b-hom
  ; rep-3      = rep3-hom
  ; rep-3-pull = rep3-pull
  ; row-1      = row-i1
  ; row-1'     = row-i1'
  ; row-1''    = row-i1''
  ; row-2'     = row-i2'
  ; row-2''    = row-i2''
  ; row-3      = row-i3
  ; trace-2a   = char2a-factor
  ; trace-2b   = char2b-factor
  }
