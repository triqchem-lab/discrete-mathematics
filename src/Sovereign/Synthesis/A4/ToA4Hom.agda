{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Synthesis.A4.ToA4Hom
--
-- **`toA4 : SL23 → A₄` 是群同态**（24 行 × 24 案 = 576 对，与 Cayley 表逐条核对）
--
-- 为什么需要它：
--   `CoverA4` 只证了"像 = A₄"（每个 toA4 x 恰好是 permAt 对应的偶置换），
--   但那还是**集合层面**的对应。有了本文件的同态性，A₄ 的所有表示（1 维、3 维）
--   才能沿 toA4 拉回成 2A₄ 的表示——`CharTable2A4` §10(a) 缺的就是这一块。
--
-- 与 576 案的 `toME-hom`（BilinearSchur2A4）同构：
--   SL23 是不透明 24 构造子 data，`_⊗_` 与 `toA4` 都是显式表；
--   本定理的命题内容是"两张表相容"的 576 条独立事实，不可归纳，只能逐条归约。
--   按"单引理 ≤27 案"纪律，按第一参数分解成 24 个行引理（每个 ∀ y，24 案）再组装。
--
-- 附带产出（A₄ ≅ SL23/{±I} 的群论面）：
--   · `toA4-hom`    —— 乘法 → 乘法（576 案，本文件主定理）
--   · `toA4-surj`   —— 满射（复用 CoverA4，12 案）
--   · `toA4-kernel` —— 核恰为 {I, −I}（由 kernel-spec + 同态性 推出，非重新枚举）
--   商群本身（SL23/{±I} 的 setoid 商 + 泛性质）仍不在库，见 §4 边界。
--
-- 0 postulate / 0 hole；零浮点。
module Sovereign.Synthesis.A4.ToA4Hom where

import Sovereign.Synthesis.A4.A4Group as A4G
open A4G using (A4; Id; Rot; Flip; perm; fromPerm)

open import Data.Product using (Σ; _×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong)

open import Sovereign.Synthesis.Representation.SL23Cayley using (_⊗_)
open import Sovereign.Synthesis.A4.A4Representation using (Zω; mulZω)
open import Sovereign.Synthesis.A4.BinaryTetrahedralDefiningRep
  using (SL23; g0; g1; g2; g3; g4; g5; g6; g7; g8; g9; g10; g11
        ; g12; g13; g14; g15; g16; g17; g18; g19; g20; g21; g22; g23)
open import Sovereign.Synthesis.A4.CoverA4
  using (toA4; toA4-surj; image-in-A4; kernel-spec)

-- A₄ 的乘法（= A4Group._⊗_ 的定义，改名以免与 SL23 的 _⊗_ 冲突）
_⊗A_ : A4 → A4 → A4
_⊗A_ = A4G._⊗_

--------------------------------------------------------------------------------
-- §1 同态性：24 个行引理（每行 ∀ y，24 案）
--------------------------------------------------------------------------------

toA4-hom-g0 : ∀ (y : SL23) → toA4 (g0 ⊗ y) ≡ toA4 g0 ⊗A toA4 y
toA4-hom-g0 g0  = refl
toA4-hom-g0 g1  = refl
toA4-hom-g0 g2  = refl
toA4-hom-g0 g3  = refl
toA4-hom-g0 g4  = refl
toA4-hom-g0 g5  = refl
toA4-hom-g0 g6  = refl
toA4-hom-g0 g7  = refl
toA4-hom-g0 g8  = refl
toA4-hom-g0 g9  = refl
toA4-hom-g0 g10 = refl
toA4-hom-g0 g11 = refl
toA4-hom-g0 g12 = refl
toA4-hom-g0 g13 = refl
toA4-hom-g0 g14 = refl
toA4-hom-g0 g15 = refl
toA4-hom-g0 g16 = refl
toA4-hom-g0 g17 = refl
toA4-hom-g0 g18 = refl
toA4-hom-g0 g19 = refl
toA4-hom-g0 g20 = refl
toA4-hom-g0 g21 = refl
toA4-hom-g0 g22 = refl
toA4-hom-g0 g23 = refl

toA4-hom-g1 : ∀ (y : SL23) → toA4 (g1 ⊗ y) ≡ toA4 g1 ⊗A toA4 y
toA4-hom-g1 g0  = refl
toA4-hom-g1 g1  = refl
toA4-hom-g1 g2  = refl
toA4-hom-g1 g3  = refl
toA4-hom-g1 g4  = refl
toA4-hom-g1 g5  = refl
toA4-hom-g1 g6  = refl
toA4-hom-g1 g7  = refl
toA4-hom-g1 g8  = refl
toA4-hom-g1 g9  = refl
toA4-hom-g1 g10 = refl
toA4-hom-g1 g11 = refl
toA4-hom-g1 g12 = refl
toA4-hom-g1 g13 = refl
toA4-hom-g1 g14 = refl
toA4-hom-g1 g15 = refl
toA4-hom-g1 g16 = refl
toA4-hom-g1 g17 = refl
toA4-hom-g1 g18 = refl
toA4-hom-g1 g19 = refl
toA4-hom-g1 g20 = refl
toA4-hom-g1 g21 = refl
toA4-hom-g1 g22 = refl
toA4-hom-g1 g23 = refl

toA4-hom-g2 : ∀ (y : SL23) → toA4 (g2 ⊗ y) ≡ toA4 g2 ⊗A toA4 y
toA4-hom-g2 g0  = refl
toA4-hom-g2 g1  = refl
toA4-hom-g2 g2  = refl
toA4-hom-g2 g3  = refl
toA4-hom-g2 g4  = refl
toA4-hom-g2 g5  = refl
toA4-hom-g2 g6  = refl
toA4-hom-g2 g7  = refl
toA4-hom-g2 g8  = refl
toA4-hom-g2 g9  = refl
toA4-hom-g2 g10 = refl
toA4-hom-g2 g11 = refl
toA4-hom-g2 g12 = refl
toA4-hom-g2 g13 = refl
toA4-hom-g2 g14 = refl
toA4-hom-g2 g15 = refl
toA4-hom-g2 g16 = refl
toA4-hom-g2 g17 = refl
toA4-hom-g2 g18 = refl
toA4-hom-g2 g19 = refl
toA4-hom-g2 g20 = refl
toA4-hom-g2 g21 = refl
toA4-hom-g2 g22 = refl
toA4-hom-g2 g23 = refl

toA4-hom-g3 : ∀ (y : SL23) → toA4 (g3 ⊗ y) ≡ toA4 g3 ⊗A toA4 y
toA4-hom-g3 g0  = refl
toA4-hom-g3 g1  = refl
toA4-hom-g3 g2  = refl
toA4-hom-g3 g3  = refl
toA4-hom-g3 g4  = refl
toA4-hom-g3 g5  = refl
toA4-hom-g3 g6  = refl
toA4-hom-g3 g7  = refl
toA4-hom-g3 g8  = refl
toA4-hom-g3 g9  = refl
toA4-hom-g3 g10 = refl
toA4-hom-g3 g11 = refl
toA4-hom-g3 g12 = refl
toA4-hom-g3 g13 = refl
toA4-hom-g3 g14 = refl
toA4-hom-g3 g15 = refl
toA4-hom-g3 g16 = refl
toA4-hom-g3 g17 = refl
toA4-hom-g3 g18 = refl
toA4-hom-g3 g19 = refl
toA4-hom-g3 g20 = refl
toA4-hom-g3 g21 = refl
toA4-hom-g3 g22 = refl
toA4-hom-g3 g23 = refl

toA4-hom-g4 : ∀ (y : SL23) → toA4 (g4 ⊗ y) ≡ toA4 g4 ⊗A toA4 y
toA4-hom-g4 g0  = refl
toA4-hom-g4 g1  = refl
toA4-hom-g4 g2  = refl
toA4-hom-g4 g3  = refl
toA4-hom-g4 g4  = refl
toA4-hom-g4 g5  = refl
toA4-hom-g4 g6  = refl
toA4-hom-g4 g7  = refl
toA4-hom-g4 g8  = refl
toA4-hom-g4 g9  = refl
toA4-hom-g4 g10 = refl
toA4-hom-g4 g11 = refl
toA4-hom-g4 g12 = refl
toA4-hom-g4 g13 = refl
toA4-hom-g4 g14 = refl
toA4-hom-g4 g15 = refl
toA4-hom-g4 g16 = refl
toA4-hom-g4 g17 = refl
toA4-hom-g4 g18 = refl
toA4-hom-g4 g19 = refl
toA4-hom-g4 g20 = refl
toA4-hom-g4 g21 = refl
toA4-hom-g4 g22 = refl
toA4-hom-g4 g23 = refl

toA4-hom-g5 : ∀ (y : SL23) → toA4 (g5 ⊗ y) ≡ toA4 g5 ⊗A toA4 y
toA4-hom-g5 g0  = refl
toA4-hom-g5 g1  = refl
toA4-hom-g5 g2  = refl
toA4-hom-g5 g3  = refl
toA4-hom-g5 g4  = refl
toA4-hom-g5 g5  = refl
toA4-hom-g5 g6  = refl
toA4-hom-g5 g7  = refl
toA4-hom-g5 g8  = refl
toA4-hom-g5 g9  = refl
toA4-hom-g5 g10 = refl
toA4-hom-g5 g11 = refl
toA4-hom-g5 g12 = refl
toA4-hom-g5 g13 = refl
toA4-hom-g5 g14 = refl
toA4-hom-g5 g15 = refl
toA4-hom-g5 g16 = refl
toA4-hom-g5 g17 = refl
toA4-hom-g5 g18 = refl
toA4-hom-g5 g19 = refl
toA4-hom-g5 g20 = refl
toA4-hom-g5 g21 = refl
toA4-hom-g5 g22 = refl
toA4-hom-g5 g23 = refl

toA4-hom-g6 : ∀ (y : SL23) → toA4 (g6 ⊗ y) ≡ toA4 g6 ⊗A toA4 y
toA4-hom-g6 g0  = refl
toA4-hom-g6 g1  = refl
toA4-hom-g6 g2  = refl
toA4-hom-g6 g3  = refl
toA4-hom-g6 g4  = refl
toA4-hom-g6 g5  = refl
toA4-hom-g6 g6  = refl
toA4-hom-g6 g7  = refl
toA4-hom-g6 g8  = refl
toA4-hom-g6 g9  = refl
toA4-hom-g6 g10 = refl
toA4-hom-g6 g11 = refl
toA4-hom-g6 g12 = refl
toA4-hom-g6 g13 = refl
toA4-hom-g6 g14 = refl
toA4-hom-g6 g15 = refl
toA4-hom-g6 g16 = refl
toA4-hom-g6 g17 = refl
toA4-hom-g6 g18 = refl
toA4-hom-g6 g19 = refl
toA4-hom-g6 g20 = refl
toA4-hom-g6 g21 = refl
toA4-hom-g6 g22 = refl
toA4-hom-g6 g23 = refl

toA4-hom-g7 : ∀ (y : SL23) → toA4 (g7 ⊗ y) ≡ toA4 g7 ⊗A toA4 y
toA4-hom-g7 g0  = refl
toA4-hom-g7 g1  = refl
toA4-hom-g7 g2  = refl
toA4-hom-g7 g3  = refl
toA4-hom-g7 g4  = refl
toA4-hom-g7 g5  = refl
toA4-hom-g7 g6  = refl
toA4-hom-g7 g7  = refl
toA4-hom-g7 g8  = refl
toA4-hom-g7 g9  = refl
toA4-hom-g7 g10 = refl
toA4-hom-g7 g11 = refl
toA4-hom-g7 g12 = refl
toA4-hom-g7 g13 = refl
toA4-hom-g7 g14 = refl
toA4-hom-g7 g15 = refl
toA4-hom-g7 g16 = refl
toA4-hom-g7 g17 = refl
toA4-hom-g7 g18 = refl
toA4-hom-g7 g19 = refl
toA4-hom-g7 g20 = refl
toA4-hom-g7 g21 = refl
toA4-hom-g7 g22 = refl
toA4-hom-g7 g23 = refl

toA4-hom-g8 : ∀ (y : SL23) → toA4 (g8 ⊗ y) ≡ toA4 g8 ⊗A toA4 y
toA4-hom-g8 g0  = refl
toA4-hom-g8 g1  = refl
toA4-hom-g8 g2  = refl
toA4-hom-g8 g3  = refl
toA4-hom-g8 g4  = refl
toA4-hom-g8 g5  = refl
toA4-hom-g8 g6  = refl
toA4-hom-g8 g7  = refl
toA4-hom-g8 g8  = refl
toA4-hom-g8 g9  = refl
toA4-hom-g8 g10 = refl
toA4-hom-g8 g11 = refl
toA4-hom-g8 g12 = refl
toA4-hom-g8 g13 = refl
toA4-hom-g8 g14 = refl
toA4-hom-g8 g15 = refl
toA4-hom-g8 g16 = refl
toA4-hom-g8 g17 = refl
toA4-hom-g8 g18 = refl
toA4-hom-g8 g19 = refl
toA4-hom-g8 g20 = refl
toA4-hom-g8 g21 = refl
toA4-hom-g8 g22 = refl
toA4-hom-g8 g23 = refl

toA4-hom-g9 : ∀ (y : SL23) → toA4 (g9 ⊗ y) ≡ toA4 g9 ⊗A toA4 y
toA4-hom-g9 g0  = refl
toA4-hom-g9 g1  = refl
toA4-hom-g9 g2  = refl
toA4-hom-g9 g3  = refl
toA4-hom-g9 g4  = refl
toA4-hom-g9 g5  = refl
toA4-hom-g9 g6  = refl
toA4-hom-g9 g7  = refl
toA4-hom-g9 g8  = refl
toA4-hom-g9 g9  = refl
toA4-hom-g9 g10 = refl
toA4-hom-g9 g11 = refl
toA4-hom-g9 g12 = refl
toA4-hom-g9 g13 = refl
toA4-hom-g9 g14 = refl
toA4-hom-g9 g15 = refl
toA4-hom-g9 g16 = refl
toA4-hom-g9 g17 = refl
toA4-hom-g9 g18 = refl
toA4-hom-g9 g19 = refl
toA4-hom-g9 g20 = refl
toA4-hom-g9 g21 = refl
toA4-hom-g9 g22 = refl
toA4-hom-g9 g23 = refl

toA4-hom-g10 : ∀ (y : SL23) → toA4 (g10 ⊗ y) ≡ toA4 g10 ⊗A toA4 y
toA4-hom-g10 g0  = refl
toA4-hom-g10 g1  = refl
toA4-hom-g10 g2  = refl
toA4-hom-g10 g3  = refl
toA4-hom-g10 g4  = refl
toA4-hom-g10 g5  = refl
toA4-hom-g10 g6  = refl
toA4-hom-g10 g7  = refl
toA4-hom-g10 g8  = refl
toA4-hom-g10 g9  = refl
toA4-hom-g10 g10 = refl
toA4-hom-g10 g11 = refl
toA4-hom-g10 g12 = refl
toA4-hom-g10 g13 = refl
toA4-hom-g10 g14 = refl
toA4-hom-g10 g15 = refl
toA4-hom-g10 g16 = refl
toA4-hom-g10 g17 = refl
toA4-hom-g10 g18 = refl
toA4-hom-g10 g19 = refl
toA4-hom-g10 g20 = refl
toA4-hom-g10 g21 = refl
toA4-hom-g10 g22 = refl
toA4-hom-g10 g23 = refl

toA4-hom-g11 : ∀ (y : SL23) → toA4 (g11 ⊗ y) ≡ toA4 g11 ⊗A toA4 y
toA4-hom-g11 g0  = refl
toA4-hom-g11 g1  = refl
toA4-hom-g11 g2  = refl
toA4-hom-g11 g3  = refl
toA4-hom-g11 g4  = refl
toA4-hom-g11 g5  = refl
toA4-hom-g11 g6  = refl
toA4-hom-g11 g7  = refl
toA4-hom-g11 g8  = refl
toA4-hom-g11 g9  = refl
toA4-hom-g11 g10 = refl
toA4-hom-g11 g11 = refl
toA4-hom-g11 g12 = refl
toA4-hom-g11 g13 = refl
toA4-hom-g11 g14 = refl
toA4-hom-g11 g15 = refl
toA4-hom-g11 g16 = refl
toA4-hom-g11 g17 = refl
toA4-hom-g11 g18 = refl
toA4-hom-g11 g19 = refl
toA4-hom-g11 g20 = refl
toA4-hom-g11 g21 = refl
toA4-hom-g11 g22 = refl
toA4-hom-g11 g23 = refl

toA4-hom-g12 : ∀ (y : SL23) → toA4 (g12 ⊗ y) ≡ toA4 g12 ⊗A toA4 y
toA4-hom-g12 g0  = refl
toA4-hom-g12 g1  = refl
toA4-hom-g12 g2  = refl
toA4-hom-g12 g3  = refl
toA4-hom-g12 g4  = refl
toA4-hom-g12 g5  = refl
toA4-hom-g12 g6  = refl
toA4-hom-g12 g7  = refl
toA4-hom-g12 g8  = refl
toA4-hom-g12 g9  = refl
toA4-hom-g12 g10 = refl
toA4-hom-g12 g11 = refl
toA4-hom-g12 g12 = refl
toA4-hom-g12 g13 = refl
toA4-hom-g12 g14 = refl
toA4-hom-g12 g15 = refl
toA4-hom-g12 g16 = refl
toA4-hom-g12 g17 = refl
toA4-hom-g12 g18 = refl
toA4-hom-g12 g19 = refl
toA4-hom-g12 g20 = refl
toA4-hom-g12 g21 = refl
toA4-hom-g12 g22 = refl
toA4-hom-g12 g23 = refl

toA4-hom-g13 : ∀ (y : SL23) → toA4 (g13 ⊗ y) ≡ toA4 g13 ⊗A toA4 y
toA4-hom-g13 g0  = refl
toA4-hom-g13 g1  = refl
toA4-hom-g13 g2  = refl
toA4-hom-g13 g3  = refl
toA4-hom-g13 g4  = refl
toA4-hom-g13 g5  = refl
toA4-hom-g13 g6  = refl
toA4-hom-g13 g7  = refl
toA4-hom-g13 g8  = refl
toA4-hom-g13 g9  = refl
toA4-hom-g13 g10 = refl
toA4-hom-g13 g11 = refl
toA4-hom-g13 g12 = refl
toA4-hom-g13 g13 = refl
toA4-hom-g13 g14 = refl
toA4-hom-g13 g15 = refl
toA4-hom-g13 g16 = refl
toA4-hom-g13 g17 = refl
toA4-hom-g13 g18 = refl
toA4-hom-g13 g19 = refl
toA4-hom-g13 g20 = refl
toA4-hom-g13 g21 = refl
toA4-hom-g13 g22 = refl
toA4-hom-g13 g23 = refl

toA4-hom-g14 : ∀ (y : SL23) → toA4 (g14 ⊗ y) ≡ toA4 g14 ⊗A toA4 y
toA4-hom-g14 g0  = refl
toA4-hom-g14 g1  = refl
toA4-hom-g14 g2  = refl
toA4-hom-g14 g3  = refl
toA4-hom-g14 g4  = refl
toA4-hom-g14 g5  = refl
toA4-hom-g14 g6  = refl
toA4-hom-g14 g7  = refl
toA4-hom-g14 g8  = refl
toA4-hom-g14 g9  = refl
toA4-hom-g14 g10 = refl
toA4-hom-g14 g11 = refl
toA4-hom-g14 g12 = refl
toA4-hom-g14 g13 = refl
toA4-hom-g14 g14 = refl
toA4-hom-g14 g15 = refl
toA4-hom-g14 g16 = refl
toA4-hom-g14 g17 = refl
toA4-hom-g14 g18 = refl
toA4-hom-g14 g19 = refl
toA4-hom-g14 g20 = refl
toA4-hom-g14 g21 = refl
toA4-hom-g14 g22 = refl
toA4-hom-g14 g23 = refl

toA4-hom-g15 : ∀ (y : SL23) → toA4 (g15 ⊗ y) ≡ toA4 g15 ⊗A toA4 y
toA4-hom-g15 g0  = refl
toA4-hom-g15 g1  = refl
toA4-hom-g15 g2  = refl
toA4-hom-g15 g3  = refl
toA4-hom-g15 g4  = refl
toA4-hom-g15 g5  = refl
toA4-hom-g15 g6  = refl
toA4-hom-g15 g7  = refl
toA4-hom-g15 g8  = refl
toA4-hom-g15 g9  = refl
toA4-hom-g15 g10 = refl
toA4-hom-g15 g11 = refl
toA4-hom-g15 g12 = refl
toA4-hom-g15 g13 = refl
toA4-hom-g15 g14 = refl
toA4-hom-g15 g15 = refl
toA4-hom-g15 g16 = refl
toA4-hom-g15 g17 = refl
toA4-hom-g15 g18 = refl
toA4-hom-g15 g19 = refl
toA4-hom-g15 g20 = refl
toA4-hom-g15 g21 = refl
toA4-hom-g15 g22 = refl
toA4-hom-g15 g23 = refl

toA4-hom-g16 : ∀ (y : SL23) → toA4 (g16 ⊗ y) ≡ toA4 g16 ⊗A toA4 y
toA4-hom-g16 g0  = refl
toA4-hom-g16 g1  = refl
toA4-hom-g16 g2  = refl
toA4-hom-g16 g3  = refl
toA4-hom-g16 g4  = refl
toA4-hom-g16 g5  = refl
toA4-hom-g16 g6  = refl
toA4-hom-g16 g7  = refl
toA4-hom-g16 g8  = refl
toA4-hom-g16 g9  = refl
toA4-hom-g16 g10 = refl
toA4-hom-g16 g11 = refl
toA4-hom-g16 g12 = refl
toA4-hom-g16 g13 = refl
toA4-hom-g16 g14 = refl
toA4-hom-g16 g15 = refl
toA4-hom-g16 g16 = refl
toA4-hom-g16 g17 = refl
toA4-hom-g16 g18 = refl
toA4-hom-g16 g19 = refl
toA4-hom-g16 g20 = refl
toA4-hom-g16 g21 = refl
toA4-hom-g16 g22 = refl
toA4-hom-g16 g23 = refl

toA4-hom-g17 : ∀ (y : SL23) → toA4 (g17 ⊗ y) ≡ toA4 g17 ⊗A toA4 y
toA4-hom-g17 g0  = refl
toA4-hom-g17 g1  = refl
toA4-hom-g17 g2  = refl
toA4-hom-g17 g3  = refl
toA4-hom-g17 g4  = refl
toA4-hom-g17 g5  = refl
toA4-hom-g17 g6  = refl
toA4-hom-g17 g7  = refl
toA4-hom-g17 g8  = refl
toA4-hom-g17 g9  = refl
toA4-hom-g17 g10 = refl
toA4-hom-g17 g11 = refl
toA4-hom-g17 g12 = refl
toA4-hom-g17 g13 = refl
toA4-hom-g17 g14 = refl
toA4-hom-g17 g15 = refl
toA4-hom-g17 g16 = refl
toA4-hom-g17 g17 = refl
toA4-hom-g17 g18 = refl
toA4-hom-g17 g19 = refl
toA4-hom-g17 g20 = refl
toA4-hom-g17 g21 = refl
toA4-hom-g17 g22 = refl
toA4-hom-g17 g23 = refl

toA4-hom-g18 : ∀ (y : SL23) → toA4 (g18 ⊗ y) ≡ toA4 g18 ⊗A toA4 y
toA4-hom-g18 g0  = refl
toA4-hom-g18 g1  = refl
toA4-hom-g18 g2  = refl
toA4-hom-g18 g3  = refl
toA4-hom-g18 g4  = refl
toA4-hom-g18 g5  = refl
toA4-hom-g18 g6  = refl
toA4-hom-g18 g7  = refl
toA4-hom-g18 g8  = refl
toA4-hom-g18 g9  = refl
toA4-hom-g18 g10 = refl
toA4-hom-g18 g11 = refl
toA4-hom-g18 g12 = refl
toA4-hom-g18 g13 = refl
toA4-hom-g18 g14 = refl
toA4-hom-g18 g15 = refl
toA4-hom-g18 g16 = refl
toA4-hom-g18 g17 = refl
toA4-hom-g18 g18 = refl
toA4-hom-g18 g19 = refl
toA4-hom-g18 g20 = refl
toA4-hom-g18 g21 = refl
toA4-hom-g18 g22 = refl
toA4-hom-g18 g23 = refl

toA4-hom-g19 : ∀ (y : SL23) → toA4 (g19 ⊗ y) ≡ toA4 g19 ⊗A toA4 y
toA4-hom-g19 g0  = refl
toA4-hom-g19 g1  = refl
toA4-hom-g19 g2  = refl
toA4-hom-g19 g3  = refl
toA4-hom-g19 g4  = refl
toA4-hom-g19 g5  = refl
toA4-hom-g19 g6  = refl
toA4-hom-g19 g7  = refl
toA4-hom-g19 g8  = refl
toA4-hom-g19 g9  = refl
toA4-hom-g19 g10 = refl
toA4-hom-g19 g11 = refl
toA4-hom-g19 g12 = refl
toA4-hom-g19 g13 = refl
toA4-hom-g19 g14 = refl
toA4-hom-g19 g15 = refl
toA4-hom-g19 g16 = refl
toA4-hom-g19 g17 = refl
toA4-hom-g19 g18 = refl
toA4-hom-g19 g19 = refl
toA4-hom-g19 g20 = refl
toA4-hom-g19 g21 = refl
toA4-hom-g19 g22 = refl
toA4-hom-g19 g23 = refl

toA4-hom-g20 : ∀ (y : SL23) → toA4 (g20 ⊗ y) ≡ toA4 g20 ⊗A toA4 y
toA4-hom-g20 g0  = refl
toA4-hom-g20 g1  = refl
toA4-hom-g20 g2  = refl
toA4-hom-g20 g3  = refl
toA4-hom-g20 g4  = refl
toA4-hom-g20 g5  = refl
toA4-hom-g20 g6  = refl
toA4-hom-g20 g7  = refl
toA4-hom-g20 g8  = refl
toA4-hom-g20 g9  = refl
toA4-hom-g20 g10 = refl
toA4-hom-g20 g11 = refl
toA4-hom-g20 g12 = refl
toA4-hom-g20 g13 = refl
toA4-hom-g20 g14 = refl
toA4-hom-g20 g15 = refl
toA4-hom-g20 g16 = refl
toA4-hom-g20 g17 = refl
toA4-hom-g20 g18 = refl
toA4-hom-g20 g19 = refl
toA4-hom-g20 g20 = refl
toA4-hom-g20 g21 = refl
toA4-hom-g20 g22 = refl
toA4-hom-g20 g23 = refl

toA4-hom-g21 : ∀ (y : SL23) → toA4 (g21 ⊗ y) ≡ toA4 g21 ⊗A toA4 y
toA4-hom-g21 g0  = refl
toA4-hom-g21 g1  = refl
toA4-hom-g21 g2  = refl
toA4-hom-g21 g3  = refl
toA4-hom-g21 g4  = refl
toA4-hom-g21 g5  = refl
toA4-hom-g21 g6  = refl
toA4-hom-g21 g7  = refl
toA4-hom-g21 g8  = refl
toA4-hom-g21 g9  = refl
toA4-hom-g21 g10 = refl
toA4-hom-g21 g11 = refl
toA4-hom-g21 g12 = refl
toA4-hom-g21 g13 = refl
toA4-hom-g21 g14 = refl
toA4-hom-g21 g15 = refl
toA4-hom-g21 g16 = refl
toA4-hom-g21 g17 = refl
toA4-hom-g21 g18 = refl
toA4-hom-g21 g19 = refl
toA4-hom-g21 g20 = refl
toA4-hom-g21 g21 = refl
toA4-hom-g21 g22 = refl
toA4-hom-g21 g23 = refl

toA4-hom-g22 : ∀ (y : SL23) → toA4 (g22 ⊗ y) ≡ toA4 g22 ⊗A toA4 y
toA4-hom-g22 g0  = refl
toA4-hom-g22 g1  = refl
toA4-hom-g22 g2  = refl
toA4-hom-g22 g3  = refl
toA4-hom-g22 g4  = refl
toA4-hom-g22 g5  = refl
toA4-hom-g22 g6  = refl
toA4-hom-g22 g7  = refl
toA4-hom-g22 g8  = refl
toA4-hom-g22 g9  = refl
toA4-hom-g22 g10 = refl
toA4-hom-g22 g11 = refl
toA4-hom-g22 g12 = refl
toA4-hom-g22 g13 = refl
toA4-hom-g22 g14 = refl
toA4-hom-g22 g15 = refl
toA4-hom-g22 g16 = refl
toA4-hom-g22 g17 = refl
toA4-hom-g22 g18 = refl
toA4-hom-g22 g19 = refl
toA4-hom-g22 g20 = refl
toA4-hom-g22 g21 = refl
toA4-hom-g22 g22 = refl
toA4-hom-g22 g23 = refl

toA4-hom-g23 : ∀ (y : SL23) → toA4 (g23 ⊗ y) ≡ toA4 g23 ⊗A toA4 y
toA4-hom-g23 g0  = refl
toA4-hom-g23 g1  = refl
toA4-hom-g23 g2  = refl
toA4-hom-g23 g3  = refl
toA4-hom-g23 g4  = refl
toA4-hom-g23 g5  = refl
toA4-hom-g23 g6  = refl
toA4-hom-g23 g7  = refl
toA4-hom-g23 g8  = refl
toA4-hom-g23 g9  = refl
toA4-hom-g23 g10 = refl
toA4-hom-g23 g11 = refl
toA4-hom-g23 g12 = refl
toA4-hom-g23 g13 = refl
toA4-hom-g23 g14 = refl
toA4-hom-g23 g15 = refl
toA4-hom-g23 g16 = refl
toA4-hom-g23 g17 = refl
toA4-hom-g23 g18 = refl
toA4-hom-g23 g19 = refl
toA4-hom-g23 g20 = refl
toA4-hom-g23 g21 = refl
toA4-hom-g23 g22 = refl
toA4-hom-g23 g23 = refl

--------------------------------------------------------------------------------
-- §2 组装：toA4 是同态
--------------------------------------------------------------------------------

toA4-hom : ∀ (x y : SL23) → toA4 (x ⊗ y) ≡ toA4 x ⊗A toA4 y
toA4-hom g0  = toA4-hom-g0
toA4-hom g1  = toA4-hom-g1
toA4-hom g2  = toA4-hom-g2
toA4-hom g3  = toA4-hom-g3
toA4-hom g4  = toA4-hom-g4
toA4-hom g5  = toA4-hom-g5
toA4-hom g6  = toA4-hom-g6
toA4-hom g7  = toA4-hom-g7
toA4-hom g8  = toA4-hom-g8
toA4-hom g9  = toA4-hom-g9
toA4-hom g10 = toA4-hom-g10
toA4-hom g11 = toA4-hom-g11
toA4-hom g12 = toA4-hom-g12
toA4-hom g13 = toA4-hom-g13
toA4-hom g14 = toA4-hom-g14
toA4-hom g15 = toA4-hom-g15
toA4-hom g16 = toA4-hom-g16
toA4-hom g17 = toA4-hom-g17
toA4-hom g18 = toA4-hom-g18
toA4-hom g19 = toA4-hom-g19
toA4-hom g20 = toA4-hom-g20
toA4-hom g21 = toA4-hom-g21
toA4-hom g22 = toA4-hom-g22
toA4-hom g23 = toA4-hom-g23

--------------------------------------------------------------------------------
-- §2.5 非平凡性核查：A₄ 非交换 ⇒ 交换参数会得到**不同**结果
--
--   这条不是装饰：它说明 §1 的 576 条 refl 对参数次序敏感，
--   因而 `toA4-hom` 不可能是空转恒真（若把两边都写成同序，它会失败）。
--------------------------------------------------------------------------------

toA4-order-matters : (toA4 g0 ⊗A toA4 g1) ≢ (toA4 g1 ⊗A toA4 g0)
toA4-order-matters = λ ()

--------------------------------------------------------------------------------
-- §3 表示沿同态拉回（A₄ 的乘法特征标 ⇒ SL23 的乘法特征标）
--
--   这是 `CharTable2A4` §10(a) 缺的那一步：有了 `toA4-hom`，
--   A₄ 的 1 维 / 3 维表示自动成为 2A₄ 的表示，且乘法性由上式搬运而来。
--------------------------------------------------------------------------------

pullback-multiplicative :
    ∀ (ψ : A4 → Zω)
    → (∀ (a b : A4) → ψ (a ⊗A b) ≡ mulZω (ψ a) (ψ b))
    → ∀ (x y : SL23) → ψ (toA4 (x ⊗ y)) ≡ mulZω (ψ (toA4 x)) (ψ (toA4 y))
pullback-multiplicative ψ ψ-hom x y =
  trans (cong ψ (toA4-hom x y)) (ψ-hom (toA4 x) (toA4 y))

--------------------------------------------------------------------------------
-- §4 核 = {I, −I}（由 kernel-spec 推出，不是重新枚举）
--
--   若 toA4 x ≡ Id，则 perm (toA4 x) ≡ perm Id，逐点即 permAt (toMat x) i ≡ i，
--   于是 kernel-spec 给出 x ≡ I 或 x ≡ −I。
--   （perm Id i 按定义就是 i，所以这一步是定义化归约，无需额外枚举。）
--------------------------------------------------------------------------------

toA4-kernel : ∀ (x : SL23) → toA4 x ≡ Id → (x ≡ g6) ⊎ (x ≡ g15)
toA4-kernel x e = kernel-spec x (λ i → trans (image-in-A4 x i) (cong (λ a → perm a i) e))

-- 单位元与 −I 都在核里（方向相反的包含，由 perm-id / perm-negI 支撑）
toA4-kernel-members : (toA4 g6 ≡ Id) × (toA4 g15 ≡ Id)
toA4-kernel-members = refl , refl

--------------------------------------------------------------------------------
-- §4 打包：A₄ ≅ SL23/{±I} 的群论面
--
--   同态 + 满射 + 核 = {±I} 三条合起来是"诱导单射 SL23/{±I} ↪ A₄ 且满"，
--   即 |SL23/{±I}| = 12 = |A₄|。**商群本身**（setoid 商 + 泛性质）不在库，
--   所以这里给的是覆盖数据，不是 GroupIsomorphism。
--------------------------------------------------------------------------------

record ToA4CoverData : Set where
  field
    hom           : ∀ (x y : SL23) → toA4 (x ⊗ y) ≡ toA4 x ⊗A toA4 y
    surj          : ∀ (a : A4) → Σ SL23 (λ x → toA4 x ≡ a)
    kernel-exact  : ∀ (x : SL23) → toA4 x ≡ Id → (x ≡ g6) ⊎ (x ≡ g15)
    kernel-member : (toA4 g6 ≡ Id) × (toA4 g15 ≡ Id)

toA4CoverData : ToA4CoverData
toA4CoverData = record
  { hom           = toA4-hom
  ; surj          = toA4-surj
  ; kernel-exact  = toA4-kernel
  ; kernel-member = toA4-kernel-members
  }
