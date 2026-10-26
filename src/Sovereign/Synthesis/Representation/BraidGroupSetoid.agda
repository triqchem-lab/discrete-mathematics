{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Synthesis.Representation.BraidGroupSetoid
-- **B₃ 的 setoid 展示**：`SetoidGroupData` + 两个生成元 + 辫关系（至 `≈`），
-- 并给出**具体模型** SL(2,F₃)。
--
-- 为什么新增而不是改写 `Algebra/GroupTheory/BraidGroup.B3`：
--   严格版 `B3` 用 `≡`，承载 `W-central-σ₁/σ₂`（(σ₁σ₂)³ 与生成元交换，60 行真内容）。
--   把 `≡` 改成 `≈` 会让那些证明全部作废——那是**裁剪成果凑形式**，不是改进。
--   正解是**泛化**：setoid 版是严格版的推广（取 `_≈_ := _≡_` 即得严格版），
--   严格版的每条定理仍成立、仍是更强陈述。
--   ⇒ 两版并存；`strict→setoid` 的强制转换留作后续（需先导出左逆，见 human_notes）。
--
-- 本模块交付：
--   ① `record B3Setoid`——B₃ 的 setoid 展示（载体群 + σ₁ σ₂ + braid-rel）
--   ② `SL2-B3Setoid : B3Setoid`——**具体模型**：SL(2,F₃)（缺口 2 的 setoid 口径闭合）
--   ③ `model-σ₁/σ₂`——模型的两个生成元就是 eval 的生成元像
--
-- ⚠ 边界：这是 B₃ 的**setoid 模型**，不是 `BraidGroup.B3`（严格 record）的实例。
--   严格实例需要 24 元载体（SL23）+ `toMat` 单射（576 例）+ assoc，约 700 行；
--   见 docs/ledger/BraidGroupSetoid.model.yaml 的路线记录。
--
-- 策略：对象级装配（record 实例）+ 具体计算（braid-rel 两侧都是具体矩阵，refl）
-- 0 postulate / 0 hole。

module Sovereign.Synthesis.Representation.BraidGroupSetoid where

open import Data.Bool using (true; false)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import _PN15 using (SetoidGroupData)

open import Sovereign.Synthesis.Representation.SL2SetoidGroup using
  ( SL2; sl2-mul; SL2-setoid-group )
open import Sovereign.Synthesis.Representation.SL2Bridge using (σ₁S; σ₂S; gen)
open import Sovereign.Algebra.GroupTheory.BraidCongruence using
  ( _≈b_; b-refl; b-sym; b-trans; b-braid; ≈b-cong
  ; unitˡ; unitʳ; assoc≈; ι; invˡ; invʳ )
open import Sovereign.Algebra.GroupTheory.Word using (Word; ε; _·a; _·b; _++W_; aba; bab)

--------------------------------------------------------------------------------
-- ① B₃ 的 setoid 展示
--------------------------------------------------------------------------------

record B3Setoid : Set₁ where
  field
    sg        : SetoidGroupData
    σ₁ σ₂     : SetoidGroupData.Carrier sg
    -- 唯一关系：σ₁·(σ₂·σ₁) ≈ σ₂·(σ₁·σ₂)
    braid-rel : SetoidGroupData._≈_ sg
                  (SetoidGroupData._⋆_ sg σ₁ (SetoidGroupData._⋆_ sg σ₂ σ₁))
                  (SetoidGroupData._⋆_ sg σ₂ (SetoidGroupData._⋆_ sg σ₁ σ₂))

--------------------------------------------------------------------------------
-- ② 具体模型：SL(2,F₃)
--
-- 辫关系在像里是**具体矩阵的等式**：两侧都算到同一个 SL(2,F₃) 元素，故 refl。
--------------------------------------------------------------------------------

SL2-braid-rel :
  SetoidGroupData._≈_ SL2-setoid-group
    (SetoidGroupData._⋆_ SL2-setoid-group σ₁S
      (SetoidGroupData._⋆_ SL2-setoid-group σ₂S σ₁S))
    (SetoidGroupData._⋆_ SL2-setoid-group σ₂S
      (SetoidGroupData._⋆_ SL2-setoid-group σ₁S σ₂S))
SL2-braid-rel = refl

SL2-B3Setoid : B3Setoid
SL2-B3Setoid = record
  { sg        = SL2-setoid-group
  ; σ₁        = σ₁S
  ; σ₂        = σ₂S
  ; braid-rel = SL2-braid-rel
  }

-- 模型的两个生成元就是 eval 的生成元像（true ↦ σ₁，false ↦ σ₂）
model-σ₁ : gen true ≡ σ₁S
model-σ₁ = refl

model-σ₂ : gen false ≡ σ₂S
model-σ₂ = refl

--------------------------------------------------------------------------------
-- ③ 词商 `Word / ≈b` 本身也是一个 B₃ 展示（Q1g）
--
-- 这是「B₃ = F₂/⟨⟨aba·(bab)⁻¹⟩⟩」的可计算形态：
-- 载体 = 词，等价 = braid 同余，∘ = 拼接，e = 空词，逆 = ι。
--------------------------------------------------------------------------------

word-setoid-group : SetoidGroupData
word-setoid-group = record
  { Carrier  = Word
  ; _≈_      = _≈b_
  ; refl≈    = b-refl
  ; sym≈     = b-sym
  ; trans≈   = b-trans
  ; _⋆_      = _++W_
  ; ⋆-cong   = ≈b-cong
  ; e₀       = ε
  ; ι        = ι
  ; unitˡ    = unitˡ
  ; unitʳ    = unitʳ
  ; invˡ     = invˡ
  ; invʳ     = invʳ
  ; assoc    = assoc≈
  }

-- σ₁ = 单字母词 a，σ₂ = 单字母词 b；辫关系的两侧在拼接下**定义性**等于 aba / bab
Word-B3Setoid : B3Setoid
Word-B3Setoid = record
  { sg        = word-setoid-group
  ; σ₁        = ε ·a
  ; σ₂        = ε ·b
  ; braid-rel = b-braid
  }
