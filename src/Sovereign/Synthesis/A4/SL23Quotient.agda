{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Synthesis.A4.SL23Quotient
--
-- **商群 `SL(2,F₃)/{±I}` ≅ A₄`（setoid 群同构）**
--
-- 数学背景：2A₄ = SL(2,F₃) 的中心是 {±I}，而 A₄ = PSL(2,F₃) 是它除掉中心。
-- 本文件不重造商结构，而是复用库里已有的 **`SetoidGroupData` / `SetoidGroupIso`**
-- （见 `pn-proofs/_PN15.agda`，B₃ 那条链也正是用它们）；商关系取
--
--     x ≈± y  ⟺  x ≡ y  或  x ≡ y·(−I)
--
-- 这不是"随手取的等价关系"：由 `g15-central`（−I 中心）与 `g15-invol`（(−I)² = I）
-- 它才成为同余；①–⑤ 把这些前提逐条证出来，⑥ 才装配成 setoid 群。
--
-- 关键点：**A₄ 侧的群律不是新证 12³ 案**，而是沿满射 `toA4-surj` 从 SL23 搬过去
-- （SL23 的群律已在 `SL23Group` 证毕）：A₄ 的每个元素都有原像，等式两边拉到原像上
-- 用 `toA4-hom` + `⊗-assocSL` 比较，再推回。
--
-- 包含：
--   ① g15-central / g15-invol / g15-not-g6            （−I 中心 + 对合 + 非平凡）
--   ② absorb-right / double-m / absorb-both           （关系封闭用的移位件）
--   ③ _≈±_ + refl/sym/trans                            （等价关系）
--   ④ ⊗-cong±                                          （乘法良定义）
--   ⑤ inv-cong±                                        （逆良定义）
--   ⑥ SL23-quotient : SetoidGroupData
--   ⑦ invA4G 与其双侧逆（12 案）+ A4 单位律/结合律（沿满射搬运）
--   ⑧ A4-setoid : SetoidGroupData
--   ⑨ toA4-cong± / toA4-reflect                        （商关系 ↔ toA4 相等）
--   ⑩ sectA4 + SetoidGroupIso SL23-quotient A4-setoid
--
-- 0 postulate / 0 hole。每条主引理 ≤4 步代数链，前提均具名。
module Sovereign.Synthesis.A4.SL23Quotient where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin using (zero; suc)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong; cong₂; module ≡-Reasoning)

open ≡-Reasoning

open import _PN15 using (SetoidGroupData; SetoidGroupIso)

open import Sovereign.Synthesis.Representation.SL23Cayley using (_⊗_)
open import Sovereign.Synthesis.A4.BinaryTetrahedralDefiningRep
  using (SL23; g0; g1; g2; g3; g4; g5; g6; g7; g8; g9; g10; g11
        ; g12; g13; g14; g15; g16; g17; g18; g19; g20; g21; g22; g23)
open import Sovereign.Synthesis.A4.SL23Inverse
  using (invSL; invSL-left; invSL-right)
open import Sovereign.Synthesis.A4.SL23Group
  using (⊗-assocSL; ⊗-idˡ; ⊗-idʳ; invSL-antihom)

import Sovereign.Synthesis.A4.A4Group as A4G
open A4G using (A4; Id; Rot; Flip)

open import Sovereign.Synthesis.A4.CoverA4 using (toA4; toA4-surj)
open import Sovereign.Synthesis.A4.ToA4Hom
  using (_⊗A_; toA4-hom; toA4-kernel; toA4-kernel-members)

--------------------------------------------------------------------------------
-- ① 中心元 −I（g15）的三条基本事实
--------------------------------------------------------------------------------

-- | −I 与所有元素交换（24 案；这是商关系成为同余的**核心**前提）
g15-central : ∀ (x : SL23) → g15 ⊗ x ≡ x ⊗ g15
g15-central g0  = refl
g15-central g1  = refl
g15-central g2  = refl
g15-central g3  = refl
g15-central g4  = refl
g15-central g5  = refl
g15-central g6  = refl
g15-central g7  = refl
g15-central g8  = refl
g15-central g9  = refl
g15-central g10 = refl
g15-central g11 = refl
g15-central g12 = refl
g15-central g13 = refl
g15-central g14 = refl
g15-central g15 = refl
g15-central g16 = refl
g15-central g17 = refl
g15-central g18 = refl
g15-central g19 = refl
g15-central g20 = refl
g15-central g21 = refl
g15-central g22 = refl
g15-central g23 = refl

-- | (−I)² = I
g15-invol : g15 ⊗ g15 ≡ g6
g15-invol = refl

-- | −I ≠ I（商确实把两个元素并成一个，不是平凡关系）
g15-not-g6 : g15 ≢ g6
g15-not-g6 = λ ()

--------------------------------------------------------------------------------
-- ② 移位件：把 −I 在乘积里搬到最右边、以及成对消去
--------------------------------------------------------------------------------

-- | (x·m)·y ≡ (x·y)·m —— 先结合、再用 m 中心、再收回结合
absorb-right : ∀ (x y : SL23) → (x ⊗ g15) ⊗ y ≡ (x ⊗ y) ⊗ g15
absorb-right x y = begin
    (x ⊗ g15) ⊗ y
  ≡⟨ ⊗-assocSL x g15 y ⟩                        -- 结合
    x ⊗ (g15 ⊗ y)
  ≡⟨ cong (x ⊗_) (g15-central y) ⟩               -- m 中心：m·y → y·m
    x ⊗ (y ⊗ g15)
  ≡⟨ sym (⊗-assocSL x y g15) ⟩                   -- 收回结合
    (x ⊗ y) ⊗ g15 ∎

-- | (x·m)·m ≡ x —— m 对合
double-m : ∀ (x : SL23) → (x ⊗ g15) ⊗ g15 ≡ x
double-m x = begin
    (x ⊗ g15) ⊗ g15
  ≡⟨ ⊗-assocSL x g15 g15 ⟩
    x ⊗ (g15 ⊗ g15)
  ≡⟨ cong (x ⊗_) g15-invol ⟩
    x ⊗ g6
  ≡⟨ ⊗-idʳ x ⟩
    x ∎

-- | (x·m)·(y·m) ≡ x·y —— 两个 −I 成对消去
absorb-both : ∀ (x y : SL23) → (x ⊗ g15) ⊗ (y ⊗ g15) ≡ x ⊗ y
absorb-both x y = begin
    (x ⊗ g15) ⊗ (y ⊗ g15)
  ≡⟨ absorb-right x (y ⊗ g15) ⟩
    (x ⊗ (y ⊗ g15)) ⊗ g15
  ≡⟨ cong (_⊗ g15) (sym (⊗-assocSL x y g15)) ⟩
    ((x ⊗ y) ⊗ g15) ⊗ g15
  ≡⟨ double-m (x ⊗ y) ⟩
    x ⊗ y ∎

--------------------------------------------------------------------------------
-- ③ 商关系（等价关系）
--------------------------------------------------------------------------------

-- | x ≈± y : 相差一个 −I
_≈±_ : SL23 → SL23 → Set
x ≈± y = (x ≡ y) ⊎ (x ≡ y ⊗ g15)

≈±-refl : ∀ {x : SL23} → x ≈± x
≈±-refl = inj₁ refl

-- | 对称：x = y·m ⇒ y = x·m（两边同乘 m 并用 m² = I）
≈±-sym : ∀ {x y : SL23} → x ≈± y → y ≈± x
≈±-sym {x} {y} (inj₁ e) = inj₁ (sym e)
≈±-sym {x} {y} (inj₂ e) = inj₂ (begin
    y
  ≡⟨ sym (⊗-idʳ y) ⟩
    y ⊗ g6
  ≡⟨ cong (y ⊗_) (sym g15-invol) ⟩
    y ⊗ (g15 ⊗ g15)
  ≡⟨ sym (⊗-assocSL y g15 g15) ⟩
    (y ⊗ g15) ⊗ g15
  ≡⟨ cong (_⊗ g15) (sym e) ⟩
    x ⊗ g15 ∎)

-- | 传递（4 案；唯一需要移位的是 (m,m) 案）
≈±-trans : ∀ {x y z : SL23} → x ≈± y → y ≈± z → x ≈± z
≈±-trans {x} {y} {z} (inj₁ e₁) (inj₁ e₂) = inj₁ (trans e₁ e₂)
≈±-trans {x} {y} {z} (inj₁ e₁) (inj₂ e₂) = inj₂ (trans e₁ e₂)
≈±-trans {x} {y} {z} (inj₂ e₁) (inj₁ e₂) = inj₂ (trans e₁ (cong (_⊗ g15) e₂))
≈±-trans {x} {y} {z} (inj₂ e₁) (inj₂ e₂) = inj₁ (begin
    x
  ≡⟨ e₁ ⟩
    y ⊗ g15
  ≡⟨ cong (_⊗ g15) e₂ ⟩
    (z ⊗ g15) ⊗ g15
  ≡⟨ double-m z ⟩
    z ∎)

--------------------------------------------------------------------------------
-- ④ 乘法良定义（4 案）
--------------------------------------------------------------------------------

⊗-cong± : ∀ {a b c d : SL23} → a ≈± c → b ≈± d → (a ⊗ b) ≈± (c ⊗ d)
⊗-cong± {a} {b} {c} {d} (inj₁ e₁) (inj₁ e₂) = inj₁ (cong₂ _⊗_ e₁ e₂)
⊗-cong± {a} {b} {c} {d} (inj₁ e₁) (inj₂ e₂) = inj₂ (begin
    a ⊗ b
  ≡⟨ cong₂ _⊗_ e₁ e₂ ⟩
    c ⊗ (d ⊗ g15)
  ≡⟨ sym (⊗-assocSL c d g15) ⟩
    (c ⊗ d) ⊗ g15 ∎)
⊗-cong± {a} {b} {c} {d} (inj₂ e₁) (inj₁ e₂) = inj₂ (begin
    a ⊗ b
  ≡⟨ cong₂ _⊗_ e₁ e₂ ⟩
    (c ⊗ g15) ⊗ d
  ≡⟨ absorb-right c d ⟩
    (c ⊗ d) ⊗ g15 ∎)
⊗-cong± {a} {b} {c} {d} (inj₂ e₁) (inj₂ e₂) = inj₁ (begin
    a ⊗ b
  ≡⟨ cong₂ _⊗_ e₁ e₂ ⟩
    (c ⊗ g15) ⊗ (d ⊗ g15)
  ≡⟨ absorb-both c d ⟩
    c ⊗ d ∎)

--------------------------------------------------------------------------------
-- ⑤ 逆良定义
--------------------------------------------------------------------------------

invSL-g15 : invSL g15 ≡ g15
invSL-g15 = refl

-- | x ≈± y ⇒ x⁻¹ ≈± y⁻¹（用反同态把 −I 推到左边，再用中心性推到右边）
inv-cong± : ∀ {x y : SL23} → x ≈± y → invSL x ≈± invSL y
inv-cong± {x} {y} (inj₁ e) = inj₁ (cong invSL e)
inv-cong± {x} {y} (inj₂ e) = inj₂ (begin
    invSL x
  ≡⟨ cong invSL e ⟩
    invSL (y ⊗ g15)
  ≡⟨ invSL-antihom y g15 ⟩
    invSL g15 ⊗ invSL y
  ≡⟨ cong (_⊗ invSL y) invSL-g15 ⟩
    g15 ⊗ invSL y
  ≡⟨ g15-central (invSL y) ⟩
    invSL y ⊗ g15 ∎)

--------------------------------------------------------------------------------
-- ⑥ 商群：SL(2,F₃)/{±I} 作为 setoid 群
--------------------------------------------------------------------------------

SL23-quotient : SetoidGroupData
SL23-quotient = record
  { Carrier  = SL23
  ; _≈_      = _≈±_
  ; refl≈    = ≈±-refl
  ; sym≈     = ≈±-sym
  ; trans≈   = ≈±-trans
  ; _⋆_      = _⊗_
  ; ⋆-cong   = ⊗-cong±
  ; e₀       = g6
  ; ι        = invSL
  ; unitˡ    = λ x → inj₁ (⊗-idˡ x)
  ; unitʳ    = λ x → inj₁ (⊗-idʳ x)
  ; invˡ     = λ x → inj₁ (invSL-left x)
  ; invʳ     = λ x → inj₁ (invSL-right x)
  ; assoc    = λ x y z → inj₁ (⊗-assocSL x y z)
  }

--------------------------------------------------------------------------------
-- ⑦ A₄ 侧：逆（12 案）与群律（沿满射搬运，不新枚举 12³）
--------------------------------------------------------------------------------

invA4G : A4 → A4
invA4G Id                        = Id
invA4G (Rot zero zero)           = Rot zero (suc zero)
invA4G (Rot zero (suc zero))     = Rot zero zero
invA4G (Rot (suc zero) zero)     = Rot (suc zero) (suc zero)
invA4G (Rot (suc zero) (suc zero)) = Rot (suc zero) zero
invA4G (Rot (suc (suc zero)) zero) = Rot (suc (suc zero)) (suc zero)
invA4G (Rot (suc (suc zero)) (suc zero)) = Rot (suc (suc zero)) zero
invA4G (Rot (suc (suc (suc zero))) zero) = Rot (suc (suc (suc zero))) (suc zero)
invA4G (Rot (suc (suc (suc zero))) (suc zero)) = Rot (suc (suc (suc zero))) zero
invA4G (Flip zero)               = Flip zero
invA4G (Flip (suc zero))         = Flip (suc zero)
invA4G (Flip (suc (suc zero)))   = Flip (suc (suc zero))

-- | A₄ 的逆与 SL23 的逆相容（24 案）
invA4-cong-toA4 : ∀ (x : SL23) → invA4G (toA4 x) ≡ toA4 (invSL x)
invA4-cong-toA4 g0  = refl
invA4-cong-toA4 g1  = refl
invA4-cong-toA4 g2  = refl
invA4-cong-toA4 g3  = refl
invA4-cong-toA4 g4  = refl
invA4-cong-toA4 g5  = refl
invA4-cong-toA4 g6  = refl
invA4-cong-toA4 g7  = refl
invA4-cong-toA4 g8  = refl
invA4-cong-toA4 g9  = refl
invA4-cong-toA4 g10 = refl
invA4-cong-toA4 g11 = refl
invA4-cong-toA4 g12 = refl
invA4-cong-toA4 g13 = refl
invA4-cong-toA4 g14 = refl
invA4-cong-toA4 g15 = refl
invA4-cong-toA4 g16 = refl
invA4-cong-toA4 g17 = refl
invA4-cong-toA4 g18 = refl
invA4-cong-toA4 g19 = refl
invA4-cong-toA4 g20 = refl
invA4-cong-toA4 g21 = refl
invA4-cong-toA4 g22 = refl
invA4-cong-toA4 g23 = refl

-- 单位元在 toA4 下的像（取自 ToA4Hom 的核成员事实）
toA4-g6 : toA4 g6 ≡ Id
toA4-g6 = proj₁ toA4-kernel-members

toA4-g15 : toA4 g15 ≡ Id
toA4-g15 = proj₂ toA4-kernel-members

-- | 把 toA4 x ⊗A toA4 y 拉回 toA4 (x ⊗ y)
pullA : ∀ (x y : SL23) → toA4 x ⊗A toA4 y ≡ toA4 (x ⊗ y)
pullA x y = sym (toA4-hom x y)

-- | A₄ 右单位（沿满射搬运：a = toA4 x ⇒ 两边拉回 SL23 用 ⊗-idʳ）
⊗A-idʳ : ∀ (a : A4) → a ⊗A Id ≡ a
⊗A-idʳ a with toA4-surj a
... | x , refl = begin
    toA4 x ⊗A Id
  ≡⟨ cong (toA4 x ⊗A_) (sym toA4-g6) ⟩
    toA4 x ⊗A toA4 g6
  ≡⟨ pullA x g6 ⟩
    toA4 (x ⊗ g6)
  ≡⟨ cong toA4 (⊗-idʳ x) ⟩
    toA4 x ∎

-- | A₄ 左单位
⊗A-idˡ : ∀ (a : A4) → Id ⊗A a ≡ a
⊗A-idˡ a with toA4-surj a
... | x , refl = begin
    Id ⊗A toA4 x
  ≡⟨ cong (_⊗A toA4 x) (sym toA4-g6) ⟩
    toA4 g6 ⊗A toA4 x
  ≡⟨ pullA g6 x ⟩
    toA4 (g6 ⊗ x)
  ≡⟨ cong toA4 (⊗-idˡ x) ⟩
    toA4 x ∎

-- 结合律搬运的两个半步（各 ≤3 步，避免长嵌套）
⊗A-assoc-step₁ : ∀ (x y z : SL23)
               → (toA4 x ⊗A toA4 y) ⊗A toA4 z ≡ toA4 ((x ⊗ y) ⊗ z)
⊗A-assoc-step₁ x y z = begin
    (toA4 x ⊗A toA4 y) ⊗A toA4 z
  ≡⟨ cong (_⊗A toA4 z) (pullA x y) ⟩
    toA4 (x ⊗ y) ⊗A toA4 z
  ≡⟨ pullA (x ⊗ y) z ⟩
    toA4 ((x ⊗ y) ⊗ z) ∎

⊗A-assoc-step₂ : ∀ (x y z : SL23)
               → toA4 ((x ⊗ y) ⊗ z) ≡ toA4 x ⊗A (toA4 y ⊗A toA4 z)
⊗A-assoc-step₂ x y z = begin
    toA4 ((x ⊗ y) ⊗ z)
  ≡⟨ cong toA4 (⊗-assocSL x y z) ⟩
    toA4 (x ⊗ (y ⊗ z))
  ≡⟨ toA4-hom x (y ⊗ z) ⟩
    toA4 x ⊗A toA4 (y ⊗ z)
  ≡⟨ cong (toA4 x ⊗A_) (toA4-hom y z) ⟩
    toA4 x ⊗A (toA4 y ⊗A toA4 z) ∎

-- | A₄ 结合律（三个原像一次取，随后 trans 两个半步）
⊗A-assoc : ∀ (a b c : A4) → (a ⊗A b) ⊗A c ≡ a ⊗A (b ⊗A c)
⊗A-assoc a b c with toA4-surj a | toA4-surj b | toA4-surj c
... | x , refl | y , refl | z , refl =
  trans (⊗A-assoc-step₁ x y z) (⊗A-assoc-step₂ x y z)

-- | A₄ 左逆
invA4-left : ∀ (a : A4) → invA4G a ⊗A a ≡ Id
invA4-left a with toA4-surj a
... | x , refl = begin
    invA4G (toA4 x) ⊗A toA4 x
  ≡⟨ cong (_⊗A toA4 x) (invA4-cong-toA4 x) ⟩
    toA4 (invSL x) ⊗A toA4 x
  ≡⟨ pullA (invSL x) x ⟩
    toA4 (invSL x ⊗ x)
  ≡⟨ cong toA4 (invSL-left x) ⟩
    toA4 g6
  ≡⟨ toA4-g6 ⟩
    Id ∎

-- | A₄ 右逆
invA4-right : ∀ (a : A4) → a ⊗A invA4G a ≡ Id
invA4-right a with toA4-surj a
... | x , refl = begin
    toA4 x ⊗A invA4G (toA4 x)
  ≡⟨ cong (toA4 x ⊗A_) (invA4-cong-toA4 x) ⟩
    toA4 x ⊗A toA4 (invSL x)
  ≡⟨ pullA x (invSL x) ⟩
    toA4 (x ⊗ invSL x)
  ≡⟨ cong toA4 (invSL-right x) ⟩
    toA4 g6
  ≡⟨ toA4-g6 ⟩
    Id ∎

-- | A₄ 作为 setoid 群（≈ 取命题相等 ⇒ 离散 setoid）
A4-setoid : SetoidGroupData
A4-setoid = record
  { Carrier  = A4
  ; _≈_      = _≡_
  ; refl≈    = refl
  ; sym≈     = sym
  ; trans≈   = trans
  ; _⋆_      = _⊗A_
  ; ⋆-cong   = cong₂ _⊗A_
  ; e₀       = Id
  ; ι        = invA4G
  ; unitˡ    = ⊗A-idˡ
  ; unitʳ    = ⊗A-idʳ
  ; invˡ     = invA4-left
  ; invʳ     = invA4-right
  ; assoc    = ⊗A-assoc
  }

--------------------------------------------------------------------------------
-- ⑧ 商关系 ↔ toA4 相等（两个方向）
--------------------------------------------------------------------------------

-- | 方向 1：≈± ⇒ toA4 相等（−I 在 A₄ 上是单位元）
toA4-cong± : ∀ {x y : SL23} → x ≈± y → toA4 x ≡ toA4 y
toA4-cong± {x} {y} (inj₁ e) = cong toA4 e
toA4-cong± {x} {y} (inj₂ e) = begin
    toA4 x
  ≡⟨ cong toA4 e ⟩
    toA4 (y ⊗ g15)
  ≡⟨ toA4-hom y g15 ⟩
    toA4 y ⊗A toA4 g15
  ≡⟨ cong (toA4 y ⊗A_) toA4-g15 ⟩
    toA4 y ⊗A Id
  ≡⟨ ⊗A-idʳ (toA4 y) ⟩
    toA4 y ∎

-- | 方向 2：toA4 相等 ⇒ ≈±（核心：x·y⁻¹ 落在核 {±I} 里）
toA4-reflect : ∀ (x y : SL23) → toA4 x ≡ toA4 y → x ≈± y
toA4-reflect x y e = split (toA4-kernel (x ⊗ invSL y) z-is-id)
  where
    -- toA4 (x·y⁻¹) = Id
    z-is-id : toA4 (x ⊗ invSL y) ≡ Id
    z-is-id = begin
        toA4 (x ⊗ invSL y)
      ≡⟨ toA4-hom x (invSL y) ⟩
        toA4 x ⊗A toA4 (invSL y)
      ≡⟨ cong (_⊗A toA4 (invSL y)) e ⟩
        toA4 y ⊗A toA4 (invSL y)
      ≡⟨ cong (toA4 y ⊗A_) (sym (invA4-cong-toA4 y)) ⟩
        toA4 y ⊗A invA4G (toA4 y)
      ≡⟨ invA4-right (toA4 y) ⟩
        Id ∎

    -- x ≡ (x·y⁻¹)·y 的两步引理
    x-as-prod : ∀ {z : SL23} → x ⊗ invSL y ≡ z → x ≡ z ⊗ y
    x-as-prod {z} h = begin
        x
      ≡⟨ sym (⊗-idʳ x) ⟩
        x ⊗ g6
      ≡⟨ cong (x ⊗_) (sym (invSL-left y)) ⟩
        x ⊗ (invSL y ⊗ y)
      ≡⟨ sym (⊗-assocSL x (invSL y) y) ⟩
        (x ⊗ invSL y) ⊗ y
      ≡⟨ cong (_⊗ y) h ⟩
        z ⊗ y ∎

    split : (x ⊗ invSL y ≡ g6) ⊎ (x ⊗ invSL y ≡ g15) → x ≈± y
    split (inj₁ h) = inj₁ (begin
        x
      ≡⟨ x-as-prod h ⟩
        g6 ⊗ y
      ≡⟨ ⊗-idˡ y ⟩
        y ∎)
    split (inj₂ h) = inj₂ (begin
        x
      ≡⟨ x-as-prod h ⟩
        g15 ⊗ y
      ≡⟨ g15-central y ⟩
        y ⊗ g15 ∎)

--------------------------------------------------------------------------------
-- ⑨ 截面 A₄ → SL23（取 toA4 的原像；12 案）与其左逆
--------------------------------------------------------------------------------

sectA4 : A4 → SL23
sectA4 Id                        = g6
sectA4 (Rot zero zero)           = g9
sectA4 (Rot zero (suc zero))     = g12
sectA4 (Rot (suc zero) zero)     = g7
sectA4 (Rot (suc zero) (suc zero)) = g8
sectA4 (Rot (suc (suc zero)) zero) = g2
sectA4 (Rot (suc (suc zero)) (suc zero)) = g11
sectA4 (Rot (suc (suc (suc zero))) zero) = g1
sectA4 (Rot (suc (suc (suc zero))) (suc zero)) = g13
sectA4 (Flip zero)               = g0
sectA4 (Flip (suc zero))         = g10
sectA4 (Flip (suc (suc zero)))   = g14

sectA4-retract : ∀ (a : A4) → toA4 (sectA4 a) ≡ a
sectA4-retract Id                        = refl
sectA4-retract (Rot zero zero)           = refl
sectA4-retract (Rot zero (suc zero))     = refl
sectA4-retract (Rot (suc zero) zero)     = refl
sectA4-retract (Rot (suc zero) (suc zero)) = refl
sectA4-retract (Rot (suc (suc zero)) zero) = refl
sectA4-retract (Rot (suc (suc zero)) (suc zero)) = refl
sectA4-retract (Rot (suc (suc (suc zero))) zero) = refl
sectA4-retract (Rot (suc (suc (suc zero))) (suc zero)) = refl
sectA4-retract (Flip zero)               = refl
sectA4-retract (Flip (suc zero))         = refl
sectA4-retract (Flip (suc (suc zero)))   = refl

--------------------------------------------------------------------------------
-- ⑩ 主定理：商群 ≅ A₄（setoid 群同构）
--------------------------------------------------------------------------------

-- | 截面保乘法（在商关系下）
sectA4-mul : ∀ (a b : A4)
           → sectA4 (a ⊗A b) ≈± (sectA4 a ⊗ sectA4 b)
sectA4-mul a b = toA4-reflect (sectA4 (a ⊗A b)) (sectA4 a ⊗ sectA4 b) (begin
    toA4 (sectA4 (a ⊗A b))
  ≡⟨ sectA4-retract (a ⊗A b) ⟩
    a ⊗A b
  ≡⟨ cong₂ _⊗A_ (sym (sectA4-retract a)) (sym (sectA4-retract b)) ⟩
    toA4 (sectA4 a) ⊗A toA4 (sectA4 b)
  ≡⟨ pullA (sectA4 a) (sectA4 b) ⟩
    toA4 (sectA4 a ⊗ sectA4 b) ∎)

-- | **SL(2,F₃)/{±I} ≅ A₄**
SL23-quotient-iso : SetoidGroupIso SL23-quotient A4-setoid
SL23-quotient-iso = record
  { to        = toA4
  ; from      = sectA4
  ; to-cong   = toA4-cong±
  ; from-cong = λ e → inj₁ (cong sectA4 e)
  ; to-mul    = toA4-hom
  ; from-mul  = sectA4-mul
  ; to-from   = sectA4-retract
  ; from-to   = λ x → toA4-reflect (sectA4 (toA4 x)) x (sectA4-retract (toA4 x))
  }
