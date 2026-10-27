{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Synthesis.A4.SL23QuotientUniversal
--
-- **商群的泛性质**：`SL(2,F₃)/{±I}` 是「把 −I 打到单位元」的**万有**解。
--
-- 数学内容（三条，缺一条就不叫商群）：
--   ① 最小性：任何含 `(−I, e)` 且右乘兼容的关系，都必然含整个 `≈±`
--      —— 所以 `≈±` 不是"随手挑的关系"，而是最小的那个；
--   ② 因子化存在：任何 setoid 群同态 `f : SL23 → H` 若把 −I 打到 e，
--      就**穿过**商关系（`x ≈± y ⇒ f x ≈_H f y`）—— 这是良定义性；
--   ③ 唯一性：穿过商的同态在同态意义下唯一。
--
-- 同态概念库内原本没有（`_PN5` 注释明说"本库无通用 GroupHom"），故此处给出
-- 最小定义 `SetoidGroupMap`：保 ≈ + 保乘法。（不要求保单位：群同态中单位由
-- 乘法+消去导出，本证明也用不到。）
--
-- 0 postulate / 0 hole。
module Sovereign.Synthesis.A4.SL23QuotientUniversal where

open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂; subst)

open import _PN15 using (SetoidGroupData)

open import Sovereign.Synthesis.Representation.SL23Cayley using (_⊗_)
open import Sovereign.Synthesis.A4.BinaryTetrahedralDefiningRep using (SL23; g6; g15)
open import Sovereign.Synthesis.A4.SL23Inverse using (invSL; invSL-left; invSL-right)
open import Sovereign.Synthesis.A4.SL23Group using (⊗-assocSL; ⊗-idˡ; ⊗-idʳ)
open import Sovereign.Synthesis.A4.SL23Quotient
  using (_≈±_; ≈±-refl; ≈±-trans; SL23-quotient)

--------------------------------------------------------------------------------
-- ① 同态概念（最小定义：保 ≈、保乘法）
--------------------------------------------------------------------------------

record SetoidGroupMap (S T : SetoidGroupData) : Set₁ where
  private
    module S' = SetoidGroupData S
    module T' = SetoidGroupData T
  field
    map      : S'.Carrier → T'.Carrier
    map-cong : ∀ {x y} → S'._≈_ x y → T'._≈_ (map x) (map y)
    map-mul  : ∀ x y → T'._≈_ (map (S'._⋆_ x y)) (T'._⋆_ (map x) (map y))

--------------------------------------------------------------------------------
-- ② 离散 setoid 群 SL23（≈ 取命题相等；群律全部取自 SL23Group）
--
--    商群的"出发对象"：对这个离散群再商掉 ±I，就是 `SL23-quotient`。
--------------------------------------------------------------------------------

SL23-discrete : SetoidGroupData
SL23-discrete = record
  { Carrier  = SL23
  ; _≈_      = _≡_
  ; refl≈    = refl
  ; sym≈     = sym
  ; trans≈   = trans
  ; _⋆_      = _⊗_
  ; ⋆-cong   = cong₂ _⊗_
  ; e₀       = g6
  ; ι        = invSL
  ; unitˡ    = ⊗-idˡ
  ; unitʳ    = ⊗-idʳ
  ; invˡ     = invSL-left
  ; invʳ     = invSL-right
  ; assoc    = ⊗-assocSL
  }

--------------------------------------------------------------------------------
-- ③ 最小性：`≈±` ⊆ 任何含 (−I, e) 且右乘兼容的关系
--
--    x ≈± y 只有两种来源：
--      x ≡ y           ⇒ 自反即可；
--      x ≡ y·(−I)      ⇒ 右乘兼容把 (−I, e) 变成 (y·(−I), y·e)，
--                        再用 y·e = y 与 x ≡ y·(−I) 搬过去。
--------------------------------------------------------------------------------

≈±-least :
    ∀ (R : SL23 → SL23 → Set)
    → (∀ x → R x x)                                              -- 自反
    → (∀ (a : SL23) {b c : SL23} → R b c → R (a ⊗ b) (a ⊗ c))     -- 右乘兼容
    → R g15 g6
    → ∀ {x y : SL23} → x ≈± y → R x y
≈±-least R R-refl R-right R-g15 {x} {y} (inj₁ e) =
  subst (λ z → R x z) e (R-refl x)
≈±-least R R-refl R-right R-g15 {x} {y} (inj₂ e) =
  subst (λ z → R z y) (sym e) step₂
  where
    -- R (y·(−I)) (y·e)，再用 y·e = y 变成 R (y·(−I)) y
    step₁ : R (y ⊗ g15) (y ⊗ g6)
    step₁ = R-right y R-g15

    step₂ : R (y ⊗ g15) y
    step₂ = subst (λ z → R (y ⊗ g15) z) (⊗-idʳ y) step₁

--------------------------------------------------------------------------------
-- ④ 因子化：把 −I 打到 e 的同态，必然尊重商关系
--
--    四步链（H 内）：
--      f x ≈ f (y·(−I)) ≈ f y ⋆ f (−I) ≈ f y ⋆ e ≈ f y
--------------------------------------------------------------------------------

module Factorization
    {H : SetoidGroupData}
    (f : SetoidGroupMap SL23-discrete H)
    (f-kills : SetoidGroupData._≈_ H
                 (SetoidGroupMap.map f g15) (SetoidGroupData.e₀ H))
  where

  private
    module H' = SetoidGroupData H
    module F  = SetoidGroupMap f

  -- 命题相等 ⇒ H 的 ≈（自反 + 搬运）
  ≡→≈H : ∀ {x y : SL23} → x ≡ y → H'._≈_ (F.map x) (F.map y)
  ≡→≈H {x} e = subst (λ z → H'._≈_ (F.map x) (F.map z)) e H'.refl≈

  factors : ∀ {x y : SL23} → x ≈± y → H'._≈_ (F.map x) (F.map y)
  factors {x} {y} (inj₁ e) = ≡→≈H e
  factors {x} {y} (inj₂ e) =
    H'.trans≈ (≡→≈H e)
      (H'.trans≈ (F.map-mul y g15)
        (H'.trans≈ (H'.⋆-cong H'.refl≈ f-kills)
          (H'.unitʳ (F.map y))))

--------------------------------------------------------------------------------
-- ⑤ 万有性：唯一因子化
--
--    "lift" 的映射就是 f 本身（商载体 = SL23），内容在于 `map-cong`
--    必须是 `factors` —— 即 f 确实穿过 ≈±；唯一性靠 H 的 ≈ 传递性。
--------------------------------------------------------------------------------

record UniqueLift {H : SetoidGroupData} (f : SetoidGroupMap SL23-discrete H) : Set₂ where
  field
    lift   : SetoidGroupMap SL23-quotient H
    agrees : ∀ x → SetoidGroupData._≈_ H
                     (SetoidGroupMap.map lift x) (SetoidGroupMap.map f x)
    unique : ∀ (g : SetoidGroupMap SL23-quotient H)
           → (∀ x → SetoidGroupData._≈_ H
                      (SetoidGroupMap.map g x) (SetoidGroupMap.map f x))
           → ∀ x → SetoidGroupData._≈_ H
                     (SetoidGroupMap.map g x) (SetoidGroupMap.map lift x)

quot-universal :
    ∀ (H : SetoidGroupData) (f : SetoidGroupMap SL23-discrete H)
    → SetoidGroupData._≈_ H
        (SetoidGroupMap.map f g15) (SetoidGroupData.e₀ H)
    → UniqueLift f
quot-universal H f f-kills = record
  { lift   = record
      { map      = SetoidGroupMap.map f
      ; map-cong = Factorization.factors f f-kills
      ; map-mul  = SetoidGroupMap.map-mul f
      }
  ; agrees = λ x → SetoidGroupData.refl≈ H
  ; unique = λ g ag x → SetoidGroupData.trans≈ H (ag x) (SetoidGroupData.refl≈ H)
  }
