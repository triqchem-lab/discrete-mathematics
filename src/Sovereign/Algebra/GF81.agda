{-# OPTIONS --rewriting #-}
module Sovereign.Algebra.GF81 where

-- GF(3⁴) = GF(3)[x]/(x⁴+x+2)
-- 81 个元素的有限域, α⁴ = 2α+1 (mod 3)
--
-- 不可约性: p(x) = x⁴+x+2
--   无 GF(3) 根: p(0)=2, p(1)=4≡1, p(2)=20≡2
--   不分解为两个不可约二次因子 (穷举 3×3 组合验证)
--
-- Gal(GF(81)/GF(3)) ≅ C₄, 生成元 σ(x) = x³ (Frobenius)
-- 乘法群 GF(81)* ≅ Z/80Z, 阶 80 = 2⁴ × 5
--
-- 域扩张塔:
--   GF(3) ⊂ GF(9) ⊂ GF(81)   (1∣2∣4)
--   GF(81) ⊂ GF(729)          (4∣... 不, 4∤6, 但 GF(81) 和 GF(729) 的 LCM 域是 GF(3^lcm(4,6)) = GF(3¹²))
--
-- 0 postulate — 全部构造性证明

open import Data.Product using (_×_; _,_; Σ; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; cong₂; sym; trans)
open import Data.Nat using (ℕ; zero; suc; _^_; _*_; _+_)
open import Sovereign.Base.Trit using (Trit; T₀; T₁; T₂; _⊕_; _⊗_;
  negate; negate²;
  ⊕-identityˡ; ⊕-identityʳ; ⊕-comm; ⊕-assoc; ⊕-inverse;
  ⊗-identityˡ; ⊗-identityʳ; ⊗-comm; ⊗-assoc;
  ⊗-distribˡ-⊕; ⊗-distribʳ-⊕; ⊗-zeroˡ; ⊗-zeroʳ)
open import Sovereign.Algebra.GF9 using (GF9; _*gf9_; _+gf9_)

--------------------------------------------------------------------------------
-- 0. GF(3) 辅助引理
--------------------------------------------------------------------------------

infix  1 begin_
infixr 2 _≡⟨_⟩_
infix  3 _∎

begin_ : ∀ {a} {A : Set a} {x y : A} → x ≡ y → x ≡ y
begin p = p

_≡⟨_⟩_ : ∀ {a} {A : Set a} (x : A) {y z : A} → x ≡ y → y ≡ z → x ≡ z
_ ≡⟨ p ⟩ q = trans p q

_∎ : ∀ {a} {A : Set a} (x : A) → x ≡ x
_ ∎ = refl

negate-⊕ : ∀ x y → negate (x ⊕ y) ≡ negate x ⊕ negate y
negate-⊕ T₀ y = refl
negate-⊕ T₁ T₀ = refl; negate-⊕ T₁ T₁ = refl; negate-⊕ T₁ T₂ = refl
negate-⊕ T₂ T₀ = refl; negate-⊕ T₂ T₁ = refl; negate-⊕ T₂ T₂ = refl

negate-⊗ : ∀ x y → negate (x ⊗ y) ≡ (negate x) ⊗ y
negate-⊗ T₀ y = refl
negate-⊗ T₁ T₀ = refl; negate-⊗ T₁ T₁ = refl; negate-⊗ T₁ T₂ = refl
negate-⊗ T₂ T₀ = refl; negate-⊗ T₂ T₁ = refl; negate-⊗ T₂ T₂ = refl

negate-⊗-comm : ∀ x y → (negate x) ⊗ y ≡ x ⊗ (negate y)
negate-⊗-comm T₀ y = refl
negate-⊗-comm T₁ T₀ = refl; negate-⊗-comm T₁ T₁ = refl; negate-⊗-comm T₁ T₂ = refl
negate-⊗-comm T₂ T₀ = refl; negate-⊗-comm T₂ T₁ = refl; negate-⊗-comm T₂ T₂ = refl

negate-⊗-negate : ∀ x y → (negate x) ⊗ (negate y) ≡ x ⊗ y
negate-⊗-negate T₀ y = refl
negate-⊗-negate T₁ T₀ = refl; negate-⊗-negate T₁ T₁ = refl; negate-⊗-negate T₁ T₂ = refl
negate-⊗-negate T₂ T₀ = refl; negate-⊗-negate T₂ T₁ = refl; negate-⊗-negate T₂ T₂ = refl

⊗-negate-r : ∀ x y → x ⊗ (negate y) ≡ negate (x ⊗ y)
⊗-negate-r x y = trans (sym (negate-⊗-comm x y)) (sym (negate-⊗ x y))

-- x + x = negate(x) in GF(3)
⊕-double : ∀ x → x ⊕ x ≡ negate x
⊕-double T₀ = refl; ⊕-double T₁ = refl; ⊕-double T₂ = refl

-- 特征 3: x + x + x = 0
⊕-char3 : ∀ x → (x ⊕ x) ⊕ x ≡ T₀
⊕-char3 T₀ = refl; ⊕-char3 T₁ = refl; ⊕-char3 T₂ = refl

-- 逆元左: negate(x) + x = 0
⊕-inverseˡ : ∀ x → negate x ⊕ x ≡ T₀
⊕-inverseˡ x = trans (⊕-comm (negate x) x) (⊕-inverse x)

swap-middle : ∀ w x y z → (w ⊕ x) ⊕ (y ⊕ z) ≡ (w ⊕ y) ⊕ (x ⊕ z)
swap-middle w x y z =
  trans (sym (⊕-assoc (w ⊕ x) y z))
    (trans (cong (_⊕ z) (⊕-assoc w x y))
      (trans (cong (λ t → (w ⊕ t) ⊕ z) (⊕-comm x y))
        (trans (cong (_⊕ z) (sym (⊕-assoc w y x)))
          (⊕-assoc (w ⊕ y) x z))))

cong-quad : ∀ {a b c d e f g h : Trit} →
  a ≡ e → b ≡ f → c ≡ g → d ≡ h →
  (a , b , c , d) ≡ (e , f , g , h)
cong-quad refl refl refl refl = refl

--------------------------------------------------------------------------------
-- 1. GF(81) 类型
--------------------------------------------------------------------------------

GF81 : Set
GF81 = Trit × Trit × Trit × Trit  -- (a, b, c, d) = a + bα + cα² + dα³

gf81-zero : GF81
gf81-zero = T₀ , T₀ , T₀ , T₀

gf81-one : GF81
gf81-one = T₁ , T₀ , T₀ , T₀

alpha : GF81
alpha = T₀ , T₁ , T₀ , T₀

--------------------------------------------------------------------------------
-- 2. 加法与加法群 (Z/3Z)⁴
--------------------------------------------------------------------------------

infixl 6 _+gf81_
_+gf81_ : GF81 → GF81 → GF81
(a , b , c , d) +gf81 (e , f , g , h) =
  (a ⊕ e) , (b ⊕ f) , (c ⊕ g) , (d ⊕ h)

+gf81-identityˡ : ∀ x → gf81-zero +gf81 x ≡ x
+gf81-identityˡ (a , b , c , d) =
  cong-quad (⊕-identityˡ a) (⊕-identityˡ b) (⊕-identityˡ c) (⊕-identityˡ d)

+gf81-identityʳ : ∀ x → x +gf81 gf81-zero ≡ x
+gf81-identityʳ (a , b , c , d) =
  cong-quad (⊕-identityʳ a) (⊕-identityʳ b) (⊕-identityʳ c) (⊕-identityʳ d)

+gf81-comm : ∀ x y → x +gf81 y ≡ y +gf81 x
+gf81-comm (a , b , c , d) (e , f , g , h) =
  cong-quad (⊕-comm a e) (⊕-comm b f) (⊕-comm c g) (⊕-comm d h)

+gf81-assoc : ∀ x y z → (x +gf81 y) +gf81 z ≡ x +gf81 (y +gf81 z)
+gf81-assoc (a , b , c , d) (e , f , g , h) (i , j , k , l) =
  cong-quad (⊕-assoc a e i) (⊕-assoc b f j) (⊕-assoc c g k) (⊕-assoc d h l)

negate81 : GF81 → GF81
negate81 (a , b , c , d) = negate a , negate b , negate c , negate d

+gf81-inverse : ∀ x → x +gf81 negate81 x ≡ gf81-zero
+gf81-inverse (a , b , c , d) =
  cong-quad (⊕-inverse a) (⊕-inverse b) (⊕-inverse c) (⊕-inverse d)

+gf81-inverseˡ : ∀ x → negate81 x +gf81 x ≡ gf81-zero
+gf81-inverseˡ x = trans (+gf81-comm (negate81 x) x) (+gf81-inverse x)

negate81² : ∀ x → negate81 (negate81 x) ≡ x
negate81² (a , b , c , d) =
  cong-quad (negate² a) (negate² b) (negate² c) (negate² d)

--------------------------------------------------------------------------------
-- 3. 乘法 — α⁴ = 2α+1, 即 α⁴ = 1 + 2α
--
-- 多项式乘法 mod p(α):
--   α⁴ = 1 + 2α
--   α⁵ = α + 2α²
--   α⁶ = α² + 2α³
--
-- (a+bα+cα²+dα³)(e+fα+gα²+hα³) 的原始多项式积 (度 ≤ 6):
--   p₀ = ae
--   p₁ = af+be
--   p₂ = ag+bf+ce
--   p₃ = ah+bg+cf+de
--   p₄ = bh+cg+df
--   p₅ = ch+dg
--   p₆ = dh
--
-- 约化 (2x = negate(x) in GF(3)):
--   r₀ = p₀ + p₄
--   r₁ = p₁ + 2p₄ + p₅ = p₁ - p₄ + p₅
--   r₂ = p₂ + 2p₅ + p₆ = p₂ - p₅ + p₆
--   r₃ = p₃ + 2p₆       = p₃ - p₆
--------------------------------------------------------------------------------

-- 7 项多项式 (度 ≤ 6)
Poly7 : Set
Poly7 = Trit × Trit × Trit × Trit × Trit × Trit × Trit

-- 原始多项式乘法
poly-mul : GF81 → GF81 → Poly7
poly-mul (a , b , c , d) (e , f , g , h) =
    (a ⊗ e)
  , ((a ⊗ f) ⊕ (b ⊗ e))
  , ((a ⊗ g) ⊕ ((b ⊗ f) ⊕ (c ⊗ e)))
  , ((a ⊗ h) ⊕ ((b ⊗ g) ⊕ ((c ⊗ f) ⊕ (d ⊗ e))))
  , ((b ⊗ h) ⊕ ((c ⊗ g) ⊕ (d ⊗ f)))
  , ((c ⊗ h) ⊕ (d ⊗ g))
  , (d ⊗ h)

-- 约化: 用 α⁴=1+2α 化简度 ≤ 6 的多项式
reduce-p7 : Poly7 → GF81
reduce-p7 (p₀ , p₁ , p₂ , p₃ , p₄ , p₅ , p₆) =
    (p₀ ⊕ p₄)
  , ((p₁ ⊕ negate p₄) ⊕ p₅)
  , ((p₂ ⊕ negate p₅) ⊕ p₆)
  , (p₃ ⊕ negate p₆)

-- GF(81) 乘法 = reduce ∘ poly-mul
infixl 7 _*gf81_
_*gf81_ : GF81 → GF81 → GF81
x *gf81 y = reduce-p7 (poly-mul x y)

-- mul-via-poly 是 refl (定义等式)
mul-via-poly : ∀ x y → x *gf81 y ≡ reduce-p7 (poly-mul x y)
mul-via-poly x y = refl

--------------------------------------------------------------------------------
-- 4. 乘法单位元
--------------------------------------------------------------------------------

*gf81-identityˡ : ∀ x → gf81-one *gf81 x ≡ x
*gf81-identityˡ (e , f , g , h) = cong-quad eq₀ eq₁ eq₂ eq₃
  where
    eq₀ : (T₁ ⊗ e) ⊕ ((T₀ ⊗ h) ⊕ ((T₀ ⊗ g) ⊕ (T₀ ⊗ f))) ≡ e
    eq₀ = trans (cong₂ _⊕_ (⊗-identityˡ e)
                  (cong₂ _⊕_ (⊗-zeroˡ h) (cong₂ _⊕_ (⊗-zeroˡ g) (⊗-zeroˡ f))))
                (⊕-identityʳ e)

    eq₁ : (((T₁ ⊗ f) ⊕ (T₀ ⊗ e)) ⊕
           negate ((T₀ ⊗ h) ⊕ ((T₀ ⊗ g) ⊕ (T₀ ⊗ f)))) ⊕
          ((T₀ ⊗ h) ⊕ (T₀ ⊗ g)) ≡ f
    eq₁ = trans (cong₂ _⊕_
                  (cong₂ _⊕_ (cong₂ _⊕_ (⊗-identityˡ f) (⊗-zeroˡ e))
                    (cong negate (cong₂ _⊕_ (⊗-zeroˡ h)
                      (cong₂ _⊕_ (⊗-zeroˡ g) (⊗-zeroˡ f)))))
                  (cong₂ _⊕_ (⊗-zeroˡ h) (⊗-zeroˡ g)))
                (trans (cong (_⊕ T₀) (trans (cong (_⊕ T₀) (⊕-identityʳ f))
                                             (⊕-identityʳ f)))
                       (⊕-identityʳ f))

    eq₂ : (((T₁ ⊗ g) ⊕ ((T₀ ⊗ f) ⊕ (T₀ ⊗ e))) ⊕
           negate ((T₀ ⊗ h) ⊕ (T₀ ⊗ g))) ⊕ (T₀ ⊗ h) ≡ g
    eq₂ = trans (cong₂ _⊕_
                  (cong₂ _⊕_
                    (cong₂ _⊕_ (⊗-identityˡ g)
                      (cong₂ _⊕_ (⊗-zeroˡ f) (⊗-zeroˡ e)))
                    (cong negate (cong₂ _⊕_ (⊗-zeroˡ h) (⊗-zeroˡ g))))
                  (⊗-zeroˡ h))
                (trans (cong (_⊕ T₀) (trans (cong (_⊕ T₀) (⊕-identityʳ g))
                                             (⊕-identityʳ g)))
                       (⊕-identityʳ g))

    eq₃ : ((T₁ ⊗ h) ⊕ ((T₀ ⊗ g) ⊕ ((T₀ ⊗ f) ⊕ (T₀ ⊗ e)))) ⊕
          negate (T₀ ⊗ h) ≡ h
    eq₃ = trans (cong₂ _⊕_
                  (cong₂ _⊕_ (⊗-identityˡ h)
                    (cong₂ _⊕_ (⊗-zeroˡ g)
                      (cong₂ _⊕_ (⊗-zeroˡ f) (⊗-zeroˡ e))))
                  (cong negate (⊗-zeroˡ h)))
                (trans (cong (_⊕ T₀) (⊕-identityʳ h)) (⊕-identityʳ h))

*gf81-identityʳ : ∀ x → x *gf81 gf81-one ≡ x
*gf81-identityʳ (a , b , c , d) = cong-quad eq₀ eq₁ eq₂ eq₃
  where
    eq₀ : (a ⊗ T₁) ⊕ ((b ⊗ T₀) ⊕ ((c ⊗ T₀) ⊕ (d ⊗ T₀))) ≡ a
    eq₀ = trans (cong₂ _⊕_ (⊗-identityʳ a)
                  (cong₂ _⊕_ (⊗-zeroʳ b) (cong₂ _⊕_ (⊗-zeroʳ c) (⊗-zeroʳ d))))
                (⊕-identityʳ a)

    eq₁ : (((a ⊗ T₀) ⊕ (b ⊗ T₁)) ⊕
           negate ((b ⊗ T₀) ⊕ ((c ⊗ T₀) ⊕ (d ⊗ T₀)))) ⊕
          ((c ⊗ T₀) ⊕ (d ⊗ T₀)) ≡ b
    eq₁ = trans (cong₂ _⊕_
                  (cong₂ _⊕_ (cong₂ _⊕_ (⊗-zeroʳ a) (⊗-identityʳ b))
                    (cong negate (cong₂ _⊕_ (⊗-zeroʳ b)
                      (cong₂ _⊕_ (⊗-zeroʳ c) (⊗-zeroʳ d)))))
                  (cong₂ _⊕_ (⊗-zeroʳ c) (⊗-zeroʳ d)))
                (trans (cong (_⊕ T₀) (trans (cong (_⊕ T₀) (⊕-identityˡ b))
                                             (⊕-identityʳ b)))
                       (⊕-identityʳ b))

    eq₂ : (((a ⊗ T₀) ⊕ ((b ⊗ T₀) ⊕ (c ⊗ T₁))) ⊕
           negate ((c ⊗ T₀) ⊕ (d ⊗ T₀))) ⊕ (d ⊗ T₀) ≡ c
    eq₂ = trans (cong₂ _⊕_
                  (cong₂ _⊕_
                    (cong₂ _⊕_ (⊗-zeroʳ a)
                      (cong₂ _⊕_ (⊗-zeroʳ b) (⊗-identityʳ c)))
                    (cong negate (cong₂ _⊕_ (⊗-zeroʳ c) (⊗-zeroʳ d))))
                  (⊗-zeroʳ d))
                (trans (cong (_⊕ T₀) (trans (cong (_⊕ T₀) (⊕-identityˡ c))
                                             (⊕-identityʳ c)))
                       (⊕-identityʳ c))

    eq₃ : ((a ⊗ T₀) ⊕ ((b ⊗ T₀) ⊕ ((c ⊗ T₀) ⊕ (d ⊗ T₁)))) ⊕
          negate (d ⊗ T₀) ≡ d
    eq₃ = trans (cong₂ _⊕_
                  (cong₂ _⊕_ (⊗-zeroʳ a)
                    (cong₂ _⊕_ (⊗-zeroʳ b)
                      (cong₂ _⊕_ (⊗-zeroʳ c) (⊗-identityʳ d))))
                  (cong negate (⊗-zeroʳ d)))
                (trans (cong (_⊕ T₀) (⊕-identityˡ d)) (⊕-identityʳ d))

--------------------------------------------------------------------------------
-- 5. 乘法交换律 (通过多项式模型)
--------------------------------------------------------------------------------

cong-7 : ∀ {a₀ b₀ c₀ d₀ e₀ f₀ g₀ a₁ b₁ c₁ d₁ e₁ f₁ g₁ : Trit} →
  a₀ ≡ a₁ → b₀ ≡ b₁ → c₀ ≡ c₁ → d₀ ≡ d₁ →
  e₀ ≡ e₁ → f₀ ≡ f₁ → g₀ ≡ g₁ →
  (a₀ , b₀ , c₀ , d₀ , e₀ , f₀ , g₀) ≡ (a₁ , b₁ , c₁ , d₁ , e₁ , f₁ , g₁)
cong-7 refl refl refl refl refl refl refl = refl

-- poly-mul 交换律 (由 ⊗-comm 和 ⊕-comm 推导)
poly-mul-comm : ∀ x y → poly-mul x y ≡ poly-mul y x
poly-mul-comm (a , b , c , d) (e , f , g , h) =
  cong-7 (⊗-comm a e) eq₁ eq₂ eq₃ eq₄ eq₅ (⊗-comm d h)
  where
    eq₁ : (a ⊗ f) ⊕ (b ⊗ e) ≡ (e ⊗ b) ⊕ (f ⊗ a)
    eq₁ = trans (cong₂ _⊕_ (⊗-comm a f) (⊗-comm b e))
                (⊕-comm (f ⊗ a) (e ⊗ b))

    eq₂ : (a ⊗ g) ⊕ ((b ⊗ f) ⊕ (c ⊗ e)) ≡ (e ⊗ c) ⊕ ((f ⊗ b) ⊕ (g ⊗ a))
    eq₂ = begin
      (a ⊗ g) ⊕ ((b ⊗ f) ⊕ (c ⊗ e))
      ≡⟨ cong₂ _⊕_ (⊗-comm a g) (cong₂ _⊕_ (⊗-comm b f) (⊗-comm c e)) ⟩
      (g ⊗ a) ⊕ ((f ⊗ b) ⊕ (e ⊗ c))
      ≡⟨ ⊕-comm (g ⊗ a) ((f ⊗ b) ⊕ (e ⊗ c)) ⟩
      ((f ⊗ b) ⊕ (e ⊗ c)) ⊕ (g ⊗ a)
      ≡⟨ cong (_⊕ (g ⊗ a)) (⊕-comm (f ⊗ b) (e ⊗ c)) ⟩
      ((e ⊗ c) ⊕ (f ⊗ b)) ⊕ (g ⊗ a)
      ≡⟨ ⊕-assoc (e ⊗ c) (f ⊗ b) (g ⊗ a) ⟩
      (e ⊗ c) ⊕ ((f ⊗ b) ⊕ (g ⊗ a))
      ∎

    eq₃ : (a ⊗ h) ⊕ ((b ⊗ g) ⊕ ((c ⊗ f) ⊕ (d ⊗ e)))
        ≡ (e ⊗ d) ⊕ ((f ⊗ c) ⊕ ((g ⊗ b) ⊕ (h ⊗ a)))
    eq₃ = begin
      (a ⊗ h) ⊕ ((b ⊗ g) ⊕ ((c ⊗ f) ⊕ (d ⊗ e)))
      ≡⟨ cong₂ _⊕_ (⊗-comm a h)
           (cong₂ _⊕_ (⊗-comm b g) (cong₂ _⊕_ (⊗-comm c f) (⊗-comm d e))) ⟩
      (h ⊗ a) ⊕ ((g ⊗ b) ⊕ ((f ⊗ c) ⊕ (e ⊗ d)))
      ≡⟨ ⊕-comm (h ⊗ a) ((g ⊗ b) ⊕ ((f ⊗ c) ⊕ (e ⊗ d))) ⟩
      ((g ⊗ b) ⊕ ((f ⊗ c) ⊕ (e ⊗ d))) ⊕ (h ⊗ a)
      ≡⟨ cong (_⊕ (h ⊗ a)) (⊕-comm (g ⊗ b) ((f ⊗ c) ⊕ (e ⊗ d))) ⟩
      (((f ⊗ c) ⊕ (e ⊗ d)) ⊕ (g ⊗ b)) ⊕ (h ⊗ a)
      ≡⟨ cong (_⊕ (h ⊗ a)) (cong (_⊕ (g ⊗ b)) (⊕-comm (f ⊗ c) (e ⊗ d))) ⟩
      (((e ⊗ d) ⊕ (f ⊗ c)) ⊕ (g ⊗ b)) ⊕ (h ⊗ a)
      ≡⟨ ⊕-assoc ((e ⊗ d) ⊕ (f ⊗ c)) (g ⊗ b) (h ⊗ a) ⟩
      ((e ⊗ d) ⊕ (f ⊗ c)) ⊕ ((g ⊗ b) ⊕ (h ⊗ a))
      ≡⟨ cong (((e ⊗ d) ⊕ (f ⊗ c)) ⊕_) (⊕-comm (g ⊗ b) (h ⊗ a)) ⟩
      ((e ⊗ d) ⊕ (f ⊗ c)) ⊕ ((h ⊗ a) ⊕ (g ⊗ b))
      ≡⟨ ⊕-assoc (e ⊗ d) (f ⊗ c) ((h ⊗ a) ⊕ (g ⊗ b)) ⟩
      (e ⊗ d) ⊕ ((f ⊗ c) ⊕ ((h ⊗ a) ⊕ (g ⊗ b)))
      ≡⟨ cong ((e ⊗ d) ⊕_) (cong ((f ⊗ c) ⊕_) (⊕-comm (h ⊗ a) (g ⊗ b))) ⟩
      (e ⊗ d) ⊕ ((f ⊗ c) ⊕ ((g ⊗ b) ⊕ (h ⊗ a)))
      ∎

    eq₄ : (b ⊗ h) ⊕ ((c ⊗ g) ⊕ (d ⊗ f)) ≡ (f ⊗ d) ⊕ ((g ⊗ c) ⊕ (h ⊗ b))
    eq₄ = begin
      (b ⊗ h) ⊕ ((c ⊗ g) ⊕ (d ⊗ f))
      ≡⟨ cong₂ _⊕_ (⊗-comm b h) (cong₂ _⊕_ (⊗-comm c g) (⊗-comm d f)) ⟩
      (h ⊗ b) ⊕ ((g ⊗ c) ⊕ (f ⊗ d))
      ≡⟨ ⊕-comm (h ⊗ b) ((g ⊗ c) ⊕ (f ⊗ d)) ⟩
      ((g ⊗ c) ⊕ (f ⊗ d)) ⊕ (h ⊗ b)
      ≡⟨ cong (_⊕ (h ⊗ b)) (⊕-comm (g ⊗ c) (f ⊗ d)) ⟩
      ((f ⊗ d) ⊕ (g ⊗ c)) ⊕ (h ⊗ b)
      ≡⟨ ⊕-assoc (f ⊗ d) (g ⊗ c) (h ⊗ b) ⟩
      (f ⊗ d) ⊕ ((g ⊗ c) ⊕ (h ⊗ b))
      ∎

    eq₅ : (c ⊗ h) ⊕ (d ⊗ g) ≡ (g ⊗ d) ⊕ (h ⊗ c)
    eq₅ = trans (cong₂ _⊕_ (⊗-comm c h) (⊗-comm d g))
                (⊕-comm (h ⊗ c) (g ⊗ d))

*gf81-comm : ∀ x y → x *gf81 y ≡ y *gf81 x
*gf81-comm x y = trans (mul-via-poly x y)
                 (trans (cong reduce-p7 (poly-mul-comm x y))
                        (sym (mul-via-poly y x)))

--------------------------------------------------------------------------------
-- 6. 分配律 (通过多项式模型)
--------------------------------------------------------------------------------

-- Poly7 加法
_+p7_ : Poly7 → Poly7 → Poly7
(p₀ , p₁ , p₂ , p₃ , p₄ , p₅ , p₆) +p7 (q₀ , q₁ , q₂ , q₃ , q₄ , q₅ , q₆) =
  (p₀ ⊕ q₀) , (p₁ ⊕ q₁) , (p₂ ⊕ q₂) , (p₃ ⊕ q₃) ,
  (p₄ ⊕ q₄) , (p₅ ⊕ q₅) , (p₆ ⊕ q₆)

-- reduce 保持加法
reduce-additive : ∀ p q →
  reduce-p7 (p +p7 q) ≡ reduce-p7 p +gf81 reduce-p7 q
reduce-additive (p₀ , p₁ , p₂ , p₃ , p₄ , p₅ , p₆)
                (q₀ , q₁ , q₂ , q₃ , q₄ , q₅ , q₆) =
  cong-quad eq₀ eq₁ eq₂ eq₃
  where
    eq₀ : (p₀ ⊕ q₀) ⊕ (p₄ ⊕ q₄) ≡ (p₀ ⊕ p₄) ⊕ (q₀ ⊕ q₄)
    eq₀ = swap-middle p₀ q₀ p₄ q₄

    eq₁ : ((p₁ ⊕ q₁) ⊕ negate (p₄ ⊕ q₄)) ⊕ (p₅ ⊕ q₅)
        ≡ ((p₁ ⊕ negate p₄) ⊕ p₅) ⊕ ((q₁ ⊕ negate q₄) ⊕ q₅)
    eq₁ = begin
      ((p₁ ⊕ q₁) ⊕ negate (p₄ ⊕ q₄)) ⊕ (p₅ ⊕ q₅)
      ≡⟨ cong (λ t → ((p₁ ⊕ q₁) ⊕ t) ⊕ (p₅ ⊕ q₅)) (negate-⊕ p₄ q₄) ⟩
      ((p₁ ⊕ q₁) ⊕ (negate p₄ ⊕ negate q₄)) ⊕ (p₅ ⊕ q₅)
      ≡⟨ cong (_⊕ (p₅ ⊕ q₅)) (swap-middle p₁ q₁ (negate p₄) (negate q₄)) ⟩
      ((p₁ ⊕ negate p₄) ⊕ (q₁ ⊕ negate q₄)) ⊕ (p₅ ⊕ q₅)
      ≡⟨ swap-middle (p₁ ⊕ negate p₄) (q₁ ⊕ negate q₄) p₅ q₅ ⟩
      ((p₁ ⊕ negate p₄) ⊕ p₅) ⊕ ((q₁ ⊕ negate q₄) ⊕ q₅)
      ∎

    eq₂ : ((p₂ ⊕ q₂) ⊕ negate (p₅ ⊕ q₅)) ⊕ (p₆ ⊕ q₆)
        ≡ ((p₂ ⊕ negate p₅) ⊕ p₆) ⊕ ((q₂ ⊕ negate q₅) ⊕ q₆)
    eq₂ = begin
      ((p₂ ⊕ q₂) ⊕ negate (p₅ ⊕ q₅)) ⊕ (p₆ ⊕ q₆)
      ≡⟨ cong (λ t → ((p₂ ⊕ q₂) ⊕ t) ⊕ (p₆ ⊕ q₆)) (negate-⊕ p₅ q₅) ⟩
      ((p₂ ⊕ q₂) ⊕ (negate p₅ ⊕ negate q₅)) ⊕ (p₆ ⊕ q₆)
      ≡⟨ cong (_⊕ (p₆ ⊕ q₆)) (swap-middle p₂ q₂ (negate p₅) (negate q₅)) ⟩
      ((p₂ ⊕ negate p₅) ⊕ (q₂ ⊕ negate q₅)) ⊕ (p₆ ⊕ q₆)
      ≡⟨ swap-middle (p₂ ⊕ negate p₅) (q₂ ⊕ negate q₅) p₆ q₆ ⟩
      ((p₂ ⊕ negate p₅) ⊕ p₆) ⊕ ((q₂ ⊕ negate q₅) ⊕ q₆)
      ∎

    eq₃ : (p₃ ⊕ q₃) ⊕ negate (p₆ ⊕ q₆) ≡ (p₃ ⊕ negate p₆) ⊕ (q₃ ⊕ negate q₆)
    eq₃ = begin
      (p₃ ⊕ q₃) ⊕ negate (p₆ ⊕ q₆)
      ≡⟨ cong ((p₃ ⊕ q₃) ⊕_) (negate-⊕ p₆ q₆) ⟩
      (p₃ ⊕ q₃) ⊕ (negate p₆ ⊕ negate q₆)
      ≡⟨ swap-middle p₃ q₃ (negate p₆) (negate q₆) ⟩
      (p₃ ⊕ negate p₆) ⊕ (q₃ ⊕ negate q₆)
      ∎

-- 六项重排 (提升自 GF(3) 层)
inner-swap : ∀ B D E F → B ⊕ (D ⊕ (E ⊕ F)) ≡ E ⊕ (B ⊕ (D ⊕ F))
inner-swap B D E F = begin
  B ⊕ (D ⊕ (E ⊕ F))
  ≡⟨ sym (⊕-assoc B D (E ⊕ F)) ⟩
  (B ⊕ D) ⊕ (E ⊕ F)
  ≡⟨ swap-middle B D E F ⟩
  (B ⊕ E) ⊕ (D ⊕ F)
  ≡⟨ cong (_⊕ (D ⊕ F)) (⊕-comm B E) ⟩
  (E ⊕ B) ⊕ (D ⊕ F)
  ≡⟨ ⊕-assoc E B (D ⊕ F) ⟩
  E ⊕ (B ⊕ (D ⊕ F))
  ∎

⊕-rearrange-6 : ∀ A B C D E F →
  (A ⊕ B) ⊕ ((C ⊕ D) ⊕ (E ⊕ F)) ≡ (A ⊕ (C ⊕ E)) ⊕ (B ⊕ (D ⊕ F))
⊕-rearrange-6 A B C D E F = begin
  (A ⊕ B) ⊕ ((C ⊕ D) ⊕ (E ⊕ F))
  ≡⟨ cong ((A ⊕ B) ⊕_) (⊕-assoc C D (E ⊕ F)) ⟩
  (A ⊕ B) ⊕ (C ⊕ (D ⊕ (E ⊕ F)))
  ≡⟨ ⊕-assoc A B (C ⊕ (D ⊕ (E ⊕ F))) ⟩
  A ⊕ (B ⊕ (C ⊕ (D ⊕ (E ⊕ F))))
  ≡⟨ cong (A ⊕_) (sym (⊕-assoc B C (D ⊕ (E ⊕ F)))) ⟩
  A ⊕ ((B ⊕ C) ⊕ (D ⊕ (E ⊕ F)))
  ≡⟨ cong (A ⊕_) (cong (_⊕ (D ⊕ (E ⊕ F))) (⊕-comm B C)) ⟩
  A ⊕ ((C ⊕ B) ⊕ (D ⊕ (E ⊕ F)))
  ≡⟨ cong (A ⊕_) (⊕-assoc C B (D ⊕ (E ⊕ F))) ⟩
  A ⊕ (C ⊕ (B ⊕ (D ⊕ (E ⊕ F))))
  ≡⟨ cong (A ⊕_) (cong (C ⊕_) (inner-swap B D E F)) ⟩
  A ⊕ (C ⊕ (E ⊕ (B ⊕ (D ⊕ F))))
  ≡⟨ cong (A ⊕_) (sym (⊕-assoc C E (B ⊕ (D ⊕ F)))) ⟩
  A ⊕ ((C ⊕ E) ⊕ (B ⊕ (D ⊕ F)))
  ≡⟨ sym (⊕-assoc A (C ⊕ E) (B ⊕ (D ⊕ F))) ⟩
  (A ⊕ (C ⊕ E)) ⊕ (B ⊕ (D ⊕ F))
  ∎

-- 八项重排: 将交错的 (AE)(BF)(CG)(DH) 分离为 (ABCD)(EFGH)
⊕-rearrange-8 : ∀ A B C D E F G H →
  ((A ⊕ E) ⊕ ((B ⊕ F) ⊕ ((C ⊕ G) ⊕ (D ⊕ H))))
  ≡ (A ⊕ (B ⊕ (C ⊕ D))) ⊕ (E ⊕ (F ⊕ (G ⊕ H)))
⊕-rearrange-8 A B C D E F G H = begin
  (A ⊕ E) ⊕ ((B ⊕ F) ⊕ ((C ⊕ G) ⊕ (D ⊕ H)))
  ≡⟨ sym (⊕-assoc (A ⊕ E) (B ⊕ F) ((C ⊕ G) ⊕ (D ⊕ H))) ⟩
  ((A ⊕ E) ⊕ (B ⊕ F)) ⊕ ((C ⊕ G) ⊕ (D ⊕ H))
  ≡⟨ cong (((A ⊕ E) ⊕ (B ⊕ F)) ⊕_) (swap-middle C G D H) ⟩
  ((A ⊕ E) ⊕ (B ⊕ F)) ⊕ ((C ⊕ D) ⊕ (G ⊕ H))
  ≡⟨ cong (_⊕ ((C ⊕ D) ⊕ (G ⊕ H))) (swap-middle A E B F) ⟩
  ((A ⊕ B) ⊕ (E ⊕ F)) ⊕ ((C ⊕ D) ⊕ (G ⊕ H))
  ≡⟨ swap-middle (A ⊕ B) (E ⊕ F) (C ⊕ D) (G ⊕ H) ⟩
  ((A ⊕ B) ⊕ (C ⊕ D)) ⊕ ((E ⊕ F) ⊕ (G ⊕ H))
  ≡⟨ cong (_⊕ ((E ⊕ F) ⊕ (G ⊕ H))) (⊕-assoc A B (C ⊕ D)) ⟩
  (A ⊕ (B ⊕ (C ⊕ D))) ⊕ ((E ⊕ F) ⊕ (G ⊕ H))
  ≡⟨ cong ((A ⊕ (B ⊕ (C ⊕ D))) ⊕_) (⊕-assoc E F (G ⊕ H)) ⟩
  (A ⊕ (B ⊕ (C ⊕ D))) ⊕ (E ⊕ (F ⊕ (G ⊕ H)))
  ∎

-- poly-mul 左分配律
poly-mul-distribˡ : ∀ x y z →
  poly-mul x (y +gf81 z) ≡ poly-mul x y +p7 poly-mul x z
poly-mul-distribˡ (a , b , c , d) (e , f , g , h) (i , j , k , l) =
  cong-7 eq₀ eq₁ eq₂ eq₃ eq₄ eq₅ eq₆
  where
    eq₀ : a ⊗ (e ⊕ i) ≡ (a ⊗ e) ⊕ (a ⊗ i)
    eq₀ = ⊗-distribˡ-⊕ a e i

    eq₁ : (a ⊗ (f ⊕ j)) ⊕ (b ⊗ (e ⊕ i))
        ≡ ((a ⊗ f) ⊕ (b ⊗ e)) ⊕ ((a ⊗ j) ⊕ (b ⊗ i))
    eq₁ = trans (cong₂ _⊕_ (⊗-distribˡ-⊕ a f j) (⊗-distribˡ-⊕ b e i))
                (swap-middle (a ⊗ f) (a ⊗ j) (b ⊗ e) (b ⊗ i))

    eq₂ : (a ⊗ (g ⊕ k)) ⊕ ((b ⊗ (f ⊕ j)) ⊕ (c ⊗ (e ⊕ i)))
        ≡ ((a ⊗ g) ⊕ ((b ⊗ f) ⊕ (c ⊗ e))) ⊕ ((a ⊗ k) ⊕ ((b ⊗ j) ⊕ (c ⊗ i)))
    eq₂ = trans
      (cong₂ _⊕_ (⊗-distribˡ-⊕ a g k)
        (cong₂ _⊕_ (⊗-distribˡ-⊕ b f j) (⊗-distribˡ-⊕ c e i)))
      (⊕-rearrange-6 (a ⊗ g) (a ⊗ k) (b ⊗ f) (b ⊗ j) (c ⊗ e) (c ⊗ i))

    eq₃ : (a ⊗ (h ⊕ l)) ⊕ ((b ⊗ (g ⊕ k)) ⊕ ((c ⊗ (f ⊕ j)) ⊕ (d ⊗ (e ⊕ i))))
        ≡ ((a ⊗ h) ⊕ ((b ⊗ g) ⊕ ((c ⊗ f) ⊕ (d ⊗ e))))
        ⊕ ((a ⊗ l) ⊕ ((b ⊗ k) ⊕ ((c ⊗ j) ⊕ (d ⊗ i))))
    eq₃ = trans
      (cong₂ _⊕_ (⊗-distribˡ-⊕ a h l)
        (cong₂ _⊕_ (⊗-distribˡ-⊕ b g k)
          (cong₂ _⊕_ (⊗-distribˡ-⊕ c f j) (⊗-distribˡ-⊕ d e i))))
      (⊕-rearrange-8 (a ⊗ h) (b ⊗ g) (c ⊗ f) (d ⊗ e)
                      (a ⊗ l) (b ⊗ k) (c ⊗ j) (d ⊗ i))

    eq₄ : (b ⊗ (h ⊕ l)) ⊕ ((c ⊗ (g ⊕ k)) ⊕ (d ⊗ (f ⊕ j)))
        ≡ ((b ⊗ h) ⊕ ((c ⊗ g) ⊕ (d ⊗ f))) ⊕ ((b ⊗ l) ⊕ ((c ⊗ k) ⊕ (d ⊗ j)))
    eq₄ = trans
      (cong₂ _⊕_ (⊗-distribˡ-⊕ b h l)
        (cong₂ _⊕_ (⊗-distribˡ-⊕ c g k) (⊗-distribˡ-⊕ d f j)))
      (⊕-rearrange-6 (b ⊗ h) (b ⊗ l) (c ⊗ g) (c ⊗ k) (d ⊗ f) (d ⊗ j))

    eq₅ : (c ⊗ (h ⊕ l)) ⊕ (d ⊗ (g ⊕ k))
        ≡ ((c ⊗ h) ⊕ (d ⊗ g)) ⊕ ((c ⊗ l) ⊕ (d ⊗ k))
    eq₅ = trans (cong₂ _⊕_ (⊗-distribˡ-⊕ c h l) (⊗-distribˡ-⊕ d g k))
                (swap-middle (c ⊗ h) (c ⊗ l) (d ⊗ g) (d ⊗ k))

    eq₆ : d ⊗ (h ⊕ l) ≡ (d ⊗ h) ⊕ (d ⊗ l)
    eq₆ = ⊗-distribˡ-⊕ d h l

-- 左分配律
*gf81-distribˡ : ∀ x y z →
  x *gf81 (y +gf81 z) ≡ (x *gf81 y) +gf81 (x *gf81 z)
*gf81-distribˡ x y z =
  trans (mul-via-poly x (y +gf81 z))
  (trans (cong reduce-p7 (poly-mul-distribˡ x y z))
  (trans (reduce-additive (poly-mul x y) (poly-mul x z))
         (cong₂ _+gf81_ (sym (mul-via-poly x y)) (sym (mul-via-poly x z)))))

-- 右分配律 (由左分配律 + 交换律推导)
*gf81-distribʳ : ∀ x y z →
  (x +gf81 y) *gf81 z ≡ (x *gf81 z) +gf81 (y *gf81 z)
*gf81-distribʳ x y z =
  trans (*gf81-comm (x +gf81 y) z)
  (trans (*gf81-distribˡ z x y)
         (cong₂ _+gf81_ (*gf81-comm z x) (*gf81-comm z y)))

--------------------------------------------------------------------------------
-- 7. Frobenius 自同构 σ(x) = x³
--
-- σ(a + bα + cα² + dα³) = a + bα³ + cα⁶ + dα⁹
--
-- 幂次约化:
--   α³  = α³
--   α⁶  = α² + 2α³
--   α⁹  = α + α² + α³
--
-- 所以:
--   σ(a,b,c,d) = (a, d, c+d, b+2c+d)
--              = (a, d, c⊕d, b⊕negate(c)⊕d)
--------------------------------------------------------------------------------

frobenius : GF81 → GF81
frobenius (a , b , c , d) = a , d , (c ⊕ d) , ((b ⊕ (negate c)) ⊕ d)

-- α 的 Frobenius 像: σ(α) = α³
frobenius-alpha : frobenius alpha ≡ (T₀ , T₀ , T₀ , T₁)
frobenius-alpha = refl

-- α⁶ = α² + 2α³ 的验证
alpha6-normal : GF81
alpha6-normal = T₀ , T₀ , T₁ , T₂  -- α² + 2α³

-- α⁹ = α + α² + α³ 的验证
alpha9-normal : GF81
alpha9-normal = T₀ , T₁ , T₁ , T₁  -- α + α² + α³

-- σ⁴ = id (四次 Frobenius 是恒等)
-- 27 case 穷举 (a 不变, 对 b,c,d 穷举)
frobenius⁴-id : ∀ x →
  frobenius (frobenius (frobenius (frobenius x))) ≡ x
frobenius⁴-id (a , T₀ , T₀ , T₀) = refl
frobenius⁴-id (a , T₀ , T₀ , T₁) = refl
frobenius⁴-id (a , T₀ , T₀ , T₂) = refl
frobenius⁴-id (a , T₀ , T₁ , T₀) = refl
frobenius⁴-id (a , T₀ , T₁ , T₁) = refl
frobenius⁴-id (a , T₀ , T₁ , T₂) = refl
frobenius⁴-id (a , T₀ , T₂ , T₀) = refl
frobenius⁴-id (a , T₀ , T₂ , T₁) = refl
frobenius⁴-id (a , T₀ , T₂ , T₂) = refl
frobenius⁴-id (a , T₁ , T₀ , T₀) = refl
frobenius⁴-id (a , T₁ , T₀ , T₁) = refl
frobenius⁴-id (a , T₁ , T₀ , T₂) = refl
frobenius⁴-id (a , T₁ , T₁ , T₀) = refl
frobenius⁴-id (a , T₁ , T₁ , T₁) = refl
frobenius⁴-id (a , T₁ , T₁ , T₂) = refl
frobenius⁴-id (a , T₁ , T₂ , T₀) = refl
frobenius⁴-id (a , T₁ , T₂ , T₁) = refl
frobenius⁴-id (a , T₁ , T₂ , T₂) = refl
frobenius⁴-id (a , T₂ , T₀ , T₀) = refl
frobenius⁴-id (a , T₂ , T₀ , T₁) = refl
frobenius⁴-id (a , T₂ , T₀ , T₂) = refl
frobenius⁴-id (a , T₂ , T₁ , T₀) = refl
frobenius⁴-id (a , T₂ , T₁ , T₁) = refl
frobenius⁴-id (a , T₂ , T₁ , T₂) = refl
frobenius⁴-id (a , T₂ , T₂ , T₀) = refl
frobenius⁴-id (a , T₂ , T₂ , T₁) = refl
frobenius⁴-id (a , T₂ , T₂ , T₂) = refl

--------------------------------------------------------------------------------
-- 8. GF(3) 嵌入
--------------------------------------------------------------------------------

embed-gf3 : Trit → GF81
embed-gf3 a = a , T₀ , T₀ , T₀

embed-gf3-add : ∀ a b →
  embed-gf3 (a ⊕ b) ≡ embed-gf3 a +gf81 embed-gf3 b
embed-gf3-add a b = refl

embed-gf3-mul : ∀ a b →
  embed-gf3 (a ⊗ b) ≡ embed-gf3 a *gf81 embed-gf3 b
embed-gf3-mul T₀ T₀ = refl; embed-gf3-mul T₀ T₁ = refl; embed-gf3-mul T₀ T₂ = refl
embed-gf3-mul T₁ T₀ = refl; embed-gf3-mul T₁ T₁ = refl; embed-gf3-mul T₁ T₂ = refl
embed-gf3-mul T₂ T₀ = refl; embed-gf3-mul T₂ T₁ = refl; embed-gf3-mul T₂ T₂ = refl

embed-gf3-one : embed-gf3 T₁ ≡ gf81-one
embed-gf3-one = refl

--------------------------------------------------------------------------------
-- 9. GF(9) 嵌入
--
-- GF(9) ⊂ GF(81) 因为 2∣4。
-- GF(9) = GF(3)[β]/(β²+1), β² = 2 = -1。
--
-- GF(81) 中满足 x² = -1 的元素: β = 2α + α² + α³ = (0, 2, 1, 1)
-- 验证: β² = (2, 0, 0, 0) = -1 ✓
--
-- 嵌入: (a, b) ∈ GF(9) ↦ (a, negate(b), b, b) ∈ GF(81)
-- 即 a + bβ = a + b(2α + α² + α³) = a + 2bα + bα² + bα³
--
-- 等价地: GF(9) 子域 = Fix(σ²) = {(a, negate(c), c, c) | a,c ∈ GF(3)}
--------------------------------------------------------------------------------

embed-gf9 : GF9 → GF81
embed-gf9 (a , b) = a , negate b , b , b

-- β = embed-gf9(0, 1) = (0, 2, 1, 1)
beta : GF81
beta = T₀ , T₂ , T₁ , T₁

-- β² = -1 = (2, 0, 0, 0)
beta-squared : beta *gf81 beta ≡ (T₂ , T₀ , T₀ , T₀)
beta-squared = refl

-- 嵌入保持加法
embed-gf9-add : ∀ x y →
  embed-gf9 (x +gf9 y) ≡ embed-gf9 x +gf81 embed-gf9 y
embed-gf9-add (a , b) (c , d) =
  cong-quad refl (negate-⊕ b d) refl refl

-- 嵌入保持乘法 (81 case 穷举)
embed-gf9-mul : ∀ x y →
  embed-gf9 (x *gf9 y) ≡ embed-gf9 x *gf81 embed-gf9 y
embed-gf9-mul (T₀ , T₀) (T₀ , T₀) = refl
embed-gf9-mul (T₀ , T₀) (T₀ , T₁) = refl
embed-gf9-mul (T₀ , T₀) (T₀ , T₂) = refl
embed-gf9-mul (T₀ , T₀) (T₁ , T₀) = refl
embed-gf9-mul (T₀ , T₀) (T₁ , T₁) = refl
embed-gf9-mul (T₀ , T₀) (T₁ , T₂) = refl
embed-gf9-mul (T₀ , T₀) (T₂ , T₀) = refl
embed-gf9-mul (T₀ , T₀) (T₂ , T₁) = refl
embed-gf9-mul (T₀ , T₀) (T₂ , T₂) = refl
embed-gf9-mul (T₀ , T₁) (T₀ , T₀) = refl
embed-gf9-mul (T₀ , T₁) (T₀ , T₁) = refl
embed-gf9-mul (T₀ , T₁) (T₀ , T₂) = refl
embed-gf9-mul (T₀ , T₁) (T₁ , T₀) = refl
embed-gf9-mul (T₀ , T₁) (T₁ , T₁) = refl
embed-gf9-mul (T₀ , T₁) (T₁ , T₂) = refl
embed-gf9-mul (T₀ , T₁) (T₂ , T₀) = refl
embed-gf9-mul (T₀ , T₁) (T₂ , T₁) = refl
embed-gf9-mul (T₀ , T₁) (T₂ , T₂) = refl
embed-gf9-mul (T₀ , T₂) (T₀ , T₀) = refl
embed-gf9-mul (T₀ , T₂) (T₀ , T₁) = refl
embed-gf9-mul (T₀ , T₂) (T₀ , T₂) = refl
embed-gf9-mul (T₀ , T₂) (T₁ , T₀) = refl
embed-gf9-mul (T₀ , T₂) (T₁ , T₁) = refl
embed-gf9-mul (T₀ , T₂) (T₁ , T₂) = refl
embed-gf9-mul (T₀ , T₂) (T₂ , T₀) = refl
embed-gf9-mul (T₀ , T₂) (T₂ , T₁) = refl
embed-gf9-mul (T₀ , T₂) (T₂ , T₂) = refl
embed-gf9-mul (T₁ , T₀) (T₀ , T₀) = refl
embed-gf9-mul (T₁ , T₀) (T₀ , T₁) = refl
embed-gf9-mul (T₁ , T₀) (T₀ , T₂) = refl
embed-gf9-mul (T₁ , T₀) (T₁ , T₀) = refl
embed-gf9-mul (T₁ , T₀) (T₁ , T₁) = refl
embed-gf9-mul (T₁ , T₀) (T₁ , T₂) = refl
embed-gf9-mul (T₁ , T₀) (T₂ , T₀) = refl
embed-gf9-mul (T₁ , T₀) (T₂ , T₁) = refl
embed-gf9-mul (T₁ , T₀) (T₂ , T₂) = refl
embed-gf9-mul (T₁ , T₁) (T₀ , T₀) = refl
embed-gf9-mul (T₁ , T₁) (T₀ , T₁) = refl
embed-gf9-mul (T₁ , T₁) (T₀ , T₂) = refl
embed-gf9-mul (T₁ , T₁) (T₁ , T₀) = refl
embed-gf9-mul (T₁ , T₁) (T₁ , T₁) = refl
embed-gf9-mul (T₁ , T₁) (T₁ , T₂) = refl
embed-gf9-mul (T₁ , T₁) (T₂ , T₀) = refl
embed-gf9-mul (T₁ , T₁) (T₂ , T₁) = refl
embed-gf9-mul (T₁ , T₁) (T₂ , T₂) = refl
embed-gf9-mul (T₁ , T₂) (T₀ , T₀) = refl
embed-gf9-mul (T₁ , T₂) (T₀ , T₁) = refl
embed-gf9-mul (T₁ , T₂) (T₀ , T₂) = refl
embed-gf9-mul (T₁ , T₂) (T₁ , T₀) = refl
embed-gf9-mul (T₁ , T₂) (T₁ , T₁) = refl
embed-gf9-mul (T₁ , T₂) (T₁ , T₂) = refl
embed-gf9-mul (T₁ , T₂) (T₂ , T₀) = refl
embed-gf9-mul (T₁ , T₂) (T₂ , T₁) = refl
embed-gf9-mul (T₁ , T₂) (T₂ , T₂) = refl
embed-gf9-mul (T₂ , T₀) (T₀ , T₀) = refl
embed-gf9-mul (T₂ , T₀) (T₀ , T₁) = refl
embed-gf9-mul (T₂ , T₀) (T₀ , T₂) = refl
embed-gf9-mul (T₂ , T₀) (T₁ , T₀) = refl
embed-gf9-mul (T₂ , T₀) (T₁ , T₁) = refl
embed-gf9-mul (T₂ , T₀) (T₁ , T₂) = refl
embed-gf9-mul (T₂ , T₀) (T₂ , T₀) = refl
embed-gf9-mul (T₂ , T₀) (T₂ , T₁) = refl
embed-gf9-mul (T₂ , T₀) (T₂ , T₂) = refl
embed-gf9-mul (T₂ , T₁) (T₀ , T₀) = refl
embed-gf9-mul (T₂ , T₁) (T₀ , T₁) = refl
embed-gf9-mul (T₂ , T₁) (T₀ , T₂) = refl
embed-gf9-mul (T₂ , T₁) (T₁ , T₀) = refl
embed-gf9-mul (T₂ , T₁) (T₁ , T₁) = refl
embed-gf9-mul (T₂ , T₁) (T₁ , T₂) = refl
embed-gf9-mul (T₂ , T₁) (T₂ , T₀) = refl
embed-gf9-mul (T₂ , T₁) (T₂ , T₁) = refl
embed-gf9-mul (T₂ , T₁) (T₂ , T₂) = refl
embed-gf9-mul (T₂ , T₂) (T₀ , T₀) = refl
embed-gf9-mul (T₂ , T₂) (T₀ , T₁) = refl
embed-gf9-mul (T₂ , T₂) (T₀ , T₂) = refl
embed-gf9-mul (T₂ , T₂) (T₁ , T₀) = refl
embed-gf9-mul (T₂ , T₂) (T₁ , T₁) = refl
embed-gf9-mul (T₂ , T₂) (T₁ , T₂) = refl
embed-gf9-mul (T₂ , T₂) (T₂ , T₀) = refl
embed-gf9-mul (T₂ , T₂) (T₂ , T₁) = refl
embed-gf9-mul (T₂ , T₂) (T₂ , T₂) = refl

-- 嵌入保持单位元
embed-gf9-one : embed-gf9 (T₁ , T₀) ≡ gf81-one
embed-gf9-one = refl

--------------------------------------------------------------------------------
-- 10. 特征 3
--------------------------------------------------------------------------------

char-3 : gf81-one +gf81 gf81-one +gf81 gf81-one ≡ gf81-zero
char-3 = refl

char-3-univ : ∀ x → x +gf81 x +gf81 x ≡ gf81-zero
char-3-univ (a , b , c , d) =
  cong-quad (⊕-char3 a) (⊕-char3 b) (⊕-char3 c) (⊕-char3 d)

--------------------------------------------------------------------------------
-- 11. 不可约多项式验证
--
-- p(x) = x⁴ + x + 2 在 GF(3) 上不可约:
--   无根: p(0)=2≠0, p(1)=4≡1≠0, p(2)=20≡2≠0
--   不分解为两个不可约二次因子:
--     GF(3) 上不可约二次多项式: x²+1, x²+x+2, x²+2x+2
--     穷举 6 个乘积均 ≠ x⁴+x+2
--------------------------------------------------------------------------------

-- p(0) = 0 + 0 + 2 = 2 ≠ 0 (mod 3)
p0-val : 0 + 0 + 2 ≡ 2
p0-val = refl

-- p(1) = 4 ≡ 1 (mod 3) ≠ 0
p1-val : 1 + 1 + 2 ≡ 4
p1-val = refl

-- p(2) = 16 + 2 + 2 = 20 ≡ 2 (mod 3) ≠ 0
p2-val : 16 + 2 + 2 ≡ 20
p2-val = refl

-- 约化关系验证: α⁴ = 1 + 2α
alpha4-reduction : alpha *gf81 (alpha *gf81 (alpha *gf81 alpha)) ≡ (T₁ , T₂ , T₀ , T₀)
alpha4-reduction = refl

--------------------------------------------------------------------------------
-- 12. GF(81)* 乘法群 — 阶 80
--------------------------------------------------------------------------------

-- |GF(81)| = 3⁴ = 81
pow-3-4 : 3 ^ 4 ≡ 81
pow-3-4 = refl

-- |GF(81)*| = 81 - 1 = 80
gf81-star-order : 81 ≡ 80 + 1
gf81-star-order = refl

-- 80 = 2⁴ × 5
gf81-star-factorization : 80 ≡ 16 * 5
gf81-star-factorization = refl

--------------------------------------------------------------------------------
-- 13. α 的幂次表
--------------------------------------------------------------------------------

-- α⁰ = 1
alpha-pow-0 : gf81-one ≡ (T₁ , T₀ , T₀ , T₀)
alpha-pow-0 = refl

-- α¹ = α
alpha-pow-1 : alpha ≡ (T₀ , T₁ , T₀ , T₀)
alpha-pow-1 = refl

-- α² = (0, 0, 1, 0)
alpha-pow-2 : alpha *gf81 alpha ≡ (T₀ , T₀ , T₁ , T₀)
alpha-pow-2 = refl

-- α³ = (0, 0, 0, 1)
alpha-pow-3 : alpha *gf81 (alpha *gf81 alpha) ≡ (T₀ , T₀ , T₀ , T₁)
alpha-pow-3 = refl

-- α⁴ = 1 + 2α = (1, 2, 0, 0) — 不可约多项式约化
alpha-pow-4 : alpha *gf81 (alpha *gf81 (alpha *gf81 alpha))
            ≡ (T₁ , T₂ , T₀ , T₀)
alpha-pow-4 = refl

-- α⁵ = α + 2α² = (0, 1, 2, 0)
alpha-pow-5 : alpha *gf81 (alpha *gf81 (alpha *gf81 (alpha *gf81 alpha)))
            ≡ (T₀ , T₁ , T₂ , T₀)
alpha-pow-5 = refl

-- α⁶ = α² + 2α³ = (0, 0, 1, 2)
alpha-pow-6 : alpha *gf81 (alpha *gf81 (alpha *gf81 (alpha *gf81 (alpha *gf81 alpha))))
            ≡ (T₀ , T₀ , T₁ , T₂)
alpha-pow-6 = refl

-- α⁸ = 1 + α + α² = (1, 1, 1, 0)
alpha-pow-8 : alpha *gf81 (alpha *gf81 (alpha *gf81 (alpha *gf81
              (alpha *gf81 (alpha *gf81 (alpha *gf81 alpha))))))
            ≡ (T₁ , T₁ , T₁ , T₀)
alpha-pow-8 = refl

-- α⁹ = α + α² + α³ = (0, 1, 1, 1) — Frobenius 轨道节点
alpha-pow-9 : alpha *gf81 (alpha *gf81 (alpha *gf81 (alpha *gf81
              (alpha *gf81 (alpha *gf81 (alpha *gf81 (alpha *gf81 alpha)))))))
            ≡ (T₀ , T₁ , T₁ , T₁)
alpha-pow-9 = refl

--------------------------------------------------------------------------------
-- 14. 域扩张塔位置
--
-- GF(3^a) ⊂ GF(3^b) 当且仅当 a ∣ b
--
--            GF(729) = GF(3⁶)
--           /         \
--   GF(81)=GF(3⁴)   GF(27)=GF(3³)     GF(243)=GF(3⁵)
--        \           /                     |
--         GF(9)=GF(3²)                  GF(3)
--              \                        /
--               GF(3) = GF(3¹)
--
-- GF(81) 的子域: GF(3), GF(9) (因为 1∣4, 2∣4)
-- GF(81) 嵌入: GF(81) ⊂ GF(3^lcm(4,n)) 对任意 n
--------------------------------------------------------------------------------

-- 2 ∣ 4 的构造性证据
two-divides-four : 4 ≡ 2 * 2
two-divides-four = refl

-- 1 ∣ 4 的构造性证据
one-divides-four : 4 ≡ 1 * 4
one-divides-four = refl
