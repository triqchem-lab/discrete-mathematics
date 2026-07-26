{-# OPTIONS --rewriting #-}
module Sovereign.Algebra.GF27 where

-- GF(3³) = GF(3)[x]/(x³+2x+1)
-- 27 个元素的有限域, α³ = α+2 (mod 3)
-- 不可约性: f(0)=1, f(1)=1+2+1≡1, f(2)=8+4+1≡1, 无根 ⟹ 不可约
-- 乘法群 GF(27)* ≅ Z/26Z, 生成元 α (阶 26, α¹³=2=-1)

open import Data.Product using (_×_; _,_; Σ; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; cong₂; sym; trans)
open import Data.Nat using (ℕ; zero; suc)
open import Sovereign.Base.Trit using (Trit; T₀; T₁; T₂; _⊕_; _⊗_;
  negate; negate²;
  ⊕-identityˡ; ⊕-identityʳ; ⊕-comm; ⊕-assoc; ⊕-inverse;
  ⊗-identityˡ; ⊗-identityʳ; ⊗-comm; ⊗-assoc;
  ⊗-distribˡ-⊕; ⊗-distribʳ-⊕; ⊗-zeroˡ; ⊗-zeroʳ)

--------------------------------------------------------------------------------
-- 0. GF(3) 辅助引理
--------------------------------------------------------------------------------

-- 等式推理组合子
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

⊗-negate-r : ∀ x y → x ⊗ (negate y) ≡ negate (x ⊗ y)
⊗-negate-r x y = trans (sym (negate-⊗-comm x y)) (sym (negate-⊗ x y))

swap-middle : ∀ w x y z → (w ⊕ x) ⊕ (y ⊕ z) ≡ (w ⊕ y) ⊕ (x ⊕ z)
swap-middle w x y z =
  trans (sym (⊕-assoc (w ⊕ x) y z))
    (trans (cong (_⊕ z) (⊕-assoc w x y))
      (trans (cong (λ t → (w ⊕ t) ⊕ z) (⊕-comm x y))
        (trans (cong (_⊕ z) (sym (⊕-assoc w y x)))
          (⊕-assoc (w ⊕ y) x z))))

cong-triple : ∀ {a b c d e f : Trit} →
  a ≡ d → b ≡ e → c ≡ f → (a , b , c) ≡ (d , e , f)
cong-triple refl refl refl = refl

-- 六项重排
inner-swap : ∀ B D E F → B ⊕ (D ⊕ (E ⊕ F)) ≡ E ⊕ (B ⊕ (D ⊕ F))
inner-swap B D E F =
  trans (sym (⊕-assoc B D (E ⊕ F)))
    (trans (swap-middle B D E F)
      (trans (cong (_⊕ (D ⊕ F)) (⊕-comm B E))
        (⊕-assoc E B (D ⊕ F))))

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
  ≡⟨ cong (A ⊕_) (cong (λ x → x ⊕ (D ⊕ (E ⊕ F))) (⊕-comm B C)) ⟩
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

--------------------------------------------------------------------------------
-- 1. GF(27) 类型
--------------------------------------------------------------------------------

GF27 : Set
GF27 = Trit × Trit × Trit  -- (a, b, c) = a + bα + cα²

gf27-zero : GF27
gf27-zero = T₀ , T₀ , T₀

gf27-one : GF27
gf27-one = T₁ , T₀ , T₀

alpha : GF27
alpha = T₀ , T₁ , T₀

alpha-sq : GF27
alpha-sq = T₀ , T₀ , T₁

embed-gf3-gf27 : Trit → GF27
embed-gf3-gf27 a = a , T₀ , T₀

--------------------------------------------------------------------------------
-- 2. 加法与加法群 (Z/3Z)³
--------------------------------------------------------------------------------

infixl 6 _+gf27_
_+gf27_ : GF27 → GF27 → GF27
(a , b , c) +gf27 (d , e , f) = (a ⊕ d) , (b ⊕ e) , (c ⊕ f)

+gf27-identityˡ : ∀ x → gf27-zero +gf27 x ≡ x
+gf27-identityˡ (a , b , c) =
  cong-triple (⊕-identityˡ a) (⊕-identityˡ b) (⊕-identityˡ c)

+gf27-identityʳ : ∀ x → x +gf27 gf27-zero ≡ x
+gf27-identityʳ (a , b , c) =
  cong-triple (⊕-identityʳ a) (⊕-identityʳ b) (⊕-identityʳ c)

+gf27-comm : ∀ x y → x +gf27 y ≡ y +gf27 x
+gf27-comm (a , b , c) (d , e , f) =
  cong-triple (⊕-comm a d) (⊕-comm b e) (⊕-comm c f)

+gf27-assoc : ∀ x y z → (x +gf27 y) +gf27 z ≡ x +gf27 (y +gf27 z)
+gf27-assoc (a , b , c) (d , e , f) (g , h , i) =
  cong-triple (⊕-assoc a d g) (⊕-assoc b e h) (⊕-assoc c f i)

negate27 : GF27 → GF27
negate27 (a , b , c) = negate a , negate b , negate c

+gf27-inverse : ∀ x → x +gf27 negate27 x ≡ gf27-zero
+gf27-inverse (a , b , c) =
  cong-triple (⊕-inverse a) (⊕-inverse b) (⊕-inverse c)

--------------------------------------------------------------------------------
-- 3. 乘法 — α³ = α+2, α⁴ = α²+2α
--------------------------------------------------------------------------------

infixl 7 _*gf27_
_*gf27_ : GF27 → GF27 → GF27
(a , b , c) *gf27 (d , e , f) =
    ((a ⊗ d) ⊕ negate ((b ⊗ f) ⊕ (c ⊗ e)))
  , (((a ⊗ e) ⊕ (b ⊗ d)) ⊕ ((b ⊗ f) ⊕ ((c ⊗ e) ⊕ negate (c ⊗ f))))
  , (((a ⊗ f) ⊕ (b ⊗ e)) ⊕ ((c ⊗ d) ⊕ (c ⊗ f)))

--------------------------------------------------------------------------------
-- 4. 乘法单位元
--------------------------------------------------------------------------------

*gf27-identityˡ : ∀ x → gf27-one *gf27 x ≡ x
*gf27-identityˡ (d , e , f) = cong-triple eq₀ eq₁ eq₂
  where
    eq₀ : (T₁ ⊗ d) ⊕ negate ((T₀ ⊗ f) ⊕ (T₀ ⊗ e)) ≡ d
    eq₀ = trans (cong₂ _⊕_ (⊗-identityˡ d)
                  (cong negate (cong₂ _⊕_ (⊗-zeroˡ f) (⊗-zeroˡ e))))
          (trans (cong (d ⊕_) (cong negate (⊕-identityˡ T₀)))
                 (⊕-identityʳ d))
    eq₁ : (((T₁ ⊗ e) ⊕ (T₀ ⊗ d)) ⊕
           ((T₀ ⊗ f) ⊕ ((T₀ ⊗ e) ⊕ negate (T₀ ⊗ f)))) ≡ e
    eq₁ = trans (cong₂ (λ u v → (u ⊕ v) ⊕
                   ((T₀ ⊗ f) ⊕ ((T₀ ⊗ e) ⊕ negate (T₀ ⊗ f))))
                  (⊗-identityˡ e) (⊗-zeroˡ d))
          (trans (cong (_⊕ ((T₀ ⊗ f) ⊕ ((T₀ ⊗ e) ⊕ negate (T₀ ⊗ f))))
                   (⊕-identityʳ e))
          (trans (cong₂ (λ u v → e ⊕ (u ⊕ (v ⊕ negate u)))
                   (⊗-zeroˡ f) (⊗-zeroˡ e))
          (trans (cong (e ⊕_) (cong₂ (λ u v → u ⊕ (v ⊕ negate u))
                   (⊕-identityˡ T₀) (⊕-identityˡ T₀)))
                 (⊕-identityʳ e))))
    eq₂ : (((T₁ ⊗ f) ⊕ (T₀ ⊗ e)) ⊕ ((T₀ ⊗ d) ⊕ (T₀ ⊗ f))) ≡ f
    eq₂ = trans (cong₂ (λ u v → (u ⊕ v) ⊕ ((T₀ ⊗ d) ⊕ (T₀ ⊗ f)))
                  (⊗-identityˡ f) (⊗-zeroˡ e))
          (trans (cong (_⊕ ((T₀ ⊗ d) ⊕ (T₀ ⊗ f))) (⊕-identityʳ f))
          (trans (cong₂ (λ u v → f ⊕ (u ⊕ v)) (⊗-zeroˡ d) (⊗-zeroˡ f))
          (trans (cong (f ⊕_) (cong₂ _⊕_ (⊕-identityˡ T₀) (⊕-identityˡ T₀)))
                 (⊕-identityʳ f))))

*gf27-identityʳ : ∀ x → x *gf27 gf27-one ≡ x
*gf27-identityʳ (a , b , c) = cong-triple eq₀ eq₁ eq₂
  where
    eq₀ : (a ⊗ T₁) ⊕ negate ((b ⊗ T₀) ⊕ (c ⊗ T₀)) ≡ a
    eq₀ = trans (cong₂ _⊕_ (⊗-identityʳ a)
                  (cong negate (cong₂ _⊕_ (⊗-zeroʳ b) (⊗-zeroʳ c))))
          (trans (cong (a ⊕_) (cong negate (⊕-identityˡ T₀)))
                 (⊕-identityʳ a))
    eq₁ : (((a ⊗ T₀) ⊕ (b ⊗ T₁)) ⊕
           ((b ⊗ T₀) ⊕ ((c ⊗ T₀) ⊕ negate (c ⊗ T₀)))) ≡ b
    eq₁ = trans (cong₂ (λ u v → (u ⊕ v) ⊕
                   ((b ⊗ T₀) ⊕ ((c ⊗ T₀) ⊕ negate (c ⊗ T₀))))
                  (⊗-zeroʳ a) (⊗-identityʳ b))
          (trans (cong (_⊕ ((b ⊗ T₀) ⊕ ((c ⊗ T₀) ⊕ negate (c ⊗ T₀))))
                   (⊕-identityˡ b))
          (trans (cong₂ (λ u v → b ⊕ (u ⊕ (v ⊕ negate v)))
                   (⊗-zeroʳ b) (⊗-zeroʳ c))
          (trans (cong (b ⊕_) (cong₂ (λ u v → u ⊕ (v ⊕ negate v))
                   (⊕-identityˡ T₀) (⊕-identityˡ T₀)))
                 (⊕-identityʳ b))))
    eq₂ : (((a ⊗ T₀) ⊕ (b ⊗ T₀)) ⊕ ((c ⊗ T₁) ⊕ (c ⊗ T₀))) ≡ c
    eq₂ = trans (cong₂ (λ u v → (u ⊕ v) ⊕ ((c ⊗ T₁) ⊕ (c ⊗ T₀)))
                  (⊗-zeroʳ a) (⊗-zeroʳ b))
          (trans (cong (_⊕ ((c ⊗ T₁) ⊕ (c ⊗ T₀))) (⊕-identityˡ T₀))
          (trans (cong (T₀ ⊕_) (cong₂ _⊕_ (⊗-identityʳ c) (⊗-zeroʳ c)))
          (trans (cong (T₀ ⊕_) (⊕-identityʳ c))
                 (⊕-identityˡ c))))

--------------------------------------------------------------------------------
-- 5. 乘法交换律
--------------------------------------------------------------------------------

*gf27-comm : ∀ x y → x *gf27 y ≡ y *gf27 x
*gf27-comm (a , b , c) (d , e , f) = cong-triple eq₀ eq₁ eq₂
  where
    eq₀ : (a ⊗ d) ⊕ negate ((b ⊗ f) ⊕ (c ⊗ e))
        ≡ (d ⊗ a) ⊕ negate ((e ⊗ c) ⊕ (f ⊗ b))
    eq₀ = cong₂ _⊕_ (⊗-comm a d)
            (cong negate (trans (cong₂ _⊕_ (⊗-comm b f) (⊗-comm c e))
                                (⊕-comm (f ⊗ b) (e ⊗ c))))

    eq₁ : (((a ⊗ e) ⊕ (b ⊗ d)) ⊕ ((b ⊗ f) ⊕ ((c ⊗ e) ⊕ negate (c ⊗ f))))
        ≡ (((d ⊗ b) ⊕ (e ⊗ a)) ⊕ ((e ⊗ c) ⊕ ((f ⊗ b) ⊕ negate (f ⊗ c))))
    eq₁ = begin
      ((a ⊗ e) ⊕ (b ⊗ d)) ⊕ ((b ⊗ f) ⊕ ((c ⊗ e) ⊕ negate (c ⊗ f)))
      ≡⟨ cong₂ (λ u v → (u ⊕ v) ⊕ ((b ⊗ f) ⊕ ((c ⊗ e) ⊕ negate (c ⊗ f))))
           (⊗-comm a e) (⊗-comm b d) ⟩
      ((e ⊗ a) ⊕ (d ⊗ b)) ⊕ ((b ⊗ f) ⊕ ((c ⊗ e) ⊕ negate (c ⊗ f)))
      ≡⟨ cong₂ (λ u v → ((e ⊗ a) ⊕ (d ⊗ b)) ⊕ (u ⊕ (v ⊕ negate (c ⊗ f))))
           (⊗-comm b f) (⊗-comm c e) ⟩
      ((e ⊗ a) ⊕ (d ⊗ b)) ⊕ ((f ⊗ b) ⊕ ((e ⊗ c) ⊕ negate (c ⊗ f)))
      ≡⟨ cong (λ u → ((e ⊗ a) ⊕ (d ⊗ b)) ⊕ ((f ⊗ b) ⊕ ((e ⊗ c) ⊕ u)))
           (cong negate (⊗-comm c f)) ⟩
      ((e ⊗ a) ⊕ (d ⊗ b)) ⊕ ((f ⊗ b) ⊕ ((e ⊗ c) ⊕ negate (f ⊗ c)))
      ≡⟨ cong (_⊕ ((f ⊗ b) ⊕ ((e ⊗ c) ⊕ negate (f ⊗ c))))
           (⊕-comm (e ⊗ a) (d ⊗ b)) ⟩
      ((d ⊗ b) ⊕ (e ⊗ a)) ⊕ ((f ⊗ b) ⊕ ((e ⊗ c) ⊕ negate (f ⊗ c)))
      ≡⟨ cong (((d ⊗ b) ⊕ (e ⊗ a)) ⊕_)
           (sym (⊕-assoc (f ⊗ b) (e ⊗ c) (negate (f ⊗ c)))) ⟩
      ((d ⊗ b) ⊕ (e ⊗ a)) ⊕ (((f ⊗ b) ⊕ (e ⊗ c)) ⊕ negate (f ⊗ c))
      ≡⟨ cong (((d ⊗ b) ⊕ (e ⊗ a)) ⊕_)
           (cong (_⊕ negate (f ⊗ c)) (⊕-comm (f ⊗ b) (e ⊗ c))) ⟩
      ((d ⊗ b) ⊕ (e ⊗ a)) ⊕ (((e ⊗ c) ⊕ (f ⊗ b)) ⊕ negate (f ⊗ c))
      ≡⟨ cong (((d ⊗ b) ⊕ (e ⊗ a)) ⊕_)
           (⊕-assoc (e ⊗ c) (f ⊗ b) (negate (f ⊗ c))) ⟩
      ((d ⊗ b) ⊕ (e ⊗ a)) ⊕ ((e ⊗ c) ⊕ ((f ⊗ b) ⊕ negate (f ⊗ c)))
      ∎

    eq₂ : (((a ⊗ f) ⊕ (b ⊗ e)) ⊕ ((c ⊗ d) ⊕ (c ⊗ f)))
        ≡ (((d ⊗ c) ⊕ (e ⊗ b)) ⊕ ((f ⊗ a) ⊕ (f ⊗ c)))
    eq₂ = begin
      ((a ⊗ f) ⊕ (b ⊗ e)) ⊕ ((c ⊗ d) ⊕ (c ⊗ f))
      ≡⟨ cong₂ (λ u v → (u ⊕ v) ⊕ ((c ⊗ d) ⊕ (c ⊗ f)))
           (⊗-comm a f) (⊗-comm b e) ⟩
      ((f ⊗ a) ⊕ (e ⊗ b)) ⊕ ((c ⊗ d) ⊕ (c ⊗ f))
      ≡⟨ cong₂ (λ u v → ((f ⊗ a) ⊕ (e ⊗ b)) ⊕ (u ⊕ v))
           (⊗-comm c d) (⊗-comm c f) ⟩
      ((f ⊗ a) ⊕ (e ⊗ b)) ⊕ ((d ⊗ c) ⊕ (f ⊗ c))
      ≡⟨ swap-middle (f ⊗ a) (e ⊗ b) (d ⊗ c) (f ⊗ c) ⟩
      ((f ⊗ a) ⊕ (d ⊗ c)) ⊕ ((e ⊗ b) ⊕ (f ⊗ c))
      ≡⟨ cong (_⊕ ((e ⊗ b) ⊕ (f ⊗ c)))
           (⊕-comm (f ⊗ a) (d ⊗ c)) ⟩
      ((d ⊗ c) ⊕ (f ⊗ a)) ⊕ ((e ⊗ b) ⊕ (f ⊗ c))
      ≡⟨ swap-middle (d ⊗ c) (f ⊗ a) (e ⊗ b) (f ⊗ c) ⟩
      ((d ⊗ c) ⊕ (e ⊗ b)) ⊕ ((f ⊗ a) ⊕ (f ⊗ c))
      ∎

--------------------------------------------------------------------------------
-- 6. α 的性质与特征 3
--------------------------------------------------------------------------------

alpha-sq-def : alpha *gf27 alpha ≡ alpha-sq
alpha-sq-def = refl

-- α³ = α+2: 不可约多项式 x³+2x+1 的根
alpha-cubed : alpha *gf27 (alpha *gf27 alpha) ≡ (T₂ , T₁ , T₀)
alpha-cubed = refl

alpha-cubed-struct : alpha *gf27 (alpha *gf27 alpha)
                   ≡ alpha +gf27 embed-gf3-gf27 T₂
alpha-cubed-struct = refl

-- 特征 3: 1+1+1 = 0
char-3 : gf27-one +gf27 gf27-one +gf27 gf27-one ≡ gf27-zero
char-3 = refl

char-3-univ : ∀ x → x +gf27 x +gf27 x ≡ gf27-zero
char-3-univ (a , b , c) = cong-triple (ch a) (ch b) (ch c)
  where ch : ∀ t → (t ⊕ t) ⊕ t ≡ T₀
        ch T₀ = refl; ch T₁ = refl; ch T₂ = refl

--------------------------------------------------------------------------------
-- 7. GF(3) 嵌入
--------------------------------------------------------------------------------

embed-add : ∀ a b →
  embed-gf3-gf27 (a ⊕ b) ≡ embed-gf3-gf27 a +gf27 embed-gf3-gf27 b
embed-add a b = refl

embed-mul : ∀ a b →
  embed-gf3-gf27 (a ⊗ b) ≡ embed-gf3-gf27 a *gf27 embed-gf3-gf27 b
embed-mul T₀ T₀ = refl; embed-mul T₀ T₁ = refl; embed-mul T₀ T₂ = refl
embed-mul T₁ T₀ = refl; embed-mul T₁ T₁ = refl; embed-mul T₁ T₂ = refl
embed-mul T₂ T₀ = refl; embed-mul T₂ T₁ = refl; embed-mul T₂ T₂ = refl

embed-one : embed-gf3-gf27 T₁ ≡ gf27-one
embed-one = refl

--------------------------------------------------------------------------------
-- 8. 多项式模型 — 分配律的干净证明
--
-- GF27 乘法 = reduce ∘ poly-mul
-- poly-mul: 原始多项式乘法 (度 ≤ 4)
-- reduce:   用 α³=α+2 化简
--------------------------------------------------------------------------------

Poly5 : Set
Poly5 = Trit × Trit × Trit × Trit × Trit

_+p5_ : Poly5 → Poly5 → Poly5
(p₀ , p₁ , p₂ , p₃ , p₄) +p5 (q₀ , q₁ , q₂ , q₃ , q₄) =
  (p₀ ⊕ q₀) , (p₁ ⊕ q₁) , (p₂ ⊕ q₂) , (p₃ ⊕ q₃) , (p₄ ⊕ q₄)

poly-mul : GF27 → GF27 → Poly5
poly-mul (a , b , c) (d , e , f) =
    (a ⊗ d)
  , ((a ⊗ e) ⊕ (b ⊗ d))
  , ((a ⊗ f) ⊕ ((b ⊗ e) ⊕ (c ⊗ d)))
  , ((b ⊗ f) ⊕ (c ⊗ e))
  , (c ⊗ f)

-- x³ = α+2 ⟹ p₃x³ → p₃·α + 2p₃ = p₃·α + negate(p₃)
-- x⁴ = α²+2α ⟹ p₄x⁴ → p₄·α² + negate(p₄)·α
reduce-p5 : Poly5 → GF27
reduce-p5 (p₀ , p₁ , p₂ , p₃ , p₄) =
    (p₀ ⊕ negate p₃)
  , ((p₁ ⊕ p₃) ⊕ negate p₄)
  , (p₂ ⊕ p₄)

-- *gf27 ≡ reduce ∘ poly-mul
mul-via-poly : ∀ x y → x *gf27 y ≡ reduce-p5 (poly-mul x y)
mul-via-poly (a , b , c) (d , e , f) = cong-triple refl
  -- r₁: X ⊕ (Y ⊕ (Z ⊕ W)) → X ⊕ ((Y ⊕ Z) ⊕ W) → (X ⊕ (Y ⊕ Z)) ⊕ W
  (trans (cong (((a ⊗ e) ⊕ (b ⊗ d)) ⊕_)
           (sym (⊕-assoc (b ⊗ f) (c ⊗ e) (negate (c ⊗ f)))))
         (sym (⊕-assoc (((a ⊗ e) ⊕ (b ⊗ d)))
                (((b ⊗ f) ⊕ (c ⊗ e))) (negate (c ⊗ f)))))
  -- r₂: (X ⊕ Y) ⊕ (Z ⊕ W) → X ⊕ (Y ⊕ (Z ⊕ W)) → X ⊕ ((Y ⊕ Z) ⊕ W) → (X ⊕ (Y ⊕ Z)) ⊕ W
  (trans (⊕-assoc (a ⊗ f) (b ⊗ e) ((c ⊗ d) ⊕ (c ⊗ f)))
    (trans (cong ((a ⊗ f) ⊕_)
             (sym (⊕-assoc (b ⊗ e) (c ⊗ d) (c ⊗ f))))
           (sym (⊕-assoc (a ⊗ f) ((b ⊗ e) ⊕ (c ⊗ d)) (c ⊗ f)))))

-- poly-mul 左分配律
poly-mul-distribˡ : ∀ x y z →
  poly-mul x (y +gf27 z) ≡ poly-mul x y +p5 poly-mul x z
poly-mul-distribˡ (a , b , c) (d , e , f) (g , h , i) =
  cong-triple-p5 eq₀ eq₁ eq₂ eq₃ eq₄
  where
    cong-triple-p5 : ∀ {a₀ b₀ c₀ d₀ e₀ a₁ b₁ c₁ d₁ e₁ : Trit} →
      a₀ ≡ a₁ → b₀ ≡ b₁ → c₀ ≡ c₁ → d₀ ≡ d₁ → e₀ ≡ e₁ →
      (a₀ , b₀ , c₀ , d₀ , e₀) ≡ (a₁ , b₁ , c₁ , d₁ , e₁)
    cong-triple-p5 refl refl refl refl refl = refl

    eq₀ : a ⊗ (d ⊕ g) ≡ (a ⊗ d) ⊕ (a ⊗ g)
    eq₀ = ⊗-distribˡ-⊕ a d g

    eq₁ : (a ⊗ (e ⊕ h)) ⊕ (b ⊗ (d ⊕ g))
        ≡ ((a ⊗ e) ⊕ (b ⊗ d)) ⊕ ((a ⊗ h) ⊕ (b ⊗ g))
    eq₁ = trans (cong₂ _⊕_ (⊗-distribˡ-⊕ a e h) (⊗-distribˡ-⊕ b d g))
                (swap-middle (a ⊗ e) (a ⊗ h) (b ⊗ d) (b ⊗ g))

    eq₂ : (a ⊗ (f ⊕ i)) ⊕ ((b ⊗ (e ⊕ h)) ⊕ (c ⊗ (d ⊕ g)))
        ≡ ((a ⊗ f) ⊕ ((b ⊗ e) ⊕ (c ⊗ d)))
        ⊕ ((a ⊗ i) ⊕ ((b ⊗ h) ⊕ (c ⊗ g)))
    eq₂ = trans (cong₂ (λ u v → u ⊕ (v ⊕ (c ⊗ (d ⊕ g))))
                  (⊗-distribˡ-⊕ a f i) (⊗-distribˡ-⊕ b e h))
          (trans (cong (((a ⊗ f) ⊕ (a ⊗ i)) ⊕_)
                  (cong (((b ⊗ e) ⊕ (b ⊗ h)) ⊕_) (⊗-distribˡ-⊕ c d g)))
                 (⊕-rearrange-6 (a ⊗ f) (a ⊗ i) (b ⊗ e) (b ⊗ h)
                                 (c ⊗ d) (c ⊗ g)))

    eq₃ : (b ⊗ (f ⊕ i)) ⊕ (c ⊗ (e ⊕ h))
        ≡ ((b ⊗ f) ⊕ (c ⊗ e)) ⊕ ((b ⊗ i) ⊕ (c ⊗ h))
    eq₃ = trans (cong₂ _⊕_ (⊗-distribˡ-⊕ b f i) (⊗-distribˡ-⊕ c e h))
                (swap-middle (b ⊗ f) (b ⊗ i) (c ⊗ e) (c ⊗ h))

    eq₄ : c ⊗ (f ⊕ i) ≡ (c ⊗ f) ⊕ (c ⊗ i)
    eq₄ = ⊗-distribˡ-⊕ c f i

-- reduce 保持加法
reduce-additive : ∀ p q →
  reduce-p5 (p +p5 q) ≡ reduce-p5 p +gf27 reduce-p5 q
reduce-additive (p₀ , p₁ , p₂ , p₃ , p₄) (q₀ , q₁ , q₂ , q₃ , q₄) =
  cong-triple eq₀ eq₁ eq₂
  where
    eq₀ : (p₀ ⊕ q₀) ⊕ negate (p₃ ⊕ q₃)
        ≡ (p₀ ⊕ negate p₃) ⊕ (q₀ ⊕ negate q₃)
    eq₀ = trans (cong ((p₀ ⊕ q₀) ⊕_) (negate-⊕ p₃ q₃))
                (swap-middle p₀ q₀ (negate p₃) (negate q₃))

    eq₁ : ((p₁ ⊕ q₁) ⊕ (p₃ ⊕ q₃)) ⊕ negate (p₄ ⊕ q₄)
        ≡ ((p₁ ⊕ p₃) ⊕ negate p₄) ⊕ ((q₁ ⊕ q₃) ⊕ negate q₄)
    eq₁ = trans (cong (((p₁ ⊕ q₁) ⊕ (p₃ ⊕ q₃)) ⊕_) (negate-⊕ p₄ q₄))
          (trans (⊕-assoc (p₁ ⊕ q₁) (p₃ ⊕ q₃) (negate p₄ ⊕ negate q₄))
          (trans (⊕-rearrange-6 p₁ q₁ p₃ q₃ (negate p₄) (negate q₄))
          (cong₂ (λ u v → u ⊕ v)
            (sym (⊕-assoc p₁ p₃ (negate p₄)))
            (sym (⊕-assoc q₁ q₃ (negate q₄))))))

    eq₂ : (p₂ ⊕ q₂) ⊕ (p₄ ⊕ q₄) ≡ (p₂ ⊕ p₄) ⊕ (q₂ ⊕ q₄)
    eq₂ = swap-middle p₂ q₂ p₄ q₄

--------------------------------------------------------------------------------
-- 9. 分配律
--------------------------------------------------------------------------------

*gf27-distribˡ : ∀ x y z →
  x *gf27 (y +gf27 z) ≡ (x *gf27 y) +gf27 (x *gf27 z)
*gf27-distribˡ x y z =
  trans (mul-via-poly x (y +gf27 z))
  (trans (cong reduce-p5 (poly-mul-distribˡ x y z))
  (trans (reduce-additive (poly-mul x y) (poly-mul x z))
         (cong₂ _+gf27_ (sym (mul-via-poly x y)) (sym (mul-via-poly x z)))))

*gf27-distribʳ : ∀ x y z →
  (x +gf27 y) *gf27 z ≡ (x *gf27 z) +gf27 (y *gf27 z)
*gf27-distribʳ x y z =
  trans (*gf27-comm (x +gf27 y) z)
  (trans (*gf27-distribˡ z x y)
         (cong₂ _+gf27_ (*gf27-comm z x) (*gf27-comm z y)))

--------------------------------------------------------------------------------
-- 10. GF(9) 不嵌入 GF(27)
--
-- GF(3²) 不是 GF(3³) 的子域, 因为 2 ∤ 3。
-- GF(p^m) ⊆ GF(p^n) ⟺ m | n。
-- GF(3) 是两者的公共子域 (embed-gf3-gf27)。
--------------------------------------------------------------------------------

--------------------------------------------------------------------------------
-- 11. GF(27)* 乘法群 — 26 个非零元素
--
-- 用 α 的幂次编号: pow_n = αⁿ
-- α 是本原元: 阶 26, α¹³ = 2 = -1
--------------------------------------------------------------------------------

data GF27Star : Set where
  pow0  : GF27Star  -- α⁰  = 1         = (1,0,0)
  pow1  : GF27Star  -- α¹  = α         = (0,1,0)
  pow2  : GF27Star  -- α²              = (0,0,1)
  pow3  : GF27Star  -- α³  = 2+α       = (2,1,0)
  pow4  : GF27Star  -- α⁴  = 2α+α²     = (0,2,1)
  pow5  : GF27Star  -- α⁵  = 2+α+2α²   = (2,1,2)
  pow6  : GF27Star  -- α⁶  = 1+α+α²    = (1,1,1)
  pow7  : GF27Star  -- α⁷  = 2+2α+α²   = (2,2,1)
  pow8  : GF27Star  -- α⁸  = 2+2α²     = (2,0,2)
  pow9  : GF27Star  -- α⁹  = 1+α       = (1,1,0)
  pow10 : GF27Star  -- α¹⁰ = α+α²      = (0,1,1)
  pow11 : GF27Star  -- α¹¹ = 2+α+α²    = (2,1,1)
  pow12 : GF27Star  -- α¹² = 2+α²      = (2,0,1)
  pow13 : GF27Star  -- α¹³ = 2 = -1    = (2,0,0)
  pow14 : GF27Star  -- α¹⁴ = 2α        = (0,2,0)
  pow15 : GF27Star  -- α¹⁵ = 2α²       = (0,0,2)
  pow16 : GF27Star  -- α¹⁶ = 1+2α      = (1,2,0)
  pow17 : GF27Star  -- α¹⁷ = α+2α²     = (0,1,2)
  pow18 : GF27Star  -- α¹⁸ = 1+2α+α²   = (1,2,1)
  pow19 : GF27Star  -- α¹⁹ = 2+2α+2α²  = (2,2,2)
  pow20 : GF27Star  -- α²⁰ = 1+α+2α²   = (1,1,2)
  pow21 : GF27Star  -- α²¹ = 1+α²      = (1,0,1)
  pow22 : GF27Star  -- α²² = 2+2α      = (2,2,0)
  pow23 : GF27Star  -- α²³ = 2α+2α²    = (0,2,2)
  pow24 : GF27Star  -- α²⁴ = 1+2α+2α²  = (1,2,2)
  pow25 : GF27Star  -- α²⁵ = 1+2α²     = (1,0,2)

toGF27 : GF27Star → GF27
toGF27 pow0  = T₁ , T₀ , T₀
toGF27 pow1  = T₀ , T₁ , T₀
toGF27 pow2  = T₀ , T₀ , T₁
toGF27 pow3  = T₂ , T₁ , T₀
toGF27 pow4  = T₀ , T₂ , T₁
toGF27 pow5  = T₂ , T₁ , T₂
toGF27 pow6  = T₁ , T₁ , T₁
toGF27 pow7  = T₂ , T₂ , T₁
toGF27 pow8  = T₂ , T₀ , T₂
toGF27 pow9  = T₁ , T₁ , T₀
toGF27 pow10 = T₀ , T₁ , T₁
toGF27 pow11 = T₂ , T₁ , T₁
toGF27 pow12 = T₂ , T₀ , T₁
toGF27 pow13 = T₂ , T₀ , T₀
toGF27 pow14 = T₀ , T₂ , T₀
toGF27 pow15 = T₀ , T₀ , T₂
toGF27 pow16 = T₁ , T₂ , T₀
toGF27 pow17 = T₀ , T₁ , T₂
toGF27 pow18 = T₁ , T₂ , T₁
toGF27 pow19 = T₂ , T₂ , T₂
toGF27 pow20 = T₁ , T₁ , T₂
toGF27 pow21 = T₁ , T₀ , T₁
toGF27 pow22 = T₂ , T₂ , T₀
toGF27 pow23 = T₀ , T₂ , T₂
toGF27 pow24 = T₁ , T₂ , T₂
toGF27 pow25 = T₁ , T₀ , T₂

fromGF27 : GF27 → GF27Star
fromGF27 (T₀ , T₀ , T₀) = pow0  -- 零元映到单位元 (约定)
fromGF27 (T₁ , T₀ , T₀) = pow0
fromGF27 (T₂ , T₀ , T₀) = pow13
fromGF27 (T₀ , T₁ , T₀) = pow1
fromGF27 (T₀ , T₂ , T₀) = pow14
fromGF27 (T₀ , T₀ , T₁) = pow2
fromGF27 (T₀ , T₀ , T₂) = pow15
fromGF27 (T₁ , T₁ , T₀) = pow9
fromGF27 (T₁ , T₂ , T₀) = pow16
fromGF27 (T₂ , T₁ , T₀) = pow3
fromGF27 (T₂ , T₂ , T₀) = pow22
fromGF27 (T₁ , T₀ , T₁) = pow21
fromGF27 (T₁ , T₀ , T₂) = pow25
fromGF27 (T₂ , T₀ , T₁) = pow12
fromGF27 (T₂ , T₀ , T₂) = pow8
fromGF27 (T₀ , T₁ , T₁) = pow10
fromGF27 (T₀ , T₁ , T₂) = pow17
fromGF27 (T₀ , T₂ , T₁) = pow4
fromGF27 (T₀ , T₂ , T₂) = pow23
fromGF27 (T₁ , T₁ , T₁) = pow6
fromGF27 (T₁ , T₁ , T₂) = pow20
fromGF27 (T₁ , T₂ , T₁) = pow18
fromGF27 (T₁ , T₂ , T₂) = pow24
fromGF27 (T₂ , T₁ , T₁) = pow11
fromGF27 (T₂ , T₁ , T₂) = pow5
fromGF27 (T₂ , T₂ , T₁) = pow7
fromGF27 (T₂ , T₂ , T₂) = pow19

fromGF27-toGF27 : ∀ x → fromGF27 (toGF27 x) ≡ x
fromGF27-toGF27 pow0  = refl
fromGF27-toGF27 pow1  = refl
fromGF27-toGF27 pow2  = refl
fromGF27-toGF27 pow3  = refl
fromGF27-toGF27 pow4  = refl
fromGF27-toGF27 pow5  = refl
fromGF27-toGF27 pow6  = refl
fromGF27-toGF27 pow7  = refl
fromGF27-toGF27 pow8  = refl
fromGF27-toGF27 pow9  = refl
fromGF27-toGF27 pow10 = refl
fromGF27-toGF27 pow11 = refl
fromGF27-toGF27 pow12 = refl
fromGF27-toGF27 pow13 = refl
fromGF27-toGF27 pow14 = refl
fromGF27-toGF27 pow15 = refl
fromGF27-toGF27 pow16 = refl
fromGF27-toGF27 pow17 = refl
fromGF27-toGF27 pow18 = refl
fromGF27-toGF27 pow19 = refl
fromGF27-toGF27 pow20 = refl
fromGF27-toGF27 pow21 = refl
fromGF27-toGF27 pow22 = refl
fromGF27-toGF27 pow23 = refl
fromGF27-toGF27 pow24 = refl
fromGF27-toGF27 pow25 = refl

-- GF(27)* 乘法 (通过域乘法)
infixl 7 _*s_
_*s_ : GF27Star → GF27Star → GF27Star
x *s y = fromGF27 (toGF27 x *gf27 toGF27 y)

-- 幂次
infixr 8 _^s_
_^s_ : GF27Star → ℕ → GF27Star
x ^s zero    = pow0
x ^s (suc n) = x *s (x ^s n)

--------------------------------------------------------------------------------
-- 12. 本原元 α — 阶 26, 生成整个 GF(27)*
--------------------------------------------------------------------------------

gen : GF27Star
gen = pow1  -- α

-- 幂次表 (Agda 计算归约)
gen-pow-0  : gen ^s 0  ≡ pow0 ;  gen-pow-0  = refl
gen-pow-1  : gen ^s 1  ≡ pow1 ;  gen-pow-1  = refl
gen-pow-2  : gen ^s 2  ≡ pow2 ;  gen-pow-2  = refl
gen-pow-3  : gen ^s 3  ≡ pow3 ;  gen-pow-3  = refl
gen-pow-4  : gen ^s 4  ≡ pow4 ;  gen-pow-4  = refl
gen-pow-5  : gen ^s 5  ≡ pow5 ;  gen-pow-5  = refl
gen-pow-6  : gen ^s 6  ≡ pow6 ;  gen-pow-6  = refl
gen-pow-7  : gen ^s 7  ≡ pow7 ;  gen-pow-7  = refl
gen-pow-8  : gen ^s 8  ≡ pow8 ;  gen-pow-8  = refl
gen-pow-9  : gen ^s 9  ≡ pow9 ;  gen-pow-9  = refl
gen-pow-10 : gen ^s 10 ≡ pow10 ; gen-pow-10 = refl
gen-pow-11 : gen ^s 11 ≡ pow11 ; gen-pow-11 = refl
gen-pow-12 : gen ^s 12 ≡ pow12 ; gen-pow-12 = refl
gen-pow-13 : gen ^s 13 ≡ pow13 ; gen-pow-13 = refl  -- α¹³ = 2 = -1
gen-pow-14 : gen ^s 14 ≡ pow14 ; gen-pow-14 = refl
gen-pow-15 : gen ^s 15 ≡ pow15 ; gen-pow-15 = refl
gen-pow-16 : gen ^s 16 ≡ pow16 ; gen-pow-16 = refl
gen-pow-17 : gen ^s 17 ≡ pow17 ; gen-pow-17 = refl
gen-pow-18 : gen ^s 18 ≡ pow18 ; gen-pow-18 = refl
gen-pow-19 : gen ^s 19 ≡ pow19 ; gen-pow-19 = refl
gen-pow-20 : gen ^s 20 ≡ pow20 ; gen-pow-20 = refl
gen-pow-21 : gen ^s 21 ≡ pow21 ; gen-pow-21 = refl
gen-pow-22 : gen ^s 22 ≡ pow22 ; gen-pow-22 = refl
gen-pow-23 : gen ^s 23 ≡ pow23 ; gen-pow-23 = refl
gen-pow-24 : gen ^s 24 ≡ pow24 ; gen-pow-24 = refl
gen-pow-25 : gen ^s 25 ≡ pow25 ; gen-pow-25 = refl

-- α²⁶ = 1: 阶整除 26
gen-pow-26 : gen ^s 26 ≡ pow0
gen-pow-26 = refl

-- α¹³ = -1 (2 阶元)
gen-pow-13-neg1 : gen ^s 13 ≡ pow13
gen-pow-13-neg1 = refl

-- 生成元遍历所有 26 个元素
gen-generates-all : ∀ x → Σ ℕ (λ n → gen ^s n ≡ x)
gen-generates-all pow0  = 0  , refl
gen-generates-all pow1  = 1  , refl
gen-generates-all pow2  = 2  , refl
gen-generates-all pow3  = 3  , refl
gen-generates-all pow4  = 4  , refl
gen-generates-all pow5  = 5  , refl
gen-generates-all pow6  = 6  , refl
gen-generates-all pow7  = 7  , refl
gen-generates-all pow8  = 8  , refl
gen-generates-all pow9  = 9  , refl
gen-generates-all pow10 = 10 , refl
gen-generates-all pow11 = 11 , refl
gen-generates-all pow12 = 12 , refl
gen-generates-all pow13 = 13 , refl
gen-generates-all pow14 = 14 , refl
gen-generates-all pow15 = 15 , refl
gen-generates-all pow16 = 16 , refl
gen-generates-all pow17 = 17 , refl
gen-generates-all pow18 = 18 , refl
gen-generates-all pow19 = 19 , refl
gen-generates-all pow20 = 20 , refl
gen-generates-all pow21 = 21 , refl
gen-generates-all pow22 = 22 , refl
gen-generates-all pow23 = 23 , refl
gen-generates-all pow24 = 24 , refl
gen-generates-all pow25 = 25 , refl

--------------------------------------------------------------------------------
-- 13. 乘法逆元 — inv(αⁿ) = α²⁶⁻ⁿ
--------------------------------------------------------------------------------

inv : GF27Star → GF27Star
inv pow0  = pow0   -- 1⁻¹ = 1
inv pow1  = pow25
inv pow2  = pow24
inv pow3  = pow23
inv pow4  = pow22
inv pow5  = pow21
inv pow6  = pow20
inv pow7  = pow19
inv pow8  = pow18
inv pow9  = pow17
inv pow10 = pow16
inv pow11 = pow15
inv pow12 = pow14
inv pow13 = pow13  -- (-1)⁻¹ = -1
inv pow14 = pow12
inv pow15 = pow11
inv pow16 = pow10
inv pow17 = pow9
inv pow18 = pow8
inv pow19 = pow7
inv pow20 = pow6
inv pow21 = pow5
inv pow22 = pow4
inv pow23 = pow3
inv pow24 = pow2
inv pow25 = pow1

inv-correct : ∀ x → x *s inv x ≡ pow0
inv-correct pow0  = refl
inv-correct pow1  = refl
inv-correct pow2  = refl
inv-correct pow3  = refl
inv-correct pow4  = refl
inv-correct pow5  = refl
inv-correct pow6  = refl
inv-correct pow7  = refl
inv-correct pow8  = refl
inv-correct pow9  = refl
inv-correct pow10 = refl
inv-correct pow11 = refl
inv-correct pow12 = refl
inv-correct pow13 = refl
inv-correct pow14 = refl
inv-correct pow15 = refl
inv-correct pow16 = refl
inv-correct pow17 = refl
inv-correct pow18 = refl
inv-correct pow19 = refl
inv-correct pow20 = refl
inv-correct pow21 = refl
inv-correct pow22 = refl
inv-correct pow23 = refl
inv-correct pow24 = refl
inv-correct pow25 = refl

inv-involutive : ∀ x → inv (inv x) ≡ x
inv-involutive pow0  = refl
inv-involutive pow1  = refl
inv-involutive pow2  = refl
inv-involutive pow3  = refl
inv-involutive pow4  = refl
inv-involutive pow5  = refl
inv-involutive pow6  = refl
inv-involutive pow7  = refl
inv-involutive pow8  = refl
inv-involutive pow9  = refl
inv-involutive pow10 = refl
inv-involutive pow11 = refl
inv-involutive pow12 = refl
inv-involutive pow13 = refl
inv-involutive pow14 = refl
inv-involutive pow15 = refl
inv-involutive pow16 = refl
inv-involutive pow17 = refl
inv-involutive pow18 = refl
inv-involutive pow19 = refl
inv-involutive pow20 = refl
inv-involutive pow21 = refl
inv-involutive pow22 = refl
inv-involutive pow23 = refl
inv-involutive pow24 = refl
inv-involutive pow25 = refl

--------------------------------------------------------------------------------
-- 14. 阶 26 = 2 × 13 的子群结构
--------------------------------------------------------------------------------

-- 2 阶子群 {1, -1} = {α⁰, α¹³} ≅ Z/2Z
data Sub2 : Set where
  sub2-1  : Sub2  -- 1
  sub2-n1 : Sub2  -- -1 = α¹³

sub2-embed : Sub2 → GF27Star
sub2-embed sub2-1  = pow0
sub2-embed sub2-n1 = pow13

-- 13 阶子群 {α⁰, α², α⁴, ..., α²⁴} ≅ Z/13Z
-- 由 α² 生成, 包含所有二次剩余
data Sub13 : Set where
  sub13-0  : Sub13  -- α⁰
  sub13-2  : Sub13  -- α²
  sub13-4  : Sub13  -- α⁴
  sub13-6  : Sub13  -- α⁶
  sub13-8  : Sub13  -- α⁸
  sub13-10 : Sub13  -- α¹⁰
  sub13-12 : Sub13  -- α¹²
  sub13-14 : Sub13  -- α¹⁴
  sub13-16 : Sub13  -- α¹⁶
  sub13-18 : Sub13  -- α¹⁸
  sub13-20 : Sub13  -- α²⁰
  sub13-22 : Sub13  -- α²²
  sub13-24 : Sub13  -- α²⁴

sub13-embed : Sub13 → GF27Star
sub13-embed sub13-0  = pow0
sub13-embed sub13-2  = pow2
sub13-embed sub13-4  = pow4
sub13-embed sub13-6  = pow6
sub13-embed sub13-8  = pow8
sub13-embed sub13-10 = pow10
sub13-embed sub13-12 = pow12
sub13-embed sub13-14 = pow14
sub13-embed sub13-16 = pow16
sub13-embed sub13-18 = pow18
sub13-embed sub13-20 = pow20
sub13-embed sub13-22 = pow22
sub13-embed sub13-24 = pow24
