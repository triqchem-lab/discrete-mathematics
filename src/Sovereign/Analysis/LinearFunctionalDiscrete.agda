{-# OPTIONS --rewriting #-}
module Sovereign.Analysis.LinearFunctionalDiscrete where

--------------------------------------------------------------------------------
-- GF(9) 上的线性泛函和 Riesz 表示定理
--
-- 核心定理:
--   每个 GF(9)ⁿ 上的线性泛函 φ 都可以唯一表示为
--   φ(f) = ⟨f, v⟩ 其中 v_i = σ(φ(e_i))
--   σ = Galois 共轭 (Frobenius 自同构)
--
-- 与 GF(3) 版本 (Sovereign.Algebra.FunctionalDiscrete) 的区别:
--   ① 内积是 sesquilinear (共轭线性), 不是 bilinear
--   ② Riesz 向量需要 Galois 共轭: v_i = σ(φ(e_i))
--   ③ 对偶空间同构是共轭线性的
--
-- 依赖:
--   Sovereign.Algebra.GF9 — GF(9) 域运算
--   Sovereign.Algebra.FunctionalDiscrete — GF(3) 版本 (参考/后续切换)
--
-- 0 postulate — 全部构造性证明
--------------------------------------------------------------------------------

open import Data.Nat using (ℕ; zero; suc)
open import Data.Fin using (Fin)
import Data.Fin as Fin
open import Data.Vec using (Vec; []; _∷_)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; cong₂; sym; trans)
  renaming (module ≡-Reasoning to ≡-Reasoning)
open import Function using (_∘_)

open import Sovereign.Base.Trit using (Trit; T₀; T₁; T₂; _⊕_; _⊗_; negate;
  ⊕-identityˡ; ⊕-identityʳ; ⊗-zeroʳ; ⊗-zeroˡ)

open import Sovereign.Algebra.GF9 using (
  GF9; _+gf9_; _*gf9_; gf9-one; galoisConjugate; galoisConjugate²;
  +gf9-comm; +gf9-assoc; +gf9-identityˡ; +gf9-identityʳ;
  *gf9-comm; *gf9-assoc; *gf9-identityˡ; *gf9-identityʳ;
  *gf9-distribˡ-+gf9; *gf9-distribʳ-+gf9;
  negate-⊗; negate-⊗-comm; negate-⊗-negate;
  lemma-frobenius-multiplicative; embed-gf3; galoisNorm)

-- GF(3) 版本参考 (后续切换到 Sovereign.Analysis.FiniteInnerProduct)
import Sovereign.Algebra.FunctionalDiscrete as GF3FuncAnalysis

--------------------------------------------------------------------------------
-- §1. GF(9) 向量空间 — 线性结构
--------------------------------------------------------------------------------

-- GF(9) 零元
gf9-zero : GF9
gf9-zero = T₀ , T₀

-- 向量空间类型
VectorSpace : ℕ → Set
VectorSpace n = Vec GF9 n

-- 向量加法: 逐分量 GF(9) 加法
infixl 6 _+v9_
_+v9_ : ∀ {n} → VectorSpace n → VectorSpace n → VectorSpace n
[] +v9 [] = []
(x ∷ xs) +v9 (y ∷ ys) = (x +gf9 y) ∷ (xs +v9 ys)

-- 标量乘法: 逐分量 GF(9) 乘法
infixl 7 _·v9_
_·v9_ : ∀ {n} → GF9 → VectorSpace n → VectorSpace n
a ·v9 [] = []
a ·v9 (x ∷ xs) = (a *gf9 x) ∷ (a ·v9 xs)

-- 零向量
0⃗₉ : ∀ n → VectorSpace n
0⃗₉ zero = []
0⃗₉ (suc n) = gf9-zero ∷ 0⃗₉ n

-- 标准基向量: eᵢ = (0,...,0,1,0,...,0)
basis9 : ∀ n → Fin n → VectorSpace n
basis9 (suc n) Fin.zero    = gf9-one ∷ 0⃗₉ n
basis9 (suc n) (Fin.suc i) = gf9-zero ∷ basis9 n i

--------------------------------------------------------------------------------
-- §1b. 向量空间辅助引理
--------------------------------------------------------------------------------

-- GF(9) 零元左乘消去
*gf9-zeroˡ : ∀ x → gf9-zero *gf9 x ≡ gf9-zero
*gf9-zeroˡ (T₀ , T₀) = refl
*gf9-zeroˡ (T₀ , T₁) = refl
*gf9-zeroˡ (T₀ , T₂) = refl
*gf9-zeroˡ (T₁ , T₀) = refl
*gf9-zeroˡ (T₁ , T₁) = refl
*gf9-zeroˡ (T₁ , T₂) = refl
*gf9-zeroˡ (T₂ , T₀) = refl
*gf9-zeroˡ (T₂ , T₁) = refl
*gf9-zeroˡ (T₂ , T₂) = refl

-- GF(9) 零元右乘消去
*gf9-zeroʳ : ∀ x → x *gf9 gf9-zero ≡ gf9-zero
*gf9-zeroʳ (T₀ , T₀) = refl
*gf9-zeroʳ (T₀ , T₁) = refl
*gf9-zeroʳ (T₀ , T₂) = refl
*gf9-zeroʳ (T₁ , T₀) = refl
*gf9-zeroʳ (T₁ , T₁) = refl
*gf9-zeroʳ (T₁ , T₂) = refl
*gf9-zeroʳ (T₂ , T₀) = refl
*gf9-zeroʳ (T₂ , T₁) = refl
*gf9-zeroʳ (T₂ , T₂) = refl

-- 标量乘零向量得零向量
scalar9-zero : ∀ n (a : GF9) → a ·v9 0⃗₉ n ≡ 0⃗₉ n
scalar9-zero zero a = refl
scalar9-zero (suc n) a = cong₂ _∷_ (*gf9-zeroʳ a) (scalar9-zero n a)

-- 零向量是加法左单位元
+v9-identityˡ : ∀ n (xs : VectorSpace n) → 0⃗₉ n +v9 xs ≡ xs
+v9-identityˡ zero [] = refl
+v9-identityˡ (suc n) (x ∷ xs) =
  cong₂ _∷_ (+gf9-identityˡ x) (+v9-identityˡ n xs)

-- 零向量是加法右单位元
+v9-identityʳ : ∀ n (xs : VectorSpace n) → xs +v9 0⃗₉ n ≡ xs
+v9-identityʳ zero [] = refl
+v9-identityʳ (suc n) (x ∷ xs) =
  cong₂ _∷_ (+gf9-identityʳ x) (+v9-identityʳ n xs)

-- GF(9) 加法 "洗牌" 引理
+gf9-shuffle : ∀ a b c d →
  (a +gf9 b) +gf9 (c +gf9 d) ≡ (a +gf9 c) +gf9 (b +gf9 d)
+gf9-shuffle a b c d =
  begin
    (a +gf9 b) +gf9 (c +gf9 d)
  ≡⟨ +gf9-assoc a b (c +gf9 d) ⟩
    a +gf9 (b +gf9 (c +gf9 d))
  ≡⟨ cong (a +gf9_) (sym (+gf9-assoc b c d)) ⟩
    a +gf9 ((b +gf9 c) +gf9 d)
  ≡⟨ cong (a +gf9_) (cong (_+gf9 d) (+gf9-comm b c)) ⟩
    a +gf9 ((c +gf9 b) +gf9 d)
  ≡⟨ cong (a +gf9_) (+gf9-assoc c b d) ⟩
    a +gf9 (c +gf9 (b +gf9 d))
  ≡⟨ sym (+gf9-assoc a c (b +gf9 d)) ⟩
    (a +gf9 c) +gf9 (b +gf9 d)
  ∎
  where open ≡-Reasoning

--------------------------------------------------------------------------------
-- §2. Sesquilinear 内积 — GF(9)ⁿ 上的共轭双线性形式
--
-- ⟨x, y⟩ = Σᵢ xᵢ · σ(yᵢ)
-- 线性于第一变量, 共轭线性于第二变量
--------------------------------------------------------------------------------

inner9 : ∀ n → VectorSpace n → VectorSpace n → GF9
inner9 zero [] [] = gf9-zero
inner9 (suc n) (x ∷ xs) (y ∷ ys) =
  (x *gf9 galoisConjugate y) +gf9 inner9 n xs ys

-- 内积与零向量 (左)
inner9-zeroˡ : ∀ n (ys : VectorSpace n) → inner9 n (0⃗₉ n) ys ≡ gf9-zero
inner9-zeroˡ zero [] = refl
inner9-zeroˡ (suc n) (y ∷ ys) =
  trans (cong₂ _+gf9_ (*gf9-zeroˡ (galoisConjugate y)) refl)
        (trans (+gf9-identityˡ (inner9 n (0⃗₉ n) ys))
               (inner9-zeroˡ n ys))

-- 内积左加性: ⟨x+x', y⟩ = ⟨x,y⟩ + ⟨x',y⟩
inner9-additiveˡ : ∀ n (xs xs' ys : VectorSpace n) →
  inner9 n (xs +v9 xs') ys ≡ inner9 n xs ys +gf9 inner9 n xs' ys
inner9-additiveˡ zero [] [] [] = refl
inner9-additiveˡ (suc n) (x ∷ xs) (x' ∷ xs') (y ∷ ys) =
  trans (cong₂ _+gf9_
    (*gf9-distribʳ-+gf9 x x' (galoisConjugate y))
    (inner9-additiveˡ n xs xs' ys))
    (+gf9-shuffle (x *gf9 galoisConjugate y) (x' *gf9 galoisConjugate y)
                  (inner9 n xs ys) (inner9 n xs' ys))

-- 内积左齐性: ⟨a·x, y⟩ = a·⟨x,y⟩
inner9-homogeneousˡ : ∀ n (a : GF9) (xs ys : VectorSpace n) →
  inner9 n (a ·v9 xs) ys ≡ a *gf9 inner9 n xs ys
inner9-homogeneousˡ zero a [] [] = sym (*gf9-zeroʳ a)
inner9-homogeneousˡ (suc n) a (x ∷ xs) (y ∷ ys) =
  trans (cong₂ _+gf9_
    (*gf9-assoc a x (galoisConjugate y))
    (inner9-homogeneousˡ n a xs ys))
    (sym (*gf9-distribˡ-+gf9 a (x *gf9 galoisConjugate y) (inner9 n xs ys)))

--------------------------------------------------------------------------------
-- §3. 线性泛函 — GF(9)ⁿ → GF(9) 的线性映射
--------------------------------------------------------------------------------

record LinearFunctional (n : ℕ) : Set where
  field
    apply       : VectorSpace n → GF9
    additive    : ∀ x y → apply (x +v9 y) ≡ apply x +gf9 apply y
    homogeneous : ∀ a x → apply (a ·v9 x) ≡ a *gf9 apply x

open LinearFunctional public using (apply; additive; homogeneous)

-- 组合线性性: φ(a·x + y) = a·φ(x) + φ(y)
linear-combined : ∀ n (φ : LinearFunctional n) a x y →
  apply φ (a ·v9 x +v9 y) ≡ (a *gf9 apply φ x) +gf9 apply φ y
linear-combined n φ a x y =
  trans (additive φ (a ·v9 x) y)
        (cong (_+gf9 apply φ y) (homogeneous φ a x))

-- 线性泛函将零向量映为零
linear-preserves-zero9 : ∀ n (φ : LinearFunctional n) →
  apply φ (0⃗₉ n) ≡ gf9-zero
linear-preserves-zero9 n φ =
  trans (sym (cong (apply φ) (scalar9-zero n gf9-zero)))
        (trans (homogeneous φ gf9-zero (0⃗₉ n))
               (*gf9-zeroˡ (apply φ (0⃗₉ n))))

--------------------------------------------------------------------------------
-- §4. 零泛函、泛函加法、标量乘
--------------------------------------------------------------------------------

-- 零泛函
zeroFunctional : ∀ n → LinearFunctional n
zeroFunctional n = record
  { apply       = λ _ → gf9-zero
  ; additive    = λ _ _ → refl
  ; homogeneous = λ a _ → sym (*gf9-zeroʳ a)
  }

-- 泛函加法
functional-add : ∀ n → LinearFunctional n → LinearFunctional n → LinearFunctional n
functional-add n φ ψ = record
  { apply       = λ x → apply φ x +gf9 apply ψ x
  ; additive    = λ x y →
      trans (cong₂ _+gf9_ (additive φ x y) (additive ψ x y))
            (+gf9-shuffle (apply φ x) (apply φ y) (apply ψ x) (apply ψ y))
  ; homogeneous = λ a x →
      trans (cong₂ _+gf9_ (homogeneous φ a x) (homogeneous ψ a x))
            (sym (*gf9-distribˡ-+gf9 a (apply φ x) (apply ψ x)))
  }

-- 泛函标量乘
functional-scale : ∀ n → GF9 → LinearFunctional n → LinearFunctional n
functional-scale n a φ = record
  { apply       = λ x → a *gf9 apply φ x
  ; additive    = λ x y →
      trans (cong (a *gf9_) (additive φ x y))
            (*gf9-distribˡ-+gf9 a (apply φ x) (apply φ y))
  ; homogeneous = λ b x →
      trans (cong (a *gf9_) (homogeneous φ b x))
            (trans (sym (*gf9-assoc a b (apply φ x)))
                   (trans (cong (_*gf9 apply φ x) (*gf9-comm a b))
                          (*gf9-assoc b a (apply φ x))))
  }

--------------------------------------------------------------------------------
-- §5. represent 和 rieszVector
--------------------------------------------------------------------------------

-- represent: 向量 → 泛函 (φ_v(f) = ⟨f, v⟩)
represent : ∀ n → VectorSpace n → LinearFunctional n
represent n v = record
  { apply       = λ f → inner9 n f v
  ; additive    = λ x y → inner9-additiveˡ n x y v
  ; homogeneous = λ a x → inner9-homogeneousˡ n a x v
  }

-- 尾部限制: 将 φ : GF(9)^(suc n) → GF(9) 限制到尾部子空间
tailFunctional : ∀ n → LinearFunctional (suc n) → LinearFunctional n
tailFunctional n φ = record
  { apply       = λ xs → apply φ (gf9-zero ∷ xs)
  ; additive    = λ xs ys → additive φ (gf9-zero ∷ xs) (gf9-zero ∷ ys)
  ; homogeneous = λ a xs →
      trans (cong (apply φ) (sym (cong₂ _∷_ (*gf9-zeroʳ a) refl)))
            (homogeneous φ a (gf9-zero ∷ xs))
  }

-- rieszVector: 泛函 → 向量 (v_i = σ(φ(e_i)))
rieszVector : ∀ n → LinearFunctional n → VectorSpace n
rieszVector zero φ = []
rieszVector (suc n) φ =
  galoisConjugate (apply φ (gf9-one ∷ 0⃗₉ n)) ∷
  rieszVector n (tailFunctional n φ)

--------------------------------------------------------------------------------
-- §6. rieszCorrect — Riesz 表示定理
--
-- ∀ φ f → φ(f) ≡ ⟨f, rieszVector φ⟩
--------------------------------------------------------------------------------

-- 向量分解: x₀∷xs ≡ (x₀·e₀) + (0∷xs)
vec9-decompose : ∀ n (x₀ : GF9) (xs : VectorSpace n) →
  x₀ ∷ xs ≡ (x₀ ·v9 (gf9-one ∷ 0⃗₉ n)) +v9 (gf9-zero ∷ xs)
vec9-decompose n x₀ xs = cong₂ _∷_ first-comp tail-comp
  where
    first-comp : x₀ ≡ (x₀ *gf9 gf9-one) +gf9 gf9-zero
    first-comp = sym (trans (cong (_+gf9 gf9-zero) (*gf9-identityʳ x₀))
                            (+gf9-identityʳ x₀))
    tail-comp : xs ≡ (x₀ ·v9 0⃗₉ n) +v9 xs
    tail-comp = sym (trans (cong (_+v9 xs) (scalar9-zero n x₀))
                           (+v9-identityˡ n xs))

-- Riesz 表示定理: φ(f) ≡ ⟨f, rieszVector φ⟩
rieszCorrect : ∀ n (φ : LinearFunctional n) (f : VectorSpace n) →
  apply φ f ≡ inner9 n f (rieszVector n φ)
rieszCorrect zero φ [] =
  trans (sym (cong (apply φ) (scalar9-zero 0 gf9-zero)))
        (trans (homogeneous φ gf9-zero [])
               (*gf9-zeroˡ (apply φ [])))
rieszCorrect (suc n) φ (f₀ ∷ fs) =
  begin
    apply φ (f₀ ∷ fs)
  ≡⟨ cong (apply φ) (vec9-decompose n f₀ fs) ⟩
    apply φ ((f₀ ·v9 (gf9-one ∷ 0⃗₉ n)) +v9 (gf9-zero ∷ fs))
  ≡⟨ linear-combined (suc n) φ f₀ (gf9-one ∷ 0⃗₉ n) (gf9-zero ∷ fs) ⟩
    (f₀ *gf9 apply φ (gf9-one ∷ 0⃗₉ n)) +gf9 apply φ (gf9-zero ∷ fs)
  ≡⟨ cong ((f₀ *gf9 apply φ (gf9-one ∷ 0⃗₉ n)) +gf9_)
       (rieszCorrect n (tailFunctional n φ) fs) ⟩
    (f₀ *gf9 apply φ (gf9-one ∷ 0⃗₉ n)) +gf9
      inner9 n fs (rieszVector n (tailFunctional n φ))
  ≡⟨ cong (_+gf9 inner9 n fs (rieszVector n (tailFunctional n φ)))
       (cong (f₀ *gf9_)
         (sym (galoisConjugate² (apply φ (gf9-one ∷ 0⃗₉ n))))) ⟩
    (f₀ *gf9 galoisConjugate (galoisConjugate (apply φ (gf9-one ∷ 0⃗₉ n)))) +gf9
      inner9 n fs (rieszVector n (tailFunctional n φ))
  ≡⟨ refl ⟩
    inner9 (suc n) (f₀ ∷ fs) (rieszVector (suc n) φ)
  ∎
  where open ≡-Reasoning

-- Riesz 表示的存在性表述
riesz-exists9 : ∀ n (φ : LinearFunctional n) →
  Σ (VectorSpace n) (λ v → ∀ f → apply φ f ≡ inner9 n f v)
riesz-exists9 n φ = rieszVector n φ , rieszCorrect n φ

--------------------------------------------------------------------------------
-- §7. 对偶空间同构 — DualSpace n ≃ VectorSpace n
--------------------------------------------------------------------------------

-- 对偶空间
DualSpace : ℕ → Set
DualSpace n = LinearFunctional n

-- Riesz 同构映射: VectorSpace n → DualSpace n
riesz-map : ∀ n → VectorSpace n → DualSpace n
riesz-map n = represent n

-- Riesz 逆映射: DualSpace n → VectorSpace n
riesz-inverse : ∀ n → DualSpace n → VectorSpace n
riesz-inverse n = rieszVector n

-- 内积在基向量处的值: ⟨e₀, v⟩ = σ(v₀)
inner9-basis₀ : ∀ n (v₀ : GF9) (vs : VectorSpace n) →
  inner9 (suc n) (gf9-one ∷ 0⃗₉ n) (v₀ ∷ vs) ≡ galoisConjugate v₀
inner9-basis₀ n v₀ vs =
  trans (cong₂ _+gf9_ (*gf9-identityˡ (galoisConjugate v₀))
                      (inner9-zeroˡ n vs))
        (+gf9-identityʳ (galoisConjugate v₀))

-- 零头内积: ⟨0∷xs, v₀∷vs⟩ = ⟨xs, vs⟩
inner9-zero-head : ∀ n (xs : VectorSpace n) (v₀ : GF9) (vs : VectorSpace n) →
  inner9 (suc n) (gf9-zero ∷ xs) (v₀ ∷ vs) ≡ inner9 n xs vs
inner9-zero-head n xs v₀ vs =
  trans (cong₂ _+gf9_ (*gf9-zeroˡ (galoisConjugate v₀)) refl)
        (+gf9-identityˡ (inner9 n xs vs))

-- rieszVector 尊重泛函外延等价
lemma-riesz-ext : ∀ n (f g : LinearFunctional n) →
  (∀ x → apply f x ≡ apply g x) → rieszVector n f ≡ rieszVector n g
lemma-riesz-ext zero f g hyp = refl
lemma-riesz-ext (suc n) f g hyp =
  cong₂ _∷_
    (cong galoisConjugate (hyp (gf9-one ∷ 0⃗₉ n)))
    (lemma-riesz-ext n (tailFunctional n f) (tailFunctional n g) tail-hyp)
  where
    tail-hyp : ∀ x → apply (tailFunctional n f) x ≡ apply (tailFunctional n g) x
    tail-hyp x = hyp (gf9-zero ∷ x)

-- Riesz 同构的逆性质: rieszVector ∘ represent = id
riesz-represent-inv : ∀ n (v : VectorSpace n) →
  rieszVector n (represent n v) ≡ v
riesz-represent-inv zero [] = refl
riesz-represent-inv (suc n) (v₀ ∷ vs) =
  cong₂ _∷_ first-comp tail-comp
  where
    first-comp : galoisConjugate
      (apply (represent (suc n) (v₀ ∷ vs)) (gf9-one ∷ 0⃗₉ n)) ≡ v₀
    first-comp = trans (cong galoisConjugate (inner9-basis₀ n v₀ vs))
                       (galoisConjugate² v₀)

    tail-comp : rieszVector n (tailFunctional n (represent (suc n) (v₀ ∷ vs))) ≡ vs
    tail-comp = trans
      (lemma-riesz-ext n
        (tailFunctional n (represent (suc n) (v₀ ∷ vs)))
        (represent n vs)
        (λ xs → inner9-zero-head n xs v₀ vs))
      (riesz-represent-inv n vs)

-- Riesz 同构的正性质: represent ∘ rieszVector = id (即 rieszCorrect)
represent-riesz-correct : ∀ n (φ : DualSpace n) (f : VectorSpace n) →
  apply (represent n (rieszVector n φ)) f ≡ apply φ f
represent-riesz-correct n φ f = sym (rieszCorrect n φ f)

-- 对偶空间同构的完整表述
dual-space-iso : ∀ n →
  Σ (VectorSpace n → DualSpace n)
    (λ to → Σ (DualSpace n → VectorSpace n)
      (λ from → (∀ v → from (to v) ≡ v)))
dual-space-iso n = riesz-map n , riesz-inverse n , riesz-represent-inv n

--------------------------------------------------------------------------------
-- 总结: GF(9) 离散泛函分析核心定理
--
-- 1. inner9: GF(9)ⁿ 上的 sesquilinear 内积
-- 2. inner9-additiveˡ / inner9-homogeneousˡ: 左线性性
-- 3. LinearFunctional: 线性泛函 record
-- 4. represent: 向量 → 泛函 (φ_v(f) = ⟨f,v⟩)
-- 5. rieszVector: 泛函 → 向量 (v_i = σ(φ(e_i)))
-- 6. rieszCorrect: φ(f) ≡ ⟨f, rieszVector φ⟩ (Riesz 表示定理)
-- 7. dual-space-iso: DualSpace n ≃ VectorSpace n
--
-- 与 GF(3) 版本的关键区别:
--   GF(3): 内积 bilinear, Riesz 向量 v_i = φ(e_i)
--   GF(9): 内积 sesquilinear, Riesz 向量 v_i = σ(φ(e_i))
--   Galois 共轭 σ 是 GF(9)/GF(3) 的非平凡自同构
--------------------------------------------------------------------------------
