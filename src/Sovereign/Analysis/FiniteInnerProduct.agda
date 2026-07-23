{-# OPTIONS --rewriting #-}
module Sovereign.Analysis.FiniteInnerProduct where

--------------------------------------------------------------------------------
-- GF(9) 有限维内积空间
--
-- 在 GF(9) = GF(3)[x]/(x²+1) 上定义 n 维 Hermitian 内积空间。
-- Galois 共轭 σ: a+bα ↦ a-bα 提供自然的共轭线性结构。
--
-- 与 GF(3) 版本 (Sovereign.Algebra.FunctionalDiscrete) 的关键区别:
--   ① GF(9) 有非平凡 Galois 共轭 → Hermitian (非对称) 内积
--   ② 范数 N(x) = x·σ(x) = a²+b² 在 GF(9) 上正定 (N(x)=0 ⟺ x=0)
--   ③ GF(3) 内积退化 (各向同性), GF(9) 单分量正定
--
-- 向量表示: VectorSpace n = Fin n → GF9 (函数表示, 非 Vec)
--
-- 0 postulate — 全部构造性证明
--------------------------------------------------------------------------------

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin using (Fin; zero; suc; toℕ)
open import Relation.Nullary using (¬_)
import Data.Fin as Fin
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Function using (_∘_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; cong₂; sym; trans)

open import Sovereign.Base.Trit using (
  Trit; T₀; T₁; T₂; _⊕_; _⊗_; negate;
  ⊕-identityˡ; ⊕-identityʳ; ⊕-comm; ⊕-assoc;
  ⊗-identityˡ; ⊗-identityʳ; ⊗-comm; ⊗-assoc;
  ⊗-distribˡ-⊕; ⊗-distribʳ-⊕; ⊗-zeroˡ; ⊗-zeroʳ;
  negate²; ⊕-inverse)

open import Sovereign.Algebra.GF9 using (
  GF9; GF3; _+gf9_; _*gf9_; gf9-one;
  galoisConjugate; galoisConjugate²;
  galoisNorm; embed-gf3;
  +gf9-comm; +gf9-assoc; +gf9-identityˡ; +gf9-identityʳ;
  *gf9-comm; *gf9-assoc; *gf9-identityˡ; *gf9-identityʳ;
  *gf9-distribˡ-+gf9; *gf9-distribʳ-+gf9;
  lemma-frobenius-multiplicative;
  negate-⊕; negate-⊗; negate-⊗-negate; negate-⊗-comm;
  swap-middle; +gf9-inverse)

--------------------------------------------------------------------------------
-- §1. 向量空间 — GF(9)ⁿ 的函数表示
--------------------------------------------------------------------------------

-- n 维 GF(9) 向量空间: Fin n → GF9
VectorSpace : ℕ → Set
VectorSpace n = Fin n → GF9

-- GF(9) 零元素
gf9-zero : GF9
gf9-zero = T₀ , T₀

-- 零向量
zeroVec : ∀ n → VectorSpace n
zeroVec n _ = gf9-zero

-- 向量加法 (逐点 GF9 加法)
infixl 6 _+V_
_+V_ : ∀ {n} → VectorSpace n → VectorSpace n → VectorSpace n
(f +V g) i = f i +gf9 g i

-- 标量乘法 (逐点 GF9 乘法)
infixl 7 _·V_
_·V_ : ∀ {n} → GF9 → VectorSpace n → VectorSpace n
(a ·V f) i = a *gf9 f i

--------------------------------------------------------------------------------
-- §2. GF9 代数辅助引理
--------------------------------------------------------------------------------

-- 零乘消去 (左): 0·x = 0
*gf9-zeroˡ : ∀ x → gf9-zero *gf9 x ≡ gf9-zero
*gf9-zeroˡ (c , d) = cong₂ _,_ real imag
  where
    real : (T₀ ⊗ c) ⊕ negate (T₀ ⊗ d) ≡ T₀
    real = cong₂ _⊕_ (⊗-zeroˡ c) (cong negate (⊗-zeroˡ d))

    imag : (T₀ ⊗ d) ⊕ (T₀ ⊗ c) ≡ T₀
    imag = cong₂ _⊕_ (⊗-zeroˡ d) (⊗-zeroˡ c)

-- 零乘消去 (右): x·0 = 0
*gf9-zeroʳ : ∀ x → x *gf9 gf9-zero ≡ gf9-zero
*gf9-zeroʳ (a , b) = cong₂ _,_ real imag
  where
    real : (a ⊗ T₀) ⊕ negate (b ⊗ T₀) ≡ T₀
    real = cong₂ _⊕_ (⊗-zeroʳ a) (cong negate (⊗-zeroʳ b))

    imag : (a ⊗ T₀) ⊕ (b ⊗ T₀) ≡ T₀
    imag = cong₂ _⊕_ (⊗-zeroʳ a) (⊗-zeroʳ b)

-- GF9 加法四项重排: (w+x)+(y+z) ≡ (w+y)+(x+z)
+gf9-swap-middle : ∀ w x y z →
  (w +gf9 x) +gf9 (y +gf9 z) ≡ (w +gf9 y) +gf9 (x +gf9 z)
+gf9-swap-middle (a , b) (c , d) (e , f) (g , h) =
  cong₂ _,_ (swap-middle a c e g) (swap-middle b d f h)

-- negate b + b = 0 (加法逆元交换形式)
negate-⊕-self : ∀ b → negate b ⊕ b ≡ T₀
negate-⊕-self b = trans (⊕-comm (negate b) b) (⊕-inverse b)

-- negate(b·negate(b)) = b·b (GF(3) 特征 3 性质)
negate-⊗-negate-self : ∀ b → negate (b ⊗ negate b) ≡ b ⊗ b
negate-⊗-negate-self b = trans (negate-⊗ b (negate b)) (negate-⊗-negate b b)

--------------------------------------------------------------------------------
-- §3. 有限和 — Fin n → GF9 的求和
--------------------------------------------------------------------------------

sumGF9 : ∀ n → (Fin n → GF9) → GF9
sumGF9 zero f = gf9-zero
sumGF9 (suc n) f = f Fin.zero +gf9 sumGF9 n (f ∘ Fin.suc)

-- 求和保持逐点相等
sumGF9-cong : ∀ n {f g : Fin n → GF9} →
  (∀ i → f i ≡ g i) → sumGF9 n f ≡ sumGF9 n g
sumGF9-cong zero h = refl
sumGF9-cong (suc n) h =
  cong₂ _+gf9_ (h Fin.zero) (sumGF9-cong n (λ i → h (Fin.suc i)))

-- 常值零函数求和为零
sumGF9-const-zero : ∀ n → sumGF9 n (λ _ → gf9-zero) ≡ gf9-zero
sumGF9-const-zero zero = refl
sumGF9-const-zero (suc n) =
  trans (cong (gf9-zero +gf9_) (sumGF9-const-zero n))
        (+gf9-identityˡ gf9-zero)

-- 求和保持加法: Σ(f+g) = Σf + Σg
sumGF9-additive : ∀ n (f g : Fin n → GF9) →
  sumGF9 n (λ i → f i +gf9 g i) ≡ sumGF9 n f +gf9 sumGF9 n g
sumGF9-additive zero f g = refl
sumGF9-additive (suc n) f g =
  trans (cong ((f Fin.zero +gf9 g Fin.zero) +gf9_)
              (sumGF9-additive n (f ∘ Fin.suc) (g ∘ Fin.suc)))
        (+gf9-swap-middle (f Fin.zero) (g Fin.zero)
                          (sumGF9 n (f ∘ Fin.suc)) (sumGF9 n (g ∘ Fin.suc)))

-- 求和与标量乘法交换: Σ(a·f) = a·Σf
sumGF9-scalar : ∀ n (a : GF9) (f : Fin n → GF9) →
  sumGF9 n (λ i → a *gf9 f i) ≡ a *gf9 sumGF9 n f
sumGF9-scalar zero a f = sym (*gf9-zeroʳ a)
sumGF9-scalar (suc n) a f =
  trans (cong ((a *gf9 f Fin.zero) +gf9_)
              (sumGF9-scalar n a (f ∘ Fin.suc)))
        (sym (*gf9-distribˡ-+gf9 a (f Fin.zero) (sumGF9 n (f ∘ Fin.suc))))

--------------------------------------------------------------------------------
-- §4. 共轭运算性质
--------------------------------------------------------------------------------

-- 共轭保持加法: σ(x+y) = σ(x)+σ(y)
conj-additive : ∀ x y →
  galoisConjugate (x +gf9 y) ≡ galoisConjugate x +gf9 galoisConjugate y
conj-additive (a , b) (c , d) = cong₂ _,_ refl (negate-⊕ b d)

-- 共轭保持零: σ(0) = 0
conj-zero : galoisConjugate gf9-zero ≡ gf9-zero
conj-zero = refl

-- 共轭保持求和: σ(Σf) = Σ(σ∘f)
conj-sum : ∀ n f →
  galoisConjugate (sumGF9 n f) ≡ sumGF9 n (galoisConjugate ∘ f)
conj-sum zero f = refl
conj-sum (suc n) f =
  trans (conj-additive (f Fin.zero) (sumGF9 n (f ∘ Fin.suc)))
        (cong (galoisConjugate (f Fin.zero) +gf9_)
              (conj-sum n (f ∘ Fin.suc)))

--------------------------------------------------------------------------------
-- §5. Hermitian 内积
--------------------------------------------------------------------------------

-- Hermitian 内积: ⟨f,g⟩ = Σᵢ f(i) · σ(g(i))
hermitianIP : ∀ n → VectorSpace n → VectorSpace n → GF9
hermitianIP n f g = sumGF9 n (λ i → f i *gf9 galoisConjugate (g i))

--------------------------------------------------------------------------------
-- §5b. 内积性质 — 共轭对称性
--------------------------------------------------------------------------------

-- ⟨f,g⟩ = σ(⟨g,f⟩)
-- 证明链: ⟨f,g⟩ = Σ f·σ(g) = Σ σ(g·σ(f)) = σ(Σ g·σ(f)) = σ(⟨g,f⟩)
hermitian-conj-sym : ∀ n f g →
  hermitianIP n f g ≡ galoisConjugate (hermitianIP n g f)
hermitian-conj-sym n f g =
  trans (sym (sumGF9-cong n (λ i →
          trans (lemma-frobenius-multiplicative (g i) (galoisConjugate (f i)))
            (trans (cong (galoisConjugate (g i) *gf9_)
                         (galoisConjugate² (f i)))
                   (*gf9-comm (galoisConjugate (g i)) (f i))))))
        (sym (conj-sum n (λ i → g i *gf9 galoisConjugate (f i))))

--------------------------------------------------------------------------------
-- §5c. 内积性质 — 左线性
--------------------------------------------------------------------------------

-- ⟨a·f + g, h⟩ = a·⟨f,h⟩ + ⟨g,h⟩
hermitian-linearˡ : ∀ n (a : GF9) (f g h : VectorSpace n) →
  hermitianIP n ((a ·V f) +V g) h ≡
  (a *gf9 hermitianIP n f h) +gf9 hermitianIP n g h
hermitian-linearˡ n a f g h =
  trans (sumGF9-cong n (λ i →
          *gf9-distribʳ-+gf9 (a *gf9 (f i)) (g i) (galoisConjugate (h i))))
    (trans (sumGF9-additive n
             (λ i → (a *gf9 (f i)) *gf9 galoisConjugate (h i))
             (λ i → (g i) *gf9 galoisConjugate (h i)))
      (cong₂ _+gf9_
        (trans (sumGF9-cong n
                (λ i → *gf9-assoc a (f i) (galoisConjugate (h i))))
               (sumGF9-scalar n a
                (λ i → (f i) *gf9 galoisConjugate (h i))))
        refl))

--------------------------------------------------------------------------------
-- §6. 范数平方与正定性
--------------------------------------------------------------------------------

-- 范数平方: ‖f‖² = ⟨f,f⟩
normSq : ∀ n → VectorSpace n → GF9
normSq n f = hermitianIP n f f

-- x·σ(x) = embed(N(x)), 其中 N(a+bα) = a²+b² ∈ GF(3)
gf9-norm-real : ∀ x → x *gf9 galoisConjugate x ≡ embed-gf3 (galoisNorm x)
gf9-norm-real (a , b) = cong₂ _,_ real-eq imag-eq
  where
    real-eq : (a ⊗ a) ⊕ negate (b ⊗ negate b) ≡ (a ⊗ a) ⊕ (b ⊗ b)
    real-eq = cong ((a ⊗ a) ⊕_) (negate-⊗-negate-self b)

    imag-eq : (a ⊗ negate b) ⊕ (b ⊗ a) ≡ T₀
    imag-eq = trans (cong ((a ⊗ negate b) ⊕_) (⊗-comm b a))
                (trans (sym (⊗-distribˡ-⊕ a (negate b) b))
                  (trans (cong (a ⊗_) (negate-⊕-self b))
                         (⊗-zeroʳ a)))

-- Galois 范数正定: N(x)=0 ⟹ x=0 (9 case 穷举)
galoisNorm-zero : ∀ x → galoisNorm x ≡ T₀ → x ≡ gf9-zero
galoisNorm-zero (T₀ , T₀) _ = refl
galoisNorm-zero (T₀ , T₁) ()  -- N = T₀⊕T₁ = T₁
galoisNorm-zero (T₀ , T₂) ()  -- N = T₀⊕T₁ = T₁
galoisNorm-zero (T₁ , T₀) ()  -- N = T₁⊕T₀ = T₁
galoisNorm-zero (T₁ , T₁) ()  -- N = T₁⊕T₁ = T₂
galoisNorm-zero (T₁ , T₂) ()  -- N = T₁⊕T₁ = T₂
galoisNorm-zero (T₂ , T₀) ()  -- N = T₁⊕T₀ = T₁
galoisNorm-zero (T₂ , T₁) ()  -- N = T₁⊕T₁ = T₂
galoisNorm-zero (T₂ , T₂) ()  -- N = T₁⊕T₁ = T₂

-- 零向量的范数平方为零
normSq-of-zero : ∀ n → normSq n (zeroVec n) ≡ gf9-zero
normSq-of-zero n = sumGF9-const-zero n

-- 一维正定性: ‖f‖²=0 ⟹ f=0 (在 GF(9) 上成立)
-- 注意: 对 n≥3, GF(3) 加法回绕使 Σ N(fᵢ)=0 可能有非零解
-- (如三个 N=1 的分量: 1⊕1⊕1=0), 故全维正定性不成立
normSq-1-positive : ∀ (f : VectorSpace 1) →
  normSq 1 f ≡ gf9-zero → f Fin.zero ≡ gf9-zero
normSq-1-positive f hyp = galoisNorm-zero (f Fin.zero) norm-is-zero
  where
    -- normSq 1 f = f(0)·σ(f(0)) +gf9 gf9-zero
    -- 由 +gf9-identityʳ 化简
    step1 : f Fin.zero *gf9 galoisConjugate (f Fin.zero) ≡ gf9-zero
    step1 = trans (sym (+gf9-identityʳ
                   (f Fin.zero *gf9 galoisConjugate (f Fin.zero))))
                  hyp
    -- 由 gf9-norm-real 转为 Galois 范数
    step2 : embed-gf3 (galoisNorm (f Fin.zero)) ≡ gf9-zero
    step2 = trans (sym (gf9-norm-real (f Fin.zero))) step1
    -- 提取 proj₁ 得 N(f(0)) ≡ T₀
    norm-is-zero : galoisNorm (f Fin.zero) ≡ T₀
    norm-is-zero = cong proj₁ step2

--------------------------------------------------------------------------------
-- §7. 正交性
--------------------------------------------------------------------------------

-- 正交性定义: ⟨f,g⟩ = 0
Orthogonal : ∀ n → VectorSpace n → VectorSpace n → Set
Orthogonal n f g = hermitianIP n f g ≡ gf9-zero

-- 正交性对称: ⟨f,g⟩=0 ⟹ ⟨g,f⟩=0
-- 证明: ⟨g,f⟩ = σ²(⟨g,f⟩) = σ(⟨f,g⟩) = σ(0) = 0
orth-sym : ∀ n f g → Orthogonal n f g → Orthogonal n g f
orth-sym n f g p =
  trans (sym (galoisConjugate² (hermitianIP n g f)))
    (trans (cong galoisConjugate
             (trans (sym (hermitian-conj-sym n f g)) p))
           conj-zero)

-- 零向量与所有向量正交 (左)
zero-orthogonalˡ : ∀ n (g : VectorSpace n) → Orthogonal n (zeroVec n) g
zero-orthogonalˡ n g =
  trans (sumGF9-cong n (λ i → *gf9-zeroˡ (galoisConjugate (g i))))
        (sumGF9-const-zero n)

-- 零向量与所有向量正交 (右)
zero-orthogonalʳ : ∀ n (f : VectorSpace n) → Orthogonal n f (zeroVec n)
zero-orthogonalʳ n f =
  trans (sumGF9-cong n (λ i →
          trans (cong (f i *gf9_) conj-zero)
                (*gf9-zeroʳ (f i))))
        (sumGF9-const-zero n)

--------------------------------------------------------------------------------
-- §8. 标准基向量
--------------------------------------------------------------------------------

-- 标准基: eᵢ(j) = δᵢⱼ (Kronecker delta)
basisVec : ∀ n → Fin n → VectorSpace n
basisVec (suc n) Fin.zero    Fin.zero    = gf9-one
basisVec (suc n) Fin.zero    (Fin.suc j) = gf9-zero
basisVec (suc n) (Fin.suc i) Fin.zero    = gf9-zero
basisVec (suc n) (Fin.suc i) (Fin.suc j) = basisVec n i j

-- 基向量对角元为 1
basisVec-diag : ∀ n (i : Fin n) → basisVec n i i ≡ gf9-one
basisVec-diag (suc n) Fin.zero    = refl
basisVec-diag (suc n) (Fin.suc i) = basisVec-diag n i

-- 非零指标基向量在零分量处为 0
basisVec-suc-at-zero : ∀ n (i : Fin n) →
  basisVec (suc n) (Fin.suc i) Fin.zero ≡ gf9-zero
basisVec-suc-at-zero n i = refl

--------------------------------------------------------------------------------
-- §8b. 基向量范数与正交性 (sumGF9 单点支撑引理)
--------------------------------------------------------------------------------
-- [分类: 已证引理] [证明策略: 对 n 归纳 + Fin 分情况]
-- 消除 HolographicSpace.agda 的 3 个 postulate

-- 辅助: σ(1) = 1, 1·1 = 1, σ(0) = 0, 0·0 = 0 (全部 refl)
private
  σ-one : galoisConjugate gf9-one ≡ gf9-one
  σ-one = refl

  one-sq : gf9-one *gf9 gf9-one ≡ gf9-one
  one-sq = refl

  σ-zero : galoisConjugate gf9-zero ≡ gf9-zero
  σ-zero = refl

  zero-sq : gf9-zero *gf9 gf9-zero ≡ gf9-zero
  zero-sq = refl

  -- 零乘以任何共轭 = 零
  zero-times-conj : ∀ x → gf9-zero *gf9 galoisConjugate x ≡ gf9-zero
  zero-times-conj x = *gf9-zeroˡ (galoisConjugate x)

  -- 任何乘以零的共轭 = 零
  times-conj-zero : ∀ x → x *gf9 galoisConjugate gf9-zero ≡ gf9-zero
  times-conj-zero x = *gf9-zeroʳ x

-- 核心引理: 基向量的范数平方 = 1
-- normSq n (basisVec n i) = Σⱼ |basisVec n i j|² = |1|² + 0 + ... + 0 = 1
normSq-basisVec : ∀ n (i : Fin n) → normSq n (basisVec n i) ≡ gf9-one
normSq-basisVec (suc n) Fin.zero =
  -- sumGF9 (suc n) (λ j → basisVec (suc n) F0 j · σ(basisVec (suc n) F0 j))
  -- = (1·σ(1)) + Σⱼ(0·σ(0)) = 1 + 0 = 1
  trans (cong₂ _+gf9_ one-sq
          (sumGF9-cong n (λ j → zero-times-conj gf9-zero)))
    (trans (cong (gf9-one +gf9_) (sumGF9-const-zero n))
           (+gf9-identityʳ gf9-one))
normSq-basisVec (suc n) (Fin.suc i) =
  -- sumGF9 (suc n) (λ j → basisVec (suc n) (Fs i) j · σ(...))
  -- = (0·σ(0)) + Σⱼ(basisVec n i j · σ(basisVec n i j))
  -- = 0 + normSq n (basisVec n i) = 0 + 1 = 1
  trans (cong₂ _+gf9_ zero-sq
          (sumGF9-cong n (λ j → refl)))
    (trans (cong (gf9-zero +gf9_) (normSq-basisVec n i))
           (+gf9-identityˡ gf9-one))

-- 核心引理: 不同基向量正交
-- hermitianIP n (basisVec n i) (basisVec n j) = 0 当 i ≠ j
basis-orthogonal : ∀ n (i j : Fin n) → ¬ (toℕ i ≡ toℕ j) →
  hermitianIP n (basisVec n i) (basisVec n j) ≡ gf9-zero
basis-orthogonal (suc n) Fin.zero Fin.zero neq =
  ⊥-elim (neq refl)
basis-orthogonal (suc n) Fin.zero (Fin.suc j) neq =
  -- (1·σ(0)) + Σₖ(0·σ(basisVec n j k)) = 0 + 0 = 0
  trans (cong₂ _+gf9_ (times-conj-zero gf9-one)
          (sumGF9-cong n (λ k → zero-times-conj (basisVec n j k))))
    (trans (cong (gf9-zero +gf9_) (sumGF9-const-zero n))
           (+gf9-identityˡ gf9-zero))
basis-orthogonal (suc n) (Fin.suc i) Fin.zero neq =
  -- (0·σ(1)) + Σₖ(basisVec n i k·σ(0)) = 0 + 0 = 0
  trans (cong₂ _+gf9_ zero-sq
          (sumGF9-cong n (λ k → times-conj-zero (basisVec n i k))))
    (trans (cong (gf9-zero +gf9_) (sumGF9-const-zero n))
           (+gf9-identityˡ gf9-zero))
basis-orthogonal (suc n) (Fin.suc i) (Fin.suc j) neq =
  -- (0·σ(0)) + Σₖ(basisVec n i k·σ(basisVec n j k))
  -- = 0 + hermitianIP n (basisVec n i) (basisVec n j) = 0 + 0 = 0
  trans (cong₂ _+gf9_ zero-sq
          (sumGF9-cong n (λ k → refl)))
    (trans (cong (gf9-zero +gf9_)
            (basis-orthogonal n i j (λ eq → neq (cong Data.Nat.suc eq))))
           (+gf9-identityˡ gf9-zero))

--------------------------------------------------------------------------------
-- §9. 内积空间结构总结
--------------------------------------------------------------------------------

-- 核心定理列表 (全部 0 postulate, 构造性证明):
--
-- 1. hermitianIP: GF(9)ⁿ 上的 Hermitian 形式
--    ⟨f,g⟩ = Σᵢ f(i)·σ(g(i))
--
-- 2. hermitian-conj-sym: 共轭对称性
--    ⟨f,g⟩ = σ(⟨g,f⟩)
--
-- 3. hermitian-linearˡ: 第一变元线性性
--    ⟨a·f+g, h⟩ = a·⟨f,h⟩ + ⟨g,h⟩
--
-- 4. gf9-norm-real: 范数实值性
--    x·σ(x) = embed(N(x)) ∈ GF(3) ⊂ GF(9)
--
-- 5. galoisNorm-zero: 单分量正定性
--    N(x) = 0 ⟹ x = 0 (9 case 穷举)
--
-- 6. normSq-1-positive: 一维正定性
--    ‖f‖² = 0 ⟹ f = 0 (dim 1)
--
-- 7. basisVec: 标准正交基
--    eᵢ(j) = δᵢⱼ
--
-- 与 GF(3) 版本 (FunctionalDiscrete) 的对比:
--   GF(3): 对称双线性形式, 退化 (各向同性向量存在)
--   GF(9): Hermitian 形式, 单分量正定, 全维正定受 GF(3) 回绕限制
--   关键区别: GF(9) 的 Galois 共轭提供自然的 "共轭转置" 结构
--------------------------------------------------------------------------------
