{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Applied.LeibnizGF9
-- Leibniz 规则从 GF(3) 3 点函数推广到 GF(9) 9 点函数
--
-- 核心结果:
--   §1. GF(9) 加法逆元的代数性质
--   §2. Z/9Z 循环索引 (9 点)
--   §3. GF(9) 9 点函数空间: shift9, Δ9
--   §4. Δ9 的线性与移位交换性
--   §5. 循环卷积 (移位叠加定义)
--   §6. Leibniz 规则: Δ9(f*g) = f*(Δ9 g)
--
-- 推广路径:
--   GF(3) 3 点: HomologyHarmonic §5 — Δ(f*g) = f*(Δg)
--   GF(9) 9 点: 本文件 — Δ9(f*g) = f*(Δ9 g)
--   证明结构完全相同: 分解 → 线性 → 标量交换 → 移位交换 → 重组
--
-- 依赖:
--   GF9: GF(3²) 域运算, 域公理
--   Trit: GF(3) 底层类型, negate 代数性质
--
-- 0 postulate — 全部构造性证明, 穷举法优先
--------------------------------------------------------------------------------

module Sovereign.Applied.LeibnizGF9 where

open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (
  _≡_; refl; cong; cong₂; sym; trans; module ≡-Reasoning)

open import Sovereign.Base.Trit using (
  Trit; T₀; T₁; T₂; _⊕_; _⊗_; negate; negate²;
  ⊕-comm; ⊕-assoc; ⊕-identityˡ; ⊕-identityʳ;
  ⊗-comm; ⊗-identityˡ; ⊗-identityʳ;
  ⊗-distribˡ-⊕; ⊗-distribʳ-⊕; ⊗-assoc)
open import Sovereign.Algebra.GF9 using (
  GF9; _+gf9_; _*gf9_; gf9-one;
  +gf9-comm; +gf9-assoc; +gf9-identityˡ; +gf9-identityʳ;
  *gf9-comm; *gf9-assoc; *gf9-identityˡ; *gf9-identityʳ;
  *gf9-distribˡ-+gf9; *gf9-distribʳ-+gf9;
  negate-⊕; negate-⊗; negate-⊗-negate; negate-⊗-comm)

--------------------------------------------------------------------------------
-- §1. GF(9) 加法逆元及其代数性质
--
-- GF(9) = GF(3)[x]/(x²+1), 元素 (a, b) = a + bα
-- 加法逆元: gf9-neg (a, b) = (negate a, negate b)
--------------------------------------------------------------------------------

gf9-neg : GF9 → GF9
gf9-neg (a , b) = (negate a , negate b)

-- 定理 1.1: -(x + y) = (-x) + (-y)
gf9-neg-⊕ : ∀ x y → gf9-neg (x +gf9 y) ≡ gf9-neg x +gf9 gf9-neg y
gf9-neg-⊕ (a , b) (c , d) = cong₂ _,_ (negate-⊕ a c) (negate-⊕ b d)

-- 定理 1.2: -(-x) = x
gf9-neg² : ∀ x → gf9-neg (gf9-neg x) ≡ x
gf9-neg² (a , b) = cong₂ _,_ (negate² a) (negate² b)

-- 定理 1.3: -(s · x) = s · (-x)
gf9-neg-*gf9 : ∀ s x → gf9-neg (s *gf9 x) ≡ s *gf9 (gf9-neg x)
gf9-neg-*gf9 (a , b) (c , d) = cong₂ _,_ real-eq imag-eq
  where
    open ≡-Reasoning
    mul-neg-r : ∀ x y → x ⊗ (negate y) ≡ negate (x ⊗ y)
    mul-neg-r x y = trans (sym (negate-⊗-comm x y)) (sym (negate-⊗ x y))

    real-eq : negate ((a ⊗ c) ⊕ (negate (b ⊗ d)))
            ≡ (a ⊗ (negate c)) ⊕ (negate (b ⊗ (negate d)))
    real-eq = begin
      negate ((a ⊗ c) ⊕ (negate (b ⊗ d)))
        ≡⟨ negate-⊕ (a ⊗ c) (negate (b ⊗ d)) ⟩
      negate (a ⊗ c) ⊕ negate (negate (b ⊗ d))
        ≡⟨ cong (λ t → negate (a ⊗ c) ⊕ t) (negate² (b ⊗ d)) ⟩
      negate (a ⊗ c) ⊕ (b ⊗ d)
        ≡⟨ cong (_⊕ (b ⊗ d)) (sym (mul-neg-r a c)) ⟩
      (a ⊗ (negate c)) ⊕ (b ⊗ d)
        ≡⟨ cong ((a ⊗ (negate c)) ⊕_)
                (sym (trans (cong negate (mul-neg-r b d)) (negate² (b ⊗ d)))) ⟩
      (a ⊗ (negate c)) ⊕ negate (b ⊗ (negate d))
      ∎

    imag-eq : negate ((a ⊗ d) ⊕ (b ⊗ c))
            ≡ (a ⊗ (negate d)) ⊕ (b ⊗ (negate c))
    imag-eq = begin
      negate ((a ⊗ d) ⊕ (b ⊗ c))
        ≡⟨ negate-⊕ (a ⊗ d) (b ⊗ c) ⟩
      negate (a ⊗ d) ⊕ negate (b ⊗ c)
        ≡⟨ cong₂ _⊕_ (sym (mul-neg-r a d)) (sym (mul-neg-r b c)) ⟩
      (a ⊗ (negate d)) ⊕ (b ⊗ (negate c))
      ∎

--------------------------------------------------------------------------------
-- §1b. GF(3)/GF(9) 加法重排引理
--------------------------------------------------------------------------------

⊕-interchange : ∀ a b c d → (a ⊕ b) ⊕ (c ⊕ d) ≡ (a ⊕ c) ⊕ (b ⊕ d)
⊕-interchange a b c d = begin
  (a ⊕ b) ⊕ (c ⊕ d)
    ≡⟨ ⊕-assoc a b (c ⊕ d) ⟩
  a ⊕ (b ⊕ (c ⊕ d))
    ≡⟨ cong (a ⊕_) (sym (⊕-assoc b c d)) ⟩
  a ⊕ ((b ⊕ c) ⊕ d)
    ≡⟨ cong (a ⊕_) (cong (_⊕ d) (⊕-comm b c)) ⟩
  a ⊕ ((c ⊕ b) ⊕ d)
    ≡⟨ cong (a ⊕_) (⊕-assoc c b d) ⟩
  a ⊕ (c ⊕ (b ⊕ d))
    ≡⟨ sym (⊕-assoc a c (b ⊕ d)) ⟩
  (a ⊕ c) ⊕ (b ⊕ d)
  ∎
  where open ≡-Reasoning

+gf9-interchange : ∀ a b c d →
  (a +gf9 b) +gf9 (c +gf9 d) ≡ (a +gf9 c) +gf9 (b +gf9 d)
+gf9-interchange (a₁ , a₂) (b₁ , b₂) (c₁ , c₂) (d₁ , d₂) =
  cong₂ _,_ (⊕-interchange a₁ b₁ c₁ d₁) (⊕-interchange a₂ b₂ c₂ d₂)

--------------------------------------------------------------------------------
-- §2. Z/9Z 循环索引
--------------------------------------------------------------------------------

data Fin9 : Set where
  f0 f1 f2 f3 f4 f5 f6 f7 f8 : Fin9

suc9 : Fin9 → Fin9
suc9 f0 = f1
suc9 f1 = f2
suc9 f2 = f3
suc9 f3 = f4
suc9 f4 = f5
suc9 f5 = f6
suc9 f6 = f7
suc9 f7 = f8
suc9 f8 = f0

--------------------------------------------------------------------------------
-- §3. GF(9) 9 点函数空间
--------------------------------------------------------------------------------

GF9Func : Set
GF9Func = Fin9 → GF9

shift9 : GF9Func → GF9Func
shift9 f i = f (suc9 i)

gf9-neg-func : GF9Func → GF9Func
gf9-neg-func f i = gf9-neg (f i)

infixl 20 _+gf9f_
_+gf9f_ : GF9Func → GF9Func → GF9Func
(f +gf9f g) i = f i +gf9 g i

infixr 25 _*gf9fs_
_*gf9fs_ : GF9 → GF9Func → GF9Func
(s *gf9fs f) i = s *gf9 f i

-- 差分算子: Δ9 f (i) = f (i+1) - f (i)
Δ9 : GF9Func → GF9Func
Δ9 f i = shift9 f i +gf9 gf9-neg (f i)

-- 迭代移位
shift9⁰ : GF9Func → GF9Func
shift9⁰ f = f
shift9¹ : GF9Func → GF9Func
shift9¹ = shift9
shift9² : GF9Func → GF9Func
shift9² f = shift9 (shift9 f)
shift9³ : GF9Func → GF9Func
shift9³ f = shift9 (shift9 (shift9 f))
shift9⁴ : GF9Func → GF9Func
shift9⁴ f = shift9 (shift9 (shift9 (shift9 f)))
shift9⁵ : GF9Func → GF9Func
shift9⁵ f = shift9 (shift9 (shift9 (shift9 (shift9 f))))
shift9⁶ : GF9Func → GF9Func
shift9⁶ f = shift9 (shift9 (shift9 (shift9 (shift9 (shift9 f)))))
shift9⁷ : GF9Func → GF9Func
shift9⁷ f = shift9 (shift9 (shift9 (shift9 (shift9 (shift9 (shift9 f))))))
shift9⁸ : GF9Func → GF9Func
shift9⁸ f = shift9 (shift9 (shift9 (shift9 (shift9 (shift9 (shift9 (shift9 f)))))))

--------------------------------------------------------------------------------
-- §4. Δ9 的线性与移位交换性
--------------------------------------------------------------------------------

-- 定理 4.1: Δ9(f + g) = Δ9 f + Δ9 g
Δ9-linear : ∀ f g i → Δ9 (f +gf9f g) i ≡ (Δ9 f +gf9f Δ9 g) i
Δ9-linear f g i = begin
  (f (suc9 i) +gf9 g (suc9 i)) +gf9 gf9-neg (f i +gf9 g i)
    ≡⟨ cong ((f (suc9 i) +gf9 g (suc9 i)) +gf9_) (gf9-neg-⊕ (f i) (g i)) ⟩
  (f (suc9 i) +gf9 g (suc9 i)) +gf9 (gf9-neg (f i) +gf9 gf9-neg (g i))
    ≡⟨ +gf9-interchange (f (suc9 i)) (g (suc9 i)) (gf9-neg (f i)) (gf9-neg (g i)) ⟩
  (f (suc9 i) +gf9 gf9-neg (f i)) +gf9 (g (suc9 i) +gf9 gf9-neg (g i))
  ∎
  where open ≡-Reasoning

-- 定理 4.2: Δ9(s · g) = s · Δ9 g
Δ9-scalar : ∀ s g i → Δ9 (s *gf9fs g) i ≡ (s *gf9fs Δ9 g) i
Δ9-scalar s g i = begin
  (s *gf9 g (suc9 i)) +gf9 gf9-neg (s *gf9 g i)
    ≡⟨ cong ((s *gf9 g (suc9 i)) +gf9_) (gf9-neg-*gf9 s (g i)) ⟩
  (s *gf9 g (suc9 i)) +gf9 (s *gf9 gf9-neg (g i))
    ≡⟨ sym (*gf9-distribˡ-+gf9 s (g (suc9 i)) (gf9-neg (g i))) ⟩
  s *gf9 (g (suc9 i) +gf9 gf9-neg (g i))
  ∎
  where open ≡-Reasoning

-- 定理 4.3: Δ9(shift9 g) = shift9(Δ9 g) [refl]
Δ9-shift-comm : ∀ g i → Δ9 (shift9 g) i ≡ shift9 (Δ9 g) i
Δ9-shift-comm g i = refl

-- 定理 4.4: Δ9 与标量-移位复合交换
-- Δ9(s · Sⁿg) = s · Sⁿ(Δ9 g)
-- 证明: Δ9-linear + Δ9-scalar, 两步
Δ9-peel : ∀ s g rest i →
  Δ9 (s *gf9fs g +gf9f rest) i ≡ ((s *gf9fs Δ9 g) +gf9f Δ9 rest) i
Δ9-peel s g rest i = begin
  Δ9 (s *gf9fs g +gf9f rest) i
    ≡⟨ Δ9-linear (s *gf9fs g) rest i ⟩
  Δ9 (s *gf9fs g) i +gf9 Δ9 rest i
    ≡⟨ cong (_+gf9 Δ9 rest i) (Δ9-scalar s g i) ⟩
  (s *gf9fs Δ9 g) i +gf9 Δ9 rest i
  ∎
  where open ≡-Reasoning

--------------------------------------------------------------------------------
-- §5. 循环卷积 — 移位叠加定义
--
-- conv9 f g = f₀·g + f₁·S⁸g + f₂·S⁷g + ... + f₈·Sg
--
-- 等价于标准循环卷积:
--   (f*g)(i) = Σ_{j=0}^{8} f(j) · g(i - j mod 9)
-- 因为 i - j ≡ i + (9-j) (mod 9), 故 S^{9-j} g(i) = g(i-j).
--------------------------------------------------------------------------------

conv9 : GF9Func → GF9Func → GF9Func
conv9 f g =
  (f f0 *gf9fs g) +gf9f
  ((f f1 *gf9fs shift9⁸ g) +gf9f
  ((f f2 *gf9fs shift9⁷ g) +gf9f
  ((f f3 *gf9fs shift9⁶ g) +gf9f
  ((f f4 *gf9fs shift9⁵ g) +gf9f
  ((f f5 *gf9fs shift9⁴ g) +gf9f
  ((f f6 *gf9fs shift9³ g) +gf9f
  ((f f7 *gf9fs shift9² g) +gf9f
  (f f8 *gf9fs shift9¹ g))))))))

zero9-func : GF9Func
zero9-func i = (T₀ , T₀)

δ9 : GF9Func
δ9 f0 = gf9-one
δ9 f1 = (T₀ , T₀)
δ9 f2 = (T₀ , T₀)
δ9 f3 = (T₀ , T₀)
δ9 f4 = (T₀ , T₀)
δ9 f5 = (T₀ , T₀)
δ9 f6 = (T₀ , T₀)
δ9 f7 = (T₀ , T₀)
δ9 f8 = (T₀ , T₀)

--------------------------------------------------------------------------------
-- §6. Leibniz 规则 — Δ9(f*g) = f*(Δ9 g)
--
-- 证明策略 (与 GF(3) HomologyHarmonic §5d 完全相同):
--   1. conv9 f g = f₀·g + f₁·S⁸g + ... + f₈·Sg  (定义)
--   2. Δ9-peel 逐项剥离: Δ9(s·g + rest) = s·Δ9 g + Δ9 rest
--   3. Δ9 与移位交换 (refl): Δ9(Sⁿg) = Sⁿ(Δ9 g)
--   4. 重组为 conv9 f (Δ9 g)
--
-- 8 次 Δ9-peel + 1 次 Δ9-scalar + refl = 完整证明
--------------------------------------------------------------------------------

Δ9-conv9-leibniz : ∀ f g i → Δ9 (conv9 f g) i ≡ conv9 f (Δ9 g) i
Δ9-conv9-leibniz f g i = begin
  Δ9 (conv9 f g) i
    -- 剥离第 0 项: f(f0)·g
    ≡⟨ Δ9-peel (f f0) g
          ((f f1 *gf9fs shift9⁸ g) +gf9f
           ((f f2 *gf9fs shift9⁷ g) +gf9f
            ((f f3 *gf9fs shift9⁶ g) +gf9f
             ((f f4 *gf9fs shift9⁵ g) +gf9f
              ((f f5 *gf9fs shift9⁴ g) +gf9f
               ((f f6 *gf9fs shift9³ g) +gf9f
                ((f f7 *gf9fs shift9² g) +gf9f
                 (f f8 *gf9fs shift9¹ g)))))))) i ⟩
  (f f0 *gf9fs Δ9 g) i +gf9
  Δ9 ((f f1 *gf9fs shift9⁸ g) +gf9f
      ((f f2 *gf9fs shift9⁷ g) +gf9f
       ((f f3 *gf9fs shift9⁶ g) +gf9f
        ((f f4 *gf9fs shift9⁵ g) +gf9f
         ((f f5 *gf9fs shift9⁴ g) +gf9f
          ((f f6 *gf9fs shift9³ g) +gf9f
           ((f f7 *gf9fs shift9² g) +gf9f
            (f f8 *gf9fs shift9¹ g)))))))) i
    -- 剥离第 1 项: f(f1)·S⁸g
    ≡⟨ cong ((f f0 *gf9fs Δ9 g) i +gf9_)
            (Δ9-peel (f f1) (shift9⁸ g)
              ((f f2 *gf9fs shift9⁷ g) +gf9f
               ((f f3 *gf9fs shift9⁶ g) +gf9f
                ((f f4 *gf9fs shift9⁵ g) +gf9f
                 ((f f5 *gf9fs shift9⁴ g) +gf9f
                  ((f f6 *gf9fs shift9³ g) +gf9f
                   ((f f7 *gf9fs shift9² g) +gf9f
                    (f f8 *gf9fs shift9¹ g))))))) i) ⟩
  (f f0 *gf9fs Δ9 g) i +gf9
  ((f f1 *gf9fs Δ9 (shift9⁸ g)) i +gf9
   Δ9 ((f f2 *gf9fs shift9⁷ g) +gf9f
       ((f f3 *gf9fs shift9⁶ g) +gf9f
        ((f f4 *gf9fs shift9⁵ g) +gf9f
         ((f f5 *gf9fs shift9⁴ g) +gf9f
          ((f f6 *gf9fs shift9³ g) +gf9f
           ((f f7 *gf9fs shift9² g) +gf9f
            (f f8 *gf9fs shift9¹ g))))))) i)
    -- 剥离第 2 项: f(f2)·S⁷g
    -- 注意: Δ9(shift9⁸ g) ≡ shift9⁸(Δ9 g) 是 refl, Agda 自动归约
    ≡⟨ cong (λ x → (f f0 *gf9fs Δ9 g) i +gf9
                    ((f f1 *gf9fs shift9⁸ (Δ9 g)) i +gf9 x))
            (Δ9-peel (f f2) (shift9⁷ g)
              ((f f3 *gf9fs shift9⁶ g) +gf9f
               ((f f4 *gf9fs shift9⁵ g) +gf9f
                ((f f5 *gf9fs shift9⁴ g) +gf9f
                 ((f f6 *gf9fs shift9³ g) +gf9f
                  ((f f7 *gf9fs shift9² g) +gf9f
                   (f f8 *gf9fs shift9¹ g)))))) i) ⟩
  (f f0 *gf9fs Δ9 g) i +gf9
  ((f f1 *gf9fs shift9⁸ (Δ9 g)) i +gf9
   ((f f2 *gf9fs Δ9 (shift9⁷ g)) i +gf9
    Δ9 ((f f3 *gf9fs shift9⁶ g) +gf9f
        ((f f4 *gf9fs shift9⁵ g) +gf9f
         ((f f5 *gf9fs shift9⁴ g) +gf9f
          ((f f6 *gf9fs shift9³ g) +gf9f
           ((f f7 *gf9fs shift9² g) +gf9f
            (f f8 *gf9fs shift9¹ g)))))) i))
    -- 剥离第 3 项: f(f3)·S⁶g
    ≡⟨ cong (λ x → (f f0 *gf9fs Δ9 g) i +gf9
                    ((f f1 *gf9fs shift9⁸ (Δ9 g)) i +gf9
                     ((f f2 *gf9fs shift9⁷ (Δ9 g)) i +gf9 x)))
            (Δ9-peel (f f3) (shift9⁶ g)
              ((f f4 *gf9fs shift9⁵ g) +gf9f
               ((f f5 *gf9fs shift9⁴ g) +gf9f
                ((f f6 *gf9fs shift9³ g) +gf9f
                 ((f f7 *gf9fs shift9² g) +gf9f
                  (f f8 *gf9fs shift9¹ g))))) i) ⟩
  (f f0 *gf9fs Δ9 g) i +gf9
  ((f f1 *gf9fs shift9⁸ (Δ9 g)) i +gf9
   ((f f2 *gf9fs shift9⁷ (Δ9 g)) i +gf9
    ((f f3 *gf9fs Δ9 (shift9⁶ g)) i +gf9
     Δ9 ((f f4 *gf9fs shift9⁵ g) +gf9f
         ((f f5 *gf9fs shift9⁴ g) +gf9f
          ((f f6 *gf9fs shift9³ g) +gf9f
           ((f f7 *gf9fs shift9² g) +gf9f
            (f f8 *gf9fs shift9¹ g))))) i)))
    -- 剥离第 4 项: f(f4)·S⁵g
    ≡⟨ cong (λ x → (f f0 *gf9fs Δ9 g) i +gf9
                    ((f f1 *gf9fs shift9⁸ (Δ9 g)) i +gf9
                     ((f f2 *gf9fs shift9⁷ (Δ9 g)) i +gf9
                      ((f f3 *gf9fs shift9⁶ (Δ9 g)) i +gf9 x))))
            (Δ9-peel (f f4) (shift9⁵ g)
              ((f f5 *gf9fs shift9⁴ g) +gf9f
               ((f f6 *gf9fs shift9³ g) +gf9f
                ((f f7 *gf9fs shift9² g) +gf9f
                 (f f8 *gf9fs shift9¹ g)))) i) ⟩
  (f f0 *gf9fs Δ9 g) i +gf9
  ((f f1 *gf9fs shift9⁸ (Δ9 g)) i +gf9
   ((f f2 *gf9fs shift9⁷ (Δ9 g)) i +gf9
    ((f f3 *gf9fs shift9⁶ (Δ9 g)) i +gf9
     ((f f4 *gf9fs Δ9 (shift9⁵ g)) i +gf9
      Δ9 ((f f5 *gf9fs shift9⁴ g) +gf9f
          ((f f6 *gf9fs shift9³ g) +gf9f
           ((f f7 *gf9fs shift9² g) +gf9f
            (f f8 *gf9fs shift9¹ g)))) i))))
    -- 剥离第 5 项: f(f5)·S⁴g
    ≡⟨ cong (λ x → (f f0 *gf9fs Δ9 g) i +gf9
                    ((f f1 *gf9fs shift9⁸ (Δ9 g)) i +gf9
                     ((f f2 *gf9fs shift9⁷ (Δ9 g)) i +gf9
                      ((f f3 *gf9fs shift9⁶ (Δ9 g)) i +gf9
                       ((f f4 *gf9fs shift9⁵ (Δ9 g)) i +gf9 x)))))
            (Δ9-peel (f f5) (shift9⁴ g)
              ((f f6 *gf9fs shift9³ g) +gf9f
               ((f f7 *gf9fs shift9² g) +gf9f
                (f f8 *gf9fs shift9¹ g))) i) ⟩
  (f f0 *gf9fs Δ9 g) i +gf9
  ((f f1 *gf9fs shift9⁸ (Δ9 g)) i +gf9
   ((f f2 *gf9fs shift9⁷ (Δ9 g)) i +gf9
    ((f f3 *gf9fs shift9⁶ (Δ9 g)) i +gf9
     ((f f4 *gf9fs shift9⁵ (Δ9 g)) i +gf9
      ((f f5 *gf9fs Δ9 (shift9⁴ g)) i +gf9
       Δ9 ((f f6 *gf9fs shift9³ g) +gf9f
           ((f f7 *gf9fs shift9² g) +gf9f
            (f f8 *gf9fs shift9¹ g))) i)))))
    -- 剥离第 6 项: f(f6)·S³g
    ≡⟨ cong (λ x → (f f0 *gf9fs Δ9 g) i +gf9
                    ((f f1 *gf9fs shift9⁸ (Δ9 g)) i +gf9
                     ((f f2 *gf9fs shift9⁷ (Δ9 g)) i +gf9
                      ((f f3 *gf9fs shift9⁶ (Δ9 g)) i +gf9
                       ((f f4 *gf9fs shift9⁵ (Δ9 g)) i +gf9
                        ((f f5 *gf9fs shift9⁴ (Δ9 g)) i +gf9 x))))))
            (Δ9-peel (f f6) (shift9³ g)
              ((f f7 *gf9fs shift9² g) +gf9f
               (f f8 *gf9fs shift9¹ g)) i) ⟩
  (f f0 *gf9fs Δ9 g) i +gf9
  ((f f1 *gf9fs shift9⁸ (Δ9 g)) i +gf9
   ((f f2 *gf9fs shift9⁷ (Δ9 g)) i +gf9
    ((f f3 *gf9fs shift9⁶ (Δ9 g)) i +gf9
     ((f f4 *gf9fs shift9⁵ (Δ9 g)) i +gf9
      ((f f5 *gf9fs shift9⁴ (Δ9 g)) i +gf9
       ((f f6 *gf9fs Δ9 (shift9³ g)) i +gf9
        Δ9 ((f f7 *gf9fs shift9² g) +gf9f
            (f f8 *gf9fs shift9¹ g)) i))))))
    -- 剥离第 7 项: f(f7)·S²g
    ≡⟨ cong (λ x → (f f0 *gf9fs Δ9 g) i +gf9
                    ((f f1 *gf9fs shift9⁸ (Δ9 g)) i +gf9
                     ((f f2 *gf9fs shift9⁷ (Δ9 g)) i +gf9
                      ((f f3 *gf9fs shift9⁶ (Δ9 g)) i +gf9
                       ((f f4 *gf9fs shift9⁵ (Δ9 g)) i +gf9
                        ((f f5 *gf9fs shift9⁴ (Δ9 g)) i +gf9
                         ((f f6 *gf9fs shift9³ (Δ9 g)) i +gf9 x)))))))
            (Δ9-peel (f f7) (shift9² g)
              (f f8 *gf9fs shift9¹ g) i) ⟩
  (f f0 *gf9fs Δ9 g) i +gf9
  ((f f1 *gf9fs shift9⁸ (Δ9 g)) i +gf9
   ((f f2 *gf9fs shift9⁷ (Δ9 g)) i +gf9
    ((f f3 *gf9fs shift9⁶ (Δ9 g)) i +gf9
     ((f f4 *gf9fs shift9⁵ (Δ9 g)) i +gf9
      ((f f5 *gf9fs shift9⁴ (Δ9 g)) i +gf9
       ((f f6 *gf9fs shift9³ (Δ9 g)) i +gf9
        ((f f7 *gf9fs Δ9 (shift9² g)) i +gf9
         Δ9 (f f8 *gf9fs shift9¹ g) i)))))))
    -- 最后一项: f(f8)·Sg — 用 Δ9-scalar
    ≡⟨ cong (λ x → (f f0 *gf9fs Δ9 g) i +gf9
                    ((f f1 *gf9fs shift9⁸ (Δ9 g)) i +gf9
                     ((f f2 *gf9fs shift9⁷ (Δ9 g)) i +gf9
                      ((f f3 *gf9fs shift9⁶ (Δ9 g)) i +gf9
                       ((f f4 *gf9fs shift9⁵ (Δ9 g)) i +gf9
                        ((f f5 *gf9fs shift9⁴ (Δ9 g)) i +gf9
                         ((f f6 *gf9fs shift9³ (Δ9 g)) i +gf9
                          ((f f7 *gf9fs shift9² (Δ9 g)) i +gf9 x))))))))
            (Δ9-scalar (f f8) (shift9¹ g) i) ⟩
  -- 最终表达式 ≡ conv9 f (Δ9 g) i [定义归约]
  conv9 f (Δ9 g) i
  ∎
  where open ≡-Reasoning

-- 定理 6.2: 二阶 Leibniz 规则
-- Δ9²(f*g) = f*(Δ9² g)
Δ9²-conv9-leibniz : ∀ f g i →
  Δ9 (Δ9 (conv9 f g)) i ≡ conv9 f (Δ9 (Δ9 g)) i
Δ9²-conv9-leibniz f g i = begin
  Δ9 (conv9 f g) (suc9 i) +gf9 gf9-neg (Δ9 (conv9 f g) i)
    ≡⟨ cong₂ _+gf9_ (Δ9-conv9-leibniz f g (suc9 i))
                    (cong gf9-neg (Δ9-conv9-leibniz f g i)) ⟩
  conv9 f (Δ9 g) (suc9 i) +gf9 gf9-neg (conv9 f (Δ9 g) i)
    ≡⟨ Δ9-conv9-leibniz f (Δ9 g) i ⟩
  conv9 f (Δ9 (Δ9 g)) i
  ∎
  where open ≡-Reasoning
