{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Algebra.GF729Field
-- GF(729) 作为 GF(9) 的三次扩张 — 内在域乘法与 ⟨α⟩ 相位内在化
--
-- 数学背景:
--   GF(729) = GF(3⁶) 是 GF(3) 的 6 次扩张; 因 2 | 6, GF(9) ⊂ GF(729).
--   取 [GF729:GF9] = 3, 视 GF729 为 GF(9) 上 3 维向量空间:
--     GF729F = GF(9)[t]/(t³ + t - α),  α² = -1 (GF9 生成元)
--   约化: t³ = 2t + α (特征 3: -1 = 2)
--
-- 不可约性 (构造性): t³ + t - γ 在 GF(9) 上无根
--   根条件 γ = -(s³ + s); 而 s³+s 在 GF(9) 上的像不含 α
--   (α = (0,1) 不在 {s³+s | s ∈ GF9}, 由 9-case 穷举验证)
--
-- 展示群相位内在化 (对比 GF729 的加法层外作用):
--   乘 α = GF9 标量作用 → 每坐标乘 α (90° 旋转), α² = -1, 阶 4
--   embed-9 是环同态 (保加保乘) → GF9⟨α⟩ 真正活在 GF729F 的域结构内
--   Frobenius σ(x) = x³ 阶 6, σ(t) = t³ = 2t + α
--
-- 与 GF729 的关系: GF729 保持 T⁶ 格点加法工具定位; 本模块提供其域结构载体
-- (同一 243/729 态空间, 两种结构层: 加法向量空间 vs 域)
--
-- 0 postulate — 全部构造性证明

module Sovereign.Algebra.GF729Field where

open import Data.Product using (_×_; _,_; proj₁; proj₂; Σ)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; cong₂; sym; trans; module ≡-Reasoning)
open import Data.Nat using (ℕ; _^_) renaming (_*_ to _*ℕ_)

open import Sovereign.Base.Trit
  using (Trit; T₀; T₁; T₂; _⊕_; _⊗_;
         ⊕-identityˡ; ⊕-identityʳ; ⊕-comm; ⊕-assoc; ⊕-inverse;
         ⊗-identityˡ; ⊗-identityʳ; ⊗-comm; ⊗-assoc;
         ⊗-distribˡ-⊕; ⊗-distribʳ-⊕; ⊗-zeroˡ; ⊗-zeroʳ;
         negate; negate²)

open import Sovereign.Algebra.GF9
  using (GF9; alpha; gf9-zero; gf9-one; alpha-powers-4; alpha-squared; _+gf9_; _*gf9_;
         +gf9-comm; +gf9-assoc; +gf9-identityˡ; +gf9-identityʳ; +gf9-inverse;
         *gf9-identityˡ; *gf9-identityʳ; *gf9-comm; *gf9-assoc;
         *gf9-distribˡ-+gf9; *gf9-distribʳ-+gf9;
         negate-⊕; negate-⊗; negate-⊗-negate; negate-⊗-comm; two-mul-is-neg;
         galoisConjugate; galoisConjugate-add; galoisConjugate-mul)

open ≡-Reasoning

--------------------------------------------------------------------------------
-- §1. 载体 GF(9)³ = GF(9)[t]/(t³ + t - α)
--
-- (x₀, x₁, x₂) 表示 x₀ + x₁t + x₂t², 约化 t³ = 2t + α
--------------------------------------------------------------------------------

GF729F : Set
GF729F = GF9 × GF9 × GF9

gf729F-zero : GF729F
gf729F-zero = gf9-zero , gf9-zero , gf9-zero

gf729F-one : GF729F
gf729F-one = gf9-one , gf9-zero , gf9-zero

-- 生成元 t
t : GF729F
t = gf9-zero , gf9-one , gf9-zero

-- 逐分量 GF9 加法
_+F_ : GF729F → GF729F → GF729F
(x₀ , x₁ , x₂) +F (y₀ , y₁ , y₂) = (x₀ +gf9 y₀) , (x₁ +gf9 y₁) , (x₂ +gf9 y₂)

-- 逐分量 GF9 取反
negF : GF729F → GF729F
negF (x₀ , x₁ , x₂) =
  (negate (proj₁ x₀) , negate (proj₂ x₀)) ,
  (negate (proj₁ x₁) , negate (proj₂ x₁)) ,
  (negate (proj₁ x₂) , negate (proj₂ x₂))

-- 三元组同余
cong-triple : ∀ {a₀ a₁ a₂ b₀ b₁ b₂ : GF9} →
  a₀ ≡ b₀ → a₁ ≡ b₁ → a₂ ≡ b₂ → (a₀ , a₁ , a₂) ≡ (b₀ , b₁ , b₂)
cong-triple refl refl refl = refl

--------------------------------------------------------------------------------
-- §2. 加法群公理 (逐分量提升自 GF9)
--------------------------------------------------------------------------------

+F-identityˡ : ∀ x → gf729F-zero +F x ≡ x
+F-identityˡ (x₀ , x₁ , x₂) =
  cong-triple (+gf9-identityˡ x₀) (+gf9-identityˡ x₁) (+gf9-identityˡ x₂)

+F-identityʳ : ∀ x → x +F gf729F-zero ≡ x
+F-identityʳ (x₀ , x₁ , x₂) =
  cong-triple (+gf9-identityʳ x₀) (+gf9-identityʳ x₁) (+gf9-identityʳ x₂)

+F-comm : ∀ x y → x +F y ≡ y +F x
+F-comm (x₀ , x₁ , x₂) (y₀ , y₁ , y₂) =
  cong-triple (+gf9-comm x₀ y₀) (+gf9-comm x₁ y₁) (+gf9-comm x₂ y₂)

+F-assoc : ∀ x y z → (x +F y) +F z ≡ x +F (y +F z)
+F-assoc (x₀ , x₁ , x₂) (y₀ , y₁ , y₂) (z₀ , z₁ , z₂) =
  cong-triple (+gf9-assoc x₀ y₀ z₀) (+gf9-assoc x₁ y₁ z₁) (+gf9-assoc x₂ y₂ z₂)

+F-inverse : ∀ x → x +F negF x ≡ gf729F-zero
+F-inverse (x₀ , x₁ , x₂) =
  cong-triple (+gf9-inverse x₀) (+gf9-inverse x₁) (+gf9-inverse x₂)

--------------------------------------------------------------------------------
-- §3. 域乘法: GF(9)[t] 卷积 (度 ≤ 4) + 约化 t³ = 2t + α
--
-- (x₀+x₁t+x₂t²)(y₀+y₁t+y₂t²) 的原始积系数:
--   p₀ = x₀y₀
--   p₁ = x₀y₁ + x₁y₀
--   p₂ = x₀y₂ + x₁y₁ + x₂y₀
--   p₃ = x₁y₂ + x₂y₁
--   p₄ = x₂y₂
-- 约化 (t³ = 2t + α, t⁴ = 2t² + αt):
--   r₀ = p₀ + p₃·α
--   r₁ = p₁ + 2p₃ + p₄·α = p₁ - p₃ + p₄α
--   r₂ = p₂ + 2p₄       = p₂ - p₄
--------------------------------------------------------------------------------

-- 2·x = negate x (GF(3)); GF9 取反
gf9-negate : GF9 → GF9
gf9-negate (a , b) = (negate a , negate b)

-- p₃ 的 GF9 取反
_*F_ : GF729F → GF729F → GF729F
(x₀ , x₁ , x₂) *F (y₀ , y₁ , y₂) =
  let p₀ = x₀ *gf9 y₀
      p₁ = (x₀ *gf9 y₁) +gf9 (x₁ *gf9 y₀)
      p₂ = ((x₀ *gf9 y₂) +gf9 (x₁ *gf9 y₁)) +gf9 (x₂ *gf9 y₀)
      p₃ = (x₁ *gf9 y₂) +gf9 (x₂ *gf9 y₁)
      p₄ = x₂ *gf9 y₂
  in  (p₀ +gf9 (p₃ *gf9 alpha)) ,
      ((p₁ +gf9 (gf9-negate p₃)) +gf9 (p₄ *gf9 alpha)) ,
      (p₂ +gf9 (gf9-negate p₄))


--------------------------------------------------------------------------------
-- §4. GF9 零元/取反辅助律 (本地补齐, 提升自 Trit)
--------------------------------------------------------------------------------

-- 零乘: (0,0)*(a,b) = (0*a - 0*b, 0*b + 0*a) = (0,0)
gf9-zero-mulˡ : ∀ x → gf9-zero *gf9 x ≡ gf9-zero
gf9-zero-mulˡ (a , b) =
  cong₂ _,_
    (trans (cong₂ (λ u v → u ⊕ negate v) (⊗-zeroˡ a) (⊗-zeroˡ b))
           (trans (cong (T₀ ⊕_) refl) (⊕-identityˡ T₀)))
    (trans (cong₂ _⊕_ (⊗-zeroˡ b) (⊗-zeroˡ a)) (⊕-identityˡ T₀))

-- 零乘: (a,b)*(0,0) = (a*0 - b*0, a*0 + b*0) = (0,0)
gf9-zero-mulʳ : ∀ x → x *gf9 gf9-zero ≡ gf9-zero
gf9-zero-mulʳ (a , b) =
  cong₂ _,_
    (trans (cong₂ (λ u v → u ⊕ negate v) (⊗-zeroʳ a) (⊗-zeroʳ b))
           (trans (cong (T₀ ⊕_) refl) (⊕-identityˡ T₀)))
    (trans (cong₂ _⊕_ (⊗-zeroʳ a) (⊗-zeroʳ b)) (⊕-identityˡ T₀))

gf9-zero-addˡ : ∀ x → gf9-zero +gf9 x ≡ x
gf9-zero-addˡ = +gf9-identityˡ

gf9-zero-addʳ : ∀ x → x +gf9 gf9-zero ≡ x
gf9-zero-addʳ = +gf9-identityʳ

-- 取反与零/单位
gf9-negate-invol : ∀ x → gf9-negate (gf9-negate x) ≡ x
gf9-negate-invol (a , b) = cong₂ _,_ (negate² a) (negate² b)

gf9-negate-add : ∀ x y → gf9-negate (x +gf9 y) ≡ gf9-negate x +gf9 gf9-negate y
gf9-negate-add (a , b) (c , d) =
  cong₂ _,_ (negate-⊕ a c) (negate-⊕ b d)

gf9-negate-zero : gf9-negate gf9-zero ≡ gf9-zero
gf9-negate-zero = refl


--------------------------------------------------------------------------------
-- §5. 乘法单位元 (分层辅助引理, 每项 ≤2 层 trans)
--------------------------------------------------------------------------------

-- p₃ = 0*x₂ + 0*x₁ ≡ 0
p3-zero : ∀ a b → (gf9-zero *gf9 a) +gf9 (gf9-zero *gf9 b) ≡ gf9-zero
p3-zero a b =
  trans (cong₂ _+gf9_ (gf9-zero-mulˡ a) (gf9-zero-mulˡ b))
        (gf9-zero-addˡ gf9-zero)

-- 0 * alpha ≡ 0
zero-*alpha : gf9-zero *gf9 alpha ≡ gf9-zero
zero-*alpha = gf9-zero-mulˡ alpha

-- (0 * y) * alpha ≡ 0
zero-mul-alpha-r : ∀ y → (gf9-zero *gf9 y) *gf9 alpha ≡ gf9-zero
zero-mul-alpha-r y =
  trans (cong (_*gf9 alpha) (gf9-zero-mulˡ y)) (gf9-zero-mulˡ alpha)

-- negate 0 ≡ 0
neg-zero : gf9-negate gf9-zero ≡ gf9-zero
neg-zero = refl

-- r₀ 分量: (1*x₀) + (0*x₂ + 0*x₁)*alpha ≡ x₀
id-r0 : ∀ x₀ x₁ x₂ →
  (gf9-one *gf9 x₀) +gf9 (((gf9-zero *gf9 x₂) +gf9 (gf9-zero *gf9 x₁)) *gf9 alpha) ≡ x₀
id-r0 x₀ x₁ x₂ =
  trans (cong₂ _+gf9_ (*gf9-identityˡ x₀) (cong (_*gf9 alpha) (p3-zero x₂ x₁)))
        (trans (cong (λ u → x₀ +gf9 u) zero-*alpha) (gf9-zero-addʳ x₀))

-- r₁ 分量: (1*x₁ + 0*x₀ + negate(0*x₂ + 0*x₁)) + (0*x₂)*alpha ≡ x₁
id-r1 : ∀ x₀ x₁ x₂ →
  (((gf9-one *gf9 x₁) +gf9 (gf9-zero *gf9 x₀)) +gf9
   gf9-negate ((gf9-zero *gf9 x₂) +gf9 (gf9-zero *gf9 x₁))) +gf9
  ((gf9-zero *gf9 x₂) *gf9 alpha) ≡ x₁
id-r1 x₀ x₁ x₂ =
  trans (cong (λ u → u +gf9 ((gf9-zero *gf9 x₂) *gf9 alpha)) p1+neg)
        (trans (cong (λ u → x₁ +gf9 u) (zero-mul-alpha-r x₂)) (gf9-zero-addʳ x₁))
  where
    p1+neg :
      ((gf9-one *gf9 x₁) +gf9 (gf9-zero *gf9 x₀)) +gf9
      gf9-negate ((gf9-zero *gf9 x₂) +gf9 (gf9-zero *gf9 x₁)) ≡ x₁
    p1+neg =
      trans (cong (λ u → u +gf9 gf9-negate ((gf9-zero *gf9 x₂) +gf9 (gf9-zero *gf9 x₁)))
                   (trans (cong₂ _+gf9_ (*gf9-identityˡ x₁) (gf9-zero-mulˡ x₀))
                          (gf9-zero-addʳ x₁)))
            (trans (cong (λ u → x₁ +gf9 u)
                         (trans (cong gf9-negate (p3-zero x₂ x₁)) neg-zero))
                   (gf9-zero-addʳ x₁))

-- r₂ 分量: (1*x₂ + 0*x₁ + 0*x₀) + negate(0*x₂) ≡ x₂
id-r2 : ∀ x₀ x₁ x₂ →
  (((gf9-one *gf9 x₂) +gf9 (gf9-zero *gf9 x₁)) +gf9 (gf9-zero *gf9 x₀)) +gf9
  gf9-negate (gf9-zero *gf9 x₂) ≡ x₂
id-r2 x₀ x₁ x₂ =
  trans (cong (λ u → u +gf9 gf9-negate (gf9-zero *gf9 x₂)) p2x₂)
        (trans (cong (λ u → x₂ +gf9 u)
                     (trans (cong gf9-negate (gf9-zero-mulˡ x₂)) neg-zero))
               (gf9-zero-addʳ x₂))
  where
    p2x₂ : ((gf9-one *gf9 x₂) +gf9 (gf9-zero *gf9 x₁)) +gf9 (gf9-zero *gf9 x₀) ≡ x₂
    p2x₂ =
      trans (cong (λ u → u +gf9 (gf9-zero *gf9 x₀))
                   (trans (cong₂ _+gf9_ (*gf9-identityˡ x₂) (gf9-zero-mulˡ x₁))
                          (gf9-zero-addʳ x₂)))
            (trans (cong (λ u → x₂ +gf9 u) (gf9-zero-mulˡ x₀)) (gf9-zero-addʳ x₂))

*F-identityˡ : ∀ x → gf729F-one *F x ≡ x
*F-identityˡ (x₀ , x₁ , x₂) =
  cong-triple (id-r0 x₀ x₁ x₂) (id-r1 x₀ x₁ x₂) (id-r2 x₀ x₁ x₂)


--------------------------------------------------------------------------------
-- §6. 乘法交换律
--
-- x*y 与 y*x 的卷积系数逐项对称 (GF9 交换), 约化项亦对称.
-- 分量级: 每个 rᵢ(x*y) ≡ rᵢ(y*x), 由系数对称 + +gf9-comm 组装.
--------------------------------------------------------------------------------

-- p1 对称: (x₀y₁ + x₁y₀) ≡ (y₀x₁ + y₁x₀)
p1-comm : ∀ x₀ x₁ y₀ y₁ →
  (x₀ *gf9 y₁) +gf9 (x₁ *gf9 y₀) ≡ (y₀ *gf9 x₁) +gf9 (y₁ *gf9 x₀)
p1-comm x₀ x₁ y₀ y₁ =
  trans (cong₂ _+gf9_ (*gf9-comm x₀ y₁) (*gf9-comm x₁ y₀))
        (+gf9-comm (y₁ *gf9 x₀) (y₀ *gf9 x₁))

-- p3 对称
p3-comm : ∀ x₁ x₂ y₁ y₂ →
  (x₁ *gf9 y₂) +gf9 (x₂ *gf9 y₁) ≡ (y₁ *gf9 x₂) +gf9 (y₂ *gf9 x₁)
p3-comm x₁ x₂ y₁ y₂ =
  trans (cong₂ _+gf9_ (*gf9-comm x₁ y₂) (*gf9-comm x₂ y₁))
        (+gf9-comm (y₂ *gf9 x₁) (y₁ *gf9 x₂))

-- p2 对称: ((x₀y₂ + x₁y₁) + x₂y₀) ≡ ((y₀x₂ + y₁x₁) + y₂x₀)
-- 三元反转: ((A+B)+C) ≡ ((C+B)+A)
rev3 : ∀ A B C → ((A +gf9 B) +gf9 C) ≡ ((C +gf9 B) +gf9 A)
rev3 A B C =
  trans (+gf9-comm (A +gf9 B) C)
    (trans (cong (λ u → C +gf9 u) (+gf9-comm A B))
           (sym (+gf9-assoc C B A)))

-- p2 对称: ((x₀y₂ + x₁y₁) + x₂y₀) ≡ ((y₀x₂ + y₁x₁) + y₂x₀)
p2-comm : ∀ x₀ x₁ x₂ y₀ y₁ y₂ →
  ((x₀ *gf9 y₂) +gf9 (x₁ *gf9 y₁)) +gf9 (x₂ *gf9 y₀)
  ≡ ((y₀ *gf9 x₂) +gf9 (y₁ *gf9 x₁)) +gf9 (y₂ *gf9 x₀)
p2-comm x₀ x₁ x₂ y₀ y₁ y₂ =
  trans (cong₂ _+gf9_
          (cong₂ _+gf9_ (*gf9-comm x₀ y₂) (*gf9-comm x₁ y₁))
          (*gf9-comm x₂ y₀))
        (rev3 (y₂ *gf9 x₀) (y₁ *gf9 x₁) (y₀ *gf9 x₂))

-- 分量级交换律: 每个 rᵢ(x*y) ≡ rᵢ(y*x)
-- 记 x*y 的约化项, 用系数对称 + alpha 项对称组装
comm-r0 : ∀ x₀ x₁ x₂ y₀ y₁ y₂ →
  (x₀ *gf9 y₀) +gf9 (((x₁ *gf9 y₂) +gf9 (x₂ *gf9 y₁)) *gf9 alpha)
  ≡ (y₀ *gf9 x₀) +gf9 (((y₁ *gf9 x₂) +gf9 (y₂ *gf9 x₁)) *gf9 alpha)
comm-r0 x₀ x₁ x₂ y₀ y₁ y₂ =
  cong₂ _+gf9_ (*gf9-comm x₀ y₀)
    (cong (λ u → u *gf9 alpha) (p3-comm x₁ x₂ y₁ y₂))

comm-r1 : ∀ x₀ x₁ x₂ y₀ y₁ y₂ →
  (((x₀ *gf9 y₁) +gf9 (x₁ *gf9 y₀)) +gf9
   gf9-negate ((x₁ *gf9 y₂) +gf9 (x₂ *gf9 y₁))) +gf9
  ((x₂ *gf9 y₂) *gf9 alpha)
  ≡ (((y₀ *gf9 x₁) +gf9 (y₁ *gf9 x₀)) +gf9
     gf9-negate ((y₁ *gf9 x₂) +gf9 (y₂ *gf9 x₁))) +gf9
    ((y₂ *gf9 x₂) *gf9 alpha)
comm-r1 x₀ x₁ x₂ y₀ y₁ y₂ =
  cong₂ _+gf9_
    (cong₂ _+gf9_ (p1-comm x₀ x₁ y₀ y₁)
       (cong gf9-negate (p3-comm x₁ x₂ y₁ y₂)))
    (cong (λ u → u *gf9 alpha) (*gf9-comm x₂ y₂))

comm-r2 : ∀ x₀ x₁ x₂ y₀ y₁ y₂ →
  (((x₀ *gf9 y₂) +gf9 (x₁ *gf9 y₁)) +gf9 (x₂ *gf9 y₀)) +gf9
  gf9-negate (x₂ *gf9 y₂)
  ≡ (((y₀ *gf9 x₂) +gf9 (y₁ *gf9 x₁)) +gf9 (y₂ *gf9 x₀)) +gf9
    gf9-negate (y₂ *gf9 x₂)
comm-r2 x₀ x₁ x₂ y₀ y₁ y₂ =
  cong₂ _+gf9_ (p2-comm x₀ x₁ x₂ y₀ y₁ y₂)
    (cong gf9-negate (*gf9-comm x₂ y₂))

*F-comm : ∀ x y → x *F y ≡ y *F x
*F-comm (x₀ , x₁ , x₂) (y₀ , y₁ , y₂) =
  cong-triple (comm-r0 x₀ x₁ x₂ y₀ y₁ y₂)
              (comm-r1 x₀ x₁ x₂ y₀ y₁ y₂)
              (comm-r2 x₀ x₁ x₂ y₀ y₁ y₂)

*F-identityʳ : ∀ x → x *F gf729F-one ≡ x
*F-identityʳ x = trans (*F-comm x gf729F-one) (*F-identityˡ x)

--------------------------------------------------------------------------------
-- §7. GF9 → GF729F 环同态 (相位源真正嵌入域结构)
--
-- embed-9 c = (c, 0, 0) — 常数多项式
-- 保加: 逐分量; 保乘: 卷积后约化 (c,0,0)*(d,0,0) = (cd, 0, 0)
--------------------------------------------------------------------------------

embed-9 : GF9 → GF729F
embed-9 c = c , gf9-zero , gf9-zero

embed-9-add : ∀ a b → embed-9 (a +gf9 b) ≡ embed-9 a +F embed-9 b
embed-9-add a b = cong-triple refl
  (sym (+gf9-identityˡ gf9-zero))
  (sym (+gf9-identityˡ gf9-zero))

-- embed-9-mul 的分量辅助: (c,0,0)*(d,0,0) 的约化
embed-mul-r0 : ∀ c d →
  (c *gf9 d) +gf9 (((gf9-zero *gf9 gf9-zero) +gf9 (gf9-zero *gf9 gf9-zero)) *gf9 alpha)
  ≡ c *gf9 d
embed-mul-r0 c d =
  trans (cong (λ u → (c *gf9 d) +gf9 u)
               (cong (λ u → u *gf9 alpha) (gf9-zero-addˡ gf9-zero)))
        (trans (cong (λ u → (c *gf9 d) +gf9 u) (gf9-zero-mulˡ alpha))
               (gf9-zero-addʳ (c *gf9 d)))

embed-mul-r1 : ∀ c d →
  (((c *gf9 gf9-zero) +gf9 (gf9-zero *gf9 d)) +gf9
   gf9-negate ((gf9-zero *gf9 gf9-zero) +gf9 (gf9-zero *gf9 gf9-zero))) +gf9
  ((gf9-zero *gf9 gf9-zero) *gf9 alpha)
  ≡ gf9-zero
embed-mul-r1 c d =
  trans (cong (λ u → ((u +gf9 (gf9-zero *gf9 d)) +gf9
                        gf9-negate ((gf9-zero *gf9 gf9-zero) +gf9 (gf9-zero *gf9 gf9-zero))) +gf9
                        ((gf9-zero *gf9 gf9-zero) *gf9 alpha))
               (gf9-zero-mulʳ c))
    (trans (cong (λ u → ((gf9-zero +gf9 u) +gf9
                          gf9-negate ((gf9-zero *gf9 gf9-zero) +gf9 (gf9-zero *gf9 gf9-zero))) +gf9
                          ((gf9-zero *gf9 gf9-zero) *gf9 alpha))
                 (gf9-zero-mulˡ d))
      (trans (cong (λ u → ((gf9-zero +gf9 gf9-zero) +gf9 u) +gf9
                            ((gf9-zero *gf9 gf9-zero) *gf9 alpha))
                   (trans (cong gf9-negate (gf9-zero-addˡ gf9-zero)) neg-zero))
        (trans (cong (λ u → (gf9-zero +gf9 gf9-zero) +gf9 u) (gf9-zero-mulˡ alpha))
          (trans (cong (λ u → u +gf9 gf9-zero) (gf9-zero-addˡ gf9-zero))
                 (gf9-zero-addʳ gf9-zero)))))

embed-mul-r2 : ∀ c d →
  (((c *gf9 gf9-zero) +gf9 (gf9-zero *gf9 gf9-zero)) +gf9 (gf9-zero *gf9 d)) +gf9
  gf9-negate (gf9-zero *gf9 gf9-zero)
  ≡ gf9-zero
embed-mul-r2 c d =
  trans (cong (λ u → ((u +gf9 (gf9-zero *gf9 gf9-zero)) +gf9 (gf9-zero *gf9 d)) +gf9
                        gf9-negate (gf9-zero *gf9 gf9-zero))
               (gf9-zero-mulʳ c))
    (trans (cong (λ u → ((gf9-zero +gf9 u) +gf9 (gf9-zero *gf9 d)) +gf9
                          gf9-negate (gf9-zero *gf9 gf9-zero))
                 (gf9-zero-mulˡ gf9-zero))
      (trans (cong (λ u → ((gf9-zero +gf9 gf9-zero) +gf9 u) +gf9
                            gf9-negate (gf9-zero *gf9 gf9-zero))
                   (gf9-zero-mulˡ d))
        (trans (cong (λ u → ((gf9-zero +gf9 gf9-zero) +gf9 gf9-zero) +gf9 u)
                     (trans (cong gf9-negate (gf9-zero-mulˡ gf9-zero)) neg-zero))
          (trans (cong (λ u → u +gf9 gf9-zero) (gf9-zero-addˡ gf9-zero))
                 (gf9-zero-addʳ gf9-zero)))))

embed-9-mul : ∀ a b → embed-9 (a *gf9 b) ≡ embed-9 a *F embed-9 b
embed-9-mul a b =
  cong-triple (sym (embed-mul-r0 a b)) (sym (embed-mul-r1 a b)) (sym (embed-mul-r2 a b))

embed-9-one : embed-9 gf9-one ≡ gf729F-one
embed-9-one = refl

embed-9-zero : embed-9 gf9-zero ≡ gf729F-zero
embed-9-zero = refl

--------------------------------------------------------------------------------
-- §8. 相位内在化: 乘 α = GF9 标量作用 (每坐标乘 α)
--
-- GF729F 是 GF9-代数, α ∈ GF9 作为标量作用于 3 个坐标.
-- 这给出 90° 旋转的内在实现 (不再依赖外部加法群作用).
--------------------------------------------------------------------------------

-- GF9 标量乘法 (逐坐标)
_*s_ : GF9 → GF729F → GF729F
c *s (x₀ , x₁ , x₂) = (c *gf9 x₀) , (c *gf9 x₁) , (c *gf9 x₂)

-- 标量作用的域乘法实现: (c,0,0)*(x₀,x₁,x₂) 的卷积
--   p₀=cx₀ p₁=cx₁ p₂=cx₂ p₃=0 p₄=0
--   r₀ = cx₀ + 0·α = cx₀ ; r₁ = cx₁ + neg 0 + 0 = cx₁ ; r₂ = cx₂ + neg 0 = cx₂
scalar-r0 : ∀ c x₀ x₁ x₂ →
  (c *gf9 x₀) +gf9 (((gf9-zero *gf9 x₂) +gf9 (gf9-zero *gf9 x₁)) *gf9 alpha)
  ≡ c *gf9 x₀
scalar-r0 c x₀ x₁ x₂ =
  trans (cong (λ u → (c *gf9 x₀) +gf9 u)
               (cong (λ u → u *gf9 alpha) (p3-zero x₂ x₁)))
        (trans (cong (λ u → (c *gf9 x₀) +gf9 u) zero-*alpha)
               (gf9-zero-addʳ (c *gf9 x₀)))

scalar-r1 : ∀ c x₀ x₁ x₂ →
  (((c *gf9 x₁) +gf9 (gf9-zero *gf9 x₀)) +gf9
   gf9-negate ((gf9-zero *gf9 x₂) +gf9 (gf9-zero *gf9 x₁))) +gf9
  ((gf9-zero *gf9 x₂) *gf9 alpha)
  ≡ c *gf9 x₁
-- 双零后缀剥除: ((t + 0) + 0) ≡ t
zero2-add : ∀ t → ((t +gf9 gf9-zero) +gf9 gf9-zero) ≡ t
zero2-add t =
  trans (cong (λ u → u +gf9 gf9-zero) (gf9-zero-addʳ t)) (gf9-zero-addʳ t)

scalar-r1 c x₀ x₁ x₂ =
  trans (cong (λ u → (((c *gf9 x₁) +gf9 u) +gf9
                        gf9-negate ((gf9-zero *gf9 x₂) +gf9 (gf9-zero *gf9 x₁))) +gf9
                      ((gf9-zero *gf9 x₂) *gf9 alpha))
               (gf9-zero-mulˡ x₀))
    (trans (cong (λ u → (((c *gf9 x₁) +gf9 gf9-zero) +gf9 u) +gf9
                          ((gf9-zero *gf9 x₂) *gf9 alpha))
                 (trans (cong gf9-negate (p3-zero x₂ x₁)) neg-zero))
      (trans (cong (λ u → u +gf9 ((gf9-zero *gf9 x₂) *gf9 alpha))
                   (zero2-add (c *gf9 x₁)))
        (trans (cong (λ u → (c *gf9 x₁) +gf9 u) (zero-mul-alpha-r x₂))
               (gf9-zero-addʳ (c *gf9 x₁)))))

scalar-r2 : ∀ c x₀ x₁ x₂ →
  (((c *gf9 x₂) +gf9 (gf9-zero *gf9 x₁)) +gf9 (gf9-zero *gf9 x₀)) +gf9
  gf9-negate (gf9-zero *gf9 x₂)
  ≡ c *gf9 x₂
scalar-r2 c x₀ x₁ x₂ =
  trans (cong (λ u → (((c *gf9 x₂) +gf9 u) +gf9 (gf9-zero *gf9 x₀)) +gf9
                        gf9-negate (gf9-zero *gf9 x₂))
               (gf9-zero-mulˡ x₁))
    (trans (cong (λ u → (((c *gf9 x₂) +gf9 gf9-zero) +gf9 u) +gf9
                          gf9-negate (gf9-zero *gf9 x₂))
                 (gf9-zero-mulˡ x₀))
      (trans (cong (λ u → u +gf9 gf9-negate (gf9-zero *gf9 x₂))
                   (zero2-add (c *gf9 x₂)))
        (trans (cong (λ u → (c *gf9 x₂) +gf9 u)
                     (trans (cong gf9-negate (gf9-zero-mulˡ x₂)) neg-zero))
               (gf9-zero-addʳ (c *gf9 x₂)))))

-- 标量作用 = 左乘常数 (相位内在化的结构根据)
-- embed-9 c *F x 展开: p₀=cx₀ p₁=cx₁ p₂=cx₂ p₃=0 p₄=0
scalar-mul : ∀ c x → c *s x ≡ embed-9 c *F x
scalar-mul c (x₀ , x₁ , x₂) =
  cong-triple (sym (scalar-r0 c x₀ x₁ x₂))
              (sym (scalar-r1 c x₀ x₁ x₂))
              (sym (scalar-r2 c x₀ x₁ x₂))

--------------------------------------------------------------------------------
-- §9. 90° 相位旋转内在化: 乘 α 作用 = 每坐标乘 α
--
-- α ∈ GF9 是 GF729F 的内蕴元素 (经 embed-9), α² = -1.
-- 左乘 α 的作用 = 标量作用 α *s, 即 90° 旋转.
-- 这是"相位活在域结构内"的核心: 旋转是域乘法的特化, 非外部附加.
--------------------------------------------------------------------------------

-- α 作为 GF729F 内蕴元素
alphaF : GF729F
alphaF = embed-9 alpha

-- 乘 α 作用 = α 标量作用 (由 scalar-mul 特化)
alpha-mul-is-scalar : ∀ x → alphaF *F x ≡ alpha *s x
alpha-mul-is-scalar x = sym (scalar-mul alpha x)

-- 相位旋转 (90°): 乘 α
rot90 : GF729F → GF729F
rot90 x = alphaF *F x

-- α 坐标: (α, 0, 0) = (0,1),0,0
alphaF-coord : alphaF ≡ ((T₀ , T₁) , gf9-zero , gf9-zero)
alphaF-coord = refl

-- 逐坐标乘 α 的 GF9 坐标公式: α*(a,b) = (0*a - 1*b, 0*b + 1*a) = (neg b, a)
-- alpha = (T₀,T₁) 的坐标等式 (用于展开投影)
alpha-pair : alpha ≡ (T₀ , T₁)
alpha-pair = refl

-- 逐坐标乘 α 的 GF9 坐标公式: α*(a,b) = (neg b, a)
-- 展开 alpha=(T₀,T₁) 后: (T₀*a - T₁*b, T₀*b + T₁*a) = (neg b, a)
mul-alpha-coord : ∀ a b → alpha *gf9 (a , b) ≡ (negate b , a)
mul-alpha-coord a b =
  trans (cong (λ p → p *gf9 (a , b)) alpha-pair)
    (cong₂ _,_
      (trans (cong₂ (λ u v → u ⊕ negate v) (⊗-zeroˡ a) (⊗-identityˡ b))
             (⊕-identityˡ (negate b)))
      (trans (cong₂ _⊕_ (⊗-zeroˡ b) (⊗-identityˡ a)) (⊕-identityˡ a)))

-- 乘 α 的坐标作用 (每坐标 (a,b) ↦ (neg b, a))
-- 经 alpha-mul-is-scalar 转到标量作用, 避免展开 *F 的高次项
rot90-coord : ∀ x₀ x₁ x₂ →
  rot90 (x₀ , x₁ , x₂) ≡
  ((negate (proj₂ x₀) , proj₁ x₀) ,
   (negate (proj₂ x₁) , proj₁ x₁) ,
   (negate (proj₂ x₂) , proj₁ x₂))
rot90-coord x₀ x₁ x₂ =
  trans (alpha-mul-is-scalar (x₀ , x₁ , x₂))
        (cong-triple (mul-alpha-coord (proj₁ x₀) (proj₂ x₀))
                     (mul-alpha-coord (proj₁ x₁) (proj₂ x₁))
                     (mul-alpha-coord (proj₁ x₂) (proj₂ x₂)))

-- α² = -1 (GF9 内蕴): rot90 两次 = 取反
alphaF-squared : alphaF *F alphaF ≡ embed-9 (alpha *gf9 alpha)
alphaF-squared = trans (scalar-mul alpha alphaF) (sym (embed-9-mul alpha alpha))

-- rot90 由标量作用给出 (相位旋转 = 乘 α)
rot90-is-scalar : ∀ x → rot90 x ≡ alpha *s x
rot90-is-scalar x = alpha-mul-is-scalar x

-- 标量作用的复合 = 标量乘积: c *s (d *s x) ≡ (c *gf9 d) *s x
scalar-assoc : ∀ c d x → c *s (d *s x) ≡ (c *gf9 d) *s x
scalar-assoc c d (x₀ , x₁ , x₂) =
  cong-triple (sym (*gf9-assoc c d x₀))
              (sym (*gf9-assoc c d x₁))
              (sym (*gf9-assoc c d x₂))

-- α⁴ 标量系数 = 1
alpha4-coef : ((alpha *gf9 alpha) *gf9 (alpha *gf9 alpha)) ≡ gf9-one
alpha4-coef = alpha-powers-4

-- α² = -1 (GF9): α² 乘任意 c = 取反 c
neg9 : GF9 → GF9
neg9 (a , b) = (negate a , negate b)

alpha2-mul : ∀ c → (alpha *gf9 alpha) *gf9 c ≡ neg9 c
alpha2-mul (a , b) =
  trans (cong (λ u → u *gf9 (a , b)) alpha-squared)
    (cong₂ _,_
      (trans (cong₂ (λ u v → u ⊕ negate v) (two-mul a) (⊗-zeroˡ b))
             (⊕-identityʳ (negate a)))
      (trans (cong₂ _⊕_ (two-mul b) (⊗-zeroˡ a)) (⊕-identityʳ (negate b))))
  where
    two-mul : ∀ x → T₂ ⊗ x ≡ negate x
    two-mul T₀ = refl
    two-mul T₁ = refl
    two-mul T₂ = refl

-- 标量作用 α²: 逐坐标取反
alpha2-scalar : ∀ x → (alpha *gf9 alpha) *s x ≡ negF x
alpha2-scalar (x₀ , x₁ , x₂) =
  cong-triple (alpha2-mul x₀) (alpha2-mul x₁) (alpha2-mul x₂)

-- rot90 两次 = α² 作用 = 取反
rot90² : ∀ x → rot90 (rot90 x) ≡ negF x
rot90² x =
  trans (cong rot90 (rot90-is-scalar x))
    (trans (rot90-is-scalar (alpha *s x))
      (trans (scalar-assoc alpha alpha x)
        (trans (alpha2-scalar x) refl)))

-- 取反对合: negF (negF x) = x
negF² : ∀ x → negF (negF x) ≡ x
negF² (x₀ , x₁ , x₂) =
  cong-triple (gf9-negate-invol x₀) (gf9-negate-invol x₁) (gf9-negate-invol x₂)

-- rot90⁴ = id (两次 α² 作用 = 取反两次 = 恒等)
rot90-4 : ∀ x → rot90 (rot90 (rot90 (rot90 x))) ≡ x
rot90-4 x =
  trans (cong (λ u → rot90 (rot90 u)) (rot90² x))
    (trans (rot90² (negF x)) (negF² x))

--------------------------------------------------------------------------------
-- §10. Frobenius 自同构 σ(x) = x³ (展示群特性, 阶 6)
--
-- σ 限制到 GF9 = galoisConjugate (GF9 的 Frobenius, 阶 2)
-- σ(t) = t³ = 2t + α (由 t³+t-α = 0)
-- σ(x₀ + x₁t + x₂t²) = σ(x₀) + σ(x₁)·σ(t) + σ(x₂)·σ(t)²
-- 展开坐标:
--   σ(t)   = (α, (2,0), 0)
--   σ(t)²  = (2, 1, 1) 即 2 + t + t²
--------------------------------------------------------------------------------

-- GF9 取反 (逐分量)
gf9-neg : GF9 → GF9
gf9-neg (a , b) = (negate a , negate b)

-- σ 的坐标公式
frobenius : GF729F → GF729F
frobenius (x₀ , x₁ , x₂) =
  let y₀ = galoisConjugate x₀
      y₁ = galoisConjugate x₁
      y₂ = galoisConjugate x₂
      -- y₁ · σ(t) = y₁ · (α, (2,0), 0)
      -- σ(t) 的分量: s0=α, s1=(T₂,T₀), s2=0
      s0 = alpha
      s1 = (T₂ , T₀)
      -- y₂ · σ(t)² = y₂ · ((2,0), α, 1)
  in  ((y₀ +gf9 (y₁ *gf9 s0)) +gf9 (y₂ *gf9 (T₂ , T₀))) ,
      ((y₁ *gf9 s1) +gf9 (y₂ *gf9 alpha)) ,
      y₂


--------------------------------------------------------------------------------
-- §11. 构造性域公理 (修正: refl 穷举 → 符号构造证明)
--
-- 审计发现原 frobenius-is-cube 为 729 条 refl 穷举 (暴力计算), 且缺
-- *F-distrib/char3 — 构造性证明的必要前提. 本节补齐 (复用 GF9 域公理).
--------------------------------------------------------------------------------

-- GF9 特征 3
gf9-char3 : ∀ x → ((x +gf9 x) +gf9 x) ≡ gf9-zero
gf9-char3 (a , b) = cong₂ _,_ (trit-char3 a) (trit-char3 b)
  where
    trit-char3 : ∀ t → ((t ⊕ t) ⊕ t) ≡ T₀
    trit-char3 T₀ = refl
    trit-char3 T₁ = refl
    trit-char3 T₂ = refl

+F-char3 : ∀ x → ((x +F x) +F x) ≡ gf729F-zero
+F-char3 (x₀ , x₁ , x₂) =
  cong-triple (gf9-char3 x₀) (gf9-char3 x₁) (gf9-char3 x₂)

-- 取反分配 (GF9)
gf9-neg-add : ∀ x y → gf9-negate (x +gf9 y) ≡ gf9-negate x +gf9 gf9-negate y
gf9-neg-add (a , b) (c , d) = cong₂ _,_ (negate-⊕ a c) (negate-⊕ b d)

-- GF9 取反 = 乘 (-1) (结构根据: -(x) = (-1)·x, 域乘法)
gf9-neg-is-mul : ∀ x → gf9-negate x ≡ (T₂ , T₀) *gf9 x
gf9-neg-is-mul (a , b) =
  sym (cong₂ _,_
    (trans (cong₂ (λ u v → u ⊕ negate v) (two-mul-is-neg a) (⊗-zeroˡ b))
           (⊕-identityʳ (negate a)))
    (trans (cong ((T₂ ⊗ b) ⊕_) (⊗-zeroˡ a))
      (trans (⊕-identityʳ (T₂ ⊗ b)) (two-mul-is-neg b))))

-- -(x·y) ≡ (-x)·y  (由 -(x·y) = (-1)·(x·y) = ((-1)·x)·y = (-x)·y, 结合律)
gf9-neg-mul : ∀ x y → gf9-negate (x *gf9 y) ≡ gf9-negate x *gf9 y
gf9-neg-mul x y =
  trans (gf9-neg-is-mul (x *gf9 y))
    (trans (sym (*gf9-assoc (T₂ , T₀) x y))
           (cong (λ u → u *gf9 y) (sym (gf9-neg-is-mul x))))

-- 4 项交换
gf9-swap4 : ∀ A B C D → ((A +gf9 B) +gf9 (C +gf9 D)) ≡ ((A +gf9 C) +gf9 (B +gf9 D))
gf9-swap4 A B C D =
  trans (sym (+gf9-assoc (A +gf9 B) C D))
    (trans (cong (λ u → u +gf9 D) (+gf9-assoc A B C))
      (trans (cong (λ u → (A +gf9 u) +gf9 D) (+gf9-comm B C))
        (trans (cong (λ u → u +gf9 D) (sym (+gf9-assoc A C B)))
          (+gf9-assoc (A +gf9 C) B D))))

-- 6 项归并: ((A+B)+(C+D))+(E+F) ≡ ((A+C)+E)+((B+D)+F)
gf9-merge6 : ∀ A B C D E F →
  (((A +gf9 B) +gf9 (C +gf9 D)) +gf9 (E +gf9 F))
  ≡ (((A +gf9 C) +gf9 E) +gf9 ((B +gf9 D) +gf9 F))
gf9-merge6 A B C D E F =
  trans (cong (λ u → u +gf9 (E +gf9 F)) (gf9-swap4 A B C D))
    (gf9-swap4 (A +gf9 C) (B +gf9 D) E F)

--------------------------------------------------------------------------------
-- 卷积/约化分解 (Poly5, 度 ≤ 4)
--------------------------------------------------------------------------------

Poly5 : Set
Poly5 = GF9 × GF9 × GF9 × GF9 × GF9

-- 3×3 卷积 → 5 系数
conv : GF729F → GF729F → Poly5
conv (x₀ , x₁ , x₂) (y₀ , y₁ , y₂) =
  (x₀ *gf9 y₀) ,
  ((x₀ *gf9 y₁) +gf9 (x₁ *gf9 y₀)) ,
  (((x₀ *gf9 y₂) +gf9 (x₁ *gf9 y₁)) +gf9 (x₂ *gf9 y₀)) ,
  ((x₁ *gf9 y₂) +gf9 (x₂ *gf9 y₁)) ,
  (x₂ *gf9 y₂)

-- 约化 t³ = 2t + α, t⁴ = 2t² + αt
reduce5 : Poly5 → GF729F
reduce5 (p₀ , p₁ , p₂ , p₃ , p₄) =
  (p₀ +gf9 (p₃ *gf9 alpha)) ,
  ((p₁ +gf9 (gf9-negate p₃)) +gf9 (p₄ *gf9 alpha)) ,
  (p₂ +gf9 (gf9-negate p₄))

-- *F = reduce5 ∘ conv (定义等式)
*F-via-conv : ∀ x y → x *F y ≡ reduce5 (conv x y)
*F-via-conv x y = refl

-- Poly5 逐分量加法
infixl 6 _+p5_
_+p5_ : Poly5 → Poly5 → Poly5
(p₀ , p₁ , p₂ , p₃ , p₄) +p5 (q₀ , q₁ , q₂ , q₃ , q₄) =
  (p₀ +gf9 q₀) , (p₁ +gf9 q₁) , (p₂ +gf9 q₂) , (p₃ +gf9 q₃) , (p₄ +gf9 q₄)

cong-5 : ∀ {a₀ a₁ a₂ a₃ a₄ b₀ b₁ b₂ b₃ b₄ : GF9} →
  a₀ ≡ b₀ → a₁ ≡ b₁ → a₂ ≡ b₂ → a₃ ≡ b₃ → a₄ ≡ b₄ →
  (a₀ , a₁ , a₂ , a₃ , a₄) ≡ (b₀ , b₁ , b₂ , b₃ , b₄)
cong-5 refl refl refl refl refl = refl


-- reduce5 保持加法: r(p+q) ≡ r(p) +F r(q)
reduce5-additive : ∀ p q → reduce5 (p +p5 q) ≡ reduce5 p +F reduce5 q
reduce5-additive (p₀ , p₁ , p₂ , p₃ , p₄) (q₀ , q₁ , q₂ , q₃ , q₄) =
  cong-triple eq₀ eq₁ eq₂
  where
    eq₀ : (p₀ +gf9 q₀) +gf9 ((p₃ +gf9 q₃) *gf9 alpha)
        ≡ (p₀ +gf9 (p₃ *gf9 alpha)) +gf9 (q₀ +gf9 (q₃ *gf9 alpha))
    eq₀ = trans (cong ((p₀ +gf9 q₀) +gf9_) (*gf9-distribʳ-+gf9 p₃ q₃ alpha))
                (gf9-swap4 p₀ q₀ (p₃ *gf9 alpha) (q₃ *gf9 alpha))

    eq₁ : ((p₁ +gf9 q₁) +gf9 gf9-negate (p₃ +gf9 q₃)) +gf9 ((p₄ +gf9 q₄) *gf9 alpha)
        ≡ ((p₁ +gf9 (gf9-negate p₃)) +gf9 (p₄ *gf9 alpha))
          +gf9 ((q₁ +gf9 (gf9-negate q₃)) +gf9 (q₄ *gf9 alpha))
    eq₁ = trans (cong₂ (λ u v → ((p₁ +gf9 q₁) +gf9 u) +gf9 v)
                        (gf9-neg-add p₃ q₃)
                        (*gf9-distribʳ-+gf9 p₄ q₄ alpha))
                (trans (cong (λ u → u +gf9 ((p₄ *gf9 alpha) +gf9 (q₄ *gf9 alpha)))
                             (gf9-swap4 p₁ q₁ (gf9-negate p₃) (gf9-negate q₃)))
                       (gf9-swap4 (p₁ +gf9 gf9-negate p₃) (q₁ +gf9 gf9-negate q₃)
                                  (p₄ *gf9 alpha) (q₄ *gf9 alpha)))

    eq₂ : (p₂ +gf9 q₂) +gf9 gf9-negate (p₄ +gf9 q₄)
        ≡ (p₂ +gf9 (gf9-negate p₄)) +gf9 (q₂ +gf9 (gf9-negate q₄))
    eq₂ = trans (cong ((p₂ +gf9 q₂) +gf9_) (gf9-neg-add p₄ q₄))
                (gf9-swap4 p₂ q₂ (gf9-negate p₄) (gf9-negate q₄))

-- conv 左线性: conv x (y+z) ≡ conv x y +p5 conv x z
conv-distribˡ : ∀ x y z → conv x (y +F z) ≡ conv x y +p5 conv x z
conv-distribˡ (x₀ , x₁ , x₂) (y₀ , y₁ , y₂) (z₀ , z₁ , z₂) =
  cong-5 eq₀ eq₁ eq₂ eq₃ eq₄
  where
    eq₀ : x₀ *gf9 (y₀ +gf9 z₀) ≡ (x₀ *gf9 y₀) +gf9 (x₀ *gf9 z₀)
    eq₀ = *gf9-distribˡ-+gf9 x₀ y₀ z₀

    eq₁ : (x₀ *gf9 (y₁ +gf9 z₁)) +gf9 (x₁ *gf9 (y₀ +gf9 z₀))
        ≡ ((x₀ *gf9 y₁) +gf9 (x₁ *gf9 y₀)) +gf9 ((x₀ *gf9 z₁) +gf9 (x₁ *gf9 z₀))
    eq₁ = trans (cong₂ _+gf9_ (*gf9-distribˡ-+gf9 x₀ y₁ z₁)
                             (*gf9-distribˡ-+gf9 x₁ y₀ z₀))
                (gf9-swap4 (x₀ *gf9 y₁) (x₀ *gf9 z₁) (x₁ *gf9 y₀) (x₁ *gf9 z₀))

    eq₂ : ((x₀ *gf9 (y₂ +gf9 z₂)) +gf9 (x₁ *gf9 (y₁ +gf9 z₁))) +gf9 (x₂ *gf9 (y₀ +gf9 z₀))
        ≡ (((x₀ *gf9 y₂) +gf9 (x₁ *gf9 y₁)) +gf9 (x₂ *gf9 y₀))
          +gf9 (((x₀ *gf9 z₂) +gf9 (x₁ *gf9 z₁)) +gf9 (x₂ *gf9 z₀))
    eq₂ = trans (cong₂ (λ u v → u +gf9 v)
                        (trans (cong₂ _+gf9_ (*gf9-distribˡ-+gf9 x₀ y₂ z₂)
                                             (*gf9-distribˡ-+gf9 x₁ y₁ z₁))
                               (gf9-swap4 (x₀ *gf9 y₂) (x₀ *gf9 z₂) (x₁ *gf9 y₁) (x₁ *gf9 z₁)))
                        (*gf9-distribˡ-+gf9 x₂ y₀ z₀))
                (gf9-swap4 ((x₀ *gf9 y₂) +gf9 (x₁ *gf9 y₁)) ((x₀ *gf9 z₂) +gf9 (x₁ *gf9 z₁))
                           (x₂ *gf9 y₀) (x₂ *gf9 z₀))

    eq₃ : (x₁ *gf9 (y₂ +gf9 z₂)) +gf9 (x₂ *gf9 (y₁ +gf9 z₁))
        ≡ ((x₁ *gf9 y₂) +gf9 (x₂ *gf9 y₁)) +gf9 ((x₁ *gf9 z₂) +gf9 (x₂ *gf9 z₁))
    eq₃ = trans (cong₂ _+gf9_ (*gf9-distribˡ-+gf9 x₁ y₂ z₂)
                             (*gf9-distribˡ-+gf9 x₂ y₁ z₁))
                (gf9-swap4 (x₁ *gf9 y₂) (x₁ *gf9 z₂) (x₂ *gf9 y₁) (x₂ *gf9 z₁))

    eq₄ : x₂ *gf9 (y₂ +gf9 z₂) ≡ (x₂ *gf9 y₂) +gf9 (x₂ *gf9 z₂)
    eq₄ = *gf9-distribˡ-+gf9 x₂ y₂ z₂

-- 左分配律
*F-distribˡ : ∀ x y z → x *F (y +F z) ≡ (x *F y) +F (x *F z)
*F-distribˡ x y z =
  trans (*F-via-conv x (y +F z))
  (trans (cong reduce5 (conv-distribˡ x y z))
  (trans (reduce5-additive (conv x y) (conv x z))
         (cong₂ _+F_ (sym (*F-via-conv x y)) (sym (*F-via-conv x z)))))

-- 显式类型的 +F 同余: 裸 cong₂ _+F_ 在复合项上触发 *F 展开而失败;
-- 显式标注 λ (u v : GF729F) → u +F v 则可用 (逐层剥离技巧)
cong-+F : ∀ {a b c d : GF729F} → a ≡ c → b ≡ d → (a +F b) ≡ (c +F d)
cong-+F {a} {b} {c} {d} p q = cong₂ (λ (u v : GF729F) → u +F v) p q

-- 左分配律 (复合项可用版): 用 cong-+F 替代裸 cong₂
*F-distribˡ' : ∀ x y z → x *F (y +F z) ≡ (x *F y) +F (x *F z)
*F-distribˡ' x y z =
  trans (*F-via-conv x (y +F z))
  (trans (cong reduce5 (conv-distribˡ x y z))
  (trans (reduce5-additive (conv x y) (conv x z))
         (cong-+F (sym (*F-via-conv x y)) (sym (*F-via-conv x z)))))

-- 右分配律 (由交换律 + 左分配律)
*F-distribʳ : ∀ x y z → (x +F y) *F z ≡ (x *F z) +F (y *F z)
*F-distribʳ x y z =
  trans (*F-comm (x +F y) z)
  (trans (*F-distribˡ z x y)
         (cong₂ _+F_ (*F-comm z x) (*F-comm z y)))



--------------------------------------------------------------------------------
-- §13. Frobenius 保加 (符号证明, 替代穷举)
--
-- σ(x) = y₀ + y₁·α - y₂  (分量0),  -y₁ + y₂·α  (分量1),  y₂  (分量2)
-- 其中 yᵢ = galoisConjugate xᵢ. 由 galoisConjugate-add (GF9 已证) + GF9 分配律,
-- σ 是加性的 — 无需穷举.
--------------------------------------------------------------------------------

-- 三分量同余 (GF729F 展开)
cong-F : ∀ {a₀ a₁ a₂ b₀ b₁ b₂ : GF9} →
  a₀ ≡ b₀ → a₁ ≡ b₁ → a₂ ≡ b₂ → (a₀ , a₁ , a₂) ≡ (b₀ , b₁ , b₂)
cong-F refl refl refl = refl

frobenius-add : ∀ x y → frobenius (x +F y) ≡ frobenius x +F frobenius y
frobenius-add (x₀ , x₁ , x₂) (y₀ , y₁ , y₂) =
  cong-F (eq0 x₀ x₁ x₂ y₀ y₁ y₂) (eq1 x₀ x₁ x₂ y₀ y₁ y₂)
         (galoisConjugate-add x₂ y₂)
  where
    -- σ 的 GF9 分量 (展开定义)
    σ0 : GF9 → GF9 → GF9 → GF9
    σ0 a b c = (galoisConjugate a +gf9 (galoisConjugate b *gf9 alpha))
               +gf9 (galoisConjugate c *gf9 (T₂ , T₀))
    σ1 : GF9 → GF9 → GF9 → GF9
    σ1 a b c = (galoisConjugate b *gf9 (T₂ , T₀)) +gf9 (galoisConjugate c *gf9 alpha)

    -- (A+B)·c = A·c + B·c
    distrib-r : ∀ A B c → (A +gf9 B) *gf9 c ≡ (A *gf9 c) +gf9 (B *gf9 c)
    distrib-r = *gf9-distribʳ-+gf9

    -- (a+b) + (c+d) 重排
    swap2 : ∀ a b c d → (a +gf9 b) +gf9 (c +gf9 d) ≡ (a +gf9 c) +gf9 (b +gf9 d)
    swap2 a b c d =
      trans (sym (+gf9-assoc (a +gf9 b) c d))
        (trans (cong (λ u → u +gf9 d) (+gf9-assoc a b c))
          (trans (cong (λ u → (a +gf9 u) +gf9 d) (+gf9-comm b c))
            (trans (cong (λ u → u +gf9 d) (sym (+gf9-assoc a c b)))
              (+gf9-assoc (a +gf9 c) b d))))

    eq0 : ∀ x₀ x₁ x₂ y₀ y₁ y₂ →
      σ0 (x₀ +gf9 y₀) (x₁ +gf9 y₁) (x₂ +gf9 y₂) ≡ (σ0 x₀ x₁ x₂) +gf9 (σ0 y₀ y₁ y₂)
    eq0 x₀ x₁ x₂ y₀ y₁ y₂ =
      trans (cong₂ (λ u v → (u +gf9 v) +gf9 (galoisConjugate (x₂ +gf9 y₂) *gf9 (T₂ , T₀)))
                   (galoisConjugate-add x₀ y₀)
                   (trans (cong₂ _*gf9_ (galoisConjugate-add x₁ y₁) refl)
                          (distrib-r (galoisConjugate x₁) (galoisConjugate y₁) alpha)))
        (trans (cong₂ _+gf9_ (swap2 (galoisConjugate x₀) (galoisConjugate y₀)
                                    (galoisConjugate x₁ *gf9 alpha)
                                    (galoisConjugate y₁ *gf9 alpha))
                               (trans (cong₂ _*gf9_ (galoisConjugate-add x₂ y₂) refl)
                                      (distrib-r (galoisConjugate x₂) (galoisConjugate y₂) (T₂ , T₀))))
               (swap2 ((galoisConjugate x₀) +gf9 (galoisConjugate x₁ *gf9 alpha))
                      ((galoisConjugate y₀) +gf9 (galoisConjugate y₁ *gf9 alpha))
                      (galoisConjugate x₂ *gf9 (T₂ , T₀))
                      (galoisConjugate y₂ *gf9 (T₂ , T₀))))

    eq1 : ∀ x₀ x₁ x₂ y₀ y₁ y₂ →
      σ1 (x₀ +gf9 y₀) (x₁ +gf9 y₁) (x₂ +gf9 y₂) ≡ (σ1 x₀ x₁ x₂) +gf9 (σ1 y₀ y₁ y₂)
    eq1 x₀ x₁ x₂ y₀ y₁ y₂ =
      trans (cong₂ _+gf9_
                   (trans (cong₂ _*gf9_ (galoisConjugate-add x₁ y₁) refl)
                          (distrib-r (galoisConjugate x₁) (galoisConjugate y₁) (T₂ , T₀)))
                   (trans (cong₂ _*gf9_ (galoisConjugate-add x₂ y₂) refl)
                          (distrib-r (galoisConjugate x₂) (galoisConjugate y₂) alpha)))
            (swap2 (galoisConjugate x₁ *gf9 (T₂ , T₀))
                   (galoisConjugate y₁ *gf9 (T₂ , T₀))
                   (galoisConjugate x₂ *gf9 alpha)
                   (galoisConjugate y₂ *gf9 alpha))



--------------------------------------------------------------------------------
-- §14. 标量线性与构造性结合律基础
--
-- conv/reduce5 对 GF9 标量线性 → (c·x)*F y ≡ c·(x*F y).
-- 由 GF9 结合律/分配律符号证明 (逐分量).
--------------------------------------------------------------------------------

-- Poly5 标量作用
_*sp_ : GF9 → Poly5 → Poly5
c *sp (p₀ , p₁ , p₂ , p₃ , p₄) =
  (c *gf9 p₀) , (c *gf9 p₁) , (c *gf9 p₂) , (c *gf9 p₃) , (c *gf9 p₄)

-- negate(x⊗y) ≡ x⊗(negate y)
nm : ∀ x y → negate (x ⊗ y) ≡ x ⊗ (negate y)
nm x y = trans (negate-⊗ x y) (negate-⊗-comm x y)

-- negate (x ⊗ negate y) ≡ x ⊗ y
nm-u : ∀ x y → negate (x ⊗ negate y) ≡ x ⊗ y
nm-u x y = trans (nm x (negate y)) (cong (x ⊗_) (negate² y))

-- -(c·u) ≡ c·(-u)  [逐分量]
neg-mul : ∀ c u → gf9-negate (c *gf9 u) ≡ c *gf9 gf9-negate u
neg-mul (c₁ , c₂) (u₁ , u₂) =
  cong₂ _,_
    (trans (negate-⊕ (c₁ ⊗ u₁) (negate (c₂ ⊗ u₂)))
           (cong₂ _⊕_ (nm c₁ u₁)
                       (trans (negate² (c₂ ⊗ u₂)) (sym (nm-u c₂ u₂)))))
    (trans (negate-⊕ (c₁ ⊗ u₂) (c₂ ⊗ u₁))
           (cong₂ _⊕_ (nm c₁ u₂) (nm c₂ u₁)))

-- conv 保持标量: conv (c *s x) y ≡ c *sp (conv x y)
conv-scalar : ∀ c x y → conv (c *s x) y ≡ c *sp (conv x y)
conv-scalar c (x₀ , x₁ , x₂) (y₀ , y₁ , y₂) = cong-5
  (*gf9-assoc c x₀ y₀)
  (trans (cong₂ _+gf9_ (*gf9-assoc c x₀ y₁) (*gf9-assoc c x₁ y₀))
         (sym (*gf9-distribˡ-+gf9 c (x₀ *gf9 y₁) (x₁ *gf9 y₀))))
  (trans (cong₂ _+gf9_
           (trans (cong₂ _+gf9_ (*gf9-assoc c x₀ y₂) (*gf9-assoc c x₁ y₁))
                  (sym (*gf9-distribˡ-+gf9 c (x₀ *gf9 y₂) (x₁ *gf9 y₁))))
           (*gf9-assoc c x₂ y₀))
         (sym (*gf9-distribˡ-+gf9 c ((x₀ *gf9 y₂) +gf9 (x₁ *gf9 y₁)) (x₂ *gf9 y₀))))
  (trans (cong₂ _+gf9_ (*gf9-assoc c x₁ y₂) (*gf9-assoc c x₂ y₁))
         (sym (*gf9-distribˡ-+gf9 c (x₁ *gf9 y₂) (x₂ *gf9 y₁))))
  (*gf9-assoc c x₂ y₂)

-- reduce5 保持标量: reduce5 (c *sp p) ≡ c *s (reduce5 p)
reduce5-scalar : ∀ c p → reduce5 (c *sp p) ≡ c *s (reduce5 p)
reduce5-scalar c (p₀ , p₁ , p₂ , p₃ , p₄) = cong-triple
  (trans (cong ((c *gf9 p₀) +gf9_) (*gf9-assoc c p₃ alpha))
         (sym (*gf9-distribˡ-+gf9 c p₀ (p₃ *gf9 alpha))))
  (trans (cong₂ (λ u v → u +gf9 v)
            (trans (cong ((c *gf9 p₁) +gf9_) (neg-mul c p₃))
                   (sym (*gf9-distribˡ-+gf9 c p₁ (gf9-negate p₃))))
            (*gf9-assoc c p₄ alpha))
         (sym (*gf9-distribˡ-+gf9 c (p₁ +gf9 gf9-negate p₃) (p₄ *gf9 alpha))))
  (trans (cong ((c *gf9 p₂) +gf9_) (neg-mul c p₄))
         (sym (*gf9-distribˡ-+gf9 c p₂ (gf9-negate p₄))))

-- 标量抽取: (c·x)*F y ≡ c·(x*F y)
scalar-extractˡ : ∀ c x y → (c *s x) *F y ≡ c *s (x *F y)
scalar-extractˡ c x y =
  trans (cong reduce5 (conv-scalar c x y))
        (reduce5-scalar c (conv x y))

--------------------------------------------------------------------------------
-- §15. 乘法结合律 *F-assoc (构造性证明, 非穷举)
--
-- 策略: *F 对每个变元都是 GF9-线性的 (加法 + 标量), 故按基 {1, t, t²} 展开.
--   三级嵌套 linear-ext:
--     z-层 (b1,b2 基): assoc-Z  →  y-层 (b1 基): assoc-Y  →  x-层: *F-assoc
--   基三元组 27 个具体情形 (assoc-basis) 全部由 GF9 约化直接得出.
--   这是符号证明 + 有限基验证, 非 729 全域穷举.
--------------------------------------------------------------------------------

record Linear (f : GF729F → GF729F) : Set where
  field
    ladd : ∀ a b → f (a +F b) ≡ f a +F f b
    lscalar : ∀ c w → f (embed-9 c *F w) ≡ embed-9 c *F f w
open Linear
ecA : ∀ c x y → embed-9 c *F (x *F y) ≡ (embed-9 c *F x) *F y
ecA c x y = trans (sym (scalar-mul c (x *F y)))
                  (trans (sym (scalar-extractˡ c x y))
                         (cong (λ u → u *F y) (scalar-mul c x)))
-- Level 1: 基三元组 (27 refl) — 用 Basis 枚举
Basis : GF729F → Set
Basis b = (b ≡ gf729F-one) ⊎ (b ≡ t) ⊎ (b ≡ t *F t)
-- 三个基元素的 assoc (27 个具体)
assoc-basis : ∀ b1 b2 b3 → Basis b1 → Basis b2 → Basis b3 →
  ((b1 *F b2) *F b3) ≡ (b1 *F (b2 *F b3))
assoc-basis _ _ _ (inj₁ refl) (inj₁ refl) (inj₁ refl) = refl
assoc-basis _ _ _ (inj₁ refl) (inj₁ refl) (inj₂ (inj₁ refl)) = refl
assoc-basis _ _ _ (inj₁ refl) (inj₁ refl) (inj₂ (inj₂ refl)) = refl
assoc-basis _ _ _ (inj₁ refl) (inj₂ (inj₁ refl)) (inj₁ refl) = refl
assoc-basis _ _ _ (inj₁ refl) (inj₂ (inj₁ refl)) (inj₂ (inj₁ refl)) = refl
assoc-basis _ _ _ (inj₁ refl) (inj₂ (inj₁ refl)) (inj₂ (inj₂ refl)) = refl
assoc-basis _ _ _ (inj₁ refl) (inj₂ (inj₂ refl)) (inj₁ refl) = refl
assoc-basis _ _ _ (inj₁ refl) (inj₂ (inj₂ refl)) (inj₂ (inj₁ refl)) = refl
assoc-basis _ _ _ (inj₁ refl) (inj₂ (inj₂ refl)) (inj₂ (inj₂ refl)) = refl
assoc-basis _ _ _ (inj₂ (inj₁ refl)) (inj₁ refl) (inj₁ refl) = refl
assoc-basis _ _ _ (inj₂ (inj₁ refl)) (inj₁ refl) (inj₂ (inj₁ refl)) = refl
assoc-basis _ _ _ (inj₂ (inj₁ refl)) (inj₁ refl) (inj₂ (inj₂ refl)) = refl
assoc-basis _ _ _ (inj₂ (inj₁ refl)) (inj₂ (inj₁ refl)) (inj₁ refl) = refl
assoc-basis _ _ _ (inj₂ (inj₁ refl)) (inj₂ (inj₁ refl)) (inj₂ (inj₁ refl)) = refl
assoc-basis _ _ _ (inj₂ (inj₁ refl)) (inj₂ (inj₁ refl)) (inj₂ (inj₂ refl)) = refl
assoc-basis _ _ _ (inj₂ (inj₁ refl)) (inj₂ (inj₂ refl)) (inj₁ refl) = refl
assoc-basis _ _ _ (inj₂ (inj₁ refl)) (inj₂ (inj₂ refl)) (inj₂ (inj₁ refl)) = refl
assoc-basis _ _ _ (inj₂ (inj₁ refl)) (inj₂ (inj₂ refl)) (inj₂ (inj₂ refl)) = refl
assoc-basis _ _ _ (inj₂ (inj₂ refl)) (inj₁ refl) (inj₁ refl) = refl
assoc-basis _ _ _ (inj₂ (inj₂ refl)) (inj₁ refl) (inj₂ (inj₁ refl)) = refl
assoc-basis _ _ _ (inj₂ (inj₂ refl)) (inj₁ refl) (inj₂ (inj₂ refl)) = refl
assoc-basis _ _ _ (inj₂ (inj₂ refl)) (inj₂ (inj₁ refl)) (inj₁ refl) = refl
assoc-basis _ _ _ (inj₂ (inj₂ refl)) (inj₂ (inj₁ refl)) (inj₂ (inj₁ refl)) = refl
assoc-basis _ _ _ (inj₂ (inj₂ refl)) (inj₂ (inj₁ refl)) (inj₂ (inj₂ refl)) = refl
assoc-basis _ _ _ (inj₂ (inj₂ refl)) (inj₂ (inj₂ refl)) (inj₁ refl) = refl
assoc-basis _ _ _ (inj₂ (inj₂ refl)) (inj₂ (inj₂ refl)) (inj₂ (inj₁ refl)) = refl
assoc-basis _ _ _ (inj₂ (inj₂ refl)) (inj₂ (inj₂ refl)) (inj₂ (inj₂ refl)) = refl

mul-t : ∀ c → embed-9 c *F t ≡ (gf9-zero , c , gf9-zero)
mul-t c = trans (sym (scalar-mul c t))
                (cong-triple (gf9-zero-mulʳ c) (*gf9-identityʳ c) (gf9-zero-mulʳ c))
mul-t2 : ∀ c → embed-9 c *F (t *F t) ≡ (gf9-zero , gf9-zero , c)
mul-t2 c = trans (sym (scalar-mul c (t *F t)))
                 (cong-triple (gf9-zero-mulʳ c) (gf9-zero-mulʳ c) (*gf9-identityʳ c))
decomp : ∀ (x₀ x₁ x₂ : GF9) →
  (embed-9 x₀ +F ((embed-9 x₁ *F t) +F (embed-9 x₂ *F (t *F t)))) ≡ (x₀ , x₁ , x₂)
decomp x₀ x₁ x₂ =
  trans (cong₂ (λ u v → u +F v) refl
               (trans (cong₂ (λ u v → u +F v) (mul-t x₁) (mul-t2 x₂)) (inner x₁ x₂)))
        (outer x₀ x₁ x₂)
  where
    inner : ∀ x₁ x₂ → ((gf9-zero , x₁ , gf9-zero) +F (gf9-zero , gf9-zero , x₂)) ≡ (gf9-zero , x₁ , x₂)
    inner x₁ x₂ = cong-triple (+gf9-identityˡ gf9-zero) (+gf9-identityʳ x₁) (+gf9-identityˡ x₂)
    outer : ∀ x₀ x₁ x₂ → ((x₀ , gf9-zero , gf9-zero) +F (gf9-zero , x₁ , x₂)) ≡ (x₀ , x₁ , x₂)
    outer x₀ x₁ x₂ = cong-triple (+gf9-identityʳ x₀) (+gf9-identityˡ x₁) (+gf9-identityˡ x₂)



-- ============================================================
-- 三级嵌套线性扩展 → *F-assoc
-- ============================================================

-- 标量穿过左乘: x *F (embed c *F w) ≡ embed c *F (x *F w)
scalar-left : ∀ x c w → x *F (embed-9 c *F w) ≡ embed-9 c *F (x *F w)
scalar-left x c w =
  trans (*F-comm x (embed-9 c *F w))
        (trans (sym (ecA c w x))
               (cong (embed-9 c *F_) (*F-comm w x)))

-- ============================================================
-- 三级嵌套: 对 x, y, z 依次线性扩展
-- ============================================================

-- 线性映射按基展开 (f 显式)
expand3 : ∀ (f : GF729F → GF729F) → Linear f → ∀ (a b c : GF9) →
  f (a , b , c) ≡ ((embed-9 a *F f gf729F-one)
                +F ((embed-9 b *F f t) +F (embed-9 c *F f (t *F t))))
expand3 f L a b c =
  trans (cong f (sym (decomp a b c)))
    (trans (ladd L (embed-9 a) ((embed-9 b *F t) +F (embed-9 c *F (t *F t))))
           (cong₂ (λ u v → u +F v)
                  (trans (cong f (sym (*F-identityʳ (embed-9 a)))) (lscalar L a gf729F-one))
                  (trans (ladd L (embed-9 b *F t) (embed-9 c *F (t *F t)))
                         (cong₂ (λ u v → u +F v) (lscalar L b t) (lscalar L c (t *F t))))))
linear-ext3 : ∀ (f g : GF729F → GF729F) → Linear f → Linear g →
  f gf729F-one ≡ g gf729F-one → f t ≡ g t → f (t *F t) ≡ g (t *F t) →
  ∀ x → f x ≡ g x
linear-ext3 f g L L' e1 et et2 (a , b , c) =
  trans (expand3 f L a b c)
  (trans (cong₂ (λ p q → p +F q)
            (cong (λ w → embed-9 a *F w) e1)
            (cong₂ (λ p q → p +F q)
              (cong (λ w → embed-9 b *F w) et)
              (cong (λ w → embed-9 c *F w) et2)))
         (sym (expand3 g L' a b c)))

-- z-层: 对固定 b1 b2 (基), ∀ z. (b1*b2)*z ≡ b1*(b2*z)
LinZ : ∀ b1 b2 → Linear (λ z → (b1 *F b2) *F z)
LinZ b1 b2 = record
  { ladd = λ a b → *F-distribˡ (b1 *F b2) a b
  ; lscalar = λ c w → scalar-left (b1 *F b2) c w }
LinZ' : ∀ b1 b2 → Linear (λ z → b1 *F (b2 *F z))
LinZ' b1 b2 = record
  { ladd = λ a b → trans (cong (b1 *F_) (*F-distribˡ b2 a b))
                         (*F-distribˡ b1 (b2 *F a) (b2 *F b))
  ; lscalar = λ c w → trans (cong (b1 *F_) (scalar-left b2 c w))
                            (scalar-left b1 c (b2 *F w)) }
z-e1 : ∀ b1 b2 → (b1 *F b2) *F gf729F-one ≡ b1 *F (b2 *F gf729F-one)
z-e1 b1 b2 = trans (*F-identityʳ (b1 *F b2))
                    (sym (cong (b1 *F_) (*F-identityʳ b2)))

-- z-层结论: 对基元素 b1 b2, ∀ z. (b1*b2)*z ≡ b1*(b2*z)
assoc-Z : ∀ b1 b2 → Basis b1 → Basis b2 → ∀ z → (b1 *F b2) *F z ≡ b1 *F (b2 *F z)
assoc-Z b1 b2 (inj₁ r1) (inj₁ r2) z =
  linear-ext3 (λ w → (b1 *F b2) *F w) (λ w → b1 *F (b2 *F w))
              (LinZ b1 b2) (LinZ' b1 b2) (z-e1 b1 b2) z-et z-et2 z
  where
    z-et : (b1 *F b2) *F t ≡ b1 *F (b2 *F t)
    z-et = assoc-basis b1 b2 t (inj₁ r1) (inj₁ r2) (inj₂ (inj₁ refl))
    z-et2 : (b1 *F b2) *F (t *F t) ≡ b1 *F (b2 *F (t *F t))
    z-et2 = assoc-basis b1 b2 (t *F t) (inj₁ r1) (inj₁ r2) (inj₂ (inj₂ refl))
assoc-Z b1 b2 (inj₁ r1) (inj₂ (inj₁ r2)) z =
  linear-ext3 (λ w → (b1 *F b2) *F w) (λ w → b1 *F (b2 *F w))
              (LinZ b1 b2) (LinZ' b1 b2) (z-e1 b1 b2) z-et z-et2 z
  where
    z-et : (b1 *F b2) *F t ≡ b1 *F (b2 *F t)
    z-et = assoc-basis b1 b2 t (inj₁ r1) (inj₂ (inj₁ r2)) (inj₂ (inj₁ refl))
    z-et2 : (b1 *F b2) *F (t *F t) ≡ b1 *F (b2 *F (t *F t))
    z-et2 = assoc-basis b1 b2 (t *F t) (inj₁ r1) (inj₂ (inj₁ r2)) (inj₂ (inj₂ refl))
assoc-Z b1 b2 (inj₁ r1) (inj₂ (inj₂ r2)) z =
  linear-ext3 (λ w → (b1 *F b2) *F w) (λ w → b1 *F (b2 *F w))
              (LinZ b1 b2) (LinZ' b1 b2) (z-e1 b1 b2) z-et z-et2 z
  where
    z-et : (b1 *F b2) *F t ≡ b1 *F (b2 *F t)
    z-et = assoc-basis b1 b2 t (inj₁ r1) (inj₂ (inj₂ r2)) (inj₂ (inj₁ refl))
    z-et2 : (b1 *F b2) *F (t *F t) ≡ b1 *F (b2 *F (t *F t))
    z-et2 = assoc-basis b1 b2 (t *F t) (inj₁ r1) (inj₂ (inj₂ r2)) (inj₂ (inj₂ refl))
assoc-Z b1 b2 (inj₂ (inj₁ r1)) b2b z =
  linear-ext3 (λ w → (b1 *F b2) *F w) (λ w → b1 *F (b2 *F w))
              (LinZ b1 b2) (LinZ' b1 b2) (z-e1 b1 b2) z-et z-et2 z
  where
    z-et : (b1 *F b2) *F t ≡ b1 *F (b2 *F t)
    z-et = assoc-basis b1 b2 t (inj₂ (inj₁ r1)) b2b (inj₂ (inj₁ refl))
    z-et2 : (b1 *F b2) *F (t *F t) ≡ b1 *F (b2 *F (t *F t))
    z-et2 = assoc-basis b1 b2 (t *F t) (inj₂ (inj₁ r1)) b2b (inj₂ (inj₂ refl))
assoc-Z b1 b2 (inj₂ (inj₂ r1)) b2b z =
  linear-ext3 (λ w → (b1 *F b2) *F w) (λ w → b1 *F (b2 *F w))
              (LinZ b1 b2) (LinZ' b1 b2) (z-e1 b1 b2) z-et z-et2 z
  where
    z-et : (b1 *F b2) *F t ≡ b1 *F (b2 *F t)
    z-et = assoc-basis b1 b2 t (inj₂ (inj₂ r1)) b2b (inj₂ (inj₁ refl))
    z-et2 : (b1 *F b2) *F (t *F t) ≡ b1 *F (b2 *F (t *F t))
    z-et2 = assoc-basis b1 b2 (t *F t) (inj₂ (inj₂ r1)) b2b (inj₂ (inj₂ refl))


-- y-层: 固定 b1 (基), 对 y 线性扩展 → ∀ y z. (b1*y)*z ≡ b1*(y*z)
LinY : ∀ b1 z → Linear (λ y → (b1 *F y) *F z)
LinY b1 z = record
  { ladd = λ a b → trans (cong (λ u → u *F z) (*F-distribˡ b1 a b))
                         (*F-distribʳ (b1 *F a) (b1 *F b) z)
  ; lscalar = λ c w → trans (cong (λ u → u *F z) (scalar-left b1 c w))
                            (sym (ecA c (b1 *F w) z)) }
LinY' : ∀ b1 z → Linear (λ y → b1 *F (y *F z))
LinY' b1 z = record
  { ladd = λ a b → trans (cong (b1 *F_) (*F-distribʳ a b z))
                         (*F-distribˡ b1 (a *F z) (b *F z))
  ; lscalar = λ c w → trans (cong (b1 *F_) (sym (ecA c w z)))
                            (scalar-left b1 c (w *F z)) }
y-e1 : ∀ b1 z → (b1 *F gf729F-one) *F z ≡ b1 *F (gf729F-one *F z)
y-e1 b1 z = trans (cong (λ u → u *F z) (*F-identityʳ b1))
                  (trans refl (cong (b1 *F_) (sym (*F-identityˡ z))))
y-et : ∀ b1 → Basis b1 → ∀ z → (b1 *F t) *F z ≡ b1 *F (t *F z)
y-et b1 (inj₁ r1) = assoc-Z b1 t (inj₁ r1) (inj₂ (inj₁ refl))
y-et b1 (inj₂ (inj₁ r1)) = assoc-Z b1 t (inj₂ (inj₁ r1)) (inj₂ (inj₁ refl))
y-et b1 (inj₂ (inj₂ r1)) = assoc-Z b1 t (inj₂ (inj₂ r1)) (inj₂ (inj₁ refl))
y-et2 : ∀ b1 → Basis b1 → ∀ z → (b1 *F (t *F t)) *F z ≡ b1 *F ((t *F t) *F z)
y-et2 b1 (inj₁ r1) = assoc-Z b1 (t *F t) (inj₁ r1) (inj₂ (inj₂ refl))
y-et2 b1 (inj₂ (inj₁ r1)) = assoc-Z b1 (t *F t) (inj₂ (inj₁ r1)) (inj₂ (inj₂ refl))
y-et2 b1 (inj₂ (inj₂ r1)) = assoc-Z b1 (t *F t) (inj₂ (inj₂ r1)) (inj₂ (inj₂ refl))
-- y-层结论
assoc-Y : ∀ b1 → Basis b1 → ∀ y z → (b1 *F y) *F z ≡ b1 *F (y *F z)
assoc-Y b1 rb y z =
  linear-ext3 (λ w → (b1 *F w) *F z) (λ w → b1 *F (w *F z))
              (LinY b1 z) (LinY' b1 z) (y-e1 b1 z) (y-et b1 rb z) (y-et2 b1 rb z) y

-- x-层: 对 x 线性扩展 → ∀ x y z. (x*y)*z ≡ x*(y*z)  ★结合律★
LinX : ∀ y z → Linear (λ x → (x *F y) *F z)
LinX y z = record
  { ladd = λ a b → trans (cong (λ u → u *F z) (*F-distribʳ a b y))
                         (*F-distribʳ (a *F y) (b *F y) z)
  ; lscalar = λ c w → trans (cong (λ u → u *F z) (sym (ecA c w y)))
                            (trans (cong (λ u → u *F z) (sym (scalar-mul c (w *F y))))
                                   (trans (scalar-extractˡ c (w *F y) z)
                                          (scalar-mul c ((w *F y) *F z)))) }
LinX' : ∀ y z → Linear (λ x → x *F (y *F z))
LinX' y z = record
  { ladd = λ a b → *F-distribʳ a b (y *F z)
  ; lscalar = λ c w → trans (cong (λ u → u *F (y *F z)) (sym (scalar-mul c w)))
                            (trans (scalar-extractˡ c w (y *F z))
                                   (scalar-mul c (w *F (y *F z)))) }
x-e1 : ∀ y z → (gf729F-one *F y) *F z ≡ gf729F-one *F (y *F z)
x-e1 y z = trans (cong (λ u → u *F z) (*F-identityˡ y))
                  (sym (*F-identityˡ (y *F z)))
x-et : ∀ y z → (t *F y) *F z ≡ t *F (y *F z)
x-et y z = assoc-Y t (inj₂ (inj₁ refl)) y z
x-et2 : ∀ y z → ((t *F t) *F y) *F z ≡ (t *F t) *F (y *F z)
x-et2 y z = assoc-Y (t *F t) (inj₂ (inj₂ refl)) y z
-- ★ 乘法结合律 ★
*F-assoc : ∀ x y z → (x *F y) *F z ≡ x *F (y *F z)
*F-assoc x y z =
  linear-ext3 (λ w → (w *F y) *F z) (λ w → w *F (y *F z))
              (LinX y z) (LinX' y z) (x-e1 y z) (x-et y z) (x-et2 y z) x

-- σ(t) = t³ 验证 (由约化 t³ = 2t + α)
frobenius-t : frobenius t ≡ t *F (t *F t)
frobenius-t = refl



-- σ 阶 6 检验点: σ⁶(t) = t (Frobenius 轨道长度 = 6)
frobenius-t-orbit :
  frobenius (frobenius (frobenius (frobenius (frobenius (frobenius t))))) ≡ t
frobenius-t-orbit = refl

-- frobenius-is-cube: σ(x) = x·x·x (立方映射, 展示群特性)
-- 关键恒等: σ 在 GF9 上 = 立方 (galoisConjugate c ≡ c³), σ(t) = t³
-- 故 σ(x₀+x₁t+x₂t²) = x₀³ + x₁³t³ + x₂³(t³)² 由 σ 是域自同构
-- 直接以坐标展开验证 (729 case 穷举)

-- frobenius-is-cube: σ(x) = x³ (全域真定理, 729 case 穷举)
frobenius-is-cube : ∀ x → frobenius x ≡ x *F (x *F x)
frobenius-is-cube ((T₀ , T₀) , (T₀ , T₀) , (T₀ , T₀)) = refl
frobenius-is-cube ((T₀ , T₀) , (T₀ , T₀) , (T₀ , T₁)) = refl
frobenius-is-cube ((T₀ , T₀) , (T₀ , T₀) , (T₀ , T₂)) = refl
frobenius-is-cube ((T₀ , T₀) , (T₀ , T₀) , (T₁ , T₀)) = refl
frobenius-is-cube ((T₀ , T₀) , (T₀ , T₀) , (T₁ , T₁)) = refl
frobenius-is-cube ((T₀ , T₀) , (T₀ , T₀) , (T₁ , T₂)) = refl
frobenius-is-cube ((T₀ , T₀) , (T₀ , T₀) , (T₂ , T₀)) = refl
frobenius-is-cube ((T₀ , T₀) , (T₀ , T₀) , (T₂ , T₁)) = refl
frobenius-is-cube ((T₀ , T₀) , (T₀ , T₀) , (T₂ , T₂)) = refl
frobenius-is-cube ((T₀ , T₀) , (T₀ , T₁) , (T₀ , T₀)) = refl
frobenius-is-cube ((T₀ , T₀) , (T₀ , T₁) , (T₀ , T₁)) = refl
frobenius-is-cube ((T₀ , T₀) , (T₀ , T₁) , (T₀ , T₂)) = refl
frobenius-is-cube ((T₀ , T₀) , (T₀ , T₁) , (T₁ , T₀)) = refl
frobenius-is-cube ((T₀ , T₀) , (T₀ , T₁) , (T₁ , T₁)) = refl
frobenius-is-cube ((T₀ , T₀) , (T₀ , T₁) , (T₁ , T₂)) = refl
frobenius-is-cube ((T₀ , T₀) , (T₀ , T₁) , (T₂ , T₀)) = refl
frobenius-is-cube ((T₀ , T₀) , (T₀ , T₁) , (T₂ , T₁)) = refl
frobenius-is-cube ((T₀ , T₀) , (T₀ , T₁) , (T₂ , T₂)) = refl
frobenius-is-cube ((T₀ , T₀) , (T₀ , T₂) , (T₀ , T₀)) = refl
frobenius-is-cube ((T₀ , T₀) , (T₀ , T₂) , (T₀ , T₁)) = refl
frobenius-is-cube ((T₀ , T₀) , (T₀ , T₂) , (T₀ , T₂)) = refl
frobenius-is-cube ((T₀ , T₀) , (T₀ , T₂) , (T₁ , T₀)) = refl
frobenius-is-cube ((T₀ , T₀) , (T₀ , T₂) , (T₁ , T₁)) = refl
frobenius-is-cube ((T₀ , T₀) , (T₀ , T₂) , (T₁ , T₂)) = refl
frobenius-is-cube ((T₀ , T₀) , (T₀ , T₂) , (T₂ , T₀)) = refl
frobenius-is-cube ((T₀ , T₀) , (T₀ , T₂) , (T₂ , T₁)) = refl
frobenius-is-cube ((T₀ , T₀) , (T₀ , T₂) , (T₂ , T₂)) = refl
frobenius-is-cube ((T₀ , T₀) , (T₁ , T₀) , (T₀ , T₀)) = refl
frobenius-is-cube ((T₀ , T₀) , (T₁ , T₀) , (T₀ , T₁)) = refl
frobenius-is-cube ((T₀ , T₀) , (T₁ , T₀) , (T₀ , T₂)) = refl
frobenius-is-cube ((T₀ , T₀) , (T₁ , T₀) , (T₁ , T₀)) = refl
frobenius-is-cube ((T₀ , T₀) , (T₁ , T₀) , (T₁ , T₁)) = refl
frobenius-is-cube ((T₀ , T₀) , (T₁ , T₀) , (T₁ , T₂)) = refl
frobenius-is-cube ((T₀ , T₀) , (T₁ , T₀) , (T₂ , T₀)) = refl
frobenius-is-cube ((T₀ , T₀) , (T₁ , T₀) , (T₂ , T₁)) = refl
frobenius-is-cube ((T₀ , T₀) , (T₁ , T₀) , (T₂ , T₂)) = refl
frobenius-is-cube ((T₀ , T₀) , (T₁ , T₁) , (T₀ , T₀)) = refl
frobenius-is-cube ((T₀ , T₀) , (T₁ , T₁) , (T₀ , T₁)) = refl
frobenius-is-cube ((T₀ , T₀) , (T₁ , T₁) , (T₀ , T₂)) = refl
frobenius-is-cube ((T₀ , T₀) , (T₁ , T₁) , (T₁ , T₀)) = refl
frobenius-is-cube ((T₀ , T₀) , (T₁ , T₁) , (T₁ , T₁)) = refl
frobenius-is-cube ((T₀ , T₀) , (T₁ , T₁) , (T₁ , T₂)) = refl
frobenius-is-cube ((T₀ , T₀) , (T₁ , T₁) , (T₂ , T₀)) = refl
frobenius-is-cube ((T₀ , T₀) , (T₁ , T₁) , (T₂ , T₁)) = refl
frobenius-is-cube ((T₀ , T₀) , (T₁ , T₁) , (T₂ , T₂)) = refl
frobenius-is-cube ((T₀ , T₀) , (T₁ , T₂) , (T₀ , T₀)) = refl
frobenius-is-cube ((T₀ , T₀) , (T₁ , T₂) , (T₀ , T₁)) = refl
frobenius-is-cube ((T₀ , T₀) , (T₁ , T₂) , (T₀ , T₂)) = refl
frobenius-is-cube ((T₀ , T₀) , (T₁ , T₂) , (T₁ , T₀)) = refl
frobenius-is-cube ((T₀ , T₀) , (T₁ , T₂) , (T₁ , T₁)) = refl
frobenius-is-cube ((T₀ , T₀) , (T₁ , T₂) , (T₁ , T₂)) = refl
frobenius-is-cube ((T₀ , T₀) , (T₁ , T₂) , (T₂ , T₀)) = refl
frobenius-is-cube ((T₀ , T₀) , (T₁ , T₂) , (T₂ , T₁)) = refl
frobenius-is-cube ((T₀ , T₀) , (T₁ , T₂) , (T₂ , T₂)) = refl
frobenius-is-cube ((T₀ , T₀) , (T₂ , T₀) , (T₀ , T₀)) = refl
frobenius-is-cube ((T₀ , T₀) , (T₂ , T₀) , (T₀ , T₁)) = refl
frobenius-is-cube ((T₀ , T₀) , (T₂ , T₀) , (T₀ , T₂)) = refl
frobenius-is-cube ((T₀ , T₀) , (T₂ , T₀) , (T₁ , T₀)) = refl
frobenius-is-cube ((T₀ , T₀) , (T₂ , T₀) , (T₁ , T₁)) = refl
frobenius-is-cube ((T₀ , T₀) , (T₂ , T₀) , (T₁ , T₂)) = refl
frobenius-is-cube ((T₀ , T₀) , (T₂ , T₀) , (T₂ , T₀)) = refl
frobenius-is-cube ((T₀ , T₀) , (T₂ , T₀) , (T₂ , T₁)) = refl
frobenius-is-cube ((T₀ , T₀) , (T₂ , T₀) , (T₂ , T₂)) = refl
frobenius-is-cube ((T₀ , T₀) , (T₂ , T₁) , (T₀ , T₀)) = refl
frobenius-is-cube ((T₀ , T₀) , (T₂ , T₁) , (T₀ , T₁)) = refl
frobenius-is-cube ((T₀ , T₀) , (T₂ , T₁) , (T₀ , T₂)) = refl
frobenius-is-cube ((T₀ , T₀) , (T₂ , T₁) , (T₁ , T₀)) = refl
frobenius-is-cube ((T₀ , T₀) , (T₂ , T₁) , (T₁ , T₁)) = refl
frobenius-is-cube ((T₀ , T₀) , (T₂ , T₁) , (T₁ , T₂)) = refl
frobenius-is-cube ((T₀ , T₀) , (T₂ , T₁) , (T₂ , T₀)) = refl
frobenius-is-cube ((T₀ , T₀) , (T₂ , T₁) , (T₂ , T₁)) = refl
frobenius-is-cube ((T₀ , T₀) , (T₂ , T₁) , (T₂ , T₂)) = refl
frobenius-is-cube ((T₀ , T₀) , (T₂ , T₂) , (T₀ , T₀)) = refl
frobenius-is-cube ((T₀ , T₀) , (T₂ , T₂) , (T₀ , T₁)) = refl
frobenius-is-cube ((T₀ , T₀) , (T₂ , T₂) , (T₀ , T₂)) = refl
frobenius-is-cube ((T₀ , T₀) , (T₂ , T₂) , (T₁ , T₀)) = refl
frobenius-is-cube ((T₀ , T₀) , (T₂ , T₂) , (T₁ , T₁)) = refl
frobenius-is-cube ((T₀ , T₀) , (T₂ , T₂) , (T₁ , T₂)) = refl
frobenius-is-cube ((T₀ , T₀) , (T₂ , T₂) , (T₂ , T₀)) = refl
frobenius-is-cube ((T₀ , T₀) , (T₂ , T₂) , (T₂ , T₁)) = refl
frobenius-is-cube ((T₀ , T₀) , (T₂ , T₂) , (T₂ , T₂)) = refl
frobenius-is-cube ((T₀ , T₁) , (T₀ , T₀) , (T₀ , T₀)) = refl
frobenius-is-cube ((T₀ , T₁) , (T₀ , T₀) , (T₀ , T₁)) = refl
frobenius-is-cube ((T₀ , T₁) , (T₀ , T₀) , (T₀ , T₂)) = refl
frobenius-is-cube ((T₀ , T₁) , (T₀ , T₀) , (T₁ , T₀)) = refl
frobenius-is-cube ((T₀ , T₁) , (T₀ , T₀) , (T₁ , T₁)) = refl
frobenius-is-cube ((T₀ , T₁) , (T₀ , T₀) , (T₁ , T₂)) = refl
frobenius-is-cube ((T₀ , T₁) , (T₀ , T₀) , (T₂ , T₀)) = refl
frobenius-is-cube ((T₀ , T₁) , (T₀ , T₀) , (T₂ , T₁)) = refl
frobenius-is-cube ((T₀ , T₁) , (T₀ , T₀) , (T₂ , T₂)) = refl
frobenius-is-cube ((T₀ , T₁) , (T₀ , T₁) , (T₀ , T₀)) = refl
frobenius-is-cube ((T₀ , T₁) , (T₀ , T₁) , (T₀ , T₁)) = refl
frobenius-is-cube ((T₀ , T₁) , (T₀ , T₁) , (T₀ , T₂)) = refl
frobenius-is-cube ((T₀ , T₁) , (T₀ , T₁) , (T₁ , T₀)) = refl
frobenius-is-cube ((T₀ , T₁) , (T₀ , T₁) , (T₁ , T₁)) = refl
frobenius-is-cube ((T₀ , T₁) , (T₀ , T₁) , (T₁ , T₂)) = refl
frobenius-is-cube ((T₀ , T₁) , (T₀ , T₁) , (T₂ , T₀)) = refl
frobenius-is-cube ((T₀ , T₁) , (T₀ , T₁) , (T₂ , T₁)) = refl
frobenius-is-cube ((T₀ , T₁) , (T₀ , T₁) , (T₂ , T₂)) = refl
frobenius-is-cube ((T₀ , T₁) , (T₀ , T₂) , (T₀ , T₀)) = refl
frobenius-is-cube ((T₀ , T₁) , (T₀ , T₂) , (T₀ , T₁)) = refl
frobenius-is-cube ((T₀ , T₁) , (T₀ , T₂) , (T₀ , T₂)) = refl
frobenius-is-cube ((T₀ , T₁) , (T₀ , T₂) , (T₁ , T₀)) = refl
frobenius-is-cube ((T₀ , T₁) , (T₀ , T₂) , (T₁ , T₁)) = refl
frobenius-is-cube ((T₀ , T₁) , (T₀ , T₂) , (T₁ , T₂)) = refl
frobenius-is-cube ((T₀ , T₁) , (T₀ , T₂) , (T₂ , T₀)) = refl
frobenius-is-cube ((T₀ , T₁) , (T₀ , T₂) , (T₂ , T₁)) = refl
frobenius-is-cube ((T₀ , T₁) , (T₀ , T₂) , (T₂ , T₂)) = refl
frobenius-is-cube ((T₀ , T₁) , (T₁ , T₀) , (T₀ , T₀)) = refl
frobenius-is-cube ((T₀ , T₁) , (T₁ , T₀) , (T₀ , T₁)) = refl
frobenius-is-cube ((T₀ , T₁) , (T₁ , T₀) , (T₀ , T₂)) = refl
frobenius-is-cube ((T₀ , T₁) , (T₁ , T₀) , (T₁ , T₀)) = refl
frobenius-is-cube ((T₀ , T₁) , (T₁ , T₀) , (T₁ , T₁)) = refl
frobenius-is-cube ((T₀ , T₁) , (T₁ , T₀) , (T₁ , T₂)) = refl
frobenius-is-cube ((T₀ , T₁) , (T₁ , T₀) , (T₂ , T₀)) = refl
frobenius-is-cube ((T₀ , T₁) , (T₁ , T₀) , (T₂ , T₁)) = refl
frobenius-is-cube ((T₀ , T₁) , (T₁ , T₀) , (T₂ , T₂)) = refl
frobenius-is-cube ((T₀ , T₁) , (T₁ , T₁) , (T₀ , T₀)) = refl
frobenius-is-cube ((T₀ , T₁) , (T₁ , T₁) , (T₀ , T₁)) = refl
frobenius-is-cube ((T₀ , T₁) , (T₁ , T₁) , (T₀ , T₂)) = refl
frobenius-is-cube ((T₀ , T₁) , (T₁ , T₁) , (T₁ , T₀)) = refl
frobenius-is-cube ((T₀ , T₁) , (T₁ , T₁) , (T₁ , T₁)) = refl
frobenius-is-cube ((T₀ , T₁) , (T₁ , T₁) , (T₁ , T₂)) = refl
frobenius-is-cube ((T₀ , T₁) , (T₁ , T₁) , (T₂ , T₀)) = refl
frobenius-is-cube ((T₀ , T₁) , (T₁ , T₁) , (T₂ , T₁)) = refl
frobenius-is-cube ((T₀ , T₁) , (T₁ , T₁) , (T₂ , T₂)) = refl
frobenius-is-cube ((T₀ , T₁) , (T₁ , T₂) , (T₀ , T₀)) = refl
frobenius-is-cube ((T₀ , T₁) , (T₁ , T₂) , (T₀ , T₁)) = refl
frobenius-is-cube ((T₀ , T₁) , (T₁ , T₂) , (T₀ , T₂)) = refl
frobenius-is-cube ((T₀ , T₁) , (T₁ , T₂) , (T₁ , T₀)) = refl
frobenius-is-cube ((T₀ , T₁) , (T₁ , T₂) , (T₁ , T₁)) = refl
frobenius-is-cube ((T₀ , T₁) , (T₁ , T₂) , (T₁ , T₂)) = refl
frobenius-is-cube ((T₀ , T₁) , (T₁ , T₂) , (T₂ , T₀)) = refl
frobenius-is-cube ((T₀ , T₁) , (T₁ , T₂) , (T₂ , T₁)) = refl
frobenius-is-cube ((T₀ , T₁) , (T₁ , T₂) , (T₂ , T₂)) = refl
frobenius-is-cube ((T₀ , T₁) , (T₂ , T₀) , (T₀ , T₀)) = refl
frobenius-is-cube ((T₀ , T₁) , (T₂ , T₀) , (T₀ , T₁)) = refl
frobenius-is-cube ((T₀ , T₁) , (T₂ , T₀) , (T₀ , T₂)) = refl
frobenius-is-cube ((T₀ , T₁) , (T₂ , T₀) , (T₁ , T₀)) = refl
frobenius-is-cube ((T₀ , T₁) , (T₂ , T₀) , (T₁ , T₁)) = refl
frobenius-is-cube ((T₀ , T₁) , (T₂ , T₀) , (T₁ , T₂)) = refl
frobenius-is-cube ((T₀ , T₁) , (T₂ , T₀) , (T₂ , T₀)) = refl
frobenius-is-cube ((T₀ , T₁) , (T₂ , T₀) , (T₂ , T₁)) = refl
frobenius-is-cube ((T₀ , T₁) , (T₂ , T₀) , (T₂ , T₂)) = refl
frobenius-is-cube ((T₀ , T₁) , (T₂ , T₁) , (T₀ , T₀)) = refl
frobenius-is-cube ((T₀ , T₁) , (T₂ , T₁) , (T₀ , T₁)) = refl
frobenius-is-cube ((T₀ , T₁) , (T₂ , T₁) , (T₀ , T₂)) = refl
frobenius-is-cube ((T₀ , T₁) , (T₂ , T₁) , (T₁ , T₀)) = refl
frobenius-is-cube ((T₀ , T₁) , (T₂ , T₁) , (T₁ , T₁)) = refl
frobenius-is-cube ((T₀ , T₁) , (T₂ , T₁) , (T₁ , T₂)) = refl
frobenius-is-cube ((T₀ , T₁) , (T₂ , T₁) , (T₂ , T₀)) = refl
frobenius-is-cube ((T₀ , T₁) , (T₂ , T₁) , (T₂ , T₁)) = refl
frobenius-is-cube ((T₀ , T₁) , (T₂ , T₁) , (T₂ , T₂)) = refl
frobenius-is-cube ((T₀ , T₁) , (T₂ , T₂) , (T₀ , T₀)) = refl
frobenius-is-cube ((T₀ , T₁) , (T₂ , T₂) , (T₀ , T₁)) = refl
frobenius-is-cube ((T₀ , T₁) , (T₂ , T₂) , (T₀ , T₂)) = refl
frobenius-is-cube ((T₀ , T₁) , (T₂ , T₂) , (T₁ , T₀)) = refl
frobenius-is-cube ((T₀ , T₁) , (T₂ , T₂) , (T₁ , T₁)) = refl
frobenius-is-cube ((T₀ , T₁) , (T₂ , T₂) , (T₁ , T₂)) = refl
frobenius-is-cube ((T₀ , T₁) , (T₂ , T₂) , (T₂ , T₀)) = refl
frobenius-is-cube ((T₀ , T₁) , (T₂ , T₂) , (T₂ , T₁)) = refl
frobenius-is-cube ((T₀ , T₁) , (T₂ , T₂) , (T₂ , T₂)) = refl
frobenius-is-cube ((T₀ , T₂) , (T₀ , T₀) , (T₀ , T₀)) = refl
frobenius-is-cube ((T₀ , T₂) , (T₀ , T₀) , (T₀ , T₁)) = refl
frobenius-is-cube ((T₀ , T₂) , (T₀ , T₀) , (T₀ , T₂)) = refl
frobenius-is-cube ((T₀ , T₂) , (T₀ , T₀) , (T₁ , T₀)) = refl
frobenius-is-cube ((T₀ , T₂) , (T₀ , T₀) , (T₁ , T₁)) = refl
frobenius-is-cube ((T₀ , T₂) , (T₀ , T₀) , (T₁ , T₂)) = refl
frobenius-is-cube ((T₀ , T₂) , (T₀ , T₀) , (T₂ , T₀)) = refl
frobenius-is-cube ((T₀ , T₂) , (T₀ , T₀) , (T₂ , T₁)) = refl
frobenius-is-cube ((T₀ , T₂) , (T₀ , T₀) , (T₂ , T₂)) = refl
frobenius-is-cube ((T₀ , T₂) , (T₀ , T₁) , (T₀ , T₀)) = refl
frobenius-is-cube ((T₀ , T₂) , (T₀ , T₁) , (T₀ , T₁)) = refl
frobenius-is-cube ((T₀ , T₂) , (T₀ , T₁) , (T₀ , T₂)) = refl
frobenius-is-cube ((T₀ , T₂) , (T₀ , T₁) , (T₁ , T₀)) = refl
frobenius-is-cube ((T₀ , T₂) , (T₀ , T₁) , (T₁ , T₁)) = refl
frobenius-is-cube ((T₀ , T₂) , (T₀ , T₁) , (T₁ , T₂)) = refl
frobenius-is-cube ((T₀ , T₂) , (T₀ , T₁) , (T₂ , T₀)) = refl
frobenius-is-cube ((T₀ , T₂) , (T₀ , T₁) , (T₂ , T₁)) = refl
frobenius-is-cube ((T₀ , T₂) , (T₀ , T₁) , (T₂ , T₂)) = refl
frobenius-is-cube ((T₀ , T₂) , (T₀ , T₂) , (T₀ , T₀)) = refl
frobenius-is-cube ((T₀ , T₂) , (T₀ , T₂) , (T₀ , T₁)) = refl
frobenius-is-cube ((T₀ , T₂) , (T₀ , T₂) , (T₀ , T₂)) = refl
frobenius-is-cube ((T₀ , T₂) , (T₀ , T₂) , (T₁ , T₀)) = refl
frobenius-is-cube ((T₀ , T₂) , (T₀ , T₂) , (T₁ , T₁)) = refl
frobenius-is-cube ((T₀ , T₂) , (T₀ , T₂) , (T₁ , T₂)) = refl
frobenius-is-cube ((T₀ , T₂) , (T₀ , T₂) , (T₂ , T₀)) = refl
frobenius-is-cube ((T₀ , T₂) , (T₀ , T₂) , (T₂ , T₁)) = refl
frobenius-is-cube ((T₀ , T₂) , (T₀ , T₂) , (T₂ , T₂)) = refl
frobenius-is-cube ((T₀ , T₂) , (T₁ , T₀) , (T₀ , T₀)) = refl
frobenius-is-cube ((T₀ , T₂) , (T₁ , T₀) , (T₀ , T₁)) = refl
frobenius-is-cube ((T₀ , T₂) , (T₁ , T₀) , (T₀ , T₂)) = refl
frobenius-is-cube ((T₀ , T₂) , (T₁ , T₀) , (T₁ , T₀)) = refl
frobenius-is-cube ((T₀ , T₂) , (T₁ , T₀) , (T₁ , T₁)) = refl
frobenius-is-cube ((T₀ , T₂) , (T₁ , T₀) , (T₁ , T₂)) = refl
frobenius-is-cube ((T₀ , T₂) , (T₁ , T₀) , (T₂ , T₀)) = refl
frobenius-is-cube ((T₀ , T₂) , (T₁ , T₀) , (T₂ , T₁)) = refl
frobenius-is-cube ((T₀ , T₂) , (T₁ , T₀) , (T₂ , T₂)) = refl
frobenius-is-cube ((T₀ , T₂) , (T₁ , T₁) , (T₀ , T₀)) = refl
frobenius-is-cube ((T₀ , T₂) , (T₁ , T₁) , (T₀ , T₁)) = refl
frobenius-is-cube ((T₀ , T₂) , (T₁ , T₁) , (T₀ , T₂)) = refl
frobenius-is-cube ((T₀ , T₂) , (T₁ , T₁) , (T₁ , T₀)) = refl
frobenius-is-cube ((T₀ , T₂) , (T₁ , T₁) , (T₁ , T₁)) = refl
frobenius-is-cube ((T₀ , T₂) , (T₁ , T₁) , (T₁ , T₂)) = refl
frobenius-is-cube ((T₀ , T₂) , (T₁ , T₁) , (T₂ , T₀)) = refl
frobenius-is-cube ((T₀ , T₂) , (T₁ , T₁) , (T₂ , T₁)) = refl
frobenius-is-cube ((T₀ , T₂) , (T₁ , T₁) , (T₂ , T₂)) = refl
frobenius-is-cube ((T₀ , T₂) , (T₁ , T₂) , (T₀ , T₀)) = refl
frobenius-is-cube ((T₀ , T₂) , (T₁ , T₂) , (T₀ , T₁)) = refl
frobenius-is-cube ((T₀ , T₂) , (T₁ , T₂) , (T₀ , T₂)) = refl
frobenius-is-cube ((T₀ , T₂) , (T₁ , T₂) , (T₁ , T₀)) = refl
frobenius-is-cube ((T₀ , T₂) , (T₁ , T₂) , (T₁ , T₁)) = refl
frobenius-is-cube ((T₀ , T₂) , (T₁ , T₂) , (T₁ , T₂)) = refl
frobenius-is-cube ((T₀ , T₂) , (T₁ , T₂) , (T₂ , T₀)) = refl
frobenius-is-cube ((T₀ , T₂) , (T₁ , T₂) , (T₂ , T₁)) = refl
frobenius-is-cube ((T₀ , T₂) , (T₁ , T₂) , (T₂ , T₂)) = refl
frobenius-is-cube ((T₀ , T₂) , (T₂ , T₀) , (T₀ , T₀)) = refl
frobenius-is-cube ((T₀ , T₂) , (T₂ , T₀) , (T₀ , T₁)) = refl
frobenius-is-cube ((T₀ , T₂) , (T₂ , T₀) , (T₀ , T₂)) = refl
frobenius-is-cube ((T₀ , T₂) , (T₂ , T₀) , (T₁ , T₀)) = refl
frobenius-is-cube ((T₀ , T₂) , (T₂ , T₀) , (T₁ , T₁)) = refl
frobenius-is-cube ((T₀ , T₂) , (T₂ , T₀) , (T₁ , T₂)) = refl
frobenius-is-cube ((T₀ , T₂) , (T₂ , T₀) , (T₂ , T₀)) = refl
frobenius-is-cube ((T₀ , T₂) , (T₂ , T₀) , (T₂ , T₁)) = refl
frobenius-is-cube ((T₀ , T₂) , (T₂ , T₀) , (T₂ , T₂)) = refl
frobenius-is-cube ((T₀ , T₂) , (T₂ , T₁) , (T₀ , T₀)) = refl
frobenius-is-cube ((T₀ , T₂) , (T₂ , T₁) , (T₀ , T₁)) = refl
frobenius-is-cube ((T₀ , T₂) , (T₂ , T₁) , (T₀ , T₂)) = refl
frobenius-is-cube ((T₀ , T₂) , (T₂ , T₁) , (T₁ , T₀)) = refl
frobenius-is-cube ((T₀ , T₂) , (T₂ , T₁) , (T₁ , T₁)) = refl
frobenius-is-cube ((T₀ , T₂) , (T₂ , T₁) , (T₁ , T₂)) = refl
frobenius-is-cube ((T₀ , T₂) , (T₂ , T₁) , (T₂ , T₀)) = refl
frobenius-is-cube ((T₀ , T₂) , (T₂ , T₁) , (T₂ , T₁)) = refl
frobenius-is-cube ((T₀ , T₂) , (T₂ , T₁) , (T₂ , T₂)) = refl
frobenius-is-cube ((T₀ , T₂) , (T₂ , T₂) , (T₀ , T₀)) = refl
frobenius-is-cube ((T₀ , T₂) , (T₂ , T₂) , (T₀ , T₁)) = refl
frobenius-is-cube ((T₀ , T₂) , (T₂ , T₂) , (T₀ , T₂)) = refl
frobenius-is-cube ((T₀ , T₂) , (T₂ , T₂) , (T₁ , T₀)) = refl
frobenius-is-cube ((T₀ , T₂) , (T₂ , T₂) , (T₁ , T₁)) = refl
frobenius-is-cube ((T₀ , T₂) , (T₂ , T₂) , (T₁ , T₂)) = refl
frobenius-is-cube ((T₀ , T₂) , (T₂ , T₂) , (T₂ , T₀)) = refl
frobenius-is-cube ((T₀ , T₂) , (T₂ , T₂) , (T₂ , T₁)) = refl
frobenius-is-cube ((T₀ , T₂) , (T₂ , T₂) , (T₂ , T₂)) = refl
frobenius-is-cube ((T₁ , T₀) , (T₀ , T₀) , (T₀ , T₀)) = refl
frobenius-is-cube ((T₁ , T₀) , (T₀ , T₀) , (T₀ , T₁)) = refl
frobenius-is-cube ((T₁ , T₀) , (T₀ , T₀) , (T₀ , T₂)) = refl
frobenius-is-cube ((T₁ , T₀) , (T₀ , T₀) , (T₁ , T₀)) = refl
frobenius-is-cube ((T₁ , T₀) , (T₀ , T₀) , (T₁ , T₁)) = refl
frobenius-is-cube ((T₁ , T₀) , (T₀ , T₀) , (T₁ , T₂)) = refl
frobenius-is-cube ((T₁ , T₀) , (T₀ , T₀) , (T₂ , T₀)) = refl
frobenius-is-cube ((T₁ , T₀) , (T₀ , T₀) , (T₂ , T₁)) = refl
frobenius-is-cube ((T₁ , T₀) , (T₀ , T₀) , (T₂ , T₂)) = refl
frobenius-is-cube ((T₁ , T₀) , (T₀ , T₁) , (T₀ , T₀)) = refl
frobenius-is-cube ((T₁ , T₀) , (T₀ , T₁) , (T₀ , T₁)) = refl
frobenius-is-cube ((T₁ , T₀) , (T₀ , T₁) , (T₀ , T₂)) = refl
frobenius-is-cube ((T₁ , T₀) , (T₀ , T₁) , (T₁ , T₀)) = refl
frobenius-is-cube ((T₁ , T₀) , (T₀ , T₁) , (T₁ , T₁)) = refl
frobenius-is-cube ((T₁ , T₀) , (T₀ , T₁) , (T₁ , T₂)) = refl
frobenius-is-cube ((T₁ , T₀) , (T₀ , T₁) , (T₂ , T₀)) = refl
frobenius-is-cube ((T₁ , T₀) , (T₀ , T₁) , (T₂ , T₁)) = refl
frobenius-is-cube ((T₁ , T₀) , (T₀ , T₁) , (T₂ , T₂)) = refl
frobenius-is-cube ((T₁ , T₀) , (T₀ , T₂) , (T₀ , T₀)) = refl
frobenius-is-cube ((T₁ , T₀) , (T₀ , T₂) , (T₀ , T₁)) = refl
frobenius-is-cube ((T₁ , T₀) , (T₀ , T₂) , (T₀ , T₂)) = refl
frobenius-is-cube ((T₁ , T₀) , (T₀ , T₂) , (T₁ , T₀)) = refl
frobenius-is-cube ((T₁ , T₀) , (T₀ , T₂) , (T₁ , T₁)) = refl
frobenius-is-cube ((T₁ , T₀) , (T₀ , T₂) , (T₁ , T₂)) = refl
frobenius-is-cube ((T₁ , T₀) , (T₀ , T₂) , (T₂ , T₀)) = refl
frobenius-is-cube ((T₁ , T₀) , (T₀ , T₂) , (T₂ , T₁)) = refl
frobenius-is-cube ((T₁ , T₀) , (T₀ , T₂) , (T₂ , T₂)) = refl
frobenius-is-cube ((T₁ , T₀) , (T₁ , T₀) , (T₀ , T₀)) = refl
frobenius-is-cube ((T₁ , T₀) , (T₁ , T₀) , (T₀ , T₁)) = refl
frobenius-is-cube ((T₁ , T₀) , (T₁ , T₀) , (T₀ , T₂)) = refl
frobenius-is-cube ((T₁ , T₀) , (T₁ , T₀) , (T₁ , T₀)) = refl
frobenius-is-cube ((T₁ , T₀) , (T₁ , T₀) , (T₁ , T₁)) = refl
frobenius-is-cube ((T₁ , T₀) , (T₁ , T₀) , (T₁ , T₂)) = refl
frobenius-is-cube ((T₁ , T₀) , (T₁ , T₀) , (T₂ , T₀)) = refl
frobenius-is-cube ((T₁ , T₀) , (T₁ , T₀) , (T₂ , T₁)) = refl
frobenius-is-cube ((T₁ , T₀) , (T₁ , T₀) , (T₂ , T₂)) = refl
frobenius-is-cube ((T₁ , T₀) , (T₁ , T₁) , (T₀ , T₀)) = refl
frobenius-is-cube ((T₁ , T₀) , (T₁ , T₁) , (T₀ , T₁)) = refl
frobenius-is-cube ((T₁ , T₀) , (T₁ , T₁) , (T₀ , T₂)) = refl
frobenius-is-cube ((T₁ , T₀) , (T₁ , T₁) , (T₁ , T₀)) = refl
frobenius-is-cube ((T₁ , T₀) , (T₁ , T₁) , (T₁ , T₁)) = refl
frobenius-is-cube ((T₁ , T₀) , (T₁ , T₁) , (T₁ , T₂)) = refl
frobenius-is-cube ((T₁ , T₀) , (T₁ , T₁) , (T₂ , T₀)) = refl
frobenius-is-cube ((T₁ , T₀) , (T₁ , T₁) , (T₂ , T₁)) = refl
frobenius-is-cube ((T₁ , T₀) , (T₁ , T₁) , (T₂ , T₂)) = refl
frobenius-is-cube ((T₁ , T₀) , (T₁ , T₂) , (T₀ , T₀)) = refl
frobenius-is-cube ((T₁ , T₀) , (T₁ , T₂) , (T₀ , T₁)) = refl
frobenius-is-cube ((T₁ , T₀) , (T₁ , T₂) , (T₀ , T₂)) = refl
frobenius-is-cube ((T₁ , T₀) , (T₁ , T₂) , (T₁ , T₀)) = refl
frobenius-is-cube ((T₁ , T₀) , (T₁ , T₂) , (T₁ , T₁)) = refl
frobenius-is-cube ((T₁ , T₀) , (T₁ , T₂) , (T₁ , T₂)) = refl
frobenius-is-cube ((T₁ , T₀) , (T₁ , T₂) , (T₂ , T₀)) = refl
frobenius-is-cube ((T₁ , T₀) , (T₁ , T₂) , (T₂ , T₁)) = refl
frobenius-is-cube ((T₁ , T₀) , (T₁ , T₂) , (T₂ , T₂)) = refl
frobenius-is-cube ((T₁ , T₀) , (T₂ , T₀) , (T₀ , T₀)) = refl
frobenius-is-cube ((T₁ , T₀) , (T₂ , T₀) , (T₀ , T₁)) = refl
frobenius-is-cube ((T₁ , T₀) , (T₂ , T₀) , (T₀ , T₂)) = refl
frobenius-is-cube ((T₁ , T₀) , (T₂ , T₀) , (T₁ , T₀)) = refl
frobenius-is-cube ((T₁ , T₀) , (T₂ , T₀) , (T₁ , T₁)) = refl
frobenius-is-cube ((T₁ , T₀) , (T₂ , T₀) , (T₁ , T₂)) = refl
frobenius-is-cube ((T₁ , T₀) , (T₂ , T₀) , (T₂ , T₀)) = refl
frobenius-is-cube ((T₁ , T₀) , (T₂ , T₀) , (T₂ , T₁)) = refl
frobenius-is-cube ((T₁ , T₀) , (T₂ , T₀) , (T₂ , T₂)) = refl
frobenius-is-cube ((T₁ , T₀) , (T₂ , T₁) , (T₀ , T₀)) = refl
frobenius-is-cube ((T₁ , T₀) , (T₂ , T₁) , (T₀ , T₁)) = refl
frobenius-is-cube ((T₁ , T₀) , (T₂ , T₁) , (T₀ , T₂)) = refl
frobenius-is-cube ((T₁ , T₀) , (T₂ , T₁) , (T₁ , T₀)) = refl
frobenius-is-cube ((T₁ , T₀) , (T₂ , T₁) , (T₁ , T₁)) = refl
frobenius-is-cube ((T₁ , T₀) , (T₂ , T₁) , (T₁ , T₂)) = refl
frobenius-is-cube ((T₁ , T₀) , (T₂ , T₁) , (T₂ , T₀)) = refl
frobenius-is-cube ((T₁ , T₀) , (T₂ , T₁) , (T₂ , T₁)) = refl
frobenius-is-cube ((T₁ , T₀) , (T₂ , T₁) , (T₂ , T₂)) = refl
frobenius-is-cube ((T₁ , T₀) , (T₂ , T₂) , (T₀ , T₀)) = refl
frobenius-is-cube ((T₁ , T₀) , (T₂ , T₂) , (T₀ , T₁)) = refl
frobenius-is-cube ((T₁ , T₀) , (T₂ , T₂) , (T₀ , T₂)) = refl
frobenius-is-cube ((T₁ , T₀) , (T₂ , T₂) , (T₁ , T₀)) = refl
frobenius-is-cube ((T₁ , T₀) , (T₂ , T₂) , (T₁ , T₁)) = refl
frobenius-is-cube ((T₁ , T₀) , (T₂ , T₂) , (T₁ , T₂)) = refl
frobenius-is-cube ((T₁ , T₀) , (T₂ , T₂) , (T₂ , T₀)) = refl
frobenius-is-cube ((T₁ , T₀) , (T₂ , T₂) , (T₂ , T₁)) = refl
frobenius-is-cube ((T₁ , T₀) , (T₂ , T₂) , (T₂ , T₂)) = refl
frobenius-is-cube ((T₁ , T₁) , (T₀ , T₀) , (T₀ , T₀)) = refl
frobenius-is-cube ((T₁ , T₁) , (T₀ , T₀) , (T₀ , T₁)) = refl
frobenius-is-cube ((T₁ , T₁) , (T₀ , T₀) , (T₀ , T₂)) = refl
frobenius-is-cube ((T₁ , T₁) , (T₀ , T₀) , (T₁ , T₀)) = refl
frobenius-is-cube ((T₁ , T₁) , (T₀ , T₀) , (T₁ , T₁)) = refl
frobenius-is-cube ((T₁ , T₁) , (T₀ , T₀) , (T₁ , T₂)) = refl
frobenius-is-cube ((T₁ , T₁) , (T₀ , T₀) , (T₂ , T₀)) = refl
frobenius-is-cube ((T₁ , T₁) , (T₀ , T₀) , (T₂ , T₁)) = refl
frobenius-is-cube ((T₁ , T₁) , (T₀ , T₀) , (T₂ , T₂)) = refl
frobenius-is-cube ((T₁ , T₁) , (T₀ , T₁) , (T₀ , T₀)) = refl
frobenius-is-cube ((T₁ , T₁) , (T₀ , T₁) , (T₀ , T₁)) = refl
frobenius-is-cube ((T₁ , T₁) , (T₀ , T₁) , (T₀ , T₂)) = refl
frobenius-is-cube ((T₁ , T₁) , (T₀ , T₁) , (T₁ , T₀)) = refl
frobenius-is-cube ((T₁ , T₁) , (T₀ , T₁) , (T₁ , T₁)) = refl
frobenius-is-cube ((T₁ , T₁) , (T₀ , T₁) , (T₁ , T₂)) = refl
frobenius-is-cube ((T₁ , T₁) , (T₀ , T₁) , (T₂ , T₀)) = refl
frobenius-is-cube ((T₁ , T₁) , (T₀ , T₁) , (T₂ , T₁)) = refl
frobenius-is-cube ((T₁ , T₁) , (T₀ , T₁) , (T₂ , T₂)) = refl
frobenius-is-cube ((T₁ , T₁) , (T₀ , T₂) , (T₀ , T₀)) = refl
frobenius-is-cube ((T₁ , T₁) , (T₀ , T₂) , (T₀ , T₁)) = refl
frobenius-is-cube ((T₁ , T₁) , (T₀ , T₂) , (T₀ , T₂)) = refl
frobenius-is-cube ((T₁ , T₁) , (T₀ , T₂) , (T₁ , T₀)) = refl
frobenius-is-cube ((T₁ , T₁) , (T₀ , T₂) , (T₁ , T₁)) = refl
frobenius-is-cube ((T₁ , T₁) , (T₀ , T₂) , (T₁ , T₂)) = refl
frobenius-is-cube ((T₁ , T₁) , (T₀ , T₂) , (T₂ , T₀)) = refl
frobenius-is-cube ((T₁ , T₁) , (T₀ , T₂) , (T₂ , T₁)) = refl
frobenius-is-cube ((T₁ , T₁) , (T₀ , T₂) , (T₂ , T₂)) = refl
frobenius-is-cube ((T₁ , T₁) , (T₁ , T₀) , (T₀ , T₀)) = refl
frobenius-is-cube ((T₁ , T₁) , (T₁ , T₀) , (T₀ , T₁)) = refl
frobenius-is-cube ((T₁ , T₁) , (T₁ , T₀) , (T₀ , T₂)) = refl
frobenius-is-cube ((T₁ , T₁) , (T₁ , T₀) , (T₁ , T₀)) = refl
frobenius-is-cube ((T₁ , T₁) , (T₁ , T₀) , (T₁ , T₁)) = refl
frobenius-is-cube ((T₁ , T₁) , (T₁ , T₀) , (T₁ , T₂)) = refl
frobenius-is-cube ((T₁ , T₁) , (T₁ , T₀) , (T₂ , T₀)) = refl
frobenius-is-cube ((T₁ , T₁) , (T₁ , T₀) , (T₂ , T₁)) = refl
frobenius-is-cube ((T₁ , T₁) , (T₁ , T₀) , (T₂ , T₂)) = refl
frobenius-is-cube ((T₁ , T₁) , (T₁ , T₁) , (T₀ , T₀)) = refl
frobenius-is-cube ((T₁ , T₁) , (T₁ , T₁) , (T₀ , T₁)) = refl
frobenius-is-cube ((T₁ , T₁) , (T₁ , T₁) , (T₀ , T₂)) = refl
frobenius-is-cube ((T₁ , T₁) , (T₁ , T₁) , (T₁ , T₀)) = refl
frobenius-is-cube ((T₁ , T₁) , (T₁ , T₁) , (T₁ , T₁)) = refl
frobenius-is-cube ((T₁ , T₁) , (T₁ , T₁) , (T₁ , T₂)) = refl
frobenius-is-cube ((T₁ , T₁) , (T₁ , T₁) , (T₂ , T₀)) = refl
frobenius-is-cube ((T₁ , T₁) , (T₁ , T₁) , (T₂ , T₁)) = refl
frobenius-is-cube ((T₁ , T₁) , (T₁ , T₁) , (T₂ , T₂)) = refl
frobenius-is-cube ((T₁ , T₁) , (T₁ , T₂) , (T₀ , T₀)) = refl
frobenius-is-cube ((T₁ , T₁) , (T₁ , T₂) , (T₀ , T₁)) = refl
frobenius-is-cube ((T₁ , T₁) , (T₁ , T₂) , (T₀ , T₂)) = refl
frobenius-is-cube ((T₁ , T₁) , (T₁ , T₂) , (T₁ , T₀)) = refl
frobenius-is-cube ((T₁ , T₁) , (T₁ , T₂) , (T₁ , T₁)) = refl
frobenius-is-cube ((T₁ , T₁) , (T₁ , T₂) , (T₁ , T₂)) = refl
frobenius-is-cube ((T₁ , T₁) , (T₁ , T₂) , (T₂ , T₀)) = refl
frobenius-is-cube ((T₁ , T₁) , (T₁ , T₂) , (T₂ , T₁)) = refl
frobenius-is-cube ((T₁ , T₁) , (T₁ , T₂) , (T₂ , T₂)) = refl
frobenius-is-cube ((T₁ , T₁) , (T₂ , T₀) , (T₀ , T₀)) = refl
frobenius-is-cube ((T₁ , T₁) , (T₂ , T₀) , (T₀ , T₁)) = refl
frobenius-is-cube ((T₁ , T₁) , (T₂ , T₀) , (T₀ , T₂)) = refl
frobenius-is-cube ((T₁ , T₁) , (T₂ , T₀) , (T₁ , T₀)) = refl
frobenius-is-cube ((T₁ , T₁) , (T₂ , T₀) , (T₁ , T₁)) = refl
frobenius-is-cube ((T₁ , T₁) , (T₂ , T₀) , (T₁ , T₂)) = refl
frobenius-is-cube ((T₁ , T₁) , (T₂ , T₀) , (T₂ , T₀)) = refl
frobenius-is-cube ((T₁ , T₁) , (T₂ , T₀) , (T₂ , T₁)) = refl
frobenius-is-cube ((T₁ , T₁) , (T₂ , T₀) , (T₂ , T₂)) = refl
frobenius-is-cube ((T₁ , T₁) , (T₂ , T₁) , (T₀ , T₀)) = refl
frobenius-is-cube ((T₁ , T₁) , (T₂ , T₁) , (T₀ , T₁)) = refl
frobenius-is-cube ((T₁ , T₁) , (T₂ , T₁) , (T₀ , T₂)) = refl
frobenius-is-cube ((T₁ , T₁) , (T₂ , T₁) , (T₁ , T₀)) = refl
frobenius-is-cube ((T₁ , T₁) , (T₂ , T₁) , (T₁ , T₁)) = refl
frobenius-is-cube ((T₁ , T₁) , (T₂ , T₁) , (T₁ , T₂)) = refl
frobenius-is-cube ((T₁ , T₁) , (T₂ , T₁) , (T₂ , T₀)) = refl
frobenius-is-cube ((T₁ , T₁) , (T₂ , T₁) , (T₂ , T₁)) = refl
frobenius-is-cube ((T₁ , T₁) , (T₂ , T₁) , (T₂ , T₂)) = refl
frobenius-is-cube ((T₁ , T₁) , (T₂ , T₂) , (T₀ , T₀)) = refl
frobenius-is-cube ((T₁ , T₁) , (T₂ , T₂) , (T₀ , T₁)) = refl
frobenius-is-cube ((T₁ , T₁) , (T₂ , T₂) , (T₀ , T₂)) = refl
frobenius-is-cube ((T₁ , T₁) , (T₂ , T₂) , (T₁ , T₀)) = refl
frobenius-is-cube ((T₁ , T₁) , (T₂ , T₂) , (T₁ , T₁)) = refl
frobenius-is-cube ((T₁ , T₁) , (T₂ , T₂) , (T₁ , T₂)) = refl
frobenius-is-cube ((T₁ , T₁) , (T₂ , T₂) , (T₂ , T₀)) = refl
frobenius-is-cube ((T₁ , T₁) , (T₂ , T₂) , (T₂ , T₁)) = refl
frobenius-is-cube ((T₁ , T₁) , (T₂ , T₂) , (T₂ , T₂)) = refl
frobenius-is-cube ((T₁ , T₂) , (T₀ , T₀) , (T₀ , T₀)) = refl
frobenius-is-cube ((T₁ , T₂) , (T₀ , T₀) , (T₀ , T₁)) = refl
frobenius-is-cube ((T₁ , T₂) , (T₀ , T₀) , (T₀ , T₂)) = refl
frobenius-is-cube ((T₁ , T₂) , (T₀ , T₀) , (T₁ , T₀)) = refl
frobenius-is-cube ((T₁ , T₂) , (T₀ , T₀) , (T₁ , T₁)) = refl
frobenius-is-cube ((T₁ , T₂) , (T₀ , T₀) , (T₁ , T₂)) = refl
frobenius-is-cube ((T₁ , T₂) , (T₀ , T₀) , (T₂ , T₀)) = refl
frobenius-is-cube ((T₁ , T₂) , (T₀ , T₀) , (T₂ , T₁)) = refl
frobenius-is-cube ((T₁ , T₂) , (T₀ , T₀) , (T₂ , T₂)) = refl
frobenius-is-cube ((T₁ , T₂) , (T₀ , T₁) , (T₀ , T₀)) = refl
frobenius-is-cube ((T₁ , T₂) , (T₀ , T₁) , (T₀ , T₁)) = refl
frobenius-is-cube ((T₁ , T₂) , (T₀ , T₁) , (T₀ , T₂)) = refl
frobenius-is-cube ((T₁ , T₂) , (T₀ , T₁) , (T₁ , T₀)) = refl
frobenius-is-cube ((T₁ , T₂) , (T₀ , T₁) , (T₁ , T₁)) = refl
frobenius-is-cube ((T₁ , T₂) , (T₀ , T₁) , (T₁ , T₂)) = refl
frobenius-is-cube ((T₁ , T₂) , (T₀ , T₁) , (T₂ , T₀)) = refl
frobenius-is-cube ((T₁ , T₂) , (T₀ , T₁) , (T₂ , T₁)) = refl
frobenius-is-cube ((T₁ , T₂) , (T₀ , T₁) , (T₂ , T₂)) = refl
frobenius-is-cube ((T₁ , T₂) , (T₀ , T₂) , (T₀ , T₀)) = refl
frobenius-is-cube ((T₁ , T₂) , (T₀ , T₂) , (T₀ , T₁)) = refl
frobenius-is-cube ((T₁ , T₂) , (T₀ , T₂) , (T₀ , T₂)) = refl
frobenius-is-cube ((T₁ , T₂) , (T₀ , T₂) , (T₁ , T₀)) = refl
frobenius-is-cube ((T₁ , T₂) , (T₀ , T₂) , (T₁ , T₁)) = refl
frobenius-is-cube ((T₁ , T₂) , (T₀ , T₂) , (T₁ , T₂)) = refl
frobenius-is-cube ((T₁ , T₂) , (T₀ , T₂) , (T₂ , T₀)) = refl
frobenius-is-cube ((T₁ , T₂) , (T₀ , T₂) , (T₂ , T₁)) = refl
frobenius-is-cube ((T₁ , T₂) , (T₀ , T₂) , (T₂ , T₂)) = refl
frobenius-is-cube ((T₁ , T₂) , (T₁ , T₀) , (T₀ , T₀)) = refl
frobenius-is-cube ((T₁ , T₂) , (T₁ , T₀) , (T₀ , T₁)) = refl
frobenius-is-cube ((T₁ , T₂) , (T₁ , T₀) , (T₀ , T₂)) = refl
frobenius-is-cube ((T₁ , T₂) , (T₁ , T₀) , (T₁ , T₀)) = refl
frobenius-is-cube ((T₁ , T₂) , (T₁ , T₀) , (T₁ , T₁)) = refl
frobenius-is-cube ((T₁ , T₂) , (T₁ , T₀) , (T₁ , T₂)) = refl
frobenius-is-cube ((T₁ , T₂) , (T₁ , T₀) , (T₂ , T₀)) = refl
frobenius-is-cube ((T₁ , T₂) , (T₁ , T₀) , (T₂ , T₁)) = refl
frobenius-is-cube ((T₁ , T₂) , (T₁ , T₀) , (T₂ , T₂)) = refl
frobenius-is-cube ((T₁ , T₂) , (T₁ , T₁) , (T₀ , T₀)) = refl
frobenius-is-cube ((T₁ , T₂) , (T₁ , T₁) , (T₀ , T₁)) = refl
frobenius-is-cube ((T₁ , T₂) , (T₁ , T₁) , (T₀ , T₂)) = refl
frobenius-is-cube ((T₁ , T₂) , (T₁ , T₁) , (T₁ , T₀)) = refl
frobenius-is-cube ((T₁ , T₂) , (T₁ , T₁) , (T₁ , T₁)) = refl
frobenius-is-cube ((T₁ , T₂) , (T₁ , T₁) , (T₁ , T₂)) = refl
frobenius-is-cube ((T₁ , T₂) , (T₁ , T₁) , (T₂ , T₀)) = refl
frobenius-is-cube ((T₁ , T₂) , (T₁ , T₁) , (T₂ , T₁)) = refl
frobenius-is-cube ((T₁ , T₂) , (T₁ , T₁) , (T₂ , T₂)) = refl
frobenius-is-cube ((T₁ , T₂) , (T₁ , T₂) , (T₀ , T₀)) = refl
frobenius-is-cube ((T₁ , T₂) , (T₁ , T₂) , (T₀ , T₁)) = refl
frobenius-is-cube ((T₁ , T₂) , (T₁ , T₂) , (T₀ , T₂)) = refl
frobenius-is-cube ((T₁ , T₂) , (T₁ , T₂) , (T₁ , T₀)) = refl
frobenius-is-cube ((T₁ , T₂) , (T₁ , T₂) , (T₁ , T₁)) = refl
frobenius-is-cube ((T₁ , T₂) , (T₁ , T₂) , (T₁ , T₂)) = refl
frobenius-is-cube ((T₁ , T₂) , (T₁ , T₂) , (T₂ , T₀)) = refl
frobenius-is-cube ((T₁ , T₂) , (T₁ , T₂) , (T₂ , T₁)) = refl
frobenius-is-cube ((T₁ , T₂) , (T₁ , T₂) , (T₂ , T₂)) = refl
frobenius-is-cube ((T₁ , T₂) , (T₂ , T₀) , (T₀ , T₀)) = refl
frobenius-is-cube ((T₁ , T₂) , (T₂ , T₀) , (T₀ , T₁)) = refl
frobenius-is-cube ((T₁ , T₂) , (T₂ , T₀) , (T₀ , T₂)) = refl
frobenius-is-cube ((T₁ , T₂) , (T₂ , T₀) , (T₁ , T₀)) = refl
frobenius-is-cube ((T₁ , T₂) , (T₂ , T₀) , (T₁ , T₁)) = refl
frobenius-is-cube ((T₁ , T₂) , (T₂ , T₀) , (T₁ , T₂)) = refl
frobenius-is-cube ((T₁ , T₂) , (T₂ , T₀) , (T₂ , T₀)) = refl
frobenius-is-cube ((T₁ , T₂) , (T₂ , T₀) , (T₂ , T₁)) = refl
frobenius-is-cube ((T₁ , T₂) , (T₂ , T₀) , (T₂ , T₂)) = refl
frobenius-is-cube ((T₁ , T₂) , (T₂ , T₁) , (T₀ , T₀)) = refl
frobenius-is-cube ((T₁ , T₂) , (T₂ , T₁) , (T₀ , T₁)) = refl
frobenius-is-cube ((T₁ , T₂) , (T₂ , T₁) , (T₀ , T₂)) = refl
frobenius-is-cube ((T₁ , T₂) , (T₂ , T₁) , (T₁ , T₀)) = refl
frobenius-is-cube ((T₁ , T₂) , (T₂ , T₁) , (T₁ , T₁)) = refl
frobenius-is-cube ((T₁ , T₂) , (T₂ , T₁) , (T₁ , T₂)) = refl
frobenius-is-cube ((T₁ , T₂) , (T₂ , T₁) , (T₂ , T₀)) = refl
frobenius-is-cube ((T₁ , T₂) , (T₂ , T₁) , (T₂ , T₁)) = refl
frobenius-is-cube ((T₁ , T₂) , (T₂ , T₁) , (T₂ , T₂)) = refl
frobenius-is-cube ((T₁ , T₂) , (T₂ , T₂) , (T₀ , T₀)) = refl
frobenius-is-cube ((T₁ , T₂) , (T₂ , T₂) , (T₀ , T₁)) = refl
frobenius-is-cube ((T₁ , T₂) , (T₂ , T₂) , (T₀ , T₂)) = refl
frobenius-is-cube ((T₁ , T₂) , (T₂ , T₂) , (T₁ , T₀)) = refl
frobenius-is-cube ((T₁ , T₂) , (T₂ , T₂) , (T₁ , T₁)) = refl
frobenius-is-cube ((T₁ , T₂) , (T₂ , T₂) , (T₁ , T₂)) = refl
frobenius-is-cube ((T₁ , T₂) , (T₂ , T₂) , (T₂ , T₀)) = refl
frobenius-is-cube ((T₁ , T₂) , (T₂ , T₂) , (T₂ , T₁)) = refl
frobenius-is-cube ((T₁ , T₂) , (T₂ , T₂) , (T₂ , T₂)) = refl
frobenius-is-cube ((T₂ , T₀) , (T₀ , T₀) , (T₀ , T₀)) = refl
frobenius-is-cube ((T₂ , T₀) , (T₀ , T₀) , (T₀ , T₁)) = refl
frobenius-is-cube ((T₂ , T₀) , (T₀ , T₀) , (T₀ , T₂)) = refl
frobenius-is-cube ((T₂ , T₀) , (T₀ , T₀) , (T₁ , T₀)) = refl
frobenius-is-cube ((T₂ , T₀) , (T₀ , T₀) , (T₁ , T₁)) = refl
frobenius-is-cube ((T₂ , T₀) , (T₀ , T₀) , (T₁ , T₂)) = refl
frobenius-is-cube ((T₂ , T₀) , (T₀ , T₀) , (T₂ , T₀)) = refl
frobenius-is-cube ((T₂ , T₀) , (T₀ , T₀) , (T₂ , T₁)) = refl
frobenius-is-cube ((T₂ , T₀) , (T₀ , T₀) , (T₂ , T₂)) = refl
frobenius-is-cube ((T₂ , T₀) , (T₀ , T₁) , (T₀ , T₀)) = refl
frobenius-is-cube ((T₂ , T₀) , (T₀ , T₁) , (T₀ , T₁)) = refl
frobenius-is-cube ((T₂ , T₀) , (T₀ , T₁) , (T₀ , T₂)) = refl
frobenius-is-cube ((T₂ , T₀) , (T₀ , T₁) , (T₁ , T₀)) = refl
frobenius-is-cube ((T₂ , T₀) , (T₀ , T₁) , (T₁ , T₁)) = refl
frobenius-is-cube ((T₂ , T₀) , (T₀ , T₁) , (T₁ , T₂)) = refl
frobenius-is-cube ((T₂ , T₀) , (T₀ , T₁) , (T₂ , T₀)) = refl
frobenius-is-cube ((T₂ , T₀) , (T₀ , T₁) , (T₂ , T₁)) = refl
frobenius-is-cube ((T₂ , T₀) , (T₀ , T₁) , (T₂ , T₂)) = refl
frobenius-is-cube ((T₂ , T₀) , (T₀ , T₂) , (T₀ , T₀)) = refl
frobenius-is-cube ((T₂ , T₀) , (T₀ , T₂) , (T₀ , T₁)) = refl
frobenius-is-cube ((T₂ , T₀) , (T₀ , T₂) , (T₀ , T₂)) = refl
frobenius-is-cube ((T₂ , T₀) , (T₀ , T₂) , (T₁ , T₀)) = refl
frobenius-is-cube ((T₂ , T₀) , (T₀ , T₂) , (T₁ , T₁)) = refl
frobenius-is-cube ((T₂ , T₀) , (T₀ , T₂) , (T₁ , T₂)) = refl
frobenius-is-cube ((T₂ , T₀) , (T₀ , T₂) , (T₂ , T₀)) = refl
frobenius-is-cube ((T₂ , T₀) , (T₀ , T₂) , (T₂ , T₁)) = refl
frobenius-is-cube ((T₂ , T₀) , (T₀ , T₂) , (T₂ , T₂)) = refl
frobenius-is-cube ((T₂ , T₀) , (T₁ , T₀) , (T₀ , T₀)) = refl
frobenius-is-cube ((T₂ , T₀) , (T₁ , T₀) , (T₀ , T₁)) = refl
frobenius-is-cube ((T₂ , T₀) , (T₁ , T₀) , (T₀ , T₂)) = refl
frobenius-is-cube ((T₂ , T₀) , (T₁ , T₀) , (T₁ , T₀)) = refl
frobenius-is-cube ((T₂ , T₀) , (T₁ , T₀) , (T₁ , T₁)) = refl
frobenius-is-cube ((T₂ , T₀) , (T₁ , T₀) , (T₁ , T₂)) = refl
frobenius-is-cube ((T₂ , T₀) , (T₁ , T₀) , (T₂ , T₀)) = refl
frobenius-is-cube ((T₂ , T₀) , (T₁ , T₀) , (T₂ , T₁)) = refl
frobenius-is-cube ((T₂ , T₀) , (T₁ , T₀) , (T₂ , T₂)) = refl
frobenius-is-cube ((T₂ , T₀) , (T₁ , T₁) , (T₀ , T₀)) = refl
frobenius-is-cube ((T₂ , T₀) , (T₁ , T₁) , (T₀ , T₁)) = refl
frobenius-is-cube ((T₂ , T₀) , (T₁ , T₁) , (T₀ , T₂)) = refl
frobenius-is-cube ((T₂ , T₀) , (T₁ , T₁) , (T₁ , T₀)) = refl
frobenius-is-cube ((T₂ , T₀) , (T₁ , T₁) , (T₁ , T₁)) = refl
frobenius-is-cube ((T₂ , T₀) , (T₁ , T₁) , (T₁ , T₂)) = refl
frobenius-is-cube ((T₂ , T₀) , (T₁ , T₁) , (T₂ , T₀)) = refl
frobenius-is-cube ((T₂ , T₀) , (T₁ , T₁) , (T₂ , T₁)) = refl
frobenius-is-cube ((T₂ , T₀) , (T₁ , T₁) , (T₂ , T₂)) = refl
frobenius-is-cube ((T₂ , T₀) , (T₁ , T₂) , (T₀ , T₀)) = refl
frobenius-is-cube ((T₂ , T₀) , (T₁ , T₂) , (T₀ , T₁)) = refl
frobenius-is-cube ((T₂ , T₀) , (T₁ , T₂) , (T₀ , T₂)) = refl
frobenius-is-cube ((T₂ , T₀) , (T₁ , T₂) , (T₁ , T₀)) = refl
frobenius-is-cube ((T₂ , T₀) , (T₁ , T₂) , (T₁ , T₁)) = refl
frobenius-is-cube ((T₂ , T₀) , (T₁ , T₂) , (T₁ , T₂)) = refl
frobenius-is-cube ((T₂ , T₀) , (T₁ , T₂) , (T₂ , T₀)) = refl
frobenius-is-cube ((T₂ , T₀) , (T₁ , T₂) , (T₂ , T₁)) = refl
frobenius-is-cube ((T₂ , T₀) , (T₁ , T₂) , (T₂ , T₂)) = refl
frobenius-is-cube ((T₂ , T₀) , (T₂ , T₀) , (T₀ , T₀)) = refl
frobenius-is-cube ((T₂ , T₀) , (T₂ , T₀) , (T₀ , T₁)) = refl
frobenius-is-cube ((T₂ , T₀) , (T₂ , T₀) , (T₀ , T₂)) = refl
frobenius-is-cube ((T₂ , T₀) , (T₂ , T₀) , (T₁ , T₀)) = refl
frobenius-is-cube ((T₂ , T₀) , (T₂ , T₀) , (T₁ , T₁)) = refl
frobenius-is-cube ((T₂ , T₀) , (T₂ , T₀) , (T₁ , T₂)) = refl
frobenius-is-cube ((T₂ , T₀) , (T₂ , T₀) , (T₂ , T₀)) = refl
frobenius-is-cube ((T₂ , T₀) , (T₂ , T₀) , (T₂ , T₁)) = refl
frobenius-is-cube ((T₂ , T₀) , (T₂ , T₀) , (T₂ , T₂)) = refl
frobenius-is-cube ((T₂ , T₀) , (T₂ , T₁) , (T₀ , T₀)) = refl
frobenius-is-cube ((T₂ , T₀) , (T₂ , T₁) , (T₀ , T₁)) = refl
frobenius-is-cube ((T₂ , T₀) , (T₂ , T₁) , (T₀ , T₂)) = refl
frobenius-is-cube ((T₂ , T₀) , (T₂ , T₁) , (T₁ , T₀)) = refl
frobenius-is-cube ((T₂ , T₀) , (T₂ , T₁) , (T₁ , T₁)) = refl
frobenius-is-cube ((T₂ , T₀) , (T₂ , T₁) , (T₁ , T₂)) = refl
frobenius-is-cube ((T₂ , T₀) , (T₂ , T₁) , (T₂ , T₀)) = refl
frobenius-is-cube ((T₂ , T₀) , (T₂ , T₁) , (T₂ , T₁)) = refl
frobenius-is-cube ((T₂ , T₀) , (T₂ , T₁) , (T₂ , T₂)) = refl
frobenius-is-cube ((T₂ , T₀) , (T₂ , T₂) , (T₀ , T₀)) = refl
frobenius-is-cube ((T₂ , T₀) , (T₂ , T₂) , (T₀ , T₁)) = refl
frobenius-is-cube ((T₂ , T₀) , (T₂ , T₂) , (T₀ , T₂)) = refl
frobenius-is-cube ((T₂ , T₀) , (T₂ , T₂) , (T₁ , T₀)) = refl
frobenius-is-cube ((T₂ , T₀) , (T₂ , T₂) , (T₁ , T₁)) = refl
frobenius-is-cube ((T₂ , T₀) , (T₂ , T₂) , (T₁ , T₂)) = refl
frobenius-is-cube ((T₂ , T₀) , (T₂ , T₂) , (T₂ , T₀)) = refl
frobenius-is-cube ((T₂ , T₀) , (T₂ , T₂) , (T₂ , T₁)) = refl
frobenius-is-cube ((T₂ , T₀) , (T₂ , T₂) , (T₂ , T₂)) = refl
frobenius-is-cube ((T₂ , T₁) , (T₀ , T₀) , (T₀ , T₀)) = refl
frobenius-is-cube ((T₂ , T₁) , (T₀ , T₀) , (T₀ , T₁)) = refl
frobenius-is-cube ((T₂ , T₁) , (T₀ , T₀) , (T₀ , T₂)) = refl
frobenius-is-cube ((T₂ , T₁) , (T₀ , T₀) , (T₁ , T₀)) = refl
frobenius-is-cube ((T₂ , T₁) , (T₀ , T₀) , (T₁ , T₁)) = refl
frobenius-is-cube ((T₂ , T₁) , (T₀ , T₀) , (T₁ , T₂)) = refl
frobenius-is-cube ((T₂ , T₁) , (T₀ , T₀) , (T₂ , T₀)) = refl
frobenius-is-cube ((T₂ , T₁) , (T₀ , T₀) , (T₂ , T₁)) = refl
frobenius-is-cube ((T₂ , T₁) , (T₀ , T₀) , (T₂ , T₂)) = refl
frobenius-is-cube ((T₂ , T₁) , (T₀ , T₁) , (T₀ , T₀)) = refl
frobenius-is-cube ((T₂ , T₁) , (T₀ , T₁) , (T₀ , T₁)) = refl
frobenius-is-cube ((T₂ , T₁) , (T₀ , T₁) , (T₀ , T₂)) = refl
frobenius-is-cube ((T₂ , T₁) , (T₀ , T₁) , (T₁ , T₀)) = refl
frobenius-is-cube ((T₂ , T₁) , (T₀ , T₁) , (T₁ , T₁)) = refl
frobenius-is-cube ((T₂ , T₁) , (T₀ , T₁) , (T₁ , T₂)) = refl
frobenius-is-cube ((T₂ , T₁) , (T₀ , T₁) , (T₂ , T₀)) = refl
frobenius-is-cube ((T₂ , T₁) , (T₀ , T₁) , (T₂ , T₁)) = refl
frobenius-is-cube ((T₂ , T₁) , (T₀ , T₁) , (T₂ , T₂)) = refl
frobenius-is-cube ((T₂ , T₁) , (T₀ , T₂) , (T₀ , T₀)) = refl
frobenius-is-cube ((T₂ , T₁) , (T₀ , T₂) , (T₀ , T₁)) = refl
frobenius-is-cube ((T₂ , T₁) , (T₀ , T₂) , (T₀ , T₂)) = refl
frobenius-is-cube ((T₂ , T₁) , (T₀ , T₂) , (T₁ , T₀)) = refl
frobenius-is-cube ((T₂ , T₁) , (T₀ , T₂) , (T₁ , T₁)) = refl
frobenius-is-cube ((T₂ , T₁) , (T₀ , T₂) , (T₁ , T₂)) = refl
frobenius-is-cube ((T₂ , T₁) , (T₀ , T₂) , (T₂ , T₀)) = refl
frobenius-is-cube ((T₂ , T₁) , (T₀ , T₂) , (T₂ , T₁)) = refl
frobenius-is-cube ((T₂ , T₁) , (T₀ , T₂) , (T₂ , T₂)) = refl
frobenius-is-cube ((T₂ , T₁) , (T₁ , T₀) , (T₀ , T₀)) = refl
frobenius-is-cube ((T₂ , T₁) , (T₁ , T₀) , (T₀ , T₁)) = refl
frobenius-is-cube ((T₂ , T₁) , (T₁ , T₀) , (T₀ , T₂)) = refl
frobenius-is-cube ((T₂ , T₁) , (T₁ , T₀) , (T₁ , T₀)) = refl
frobenius-is-cube ((T₂ , T₁) , (T₁ , T₀) , (T₁ , T₁)) = refl
frobenius-is-cube ((T₂ , T₁) , (T₁ , T₀) , (T₁ , T₂)) = refl
frobenius-is-cube ((T₂ , T₁) , (T₁ , T₀) , (T₂ , T₀)) = refl
frobenius-is-cube ((T₂ , T₁) , (T₁ , T₀) , (T₂ , T₁)) = refl
frobenius-is-cube ((T₂ , T₁) , (T₁ , T₀) , (T₂ , T₂)) = refl
frobenius-is-cube ((T₂ , T₁) , (T₁ , T₁) , (T₀ , T₀)) = refl
frobenius-is-cube ((T₂ , T₁) , (T₁ , T₁) , (T₀ , T₁)) = refl
frobenius-is-cube ((T₂ , T₁) , (T₁ , T₁) , (T₀ , T₂)) = refl
frobenius-is-cube ((T₂ , T₁) , (T₁ , T₁) , (T₁ , T₀)) = refl
frobenius-is-cube ((T₂ , T₁) , (T₁ , T₁) , (T₁ , T₁)) = refl
frobenius-is-cube ((T₂ , T₁) , (T₁ , T₁) , (T₁ , T₂)) = refl
frobenius-is-cube ((T₂ , T₁) , (T₁ , T₁) , (T₂ , T₀)) = refl
frobenius-is-cube ((T₂ , T₁) , (T₁ , T₁) , (T₂ , T₁)) = refl
frobenius-is-cube ((T₂ , T₁) , (T₁ , T₁) , (T₂ , T₂)) = refl
frobenius-is-cube ((T₂ , T₁) , (T₁ , T₂) , (T₀ , T₀)) = refl
frobenius-is-cube ((T₂ , T₁) , (T₁ , T₂) , (T₀ , T₁)) = refl
frobenius-is-cube ((T₂ , T₁) , (T₁ , T₂) , (T₀ , T₂)) = refl
frobenius-is-cube ((T₂ , T₁) , (T₁ , T₂) , (T₁ , T₀)) = refl
frobenius-is-cube ((T₂ , T₁) , (T₁ , T₂) , (T₁ , T₁)) = refl
frobenius-is-cube ((T₂ , T₁) , (T₁ , T₂) , (T₁ , T₂)) = refl
frobenius-is-cube ((T₂ , T₁) , (T₁ , T₂) , (T₂ , T₀)) = refl
frobenius-is-cube ((T₂ , T₁) , (T₁ , T₂) , (T₂ , T₁)) = refl
frobenius-is-cube ((T₂ , T₁) , (T₁ , T₂) , (T₂ , T₂)) = refl
frobenius-is-cube ((T₂ , T₁) , (T₂ , T₀) , (T₀ , T₀)) = refl
frobenius-is-cube ((T₂ , T₁) , (T₂ , T₀) , (T₀ , T₁)) = refl
frobenius-is-cube ((T₂ , T₁) , (T₂ , T₀) , (T₀ , T₂)) = refl
frobenius-is-cube ((T₂ , T₁) , (T₂ , T₀) , (T₁ , T₀)) = refl
frobenius-is-cube ((T₂ , T₁) , (T₂ , T₀) , (T₁ , T₁)) = refl
frobenius-is-cube ((T₂ , T₁) , (T₂ , T₀) , (T₁ , T₂)) = refl
frobenius-is-cube ((T₂ , T₁) , (T₂ , T₀) , (T₂ , T₀)) = refl
frobenius-is-cube ((T₂ , T₁) , (T₂ , T₀) , (T₂ , T₁)) = refl
frobenius-is-cube ((T₂ , T₁) , (T₂ , T₀) , (T₂ , T₂)) = refl
frobenius-is-cube ((T₂ , T₁) , (T₂ , T₁) , (T₀ , T₀)) = refl
frobenius-is-cube ((T₂ , T₁) , (T₂ , T₁) , (T₀ , T₁)) = refl
frobenius-is-cube ((T₂ , T₁) , (T₂ , T₁) , (T₀ , T₂)) = refl
frobenius-is-cube ((T₂ , T₁) , (T₂ , T₁) , (T₁ , T₀)) = refl
frobenius-is-cube ((T₂ , T₁) , (T₂ , T₁) , (T₁ , T₁)) = refl
frobenius-is-cube ((T₂ , T₁) , (T₂ , T₁) , (T₁ , T₂)) = refl
frobenius-is-cube ((T₂ , T₁) , (T₂ , T₁) , (T₂ , T₀)) = refl
frobenius-is-cube ((T₂ , T₁) , (T₂ , T₁) , (T₂ , T₁)) = refl
frobenius-is-cube ((T₂ , T₁) , (T₂ , T₁) , (T₂ , T₂)) = refl
frobenius-is-cube ((T₂ , T₁) , (T₂ , T₂) , (T₀ , T₀)) = refl
frobenius-is-cube ((T₂ , T₁) , (T₂ , T₂) , (T₀ , T₁)) = refl
frobenius-is-cube ((T₂ , T₁) , (T₂ , T₂) , (T₀ , T₂)) = refl
frobenius-is-cube ((T₂ , T₁) , (T₂ , T₂) , (T₁ , T₀)) = refl
frobenius-is-cube ((T₂ , T₁) , (T₂ , T₂) , (T₁ , T₁)) = refl
frobenius-is-cube ((T₂ , T₁) , (T₂ , T₂) , (T₁ , T₂)) = refl
frobenius-is-cube ((T₂ , T₁) , (T₂ , T₂) , (T₂ , T₀)) = refl
frobenius-is-cube ((T₂ , T₁) , (T₂ , T₂) , (T₂ , T₁)) = refl
frobenius-is-cube ((T₂ , T₁) , (T₂ , T₂) , (T₂ , T₂)) = refl
frobenius-is-cube ((T₂ , T₂) , (T₀ , T₀) , (T₀ , T₀)) = refl
frobenius-is-cube ((T₂ , T₂) , (T₀ , T₀) , (T₀ , T₁)) = refl
frobenius-is-cube ((T₂ , T₂) , (T₀ , T₀) , (T₀ , T₂)) = refl
frobenius-is-cube ((T₂ , T₂) , (T₀ , T₀) , (T₁ , T₀)) = refl
frobenius-is-cube ((T₂ , T₂) , (T₀ , T₀) , (T₁ , T₁)) = refl
frobenius-is-cube ((T₂ , T₂) , (T₀ , T₀) , (T₁ , T₂)) = refl
frobenius-is-cube ((T₂ , T₂) , (T₀ , T₀) , (T₂ , T₀)) = refl
frobenius-is-cube ((T₂ , T₂) , (T₀ , T₀) , (T₂ , T₁)) = refl
frobenius-is-cube ((T₂ , T₂) , (T₀ , T₀) , (T₂ , T₂)) = refl
frobenius-is-cube ((T₂ , T₂) , (T₀ , T₁) , (T₀ , T₀)) = refl
frobenius-is-cube ((T₂ , T₂) , (T₀ , T₁) , (T₀ , T₁)) = refl
frobenius-is-cube ((T₂ , T₂) , (T₀ , T₁) , (T₀ , T₂)) = refl
frobenius-is-cube ((T₂ , T₂) , (T₀ , T₁) , (T₁ , T₀)) = refl
frobenius-is-cube ((T₂ , T₂) , (T₀ , T₁) , (T₁ , T₁)) = refl
frobenius-is-cube ((T₂ , T₂) , (T₀ , T₁) , (T₁ , T₂)) = refl
frobenius-is-cube ((T₂ , T₂) , (T₀ , T₁) , (T₂ , T₀)) = refl
frobenius-is-cube ((T₂ , T₂) , (T₀ , T₁) , (T₂ , T₁)) = refl
frobenius-is-cube ((T₂ , T₂) , (T₀ , T₁) , (T₂ , T₂)) = refl
frobenius-is-cube ((T₂ , T₂) , (T₀ , T₂) , (T₀ , T₀)) = refl
frobenius-is-cube ((T₂ , T₂) , (T₀ , T₂) , (T₀ , T₁)) = refl
frobenius-is-cube ((T₂ , T₂) , (T₀ , T₂) , (T₀ , T₂)) = refl
frobenius-is-cube ((T₂ , T₂) , (T₀ , T₂) , (T₁ , T₀)) = refl
frobenius-is-cube ((T₂ , T₂) , (T₀ , T₂) , (T₁ , T₁)) = refl
frobenius-is-cube ((T₂ , T₂) , (T₀ , T₂) , (T₁ , T₂)) = refl
frobenius-is-cube ((T₂ , T₂) , (T₀ , T₂) , (T₂ , T₀)) = refl
frobenius-is-cube ((T₂ , T₂) , (T₀ , T₂) , (T₂ , T₁)) = refl
frobenius-is-cube ((T₂ , T₂) , (T₀ , T₂) , (T₂ , T₂)) = refl
frobenius-is-cube ((T₂ , T₂) , (T₁ , T₀) , (T₀ , T₀)) = refl
frobenius-is-cube ((T₂ , T₂) , (T₁ , T₀) , (T₀ , T₁)) = refl
frobenius-is-cube ((T₂ , T₂) , (T₁ , T₀) , (T₀ , T₂)) = refl
frobenius-is-cube ((T₂ , T₂) , (T₁ , T₀) , (T₁ , T₀)) = refl
frobenius-is-cube ((T₂ , T₂) , (T₁ , T₀) , (T₁ , T₁)) = refl
frobenius-is-cube ((T₂ , T₂) , (T₁ , T₀) , (T₁ , T₂)) = refl
frobenius-is-cube ((T₂ , T₂) , (T₁ , T₀) , (T₂ , T₀)) = refl
frobenius-is-cube ((T₂ , T₂) , (T₁ , T₀) , (T₂ , T₁)) = refl
frobenius-is-cube ((T₂ , T₂) , (T₁ , T₀) , (T₂ , T₂)) = refl
frobenius-is-cube ((T₂ , T₂) , (T₁ , T₁) , (T₀ , T₀)) = refl
frobenius-is-cube ((T₂ , T₂) , (T₁ , T₁) , (T₀ , T₁)) = refl
frobenius-is-cube ((T₂ , T₂) , (T₁ , T₁) , (T₀ , T₂)) = refl
frobenius-is-cube ((T₂ , T₂) , (T₁ , T₁) , (T₁ , T₀)) = refl
frobenius-is-cube ((T₂ , T₂) , (T₁ , T₁) , (T₁ , T₁)) = refl
frobenius-is-cube ((T₂ , T₂) , (T₁ , T₁) , (T₁ , T₂)) = refl
frobenius-is-cube ((T₂ , T₂) , (T₁ , T₁) , (T₂ , T₀)) = refl
frobenius-is-cube ((T₂ , T₂) , (T₁ , T₁) , (T₂ , T₁)) = refl
frobenius-is-cube ((T₂ , T₂) , (T₁ , T₁) , (T₂ , T₂)) = refl
frobenius-is-cube ((T₂ , T₂) , (T₁ , T₂) , (T₀ , T₀)) = refl
frobenius-is-cube ((T₂ , T₂) , (T₁ , T₂) , (T₀ , T₁)) = refl
frobenius-is-cube ((T₂ , T₂) , (T₁ , T₂) , (T₀ , T₂)) = refl
frobenius-is-cube ((T₂ , T₂) , (T₁ , T₂) , (T₁ , T₀)) = refl
frobenius-is-cube ((T₂ , T₂) , (T₁ , T₂) , (T₁ , T₁)) = refl
frobenius-is-cube ((T₂ , T₂) , (T₁ , T₂) , (T₁ , T₂)) = refl
frobenius-is-cube ((T₂ , T₂) , (T₁ , T₂) , (T₂ , T₀)) = refl
frobenius-is-cube ((T₂ , T₂) , (T₁ , T₂) , (T₂ , T₁)) = refl
frobenius-is-cube ((T₂ , T₂) , (T₁ , T₂) , (T₂ , T₂)) = refl
frobenius-is-cube ((T₂ , T₂) , (T₂ , T₀) , (T₀ , T₀)) = refl
frobenius-is-cube ((T₂ , T₂) , (T₂ , T₀) , (T₀ , T₁)) = refl
frobenius-is-cube ((T₂ , T₂) , (T₂ , T₀) , (T₀ , T₂)) = refl
frobenius-is-cube ((T₂ , T₂) , (T₂ , T₀) , (T₁ , T₀)) = refl
frobenius-is-cube ((T₂ , T₂) , (T₂ , T₀) , (T₁ , T₁)) = refl
frobenius-is-cube ((T₂ , T₂) , (T₂ , T₀) , (T₁ , T₂)) = refl
frobenius-is-cube ((T₂ , T₂) , (T₂ , T₀) , (T₂ , T₀)) = refl
frobenius-is-cube ((T₂ , T₂) , (T₂ , T₀) , (T₂ , T₁)) = refl
frobenius-is-cube ((T₂ , T₂) , (T₂ , T₀) , (T₂ , T₂)) = refl
frobenius-is-cube ((T₂ , T₂) , (T₂ , T₁) , (T₀ , T₀)) = refl
frobenius-is-cube ((T₂ , T₂) , (T₂ , T₁) , (T₀ , T₁)) = refl
frobenius-is-cube ((T₂ , T₂) , (T₂ , T₁) , (T₀ , T₂)) = refl
frobenius-is-cube ((T₂ , T₂) , (T₂ , T₁) , (T₁ , T₀)) = refl
frobenius-is-cube ((T₂ , T₂) , (T₂ , T₁) , (T₁ , T₁)) = refl
frobenius-is-cube ((T₂ , T₂) , (T₂ , T₁) , (T₁ , T₂)) = refl
frobenius-is-cube ((T₂ , T₂) , (T₂ , T₁) , (T₂ , T₀)) = refl
frobenius-is-cube ((T₂ , T₂) , (T₂ , T₁) , (T₂ , T₁)) = refl
frobenius-is-cube ((T₂ , T₂) , (T₂ , T₁) , (T₂ , T₂)) = refl
frobenius-is-cube ((T₂ , T₂) , (T₂ , T₂) , (T₀ , T₀)) = refl
frobenius-is-cube ((T₂ , T₂) , (T₂ , T₂) , (T₀ , T₁)) = refl
frobenius-is-cube ((T₂ , T₂) , (T₂ , T₂) , (T₀ , T₂)) = refl
frobenius-is-cube ((T₂ , T₂) , (T₂ , T₂) , (T₁ , T₀)) = refl
frobenius-is-cube ((T₂ , T₂) , (T₂ , T₂) , (T₁ , T₁)) = refl
frobenius-is-cube ((T₂ , T₂) , (T₂ , T₂) , (T₁ , T₂)) = refl
frobenius-is-cube ((T₂ , T₂) , (T₂ , T₂) , (T₂ , T₀)) = refl
frobenius-is-cube ((T₂ , T₂) , (T₂ , T₂) , (T₂ , T₁)) = refl
frobenius-is-cube ((T₂ , T₂) , (T₂ , T₂) , (T₂ , T₂)) = refl
