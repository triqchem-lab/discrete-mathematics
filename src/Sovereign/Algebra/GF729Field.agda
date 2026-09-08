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
         negate-⊕; negate-⊗; negate-⊗-negate; negate-⊗-comm;
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
  trans (cong (λ u → (u +gf9 (gf9-zero *gf9 d)) +gf9
                        gf9-negate ((gf9-zero *gf9 gf9-zero) +gf9 (gf9-zero *gf9 gf9-zero)) +gf9
                        ((gf9-zero *gf9 gf9-zero) *gf9 alpha))
               (gf9-zero-mulʳ c))
    (trans (cong (λ u → (gf9-zero +gf9 u) +gf9
                          ((gf9-zero *gf9 gf9-zero) *gf9 alpha))
                 (trans (cong gf9-negate (gf9-zero-addˡ gf9-zero)) neg-zero))
      (trans (cong (λ u → (gf9-zero +gf9 gf9-zero) +gf9 u) (gf9-zero-mulˡ alpha))
        (trans (cong (λ u → u +gf9 gf9-zero) (gf9-zero-addˡ gf9-zero))
               (gf9-zero-addʳ gf9-zero))))

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
