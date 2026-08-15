{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Physics.EntropySpinLaw
-- 渠玉芝熵旋定律的形式化核心 (0 postulate, 无洞)
--
-- 定律原文 (项目公理文档 ESB-MASS-EMERGENCE-20260306,
--   pyBitNet/docs/huntian/quantum-physics/axioms/ENTROPY_SPIN_MASS_EMERGENCE_THEORY.md):
--   熵旋矢量   S⃗ = ∇×Ψ⃗ − κ·ℋ²·n̂        (κ = 0.85, 理论值/经验常数)
--   熵旋密度张量 ρ_S^{μν} = ∂S^μ/∂x^ν − ∂S^ν/∂x^μ  (反对称)
--   质量涌现   m = ∮_C S⃗·dA⃗  (离散化: 环绕平面 k=0 的有限求和)
--   环面闭合条件 ∮_{γ₁}S·dl + ∮_{γ₂}S·dl = 2πC (未形式化, 见诚实边界)
--
-- 本模块在 (Fin 3)³ 环面 + ℚ 系数上形式化定律的可证核心:
--   §1 定律定义 (离散化): curlℚ / κ / n̂=(0,0,1) / entropySpinLaw
--   §2 ρ_S^{μν} 反对称: ρ^{xy} + ρ^{yx} ≡ 0 (符号, ℚ 环律)
--   §3 离散斯托克斯: 质量积分的旋度项消失
--      massIntegral (curlℚ Ψ) ≡ 0ℚ (望远镜消去, 符号)
--      推论: m(Ψ,H) ≡ −κ·Σℋ² — 质量积分只余 ℋ² 项
--      (公理文档 m = ∮S·dA 的代数内核: 旋度部分对环绕平面积分无贡献)
--
-- 诚实边界:
--   1) κ = 0.85 是公理文档给出的"理论值", 无公开推导 — 经验常数。
--   2) Ψ_{4320D} = Σ ψᵢe⃗ᵢ (ψᵢ = Ψ₀·cos(2πnᵢ/36)·e^{iφᵢ}) 涉及三角函数与
--      复相位, 超出 GF(3)/ℚ 域 — 未形式化; 本模块的 Ψ 是任意 ℚ 向量场。
--   3) ρ_S^{μν} 的 4320×4320 张量及其独立分量数 N=4320×4319/2 未形式化,
--      本模块只证 3×3 空间分量的反对称。
--   4) 环面闭合条件 ∮_{γ₁}S·dl + ∮_{γ₂}S·dl = 2πC 与粒子质量预测表
--      (偏差<1%) 未形式化。
--   5) 与简化模型 ρ_S(a,C) = C·0.0268/(a+1) (EntropySpin.agda) 的
--      约化关系在公理文档中是"简化模型"断言, 无推导 — 未形式化。

module Sovereign.Physics.EntropySpinLaw where

open import Data.Fin using (Fin) renaming (zero to fz; suc to fs)
open import Data.Integer using (ℤ; +_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂; module ≡-Reasoning)
open ≡-Reasoning
open import Data.Rational using (ℚ; _+_; _-_; _*_; _/_; -_; 0ℚ; 1ℚ)
open import Data.Rational.Properties
  using (+-assoc; +-comm; +-identityˡ; +-identityʳ; +-inverseʳ;
         *-distribˡ-+; neg-distrib-+)
open import Sovereign.Physics.DiscreteEMField3D using (Point3D; next)

--------------------------------------------------------------------------------
-- §0. ℚ 值场与离散差分
--------------------------------------------------------------------------------

QScalar : Set
QScalar = Point3D → ℚ

QVector : Set
QVector = Point3D → ℚ × ℚ × ℚ

dxℚ dyℚ dzℚ : QScalar → QScalar
dxℚ φ (i , j , k) = φ (next i , j , k) - φ (i , j , k)
dyℚ φ (i , j , k) = φ (i , next j , k) - φ (i , j , k)
dzℚ φ (i , j , k) = φ (i , j , next k) - φ (i , j , k)

qx qy qz : QVector → QScalar
qx A = λ q → proj₁ (A q)
qy A = λ q → proj₁ (proj₂ (A q))
qz A = λ q → proj₂ (proj₂ (A q))

curlℚ : QVector → QVector
curlℚ A p = dyℚ (qz A) p - dzℚ (qy A) p
          , dzℚ (qx A) p - dxℚ (qz A) p
          , dxℚ (qy A) p - dyℚ (qx A) p

--------------------------------------------------------------------------------
-- §1. 渠玉芝熵旋定律 (离散化定义)
--   S⃗ = ∇×Ψ⃗ − κ·ℋ²·n̂, n̂ = (0,0,1) (环绕平面法向), κ = 85/100
--------------------------------------------------------------------------------

kappaQ : ℚ
kappaQ = (+ 85) / 100   -- 0.85 (公理文档"理论值"; 经验常数, 无公开推导)

normalZ : QVector
normalZ p = (0ℚ , 0ℚ , 1ℚ)

vscale : ℚ → ℚ × ℚ × ℚ → ℚ × ℚ × ℚ
vscale s (x , y , z) = (s * x , s * y , s * z)

vsub : ℚ × ℚ × ℚ → ℚ × ℚ × ℚ → ℚ × ℚ × ℚ
vsub (x1 , y1 , z1) (x2 , y2 , z2) = (x1 - x2 , y1 - y2 , z1 - z2)

-- 熵旋定律 (离散): S(Ψ,ℋ) = curlℚ Ψ − κ·ℋ²·n̂
entropySpinLaw : QVector → QScalar → QVector
entropySpinLaw Ψ H p =
  vsub (curlℚ Ψ p) (vscale (kappaQ * (H p * H p)) (normalZ p))

--------------------------------------------------------------------------------
-- §2. 熵旋密度张量反对称: ρ^{μν} = ∂νS^μ − ∂μS^ν, ρ^{xy} + ρ^{yx} ≡ 0
--------------------------------------------------------------------------------

rhoXY rhoYX : QVector → QScalar
rhoXY A p = dyℚ (qx A) p - dxℚ (qy A) p
rhoYX A p = dxℚ (qy A) p - dyℚ (qx A) p

-- 环引理: (a−b) + (b−a) ≡ 0
sub-antisym : ∀ a b → (a - b) + (b - a) ≡ 0ℚ
sub-antisym a b = begin
  (a - b) + (b - a)
    ≡⟨ sym (+-assoc (a - b) b (- a)) ⟩
  ((a - b) + b) - a
    ≡⟨ cong (λ t → t - a) (+-assoc a (- b) b) ⟩
  (a + ((- b) + b)) - a
    ≡⟨ cong (λ t → (a + t) - a) (+-comm (- b) b) ⟩
  (a + (b - b)) - a
    ≡⟨ cong (λ t → (a + t) - a) (+-inverseʳ b) ⟩
  (a + 0ℚ) - a
    ≡⟨ cong (λ t → t - a) (+-identityʳ a) ⟩
  a - a
    ≡⟨ +-inverseʳ a ⟩
  0ℚ ∎

-- ρ_S^{μν} 反对称 (符号, 任意向量场)
rho-antisym : ∀ A p → rhoXY A p + rhoYX A p ≡ 0ℚ
rho-antisym A p = sub-antisym (dyℚ (qx A) p) (dxℚ (qy A) p)

--------------------------------------------------------------------------------
-- §3. 离散斯托克斯: 质量积分的旋度项消失
--   有限求和与望远镜引理 (ℚ 环律符号链)
--------------------------------------------------------------------------------

sum3ℚ : (Fin 3 → ℚ) → ℚ
sum3ℚ g = g fz + (g (fs fz) + g (fs (fs fz)))

-- 二项望远镜: (b−a) + (c−b) ≡ c−a
telescope2 : ∀ a b c → (b - a) + (c - b) ≡ c - a
telescope2 a b c = begin
  (b - a) + (c - b)
    ≡⟨ sym (+-assoc (b - a) c (- b)) ⟩
  ((b - a) + c) - b
    ≡⟨ cong (λ t → t - b) (+-assoc b (- a) c) ⟩
  (b + ((- a) + c)) - b
    ≡⟨ cong (λ t → (b + t) - b) (+-comm (- a) c) ⟩
  (b + (c - a)) - b
    ≡⟨ +-assoc b (c - a) (- b) ⟩
  b + ((c - a) - b)
    ≡⟨ cong (λ t → b + t) (+-assoc c (- a) (- b)) ⟩
  b + (c + ((- a) - b))
    ≡⟨ cong (λ t → b + (c + t)) (+-comm (- a) (- b)) ⟩
  b + (c + ((- b) - a))
    ≡⟨ cong (λ t → b + t) (sym (+-assoc c (- b) (- a))) ⟩
  b + ((c - b) - a)
    ≡⟨ sym (+-assoc b (c - b) (- a)) ⟩
  (b + (c - b)) - a
    ≡⟨ cong (λ t → t - a) (+-comm b (c - b)) ⟩
  ((c - b) + b) - a
    ≡⟨ cong (λ t → t - a)
            (trans (+-assoc c (- b) b)
                   (trans (cong (λ t → c + t) (+-comm (- b) b))
                          (trans (cong (λ t → c + t) (+-inverseʳ b)) (+-identityʳ c)))) ⟩
  c - a ∎

-- 三项望远镜: (b−a) + ((c−b) + (a−c)) ≡ 0
telescope3 : ∀ a b c → (b - a) + ((c - b) + (a - c)) ≡ 0ℚ
telescope3 a b c = begin
  (b - a) + ((c - b) + (a - c))
    ≡⟨ cong (λ t → (b - a) + t) (telescope2 b c a) ⟩
  (b - a) + (a - b)
    ≡⟨ sub-antisym b a ⟩
  0ℚ ∎

-- 4 项合并: (a−b) + (c−d) ≡ (a+c) − (b+d)
merge4 : ∀ a b c d → (a - b) + (c - d) ≡ (a + c) - (b + d)
merge4 a b c d = begin
  (a - b) + (c - d)
    ≡⟨ sym (+-assoc (a - b) c (- d)) ⟩
  ((a - b) + c) - d
    ≡⟨ cong (λ t → t - d) (+-assoc a (- b) c) ⟩
  (a + ((- b) + c)) - d
    ≡⟨ cong (λ t → (a + t) - d) (+-comm (- b) c) ⟩
  (a + (c - b)) - d
    ≡⟨ cong (λ t → t - d) (sym (+-assoc a c (- b))) ⟩
  ((a + c) - b) - d
    ≡⟨ +-assoc (a + c) (- b) (- d) ⟩
  (a + c) + ((- b) - d)
    ≡⟨ cong (λ t → (a + c) + t) (sym (neg-distrib-+ b d)) ⟩
  (a + c) - (b + d) ∎

-- 逐点可加性: sum3ℚ (λ i → f i − g i) ≡ sum3ℚ f − sum3ℚ g
sum3-distrib : ∀ f g → sum3ℚ (λ i → f i - g i) ≡ sum3ℚ f - sum3ℚ g
sum3-distrib f g = begin
  sum3ℚ (λ i → f i - g i)
    ≡⟨ refl ⟩
  (f fz - g fz) + ((f (fs fz) - g (fs fz)) + (f (fs (fs fz)) - g (fs (fs fz))))
    ≡⟨ cong (λ t → (f fz - g fz) + t)
            (merge4 (f (fs fz)) (g (fs fz)) (f (fs (fs fz))) (g (fs (fs fz)))) ⟩
  (f fz - g fz) + ((f (fs fz) + f (fs (fs fz))) - (g (fs fz) + g (fs (fs fz))))
    ≡⟨ merge4 (f fz) (g fz) (f (fs fz) + f (fs (fs fz))) (g (fs fz) + g (fs (fs fz))) ⟩
  (f fz + (f (fs fz) + f (fs (fs fz)))) - (g fz + (g (fs fz) + g (fs (fs fz))))
    ≡⟨ refl ⟩
  sum3ℚ f - sum3ℚ g ∎

-- Σi Σj dxℚ f (i,j,k) ≡ 0 (对 i 望远镜, j 内层; 构造子实例化)
sum3-nested-dx-zero : ∀ f k →
  sum3ℚ (λ i → sum3ℚ (λ j → dxℚ f (i , j , k))) ≡ 0ℚ
sum3-nested-dx-zero f k = begin
  sum3ℚ (λ i → sum3ℚ (λ j → dxℚ f (i , j , k)))
    ≡⟨ cong₂ _+_
         (sum3-distrib (λ j → f (fs fz , j , k)) (λ j → f (fz , j , k)))
         (cong₂ _+_
           (sum3-distrib (λ j → f (fs (fs fz) , j , k)) (λ j → f (fs fz , j , k)))
           (sum3-distrib (λ j → f (fz , j , k)) (λ j → f (fs (fs fz) , j , k)))) ⟩
  (g1 - g0) + ((g2 - g1) + (g0 - g2))
    ≡⟨ telescope3 g0 g1 g2 ⟩
  0ℚ ∎
  where
  g0 = sum3ℚ (λ j → f (fz , j , k))
  g1 = sum3ℚ (λ j → f (fs fz , j , k))
  g2 = sum3ℚ (λ j → f (fs (fs fz) , j , k))

-- Σj dyℚ f (i,j,k) ≡ 0 (对 j 望远镜, i 任意)
sum3-dy-zero : ∀ f i k → sum3ℚ (λ j → dyℚ f (i , j , k)) ≡ 0ℚ
sum3-dy-zero f i k =
  telescope3 (f (i , fz , k)) (f (i , fs fz , k)) (f (i , fs (fs fz) , k))

-- Σi Σj dyℚ f (i,j,k) ≡ 0 (内层望远镜 + 零和)
sum3-nested-dy-zero : ∀ f k →
  sum3ℚ (λ i → sum3ℚ (λ j → dyℚ f (i , j , k))) ≡ 0ℚ
sum3-nested-dy-zero f k = begin
  sum3ℚ (λ i → sum3ℚ (λ j → dyℚ f (i , j , k)))
    ≡⟨ cong₂ _+_
         (sum3-dy-zero f fz k)
         (cong₂ _+_ (sum3-dy-zero f (fs fz) k) (sum3-dy-zero f (fs (fs fz)) k)) ⟩
  0ℚ + (0ℚ + 0ℚ)
    ≡⟨ +-identityˡ 0ℚ ⟩
  0ℚ + 0ℚ
    ≡⟨ +-identityˡ 0ℚ ⟩
  0ℚ ∎

--------------------------------------------------------------------------------
-- §4. 质量积分 (环绕平面 k=0 的有限求和) 与离散斯托克斯定理
--------------------------------------------------------------------------------

massIntegral : QVector → ℚ
massIntegral F = sum3ℚ (λ i → sum3ℚ (λ j → proj₂ (proj₂ (F (i , j , fz)))))

scalarSum : QScalar → ℚ
scalarSum φ = sum3ℚ (λ i → sum3ℚ (λ j → φ (i , j , fz)))

-- 离散斯托克斯: 质量积分的旋度项消失
massIntegral-curl-zero : ∀ Ψ → massIntegral (curlℚ Ψ) ≡ 0ℚ
massIntegral-curl-zero Ψ = begin
  massIntegral (curlℚ Ψ)
    ≡⟨ refl ⟩
  sum3ℚ (λ i → sum3ℚ (λ j → dxℚ (qy Ψ) (i , j , fz) - dyℚ (qx Ψ) (i , j , fz)))
    ≡⟨ cong₂ _+_
         (sum3-distrib (λ j → dxℚ (qy Ψ) (fz , j , fz)) (λ j → dyℚ (qx Ψ) (fz , j , fz)))
         (cong₂ _+_
           (sum3-distrib (λ j → dxℚ (qy Ψ) (fs fz , j , fz)) (λ j → dyℚ (qx Ψ) (fs fz , j , fz)))
           (sum3-distrib (λ j → dxℚ (qy Ψ) (fs (fs fz) , j , fz)) (λ j → dyℚ (qx Ψ) (fs (fs fz) , j , fz)))) ⟩
  (dx0 - dy0) + ((dx1 - dy1) + (dx2 - dy2))
    ≡⟨ cong (λ t → (dx0 - dy0) + t) (merge4 dx1 dy1 dx2 dy2) ⟩
  (dx0 - dy0) + ((dx1 + dx2) - (dy1 + dy2))
    ≡⟨ merge4 dx0 dy0 (dx1 + dx2) (dy1 + dy2) ⟩
  (dx0 + (dx1 + dx2)) - (dy0 + (dy1 + dy2))
    ≡⟨ refl ⟩
  sum3ℚ (λ i → sum3ℚ (λ j → dxℚ (qy Ψ) (i , j , fz)))
    - sum3ℚ (λ i → sum3ℚ (λ j → dyℚ (qx Ψ) (i , j , fz)))
    ≡⟨ cong₂ _-_ (sum3-nested-dx-zero (qy Ψ) fz) (sum3-nested-dy-zero (qx Ψ) fz) ⟩
  0ℚ - 0ℚ
    ≡⟨ refl ⟩
  0ℚ ∎
  where
  dx0 = sum3ℚ (λ j → dxℚ (qy Ψ) (fz , j , fz))
  dx1 = sum3ℚ (λ j → dxℚ (qy Ψ) (fs fz , j , fz))
  dx2 = sum3ℚ (λ j → dxℚ (qy Ψ) (fs (fs fz) , j , fz))
  dy0 = sum3ℚ (λ j → dyℚ (qx Ψ) (fz , j , fz))
  dy1 = sum3ℚ (λ j → dyℚ (qx Ψ) (fs fz , j , fz))
  dy2 = sum3ℚ (λ j → dyℚ (qx Ψ) (fs (fs fz) , j , fz))

-- 熵旋定律的质量积分只余 ℋ² 项:
--   m(Ψ,ℋ) = ∮(∇×Ψ − κℋ²n̂)·n̂ dA = 0 − Σ[(κ·ℋ²)·1] = −Σ[(κ·ℋ²)·1]
-- (RHS 括号与定律定义一致: vscale 的 z 分量 = (κ·ℋ²)·1;
--  "= −κ·Σℋ²" 形式还需 *-assoc/分配律重排, 留作后续, 不写假 refl)
entropySpinMass-reduction : ∀ Ψ H →
  massIntegral (entropySpinLaw Ψ H)
    ≡ - (sum3ℚ (λ i → sum3ℚ (λ j → (kappaQ * (H (i , j , fz) * H (i , j , fz))) * 1ℚ)))
entropySpinMass-reduction Ψ H = begin
  massIntegral (entropySpinLaw Ψ H)
    ≡⟨ refl ⟩
  sum3ℚ (λ i → sum3ℚ (λ j →
    (dxℚ (qy Ψ) (i , j , fz) - dyℚ (qx Ψ) (i , j , fz))
      - ((kappaQ * (H (i , j , fz) * H (i , j , fz))) * 1ℚ)))
    ≡⟨ cong₂ _+_
         (sum3-distrib
           (λ j → dxℚ (qy Ψ) (fz , j , fz) - dyℚ (qx Ψ) (fz , j , fz))
           (λ j → (kappaQ * (H (fz , j , fz) * H (fz , j , fz))) * 1ℚ))
         (cong₂ _+_
           (sum3-distrib
             (λ j → dxℚ (qy Ψ) (fs fz , j , fz) - dyℚ (qx Ψ) (fs fz , j , fz))
             (λ j → (kappaQ * (H (fs fz , j , fz) * H (fs fz , j , fz))) * 1ℚ))
           (sum3-distrib
             (λ j → dxℚ (qy Ψ) (fs (fs fz) , j , fz) - dyℚ (qx Ψ) (fs (fs fz) , j , fz))
             (λ j → (kappaQ * (H (fs (fs fz) , j , fz) * H (fs (fs fz) , j , fz))) * 1ℚ))) ⟩
  (a0 - h0) + ((a1 - h1) + (a2 - h2))
    ≡⟨ cong (λ t → (a0 - h0) + t) (merge4 a1 h1 a2 h2) ⟩
  (a0 - h0) + ((a1 + a2) - (h1 + h2))
    ≡⟨ merge4 a0 h0 (a1 + a2) (h1 + h2) ⟩
  (a0 + (a1 + a2)) - (h0 + (h1 + h2))
    ≡⟨ refl ⟩
  sum3ℚ (λ i → sum3ℚ (λ j → dxℚ (qy Ψ) (i , j , fz) - dyℚ (qx Ψ) (i , j , fz)))
    - sum3ℚ (λ i → sum3ℚ (λ j → (kappaQ * (H (i , j , fz) * H (i , j , fz))) * 1ℚ))
    ≡⟨ cong₂ _-_ (massIntegral-curl-zero Ψ) refl ⟩
  0ℚ - sum3ℚ (λ i → sum3ℚ (λ j → (kappaQ * (H (i , j , fz) * H (i , j , fz))) * 1ℚ))
    ≡⟨ +-identityˡ (- sum3ℚ (λ i → sum3ℚ (λ j → (kappaQ * (H (i , j , fz) * H (i , j , fz))) * 1ℚ))) ⟩
  - sum3ℚ (λ i → sum3ℚ (λ j → (kappaQ * (H (i , j , fz) * H (i , j , fz))) * 1ℚ))
    ≡⟨ refl ⟩
  - (sum3ℚ (λ i → sum3ℚ (λ j → (kappaQ * (H (i , j , fz) * H (i , j , fz))) * 1ℚ))) ∎
  where
  a0 = sum3ℚ (λ j → dxℚ (qy Ψ) (fz , j , fz) - dyℚ (qx Ψ) (fz , j , fz))
  a1 = sum3ℚ (λ j → dxℚ (qy Ψ) (fs fz , j , fz) - dyℚ (qx Ψ) (fs fz , j , fz))
  a2 = sum3ℚ (λ j → dxℚ (qy Ψ) (fs (fs fz) , j , fz) - dyℚ (qx Ψ) (fs (fs fz) , j , fz))
  h0 = sum3ℚ (λ j → (kappaQ * (H (fz , j , fz) * H (fz , j , fz))) * 1ℚ)
  h1 = sum3ℚ (λ j → (kappaQ * (H (fs fz , j , fz) * H (fs fz , j , fz))) * 1ℚ)
  h2 = sum3ℚ (λ j → (kappaQ * (H (fs (fs fz) , j , fz) * H (fs (fs fz) , j , fz))) * 1ℚ)

-- 0 postulate.
