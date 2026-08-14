{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Problem.Riemann.ZetaFunctional
-- 有限域 zeta 函数的有理式、函数方程与零点刚性 (P1-1, 11M 离散版)
--
-- 数学背景:
--   E/F_q 椭圆曲线, Frobenius 迹 t = q+1−#E。L(E,T) = 1 − tT + qT²,
--   Z(T) = L(T)/((1−T)(1−qT)) 是 E 的 zeta 函数 (有理式)。
--   函数方程 (genus 1): Z(1/qT) = Z(T) —— 权重因子 q^(1−g)T^(2−2g) = 1。
--   零点: Z 的零点 = L 的零点 = α⁻¹, β⁻¹, 其中 α,β 为 L 的互逆根
--   (αβ = q, α+β = t, α ∈ ℤ[ω] — Eisenstein 刚性 t²+3s²=4q 见 WeilRigidity)。
--
-- 宪法原则 (全离散, 无浮点, 无除法):
--   1. T ↦ 1/qT 的替换以"通分多项式" recipClear q P := q²T²·P(1/qT) 实现,
--      系数运算只含 ℤ 加减乘; 分式相等用交叉相乘四次恒等式表达。
--   2. 零点不取逆元: "α⁻¹ 是零点"以互逆多项式 P*(T) = T²·P(1/T) = T²−tT+q
--      在 α 处取零的整数形式陈述。
--   3. 函数方程 = recipClear(q,L)·D ≡ L·recipClear(q,D) (四次恒等式),
--      三条曲线逐条 refl 验证 (与 WeilRigidity 同款实例)。
--
-- 本模块证明 (0 postulate, 全 refl/cong):
--   §0 多项式与分数类型 (Quad/Quart/ZetaFraction, 通分 recipClear, 求值 evalE)
--   §1 有理式分解: Z(T) = (1−αT)(1−βT)/((1−T)(1−qT)) — 迹/范数恒等式
--   §2 函数方程: Z(1/qT) = Z(T) — 交叉相乘 + 约分形式 (三条曲线 + GF(9) 层)
--   §3 零点刚性: P*(α)=P*(β)=0 (互逆多项式), 判别式 Δ=t²−4q=−3s²

module Sovereign.Problem.Riemann.ZetaFunctional where

open import Data.Integer using (ℤ; +_; -[1+_]; _+_; _-_; _*_; -_)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; _≢_; cong; cong₂)
open import Sovereign.RootMath.Eisenstein
  using (Eisenstein; eis; 0ᵉ; 1ᵉ; 3ᵉ; _+ᵉ_; _*ᵉ_; conjᵉ)
open import Sovereign.Problem.Riemann.WeilRigidity
  using (q3; t1-E1; t1-E2; t1-E6; t2-E1; t2-E2; t2-E6;
         alpha-E1; alpha-E2; alpha-E6; alpha-E1-9; alpha-E2-9;
         trace-sum-E1; trace-sum-E2; trace-sum-E6; trace-sum-E2-9;
         norm-product-E1; norm-product-E2; norm-product-E6; norm-product-E2-9)

--------------------------------------------------------------------------------
-- §0. 多项式与分数类型
--------------------------------------------------------------------------------

-- 二次多项式 c0 + c1·T + c2·T² (ℤ 系数)
record Quad : Set where
  constructor quad
  field
    c0 : ℤ
    c1 : ℤ
    c2 : ℤ

-- 二次多项式 (Eisenstein 系数, 用于 (1−αT)(1−βT) 分解)
record QuadE : Set where
  constructor quadE
  field
    e0 : Eisenstein
    e1 : Eisenstein
    e2 : Eisenstein

-- 四次多项式 d0 + d1·T + d2·T² + d3·T³ + d4·T⁴ (交叉相乘产物)
record Quart : Set where
  constructor quart
  field
    d0 d1 d2 d3 d4 : ℤ

-- zeta 分数 Z(T) = num/den
record ZetaFraction : Set where
  constructor frac
  field
    num : Quad
    den : Quad

-- Quad 乘法 → Quart (系数公式, 卷积)
_*q_ : Quad → Quad → Quart
quad a0 a1 a2 *q quad b0 b1 b2 =
  quart (a0 * b0)
        (a0 * b1 + a1 * b0)
        (a0 * b2 + a1 * b1 + a2 * b0)
        (a1 * b2 + a2 * b1)
        (a2 * b2)

-- 通分替换: q²T²·P(1/qT), 即系数 (c0+c1T+c2T²) ↦ (c2 + c1·q·T + c0·q²·T²)
recipClear : ℤ → Quad → Quad
recipClear q (quad c0 c1 c2) = quad c2 (c1 * q) (c0 * q * q)

-- 标量乘
_*ₖ_ : ℤ → Quad → Quad
k *ₖ quad c0 c1 c2 = quad (k * c0) (k * c1) (k * c2)

-- 一次多项式乘法 (a0+a1T)(b0+b1T), 用于分母因式分解
mulLin : ℤ → ℤ → ℤ → ℤ → Quad
mulLin a0 a1 b0 b1 = quad (a0 * b0) (a0 * b1 + a1 * b0) (a1 * b1)

-- ℤ 系数嵌入 Eisenstein 系数
embed : Quad → QuadE
embed (quad c0 c1 c2) = quadE (eis c0 (+ 0)) (eis c1 (+ 0)) (eis c2 (+ 0))

-- Eisenstein 一元负
negᵉ : Eisenstein → Eisenstein
negᵉ (eis a b) = eis (- a) (- b)

-- 多项式求值 (Eisenstein)
evalE : QuadE → Eisenstein → Eisenstein
evalE (quadE c0 c1 c2) x = c0 +ᵉ c1 *ᵉ x +ᵉ c2 *ᵉ x *ᵉ x

-- Z(T) 的分子 L(T) = 1 − tT + qT²
Zpoly : ℤ → ℤ → Quad
Zpoly t q = quad (+ 1) (- t) q

-- Z(T) 的分母 (1−T)(1−qT) = (qT−1)(T−1) = 1 − (1+q)T + qT² (展开式)
denPoly : ℤ → Quad
denPoly q = quad (+ 1) (- (+ 1 + q)) q

-- Z(T) = L(T)/((1−T)(1−qT))
Z : ℤ → ℤ → ZetaFraction
Z t q = frac (Zpoly t q) (denPoly q)

-- 分子 (1−αT)(1−βT) 的展开式 (Eisenstein 系数): 1 − (α+β)T + αβ·T²
numEis : Eisenstein → Eisenstein → QuadE
numEis α β = quadE 1ᵉ (negᵉ (α +ᵉ β)) (α *ᵉ β)

-- 互逆多项式 P*(T) = T²·P(1/T) = (T−α)(T−β) = T² − tT + q
reversePoly : ℤ → ℤ → Quad
reversePoly t q = quad q (- t) (+ 1)

--------------------------------------------------------------------------------
-- §1. 有理式分解: Z(T) = (1−αT)(1−βT)/((1−T)(1−qT))
--   分子: (1−αT)(1−βT) 展开系数 = 1, −(α+β), αβ
--   由 WeilRigidity 的迹/范数恒等式 (α+β = t, αβ = q) 收缩到 ℤ 系数。
--------------------------------------------------------------------------------

num-factor-E1 : numEis alpha-E1 (conjᵉ alpha-E1) ≡ embed (Zpoly t1-E1 q3)
num-factor-E1 = cong₂ (λ x y → quadE 1ᵉ x y)
  (cong negᵉ (trace-sum-E1)) (norm-product-E1)

num-factor-E2 : numEis alpha-E2 (conjᵉ alpha-E2) ≡ embed (Zpoly t1-E2 q3)
num-factor-E2 = cong₂ (λ x y → quadE 1ᵉ x y)
  (cong negᵉ (trace-sum-E2)) (norm-product-E2)

num-factor-E6 : numEis alpha-E6 (conjᵉ alpha-E6) ≡ embed (Zpoly t1-E6 q3)
num-factor-E6 = cong₂ (λ x y → quadE 1ᵉ x y)
  (cong negᵉ (trace-sum-E6)) (norm-product-E6)

-- 分母两种因式分解一致: (1−T)(1−qT) = (qT−1)(T−1) = 1 − (1+q)T + qT²
den-factor-direct : mulLin (+ 1) (- (+ 1)) (+ 1) (- q3) ≡ denPoly q3
den-factor-direct = refl                    -- (1−T)(1−qT)

den-factor-swapped : mulLin (- (+ 1)) q3 (- (+ 1)) (+ 1) ≡ denPoly q3
den-factor-swapped = refl                   -- (qT−1)(T−1)

--------------------------------------------------------------------------------
-- §2. 函数方程: Z(1/qT) = Z(T)
--   通分: Z(1/qT) = recipClear q L / recipClear q D (分母均乘 q²T²)。
--   交叉相乘四次恒等式 recipClear(q,L)·D ≡ L·recipClear(q,D) 即分式相等。
--   再由约分引理 recipClear q P ≡ q·P (共公因子 q) 得经典约分形式:
--   Z(1/qT) = (qT²−tT+1)/((qT−1)(T−1)) = L(T)/((1−T)(1−qT)) = Z(T)。
--------------------------------------------------------------------------------

-- 约分引理: q²T²·P(1/qT) ≡ q·P (对 L 与 D, 逐曲线)
clear-num-E1 : recipClear q3 (Zpoly t1-E1 q3) ≡ q3 *ₖ Zpoly t1-E1 q3
clear-num-E1 = refl

clear-num-E2 : recipClear q3 (Zpoly t1-E2 q3) ≡ q3 *ₖ Zpoly t1-E2 q3
clear-num-E2 = refl

clear-num-E6 : recipClear q3 (Zpoly t1-E6 q3) ≡ q3 *ₖ Zpoly t1-E6 q3
clear-num-E6 = refl

clear-den-E1 : recipClear q3 (denPoly q3) ≡ q3 *ₖ denPoly q3
clear-den-E1 = refl

-- 函数方程 (交叉相乘形式): recipClear(q,L)·D ≡ L·recipClear(q,D)
fe-cross-E1 : recipClear q3 (Zpoly t1-E1 q3) *q denPoly q3
              ≡ Zpoly t1-E1 q3 *q recipClear q3 (denPoly q3)
fe-cross-E1 = refl

fe-cross-E2 : recipClear q3 (Zpoly t1-E2 q3) *q denPoly q3
              ≡ Zpoly t1-E2 q3 *q recipClear q3 (denPoly q3)
fe-cross-E2 = refl

fe-cross-E6 : recipClear q3 (Zpoly t1-E6 q3) *q denPoly q3
              ≡ Zpoly t1-E6 q3 *q recipClear q3 (denPoly q3)
fe-cross-E6 = refl

-- 约分后的经典形式: Z(1/qT) = (qT²−tT+1)/((qT−1)(T−1)) = Z(T)
-- 分子 qT²−tT+1 与 L(T)=1−tT+qT² 是同一系数三元组 (1, −t, q);
-- 分母 (qT−1)(T−1) 的展开式与 (1−T)(1−qT) 相同 (den-factor-swapped)。
zeta-recip-E1 : frac (quad (+ 1) (- t1-E1) q3) (mulLin (- (+ 1)) q3 (- (+ 1)) (+ 1)) ≡ Z t1-E1 q3
zeta-recip-E1 = refl

zeta-recip-E2 : frac (quad (+ 1) (- t1-E2) q3) (mulLin (- (+ 1)) q3 (- (+ 1)) (+ 1)) ≡ Z t1-E2 q3
zeta-recip-E2 = refl

zeta-recip-E6 : frac (quad (+ 1) (- t1-E6) q3) (mulLin (- (+ 1)) q3 (- (+ 1)) (+ 1)) ≡ Z t1-E6 q3
zeta-recip-E6 = refl

-- GF(9) 层 (q = 9, 迹 t₂ = t₁² − 2q): 同款函数方程
fe-cross-E1-9 : recipClear (+ 9) (Zpoly t2-E1 (+ 9)) *q denPoly (+ 9)
                ≡ Zpoly t2-E1 (+ 9) *q recipClear (+ 9) (denPoly (+ 9))
fe-cross-E1-9 = refl

fe-cross-E2-9 : recipClear (+ 9) (Zpoly t2-E2 (+ 9)) *q denPoly (+ 9)
                ≡ Zpoly t2-E2 (+ 9) *q recipClear (+ 9) (denPoly (+ 9))
fe-cross-E2-9 = refl

zeta-recip-E1-9 : frac (quad (+ 1) (- t2-E1) (+ 9)) (mulLin (- (+ 1)) (+ 9) (- (+ 1)) (+ 1)) ≡ Z t2-E1 (+ 9)
zeta-recip-E1-9 = refl

zeta-recip-E2-9 : frac (quad (+ 1) (- t2-E2) (+ 9)) (mulLin (- (+ 1)) (+ 9) (- (+ 1)) (+ 1)) ≡ Z t2-E2 (+ 9)
zeta-recip-E2-9 = refl

--------------------------------------------------------------------------------
-- §3. 零点刚性: Z 的零点 = α⁻¹, β⁻¹
--   L(T) = (1−αT)(1−βT) 的零点为 T = α⁻¹, β⁻¹;
--   其代数形式: 互逆多项式 P*(T) = T²·L(1/T) = (T−α)(T−β) = T²−tT+q
--   在 α, β 处取零 (⇔ 特征方程 α²+q = tα, 见 WeilRigidity.eigen-*)。
--   刚性: 判别式 Δ = t²−4q = −3s² ≤ 0 ⟹ 零点为 ℚ(ω) 共轭对 (非实),
--   |α|=√q 的整数形式 t²+3s²=4q 已由 WeilRigidity 证明。
--------------------------------------------------------------------------------

-- 互逆多项式在特征值处取零 (即 α⁻¹, β⁻¹ 为 Z 的零点)
zero-alpha-E1 : evalE (embed (reversePoly t1-E1 q3)) alpha-E1 ≡ 0ᵉ
zero-alpha-E1 = refl

zero-beta-E1 : evalE (embed (reversePoly t1-E1 q3)) (conjᵉ alpha-E1) ≡ 0ᵉ
zero-beta-E1 = refl

zero-alpha-E2 : evalE (embed (reversePoly t1-E2 q3)) alpha-E2 ≡ 0ᵉ
zero-alpha-E2 = refl

zero-beta-E2 : evalE (embed (reversePoly t1-E2 q3)) (conjᵉ alpha-E2) ≡ 0ᵉ
zero-beta-E2 = refl

zero-alpha-E6 : evalE (embed (reversePoly t1-E6 q3)) alpha-E6 ≡ 0ᵉ
zero-alpha-E6 = refl

zero-beta-E6 : evalE (embed (reversePoly t1-E6 q3)) (conjᵉ alpha-E6) ≡ 0ᵉ
zero-beta-E6 = refl

-- GF(9) 层零点 (α, β 为 L₂(T) = 1−t₂T+9T² 的互逆根)
zero-alpha-E1-9 : evalE (embed (reversePoly t2-E1 (+ 9))) alpha-E1-9 ≡ 0ᵉ
zero-alpha-E1-9 = refl

zero-alpha-E2-9 : evalE (embed (reversePoly t2-E2 (+ 9))) alpha-E2-9 ≡ 0ᵉ
zero-alpha-E2-9 = refl

zero-beta-E2-9 : evalE (embed (reversePoly t2-E2 (+ 9))) (conjᵉ alpha-E2-9) ≡ 0ᵉ
zero-beta-E2-9 = refl

-- 分子-互逆对偶: T²·P(1/T) ≡ T²−tT+q (即 P 的零点为 P* 零点的倒数)
recip-num-E1 : quadE (alpha-E1 *ᵉ conjᵉ alpha-E1) (negᵉ (alpha-E1 +ᵉ conjᵉ alpha-E1)) 1ᵉ
               ≡ embed (reversePoly t1-E1 q3)
recip-num-E1 = cong₂ (λ x y → quadE x y 1ᵉ) (norm-product-E1) (cong negᵉ (trace-sum-E1))

recip-num-E2 : quadE (alpha-E2 *ᵉ conjᵉ alpha-E2) (negᵉ (alpha-E2 +ᵉ conjᵉ alpha-E2)) 1ᵉ
               ≡ embed (reversePoly t1-E2 q3)
recip-num-E2 = cong₂ (λ x y → quadE x y 1ᵉ) (norm-product-E2) (cong negᵉ (trace-sum-E2))

recip-num-E6 : quadE (alpha-E6 *ᵉ conjᵉ alpha-E6) (negᵉ (alpha-E6 +ᵉ conjᵉ alpha-E6)) 1ᵉ
               ≡ embed (reversePoly t1-E6 q3)
recip-num-E6 = cong₂ (λ x y → quadE x y 1ᵉ) (norm-product-E6) (cong negᵉ (trace-sum-E6))

-- 判别式: Δ = t²−4q = −3s² (刚性判据的零位形式, s 见 WeilRigidity)
disc-E1 : t1-E1 * t1-E1 - (+ 4) * q3 ≡ - (+ 3 * (+ 2 * + 2))
disc-E1 = refl                        -- 0−12 = −12 = −3·2²

disc-E2 : t1-E2 * t1-E2 - (+ 4) * q3 ≡ - (+ 3 * (+ 1 * + 1))
disc-E2 = refl                        -- 9−12 = −3 = −3·1²

disc-E6 : t1-E6 * t1-E6 - (+ 4) * q3 ≡ - (+ 3 * (+ 1 * + 1))
disc-E6 = refl                        -- 9−12 = −3 = −3·1²

-- GF(9) 层判别式: Δ = t₂²−36 = −3s²
disc-E1-9 : t2-E1 * t2-E1 - (+ 4) * (+ 9) ≡ - (+ 3 * (+ 0 * + 0))
disc-E1-9 = refl                      -- 36−36 = 0 (实分裂, s=0)

disc-E2-9 : t2-E2 * t2-E2 - (+ 4) * (+ 9) ≡ - (+ 3 * (+ 3 * + 3))
disc-E2-9 = refl                      -- 9−36 = −27 = −3·3²
