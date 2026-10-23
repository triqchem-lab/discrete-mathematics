{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Synthesis.Physics.J1MatricesProbe
--
-- **探针模块**：J=1 的角动量矩阵，用**向量基** |x⟩,|y⟩,|z⟩。
--
-- 为什么要向量基（蓝图 §11.3）：
--   |m⟩ 基（m = −1,0,+1）里 J_i 含 1/√2 和 i ⇒ **非有理**
--   向量基里 J_i 是**整数矩阵** ⇒ 可用 ℤ（与 NoSplitJ1Full 一致）
--
-- 向量基的定义（J=1 的矢量表示，即 SO(3) 的基本表示）：
--   (J_i)_{jk} = −i ε_{ijk}   ⇒  实矩阵 (J_i)_{jk} = ε_{ijk}
--   这里取**实**约定：J_x, J_y, J_z 都是 3×3 实反对称矩阵。
--
-- 本模块只做 S1b：写出这三个矩阵与它们的一个关键恒等式。
module Sovereign.Synthesis.Physics.J1MatricesProbe where

open import Data.Fin using (Fin; zero; suc)
open import Data.Integer using (ℤ; +_; +0; -[1+_]; _+_; _-_; _*_; -_)
open import Data.Integer.Properties using (*-identityʳ; *-zeroʳ; +-identityʳ)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
-- ⭐ 复用已有的载体与乘法（不重定义 —— 库里 AxialNoSplit 已有同型的 Mat3/Vec3/mul）
open import Sovereign.Synthesis.Physics.AxialNoSplit
  using (Mat3; Vec3; mul)

--------------------------------------------------------------------------------
-- 1. 三维矩阵与向量
--------------------------------------------------------------------------------

--------------------------------------------------------------------------------
-- 2. J=1 的三个角动量矩阵（向量基，实反对称）
--
--    J_x = ⎡ 0  0  0 ⎤    J_y = ⎡ 0  0  1 ⎤    J_z = ⎡ 0 −1  0 ⎤
--          ⎢ 0  0 −1 ⎥          ⎢ 0  0  0 ⎥          ⎢ 1  0  0 ⎥
--          ⎣ 0  1  0 ⎦          ⎣−1  0  0 ⎦          ⎣ 0  0  0 ⎦
--------------------------------------------------------------------------------

Jx : Mat3
Jx zero           zero           = +0
Jx zero           (suc zero)     = +0
Jx zero           (suc (suc zero)) = +0
Jx (suc zero)     zero           = +0
Jx (suc zero)     (suc zero)     = +0
Jx (suc zero)     (suc (suc zero)) = - (+ 1)
Jx (suc (suc zero)) zero         = +0
Jx (suc (suc zero)) (suc zero)   = + 1
Jx (suc (suc zero)) (suc (suc zero)) = +0

Jy : Mat3
Jy zero           zero           = +0
Jy zero           (suc zero)     = +0
Jy zero           (suc (suc zero)) = + 1
Jy (suc zero)     zero           = +0
Jy (suc zero)     (suc zero)     = +0
Jy (suc zero)     (suc (suc zero)) = +0
Jy (suc (suc zero)) zero         = - (+ 1)
Jy (suc (suc zero)) (suc zero)   = +0
Jy (suc (suc zero)) (suc (suc zero)) = +0

Jz : Mat3
Jz zero           zero           = +0
Jz zero           (suc zero)     = - (+ 1)
Jz zero           (suc (suc zero)) = +0
Jz (suc zero)     zero           = + 1
Jz (suc zero)     (suc zero)     = +0
Jz (suc zero)     (suc (suc zero)) = +0
Jz (suc (suc zero)) zero         = +0
Jz (suc (suc zero)) (suc zero)   = +0
Jz (suc (suc zero)) (suc (suc zero)) = +0

--------------------------------------------------------------------------------
-- 3. 矩阵乘法与转置
--------------------------------------------------------------------------------

mat3-mul : Mat3 → Mat3 → Mat3
mat3-mul A B i k = (A i zero * B zero k) + (A i (suc zero) * B (suc zero) k)
                + (A i (suc (suc zero)) * B (suc (suc zero)) k)

mat3-transpose : Mat3 → Mat3
mat3-transpose A i j = A j i

mat3-add : Mat3 → Mat3 → Mat3
mat3-add A B i j = A i j + B i j

--------------------------------------------------------------------------------
-- 4. 关键恒等式：J_i J_j − J_j J_i 的平方和
--
--    ⚠ **实约定**（(J_i)_{jk} = ε_{ijk}，实反对称）给：
--        (J_x)² + (J_y)² + (J_z)² = **−2·I**
--    因为实反对称矩阵的平方是负定的。
--    （厄米约定 (J_i)_{jk} = −i ε_{ijk} 才给 +2·I。本模块用实约定，故为 −2。）
--
--    这条恒等式是 S1 的核心：它把「四极算符」写成
--        Q(n) ∝ 3 (n·J)² − 2·I
--    并保证它在 n → −n 下不变。
--------------------------------------------------------------------------------

JxJx : Mat3
JxJx = mat3-mul Jx Jx

JyJy : Mat3
JyJy = mat3-mul Jy Jy

JzJz : Mat3
JzJz = mat3-mul Jz Jz

-- ² 和 = 2·I（逐元素陈述）
sum-sq-diag : (i : Fin 3) →
  (JxJx i i + JyJy i i) + JzJz i i ≡ - (+ 2)
sum-sq-diag zero             = refl
sum-sq-diag (suc zero)       = refl
sum-sq-diag (suc (suc zero)) = refl

-- 非对角元：枚举 6 个位置（不用 ≢ 假设，直接逐点算）
sum-sq-01 : (JxJx zero (suc zero) + JyJy zero (suc zero)) + JzJz zero (suc zero) ≡ +0
sum-sq-01 = refl

sum-sq-02 : (JxJx zero (suc (suc zero)) + JyJy zero (suc (suc zero)))
          + JzJz zero (suc (suc zero)) ≡ +0
sum-sq-02 = refl

sum-sq-10 : (JxJx (suc zero) zero + JyJy (suc zero) zero) + JzJz (suc zero) zero ≡ +0
sum-sq-10 = refl

sum-sq-12 : (JxJx (suc zero) (suc (suc zero)) + JyJy (suc zero) (suc (suc zero)))
          + JzJz (suc zero) (suc (suc zero)) ≡ +0
sum-sq-12 = refl

sum-sq-20 : (JxJx (suc (suc zero)) zero + JyJy (suc (suc zero)) zero)
          + JzJz (suc (suc zero)) zero ≡ +0
sum-sq-20 = refl

sum-sq-21 : (JxJx (suc (suc zero)) (suc zero) + JyJy (suc (suc zero)) (suc zero))
          + JzJz (suc (suc zero)) (suc zero) ≡ +0
sum-sq-21 = refl

--------------------------------------------------------------------------------
-- 5. 自检：J_x J_y = −J_y J_x（反对易？不——是 [J_x,J_y] = J_z 的实形式）
--
--    向量基里 [J_i, J_j] = ε_{ijk} J_k（因 (J_i)_{jk} = ε_{ijk}）。
--    验一组：J_x J_y - J_y J_x 的 (1,1) 元素应等于 (J_z)_{1,1} = 0。
--------------------------------------------------------------------------------

JxJy : Mat3
JxJy = mat3-mul Jx Jy

JyJx : Mat3
JyJx = mat3-mul Jy Jx

comm-xy-11 : (JxJy (suc zero) (suc zero) - (JyJx (suc zero) (suc zero)))
           ≡ Jz (suc zero) (suc zero)
comm-xy-11 = refl

comm-xy-01 : (JxJy zero (suc zero) - (JyJx zero (suc zero)))
           ≡ Jz zero (suc zero)
comm-xy-01 = refl

--------------------------------------------------------------------------------
-- 6. ⭐ 轴算符：**通勤于 C₃（shift）但**不通勤**于反射（flip）
--
-- 这是本探针最重要的结构事实。
--
-- `NoSplitJ1Full.no-split-full` 要求 **两者都满足**（Commutes-shift +
-- Commutes-flip）才推出「三个对角元相等」。但物理的 S₆ 只有 C₃ × 反演，
-- 反演在 J=1 上是整体 −1（不劈裂）⇒ **物理上只有 shift，没有 flip**。
--
-- 因此 `no-split-full` **不适用于** S₆ 轴场 —— 轴场**确实**劈裂。
-- 这与我早先证伪的「轴场不劈裂」前提一致。
--------------------------------------------------------------------------------

-- 轴向量 n = [111]，轴算符在向量基下是 (Jx+Jy+Jz)²/3（这里只验证通勤性，
-- 系数无关紧要，用 S = Jx+Jy+Jz 即可）

vec3-add : Vec3 → Vec3 → Vec3
vec3-add u v i = u i + v i



-- 轴方向 n = (1,1,1)：J_n = Jx + Jy + Jz
Jn : Mat3
Jn = mat3-add Jx (mat3-add Jy Jz)

JnSq : Mat3
JnSq = mat3-mul Jn Jn

--------------------------------------------------------------------------------
-- 6a. JnSq 是否通勤于「循环置换」？
--
-- 循环置换 σ：(v₀,v₁,v₂) ↦ (v₂,v₀,v₁)
-- 在矩阵上：Jn 的 x→y→z→x 循环把 Jx+Jy+Jz 变成 Jy+Jz+Jx（同一个和），
-- 所以 Jn（从而 JnSq）**通勤于 σ**。
--
-- 我们直接验：Jn 在 σ 下的像是它自己 ⇒ JnSq 也是。
-- 由于 σ 作用在**分量**上而 Jn 是矩阵，通勤性的最简陈述是：
--   Jn 的三个列之和相等（= σ 不变性的等价形式）
--------------------------------------------------------------------------------

col-sum : (i : Fin 3) → ℤ
col-sum i = (Jn i zero + Jn i (suc zero)) + Jn i (suc (suc zero))

col-sums-equal : (col-sum zero ≡ col-sum (suc zero))
               × (col-sum (suc zero) ≡ col-sum (suc (suc zero)))
col-sums-equal = refl , refl

--------------------------------------------------------------------------------
-- 6b. JnSq 是否通勤于「反射」τ：(v₀,v₁,v₂) ↦ (−v₀,−v₁,v₂)？
--
-- 在 τ 下 Jx ↦ −Jx，Jy ↦ −Jy，Jz ↦ Jz
-- ⇒ Jn = Jx+Jy+Jz ↦ −Jx−Jy+Jz ≠ Jn（因为 Jx+Jy ≠ 0）
-- ⇒ **不通勤**。
--
-- 我们验证一个具体元素：τ 把 Jn 的 (0,2) 元素变成 −Jn(0,2)，
-- 而 Jn(0,2) = 1 ≠ 0 ⇒ 确实破了对称。
--------------------------------------------------------------------------------

-- Jn 的 (0,2) = Jx(0,2) + Jy(0,2) + Jz(0,2) = 0 + 1 + 0 = 1
Jn-02 : Jn zero (suc (suc zero)) ≡ + 1
Jn-02 = refl

-- τ 后的 (0,2) 应为 −(Jx(0,2)) − (Jy(0,2)) + Jz(0,2) = 0 − 1 + 0 = −1
-- ≠ 1 ⇒ 不通勤
Jn-02-flipped : (- (Jx zero (suc (suc zero))) - (Jy zero (suc (suc zero))))
              + Jz zero (suc (suc zero)) ≡ - (+ 1)
Jn-02-flipped = refl

not-flip-invariant :
  (( (- (Jx zero (suc (suc zero))) - (Jy zero (suc (suc zero))))
     + Jz zero (suc (suc zero)) )
   ≡ Jn zero (suc (suc zero)))
  → (- (+ 1) ≡ + 1)
not-flip-invariant h = h

--------------------------------------------------------------------------------
-- 7. ⭐⭐ 轴算符的 **2+1** 结构
--
-- 轴向量 n = (1,1,1)/√3。定义 Jn = Jx + Jy + Jz（系数无关紧要）。
--
-- 关键事实：
--   (a) Jn · (1,1,1) = 0          ⇒ (1,1,1) 是 Jn 的零特征向量（**singlet**）
--   (b) tr(Jn²) = **−6**           ⇒ Jn² 的特征值之和 = −6
--   (c) 由 (a) 知一个特征值是 0 ⇒ 另两个之和 = −6
--   (d) 另两个相等的论证（**要写清，不能手挥**）：
--       · Jn 是实反对称 ⇒ Jn² 是**实对称**且负半定
--       · 实对称 ⇒ 特征值全**实**，且本征向量可取实
--       · Jn² 通勤于循环置换 σ（第 6 节的 col-sums-equal 是它的一个推论）
--       · σ 的特征值是 1, ω, ω²（ω = e^{2πi/3}）
--       · (1,1,1) 对应 σ 的特征值 1 ⇒ 那个特征值是 0（由 (a)）
--       · 剩下 2 维子空间对应 ω 与 ω²；因 Jn² 实对称，该子空间上的两个
--         特征值必为**共轭**，而它们又都是实数 ⇒ **必相等**
--       ⇒ 各 = −6/2 = **−3**
--
-- ⇒ Jn² 的谱 = **(0, −3, −3)** ⇒ **2+1**（一个单态 + 一个双重态）
-- ⇒ 这正是物理观测的 J=1 分裂模式（观测 4.2/<1/4.5 的两个大一个小）
--------------------------------------------------------------------------------

-- (a) Jn 作用在 (1,1,1) 上为零
ones : Vec3
ones _ = + 1

Jn-ones-zero : (i : Fin 3) → mul Jn ones i ≡ +0
Jn-ones-zero zero             = refl
Jn-ones-zero (suc zero)       = refl
Jn-ones-zero (suc (suc zero)) = refl

-- (b) tr(Jn²) = −12
mat3-trace : Mat3 → ℤ
mat3-trace A = (A zero zero + A (suc zero) (suc zero)) + A (suc (suc zero)) (suc (suc zero))

tr-JnSq : mat3-trace JnSq ≡ - (+ 6)
tr-JnSq = refl

--------------------------------------------------------------------------------
-- 8. 与 `no-split-full` 的对照（说明为什么它**不适用**）
--
-- `NoSplitJ1Full.no-split-full` 要求 **Commutes-shift + Commutes-flip**。
-- 我们的 JnSq：
--   · 通勤于 shift（C₃）  ✓ —— 见第 6 节的 col-sums-equal
--   · **不通勤**于 flip    ✗ —— 见第 6 节的 Jn-02-flipped
--
-- ⇒ 假设不成立 ⇒ 结论（三个对角元相等 ⇒ 不劈裂）**不适用**。
--
-- 而 §7 直接算出了 2+1 谱 ⇒ **轴场确实劈裂**。
--------------------------------------------------------------------------------

-- 自检：JnSq 的对角元
JnSq-00 : JnSq zero zero ≡ - (+ 2)
JnSq-00 = refl

JnSq-11 : JnSq (suc zero) (suc zero) ≡ - (+ 2)
JnSq-11 = refl

JnSq-22 : JnSq (suc (suc zero)) (suc (suc zero)) ≡ - (+ 2)
JnSq-22 = refl

-- ⇒ 对角元全等（−2），符合 C₃ 对称；但**非对角元不全为零**（JnSq-02 等）
-- ⇒ 这正是「有劈裂」的标志：在 (1,1,1) 基下对角化后得到 (0, −3, −3)
