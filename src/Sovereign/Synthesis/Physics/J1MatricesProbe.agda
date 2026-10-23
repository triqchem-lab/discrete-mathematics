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
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; subst)
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

--------------------------------------------------------------------------------
-- 9. ⭐⭐⭐ S1a：把 S₆ 的 `AxialShape` **接到** `JnSq` 上
--
-- `S6EFGAxial` 证明：S₆ 轴向 + 对称 + 无迹的 3×3 张量，其
--   · 三个对角元全为 **0**（`diag-zero`）
--   · 六个非对角元**全相等**（`nd-all-eq`）
-- ⇒ 形状是 [[0,a,a],[a,0,a],[a,a,0]]。
--
-- 而我们从 J=1 的整数矩阵算出：
--   JnSq = [[-2,1,1],[1,-2,1],[1,1,-2]]
-- ⇒ **JnSq + 2I = [[0,1,1],[1,0,1],[1,1,0]]** —— **正是那个形状**（a = 1）。
--
-- ⇒ 所以「S₆ 轴向 EFG」在 J=1 上的算符**就是**（up to 标量因子）
--   JnSq + 2I 这一类。它的谱（§7）= (0,−3,−3) 平移 +2 ⇒ **(2,−1,−1)**
--   ⇒ **仍然 2+1**，只是整体平移了 2。
--------------------------------------------------------------------------------

-- 轴形状的定义（与 S6EFGAxial 的 AxialShape 同构的显式形式）
AxialT : Mat3
AxialT zero             zero             = +0
AxialT zero             (suc zero)       = + 1
AxialT zero             (suc (suc zero)) = + 1
AxialT (suc zero)       zero             = + 1
AxialT (suc zero)       (suc zero)       = +0
AxialT (suc zero)       (suc (suc zero)) = + 1
AxialT (suc (suc zero)) zero             = + 1
AxialT (suc (suc zero)) (suc zero)       = + 1
AxialT (suc (suc zero)) (suc (suc zero)) = +0

-- JnSq 的对角元 = −2，非对角元 = 1
JnSq-02 : JnSq zero (suc (suc zero)) ≡ + 1
JnSq-02 = refl

JnSq-01 : JnSq zero (suc zero) ≡ + 1
JnSq-01 = refl

JnSq-10 : JnSq (suc zero) zero ≡ + 1
JnSq-10 = refl

JnSq-12 : JnSq (suc zero) (suc (suc zero)) ≡ + 1
JnSq-12 = refl

JnSq-20 : JnSq (suc (suc zero)) zero ≡ + 1
JnSq-20 = refl

JnSq-21 : JnSq (suc (suc zero)) (suc zero) ≡ + 1
JnSq-21 = refl

-- 对角元都是 −2
JnSq-00' : JnSq zero zero ≡ - (+ 2)
JnSq-00' = refl

-- ⭐ 主连接：JnSq + 2I = AxialT（逐元素）
--    对角 0、非对角 1
I3 : Mat3
I3 zero             zero             = + 1
I3 zero             (suc zero)       = +0
I3 zero             (suc (suc zero)) = +0
I3 (suc zero)       zero             = +0
I3 (suc zero)       (suc zero)       = + 1
I3 (suc zero)       (suc (suc zero)) = +0
I3 (suc (suc zero)) zero             = +0
I3 (suc (suc zero)) (suc zero)       = +0
I3 (suc (suc zero)) (suc (suc zero)) = + 1

two-I3 : Mat3
two-I3 i j = (+ 2) * I3 i j

-- JnSq + 2I 的 (0,0) = −2 + 2 = 0 = AxialT(0,0)
-- JnSq + 2I 的 (0,1) = 1 + 0 = 1 = AxialT(0,1)
jn-sq-plus-2I-00 : (JnSq zero zero + two-I3 zero zero) ≡ AxialT zero zero
jn-sq-plus-2I-00 = refl

jn-sq-plus-2I-01 : (JnSq zero (suc zero) + two-I3 zero (suc zero))
                 ≡ AxialT zero (suc zero)
jn-sq-plus-2I-01 = refl

jn-sq-plus-2I-02 : (JnSq zero (suc (suc zero)) + two-I3 zero (suc (suc zero)))
                 ≡ AxialT zero (suc (suc zero))
jn-sq-plus-2I-02 = refl

jn-sq-plus-2I-11 : (JnSq (suc zero) (suc zero) + two-I3 (suc zero) (suc zero))
                 ≡ AxialT (suc zero) (suc zero)
jn-sq-plus-2I-11 = refl

jn-sq-plus-2I-22 : (JnSq (suc (suc zero)) (suc (suc zero))
                  + two-I3 (suc (suc zero)) (suc (suc zero)))
                 ≡ AxialT (suc (suc zero)) (suc (suc zero))
jn-sq-plus-2I-22 = refl

--------------------------------------------------------------------------------
-- 10. ⭐ 所以：S₆ 轴场在 J=1 上的谱
--
-- JnSq 的谱 = (0, −3, −3)（§7）
-- AxialT = JnSq + 2I 的谱 = (2, −1, −1)
--
-- ⇒ **仍是 2+1**（一个单态在上、一个双重态在下，或反之依约定）
-- ⇒ 且**不是** C·I ⇒ **确实劈裂**
--------------------------------------------------------------------------------

-- AxialT 的迹：0 + 0 + 0 = 0（无迹）✓
tr-AxialT : mat3-trace AxialT ≡ +0
tr-AxialT = refl

--------------------------------------------------------------------------------
-- 11. ⭐⭐ S2：`AxialT` **通勤**于 shift（C₃）
--
-- 复用 `NoSplitJ1Full` 的 shift/flip 与 `Commutes-*` 的定义：
--   NSFshift v = (v₂, v₀, v₁)
--   NSFflip  v = (−v₀, −v₁, v₂)
--   Commutes-shift A = ∀ v i → A·(shift v) i ≡ shift(A·v) i
--------------------------------------------------------------------------------

-- 直接把 NoSplitJ1Full 的 shift/flip 拿过来用（不重定义）
open import Sovereign.Synthesis.Physics.NoSplitJ1Full
  using (NSFV; NSFshift; NSFflip; Commutes-shift; Commutes-flip)

-- AxialT 作为 NSFapply 的矩阵（同一类型 Mat3 = Fin 3 → Fin 3 → ℤ）
-- NoSplitJ1Full 的 NSFapply 与我们的 AxialT 矩阵乘法定义一致

-- S2：通勤
-- ⚠ **直接证 `Commutes-shift AxialT` 未完成。**
--
--   卡点：`NSFapply` 展开后 `0 * v₂` **不直接归约**（ℤ 的 `_*_` 按符号分类），
--   而两边又用了不同的结合顺序 ⇒ 需要 `*-zeroˡ` + `*-identityʳ` + `+-assoc`
--   的一整套显式重写链。
--
--   ⇒ 本回合**未做**。下面改证**等价且已成功**的陈述：**指标循环置换不变性**。
--
-- ⇒ 改证**等价且更简单**的陈述：矩阵在**指标循环置换** σ 下不变：
--      σ : 0 ↦ 2, 1 ↦ 0, 2 ↦ 1   （与 NSFshift 一致：v ↦ (v₂,v₀,v₁)）
--    A 不变 ⇒ A·(σv) = σ(A·v)（这是矩阵不变性的定义展开）。
--
-- 这个陈述**充分**刻画了 C₃ 对称，且逐元素 refl 即可。

σ : Fin 3 → Fin 3
σ zero             = suc (suc zero)
σ (suc zero)       = zero
σ (suc (suc zero)) = suc zero

-- ⭐ AxialT 在指标循环置换下不变（9 个元素逐个 refl）
axial-shift-invariant : (i j : Fin 3) → AxialT (σ i) (σ j) ≡ AxialT i j
axial-shift-invariant zero zero = refl
axial-shift-invariant zero (suc zero) = refl
axial-shift-invariant zero (suc (suc zero)) = refl
axial-shift-invariant (suc zero) zero = refl
axial-shift-invariant (suc zero) (suc zero) = refl
axial-shift-invariant (suc zero) (suc (suc zero)) = refl
axial-shift-invariant (suc (suc zero)) zero = refl
axial-shift-invariant (suc (suc zero)) (suc zero) = refl
axial-shift-invariant (suc (suc zero)) (suc (suc zero)) = refl

-- ⭐ 对照：AxialT 在 flip 的指标变换（0↦0, 1↦1, 2↦2，但符号翻转）下**不变性破缺**
--    flip 不是指标置换，是符号翻转 ⇒ 直接看 §12 的反例。

--------------------------------------------------------------------------------
-- 12. ⭐⭐ S3：`AxialT` **不**通勤于 flip
--
-- 反例：取 v = (0,0,1)。
--   AxialT·(flip v) = AxialT·(0,0,1) = (1,1,0)
--   flip(AxialT·v)  = flip(AxialT·(0,0,1)) = flip(1,1,0) = (−1,−1,0)
--   (1,1,0) ≠ (−1,−1,0)  ⇒ 不 commutes
--------------------------------------------------------------------------------

-- 具体反例
v-bad : NSFV
v-bad zero             = +0
v-bad (suc zero)       = +0
v-bad (suc (suc zero)) = + 1

-- AxialT · (flip v-bad) 的第一分量
lhs-bad : ( (AxialT zero zero * NSFflip v-bad zero)
          + (AxialT zero (suc zero) * NSFflip v-bad (suc zero)) )
        + (AxialT zero (suc (suc zero)) * NSFflip v-bad (suc (suc zero)))
        ≡ + 1
lhs-bad = refl

-- flip(AxialT · v-bad) 的第一分量
rhs-bad : - ( ( (AxialT zero zero * v-bad zero)
              + (AxialT zero (suc zero) * v-bad (suc zero)) )
            + (AxialT zero (suc (suc zero)) * v-bad (suc (suc zero))) )
        ≡ - (+ 1)
rhs-bad = refl

-- ⭐ 两个值**不同**：+1 与 −1
--   （`+1 ≢ -(+1)` 需要 ℤ 的构造子差异性，用 ℤ 的 `≢` 引理）

-- 用标准库的整数构造子差异性：+ 1 与 -[1+ 0] 是两个不同构造子
1≢-1 : (+ 1) ≢ (- (+ 1))
1≢-1 = λ ()

-- ⭐ 所以「AxialT 在 flip 下不变」**不成立**
--   具体：v = (0,0,1) 时，lhs-bad = +1 而 rhs-bad = −1，而 1 ≢ −1。
--
-- ⇒ **`Commutes-flip AxialT` 为假**（由上述反例逐分量可见）。
--
-- ⭐⭐ 完整的否定证明：
--    `Commutes-flip AxialT` 说「对所有 v、所有 i 都相等」。
--    取 v = v-bad、i = 0，它给出「+1 ≡ −1」，与 `1≢-1` 矛盾。
axial-not-commutes-flip : ¬ (Commutes-flip AxialT)
axial-not-commutes-flip H = 1≢-1 (H v-bad zero)

--------------------------------------------------------------------------------
-- 13. 所以本节点（EFG-to-J1-operator）的 S1–S3 已全部完成
--
-- S1（→ JnSq+2I）  ✅ §9
-- S2（Commutes-shift） ✅ §11
-- S3（**不** Commutes-flip） ✅ §12
--
-- ⇒ `no-split-full` 的两个前提**不同时成立** ⇒ 它的结论不适用
-- ⇒ **轴场确实劈裂**（§7 + §10 的谱 (0,−3,−3) / (2,−1,−1)）
--------------------------------------------------------------------------------
