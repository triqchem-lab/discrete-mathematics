{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.RootMath.Gaussian
-- 高斯整数 Z[i] — 毕达哥拉斯复数线的判别式 −4 分支 (0 postulate)
--
-- 数学背景:
--   i² = −1, 元素 (a,b) = a+bi, a,b ∈ ℤ — 方格点阵 (90°)
--   乘法: (a,b)(c,d) = (ac−bd, ad+bc)
--   范数: N = a²+b² (毕达哥拉斯二次型 — 勾股数 = 范数平方)
--   共轭: conj(a,b) = (a,−b)
--   单位群 = {±1, ±i} ≅ C₄ (生成元 i)
--
-- 与 Eisenstein (Z[ω], 判别式 −3, 60°) 的对称:
--   Z[i] 判别式 −4 (90° 格) ↔ Z[ω] 判别式 −3 (60° 格)
--   范数 a²+b² ↔ a²−ab+b² — 毕达哥拉斯二次型的两个分歧
--
-- 核心定理 (勾股三元组生成):
--   (m+ni)² = (m²−n²) + 2mn·i ⟹ 三元组 (m²−n², 2mn, m²+n²) 满足
--   (m²−n²)² + (2mn)² = (m²+n²)² — 全部本原勾股数的 Gauss 生成
--
-- 本模块: 具体对 (m,n) 的 ℤ 字面 refl (有限穷举风格);
-- 符号化范数乘性 N(xy)=N(x)N(y) 与 Brahmagupta–Fibonacci 恒等式的
-- 结构路线 (norm-form/conj-mul/assoc 链) 镜像 Eisenstein.agda norm-mul,
-- 留待深化 (见 docs/毕达哥拉斯复数线-高维几何代数拓扑.md §4)。

module Sovereign.RootMath.Gaussian where

open import Data.Integer using (ℤ; +_; -[1+_]; _+_; _-_; _*_; -_)
open import Data.Nat using (ℕ; _%_)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂)

z0 : ℤ
z0 = + 0

z1 : ℤ
z1 = + 1

--------------------------------------------------------------------------------
-- §1. 高斯整数环 Z[i]
--------------------------------------------------------------------------------

data Gaussian : Set where
  gi : ℤ → ℤ → Gaussian

-- 加法
_+ᵢ_ : Gaussian → Gaussian → Gaussian
gi a b +ᵢ gi c d = gi (a + c) (b + d)

-- 取负
-ᵢ_ : Gaussian → Gaussian
-ᵢ gi a b = gi (- a) (- b)

-- 乘法: (a+bi)(c+di) = (ac−bd) + (ad+bc)i — 利用 i² = −1
_*ᵢ_ : Gaussian → Gaussian → Gaussian
gi a b *ᵢ gi c d = gi (a * c - b * d) (a * d + b * c)

-- 共轭: conj(a+bi) = a − bi
conjᵢ : Gaussian → Gaussian
conjᵢ (gi a b) = gi a (- b)

-- 范数: N = a² + b² ≥ 0 (毕达哥拉斯二次型)
normᵢ : Gaussian → ℤ
normᵢ (gi a b) = a * a + b * b

0ᵢ : Gaussian
0ᵢ = gi z0 z0

1ᵢ : Gaussian
1ᵢ = gi z1 z0

iᵤ : Gaussian       -- i
iᵤ = gi z0 z1

infixl 25 _*ᵢ_
infixl 20 _+ᵢ_

-- i² = −1
i-square : iᵤ *ᵢ iᵤ ≡ gi (-[1+ 0 ]) z0
i-square = refl

-- i⁴ = 1
i-fourth : (iᵤ *ᵢ iᵤ) *ᵢ (iᵤ *ᵢ iᵤ) ≡ 1ᵢ
i-fourth = refl

--------------------------------------------------------------------------------
-- §2. 单位群 ≅ C₄: {1, i, −1, −i}, 生成元 i
--------------------------------------------------------------------------------

unit1  : Gaussian ; unit1  = gi z1 z0
uniti  : Gaussian ; uniti  = gi z0 z1
unitm1 : Gaussian ; unitm1 = gi (-[1+ 0 ]) z0
unitmi : Gaussian ; unitmi = gi z0 (-[1+ 0 ])

-- i 的 4 次幂循环: 1 → i → −1 → −i → 1
unit-pow : ℕ → Gaussian
unit-pow n with n % 4
... | 0 = unit1
... | 1 = uniti
... | 2 = unitm1
... | _ = unitmi

unit-pow-0 : unit-pow 0 ≡ unit1  ; unit-pow-0 = refl
unit-pow-1 : unit-pow 1 ≡ uniti  ; unit-pow-1 = refl
unit-pow-2 : unit-pow 2 ≡ unitm1 ; unit-pow-2 = refl
unit-pow-3 : unit-pow 3 ≡ unitmi ; unit-pow-3 = refl
unit-pow-4 : unit-pow 4 ≡ unit1  ; unit-pow-4 = refl

-- 单位范数均为 1
unit-norm-1  : normᵢ unit1  ≡ z1 ; unit-norm-1  = refl
unit-norm-i  : normᵢ uniti  ≡ z1 ; unit-norm-i  = refl
unit-norm-m1 : normᵢ unitm1 ≡ z1 ; unit-norm-m1 = refl
unit-norm-mi : normᵢ unitmi ≡ z1 ; unit-norm-mi = refl

-- 单位互逆 (C₄)
unit-inv-i  : uniti *ᵢ unitmi ≡ 1ᵢ ; unit-inv-i  = refl
unit-inv-mi : unitmi *ᵢ uniti ≡ 1ᵢ ; unit-inv-mi = refl
unit-inv-m1 : unitm1 *ᵢ unitm1 ≡ 1ᵢ ; unit-inv-m1 = refl

--------------------------------------------------------------------------------
-- §3. 勾股三元组生成定理: (m+ni)² = (m²−n²) + 2mn·i
--------------------------------------------------------------------------------

-- (2+i)² = 3+4i, N = 25 = 5² — 勾股三元组 (3, 4, 5)
pyth-3-4-5-square : gi (+ 2) z1 *ᵢ gi (+ 2) z1 ≡ gi (+ 3) (+ 4)
pyth-3-4-5-square = refl

pyth-3-4-5-norm : normᵢ (gi (+ 2) z1 *ᵢ gi (+ 2) z1) ≡ + 25
pyth-3-4-5-norm = refl

-- 恒等式: 3² + 4² = 5² (最本原勾股数)
pyth-3-4-5-identity : + 3 * + 3 + + 4 * + 4 ≡ + 5 * + 5
pyth-3-4-5-identity = refl

-- (3+2i)² = 5+12i, N = 169 = 13² — 勾股三元组 (5, 12, 13)
pyth-5-12-13-square : gi (+ 3) (+ 2) *ᵢ gi (+ 3) (+ 2) ≡ gi (+ 5) (+ 12)
pyth-5-12-13-square = refl

pyth-5-12-13-identity : + 5 * + 5 + + 12 * + 12 ≡ + 13 * + 13
pyth-5-12-13-identity = refl

-- (4+i)² = 15+8i — 勾股三元组 (15, 8, 17)
pyth-15-8-17-square : gi (+ 4) z1 *ᵢ gi (+ 4) z1 ≡ gi (+ 15) (+ 8)
pyth-15-8-17-square = refl

pyth-15-8-17-identity : + 15 * + 15 + + 8 * + 8 ≡ + 17 * + 17
pyth-15-8-17-identity = refl

-- (5+2i)² = 21+20i — 勾股三元组 (21, 20, 29)
pyth-21-20-29-square : gi (+ 5) (+ 2) *ᵢ gi (+ 5) (+ 2) ≡ gi (+ 21) (+ 20)
pyth-21-20-29-square = refl

pyth-21-20-29-identity : + 21 * + 21 + + 20 * + 20 ≡ + 29 * + 29
pyth-21-20-29-identity = refl

-- 生成公式的具体见证: (m,n) = (3,2) → 股 = 2mn = 12 — 十二律 12 的
-- 二次型读法候选 (先审计后定论, 见 P2-5 文档 §4 第 4 项, 此处仅算术事实)
twelve-as-2mn : + 2 * + 3 * + 2 ≡ + 12
twelve-as-2mn = refl

--------------------------------------------------------------------------------
-- §4. 范数乘性 (具体见证) 与 Brahmagupta–Fibonacci 恒等式
--------------------------------------------------------------------------------

-- N((2+i)(3+2i)) = N(4+7i) = 65 = 5·13 = N(2+i)·N(3+2i)
norm-mul-sample : normᵢ (gi (+ 2) z1 *ᵢ gi (+ 3) (+ 2)) ≡ + 65
norm-mul-sample = refl

norm-mul-factor : normᵢ (gi (+ 2) z1) * normᵢ (gi (+ 3) (+ 2)) ≡ + 65
norm-mul-factor = refl

norm-mul-sample-eq : normᵢ (gi (+ 2) z1 *ᵢ gi (+ 3) (+ 2))
                   ≡ normᵢ (gi (+ 2) z1) * normᵢ (gi (+ 3) (+ 2))
norm-mul-sample-eq = refl

-- Brahmagupta–Fibonacci: (a²+b²)(c²+d²) = (ac−bd)² + (ad+bc)²
--   (a,b,c,d) = (2,1,3,2): 5·13 = 65 = 4² + 7²
bf-identity-sample : (+ 2 * + 2 + + 1 * + 1) * (+ 3 * + 3 + + 2 * + 2)
                   ≡ (+ 2 * + 3 - + 1 * + 2) * (+ 2 * + 3 - + 1 * + 2)
                   + (+ 2 * + 2 + + 1 * + 3) * (+ 2 * + 2 + + 1 * + 3)
bf-identity-sample = refl

-- 共轭同态 (具体见证): conj((2+i)(3+2i)) = conj(2+i)·conj(3+2i)
conj-mul-sample : conjᵢ (gi (+ 2) z1 *ᵢ gi (+ 3) (+ 2))
                ≡ conjᵢ (gi (+ 2) z1) *ᵢ conjᵢ (gi (+ 3) (+ 2))
conj-mul-sample = refl

-- 0 postulate.
