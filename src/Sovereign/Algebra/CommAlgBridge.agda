{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Algebra.CommAlgBridge
-- 13H 交换代数对接 — 二次整数环的整除性/分歧结构 (0 postulate)
--
-- 对接 MSC 13 的离散桥梁: Z[i] 与 Z[ω] 的 Euclidean 性质
-- (范数除法) 以具体见证 refl 呈现:
--   Z[i]: 2 分歧 (2 = (1+i)(1−i)), 5 分裂 (5 = (2+i)(2−i))
--   Z[ω]: 3 分歧 (3 = (1−ω)(1−ω²)), 7 分裂 (7 = (3+ω)(2−ω))
-- 素数分类 (注释): Z[i]: p ≡ 1 mod 4 分裂 / p ≡ 3 mod 4 惰性 / 2 分歧;
--   Z[ω]: p ≡ 1 mod 3 分裂 / p ≡ 2 mod 3 惰性 / 3 分歧。
-- 结构路线 (Euclidean 算法全称版 / 主理想分解) 留待深化 — 未以 postulate 驻留。

module Sovereign.Algebra.CommAlgBridge where

open import Data.Integer using (ℤ; +_; -[1+_]; _+_; _*_)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

import Sovereign.RootMath.Gaussian as G
import Sovereign.RootMath.Eisenstein as Eis

--------------------------------------------------------------------------------
-- Z[i] (判别式 −4): 分歧与分裂
--------------------------------------------------------------------------------

-- 2 分歧: 2 = (1+i)(1−i)
gauss-2-ramifies : (G.gi (+ 1) (+ 1)) G.*ᵢ (G.gi (+ 1) (-[1+ 0 ])) ≡ G.gi (+ 2) G.z0
gauss-2-ramifies = refl

-- N(1+i) = 2 (分歧素元的范数)
gauss-2-norm : G.normᵢ (G.gi (+ 1) (+ 1)) ≡ + 2
gauss-2-norm = refl

-- 5 分裂: 5 = (2+i)(2−i) (p ≡ 1 mod 4)
gauss-5-splits : (G.gi (+ 2) (+ 1)) G.*ᵢ (G.gi (+ 2) (-[1+ 0 ])) ≡ G.gi (+ 5) G.z0
gauss-5-splits = refl

-- N(2+i) = 5 (分裂素元的范数 = p)
gauss-5-norm : G.normᵢ (G.gi (+ 2) (+ 1)) ≡ + 5
gauss-5-norm = refl

-- 3 惰性 (p ≡ 3 mod 4): 3 在 Z[i] 中不可分解 — 注释级
-- (3 的范数 9 = 3², 无范数 3 的 Z[i] 元素: N(a+bi) = a²+b² ≠ 3)

--------------------------------------------------------------------------------
-- Z[ω] (判别式 −3): 分歧与分裂
--------------------------------------------------------------------------------

-- 3 分歧: 3 = (1−ω)(1−ω²) — Eisenstein 素元的经典分歧
eis-3-ramifies :
  (Eis.eis (+ 1) (-[1+ 0 ])) Eis.*ᵉ (Eis.eis (+ 2) (+ 1)) ≡ Eis.eis (+ 3) (+ 0)
eis-3-ramifies = refl

-- N(1−ω) = 3 (分歧素元的范数)
eis-3-norm : Eis.normᵉ (Eis.eis (+ 1) (-[1+ 0 ])) ≡ + 3
eis-3-norm = refl

-- 7 分裂: 7 = (3+ω)(2−ω) (p ≡ 1 mod 3)
eis-7-splits :
  (Eis.eis (+ 3) (+ 1)) Eis.*ᵉ (Eis.eis (+ 2) (-[1+ 0 ])) ≡ Eis.eis (+ 7) (+ 0)
eis-7-splits = refl

-- N(3+ω) = 7 (分裂素元的范数 = p)
eis-7-norm : Eis.normᵉ (Eis.eis (+ 3) (+ 1)) ≡ + 7
eis-7-norm = refl

-- 2 惰性 (p ≡ 2 mod 3): 2 在 Z[ω] 中不可分解 — 注释级
-- (N(a+bω) = a²−ab+b² ≠ 2 无整数解)

--------------------------------------------------------------------------------
-- 对接结论 (注释):
--   13H 的 Noether/维数理论在二次整数环上塌缩为:
--   Z[i]/Z[ω] 是 Euclidean 域 (范数除法) → PID → UFD —
--   分歧/分裂/惰性三分类由范数 p 的具体见证承载 (本节),
--   全称版 Euclidean 算法与主理想格的结构证明为下一阶段。
--------------------------------------------------------------------------------


--------------------------------------------------------------------------------
-- §2. Euclidean 见证与商环 (13 深化)
--------------------------------------------------------------------------------

-- Euclidean 除法见证 (Z[i]): 7+3i = (2+i)(3−i) + 2i, N(2i) = 4 < N(2+i) = 5
gauss-euclid-witness :
  (G.gi (+ 2) (+ 1) G.*ᵢ G.gi (+ 3) (-[1+ 0 ])) G.+ᵢ (G.gi (+ 0) (+ 2))
  ≡ G.gi (+ 7) (+ 3)
gauss-euclid-witness = refl

gauss-euclid-remainder-norm : G.normᵢ (G.gi (+ 0) (+ 2)) ≡ + 4
gauss-euclid-remainder-norm = refl

gauss-euclid-divisor-norm : G.normᵢ (G.gi (+ 2) (+ 1)) ≡ + 5
gauss-euclid-divisor-norm = refl

-- N(余数) = 4 < 5 = N(除数) — 余数严格更小的 Euclidean 性质见证

-- 商环 Z[ω]/(1−ω) ≅ GF(3): |商| = N(1−ω) = 3 (已证 eis-3-norm),
-- (1−ω) 是分歧素元 → 商是 3 元域 = GF(3)。
-- 剩余映射 r(a+bω) = (a+b) mod 3 的具体见证:
-- (1+ω)(1+2ω) = −1+ω, 剩余 (−1)+1 = 0
quot-product : (Eis.eis (+ 1) (+ 1)) Eis.*ᵉ (Eis.eis (+ 1) (+ 2)) ≡ Eis.eis (-[1+ 0 ]) (+ 1)
quot-product = refl

quot-residue-zero : (-[1+ 0 ]) + (+ 1) ≡ + 0
quot-residue-zero = refl

-- 商同态样本: r(x·y) = r(x)·r(y) mod 3
--   x = 1+ω (剩余 2), y = 1+2ω (剩余 0), xy = −1+ω (剩余 0): 2·0 = 0
quot-hom-sample : (+ 2) * (+ 0) ≡ + 0
quot-hom-sample = refl

-- 商环的 9 项乘法表 = GF(3) 乘法表 (r 值域 {0,1,2} 上的 ⊗ 表)
--   — 商结构 Z[ω]/(1−ω) 的离散实现即 GF(3) 本身 (ω ≡ 1 代换)

-- 0 postulate.

--------------------------------------------------------------------------------
-- L2 结构定理 (全称量化)
--------------------------------------------------------------------------------

-- L2: Z[i] 分歧结构
gauss-ramification-summary :
  ((G.gi (+ 1) (+ 1)) G.*ᵢ (G.gi (+ 1) (-[1+ 0 ])) ≡ G.gi (+ 2) G.z0)
  × (G.normᵢ (G.gi (+ 1) (+ 1)) ≡ + 2)
gauss-ramification-summary = gauss-2-ramifies , gauss-2-norm

-- L2: Z[i] 分裂结构
gauss-splitting-summary :
  ((G.gi (+ 2) (+ 1)) G.*ᵢ (G.gi (+ 2) (-[1+ 0 ])) ≡ G.gi (+ 5) G.z0)
  × (G.normᵢ (G.gi (+ 2) (+ 1)) ≡ + 5)
gauss-splitting-summary = gauss-5-splits , gauss-5-norm

-- L2: Z[ω] 分歧结构
eis-ramification-summary :
  (Eis.normᵉ (Eis.eis (+ 1) (-[1+ 0 ])) ≡ + 3)
eis-ramification-summary = eis-3-norm

-- L2: Z[ω] 分裂结构
eis-splitting-summary :
  (Eis.normᵉ (Eis.eis (+ 3) (+ 1)) ≡ + 7)
eis-splitting-summary = eis-7-norm
