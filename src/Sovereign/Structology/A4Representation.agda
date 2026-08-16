{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Structology.A4Representation
-- A₄ 表示论: 不可约表示 {1, 1′, 1″, 3} + 特征标正交性 (0 postulate, 全 refl)
--
-- 三代费米子的代数起源: A₄ 的三维不可约表示在 Z₃ 子群上分支为
--   1 ⊕ 1′ ⊕ 1″ — 三代不是可调参数, 而是 A₄ 群结构的刚性预测。
--
-- 诚实边界 (必须记录): A₄ 的 ω 特征需要 3 阶元素 (ω³=1), 而 GF(9) 的
--   非零元是 8 阶循环群 (3∤8), 无 3 阶元素。因此本模块工作在 Z[ω] 环
--   (特征 0) 上, 与 GF(9) 的 Frobenius 共轭 (4 阶) 各自服务不同目的:
--     GF(9) 负责 Frobenius 共轭 (4 阶, E⊥B 90°)
--     Z[ω]  负责 A₄ 的 3 阶对称 (三代费米子)
--   两者不可互相替代。

module Sovereign.Structology.A4Representation where

open import Data.Nat using (ℕ; zero; suc) renaming (_+_ to _+ℕ_; _*_ to _*ℕ_)
open import Data.Integer.Base using (ℤ; +_; -[1+_]; _+_; _-_; _*_; -_)
open import Data.Fin using (Fin; zero; suc)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂)

------------------------------------------------------------------------------
-- 1. Z[ω] 环: ω² = -ω - 1, ω³ = 1
------------------------------------------------------------------------------

record Zω : Set where
  constructor mkZω
  field
    a : ℤ   -- 实部系数
    b : ℤ   -- ω 系数

open Zω

-- 零元与一
zeroZω : Zω
zeroZω = mkZω (+ 0) (+ 0)

oneZω : Zω
oneZω = mkZω (+ 1) (+ 0)

-- ω 生成元
ω : Zω
ω = mkZω (+ 0) (+ 1)

-- ω² = -1 - ω
ω² : Zω
ω² = mkZω -[1+ 0 ] -[1+ 0 ]

-- 加法
addZω : Zω → Zω → Zω
addZω (mkZω a b) (mkZω c d) = mkZω (a + c) (b + d)

-- 负元
negZω : Zω → Zω
negZω (mkZω a b) = mkZω (- a) (- b)

-- 减法
subZω : Zω → Zω → Zω
subZω x y = addZω x (negZω y)

-- 乘法: (a+bω)(c+dω) = (ac-bd) + (ad+bc-bd)ω
mulZω : Zω → Zω → Zω
mulZω (mkZω a b) (mkZω c d) =
  mkZω (a * c - b * d) (a * d + b * c - b * d)

-- 共轭: (a+bω)* = (a-b) - bω
conjZω : Zω → Zω
conjZω (mkZω a b) = mkZω (a - b) (- b)

------------------------------------------------------------------------------
-- 2. 核心恒等式: 1 + ω + ω² = 0 与 ω³ = 1
------------------------------------------------------------------------------

omega-sum-zero : addZω (addZω ω² ω) oneZω ≡ zeroZω
omega-sum-zero = refl

omega-cubed : mulZω (mulZω ω ω) ω ≡ oneZω
omega-cubed = refl

omega-squared-form : ω² ≡ addZω (negZω oneZω) (negZω ω)
omega-squared-form = refl

------------------------------------------------------------------------------
-- 3. A₄ 特征标表
------------------------------------------------------------------------------

ConjClass : Set
ConjClass = Fin 4

Irrep : Set
Irrep = Fin 4

classSize : ConjClass → ℕ
classSize zero = 1
classSize (suc zero) = 4
classSize (suc (suc zero)) = 4
classSize (suc (suc (suc zero))) = 3

-- 平凡表示 χ₁
chi1 : ConjClass → Zω
chi1 _ = oneZω

-- 一维表示 χ₁′ (ω 特征)
chi1' : ConjClass → Zω
chi1' zero = oneZω
chi1' (suc zero) = ω
chi1' (suc (suc zero)) = ω²
chi1' (suc (suc (suc zero))) = oneZω

-- 一维表示 χ₁″ (ω² 特征)
chi1'' : ConjClass → Zω
chi1'' zero = oneZω
chi1'' (suc zero) = ω²
chi1'' (suc (suc zero)) = ω
chi1'' (suc (suc (suc zero))) = oneZω

-- 三维表示 χ₃
chi3 : ConjClass → Zω
chi3 zero = mkZω (+ 3) (+ 0)
chi3 (suc zero) = zeroZω
chi3 (suc (suc zero)) = zeroZω
chi3 (suc (suc (suc zero))) = mkZω -[1+ 0 ] (+ 0)

-- 特征标函数表
chi : Irrep → ConjClass → Zω
chi zero = chi1
chi (suc zero) = chi1'
chi (suc (suc zero)) = chi1''
chi (suc (suc (suc zero))) = chi3

------------------------------------------------------------------------------
-- 4. 主定理 1: 维数平方和 = 12
------------------------------------------------------------------------------

dim-squared-sum : (1 +ℕ 1 +ℕ 1 +ℕ 9) ≡ 12
dim-squared-sum = refl

------------------------------------------------------------------------------
-- 5. 主定理 2: 列正交性 (第一正交关系)
------------------------------------------------------------------------------

colInnerProduct : ConjClass → ConjClass → Zω
colInnerProduct c d =
  addZω
    (addZω
      (mulZω (chi1 c) (conjZω (chi1 d)))
      (mulZω (chi1' c) (conjZω (chi1' d))))
    (addZω
      (mulZω (chi1'' c) (conjZω (chi1'' d)))
      (mulZω (chi3 c) (conjZω (chi3 d))))

-- 对角线值: 12/|class|
column-orth-diag :
  (colInnerProduct zero zero ≡ mkZω (+ 12) (+ 0)) ×
  (colInnerProduct (suc zero) (suc zero) ≡ mkZω (+ 3) (+ 0)) ×
  (colInnerProduct (suc (suc zero)) (suc (suc zero)) ≡ mkZω (+ 3) (+ 0)) ×
  (colInnerProduct (suc (suc (suc zero))) (suc (suc (suc zero))) ≡ mkZω (+ 4) (+ 0))
column-orth-diag = refl , refl , refl , refl

-- 非对角线值: 全部为零
column-orth-offdiag :
  (colInnerProduct zero (suc zero) ≡ zeroZω) ×
  (colInnerProduct zero (suc (suc zero)) ≡ zeroZω) ×
  (colInnerProduct zero (suc (suc (suc zero))) ≡ zeroZω) ×
  (colInnerProduct (suc zero) zero ≡ zeroZω) ×
  (colInnerProduct (suc zero) (suc (suc zero)) ≡ zeroZω) ×
  (colInnerProduct (suc zero) (suc (suc (suc zero))) ≡ zeroZω) ×
  (colInnerProduct (suc (suc zero)) zero ≡ zeroZω) ×
  (colInnerProduct (suc (suc zero)) (suc zero) ≡ zeroZω) ×
  (colInnerProduct (suc (suc zero)) (suc (suc (suc zero))) ≡ zeroZω) ×
  (colInnerProduct (suc (suc (suc zero))) zero ≡ zeroZω) ×
  (colInnerProduct (suc (suc (suc zero))) (suc zero) ≡ zeroZω) ×
  (colInnerProduct (suc (suc (suc zero))) (suc (suc zero)) ≡ zeroZω)
column-orth-offdiag =
  refl , refl , refl , refl , refl , refl ,
  refl , refl , refl , refl , refl , refl

------------------------------------------------------------------------------
-- 6. 主定理 3: 行正交性 (第二正交关系)
------------------------------------------------------------------------------

rowInnerProduct : Irrep → Irrep → Zω
rowInnerProduct i j =
  addZω
    (mulZω (mkZω (+ 1) (+ 0)) (mulZω (chi i zero) (conjZω (chi j zero))))
    (addZω
      (mulZω (mkZω (+ 4) (+ 0)) (mulZω (chi i (suc zero)) (conjZω (chi j (suc zero)))))
      (addZω
        (mulZω (mkZω (+ 4) (+ 0)) (mulZω (chi i (suc (suc zero))) (conjZω (chi j (suc (suc zero))))))
        (mulZω (mkZω (+ 3) (+ 0)) (mulZω (chi i (suc (suc (suc zero)))) (conjZω (chi j (suc (suc (suc zero)))))))))

row-orth-diag :
  (rowInnerProduct zero zero ≡ mkZω (+ 12) (+ 0)) ×
  (rowInnerProduct (suc zero) (suc zero) ≡ mkZω (+ 12) (+ 0)) ×
  (rowInnerProduct (suc (suc zero)) (suc (suc zero)) ≡ mkZω (+ 12) (+ 0)) ×
  (rowInnerProduct (suc (suc (suc zero))) (suc (suc (suc zero))) ≡ mkZω (+ 12) (+ 0))
row-orth-diag = refl , refl , refl , refl

row-orth-offdiag :
  (rowInnerProduct zero (suc zero) ≡ zeroZω) ×
  (rowInnerProduct zero (suc (suc zero)) ≡ zeroZω) ×
  (rowInnerProduct zero (suc (suc (suc zero))) ≡ zeroZω) ×
  (rowInnerProduct (suc zero) zero ≡ zeroZω) ×
  (rowInnerProduct (suc zero) (suc (suc zero)) ≡ zeroZω) ×
  (rowInnerProduct (suc zero) (suc (suc (suc zero))) ≡ zeroZω) ×
  (rowInnerProduct (suc (suc zero)) zero ≡ zeroZω) ×
  (rowInnerProduct (suc (suc zero)) (suc zero) ≡ zeroZω) ×
  (rowInnerProduct (suc (suc zero)) (suc (suc (suc zero))) ≡ zeroZω) ×
  (rowInnerProduct (suc (suc (suc zero))) zero ≡ zeroZω) ×
  (rowInnerProduct (suc (suc (suc zero))) (suc zero) ≡ zeroZω) ×
  (rowInnerProduct (suc (suc (suc zero))) (suc (suc zero)) ≡ zeroZω)
row-orth-offdiag =
  refl , refl , refl , refl , refl , refl ,
  refl , refl , refl , refl , refl , refl

------------------------------------------------------------------------------
-- 7. 主定理 4: 置换表示分解 (4 = 1 + 3)
------------------------------------------------------------------------------

chi-perm : ConjClass → Zω
chi-perm zero = mkZω (+ 4) (+ 0)
chi-perm (suc zero) = mkZω (+ 1) (+ 0)
chi-perm (suc (suc zero)) = mkZω (+ 1) (+ 0)
chi-perm (suc (suc (suc zero))) = zeroZω

perm-decompose :
  (chi-perm zero ≡ addZω (chi1 zero) (chi3 zero)) ×
  (chi-perm (suc zero) ≡ addZω (chi1 (suc zero)) (chi3 (suc zero))) ×
  (chi-perm (suc (suc zero)) ≡ addZω (chi1 (suc (suc zero))) (chi3 (suc (suc zero)))) ×
  (chi-perm (suc (suc (suc zero))) ≡ addZω (chi1 (suc (suc (suc zero)))) (chi3 (suc (suc (suc zero)))))
perm-decompose = refl , refl , refl , refl

------------------------------------------------------------------------------
-- 8. 主定理 5: Z₃ 分支规则 (3 = 1 + 1 + 1)
------------------------------------------------------------------------------

branching-Z3 :
  (chi3 zero ≡ addZω (addZω (chi1 zero) (chi1' zero)) (chi1'' zero)) ×
  (chi3 (suc zero) ≡ addZω (addZω (chi1 (suc zero)) (chi1' (suc zero))) (chi1'' (suc zero))) ×
  (chi3 (suc (suc zero)) ≡ addZω (addZω (chi1 (suc (suc zero))) (chi1' (suc (suc zero)))) (chi1'' (suc (suc zero))))
branching-Z3 = refl , refl , refl

-- 0 postulate.
