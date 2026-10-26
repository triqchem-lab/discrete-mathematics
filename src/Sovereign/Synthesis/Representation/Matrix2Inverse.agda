{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Synthesis.Representation.Matrix2Inverse
-- **GF(3) 上 2×2 矩阵的逆理论**：行列式、伴随矩阵（adjugate）、
-- 以及 2×2 的 Cayley–Hamilton 恒等式 `M · adj M = det M · I`（双侧）。
--
-- 数学背景：
--   2×2 矩阵 M = [[a,b],[c,d]] 的伴随矩阵 adj M = [[d,−b],[−c,a]] 满足
--       M · adj M = adj M · M = (det M) · I
--   这是 Cayley–Hamilton 的 2×2 特例（特征多项式 x² − tr·x + det）。
--   当 det M = 1 时，adj M 就是 M 的逆——**不需要做除法**，
--   这正是 GF(3) 上唯一可行的写法（det 只有 0/1/2，而 2 可逆，1 可逆，0 不可逆）。
--
-- 为什么是 GF(3) 具体版而不是抽象交换环版：
--   · 库里只有 `CommSemiring`（**无 neg**）与 `Ring`（**无 mul-comm**），
--     没有「交换环」记录；抽象版要先建 CommRing 记录 + 约 10 条取反/消去泛型引理；
--   · 消费方只有 SL(2,F₃)，且论域有限（Fin 3）⇒ 按库的策略 A「穷举优于归纳」，
--     9-case refl 比泛型链更短更稳；
--   · 抽象版留作后续（接口已按可泛化的形状写：`_*s_` 与 `I2` 不依赖具体域）。
--
-- 包含：det3 / adj / _*s_ / 四条分量引理 / mul-adj / adj-mul / det≡1 推论
--
-- 策略：代数链（分量级 ≤4 步）+ 9-case 穷举（neg/mul 相容律，见 Fin3Semiring）
-- 0 postulate / 0 hole。

module Sovereign.Synthesis.Representation.Matrix2Inverse where

open import Data.Fin using (Fin; zero; suc)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂)

open import Sovereign.Synthesis.Representation.Fin3Semiring using
  ( neg3
  ; neg3-zero; neg3-inv; neg3-add; neg3-invol; neg3-mulˡ; neg3-mulʳ
  ; add3-comm; add3-idˡ; add3-idʳ; mul3-comm; mul3-idʳ; mul3-zeroʳ
  ; I2; mat-assoc; mat-idˡ; mat-idʳ; fin3CS )
-- ⚠ `using` 导入的符号不再二次导出 ⇒ 运算本体直接从源头取
open import Sovereign.Synthesis.Representation.SL23Cayley using (Mat2; mulMat2; add3; mul3)
open import Sovereign.Algebra.LinearAlgebra.Matrix2 using (mkMat2; m00; m01; m10; m11)
open import Sovereign.Algebra.LinearAlgebra.Matrix2Laws using (mat2-cong)

--------------------------------------------------------------------------------
-- 1. 行列式与伴随矩阵
--------------------------------------------------------------------------------

-- det [[a,b],[c,d]] = a·d − b·c = a·d + (−b)·c
det3 : Mat2 → Fin 3
det3 M = add3 (mul3 (m00 M) (m11 M)) (mul3 (neg3 (m01 M)) (m10 M))

-- adj [[a,b],[c,d]] = [[d,−b],[−c,a]]
adj : Mat2 → Mat2
adj (mkMat2 a b c d) = mkMat2 d (neg3 b) (neg3 c) a

-- 标量乘
_*s_ : Fin 3 → Mat2 → Mat2
k *s (mkMat2 a b c d) = mkMat2 (mul3 k a) (mul3 k b) (mul3 k c) (mul3 k d)

--------------------------------------------------------------------------------
-- 2. M · adj M 的四个分量（目标形 = det · I）
--
--   M·adj = [[ a·d + b·(−c),  a·(−b) + b·a ],
--            [ c·d + d·(−c),  c·(−b) + d·a ]]
--   目标 = [[det, 0], [0, det]]
--------------------------------------------------------------------------------

-- 分量 00：a·d + b·(−c) ≡ det
e00 : ∀ a b c d →
      add3 (mul3 a d) (mul3 b (neg3 c))
    ≡ add3 (mul3 a d) (mul3 (neg3 b) c)
e00 a b c d =
  trans (cong (add3 (mul3 a d)) (neg3-mulʳ b c))                    -- b·(−c) → −(b·c)
    (trans (cong (add3 (mul3 a d)) (sym (neg3-mulˡ b c)))           -- −(b·c) → (−b)·c
           refl)

-- 分量 01：a·(−b) + b·a ≡ 0
e01 : ∀ a b → add3 (mul3 a (neg3 b)) (mul3 b a) ≡ zero
e01 a b =
  trans (cong (λ u → add3 u (mul3 b a)) (neg3-mulʳ a b))            -- a·(−b) → −(a·b)
    (trans (cong (λ u → add3 (neg3 (mul3 a b)) u) (mul3-comm b a))  -- b·a → a·b
      (trans (add3-comm (neg3 (mul3 a b)) (mul3 a b))               -- 换位成 neg3-inv 的形状
             (neg3-inv (mul3 a b))))                                -- −x + x → 0

-- 分量 10：c·d + d·(−c) ≡ 0
e10 : ∀ c d → add3 (mul3 c d) (mul3 d (neg3 c)) ≡ zero
e10 c d =
  trans (cong (add3 (mul3 c d)) (neg3-mulʳ d c))                    -- d·(−c) → −(d·c)
    (trans (cong (λ u → add3 (mul3 c d) (neg3 u)) (mul3-comm d c))  -- d·c → c·d
      (neg3-inv (mul3 c d)))

-- 分量 11：c·(−b) + d·a ≡ det（先交换两项再对齐 det 的写法）
e11 : ∀ a b c d →
      add3 (mul3 c (neg3 b)) (mul3 d a)
    ≡ add3 (mul3 a d) (mul3 (neg3 b) c)
e11 a b c d =
  trans (cong (λ u → add3 u (mul3 d a)) (neg3-mulʳ c b))            -- c·(−b) → −(c·b)
    (trans (add3-comm (neg3 (mul3 c b)) (mul3 d a))                 -- 换位
      (trans (cong₂ add3 (mul3-comm d a) (cong neg3 (mul3-comm c b)))
             (cong (λ u → add3 (mul3 a d) u) (sym (neg3-mulˡ b c)))))

--------------------------------------------------------------------------------
-- 3. 主恒等式：M · adj M ≡ det M · I
--------------------------------------------------------------------------------

mul-adj : ∀ M → mulMat2 M (adj M) ≡ det3 M *s I2
mul-adj (mkMat2 a b c d) =
  mat2-cong fin3CS
    (trans (e00 a b c d) (sym (mul3-idʳ (det3 (mkMat2 a b c d)))))
    (trans (e01 a b) (sym (mul3-zeroʳ (det3 (mkMat2 a b c d)))))
    (trans (e10 c d) (sym (mul3-zeroʳ (det3 (mkMat2 a b c d)))))
    (trans (e11 a b c d) (sym (mul3-idʳ (det3 (mkMat2 a b c d)))))

--------------------------------------------------------------------------------
-- 4. 另一侧：adj M · M ≡ det M · I
--
--   adj·M = [[ d·a + (−b)·c,  d·b + (−b)·d ],
--            [ (−c)·a + a·c, (−c)·b + a·d ]]
--------------------------------------------------------------------------------

f00 : ∀ a b c d →
      add3 (mul3 d a) (mul3 (neg3 b) c)
    ≡ add3 (mul3 a d) (mul3 (neg3 b) c)
f00 a b c d = cong (λ u → add3 u (mul3 (neg3 b) c)) (mul3-comm d a)

f01 : ∀ b d → add3 (mul3 d b) (mul3 (neg3 b) d) ≡ zero
f01 b d =
  trans (cong₂ add3 (mul3-comm d b) (neg3-mulˡ b d))                -- d·b → b·d；(−b)·d → −(b·d)
    (neg3-inv (mul3 b d))

f10 : ∀ a c → add3 (mul3 (neg3 c) a) (mul3 a c) ≡ zero
f10 a c =
  trans (cong₂ add3 (neg3-mulˡ c a) (mul3-comm a c))                -- (−c)·a → −(c·a)；a·c → c·a
    (trans (add3-comm (neg3 (mul3 c a)) (mul3 c a))                 -- 换位成 neg3-inv 的形状
           (neg3-inv (mul3 c a)))

f11 : ∀ a b c d →
      add3 (mul3 (neg3 c) b) (mul3 a d)
    ≡ add3 (mul3 a d) (mul3 (neg3 b) c)
f11 a b c d =
  trans (cong (λ u → add3 u (mul3 a d)) (neg3-mulˡ c b))            -- (−c)·b → −(c·b)
    (trans (add3-comm (neg3 (mul3 c b)) (mul3 a d))                 -- 换位
           (cong (λ u → add3 (mul3 a d) u)
                 (trans (cong neg3 (mul3-comm c b)) (sym (neg3-mulˡ b c)))))

adj-mul : ∀ M → mulMat2 (adj M) M ≡ det3 M *s I2
adj-mul (mkMat2 a b c d) =
  mat2-cong fin3CS
    (trans (f00 a b c d) (sym (mul3-idʳ (det3 (mkMat2 a b c d)))))
    (trans (f01 b d) (sym (mul3-zeroʳ (det3 (mkMat2 a b c d)))))
    (trans (f10 a c) (sym (mul3-zeroʳ (det3 (mkMat2 a b c d)))))
    (trans (f11 a b c d) (sym (mul3-idʳ (det3 (mkMat2 a b c d)))))

-- adj 不改行列式（det(adj M) = det M，2×2 特例）
det-adj : ∀ M → det3 (adj M) ≡ det3 M
det-adj (mkMat2 a b c d) =
  cong₂ add3
    (mul3-comm d a)                                              -- d·a → a·d
    (trans (cong (λ u → mul3 u (neg3 c)) (neg3-invol b))         -- −(−b) → b
      (trans (neg3-mulʳ b c)                                     -- b·(−c) → −(b·c)
             (sym (neg3-mulˡ b c))))                             -- −(b·c) → (−b)·c

--------------------------------------------------------------------------------
-- 5. det = 1 ⇒ adj 就是逆（双侧）
--------------------------------------------------------------------------------

scale-one : (suc zero) *s I2 ≡ I2
scale-one = refl

det-one-mul : ∀ M → det3 M ≡ suc zero → mulMat2 M (adj M) ≡ I2
det-one-mul M eq =
  trans (mul-adj M)
    (trans (cong (λ k → k *s I2) eq) scale-one)

det-one-adj : ∀ M → det3 M ≡ suc zero → mulMat2 (adj M) M ≡ I2
det-one-adj M eq =
  trans (adj-mul M)
    (trans (cong (λ k → k *s I2) eq) scale-one)
