{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Algebra.AdjacencyMatrix
-- GF(9) 邻接矩阵与图谱基础
--
-- 语料锚: "幻方本征谱 {34, 0, 16, -16}" (torus-geometry-and-magic-square)
--         "谱有限性" (几何闭包问题)
--
-- 定义:
--   §1 通用 n 阶邻接矩阵 (Fin n → Fin n → GF9)
--   §2 矩阵乘法 (4 阶)
--   §3 对角线/迹
--   §4 对称性检测
--   §5 基本性质
--
-- 0 postulate.

module Sovereign.Algebra.AdjacencyMatrix where

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Fin using (Fin; zero; suc)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; trans; sym)

open import Sovereign.Base.Trit using (Trit; T₀; T₁; T₂; _⊕_; _⊗_)
open import Sovereign.Algebra.GF9
  using ( GF9; gf9-zero; gf9-one; _+gf9_; _*gf9_
        ; +gf9-assoc; +gf9-comm; +gf9-identityˡ; +gf9-identityʳ
        ; *gf9-assoc; *gf9-comm; *gf9-identityˡ; *gf9-identityʳ
        ; gf9-zero-mulˡ; gf9-zero-mulʳ
        )

--------------------------------------------------------------------------------
-- §1. 通用 n 阶邻接矩阵
--------------------------------------------------------------------------------

-- n 阶 GF(9)-值矩阵 (邻接矩阵)
AdjMatrix : ℕ → Set
AdjMatrix n = Fin n → Fin n → GF9

-- 零矩阵 (无边图)
zeroAdj : ∀ n → AdjMatrix n
zeroAdj n i j = gf9-zero

-- 4 阶矩阵类型
AdjMatrix4 : Set
AdjMatrix4 = AdjMatrix 4

-- 4 阶单位矩阵 (显式 16-case, 避免 with 模式匹配问题)
matI4 : AdjMatrix4
matI4 zero                   zero                   = gf9-one
matI4 zero                   (suc _)                = gf9-zero
matI4 (suc zero)             zero                   = gf9-zero
matI4 (suc zero)             (suc zero)             = gf9-one
matI4 (suc zero)             (suc (suc _))          = gf9-zero
matI4 (suc (suc zero))       zero                   = gf9-zero
matI4 (suc (suc zero))       (suc zero)             = gf9-zero
matI4 (suc (suc zero))       (suc (suc zero))       = gf9-one
matI4 (suc (suc zero))       (suc (suc (suc _)))    = gf9-zero
matI4 (suc (suc (suc _)))    zero                   = gf9-zero
matI4 (suc (suc (suc _)))    (suc zero)             = gf9-zero
matI4 (suc (suc (suc _)))    (suc (suc zero))       = gf9-zero
matI4 (suc (suc (suc zero))) (suc (suc (suc zero))) = gf9-one
matI4 (suc (suc (suc zero))) (suc (suc (suc (suc ()))))
matI4 (suc (suc (suc (suc ())))) _

--------------------------------------------------------------------------------
-- §2. 矩阵乘法
--------------------------------------------------------------------------------

-- 4 阶矩阵乘法: (A·B)_{ij} = Σ_k A_{ik} * B_{kj}
mulMat4 : AdjMatrix4 → AdjMatrix4 → AdjMatrix4
mulMat4 A B i j =
  (A i zero *gf9 B zero j) +gf9
  ((A i (suc zero) *gf9 B (suc zero) j) +gf9
   ((A i (suc (suc zero)) *gf9 B (suc (suc zero)) j) +gf9
    (A i (suc (suc (suc zero))) *gf9 B (suc (suc (suc zero))) j)))

-- 4 阶矩阵幂
powMat4 : AdjMatrix4 → ℕ → AdjMatrix4
powMat4 A zero    = matI4
powMat4 A (suc n) = mulMat4 A (powMat4 A n)

-- 零矩阵幂吸收: 0^(suc n) = 0
-- 证明策略: 0·A = 0 (零乘吸收) + 归纳
zero-mat4-mulˡ : ∀ B → mulMat4 (zeroAdj 4) B ≡ zeroAdj 4
zero-mat4-mulˡ B = refl  -- gf9-zero *gf9 _ = gf9-zero (gf9-zero-mulˡ), 全部 +gf9 gf9-zero = gf9-zero

zero-mat4-pow : ∀ n → powMat4 (zeroAdj 4) (suc n) ≡ zeroAdj 4
zero-mat4-pow zero    = refl
zero-mat4-pow (suc n) = trans (zero-mat4-mulˡ (powMat4 (zeroAdj 4) (suc n)))
                               (zero-mat4-pow n)

--------------------------------------------------------------------------------
-- §3. 对角线与迹
--------------------------------------------------------------------------------

-- 对角线元素
diag4 : AdjMatrix4 → Fin 4 → GF9
diag4 A i = A i i

-- 迹 (对角线和)
trace4 : AdjMatrix4 → GF9
trace4 A = diag4 A zero +gf9
           (diag4 A (suc zero) +gf9
            (diag4 A (suc (suc zero)) +gf9
             diag4 A (suc (suc (suc zero)))))

-- 零矩阵迹为零
trace-zero : trace4 (zeroAdj 4) ≡ gf9-zero
trace-zero = refl

--------------------------------------------------------------------------------
-- §4. 对称性
--------------------------------------------------------------------------------

-- 转置
adj-transpose : AdjMatrix4 → AdjMatrix4
adj-transpose A i j = A j i

-- 对称性: A = Aᵀ
Symmetric4 : AdjMatrix4 → Set
Symmetric4 A = ∀ i j → A i j ≡ A j i

-- 零矩阵对称
zero-symmetric : Symmetric4 (zeroAdj 4)
zero-symmetric i j = refl

-- 单位矩阵对称 (显式全部 case)
identity-symmetric : Symmetric4 matI4
identity-symmetric zero                   zero                   = refl
identity-symmetric zero                   (suc zero)             = refl
identity-symmetric zero                   (suc (suc zero))       = refl
identity-symmetric zero                   (suc (suc (suc zero))) = refl
identity-symmetric (suc zero)             zero                   = refl
identity-symmetric (suc zero)             (suc zero)             = refl
identity-symmetric (suc zero)             (suc (suc zero))       = refl
identity-symmetric (suc zero)             (suc (suc (suc zero))) = refl
identity-symmetric (suc (suc zero))       zero                   = refl
identity-symmetric (suc (suc zero))       (suc zero)             = refl
identity-symmetric (suc (suc zero))       (suc (suc zero))       = refl
identity-symmetric (suc (suc zero))       (suc (suc (suc zero))) = refl
identity-symmetric (suc (suc (suc zero))) zero                   = refl
identity-symmetric (suc (suc (suc zero))) (suc zero)             = refl
identity-symmetric (suc (suc (suc zero))) (suc (suc zero))       = refl
identity-symmetric (suc (suc (suc zero))) (suc (suc (suc zero))) = refl

--------------------------------------------------------------------------------
-- §5. 基本性质
--------------------------------------------------------------------------------

-- 零矩阵对角线全零
zero-diag : ∀ i → diag4 (zeroAdj 4) i ≡ gf9-zero
zero-diag i = refl

-- 单位矩阵对角线全一
identity-diag : ∀ i → diag4 matI4 i ≡ gf9-one
identity-diag zero                   = refl
identity-diag (suc zero)             = refl
identity-diag (suc (suc zero))       = refl
identity-diag (suc (suc (suc zero))) = refl

-- 0 postulate.
