{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Structology.A4ThreeDimRep
-- A₄ 三维不可约表示 ρ₃ 的构造 + 同态证明 (0 postulate)
--
-- 深度证明 (最后一步): 三代费米子的代数起源 = "3 维表示" 不再手写特征标,
-- 而是从置换表示 (4 顶点) 限制到 V₀ = {x | Σxᵢ = 0} 导出:
--   基 b₁=(1,-1,0,0), b₂=(0,1,-1,0), b₃=(0,0,1,-1)
--   ρ₃(g) 的列 j = perm(g)·bⱼ 在 {b₁,b₂,b₃} 下的整数坐标
-- 矩阵元 ∈ {-1,0,1} ⊂ Z[ω], 迹 = χ₃ (3,0,0,-1), Python 已核验 144 同态。
--
-- 至此 A₄ 全部 4 个不可约表示的特征标均由构造导出:
--   ρ₁ (平凡)      — A4Representation / 显式
--   ρ₁′, ρ₁″ (1 维) — A4OneDimHom (ω 幂 ∘ abelianization)
--   ρ₃ (3 维)       — 本模块 (V₀ 限制, 迹即 χ₃)

module Sovereign.Structology.A4ThreeDimRep where

open import Data.Fin using (Fin; zero; suc)
open import Data.Integer using (ℤ; +_; -[1+_])
open import Data.Product using (_×_; _,_)
open import Data.Vec using (Vec; []; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Sovereign.Structology.A4Group using (A4; Id; Rot; Flip; _⊗_)
open import Sovereign.Structology.A4Representation
  using (Zω; oneZω; zeroZω; negZω; mkZω; ConjClass; chi3)
open import Sovereign.Structology.MatrixZω using (Mat; mulMat; trace)

--------------------------------------------------------------------------------
-- §1. ρ₃: 12 个 3×3 矩阵 (V₀ 基下的整数坐标, 全显式)
--------------------------------------------------------------------------------

rho3 : A4 → Mat 3 3
rho3 Id = ((oneZω ∷ zeroZω ∷ zeroZω ∷ []) ∷ (zeroZω ∷ oneZω ∷ zeroZω ∷ []) ∷ (zeroZω ∷ zeroZω ∷ oneZω ∷ []) ∷ [])
rho3 (Rot zero zero) = ((oneZω ∷ zeroZω ∷ zeroZω ∷ []) ∷ (oneZω ∷ zeroZω ∷ negZω oneZω ∷ []) ∷ (zeroZω ∷ oneZω ∷ negZω oneZω ∷ []) ∷ [])
rho3 (Rot zero (suc zero)) = ((oneZω ∷ zeroZω ∷ zeroZω ∷ []) ∷ (oneZω ∷ negZω oneZω ∷ oneZω ∷ []) ∷ (oneZω ∷ negZω oneZω ∷ zeroZω ∷ []) ∷ [])
rho3 (Rot (suc zero) zero) = ((zeroZω ∷ zeroZω ∷ negZω oneZω ∷ []) ∷ (negZω oneZω ∷ oneZω ∷ negZω oneZω ∷ []) ∷ (zeroZω ∷ oneZω ∷ negZω oneZω ∷ []) ∷ [])
rho3 (Rot (suc zero) (suc zero)) = ((zeroZω ∷ negZω oneZω ∷ oneZω ∷ []) ∷ (negZω oneZω ∷ zeroZω ∷ oneZω ∷ []) ∷ (negZω oneZω ∷ zeroZω ∷ zeroZω ∷ []) ∷ [])
rho3 (Rot (suc (suc zero)) zero) = ((zeroZω ∷ zeroZω ∷ negZω oneZω ∷ []) ∷ (oneZω ∷ zeroZω ∷ negZω oneZω ∷ []) ∷ (oneZω ∷ negZω oneZω ∷ zeroZω ∷ []) ∷ [])
rho3 (Rot (suc (suc zero)) (suc zero)) = ((negZω oneZω ∷ oneZω ∷ zeroZω ∷ []) ∷ (negZω oneZω ∷ oneZω ∷ negZω oneZω ∷ []) ∷ (negZω oneZω ∷ zeroZω ∷ zeroZω ∷ []) ∷ [])
rho3 (Rot (suc (suc (suc zero))) zero) = ((zeroZω ∷ negZω oneZω ∷ oneZω ∷ []) ∷ (oneZω ∷ negZω oneZω ∷ oneZω ∷ []) ∷ (zeroZω ∷ zeroZω ∷ oneZω ∷ []) ∷ [])
rho3 (Rot (suc (suc (suc zero))) (suc zero)) = ((negZω oneZω ∷ oneZω ∷ zeroZω ∷ []) ∷ (negZω oneZω ∷ zeroZω ∷ oneZω ∷ []) ∷ (zeroZω ∷ zeroZω ∷ oneZω ∷ []) ∷ [])
rho3 (Flip zero) = ((negZω oneZω ∷ oneZω ∷ zeroZω ∷ []) ∷ (zeroZω ∷ oneZω ∷ zeroZω ∷ []) ∷ (zeroZω ∷ oneZω ∷ negZω oneZω ∷ []) ∷ [])
rho3 (Flip (suc zero)) = ((zeroZω ∷ negZω oneZω ∷ oneZω ∷ []) ∷ (zeroZω ∷ negZω oneZω ∷ zeroZω ∷ []) ∷ (oneZω ∷ negZω oneZω ∷ zeroZω ∷ []) ∷ [])
rho3 (Flip (suc (suc zero))) = ((zeroZω ∷ zeroZω ∷ negZω oneZω ∷ []) ∷ (zeroZω ∷ negZω oneZω ∷ zeroZω ∷ []) ∷ (negZω oneZω ∷ zeroZω ∷ zeroZω ∷ []) ∷ [])

--------------------------------------------------------------------------------
-- §2. rho3-hom: ρ₃(g ⊗ h) = ρ₃(g) · ρ₃(h)  (12×12 = 144 情形, 全 refl)
-- 两侧均归一化为相同的 3×3 整数矩阵 (mulMat/dot 全展开)。
--------------------------------------------------------------------------------

rho3-hom : ∀ (g h : A4) → mulMat (rho3 g) (rho3 h) ≡ rho3 (g ⊗ h)
rho3-hom (Id) (Id) = refl
rho3-hom (Id) (Rot zero zero) = refl
rho3-hom (Id) (Rot zero (suc zero)) = refl
rho3-hom (Id) (Rot (suc zero) zero) = refl
rho3-hom (Id) (Rot (suc zero) (suc zero)) = refl
rho3-hom (Id) (Rot (suc (suc zero)) zero) = refl
rho3-hom (Id) (Rot (suc (suc zero)) (suc zero)) = refl
rho3-hom (Id) (Rot (suc (suc (suc zero))) zero) = refl
rho3-hom (Id) (Rot (suc (suc (suc zero))) (suc zero)) = refl
rho3-hom (Id) (Flip zero) = refl
rho3-hom (Id) (Flip (suc zero)) = refl
rho3-hom (Id) (Flip (suc (suc zero))) = refl
rho3-hom (Rot zero zero) (Id) = refl
rho3-hom (Rot zero zero) (Rot zero zero) = refl
rho3-hom (Rot zero zero) (Rot zero (suc zero)) = refl
rho3-hom (Rot zero zero) (Rot (suc zero) zero) = refl
rho3-hom (Rot zero zero) (Rot (suc zero) (suc zero)) = refl
rho3-hom (Rot zero zero) (Rot (suc (suc zero)) zero) = refl
rho3-hom (Rot zero zero) (Rot (suc (suc zero)) (suc zero)) = refl
rho3-hom (Rot zero zero) (Rot (suc (suc (suc zero))) zero) = refl
rho3-hom (Rot zero zero) (Rot (suc (suc (suc zero))) (suc zero)) = refl
rho3-hom (Rot zero zero) (Flip zero) = refl
rho3-hom (Rot zero zero) (Flip (suc zero)) = refl
rho3-hom (Rot zero zero) (Flip (suc (suc zero))) = refl
rho3-hom (Rot zero (suc zero)) (Id) = refl
rho3-hom (Rot zero (suc zero)) (Rot zero zero) = refl
rho3-hom (Rot zero (suc zero)) (Rot zero (suc zero)) = refl
rho3-hom (Rot zero (suc zero)) (Rot (suc zero) zero) = refl
rho3-hom (Rot zero (suc zero)) (Rot (suc zero) (suc zero)) = refl
rho3-hom (Rot zero (suc zero)) (Rot (suc (suc zero)) zero) = refl
rho3-hom (Rot zero (suc zero)) (Rot (suc (suc zero)) (suc zero)) = refl
rho3-hom (Rot zero (suc zero)) (Rot (suc (suc (suc zero))) zero) = refl
rho3-hom (Rot zero (suc zero)) (Rot (suc (suc (suc zero))) (suc zero)) = refl
rho3-hom (Rot zero (suc zero)) (Flip zero) = refl
rho3-hom (Rot zero (suc zero)) (Flip (suc zero)) = refl
rho3-hom (Rot zero (suc zero)) (Flip (suc (suc zero))) = refl
rho3-hom (Rot (suc zero) zero) (Id) = refl
rho3-hom (Rot (suc zero) zero) (Rot zero zero) = refl
rho3-hom (Rot (suc zero) zero) (Rot zero (suc zero)) = refl
rho3-hom (Rot (suc zero) zero) (Rot (suc zero) zero) = refl
rho3-hom (Rot (suc zero) zero) (Rot (suc zero) (suc zero)) = refl
rho3-hom (Rot (suc zero) zero) (Rot (suc (suc zero)) zero) = refl
rho3-hom (Rot (suc zero) zero) (Rot (suc (suc zero)) (suc zero)) = refl
rho3-hom (Rot (suc zero) zero) (Rot (suc (suc (suc zero))) zero) = refl
rho3-hom (Rot (suc zero) zero) (Rot (suc (suc (suc zero))) (suc zero)) = refl
rho3-hom (Rot (suc zero) zero) (Flip zero) = refl
rho3-hom (Rot (suc zero) zero) (Flip (suc zero)) = refl
rho3-hom (Rot (suc zero) zero) (Flip (suc (suc zero))) = refl
rho3-hom (Rot (suc zero) (suc zero)) (Id) = refl
rho3-hom (Rot (suc zero) (suc zero)) (Rot zero zero) = refl
rho3-hom (Rot (suc zero) (suc zero)) (Rot zero (suc zero)) = refl
rho3-hom (Rot (suc zero) (suc zero)) (Rot (suc zero) zero) = refl
rho3-hom (Rot (suc zero) (suc zero)) (Rot (suc zero) (suc zero)) = refl
rho3-hom (Rot (suc zero) (suc zero)) (Rot (suc (suc zero)) zero) = refl
rho3-hom (Rot (suc zero) (suc zero)) (Rot (suc (suc zero)) (suc zero)) = refl
rho3-hom (Rot (suc zero) (suc zero)) (Rot (suc (suc (suc zero))) zero) = refl
rho3-hom (Rot (suc zero) (suc zero)) (Rot (suc (suc (suc zero))) (suc zero)) = refl
rho3-hom (Rot (suc zero) (suc zero)) (Flip zero) = refl
rho3-hom (Rot (suc zero) (suc zero)) (Flip (suc zero)) = refl
rho3-hom (Rot (suc zero) (suc zero)) (Flip (suc (suc zero))) = refl
rho3-hom (Rot (suc (suc zero)) zero) (Id) = refl
rho3-hom (Rot (suc (suc zero)) zero) (Rot zero zero) = refl
rho3-hom (Rot (suc (suc zero)) zero) (Rot zero (suc zero)) = refl
rho3-hom (Rot (suc (suc zero)) zero) (Rot (suc zero) zero) = refl
rho3-hom (Rot (suc (suc zero)) zero) (Rot (suc zero) (suc zero)) = refl
rho3-hom (Rot (suc (suc zero)) zero) (Rot (suc (suc zero)) zero) = refl
rho3-hom (Rot (suc (suc zero)) zero) (Rot (suc (suc zero)) (suc zero)) = refl
rho3-hom (Rot (suc (suc zero)) zero) (Rot (suc (suc (suc zero))) zero) = refl
rho3-hom (Rot (suc (suc zero)) zero) (Rot (suc (suc (suc zero))) (suc zero)) = refl
rho3-hom (Rot (suc (suc zero)) zero) (Flip zero) = refl
rho3-hom (Rot (suc (suc zero)) zero) (Flip (suc zero)) = refl
rho3-hom (Rot (suc (suc zero)) zero) (Flip (suc (suc zero))) = refl
rho3-hom (Rot (suc (suc zero)) (suc zero)) (Id) = refl
rho3-hom (Rot (suc (suc zero)) (suc zero)) (Rot zero zero) = refl
rho3-hom (Rot (suc (suc zero)) (suc zero)) (Rot zero (suc zero)) = refl
rho3-hom (Rot (suc (suc zero)) (suc zero)) (Rot (suc zero) zero) = refl
rho3-hom (Rot (suc (suc zero)) (suc zero)) (Rot (suc zero) (suc zero)) = refl
rho3-hom (Rot (suc (suc zero)) (suc zero)) (Rot (suc (suc zero)) zero) = refl
rho3-hom (Rot (suc (suc zero)) (suc zero)) (Rot (suc (suc zero)) (suc zero)) = refl
rho3-hom (Rot (suc (suc zero)) (suc zero)) (Rot (suc (suc (suc zero))) zero) = refl
rho3-hom (Rot (suc (suc zero)) (suc zero)) (Rot (suc (suc (suc zero))) (suc zero)) = refl
rho3-hom (Rot (suc (suc zero)) (suc zero)) (Flip zero) = refl
rho3-hom (Rot (suc (suc zero)) (suc zero)) (Flip (suc zero)) = refl
rho3-hom (Rot (suc (suc zero)) (suc zero)) (Flip (suc (suc zero))) = refl
rho3-hom (Rot (suc (suc (suc zero))) zero) (Id) = refl
rho3-hom (Rot (suc (suc (suc zero))) zero) (Rot zero zero) = refl
rho3-hom (Rot (suc (suc (suc zero))) zero) (Rot zero (suc zero)) = refl
rho3-hom (Rot (suc (suc (suc zero))) zero) (Rot (suc zero) zero) = refl
rho3-hom (Rot (suc (suc (suc zero))) zero) (Rot (suc zero) (suc zero)) = refl
rho3-hom (Rot (suc (suc (suc zero))) zero) (Rot (suc (suc zero)) zero) = refl
rho3-hom (Rot (suc (suc (suc zero))) zero) (Rot (suc (suc zero)) (suc zero)) = refl
rho3-hom (Rot (suc (suc (suc zero))) zero) (Rot (suc (suc (suc zero))) zero) = refl
rho3-hom (Rot (suc (suc (suc zero))) zero) (Rot (suc (suc (suc zero))) (suc zero)) = refl
rho3-hom (Rot (suc (suc (suc zero))) zero) (Flip zero) = refl
rho3-hom (Rot (suc (suc (suc zero))) zero) (Flip (suc zero)) = refl
rho3-hom (Rot (suc (suc (suc zero))) zero) (Flip (suc (suc zero))) = refl
rho3-hom (Rot (suc (suc (suc zero))) (suc zero)) (Id) = refl
rho3-hom (Rot (suc (suc (suc zero))) (suc zero)) (Rot zero zero) = refl
rho3-hom (Rot (suc (suc (suc zero))) (suc zero)) (Rot zero (suc zero)) = refl
rho3-hom (Rot (suc (suc (suc zero))) (suc zero)) (Rot (suc zero) zero) = refl
rho3-hom (Rot (suc (suc (suc zero))) (suc zero)) (Rot (suc zero) (suc zero)) = refl
rho3-hom (Rot (suc (suc (suc zero))) (suc zero)) (Rot (suc (suc zero)) zero) = refl
rho3-hom (Rot (suc (suc (suc zero))) (suc zero)) (Rot (suc (suc zero)) (suc zero)) = refl
rho3-hom (Rot (suc (suc (suc zero))) (suc zero)) (Rot (suc (suc (suc zero))) zero) = refl
rho3-hom (Rot (suc (suc (suc zero))) (suc zero)) (Rot (suc (suc (suc zero))) (suc zero)) = refl
rho3-hom (Rot (suc (suc (suc zero))) (suc zero)) (Flip zero) = refl
rho3-hom (Rot (suc (suc (suc zero))) (suc zero)) (Flip (suc zero)) = refl
rho3-hom (Rot (suc (suc (suc zero))) (suc zero)) (Flip (suc (suc zero))) = refl
rho3-hom (Flip zero) (Id) = refl
rho3-hom (Flip zero) (Rot zero zero) = refl
rho3-hom (Flip zero) (Rot zero (suc zero)) = refl
rho3-hom (Flip zero) (Rot (suc zero) zero) = refl
rho3-hom (Flip zero) (Rot (suc zero) (suc zero)) = refl
rho3-hom (Flip zero) (Rot (suc (suc zero)) zero) = refl
rho3-hom (Flip zero) (Rot (suc (suc zero)) (suc zero)) = refl
rho3-hom (Flip zero) (Rot (suc (suc (suc zero))) zero) = refl
rho3-hom (Flip zero) (Rot (suc (suc (suc zero))) (suc zero)) = refl
rho3-hom (Flip zero) (Flip zero) = refl
rho3-hom (Flip zero) (Flip (suc zero)) = refl
rho3-hom (Flip zero) (Flip (suc (suc zero))) = refl
rho3-hom (Flip (suc zero)) (Id) = refl
rho3-hom (Flip (suc zero)) (Rot zero zero) = refl
rho3-hom (Flip (suc zero)) (Rot zero (suc zero)) = refl
rho3-hom (Flip (suc zero)) (Rot (suc zero) zero) = refl
rho3-hom (Flip (suc zero)) (Rot (suc zero) (suc zero)) = refl
rho3-hom (Flip (suc zero)) (Rot (suc (suc zero)) zero) = refl
rho3-hom (Flip (suc zero)) (Rot (suc (suc zero)) (suc zero)) = refl
rho3-hom (Flip (suc zero)) (Rot (suc (suc (suc zero))) zero) = refl
rho3-hom (Flip (suc zero)) (Rot (suc (suc (suc zero))) (suc zero)) = refl
rho3-hom (Flip (suc zero)) (Flip zero) = refl
rho3-hom (Flip (suc zero)) (Flip (suc zero)) = refl
rho3-hom (Flip (suc zero)) (Flip (suc (suc zero))) = refl
rho3-hom (Flip (suc (suc zero))) (Id) = refl
rho3-hom (Flip (suc (suc zero))) (Rot zero zero) = refl
rho3-hom (Flip (suc (suc zero))) (Rot zero (suc zero)) = refl
rho3-hom (Flip (suc (suc zero))) (Rot (suc zero) zero) = refl
rho3-hom (Flip (suc (suc zero))) (Rot (suc zero) (suc zero)) = refl
rho3-hom (Flip (suc (suc zero))) (Rot (suc (suc zero)) zero) = refl
rho3-hom (Flip (suc (suc zero))) (Rot (suc (suc zero)) (suc zero)) = refl
rho3-hom (Flip (suc (suc zero))) (Rot (suc (suc (suc zero))) zero) = refl
rho3-hom (Flip (suc (suc zero))) (Rot (suc (suc (suc zero))) (suc zero)) = refl
rho3-hom (Flip (suc (suc zero))) (Flip zero) = refl
rho3-hom (Flip (suc (suc zero))) (Flip (suc zero)) = refl
rho3-hom (Flip (suc (suc zero))) (Flip (suc (suc zero))) = refl

--------------------------------------------------------------------------------
-- §3. classOf: A₄ → 共轭类 (Fin 4)  — 与 abelianization 一致, Flip → 第 4 类
--------------------------------------------------------------------------------

classOf : A4 → ConjClass
classOf Id = zero
classOf (Rot zero zero) = suc (suc zero)
classOf (Rot zero (suc zero)) = suc zero
classOf (Rot (suc zero) zero) = suc zero
classOf (Rot (suc zero) (suc zero)) = suc (suc zero)
classOf (Rot (suc (suc zero)) zero) = suc (suc zero)
classOf (Rot (suc (suc zero)) (suc zero)) = suc zero
classOf (Rot (suc (suc (suc zero))) zero) = suc zero
classOf (Rot (suc (suc (suc zero))) (suc zero)) = suc (suc zero)
classOf (Flip k) = suc (suc (suc zero))

--------------------------------------------------------------------------------
-- §4. chi3FromRep: trace ρ₃(g) = χ₃(classOf g)  (12 情形, 全 refl)
-- 三维不可约表示的特征标 χ₃ 由迹直接导出, 不再作为手写数据:
--   迹(Id)=3, 迹(3 循环)=0, 迹(双对换)=-1
--------------------------------------------------------------------------------

chi3FromRep : ∀ (g : A4) → trace (rho3 g) ≡ chi3 (classOf g)
chi3FromRep (Id) = refl
chi3FromRep (Rot zero zero) = refl
chi3FromRep (Rot zero (suc zero)) = refl
chi3FromRep (Rot (suc zero) zero) = refl
chi3FromRep (Rot (suc zero) (suc zero)) = refl
chi3FromRep (Rot (suc (suc zero)) zero) = refl
chi3FromRep (Rot (suc (suc zero)) (suc zero)) = refl
chi3FromRep (Rot (suc (suc (suc zero))) zero) = refl
chi3FromRep (Rot (suc (suc (suc zero))) (suc zero)) = refl
chi3FromRep (Flip zero) = refl
chi3FromRep (Flip (suc zero)) = refl
chi3FromRep (Flip (suc (suc zero))) = refl

-- 0 postulate.

--------------------------------------------------------------------------------
-- §5. L2 补充定理
--------------------------------------------------------------------------------

-- L2: ρ₃(Id) = I₃ (单位表示)
rho3-identity : rho3 Id ≡
  ((oneZω ∷ zeroZω ∷ zeroZω ∷ []) ∷
   (zeroZω ∷ oneZω ∷ zeroZω ∷ []) ∷
   (zeroZω ∷ zeroZω ∷ oneZω ∷ []) ∷ [])
rho3-identity = refl

-- L2: χ₃ 值表 (由 chi3FromRep 直接导出)
-- Id → 3, 3-循环 → 0, 双对换 → -1
chi3-id : trace (rho3 Id) ≡ mkZω (+ 3) (+ 0)
chi3-id = refl

chi3-3cycle : trace (rho3 (Rot zero zero)) ≡ zeroZω
chi3-3cycle = refl

chi3-double-transposition : trace (rho3 (Flip zero)) ≡ mkZω -[1+ 0 ] (+ 0)
chi3-double-transposition = refl

-- L2: 特征标值总结 (3, 0, 0, -1)
chi3-values :
  (trace (rho3 Id) ≡ mkZω (+ 3) (+ 0))
  × (trace (rho3 (Rot zero zero)) ≡ zeroZω)
  × (trace (rho3 (Rot (suc zero) zero)) ≡ zeroZω)
  × (trace (rho3 (Flip zero)) ≡ mkZω -[1+ 0 ] (+ 0))
chi3-values = refl , refl , refl , refl

