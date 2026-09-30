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
-- §2. rho3-hom: ρ₃(g ⊗ h) = ρ₃(g) · ρ₃(h)
-- 两侧均归一化为相同的 3×3 整数矩阵 (mulMat/dot 全展开)。
--
-- 证明按第一参数拆 12 个子引理 (各 12 案 refl, ≤27) + dispatcher:
--   rho3-hom-XX : ∀ h → mulMat (rho3 (XX)) (rho3 h) ≡ rho3 ((XX) ⊗ h)
-- 路径 (C) 拆子引理保底 — 生成元分解 (路径 A) 在此需 mulMat 结合律,
-- 而 mulZω 的结合/分配环律不在库中 (矩阵元为符号 ℤ 对, refl 不闭合),
-- 估算 ≈250 行 Zω 环律 + 矩阵结合律新代数, 属后续任务。
--------------------------------------------------------------------------------

-- 第一参数 = Id
rho3-hom-Id : ∀ (h : A4) → mulMat (rho3 (Id)) (rho3 h) ≡ rho3 ((Id) ⊗ h)
rho3-hom-Id (Id) = refl
rho3-hom-Id (Rot zero zero) = refl
rho3-hom-Id (Rot zero (suc zero)) = refl
rho3-hom-Id (Rot (suc zero) zero) = refl
rho3-hom-Id (Rot (suc zero) (suc zero)) = refl
rho3-hom-Id (Rot (suc (suc zero)) zero) = refl
rho3-hom-Id (Rot (suc (suc zero)) (suc zero)) = refl
rho3-hom-Id (Rot (suc (suc (suc zero))) zero) = refl
rho3-hom-Id (Rot (suc (suc (suc zero))) (suc zero)) = refl
rho3-hom-Id (Flip zero) = refl
rho3-hom-Id (Flip (suc zero)) = refl
rho3-hom-Id (Flip (suc (suc zero))) = refl

-- 第一参数 = Rot zero zero
rho3-hom-R00 : ∀ (h : A4) → mulMat (rho3 (Rot zero zero)) (rho3 h) ≡ rho3 ((Rot zero zero) ⊗ h)
rho3-hom-R00 (Id) = refl
rho3-hom-R00 (Rot zero zero) = refl
rho3-hom-R00 (Rot zero (suc zero)) = refl
rho3-hom-R00 (Rot (suc zero) zero) = refl
rho3-hom-R00 (Rot (suc zero) (suc zero)) = refl
rho3-hom-R00 (Rot (suc (suc zero)) zero) = refl
rho3-hom-R00 (Rot (suc (suc zero)) (suc zero)) = refl
rho3-hom-R00 (Rot (suc (suc (suc zero))) zero) = refl
rho3-hom-R00 (Rot (suc (suc (suc zero))) (suc zero)) = refl
rho3-hom-R00 (Flip zero) = refl
rho3-hom-R00 (Flip (suc zero)) = refl
rho3-hom-R00 (Flip (suc (suc zero))) = refl

-- 第一参数 = Rot zero (suc zero)
rho3-hom-R01 : ∀ (h : A4) → mulMat (rho3 (Rot zero (suc zero))) (rho3 h) ≡ rho3 ((Rot zero (suc zero)) ⊗ h)
rho3-hom-R01 (Id) = refl
rho3-hom-R01 (Rot zero zero) = refl
rho3-hom-R01 (Rot zero (suc zero)) = refl
rho3-hom-R01 (Rot (suc zero) zero) = refl
rho3-hom-R01 (Rot (suc zero) (suc zero)) = refl
rho3-hom-R01 (Rot (suc (suc zero)) zero) = refl
rho3-hom-R01 (Rot (suc (suc zero)) (suc zero)) = refl
rho3-hom-R01 (Rot (suc (suc (suc zero))) zero) = refl
rho3-hom-R01 (Rot (suc (suc (suc zero))) (suc zero)) = refl
rho3-hom-R01 (Flip zero) = refl
rho3-hom-R01 (Flip (suc zero)) = refl
rho3-hom-R01 (Flip (suc (suc zero))) = refl

-- 第一参数 = Rot (suc zero) zero
rho3-hom-R10 : ∀ (h : A4) → mulMat (rho3 (Rot (suc zero) zero)) (rho3 h) ≡ rho3 ((Rot (suc zero) zero) ⊗ h)
rho3-hom-R10 (Id) = refl
rho3-hom-R10 (Rot zero zero) = refl
rho3-hom-R10 (Rot zero (suc zero)) = refl
rho3-hom-R10 (Rot (suc zero) zero) = refl
rho3-hom-R10 (Rot (suc zero) (suc zero)) = refl
rho3-hom-R10 (Rot (suc (suc zero)) zero) = refl
rho3-hom-R10 (Rot (suc (suc zero)) (suc zero)) = refl
rho3-hom-R10 (Rot (suc (suc (suc zero))) zero) = refl
rho3-hom-R10 (Rot (suc (suc (suc zero))) (suc zero)) = refl
rho3-hom-R10 (Flip zero) = refl
rho3-hom-R10 (Flip (suc zero)) = refl
rho3-hom-R10 (Flip (suc (suc zero))) = refl

-- 第一参数 = Rot (suc zero) (suc zero)
rho3-hom-R11 : ∀ (h : A4) → mulMat (rho3 (Rot (suc zero) (suc zero))) (rho3 h) ≡ rho3 ((Rot (suc zero) (suc zero)) ⊗ h)
rho3-hom-R11 (Id) = refl
rho3-hom-R11 (Rot zero zero) = refl
rho3-hom-R11 (Rot zero (suc zero)) = refl
rho3-hom-R11 (Rot (suc zero) zero) = refl
rho3-hom-R11 (Rot (suc zero) (suc zero)) = refl
rho3-hom-R11 (Rot (suc (suc zero)) zero) = refl
rho3-hom-R11 (Rot (suc (suc zero)) (suc zero)) = refl
rho3-hom-R11 (Rot (suc (suc (suc zero))) zero) = refl
rho3-hom-R11 (Rot (suc (suc (suc zero))) (suc zero)) = refl
rho3-hom-R11 (Flip zero) = refl
rho3-hom-R11 (Flip (suc zero)) = refl
rho3-hom-R11 (Flip (suc (suc zero))) = refl

-- 第一参数 = Rot (suc (suc zero)) zero
rho3-hom-R20 : ∀ (h : A4) → mulMat (rho3 (Rot (suc (suc zero)) zero)) (rho3 h) ≡ rho3 ((Rot (suc (suc zero)) zero) ⊗ h)
rho3-hom-R20 (Id) = refl
rho3-hom-R20 (Rot zero zero) = refl
rho3-hom-R20 (Rot zero (suc zero)) = refl
rho3-hom-R20 (Rot (suc zero) zero) = refl
rho3-hom-R20 (Rot (suc zero) (suc zero)) = refl
rho3-hom-R20 (Rot (suc (suc zero)) zero) = refl
rho3-hom-R20 (Rot (suc (suc zero)) (suc zero)) = refl
rho3-hom-R20 (Rot (suc (suc (suc zero))) zero) = refl
rho3-hom-R20 (Rot (suc (suc (suc zero))) (suc zero)) = refl
rho3-hom-R20 (Flip zero) = refl
rho3-hom-R20 (Flip (suc zero)) = refl
rho3-hom-R20 (Flip (suc (suc zero))) = refl

-- 第一参数 = Rot (suc (suc zero)) (suc zero)
rho3-hom-R21 : ∀ (h : A4) → mulMat (rho3 (Rot (suc (suc zero)) (suc zero))) (rho3 h) ≡ rho3 ((Rot (suc (suc zero)) (suc zero)) ⊗ h)
rho3-hom-R21 (Id) = refl
rho3-hom-R21 (Rot zero zero) = refl
rho3-hom-R21 (Rot zero (suc zero)) = refl
rho3-hom-R21 (Rot (suc zero) zero) = refl
rho3-hom-R21 (Rot (suc zero) (suc zero)) = refl
rho3-hom-R21 (Rot (suc (suc zero)) zero) = refl
rho3-hom-R21 (Rot (suc (suc zero)) (suc zero)) = refl
rho3-hom-R21 (Rot (suc (suc (suc zero))) zero) = refl
rho3-hom-R21 (Rot (suc (suc (suc zero))) (suc zero)) = refl
rho3-hom-R21 (Flip zero) = refl
rho3-hom-R21 (Flip (suc zero)) = refl
rho3-hom-R21 (Flip (suc (suc zero))) = refl

-- 第一参数 = Rot (suc (suc (suc zero))) zero
rho3-hom-R30 : ∀ (h : A4) → mulMat (rho3 (Rot (suc (suc (suc zero))) zero)) (rho3 h) ≡ rho3 ((Rot (suc (suc (suc zero))) zero) ⊗ h)
rho3-hom-R30 (Id) = refl
rho3-hom-R30 (Rot zero zero) = refl
rho3-hom-R30 (Rot zero (suc zero)) = refl
rho3-hom-R30 (Rot (suc zero) zero) = refl
rho3-hom-R30 (Rot (suc zero) (suc zero)) = refl
rho3-hom-R30 (Rot (suc (suc zero)) zero) = refl
rho3-hom-R30 (Rot (suc (suc zero)) (suc zero)) = refl
rho3-hom-R30 (Rot (suc (suc (suc zero))) zero) = refl
rho3-hom-R30 (Rot (suc (suc (suc zero))) (suc zero)) = refl
rho3-hom-R30 (Flip zero) = refl
rho3-hom-R30 (Flip (suc zero)) = refl
rho3-hom-R30 (Flip (suc (suc zero))) = refl

-- 第一参数 = Rot (suc (suc (suc zero))) (suc zero)
rho3-hom-R31 : ∀ (h : A4) → mulMat (rho3 (Rot (suc (suc (suc zero))) (suc zero))) (rho3 h) ≡ rho3 ((Rot (suc (suc (suc zero))) (suc zero)) ⊗ h)
rho3-hom-R31 (Id) = refl
rho3-hom-R31 (Rot zero zero) = refl
rho3-hom-R31 (Rot zero (suc zero)) = refl
rho3-hom-R31 (Rot (suc zero) zero) = refl
rho3-hom-R31 (Rot (suc zero) (suc zero)) = refl
rho3-hom-R31 (Rot (suc (suc zero)) zero) = refl
rho3-hom-R31 (Rot (suc (suc zero)) (suc zero)) = refl
rho3-hom-R31 (Rot (suc (suc (suc zero))) zero) = refl
rho3-hom-R31 (Rot (suc (suc (suc zero))) (suc zero)) = refl
rho3-hom-R31 (Flip zero) = refl
rho3-hom-R31 (Flip (suc zero)) = refl
rho3-hom-R31 (Flip (suc (suc zero))) = refl

-- 第一参数 = Flip zero
rho3-hom-F0 : ∀ (h : A4) → mulMat (rho3 (Flip zero)) (rho3 h) ≡ rho3 ((Flip zero) ⊗ h)
rho3-hom-F0 (Id) = refl
rho3-hom-F0 (Rot zero zero) = refl
rho3-hom-F0 (Rot zero (suc zero)) = refl
rho3-hom-F0 (Rot (suc zero) zero) = refl
rho3-hom-F0 (Rot (suc zero) (suc zero)) = refl
rho3-hom-F0 (Rot (suc (suc zero)) zero) = refl
rho3-hom-F0 (Rot (suc (suc zero)) (suc zero)) = refl
rho3-hom-F0 (Rot (suc (suc (suc zero))) zero) = refl
rho3-hom-F0 (Rot (suc (suc (suc zero))) (suc zero)) = refl
rho3-hom-F0 (Flip zero) = refl
rho3-hom-F0 (Flip (suc zero)) = refl
rho3-hom-F0 (Flip (suc (suc zero))) = refl

-- 第一参数 = Flip (suc zero)
rho3-hom-F1 : ∀ (h : A4) → mulMat (rho3 (Flip (suc zero))) (rho3 h) ≡ rho3 ((Flip (suc zero)) ⊗ h)
rho3-hom-F1 (Id) = refl
rho3-hom-F1 (Rot zero zero) = refl
rho3-hom-F1 (Rot zero (suc zero)) = refl
rho3-hom-F1 (Rot (suc zero) zero) = refl
rho3-hom-F1 (Rot (suc zero) (suc zero)) = refl
rho3-hom-F1 (Rot (suc (suc zero)) zero) = refl
rho3-hom-F1 (Rot (suc (suc zero)) (suc zero)) = refl
rho3-hom-F1 (Rot (suc (suc (suc zero))) zero) = refl
rho3-hom-F1 (Rot (suc (suc (suc zero))) (suc zero)) = refl
rho3-hom-F1 (Flip zero) = refl
rho3-hom-F1 (Flip (suc zero)) = refl
rho3-hom-F1 (Flip (suc (suc zero))) = refl

-- 第一参数 = Flip (suc (suc zero))
rho3-hom-F2 : ∀ (h : A4) → mulMat (rho3 (Flip (suc (suc zero)))) (rho3 h) ≡ rho3 ((Flip (suc (suc zero))) ⊗ h)
rho3-hom-F2 (Id) = refl
rho3-hom-F2 (Rot zero zero) = refl
rho3-hom-F2 (Rot zero (suc zero)) = refl
rho3-hom-F2 (Rot (suc zero) zero) = refl
rho3-hom-F2 (Rot (suc zero) (suc zero)) = refl
rho3-hom-F2 (Rot (suc (suc zero)) zero) = refl
rho3-hom-F2 (Rot (suc (suc zero)) (suc zero)) = refl
rho3-hom-F2 (Rot (suc (suc (suc zero))) zero) = refl
rho3-hom-F2 (Rot (suc (suc (suc zero))) (suc zero)) = refl
rho3-hom-F2 (Flip zero) = refl
rho3-hom-F2 (Flip (suc zero)) = refl
rho3-hom-F2 (Flip (suc (suc zero))) = refl

-- 主定理 (dispatcher): 按第一参数分派到 12 个子引理
rho3-hom : ∀ (g h : A4) → mulMat (rho3 g) (rho3 h) ≡ rho3 (g ⊗ h)
rho3-hom (Id) h = rho3-hom-Id h
rho3-hom (Rot zero zero) h = rho3-hom-R00 h
rho3-hom (Rot zero (suc zero)) h = rho3-hom-R01 h
rho3-hom (Rot (suc zero) zero) h = rho3-hom-R10 h
rho3-hom (Rot (suc zero) (suc zero)) h = rho3-hom-R11 h
rho3-hom (Rot (suc (suc zero)) zero) h = rho3-hom-R20 h
rho3-hom (Rot (suc (suc zero)) (suc zero)) h = rho3-hom-R21 h
rho3-hom (Rot (suc (suc (suc zero))) zero) h = rho3-hom-R30 h
rho3-hom (Rot (suc (suc (suc zero))) (suc zero)) h = rho3-hom-R31 h
rho3-hom (Flip zero) h = rho3-hom-F0 h
rho3-hom (Flip (suc zero)) h = rho3-hom-F1 h
rho3-hom (Flip (suc (suc zero))) h = rho3-hom-F2 h

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

--------------------------------------------------------------------------------
-- §6. mulMat-chain: 生成元词的右嵌套矩阵链 = ρ₃ 的词求值 (生成元路线地基)
--
-- 挂接点注记 (环律依赖的具体位置):
--   (a) 本引理把链特化为右嵌套 (与 A4GenWords.ev 的右嵌套求值同形), 起点取
--       rho3 h ⇒ 无需 mulMat 结合律, 只消耗 rho3-hom + ⊗-assocₚ + 单位律;
--   (b) 一般 X 版本  chain w X ≡ mulMat (rho3 (ev w)) X
--       需 mulMat-assoc 把右嵌套链重排, 其分量证明逐条消耗
--       Sovereign.Algebra.Zomega 的 mulZω-assoc / mulZω-distribˡ / mulZω-distribʳ
--       / mulZω-comm (dot 求和重排) —— 该环律模块已收口 (0 postulate)。
--   本节只追加, 不改动 rho3-hom 既有 12×12 拆子表证明。
--------------------------------------------------------------------------------

open import Data.Product using (proj₁)
open import Relation.Binary.PropositionalEquality using (sym; cong; trans)
open import Sovereign.Structology.A4GenWords
  using (Word; ε; _▸_; gen; ev; ⊗-assocₚ; pathToEqA4)
open import Sovereign.Structology.A4Group using (identity)

-- 生成元词的右嵌套矩阵链: chain ε X = X; chain (c ▸ w) X = ρ₃(gen c) · chain w X
chain : Word → Mat 3 3 → Mat 3 3
chain ε X = X
chain (c ▸ w) X = mulMat (rho3 (gen c)) (chain w X)

-- 词求值的矩阵实现: ρ₃ 沿词右嵌套累乘 = ρ₃ 词求值 (生成元路线的链式引理)
mulMat-chain : ∀ (w : Word) (h : A4) → chain w (rho3 h) ≡ rho3 (ev w ⊗ h)
mulMat-chain ε h = cong rho3 (sym (pathToEqA4 (proj₁ (identity h))))
mulMat-chain (c ▸ w) h =
  trans (cong (mulMat (rho3 (gen c))) (mulMat-chain w h))
    (trans (rho3-hom (gen c) (ev w ⊗ h))
      (cong rho3 (sym (⊗-assocₚ (gen c) (ev w) h))))

