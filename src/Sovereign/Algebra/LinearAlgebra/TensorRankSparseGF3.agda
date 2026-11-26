{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Algebra.LinearAlgebra.TensorRankSparseGF3
-- M19: 稀疏加权层——下界机制的第一块陈述层
-- （镜像 Lean `Rectangle/Weights.lean` 的 WeightedRankLE / supportSize;
--   承载 Bläser 2003 的 rank ≥ 2n²+n−2 与 2609.06725 的 F₂ 下界 21 这类
--   「限制界 + 穷举」证明的承重结构; 2026-11-26 文献检索后在用户定案下开建）
--
-- 数学背景
--   下界（rank ≥ …）不走「表」, 走**约束**: 一个加权张量 w 的支撑结构
--   （哪些三元组非零）约束一切分解的形态。Lean 的 WeightedRankLE w r 说:
--   加权矩阵张量（结构常数条件处取 w, 其余取 T₀）有 r 项分解;
--   supportSize 数 w 的非零条目。Wang 自动框架（arXiv:2603.07280）在
--   F₂ 上把 3×3 下界从 19（Bläser 2003, 域泛型）推到 20, 2609.06725 再推到 21,
--   并把 F₃ 的 ⟨2,3,3⟩ 精确解出 = 15——这些证明的陈述对象就是本件镜像的谓词。
--
-- 内容
--   §1 加权结构常数 wmm 与谓词 WeightedRankLE₃
--   §2 支撑指示 suppInd 与支撑数 supportSize₃（嵌套 ℕ 和）
--   §3 桥: RankLE₃ n r → WeightedRankLE₃ n r (λ _ _ _ → T₁)（mm = 全 T₁ 加权特例）
--   §4 哨兵: n = 1, 2 的支撑数
--
-- 诚实边界
--   · 本件只有谓词层。三条稀疏定律（DensityBound/CellBound/DegreeBound）在 Lean 里
--     是关于**抽象指数**的泛量化命题（K.1: 域泛型组合学）, 无可枚举的有限核对对象;
--     它们的有限形态要等 exponent 机制的镜像口径（ℝ 被宪法排除, 走 Saving 型有限化）。
--   · 限制界词汇（rows/cols/inner、陪集分析）未镜像——那是 2609.06725 的下一条。
--
-- 复用(先查后写): RankLE₃ / mm / oneIf / Pos / Out（TensorRankGF3）、sumℕ（TensorRankCircuitGF3）。
--
-- 0 postulate / 0 REWRITE 规则 / 0 洞
module Sovereign.Algebra.LinearAlgebra.TensorRankSparseGF3 where

open import Data.Nat using (ℕ; zero; suc; _*_)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; sym)

open import Sovereign.Base.Trit using (Trit; T₀; T₁; _⊗_; ⊗-identityˡ)
open import Sovereign.Algebra.LinearAlgebra.GF3LaplacianN using (sumFin)
open import Sovereign.Algebra.LinearAlgebra.TensorRankGF3
  using (RankLE₃; mm; Pos; Out)
open import Sovereign.Algebra.LinearAlgebra.TensorRankCircuitGF3 using (sumℕ)

--------------------------------------------------------------------------------
-- §1. 加权结构常数与谓词
--------------------------------------------------------------------------------

-- 加权结构常数: 结构常数条件成立处取 w(i,j,k)（x₁=i, y₂=k, x₂=j）, 其余 T₀
--   （w ⊗ mm: mm 是 0/1 指示积, T₀ 会吞掉一切——⊗-zeroʳ）
wmm : (n : ℕ) → (Fin n → Fin n → Fin n → Trit) → Pos n → Pos n → Out n → Trit
wmm n w x y z = (w (proj₁ x) (proj₂ y) (proj₂ x)) ⊗ (mm n x y z)

-- ★ 加权矩阵张量的 r 项分解（镜像 Lean `Weights.lean` WeightedRankLE）
record WeightedRankLE₃ (n r : ℕ) (w : Fin n → Fin n → Fin n → Trit) : Set where
  field
    ra : Fin r → Pos n → Trit
    rb : Fin r → Pos n → Trit
    rc : Fin r → Out n → Trit
    wrank-eq : ∀ x y z →
      sumFin (λ l → (ra l x) ⊗ ((rb l y) ⊗ (rc l z))) ≡ wmm n w x y z

--------------------------------------------------------------------------------
-- §2. 支撑指示与支撑数
--------------------------------------------------------------------------------

-- 支撑指示: T₀ 记 0, T₁/T₂ 记 1
suppInd : Trit → ℕ
suppInd T₀ = zero
suppInd T₁ = suc zero
suppInd T₂ = suc zero

-- 支撑数: w 的非零条目个数（嵌套 ℕ 和, 镜像 Lean supportSize 的 Σ-指示）
supportSize₃ : ∀ n → (Fin n → Fin n → Fin n → Trit) → ℕ
supportSize₃ n w = sumℕ {n} (λ i → sumℕ {n} (λ j → sumℕ {n} (λ k → suppInd (w i j k))))

--------------------------------------------------------------------------------
-- §3. 桥: 方形秩分解 = 全 T₁ 加权的分解
--------------------------------------------------------------------------------

-- 全 T₁ 加权的结构常数就是 mm（T₁ ⊗ mm 按定义归约到 mm）
rankLE₃→weighted : ∀ n r → RankLE₃ n r → WeightedRankLE₃ n r (λ a b c → T₁)
rankLE₃→weighted n r R = record
  { ra = RankLE₃.ra R
  ; rb = RankLE₃.rb R
  ; rc = RankLE₃.rc R
  ; wrank-eq = λ x y z → trans (RankLE₃.rank-eq R x y z) (sym (⊗-identityˡ (mm n x y z)))
  }

--------------------------------------------------------------------------------
-- §4. 哨兵
--------------------------------------------------------------------------------

-- n = 1: 全 T₁ 加权的支撑数 = 1
sentinel-support-1 : supportSize₃ 1 (λ _ _ _ → T₁) ≡ 1
sentinel-support-1 = refl

-- n = 2: 全 T₁ 加权的支撑数 = 8
sentinel-support-2 : supportSize₃ 2 (λ _ _ _ → T₁) ≡ 8
sentinel-support-2 = refl

-- n = 1 的 mm 哨兵（与 M18 呼应）
sentinel-mm-1 : wmm 1 (λ _ _ _ → T₁) (fzero , fzero) (fzero , fzero) (fzero , fzero) ≡ T₁
sentinel-mm-1 = refl
