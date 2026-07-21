{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Algebra.RepresentationBridge
-- P3-C: 表示论统一框架 — SO(3)→A₄ 与 SU(2)→2A₄ 分支规则的结构性连接
--
-- 核心定理:
--   1. 膨胀 (Inflation): A₄ 的 4 个不可约表示 {V1,V1',V1'',V3}
--      膨胀为 2A₄ 的 {W1,W1',W1'',W3}, 维数保持
--   2. 旋量识别: 2A₄ 多出的 3 个不可约表示 {W2,W2',W2''} (dim=2)
--      是 SU(2) 旋量结构的离散遗迹, -1 在其上作用为 -1
--   3. SU(2)→2A₄ 分支表: j=0→W1, j=1/2→W2, j=1→W3,
--      j=3/2→W2'⊕W2'', j=2→W1'⊕W1''⊕W3
--   4. 覆盖一致性: 整数自旋 → 仅膨胀表示 (无旋量);
--      半整数自旋 → 仅旋量表示 (无膨胀)
--   5. SO(3)↔SU(2) 匹配: 整数自旋的 SU(2)→2A₄ 分支
--      与 SO(3)→A₄ 分支通过膨胀映射一致
--   6. 维数会计: Σ(膨胀 dim²) = 12 = |A₄|,
--      Σ(旋量 dim²) = 12, 总计 24 = |2A₄|
--
-- 证明策略: 穷举法 (全 refl)
-- 宪法合规: 0 postulate, 禁止浮点
--
-- 依赖:
--   A4Representations  — A₄ 不可约表示
--   BinaryTetrahedral  — 2A₄ 群与不可约表示
--   BranchingRules     — SO(3)→A₄ 分支重数

module Sovereign.Algebra.RepresentationBridge where

open import Data.Nat using (ℕ; zero; suc)
  renaming (_+_ to _+N_; _*_ to _*N_)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Sovereign.Structology.A4Representations
  using (A4Irrep; V3; V1; V1'; V1''; dim)

open import Sovereign.Structology.BinaryTetrahedral
  using (BTIrrep; btDim)
  renaming (W1 to BW1; W1' to BW1'; W1'' to BW1''; W2 to BW2; W2' to BW2'; W2'' to BW2''; W3 to BW3)

open import Sovereign.Algebra.BranchingRules
  using (branchMult)

--------------------------------------------------------------------------------
-- §1. 膨胀映射: A₄ 不可约表示 → 2A₄ 不可约表示
--------------------------------------------------------------------------------
-- A₄ = 2A₄/Z₂ 的不可约表示通过商映射"膨胀"为 2A₄ 的不可约表示.
-- 这些表示中 -1 ∈ Z₂ 作用为 +1 (平凡), 因此因子化通过 A₄.

inflate : A4Irrep → BTIrrep
inflate V1   = BW1
inflate V1'  = BW1'
inflate V1'' = BW1''
inflate V3   = BW3

-- [分类: 已证引理] 膨胀保持维数 (穷举 4 case)
inflate-dim : ∀ v → btDim (inflate v) ≡ dim v
inflate-dim V1   = refl
inflate-dim V1'  = refl
inflate-dim V1'' = refl
inflate-dim V3   = refl

--------------------------------------------------------------------------------
-- §2. 旋量表示识别
--------------------------------------------------------------------------------
-- 2A₄ 比 A₄ 多出 3 个不可约表示 {W2, W2', W2''}, 均为 2 维.
-- 这些是 SU(2) 旋量结构的离散遗迹:
-- 中心元素 -1 ∈ Z₂ 在其上作用为 -1 (非平凡), 不因子化通过 A₄.

isSpinor : BTIrrep → ℕ
isSpinor BW2   = 1
isSpinor BW2'  = 1
isSpinor BW2'' = 1
isSpinor _     = 0

-- [分类: 已证引理] 旋量表示维数 = 2
spinor-dim-W2 : btDim BW2 ≡ 2
spinor-dim-W2 = refl

spinor-dim-W2' : btDim BW2' ≡ 2
spinor-dim-W2' = refl

spinor-dim-W2'' : btDim BW2'' ≡ 2
spinor-dim-W2'' = refl

-- [分类: 已证引理] 膨胀表示不是旋量
inflate-not-spinor : ∀ v → isSpinor (inflate v) ≡ 0
inflate-not-spinor V1   = refl
inflate-not-spinor V1'  = refl
inflate-not-spinor V1'' = refl
inflate-not-spinor V3   = refl

--------------------------------------------------------------------------------
-- §3. SU(2) 自旋层级
--------------------------------------------------------------------------------

data SU2Level : Set where
  J0   : SU2Level  -- j=0,   dim=1
  J1/2 : SU2Level  -- j=1/2, dim=2
  J1   : SU2Level  -- j=1,   dim=3
  J3/2 : SU2Level  -- j=3/2, dim=4
  J2   : SU2Level  -- j=2,   dim=5

su2Dim : SU2Level → ℕ
su2Dim J0   = 1
su2Dim J1/2 = 2
su2Dim J1   = 3
su2Dim J3/2 = 4
su2Dim J2   = 5

-- [分类: 已证引理] SU(2) 维数公式: dim(j) = 2j+1
su2DimFormula : ℕ → ℕ
su2DimFormula j = suc (j +N j)

su2Dim-matches : (su2DimFormula 0 ≡ su2Dim J0) × (su2DimFormula 1 ≡ su2Dim J1)
               × (su2DimFormula 2 ≡ su2Dim J2)
su2Dim-matches = refl , refl , refl

--------------------------------------------------------------------------------
-- §4. SU(2)→2A₄ 分支表
--------------------------------------------------------------------------------
-- SU(2) spin-j 表示限制到 2A₄ 后的分解:
--   j=0   (dim 1): W1
--   j=1/2 (dim 2): W2              ← 基本旋量
--   j=1   (dim 3): W3
--   j=3/2 (dim 4): W2' ⊕ W2''
--   j=2   (dim 5): W1' ⊕ W1'' ⊕ W3
--
-- 数学依据: 特征标内积 m(W,j) = (1/24) Σ_C |C| χ_j(C) conj(χ_W(C))

su2Branch : SU2Level → BTIrrep → ℕ
-- j=0: W1
su2Branch J0 BW1   = 1
su2Branch J0 BW1'  = 0
su2Branch J0 BW1'' = 0
su2Branch J0 BW2   = 0
su2Branch J0 BW2'  = 0
su2Branch J0 BW2'' = 0
su2Branch J0 BW3   = 0
-- j=1/2: W2
su2Branch J1/2 BW1   = 0
su2Branch J1/2 BW1'  = 0
su2Branch J1/2 BW1'' = 0
su2Branch J1/2 BW2   = 1
su2Branch J1/2 BW2'  = 0
su2Branch J1/2 BW2'' = 0
su2Branch J1/2 BW3   = 0
-- j=1: W3
su2Branch J1 BW1   = 0
su2Branch J1 BW1'  = 0
su2Branch J1 BW1'' = 0
su2Branch J1 BW2   = 0
su2Branch J1 BW2'  = 0
su2Branch J1 BW2'' = 0
su2Branch J1 BW3   = 1
-- j=3/2: W2' ⊕ W2''
su2Branch J3/2 BW1   = 0
su2Branch J3/2 BW1'  = 0
su2Branch J3/2 BW1'' = 0
su2Branch J3/2 BW2   = 0
su2Branch J3/2 BW2'  = 1
su2Branch J3/2 BW2'' = 1
su2Branch J3/2 BW3   = 0
-- j=2: W1' ⊕ W1'' ⊕ W3
su2Branch J2 BW1   = 0
su2Branch J2 BW1'  = 1
su2Branch J2 BW1'' = 1
su2Branch J2 BW2   = 0
su2Branch J2 BW2'  = 0
su2Branch J2 BW2'' = 0
su2Branch J2 BW3   = 1

--------------------------------------------------------------------------------
-- §5. SU(2)→2A₄ 分支维数验证
--------------------------------------------------------------------------------

su2-branch-dim : (j : SU2Level) →
  su2Branch j BW1   *N btDim BW1
  +N su2Branch j BW1'  *N btDim BW1'
  +N su2Branch j BW1'' *N btDim BW1''
  +N su2Branch j BW2   *N btDim BW2
  +N su2Branch j BW2'  *N btDim BW2'
  +N su2Branch j BW2'' *N btDim BW2''
  +N su2Branch j BW3   *N btDim BW3
  ≡ su2Dim j
su2-branch-dim J0   = refl
su2-branch-dim J1/2 = refl
su2-branch-dim J1   = refl
su2-branch-dim J3/2 = refl
su2-branch-dim J2   = refl

--------------------------------------------------------------------------------
-- §6. 覆盖一致性: 整数自旋 → 无旋量内容
--------------------------------------------------------------------------------
-- 覆盖映射 SU(2)→SO(3) 的核为 Z₂={±I}.
-- 整数自旋表示中 -I 作用为 +1, 因此因子化通过 SO(3),
-- 限制到 2A₄ 后仅包含膨胀表示 (来自 A₄), 不含旋量.

-- [分类: 已证引理] 整数自旋 j=0: 无旋量
integer-no-spinor-0 : (su2Branch J0 BW2 ≡ 0) × (su2Branch J0 BW2' ≡ 0) × (su2Branch J0 BW2'' ≡ 0)
integer-no-spinor-0 = refl , refl , refl

-- [分类: 已证引理] 整数自旋 j=1: 无旋量
integer-no-spinor-1 : (su2Branch J1 BW2 ≡ 0) × (su2Branch J1 BW2' ≡ 0) × (su2Branch J1 BW2'' ≡ 0)
integer-no-spinor-1 = refl , refl , refl

-- [分类: 已证引理] 整数自旋 j=2: 无旋量
integer-no-spinor-2 : (su2Branch J2 BW2 ≡ 0) × (su2Branch J2 BW2' ≡ 0) × (su2Branch J2 BW2'' ≡ 0)
integer-no-spinor-2 = refl , refl , refl

--------------------------------------------------------------------------------
-- §7. 覆盖一致性: 半整数自旋 → 无膨胀内容
--------------------------------------------------------------------------------
-- 半整数自旋表示中 -I 作用为 -1, 不因子化通过 SO(3).
-- 限制到 2A₄ 后仅包含旋量表示, 不含膨胀表示.

-- [分类: 已证引理] 半整数自旋 j=1/2: 无膨胀
halfint-no-inflate-1/2 : (su2Branch J1/2 BW1 ≡ 0) × (su2Branch J1/2 BW1' ≡ 0)
                       × (su2Branch J1/2 BW1'' ≡ 0) × (su2Branch J1/2 BW3 ≡ 0)
halfint-no-inflate-1/2 = refl , refl , refl , refl

-- [分类: 已证引理] 半整数自旋 j=3/2: 无膨胀
halfint-no-inflate-3/2 : (su2Branch J3/2 BW1 ≡ 0) × (su2Branch J3/2 BW1' ≡ 0)
                       × (su2Branch J3/2 BW1'' ≡ 0) × (su2Branch J3/2 BW3 ≡ 0)
halfint-no-inflate-3/2 = refl , refl , refl , refl

--------------------------------------------------------------------------------
-- §8. SO(3)↔SU(2) 匹配: 整数自旋分支通过膨胀一致
--------------------------------------------------------------------------------
-- 对整数自旋 l, SU(2)→2A₄ 分支中膨胀表示的重数
-- 等于 SO(3)→A₄ 分支中对应 A₄ 表示的重数:
--   su2Branch(l, inflate(v)) = branchMult(v, l)

-- j=0 ↔ l=0
match-0 : (su2Branch J0 (inflate V1) ≡ branchMult V1 0)
        × (su2Branch J0 (inflate V1') ≡ branchMult V1' 0)
        × (su2Branch J0 (inflate V1'') ≡ branchMult V1'' 0)
        × (su2Branch J0 (inflate V3) ≡ branchMult V3 0)
match-0 = refl , refl , refl , refl

-- j=1 ↔ l=1
match-1 : (su2Branch J1 (inflate V1) ≡ branchMult V1 1)
        × (su2Branch J1 (inflate V1') ≡ branchMult V1' 1)
        × (su2Branch J1 (inflate V1'') ≡ branchMult V1'' 1)
        × (su2Branch J1 (inflate V3) ≡ branchMult V3 1)
match-1 = refl , refl , refl , refl

-- j=2 ↔ l=2
match-2 : (su2Branch J2 (inflate V1) ≡ branchMult V1 2)
        × (su2Branch J2 (inflate V1') ≡ branchMult V1' 2)
        × (su2Branch J2 (inflate V1'') ≡ branchMult V1'' 2)
        × (su2Branch J2 (inflate V3) ≡ branchMult V3 2)
match-2 = refl , refl , refl , refl

--------------------------------------------------------------------------------
-- §9. 维数会计: 12 + 12 = 24
--------------------------------------------------------------------------------
-- A₄ 的 4 个不可约表示的维数平方和 = 12 = |A₄|
-- 2A₄ 多出的 3 个旋量表示的维数平方和 = 12
-- 总计 = 24 = |2A₄|

-- [分类: 已证引理] 膨胀表示维数平方和 = 12
inflate-dim-sq-sum :
  btDim BW1 *N btDim BW1 +N btDim BW1' *N btDim BW1'
  +N btDim BW1'' *N btDim BW1'' +N btDim BW3 *N btDim BW3
  ≡ 12
inflate-dim-sq-sum = refl

-- [分类: 已证引理] 旋量表示维数平方和 = 12
spinor-dim-sq-sum :
  btDim BW2 *N btDim BW2 +N btDim BW2' *N btDim BW2'
  +N btDim BW2'' *N btDim BW2''
  ≡ 12
spinor-dim-sq-sum = refl

-- [分类: 已证引理] 12 + 12 = 24 = |2A₄|
dim-accounting : 12 +N 12 ≡ 24
dim-accounting = refl

--------------------------------------------------------------------------------
-- §10. 表示论层级总结
--------------------------------------------------------------------------------
--
--   SU(2) ⊃ 2A₄ (Q₈ ⋊ C₃, 24 元素)
--     ↓       ↓
--   SO(3) ⊃ A₄  (12 元素)
--
--   SU(2) 表示论:  spin j = 0, 1/2, 1, 3/2, 2, ...
--   2A₄ 表示论:    7 个不可约表示 {W1,W1',W1'',W2,W2',W2'',W3}
--   A₄ 表示论:     4 个不可约表示 {V1,V1',V1'',V3}
--
--   整数自旋 (玻色):   SU(2)→2A₄ 仅含膨胀表示 ↔ SO(3)→A₄
--   半整数自旋 (费米): SU(2)→2A₄ 仅含旋量表示 (无 SO(3) 对应)
--
--   旋量表示 {W2,W2',W2''} 是 SU(2) 覆盖结构的离散遗迹,
--   在 SO(3) 投影中不可见 — 这正是"自旋"的拓扑本质.
