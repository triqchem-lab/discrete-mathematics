{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Algebra.Jacobian.jac_Topology
-- 离散同调矩阵化 — 有限复形 · 边界矩阵 · dimH · 欧拉示性数
--
-- 数学背景:
--   离散代数拓扑把链复形的同调完全矩阵化:
--   有限复形 (顶点 Fin V, 边 Fin E, 面 Fin F) 的边界算子 ∂ₖ 表现为 GF(3) 上的
--   入射矩阵 M_∂[k], 同调维数 dim Hₖ = nullity(∂ₖ) − rank(∂ₖ₊₁), 欧拉示性数
--   χ = Σ(−1)ᵏ dim Hₖ。所有计算在有限域 GF(3) 上进行, 0 postulate, 无连续统参与。
--   蓝图: docs/Topology/第四波-代数拓扑与代数群-红灯审查与离散重构.md §3.1
--
-- 核心原则:
--   1. 边界算子 = 入射矩阵 (§2 桥接定理 M∂1-boundary3: 矩阵元与 ∂₁ 系数逐点一致)
--   2. rank/nullity 由双侧证书钉住 (消元法具体而真):
--      rank ∂₁ = 2 — 下界: 2×2 子式 det = T₁ ≠ T₀ ⟹ 满秩 (复用 jac_Matrix.rank);
--                  上界: 列消元 c₂ = T₂·c₀ ⊕ T₂·c₁ (elim-c2)
--      nullity ∂₁ = 1 — ker ∂₁ = { k·(T₁,T₁,T₁) } 完备刻画 (ker-span, 27-case)
--   3. dimH 复用 Problem.Hodge.ChainComplex 记录 (不重定义), 与既有 tri 实例对齐
--   4. χ = Σ(−1)ᵏ dim Hₖ 在 ℤ 上定义 (对齐 Problem.Hodge.EulerChar 口径);
--      具象复形上 χ 的计算已闭合, χ = 0 ⟺ 双射 F : V → E 的一般等价如实留 roadmap
--   5. 0 postulate / 0 hole / 0 sorry; 单引理 refl ≤ 27 case
--
-- 包含:
--   §1 有限复形 FiniteComplex (顶点/边/面 + 入射数据, 三角复形两实例)
--   §2 边界矩阵 BoundaryMatrix (M_∂[1], GF(3) 消元 rank/nullity, ∂₁∘∂₂ = 0)
--   §3 dimH (ChainComplex 记录实例 + 与 Hodge.tri 对齐)
--   §4 欧拉示性数 EulerCharacteristic (χ = Σ(−1)ᵏ dimHₖ, 具象计算)

module Sovereign.Algebra.Jacobian.jac_Topology where

open import Data.Nat using (ℕ; zero; suc; _+_; _∸_)
open import Data.Fin using (Fin; zero; suc)
open import Data.Fin.Properties using (_≟_)
open import Data.Product using (_×_; _,_; Σ)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong)
open import Data.Integer using (ℤ; +_) renaming (_+_ to _+ℤ_; _-_ to _-ℤ_)
open import Sovereign.Base.Trit using (Trit; T₀; T₁; T₂; _⊕_; _⊗_)
open import Sovereign.Algebra.Jacobian.jac_Discrete using (Mat2; det2)
open import Sovereign.Algebra.Jacobian.jac_Matrix
  using (Rank; rank; rank2; det≠0→rank2)
open import Sovereign.Problem.Hodge.ChainComplex as CC
  using (ChainComplex; dimH; tri)

-- 注: _⊕_/_⊗_ 来自 Base.Trit (import), Agda 不允许在使用方模块重声明 fixity
--   (UnknownNamesInFixityDecl); 本模块所有表达式均显式加括号, 不依赖 fixity。

--------------------------------------------------------------------------------
-- §1. 有限复形 (FiniteComplex)
--------------------------------------------------------------------------------

-- 链群 Cₖ = GF(3)^n —— n 维 GF(3) 向量 (以 Fin n → Trit 表示)
GF3Vec : ℕ → Set
GF3Vec n = Fin n → Trit

0v : ∀ {n} → GF3Vec n
0v _ = T₀

-- C₃ 的标准基
e₀ e₁ e₂ : GF3Vec 3
e₀ zero = T₁; e₀ (suc zero) = T₀; e₀ (suc (suc zero)) = T₀; e₀ (suc (suc (suc ())))
e₁ zero = T₀; e₁ (suc zero) = T₁; e₁ (suc (suc zero)) = T₀; e₁ (suc (suc (suc ())))
e₂ zero = T₀; e₂ (suc zero) = T₀; e₂ (suc (suc zero)) = T₁; e₂ (suc (suc (suc ())))

-- GF(3) 乘法验证 (编译期 refl)
⊗-verify : (T₁ ⊗ T₂ ≡ T₂) × (T₁ ⊗ T₁ ≡ T₁) × (T₀ ⊗ T₁ ≡ T₀)
⊗-verify = refl , refl , refl

-- 有限复形: 顶点集 Fin V、边集 Fin E、面集 Fin F + 入射数据
--   edge-ends : 每条边的定向端点 (起点, 终点)
--   face-∂    : 每个面的边界链 (GF(3) 系数)
-- [roadmap] 同胚于 T⁶ 格点结构: T⁶ 一维骨架 (729 格点 + 邻接边) 是本记录的
--   高维实例, 其 rank/nullity 计算沿 §2 同一消元路径推广, 本模块先在 3 顶点
--   三角复形上给出完整可验证计算。
record FiniteComplex (V E F : ℕ) : Set where
  field
    edge-ends : Fin E → Fin V × Fin V
    face-∂    : Fin F → GF3Vec E

-- 边的端点表: e₀=(0→1), e₁=(1→2), e₂=(2→0) (三角形定向)
ends3 : Fin 3 → Fin 3 × Fin 3
ends3 zero = zero , suc zero
ends3 (suc zero) = suc zero , suc (suc zero)
ends3 (suc (suc zero)) = suc (suc zero) , zero
ends3 (suc (suc (suc ())))

-- 三角形 1-骨架 (图复形): V=3, E=3, F=0
graph3 : FiniteComplex 3 3 0
graph3 = record { edge-ends = ends3 ; face-∂ = λ () }

-- 单面闭链 (面边界 = e₀+e₁+e₂, 恰为 §2 的核向量)
face1 : GF3Vec 3
face1 _ = T₁

-- 三角剖分 (填入 2-胞腔): V=3, E=3, F=1
filled3 : FiniteComplex 3 3 1
filled3 = record { edge-ends = ends3 ; face-∂ = λ { zero → face1 ; (suc ()) } }

--------------------------------------------------------------------------------
-- §2. 边界矩阵 (BoundaryMatrix)
--------------------------------------------------------------------------------

-- 入射元: 顶点 v 在定向边 (u,w) 上的系数 (起点 −1 = T₂, 终点 +1 = T₁)
inc : ∀ {V} → Fin V → Fin V × Fin V → Trit
inc v (u , w) with v ≟ u | v ≟ w
... | yes _ | _     = T₂
... | no _  | yes _ = T₁
... | no _  | no _  = T₀

-- ∂₁ 的矩阵表示 M_∂[1]: V×E 元 (GF(3))
M∂1 : ∀ {V E F} → FiniteComplex V E F → Fin V → Fin E → Trit
M∂1 C v e = inc v (FiniteComplex.edge-ends C e)

-- 三角形 1-骨架的边界算子 (循环置换矩阵)
-- M = [[T₂,T₀,T₁], [T₁,T₂,T₀], [T₀,T₁,T₂]] (行 = 顶点, 列 = 边)
boundary3 : GF3Vec 3 → GF3Vec 3
boundary3 v = λ { zero               → ((v zero ⊗ T₂) ⊕ (v (suc zero) ⊗ T₀)) ⊕ (v (suc (suc zero)) ⊗ T₁)
                ; (suc zero)         → ((v zero ⊗ T₁) ⊕ (v (suc zero) ⊗ T₂)) ⊕ (v (suc (suc zero)) ⊗ T₀)
                ; (suc (suc zero))   → ((v zero ⊗ T₀) ⊕ (v (suc zero) ⊗ T₁)) ⊕ (v (suc (suc zero)) ⊗ T₂)
                ; (suc (suc (suc ())))
                }

-- 基向量按 Fin 3 索引
basis : Fin 3 → GF3Vec 3
basis zero = e₀
basis (suc zero) = e₁
basis (suc (suc zero)) = e₂
basis (suc (suc (suc ())))

-- 桥接定理: 边界算子 = 入射矩阵 M∂1 的列 (逐点一致, 9-case refl)
M∂1-boundary3 : ∀ (v j : Fin 3) → M∂1 graph3 v j ≡ boundary3 (basis j) v
M∂1-boundary3 zero zero = refl
M∂1-boundary3 zero (suc zero) = refl
M∂1-boundary3 zero (suc (suc zero)) = refl
M∂1-boundary3 (suc zero) zero = refl
M∂1-boundary3 (suc zero) (suc zero) = refl
M∂1-boundary3 (suc zero) (suc (suc zero)) = refl
M∂1-boundary3 (suc (suc zero)) zero = refl
M∂1-boundary3 (suc (suc zero)) (suc zero) = refl
M∂1-boundary3 (suc (suc zero)) (suc (suc zero)) = refl

-- ─── 元组视图 (27-case 核计算用) ───
V3 : Set
V3 = Trit × Trit × Trit

to3 : GF3Vec 3 → V3
to3 v = v zero , v (suc zero) , v (suc (suc zero))

∂₁Δ : V3 → V3
∂₁Δ (x , y , z) = (((x ⊗ T₂) ⊕ (y ⊗ T₀)) ⊕ (z ⊗ T₁))
                , (((x ⊗ T₁) ⊕ (y ⊗ T₂)) ⊕ (z ⊗ T₀))
                , (((x ⊗ T₀) ⊕ (y ⊗ T₁)) ⊕ (z ⊗ T₂))

zeroV oneV twoV : V3
zeroV = T₀ , T₀ , T₀
oneV  = T₁ , T₁ , T₁
twoV  = T₂ , T₂ , T₂

-- 元组视图与 Fin 视图一致 (定义相等即 refl)
∂₁Δ-bridge : ∀ (v : GF3Vec 3) → ∂₁Δ (to3 v) ≡ to3 (boundary3 v)
∂₁Δ-bridge v = refl

-- 常向量在核中 (与旧版口径一致)
const1 : GF3Vec 3
const1 _ = T₁

const1-ker0 : ((T₁ ⊗ T₂) ⊕ (T₁ ⊗ T₀)) ⊕ (T₁ ⊗ T₁) ≡ T₀; const1-ker0 = refl
const1-ker1 : ((T₁ ⊗ T₁) ⊕ (T₁ ⊗ T₂)) ⊕ (T₁ ⊗ T₀) ≡ T₀; const1-ker1 = refl
const1-ker2 : ((T₁ ⊗ T₀) ⊕ (T₁ ⊗ T₁)) ⊕ (T₁ ⊗ T₂) ≡ T₀; const1-ker2 = refl

const1-in-kernel : ((T₁ ⊗ T₂) ⊕ (T₁ ⊗ T₀)) ⊕ (T₁ ⊗ T₁) ≡ T₀
const1-in-kernel = refl

-- ─── 核的完备刻画: ker ∂₁ = { k·(T₁,T₁,T₁) } —— nullity = 1 ───

π₁ π₂ π₃ : V3 → Trit
π₁ (a , _ , _) = a
π₂ (_ , b , _) = b
π₃ (_ , _ , c) = c

-- [策略A] 27-case 完备核对 (3 条核向量 + 24 条消去):
--   ∂₁Δ (x,y,z) = (2x+z, x+2y, y+2z), 解 ∂₁Δ v = 0 ⟺ x = y = z。
--   每个非核分支以空模式 () 拒绝 ∂₁Δ v ≡ zeroV。
ker-span : (v : V3) → ∂₁Δ v ≡ zeroV
         → Σ Trit (λ k → v ≡ (k ⊗ T₁ , k ⊗ T₁ , k ⊗ T₁))
-- 核中的三个向量: 0, (T₁,T₁,T₁), (T₂,T₂,T₂)
ker-span (T₀ , T₀ , T₀) _ = T₀ , refl
ker-span (T₁ , T₁ , T₁) _ = T₁ , refl
ker-span (T₂ , T₂ , T₂) _ = T₂ , refl
-- 其余 24 个向量均不在核中
ker-span (T₀ , T₀ , T₁) ()
ker-span (T₀ , T₀ , T₂) ()
ker-span (T₀ , T₁ , T₀) ()
ker-span (T₀ , T₁ , T₁) ()
ker-span (T₀ , T₁ , T₂) ()
ker-span (T₀ , T₂ , T₀) ()
ker-span (T₀ , T₂ , T₁) ()
ker-span (T₀ , T₂ , T₂) ()
ker-span (T₁ , T₀ , T₀) ()
ker-span (T₁ , T₀ , T₁) ()
ker-span (T₁ , T₀ , T₂) ()
ker-span (T₁ , T₁ , T₀) ()
ker-span (T₁ , T₁ , T₂) ()
ker-span (T₁ , T₂ , T₀) ()
ker-span (T₁ , T₂ , T₁) ()
ker-span (T₁ , T₂ , T₂) ()
ker-span (T₂ , T₀ , T₀) ()
ker-span (T₂ , T₀ , T₁) ()
ker-span (T₂ , T₀ , T₂) ()
ker-span (T₂ , T₁ , T₀) ()
ker-span (T₂ , T₁ , T₁) ()
ker-span (T₂ , T₁ , T₂) ()
ker-span (T₂ , T₂ , T₀) ()
ker-span (T₂ , T₂ , T₁) ()

-- ─── rank 计算: 双侧证书 (消元法) ───

-- 边界矩阵的三列: ∂₁ eᵢ
col0 col1 col2 : V3
col0 = T₂ , T₁ , T₀
col1 = T₀ , T₂ , T₁
col2 = T₁ , T₀ , T₂

col0-correct : ∂₁Δ (T₁ , T₀ , T₀) ≡ col0; col0-correct = refl
col1-correct : ∂₁Δ (T₀ , T₁ , T₀) ≡ col1; col1-correct = refl
col2-correct : ∂₁Δ (T₀ , T₀ , T₁) ≡ col2; col2-correct = refl

-- 2×2 子式 (col0,col1 的前两行): [[T₂,T₀],[T₁,T₂]]
minor2 : Mat2
minor2 = (T₂ , T₀) , (T₁ , T₂)

minor2-det : det2 minor2 ≡ T₁
minor2-det = refl

minor2-det≢0 : det2 minor2 ≢ T₀
minor2-det≢0 = λ ()

-- 复用 jac_Matrix: det ≠ T₀ ⟹ 2×2 子式满秩 (rank2)
-- ⟹ rank ∂₁ ≥ 2 (下界证书)
minor2-rank : rank minor2 ≡ rank2
minor2-rank = det≠0→rank2 minor2 minor2-det≢0

_·v_ : Trit → V3 → V3
k ·v (a , b , c) = (k ⊗ a) , (k ⊗ b) , (k ⊗ c)

_+v_ : V3 → V3 → V3
(a , b , c) +v (d , e , f) = (a ⊕ d) , (b ⊕ e) , (c ⊕ f)

-- 列消元: c₂ ← c₂ ⊖ T₂·c₀ ⊖ T₂·c₁ = 0 (第三列可由前两列表出)
-- ⟹ 像 ⊆ span{col0,col1} ⟹ rank ∂₁ ≤ 2 (上界证书)
elim-c2 : col2 ≡ (T₂ ·v col0) +v (T₂ ·v col1)
elim-c2 = refl

-- 消元法 rank/nullity 计算 (双侧证书钉住):
--   rank∂1 = 2: 下界 minor2-rank, 上界 elim-c2
--   nullity∂1 = 1: ker-span 完备刻画 (核恰 = 一维 span{oneV})
rank∂1 nullity∂1 : ℕ
rank∂1 = 2
nullity∂1 = 1

-- 秩-零度一致性: rank + nullity = dim C₁ = 3
rank-nullity-Δ : rank∂1 + nullity∂1 ≡ 3
rank-nullity-Δ = refl

-- ─── ∂₂ (面边界) 与链条件 ∂₁∘∂₂ = 0 ───

-- C₂ = GF(3)·面; ∂₂ x = x·(面边界链) = x·(T₁,T₁,T₁)
∂₂Δ : Trit → V3
∂₂Δ x = x ·v oneV

face-cycle : ∂₂Δ T₁ ≡ oneV
face-cycle = refl

-- 链条件: ∂₁∘∂₂ = 0 (3-case refl)
∂₁∂₂-zero : ∀ x → ∂₁Δ (∂₂Δ x) ≡ zeroV
∂₁∂₂-zero T₀ = refl
∂₁∂₂-zero T₁ = refl
∂₁∂₂-zero T₂ = refl

-- nullity ∂₂ = 0 证书: ∂₂ x = 0 ⟹ x = T₀ (3-case)
∂₂-inj : ∀ x → ∂₂Δ x ≡ zeroV → x ≡ T₀
∂₂-inj T₀ _ = refl
∂₂-inj T₁ h = ⊥-elim (oneV≢zeroV h)
  where
  oneV≢zeroV : oneV ≡ zeroV → ⊥
  oneV≢zeroV ()
∂₂-inj T₂ h = ⊥-elim (twoV≢zeroV h)
  where
  twoV≢zeroV : twoV ≡ zeroV → ⊥
  twoV≢zeroV ()

-- rank ∂₂ = 1: 像 = span{oneV}, oneV ≠ zeroV, ∂₂ T₁ = oneV
rank∂2 nullity∂2 : ℕ
rank∂2 = 1
nullity∂2 = 0

-- Fin 视图的链条件: 面的边界链是闭链 (boundary3 (face-∂ filled3 zero) = 0)
chain-cond : ∀ (i : Fin 3) → boundary3 (FiniteComplex.face-∂ filled3 zero) i ≡ T₀
chain-cond zero = refl
chain-cond (suc zero) = refl
chain-cond (suc (suc zero)) = refl
chain-cond (suc (suc (suc ())))

-- 面边界链的元组视图 = 核向量
face-∂-filled3 : to3 (FiniteComplex.face-∂ filled3 zero) ≡ oneV
face-∂-filled3 = refl

-- [roadmap] GF(9) 侧的消元法 rank 接口已存在: jac_GF9Matrix.rank2-gf9 / rank3-gf9;
--   本模块的 GF(3) 消元计算与 GF(9) 版本的对齐留后续模块。

--------------------------------------------------------------------------------
-- §3. 同调维数 dimH (复用 Problem.Hodge.ChainComplex 记录, 勿重定义)
--------------------------------------------------------------------------------

-- 与旧版口径一致的兼容常量 (Problem.Hodge.Hodge 依赖以下符号):
rank∂ nullity∂ : ℕ
rank∂ = rank∂1
nullity∂ = nullity∂1

rank-nullity-ok : rank∂ + nullity∂ ≡ 3
rank-nullity-ok = refl

dimH0 dimH1 : ℕ
dimH0 = 3 ∸ rank∂     -- dim H₀ = dim C₀ − rank ∂₁ = 1
dimH1 = nullity∂      -- dim H₁ = nullity ∂₁ = 1

-- ─── ChainComplex 记录实例 (copattern 构造, 不与记录字段名冲突) ───

-- 图复形 (三角形 1-骨架): dimC = (3,3), rank∂ = (0,2),
--   nullity∂ = (3,1), dimℋ = (1,1)
g3-dimC g3-rank g3-null g3-harm : ℕ → ℕ
g3-dimC 0 = 3
g3-dimC 1 = 3
g3-dimC _ = 0
g3-rank 0 = 0
g3-rank 1 = 2
g3-rank _ = 0
g3-null k = g3-dimC k ∸ g3-rank k
g3-harm 0 = 1
g3-harm 1 = 1
g3-harm _ = 0

g3-hodge : ∀ k → g3-null k ≡ g3-rank (suc k) + g3-harm k
g3-hodge 0 = refl
g3-hodge 1 = refl
g3-hodge (suc (suc k)) = refl

graph3C : ChainComplex 2
CC.ChainComplex.dimC graph3C = g3-dimC
CC.ChainComplex.rank∂ graph3C = g3-rank
CC.ChainComplex.nullity∂ graph3C = g3-null
CC.ChainComplex.dimℋ graph3C = g3-harm
CC.ChainComplex.hodge-decomp graph3C = g3-hodge

-- 记录数字与 §2 消元计算对齐 (双向 refl)
rank-bridge : g3-rank 1 ≡ rank∂1
rank-bridge = refl

nullity-bridge : g3-null 1 ≡ nullity∂1
nullity-bridge = refl

-- dimH 复用记录函数 dimH (ChainComplex.dimH), 不重定义
dimH-graph3-0 : dimH graph3C 0 ≡ 1
dimH-graph3-0 = refl

dimH-graph3-1 : dimH graph3C 1 ≡ 1
dimH-graph3-1 = refl

-- 与既有 Hodge.tri 实例逐点对齐 (tri 即同一三角形 1-骨架)
align-tri : ∀ k → dimH graph3C k ≡ dimH tri k
align-tri 0 = refl
align-tri 1 = refl
align-tri (suc (suc k)) = refl

-- ─── 填入 2-胞腔后的复形: H₁ 被面边界杀死 ───

-- filled3: dimC = (3,3,1), rank∂ = (0,2,1),
--   nullity∂ = (3,1,0), dimℋ = (1,0,0)
-- 注: rank∂ 2 = 1 由 §2 证书 (rank∂2=1, ∂₂-inj) 支持;
--     nullity∂ 1 = 1 = rank∂ 2 (面边界恰为核向量) ⟹ dim H₁ = 0。
f3-dimC f3-rank f3-null f3-harm : ℕ → ℕ
f3-dimC 0 = 3
f3-dimC 1 = 3
f3-dimC 2 = 1
f3-dimC _ = 0
f3-rank 0 = 0
f3-rank 1 = 2
f3-rank 2 = 1
f3-rank _ = 0
f3-null k = f3-dimC k ∸ f3-rank k
f3-harm 0 = 1
f3-harm 1 = 0
f3-harm 2 = 0
f3-harm _ = 0

f3-hodge : ∀ k → f3-null k ≡ f3-rank (suc k) + f3-harm k
f3-hodge 0 = refl
f3-hodge 1 = refl
f3-hodge 2 = refl
f3-hodge (suc (suc (suc k))) = refl

filled3C : ChainComplex 3
CC.ChainComplex.dimC filled3C = f3-dimC
CC.ChainComplex.rank∂ filled3C = f3-rank
CC.ChainComplex.nullity∂ filled3C = f3-null
CC.ChainComplex.dimℋ filled3C = f3-harm
CC.ChainComplex.hodge-decomp filled3C = f3-hodge

dimH-filled3-0 : dimH filled3C 0 ≡ 1
dimH-filled3-0 = refl

dimH-filled3-1 : dimH filled3C 1 ≡ 0
dimH-filled3-1 = refl

dimH-filled3-2 : dimH filled3C 2 ≡ 0
dimH-filled3-2 = refl

--------------------------------------------------------------------------------
-- §4. 欧拉示性数 (EulerCharacteristic)
--------------------------------------------------------------------------------

-- χ = Σ (−1)ᵏ dim Hₖ, ℤ 上交替和 (对齐 Problem.Hodge.EulerChar 口径)
χH : ∀ {len} → ChainComplex len → ℤ
χH C = (+ (dimH C 0) -ℤ + (dimH C 1)) +ℤ + (dimH C 2)

-- 链侧交替和: χ = Σ (−1)ᵏ dim Cₖ
χC : ∀ {len} → ChainComplex len → ℤ
χC C = (+ (CC.ChainComplex.dimC C 0) -ℤ + (CC.ChainComplex.dimC C 1))
       +ℤ + (CC.ChainComplex.dimC C 2)

-- 具象实例 1: 三角形 1-骨架 (graph3C)
--   χ_C = 3 − 3 = 0, χ_H = 1 − 1 = 0
χ-graph3 : χH graph3C ≡ + 0
χ-graph3 = refl

χ-graph3-chain : χC graph3C ≡ + 0
χ-graph3-chain = refl

-- 欧拉-庞加莱 (具象): χ_C = χ_H
euler-poincare-graph3 : χC graph3C ≡ χH graph3C
euler-poincare-graph3 = refl

-- 具象实例 2: 三角剖分 (filled3C)
--   χ_C = 3 − 3 + 1 = 1, χ_H = 1 − 0 + 0 = 1
χ-filled3 : χH filled3C ≡ + 1
χ-filled3 = refl

χ-filled3-chain : χC filled3C ≡ + 1
χ-filled3-chain = refl

euler-poincare-filled3 : χC filled3C ≡ χH filled3C
euler-poincare-filled3 = refl

-- [roadmap] 一般定理「χ = 0 ⟺ 存在双射 F : V → E」(与 det(M_F) ≠ 0 ⟺ 双射的
--   代数恒等) 未形式化, 不在此断言。两侧引理已备:
--   - 双射侧: jac_Pigeonhole.pigeonhole-2 (Inj2 F → Surj2 F), encode9/decode9 往返
--   - 行列式侧: jac_Matrix.det≠0→rank2 / det-mul / inverse
--   本模块给出的是具象复形上的 χ 计算 (χ_graph3 = 0, |V| = |E| = 3 时存在双射
--   Fin 3 → Fin 3 是鸽巢平凡情形), 一般等价待 §2 消元框架推广到任意 V×E 矩阵。
--------------------------------------------------------------------------------

--------------------------------------------------------------------------------
open import Data.Product using (proj₁)

-- §5. 边界类商对象（DEEP.derived-functors 具体实例）：
--     H₁ = Z₁ / B₁ —— graph3：B₁=0 ⇒ H₁ ≅ Trit 三类；filled3：B₁=Z₁ ⇒ H₁ 单类
--------------------------------------------------------------------------------

-- 循环子型（商对象的可计算代表层）
H1c : Set
H1c = Σ V3 (λ v → ∂₁Δ v ≡ zeroV)

-- 类映射：k ↦ 对角循环
h1 : Trit → H1c
h1 k = (k ⊗ T₁ , k ⊗ T₁ , k ⊗ T₁) , cyc k
  where
    cyc : ∀ k → ∂₁Δ (k ⊗ T₁ , k ⊗ T₁ , k ⊗ T₁) ≡ zeroV
    cyc T₀ = refl
    cyc T₁ = refl
    cyc T₂ = refl

h1-inj : ∀ k₁ k₂ → proj₁ (h1 k₁) ≡ proj₁ (h1 k₂) → k₁ ≡ k₂
h1-inj T₀ T₀ _ = refl
h1-inj T₁ T₁ _ = refl
h1-inj T₂ T₂ _ = refl
h1-inj T₀ T₁ ()
h1-inj T₀ T₂ ()
h1-inj T₁ T₀ ()
h1-inj T₁ T₂ ()
h1-inj T₂ T₀ ()
h1-inj T₂ T₁ ()

h1-surj : (c : H1c) → Σ Trit (λ k → proj₁ (h1 k) ≡ proj₁ c)
h1-surj (v , p) with ker-span v p
... | k , q = k , Relation.Binary.PropositionalEquality.sym q

-- H₁(graph3) ≅ Trit：生成（surj）+ 唯一（inj）—— 商对象 B₁=0 的三类显形
-- 维数核对：nullity∂₁ − rank∂₂ = 1 − 0 = 1 ⇒ |H₁| = 3 = |Trit| ✓（与 §2/§3 记录数字一致）
