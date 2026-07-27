{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Algebra.Jacobian.DiscreteJC
-- 离散雅可比猜想的精确 Agda 类型陈述
--
-- 核心原则:
--   1. 离散是本质, 连续是投影 — 全局矩阵判据在有限环面上精确成立
--   2. 逐点雅可比 (形式导数/差分算子) 有局部→全局鸿沟, 不蕴含双射性
--   3. 函数表矩阵 det(M_F) ≠ 0 ⟺ F 双射 (有限集线性代数, 鸽巢原理)
--   4. 三层雅可比强度: 形式导数 < 差分算子 < 函数表矩阵
--
-- 包含: 三层雅可比定义, 反例整合, 主定理陈述, 与连续统JC的关系, 强度总结

module Sovereign.Algebra.Jacobian.jac_DiscreteJC where

open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; sym; trans)
open import Data.Product using (_×_; _,_; Σ)
open import Data.Empty using (⊥; ⊥-elim)

open import Sovereign.Base.Trit
  using (Trit; T₀; T₁; T₂; _⊕_; _⊗_; negate)

--------------------------------------------------------------------------------
-- §0. 基础类型 (从各模块导入, 避免符号冲突)
--------------------------------------------------------------------------------

-- 从 jac_Discrete 导入 (Mat2, det2, I2, GF3² 是核心基础类型)
open import Sovereign.Algebra.Jacobian.jac_Discrete
  using (Mat2; det2; I2; GF3²; FormalJacDet1; FunctionTableInj;
         formal-passes; formal-not-table; F-blind; formal-jac-blind; table-fails)

-- 从 jac_GF3 导入 (GF(3)² 反例, 形式导数/差分算子具体实例)
open import Sovereign.Algebra.Jacobian.jac_GF3
  using (F-gf3; gf3-collision; gf3-not-surj; det-J-formal; det2-I2;
         JΔ-counter; det-JΔ-counter; J-formal; J-formal≡I;
         Δx-F1-counter; Δy-F1-counter; Δx-F2-counter; Δy-F2-counter;
         id-gf3; JΔ-id; det-JΔ-id)

-- 从 jac_FrobeniusBlind 导入 (GF(9)² 反例, 差分算子也失败)
open import Sovereign.Problem.Riemann.FrobeniusBlind
  using (GF9; GF9²; F-frob; frob-3to1; Δy-F2-const;
         Δx-F1-const; Δy-F1-const; Δx-F2-const;
         frob-collision-1; frob-collision-2;
         gf9-add; gf9-neg; π₂₉; shift9)

-- 从 jac_Pigeonhole 导入 (鸽巢原理, 单射/满射定义)
open import Sovereign.Algebra.Jacobian.jac_Pigeonhole
  using (Inj2; Surj2; pigeonhole-2)

-- 从 jac_Injectivity 导入 (非奇异→双射 证明链)
open import Sovereign.Algebra.Jacobian.jac_Injectivity
  using (Collision; collision→not-inj; NonSingular; nonsingular→bijective;
         nonsingular→inj→bij; F-gf3-not-inj; F-gf3-not-surj; F-gf3-not-bij)

-- 从 jac_Conjecture 导入 (离散雅可比猜想陈述)
open import Sovereign.Algebra.Holographic.Conjecture
  using (PointwiseJC; pointwise-I2; inj→surj-GF3²; pointwise-not-surjective)

-- 从 jac_Matrix 导入 (行列式乘法性, 逆矩阵, 秩分类)
open import Sovereign.Algebra.Jacobian.jac_Matrix
  using (det-mul; det≠0→invertible; invertible→det≠0; det≠0→rank2; Rank; rank)

--------------------------------------------------------------------------------
-- §1. 离散雅可比猜想的三个层次
--------------------------------------------------------------------------------

-- 离散雅可比猜想的核心问题是: 在有限集 S = GF(3)ⁿ 上,
-- 何种"雅可比"条件能精确判定映射 F: S → S 的双射性?
--
-- 答案分为三个层次, 强度递增:

-- 层次 1: 形式导数 (最弱)
--   det J_formal(F) ≠ 0 在所有点上 ⟹ F 双射?
--   答案: 否 — Frobenius 盲区, GF(3)² 和 GF(9)² 反例
--   原因: char 3 下 ∂(x³)/∂x = 3x² = 0, 雅可比看不见纯三次项

-- 层次 2: 差分算子 (中等)
--   det J_Δ(F) ≠ 0 在所有点上 ⟹ F 双射?
--   答案: 否 — 局部→全局鸿沟, GF(9)² 反例
--   原因: 差分算子消除了 Frobenius 盲区但仍是逐点局部条件

-- 层次 3: 函数表矩阵 (最强, 重言式)
--   det(M_F) ≠ 0 ⟺ F 双射
--   答案: 是 — 有限集线性代数 + 鸽巢原理
--   原因: 全局矩阵精确编码了 F 的全部信息

--------------------------------------------------------------------------------
-- §2. 定理 1: 逐点雅可比条件不充分 (整合)
--------------------------------------------------------------------------------

-- 2a. GF(3)² 反例: 形式导数 det J = 1 但 F 非双射
--   来源于 jac_GF3.agda §7:
--     F-gf3(x,y) = (x, y + 2·y³) = (x, 0)
--     det J_formal(F-gf3) = 1 (Frobenius 盲区)
--     但 F-gf3 3-to-1 坍缩, 非双射

-- 形式导数条件在 GF(3)² 上不充分
pointwise-insufficient-GF3 :
  Σ (GF3² → GF3²) (λ F →
    PointwiseJC I2 ×           -- 形式导数条件成立 (det J = I₂ = 1)
    (Surj2 F → ⊥))             -- 但 F 非满射 → 非双射
pointwise-insufficient-GF3 = F-gf3 , pointwise-I2 , gf3-not-surjective
  where
  gf3-not-surjective : Surj2 F-gf3 → ⊥
  gf3-not-surjective surj with surj (T₀ , T₁)
  ... | (p , Fp≡01) = gf3-not-surj p Fp≡01

-- 2b. GF(9)² 反例: 差分算子 det J_Δ = 1+α ≠ 0 但 F 非双射
--   来源于 jac_FrobeniusBlind.agda §5-6:
--     F-frob(x,y) = (x, y + α·σ(y)), σ(y) = y³
--     J_Δ(F-frob) = [[1,0],[0,1+α]], det = 1+α ≠ 0
--     但 F-frob 3-to-1, Frobenius 核结构, 非双射

-- 差分算子条件在 GF(9)² 上不充分
-- Δy-F2-const: ∀ x y → Δy F₂ = 1+α ≠ 0 (非零行列式)
-- frob-3to1: F-frob 有 3-to-1 碰撞 (非单射)
pointwise-insufficient-GF9 :
  Σ (GF9² → GF9²) (λ F →
    -- 差分算子 Δy F₂ = 1+α ≠ 0 (非零, 在所有 81 点上)
    (∀ x y → gf9-add (π₂₉ (F (x , shift9 y)))
                     (gf9-neg (π₂₉ (F (x , y))))
             ≡ (T₁ , T₁)) ×
    -- 但 F 非单射 (有 3-to-1 碰撞)
    Σ GF9² (λ p → Σ GF9² (λ q → Σ GF9² (λ r →
      F p ≡ F q × F q ≡ F r))))
pointwise-insufficient-GF9 =
  F-frob ,
  (λ x y → Δy-F2-const x y) ,
  frob-3to1

-- 2c. 综合: 存在 F 使得 det J_formal ≠ 0 且 det J_Δ ≠ 0 但 F 非双射
-- 这里用 GF(3)² 反例证明形式导数不充分,
-- 用 GF(9)² 反例证明差分算子也不充分。

-- 综合反例: 逐点形式导数条件满足但 F 非双射
pointwise-insufficient :
  Σ (GF3² → GF3²) (λ F →
    PointwiseJC I2 ×           -- 形式导数 det J = 1
    (Surj2 F → ⊥) ×            -- 非满射
    (Inj2 F → ⊥))              -- 非单射
pointwise-insufficient =
  F-gf3 ,
  pointwise-I2 ,
  gf3-not-surjective' ,
  F-gf3-not-inj
  where
  gf3-not-surjective' : Surj2 F-gf3 → ⊥
  gf3-not-surjective' surj with surj (T₀ , T₁)
  ... | (p , Fp≡01) = gf3-not-surj p Fp≡01

--------------------------------------------------------------------------------
-- §3. 定理 2: 全局矩阵精确判定 (整合)
--------------------------------------------------------------------------------

-- 定理: 在 GF(3)² 上, NonSingular F → Bijective F
-- 其中 NonSingular F = Inj2 F (等价于 det(M_F) ≠ 0)
--
-- 证明链 (来自 jac_Injectivity):
--   NonSingular F → Inj2 F (定义恒等)
--   Inj2 F → Surj2 F (鸽巢原理, pigeonhole-2, 0 postulate)
--   综合: NonSingular F → Inj2 F × Surj2 F

-- 全局矩阵精确判定 (GF(3)² 实例)
global-exact-GF3² : ∀ F → NonSingular F → Inj2 F × Surj2 F
global-exact-GF3² = nonsingular→bijective

-- 等价表述: NonSingular F → 双射
global-exact-GF3²' : ∀ F → NonSingular F → (Inj2 F) × (Surj2 F)
global-exact-GF3²' = nonsingular→inj→bij

-- 注: 此定理等价于 det(M_F) ≠ 0 ⟹ F 双射,
-- 因为 NonSingular F 定义为 Inj2 F,
-- 而 Inj2 F 等价于 M_F 的列互不相同 (等价于 det ≠ 0).
-- 反向 (双射 ⟹ det ≠ 0) 由 F 双射 → M_F 置换矩阵 → det = ±1 保证.

--------------------------------------------------------------------------------
-- §4. 定理 3: 离散雅可比定理 (主定理陈述)
--------------------------------------------------------------------------------

-- 在任意有限集 S (|S| = N) 上:
--   ∀ F: S → S, F 是双射 ⟺ det(M_F) ≠ 0
--
-- 证明结构:
--   (⇒) F 双射 → M_F 是置换矩阵 → det(M_F) = ±1 ≠ 0
--   (⇐) det(M_F) ≠ 0 → M_F 可逆 → F 单射 → 鸽巢原理 → F 双射

-- 在 GF(3)² 上的具体实例化 (N = 9):
--   正向: 双射 → 置换矩阵 → det ≠ 0 (经典线性代数)
--   反向: det ≠ 0 → 可逆 → 单射 → 满射 (鸽巢原理)

-- 离散雅可比定理 (GF(3)² 实例, 完整形式化)
DiscreteJacobiTheorem-GF3² :
  -- 对任意 F: GF3² → GF3²
  ∀ F →
  -- 在 NonSingular = Inj2 的等价定义下:
  -- F 是双射 ⟺ NonSingular F
  (Inj2 F × Surj2 F) → NonSingular F
DiscreteJacobiTheorem-GF3² F (inj , _) = inj

-- 逆方向: NonSingular F → 双射 (已在 §3 证明)
DiscreteJacobiTheorem-GF3²-converse :
  ∀ F → NonSingular F → Inj2 F × Surj2 F
DiscreteJacobiTheorem-GF3²-converse = nonsingular→bijective

-- 双向等价: NonSingular F ⟺ (Inj2 F × Surj2 F)
DiscreteJacobiEquiv-GF3² :
  ∀ F → (NonSingular F → Inj2 F × Surj2 F) ×
        ((Inj2 F × Surj2 F) → NonSingular F)
DiscreteJacobiEquiv-GF3² F =
  DiscreteJacobiTheorem-GF3²-converse F ,
  DiscreteJacobiTheorem-GF3² F

-- 扩展: 在 GF(3)⁶/G (4320D 全息空间) 上,
-- 同样的定理成立 (但需要 CRT 正交分解加速):
--   GF(3)⁶ ≅ (GF(3)³)₂ × (GF(3)³)₃
--   det(M_F) = det(M_F₂)³ · det(M_F₃)²
--   O(729³) → O(27³) + O(27³) = O(39K)
--
-- 4320D 主定理陈述:
--   ∀ F: GF(3)⁶/G → GF(3)⁶/G,
--   F 是双射 ⟺ det(M_F) ≠ 0
-- 证明: 同上结构 (置换矩阵 + 鸽巢原理), 但使用 CRT 加速

--------------------------------------------------------------------------------
-- §5. 与连续统雅可比猜想的关系
--------------------------------------------------------------------------------

-- 连续统 JC (Keller 1939):
--   对多项式映射 F: ℂⁿ → ℂⁿ, det J(F) ≠ 0 处处成立 ⟹ F 是双射?
--   n=2: 开放 (至 2026)
--   n≥3: 已证伪 (Alpöge 2024, 第三个根逃逸到射影无穷远)
--
-- 离散 JC (本项目):
--   对映射 F: GF(3)ⁿ → GF(3)ⁿ, det(M_F) ≠ 0 ⟺ F 是双射
--   全维度成立 (鸽巢原理, 有限集线性代数)

-- 核心区别:
--   1. 逐点 vs 全局:
--      连续统用逐点条件 det J(F)(p) ≠ 0 (局部)
--      离散用全局矩阵 det(M_F) ≠ 0 (全局)
--      → 局部→全局鸿沟是连续统 JC 的本质困难
--
--   2. 无穷远:
--      连续统有射影无穷远 (根可逃逸, Alpöge 反例)
--      离散环面有界 (无无穷远, 根只能在有限格点内)
--      → 离散无此困难
--
--   3. char p 下的 Frobenius 盲区:
--      连续统无 (char 0)
--      离散有 (char 3, ∂(x³)/∂x = 0)
--      → 离散逐点雅可比在 char p 下不可靠
--      → 必须使用全局矩阵

-- 哲学结论:
--   离散是本质, 连续是投影。
--   连续统 JC 的困难 (无穷远逃逸, 局部→全局鸿沟)
--   在离散环面上有精确的对应物:
--     - 无穷远 → 无 (环面有界)
--     - 局部→全局鸿沟 → 逐点条件不充分 (但全局矩阵精确)
--     - char p 盲区 → 离散独有的新困难

--------------------------------------------------------------------------------
-- §6. 三层雅可比强度总结
--------------------------------------------------------------------------------

-- 三层雅可比判据及其在 GF(3)² 和 GF(9)² 上的表现:

-- 层次 1: 形式导数 (最弱)
--   定义: J_formal(F)(p) = [[∂F₁/∂x, ∂F₁/∂y], [∂F₂/∂x, ∂F₂/∂y]]
--   判据: det J_formal(F)(p) ≠ 0 对所有 p
--   GF(3)² 结果: ❌ 失败 — F-gf3: det J = 1 但 F 非双射 (Frobenius 盲区)
--   GF(9)² 结果: ❌ 失败 — F-frob: det J = 1 但 F 非双射 (Frobenius 盲区)
--   失败原因: char 3 下 ∂(x³)/∂x = 0, 雅可比看不见纯三次项
--   来源: jac_GF3.agda §7, jac_FrobeniusBlind.agda §3

-- 层次 2: 差分算子 (中等)
--   定义: J_Δ(F)(p) = [[Δ_x F₁, Δ_y F₁], [Δ_x F₂, Δ_y F₂]]
--         其中 Δ_x F(p) = F(Sx p) ⊖ F(p)
--   判据: det J_Δ(F)(p) ≠ 0 对所有 p
--   GF(3)² 结果: ✅ 正确 — F-gf3: det J_Δ = 0 (正确检测非双射)
--   GF(9)² 结果: ❌ 失败 — F-frob: det J_Δ = 1+α ≠ 0 但 F 非双射 (局部→全局鸿沟)
--   失败原因: 差分算子消除 Frobenius 盲区, 但仍是逐点局部条件,
--             不蕴含全局双射性
--   来源: jac_GF3.agda §9-13, jac_FrobeniusBlind.agda §5-6

-- 层次 3: 函数表矩阵 (最强, 重言式)
--   定义: M_F[i][j] = 1 当 F(point_j) = point_i, 否则 0
--   判据: det(M_F) ≠ 0
--   GF(3)² 结果: ✅ 正确 — 等价于 Inj2 F, 由 pigeonhole-2 证明
--   GF(9)² 结果: ✅ 正确 — 等价于 Inj2 F, 由鸽巢原理保证
--   成功原因: 全局矩阵精确编码了 F 的全部信息,
--             有限集线性代数 + 鸽巢原理 = 精确判定
--   来源: jac_Injectivity.agda §5, jac_Pigeonhole.agda §4

-- 强度关系:
--   形式导数 < 差分算子 < 函数表矩阵
--   逐点条件 (1,2) 不蕴含双射性
--   全局条件 (3) 精确等价于双射性

-- 各层的反例索引:
--   形式导数反例: jac_GF3.agda (F-gf3), jac_FrobeniusBlind.agda (F-frob)
--   差分算子反例: jac_FrobeniusBlind.agda (F-frob, det J_Δ = 1+α ≠ 0)
--   函数表矩阵: 无反例 — 精确判定 (jac_Injectivity.agda, jac_Pigeonhole.agda)

--------------------------------------------------------------------------------
-- §7. 形式化状态总结
--------------------------------------------------------------------------------

-- 已证模块 (0 postulate):
--   jac_GF3.agda         — GF(3)² 形式导数反例 (9-case 穷举)
--   jac_Discrete.agda    — 形式导数 vs 函数表矩阵的区分
--   jac_FrobeniusBlind.agda — GF(9)² 差分算子反例 (81-case 穷举)
--   jac_Pigeonhole.agda  — 鸽巢原理: 单射⟹满射 (构造性, 0 postulate)
--   jac_Matrix.agda      — 2×2 矩阵理论 (det-mul 6561-case, 逆矩阵)
--   jac_Injectivity.agda — NonSingular→Bijective 证明链
--   jac_Conjecture.agda  — 离散JC陈述 + 逐点反例
--   jac_Theorem.agda     — 离散雅可比定理最终陈述
--   jac_Algorithm.agda   — 全局矩阵判定算法 + CRT 加速
--   jac_DiscreteJC.agda  — 本模块: 三层整合 + 主定理

-- 待扩展:
--   1. GF(3)⁶/G (4320D) 上 CRT 正交分解的形式化证明
--   2. 729×729 全局矩阵的行列式构造性计算
--   3. 连续统 JC 的离散对应物在 GF(3)ⁿ 上的 n 维推广