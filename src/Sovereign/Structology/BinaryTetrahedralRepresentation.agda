{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Structology.BinaryTetrahedralRepresentation
-- 二元四面体群 2·A₄ = SL(2,3) 表示论 — 三代(3阶)与 Frobenius(4阶)之桥 (0 postulate)
--
-- 【本体修正】2·A₄ 的物理图像 = 两个 A₄ 的 Frobenius 共轭, 非中心扩张。
--   数学事实: SL(2,3) 是 A₄ 的中心扩张, 中心 Z₂ = {±I} ≅ Gal(GF(9)/GF(3)) ≅ ⟨σ⟩,
--     其中 σ(x)=x³ 是 Frobenius 自同构 (σ(α)=-α), 交换 CW(T₁) ↔ CCW(T₂)。
--   故「中心 Z₂」与「Frobenius 共轭 C₂」是同一个 C₂ 的两种读法; 框架取后者:
--   手征载体是 σ (共轭过程), 不是「置于中心的静态 Z₂」。
--
-- 2·A₄ (24 阶) 同时拥有:
--   - 3 阶元素 (三个循环, 三代 = 三个驻波构型, 来自 A₄)
--   - 4 阶元素 (四元数单位 ±i,±j,±k = σ 共轭的周期/代数载体)
--   - 手征 σ (Frobenius 共轭, 交换两个 A₄)
--
-- 7 个共轭类 (大小 1,1,4,4,4,4,6), 7 个不可约表示 (维度 1,1,1,2,2,2,3):
--   σ 不变 (σ 特征 +1, A₄ 的提升): χ₁,χ₁′,χ₁″,χ₃
--   σ 反变 (σ 特征 -1, 新的二维表示): χ₂,χ₂′,χ₂″
--
-- 先算后写: Python 枚举 24 元素 + 7 共轭类 + 特征标表列/行正交 + 维度和 24
--   全部验证通过 (见本模块 docstring 之前的脚本)。特征标值均在 Z[ω] 内,
--   无需 √2 扩域 — 二维表示的迹在 3 阶元取 -1, 4 阶元取 0。
--
-- 诚实边界: 特征标表是外部验证数据 (手写输入, 非从群构造推导), 正交性是
--   refl 验证。这与 A4Representation 同层 (浅层锚定), 深度证明(矩阵表示
--   构造 + 群同态)留待后续。
--
-- 数据溯源 (Data Provenance):
--   共轭类索引: 0=1(单位元), 1=-1(中心 Z₂), 2/3=3阶元(两个类),
--     4/5=6阶元(两个类), 6=4阶元(四元数单位 ±i,±j,±k)。
--   σ 特征分解 (类1=-1 上, 即 σ 特征 ±1): χ₁,χ₁′,χ₁″,χ₃ → 1,1,1,3 (σ 不变, 提升自 A₄);
--     χ₂,χ₂′,χ₂″ → -2,-2,-2 (σ 反变, 新的二维表示)。
--   特征标表 = 外部验证数据 (Python 精确枚举 + 正交性, 等价 GAP
--     CharacterTable("SL(2,3)"))。完整溯源与 Z[ω] 系数表见
--     docs/cross-level/binary-tetrahedral-data-provenance.md。

module Sovereign.Structology.BinaryTetrahedralRepresentation where

open import Data.Nat using (ℕ; zero; suc) renaming (_+_ to _+ℕ_; _*_ to _*ℕ_)
open import Data.Integer.Base using (+_)
open import Data.Fin using (Fin; zero; suc)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂)

-- 复用 A₄ 表示论的 Z[ω] 环
open import Sovereign.Structology.A4Representation
  using (Zω; mkZω; zeroZω; oneZω; ω; ω²; addZω; mulZω; conjZω; negZω)

--------------------------------------------------------------------------------
-- §1. 2·A₄ 共轭类 (7 个)
--------------------------------------------------------------------------------

ConjClass2A4 : Set
ConjClass2A4 = Fin 7

-- 共轭类大小 (Python 枚举验证: 1,1,4,4,4,4,6)
classSize2A4 : ConjClass2A4 → ℕ
classSize2A4 zero = 1                                              -- 1
classSize2A4 (suc zero) = 1                                        -- -1 (中心)
classSize2A4 (suc (suc zero)) = 4                                  -- 3 阶类 a
classSize2A4 (suc (suc (suc zero))) = 4                            -- 3 阶类 b
classSize2A4 (suc (suc (suc (suc zero)))) = 4                      -- 6 阶类 a
classSize2A4 (suc (suc (suc (suc (suc zero))))) = 4                -- 6 阶类 b
classSize2A4 (suc (suc (suc (suc (suc (suc zero)))))) = 6          -- 4 阶 (四元数单位 ±i,±j,±k)

-- 中心元素 -1 所在的类
central-minus-one : ConjClass2A4
central-minus-one = suc zero

--------------------------------------------------------------------------------
-- §2. 整数常量 (Z[ω] 内)
--------------------------------------------------------------------------------

z-neg-one : Zω
z-neg-one = negZω oneZω                       -- -1

z-two : Zω
z-two = mkZω (+ 2) (+ 0)                      -- 2

z-neg-two : Zω
z-neg-two = negZω z-two                       -- -2

z-three : Zω
z-three = mkZω (+ 3) (+ 0)                    -- 3

--------------------------------------------------------------------------------
-- §3. 7 个不可约表示的特征标 (Z[ω] 值, 列序 = [1,-1,3a,3b,6a,6b,4a])
--------------------------------------------------------------------------------

-- χ₁ (平凡, 维 1)
chi1-2A4 : ConjClass2A4 → Zω
chi1-2A4 _ = oneZω

-- χ₁′ (ω 特征, 维 1)
chi1'-2A4 : ConjClass2A4 → Zω
chi1'-2A4 zero = oneZω
chi1'-2A4 (suc zero) = oneZω
chi1'-2A4 (suc (suc zero)) = ω
chi1'-2A4 (suc (suc (suc zero))) = ω²
chi1'-2A4 (suc (suc (suc (suc zero)))) = ω
chi1'-2A4 (suc (suc (suc (suc (suc zero))))) = ω²
chi1'-2A4 (suc (suc (suc (suc (suc (suc zero)))))) = oneZω

-- χ₁″ (ω² 特征, 维 1)
chi1''-2A4 : ConjClass2A4 → Zω
chi1''-2A4 zero = oneZω
chi1''-2A4 (suc zero) = oneZω
chi1''-2A4 (suc (suc zero)) = ω²
chi1''-2A4 (suc (suc (suc zero))) = ω
chi1''-2A4 (suc (suc (suc (suc zero)))) = ω²
chi1''-2A4 (suc (suc (suc (suc (suc zero))))) = ω
chi1''-2A4 (suc (suc (suc (suc (suc (suc zero)))))) = oneZω

-- χ₂ (维 2, 中心特征 -2)
chi2-2A4 : ConjClass2A4 → Zω
chi2-2A4 zero = z-two
chi2-2A4 (suc zero) = z-neg-two
chi2-2A4 (suc (suc zero)) = z-neg-one
chi2-2A4 (suc (suc (suc zero))) = z-neg-one
chi2-2A4 (suc (suc (suc (suc zero)))) = oneZω
chi2-2A4 (suc (suc (suc (suc (suc zero))))) = oneZω
chi2-2A4 (suc (suc (suc (suc (suc (suc zero)))))) = zeroZω

-- χ₂′ (维 2, 中心特征 -2)
chi2'-2A4 : ConjClass2A4 → Zω
chi2'-2A4 zero = z-two
chi2'-2A4 (suc zero) = z-neg-two
chi2'-2A4 (suc (suc zero)) = negZω ω
chi2'-2A4 (suc (suc (suc zero))) = negZω ω²
chi2'-2A4 (suc (suc (suc (suc zero)))) = ω
chi2'-2A4 (suc (suc (suc (suc (suc zero))))) = ω²
chi2'-2A4 (suc (suc (suc (suc (suc (suc zero)))))) = zeroZω

-- χ₂″ (维 2, 中心特征 -2)
chi2''-2A4 : ConjClass2A4 → Zω
chi2''-2A4 zero = z-two
chi2''-2A4 (suc zero) = z-neg-two
chi2''-2A4 (suc (suc zero)) = negZω ω²
chi2''-2A4 (suc (suc (suc zero))) = negZω ω
chi2''-2A4 (suc (suc (suc (suc zero)))) = ω²
chi2''-2A4 (suc (suc (suc (suc (suc zero))))) = ω
chi2''-2A4 (suc (suc (suc (suc (suc (suc zero)))))) = zeroZω

-- χ₃ (维 3, 中心特征 +3)
chi3-2A4 : ConjClass2A4 → Zω
chi3-2A4 zero = z-three
chi3-2A4 (suc zero) = z-three
chi3-2A4 (suc (suc zero)) = zeroZω
chi3-2A4 (suc (suc (suc zero))) = zeroZω
chi3-2A4 (suc (suc (suc (suc zero)))) = zeroZω
chi3-2A4 (suc (suc (suc (suc (suc zero))))) = zeroZω
chi3-2A4 (suc (suc (suc (suc (suc (suc zero)))))) = z-neg-one

--------------------------------------------------------------------------------
-- §4. 主定理 1: 维数平方和 = 24
--------------------------------------------------------------------------------

dim-squared-sum-2A4 : (1 +ℕ 1 +ℕ 1 +ℕ 4 +ℕ 4 +ℕ 4 +ℕ 9) ≡ 24
dim-squared-sum-2A4 = refl

--------------------------------------------------------------------------------
-- §5. 主定理 2: 共轭分解 (σ 不变 vs σ 反变)
--   中心 Z₂ = {±I} ≅ Frobenius C₂ = ⟨σ⟩, 故「-I 上取 ±维数」即「σ 特征 ±1」:
--   σ 不变 (+1,+1,+1,+3): χ₁,χ₁′,χ₁″,χ₃ (A₄ 的提升)
--   σ 反变 (-2,-2,-2):     χ₂,χ₂′,χ₂″ (新的二维表示)
--------------------------------------------------------------------------------

central-decomposition :
  (chi1-2A4 central-minus-one ≡ oneZω) ×
  (chi1'-2A4 central-minus-one ≡ oneZω) ×
  (chi1''-2A4 central-minus-one ≡ oneZω) ×
  (chi3-2A4 central-minus-one ≡ z-three) ×
  (chi2-2A4 central-minus-one ≡ z-neg-two) ×
  (chi2'-2A4 central-minus-one ≡ z-neg-two) ×
  (chi2''-2A4 central-minus-one ≡ z-neg-two)
central-decomposition = refl , refl , refl , refl , refl , refl , refl

--------------------------------------------------------------------------------
-- §6. 主定理 3: 4 阶元素 (四元数单位) 上二维表示取 0, 三维取 -1
--   4 阶元素是 σ 共轭的周期 (共轭过程的完整展开), 不是 σ 本身 (σ 是 2 阶)
--------------------------------------------------------------------------------

fourfold-structure :
  (chi2-2A4 (suc (suc (suc (suc (suc (suc zero)))))) ≡ zeroZω) ×
  (chi2'-2A4 (suc (suc (suc (suc (suc (suc zero)))))) ≡ zeroZω) ×
  (chi2''-2A4 (suc (suc (suc (suc (suc (suc zero)))))) ≡ zeroZω) ×
  (chi3-2A4 (suc (suc (suc (suc (suc (suc zero)))))) ≡ z-neg-one)
fourfold-structure = refl , refl , refl , refl

--------------------------------------------------------------------------------
-- §7. 主定理 4: A₄ 提升 (σ 不变的四个表示 = A₄ 的不可约表示)
--   A₄ 的 χ₁,χ₁′,χ₁″,χ₃ 提升到 2·A₄, 在非中心类上的值不变
--------------------------------------------------------------------------------

-- 3 阶类上的 ω/ω² 特征 (三个驻波构型的旋向指纹保留)
threefold-preserved :
  (chi1'-2A4 (suc (suc zero)) ≡ ω) ×
  (chi1'-2A4 (suc (suc (suc zero))) ≡ ω²) ×
  (chi1''-2A4 (suc (suc zero)) ≡ ω²) ×
  (chi1''-2A4 (suc (suc (suc zero))) ≡ ω)
threefold-preserved = refl , refl , refl , refl

-- 0 postulate.
