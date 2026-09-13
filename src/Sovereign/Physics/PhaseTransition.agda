{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Physics.PhaseTransition
-- 相变 = 范数边界穿越
--
-- 核心映射:
--   固态→液态: N=2→N=1 (范数减小)
--   液态→气态: N=1→N=2 (范数增大)
--   超导相变: N=1→N=0 (范数坍缩到零态)
--
-- 诚实边界:
--   临界温度的具体数值是实验输入, 非框架推导
--   -45℃ 作为水的特征温度已被实验确认, 但第二临界点确切位置仍有争议
--
-- 0 postulate.

module Sovereign.Physics.PhaseTransition where

open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _%_; _∸_)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; sym; trans)

open import Sovereign.Base.Trit using (Trit; T₀; T₁; T₂; _⊕_; _⊗_)
open import Sovereign.Algebra.GF9
  using ( GF9; gf9-one; gf9-zero; alpha
        ; galoisNorm
        ; gf9-pow; zero-power-gf9
        )
open import Sovereign.Base.Invariants using (POLAR_WINDING; TOROIDAL_WINDING)

--------------------------------------------------------------------------------
-- §1. 相变类型
--------------------------------------------------------------------------------

-- 相变 = 范数状态之间的跃迁
data PhaseTransition : Set where
  solid-to-liquid  : PhaseTransition  -- N=2→N=1 (固态→液态)
  liquid-to-gas    : PhaseTransition  -- N=1→N=2 (液态→气态)
  superconducting  : PhaseTransition  -- N=1→N=0 (进入超导态)
  confined         : PhaseTransition  -- N=1→N=2 (进入受限态)

--------------------------------------------------------------------------------
-- §2. 水的相变温度 (实验锚点)
--------------------------------------------------------------------------------

-- 均质形核温度 TH = 232K (-41℃) — 已确认
homogeneous-nucleation-temp : ℕ
homogeneous-nucleation-temp = 232

-- 第二临界点温度区间 (实验数据, 非精确值)
-- 主流实验: 190K ~ 240K
-- 语料锚: -45℃ / 228K (热力学响应函数发散)
second-critical-temp-low : ℕ
second-critical-temp-low = 190

second-critical-temp-high : ℕ
second-critical-temp-high = 240

-- 诚实声明 (基于 Nature 2014 等实验数据):
--   228K / -45℃ 是热力学响应函数发散的特征温度
--   不是"第二临界点"本身 (临界点位置仍有争议: 168K~228K)
--   是 Widom 线经过的位置
--   实验方法: LCLS 飞秒 X 射线激光脉冲探测亚稳态液态水 (Sellberg et al. 2014)
--   2020 EOS 预测: T_C' = 228.3K, p_C' = 0.954 kbar, ρ_C' = 1.045 g/cm³
--
-- 与框架常量的关系 (数值拟合, 非理论推导):
--   FULL_TOUR / 29 = 228.41 ≈ 228.3K (误差 0.11K)
--   228 / TOROIDAL_WINDING(46) ≈ 5 (误差 2K)
--   这些是后验数值关系, 不是先验推导

--------------------------------------------------------------------------------
-- §3. 范数边界 = 相变点
--------------------------------------------------------------------------------

-- 固态: N=2 (最大偏离态)
solid-norm : galoisNorm (T₁ , T₁) ≡ T₂
solid-norm = refl

-- 液态: N=1 (非零单位态)
liquid-norm : galoisNorm alpha ≡ T₁
liquid-norm = refl

-- 超导态: N=0 (零态)
superconducting-norm : galoisNorm gf9-zero ≡ T₀
superconducting-norm = refl

-- 相变 = 范数跃迁 (离散, 确定性)
-- 不是连续变化, 是离散跃迁

--------------------------------------------------------------------------------
-- §4. FULL_TOUR 与临界温度的关系
--------------------------------------------------------------------------------

-- FULL_TOUR = 6624 = 144 × 46
-- 诚实声明: 6624 与 228K 的关系是数值拟合, 非理论推导
-- 但可以展示: 6624 / 29.03 ≈ 228.15

-- 框架能做的:
--   将 -45℃ 作为物理锚点记录
--   展示它与 FULL_TOUR 的数值关系
--   定位为 N=1→N=2 范数边界的实验锚点

-- 框架不能做的:
--   从 GF(9) 推导出 -45℃ 这个具体数值
--   证明 228.15K 是唯一可能的临界温度

-- 0 postulate.
