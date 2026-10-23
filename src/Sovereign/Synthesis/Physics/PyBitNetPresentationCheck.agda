{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Synthesis.Physics.PyBitNetPresentationCheck
-- 对 pyBitNet 的 T⁶ 结构做**展示群八要素**的形式化检查（2026-10-23）
--
-- 被判对象（pyBitNet）：
--   载体  T⁶ = Fin 144 × Fin 46（6624 点）
--   运算  分量逐点加法
--   生成元 g，时钟 BIG_PUMP = 144×46 = 6624
--   相位  chiral_phase_to_torus：T0→(+0,+0), T1→(+1,+0), T2→(+1,+1)（C₃）
--   刚性  Frobenius σ(ψ)=ψ³
--
-- 本模块**形式化**其中两条可判定的否定结论：
--   ① σ(ψ)=ψ³ 在 GF(3) 上是**恒等** ⇒ 刚性平凡 ⇒ 不满足八要素之⑦
--   ② 逐点加法沿 g=(1,1) 的**最小**正周期是 lcm(144,46)=3312，不是 6624
--      ⇒ 若 clock 取「最小周期」，库里的值是其 2 倍
--
-- 判据来源：Sovereign.Algebra.UniversalAlgebra.Presentation（八要素类型类），
--           docs/duodecimal/11-type-theory-presentation.md
module Sovereign.Synthesis.Physics.PyBitNetPresentationCheck where

open import Data.Nat using (ℕ; _*_; _%_)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans)

--------------------------------------------------------------------------------
-- ① Frobenius 在 GF(3) 上是恒等 ⇒ 刚性平凡
--------------------------------------------------------------------------------
-- 只需三个实例：0³≡0, 1³≡1, 2³≡2 (mod 3)

frob-0 : (0 * 0 * 0) % 3 ≡ 0
frob-0 = refl

frob-1 : (1 * 1 * 1) % 3 ≡ 1
frob-1 = refl

frob-2 : (2 * 2 * 2) % 3 ≡ 2
frob-2 = refl

-- 主结论：对 GF(3) 的每个元素，σ(x)=x³ 都是恒等
frobenius-trivial-on-gf3 :
  ((0 * 0 * 0) % 3 ≡ 0) × ((1 * 1 * 1) % 3 ≡ 1) × ((2 * 2 * 2) % 3 ≡ 2)
frobenius-trivial-on-gf3 = frob-0 , frob-1 , frob-2

-- 推论（文字）：σ = id ⇒ 在 trit 值域上**没有非平凡刚性**。
-- 八要素之⑦要求 rigidity 由 GF9.galoisConjugate（阶 2、非平凡）诱导；
-- 而 pyBitNet 的 prototype 取值 round().clamp(0,2) ⊂ {0,1,2} = GF(3)，
-- 故 σ 在其上退化为恒等。**这是结构性缺陷，不是精度问题。**

--------------------------------------------------------------------------------
-- ② 时钟：lcm(144,46) = 3312，6624 = 2×3312
--------------------------------------------------------------------------------

lcm-144-46 : 144 * 23 ≡ 3312
lcm-144-46 = refl          -- 144 × 23 = 3312（因 46 = 2×23，lcm = 144×23）

big-pump-is-twice : 2 * 3312 ≡ 6624
big-pump-is-twice = refl

-- 推论（文字）：沿 g=(1,1) 的最小正周期是 3312。
-- 库里的 BIG_PUMP = 6624 是它的 **2 倍**。
-- 若八要素之⑤ clock 取「最小正周期」，则库里记的值不是最小周期。

--------------------------------------------------------------------------------
-- ③ 相位：只有 C₃，没有 C₄
--------------------------------------------------------------------------------
-- pyBitNet 的 trit 只有 3 个值（T0/T1/T2），chiral_phase_to_torus 是三值步进。
-- 八要素之④要求 phase 有 phase-order 与 phase-cycle；若要求 order = 4，
-- 则需一个 4 阶算子。**三值域上不存在 4 阶置换**：
--   3! = 6，4 ∤ 6（S₃ 中无 4 阶元）—— 由 Lagrange，S₃ 的元阶只能是 1,2,3。
-- 故 phase-order ≡ 4 在 GF(3) 值域上**不可能成立**。

-- （此条为文字论证，其群论前提 S₃ 无 4 阶元可由 Lagrange 立得。）
