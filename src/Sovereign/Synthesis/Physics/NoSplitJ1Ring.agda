{-# OPTIONS --rewriting --guardedness #-}

------------------------------------------------------------------------
-- | Sovereign.Synthesis.Physics.NoSplitJ1Ring
--
-- 「A₄ 不变的 3×3 矩阵必为标量」——从 ℤ 提升到**任意无挠交换环** R。
--
-- 与 NoSplitJ1 / NoSplitJ1Full 的关系：
--   · NoSplitJ1     只证**对角**情形（3-循环 ⇒ 三个对角元相等）；
--   · NoSplitJ1Full 证一般（含非对角）情形，但只在 ℤ 上，无挠性靠**整数构造子互异**；
--   · 本模块把 NoSplitJ1Full 的证明结构原样搬到「无挠交换环」上：
--     不碰整数构造子，把无挠性作为**假设**传进来（- x ≈ x → x ≈ 0#）。
--
-- 为什么值得做：物理上的耦合常数不必是整数（可为 GF(p)、ℚ、ℝ 系数），
--   结论「A₄ 不变微扰不能劈裂 J=1 三重态」只依赖环公理 + 无挠性，与载体无关。
--
-- 记号约定（诚实边界）：
--   R 的等式取环自带的 setoid 等式 _≈_（stdlib 的 CommutativeRing 不保证 Carrier
--   有命题等式）。命题里的「≡」按 setoid 层的标准读法读作 ≈；本模块**不**引入
--   可判定相等，也不假设载体是 ℤ。
--
-- 证明结构与 NoSplitJ1Full 逐条对应（apply-e0/…/c01-20/…/n20/n21），
--   只有基础引理换代：整数构造子互异 → 环公理 + 无挠性假设。
--
-- 0 postulate / 0 hole。
------------------------------------------------------------------------
module Sovereign.Synthesis.Physics.NoSplitJ1Ring where

open import Agda.Primitive using (_⊔_)
open import Algebra.Bundles using (CommutativeRing)
open import Data.Fin using (Fin; zero; suc)
open import Data.Product using (_×_; _,_)
open import Relation.Binary using (Setoid)

module General {a ℓ} (R : CommutativeRing a ℓ) where

  open CommutativeRing R public hiding (zero)

  -- 环等式的 setoid（equational reasoning 用）
  R-setoid : Setoid a ℓ
  R-setoid = record { Carrier = Carrier ; _≈_ = _≈_ ; isEquivalence = isEquivalence }

  open import Relation.Binary.Reasoning.Setoid R-setoid
  open import Algebra.Properties.Ring ring using (-1*x≈-x; -‿involutive)

  ------------------------------------------------------------------------
  -- §1. 载体：V = Fin 3 → R，以及三个基向量
  ------------------------------------------------------------------------

  V : Set a
  V = Fin 3 → Carrier

  e0 e1 e2 : V
  e0 zero             = 1#
  e0 (suc zero)       = 0#
  e0 (suc (suc zero)) = 0#

  e1 zero             = 0#
  e1 (suc zero)       = 1#
  e1 (suc (suc zero)) = 0#

  e2 zero             = 0#
  e2 (suc zero)       = 0#
  e2 (suc (suc zero)) = 1#

  ------------------------------------------------------------------------
  -- §2. 环上的基础引理（全部取环公理 / 环属性，不引入新假设）
  ------------------------------------------------------------------------

  *1ʳ : ∀ x → x * 1# ≈ x
  *1ʳ = *-identityʳ

  *0ʳ : ∀ x → x * 0# ≈ 0#
  *0ʳ = zeroʳ

  +0ʳ : ∀ x → x + 0# ≈ x
  +0ʳ = +-identityʳ

  +0ˡ : ∀ x → 0# + x ≈ x
  +0ˡ = +-identityˡ

  -- 负零：- 0# ≈ 0#（由逆元的唯一性；不依赖无挠性）
  neg-0 : - 0# ≈ 0#
  neg-0 = trans (sym (+0ˡ (- 0#))) (-‿inverseʳ 0#)

  -- 乘 -1# = 取负
  x*-1≈-x : ∀ x → x * (- 1#) ≈ - x
  x*-1≈-x x = begin
    x * (- 1#)  ≈⟨ *-comm x (- 1#) ⟩
    (- 1#) * x  ≈⟨ -1*x≈-x x ⟩
    - x         ∎

  ------------------------------------------------------------------------
  -- §3. 矩阵在向量上的作用、两个生成元
  ------------------------------------------------------------------------

  apply : (Fin 3 → Fin 3 → Carrier) → V → V
  apply A v zero             = A zero zero * v zero
                             + A zero (suc zero) * v (suc zero)
                             + A zero (suc (suc zero)) * v (suc (suc zero))
  apply A v (suc zero)       = A (suc zero) zero * v zero
                             + A (suc zero) (suc zero) * v (suc zero)
                             + A (suc zero) (suc (suc zero)) * v (suc (suc zero))
  apply A v (suc (suc zero)) = A (suc (suc zero)) zero * v zero
                             + A (suc (suc zero)) (suc zero) * v (suc zero)
                             + A (suc (suc zero)) (suc (suc zero)) * v (suc (suc zero))

  shift : V → V                       -- 3-循环 (v₀,v₁,v₂) ↦ (v₂,v₀,v₁)
  shift v zero             = v (suc (suc zero))
  shift v (suc zero)       = v zero
  shift v (suc (suc zero)) = v (suc zero)

  flip : V → V                        -- 反演型 180° 旋转 (v₀,v₁,v₂) ↦ (−v₀,−v₁,v₂)
  flip v zero             = - v zero
  flip v (suc zero)       = - v (suc zero)
  flip v (suc (suc zero)) = v (suc (suc zero))

  ------------------------------------------------------------------------
  -- §4. 三个基向量上的取值 = 取列（只需「乘 1 / 乘 0 / 加 0」）
  ------------------------------------------------------------------------

  -- 系数为 (1#, 0#, 0#) 时线性组合退化为第一项
  lin-100 : ∀ a b c → a * 1# + b * 0# + c * 0# ≈ a
  lin-100 a b c = begin
    (a * 1# + b * 0#) + c * 0#  ≈⟨ +-cong (+-cong (*1ʳ a) (*0ʳ b)) (*0ʳ c) ⟩
    (a + 0#) + 0#               ≈⟨ +0ʳ (a + 0#) ⟩
    a + 0#                      ≈⟨ +0ʳ a ⟩
    a                           ∎

  -- 系数为 (0#, 1#, 0#) 时退化为第二项
  lin-010 : ∀ a b c → a * 0# + b * 1# + c * 0# ≈ b
  lin-010 a b c = begin
    (a * 0# + b * 1#) + c * 0#  ≈⟨ +-cong (+-cong (*0ʳ a) (*1ʳ b)) (*0ʳ c) ⟩
    (0# + b) + 0#               ≈⟨ +-cong (+0ˡ b) refl ⟩
    b + 0#                      ≈⟨ +0ʳ b ⟩
    b                           ∎

  -- 系数为 (0#, 0#, 1#) 时退化为第三项
  lin-001 : ∀ a b c → a * 0# + b * 0# + c * 1# ≈ c
  lin-001 a b c = begin
    (a * 0# + b * 0#) + c * 1#  ≈⟨ +-cong (+-cong (*0ʳ a) (*0ʳ b)) (*1ʳ c) ⟩
    (0# + 0#) + c               ≈⟨ +-cong (+0ˡ 0#) refl ⟩
    0# + c                      ≈⟨ +0ˡ c ⟩
    c                           ∎

  -- 系数为 (−1#, −0#, 0#)（= flip e0）时退化为第一项的负
  lin-neg100 : ∀ a b c → a * (- 1#) + b * (- 0#) + c * 0# ≈ - a
  lin-neg100 a b c = begin
    (a * (- 1#) + b * (- 0#)) + c * 0#
      ≈⟨ +-cong (+-cong (x*-1≈-x a) (trans (*-cong refl neg-0) (*0ʳ b))) (*0ʳ c) ⟩
    (- a + 0#) + 0#             ≈⟨ +0ʳ (- a + 0#) ⟩
    - a + 0#                    ≈⟨ +0ʳ (- a) ⟩
    - a                         ∎

  -- 系数为 (−0#, −1#, 0#)（= flip e1）时退化为第二项的负
  lin-neg010 : ∀ a b c → a * (- 0#) + b * (- 1#) + c * 0# ≈ - b
  lin-neg010 a b c = begin
    (a * (- 0#) + b * (- 1#)) + c * 0#
      ≈⟨ +-cong (+-cong (trans (*-cong refl neg-0) (*0ʳ a)) (x*-1≈-x b)) (*0ʳ c) ⟩
    (0# + - b) + 0#             ≈⟨ +-cong (+0ˡ (- b)) refl ⟩
    - b + 0#                    ≈⟨ +0ʳ (- b) ⟩
    - b                         ∎

  apply-e0 : ∀ A i → apply A e0 i ≈ A i zero
  apply-e0 A zero             = lin-100 (A zero zero) (A zero (suc zero)) (A zero (suc (suc zero)))
  apply-e0 A (suc zero)       = lin-100 (A (suc zero) zero) (A (suc zero) (suc zero)) (A (suc zero) (suc (suc zero)))
  apply-e0 A (suc (suc zero)) = lin-100 (A (suc (suc zero)) zero) (A (suc (suc zero)) (suc zero)) (A (suc (suc zero)) (suc (suc zero)))

  apply-e1 : ∀ A i → apply A e1 i ≈ A i (suc zero)
  apply-e1 A zero             = lin-010 (A zero zero) (A zero (suc zero)) (A zero (suc (suc zero)))
  apply-e1 A (suc zero)       = lin-010 (A (suc zero) zero) (A (suc zero) (suc zero)) (A (suc zero) (suc (suc zero)))
  apply-e1 A (suc (suc zero)) = lin-010 (A (suc (suc zero)) zero) (A (suc (suc zero)) (suc zero)) (A (suc (suc zero)) (suc (suc zero)))

  apply-e2 : ∀ A i → apply A e2 i ≈ A i (suc (suc zero))
  apply-e2 A zero             = lin-001 (A zero zero) (A zero (suc zero)) (A zero (suc (suc zero)))
  apply-e2 A (suc zero)       = lin-001 (A (suc zero) zero) (A (suc zero) (suc zero)) (A (suc zero) (suc (suc zero)))
  apply-e2 A (suc (suc zero)) = lin-001 (A (suc (suc zero)) zero) (A (suc (suc zero)) (suc zero)) (A (suc (suc zero)) (suc (suc zero)))

  apply-flip-e0 : ∀ A i → apply A (flip e0) i ≈ - (A i zero)
  apply-flip-e0 A zero             = lin-neg100 (A zero zero) (A zero (suc zero)) (A zero (suc (suc zero)))
  apply-flip-e0 A (suc zero)       = lin-neg100 (A (suc zero) zero) (A (suc zero) (suc zero)) (A (suc zero) (suc (suc zero)))
  apply-flip-e0 A (suc (suc zero)) = lin-neg100 (A (suc (suc zero)) zero) (A (suc (suc zero)) (suc zero)) (A (suc (suc zero)) (suc (suc zero)))

  apply-flip-e1 : ∀ A i → apply A (flip e1) i ≈ - (A i (suc zero))
  apply-flip-e1 A zero             = lin-neg010 (A zero zero) (A zero (suc zero)) (A zero (suc (suc zero)))
  apply-flip-e1 A (suc zero)       = lin-neg010 (A (suc zero) zero) (A (suc zero) (suc zero)) (A (suc zero) (suc (suc zero)))
  apply-flip-e1 A (suc (suc zero)) = lin-neg010 (A (suc (suc zero)) zero) (A (suc (suc zero)) (suc zero)) (A (suc (suc zero)) (suc (suc zero)))

  ------------------------------------------------------------------------
  -- §5. 两条交换性假设与由此导出的分量关系
  ------------------------------------------------------------------------

  Commutes-shift : (Fin 3 → Fin 3 → Carrier) → Set (a ⊔ ℓ)
  Commutes-shift A = ∀ v i → apply A (shift v) i ≈ shift (apply A v) i

  Commutes-flip : (Fin 3 → Fin 3 → Carrier) → Set (a ⊔ ℓ)
  Commutes-flip A = ∀ v i → apply A (flip v) i ≈ flip (apply A v) i

  -- 3-循环给出的循环关系（与 NoSplitJ1Full §5 一一对应）
  c01-20 : ∀ A → Commutes-shift A → A zero (suc zero) ≈ A (suc (suc zero)) zero
  c01-20 A H = begin
    A zero (suc zero)             ≈⟨ sym (apply-e1 A zero) ⟩
    apply A e1 zero               ≈⟨ H e0 zero ⟩
    apply A e0 (suc (suc zero))   ≈⟨ apply-e0 A (suc (suc zero)) ⟩
    A (suc (suc zero)) zero       ∎

  c11-00 : ∀ A → Commutes-shift A → A (suc zero) (suc zero) ≈ A zero zero
  c11-00 A H = begin
    A (suc zero) (suc zero)       ≈⟨ sym (apply-e1 A (suc zero)) ⟩
    apply A e1 (suc zero)         ≈⟨ H e0 (suc zero) ⟩
    apply A e0 zero               ≈⟨ apply-e0 A zero ⟩
    A zero zero                   ∎

  c21-10 : ∀ A → Commutes-shift A → A (suc (suc zero)) (suc zero) ≈ A (suc zero) zero
  c21-10 A H = begin
    A (suc (suc zero)) (suc zero)      ≈⟨ sym (apply-e1 A (suc (suc zero))) ⟩
    apply A e1 (suc (suc zero))        ≈⟨ H e0 (suc (suc zero)) ⟩
    apply A e0 (suc zero)              ≈⟨ apply-e0 A (suc zero) ⟩
    A (suc zero) zero                  ∎

  c02-21 : ∀ A → Commutes-shift A → A zero (suc (suc zero)) ≈ A (suc (suc zero)) (suc zero)
  c02-21 A H = begin
    A zero (suc (suc zero))            ≈⟨ sym (apply-e2 A zero) ⟩
    apply A e2 zero                    ≈⟨ H e1 zero ⟩
    apply A e1 (suc (suc zero))        ≈⟨ apply-e1 A (suc (suc zero)) ⟩
    A (suc (suc zero)) (suc zero)      ∎

  c12-01 : ∀ A → Commutes-shift A → A (suc zero) (suc (suc zero)) ≈ A zero (suc zero)
  c12-01 A H = begin
    A (suc zero) (suc (suc zero))      ≈⟨ sym (apply-e2 A (suc zero)) ⟩
    apply A e2 (suc zero)              ≈⟨ H e1 (suc zero) ⟩
    apply A e1 zero                    ≈⟨ apply-e1 A zero ⟩
    A zero (suc zero)                  ∎

  c22-11 : ∀ A → Commutes-shift A → A (suc (suc zero)) (suc (suc zero)) ≈ A (suc zero) (suc zero)
  c22-11 A H = begin
    A (suc (suc zero)) (suc (suc zero))  ≈⟨ sym (apply-e2 A (suc (suc zero))) ⟩
    apply A e2 (suc (suc zero))          ≈⟨ H e1 (suc (suc zero)) ⟩
    apply A e1 (suc zero)                ≈⟨ apply-e1 A (suc zero) ⟩
    A (suc zero) (suc zero)              ∎

  c10-02 : ∀ A → Commutes-shift A → A (suc zero) zero ≈ A zero (suc (suc zero))
  c10-02 A H = begin
    A (suc zero) zero                    ≈⟨ sym (apply-e0 A (suc zero)) ⟩
    apply A e0 (suc zero)                ≈⟨ H e2 (suc zero) ⟩
    apply A e2 zero                      ≈⟨ apply-e2 A zero ⟩
    A zero (suc (suc zero))              ∎

  c20-12 : ∀ A → Commutes-shift A → A (suc (suc zero)) zero ≈ A (suc zero) (suc (suc zero))
  c20-12 A H = begin
    A (suc (suc zero)) zero              ≈⟨ sym (apply-e0 A (suc (suc zero))) ⟩
    apply A e0 (suc (suc zero))          ≈⟨ H e2 (suc (suc zero)) ⟩
    apply A e2 (suc zero)                ≈⟨ apply-e2 A (suc zero) ⟩
    A (suc zero) (suc (suc zero))        ∎

  -- 反演型元素给出的两条「自反 ⇒ 零」（注意这里**还没有**用无挠性：
  -- n20/n21 只给出 - a ≈ a，变成 a ≈ 0# 需要 torsion 假设）
  n20 : ∀ A → Commutes-flip A → - (A (suc (suc zero)) zero) ≈ A (suc (suc zero)) zero
  n20 A H = begin
    - (A (suc (suc zero)) zero)          ≈⟨ sym (apply-flip-e0 A (suc (suc zero))) ⟩
    apply A (flip e0) (suc (suc zero))   ≈⟨ H e0 (suc (suc zero)) ⟩
    flip (apply A e0) (suc (suc zero))   ≈⟨ apply-e0 A (suc (suc zero)) ⟩
    A (suc (suc zero)) zero              ∎

  n21 : ∀ A → Commutes-flip A → - (A (suc (suc zero)) (suc zero)) ≈ A (suc (suc zero)) (suc zero)
  n21 A H = begin
    - (A (suc (suc zero)) (suc zero))           ≈⟨ sym (apply-flip-e1 A (suc (suc zero))) ⟩
    apply A (flip e1) (suc (suc zero))          ≈⟨ H e1 (suc (suc zero)) ⟩
    flip (apply A e1) (suc (suc zero))          ≈⟨ apply-e1 A (suc (suc zero)) ⟩
    A (suc (suc zero)) (suc zero)               ∎

  ------------------------------------------------------------------------
  -- §6. 无挠性：- x ≈ x ⇒ x ≈ 0#
  --
  -- 这是本模块**唯一**的额外假设（NoSplitJ1Full 里由整数构造子互异免费得到）。
  -- ℚ / ℝ / GF(p)（p ≠ 2）都满足它（2 可逆 ⇒ -x ≈ x 迫使 x ≈ 0#）。
  -- 特征 2 的**非平凡**环不满足：那里 -x ≈ x 对一切 x 成立，假说会迫使 x ≈ 0#。
  --
  -- [未验证·非内核] 特征 2 上结论确实失效（GF(2) 里 A = S 与 S、F 都交换但非标量）。
  --   该反例只有**数值**验证（oracle 回执见台账节点 Agda.NoSplitJ1.ring-general 的
  --   oracle 字段；脚本 engineering/oracle_nosplit_ring_general.py）；
  --   **不是** Agda 定理 —— 本库没有 GF(2) 环实例的形式化。
  ------------------------------------------------------------------------

  TorsionFree : Set (a ⊔ ℓ)
  TorsionFree = ∀ x → - x ≈ x → x ≈ 0#

  ------------------------------------------------------------------------
  -- §7. 主定理：与两个生成元都交换 ⇒ 六个非对角元为 0、三个对角元相等
  ------------------------------------------------------------------------

  no-split-ring-general :
    TorsionFree →
    ∀ A → Commutes-shift A → Commutes-flip A →
    (A zero (suc zero) ≈ 0#) × (A zero (suc (suc zero)) ≈ 0#)
    × (A (suc zero) zero ≈ 0#) × (A (suc zero) (suc (suc zero)) ≈ 0#)
    × (A (suc (suc zero)) zero ≈ 0#) × (A (suc (suc zero)) (suc zero) ≈ 0#)
    × (A zero zero ≈ A (suc zero) (suc zero))
    × (A (suc zero) (suc zero) ≈ A (suc (suc zero)) (suc (suc zero)))
  no-split-ring-general torsion A Hs Hf = z01 , z02 , z10 , z12 , z20 , z21 , d01 , d12
    where
      z20 : A (suc (suc zero)) zero ≈ 0#
      z20 = torsion (A (suc (suc zero)) zero) (n20 A Hf)

      z21 : A (suc (suc zero)) (suc zero) ≈ 0#
      z21 = torsion (A (suc (suc zero)) (suc zero)) (n21 A Hf)

      z01 : A zero (suc zero) ≈ 0#
      z01 = trans (c01-20 A Hs) z20

      z02 : A zero (suc (suc zero)) ≈ 0#
      z02 = trans (c02-21 A Hs) z21

      z10 : A (suc zero) zero ≈ 0#
      z10 = trans (c10-02 A Hs) z02

      z12 : A (suc zero) (suc (suc zero)) ≈ 0#
      z12 = trans (c12-01 A Hs) z01

      d01 : A zero zero ≈ A (suc zero) (suc zero)
      d01 = sym (c11-00 A Hs)

      d12 : A (suc zero) (suc zero) ≈ A (suc (suc zero)) (suc (suc zero))
      d12 = sym (c22-11 A Hs)

  ------------------------------------------------------------------------
  -- §8. 两个生成元的阶（展示关系 s³ = 1、f² = 1、(fs)³ = 1）——与载体无关
  ------------------------------------------------------------------------

  shift³ : ∀ v i → shift (shift (shift v)) i ≈ v i
  shift³ v zero             = refl
  shift³ v (suc zero)       = refl
  shift³ v (suc (suc zero)) = refl

  flip² : ∀ v i → flip (flip v) i ≈ v i
  flip² v zero             = -‿involutive (v zero)
  flip² v (suc zero)       = -‿involutive (v (suc zero))
  flip² v (suc (suc zero)) = refl

  g : V → V
  g v = flip (shift v)

  g³ : ∀ v i → g (g (g v)) i ≈ v i
  g³ v zero             = -‿involutive (v zero)
  g³ v (suc zero)       = -‿involutive (v (suc zero))
  g³ v (suc (suc zero)) = -‿involutive (v (suc (suc zero)))

------------------------------------------------------------------------
-- §9. 实例化到 ℤ：通用定理 ⇒ ℤ 版（NoSplitJ1Full 的结论）
--
-- **这不是重复证明**：它是 §7 的通用定理在 ℤ 上的实例化，作用是确认「推广没有
-- 变弱」——ℤ 环的 _≈_ 就是命题等式 ≡，故结论与 no-split-full 同型；§9b 在**内核**
-- 里把「同型」证成：把 NoSplitJ1Full 的假设逐点转换成本模块的假设，于是本模块的
-- ℤ 实例**蕴含** no-split-full 的陈述（不是「看起来一样」，是类型检查器接受）。
-- 无挠性那一环直接复用 NoSplitJ1Full.neg-eq-self（整数构造子互异），不重证。
------------------------------------------------------------------------
open import Data.Integer using (ℤ; +0; +[1+_]; -[1+_])
open import Data.Integer.Properties using (+-*-commutativeRing)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
import Sovereign.Synthesis.Physics.NoSplitJ1Full as Full

module ℤ-instance = General +-*-commutativeRing

no-split-full-via-ring :
  ∀ A → ℤ-instance.Commutes-shift A → ℤ-instance.Commutes-flip A →
  (A zero (suc zero) ≡ +0) × (A zero (suc (suc zero)) ≡ +0)
  × (A (suc zero) zero ≡ +0) × (A (suc zero) (suc (suc zero)) ≡ +0)
  × (A (suc (suc zero)) zero ≡ +0) × (A (suc (suc zero)) (suc zero) ≡ +0)
  × (A zero zero ≡ A (suc zero) (suc zero))
  × (A (suc zero) (suc zero) ≡ A (suc (suc zero)) (suc (suc zero)))
no-split-full-via-ring = ℤ-instance.no-split-ring-general Full.neg-eq-self

------------------------------------------------------------------------
-- §9b. 内核核验「推广没有变弱」：把 NoSplitJ1Full 的两条交换性假设**逐点**转换成
--   本模块的假设（Fin 3 只有 3 个元素，逐案展开后两边同时归约到同一项 ⇒ 每案就是
--   那条假设本身），于是 §7 的 ℤ 实例**蕴含** NoSplitJ1Full 的主定理。
--   （注意：两模块的 apply/shift 是两个不同的定义 ⇒ 作为函数它们**不**定义相等，
--    对变量 i 直接比较会 `UnequalTerms`；必须逐点展开。这也是本节的必要性。）
------------------------------------------------------------------------

from-Full-shift : ∀ A → Full.Commutes-shift A → ℤ-instance.Commutes-shift A
from-Full-shift A H v zero             = H v zero
from-Full-shift A H v (suc zero)       = H v (suc zero)
from-Full-shift A H v (suc (suc zero)) = H v (suc (suc zero))

from-Full-flip : ∀ A → Full.Commutes-flip A → ℤ-instance.Commutes-flip A
from-Full-flip A H v zero             = H v zero
from-Full-flip A H v (suc zero)       = H v (suc zero)
from-Full-flip A H v (suc (suc zero)) = H v (suc (suc zero))

no-split-full-from-ring :
  ∀ A → Full.Commutes-shift A → Full.Commutes-flip A →
  (A zero (suc zero) ≡ +0) × (A zero (suc (suc zero)) ≡ +0)
  × (A (suc zero) zero ≡ +0) × (A (suc zero) (suc (suc zero)) ≡ +0)
  × (A (suc (suc zero)) zero ≡ +0) × (A (suc (suc zero)) (suc zero) ≡ +0)
  × (A zero zero ≡ A (suc zero) (suc zero))
  × (A (suc zero) (suc zero) ≡ A (suc (suc zero)) (suc (suc zero)))
no-split-full-from-ring A Hs Hf =
  no-split-full-via-ring A (from-Full-shift A Hs) (from-Full-flip A Hf)
