{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Algebra.GroupTheory.ActionIsomorphism
--
-- **轨道数是作用的同构不变量**（Burnside 块 6 的承重件）。
--
-- 数学背景：
--   两个作用 A : Action G (Fin p) 与 B : Action G (Fin q) 称为**同构**，若存在
--   互相的等变单射 f : Fin p → Fin q 与 fb : Fin q → Fin p：
--       f  (g ·_A x) ≡ g ·_B (f  x)
--       fb (g ·_B y) ≡ g ·_A (fb y)
--   等变映射把轨道送到轨道，且同构下轨道一一对应，故 #orbits 相等。
--
-- 为什么不能靠「同构 ⟹ 结构相同」一句话过去：
--   本库的 #orbits 是**算出来的**（enum 的 size，绕不开 orbRep 的最小元搜索），
--   所以「轨道一一对应」必须落成两个有限枚举之间的双射 —— 即 §1 的 φ / ψ 两向单射
--   + stdlib cantor-schröder-bernstein。这与块 2 / 3 / 4 是同一手法。
--
-- 为什么这个定理有用：
--   它把「#orbits」从**具体编码**里解放出来。块 5 的项链计数依赖把 4 珠 2 色编码成
--   4-bit 串（低位 = 第 0 珠）；换一种编码（或把旋转换成反向旋转）得到的是**同构**的
--   作用，故项链数不变 —— 见 NecklaceInvariance.agda。
--
-- 核心原则：
--   1. **不重证轨道机器**：orbEq / orbRep / orbRep-eq / orbRep-eq-of-eq / RepEnum 全部
--      取自 OrbitPartition，本模块只用它们做两向单射
--   2. CSB 收口（块 2 起的一贯做法），不自己写基数搬运
--   3. **强于「基数相等」**：结论是 numOrbits 相等，不需要 p ≡ q（两个载体的基数可以
--      在小中间下相等，本模块不证这一点 —— 见诚实边界）
--   4. 0 postulate / 0 hole；无 funExt（全部是等式）；不引 Choice
--
-- 诚实边界：
--   结论只是 #orbits 相等，**不**断言 p ≡ q，也**不**断言两个作用作为 G-集同构
--   （相互等变单射 + CSB 会给出 p ≡ q，但那是另一条陈述，本模块不证）。
--   载体仍须是有限集 Fin p / Fin q —— #orbits 才有限。
--
-- 包含：Φ / Ψ / Φ-inj / Ψ-inj / iso-invariant / action-iso-invariant

module Sovereign.Algebra.GroupTheory.ActionIsomorphism where

open import Data.Nat using (ℕ)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.Fin.Properties using (cantor-schröder-bernstein)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Function.Definitions using (Injective)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; subst)

open import Sovereign.Algebra.GroupTheory.Lagrange using (FinGroup)
open import Sovereign.Algebra.GroupTheory.OrbitStabilizer using (Action)
open import Sovereign.Algebra.GroupTheory.CosetAuto using (SubEnum)
open import Sovereign.Algebra.GroupTheory.OrbitPartition using (module OrbitPart)
open import Sovereign.Algebra.GroupTheory.BurnsideMain using (numOrbitsOf)

--------------------------------------------------------------------------------
-- §1. 同构不变性
--------------------------------------------------------------------------------

module ActionIso {n p q : ℕ} (G : FinGroup n)
                 (A : Action G (Fin p)) (B : Action G (Fin q)) where
  module PA = OrbitPart G A
  module PB = OrbitPart G B

  -- 把 A 的「不动代表元」打到 B 的不动代表元
  Φ : (f : Fin p → Fin q)
    → Fin (SubEnum.size PA.RepEnum) → Fin (SubEnum.size PB.RepEnum)
  Φ f i = SubEnum.index PB.RepEnum
             (PB.orbRep (f (SubEnum.toFin PA.RepEnum i)))
             (PB.orbRep-idem (f (SubEnum.toFin PA.RepEnum i)))

  -- 反向：把 B 的「不动代表元」打回 A 的不动代表元
  Ψ : (fb : Fin q → Fin p)
    → Fin (SubEnum.size PB.RepEnum) → Fin (SubEnum.size PA.RepEnum)
  Ψ fb j = SubEnum.index PA.RepEnum
             (PA.orbRep (fb (SubEnum.toFin PB.RepEnum j)))
             (PA.orbRep-idem (fb (SubEnum.toFin PB.RepEnum j)))

  -- 等变 + 单射 ⟹ Φ 单射
  --
  -- 关键一步：f a、f b 在 B 中同轨道 ⟹ 存在 g 使 g ·_B (f a) ≡ f b
  --           ⟹ 等变性给 f (g ·_A a) ≡ f b ⟹ f 单射给 g ·_A a ≡ b
  --           ⟹ a、b 在 A 中同轨道 ⟹ 两者都是 A 的不动代表元 ⟹ a ≡ b
  Φ-inj : (f : Fin p → Fin q) (f-inj : Injective _≡_ _≡_ f)
          (f-eq : ∀ g x → f (Action._·_ A g x) ≡ Action._·_ B g (f x))
        → Injective _≡_ _≡_ (Φ f)
  Φ-inj f f-inj f-eq {i} {j} e = SubEnum.toFin-inj PA.RepEnum a≡b
    where
      a : Fin p
      a = SubEnum.toFin PA.RepEnum i
      b : Fin p
      b = SubEnum.toFin PA.RepEnum j

      h : PB.orbRep (f a) ≡ PB.orbRep (f b)
      h = trans (sym (SubEnum.index-ok PB.RepEnum
                        (PB.orbRep (f a)) (PB.orbRep-idem (f a))))
                (trans (cong (SubEnum.toFin PB.RepEnum) e)
                       (SubEnum.index-ok PB.RepEnum
                          (PB.orbRep (f b)) (PB.orbRep-idem (f b))))

      orbB : PB.orbEq (f a) (f b)
      orbB = PB.orbEq-trans {x = f b} {y = PB.orbRep (f a)} {z = f a}
               (PB.orbEq-sym (PB.orbRep-eq (f a)))
               (subst (λ z → PB.orbEq z (f b)) (sym h) (PB.orbRep-eq (f b)))

      orbA : PA.orbEq a b
      orbA = proj₁ orbB , f-inj (trans (f-eq (proj₁ orbB) a) (proj₂ orbB))

      a≡b : a ≡ b
      a≡b = trans (sym (SubEnum.toFin-P PA.RepEnum i))
                  (trans (PA.orbRep-eq-of-eq orbA)
                         (SubEnum.toFin-P PA.RepEnum j))

  -- 反向等变 + 单射 ⟹ Ψ 单射（镜像论证）
  Ψ-inj : (fb : Fin q → Fin p) (fb-inj : Injective _≡_ _≡_ fb)
          (fb-eq : ∀ h y → fb (Action._·_ B h y) ≡ Action._·_ A h (fb y))
        → Injective _≡_ _≡_ (Ψ fb)
  Ψ-inj fb fb-inj fb-eq {j} {k} e = SubEnum.toFin-inj PB.RepEnum y≡z
    where
      y : Fin q
      y = SubEnum.toFin PB.RepEnum j
      z : Fin q
      z = SubEnum.toFin PB.RepEnum k

      h : PA.orbRep (fb y) ≡ PA.orbRep (fb z)
      h = trans (sym (SubEnum.index-ok PA.RepEnum
                        (PA.orbRep (fb y)) (PA.orbRep-idem (fb y))))
                (trans (cong (SubEnum.toFin PA.RepEnum) e)
                       (SubEnum.index-ok PA.RepEnum
                          (PA.orbRep (fb z)) (PA.orbRep-idem (fb z))))

      orbA : PA.orbEq (fb y) (fb z)
      orbA = PA.orbEq-trans {x = fb z} {y = PA.orbRep (fb y)} {z = fb y}
               (PA.orbEq-sym (PA.orbRep-eq (fb y)))
               (subst (λ w → PA.orbEq w (fb z)) (sym h) (PA.orbRep-eq (fb z)))

      orbB : PB.orbEq y z
      orbB = proj₁ orbA , fb-inj (trans (fb-eq (proj₁ orbA) y) (proj₂ orbA))

      y≡z : y ≡ z
      y≡z = trans (sym (SubEnum.toFin-P PB.RepEnum j))
                  (trans (PB.orbRep-eq-of-eq orbB)
                         (SubEnum.toFin-P PB.RepEnum k))

  iso-invariant : (f : Fin p → Fin q) (f-inj : Injective _≡_ _≡_ f)
                  (f-eq : ∀ g x → f (Action._·_ A g x) ≡ Action._·_ B g (f x))
                  (fb : Fin q → Fin p) (fb-inj : Injective _≡_ _≡_ fb)
                  (fb-eq : ∀ h y → fb (Action._·_ B h y) ≡ Action._·_ A h (fb y))
                → numOrbitsOf G A ≡ numOrbitsOf G B
  iso-invariant f f-inj f-eq fb fb-inj fb-eq =
    cantor-schröder-bernstein {f = Φ f} {g = Ψ fb}
      (Φ-inj f f-inj f-eq) (Ψ-inj fb fb-inj fb-eq)

--------------------------------------------------------------------------------
-- 顶层入口
--------------------------------------------------------------------------------

action-iso-invariant
  : ∀ {n p q} (G : FinGroup n) (A : Action G (Fin p)) (B : Action G (Fin q))
    (f : Fin p → Fin q) (f-inj : Injective _≡_ _≡_ f)
    (f-eq : ∀ g x → f (Action._·_ A g x) ≡ Action._·_ B g (f x))
    (fb : Fin q → Fin p) (fb-inj : Injective _≡_ _≡_ fb)
    (fb-eq : ∀ h y → fb (Action._·_ B h y) ≡ Action._·_ A h (fb y))
  → numOrbitsOf G A ≡ numOrbitsOf G B
action-iso-invariant G A B = ActionIso.iso-invariant G A B
