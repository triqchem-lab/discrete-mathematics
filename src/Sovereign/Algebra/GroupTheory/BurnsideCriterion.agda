{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Algebra.GroupTheory.BurnsideCriterion
--
-- **#orbits 的判据无关性**（Burnside 块 4）。
--
-- 本模块补上块 3 模块头明写的诚实边界：
--   「#orbits 的定义取『轨道内 toℕ 最小元』作判据 —— 换判据结论不变，本模块不证这一点。」
--
-- 主定理（rep-count-invariant）：
--   任意 r : Fin p → Fin p，只要满足两条**结构性**条件
--     ① lands : ∀ x → orbEq (r x) x            （落在 x 自己的轨道内）
--     ② const : ∀ {x y} → orbEq x y → r x ≡ r y（只依赖轨道，不依赖轨道内的点）
--   则「r 的不动点个数」≡ numOrbits。
--
-- 为什么这是对的（不是「碰巧相等」）：
--   两条条件合起来说明 r 在**每条轨道上取唯一值**，故 r 的不动点集合 = 「每轨道恰一个」
--   的系统；orbRep 的不动点集合也是。两个「每轨道恰一个」的系统必然等势 ——
--   双向映射是 x ↦ orbRep x 与 b ↦ r b，各自单射，交给 stdlib
--   cantor-schröder-bernstein 收口（不自己写基数搬运）。
--
-- 为什么幂等不必作假设：
--   r (r x) ≡ r x 由两条条件导出：lands 给 orbEq (r x) x，取对称得 orbEq x (r x)，
--   再用 const 即得。故 IsRepCriterion 只有两个字段。
--
-- 为什么这不是空定理：
--   orbRep 本身是一个实例（orbRep-criterion），故 burnside-any-rep 在 r = orbRep 处
--   退化为块 3 的 burnside-lemma —— 泛化是真泛化，不是另一个定理。
--   另有**非最小元**判据的实例：平凡作用取 r = id（不动点 = 全部点），见
--   BurnsideInstance.agda §4 的 refl 交叉验证。
--
-- 核心原则：
--   1. 复用优先：orbEq / orbRep / orbRep-eq / orbRep-idem / orbRep-eq-of-eq / RepEnum
--      全部来自 OrbitPartition，本模块不重证轨道机器
--   2. CSB 双向单射（块 2 已用同一手法），不自己写基数搬运
--   3. 0 postulate / 0 hole；无 funExt（全部是等式）；不对相位/时钟作任何断言
--
-- 诚实边界：
--   作用仍取在**有限集 Fin p** 上（#orbits 才有限）。
--   本模块证的是「合法判据都给同一个数」，不是「任意判据都给同一个数」——
--   反例：对非平凡作用取 r = id 不满足 const。
--
-- 包含：IsRepCriterion / FixEnum / r-idem / rep-count-invariant / orbRep-criterion /
--       burnside-any-rep

module Sovereign.Algebra.GroupTheory.BurnsideCriterion where

open import Data.Nat using (ℕ; _*_)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.Fin.Properties using (_≟_; cantor-schröder-bernstein)
open import Data.Product using (Σ; _,_)
open import Function.Definitions using (Injective)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; subst; module ≡-Reasoning)

open import Sovereign.Algebra.GroupTheory.Lagrange using (FinGroup)
open import Sovereign.Algebra.GroupTheory.OrbitStabilizer using (Action)
open import Sovereign.Algebra.GroupTheory.CosetAuto using (SubEnum; enum)
open import Sovereign.Algebra.GroupTheory.Burnside using (stabCount)
open import Sovereign.Algebra.GroupTheory.OrbitPartition using (module OrbitPart)
open import Sovereign.Algebra.GroupTheory.BurnsideMain using (numOrbitsOf; burnside-lemma)

--------------------------------------------------------------------------------
-- §1. 判据无关性（主定理）
--------------------------------------------------------------------------------

module CriterionFree {n p : ℕ} (G : FinGroup n) (A : Action G (Fin p)) where
  open OrbitPart G A
  open ≡-Reasoning

  -- 合法代表元判据：落在轨道内 + 只依赖轨道
  record IsRepCriterion (r : Fin p → Fin p) : Set where
    field
      lands : ∀ x → orbEq (r x) x
      const : ∀ {x y} → orbEq x y → r x ≡ r y

  -- r 的不动点枚举（= r 挑选出的代表元系统）
  FixEnum : (r : Fin p → Fin p) → SubEnum p (λ x → r x ≡ x)
  FixEnum r = enum (λ x → r x ≡ x) (λ x → r x ≟ x)

  -- 幂等是 lands + const 的推论（故不作假设）
  r-idem : (r : Fin p → Fin p) → IsRepCriterion r → ∀ x → r (r x) ≡ r x
  r-idem r C x = sym (IsRepCriterion.const C (orbEq-sym (IsRepCriterion.lands C x)))

  rep-count-invariant : (r : Fin p → Fin p) (C : IsRepCriterion r)
                      → SubEnum.size (FixEnum r) ≡ numOrbits
  rep-count-invariant r C = cantor-schröder-bernstein {f = φ} {g = ψ} φ-inj ψ-inj
    where
      Er : SubEnum p (λ x → r x ≡ x)
      Er = FixEnum r

      Eo : SubEnum p isRep
      Eo = RepEnum

      φ : Fin (SubEnum.size Er) → Fin (SubEnum.size Eo)
      φ i = SubEnum.index Eo (orbRep (SubEnum.toFin Er i))
                             (orbRep-idem (SubEnum.toFin Er i))

      ψ : Fin (SubEnum.size Eo) → Fin (SubEnum.size Er)
      ψ j = SubEnum.index Er (r (SubEnum.toFin Eo j))
                             (r-idem r C (SubEnum.toFin Eo j))

      -- φ 单射：像相同 ⟹ 同轨道 ⟹ const 给 r a ≡ r b ⟹ a ≡ b（两者都是 r 的不动点）
      φ-inj : Injective _≡_ _≡_ φ
      φ-inj {i} {j} eq = SubEnum.toFin-inj Er a≡b
        where
          a : Fin p
          a = SubEnum.toFin Er i
          b : Fin p
          b = SubEnum.toFin Er j

          h : orbRep a ≡ orbRep b
          h = trans (sym (SubEnum.index-ok Eo (orbRep a) (orbRep-idem a)))
                    (trans (cong (SubEnum.toFin Eo) eq)
                           (SubEnum.index-ok Eo (orbRep b) (orbRep-idem b)))

          orb-a-b : orbEq a b
          orb-a-b = orbEq-trans {x = b} {y = orbRep a} {z = a}
                      (orbEq-sym (orbRep-eq a))
                      (subst (λ z → orbEq z b) (sym h) (orbRep-eq b))

          a≡b : a ≡ b
          a≡b = trans (sym (SubEnum.toFin-P Er i))
                      (trans (IsRepCriterion.const C orb-a-b)
                             (SubEnum.toFin-P Er j))

      -- ψ 单射：像相同 ⟹ r a ≡ r b ⟹ 同轨道 ⟹ orbRep a ≡ orbRep b ⟹ a ≡ b（同为代表元）
      ψ-inj : Injective _≡_ _≡_ ψ
      ψ-inj {i} {j} eq = SubEnum.toFin-inj Eo a≡b
        where
          a : Fin p
          a = SubEnum.toFin Eo i
          b : Fin p
          b = SubEnum.toFin Eo j

          h : r a ≡ r b
          h = trans (sym (SubEnum.index-ok Er (r a) (r-idem r C a)))
                    (trans (cong (SubEnum.toFin Er) eq)
                           (SubEnum.index-ok Er (r b) (r-idem r C b)))

          orb-a-b : orbEq a b
          orb-a-b = orbEq-trans {x = b} {y = r a} {z = a}
                      (orbEq-sym (IsRepCriterion.lands C a))
                      (subst (λ z → orbEq z b) (sym h) (IsRepCriterion.lands C b))

          a≡b : a ≡ b
          a≡b = trans (sym (SubEnum.toFin-P Eo i))
                      (trans (orbRep-eq-of-eq orb-a-b) (SubEnum.toFin-P Eo j))

  -- orbRep 本身是合法判据（保证泛化是真泛化）
  orbRep-criterion : IsRepCriterion orbRep
  orbRep-criterion = record
    { lands = orbRep-eq
    ; const = λ {x} {y} q → orbRep-eq-of-eq q
    }

--------------------------------------------------------------------------------
-- §2. 推论：任意判据的 Burnside 乘法形式
--------------------------------------------------------------------------------

burnside-any-rep : ∀ {n p} (G : FinGroup n) (A : Action G (Fin p))
                   (r : Fin p → Fin p)
                 → CriterionFree.IsRepCriterion G A r
                 → n * SubEnum.size (CriterionFree.FixEnum G A r) ≡ stabCount G A
burnside-any-rep {n} {p} G A r C =
  trans (cong (n *_) (CriterionFree.rep-count-invariant G A r C))
        (burnside-lemma G A)
