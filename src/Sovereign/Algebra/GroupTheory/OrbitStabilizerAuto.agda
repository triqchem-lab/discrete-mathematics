{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Algebra.GroupTheory.OrbitStabilizerAuto
--
-- orbit-stabilizer 的**自动构造**：把 OrbitStabilizerThm 的 8 个手工假设
-- （hAt / hAt-inj / stab-sound / stab-complete / q / repr / section / q-orbit）
-- 从「有限作用」本身自动产出，调用点降到一行。
--
-- 数学背景：
--   8 个假设其实是**两处子类型枚举**：
--     · 稳定子枚举：P_stab g := g · a ≡ a          —— 给出 hAt / hAt-inj / stab-sound /
--                                                       stab-complete（= index / index-ok）
--     · 轨道枚举：  P_orb  x := Σ g, g · a ≡ x     —— 给出轨道代表元 toFin（= repr 的来源）、
--                                                       q（= index ∘ (·a)）与 section / q-orbit
--   两者共用 CosetAuto.SubEnum（Fin n 的可判定子类型与 Fin m 双射）。
--
-- 前提与边界：
--   · 结论里 |Orbit|、|Stab| 要有限，故作用取在**有限集 X = Fin p** 上（诚实边界：
--     Orbits 的基数只有在 X 有限时才是自然数）；
--   · 可判定性来自 Fin p / Fin n 的 _≟_ 与 B.q-iff 路线上已有的 searchFin；
--   · Stab 的子群结构仍由 OrbitStabilizerThm 从作用公理导出（本模块不假设它）。
--
-- 核心原则：
--   1. |Orbit| 与 |Stab| 是**算出来的**（见 §1 对抗验证）
--   2. 不重证 Lagrange / 不重证子群结构：只做枚举与往返
--   3. 无 funExt（逐点/等式形式）
--   4. 0 postulate / 0 hole
--
-- 包含：stab-enum / orb-enum / orbit-stabilizer-auto

module Sovereign.Algebra.GroupTheory.OrbitStabilizerAuto where

open import Data.Nat using (ℕ; _*_)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.Fin.Properties using (_≟_)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Function.Bundles using (mk⇔; _⇔_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong)

open import Sovereign.Algebra.GroupTheory.Lagrange using (FinGroup)
open import Sovereign.Algebra.GroupTheory.CosetAuto using (SubEnum; enum; index-cong)
import Sovereign.Algebra.GroupTheory.OrbitStabilizer as OSA
open import Sovereign.Algebra.Holographic.4320DClosure using (searchFin)

--------------------------------------------------------------------------------
-- §1. 两处子类型枚举
--------------------------------------------------------------------------------

-- 稳定子枚举：hAt / hAt-inj / stab-sound / stab-complete 全在这里
stab-enum : ∀ {n p} (G : FinGroup n) (A : OSA.Action G (Fin p)) (a : Fin p)
          → SubEnum n (λ g → OSA.Action._·_ A g a ≡ a)
stab-enum G A a = enum (λ g → OSA.Action._·_ A g a ≡ a) (λ g → OSA.Action._·_ A g a ≟ a)

-- 轨道枚举：见证随元素携带（每个轨道点带一个到达它的群元）
orb-enum : ∀ {n p} (G : FinGroup n) (A : OSA.Action G (Fin p)) (a : Fin p)
         → SubEnum p (λ x → Σ (Fin n) (λ g → OSA.Action._·_ A g a ≡ x))
orb-enum {n} {p} G A a =
  enum (λ x → Σ (Fin n) (λ g → OSA.Action._·_ A g a ≡ x))
       (λ x → searchFin (λ g → OSA.Action._·_ A g a ≡ x) (λ g → OSA.Action._·_ A g a ≟ x))

--------------------------------------------------------------------------------
-- §2. 主定理：自动 orbit-stabilizer（|Orbit| * |Stab| ≡ |G|）
--------------------------------------------------------------------------------

orbit-stabilizer-auto :
  ∀ {n p} (G : FinGroup n) (A : OSA.Action G (Fin p)) (a : Fin p)
  → Σ ℕ (λ m → Σ ℕ (λ k → m * k ≡ n))
orbit-stabilizer-auto {n} {p} G A a =
  SubEnum.size Eo , (SubEnum.size Es , theorem)
  where
    Es : SubEnum n (λ g → OSA.Action._·_ A g a ≡ a)
    Es = stab-enum G A a

    Eo : SubEnum p (λ x → Σ (Fin n) (λ g → OSA.Action._·_ A g a ≡ x))
    Eo = orb-enum G A a

    -- 轨道标号：g ↦ 「g · a 在轨道枚举中的下标」
    q : Fin n → Fin (SubEnum.size Eo)
    q g = SubEnum.index Eo (OSA.Action._·_ A g a) (g , refl)

    -- toFin (q g) ≡ g · a
    q-ok : ∀ g → SubEnum.toFin Eo (q g) ≡ OSA.Action._·_ A g a
    q-ok g = SubEnum.index-ok Eo (OSA.Action._·_ A g a) (g , refl)

    -- 代表元：轨道点的到达见证（枚举时随身携带）
    repr : Fin (SubEnum.size Eo) → Fin n
    repr r = proj₁ (SubEnum.toFin-P Eo r)

    repr-ok : ∀ r → OSA.Action._·_ A (repr r) a ≡ SubEnum.toFin Eo r
    repr-ok r = proj₂ (SubEnum.toFin-P Eo r)

    section : ∀ r → q (repr r) ≡ r
    section r =
      trans (index-cong Eo (repr r , refl) (SubEnum.toFin-P Eo r) (repr-ok r))
            (SubEnum.toFin-inj Eo (SubEnum.index-ok Eo (SubEnum.toFin Eo r) (SubEnum.toFin-P Eo r)))

    q-orbit : ∀ x y → (q x ≡ q y) ⇔ (OSA.Action._·_ A y a ≡ OSA.Action._·_ A x a)
    q-orbit x y = mk⇔ fwd bwd
      where
        fwd : q x ≡ q y → OSA.Action._·_ A y a ≡ OSA.Action._·_ A x a
        fwd eq = sym (trans (sym (q-ok x))
                            (trans (cong (SubEnum.toFin Eo) eq) (q-ok y)))
        bwd : OSA.Action._·_ A y a ≡ OSA.Action._·_ A x a → q x ≡ q y
        bwd eq = index-cong Eo (x , refl) (y , refl) (sym eq)

    theorem : SubEnum.size Eo * SubEnum.size Es ≡ n
    theorem =
      OSA.OrbitStabilizerThm.orbit-stabilizer {n = n} G A a
        (SubEnum.toFin Es) (SubEnum.toFin-inj Es)
        (SubEnum.toFin-P Es)
        (λ g p → SubEnum.index Es g p , SubEnum.index-ok Es g p)
        q repr section q-orbit
