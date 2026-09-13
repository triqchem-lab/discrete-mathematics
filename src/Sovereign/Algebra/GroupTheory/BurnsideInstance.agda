{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Algebra.GroupTheory.BurnsideInstance
--
-- Burnside（块 4）的**具体应用实例**与对抗验证。
--
-- 实例：C₄ 经商 Z/4 ↠ Z/2 再嵌入 2Z/4 的**平移作用**
--       t g = 2·(q₂ g) ∈ {0,2}，   act g x = x +4 t g
--   · 轨道：{0,2} 与 {1,3} —— **非传递**（2 条轨道）
--   · 稳定子：Stab x = {g | t g ≡ 0} = {0,2}，阶 2 —— **非自由**
--   · Burnside 实例：4 × 2 ≡ 8，且 Σ_x |Stab x| 独立算出 8
--
-- 为什么这个实例比块 3 的三个更有价值：
--   块 3 的实例只有 #orbits ∈ {1, 3}（传递，或平凡到每点自成一轨）。
--   本实例是**中间情形**：非传递且非自由，且 t 非零 —— 它同时压到
--   「轨道划分」「共轭拉平」「orbit-stabilizer」「纤维分解」四条链。
--
-- 踩过的坑（留作纪律）：
--   初版把 t 写成 ι(q₂ g) +4 ι(q₂ g)，直觉是「翻倍」；但在 Z/4 里 2 +4 2 = 0，
--   于是 t ≡ 0、作用退化成平凡作用、#orbits 算出 4 而非 2。
--   是 §4 的 refl 交叉验证当场挡回的 —— 这正是对抗验证存在的理由。
--
-- 核心原则：
--   1. t-hom 16 个 case（4 × 4 ≤ 27）用 refl 穷举：t 是群同态，这是 act-⊙ 的支点
--   2. act-⊙ 走代数链（+4-assoc / +4-comm / t-hom），不穷举 4 × 4 × 4 = 64 个 case
--      —— 超过 27 case 的穷举是暴力计算，不是构造性证明
--   3. §4 用独立 refl 计算与定理实例逐位比对（含**非最小元判据** idF 的验证）
--   4. 0 postulate / 0 hole；无 funExt
--
-- 包含：ι₂₄ / t / t-hom / act / act-ε / act-⊙ / C4-dbl
--       §4 dbl-numOrbits / dbl-stabCount / dbl-agree / triv-criterion /
--          triv-fix-count / triv-criterion-agree / orbRep-agree

module Sovereign.Algebra.GroupTheory.BurnsideInstance where

open import Data.Nat using (ℕ; _*_)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.Product using (Σ; _,_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; module ≡-Reasoning)

open import Sovereign.Algebra.GroupTheory.Lagrange
  using (FinGroup; C4; _+4_; +4-assoc; +4-comm; +4-idʳ; q₂)
open import Sovereign.Algebra.GroupTheory.OrbitStabilizer using (Action)
open import Sovereign.Algebra.GroupTheory.CosetAuto using (SubEnum)
open import Sovereign.Algebra.GroupTheory.Burnside using (stabCount)
open import Sovereign.Algebra.GroupTheory.OrbitPartition using (module OrbitPart)
open import Sovereign.Algebra.GroupTheory.BurnsideMain
  using (numOrbitsOf; burnside-lemma; C4-trivial)
open import Sovereign.Algebra.GroupTheory.BurnsideCriterion
  using (module CriterionFree; burnside-any-rep)

--------------------------------------------------------------------------------
-- §1. 平移作用 C₄ ↷ Fin 4
--------------------------------------------------------------------------------

-- Fin 2 ↪ Fin 4：0 ↦ 0，1 ↦ 2
ι₂₄ : Fin 2 → Fin 4
ι₂₄ fzero = fzero
ι₂₄ (fsuc fzero) = fsuc (fsuc fzero)

-- t g = 2·(q₂ g)：即 g ↦ 0,2,0,2
t : Fin 4 → Fin 4
t g = ι₂₄ (q₂ g)

-- t 是群同态 C₄ → Z/4（16 个 case，≤ 27，穷举合规）
t-hom : ∀ g h → t (g +4 h) ≡ t g +4 t h
t-hom fzero fzero = refl
t-hom fzero (fsuc fzero) = refl
t-hom fzero (fsuc (fsuc fzero)) = refl
t-hom fzero (fsuc (fsuc (fsuc fzero))) = refl
t-hom (fsuc fzero) fzero = refl
t-hom (fsuc fzero) (fsuc fzero) = refl
t-hom (fsuc fzero) (fsuc (fsuc fzero)) = refl
t-hom (fsuc fzero) (fsuc (fsuc (fsuc fzero))) = refl
t-hom (fsuc (fsuc fzero)) fzero = refl
t-hom (fsuc (fsuc fzero)) (fsuc fzero) = refl
t-hom (fsuc (fsuc fzero)) (fsuc (fsuc fzero)) = refl
t-hom (fsuc (fsuc fzero)) (fsuc (fsuc (fsuc fzero))) = refl
t-hom (fsuc (fsuc (fsuc fzero))) fzero = refl
t-hom (fsuc (fsuc (fsuc fzero))) (fsuc fzero) = refl
t-hom (fsuc (fsuc (fsuc fzero))) (fsuc (fsuc fzero)) = refl
t-hom (fsuc (fsuc (fsuc fzero))) (fsuc (fsuc (fsuc fzero))) = refl

act : Fin 4 → Fin 4 → Fin 4
act g x = x +4 t g

act-ε : ∀ x → act fzero x ≡ x
act-ε x = +4-idʳ x

-- 4 × 4 × 4 = 64 个 case 超过穷举上限，故走代数链：
--   (x + t h) + t g ≡ x + (t h + t g) ≡ x + (t g + t h) ≡ x + t (g + h)
act-⊙ : ∀ g h x → act (g +4 h) x ≡ act g (act h x)
act-⊙ g h x = sym (begin
  act g (act h x)          ≡⟨⟩
  (x +4 t h) +4 t g        ≡⟨ +4-assoc x (t h) (t g) ⟩
  x +4 (t h +4 t g)        ≡⟨ cong (x +4_) (+4-comm (t h) (t g)) ⟩
  x +4 (t g +4 t h)        ≡⟨ cong (x +4_) (sym (t-hom g h)) ⟩
  x +4 t (g +4 h)          ≡⟨⟩
  act (g +4 h) x           ∎)
  where open ≡-Reasoning

C4-dbl : Action C4 (Fin 4)
C4-dbl = record
  { _·_ = act
  ; ·-ε = act-ε
  ; ·-⊙ = act-⊙
  }

--------------------------------------------------------------------------------
-- §2. 对抗验证：具体点 refl 交叉比对
--------------------------------------------------------------------------------

-- ① 新实例：非传递（2 条轨道）+ 非自由（|Stab| = 2）
--    独立算出的 #orbits 与 Σ_x |Stab x|，与定理实例逐位一致
dbl-numOrbits : numOrbitsOf C4 C4-dbl ≡ 2
dbl-numOrbits = refl

dbl-stabCount : stabCount C4 C4-dbl ≡ 8
dbl-stabCount = refl

dbl-agree : 4 * 2 ≡ 8
dbl-agree = burnside-lemma C4 C4-dbl

-- ② 判据无关性：对**平凡作用**取 r = id（不动点 = 全部 3 点，**非最小元判据**）
idF : Fin 3 → Fin 3
idF x = x

triv-criterion : CriterionFree.IsRepCriterion C4 C4-trivial idF
triv-criterion = record
  { lands = λ x → FinGroup.ε C4 , refl
  ; const = λ {x} {y} (g , p) → p
  }

triv-fix-count : SubEnum.size (CriterionFree.FixEnum C4 C4-trivial idF) ≡ 3
triv-fix-count = refl

-- 独立算出 3，与判据无关性定理给出的一致（numOrbits 也独立算出 3）：
-- 这条说明**判据不必是最小元** —— 换判据结论不变
triv-criterion-agree : 3 ≡ 3
triv-criterion-agree =
  trans triv-fix-count
        (CriterionFree.rep-count-invariant C4 C4-trivial idF triv-criterion)

-- ③ 一致性：orbRep 判据下的推论与块 3 主定理是同一条（定义性地）
orbRep-agree : 4 * numOrbitsOf C4 C4-dbl ≡ stabCount C4 C4-dbl
orbRep-agree = burnside-any-rep C4 C4-dbl (OrbitPart.orbRep C4 C4-dbl)
                              (CriterionFree.orbRep-criterion C4 C4-dbl)
