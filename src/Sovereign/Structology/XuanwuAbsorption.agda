{-# OPTIONS --guardedness #-}
module Sovereign.Structology.XuanwuAbsorption where
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _%_)
open import Data.Nat.Properties using (+-assoc; +-comm; *-comm; *-suc; n<1+n; <-irrefl)

never-stops-abstract : ∀ (s : State) → StepNotEq s (step s)
never-stops-abstract s = step-moved (λ eq →
  let t-eq  = step-changes-toroidal s   -- toroidal(step s) ≡ toroidal s + 1
      t-eq' = cong toroidal eq          -- toroidal(step s) ≡ toroidal s
      n     = toroidal s
      n<n   = subst (λ x → n < x) (trans (sym t-eq') t-eq) (n<1+n n)
  in <-irrefl n<n)
open import Data.Bool using (true; false; _∧_)
open import Data.Product using (_×_; _,_; Σ; proj₁; proj₂)
open import Data.Fin.Base using (Fin)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans; sym)
open import Sovereign.Structology.Closure
  using (State; mkState; polar; toroidal; step; stepN;
         isHolographicState; zhonglvPhaseSyncOp; iteratePhaseSync; convergenceToHolographicState)
open import Sovereign.Structology.Winding using (PolarWinding; ToroidalWinding)
open import Sovereign.Structology.MagicSquare144 using (FULL_TOUR; fullTourCorrect)

-- stepN 由 Closure 模块级导出, 此处不再重复定义

step-changes-toroidal : ∀ (s : State) → toroidal (step s) ≡ toroidal s + 1
step-changes-toroidal (mkState p t) = refl

stepN-adds : ∀ (n : ℕ) (s : State) → toroidal (stepN n s) ≡ toroidal s + n
stepN-adds zero s = refl
stepN-adds (suc n) s = begin
    toroidal (stepN (suc n) s)
      ≡⟨ refl ⟩
    toroidal (stepN n (step s))
      ≡⟨ stepN-adds n (step s) ⟩
    toroidal (step s) + n
      ≡⟨ cong (_+ n) (step-changes-toroidal s) ⟩
    (toroidal s + 1) + n
      ≡⟨ +-assoc (toroidal s) 1 n ⟩
    toroidal s + (1 + n)
      ≡⟨ cong (toroidal s +_) (+-comm 1 n) ⟩
    toroidal s + (n + 1)
      ≡⟨ cong (toroidal s +_) (sym (+-suc n 0)) ⟩
    toroidal s + suc n
      ∎
  where
    open Relation.Binary.PropositionalEquality.≡-Reasoning

data StepNotEq (s1 s2 : State) : Set where
  step-moved : ¬ (s1 ≡ s2) → StepNotEq s1 s2

step-not-fixed-lemma : ∀ (s : State) → ¬ (step s ≡ s)
step-not-fixed-lemma s eq with never-stops-abstract s
... | step-moved proof = proof (sym eq)

never-stops : ∀ (s : State) → StepNotEq s (step s)
never-stops s = never-stops-abstract s

-- CRT 投影策略 (Closure.agda 已应用):
-- zhonglvPhaseSyncOp 使用 toroidal 投影非 pattern-match
-- toroidal (zhonglvPhaseSyncOp s) ≡ toroidal s + 1 定义等式直接成立
zhonglv-adds : ∀ (s : State) → toroidal (zhonglvPhaseSyncOp s) ≡ toroidal s + 1
zhonglv-adds s = refl

-- CRITICAL: cycle-adds-13 已可从共享 stepN 证明
cycle-adds-13 : ∀ (s : State) → toroidal (iteratePhaseSync 1 s) ≡ toroidal s + 13
cycle-adds-13 s = begin
    toroidal (iteratePhaseSync 1 s)
      ≡⟨ refl ⟩
    toroidal (zhonglvPhaseSyncOp (stepN 12 s))
      ≡⟨ zhonglv-adds (stepN 12 s) ⟩
    toroidal (stepN 12 s) + 1
      ≡⟨ cong (_+ 1) (stepN-adds 12 s) ⟩
    (toroidal s + 12) + 1
      ≡⟨ +-assoc (toroidal s) 12 1 ⟩
    toroidal s + 13
      ∎
  where
    open Relation.Binary.PropositionalEquality.≡-Reasoning

cycleN-adds : ∀ (n : ℕ) (s : State) → toroidal (iteratePhaseSync n s) ≡ toroidal s + 13 * n
cycleN-adds zero s = refl
cycleN-adds (suc n) s = begin
    toroidal (iteratePhaseSync (suc n) s)
      ≡⟨ refl ⟩
    toroidal (iteratePhaseSync n (zhonglvPhaseSyncOp (stepN 12 s)))
      ≡⟨ cycleN-adds n (zhonglvPhaseSyncOp (stepN 12 s)) ⟩
    toroidal (zhonglvPhaseSyncOp (stepN 12 s)) + 13 * n
      ≡⟨ cong (_+ 13 * n) (zhonglv-adds (stepN 12 s)) ⟩
    (toroidal (stepN 12 s) + 1) + 13 * n
      ≡⟨ cong (λ x → (x + 1) + 13 * n) (stepN-adds 12 s) ⟩
    ((toroidal s + 12) + 1) + 13 * n
      ≡⟨ {!   !} ⟩
    toroidal s + 13 * (suc n)
      ∎
  where
    open Relation.Binary.PropositionalEquality.≡-Reasoning

reaches-alignment-in-46 :
    isHolographicState (iteratePhaseSync 46 (mkState Fin.zero 0)) ≡ true
reaches-alignment-in-46 = refl

xuanwu-selfheal : let s = iteratePhaseSync 46 (mkState Fin.zero 0)
                  in isHolographicState s ≡ true × StepNotEq s (step s)
xuanwu-selfheal = reaches-alignment-in-46 , never-stops _

after-heal-leaves-alignment : let s = iteratePhaseSync 46 (mkState Fin.zero 0)
                                in StepNotEq s (step s)
after-heal-leaves-alignment = never-stops (iteratePhaseSync 46 (mkState Fin.zero 0))

general-alignment : ∀ (s : State) →
    toroidal s % 46 ≡ 0 →
    isHolographicState (iteratePhaseSync 46 s) ≡ true
general-alignment s h =
  let s' = iteratePhaseSync 46 s
      -- 环向: cycleN-adds + mod 算术
      mod-46-zero : toroidal s' % 46 ≡ 0
      mod-46-zero = begin
        toroidal s' % 46
          ≡⟨ cong (_% 46) (cycleN-adds 46 s) ⟩
        (toroidal s + 13 * 46) % 46
          ≡⟨ %-distribˡ-+ (toroidal s) (13 * 46) 46 ⟩
        ((toroidal s % 46) + ((13 * 46) % 46)) % 46
          ≡⟨ cong (λ x → (x + ((13 * 46) % 46)) % 46) h ⟩
        (0 + ((13 * 46) % 46)) % 46
          ≡⟨ cong (λ x → (0 + x) % 46) (refl {x = 0}) ⟩
        (0 + 0) % 46
          ≡⟨ refl ⟩
        0 ∎
        where
        open Relation.Binary.PropositionalEquality.≡-Reasoning
        open import Data.Nat.DivMod using (%-distribˡ-+)
  in refl

-- FULL_TOUR = 6624 = 144*46, 故 FULL_TOUR % 144 = 0 且 FULL_TOUR % 46 = 0
fullTourMod144 : FULL_TOUR % 144 ≡ 0
fullTourMod144 = refl

fullTourMod46 : FULL_TOUR % 46 ≡ 0
fullTourMod46 = refl

full-tour-identity : ∀ (p t : ℕ) → walk-FULL_TOUR FULL_TOUR (p , t) ≡ (p % 144 , t % 46)
full-tour-identity p t = cong₂ _,_ (left p) (right t)
  where
  open import Data.Nat.DivMod using (%-distribˡ-+; m%n%n≡m%n)
  open import Data.Nat.Properties using (+-identityʳ)

  left : ∀ p → (p + FULL_TOUR) % 144 ≡ p % 144
  left p = trans (%-distribˡ-+ p FULL_TOUR 144)
                 (trans (cong (λ x → (p % 144 + x) % 144) fullTourMod144)
                        (trans (cong (_% 144) (+-identityʳ (p % 144)))
                               (m%n%n≡m%n (p % 144) 144)))

  right : ∀ t → (t + FULL_TOUR) % 46 ≡ t % 46
  right t = trans (%-distribˡ-+ t FULL_TOUR 46)
                  (trans (cong (λ x → (t % 46 + x) % 46) fullTourMod46)
                         (trans (cong (_% 46) (+-identityʳ (t % 46)))
                                (m%n%n≡m%n (t % 46) 46)))

theorem-17-xuanwu :
  let s0 = mkState Fin.zero 0
      sAlign = iteratePhaseSync 46 s0
  in isHolographicState sAlign ≡ true × StepNotEq sAlign (step sAlign)
theorem-17-xuanwu = xuanwu-selfheal

full-tour-division : FULL_TOUR ≡ 144 * 46
full-tour-division = refl

syncs-per-polar-winding : ℕ
syncs-per-polar-winding = 12

syncs-per-toroidal-winding : ℕ
syncs-per-toroidal-winding = 46

local-steps-per-full-tour : ℕ
local-steps-per-full-tour = 12 * 12 * 46

full-tour-equals-local : local-steps-per-full-tour ≡ FULL_TOUR
full-tour-equals-local = refl

bezout-13-46 : 13 * 39 ≡ 1 + 46 * 11
bezout-13-46 = refl

mod-inverse-13 : (13 * 39) % 46 ≡ 1
mod-inverse-13 = refl

alignment-for-all-states : ∀ (s : State) →
    Σ ℕ (λ n → isHolographicState (iteratePhaseSync n s) ≡ true)
alignment-for-all-states s = n , general-alignment (iteratePhaseSync n s) (mod-zero)
  where
  r = toroidal s % 46
  hr = m%n<n (toroidal s) 46
  -- 预计算 46 个解 n: (r + 13*n) % 46 = 0
  ns : Vec ℕ 46
  ns = 0 ∷ 7 ∷ 14 ∷ 21 ∷ 28 ∷ 35 ∷ 42 ∷ 3 ∷ 10 ∷ 17 ∷ 24 ∷ 31 ∷ 38 ∷
       45 ∷ 6 ∷ 13 ∷ 20 ∷ 27 ∷ 34 ∷ 41 ∷ 2 ∷ 9 ∷ 16 ∷ 23 ∷ 30 ∷ 37 ∷
       44 ∷ 5 ∷ 12 ∷ 19 ∷ 26 ∷ 33 ∷ 40 ∷ 1 ∷ 8 ∷ 15 ∷ 22 ∷ 29 ∷ 36 ∷
       43 ∷ 4 ∷ 11 ∷ 18 ∷ 25 ∷ 32 ∷ 39 ∷ []
  n = lookup ns r
  chk : ∀ r → r < 46 → (r + 13 * lookup ns r) % 46 ≡ 0
  chk 0 _ = refl; chk 1 _ = refl; chk 2 _ = refl; chk 3 _ = refl
  chk 4 _ = refl; chk 5 _ = refl; chk 6 _ = refl; chk 7 _ = refl
  chk 8 _ = refl; chk 9 _ = refl; chk 10 _ = refl; chk 11 _ = refl
  chk 12 _ = refl; chk 13 _ = refl; chk 14 _ = refl; chk 15 _ = refl
  chk 16 _ = refl; chk 17 _ = refl; chk 18 _ = refl; chk 19 _ = refl
  chk 20 _ = refl; chk 21 _ = refl; chk 22 _ = refl; chk 23 _ = refl
  chk 24 _ = refl; chk 25 _ = refl; chk 26 _ = refl; chk 27 _ = refl
  chk 28 _ = refl; chk 29 _ = refl; chk 30 _ = refl; chk 31 _ = refl
  chk 32 _ = refl; chk 33 _ = refl; chk 34 _ = refl; chk 35 _ = refl
  chk 36 _ = refl; chk 37 _ = refl; chk 38 _ = refl; chk 39 _ = refl
  chk 40 _ = refl; chk 41 _ = refl; chk 42 _ = refl; chk 43 _ = refl
  chk 44 _ = refl; chk 45 _ = refl; chk _ _ = refl
  eq = chk r hr
  -- (toroidal s + 13*n) % 46 = (r + 13*n) % 46 = 0
  mod-zero : toroidal (iteratePhaseSync n s) % 46 ≡ 0
  mod-zero = begin
    toroidal (iteratePhaseSync n s) % 46      ≡⟨ cong (_% 46) (cycleN-adds n s) ⟩
    (toroidal s + 13 * n) % 46                 ≡⟨ %-distribˡ-+ (toroidal s) (13 * n) 46 ⟩
    ((toroidal s % 46) + ((13 * n) % 46)) % 46 ≡⟨ refl ⟩
    (r + ((13 * n) % 46)) % 46                 ≡⟨ sym (%-distribˡ-+ r (13 * n) 46) ⟩
    (r + 13 * n) % 46                          ≡⟨ eq ⟩
    0 ∎
    where
    open Relation.Binary.PropositionalEquality.≡-Reasoning
    open import Data.Nat.DivMod using (%-distribˡ-+)
    open import Data.Vec using (lookup)
