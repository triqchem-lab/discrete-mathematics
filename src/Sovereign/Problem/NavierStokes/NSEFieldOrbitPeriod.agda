{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Problem.NavierStokes.NSEFieldOrbitPeriod
-- **supportCount 轨道的无条件最终周期**（⑤ 收官·真·最后一件）
--
-- 主定理（本模块）:
--   `supportCount-orbit-period`：∀ v → ∃ s p → ∀ n →
--     supportCount (orbit nsStep v (s + n + p)) ≡ supportCount (orbit nsStep v (s + n))
--   ——**无条件**（不再依赖 EventuallyPeriodic 见证）⇒ 无漂移型集中**无条件成立**。
--
-- 证明路线（零件盘点见流水 257）:
--   ① 槽位管道 `slotOf/slotAt : Fin 4374 ↔ Fin 6 × Torus6`（6 × 729 = 4374 槽；
--      splitAt/inject+/raise 纯 stdlib 组合子 + NSEPresentation 的 encodePt/decodePt-encodePt）
--   ② 数字嵌入 `Trit ↪ Fin 12`（tritToFin3 + `PairEnc.pairEnc : Fin 3 × Fin 4 → Fin 12`）
--   ③ 混合基数编码 `enc12 4374`（FinMixedRadix，逐点注入 `enc12-inj-pointwise` 已证）
--   ④ `finite-orbit-obs`（Analysis.FiniteOrbitObs，上批交付）+ nsStep 的观察逐点性
--   ⑤ supportCount-ext（NSESupportFixedInv）把逐点周期投影成计数周期
--
-- 诚实边界: 观察值层结论（本库无 funExt；状态相等不可达）；存在性证明（非算法——
--   界 12^4374 用 abstract 封装，避免归一化爆炸，承 NSEFinalClosure §3 的承重经验）。
--
-- 0 postulate / 0 hole。

module Sovereign.Problem.NavierStokes.NSEFieldOrbitPeriod where

open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _^_; _≤_; _<_; z≤n; s≤s)
open import Data.Nat.Properties using (+-mono-≤; *-mono-≤; ≤-refl)
open import Data.Fin using (Fin; toℕ; fromℕ<; inject+; raise; splitAt)
  renaming (zero to fzero; suc to fsuc)
open import Data.Fin.Properties using (toℕ-injective; toℕ-fromℕ<; toℕ<n; splitAt-inject+; splitAt-raise)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_×_; _,_; Σ; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; cong₂; trans; sym)

open import Sovereign.Base.Trit using (Trit; T₀; T₁; T₂; _⊕_; negate; fin3ToTrit)
open import Sovereign.Analysis.PairEnc using (pairEnc; pairEnc-injective)
open import Sovereign.Analysis.FinMixedRadix using (enc12; enc12-inj-pointwise; suc≤12)
open import Sovereign.Analysis.FiniteDynamics using (orbit)
open import Sovereign.Analysis.FiniteOrbitObs using (finite-orbit-obs)
open import Sovereign.Problem.NavierStokes.NSEPresentation using
  (decodePt; encodePt; decodePt-encodePt)
open import Sovereign.Problem.NavierStokes.NSEOnT6 using
  (C3; Torus6; ScalarField; Field; v1; v2; v3; v4; v5; v6;
   sum6; shiftAt; diffF; _+S_; _+F_; div; grad; nsStep)
open import Sovereign.Problem.NavierStokes.NSEFixedPoint using (comp; axisOf)
open import Sovereign.Problem.NavierStokes.NSEFixedPointStrict using (supportCount)
open import Sovereign.Problem.NavierStokes.NSEConservation using (sum6-cong)
open import Sovereign.Problem.NavierStokes.NSESupportFixedInv using (supportCount-ext)

--------------------------------------------------------------------------------
-- §1. 槽位管道: Fin 4374 ↔ Fin 6 × Torus6（6 × 729）
--------------------------------------------------------------------------------

-- 正向: 6 个 729-块。**显式 lvl 具名**（不用 with/rewrite——with-reduce 会撞
-- `fromℕ<` 证明项的 K-禁用合一问题；cong 链 + 普通模式匹配则完全避开）
lvl1 : Fin 729 Data.Sum.⊎ Fin 3645 → Fin 6 × Torus6
lvl2 : Fin 729 Data.Sum.⊎ Fin 2916 → Fin 6 × Torus6
lvl3 : Fin 729 Data.Sum.⊎ Fin 2187 → Fin 6 × Torus6
lvl4 : Fin 729 Data.Sum.⊎ Fin 1458 → Fin 6 × Torus6
lvl5 : Fin 729 Data.Sum.⊎ Fin 729 → Fin 6 × Torus6

lvl1 (inj₁ r) = fzero , decodePt r
lvl1 (inj₂ j) = lvl2 (splitAt 729 j)

lvl2 (inj₁ r) = fsuc fzero , decodePt r
lvl2 (inj₂ j) = lvl3 (splitAt 729 j)

lvl3 (inj₁ r) = fsuc (fsuc fzero) , decodePt r
lvl3 (inj₂ j) = lvl4 (splitAt 729 j)

lvl4 (inj₁ r) = fsuc (fsuc (fsuc fzero)) , decodePt r
lvl4 (inj₂ j) = lvl5 (splitAt 729 j)

lvl5 (inj₁ r) = fsuc (fsuc (fsuc (fsuc fzero))) , decodePt r
lvl5 (inj₂ r) = fsuc (fsuc (fsuc (fsuc (fsuc fzero)))) , decodePt r

slotAt : Fin 4374 → Fin 6 × Torus6
slotAt i = lvl1 (splitAt 729 i)

-- 反向: 块偏移 + encodePt
slotOf : Fin 6 × Torus6 → Fin 4374
slotOf (fzero , x)                                     = inject+ 3645 (encodePt x)
slotOf (fsuc fzero , x)                                = raise 729 (inject+ 2916 (encodePt x))
slotOf (fsuc (fsuc fzero) , x)                         = raise 1458 (inject+ 2187 (encodePt x))
slotOf (fsuc (fsuc (fsuc fzero)) , x)                  = raise 2187 (inject+ 1458 (encodePt x))
slotOf (fsuc (fsuc (fsuc (fsuc fzero))) , x)           = raise 2916 (inject+ 729 (encodePt x))
slotOf (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))) , x)    = raise 3645 (encodePt x)

-- 往返（见证方向: slotAt ∘ slotOf ≡ id）——注入性论证只需这一侧
-- 纯 `cong` 链（无 rewrite/with）：绕开 `fromℕ<` 证明项的 K-禁用合一问题
slotAt-slotOf : ∀ k x → slotAt (slotOf (k , x)) ≡ (k , x)
slotAt-slotOf fzero x =
  trans (cong lvl1 (splitAt-inject+ 729 3645 (encodePt x)))
        (cong (fzero ,_) (decodePt-encodePt x))
slotAt-slotOf (fsuc fzero) x =
  trans (cong lvl1 (splitAt-raise 729 3645 (inject+ 2916 (encodePt x))))
  (trans (cong lvl2 (splitAt-inject+ 729 2916 (encodePt x)))
         (cong (fsuc fzero ,_) (decodePt-encodePt x)))
slotAt-slotOf (fsuc (fsuc fzero)) x =
  trans (cong lvl1 (splitAt-raise 729 3645 (raise 729 (inject+ 2187 (encodePt x)))))
  (trans (cong lvl2 (splitAt-raise 729 2916 (inject+ 2187 (encodePt x))))
  (trans (cong lvl3 (splitAt-inject+ 729 2187 (encodePt x)))
         (cong (fsuc (fsuc fzero) ,_) (decodePt-encodePt x))))
slotAt-slotOf (fsuc (fsuc (fsuc fzero))) x =
  trans (cong lvl1 (splitAt-raise 729 3645 (raise 1458 (inject+ 1458 (encodePt x)))))
  (trans (cong lvl2 (splitAt-raise 729 2916 (raise 729 (inject+ 1458 (encodePt x)))))
  (trans (cong lvl3 (splitAt-raise 729 2187 (inject+ 1458 (encodePt x))))
  (trans (cong lvl4 (splitAt-inject+ 729 1458 (encodePt x)))
         (cong (fsuc (fsuc (fsuc fzero)) ,_) (decodePt-encodePt x)))))
slotAt-slotOf (fsuc (fsuc (fsuc (fsuc fzero)))) x =
  trans (cong lvl1 (splitAt-raise 729 3645 (raise 2187 (inject+ 729 (encodePt x)))))
  (trans (cong lvl2 (splitAt-raise 729 2916 (raise 1458 (inject+ 729 (encodePt x)))))
  (trans (cong lvl3 (splitAt-raise 729 2187 (raise 729 (inject+ 729 (encodePt x)))))
  (trans (cong lvl4 (splitAt-raise 729 1458 (inject+ 729 (encodePt x))))
  (trans (cong lvl5 (splitAt-inject+ 729 729 (encodePt x)))
         (cong (fsuc (fsuc (fsuc (fsuc fzero))) ,_) (decodePt-encodePt x))))))
slotAt-slotOf (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))) x =
  trans (cong lvl1 (splitAt-raise 729 3645 (raise 2916 (encodePt x))))
  (trans (cong lvl2 (splitAt-raise 729 2916 (raise 2187 (encodePt x))))
  (trans (cong lvl3 (splitAt-raise 729 2187 (raise 1458 (encodePt x))))
  (trans (cong lvl4 (splitAt-raise 729 1458 (raise 729 (encodePt x))))
  (trans (cong lvl5 (splitAt-raise 729 729 (encodePt x)))
         (cong (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))) ,_) (decodePt-encodePt x))))))

--------------------------------------------------------------------------------
-- §2. 数字嵌入: Trit ↪ Fin 12（经 Fin 3 × Fin 4）
--------------------------------------------------------------------------------

tritToFin3 : Trit → Fin 3
tritToFin3 T₀ = fzero
tritToFin3 T₁ = fsuc fzero
tritToFin3 T₂ = fsuc (fsuc fzero)

fin3ToTrit-tritToFin3 : ∀ t → fin3ToTrit (tritToFin3 t) ≡ t
fin3ToTrit-tritToFin3 T₀ = refl
fin3ToTrit-tritToFin3 T₁ = refl
fin3ToTrit-tritToFin3 T₂ = refl

tritToFin3-inj : ∀ {a b : Trit} → tritToFin3 a ≡ tritToFin3 b → a ≡ b
tritToFin3-inj {a} {b} eq =
  trans (sym (fin3ToTrit-tritToFin3 a))
  (trans (cong fin3ToTrit eq) (fin3ToTrit-tritToFin3 b))

look : Field → Fin 6 × Torus6 → Trit
look v (k , x) = comp k v x

dig : Field → Fin 4374 → Fin 12
dig v i = pairEnc (tritToFin3 (look v (slotAt i)) , fzero)

--------------------------------------------------------------------------------
-- §3. 编码与逐点注入性（abstract 界，承 NSEFinalClosure §3 承重经验）
--------------------------------------------------------------------------------

abstract
  N4374 : ℕ
  N4374 = 12 ^ 4374

  fieldEnc : Field → Fin N4374
  fieldEnc v = fromℕ< {enc12 4374 (dig v)} {12 ^ 4374} (suc≤12 4374 (dig v))

  toℕ-fieldEnc : ∀ v → toℕ (fieldEnc v) ≡ enc12 4374 (dig v)
  toℕ-fieldEnc v = toℕ-fromℕ< _

  fieldEnc-inj :
    ∀ {s t : Field} → fieldEnc s ≡ fieldEnc t → ∀ k x → comp k s x ≡ comp k t x
  fieldEnc-inj {s} {t} eq k x = tritToFin3-inj (cong proj₁ (pairEnc-injective (tritToFin3 (comp k s x) , fzero) (tritToFin3 (comp k t x) , fzero) step₂))
    where
      step₀ : enc12 4374 (dig s) ≡ enc12 4374 (dig t)
      step₀ = trans (sym (toℕ-fieldEnc s)) (trans (cong toℕ eq) (toℕ-fieldEnc t))
      step₁ : ∀ i → dig s i ≡ dig t i
      step₁ = enc12-inj-pointwise 4374 (dig s) (dig t) step₀
      step₂ : pairEnc (tritToFin3 (comp k s x) , fzero) ≡ pairEnc (tritToFin3 (comp k t x) , fzero)
      step₂ =
        trans (sym (cong (λ z → pairEnc (tritToFin3 (look s z) , fzero)) (slotAt-slotOf k x)))
        (trans (step₁ (slotOf (k , x)))
               (cong (λ z → pairEnc (tritToFin3 (look t z) , fzero)) (slotAt-slotOf k x)))

--------------------------------------------------------------------------------

diffF-ext : ∀ {f g : ScalarField} i → (∀ y → f y ≡ g y) → ∀ x → diffF i f x ≡ diffF i g x
diffF-ext i p x = cong₂ _⊕_ (p (shiftAt i x)) (cong negate (p x))

div-ext : ∀ {s t : Field} → (∀ k x → comp k s x ≡ comp k t x) →
  ∀ x → div s x ≡ div t x
div-ext {s} {t} p x =
  sum6-cong
    (diffF-ext fzero (p fzero) x)
    (diffF-ext (fsuc fzero) (p (fsuc fzero)) x)
    (diffF-ext (fsuc (fsuc fzero)) (p (fsuc (fsuc fzero))) x)
    (diffF-ext fzero (p (fsuc (fsuc (fsuc fzero)))) x)
    (diffF-ext (fsuc fzero) (p (fsuc (fsuc (fsuc (fsuc fzero))))) x)
    (diffF-ext (fsuc (fsuc fzero)) (p (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))) x)

nsStep-pw : ∀ {s t : Field} → (∀ k x → comp k s x ≡ comp k t x) →
  ∀ k x → comp k (nsStep s) x ≡ comp k (nsStep t) x
nsStep-pw {s} {t} p fzero x =
  cong₂ _⊕_ (p fzero x) (diffF-ext fzero (div-ext p) x)
nsStep-pw {s} {t} p (fsuc fzero) x =
  cong₂ _⊕_ (p (fsuc fzero) x) (diffF-ext (fsuc fzero) (div-ext p) x)
nsStep-pw {s} {t} p (fsuc (fsuc fzero)) x =
  cong₂ _⊕_ (p (fsuc (fsuc fzero)) x) (diffF-ext (fsuc (fsuc fzero)) (div-ext p) x)
nsStep-pw {s} {t} p (fsuc (fsuc (fsuc fzero))) x =
  cong₂ _⊕_ (p (fsuc (fsuc (fsuc fzero))) x) (diffF-ext fzero (div-ext p) x)
nsStep-pw {s} {t} p (fsuc (fsuc (fsuc (fsuc fzero)))) x =
  cong₂ _⊕_ (p (fsuc (fsuc (fsuc (fsuc fzero)))) x) (diffF-ext (fsuc fzero) (div-ext p) x)
nsStep-pw {s} {t} p (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))) x =
  cong₂ _⊕_ (p (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))) x) (diffF-ext (fsuc (fsuc fzero)) (div-ext p) x)

--------------------------------------------------------------------------------
-- §5. 实例化: 轨道逐点周期 + supportCount 无条件周期
--------------------------------------------------------------------------------

obs6 : Field → Fin 6 × Torus6 → Trit
obs6 v i = comp (proj₁ i) v (proj₂ i)

-- 全场轨道的**逐点**最终周期（无条件）
field-orbit-period : ∀ (v : Field) →
  Σ ℕ (λ s → Σ ℕ (λ p → ∀ n k x →
    comp k (orbit nsStep v (s + n + p)) x ≡ comp k (orbit nsStep v (s + n)) x))
field-orbit-period v =
  proj₁ pack , proj₁ (proj₂ pack) , (λ n k x → proj₂ (proj₂ pack) n (k , x))
  where
    pack : Σ ℕ (λ s → Σ ℕ (λ p → ∀ n i →
      obs6 (orbit nsStep v (s + n + p)) i ≡ obs6 (orbit nsStep v (s + n)) i))
    pack = finite-orbit-obs N4374 fieldEnc obs6
             (λ {s} {t} eq i → fieldEnc-inj eq (proj₁ i) (proj₂ i))
             nsStep
             (λ {s} {t} p i → nsStep-pw (λ k x → p (k , x)) (proj₁ i) (proj₂ i))
             v

-- **主定理**: supportCount 轨道无条件最终周期 ⇒ 无漂移型集中（无条件）
supportCount-orbit-period : ∀ (v : Field) →
  Σ ℕ (λ s → Σ ℕ (λ p → ∀ n →
    supportCount (orbit nsStep v (s + n + p)) ≡ supportCount (orbit nsStep v (s + n))))
supportCount-orbit-period v =
  s , p , (λ n → supportCount-ext _ _ (λ k x → per n k x))
  where
    s : ℕ
    s = proj₁ (field-orbit-period v)
    p : ℕ
    p = proj₁ (proj₂ (field-orbit-period v))
    per : ∀ n k x →
      comp k (orbit nsStep v (s + n + p)) x ≡ comp k (orbit nsStep v (s + n)) x
    per = proj₂ (proj₂ (field-orbit-period v))

--------------------------------------------------------------------------------
-- 诚实边界
--
-- ✓: §1 槽位管道往返、§2 数字嵌入注入、§3 编码逐点注入（abstract 界）、
--   §4 nsStep 观察逐点性、**§5 主定理（supportCount 轨道无条件最终周期）**。
-- ✗: 观察值层结论（本库无 funExt，状态相等不可达）；存在性证明（界 12^4374
--   不可归一化求值，承 NSEFinalClosure §3 承重经验）；周期 p 的界未刻画。
--------------------------------------------------------------------------------
