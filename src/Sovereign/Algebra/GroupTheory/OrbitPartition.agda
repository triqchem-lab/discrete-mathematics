{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Algebra.GroupTheory.OrbitPartition
--
-- 有限作用的**轨道划分**与**最小代表元**（Burnside 块 3 第 1–2 步）。
--
-- 数学背景：
--   有限群 G : FinGroup n 作用在有限集 X = Fin p。定义轨道关系
--       orbEq y x  :=  Σ (Fin n) (λ g → g · y ≡ x)      -- x 经 G 作用可达 y
--   它自反（ε）、对称（g⁻¹）、传递（复合），并且**可判定**（searchFin 枚举群元）。
--   轨道是等价类，于是有**唯一**的 toℕ 最小元 orbRep x —— 代表元的唯一性与可判定性
--   就是本模块的两条主线。
--
-- 核心原则：
--   1. **结构性最小搜索**：最小性用 firstIn（对界 ℕ 结构递归）证明，不用 searchFin
--      的返回结构。根因见 prover_limits: agda-empty-goal-ton-stuck（沿用
--      CosetConstruction §3 已闭合的路线，本模块是它的同构复刻：陪集 → 轨道）
--   2. **代表元唯一性靠幂等**：orbRep-idem（orbRep (orbRep x) ≡ orbRep x）由
--      orbRep-min 的两侧夹逼 + ≤-antisym 得到，纯算术，无新数学
--   3. **标签纤维 = 轨道**：fiberSize orbLabel y ≡ |Orbit (toFin RepEnum y)|。
--      这是 Burnside 组装里唯一需要基数搬运的一步；用 stdlib 的
--      cantor-schröder-bernstein（两向单射 ⇒ 基数相等）收口，不自己写计数
--   4. 0 postulate / 0 hole；无 funExt（全部是等式）；不对相位/时钟作任何断言
--
-- 诚实边界：
--   结论里 #orbits 有限，故作用必须取在**有限集 Fin p** 上——本模块不声称无限作用。
--   代表元是「轨道内 toℕ 最小元」，这是**判据**的选择，不是数学内容；
--   换任何可判定判据得到的 #orbits 相同（本模块不证这一点）。
--
-- 包含：
--   §2a orbEq / orbEq-dec / orbEq-refl / orbEq-sym / orbEq-trans
--   §2b orbMemIdx / orbRep-core / orbRep / orbRep-eq / orbRep-min / orbRep-idem /
--       orbRep-eq-of-eq
--   §2c isRep / RepEnum / numOrbits / orbLabel / orbLabel-ok / orbLabel-cong
--   §2d orbEnum / fiberSizeEqOrbit

module Sovereign.Algebra.GroupTheory.OrbitPartition where

open import Data.Nat using (ℕ; _<_; _≤_; z≤n; s≤s; _+_; _*_; zero; suc)
open import Data.Nat.Properties using (≤-refl; ≤-trans; ≤-antisym; ≤-total; _<?_; *-comm)
open import Data.Fin using (Fin; toℕ; fromℕ<) renaming (zero to fzero; suc to fsuc)
open import Data.Fin.Properties using (_≟_; toℕ-injective; toℕ<n; toℕ-fromℕ<;
                                      cantor-schröder-bernstein)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Function.Definitions using (Injective)
open import Relation.Nullary.Decidable using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; subst; module ≡-Reasoning)

open import Sovereign.Algebra.GroupTheory.Lagrange using (FinGroup)
open import Sovereign.Algebra.GroupTheory.OrbitStabilizer using (Action)
open import Sovereign.Algebra.GroupTheory.CosetConstruction using (firstIn)
open import Sovereign.Algebra.GroupTheory.CosetAuto using (SubEnum; enum; index-cong)
open import Sovereign.Algebra.GroupTheory.BurnsideFiber using (fiberSize)
open import Sovereign.Algebra.Holographic.4320DClosure using (searchFin)

module OrbitPart {n p : ℕ} (G : FinGroup n) (A : Action G (Fin p)) where
  open FinGroup G
  open Action A
  open ≡-Reasoning

  ------------------------------------------------------------------------------
  -- §2a. 轨道关系与等价关系（第 1 步）
  ------------------------------------------------------------------------------

  orbEq : Fin p → Fin p → Set
  orbEq y x = Σ (Fin n) (λ g → g · y ≡ x)

  orbEq-dec : ∀ y x → Dec (orbEq y x)
  orbEq-dec y x = searchFin (λ g → g · y ≡ x) (λ g → g · y ≟ x)

  orbEq-refl : ∀ x → orbEq x x
  orbEq-refl x = ε , ·-ε x

  orbEq-sym : ∀ {x y} → orbEq y x → orbEq x y
  orbEq-sym {x} {y} (g , pg) = inv g , (begin
    inv g · x        ≡⟨ cong (inv g ·_) (sym pg) ⟩
    inv g · (g · y)  ≡⟨ sym (·-⊙ (inv g) g y) ⟩
    (inv g ⊙ g) · y  ≡⟨ cong (_· y) (inverseˡ g) ⟩
    ε · y            ≡⟨ ·-ε y ⟩
    y                ∎)

  orbEq-trans : ∀ {x y z} → orbEq z y → orbEq y x → orbEq z x
  orbEq-trans {x} {y} {z} (g , pg) (h , ph) = (h ⊙ g) , (begin
    (h ⊙ g) · z  ≡⟨ ·-⊙ h g z ⟩
    h · (g · z)  ≡⟨ cong (h ·_) pg ⟩
    h · y        ≡⟨ ph ⟩
    x            ∎)

  ------------------------------------------------------------------------------
  -- §2b. 轨道内 toℕ 最小代表元（第 2 步）
  ------------------------------------------------------------------------------

  orbMemIdx : Fin p → ℕ → Set
  orbMemIdx x i = Σ (i < p) (λ i<p → orbEq (fromℕ< {i} {p} i<p) x)

  orbMemIdx-dec : ∀ x i → Dec (orbMemIdx x i)
  orbMemIdx-dec x i with i <? p
  ... | yes i<p = fromEq (orbEq-dec (fromℕ< {i} {p} i<p) x)
    where
      fromEq : Dec (orbEq (fromℕ< {i} {p} i<p) x) → Dec (orbMemIdx x i)
      fromEq (yes q) = yes (i<p , q)
      fromEq (no ¬q) = no (λ (_ , q) → ¬q q)
  ... | no ¬i<p = no (λ (i<p , _) → ¬i<p i<p)

  -- x 自身就是界 toℕ x 处的见证（取单位元）
  witness-x : ∀ x → orbMemIdx x (toℕ x)
  witness-x x = toℕ<n x ,
    subst (λ j → orbEq j x)
          (sym (toℕ-injective (toℕ-fromℕ< (toℕ<n x))))
          (orbEq-refl x)

  -- 最小元的「核心」：界内最小 + 见证恰在界上
  orbRep-core : ∀ x → Σ ℕ (λ k → k ≤ toℕ x × orbMemIdx x k
                              × (∀ m → m ≤ toℕ x → orbMemIdx x m → k ≤ m))
  orbRep-core x with firstIn (orbMemIdx x) (orbMemIdx-dec x) (toℕ x)
  ... | inj₁ (k , (k≤t , (pk , min))) = k , (k≤t , (pk , min))
  ... | inj₂ none = ⊥-elim (none (toℕ x) ≤-refl (witness-x x))

  orbRep : Fin p → Fin p
  orbRep x with orbRep-core x
  ... | k , (_ , ((k<p , _) , _)) = fromℕ< {k} {p} k<p

  orbRep-eq : ∀ x → orbEq (orbRep x) x
  orbRep-eq x with orbRep-core x
  ... | k , (_ , ((k<p , q) , _)) = q

  orb-min-global : ∀ (P : ℕ → Set) {k t i : ℕ}
                 → k ≤ t → (∀ m → m ≤ t → P m → k ≤ m)
                 → (i ≤ t) ⊎ (t ≤ i) → P i → k ≤ i
  orb-min-global P {i = i} k≤t min (inj₁ i≤t) qi = min i i≤t qi
  orb-min-global P k≤t min (inj₂ t≤i) qi = ≤-trans k≤t t≤i

  orbRep-min : ∀ x i → orbEq i x → toℕ (orbRep x) ≤ toℕ i
  orbRep-min x i q with orbRep-core x
  ... | k , (k≤t , (_ , min)) =
        subst (λ z → z ≤ toℕ i)
              (sym (toℕ-fromℕ< {m = k} {n = p} _))
              (orb-min-global (orbMemIdx x) k≤t min (≤-total (toℕ i) (toℕ x))
                              (toℕ<n i ,
                               subst (λ j → orbEq j x)
                                     (sym (toℕ-injective (toℕ-fromℕ< (toℕ<n i))))
                                     q))

  -- 幂等：代表元的代表元还是自己（唯一性）
  orbRep-idem : ∀ x → orbRep (orbRep x) ≡ orbRep x
  orbRep-idem x = toℕ-injective (≤-antisym lo hi)
    where
      lo : toℕ (orbRep (orbRep x)) ≤ toℕ (orbRep x)
      lo = orbRep-min (orbRep x) (orbRep x) (orbEq-refl (orbRep x))
      hi : toℕ (orbRep x) ≤ toℕ (orbRep (orbRep x))
      hi = orbRep-min x (orbRep (orbRep x))
             (orbEq-trans (orbRep-eq (orbRep x)) (orbRep-eq x))

  -- 同轨道 ⇒ 同代表元
  orbRep-eq-of-eq : ∀ {x y} → orbEq x y → orbRep x ≡ orbRep y
  orbRep-eq-of-eq {x} {y} q =
    sym (toℕ-injective (≤-antisym
      (orbRep-min y (orbRep x) (orbEq-trans (orbRep-eq x) q))
      (orbRep-min x (orbRep y) (orbEq-trans (orbRep-eq y) (orbEq-sym q)))))

  ------------------------------------------------------------------------------
  -- §2c. 轨道标签（不动代表元枚举 + 标签映射）
  ------------------------------------------------------------------------------

  isRep : Fin p → Set
  isRep x = orbRep x ≡ x

  isRep-dec : ∀ x → Dec (isRep x)
  isRep-dec x = orbRep x ≟ x

  RepEnum : SubEnum p isRep
  RepEnum = enum isRep isRep-dec

  numOrbits : ℕ
  numOrbits = SubEnum.size RepEnum

  orbLabel : Fin p → Fin numOrbits
  orbLabel x = SubEnum.index RepEnum (orbRep x) (orbRep-idem x)

  orbLabel-ok : ∀ x → SubEnum.toFin RepEnum (orbLabel x) ≡ orbRep x
  orbLabel-ok x = SubEnum.index-ok RepEnum (orbRep x) (orbRep-idem x)

  -- 走 toFin-inj 而不是 index-cong：后者要从 orbRep ? ≡ orbRep ? 反解隐式参数，
  -- 而 orbRep 是定义（Agda 不反演），会留下未解元变量。
  orbLabel-cong : ∀ {x y} → orbRep x ≡ orbRep y → orbLabel x ≡ orbLabel y
  orbLabel-cong {x} {y} e =
    SubEnum.toFin-inj RepEnum
      (trans (orbLabel-ok x) (trans e (sym (orbLabel-ok y))))

  ------------------------------------------------------------------------------
  -- §2d. 标签纤维 = 轨道（第 3 步的承重半）
  ------------------------------------------------------------------------------

  orbEnum : (r : Fin p) → SubEnum p (orbEq r)
  orbEnum r = enum (orbEq r) (orbEq-dec r)

  -- |{x | orbLabel x ≡ y}| ≡ |Orbit (toFin RepEnum y)|
  -- 两侧都作为 Fin p 的子类型，用 CSB 收口（不自己写基数搬运）
  fiberSizeEqOrbit : ∀ (y : Fin numOrbits)
                   → fiberSize orbLabel y
                   ≡ SubEnum.size (orbEnum (SubEnum.toFin RepEnum y))
  fiberSizeEqOrbit y = sym (cantor-schröder-bernstein {f = φ} {g = ψ} φ-inj ψ-inj)
    where
      r : Fin p
      r = SubEnum.toFin RepEnum y

      r-rep : isRep r
      r-rep = SubEnum.toFin-P RepEnum y

      Efib : SubEnum p (λ x → y ≡ orbLabel x)
      Efib = enum (λ x → y ≡ orbLabel x) (λ x → y ≟ orbLabel x)

      Eorb : SubEnum p (orbEq r)
      Eorb = orbEnum r

      -- 不动代表元的标签就是它自己
      label-r : orbLabel r ≡ y
      label-r = SubEnum.toFin-inj RepEnum (trans (orbLabel-ok r) r-rep)

      toFib : ∀ x → orbEq r x → (y ≡ orbLabel x)
      toFib x h = sym (trans (orbLabel-cong {x} {r}
                                            (sym (orbRep-eq-of-eq {r} {x} h)))
                               label-r)

      toOrb : ∀ x → (y ≡ orbLabel x) → orbEq r x
      toOrb x e =
        subst (λ z → orbEq z x)
              (trans (sym (orbLabel-ok x))
                     (sym (cong (SubEnum.toFin RepEnum) e)))
              (orbRep-eq x)

      φ : Fin (SubEnum.size Eorb) → Fin (SubEnum.size Efib)
      φ i = SubEnum.index Efib (SubEnum.toFin Eorb i)
                             (toFib (SubEnum.toFin Eorb i) (SubEnum.toFin-P Eorb i))

      ψ : Fin (SubEnum.size Efib) → Fin (SubEnum.size Eorb)
      ψ j = SubEnum.index Eorb (SubEnum.toFin Efib j)
                             (toOrb (SubEnum.toFin Efib j) (SubEnum.toFin-P Efib j))

      φ-toFin : ∀ i → SubEnum.toFin Efib (φ i) ≡ SubEnum.toFin Eorb i
      φ-toFin i = SubEnum.index-ok Efib _ _

      ψ-toFin : ∀ j → SubEnum.toFin Eorb (ψ j) ≡ SubEnum.toFin Efib j
      ψ-toFin j = SubEnum.index-ok Eorb _ _

      φ-inj : Injective _≡_ _≡_ φ
      φ-inj {i} {j} eq =
        SubEnum.toFin-inj Eorb
          (trans (sym (φ-toFin i))
                 (trans (cong (SubEnum.toFin Efib) eq) (φ-toFin j)))

      ψ-inj : Injective _≡_ _≡_ ψ
      ψ-inj {i} {j} eq =
        SubEnum.toFin-inj Efib
          (trans (sym (ψ-toFin i))
                 (trans (cong (SubEnum.toFin Eorb) eq) (ψ-toFin j)))

--------------------------------------------------------------------------------
-- 顶层入口
--------------------------------------------------------------------------------

numOrbitsOf : ∀ {n p} (G : FinGroup n) (A : Action G (Fin p)) → ℕ
numOrbitsOf G A = OrbitPart.numOrbits G A
