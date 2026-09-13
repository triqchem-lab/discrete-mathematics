{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Algebra.GroupTheory.OrbitStabilizer
-- 通用 orbit-stabilizer 定理（构造性）：|Orbit a| × |Stab a| = |G|
--
-- 数学背景:
--   有限群 G 作用于集合 X，a ∈ X。轨道-稳定子定理断言
--       |Orbit a| × |Stab a| = |G|，
--   等价于 G/Stab a ≅ Orbit a（g·Stab a ↦ g·a）。
--   本模块把它**归约到 Lagrange 定理**：Stab a 是 G 的子群，
--   而轨道映射 q 的纤维恰是 Stab a 的左陪集，于是 B1 的纤维计数直接收口。
--
-- 核心原则:
--   1. Stab a 的子群结构**由作用公理导出**（不必作为额外假设）：
--      封闭性由 ·-⊙ 给出，逆元封闭由 ·-ε/·-⊙/inverseˡ 给出；
--   2. 轨道映射 q 只须满足 q x ≡ q y ⇔ y·a ≡ x·a（分类轨道），
--      陪集判定 q x ≡ q y ⇔ x⁻¹y ∈ Stab a 由作用公理由本模块**证明**；
--   3. 0 postulate / 0 hole / 0 sorry；无 funExt（逐点等式）。
--
-- 依赖方向: Algebra.GroupTheory.Lagrange → 本模块（同层，无反向依赖）
--
-- 包含:
--   §1 Action：群作用公理
--   §2 Stab：稳定子的子群结构（由作用公理导出）
--   §3 orbit-stabilizer 主定理
--   §4 具体实例：C₄ 正则作用（|Orbit|=4, |Stab|=1）；C₄ 在 Fin 2 上的奇偶作用（|Orbit|=2, |Stab|=2）
--   §5 对抗验证：具体点 refl 交叉比对

module Sovereign.Algebra.GroupTheory.OrbitStabilizer where

open import Data.Nat using (ℕ; _*_)
open import Data.Fin using (Fin; zero; suc)
open import Data.Product using (_×_; _,_; Σ; proj₁; proj₂)
open import Data.Nat.Properties using (*-comm)
open import Function.Definitions using (Injective)
open import Function.Bundles using (_⇔_; Equivalence; mk⇔)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; module ≡-Reasoning)
open import Sovereign.Algebra.GroupTheory.Lagrange
  using (FinGroup; Subgroup; lagrange; fin1-inj;
         C4; _+4_; +4-assoc; +4-idʳ; q₂; repr₂; section₂)

open ≡-Reasoning

--------------------------------------------------------------------------------
-- §1. 群作用
--------------------------------------------------------------------------------

record Action {n : ℕ} (G : FinGroup n) (X : Set) : Set where
  open FinGroup G
  infixl 8 _·_
  field
    _·_ : Fin n → X → X
    ·-ε : ∀ x → ε · x ≡ x
    ·-⊙ : ∀ g h x → (g ⊙ h) · x ≡ g · (h · x)

--------------------------------------------------------------------------------
-- §1.1 逻辑等价（⇔）的复合
--------------------------------------------------------------------------------

⇔-comp : ∀ {A B C : Set} → A ⇔ B → B ⇔ C → A ⇔ C
⇔-comp f g = mk⇔ (λ x → Equivalence.to g (Equivalence.to f x))
                  (λ z → Equivalence.from f (Equivalence.from g z))

--------------------------------------------------------------------------------
-- §2–§3. 稳定子是子群 + orbit-stabilizer 主定理
--------------------------------------------------------------------------------

module OrbitStabilizerThm
  {n : ℕ} (G : FinGroup n) {X : Set} (A : Action G X) (a : X)
  {k m : ℕ} (hAt : Fin k → Fin n)
  (hAt-inj : Injective _≡_ _≡_ hAt)
  (stab-sound : ∀ t → Action._·_ A (hAt t) a ≡ a)
  (stab-complete : ∀ g → Action._·_ A g a ≡ a → Σ (Fin k) (λ t → hAt t ≡ g))
  (q : Fin n → Fin m) (repr : Fin m → Fin n)
  (section : ∀ r → q (repr r) ≡ r)
  (q-orbit : ∀ x y → (q x ≡ q y) ⇔ (Action._·_ A y a ≡ Action._·_ A x a))
  where

  open FinGroup G
  open Action A

  ------------------------------------------------------------------------------
  -- §2. 稳定子的子群结构（由作用公理导出，不是额外假设）
  ------------------------------------------------------------------------------

  -- 枚举元素固定在 a 上（H ⊆ Stab a）
  -- 乘法封闭: (h₁ ⊙ h₂)·a = h₁·(h₂·a) = h₁·a = a
  stab-mul : ∀ t u → (hAt t ⊙ hAt u) · a ≡ a
  stab-mul t u =
    trans (·-⊙ (hAt t) (hAt u) a)
          (trans (cong (hAt t ·_) (stab-sound u)) (stab-sound t))

  -- 逆元封闭: a = ε·a = (g⁻¹⊙g)·a = g⁻¹·(g·a) = g⁻¹·a
  stab-inv : ∀ t → inv (hAt t) · a ≡ a
  stab-inv t = sym (begin
    a                       ≡⟨ sym (·-ε a) ⟩
    ε · a                   ≡⟨ cong (_· a) (sym (inverseˡ (hAt t))) ⟩
    (inv (hAt t) ⊙ hAt t) · a ≡⟨ ·-⊙ (inv (hAt t)) (hAt t) a ⟩
    inv (hAt t) · (hAt t · a) ≡⟨ cong (inv (hAt t) ·_) (stab-sound t) ⟩
    inv (hAt t) · a         ∎)

  -- 稳定子作为子群
  Stab : Subgroup G k
  Stab = record
    { hAt = hAt
    ; hAt-inj = hAt-inj
    ; hAt-ε = stab-complete ε (·-ε a)
    ; hAt-⊙ = λ t u → stab-complete (hAt t ⊙ hAt u) (stab-mul t u)
    ; hAt-inv = λ t → stab-complete (inv (hAt t)) (stab-inv t)
    }

  -- 固定 a  ⟺  属于 Stab 的枚举
  stab-iff : ∀ z → (z · a ≡ a) ⇔ Subgroup.mem Stab z
  stab-iff z = mk⇔ (stab-complete z)
                   (λ { (t , p) → trans (sym (cong (_· a) p)) (stab-sound t) })

  ------------------------------------------------------------------------------
  -- §3. 主定理
  ------------------------------------------------------------------------------

  -- 轨道判定 ⇔ 陪集判定:
  --   (inv x ⊙ y)·a = a  ⟺  y·a = x·a
  orbit-cong : ∀ x y → (y · a ≡ x · a) ⇔ ((inv x ⊙ y) · a ≡ a)
  orbit-cong x y = mk⇔ fwd bwd
    where
      fwd : y · a ≡ x · a → (inv x ⊙ y) · a ≡ a
      fwd p = begin
        (inv x ⊙ y) · a       ≡⟨ ·-⊙ (inv x) y a ⟩
        inv x · (y · a)       ≡⟨ cong (inv x ·_) p ⟩
        inv x · (x · a)       ≡⟨ sym (·-⊙ (inv x) x a) ⟩
        (inv x ⊙ x) · a       ≡⟨ cong (_· a) (inverseˡ x) ⟩
        ε · a                 ≡⟨ ·-ε a ⟩
        a                     ∎
      bwd : (inv x ⊙ y) · a ≡ a → y · a ≡ x · a
      bwd p = begin
        y · a                     ≡⟨ sym (·-ε (y · a)) ⟩
        ε · (y · a)               ≡⟨ cong (_· (y · a)) (sym (inverseʳ x)) ⟩
        (x ⊙ inv x) · (y · a)     ≡⟨ ·-⊙ x (inv x) (y · a) ⟩
        x · (inv x · (y · a))     ≡⟨ cong (x ·_) (sym (·-⊙ (inv x) y a)) ⟩
        x · ((inv x ⊙ y) · a)     ≡⟨ cong (x ·_) p ⟩
        x · a                     ∎

  -- 由 Lagrange 得到 orbit-stabilizer: m × k ≡ n
  orbit-stabilizer : m * k ≡ n
  orbit-stabilizer =
    trans (*-comm m k)
          (sym (lagrange G Stab q repr section q-coset))
    where
      q-coset : ∀ x y → (q x ≡ q y) ⇔ Subgroup.mem Stab (inv x ⊙ y)
      q-coset x y = ⇔-comp (q-orbit x y) (⇔-comp (orbit-cong x y) (stab-iff (inv x ⊙ y)))

  -- 等价表述: n ≡ k × m
  orbit-stabilizer′ : n ≡ k * m
  orbit-stabilizer′ = trans (sym orbit-stabilizer) (*-comm m k)

--------------------------------------------------------------------------------
-- §4. 具体实例
--------------------------------------------------------------------------------

--------------------------------------------------------------------------------
-- §4.1 C₄ 在自身上的正则作用（|Orbit| = 4, |Stab| = 1）
--------------------------------------------------------------------------------

C4-regular : Action C4 (Fin 4)
C4-regular = record
  { _·_ = _+4_
  ; ·-ε = λ x → refl
  ; ·-⊙ = λ g h x → +4-assoc g h x
  }

-- 稳定子 {0}，阶 1
reg-stab : ∀ (t : Fin 1) → (Data.Fin.zero {3}) +4 (Data.Fin.zero {3}) ≡ (Data.Fin.zero {3})
reg-stab t = refl

reg-complete : ∀ g → g +4 (Data.Fin.zero {3}) ≡ (Data.Fin.zero {3})
             → Σ (Fin 1) (λ t → (Data.Fin.zero {3}) ≡ g)
reg-complete g p = Data.Fin.zero {0} , sym (trans (sym (+4-idʳ g)) p)

-- 轨道映射 = 恒等（正则作用是自由的且传递）
reg-orbit : ∀ x y → (x ≡ y) ⇔ (y +4 zero ≡ x +4 zero)
reg-orbit x y = mk⇔ to from
  where
    to : x ≡ y → y +4 zero ≡ x +4 zero
    to p = sym (cong (_+4 zero) p)
    from : y +4 zero ≡ x +4 zero → x ≡ y
    from p = sym (trans (sym (+4-idʳ y)) (trans p (+4-idʳ x)))

-- |Orbit| × |Stab| = |G|:  4 × 1 = 4
orbit-stabilizer-C4-regular : 4 * 1 ≡ 4
orbit-stabilizer-C4-regular =
  OrbitStabilizerThm.orbit-stabilizer {n = 4} C4 C4-regular zero
    (λ _ → Data.Fin.zero {3}) (fin1-inj _) reg-stab reg-complete
    (λ x → x) (λ r → r) (λ r → refl) reg-orbit

--------------------------------------------------------------------------------
-- §4.2 C₄ 在 Fin 2 上的奇偶作用（|Orbit| = 2, |Stab| = 2）—— 非平凡稳定子
--
-- 作用: g · r = q₂ g ⊕ r（q₂ = C₄ → C₂ 的商映射，⊕ = Fin 2 的加法）
-- 这是 C₄ 通过商群 C₂ 的作用；稳定子是 2 阶子群 {0,2}，轨道是全部 Fin 2。
--------------------------------------------------------------------------------

xor : Fin 2 → Fin 2 → Fin 2
xor zero r = r
xor (suc zero) zero = suc zero
xor (suc zero) (suc zero) = zero

xor-idˡ : ∀ r → xor zero r ≡ r
xor-idˡ r = refl

xor-assoc : ∀ a b r → xor (xor a b) r ≡ xor a (xor b r)
xor-assoc zero zero r = refl
xor-assoc zero (suc zero) zero = refl
xor-assoc zero (suc zero) (suc zero) = refl
xor-assoc (suc zero) zero zero = refl
xor-assoc (suc zero) zero (suc zero) = refl
xor-assoc (suc zero) (suc zero) zero = refl
xor-assoc (suc zero) (suc zero) (suc zero) = refl

-- q₂ 是群同态 C₄ → C₂（16 case refl，≤27）
q₂-hom : ∀ g h → q₂ (g +4 h) ≡ xor (q₂ g) (q₂ h)
q₂-hom zero zero = refl
q₂-hom zero (suc zero) = refl
q₂-hom zero (suc (suc zero)) = refl
q₂-hom zero (suc (suc (suc zero))) = refl
q₂-hom (suc zero) zero = refl
q₂-hom (suc zero) (suc zero) = refl
q₂-hom (suc zero) (suc (suc zero)) = refl
q₂-hom (suc zero) (suc (suc (suc zero))) = refl
q₂-hom (suc (suc zero)) zero = refl
q₂-hom (suc (suc zero)) (suc zero) = refl
q₂-hom (suc (suc zero)) (suc (suc zero)) = refl
q₂-hom (suc (suc zero)) (suc (suc (suc zero))) = refl
q₂-hom (suc (suc (suc zero))) zero = refl
q₂-hom (suc (suc (suc zero))) (suc zero) = refl
q₂-hom (suc (suc (suc zero))) (suc (suc zero)) = refl
q₂-hom (suc (suc (suc zero))) (suc (suc (suc zero))) = refl

-- 作用
act : Fin 4 → Fin 2 → Fin 2
act g r = xor (q₂ g) r

act-ε : ∀ r → act zero r ≡ r
act-ε r = refl

act-⊙ : ∀ g h r → act (g +4 h) r ≡ act g (act h r)
act-⊙ g h r = begin
  xor (q₂ (g +4 h)) r        ≡⟨ cong (λ a → xor a r) (q₂-hom g h) ⟩
  xor (xor (q₂ g) (q₂ h)) r  ≡⟨ xor-assoc (q₂ g) (q₂ h) r ⟩
  xor (q₂ g) (xor (q₂ h) r)  ∎

C4-parity : Action C4 (Fin 2)
C4-parity = record
  { _·_ = act
  ; ·-ε = act-ε
  ; ·-⊙ = act-⊙
  }

-- 稳定子 {0,2}，阶 2
stabAt : Fin 2 → Fin 4
stabAt zero = zero
stabAt (suc zero) = suc (suc zero)

stabAt-inj : Injective _≡_ _≡_ stabAt
stabAt-inj {zero} {zero} _ = refl
stabAt-inj {zero} {suc zero} ()
stabAt-inj {suc zero} {zero} ()
stabAt-inj {suc zero} {suc zero} _ = refl

par-stab : ∀ t → act (stabAt t) zero ≡ zero
par-stab zero = refl
par-stab (suc zero) = refl

par-complete : ∀ g → act g zero ≡ zero → Σ (Fin 2) (λ t → stabAt t ≡ g)
par-complete zero p = zero , refl
par-complete (suc zero) ()
par-complete (suc (suc zero)) p = suc zero , refl
par-complete (suc (suc (suc zero))) ()

-- act g zero = q₂ g（由 xor 的右单位性）
act-zero : ∀ g → act g zero ≡ q₂ g
act-zero zero = refl
act-zero (suc zero) = refl
act-zero (suc (suc zero)) = refl
act-zero (suc (suc (suc zero))) = refl

-- 轨道映射 = q₂（a = zero 时 act g zero = q₂ g）
par-orbit : ∀ x y → (q₂ x ≡ q₂ y) ⇔ (act y zero ≡ act x zero)
par-orbit x y = mk⇔ fwd bwd
  where
    fwd : q₂ x ≡ q₂ y → act y zero ≡ act x zero
    fwd p = trans (act-zero y) (trans (sym p) (sym (act-zero x)))
    bwd : act y zero ≡ act x zero → q₂ x ≡ q₂ y
    bwd p = trans (sym (act-zero x)) (trans (sym p) (act-zero y))

-- |Orbit| × |Stab| = |G|:  2 × 2 = 4
orbit-stabilizer-C4-parity : 2 * 2 ≡ 4
orbit-stabilizer-C4-parity =
  OrbitStabilizerThm.orbit-stabilizer C4 C4-parity zero
    stabAt stabAt-inj par-stab par-complete
    q₂ repr₂ section₂ par-orbit

--------------------------------------------------------------------------------
-- §5. 对抗验证：具体点 refl 交叉比对
--------------------------------------------------------------------------------

-- ① 稳定子枚举值（独立计算）
stab-values : stabAt zero ≡ zero × stabAt (suc zero) ≡ suc (suc zero)
stab-values = refl , refl

-- ② 轨道大小 2：q₂ 在 {0,1} 上取到两个不同的值（满射 ⇒ |Orbit| = 2）
orbit-hits : q₂ zero ≡ zero × q₂ (suc zero) ≡ suc zero
orbit-hits = refl , refl

-- ③ 作用的非平凡性：2 · 0 = 0（2 在稳定子中），1 · 0 = 1（1 不在）
act-2-zero : act (suc (suc zero)) zero ≡ zero
act-2-zero = refl

act-1-zero : act (suc zero) zero ≡ suc zero
act-1-zero = refl

-- ④ 定理结论与直接计算比对：2 × 2 = 4
check-parity : 2 * 2 ≡ 4
check-parity = refl

check-parity-agree : 2 * 2 ≡ 4
check-parity-agree = orbit-stabilizer-C4-parity

-- ⑤ 正则作用：|Orbit| = 4（作用是传递的：每个元素都是某个 g 的像）
reg-transitive : ∀ x → Σ (Fin 4) (λ g → g +4 zero ≡ x)
reg-transitive x = x , +4-idʳ x

-- ⑥ Lagrange 与 orbit-stabilizer 在 C₄ 上的交叉一致性：
--    正则作用给出 4 × 1 = 4，奇偶作用给出 2 × 2 = 4 —— 同一群的两条轨道分解
cross-check-C4 : (4 * 1) ≡ (2 * 2)
cross-check-C4 = refl
