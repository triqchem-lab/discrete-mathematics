{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Algebra.LinearAlgebra.GF3Barrier
-- 系数表示下的**壁垒定理**准备工作（T4，2026-10-20）
--
-- 数学内容
--   `CoeffN n = Torus n → Trit` 是**系数函数**：`p a` = 单项式 `x^a` 的系数。
--   乘 `x_i²` 在系数表示下是**索引回退**：`(x_i²·p)(b) = p(b 的第 i 坐标减 2)`，
--   越界（第 i 坐标 < 2）时为 0 ⇒ **截断自动** ✓
--
-- 壁垒（人类给出的纯组合证明）
--   若 `p ≠ 0` 且 `p b ≠ 0 ⇒ b_i = 0`（支撑避开坐标 i），则 `Σ_j x_j²·p ≠ 0`。
--   证：取 `a` 使 `p a ≠ 0` ⇒ `a_i = 0` ⇒ 在 `twoAt i a` 处只有 `j = i` 项存活，
--       其值 = `p a ≠ 0` ✓
--
-- 本模块现状（**全部完成**；原「⬜ §4 未完成」是过期标注，已更正）
--   ✅ §1 系数表示 · §2 坐标改写 · §3 `zeroAt-twoAt`
--   ✅ §4 乘 `x_i²`（`mulX2`）—— 原判断「`with` 阻断定义展开，需重构为 `Maybe` 版」
--      **不成立**：`with` 只在证明 `mulX2` 自己的递归时挡路，而那种情形改用
--      **`rewrite`** 即可（见 §5 的 `mulX2-twoAt`，一行 `rewrite lookupAt-twoAt i a`）。
--   ✅ §5 `mulX2-twoAt` / §6 `mulX2-other` / §7 `sumFin-single`
--   ✅ §8 **壁垒定理 `barrier`**（支撑避开一个坐标 ⇒ 恒零）
--   ✅ §9 推论 `barrier-all-coords`（对所有坐标避让 ⇒ 恒零）
--
-- 依赖: Sovereign.Algebra.LinearAlgebra.GF3LaplacianN（Torus）
-- 0 postulate / 0 hole

module Sovereign.Algebra.LinearAlgebra.GF3Barrier where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Vec using (Vec; []; _∷_)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; cong₂)

open import Sovereign.Base.Trit using (Trit; T₀; T₁; T₂; _⊕_; negate;
  ⊕-identityˡ; ⊕-identityʳ)
open import Sovereign.Algebra.LinearAlgebra.GF3LaplacianN using
  (Torus; sumFin; sumFin-cong; sumFin-zero)

--------------------------------------------------------------------------------
-- §1. 系数表示
--------------------------------------------------------------------------------

CoeffN : ℕ → Set
CoeffN n = Torus n → Trit

f0 f2 : Fin 3
f0 = fzero
f2 = fsuc (fsuc fzero)

--------------------------------------------------------------------------------
-- §2. 坐标改写（第 i 坐标设为 T₀ / T₂）
--------------------------------------------------------------------------------

zeroAt : ∀ {n} → Fin n → Torus n → Torus n
zeroAt {n = suc n} fzero     (_ ∷ xs) = f0 ∷ xs
zeroAt {n = suc n} (fsuc i)  (x ∷ xs) = x  ∷ zeroAt i xs

twoAt : ∀ {n} → Fin n → Torus n → Torus n
twoAt {n = suc n} fzero     (_ ∷ xs) = f2 ∷ xs
twoAt {n = suc n} (fsuc i)  (x ∷ xs) = x  ∷ twoAt i xs

lookupAt : ∀ {n} → Fin n → Torus n → Fin 3
lookupAt {n = suc n} fzero     (x ∷ _)  = x
lookupAt {n = suc n} (fsuc i)  (_ ∷ xs) = lookupAt i xs

--------------------------------------------------------------------------------
-- §3. 关键引理：先设 T₂ 再设 T₀ 复原（当原值为 T₀）
--------------------------------------------------------------------------------

zeroAt-twoAt : ∀ {n} (i : Fin n) (a : Torus n) →
  lookupAt i a ≡ f0 → zeroAt i (twoAt i a) ≡ a
zeroAt-twoAt {n = suc n} fzero     (x ∷ xs) eq = cong₂ _∷_ (sym eq) refl
zeroAt-twoAt {n = suc n} (fsuc i)  (x ∷ xs) eq =
  cong₂ _∷_ refl (zeroAt-twoAt i xs eq)

--------------------------------------------------------------------------------
-- §4. 乘 `x_i²`（索引回退；第 i 坐标 < 2 时归零 ⇒ 截断自动）
--
-- 注：`with` 在这里是安全的 —— 它只在**证明 `mulX2` 自己的递归**时才挡路，
--     而那种情形改用 `rewrite` 即可（见 `mulX2-twoAt`）。
--------------------------------------------------------------------------------

mulX2 : ∀ {n} → Fin n → CoeffN n → CoeffN n
mulX2 i p b with lookupAt i b
... | fzero               = T₀
... | fsuc fzero          = T₀
... | fsuc (fsuc fzero)   = p (zeroAt i b)

--------------------------------------------------------------------------------
-- §5. 基本引理
--------------------------------------------------------------------------------

nothing≢just : ∀ {A : Set} {a : A} → nothing ≢ just a
nothing≢just ()

T₁≢T₀ : T₁ ≢ T₀
T₁≢T₀ ()

T₂≢T₀ : T₂ ≢ T₀
T₂≢T₀ ()

f2≢f0 : f2 ≢ f0
f2≢f0 ()

-- `twoAt i a` 的第 i 坐标是 T₂
lookupAt-twoAt : ∀ {n} (i : Fin n) (a : Torus n) → lookupAt i (twoAt i a) ≡ f2
lookupAt-twoAt {n = suc n} fzero (a ∷ as) = refl
lookupAt-twoAt {n = suc n} (fsuc i) (a ∷ as) = lookupAt-twoAt i as

-- `zeroAt j` 不改动 i-坐标（i ≠ j）
lookupAt-zeroAt-general : ∀ {n} (i j : Fin n) → i ≢ j → (x : Torus n) →
  lookupAt i (zeroAt j x) ≡ lookupAt i x
lookupAt-zeroAt-general {n = suc n} fzero fzero ne (x ∷ xs) = ⊥-elim (ne refl)
lookupAt-zeroAt-general {n = suc n} fzero (fsuc j) ne (x ∷ xs) = refl
lookupAt-zeroAt-general {n = suc n} (fsuc i) fzero ne (x ∷ xs) = refl
lookupAt-zeroAt-general {n = suc n} (fsuc i) (fsuc j) ne (x ∷ xs) =
  lookupAt-zeroAt-general i j (λ e → ne (cong fsuc e)) xs

-- ★ 乘 `x_i²` 在 `twoAt` 处解回 `p`（用 rewrite 避开 with 的抽象）
mulX2-twoAt : ∀ {n} (i : Fin n) (p : CoeffN n) (a : Torus n) →
  mulX2 i p (twoAt i a) ≡ p (zeroAt i (twoAt i a))
mulX2-twoAt i p a rewrite lookupAt-twoAt i a = refl

--------------------------------------------------------------------------------
-- §6. 壁垒第一步：其余项归零
--
-- 数学：`avoid p i` 说「p 非零处第 i 坐标必为 T₀」。
-- 在 `twoAt i a` 处，`x_j²·p`（j ≠ i）若语出，落在 `zeroAt j (twoAt i a)`，
-- 其第 i 坐标仍是 T₂（i≠j）⇒ 与 avoid 矛盾 ⇒ 该项为零。
--------------------------------------------------------------------------------

-- 辅助（顶层，不依赖 where 的子句作用域）
zw-chain : ∀ {n} (i j : Fin n) → i ≢ j → (a : Torus n) →
  lookupAt i (zeroAt j (twoAt i a)) ≡ f2
zw-chain i j ne a =
  trans (lookupAt-zeroAt-general i j ne (twoAt i a)) (lookupAt-twoAt i a)

-- 三值消去：若「非零」会导出矛盾，则该值必为零（对 Trit 三分，不做 with）
trit-zero : (v : Trit) → (v ≢ T₀ → ⊥) → v ≡ T₀
trit-zero T₀ h = refl
trit-zero T₁ h = ⊥-elim (h T₁≢T₀)
trit-zero T₂ h = ⊥-elim (h T₂≢T₀)

mulX2-other : ∀ {n} (i j : Fin n) → i ≢ j → (p : CoeffN n) (a : Torus n) →
  (∀ b → p b ≢ T₀ → lookupAt i b ≡ f0) →
  mulX2 j p (twoAt i a) ≡ T₀
mulX2-other i j ne p a avoid with lookupAt j (twoAt i a)
... | fzero            = refl
... | fsuc fzero       = refl
... | fsuc (fsuc fzero) =
      trit-zero (p (zeroAt j (twoAt i a)))
        (λ e → f2≢f0 (trans (sym (zw-chain i j ne a))
                            (avoid (zeroAt j (twoAt i a)) e)))

--------------------------------------------------------------------------------
-- §7. 单点求和：若 f 只在 i 处非零，则 sumFin f = f i
--------------------------------------------------------------------------------

fsuc≢fzero : ∀ {n} {i : Fin n} → fsuc i ≢ fzero
fsuc≢fzero ()

fzero≢fsuc : ∀ {n} {i : Fin n} → fzero ≢ fsuc i
fzero≢fsuc ()

fsuc-inj : ∀ {n} {i j : Fin n} → fsuc i ≡ fsuc j → i ≡ j
fsuc-inj refl = refl

sumFin-single : ∀ {n} (i : Fin n) (f : Fin n → Trit) (v : Trit) →
  f i ≡ v → (∀ j → i ≢ j → f j ≡ T₀) → sumFin f ≡ v
sumFin-single {n = suc n} fzero f v eq h =
  trans (cong₂ _⊕_ eq tail) (⊕-identityʳ v)
  where
    tail : sumFin (λ k → f (fsuc k)) ≡ T₀
    tail = trans (sumFin-cong {n = n} (λ k → h (fsuc k) fzero≢fsuc)) (sumFin-zero {n})
sumFin-single {n = suc n} (fsuc i) f v eq h =
  trans (cong₂ _⊕_ head
               (sumFin-single i (λ k → f (fsuc k)) v eq
                                (λ k e → h (fsuc k) (λ p → e (fsuc-inj p)))))
        (⊕-identityˡ v)
  where
    head : f fzero ≡ T₀
    head = h fzero fsuc≢fzero

--------------------------------------------------------------------------------
-- §8. ★ 壁垒定理
--
-- 若 `p` 满足：
--   ① `sum2 p ≡ 0`（即 `Σ_j x_j²·p = 0`，调和）
--   ② `p` 非零处的第 i 坐标必为 T₀（支撑避开坐标 i）
-- 则 `p ≡ 0`。
-- 证：若 `p b ≠ 0`，则在 `twoAt i b` 处只有 `j = i` 项存活，其值 = `p b ≠ 0`，
--     与 ① 矛盾。
--------------------------------------------------------------------------------

sum2 : ∀ {n} → CoeffN n → CoeffN n
sum2 p b = sumFin (λ j → mulX2 j p b)

barrier-step : ∀ {n} (p : CoeffN n) (i : Fin n) (b : Torus n) →
  (∀ b → sum2 p b ≡ T₀) →
  (∀ b → p b ≢ T₀ → lookupAt i b ≡ f0) →
  p b ≢ T₀ → p b ≡ T₀
barrier-step p i b hyp avoid e =
  trans (sym (sumFin-single i (λ j → mulX2 j p (twoAt i b)) (p b) at-i not-i))
        (hyp (twoAt i b))
  where
    at-i : mulX2 i p (twoAt i b) ≡ p b
    at-i = trans (mulX2-twoAt i p b) (cong p (zeroAt-twoAt i b (avoid b e)))

    not-i : ∀ j → i ≢ j → mulX2 j p (twoAt i b) ≡ T₀
    not-i j ne = mulX2-other i j ne p b avoid

barrier : ∀ {n} (p : CoeffN n) (i : Fin n) →
  (∀ b → sum2 p b ≡ T₀) →
  (∀ b → p b ≢ T₀ → lookupAt i b ≡ f0) →
  ∀ b → p b ≡ T₀
barrier p i hyp avoid b =
  trit-zero (p b) (λ e → e (barrier-step p i b hyp avoid e))

--------------------------------------------------------------------------------
-- §9. 推论：全坐标支撑避让 ⇒ 零
--
-- `barrier` 是「支撑避开**一个**坐标 ⇒ 零」。
-- 若对**所有**坐标都避让，则该元素只能支撑在原点 `0^n` —— 而原点处的
-- 单项式被 `x_j²` 推到 `2e_j`（非零）⇒ 只能为零。
--
-- 这是 `ker F ∩ V_{[n]} = {0}` 的系数形式，也是「零全局耦合」的最强形态：
-- 任一非零调和元素的支撑**必然跨越所有坐标**。
--------------------------------------------------------------------------------

-- 更强形式的读法：对**每个**坐标都避让 ⇒ 零
-- （只需其中一个坐标即可，其余是加强的前提）
-- 注：`n ≥ 1`（否则 `fzero : Fin zero` 无意义）
barrier-all-coords : ∀ {n} (p : CoeffN (suc n)) →
  (∀ b → sum2 p b ≡ T₀) →
  (∀ i b → p b ≢ T₀ → lookupAt i b ≡ f0) →
  (∀ b → p b ≡ T₀)
barrier-all-coords p hyp avoid = barrier p fzero hyp (λ b → avoid fzero b)
