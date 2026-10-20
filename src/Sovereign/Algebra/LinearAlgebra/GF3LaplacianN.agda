{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Algebra.LinearAlgebra.GF3LaplacianN
-- GF(3)ⁿ 环面上的**广义** Laplacian（T4 / 路线 A / ③a 的前置，2026-10-20）
--
-- 数学背景
--   现有 `NSEOnT6SixAxis` 的 `Torus6` 是**固定六元组**（`C3 × … × C3`），
--   无法对 `n` 做归纳 ✗。而 ③a 的分解同构
--     `ann(F_n) ≅ ann(F_{n−1}) ⊕ ann(F_{n−1}²)`
--   本质上是**对最后一个坐标**做分解 ⇒ 必须先有 `Torus : ℕ → Set`。
--
-- 核心原则
--   ① `Torus n = Vec (Fin 3) n` —— 用 `Vec` 而非嵌套积，才能对 `n` 归纳
--   ② `shiftAt` 用 **`Fin` 上的结构递归**（`Fin zero` 为空），不需要 `updateAt`
--   ③ `shift3³ = id` ⇒ `shiftAt³ = id`（归纳）
--
-- 本模块（T-A）：载体 + 移位 + 三次移位恒等。算子层（T-B）随后。
--
-- 依赖: Sovereign.Base.Trit（GF(3) 环公理）

module Sovereign.Algebra.LinearAlgebra.GF3LaplacianN where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Vec using (Vec; []; _∷_; replicate)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.Product using (_×_; _,_; _↔_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂)

open import Sovereign.Base.Trit using
  (Trit; T₀; T₁; T₂; _⊕_; _⊗_; negate; ⊕-assoc; ⊕-comm)
open import Sovereign.Base.Trit using () renaming (⊕-identityʳ to ⊕-idʳ)

--------------------------------------------------------------------------------
-- §1. 载体（T-A1）
--------------------------------------------------------------------------------

Torus : ℕ → Set
Torus n = Vec (Fin 3) n

--------------------------------------------------------------------------------
-- §2. 单坐标循环移位（T-A2）
--------------------------------------------------------------------------------

-- `Fin 3` 上的循环移位 0 → 1 → 2 → 0
shift3 : Fin 3 → Fin 3
shift3 fzero           = fsuc fzero
shift3 (fsuc fzero)    = fsuc (fsuc fzero)
shift3 (fsuc (fsuc fzero)) = fzero

-- 第 i 个坐标循环移位（`Fin` 上的结构递归）
shiftAt : ∀ {n} → Fin n → Torus n → Torus n
shiftAt {n = suc n} fzero      (x ∷ xs) = shift3 x   ∷ xs
shiftAt {n = suc n} (fsuc i)   (x ∷ xs) = x          ∷ shiftAt i xs

--------------------------------------------------------------------------------
-- §3. 三次移位回原点（T-A3）
--------------------------------------------------------------------------------

shift3-3 : ∀ a → shift3 (shift3 (shift3 a)) ≡ a
shift3-3 fzero           = refl
shift3-3 (fsuc fzero)    = refl
shift3-3 (fsuc (fsuc fzero)) = refl

-- 逐点断言 `shiftAt³ = id`（逐坐标版本，值为 `refl` 型等式的 `≡`）
shiftAt3 : ∀ {n} (i : Fin n) (x : Torus n) → shiftAt i (shiftAt i (shiftAt i x)) ≡ x
shiftAt3 {n = suc n} fzero     (x ∷ xs) = cong₂ _∷_ (shift3-3 x) refl
shiftAt3 {n = suc n} (fsuc i)  (x ∷ xs) = cong₂ _∷_ refl (shiftAt3 i xs)

--------------------------------------------------------------------------------
-- §4. 算子层（T-B）
--------------------------------------------------------------------------------

ScalarN : ℕ → Set
ScalarN n = Torus n → Trit

-- `Fin n` 上的求和（结构递归；`Fin 0` 为空 ⇒ 和为 T₀）
sumFin : ∀ {n} → (Fin n → Trit) → Trit
sumFin {zero}  g = T₀
sumFin {suc n} g = g fzero ⊕ sumFin (λ i → g (fsuc i))

-- 沿第 i 个坐标的前向差分：`x_i = s_i − 1`
diffAt : ∀ {n} → Fin n → ScalarN n → ScalarN n
diffAt i f x = f (shiftAt i x) ⊕ negate (f x)

-- 广义 Laplacian：`Δ f x = Σ_j (x_j² f) x`
lapN : ∀ {n} → ScalarN n → ScalarN n
lapN f x = sumFin (λ j → diffAt j (diffAt j f) x)

--------------------------------------------------------------------------------
-- §5. 零场的 sanity（2026-10-20 补 —— 曾被误删 ✗）
--
-- 教训：`lapN-zero` 是**真命题**，不能因为「验证不了就删掉」✗。
-- 正确做法是补上它依赖的辅助引理（`sumFin-zero` / `sumFin-cong`）。
--------------------------------------------------------------------------------

-- `sumFin` 对点态相同的函数同余
sumFin-cong : ∀ {n} {g h : Fin n → Trit} → (∀ i → g i ≡ h i) → sumFin g ≡ sumFin h
sumFin-cong {zero}  h' = refl
sumFin-cong {suc n} h' = cong₂ _⊕_ (h' fzero) (sumFin-cong (λ i → h' (fsuc i)))

-- 恒为零的函数，其和为 T₀
sumFin-zero : ∀ {n} → sumFin {n} (λ _ → T₀) ≡ T₀
sumFin-zero {zero}  = refl
sumFin-zero {suc n} = sumFin-zero {n}

-- 零场的单坐标差分为零
diffAt-zero : ∀ {n} (i : Fin n) (x : Torus n) → diffAt i (λ _ → T₀) x ≡ T₀
diffAt-zero i x = refl

-- ★ 零场的 Laplacian 为零（逐点）
lapN-zero : ∀ {n} (x : Torus n) → lapN (λ _ → T₀) x ≡ T₀
lapN-zero {n} x =
  trans (sumFin-cong {n = n}
                     {g = λ j → diffAt j (diffAt j (λ _ → T₀)) x}
                     {h = λ _ → T₀}
                     (λ j → refl))
        (sumFin-zero {n})

--------------------------------------------------------------------------------
-- §6. 线性性（T-C）
--------------------------------------------------------------------------------

-- 标量场逐点加法
_+S_ : ∀ {n} → ScalarN n → ScalarN n → ScalarN n
(f +S g) x = f x ⊕ g x

-- `negate` 对 `⊕` 分配（9 情形）
negate-⊕ : ∀ a b → negate (a ⊕ b) ≡ negate a ⊕ negate b
negate-⊕ T₀ T₀ = refl
negate-⊕ T₀ T₁ = refl
negate-⊕ T₀ T₂ = refl
negate-⊕ T₁ T₀ = refl
negate-⊕ T₁ T₁ = refl
negate-⊕ T₁ T₂ = refl
negate-⊕ T₂ T₀ = refl
negate-⊕ T₂ T₁ = refl
negate-⊕ T₂ T₂ = refl

-- `(a ⊕ b) ⊕ (c ⊕ d) ≡ (a ⊕ c) ⊕ (b ⊕ d)`
--   **代数链**（5 步）而非 81 情形穷举 —— `⊕-assoc` 方向：`(x ⊕ y) ⊕ z ≡ x ⊕ (y ⊕ z)`
sum4 : ∀ a b c d → (a ⊕ b) ⊕ (c ⊕ d) ≡ (a ⊕ c) ⊕ (b ⊕ d)
sum4 a b c d =
  trans (⊕-assoc a b (c ⊕ d))
 (trans (cong (a ⊕_) (sym (⊕-assoc b c d)))
 (trans (cong (λ z → a ⊕ (z ⊕ d)) (⊕-comm b c))
 (trans (cong (a ⊕_) (⊕-assoc c b d))
        (sym (⊕-assoc a c (b ⊕ d))))))

-- 单坐标差分线性
--   `diffAt i (f +S g) x = [f(sx) ⊕ g(sx)] ⊕ negate (f x ⊕ g x)`
--   `(diffAt i f +S diffAt i g) x = [f(sx) ⊕ negate (f x)] ⊕ [g(sx) ⊕ negate (g x)]`
--   靠 `negate-⊕` + `sum4` 通；此处只给陈述（下面给出证明）
diffAt-+S : ∀ {n} (i : Fin n) (f g : ScalarN n) (x : Torus n) →
  diffAt i (f +S g) x ≡ (diffAt i f +S diffAt i g) x
diffAt-+S i f g x =
  trans (cong (λ z → (f (shiftAt i x) ⊕ g (shiftAt i x)) ⊕ z) (negate-⊕ (f x) (g x)))
        (sum4 (f (shiftAt i x)) (g (shiftAt i x)) (negate (f x)) (negate (g x)))

--------------------------------------------------------------------------------
-- §7. T-D 探针：n=1 时 `lapN` 是常数（三点之和）
--
-- 数学：`x² f (y) = f(y+2) ⊕ f(y+1) ⊕ f(y)`，循环 ⇒ **与 y 无关** ✓
-- 三个 y 只差**括号顺序** ⇒ 只需 `⊕` 重排，不需要值分类 ✓
--------------------------------------------------------------------------------

p0 p1 p2 : Torus 1
p0 = fzero ∷ []
p1 = fsuc fzero ∷ []
p2 = fsuc (fsuc fzero) ∷ []

-- `x²` 展开核：`(c ⊕ negate b) ⊕ negate (b ⊕ negate a) ≡ a ⊕ (b ⊕ c)`（27 情形）
p-lap : ∀ a b c → (c ⊕ negate b) ⊕ negate (b ⊕ negate a) ≡ a ⊕ (b ⊕ c)
p-lap T₀ T₀ T₀ = refl
p-lap T₀ T₀ T₁ = refl
p-lap T₀ T₀ T₂ = refl
p-lap T₀ T₁ T₀ = refl
p-lap T₀ T₁ T₁ = refl
p-lap T₀ T₁ T₂ = refl
p-lap T₀ T₂ T₀ = refl
p-lap T₀ T₂ T₁ = refl
p-lap T₀ T₂ T₂ = refl
p-lap T₁ T₀ T₀ = refl
p-lap T₁ T₀ T₁ = refl
p-lap T₁ T₀ T₂ = refl
p-lap T₁ T₁ T₀ = refl
p-lap T₁ T₁ T₁ = refl
p-lap T₁ T₁ T₂ = refl
p-lap T₁ T₂ T₀ = refl
p-lap T₁ T₂ T₁ = refl
p-lap T₁ T₂ T₂ = refl
p-lap T₂ T₀ T₀ = refl
p-lap T₂ T₀ T₁ = refl
p-lap T₂ T₀ T₂ = refl
p-lap T₂ T₁ T₀ = refl
p-lap T₂ T₁ T₁ = refl
p-lap T₂ T₁ T₂ = refl
p-lap T₂ T₂ T₀ = refl
p-lap T₂ T₂ T₁ = refl
p-lap T₂ T₂ T₂ = refl

-- 三循环旋转：`a ⊕ (b ⊕ c) ≡ c ⊕ (a ⊕ b)`（27 情形）
rot3 : ∀ a b c → a ⊕ (b ⊕ c) ≡ c ⊕ (a ⊕ b)
rot3 T₀ T₀ T₀ = refl
rot3 T₀ T₀ T₁ = refl
rot3 T₀ T₀ T₂ = refl
rot3 T₀ T₁ T₀ = refl
rot3 T₀ T₁ T₁ = refl
rot3 T₀ T₁ T₂ = refl
rot3 T₀ T₂ T₀ = refl
rot3 T₀ T₂ T₁ = refl
rot3 T₀ T₂ T₂ = refl
rot3 T₁ T₀ T₀ = refl
rot3 T₁ T₀ T₁ = refl
rot3 T₁ T₀ T₂ = refl
rot3 T₁ T₁ T₀ = refl
rot3 T₁ T₁ T₁ = refl
rot3 T₁ T₁ T₂ = refl
rot3 T₁ T₂ T₀ = refl
rot3 T₁ T₂ T₁ = refl
rot3 T₁ T₂ T₂ = refl
rot3 T₂ T₀ T₀ = refl
rot3 T₂ T₀ T₁ = refl
rot3 T₂ T₀ T₂ = refl
rot3 T₂ T₁ T₀ = refl
rot3 T₂ T₁ T₁ = refl
rot3 T₂ T₁ T₂ = refl
rot3 T₂ T₂ T₀ = refl
rot3 T₂ T₂ T₁ = refl
rot3 T₂ T₂ T₂ = refl

-- ★ 三点同值：`lapN f` 在 `Torus 1` 上取常数（= 三点之和）
--
-- 关键：`sumFin {1} g = g fzero ⊕ T₀` ⇒ 左端多一层 `⊕ T₀`，用 `⊕-idʳ` 收掉 ✓
-- （2026-10-20：先手工展开 `sumFin` 再写证，一次通过）
lapN1-eq : ∀ (f : ScalarN 1) (a : Fin 3) →
  lapN f (a ∷ []) ≡ f p0 ⊕ (f p1 ⊕ f p2)
lapN1-eq f fzero =
  trans (cong (λ z → z ⊕ T₀) (p-lap (f p0) (f p1) (f p2)))
        (⊕-idʳ (f p0 ⊕ (f p1 ⊕ f p2)))
lapN1-eq f (fsuc fzero) =
  trans (cong (λ z → z ⊕ T₀)
              (trans (p-lap (f p1) (f p2) (f p0)) (rot3 (f p1) (f p2) (f p0))))
        (⊕-idʳ (f p0 ⊕ (f p1 ⊕ f p2)))
lapN1-eq f (fsuc (fsuc fzero)) =
  trans (cong (λ z → z ⊕ T₀)
              (trans (p-lap (f p2) (f p0) (f p1))
                     (trans (rot3 (f p2) (f p0) (f p1))
                            (rot3 (f p1) (f p2) (f p0)))))
        (⊕-idʳ (f p0 ⊕ (f p1 ⊕ f p2)))

-- ★ T-D 的 n=1 结论：`annN 1` 由「三点之和为零」完全刻画
--   （⇒ `annN 1` 是 2 维的，与公式 `3^{n−1}+2^{n−1}` 在 n=1 处 = 2 一致 ✓）
annN1-iff : ∀ (f : ScalarN 1) →
  ((∀ a → lapN f (a ∷ []) ≡ T₀) → (f p0 ⊕ (f p1 ⊕ f p2) ≡ T₀))
  × ((f p0 ⊕ (f p1 ⊕ f p2) ≡ T₀) → (∀ a → lapN f (a ∷ []) ≡ T₀))
annN1-iff f =
    (λ h → trans (sym (lapN1-eq f fzero)) (h fzero))
  , (λ h → λ { fzero               → trans (lapN1-eq f fzero) h
             ; (fsuc fzero)        → trans (lapN1-eq f (fsuc fzero)) h
             ; (fsuc (fsuc fzero)) → trans (lapN1-eq f (fsuc (fsuc fzero))) h })

--------------------------------------------------------------------------------
-- §9. 首坐标分裂（③a 的第一步，2026-10-20）
--
-- `sumFin {suc n} g = g fzero ⊕ sumFin {n} (λ i → g (fsuc i))`
-- ⇒ `lapN {suc n}` 在首坐标处分裂成「首坐标的二阶差分」⊕「其余坐标的 lapN」
--
-- 关键恒等式（点态成立）：
--   `diffAt (fsuc i) f (a ∷ rest) = diffAt i (λ r → f (a ∷ r)) rest`
--------------------------------------------------------------------------------

lapN-suc-split : ∀ {n} (f : ScalarN (suc n)) (a : Fin 3) (rest : Torus n) →
  lapN {suc n} f (a ∷ rest)
    ≡ diffAt fzero (diffAt fzero f) (a ∷ rest) ⊕ lapN {n} (λ r → f (a ∷ r)) rest
lapN-suc-split {n} f a rest =
  cong (λ z → diffAt fzero (diffAt fzero f) (a ∷ rest) ⊕ z)
       (sumFin-cong {n = n} (λ i → refl))

--------------------------------------------------------------------------------
-- §10. 壁垒的第一步：不变 ⇒ x_i² 消失（2026-10-20）
--
-- 翻译：`x_i = diffAt i`。「g 的所有单项式在 x_i 上指数 = 0」
--   ⟺ `diffAt i g ≡ 0`（g 不含 x_i，即 g 在坐标 i 上不变）✓
--
-- 这是壁垒 `ker F ∩ V_S = {0}` 的第一块：
--   若 `f` 在坐标 i 上不变，则 `F f` 里 `x_i² f` 项恒为零 ✓
--------------------------------------------------------------------------------

-- ⚠ 本库**不假设函数外延**（funext）✗ ⇒ 所有陈述必须**点态**（`∀ x → f x ≡ g x`）✓

-- ★ 不变 ⇒ x_i² 消失（点态形式，无外延）
x²-zero-of-invariant : ∀ {n} (i : Fin n) (f : ScalarN n) →
  (∀ x → diffAt i f x ≡ T₀) → (∀ x → diffAt i (diffAt i f) x ≡ T₀)
x²-zero-of-invariant i f h x =
  trans (cong₂ _⊕_ (h (shiftAt i x)) (cong negate (h x))) refl

--------------------------------------------------------------------------------
-- §11. 单项式基的 1 维基例（2026-10-20）
--
-- 实算（穷举 27 个 g 验证）：基矩阵 B = [[1,2,1],[0,0,1],[0,1,1]]，逆 = [[1,1,1],[0,2,1],[0,1,0]]
-- 展开系数：c0 = g₀⊕g₁⊕g₂（= sum3 g ✓）、c1 = (g₁⊕g₁)⊕g₂、c2 = g₁
--
-- ⚠ 本库无 funext ⇒ g 的三个值必须**参数化**
--------------------------------------------------------------------------------

q0 q1 q2 : Torus 1
q0 = fzero ∷ []
q1 = fsuc fzero ∷ []
q2 = fsuc (fsuc fzero) ∷ []

delta0 : ScalarN 1
delta0 (fzero ∷ [])             = T₁
delta0 (fsuc fzero ∷ [])        = T₀
delta0 (fsuc (fsuc fzero) ∷ []) = T₀

b0 b1 b2 : ScalarN 1
b0 = delta0
b1 = diffAt fzero delta0
b2 = diffAt fzero (diffAt fzero delta0)

-- 展开系数（实算得出，穷举验证 ✓）
c0 c1 c2 : Trit → Trit → Trit → Trit
c0 v0 v1 v2 = v0 ⊕ (v1 ⊕ v2)
c1 v0 v1 v2 = (v1 ⊕ v1) ⊕ v2
c2 v0 v1 v2 = v1

-- 组合算子（统一写法）
comb : Trit → Trit → Trit → Fin 3 → Trit
comb v0 v1 v2 a =
  (c0 v0 v1 v2 ⊗ b0 (a ∷ []))
    ⊕ ((c1 v0 v1 v2 ⊗ b1 (a ∷ [])) ⊕ (c2 v0 v1 v2 ⊗ b2 (a ∷ [])))

-- ★ 三个基点上的分解式（各 27 情形）
--   在每个点上，LHS 只依赖 v0 v1 v2，且应等于该点对应之值 ✓
basis1-at-q0 : ∀ (v0 v1 v2 : Trit) → comb v0 v1 v2 fzero ≡ v0
basis1-at-q0 T₀ T₀ T₀ = refl
basis1-at-q0 T₀ T₀ T₁ = refl
basis1-at-q0 T₀ T₀ T₂ = refl
basis1-at-q0 T₀ T₁ T₀ = refl
basis1-at-q0 T₀ T₁ T₁ = refl
basis1-at-q0 T₀ T₁ T₂ = refl
basis1-at-q0 T₀ T₂ T₀ = refl
basis1-at-q0 T₀ T₂ T₁ = refl
basis1-at-q0 T₀ T₂ T₂ = refl
basis1-at-q0 T₁ T₀ T₀ = refl
basis1-at-q0 T₁ T₀ T₁ = refl
basis1-at-q0 T₁ T₀ T₂ = refl
basis1-at-q0 T₁ T₁ T₀ = refl
basis1-at-q0 T₁ T₁ T₁ = refl
basis1-at-q0 T₁ T₁ T₂ = refl
basis1-at-q0 T₁ T₂ T₀ = refl
basis1-at-q0 T₁ T₂ T₁ = refl
basis1-at-q0 T₁ T₂ T₂ = refl
basis1-at-q0 T₂ T₀ T₀ = refl
basis1-at-q0 T₂ T₀ T₁ = refl
basis1-at-q0 T₂ T₀ T₂ = refl
basis1-at-q0 T₂ T₁ T₀ = refl
basis1-at-q0 T₂ T₁ T₁ = refl
basis1-at-q0 T₂ T₁ T₂ = refl
basis1-at-q0 T₂ T₂ T₀ = refl
basis1-at-q0 T₂ T₂ T₁ = refl
basis1-at-q0 T₂ T₂ T₂ = refl

basis1-at-q1 : ∀ (v0 v1 v2 : Trit) → comb v0 v1 v2 (fsuc fzero) ≡ v1
basis1-at-q1 T₀ T₀ T₀ = refl
basis1-at-q1 T₀ T₀ T₁ = refl
basis1-at-q1 T₀ T₀ T₂ = refl
basis1-at-q1 T₀ T₁ T₀ = refl
basis1-at-q1 T₀ T₁ T₁ = refl
basis1-at-q1 T₀ T₁ T₂ = refl
basis1-at-q1 T₀ T₂ T₀ = refl
basis1-at-q1 T₀ T₂ T₁ = refl
basis1-at-q1 T₀ T₂ T₂ = refl
basis1-at-q1 T₁ T₀ T₀ = refl
basis1-at-q1 T₁ T₀ T₁ = refl
basis1-at-q1 T₁ T₀ T₂ = refl
basis1-at-q1 T₁ T₁ T₀ = refl
basis1-at-q1 T₁ T₁ T₁ = refl
basis1-at-q1 T₁ T₁ T₂ = refl
basis1-at-q1 T₁ T₂ T₀ = refl
basis1-at-q1 T₁ T₂ T₁ = refl
basis1-at-q1 T₁ T₂ T₂ = refl
basis1-at-q1 T₂ T₀ T₀ = refl
basis1-at-q1 T₂ T₀ T₁ = refl
basis1-at-q1 T₂ T₀ T₂ = refl
basis1-at-q1 T₂ T₁ T₀ = refl
basis1-at-q1 T₂ T₁ T₁ = refl
basis1-at-q1 T₂ T₁ T₂ = refl
basis1-at-q1 T₂ T₂ T₀ = refl
basis1-at-q1 T₂ T₂ T₁ = refl
basis1-at-q1 T₂ T₂ T₂ = refl

basis1-at-q2 : ∀ (v0 v1 v2 : Trit) → comb v0 v1 v2 (fsuc (fsuc fzero)) ≡ v2
basis1-at-q2 T₀ T₀ T₀ = refl
basis1-at-q2 T₀ T₀ T₁ = refl
basis1-at-q2 T₀ T₀ T₂ = refl
basis1-at-q2 T₀ T₁ T₀ = refl
basis1-at-q2 T₀ T₁ T₁ = refl
basis1-at-q2 T₀ T₁ T₂ = refl
basis1-at-q2 T₀ T₂ T₀ = refl
basis1-at-q2 T₀ T₂ T₁ = refl
basis1-at-q2 T₀ T₂ T₂ = refl
basis1-at-q2 T₁ T₀ T₀ = refl
basis1-at-q2 T₁ T₀ T₁ = refl
basis1-at-q2 T₁ T₀ T₂ = refl
basis1-at-q2 T₁ T₁ T₀ = refl
basis1-at-q2 T₁ T₁ T₁ = refl
basis1-at-q2 T₁ T₁ T₂ = refl
basis1-at-q2 T₁ T₂ T₀ = refl
basis1-at-q2 T₁ T₂ T₁ = refl
basis1-at-q2 T₁ T₂ T₂ = refl
basis1-at-q2 T₂ T₀ T₀ = refl
basis1-at-q2 T₂ T₀ T₁ = refl
basis1-at-q2 T₂ T₀ T₂ = refl
basis1-at-q2 T₂ T₁ T₀ = refl
basis1-at-q2 T₂ T₁ T₁ = refl
basis1-at-q2 T₂ T₁ T₂ = refl
basis1-at-q2 T₂ T₂ T₀ = refl
basis1-at-q2 T₂ T₂ T₁ = refl
basis1-at-q2 T₂ T₂ T₂ = refl

