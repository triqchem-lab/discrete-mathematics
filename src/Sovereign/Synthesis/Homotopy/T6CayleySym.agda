{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Synthesis.Homotopy.T6CayleySym
--
-- **C3-a（人类 2026-10-21 裁决）**：对称化载体 `T⁶_sym`（`±e_j`），新对象 `π₁ᵈˢᵗᵈ`
--
-- ## 裁决原文
--
-- > **C3-a 的载体用 `±e_j`（对称化），新对象 `T⁶_sym`**，不是裁决 2 步 1 的字面 `T6Cayley`。
-- > 理由：`π₁ᵈˢᵗᵈ` 是标准 A-同伦的离散化，标准 A-同伦的载体是**对称图**，
-- > `+e_j` 单向图不满足 `bt` 的前提（无反向边）。
-- >
-- > 验证目标：`π₁ᵈˢᵗᵈ(T¹_sym) ≅ C₃`。
--
-- ## 关键设计：`-e_j` 不需要新定义
--
-- 在 `Fin 3` 上 `-1 ≡ +2`，而 `updAt j` 做的是 `+1` ⇒ **两次 `updAt j` 就是 `-e_j`** ✓
-- 反向边由已证的 `updAt-cubed`（三次 = id）提供：
--
-- ```
--   +e_j : x → updAt j x                     （定义性，refl）
--   -e_j : updAt j x → x                     （靠 sym (updAt-cubed j x)）
-- ```
--
-- **⚠ 为什么必须用 Vec 载体**：反向边要求**函数/向量相等**
-- `updAt j (updAt j (updAt j x)) ≡ x`。函数载体上这需要 `funext`（库无）⇒ 卡死 ✗；
-- Vec 载体的 `updAt-cubed` 是真等式 ✓ ⇒ 只有 Vec 载体能承载对称化。
--
-- ## 本模块交付（裁决列的步 1–3 + 步 5 的坍缩方向）
--
-- | 步 | 内容 | 状态 |
-- |---|---|---|
-- | 1 | `T6CayleySym` 定义（顶点 `Fin n → Fin 3` 的向量版，边 `±e_j`）| ✅ |
-- | 2 | `tri-slide` 可用（`[0]→[1]→[2]` 带弦 `[0]→[2]`，弦是 `-e_0`）| ✅ `tri-available` |
-- | 3 | `bt` 可用（`+e_j` 与 `-e_j` 互为反向）| ✅ `bt-available` |
-- | 5a | **三点环坍缩到空走**（`tri-slide` + `bt` 两步）| ✅ `cyc3-collapse` |
-- | 5b | 完整的 `≅ C₃`（还需「每个闭走等价到三类之一」的完备性）| ⬜ 见 §4 |
--
-- ## 核心原则
--   · 0 postulate / 0 hole
--   · 复用 `T6CayleyVec` 的 `updAt` / `updAt-cubed`（不重证）

module Sovereign.Synthesis.Homotopy.T6CayleySym where

open import Data.Nat using (ℕ)
open import Data.Fin using (Fin)
import Data.Fin as Fin
open import Data.Vec using (Vec; []; _∷_)
open import Data.Product using (Σ; _×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym)

open import Sovereign.Synthesis.Homotopy.BarceloAHomotopy
  using (DiGraph; Walk; nil; cons)
open import Sovereign.Synthesis.Homotopy.T6CayleyVec
  using (T6Vec; updAt; updAt-cubed)
open import Sovereign.Synthesis.Homotopy.AStepStd
  using (AStepStd; AHomotopyStd; tri-slide; bt; gen; trn)

--------------------------------------------------------------------------------
-- §1. 对称化载体：边 = `±e_j`
--------------------------------------------------------------------------------

T6SymEdge : ∀ {n : ℕ} → T6Vec n → T6Vec n → Set
T6SymEdge {n} x y =
    (Σ (Fin n) (λ j → y ≡ updAt j x))              -- `+e_j`
  ⊎ (Σ (Fin n) (λ j → y ≡ updAt j (updAt j x)))    -- `-e_j`（= `+2e_j`，因 `-1 ≡ +2` 于 Fin 3）

T6CayleySym : (n : ℕ) → DiGraph
T6CayleySym n = record { V = T6Vec n ; edge = T6SymEdge }

--------------------------------------------------------------------------------
-- §2. 步 1–3：`+e_j` / `-e_j` 边与 `bt` 可用性
--------------------------------------------------------------------------------

plus-edge : ∀ {n : ℕ} (j : Fin n) (x : T6Vec n) → T6SymEdge x (updAt j x)
plus-edge j x = inj₁ (j , refl)

-- 反向边：从 `updAt j x` 回到 `x`（`+2` 步 = `-1` 步）
minus-edge : ∀ {n : ℕ} (j : Fin n) (x : T6Vec n) → T6SymEdge (updAt j x) x
minus-edge j x = inj₂ (j , sym (updAt-cubed j x))

-- ★ 步 3：`bt` 的前提成立 —— 回溯对存在（任意 n、任意坐标）
bt-available : ∀ {n : ℕ} (j : Fin n) (x : T6Vec n)
             → T6SymEdge x (updAt j x) × T6SymEdge (updAt j x) x
bt-available j x = plus-edge j x , minus-edge j x

--------------------------------------------------------------------------------
-- §3. 步 2 + 步 5a：`T¹` 的三点环有三角形，且**坍缩到空走**
--------------------------------------------------------------------------------

v0 v1 v2 : T6Vec 1
v0 = Fin.zero ∷ []
v1 = Fin.suc Fin.zero ∷ []
v2 = Fin.suc (Fin.suc Fin.zero) ∷ []

-- 三条边：`[0]→[1]`（+e）、`[1]→[2]`（+e）、`[0]→[2]`（−e，即弦）
e01 : T6SymEdge v0 v1
e01 = plus-edge Fin.zero v0

e12 : T6SymEdge v1 v2
e12 = plus-edge Fin.zero v1

e03 : T6SymEdge v0 v2
e03 = minus-edge Fin.zero v2

e20 : T6SymEdge v2 v0
e20 = plus-edge Fin.zero v2

-- ★ 步 2：有向三角形存在（**这在 `+e_j` 载体上不可能** —— `tfN` 已证无三角形）
tri-available : T6SymEdge v0 v1 × T6SymEdge v1 v2 × T6SymEdge v0 v2
tri-available = e01 , e12 , e03

-- 三点环（闭走，长度 3）
cyc3 : Walk (T6CayleySym 1) v0 v0
cyc3 = cons e01 (cons e12 (cons e20 (nil v0)))

-- `tri-slide` 把它换成 `[0]→[2]→[0]`（长度 2）
step-tri : AStepStd (T6CayleySym 1) cyc3 (cons e03 (cons e20 (nil v0)))
step-tri = tri-slide (nil v0) (cons e20 (nil v0)) e01 e12 e03

-- `bt` 再把 `[0]→[2]→[0]` 消掉（回溯对 `e03 : v0→v2`、`e20 : v2→v0`）
step-bt : AStepStd (T6CayleySym 1) (cons e03 (cons e20 (nil v0))) (nil v0)
step-bt = bt (nil v0) (nil v0) e03 e20

-- ★★ 步 5a：三点环**坍缩到空走**（AStepStd 口径）
cyc3-collapse : AHomotopyStd (T6CayleySym 1) cyc3 (nil v0)
cyc3-collapse = trn (gen step-tri) (gen step-bt)

--------------------------------------------------------------------------------
-- §4. ⬜ 步 5b（未做）：完整的 `π₁ᵈˢᵗᵈ(T¹_sym) ≅ C₃`
--
-- 已证的是**坍缩方向**：`cyc3 ⁓ nil` ⇒ 三点环的类等于单位类 ⇒ π₁ᵈˢᵗᵈ 中 `g = e`。
-- 但这**不等于** `π₁ᵈˢᵗᵈ ≅ C₃` —— 还差两件事：
--
--   ① **完备性**：每个闭走都等价到 `{nil}` 三类之一（即类集合恰是 3 个）——
--      实际上若 `cyc3 ⁓ nil` 且图是**对称**的，很可能全部闭走都 ⁓ nil
--      （即 π₁ᵈˢᵗᵈ 平凡，而不是 C₃！）——**这一点必须先算清再断言** ⚠
--   ② 反向：C₃ 的三个元素都要有代表（若 π₁ᵈˢᵗᵈ 平凡则不成立）
--
-- ⇒ **本模块不声称 `≅ C₃`**。已证的是「`AStepStd` 在对称载体上确实比 `AStep` 强」
--   （`cyc3-collapse`），这正是 C3-a 的实质进展；完整同构判定是下一步。
--------------------------------------------------------------------------------
