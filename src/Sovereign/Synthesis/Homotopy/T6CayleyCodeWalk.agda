{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Synthesis.Homotopy.T6CayleyCodeWalk
--
-- **翻译边界**：码 → 走（见证只在这里出现一次，且是 `refl`）
--
-- ## 关键洞察：见证不需要「找」，它是 `refl`
--
-- 之前的路线（(a3)）想用 `findEdge` **搜索**边见证 —— 那是多余的。
-- 因为码层已经把**方向 + 坐标**写清了，**目标顶点由码算出来**：
-- ```
--   ctarget x (cplus j)  = updAt j x
--   ctarget x (cminus j) = updAt j (updAt j x)
-- ```
-- ⇒ 见证的类型 `T6SymEdge x (ctarget x s)` 在 `cplus`/`cminus` 两情形下**恰好是 `refl`**：
-- ```
--   cEdge x (cplus j)  = inj₁ (j , refl)      -- refl : updAt j x ≡ updAt j x
--   cEdge x (cminus j) = inj₂ (j , refl)      -- refl : updAt j (updAt j x) ≡ updAt j (updAt j x)
-- ```
-- ⇒ **无需 `findEdge`、无需 uip、无需搜索**。
--
-- ## ★ 码的逆在「目标」意义下正确 —— 靠 GF(3) 的 3 阶
--
-- `cplus j`（1 步）与 `cminus j`（2 步）互为逆，但**往返是 3 步**：
-- ```
--   ctarget (ctarget x (cplus j)) (cminus j) = updAt j (updAt j (updAt j x)) ≡ x
-- ```
-- **正是 `updAt-cubed`（特征 3，三步归零）** ✓ 两个情形归约到**同一条引理**。
--
-- ## 核心原则
--   · 0 postulate / 0 hole；零 Cubical
--   · 复用 `T6CayleyVec.updAt-cubed`（不重证）

module Sovereign.Synthesis.Homotopy.T6CayleyCodeWalk where

open import Data.Nat using (ℕ)
open import Data.Fin using (Fin)
open import Data.List using (List; []; _∷_; foldl)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Sovereign.Synthesis.Homotopy.BarceloAHomotopy
  using (DiGraph; Walk; nil; cons)
open import Sovereign.Synthesis.Homotopy.T6CayleyVec
  using (T6Vec; updAt; updAt-cubed)
open import Sovereign.Synthesis.Homotopy.T6CayleySym
  using (T6CayleySym; T6SymEdge)
open import Sovereign.Synthesis.Homotopy.T6CayleyCode
  using (CStep; CWalk; cplus; cminus; cstep-inv)

--------------------------------------------------------------------------------
-- §1. 沿一个码算目标顶点（纯计算，无见证）
--------------------------------------------------------------------------------

ctarget : ∀ {n : ℕ} (x : T6Vec n) → CStep n → T6Vec n
ctarget x (cplus j)  = updAt j x
ctarget x (cminus j) = updAt j (updAt j x)

--------------------------------------------------------------------------------
-- §2. ★★ 见证是 `refl`（因为目标顶点由码算出来）
--------------------------------------------------------------------------------

cEdge : ∀ {n : ℕ} (x : T6Vec n) (s : CStep n)
      → T6SymEdge x (ctarget x s)
cEdge x (cplus j)  = inj₁ (j , refl)
cEdge x (cminus j) = inj₂ (j , refl)

--------------------------------------------------------------------------------
-- §3. ★★ 翻译：码走 → (终点顶点 , 走)
--------------------------------------------------------------------------------

interpC : ∀ {n : ℕ} (x : T6Vec n) (w : CWalk n)
          → Σ (T6Vec n) (λ y → Walk (T6CayleySym n) x y)
interpC x []      = x , nil x
interpC x (s ∷ w) with interpC (ctarget x s) w
... | (y , rest) = y , cons (cEdge x s) rest

-- 终点就是逐步 `ctarget`（定义性）
interpC-fst : ∀ {n : ℕ} (x : T6Vec n) (w : CWalk n)
              → proj₁ (interpC x w) ≡ foldl (λ acc s → ctarget acc s) x w
interpC-fst x []      = refl
interpC-fst x (s ∷ w) = interpC-fst (ctarget x s) w

--------------------------------------------------------------------------------
-- §4. ★★★ 码的逆在「目标」意义下正确 —— 靠 `updAt-cubed`（特征 3）
--
-- 两个情形（`cplus` / `cminus`）**归约到同一条引理** `updAt-cubed` ✓
--------------------------------------------------------------------------------

ctarget-inv : ∀ {n : ℕ} (x : T6Vec n) (s : CStep n)
            → ctarget (ctarget x s) (cstep-inv s) ≡ x
ctarget-inv x (cplus j)  = updAt-cubed j x
ctarget-inv x (cminus j) = updAt-cubed j x

--------------------------------------------------------------------------------
-- §5. ⬜ 下一步（判据明确）
--
-- ① **soundness**：`interpC` 后，`creduce` 的每次消去对应 `Ω3Walk⁺`
--    —— 因为消去的一对 `(s, cstep-inv s)` 恰好是一个 `bub`，
--    而 `bub3` 已证（`Omega3Plus`）⇒ 这一步**应该不难**。
-- ② **完备性 / 汇合性**：迭代到不动点是否唯一 —— 本线最硬的一段（未做）。
--------------------------------------------------------------------------------
