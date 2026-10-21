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
open import Data.List using (List; []; _∷_; foldl; reverse; _++_)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans)

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
-- §5. ★★★ 每个码步在目标层都是 3 阶 —— 与 `(C₃)ⁿ` 一致
--
-- `cplus j` 一次一步、`cminus j` 一次两步；但**迭代三次**后：
-- ```
--   ctarget (ctarget (ctarget x s) s) s
--     = updAt j (… (updAt j x))    -- cplus：3 步；cminus：6 步
--     ≡ x                          -- cplus：一次 cubed；cminus：两次 cubed（6 步 = 2×3）
-- ```
-- ⇒ **两个情形归约到同一条 `updAt-cubed`**（特征 3）。
--
-- 这是 `π₁ᵈ(T6Cayley n) ≅ (C₃)ⁿ` 的**生成元阶数**一半
-- （另一半「不同坐标独立」—— ✅ **已证**：`T6CayleyVecOther.updAt-other`）。
--------------------------------------------------------------------------------

ctarget-3 : ∀ {n : ℕ} (x : T6Vec n) (s : CStep n)
          → ctarget (ctarget (ctarget x s) s) s ≡ x
ctarget-3 x (cplus j)  = updAt-cubed j x
ctarget-3 x (cminus j) =
  trans (updAt-cubed j (updAt j (updAt j (updAt j x))))
        (updAt-cubed j x)

--------------------------------------------------------------------------------
-- §6. ★★★ 码走的逆律：反向后终点回到起点
--
-- 这是 `π₁ᵈ` 的**核心要求**（每条走都有反向走回起点），
-- 而证明只用 `ctarget-inv`（← `updAt-cubed`，特征 3）。
--------------------------------------------------------------------------------

-- 逐步折叠（就是「码的右作用」）
foldT : ∀ {n : ℕ} (x : T6Vec n) (w : CWalk n) → T6Vec n
foldT x []      = x
foldT x (s ∷ w) = foldT (ctarget x s) w

-- 作用对拼接可加（自由幺半群作用）
foldT-++ : ∀ {n : ℕ} (x : T6Vec n) (a b : CWalk n)
         → foldT x (a ++ b) ≡ foldT (foldT x a) b
foldT-++ x []      b = refl
foldT-++ x (s ∷ a) b = foldT-++ (ctarget x s) a b

-- 码的倒转 + 取逆
crev : ∀ {n : ℕ} → CWalk n → CWalk n
crev []      = []
crev (s ∷ w) = crev w ++ (cstep-inv s ∷ [])

-- ★★★ 逆律：反向后回到起点
ctarget-rev : ∀ {n : ℕ} (x : T6Vec n) (w : CWalk n)
            → foldT (foldT x w) (crev w) ≡ x
ctarget-rev x []      = refl
ctarget-rev x (s ∷ w) =
  trans (foldT-++ (foldT (ctarget x s) w) (crev w) (cstep-inv s ∷ []))
        (trans (cong (λ z → foldT z (cstep-inv s ∷ []))
                     (ctarget-rev (ctarget x s) w))
               (ctarget-inv x s))

--------------------------------------------------------------------------------
-- §7. ⬜ 下一步（判据明确）
--
-- ⚠ **本码层服务 `π₁ᵈ`，不服务 `π₂ᵈ⁺`**（`Ω2Walk` 的步是 `ASTep`，不是图边）。
--
-- 目标：`π₁ᵈ(T6Cayley n) ≅ (C₃)ⁿ`
--   已备：① 每步 3 阶（`ctarget-3`）；② 逆律（`ctarget-inv` / `ctarget-rev`）；
--         ③ 归约（`creduce`）；④ 作用可加（`foldT-++`）。
--   ⑤ ✅ **已完成**：「不同坐标独立」= `T6CayleyVecOther.updAt-other`（lookup 级，`Vec` 索引引理）；
--         ⑥ 由 ⑤ + ① 得 `foldT` 诱导的映射 `CWalk n / ⁓ → (Fin 3)ⁿ` 是同构。
--------------------------------------------------------------------------------
