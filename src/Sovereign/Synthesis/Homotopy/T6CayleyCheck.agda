{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Synthesis.Homotopy.T6CayleyCheck
--
-- **对抗验证（纪律 §6）：①②③ 在具体点上用 `refl` 交叉比对**
--
-- ④ 线已有具体点验证（`T6CayleyInterp.step-1`）；本模块补 ①②③：
--
-- | 定理 | 具体点检验什么 |
-- |---|---|
-- | ① `creduceA` 范式性 | 归约结果里**没有**可消相邻对 |
-- | ② `creduceA` 幂等 | `creduceA (creduceA w) ≡ creduceA w` |
-- | ③ 语义正确 | 归约**不改**终点（`foldT`）|
--
-- 取最少的具体例子（`n = 1`）：
--
-- | `w` | 期望 `creduceA w` | 理由 |
-- |---|---|---|
-- | `[]` | `[]` | 空 |
-- | `[+e₀]` | `[+e₀]` | 无可消对 |
-- | `[+e₀, −e₀]` | `[]` | **互逆对消掉** |
-- | `[+e₀, +e₀, +e₀]` | `[+e₀, +e₀, +e₀]` | 三步归零是**顶点**层，不是消去层 |
-- | `[−e₀, +e₀]` | `[]` | 反向的互逆对也消（`adj-sym'`）|
--
-- 全部是 `refl` —— 不是「论证」，是**计算** ✓
--
-- ## 核心原则
--   · 0 postulate / 0 hole；零 Cubical
--   · 复用 `T6CayleyNorm.creduceA`（不重写任何件）

module Sovereign.Synthesis.Homotopy.T6CayleyCheck where

open import Data.Nat using (ℕ)
open import Data.List using ([]; _∷_)
open import Data.Fin using (zero)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Sovereign.Synthesis.Homotopy.T6CayleyVec using (T6Vec; updAt; updAt-cubed)
open import Relation.Binary.PropositionalEquality using (sym; cong)
open import Sovereign.Synthesis.Homotopy.T6CayleyCode using (CStep; CWalk; cplus; cminus)
open import Sovereign.Synthesis.Homotopy.T6CayleyNorm using (creduceA)
open import Sovereign.Synthesis.Homotopy.T6CayleyCodeWalk using (foldT; ctarget)
open import Sovereign.Synthesis.Homotopy.T6CayleyInterp
  using (interpAt; x1; stepE1; stepE2; stepE3; side-ok; toStep)
open import Sovereign.Synthesis.Homotopy.T6AStepCodeMap using (toStepExpand)
open import Sovereign.Synthesis.Homotopy.T6CayleySym using (T6CayleySym)
open import Sovereign.Synthesis.Homotopy.BarceloAHomotopy using (Walk; nil; cons; _++w_; AStep)
open import Sovereign.Synthesis.Homotopy.AStepStd using (AHomotopyStd)
open import Sovereign.Synthesis.Homotopy.AStepStdGroup using (rev)
open import Sovereign.Synthesis.Homotopy.T6SymEdgeReverse using (sym-edge-T6; rev-cancel-T6)
open import Sovereign.Synthesis.Homotopy.T6CayleyCodeWalk using (cEdge)

--------------------------------------------------------------------------------
-- §1. 起点：`n = 1` 的零向量
--------------------------------------------------------------------------------

-- ⚠ `x1 : T6Vec 1` **复用** `T6CayleyInterp` 的定义（不重造，依重复符号闸门纪律）。

ep : CStep 1
ep = cplus zero

em : CStep 1
em = cminus zero

--------------------------------------------------------------------------------
-- §2. ★ ① 与 ② 的具体点检验（全部 `refl`）
--------------------------------------------------------------------------------

-- 空：归约不动
check-nil : creduceA {n = 1} [] ≡ []
check-nil = refl

-- 单步：无可消对，归约不动
check-one : creduceA {n = 1} (ep ∷ []) ≡ (ep ∷ [])
check-one = refl

-- ★ 互逆对**消掉**
check-cancel-pair : creduceA {n = 1} (ep ∷ em ∷ []) ≡ []
check-cancel-pair = refl

-- ★ 反向的互逆对也消
check-cancel' : creduceA {n = 1} (em ∷ ep ∷ []) ≡ []
check-cancel' = refl

-- 三步同向：**不消**（三步归零是顶点层，不是消去层）
check-three : creduceA {n = 1} (ep ∷ ep ∷ ep ∷ []) ≡ (ep ∷ ep ∷ ep ∷ [])
check-three = refl

-- ★★ ② 幂等在具体点（两种例子）
check-idem-1 : creduceA {n = 1} (creduceA {n = 1} (ep ∷ em ∷ []))
             ≡ creduceA {n = 1} (ep ∷ em ∷ [])
check-idem-1 = refl

check-idem-2 : creduceA {n = 1} (creduceA {n = 1} (ep ∷ ep ∷ em ∷ em ∷ []))
             ≡ creduceA {n = 1} (ep ∷ ep ∷ em ∷ em ∷ [])
check-idem-2 = refl

--------------------------------------------------------------------------------
-- §3. ★ ③ 语义在具体点：归约**不改**终点
--------------------------------------------------------------------------------

-- 互逆对消掉后终点仍是 `x`（`−e₀` 把 `+e₀` 抵消）
check-end : foldT x1 (creduceA {n = 1} (ep ∷ em ∷ [])) ≡ foldT x1 (ep ∷ em ∷ [])
check-end = refl

-- ★ 走一步的终点 = `updAt 0 x`（与 `interpAt` 侧的 `endpoint-1` 同一事实的另一半）
check-interp : foldT x1 (ep ∷ []) ≡ updAt zero x1
check-interp = refl

--------------------------------------------------------------------------------
-- §4. ★★ ⑤ 的具体点验证（此前 ①②③④ 都有，⑤ 独缺）
--
-- `rev-cancel-T6` 产出的是 `AHomotopyStd` 的**值**（不是等式）
-- ⇒ 具体点检验 = **在具体走上实例化**并确认类型对上（同 `step-1` 的手法）。
-- 再加一条 `refl`：一步走的逆走**算得出来**。
--------------------------------------------------------------------------------

check-p1 : Walk (T6CayleySym 1) x1 (updAt zero x1)
check-p1 = cons (cEdge x1 ep) (nil _)

-- ★ `refl`：一步走的逆 = 反向的那一步（`rev` 与 `sym-edge-T6` 的具体计算）
check-rev-one : rev sym-edge-T6 check-p1 ≡ cons (sym-edge-T6 (cEdge x1 ep)) (nil _)
check-rev-one = refl

-- ★★ 具体点实例化：`[+e₀] ++ 逆走` A-同伦于空走
check-rev-cancel : AHomotopyStd (T6CayleySym 1)
                     (check-p1 ++w rev sym-edge-T6 check-p1) (nil x1)
check-rev-cancel = rev-cancel-T6 check-p1

--------------------------------------------------------------------------------
-- §5. ★★ ④ 的 expand 侧具体点（此前 `step-1` 只验了 slide 侧）
--
-- 按「逐个核对构造子/分支覆盖率」的教训：`ASTep` 有两个构造子，
-- 而此前**只有一个**有具体点验证 ✗ ⇒ 本批补上 `expand` 侧。
--------------------------------------------------------------------------------

step-1e : AStep (T6CayleySym 1)
            (interpAt x1 [] ++w
              (cons (stepE3 x1 [] (cminus zero) side-ok)
                    (interpAt (ctarget (ctarget x1 (cplus zero)) (cplus zero)) [])))
            (interpAt x1 [] ++w
              (cons (stepE1 x1 [] (cplus zero))
                    (cons (stepE2 x1 [] (cplus zero) (cplus zero))
                          (interpAt (ctarget (ctarget x1 (cplus zero)) (cplus zero)) []))))
step-1e = toStepExpand x1 [] (cplus zero) (cplus zero) (cminus zero) [] side-ok

--------------------------------------------------------------------------------
-- §6. ★★ ④ 的**混合方向**具体点（`s1`/`s2` 取 `cminus`，此前只验过 `cplus`）
--
-- 此前 `step-1`/`step-1e` 都取 `s1 = s2 = cplus`、`s3 = cminus`
-- ⇒ **`cminus` 在 `s1`/`s2` 位置从未被具体点验过** ✗
--
-- 本批取 `s1 = s2 = cminus`、`s3 = cplus`：
--   `y = x−2e`、`z = y−2e = x−4e = x+e`（因 `3e = 0`），而 `ctarget x (cplus 0) = x+e` ✓
-- ⇒ 侧条件成立，但**不是 `refl`**（要靠 `updAt-cubed` 推），所以单独立一条。
--------------------------------------------------------------------------------

side-m : ctarget x1 (cplus zero)
       ≡ ctarget (ctarget x1 (cminus zero)) (cminus zero)
side-m = sym (cong (updAt zero) (updAt-cubed zero x1))

step-1m : AStep (T6CayleySym 1)
            (interpAt x1 [] ++w
              (cons (stepE1 x1 [] (cminus zero))
                    (cons (stepE2 x1 [] (cminus zero) (cminus zero))
                          (interpAt (ctarget (ctarget x1 (cminus zero)) (cminus zero)) []))))
            (interpAt x1 [] ++w
              (cons (stepE3 x1 [] (cplus zero) side-m)
                    (interpAt (ctarget (ctarget x1 (cminus zero)) (cminus zero)) [])))
step-1m = toStep x1 [] (cminus zero) (cminus zero) (cplus zero) [] side-m
