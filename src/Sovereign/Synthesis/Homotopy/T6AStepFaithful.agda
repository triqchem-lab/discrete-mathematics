{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Synthesis.Homotopy.T6AStepFaithful
--
-- **码 → 步的「忠实性」到底能陈述成什么**（把一个错误的目标修正为可证形态）
--
-- ## 背景：原始目标不成立
--
-- 最初想写「**不同码 ⇒ 不同步**」（忠实性 = 单射）。读了定义后它**是假的** ✗：
--
-- ```agda
-- srcCode (mkStep _ pref s1 s2 _ suff) = pref ++ (s1 ∷ s2 ∷ suff)   -- 不用 d、不用 s3
-- tgtCode (mkStep _ pref _ _ s3 suff)  = pref ++ (s3 ∷ suff)        -- 不用 d、不用 s1 s2
-- ```
--
-- ⇒ `mkStep dslide  pref s1 s2 s3 suff` 与 `mkStep dexpand pref s1 s2 s3 suff`
--   **共享同一对走**（`srcCode`/`tgtCode` 定义性地相等），却是**不同码** ✓
-- ⇒ **码不由走对决定** ✗（至少 `ADir` 不可从走恢复）
--
-- ## 正确的可证形态（本模块内容）
--
-- `ADir` **不影响步的内容** —— 它只决定 `AHomotopy` 层用哪个方向
-- （`toAHomotopyDir` 按 `d` 分派）。这正是「码里哪部分是步、哪部分是分派标记」的
-- **精确边界**，也是 `ASTep` 层不能分派而 `AHomotopy` 层能分派的**代码层根因**。
--
-- ## 核心原则
--   · 0 postulate / 0 hole；三条定理全部 `refl`（定义性的事实，不是论证）
--   · 复用 `T6AStepMap.srcCode/tgtCode`（不重写）

module Sovereign.Synthesis.Homotopy.T6AStepFaithful where

open import Data.Nat using (ℕ)
open import Data.List using (List; []; _∷_)
open import Data.Product using (_,_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong; cong₂)

open import Sovereign.Synthesis.Homotopy.T6CayleyCode using (CStep; CWalk)
open import Sovereign.Synthesis.Homotopy.T6AStepCode using (ADir; dslide; dexpand)
open import Sovereign.Synthesis.Homotopy.T6AStepCode2 using (StepCode; mkStep)
open import Sovereign.Synthesis.Homotopy.T6AStepMap using (srcCode; tgtCode)

--------------------------------------------------------------------------------
-- §1. ★ `ADir` 不影响走（定义性）
--------------------------------------------------------------------------------

srcCode-dir-irrel : ∀ {n : ℕ} (d d' : ADir) (pref : CWalk n)
                    (s1 s2 s3 : CStep n) (suff : CWalk n)
                  → srcCode (mkStep d  pref s1 s2 s3 suff)
                  ≡ srcCode (mkStep d' pref s1 s2 s3 suff)
srcCode-dir-irrel _ _ _ _ _ _ _ = refl

tgtCode-dir-irrel : ∀ {n : ℕ} (d d' : ADir) (pref : CWalk n)
                    (s1 s2 s3 : CStep n) (suff : CWalk n)
                  → tgtCode (mkStep d  pref s1 s2 s3 suff)
                  ≡ tgtCode (mkStep d' pref s1 s2 s3 suff)
tgtCode-dir-irrel _ _ _ _ _ _ _ = refl

--------------------------------------------------------------------------------
-- §2. ★ 因此「码由走对决定」是**假的** —— 显式反例骨架
--
-- 结论写成 `Set` 而非 `¬`，因为否定需要先有「码相等」的可判定比较
-- （有：`DecEq-StepCode`，见 `T6AStepCode2`）；这里直接给**两条不同的码**：
--
--   `mkStep dslide  pref s1 s2 s3 suff`   与
--   `mkStep dexpand pref s1 s2 s3 suff`
--
-- 它们 `srcCode`/`tgtCode` **定义性相等**（§1 的两条），而构造函数参数 `d` 不同
-- ⇒ 不存在 `walks ↦ code` 的函数使其同时还原两者 ⇒ **忠实性（单射）陈述为假**。
--------------------------------------------------------------------------------

-- 证人的「走对相同」：直接由 §1 组合
same-walks : ∀ {n : ℕ} (pref : CWalk n) (s1 s2 s3 : CStep n) (suff : CWalk n)
           → ( srcCode (mkStep dslide  pref s1 s2 s3 suff)
             , tgtCode (mkStep dslide  pref s1 s2 s3 suff) )
           ≡ ( srcCode (mkStep dexpand pref s1 s2 s3 suff)
             , tgtCode (mkStep dexpand pref s1 s2 s3 suff) )
same-walks pref s1 s2 s3 suff =
  cong₂ (λ a b → (a , b))
        (srcCode-dir-irrel dslide dexpand pref s1 s2 s3 suff)
        (tgtCode-dir-irrel dslide dexpand pref s1 s2 s3 suff)

--------------------------------------------------------------------------------
-- §3. 小结 / 如实边界
--
-- ✅ 已证：`ADir` 不影响 `srcCode`/`tgtCode`（§1），因此同一对走对应 ≥2 个码（§2 的形）。
-- ⬜ 未做：`suff` 与 `s1 s2 s3` 的可恢复性（需先证 `++` 的消去，且 `suff` 本身
--        在 `pref ++ [s1,s2] ++ suff` 里**不可唯一恢复** ⇒ 那条也更可能是假的）。
--------------------------------------------------------------------------------
--------------------------------------------------------------------------------
-- §3. ★★ 「码不能由走对恢复」—— 从判断升级为**已证命题**
--
-- §2 只是结构观察；本节把它写成**否定命题**并证。
-- 做法：**参数化**（不需要具体 `CStep` 值）——给任意 `pref / s1 s2 s3 / suff`，
-- 都能造出两个只差 `ADir` 的码，它们走对相同但码不同。
--------------------------------------------------------------------------------

-- 两种方向标记不同（构造子互异 ⇒ 一行）
dslide≢dexpand : dslide ≢ dexpand
dslide≢dexpand ()

-- `mkStep` 是**同一个构造子**（不是互异构造子）⇒ 从参数分出来：取其第一个参数
mkStep-dir : ∀ {n : ℕ} (d d' : ADir) (pref : CWalk n)
             (s1 s2 s3 : CStep n) (suff : CWalk n)
           → mkStep d  pref s1 s2 s3 suff ≡ mkStep d' pref s1 s2 s3 suff
           → d ≡ d'
mkStep-dir d d' pref s1 s2 s3 suff p =
  cong (λ { (mkStep e _ _ _ _ _) → e }) p

-- ★★ 主定理：**不存在**「由走对恢复码」的函数
--    （等价说法：`(srcCode, tgtCode)` 对 `StepCode` **不是单射**）
no-walks-recover-code :
  ∀ {n : ℕ} (pref : CWalk n) (s1 s2 s3 : CStep n) (suff : CWalk n)
  → ¬ (∀ (c c' : StepCode n)
       → srcCode c ≡ srcCode c' → tgtCode c ≡ tgtCode c' → c ≡ c')
no-walks-recover-code pref s1 s2 s3 suff h =
  dslide≢dexpand
    (mkStep-dir dslide dexpand pref s1 s2 s3 suff
      (h (mkStep dslide  pref s1 s2 s3 suff)
         (mkStep dexpand pref s1 s2 s3 suff) refl refl))

