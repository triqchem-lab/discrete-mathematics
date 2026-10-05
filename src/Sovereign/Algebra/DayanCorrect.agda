{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Algebra.DayanCorrect
-- 大衍求一术 L2 不变量定理——框架与义务类型（实现 roadmap）
--
-- 数学内容：
--   不变量：lt × 奇 + lb × 定 = right-top（在每一步保持）
--   初始：1 × 奇 + 0 × 定 = 奇 ✓
--   终止：right-top = 1 ⟹ lt × 奇 + lb × 定 = 1
--   推论：lt × 奇 ≡ 1 (mod 定)（乘率性质）
--
-- 诚实边界：L2 框架建立，三个义务的实现需要 ℤ 或详细 ℕ 代数 + 终止性证明（S-D3）。
--   本模块只给出义务类型签名和数学推导，不给出证明项。
--
-- 0 postulate / 0 hole。
module Sovereign.Algebra.DayanCorrect where

open import Data.Nat using (ℕ; zero; suc; _*_; _+_; _∸_; _/_; _%_; _<_; NonZero)
open import Data.Nat.Properties using (m∸n+n≡m; m+n∸n≡m; +-∸-comm; *-distribˡ-+; *-distribʳ-+)
open import Data.Nat.DivMod using (%-distribˡ-+)
open import Data.Nat.DivMod using (%-distribˡ-+)
open import Data.Nat.Properties using (+-identityʳ)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong; sym; trans; module ≡-Reasoning)
open ≡-Reasoning

--------------------------------------------------------------------------------
-- §1. DayanState 引入
--------------------------------------------------------------------------------

open import Sovereign.Algebra.DayanState
  using (DayanState; dayan; dayan-init; dayan-step; dayan-terminates;
         left-top; left-bottom; right-top; right-bottom)

--------------------------------------------------------------------------------
-- §2. 不变量定义
--
--   Invariant 奇 定 s := (left-top s × 奇 + left-bottom s × 定) ≡ right-top s
--
--   数学含义：lt 是奇的系数，lb 是定的系数，它们的线性组合 = 当前余数。
--   这是 Bezout 恒等式的递推形式。
--------------------------------------------------------------------------------

Invariant : (奇 定 : ℕ) → DayanState → Set
Invariant 奇 定 s =
  (left-top s * 奇 + left-bottom s * 定) ≡ right-top s

--------------------------------------------------------------------------------
-- §3. 三个证明义务（L2 核心）
--------------------------------------------------------------------------------

-- 义务 1：初始状态满足不变量
--   dayan-init 奇 定 = dayan 1 0 奇 定
--   代入：1 × 奇 + 0 × 定 = 奇 + 0 ≡ 奇
--   需要：ℕ 的 *-identityˡ, *-zeroʳ, +-identityʳ
init-invariant-type : Set
init-invariant-type = ∀ (奇 定 : ℕ) → Invariant 奇 定 (dayan-init 奇 定)

-- 义务 2：每一步保持不变量
--   标准 Bezout 递推：new_lt = lb - q×lt, new_lb = lt, new_rt = r
--   需要：旧不变量 + 除法关系 rb = q×rt + r + ℕ/ℤ 代数
--   ⚠ 需要 NonZero (right-top s)（dayan-step 的依赖）——终止性证明核心
step-invariant-type : Set
step-invariant-type =
  ∀ (奇 定 : ℕ) (s : DayanState) →
  Invariant 奇 定 s →
  ⦃ _ : NonZero (right-top s) ⦄ →
  Invariant 奇 定 (dayan-step s)

-- 义务 3：终止时推出乘率性质
--   终止时 right-top = 1，代入不变量：
--     lt × 奇 + lb × 定 = 1
--   两边 mod 定：
--     lt × 奇 ≡ 1 (mod 定)
--   需要：ℕ 的 mod 性质
terminate-correct-type : Set
terminate-correct-type =
  ∀ (奇 定 : ℕ) (s : DayanState) →
  ⦃ _ : NonZero 定 ⦄ →
  Invariant 奇 定 s →
  right-top s ≡ 1 →
  (left-top s * 奇) % 定 ≡ 1

--------------------------------------------------------------------------------
-- §4. L2 完成度评估
--
--   义务 1（init-invariant）：⚠ 需要 ℕ 代数（*-identityˡ, *-zeroʳ, +-identityʳ）
--   义务 2（step-invariant）：⚠ 需要 ℤ 或 ℕ 代数 + NonZero 约束（S-D3 依赖）
--   义务 3（terminate-correct）：⚠ 需要 mod 性质 + NonZero 约束
--
--   框架已建立。不变量定理与输入规模无关——天文历法的大数输入由不变量直接覆盖。
--
--   下一步：
--   ① 用 ℤ 实现不变量（更干净，忠实秦九韶算筹正负约定）
--   ② 证明 S-D3 终止性（right-top 递减）
--   ③ 完成三个义务的证明项
--------------------------------------------------------------------------------
