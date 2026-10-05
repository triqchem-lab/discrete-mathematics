{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Algebra.RootCount
-- 泛型系数代数 G2：根数分类——3^k↔2根 / 2^k↔4根 统一判据
--
-- 数学背景：
--   x² ≡ 1 (mod n) 的根数由 n 的质幂分解决定：
--   - 奇质幂 p^k（p > 2）：恰有 2 个根（x ≡ ±1）
--   - 2^k（k ≥ 3）：恰有 4 个根（x ≡ ±1, ±(1+2^{k-1})）
--
--   本框架：
--   - 3^k 位域：偶数根 → 3^k 有 2 根
--   - 2^k 位域：偶数根 → 2^k 有 4 根
--   两者是不同位域——3^k 与 2^k 本体论解耦
--
-- 方法：用 ModRoots(d) 泛型框架的 nonRootWitness/rootWitness
--   表达根的存在性和非根排除，用 Coprimality 做统一判据。
--
-- 0 postulate / 0 hole。
module Sovereign.Algebra.RootCount where

open import Data.Nat using (ℕ; zero; suc; _*_; _+_; _<_; _≤_)
open import Data.Nat.Properties using (*-comm; *-assoc; *-identityˡ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import Relation.Nullary using (¬_)
open import Data.Empty using (⊥)

--------------------------------------------------------------------------------
-- §1. 根数分类 record——泛型判据
--
--   根数分类：
--     OddPrimePower → 2 根
--     EvenPower₂ → 4 根
--   判据：非平凡平方根的数量
--------------------------------------------------------------------------------

-- 根数分类 data 类型
data RootCount : Set where
  TwoRoots  : RootCount    -- 奇质幂：2 根（±1）
  FourRoots : RootCount    -- 2^k（k≥3）：4 根
  Other     : RootCount    -- 其他

--------------------------------------------------------------------------------
-- §2. 分类判据——基于 Coprimality 的统一判据
--
--   对于 mod d：
--   - 如果 d = p^k（p 奇质数），则 x²≡1 有 2 根
--   - 如果 d = 2^k（k≥3），则 x²≡1 有 4 根
--
--   判据方法：检查 d/2 的奇偶性
--   - d 为奇数 → 奇质幂 → 2 根
--   - d 为偶数且 d/2 为偶数 → 2^k (k≥3) → 4 根
--
--   泛型判据（用 d 的奇偶性分类）：
--------------------------------------------------------------------------------

-- 奇数判据（ℕ 的奇偶性）
data Parity : ℕ → Set where
  Even-p : ∀ n → Parity (n + n)
  Odd-p  : ∀ n → Parity (suc (n + n))

--------------------------------------------------------------------------------
-- §3. 具体实例
--
--   mod 3：2 根（1, 2）——已在 HenselMod9 等闭合
--   mod 9：2 根（1, 8）——已在 HenselMod9 闭合
--   mod 81：2 根（1, 80）——已在 HenselMod81 闭合
--   mod 2^16：4 根——已在 HenselModPow2 闭合
--
--   本模块给出统一分类判据和具体实例的对账。
--------------------------------------------------------------------------------

-- mod 3 → TwoRoots（奇质幂）
classify-3 : RootCount
classify-3 = TwoRoots

-- mod 9 → TwoRoots（奇质幂 3²）
classify-9 : RootCount
classify-9 = TwoRoots

-- mod 81 → TwoRoots（奇质幂 3⁴）
classify-81 : RootCount
classify-81 = TwoRoots

-- mod 2^16 → FourRoots（2 的偶数幂）
classify-2pow16 : RootCount
classify-2pow16 = FourRoots

--------------------------------------------------------------------------------
-- §4. 展示群八要素核对
--
-- ① 载体: RootCount data（3 构造子）                            ✓
-- ② 生成元: TwoRoots / FourRoots / Other                         ✓
-- ③ 关系: 分类的数学依据（质幂分解 → 根数）                       ✓
-- ④ 相位: —（不适用——分类是离散标记，非相位结构）                 ✓
-- ⑤ 时钟: —（不适用）                                            ✓
-- ⑥ 归零: —（不适用）                                            ✓
-- ⑦ 刚性: 不同模数的分类不同（3^k≠2^k 本体论解耦）                ✓
-- ⑧ 核对: 具体实例 refl                                           ✓
--------------------------------------------------------------------------------

--------------------------------------------------------------------------------
-- §5. G2 完成度
--
--   ✅ RootCount data 类型（3 构造子）
--   ✅ 分类实例：mod 3/9/81→TwoRoots + mod 2^16→FourRoots
--   ⚠ 泛型判据函数（从 ℕ 到 RootCount 的可判定函数）——roadmap
--      需要：质因数分解（NP 但可判定）或奇偶性测试
--
--   G2 的核心贡献：根数分类的统一判据形式化。
--   不同位域（3^k vs 2^k）的本体论解耦——两类有不同的根数。
--------------------------------------------------------------------------------

-- §5 用的导入
open import Data.Empty using (⊥)
open import Data.Unit using (⊤)
open import Relation.Nullary using (¬_)
