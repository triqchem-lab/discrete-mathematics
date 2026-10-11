{-# OPTIONS --rewriting --guardedness #-}

-- | _PW2
-- 接线续批：余叶件扩面（前批 _PW1 五线范式续——每条接线=可编译对账定理+真实 import 边）
--
-- 核心原则：
--   1. 每条接线 = 可编译对账定理（refl/trans 级核对）+ 真实 import 边——不是注释
--   2. 不改旧件语义（只引不改）
--   3. 六条高价值线：UniformProb×DiscreteProbability / Primes×Hensel /
--      DFA×RegularGrammar（正则面自洽）/ LinearRecurrence×GF(3) 特征 /
--      Designs×Counting / Partitions×Multisets（载体面）
--
-- 包含：w2-uniform-norm-agree · w2-primes-hensel3 · w2-egs-mod2-ε
--       · w2-fib3-step · w2-design-binom · w2-part-mult-carrier

module _PW2 where

open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_)
open import Data.List using (List; []; _∷_)
open import Data.Fin using (Fin; toℕ) renaming (zero to fzero; suc to fsuc)
open import Data.Unit using (⊤; tt)
open import Data.Bool using (Bool; true; false)
open import Data.Product using (_×_; _,_)
open import Data.Nat.Divisibility using (_∣_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans)

open import Sovereign.Base.Trit using (Trit; T₀; T₁; T₂; _⊕_)

-- 线①：DiscreteProbability × UniformProb（归一化面对账——两侧 ≡ 3）
open import Sovereign.Application.DiscreteProbability using (uniform; uniform-norm)
open import Sovereign.Application.UniformProb using (count; normalization)

-- 线②：Primes × HenselLiftMinimal（Hensel 前提的素数侧锚）
open import Sovereign.Algebra.NumberTheory.Primes using (IsPrime; isPrime-3)
open import Sovereign.Algebra.HenselLiftMinimal using (root-1-mod-3)

-- 线③：DFA × RegularGrammar（正则面自洽网锚）
open import Sovereign.Algebra.Automata.DFA using (mod2; Lang; check-mod2-empty)
open import Sovereign.Algebra.Automata.RegularGrammar using (Generates; egProd; check-gen-ε)

-- 线④：LinearRecurrence × GF(3) 特征面（Fib 步进律 = ⊕ 形）
open import Sovereign.Arithmetic.LinearRecurrence using (fib3)

-- 线⑤：Designs × Counting（点对共现计数 = 二项式面）
open import Sovereign.Algebra.Combinatorics.Designs using (countB; tri-blocks; check-pair-01)
open import Sovereign.Algebra.Combinatorics.Counting using (binom; binom-n-n)

-- 线⑥：Partitions × Multisets（载体面——分拆的多重集承载）
open import Sovereign.Algebra.Combinatorics.Partitions using (toMulti; countVal)
open import Sovereign.Algebra.Combinatorics.Multisets using (Multi; size)

-- ────────────────────────────────────────────────────────────────────
-- §1 线①：归一化面对账
--   uniform-norm : uniform T₀ + uniform T₁ + uniform T₂ ≡ 3
--   normalization : count {3} (λ _ → true) ≡ 3
--   ⇒ 两形在 3 处相遇——DiscreteProbability 的权面与 UniformProb 的计数面归一
-- ────────────────────────────────────────────────────────────────────

w2-uniform-norm-agree : uniform T₀ + uniform T₁ + uniform T₂ ≡ count {3} (λ _ → true)
w2-uniform-norm-agree = trans uniform-norm (sym (normalization 3))

-- ────────────────────────────────────────────────────────────────────
-- §2 线②：Hensel 前提的素数侧锚
--   isPrime-3 : IsPrime 3（NumberTheory 侧）
--   root-1-mod-3 : 3 ∣ ((1 * 1) ∸ 1)（Hensel 塔侧根前提）
--   ⇒ 素数面与 Hensel 塔前提同点对账
-- ────────────────────────────────────────────────────────────────────

w2-primes-hensel3 : IsPrime 3 × (3 ∣ ((1 * 1) ∸ 1))
w2-primes-hensel3 = isPrime-3 , root-1-mod-3

-- ────────────────────────────────────────────────────────────────────
-- §3 线③：正则面自洽网
--   check-gen-ε : Generates egProd tt []（文法侧生成空词）
--   check-mod2-empty : Lang mod2 []（自动机侧接受空词）
--   ⇒ 两正则面机件同词锚定
-- ────────────────────────────────────────────────────────────────────

w2-egs-mod2-ε : Generates egProd tt [] × Lang mod2 []
w2-egs-mod2-ε = check-gen-ε , check-mod2-empty

-- ────────────────────────────────────────────────────────────────────
-- §4 线④：Fib 步进律 = GF(3) ⊕ 形
--   fib3 = Fib 型 GF(3) 递推（前五项 0,1,1,2,0）——步进律在 ⊕ 上形变自洽
-- ────────────────────────────────────────────────────────────────────

w2-fib3-step : fib3 2 ≡ fib3 1 ⊕ fib3 0
w2-fib3-step = refl

-- ────────────────────────────────────────────────────────────────────
-- §5 线⑤：点对共现计数 = 二项式面
--   check-pair-01 : countB fzero (fsuc fzero) tri-blocks ≡ 1
--   binom-n-n : binom n n ≡ 1
--   ⇒ 设计面点对覆盖与组合面边缘律对账
-- ────────────────────────────────────────────────────────────────────

w2-design-binom : countB fzero (fsuc fzero) tri-blocks ≡ binom 2 2
w2-design-binom = trans check-pair-01 (sym (binom-n-n 2))

-- ────────────────────────────────────────────────────────────────────
-- §6 线⑥：分拆的多重集承载（载体面）
--   toMulti : List ℕ → Multi (suc n)（Partitions → Multisets 载体映射）
--   ⇒ 分拆面与多重集面的承载自洽（defeq 形）
-- ────────────────────────────────────────────────────────────────────

w2-part-mult-carrier : ∀ {n} (xs : List ℕ) → Multi (suc n)
w2-part-mult-carrier {n} xs = toMulti {n} xs

w2-part-mult-def : ∀ {n} (xs : List ℕ) (i : Fin (suc n)) → toMulti xs i ≡ countVal (toℕ i) xs
w2-part-mult-def xs i = refl
