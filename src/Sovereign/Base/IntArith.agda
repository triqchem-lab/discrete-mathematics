{-# OPTIONS --cubical --guardedness #-}

-- | Sovereign.Base.IntArith
-- Cubical ℤ 算术补丁引理（减法与加法重排）
--
-- 核心原则：
--   1. 减法重排 ≠ negDistrib（等式里没有负号）
--   2. 4 条独立引理组合，不写 subst 链
--   3. 纯字母名避开 +pos 解析冲突
--
-- 包含：sucPush, pos-+pos, sucℤ-minus, minus-assoc, minus-shift

-- ③ 基础件层（sucPush/pos-+pos 等桥件）→ ④ 主引理层（negDistrib 族）→ ⑥ 核对层（补件区 refl 交叉）

module Sovereign.Base.IntArith where

-- ② 导入区
open import Cubical.Data.Nat using (ℕ; zero; suc; _∸_) renaming (_+_ to _+ℕ_)
open import Cubical.Data.Nat.Properties using (+-zero; +-suc)
open import Cubical.Data.Int using (ℤ; _+_; _-_; pos; negsuc; _+negsuc_; sucℤ; predℤ; _+pos_)
open import Cubical.Data.Int.Properties using (+Comm; +Assoc; minusPlus; plusMinus; -Cancel; -Cancel'; neg+; -pos; -neg; predℤ+negsuc; predℤ+pos; -predℤ; -sucℤ; predSuc; sucPred)
open import Cubical.Foundations.Prelude using (_≡_; refl; sym; cong; cong₂; _∙_; Σ; _,_; fst; snd)

-- ────────────────────────────────────────────────────────────────────
-- sucInt : sucℤ (x + y) ≡ sucℤ x + y
-- ────────────────────────────────────────────────────────────────────

sucInt : ∀ x y → sucℤ (x + y) ≡ sucℤ x + y
sucInt x (pos zero) = refl
sucInt x (pos (suc n)) = cong sucℤ (sucInt x (pos n))
sucInt x (negsuc n) =
      cong sucℤ (plusnegsuc-predL x n)
      ∙ sucPred (sucℤ x +negsuc n)
      where
      -- 强化引理：x +negsuc n ≡ predℤ (sucℤ x +negsuc n)（对 n 归纳）
      plusnegsuc-predL : ∀ z n → z +negsuc n ≡ predℤ (sucℤ z +negsuc n)
      plusnegsuc-predL z zero = sym (cong predℤ (predSuc z))
      plusnegsuc-predL z (suc n) = cong predℤ (plusnegsuc-predL z n)

-- ────────────────────────────────────────────────────────────────────
-- addPos : ℤ → ℕ → ℤ（纯字母名避开 +pos 解析冲突）
-- ────────────────────────────────────────────────────────────────────

addPos : ℤ → ℕ → ℤ
addPos x zero = x
addPos x (suc k) = sucℤ (addPos x k)

addPos-def : ∀ x k → addPos x k ≡ x + pos k
addPos-def x zero = refl
addPos-def x (suc k) = cong sucℤ (addPos-def x k)

-- ────────────────────────────────────────────────────────────────────
-- sucPush : sucℤ (x + y) ≡ sucℤ x + y（sucℤ 对加法的分配）
-- 用 sucInt renaming 避开 sucℤ+ 解析冲突
-- ────────────────────────────────────────────────────────────────────

sucPush : ∀ x y → sucℤ (x + y) ≡ sucℤ x + y
sucPush x y = sucInt x y

-- ────────────────────────────────────────────────────────────────────
-- pos-+pos : pos a +pos b ≡ pos (a +ℕ b)
-- ────────────────────────────────────────────────────────────────────

pos-+pos : ∀ (a b : ℕ) → _+pos_ (pos a) b ≡ pos (a +ℕ b)
pos-+pos a zero = cong pos (sym (+-zero a))
pos-+pos a (suc b) = cong sucℤ (pos-+pos a b) ∙ cong pos (sym (+-suc a b))

-- ────────────────────────────────────────────────────────────────────
-- negDistrib : -(x + y) ≡ -x + -y（用 neg+ 组合）
-- ────────────────────────────────────────────────────────────────────

-- pos/negsuc 情形提取为独立引理（供 negsuc/pos 对称情形跨函数调用，避开终止检查字典序）
negDistrib-pos-negsuc : ∀ a b → Cubical.Data.Int.-_ (pos a + negsuc b) ≡ Cubical.Data.Int.-_ (pos a) + Cubical.Data.Int.-_ (negsuc b)
negDistrib-pos-negsuc a zero = -predℤ (pos a)
negDistrib-pos-negsuc a (suc b) = -predℤ (pos a +negsuc b) ∙ cong sucℤ (negDistrib-pos-negsuc a b)

negDistrib : ∀ x y → Cubical.Data.Int.-_ (x + y) ≡ Cubical.Data.Int.-_ x + Cubical.Data.Int.-_ y
negDistrib (pos a) (pos b) = cong Cubical.Data.Int.-_ (pos-+pos a b) ∙ -pos (a +ℕ b) ∙ neg+ a b ∙ cong₂ _+_ (sym (-pos a)) (sym (-pos b))
negDistrib (pos a) (negsuc zero) = negDistrib-pos-negsuc a zero
negDistrib (pos a) (negsuc (suc b')) = -predℤ (Cubical.Data.Int._+negsuc_ (pos a) b') ∙ cong sucℤ (negDistrib (pos a) (negsuc b'))
negDistrib (negsuc a) (pos zero) = refl
negDistrib (negsuc a) (pos (suc b')) =
      cong Cubical.Data.Int.-_ (+Comm (negsuc a) (pos (suc b')))
      ∙ negDistrib-pos-negsuc (suc b') a
      ∙ +Comm (Cubical.Data.Int.-_ (pos (suc b'))) (Cubical.Data.Int.-_ (negsuc a))
negDistrib (negsuc a) (negsuc zero) = refl
negDistrib (negsuc a) (negsuc (suc b')) = -predℤ (Cubical.Data.Int._+negsuc_ (negsuc a) b') ∙ cong sucℤ (negDistrib (negsuc a) (negsuc b'))

-- ────────────────────────────────────────────────────────────────────
-- sucℤ-minus : sucℤ (x - y) ≡ sucℤ x - y（sucℤ 对减法的分配）
-- ────────────────────────────────────────────────────────────────────

sucℤ-minus : ∀ x y → sucℤ (x - y) ≡ sucℤ x - y
sucℤ-minus x y = sucPush x (Cubical.Data.Int.-_ y)

-- ────────────────────────────────────────────────────────────────────
-- minus-assoc : x - (y + z) ≡ (x - y) - z（减法结合）
-- ────────────────────────────────────────────────────────────────────

minus-assoc : ∀ x y z → x - (y + z) ≡ (x - y) - z
minus-assoc x y z = cong (x +_) (negDistrib y z) ∙ +Assoc x (Cubical.Data.Int.-_ y) (Cubical.Data.Int.-_ z)

-- ────────────────────────────────────────────────────────────────────
-- minus-shift : (x - y) + z ≡ (x + z) - y（减法与加法交换）
-- ────────────────────────────────────────────────────────────────────

minus-shift : ∀ x y z → (x - y) + z ≡ (x + z) - y
minus-shift x y z = sym (+Assoc x (Cubical.Data.Int.-_ y) z) ∙ cong (x +_) (+Comm (Cubical.Data.Int.-_ y) z) ∙ +Assoc x z (Cubical.Data.Int.-_ y)

-- ─── 2026-10-11 补件 ───
-- negDistrib-suc : negDistrib 的 (negsuc a, pos (suc b)) 情形提层（下游按名引用）
-- 归约链：-(negsuc a + pos (suc b)) →[+Comm 换序]→ -(pos (suc b) + negsuc a)
--   →[negDistrib-pos-negsuc]→ -pos (suc b) + -negsuc a →[+Comm 换回]→ (- negsuc a) + (- pos (suc b))
negDistrib-suc : ∀ a b → Cubical.Data.Int.-_ (negsuc a + pos (suc b)) ≡ Cubical.Data.Int.-_ (negsuc a) + Cubical.Data.Int.-_ (pos (suc b))
negDistrib-suc a b =
      cong Cubical.Data.Int.-_ (+Comm (negsuc a) (pos (suc b)))
      ∙ negDistrib-pos-negsuc (suc b) a
      ∙ +Comm (Cubical.Data.Int.-_ (pos (suc b))) (Cubical.Data.Int.-_ (negsuc a))
