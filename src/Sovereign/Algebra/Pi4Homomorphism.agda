{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Algebra.Pi4Homomorphism
-- π₄ : Duodec → Fin 4 保持加法 (缺口 G2 闭合)
--
-- 数学背景: CRT 投影 π₄ 是 mod 4 投影。本模块证明它是**加法群同态**:
--     π₄ (x +12 y) ≡ (π₄ x) +4 (π₄ y)
-- 此前库里只有 π₃ 的同态性 (π3-homo-+ / π3-homo-*), π₄ 一直列为缺口
-- (docs/duodecimal/07-proof-status.md §6.1 G2; 05-crt-decomposition.md §八 未解决问题 1)。
--
-- 证明图 (DAG, 4 节点):
--   L1: π₄ (+1 x) ≡ fin4-suc (π₄ x)                        (12 case refl)
--   L3: iterate fin4-suc 4 i ≡ i                            (4 case refl, C₄ 周期)
--   L2: π₄ (iterate +1 n y) ≡ iterate fin4-suc n (π₄ y)     (对 n 归纳, 用 L1)
--   L4: 目标 —— 12 case on x, 每 case 用 L2 把 +1^k 折成迭代,
--       再用 L3 (及由 L3 导出的 8 步约化) 把 k 约到 k mod 4
--
-- 核心原则:
--   1. Duodec 是 12 个零元构造子 (非递归), 故目标按 x 穷举 12 case
--   2. _+12_ 的定义使 d_k +12 y ≡ +1^k y (定义性), 与 iterate +1 k 对齐
--   3. Fin 4 侧不引入 fromℕ< 算术: 周期 4 由 fin4-suc 迭代给出
-- 0 postulate, 0 hole.

module Sovereign.Algebra.Pi4Homomorphism where

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Fin.Base using (Fin; toℕ) renaming (zero to fzero; suc to fsuc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans)
open import Sovereign.Algebra.Duodecimal using
  (Duodec; d0; d1; d2; d3; d4; d5; d6; d7; d8; d9; d10; d11; +1; _+12_; π4)
open import Sovereign.Algebra.GroupTheory.DayanCore using (iterate)

--------------------------------------------------------------------------------
-- §0. Fin 4 侧的循环后继与加法 (投影目标的结构)
--     fin4-suc 是 C₄ 的生成平移; _+4_ 用 toℕ 迭代它 (即 mod 4 加法)
--------------------------------------------------------------------------------

fin4-suc : Fin 4 → Fin 4
fin4-suc fzero = fsuc fzero
fin4-suc (fsuc fzero) = fsuc (fsuc fzero)
fin4-suc (fsuc (fsuc fzero)) = fsuc (fsuc (fsuc fzero))
fin4-suc (fsuc (fsuc (fsuc fzero))) = fzero

_+4_ : Fin 4 → Fin 4 → Fin 4
i +4 j = iterate fin4-suc (toℕ i) j

--------------------------------------------------------------------------------
-- §1 (L1). π₄ 与循环后继交换 —— 12 case 定义性相等
--------------------------------------------------------------------------------

pi4-+1 : ∀ x → π4 (+1 x) ≡ fin4-suc (π4 x)
pi4-+1 d0 = refl
pi4-+1 d1 = refl
pi4-+1 d2 = refl
pi4-+1 d3 = refl
pi4-+1 d4 = refl
pi4-+1 d5 = refl
pi4-+1 d6 = refl
pi4-+1 d7 = refl
pi4-+1 d8 = refl
pi4-+1 d9 = refl
pi4-+1 d10 = refl
pi4-+1 d11 = refl

--------------------------------------------------------------------------------
-- §2 (L3). C₄ 周期: 迭代 4 步 = 恒等 —— 4 case 定义性相等
--------------------------------------------------------------------------------

fin4-suc-4 : ∀ i → iterate fin4-suc 4 i ≡ i
fin4-suc-4 fzero = refl
fin4-suc-4 (fsuc fzero) = refl
fin4-suc-4 (fsuc (fsuc fzero)) = refl
fin4-suc-4 (fsuc (fsuc (fsuc fzero))) = refl

-- 迭代加法律 (局部; 用于把 8 步拆成 4+4)
iter-+ : ∀ {A : Set} (f : A → A) m n c → iterate f (m + n) c ≡ iterate f m (iterate f n c)
iter-+ f zero n c = refl
iter-+ f (suc m) n c = cong f (iter-+ f m n c)

-- 8 步 = 两个 4 步
fin4-suc-8 : ∀ i → iterate fin4-suc 8 i ≡ i
fin4-suc-8 i =
  trans (iter-+ fin4-suc 4 4 i)
        (trans (cong (iterate fin4-suc 4) (fin4-suc-4 i))
               (fin4-suc-4 i))

--------------------------------------------------------------------------------
-- §3 (L2). 迭代下的同态: 对 n 归纳, 用 L1 与迭代定义
--------------------------------------------------------------------------------

pi4-iter : ∀ n y → π4 (iterate +1 n y) ≡ iterate fin4-suc n (π4 y)
pi4-iter zero y = refl
pi4-iter (suc n) y =
  trans (pi4-+1 (iterate +1 n y)) (cong fin4-suc (pi4-iter n y))

--------------------------------------------------------------------------------
-- §4 (L4). 主定理: π₄ 是加法群同态
--     按 x 穷举 12 case; d_k +12 y ≡ +1^k y 定义性成立, 故用 pi4-iter k,
--     再把 iterate fin4-suc k 约到 iterate fin4-suc (k mod 4) (即 toℕ (π₄ d_k))
--------------------------------------------------------------------------------

pi4-homo-+ : ∀ x y → π4 (x +12 y) ≡ (π4 x) +4 (π4 y)
pi4-homo-+ d0 y = refl
pi4-homo-+ d1 y = pi4-iter 1 y
pi4-homo-+ d2 y = pi4-iter 2 y
pi4-homo-+ d3 y = pi4-iter 3 y
pi4-homo-+ d4 y = trans (pi4-iter 4 y) (fin4-suc-4 (π4 y))
pi4-homo-+ d5 y = trans (pi4-iter 5 y) (cong fin4-suc (fin4-suc-4 (π4 y)))
pi4-homo-+ d6 y =
  trans (pi4-iter 6 y) (cong (λ z → fin4-suc (fin4-suc z)) (fin4-suc-4 (π4 y)))
pi4-homo-+ d7 y =
  trans (pi4-iter 7 y)
        (cong (λ z → fin4-suc (fin4-suc (fin4-suc z))) (fin4-suc-4 (π4 y)))
pi4-homo-+ d8 y = trans (pi4-iter 8 y) (fin4-suc-8 (π4 y))
pi4-homo-+ d9 y = trans (pi4-iter 9 y) (cong fin4-suc (fin4-suc-8 (π4 y)))
pi4-homo-+ d10 y =
  trans (pi4-iter 10 y) (cong (λ z → fin4-suc (fin4-suc z)) (fin4-suc-8 (π4 y)))
pi4-homo-+ d11 y =
  trans (pi4-iter 11 y)
        (cong (λ z → fin4-suc (fin4-suc (fin4-suc z))) (fin4-suc-8 (π4 y)))

--------------------------------------------------------------------------------
-- §5. 对抗验证: 具体点独立 refl 交叉比对 (生成元 / 环绕点 / 混合点)
--------------------------------------------------------------------------------

check-gen : π4 (d1 +12 d3) ≡ (π4 d1) +4 (π4 d3)
check-gen = refl

check-wrap : π4 (d9 +12 d7) ≡ (π4 d9) +4 (π4 d7)
check-wrap = refl

check-mixed : π4 (d7 +12 d10) ≡ (π4 d7) +4 (π4 d10)
check-mixed = refl
