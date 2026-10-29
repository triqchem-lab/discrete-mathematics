{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Algebra.Complexity.SATFam
-- SAT 渐近族——变元池随 n 增长的 log₃ 位宽编码（F7 核心件，WIP 分批交付）
--
-- ⚠ WIP 声明（分批交付纪律）：本件已闭合 解码器/位宽函数/往返核，
--   **Mono/Pos 与族装配（SATMember 立界 (i) 的完整闭合）待续**——
--   头注即 journal，未完成部分不留洞、以本声明承载。
--
-- 数学背景：SATMember 的变元池是「独热 suc m 宽」——m 固定时可行，
-- 渐近族需要变元号以 ⌈log₃⌉ 位宽的三进制编码（池随 n 增长）。
-- 本件落地三块基元：
--   §1 Trit→ℕ 解码器 + 定宽位（digit）往返（3 案 refl）
--   §2 三分函数 SF-third（结构性 4 案，≈ ⌊m/3⌋ 的干净可证形）
--   §3 燃料形位宽 SF-wlog3-fuel（fuel=节点预算；上界位宽，Mono 待续）
--   §4 核对层（小值 refl 交叉）
--
-- 已知边界（诚实）：
--   (i)  SF-third 是 ⌊m/3⌋ 的**可证形**（结构性 4 案），与 ⌊m/3⌋ 的
--        逐点恒等未证（属 DivMod 引理层，待续）；
--   (ii) SF-wlog3-fuel 的 Mono（m ≤ n → w fuel m ≤ w fuel n）待续——
--        依赖 SF-third 的单调（third m ≤ third n，同上 DivMod 层）；
--   (iii) 位宽语义「3^w ≥ m」以上界口径使用，精确 ⌈log₃⌉ 立界同 (ii)。
--
-- 0 postulate / 0 hole。

module Sovereign.Algebra.Complexity.SATFam where

open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Sovereign.Base.Trit using (Trit; T₀; T₁; T₂)

-- ────────────────────────────────────────────────────────────────────
-- §1 Trit→ℕ 解码器与定宽位〔结构定义 + refl 往返〕
-- ────────────────────────────────────────────────────────────────────

SF-dec : Trit → ℕ
SF-dec T₀ = zero
SF-dec T₁ = suc zero
SF-dec T₂ = suc (suc zero)

SF-digit : ℕ → Trit
SF-digit zero = T₀
SF-digit (suc zero) = T₁
SF-digit _ = T₂

-- 往返：位读出后 digit 化恒等（Trit 三案 refl）〔refl 枚举〕
SF-digit-dec : ∀ t → SF-digit (SF-dec t) ≡ t
SF-digit-dec T₀ = refl
SF-digit-dec T₁ = refl
SF-digit-dec T₂ = refl

-- ────────────────────────────────────────────────────────────────────
-- §2 三分函数〔结构定义〕——⌊m/3⌋ 的可证形（4 案结构匹配）
-- ────────────────────────────────────────────────────────────────────

SF-third : ℕ → ℕ
SF-third zero = zero
SF-third (suc zero) = zero
SF-third (suc (suc zero)) = zero
SF-third (suc (suc (suc n))) = suc (SF-third n)

-- ────────────────────────────────────────────────────────────────────
-- §3 燃料形位宽〔结构定义〕——fuel = 节点预算，递归消耗燃料
-- ────────────────────────────────────────────────────────────────────

SF-wlog3-fuel : ℕ → ℕ → ℕ
SF-wlog3-fuel zero m = zero
SF-wlog3-fuel (suc k) zero = zero
SF-wlog3-fuel (suc k) (suc m) =
  suc (SF-wlog3-fuel k (SF-third (suc m)))

SF-wlog3 : ℕ → ℕ
SF-wlog3 m = SF-wlog3-fuel m m

-- ────────────────────────────────────────────────────────────────────
-- §4 核对层〔refl 枚举〕
-- ────────────────────────────────────────────────────────────────────

-- 位宽小值（fuel 上界口径，保守非精确）：w(1)=1、w(2)=1（3¹=3≥2 上界 ✓）
SF-check-w1 : SF-wlog3 (suc zero) ≡ suc zero
SF-check-w1 = refl

SF-check-w3 : SF-wlog3 (suc (suc zero)) ≡ suc zero
SF-check-w3 = refl

-- third 小值：third 3 = 1、third 4 = 1
SF-check-third3 : SF-third (suc (suc zero)) ≡ zero
SF-check-third3 = refl

SF-check-third4 : SF-third (suc (suc (suc zero))) ≡ suc zero
SF-check-third4 = refl

-- ────────────────────────────────────────────────────────────────────
-- §5 待续立界（WIP 分批交付的剩余清单——头注 WIP 声明的明细）
-- ────────────────────────────────────────────────────────────────────
-- (i)  SF-third 单调：m ≤ n → SF-third m ≤ SF-third n（4 案 + n≤m+n 簿记）
-- (ii) SF-wlog3-fuel 的 Mono（依赖 (i) 的逐 fuel 归纳）
-- (iii) 位宽语义 3^w ≥ m 的精确形式与 ⌈log₃⌉ 立界收口
-- (iv) 族装配：变元号定宽编码 + L-SAT 渐近族（SATMember 立界 (i) 收口）
-- (v)  roundtrip：dec ∘ 位编码 于 Fin m 的恒等（依赖 (i)）

-- 0 postulate / 0 hole。
-- WIP：待补 §5 (i)-(v)。可编译部分原样保留。
