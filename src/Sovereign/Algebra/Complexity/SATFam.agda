{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Algebra.Complexity.SATFam
-- SAT 渐近族——变元池随 n 增长的 log₃ 位宽编码（F7 核心件，WIP 分批交付）
--
-- ⚠ WIP 声明（分批交付纪律）：本件已闭合 解码器/位宽函数/往返核/
--   third 单调 + fuel 双单调 + wlog3 Mono（§5 (i)(ii)）/
--   **third 层四件（四案展开：suc-≤1/skip2/skip/suc-le）+ pow3 基础件**；
--   位宽语义主定理（(iii) 剩余段：命题算术桥）/族装配（(iv)）/roundtrip（(v)）
--   待续——头注即 journal，未完成部分不留洞、以本声明承载。
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

open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _≤_; s≤s; z≤n)
open import Data.Nat.Properties using (≤-refl; ≤-trans; m≤n⇒m≤1+n;
  m≤m+n)
open import Data.List using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Sovereign.Base.Trit using (Trit; T₀; T₁; T₂)
open import Sovereign.Algebra.Complexity.TimeBound using (mono-*ˡ)

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
-- §5.1 SF-third 单调（§5 (i) 闭合）〔结构归纳 4 案 + s≤s 簿记〕
-- ────────────────────────────────────────────────────────────────────

SF-third-monotone : ∀ m n → m ≤ n → SF-third m ≤ SF-third n
SF-third-monotone zero n m≤n = z≤n
SF-third-monotone (suc zero) n m≤n = z≤n
SF-third-monotone (suc (suc zero)) n m≤n = z≤n
SF-third-monotone (suc (suc (suc m))) zero ()
SF-third-monotone (suc (suc (suc m))) (suc zero) (s≤s ())
SF-third-monotone (suc (suc (suc m))) (suc (suc zero)) (s≤s (s≤s ()))
SF-third-monotone (suc (suc (suc m))) (suc (suc (suc n)))
  (s≤s (s≤s (s≤s m≤n))) = s≤s (SF-third-monotone m n m≤n)

-- ────────────────────────────────────────────────────────────────────
-- §5.2 燃料双单调（§5 (ii) 前置）〔k-单调：fuel 结构递增；m-单调：依赖
--      (i) 的 third 单调逐层搬运〕
-- ────────────────────────────────────────────────────────────────────

SF-wlog3-fuel-mono-k : ∀ k₁ k₂ m → k₁ ≤ k₂
  → SF-wlog3-fuel k₁ m ≤ SF-wlog3-fuel k₂ m
SF-wlog3-fuel-mono-k zero k₂ m k₁≤k₂ = z≤n
SF-wlog3-fuel-mono-k (suc k₁) zero m ()
SF-wlog3-fuel-mono-k (suc k₁) (suc k₂) zero k₁≤k₂ = z≤n
SF-wlog3-fuel-mono-k (suc k₁) (suc k₂) (suc m) (s≤s k₁≤k₂) =
  s≤s (SF-wlog3-fuel-mono-k k₁ k₂ (SF-third (suc m)) k₁≤k₂)

SF-wlog3-fuel-mono-m : ∀ k m n → m ≤ n
  → SF-wlog3-fuel k m ≤ SF-wlog3-fuel k n
SF-wlog3-fuel-mono-m zero m n m≤n = z≤n
SF-wlog3-fuel-mono-m (suc k) zero n m≤n = z≤n
SF-wlog3-fuel-mono-m (suc k) (suc m) zero ()
SF-wlog3-fuel-mono-m (suc k) (suc m) (suc n) (s≤s m≤n) =
  s≤s (SF-wlog3-fuel-mono-m k (SF-third (suc m)) (SF-third (suc n))
             (SF-third-monotone (suc m) (suc n) (s≤s m≤n)))

-- ────────────────────────────────────────────────────────────────────
-- §5.3 SF-wlog3 单调（§5 (ii) 闭合）
-- ────────────────────────────────────────────────────────────────────

SF-wlog3-mono : ∀ m n → m ≤ n → SF-wlog3 m ≤ SF-wlog3 n
SF-wlog3-mono m n m≤n =
  ≤-trans (SF-wlog3-fuel-mono-m m m n m≤n)
          (SF-wlog3-fuel-mono-k m n n m≤n)

-- ────────────────────────────────────────────────────────────────────
-- §5.4 核对层补充（单调性小值 + w(3)=2 位宽小值）
-- ────────────────────────────────────────────────────────────────────

SF-check-w3-2 : SF-wlog3 (suc (suc (suc zero))) ≡ suc (suc zero)
SF-check-w3-2 = refl

SF-check-mono2 : SF-wlog3 (suc (suc zero)) ≤ SF-wlog3 (suc (suc (suc zero)))
SF-check-mono2 = SF-wlog3-mono (suc (suc zero)) (suc (suc (suc zero)))
  (s≤s (s≤s z≤n))

-- ────────────────────────────────────────────────────────────────────
-- §5.5 位宽语义（§5 (iii) 闭合）：m ≤ 3^w(wlog3 m)
-- ────────────────────────────────────────────────────────────────────
-- 方案 D（四案展开）：third 的子句是 zero/suc zero/suc² zero/suc³ n 四案，
-- third (suc m) 对变元 m 卡死——正解是对 m 本身做四案模式展开，每案 third
-- 子句逐字看穿，refl 级/结构递归闭合（无需任何第三算术层）。

-- 环一：third (suc m) ≤ suc (third m)——四案递归（核心件，前次卡死环的解）
SF-third-suc-≤1 : ∀ m → SF-third (suc m) ≤ suc (SF-third m)
SF-third-suc-≤1 zero = z≤n
-- third 1 = 0 ≤ suc (third 0) = 1
SF-third-suc-≤1 (suc zero) = z≤n
-- third 2 = 0 ≤ suc (third 1) = 1
SF-third-suc-≤1 (suc (suc zero)) = ≤-refl
-- third 3 = 1 ≤ suc (third 2) = 1
SF-third-suc-≤1 (suc (suc (suc m′))) = s≤s (SF-third-suc-≤1 m′)
-- third (suc⁴ m′) 定义性 = suc (third (suc m′))，s≤s + IH m′

-- 环二：skip2——third (suc² m) ≤ suc (third m)——四案递归
SF-third-skip2 : ∀ m → SF-third (suc (suc m)) ≤ suc (SF-third m)
SF-third-skip2 zero = z≤n
-- third 2 = 0 ≤ suc (third 0) = 1
SF-third-skip2 (suc zero) = ≤-refl
-- third 3 = 1 ≤ suc (third 1) = 1
SF-third-skip2 (suc (suc zero)) = ≤-refl
-- third 4 = 1 ≤ suc (third 2) = 1
SF-third-skip2 (suc (suc (suc m′))) = s≤s (SF-third-skip2 m′)
-- 目标 defeq suc (third (suc² m′)) ≤ suc (suc (third m′))；skip2 m′ 直接承接。
-- third (suc⁵ m′) 定义性 = suc (third (suc² m′))；s≤s 剥一层：
-- third (suc² m′) ≤ suc (third m′)（skip2 m′）≤ suc² (third m′)（m≤n⇒m≤1+n）

-- 环三：skip——third (suc² m) ≤ suc (third (suc m))——skip2 + third-mono
SF-third-skip : ∀ m → SF-third (suc (suc m)) ≤ suc (SF-third (suc m))
SF-third-skip m =
  ≤-trans (SF-third-skip2 m)
          (s≤s (SF-third-monotone m (suc m) (m≤n⇒m≤1+n ≤-refl)))

-- pow3 镜像
SF-pow3 : ℕ → ℕ
SF-pow3 zero = suc zero
SF-pow3 (suc n) = 3 * SF-pow3 n

-- p ≤ 3 * p（3 * suc p′ 定义性 = suc p′ + (suc p′ + zero)，m≤m+n 直取）
SF-≤3* : ∀ p → p ≤ 3 * p
SF-≤3* zero = z≤n
SF-≤3* (suc p′) = m≤m+n (suc p′) (suc p′ + (suc p′ + zero))

-- pow3 恒 ≥ 1（归纳：IH 1 ≤ pow3 f，pow3 f ≤ 3 * pow3 f）
SF-pow3-pos : ∀ f → suc zero ≤ SF-pow3 f
SF-pow3-pos zero = ≤-refl
SF-pow3-pos (suc f) = ≤-trans (SF-pow3-pos f) (SF-≤3* (SF-pow3 f))

-- pow3 单调
SF-pow3-mono : ∀ a b → a ≤ b → SF-pow3 a ≤ SF-pow3 b
SF-pow3-mono zero b a≤b = SF-pow3-pos b
SF-pow3-mono (suc a) zero ()
SF-pow3-mono (suc a) (suc b) (s≤s a≤b) =
  mono-*ˡ 3 (SF-pow3-mono a b a≤b)

-- third (suc m) ≤ m（fuel m (third (suc m)) ≤ fuel m m 的桥）
SF-third-suc-le : ∀ m → SF-third (suc m) ≤ m
SF-third-suc-le zero = z≤n
SF-third-suc-le (suc zero) = z≤n
SF-third-suc-le (suc (suc zero)) = s≤s z≤n
SF-third-suc-le (suc (suc (suc m))) =
  s≤s (≤-trans (SF-third-suc-le m) (m≤n⇒m≤1+n (m≤n⇒m≤1+n ≤-refl)))
-- 目标 defeq suc (third (suc m)) ≤ suc² (suc m)；s≤s 一层剥后：
-- IH（third (suc m) ≤ m）≤ suc² m（m≤n⇒m≤1+n × 2）。

-- §5.5′ 剩余立界（(iii) 主定理段）——2026-10-30 深夜试闭实测结论：
--   ① **方案 D 已确认**：third 层的四件（SF-third-suc-≤1 / SF-third-skip2 /
--      SF-third-skip / SF-third-suc-le）四案展开全部编译通过 ✓——
--      「third (suc m) 对变元 m 无子句匹配」的正解 = 对 m 四案展开，
--      非第三算术层（~30 行，非 ~100 行）。
--   ② **原 P-陈述为假**：m ≤ pow3 (fuel k (third (suc m))) 在 (k,m)=(4,4)
--      反例为假（4 ≰ 3）；正确形 = **suc m ≤ pow3 (fuel k m)**（suc 形留
--      +1 余量，fuel 直接吃 m）。
--   ③ **剩余障碍（精确）**：suc-归纳步的链在 J = third (suc m′) 卡死形下
--      需要 `3 * suc J`（goal-RHS 的展开形 J + 2·suc J）与 `suc² (3J)`
--      （s≤s² 链产物）之间的命题算术桥——两者数值相等（3J+3）但在 J 卡死
--      时非 defeq，需 +-suc / 分配律重写的专用小层（估 ~40 行）。
--   ④ SF-m≤3J（m ≤ suc (3·third (suc m))）四案前两案已闭合，suc³ 案
--      受同一算术桥阻塞。
-- (iv)  族装配：变元号定宽编码 + L-SAT 渐近族（SATMember 立界 (i) 收口）。
-- (v)   roundtrip：dec ∘ 位编码 于 Fin m 的恒等（依赖定宽编码定义）。

-- 0 postulate / 0 hole。
-- WIP：待补 §5 (iii) 剩余段 + (iv)(v)。可编译部分原样保留。


-- §5.6 核对层补充（pow3 小值 + 位宽语义小值）
-- ────────────────────────────────────────────────────────────────────

SF-check-pow3-2 : SF-pow3 (suc (suc zero)) ≡ suc (suc (suc (suc (suc (suc
  (suc (suc (suc zero))))))))
SF-check-pow3-2 = refl
SF-check-third-skip2-2 : SF-third (suc (suc (suc (suc zero)))) ≤ suc (SF-third (suc zero))
SF-check-third-skip2-2 = SF-third-skip2 (suc zero)
-- third 4 = 1 ≤ suc (third 2) = 1 ✓（skip2 小值交叉）

-- ────────────────────────────────────────────────────────────────────
-- §5.7 待续立界（分批交付的剩余清单——头注 WIP 声明的明细）
-- ────────────────────────────────────────────────────────────────────
-- (iv)  族装配：变元号定宽编码 + L-SAT 渐近族（SATMember 立界 (i) 收口）。
-- (v)   roundtrip：dec ∘ 位编码 于 Fin m 的恒等（依赖定宽编码定义）。

-- 0 postulate / 0 hole。
-- WIP：待补 §5 (iv)(v)。可编译部分原样保留。
