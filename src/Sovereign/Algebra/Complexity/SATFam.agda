{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Algebra.Complexity.SATFam
-- SAT 渐近族——变元池随 n 增长的 log₃ 位宽编码（F7 核心件）
--
-- 状态：§5 立界 (i)–(v) 全闭合（2026-10-29）。头注即 journal。
--
-- 数学背景：SATMember 的变元池是「独热 suc m 宽」——m 固定时可行，
-- 渐近族需要变元号以 ⌈log₃⌉ 位宽的三进制编码（池随 n 增长）。
-- 本件落地：
--   §1 Trit→ℕ 解码器 + 定宽位（digit）往返（3 案 refl）
--   §2 三分函数 SF-third（结构性 4 案，⌊m/3⌋ 的干净可证形）
--   §3 燃料形位宽 SF-wlog3-fuel（fuel=节点预算；上界位宽）
--   §4 核对层（小值 refl 交叉）
--   §5.1 third 单调；§5.2 fuel 双单调；§5.3 wlog3 单调（(ii)）
--   §5.5 third 层四件（四案展开）+ pow3 基础件 + 位宽语义主定理（(iii)：
--        命题算术桥 SF-mul3-suc + SF-m≤3J + SF-fuel-ge + SF-wlog3-ge）
--   §5.8 变元号定宽编码 SF-d0/SF-digits3/SF-undigits3 + SF-div3
--        （除法恒等式，即 (i) 的 DivMod 刻画）+ SF-third-lt
--   §5.9 定宽往返 SF-undigits3-digits3（n < 3^w ⟹ 解码∘编码 = id）(iv)
--   §5.10 变元号编码于 Fin m（SF-enc-var / SF-dec-enc 恒等）(v)
--   §5.11 L-SAT 渐近族 SF-LSAT-fam（池 = w(n)）+ 池单调 + 池容量 (iv)
--
-- 已知边界（诚实）：
--   (i)  SF-third 与 ⌊_/3⌋ 的逐点恒等：已由 SF-div3
--        （n ≡ n mod 3 + 3·⌊n/3⌋）给出 Euclidean 刻画；余数 < 3 的
--        唯一性未单独证（divmod 唯一性属 DivMod 引理层，未取用）。
--   (ii) 精确 ⌈log₃⌉ 立界（w 的最小性）未证——本件只以上界口径使用
--        「3^w ≥ m」（SF-wlog3-ge），这对编码充分性够用。
--   (iii) 族的**一致性**（uniformity）未证：SF-LSAT-fam 把池换成 w(n)
--        并给出池单调/容量，但「m 随 n 变化时验证器/公式族的一致生成
--        与代价界搬运」不在本件——SATMember 的 sat-in-NP 只对固定 m。
--
-- 0 postulate / 0 hole。

module Sovereign.Algebra.Complexity.SATFam where

open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _≤_; _<_; s≤s; z≤n)
open import Data.Nat.Properties using (≤-refl; ≤-trans; ≤-reflexive;
  m≤n⇒m≤1+n; m≤m+n; *-suc; +-assoc; +-comm; <-≤-trans)
open import Data.List using (List; []; _∷_; length)
open import Data.Vec.Base using (Vec)
open import Data.Fin using (Fin; toℕ)
open import Data.Fin.Properties using (toℕ<n)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong;
  trans; subst; module ≡-Reasoning)

open import Sovereign.Base.Trit using (Trit; T₀; T₁; T₂)
open import Sovereign.Algebra.Complexity.TimeBound using (mono-*ˡ)
open import Sovereign.Algebra.Complexity.SATMember using (L-SAT; clauseW)

open ≡-Reasoning

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

-- §5.5′ 命题算术桥：3 * suc J ≡ suc³ (3 * J)（J 卡死形下的 ≡ 桥，
--   J 任意）——{*-suc 3 J} 把首参展开为 3 + 3 * J，{3 + X} 对 X 定义性
--   归约为 suc³ X（3 = suc³ zero，+ 首参递归）。
SF-mul3-suc : ∀ J → 3 * suc J ≡ suc (suc (suc (3 * J)))
SF-mul3-suc J = trans (*-suc 3 J) refl

-- m ≤ suc (3 * third (suc m))（⌈m/3⌉ 三倍覆盖 + 1 余量）——四案归纳
SF-m≤3J : ∀ m → m ≤ suc (3 * SF-third (suc m))
SF-m≤3J zero = z≤n
SF-m≤3J (suc zero) = ≤-refl
SF-m≤3J (suc (suc zero)) = s≤s (s≤s z≤n)
SF-m≤3J (suc (suc (suc m″))) =
  ≤-trans (s≤s (s≤s (s≤s (SF-m≤3J m″))))
          (≤-reflexive (sym (cong suc (SF-mul3-suc (SF-third (suc m″))))))
-- suc³ 案：s≤s³ (IH)：suc³ m″ ≤ suc³ (suc (3J)) = suc⁴ (3J)；
--   桥（sym (cong suc (SF-mul3-suc J))）：suc⁴ (3J) ≡ suc (3 * suc J) —— goal RHS。

-- ★ 主引理（suc 形留 +1 余量）：m ≤ k → suc m ≤ pow3 (fuel k m)
SF-fuel-ge : ∀ k m → m ≤ k → suc m ≤ SF-pow3 (SF-wlog3-fuel k m)
SF-fuel-ge zero zero m≤k = ≤-refl
SF-fuel-ge zero (suc m′) ()
SF-fuel-ge (suc k′) zero m≤k = ≤-refl
SF-fuel-ge (suc k′) (suc m′) (s≤s m′≤k′) =
  ≤-trans (≤-trans (s≤s (s≤s (SF-m≤3J m′)))
                   (≤-reflexive (sym (SF-mul3-suc (SF-third (suc m′))))))
          (mono-*ˡ 3 (SF-fuel-ge k′ (SF-third (suc m′))
                        (≤-trans (SF-third-suc-le m′) m′≤k′)))
-- fuel (suc k′) (suc m′) 定义性 = suc (fuel k′ J)，J = third (suc m′)
-- → goal RHS = 3 * pow3 (fuel k′ J)。
--   第一段：s≤s² (SF-m≤3J m′)：suc² m′ ≤ suc³ (3J)；桥：suc³ (3J) ≡ 3 * suc J。
--   第二段：mono-*ˡ 3（IH (k′, J)：suc J ≤ pow3 (fuel k′ J)）——J ≤ m′（third-suc-le）
--   且 m′ ≤ k′。

-- ★ 主定理：m ≤ 3^w(wlog3 m)——位宽语义收口（§5 (iii)）
SF-wlog3-ge : ∀ m → m ≤ SF-pow3 (SF-wlog3 m)
SF-wlog3-ge zero = z≤n
SF-wlog3-ge (suc m′) =
  ≤-trans (s≤s (m≤n⇒m≤1+n ≤-refl))
          (SF-fuel-ge (suc m′) (suc m′) ≤-refl)
-- wlog3 (suc m′) = fuel (suc m′) (suc m′)；m′ ≤ suc² m′（m≤n⇒m≤1+n × 2），
-- SF-fuel-ge (suc m′) (suc m′)：suc² m′ ≤ pow3 (fuel (suc m′) (suc m′))。
-- §5 (iii) 主定理闭合（SF-wlog3-ge）：m ≤ 3^w(wlog3 m)。
-- (iv)(v) 见 §5.8–§5.11（变元号定宽编码 / 往返 / 变元号恒等 / L-SAT 族）。


-- §5.6 核对层补充（pow3 小值 + 位宽语义小值）
-- ────────────────────────────────────────────────────────────────────

SF-check-pow3-2 : SF-pow3 (suc (suc zero)) ≡ suc (suc (suc (suc (suc (suc
  (suc (suc (suc zero))))))))
SF-check-pow3-2 = refl
SF-check-third-skip2-2 : SF-third (suc (suc (suc (suc zero)))) ≤ suc (SF-third (suc zero))
SF-check-third-skip2-2 = SF-third-skip2 (suc zero)
-- third 4 = 1 ≤ suc (third 2) = 1 ✓（skip2 小值交叉）

-- 位宽语义小值端到端：8 ≤ 3^w(8)（w(8)=2 → 9 ≥ 8）
SF-check-ge-8 : suc (suc (suc (suc (suc (suc (suc (suc zero)))))))
  ≤ SF-pow3 (SF-wlog3 (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))
SF-check-ge-8 = SF-wlog3-ge (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))

-- 桥引理小值：3 * suc 0 = 3 ≡ suc³ (3 * 0) = 3
SF-check-mul3-suc-0 : 3 * suc zero ≡ suc (suc (suc (3 * zero)))
SF-check-mul3-suc-0 = SF-mul3-suc zero

-- ────────────────────────────────────────────────────────────────────
-- §5.8 变元号定宽编码（(iv) 基元）〔结构定义 + 结构证明〕
-- ────────────────────────────────────────────────────────────────────

-- n mod 3 的数字位（4 案结构匹配，与 SF-third = ⌊n/3⌋ 互补）
SF-d0 : ℕ → Trit
SF-d0 zero = T₀
SF-d0 (suc zero) = T₁
SF-d0 (suc (suc zero)) = T₂
SF-d0 (suc (suc (suc n))) = SF-d0 n

-- w 位 base-3 展开（低位在前）：digits3 w n = d₀ d₁ … d_{w-1}
SF-digits3 : (w n : ℕ) → List Trit
SF-digits3 zero _ = []
SF-digits3 (suc w) n = SF-d0 n ∷ SF-digits3 w (SF-third n)

-- 位串 → ℕ：Σ dᵢ·3^i
SF-undigits3 : List Trit → ℕ
SF-undigits3 [] = zero
SF-undigits3 (t ∷ ts) = SF-dec t + 3 * SF-undigits3 ts

-- 编码长恒为 w
SF-digits3-len : ∀ w n → length (SF-digits3 w n) ≡ w
SF-digits3-len zero n = refl
SF-digits3-len (suc w) n = cong suc (SF-digits3-len w (SF-third n))

-- 除法恒等（SF-d0/SF-third 的定义性互逆）：n = (n mod 3) + 3⌊n/3⌋
SF-div3 : ∀ n → n ≡ SF-dec (SF-d0 n) + 3 * SF-third n
SF-div3 zero = refl
SF-div3 (suc zero) = refl
SF-div3 (suc (suc zero)) = refl
SF-div3 (suc (suc (suc n))) = begin
  suc (suc (suc n))
    ≡⟨ refl ⟩  -- 3 + n 定义性 = suc³ n
  3 + n
    ≡⟨ cong (3 +_) (SF-div3 n) ⟩
  3 + (SF-dec (SF-d0 n) + 3 * SF-third n)
    ≡⟨ sym (+-assoc 3 (SF-dec (SF-d0 n)) (3 * SF-third n)) ⟩
  (3 + SF-dec (SF-d0 n)) + 3 * SF-third n
    ≡⟨ cong (_+ 3 * SF-third n) (+-comm 3 (SF-dec (SF-d0 n))) ⟩
  (SF-dec (SF-d0 n) + 3) + 3 * SF-third n
    ≡⟨ +-assoc (SF-dec (SF-d0 n)) 3 (3 * SF-third n) ⟩
  SF-dec (SF-d0 n) + (3 + 3 * SF-third n)
    ≡⟨ cong (SF-dec (SF-d0 n) +_) (sym (*-suc 3 (SF-third n))) ⟩
  SF-dec (SF-d0 n) + 3 * SF-third (suc (suc (suc n))) ∎
-- 3+n 案：d0/third 定义性归约为 d0 n / suc (third n)；
-- 链：3+n = 3+(a+3t) →(assoc/comm) a+3+3t → a+3·suc t（*-suc 反向）。

-- 除法单调：n < 3k ⟹ ⌊n/3⌋ < k（往返的 w-归纳步）
-- 3 前缀消去：3 + a = suc³ a，四层 s≤s 的唯一构造子就是三层剥离后的证据。
SF-cancel3 : ∀ a b → 3 + a ≤ 3 + b → a ≤ b
SF-cancel3 a b (s≤s (s≤s (s≤s h))) = h

SF-third-lt : ∀ n k → suc n ≤ 3 * k → suc (SF-third n) ≤ k
SF-third-lt zero zero h = h
SF-third-lt zero (suc k) h = s≤s z≤n
SF-third-lt (suc zero) zero ()
SF-third-lt (suc zero) (suc k) h = s≤s z≤n
SF-third-lt (suc (suc zero)) zero ()
SF-third-lt (suc (suc zero)) (suc k) h = s≤s z≤n
SF-third-lt (suc (suc (suc n))) zero ()
SF-third-lt (suc (suc (suc n))) (suc k) h =
  s≤s (SF-third-lt n k
        (SF-cancel3 (suc n) (3 * k)
          (subst (λ X → 3 + suc n ≤ X) (*-suc 3 k) h)))
-- 3+j 案：h : suc⁴ n ≤ 3 * suc k，两处定义性归约给出 3 + suc n ≤ 3 + 3k
-- （suc⁴ n = 3 + suc n；3 * suc k = 3 + 3k），SF-cancel3 消前缀，IH 收口。

-- ────────────────────────────────────────────────────────────────────
-- §5.9 定宽往返（(iv) 的结构证明）
-- ────────────────────────────────────────────────────────────────────

-- 定宽往返：n 在 w 位值域内（n < 3^w）⟹ 编码再解码回到 n
SF-undigits3-digits3 : ∀ w n → n < SF-pow3 w → SF-undigits3 (SF-digits3 w n) ≡ n
SF-undigits3-digits3 zero zero h = refl
SF-undigits3-digits3 zero (suc m) (s≤s ())
SF-undigits3-digits3 (suc w) n h =
  trans (cong (λ X → SF-dec (SF-d0 n) + 3 * X)
              (SF-undigits3-digits3 w (SF-third n) (SF-third-lt n (SF-pow3 w) h)))
        (sym (SF-div3 n))
-- 归纳步靠 SF-div3 的"低两位 + 3·高位"分解：把 IH 代入尾部位串即得 n。

-- 核对层：4 = (1,1)₃，两位往返；位宽 3 的 7 = (1,2,1)₃
SF-check-digits3-4 : SF-digits3 (suc (suc zero)) (suc (suc (suc (suc zero))))
  ≡ T₁ ∷ T₁ ∷ []
SF-check-digits3-4 = refl

SF-check-undigits3-4 :
  SF-undigits3 (SF-digits3 (suc (suc zero)) (suc (suc (suc (suc zero)))))
    ≡ suc (suc (suc (suc zero)))
SF-check-undigits3-4 = refl

SF-check-len-3 : length (SF-digits3 (suc (suc (suc zero))) (suc (suc (suc (suc zero))))) ≡ 3
SF-check-len-3 = refl

SF-check-d0-4 : SF-d0 (suc (suc (suc (suc zero)))) ≡ T₁
SF-check-d0-4 = refl

-- ────────────────────────────────────────────────────────────────────
-- §5.10 变元号编码于 Fin m（(iv) 语义件：编码 / 解码恒等）
-- ────────────────────────────────────────────────────────────────────

-- 变元号 i : Fin m 的定宽 w(m) 位编码
SF-enc-var : ∀ m → Fin m → List Trit
SF-enc-var m i = SF-digits3 (SF-wlog3 m) (toℕ i)

-- 值域：变元号 < m ≤ 3^w(m)，落在可编码域内
SF-var-bound : ∀ m (i : Fin m) → toℕ i < SF-pow3 (SF-wlog3 m)
SF-var-bound m i = <-≤-trans (toℕ<n i) (SF-wlog3-ge m)

-- 解码 ∘ 编码 = 恒等（变元号往返）
SF-dec-enc : ∀ m (i : Fin m) → SF-undigits3 (SF-enc-var m i) ≡ toℕ i
SF-dec-enc m i = SF-undigits3-digits3 (SF-wlog3 m) (toℕ i) (SF-var-bound m i)

-- ────────────────────────────────────────────────────────────────────
-- §5.11 L-SAT 渐近族（(iv) 族装配：池 = w(n) 随 n 增长）
-- ────────────────────────────────────────────────────────────────────

-- 渐近族：n 长串在 w(n) 位池上的 SAT 语言（SATMember 的 L-SAT 实例化）
SF-LSAT-fam : ∀ n → Vec Trit n → Set
SF-LSAT-fam n x = L-SAT (SF-wlog3 n) n x

-- 池随 n 单调（族不是嵌套的，但池宽度不回落）
SF-fam-pool-mono : ∀ m n → m ≤ n → SF-wlog3 m ≤ SF-wlog3 n
SF-fam-pool-mono = SF-wlog3-mono

-- 池容量：n 长串的全部变元号（< n）都在 w(n) 位可编码域内
SF-fam-pool-cap : ∀ n → n ≤ SF-pow3 (SF-wlog3 n)
SF-fam-pool-cap = SF-wlog3-ge

-- 核对层：池宽度在 8→9 上不回落；n=8 的池覆盖 8 个变元号
SF-check-fam-pool : SF-wlog3 (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))
  ≤ SF-wlog3 (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))
SF-check-fam-pool = SF-fam-pool-mono
  (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))
  (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))
  (m≤n⇒m≤1+n ≤-refl)

SF-check-fam-cap-8 : suc (suc (suc (suc (suc (suc (suc (suc zero)))))))
  ≤ SF-pow3 (SF-wlog3 (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))
SF-check-fam-cap-8 = SF-fam-pool-cap (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))


-- 0 postulate / 0 hole。
