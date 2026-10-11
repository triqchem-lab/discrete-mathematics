{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Analysis.IntegrationByParts
-- 分部积分统一结构 (L3 深层证明)
--
-- 核心命题:
--   将离散分部积分、Green 恒等式、散度定理统一为一个自洽的框架。
--
-- 证明策略:
--   §1 分部积分 (1D 离散三点循环形——上游 DiscreteDiffOps 已证, 本件具名引接)
--   §2 分部积分推论 (差分求和为零——同上引接)
--   §3 Green 恒等式 (离散版) —— **立界 roadmap**（多维点格和机件, 见节尾精确剩余）
--   §4 散度定理 (离散版) —— **立界 roadmap**（同上）
--   §5 Abel 求和边界形 (ℤ 版——非周期全形, 边界项显式; 本件主证区)
--   §6 核对层 (具体 φ ψ refl 级双通道)
--
-- 全部 0 postulate, GF(3) 穷举 refl + 符号推理。

-- | 离散分部积分实例核
--
-- 核心原则：离散分部积分实例核——离散基座实例核（非一般定理，诚实边界随引用）
--          穷举/归纳边界遵守（≤27 case 或具名链，trans ≤3）
--          代数污染禁令（禁 Float/Double/超越函数）
--
-- 包含：integration-by-parts-theorem、diff-sum-zero

module Sovereign.Analysis.IntegrationByParts where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Fin using (Fin) renaming (zero to fz; suc to fs)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; cong₂; sym; trans; module ≡-Reasoning)

-- ℤ 环件（§5 Abel 边界形用——符号/具体值拆分正解：ℤ 代数符号证 + 小例 refl）
open import Data.Integer using (ℤ; _+_; _*_; _-_; +_; -_)
open import Data.Integer.Properties using
  (+-assoc; +-comm; +-identityʳ; +-inverseʳ; *-distribˡ-+; *-distribʳ-+;
   neg-distribˡ-*; neg-distribʳ-*)

open import Sovereign.Base.Trit using (Trit; T₀; T₁; T₂; _⊕_; _⊗_; negate)

open ≡-Reasoning

--------------------------------------------------------------------------------
-- §1. 分部积分 (1D 离散版)
--------------------------------------------------------------------------------

-- 离散分部积分: Σ φ·Δψ = -Σ ∇φ·∇ψ
-- 已有: integration-by-parts-1d : ∀ φ ψ → sum-forward φ ψ ≡ sum-backward φ ψ

-- [波 2-C 检查件外移] integration-by-parts-theorem 委托对已迁 Sovereign.Physics.DiscreteDiffOpsChecks

-- 推论: 差分求和为零
-- 已有: integration-by-parts-zero : ∀ φ ψ → diff-sum φ ψ ≡ fz

-- [波 2-C 检查件外移] diff-sum-zero 委托对已迁 Sovereign.Physics.DiscreteDiffOpsChecks

--------------------------------------------------------------------------------
-- §2. 分部积分推论
--------------------------------------------------------------------------------

-- 推论 1: 乘法交换律 (用于分部积分)
-- 已有: mul3-comm : ∀ a b → a ⊗ b ≡ b ⊗ a

-- 推论 2: 加法循环 (用于分部积分)
-- 已有: add3-cyclic : ∀ a b c → add3 (add3 a b) c ≡ add3 (add3 c a) b

-- 推论 3: 加逆归零 (用于分部积分)
-- 已有: add-neg-zero : ∀ x → add3 x (neg3 x) ≡ fz

--------------------------------------------------------------------------------
-- §3. Green 恒等式 (离散版)
--------------------------------------------------------------------------------

-- Green 第一恒等式: ∫(∇u·∇v) = -∫(u·Δv) + 边界项
-- 离散版: Σ ∇φ·∇ψ = -Σ φ·Δψ + 边界项

-- Green 第二恒等式: ∫(uΔv - vΔu) = 边界项
-- 离散版: Σ(φ·Δψ - ψ·Δφ) = 边界项

-- 在离散格点上, Green 恒等式由分部积分推导

--------------------------------------------------------------------------------
-- §4. 散度定理 (离散版)
--------------------------------------------------------------------------------

-- 散度定理: ∫∫∫ div E dV = ∫∫ E·n dS
-- 离散版: Σ div E = 边界项

-- 在离散格点上, 散度定理由分部积分推导


--------------------------------------------------------------------------------
-- §5. Abel 求和边界形 (ℤ 版——分部积分的非周期全形)
--------------------------------------------------------------------------------
--
-- 数学内容（边界项显式在场的离散分部积分）:
--   φ(0)·ψ(0) + Σ_{i<n} [ φ(i)·Δψ(i) + Δφ(i)·ψ(i+1) ] = φ(n)·ψ(n)
--   等价移项形即 Σ φ·Δψ = [φ·ψ]₀ⁿ 边界 − Σ Δφ·ψ⁺（Abel 求和/分部求和）。
-- 与 §1 关系: §1 三点循环形 = 周期边界对消后的推论（闭链无边界项）。
-- 策略: 符号段 ℤ 代数链（环恒等式）+ 具名拆分（每链 ≤3）；核对层见 §6。

-- 前 n 项和（ℕ 递归——自含零依赖）
sumTo : (ℕ → ℤ) → ℕ → ℤ
sumTo f zero = + 0
sumTo f (suc n) = sumTo f n + f n

-- 前向差分
fwdDiff : (ℕ → ℤ) → ℕ → ℤ
fwdDiff f n = f (suc n) - f n

-- ── 基础件层（加法群消去三件——具名拆分） ──

-- 左消去: X + (P + -X) = P + (X + -X)（换序+结合，3 步）
swap-cancel : ∀ (X P : ℤ) → X + (P + - X) ≡ P + (X + - X)
swap-cancel X P =
  trans (sym (+-assoc X P (- X)))
  (trans (cong (λ w → w + - X) (+-comm X P))
        (+-assoc P X (- X)))

-- 逆元消去: P + (X + -X) = P（2 步）
inv-cancel : ∀ (X P : ℤ) → P + (X + - X) ≡ P
inv-cancel X P = trans (cong (λ w → P + w) (+-inverseʳ X)) (+-identityʳ P)

-- 右腿前件（恒等桥，备用）: (P + 0) + (Q + -P) = P + (Q + -P)
right-leg-a : ∀ (P Q : ℤ) → (P + + 0) + (Q + - P) ≡ P + (Q + - P)
right-leg-a P Q = cong (λ w → w + (Q + - P)) (+-identityʳ P)

right-leg-b : ∀ (P Q : ℤ) → P + (Q + - P) ≡ Q + (P + - P)
right-leg-b P Q =
  trans (sym (+-assoc P Q (- P)))
  (trans (cong (λ w → w + - P) (+-comm P Q))
        (+-assoc Q P (- P)))

right-leg-c : ∀ (P Q : ℤ) → Q + (P + - P) ≡ Q
right-leg-c P Q = trans (cong (λ w → Q + w) (+-inverseʳ P)) (+-identityʳ Q)

-- ── 主引理层 ──

-- 望远镜核: X + ((P + -X) + (Q + -P)) = Q（纯加法群重排）
kernel-a : ∀ (X P Q : ℤ) → X + ((P + - X) + (Q + - P)) ≡ P + (Q + - P)
kernel-a X P Q =
  trans (sym (+-assoc X (P + - X) (Q + - P)))
        (cong (λ w → w + (Q + - P)) (trans (swap-cancel X P) (inv-cancel X P)))
  -- X+((P+−X)+(Q+−P)) → (X+(P+−X))+(Q+−P) → P+(Q+−P)  [assoc 对齐 + 换序/逆消]

telescope-kernel : ∀ (X P Q : ℤ) → X + ((P + - X) + (Q + - P)) ≡ Q
telescope-kernel X P Q =
  trans (kernel-a X P Q) (trans (right-leg-b P Q) (right-leg-c P Q))
  -- P+(Q+−P) → (Q+P)+−P → Q+(P+−P) → Q  [右腿换序 + 逆消]

-- 项展开: a·(c−b) + (d−a)·c = (a·c + −(a·b)) + (d·c + −(a·c))（分配+负分配，2 步）
term-expand : ∀ (a b c d : ℤ) →
  a * (c - b) + (d - a) * c ≡ (a * c + - (a * b)) + (d * c + - (a * c))
term-expand a b c d =
  trans (cong₂ (λ u v → u + v)
          (*-distribˡ-+ a c (- b))
          (*-distribʳ-+ c d (- a)))
        (cong₂ (λ u v → u + v)
          (cong (λ w → a * c + w) (sym (neg-distribʳ-* a b)))
          (cong (λ w → d * c + w) (sym (neg-distribˡ-* a c))))
  -- 步1 分配展开: a·(c−b) → a·c + a·(−b)；(d−a)·c → d·c + (−a)·c  [*-distribˡ/ʳ-+]
  -- 步2 负分配对齐: a·(−b) → −(a·b)；(−a)·c → −(a·c)  [neg-distribʳ/ˡ-*]

-- ── 组合层（主定理——望远镜归纳） ──

-- Abel 分部求和（边界形）: φ(0)ψ(0) + Σ_{i<n} [φ(i)Δψ(i) + Δφ(i)ψ(i+1)] = φ(n)ψ(n)
abel-ibp-telescope : ∀ (φ ψ : ℕ → ℤ) (n : ℕ) →
  φ 0 * ψ 0 + sumTo (λ i → φ i * fwdDiff ψ i + fwdDiff φ i * ψ (suc i)) n
    ≡ φ n * ψ n
abel-ibp-telescope φ ψ zero = +-identityʳ (φ 0 * ψ 0)
abel-ibp-telescope φ ψ (suc n) =
  let
    X : ℤ ; X = φ n * ψ n
    P : ℤ ; P = φ n * ψ (suc n)
    Q : ℤ ; Q = φ (suc n) * ψ (suc n)
    -- 项展开实例: s(n) = φn·Δψn + Δφn·ψ⁺ = (P + -X) + (Q + -P)
    s-expand : φ n * fwdDiff ψ n + fwdDiff φ n * ψ (suc n)
               ≡ (P + - X) + (Q + - P)
    s-expand = term-expand (φ n) (ψ n) (ψ (suc n)) (φ (suc n))
  in
  trans (sym (+-assoc (φ 0 * ψ 0) _ _))
  (trans (cong (λ w → w + (φ n * fwdDiff ψ n + fwdDiff φ n * ψ (suc n)))
              (abel-ibp-telescope φ ψ n))
  (trans (cong (λ w → X + w) s-expand) (telescope-kernel X P Q)))
  -- LHS(0..n+1) → (LHS(0..n) + s(n)) → X + s(n) → X + ((P+−X)+(Q+−P)) → Q  [assoc/IH/展开/核]

--------------------------------------------------------------------------------
-- §6. 核对层（具体 φ ψ——refl 级双通道）
--------------------------------------------------------------------------------

-- 具体实例: φ ≡ 3 (常), ψ(i) = i+1 → n=2 通道一（直接计算）
private
  φc : ℕ → ℤ
  φc _ = + 3
  ψc : ℕ → ℤ
  ψc i = + 1 + + i

check-abel-2 : φc 0 * ψc 0
  + ((φc 0 * (ψc 1 - ψc 0) + (φc 1 - φc 0) * ψc 1)
   + (φc 1 * (ψc 2 - ψc 1) + (φc 2 - φc 1) * ψc 2))
  ≡ φc 2 * ψc 2
check-abel-2 = refl

-- 通道二（真定理调用）
check-abel-via : φc 0 * ψc 0
  + ((φc 0 * (ψc 1 - ψc 0) + (φc 1 - φc 0) * ψc 1)
   + (φc 1 * (ψc 2 - ψc 1) + (φc 2 - φc 1) * ψc 2))
  ≡ φc 2 * ψc 2
check-abel-via = abel-ibp-telescope φc ψc 2

-- §3/§4 精确剩余（立界，不硬造）:
--   Green 第一恒等式离散形 = 二维点格上的 Σ ∇φ·∇ψ 与 Σ φ·Δψ 对照 + 边界环
--     → 需 Point3D 点格求和机件（Σ_p : (Point3D → GF3) → GF3 形）+ 边界面枚举;
--   散度定理离散形 = Σ_p div E = 边界通量 → 同上机件 + 法向分量枚举;
--   一旦点格和机件落位, 两者均为 §5 Abel 形的逐维迭代（每维边界项即面通量）。
--   当前 §5 的 1D 边界形即其引擎——多维推广为纯机件工程, 估 1-2 批。

-- 分部积分总结:
-- 1. Σ φ·Δψ = -Σ ∇φ·∇ψ (1D 分部积分)
-- 2. diff-sum = 0 (差分求和为零)
-- 3. mul3-comm (乘法交换律)
-- 4. add3-cyclic (加法循环)
-- 5. add-neg-zero (加逆归零)

-- 0 postulate.
