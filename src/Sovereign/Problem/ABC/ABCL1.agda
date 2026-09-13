{-# OPTIONS --rewriting --guardedness #-}

module Sovereign.Problem.ABC.ABCL1 where

-- | 两维度壁垒：**乘法轴穿不过平展投影**（IUTT「不可压成一维」的离散对应）
--
-- ── 这一层在问题里的位置 ─────────────────────────────────────────────
-- 望月把环的加法结构与乘法结构称为「**两个底层算术维度**」，并明确写出：若把这两个维度
-- 「压成一个维度」（假设二者之间存在**固定**关系），**立即得到矛盾**（[EssLog], §3.1, (1-Dim)/(2-Dim)，
-- 见 `docs/duodecimal/23-two-arithmetic-dimensions.md` 的原文与页码）。
--
-- 本模块把这句话**在离散基座上定理化**成一个可证命题：
--
--   加法维度：平展投影 `crt12` 是**双射**（Z/12 ≅ Z/3 × Z/4）——**穿得过**。
--   乘法维度：`⟨α⟩`（4 阶循环 C₄）到平展载体 R₁₂ 的单位群（Klein 四元群 V₄）**不存在**
--             保单位单射同态——**穿不过**。原因是一行算术：V₄ 的指数是 2（每个单位平方回单位元），
--             而 C₄ 有 4 阶元。
--
-- 于是「一边穿得过、另一边穿不过」正是「两个维度不能压成一个」的离散版本。
--
-- ⚠️ **本模块不是 abc 猜想的证据，也不是对 IUTT 对错的判断。** 它只是把一种**结构对应**
-- 落到可证命题上；对应关系本身是研究线索（见上述文档），不是证明链。引用本模块时**不得**
-- 写成「abc 因此在离散基座上可证/不可证」。
--
-- ── 依赖（全部复用库中已证事实，不重新证明数学）──────────────────────
--   · `DuodecClock.mulAlpha` 乘法表（a1·a1 = a2, a2·a2 = a0 ⇒ ord(a1) = 4）
--   · `Duodecimal._*u_` 单位群乘法表 与 `u5²`/`u7²`/`u11²`（V₄ 指数 2）
--   · `Duodecimal.crt12-roundtrip`（加法侧的双射）

open import Data.Product using (Σ; _×_; _,_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong; module ≡-Reasoning)

open import Sovereign.Algebra.GroupTheory.DuodecClock
  using (AlphaPower; a0; a1; a2; a3; mulAlpha)
open import Sovereign.Algebra.Duodecimal
  using (Duodec; DuodecUnit; u1; u5; u7; u11; _*u_; u5²; u7²; u11²
        ; crt12; π3; π4; crt12-roundtrip)

open ≡-Reasoning

--------------------------------------------------------------------------------
-- §1. 平展侧：V₄ 的指数是 2
--------------------------------------------------------------------------------

-- 每个单位自乘都回单位元 —— 这正是「平展载体记不住 4 阶」的原因
unit-square : ∀ u → u *u u ≡ u1
unit-square u1  = refl
unit-square u5  = u5²
unit-square u7  = u7²
unit-square u11 = u11²

--------------------------------------------------------------------------------
-- §2. 乘法侧：⟨α⟩ 有 4 阶元
--------------------------------------------------------------------------------

-- a1 · a1 = a2（定义即得）
mulAlpha-a1a1 : mulAlpha a1 a1 ≡ a2
mulAlpha-a1a1 = refl

-- 4 阶的见证：a1 迭代两步回到 a2 ≠ a0，四步才回 a0
a2≢a0 : a2 ≢ a0
a2≢a0 ()

mulAlpha-4th : mulAlpha a2 a2 ≡ a0
mulAlpha-4th = refl

--------------------------------------------------------------------------------
-- §3. 壁垒定理
--------------------------------------------------------------------------------

-- 保单位的同态 f : ⟨α⟩(×) → V₄(*u)
IsUnitHom : (AlphaPower → DuodecUnit) → Set
IsUnitHom f = (f a0 ≡ u1) × (∀ x y → f (mulAlpha x y) ≡ f x *u f y)

Inj : (AlphaPower → DuodecUnit) → Set
Inj f = ∀ x y → f x ≡ f y → x ≡ y

-- **核心**：任何这样的同态都必然把 a2 与 a0 压到一起 —— 乘法轴的高阶结构在平展侧丢失
hom-collapses : (f : AlphaPower → DuodecUnit) → IsUnitHom f → f a2 ≡ f a0
hom-collapses f (f0 , hom) = begin
  f a2
    ≡⟨ cong f (sym mulAlpha-a1a1) ⟩
  f (mulAlpha a1 a1)
    ≡⟨ hom a1 a1 ⟩
  f a1 *u f a1
    ≡⟨ unit-square (f a1) ⟩
  u1
    ≡⟨ sym f0 ⟩
  f a0 ∎

-- **壁垒**：不存在「保单位 ∧ 保乘法 ∧ 单射」的 f
no-injective-hom : ¬ Σ (AlphaPower → DuodecUnit) (λ f → IsUnitHom f × Inj f)
no-injective-hom (f , isHom , inj) = a2≢a0 (inj a2 a0 (hom-collapses f isHom))

--------------------------------------------------------------------------------
-- §4. 对照：加法维度**穿得过**（库中已证，此处只引用）
--------------------------------------------------------------------------------

-- 加法侧：`crt12`/`π3`/`π4` 给出 Z/12 ≅ Z/3 × Z/4 的双射 —— 加法维度可无损穿过平展投影
additive-dim-passes : ∀ (n : Duodec) → crt12 (π3 n) (π4 n) ≡ n
additive-dim-passes = crt12-roundtrip

-- 合起来：
--   加法维度  ：∃ 无损投影（crt12，双射）                    → 穿得过
--   乘法维度  ：¬ ∃ 保单位单射同态 ⟨α⟩ → V₄                → 穿不过
-- 这就是「两个底层算术维度不能压成一个」的离散定理化版本。
