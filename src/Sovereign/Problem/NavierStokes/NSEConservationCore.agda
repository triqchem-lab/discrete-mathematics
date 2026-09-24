{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Problem.NavierStokes.NSEConservationCore
-- 总量守恒的核心代数包（C₃ 循环层）+ 剩余装配步骤的障碍记录
--
-- 背景: O3 线的多步/耦合集中需要**总量守恒**（Σ 场量在 `nsStep` 下不变）。
--   该守恒 = 「全环面求和对 `diffF` 恒为 T₀」= 三个单层事实的装配:
--     (i)  C₃ 循环 telescoping（本模块 §1.1, **轴无关的核心定理**）
--     (ii) 求和对 ⊕ 的同态性（**已有**: `NSEOnT6.sum3-+` / `sumN-distrib`）
--     (iii) 求和与取负交换（本模块 §1.2）
--     (iv) 全环面求和的移位不变（本模块 §1.3 的 C₃ 版; 6 层装配见 §2）
--
-- 本模块交付 (i)(iii) 与 C₃ 版 (iv)——**全部闭合, 0 postulate / 0 hole**;
-- §2 记录 6 层装配的**真实障碍**（本库无 funext ⇒ 嵌套 λ 下不可逐点改写）
-- 与可行路线（列表化 + `sumN-distrib`），**不硬写、不留洞**。
--
-- 依赖: NSEOnT6（sum3 / shift3 / sum3-+ / negate-⊕）, NSEFluxTelescope（cancel3）, Base.Trit

module Sovereign.Problem.NavierStokes.NSEConservationCore where

open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; sym; trans; cong; module ≡-Reasoning)

open import Sovereign.Base.Trit using
  (Trit; T₀; T₁; T₂; _⊕_; negate; ⊕-assoc; ⊕-comm; ⊕-identityˡ; ⊕-identityʳ)
open import Sovereign.Problem.NavierStokes.NSEOnT6 using
  (C3; Torus6; ScalarField; sum3; shift3; sum3-+; negate-⊕)
open import Sovereign.Problem.NavierStokes.NSEFluxTelescope using (cancel3; swap2)

open ≡-Reasoning

--------------------------------------------------------------------------------
-- §0. 单坐标求和（C₃ 三点）
--------------------------------------------------------------------------------

fold1 : (C3 → Trit) → Trit
fold1 g = sum3 (g fzero) (g (fsuc fzero)) (g (fsuc (fsuc fzero)))

--------------------------------------------------------------------------------
-- §1.1 核心定理: C₃ 循环 telescoping（轴无关的通量恒零）
--
-- 对**任何** g : C3 → Trit, 沿循环 0→1→2→0 的三段差分之和恒为 T₀。
-- 这是 `NSEFluxTelescope.axisFlux-zero` 的**去轴抽象**版本:
-- 后者是本定理在「固定横截点的轴切片」上的直接实例。
--------------------------------------------------------------------------------

cycle-flux-zero : ∀ (g : C3 → Trit) →
  fold1 (λ y → g (shift3 y) ⊕ negate (g y)) ≡ T₀
cycle-flux-zero g = cancel3 (g fzero) (g (fsuc fzero)) (g (fsuc (fsuc fzero)))

--------------------------------------------------------------------------------
-- §1.2 求和与取负交换: Σ(−aᵢ) ≡ −(Σ aᵢ)
--
-- 链式依据: `negate-⊕`（NSEOnT6:188）三次 + `negate T₀ ≡ T₀`（定义性）。
-- 注意: 取负在各层「合并」为一个外层取负（不是逐层嵌套）——
-- 这正是总量守恒推导里 Σ(diffF) ≡ Σ(shiftF) ⊕ Σ(−f) ≡ Σf ⊕ (−Σf) ≡ T₀ 的关键一步。
--------------------------------------------------------------------------------

sum3-negate : ∀ (a b c : Trit) →
  sum3 (negate a) (negate b) (negate c) ≡ negate (sum3 a b c)
sum3-negate a b c = sym (
  trans (negate-⊕ a (b ⊕ (c ⊕ T₀)))
  (trans (cong (negate a ⊕_) (negate-⊕ b (c ⊕ T₀)))
         (cong (λ z → negate a ⊕ (negate b ⊕ z)) (negate-⊕ c T₀))))

fold1-negate : ∀ (g : C3 → Trit) →
  fold1 (λ y → negate (g y)) ≡ negate (fold1 g)
fold1-negate g = sum3-negate (g fzero) (g (fsuc fzero)) (g (fsuc (fsuc fzero)))

--------------------------------------------------------------------------------
-- §1.3 旋转不变: Σ(g ∘ shift3) ≡ Σ g（C₃ 三点轮转）—— **置换型配对重排**
--
-- 判型（技术文档 §2/§4.3）: `sum3 b c a ≡ sum3 a b c` 是**同项异位、无符号变化**
-- ⇒ **置换型**, 用 `swap2`（非 `swap4`/`cancel-pair`）。两步交换把 a 从第三位换到首位。
-- **命题一字不改**（原 27 条 refl 穷举已替换, 全程不分情形）。
--------------------------------------------------------------------------------

sum3-shift-vals : ∀ (a b c : Trit) →
  sum3 b c a ≡ sum3 a b c
sum3-shift-vals a b c = begin
    sum3 b c a
  ≡⟨ cong (b ⊕_) (swap2 c a T₀) ⟩
    b ⊕ (a ⊕ (c ⊕ T₀))
  ≡⟨ swap2 b a (c ⊕ T₀) ⟩
    sum3 a b c
  ∎

-- 对抗验证（技术文档 §7④: 删去的逐 case 证据以具体点 refl 补回）
sum3-shift-spot₁ : sum3 T₁ T₂ T₀ ≡ sum3 T₀ T₁ T₂
sum3-shift-spot₁ = refl

sum3-shift-spot₂ : sum3 T₂ T₁ T₂ ≡ sum3 T₂ T₂ T₁
sum3-shift-spot₂ = refl

sum3-shift-spot₃ : sum3 T₀ T₀ T₁ ≡ sum3 T₁ T₀ T₀
sum3-shift-spot₃ = refl

fold1-shift : ∀ (g : C3 → Trit) → fold1 (λ y → g (shift3 y)) ≡ fold1 g
fold1-shift g = sum3-shift-vals (g fzero) (g (fsuc fzero)) (g (fsuc (fsuc fzero)))

--------------------------------------------------------------------------------
-- §1.4 逐点 → 整体的提升（**funext 障碍的解除件**, 自我更正）
--
-- 初版 §2 判定「本库无 funext ⇒ `cong fold1` 穿不透 λ, 6 层装配卡住」——**判错了**。
-- 有限折叠的「逐点 → 整体」**不需要 funext**: 对 fold1 的三个求和位各 `cong` 一次即可。
-- 配 `fold1-+`（`sum3-+` 的函数式）, 6 层嵌套装配是「逐层 (fold1-cong ∘ 逐点引理)
-- + fold1-+」的机械重复。装配模块: `Sovereign.Problem.NavierStokes.NSEConservation`。
--------------------------------------------------------------------------------

fold1-cong : ∀ {u v : C3 → Trit} → (∀ y → u y ≡ v y) → fold1 u ≡ fold1 v
fold1-cong {u} {v} p =
  trans (cong (λ z → sum3 z (u (fsuc fzero)) (u (fsuc (fsuc fzero)))) (p fzero))
  (trans (cong (λ z → sum3 (v fzero) z (u (fsuc (fsuc fzero)))) (p (fsuc fzero)))
         (cong (λ z → sum3 (v fzero) (v (fsuc fzero)) z) (p (fsuc (fsuc fzero)))))

fold1-+ : ∀ (u v : C3 → Trit) →
  fold1 (λ y → u y ⊕ v y) ≡ fold1 u ⊕ fold1 v
fold1-+ u v = sum3-+
  (u fzero) (v fzero)
  (u (fsuc fzero)) (v (fsuc fzero))
  (u (fsuc (fsuc fzero))) (v (fsuc (fsuc fzero)))

--------------------------------------------------------------------------------
-- §2. 装配状态（**自我更正后的记录**）
--
-- 目标定理（**已可装配**, 见 `NSEConservation`）:
--   torusSum (diffF i f) ≡ T₀
--   推导链: torusSum(f +S g) ≡ torusSum f ⊕ torusSum g     （fold1-+ 逐层）
--         + torusSum (shiftF i f) ≡ torusSum f             （fold1-shift 逐层）
--         + torusSum (negateF f) ≡ negate (torusSum f)     （fold1-negate 逐层）
--         + x ⊕ negate x ≡ T₀
--   ⇒ Σ(diffF) ≡ Σ(shiftF) ⊕ Σ(−f) ≡ Σf ⊕ (−Σf) ≡ T₀ ⇒ nsStep 保总量。
--
-- 初版此处记的「funext 障碍 + (甲) 列表化/(乙) 逐点化两路线」**已作废**:
-- 障碍被 §1.4 的 `fold1-cong` 解除, 无需列表化、无需 funext。
--------------------------------------------------------------------------------
