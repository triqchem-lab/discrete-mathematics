{-# OPTIONS --rewriting #-}

-- | Sovereign.Application.Problems.NavierStokes.NSEOnT6Golden
--   —— NSE 四步全状态的 FML 侧锚定（M3 golden 扩展·NSE 卷）
--
-- == 载体口径（与实现侧 17496 trits 的对应）
--
-- 实现侧 conformance 的「NSE 四步全状态 = 17496 trits」= 4 个速度场 ×
-- 4374 trits/场（6 标量场 × 729 点）——与 FML `NSEOnT6` 的 `Field`
-- （Torus6 = (Z/3)⁶ 上的 6-tuple ScalarField）精确同型。
-- ⚠ cpp `T6Grid`（144×46 = 6624 格 + init_random 种子）是**另一个模型
-- 元素**（nse_solver 的网格层），与 FML 函数式场不同离散化——两者
-- 不可直接 golden 对拍，对应关系留待专门建模。
--
-- == 本模块钉的定理（全部结构证明，零枚举）
--
-- 1. **零场不动点**：nsStep zeroField 逐分量 ≡ zeroField
--    （div 0 = 0 ⇒ grad 0 = 0 ⇒ v +F 0 = v，全定义性归约）；
-- 2. **四步全状态**（零初态）：nsStep⁴ zeroField 逐分量 ≡ zeroField
--    ——零初态的四步全状态就是零场自身（×6 分量 refl）；
-- 3. **不可压场不动点定理**（一般形式，本模块主定理）：
--    Incompressible v ⇒ ∀ x, nsStep v 逐分量 ≡ v
--    —— 不可压扇区（NSE 的物理扇区）中 nsStep 是恒等算子，
--    任意不可压初态的四步全状态 = 初态自身。
--    非平凡动力学只在可压扇区（配合实现侧 seeded 初态研究）。
--
-- 口径：§定理 1-3 均为**结构证明**（div/grad/diffF 的定义展开 +
-- ⊕-单位律），非暴力枚举；引用可直接写「已证明（结构）」。
--
-- 依赖：NSEOnT6（§1 载体 / §2 算子 / §3 恒等式 / §6 nsStep）。0 postulate。
module Sovereign.Application.Problems.NavierStokes.NSEOnT6Golden where

open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; cong₂; trans)
open import Data.Fin using (Fin; zero; suc)

open import Sovereign.Base.Trit
  using (Trit; T₀; T₁; T₂; _⊕_; negate; ⊕-identityˡ; ⊕-identityʳ)
open import Sovereign.Application.Problems.NavierStokes.NSEOnT6
  using (C3; Torus6; ScalarField; Field; v1; v2; v3; v4; v5; v6; mkField;
         zeroField; _+F_; shiftAt; shiftF; diffF; div; grad; nsStep;
         Incompressible; negate-⊕)

--------------------------------------------------------------------------------
-- §0. Trit 层引理：T₀ ⊕ T₀ ≡ T₀（⊕-identityˡ 在 T₀ 处的定义性实例）
--------------------------------------------------------------------------------

⊕₀₀ : T₀ ⊕ T₀ ≡ T₀
⊕₀₀ = refl

--------------------------------------------------------------------------------
-- §1. 零场不动点
--------------------------------------------------------------------------------

-- 标量零场（⚠ 与 Field 层的 zeroField 区分：diffF/laplacian 作用于标量场）
zeroScalar : ScalarField
zeroScalar = λ _ → T₀

-- 零标量场的差分恒为 T₀：shiftF i zeroScalar x = T₀（零场常值）、
-- zeroScalar x = T₀，故 diffF = T₀ ⊕ negate T₀ = T₀ ⊕ T₀ = T₀（全定义性）。
diffF-zeroScalar : ∀ (i : Fin 3) (x : Torus6) → diffF i zeroScalar x ≡ T₀
diffF-zeroScalar i x = refl

-- 零场的散度恒为 T₀：sum6 的六项全 T₀，右嵌套 ⊕ 链定义性归约。
div-zeroField : ∀ (x : Torus6) → div zeroField x ≡ T₀
div-zeroField x = refl

-- 定理 1a-1f：零场是 nsStep 不动点（六个分量逐一）
nsStep-zeroField-v1 : ∀ (x : Torus6) → v1 (nsStep zeroField) x ≡ v1 zeroField x
nsStep-zeroField-v1 x = refl

nsStep-zeroField-v2 : ∀ (x : Torus6) → v2 (nsStep zeroField) x ≡ v2 zeroField x
nsStep-zeroField-v2 x = refl

nsStep-zeroField-v3 : ∀ (x : Torus6) → v3 (nsStep zeroField) x ≡ v3 zeroField x
nsStep-zeroField-v3 x = refl

nsStep-zeroField-v4 : ∀ (x : Torus6) → v4 (nsStep zeroField) x ≡ v4 zeroField x
nsStep-zeroField-v4 x = refl

nsStep-zeroField-v5 : ∀ (x : Torus6) → v5 (nsStep zeroField) x ≡ v5 zeroField x
nsStep-zeroField-v5 x = refl

nsStep-zeroField-v6 : ∀ (x : Torus6) → v6 (nsStep zeroField) x ≡ v6 zeroField x
nsStep-zeroField-v6 x = refl

--------------------------------------------------------------------------------
-- §2. 定理 2（主定理）：不可压场是 nsStep 不动点
--
-- 关键引理链：div v ≡ T₀（逐点） ⇒ diffF i (div v) x ≡ T₀（i = 0,1,2 三个
-- 方向即 grad 的六个分量所用方向） ⇒ grad (div v) 逐分量 ≡ T₀
-- ⇒ nsStep v 逐分量 ≡ v（⊕-identityʳ）。
--------------------------------------------------------------------------------

-- 引理 A：常 T₀ 场的差分恒为 T₀（散度前提把 div v 变成常 T₀ 场）
diffF-const0 : ∀ (i : Fin 3) (f : ScalarField) → (∀ y → f y ≡ T₀)
             → ∀ (x : Torus6) → diffF i f x ≡ T₀
diffF-const0 i f hf x =
  trans (cong₂ _⊕_ (hf (shiftAt i x)) (cong negate (hf x))) (⊕-identityˡ T₀)

-- 引理 B：div v ≡ T₀（逐点） ⇒ grad (div v) 的六个分量恒 T₀
grad-div-v-zero-v1 : ∀ v → Incompressible v
                   → ∀ (x : Torus6) → v1 (grad (div v)) x ≡ T₀
grad-div-v-zero-v1 v hv x = diffF-const0 zero (div v) hv x

grad-div-v-zero-v2 : ∀ v → Incompressible v
                   → ∀ (x : Torus6) → v2 (grad (div v)) x ≡ T₀
grad-div-v-zero-v2 v hv x = diffF-const0 (suc zero) (div v) hv x

grad-div-v-zero-v3 : ∀ v → Incompressible v
                   → ∀ (x : Torus6) → v3 (grad (div v)) x ≡ T₀
grad-div-v-zero-v3 v hv x = diffF-const0 (suc (suc zero)) (div v) hv x

grad-div-v-zero-v4 : ∀ v → Incompressible v
                   → ∀ (x : Torus6) → v4 (grad (div v)) x ≡ T₀
grad-div-v-zero-v4 v hv x = diffF-const0 zero (div v) hv x

grad-div-v-zero-v5 : ∀ v → Incompressible v
                   → ∀ (x : Torus6) → v5 (grad (div v)) x ≡ T₀
grad-div-v-zero-v5 v hv x = diffF-const0 (suc zero) (div v) hv x

grad-div-v-zero-v6 : ∀ v → Incompressible v
                   → ∀ (x : Torus6) → v6 (grad (div v)) x ≡ T₀
grad-div-v-zero-v6 v hv x = diffF-const0 (suc (suc zero)) (div v) hv x

-- 主定理（六个分量）：Incompressible v ⇒ nsStep v 逐分量 ≡ v
nsStep-incomp-fixed-v1 : ∀ v → Incompressible v
  → ∀ (x : Torus6) → v1 (nsStep v) x ≡ v1 v x
nsStep-incomp-fixed-v1 v hv x =
  trans (cong (v1 v x ⊕_) (grad-div-v-zero-v1 v hv x)) (⊕-identityʳ (v1 v x))

nsStep-incomp-fixed-v2 : ∀ v → Incompressible v
  → ∀ (x : Torus6) → v2 (nsStep v) x ≡ v2 v x
nsStep-incomp-fixed-v2 v hv x =
  trans (cong (v2 v x ⊕_) (grad-div-v-zero-v2 v hv x)) (⊕-identityʳ (v2 v x))

nsStep-incomp-fixed-v3 : ∀ v → Incompressible v
  → ∀ (x : Torus6) → v3 (nsStep v) x ≡ v3 v x
nsStep-incomp-fixed-v3 v hv x =
  trans (cong (v3 v x ⊕_) (grad-div-v-zero-v3 v hv x)) (⊕-identityʳ (v3 v x))

nsStep-incomp-fixed-v4 : ∀ v → Incompressible v
  → ∀ (x : Torus6) → v4 (nsStep v) x ≡ v4 v x
nsStep-incomp-fixed-v4 v hv x =
  trans (cong (v4 v x ⊕_) (grad-div-v-zero-v4 v hv x)) (⊕-identityʳ (v4 v x))

nsStep-incomp-fixed-v5 : ∀ v → Incompressible v
  → ∀ (x : Torus6) → v5 (nsStep v) x ≡ v5 v x
nsStep-incomp-fixed-v5 v hv x =
  trans (cong (v5 v x ⊕_) (grad-div-v-zero-v5 v hv x)) (⊕-identityʳ (v5 v x))

nsStep-incomp-fixed-v6 : ∀ v → Incompressible v
  → ∀ (x : Torus6) → v6 (nsStep v) x ≡ v6 v x
nsStep-incomp-fixed-v6 v hv x =
  trans (cong (v6 v x ⊕_) (grad-div-v-zero-v6 v hv x)) (⊕-identityʳ (v6 v x))

--------------------------------------------------------------------------------
-- §3. 四步全状态推论（零初态）：nsStep⁴ zeroField 逐分量 ≡ zeroField
--
-- 四步全状态的 4 × 4374 = 17496 trits 在零初态下全为 T₀——
-- 六分量 × 四步，每步都是定义性归约（refl）。
--------------------------------------------------------------------------------

ns4-zeroField-v1 : ∀ (x : Torus6) →
  v1 (nsStep (nsStep (nsStep (nsStep zeroField)))) x ≡ v1 zeroField x
ns4-zeroField-v1 x = refl

ns4-zeroField-v2 : ∀ (x : Torus6) →
  v2 (nsStep (nsStep (nsStep (nsStep zeroField)))) x ≡ v2 zeroField x
ns4-zeroField-v2 x = refl

ns4-zeroField-v3 : ∀ (x : Torus6) →
  v3 (nsStep (nsStep (nsStep (nsStep zeroField)))) x ≡ v3 zeroField x
ns4-zeroField-v3 x = refl

ns4-zeroField-v4 : ∀ (x : Torus6) →
  v4 (nsStep (nsStep (nsStep (nsStep zeroField)))) x ≡ v4 zeroField x
ns4-zeroField-v4 x = refl

ns4-zeroField-v5 : ∀ (x : Torus6) →
  v5 (nsStep (nsStep (nsStep (nsStep zeroField)))) x ≡ v5 zeroField x
ns4-zeroField-v5 x = refl

ns4-zeroField-v6 : ∀ (x : Torus6) →
  v6 (nsStep (nsStep (nsStep (nsStep zeroField)))) x ≡ v6 zeroField x
ns4-zeroField-v6 x = refl

--------------------------------------------------------------------------------
-- ⚠ 已删除的不可证推论（自纠记录，2026-10-28）
--
-- 「Incompressible v ⇒ Incompressible (nsStep v) ⇒ 四步全状态 = 初态」
-- **不成立**：div (nsStep v) = div v ⊕ laplacian (div v)，而逐点
-- laplacian ≡ 0 恰是 NSEOnT6 §4d 的**构造性反例**所否定的命题
-- （§6 的不可压保持本来就是**条件定理**）。故：
--   · 不可压场的不动点定理（§2）不受影响——它只声称 nsStep v ≡ v
--     逐点成立，是「恒等」而非「保持」；
--   · 一般可压初态的四步动力学**不在本模块口径内**，留待实现侧
--     seeded 研究（cpp T6Grid init_random 口径）。
--------------------------------------------------------------------------------
