{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Algebra.GF9FrobeniusC4
-- Frobenius = x³ 的全域形式化，及其在 C₄ 相位子群上**等于取逆**这一定理。
--
-- 定位（本模块只补缺，不重复已证）：
--   · `FieldTower/GF9.agda` 已证：galoisConjugate 定义、σ²=id、σ 的不动点是基座、
--     alpha 的立方 = σ(alpha)、φ=1+2α 的 8 阶性、α⁴=1。
--     ⇒ 本模块**不重定义** GF9 / α / σ / C₈ 生成元。
--   · `GroupTheory/PhaseSubgroup.agda` 已证：⟨α⟩ ≅ C₄ ⊂ GF(9)×≅C₈，α=gen⁶。
--     ⇒ 本模块**不重复**阶的计算。
--
--   · 本模块新增（此前缺口）：
--       §1 frob9-is-cube      — **一般元素** x 的 σ(x) ≡ x³（9-case 穷举）
--       §2 alphaPow / frob9-c4-action — σ 在 C₄ 上**逐元素等于取逆**
--       §3 frob9-c4-inverse   — 代数形式：x · σ(x) ≡ 1（4-case 穷举）
--
-- ═══════════════════════════════════════════════════════════════
-- 八要素对照（形状规范: docs/maps/八要素统一形状-2026-10-14.md）
-- ═══════════════════════════════════════════════════════════════
--  ① 载体      GF(9) = GF(3)[α]/(α²+1)；C₄ = ⟨α⟩ = {1, α, α², α³}
--  ② 生成元    α（C₄）、φ=1+2α（C₈，见 GF9）；σ 由域自同构给出，非外加
--  ③ 关系      α⁴ = 1（GF9: alpha-powers-4）；σ² = id（GF9: galoisConjugate²）
--  ④ 相位      alphaPow : Fin 4 → GF9（0°/90°/180°/270°）
--  ⑤ 时钟      **本件不提供**：C₄ 是相位，不是会话级时钟（时钟留在 wuxing / DC）
--  ⑥ 归零      α⁴ = 1（导入）；本模块的 σ³ 闭合不构成新归零
--  ⑦ 刚性      **本件即「刚性」要素的专门补件**：σ = Frobenius = x³，
--              且在 C₄ 上 σ = 取逆（frob9-c4-action）
--  ⑧ 核对      9-case（全域）/ 4-case（C₄）穷举 refl；另证 σ ≠ id 于 α
--
-- 形状贴合: **6/8**（① ② ③ ④ ⑦ ⑧；缺 ⑤ 时钟、⑥ 归零——二者属 DC 层）
--
-- ⚠ 范畴红线（不得混读）：
--   · 本模块的 σ 是**域自同构**（加法分量不动），不是群反转 ρ = λ∘μ
--     （见 docs/duodecimal/39-frobenius-vs-group-inversion.md）。
--   · 7/8 ≠ 12：C₄ ⊂ C₈ 的阶与 DC 的 12 是不同层的数，不可互推。

module Sovereign.Algebra.GF9FrobeniusC4 where

open import Data.Fin using (Fin; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)

open import Sovereign.Base.Trit using (Trit; T₀; T₁; T₂; negate; negate²)
open import Sovereign.Algebra.FieldTower.GF9 using
  ( GF9; alpha; gf9-one; galoisConjugate; galoisConjugate²
  ; _*gf9_; alpha-squared; alpha-powers-4
  ; sigma-alpha; frobenius-alpha-is-cube )

--------------------------------------------------------------------------------
-- 1. Frobenius 就是三次方（一般元素）
--

-- | 对 GF(9) 的**每个**元素，Galois 共轭等于立方。
--
-- 数学依据（char 3 下三个中间项全消）：
--   (a+bα)³ = a³ + 3a²bα + 3ab²α² + b³α³ ≡ a³ + b³α³
--          = a³ − b³  (α³ = −α)
--          = a − b    (Fermat: x³ ≡ x mod 3)
-- 全部 9 个输入均为构造子，故每一分支都是 refl（计算归约，非公理）。
frob9-is-cube : ∀ x → galoisConjugate x ≡ x *gf9 (x *gf9 x)
frob9-is-cube (T₀ , T₀) = refl
frob9-is-cube (T₀ , T₁) = refl
frob9-is-cube (T₀ , T₂) = refl
frob9-is-cube (T₁ , T₀) = refl
frob9-is-cube (T₁ , T₁) = refl
frob9-is-cube (T₁ , T₂) = refl
frob9-is-cube (T₂ , T₀) = refl
frob9-is-cube (T₂ , T₁) = refl
frob9-is-cube (T₂ , T₂) = refl

--------------------------------------------------------------------------------
-- 2. C₄ 相位子群上的 Frobenius = 取逆
--

-- | C₄ = ⟨α⟩ 的四个元素，按 0°/90°/180°/270° 编号。
alphaPow : Fin 4 → GF9
alphaPow zero                = gf9-one
alphaPow (suc zero)          = alpha
alphaPow (suc (suc zero))    = alpha *gf9 alpha
alphaPow (suc (suc (suc zero))) = (alpha *gf9 alpha) *gf9 alpha

-- | C₄ 上的取逆指数：0↦0, 1↦3, 2↦2, 3↦1（k ↦ −k mod 4）。
inv4 : Fin 4 → Fin 4
inv4 zero                       = zero
inv4 (suc zero)                 = suc (suc (suc zero))   -- 1 ↦ 3
inv4 (suc (suc zero))           = suc (suc zero)         -- 2 ↦ 2
inv4 (suc (suc (suc zero)))     = suc zero               -- 3 ↦ 1

-- | **核心定理**：Frobenius 在 C₄ 上逐元素等于取逆。
--
-- 这就是「刚性作用只碰相位分量」的形式化：9-case 的全域 σ(x)=x³ 之下，
-- 限制到 C₄ 恰好是 αᵏ ↦ α⁻ᵏ。逐元素 refl，无 postulate。
frob9-c4-action : ∀ k → galoisConjugate (alphaPow k) ≡ alphaPow (inv4 k)
frob9-c4-action zero                    = refl
frob9-c4-action (suc zero)              = refl
frob9-c4-action (suc (suc zero))        = refl
frob9-c4-action (suc (suc (suc zero)))  = refl

-- | 同一事实的代数形式：x · σ(x) = 1（“取逆”不依赖指数编号）。
frob9-c4-inverse : ∀ k → alphaPow k *gf9 galoisConjugate (alphaPow k) ≡ gf9-one
frob9-c4-inverse zero                    = refl
frob9-c4-inverse (suc zero)              = refl
frob9-c4-inverse (suc (suc zero))        = refl
frob9-c4-inverse (suc (suc (suc zero)))  = refl

--------------------------------------------------------------------------------
-- 3. 否证式核对（⑧）：σ 不是恒等，也有非平凡作用
--

-- | α 不是 Frobenius 的不动点（α ∉ GF(3)）。
sigma-alpha-not-id : galoisConjugate alpha ≡ alpha → ⊥
sigma-alpha-not-id ()

-- | σ 是对合，且在 C₄ 上非平凡 ⇒ 它在 C₄ 上的作用就是那个唯一的 2 阶自同构。
frob9-c4-involution : ∀ k → galoisConjugate (galoisConjugate (alphaPow k)) ≡ alphaPow k
frob9-c4-involution k = galoisConjugate² (alphaPow k)
