{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Problem.NavierStokes.NSEMadelungConstrained
-- Madelung 耦合「受约束版」的判定：为何钉死 Qphase 仍不够，以及正确的归约形式
--
-- 背景: 上一轮我（依据 `NSEPhaseField:350` 的散文注记）建议把 O2 重述为
--   「**钉死** Qphase := quantumPotentialPhase，再问 transport 是否存在」。
--   本模块证明: **该重述仍然是空洞的** —— 因为 `transport` 依旧是自由字段。
--   这是对**我自己上一轮提议**的更正。
--
-- 结论结构:
--   §0 两条局部代数引理 (库内缺失的左逆 / 解耦引理)
--   §1 **钉死 Q 也无用**: 对**任意** Q 都有 transport 使耦合律成立 (仍由 refl 给出)
--   §2 **正确形态**: 只有让**两边都由场决定**才有内容, 即
--        coupling-full : ∀ θ x → phaseDiff zero θ x
--                      ≡ mulAlpha (quantumPotentialPhase θ x) (pressurePhase θ x)
--      本模块给出**归约引理**: 该式**等价于** `p² ≡ Q`
--        (p := phaseDiff zero θ x, Q := quantumPotentialPhase θ x)
--      —— 因为 pressurePhase 定义为 p 的逆, 两边同乘 p 即化为平方等式。
--   §3 该归约形式的现状 (诚实标注, 含对 `:350` 散文断言的核查)
--
-- ⚠ 对 `NSEPhaseField:350` 的核查: 其注记「真正非平凡的耦合方程对任意 θ 不成立
--   (反例 θ-e1-e2 在原点)」中的 **`theta-e1-e2` 在源码中不存在**
--   (`grep -n "theta-e1-e2" NSEPhaseField.agda` → 0 命中) ⇒ 它是**纯散文断言、未形式化**,
--   不得当作已证事实引用。
--
-- 0 postulate / 0 hole

module Sovereign.Problem.NavierStokes.NSEMadelungConstrained where

open import Data.Product using (Σ; _,_)
open import Data.Fin using (zero; suc)
open import Relation.Binary.PropositionalEquality using (refl; trans; cong; sym; _≡_)

open import Sovereign.Algebra.GroupTheory.DuodecClock using (
  AlphaPower; a0; a1; a2; a3; mulAlpha; alphaInv;
  mulAlpha-assoc; mulAlpha-identityʳ; mulAlpha-inverse)
open import Sovereign.Problem.NavierStokes.NSEPhaseField using (
  PhField; phaseDiff; pressurePhase; quantumPotentialPhase)

--------------------------------------------------------------------------------
-- §0. 两条局部代数引理
--
-- ① `alphaInv-invˡ`: 库内只有**右**逆 `mulAlpha-inverse : x · x⁻¹ ≡ a0`,
--    这里需要左逆 `x⁻¹ · x ≡ a0`。C₄ 只有 4 个元素, 逐 case 即得。
-- ② `solve-lemma`: `(t · p⁻¹) · p ≡ t`  (结合律 + 左逆 + 单位律)
--------------------------------------------------------------------------------

alphaInv-invˡ : ∀ x → mulAlpha (alphaInv x) x ≡ a0
alphaInv-invˡ a0 = refl
alphaInv-invˡ a1 = refl
alphaInv-invˡ a2 = refl
alphaInv-invˡ a3 = refl

solve-lemma : ∀ (t p : AlphaPower) → mulAlpha (mulAlpha t (alphaInv p)) p ≡ t
solve-lemma t p =
  trans (mulAlpha-assoc t (alphaInv p) p)
        (trans (cong (λ z → mulAlpha t z) (alphaInv-invˡ p))
               (mulAlpha-identityʳ t))

--------------------------------------------------------------------------------
-- §1. 钉死 Q 也不能救活该义务
--
-- 对**任意**给定的 Q (特别地 Q := quantumPotentialPhase),
-- 取 transport := Q · pressurePhase 即满足 coupling 律 (由 refl)。
-- ⇒ transport 自由 ⇒ 方程仍不约束任何东西。
--------------------------------------------------------------------------------

pinned-Q-still-vacuous : (Q : PhField → PhField) →
  Σ (PhField → PhField)
    (λ t → ∀ θ x → t θ x ≡ mulAlpha (Q θ x) (pressurePhase θ x))
pinned-Q-still-vacuous Q =
  (λ θ x → mulAlpha (Q θ x) (pressurePhase θ x)) , (λ θ x → refl)

--------------------------------------------------------------------------------
-- §2. 正确形态与归约引理
--
-- 只有**两边都由场决定**时方程才有内容:
--   p ≡ Q · p⁻¹        (p := phaseDiff zero θ x, Q := quantumPotentialPhase θ x)
-- 由于 pressurePhase θ x = (phaseDiff zero θ x)⁻¹ (定义, NSEPhaseField:344),
-- 两边同乘 p 即得等价的平方等式  p² ≡ Q。
--------------------------------------------------------------------------------

-- 正向: p ≡ Q · p⁻¹  ⇒  p² ≡ Q
coupling⇒square : ∀ (p Q : AlphaPower) → p ≡ mulAlpha Q (alphaInv p) → mulAlpha p p ≡ Q
coupling⇒square p Q h =
  trans (cong (λ z → mulAlpha z p) h) (solve-lemma Q p)

-- 反向: p² ≡ Q  ⇒  p ≡ Q · p⁻¹
square⇒coupling : ∀ (p Q : AlphaPower) → mulAlpha p p ≡ Q → p ≡ mulAlpha Q (alphaInv p)
square⇒coupling p Q h =
  sym (trans (sym (cong (λ z → mulAlpha z (alphaInv p)) h))
             (trans (mulAlpha-assoc p p (alphaInv p))
                    (trans (cong (λ z → mulAlpha p z) (mulAlpha-inverse p))
                           (mulAlpha-identityʳ p))))

--------------------------------------------------------------------------------
-- §3. 归约后的义务形态 (诚实标注)
--
-- 由 §2, 「两边都由场决定」的耦合方程等价于:
--
--      (★)  ∀ θ x → mulAlpha (phaseDiff zero θ x) (phaseDiff zero θ x)
--                   ≡ quantumPotentialPhase θ x
--
-- 即: **0-轴相位输运的平方** 是否等于 **六轴相位差的共轭乘积**。
-- 这是一个**尖锐的恒等式**, 不是自由参数问题 ⇒ 它**可能为真, 也可能为假**,
-- 是有内容的义务 (与 §1 的恒真问题形成对照)。
--
-- 现状 (诚实):
--   ✓ 已知**单点**成立: `NSEPhaseField:477-481 madelung-witness` 在
--     (θ-e1, origin) 处给出 refl 等式; 而 `:455 Qphase-e1-origin` 给出该点 Q = a2,
--     且 `:451 phaseDiff-e1-zero` 给出该点 p = a1, 而 a1² = a2 —— 三者自洽。
--   ✗ **全称版 (★) 未知**: 未证明, 也未找到反例。
--   ✗ `NSEPhaseField:350` 声称的反例 `θ-e1-e2` **在源码中不存在**(grep 0 命中)
--     ⇒ 该断言**未形式化**, 不得当作反例证据。
--
-- 下一步(不在本模块内): 对 (★) 做**优先穷举搜索**——相位场空间小
--   (6 轴上取值 ∈ C₄), 可用小的生成元族穷举找反例或确认; 若找到反例,
--   则 (★) 应标 refuted 并附见证; 若全例通过则再考虑符号化证明。
--------------------------------------------------------------------------------
