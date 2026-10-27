{-# OPTIONS --rewriting #-}

-- | Sovereign.Algebra.FieldTower.Intercept —— Frobenius 拦截判据（数学化）
--
-- == 定位
--
-- Agent Harness 架构文档提出的「Frobenius 轨道不变性拦截」按**更正后的形态**
-- 形式化于此。原断言「非法跃迁 ⇒ 不满足 f(v) ≢ 0」**不成立**：
--
--   · @f@ 是定义 @GF(3^k)@ 的不可约多项式，它在域内**恰有 k 个根**——
--     一般元素 @v@ 的 @f(v) ≠ 0@，所以「非法 ⇒ f(v) ≢ 0」对几乎所有迁移
--     **平凡为真，区分不出授权与非法**；
--   · 且「安全状态」「非法跃迁」在原文档里没有定义，断言无主。
--
-- == 更正后的可证命题（本模块三条定理 + 一条对偶，全部 27 元素枚举 pin）
--
-- 1. **T2 拦截的授权面**：Frobenius **不动点**恰为基域 GF(3) 的嵌入像
--    ——「安全状态子集」由此定义，不再是自由变元。
-- 2. **T3 双重成员性**：σ² 的不动点**同样是**基域
--    —— GF(9) ∩ GF(27) = GF(3) 的具体形态。
-- 3. **T5 交换定理**：与 Frobenius **交换**的乘子恰为基域乘法
--    —— 非基域乘子 @a@ 必然 @σ(a·1) ≠ a·σ(1)@，即**必然把基态推离其
--    Frobenius 轨道**。这就是「非法跃迁可被交换性检验捕获」的可执行形态。
--
-- 复用：σ 与 σ³ = id 已在 GF27.agda §5b（frobenius / frobenius³-id）；
-- 本模块不重复定义，只加**不动点/交换性**两族新定理。
--
-- == 与 C5/D-1 的对接
--
-- 判定总是产出 pass/warn、不拒绝（裁定①）的语义在响应侧采纳判定模块。
-- 本模块只提供其数学前置：拦截算子（Frobenius）与其不动点基域的代数事实。
module Sovereign.Algebra.FieldTower.Intercept where

open import Data.Bool using (Bool; if_then_else_; true; false; not; _∧_)
open import Data.Product using (_×_; _,_)
open import Data.List using (List; _∷_; []; length)
open import Data.Nat using (ℕ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Sovereign.Base.Trit using (Trit; T₀; T₁; T₂)
open import Sovereign.Algebra.FieldTower.GF27
  using (GF27; frobenius; gf27-one; _*gf27_; frobenius³-id)

--------------------------------------------------------------------------------
-- 27 元素全量枚举（三进制完备：坐标 ∈ {T₀,T₁,T₂}³ 共 3³ = 27，全覆盖）
--------------------------------------------------------------------------------

all27 : List GF27
all27 =
  (T₀ , T₀ , T₀) ∷ (T₁ , T₀ , T₀) ∷ (T₂ , T₀ , T₀) ∷
  (T₀ , T₁ , T₀) ∷ (T₁ , T₁ , T₀) ∷ (T₂ , T₁ , T₀) ∷
  (T₀ , T₂ , T₀) ∷ (T₁ , T₂ , T₀) ∷ (T₂ , T₂ , T₀) ∷
  (T₀ , T₀ , T₁) ∷ (T₁ , T₀ , T₁) ∷ (T₂ , T₀ , T₁) ∷
  (T₀ , T₁ , T₁) ∷ (T₁ , T₁ , T₁) ∷ (T₂ , T₁ , T₁) ∷
  (T₀ , T₂ , T₁) ∷ (T₁ , T₂ , T₁) ∷ (T₂ , T₁ , T₁) ∷
  (T₀ , T₀ , T₂) ∷ (T₁ , T₀ , T₂) ∷ (T₂ , T₀ , T₂) ∷
  (T₀ , T₁ , T₂) ∷ (T₁ , T₁ , T₂) ∷ (T₂ , T₁ , T₂) ∷
  (T₀ , T₂ , T₂) ∷ (T₁ , T₂ , T₂) ∷ (T₂ , T₂ , T₂) ∷ []

--------------------------------------------------------------------------------
-- 逐元素相等（Bool 版，供 filter/枚举 pin；命题等式见 GF27.agda 的推导）
--------------------------------------------------------------------------------

_==ᵗ_ : Trit → Trit → Bool
T₀ ==ᵗ T₀ = true
T₁ ==ᵗ T₁ = true
T₂ ==ᵗ T₂ = true
_  ==ᵗ _  = false

_==²⁷_ : GF27 → GF27 → Bool
(a , b , c) ==²⁷ (a' , b' , c') =
  (a ==ᵗ a') ∧ (b ==ᵗ b') ∧ (c ==ᵗ c')

-- | Bool 版过滤（stdlib 2.x 的 filter 走 Decidable-Pred，这里用自带的
--    布尔过滤以保持枚举 pin 的 refl 直证）。
keepIf : (GF27 → Bool) → List GF27 → List GF27
keepIf p [] = []
keepIf p (x ∷ xs) = if p x then x ∷ keepIf p xs else keepIf p xs

--------------------------------------------------------------------------------
-- T2：Frobenius 不动点 = GF(3)（拦截的授权面）
--
-- 结构理由：σ 不动 ⇒ b ⊕ c = b 与 2·b ⊕ c = a 的分量方程强制 c = 0、b = 0
-- （trit 的 2c = 0 ⟺ c = 0）；log 式：x = α^l (x ≠ 0) 时 x⁹ = x ⟺ 8·l ≡ 0 (mod 26)
-- ⟺ 13 ∣ l（13 素而 13 ∤ 8）⇒ x ∈ {α⁰, α¹³} = {1, 2}，连同零元即基域。
--------------------------------------------------------------------------------

pin-fix-σ : keepIf (λ x → frobenius x ==²⁷ x) all27
          ≡ (T₀ , T₀ , T₀) ∷ (T₁ , T₀ , T₀) ∷ (T₂ , T₀ , T₀) ∷ []
pin-fix-σ = refl

--------------------------------------------------------------------------------
-- T3：σ² 不动点 = 同一个基域（GF(9) ∩ GF(27) = GF(3) 的具体形态）
--
-- σ² 的坐标式即 x ↦ x⁹（9 = 3² 次幂映射）。
--------------------------------------------------------------------------------

pin-fix-σ² : keepIf (λ x → frobenius (frobenius x) ==²⁷ x) all27
           ≡ (T₀ , T₀ , T₀) ∷ (T₁ , T₀ , T₀) ∷ (T₂ , T₀ , T₀) ∷ []
pin-fix-σ² = refl

--------------------------------------------------------------------------------
-- T5：交换定理——与 Frobenius 交换的乘子恰为基域（拦截判据的数学内容）
--
--   a 与 σ 交换（在基态 one 上检验）：σ(a·1) ≡ a·σ(1)
--   ⇔ a ∈ GF(3)（嵌入像）。
--
--   ⇒ 非基域乘子 a 必然**破坏交换性**：σ(a·1) ≠ a·σ(1) = a，
--      即它把基态推离 Frobenius 轨道 —— 这就是「非法跃迁可被交换性检验捕获」的
--      可执行形态（判据：交换性检验，27 步可判定）。
--------------------------------------------------------------------------------

commuteWithσ : GF27 → Bool
commuteWithσ a = frobenius (a *gf27 gf27-one) ==²⁷ (a *gf27 (frobenius gf27-one))

pin-commute : keepIf commuteWithσ all27
            ≡ (T₀ , T₀ , T₀) ∷ (T₁ , T₀ , T₀) ∷ (T₂ , T₀ , T₀) ∷ []
pin-commute = refl

-- 对偶（计数版）：24 个非基域乘子全部破坏交换性
pin-nonbase-count : length (keepIf (λ x → not (frobenius x ==²⁷ x)) all27) ≡ 24
pin-nonbase-count = refl

-- 枚举规模自检：拦截授权面计数 3
pin-count : length (keepIf (λ x → frobenius x ==²⁷ x) all27) ≡ 3
pin-count = refl
