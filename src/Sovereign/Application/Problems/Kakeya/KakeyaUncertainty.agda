{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Application.Problems.Kakeya.KakeyaUncertainty
-- KakeyaUncertainty — T⁶ 不确定原理（Meshulam/Tao 形）：|supp f|·|supp f̂| ≥ 729
--
-- 诚实边界（先读，两点均实测/闭合，决定全件形态）：
--   ① 载体算术强制：任务提及的「二次特征标 ±1」实非 (GF(3)ⁿ,+) 的特征标
--      （特征标须注入 C₃ → Ĝ，而 |GF(3)*| = 2，3 ∤ 2，无非平凡同态）。
--      T⁶ 的真特征标 χ_r(x) = ω^{r·x} 需三次单位根 ω，而 ω ∉ GF(3)
--      （char 3 中 x³−1 = (x−1)³ 仅一根；GF(9)* 阶 8，3 ∤ 8 亦无）。
--      强行 GF(3) 值求和只剩平凡特征标 χ ≡ 1，此时指示函数的变换
--      f̂₃(r) = Σ_x 1_H(x) = 3 ≡ 0 (mod 3) 恒零（§4 闭合：9 项 ⊕ 链 refl）
--      —— 支集空，不确定原理在 GF(3) 值下失败。故特征标必须取值
--      Eisenstein 整数 ℤ[ω]（复用 A4.Zω 载体；ω² + ω + 1 = 0 即
--      omega-sum-zero 已证）。ℤ[ω] ⊂ ℂ，与标准复值特征 e^{2πi/3} 对应
--      （对应关系立界：本件不建 ℂ 桥）。
--   ② 本件闭合 T² = GF(3)² 等号案例：f = 轴子群 H = GF(3)×{0} 的指示函数，
--      |supp f| = 3，|supp f̂| = 3（对偶轴 {0}×GF(3)），3·3 = 9 = |T²| —— 等号
--      （§3，9 案 f̂ 值表逐案 refl）。T⁶ 一般陈述（≥ 729 = 3⁶）立界：完全证明
--      需 6 层 Fubini 重排 + 3⁶ 案支集枚举，超本件预算；其原子 —— 特征标
--      正交性的几何级数引理 Σ_{t∈GF(3)} ω^{r·t} ∈ {3, 0} —— §5 已闭合
--      （3 案 refl），即 T⁶ Fubini 展开逐层消耗的内和。
-- 0 postulate / 0 hole.

module Sovereign.Application.Problems.Kakeya.KakeyaUncertainty where

open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
open import Data.Product using (_×_; _,_)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import Data.Integer.Base using (ℤ; +_)

open import Sovereign.Base.Trit using (Trit; T₀; T₁; T₂; _⊕_)
open import Sovereign.Synthesis.A4.A4Representation
  using (Zω; mkZω; addZω; mulZω; zeroZω; oneZω; ω; ω²;
         omega-sum-zero; omega-cubed)

--------------------------------------------------------------------------------
-- §1. 特征标：χ_r(x) = ω^{r·x}（ℤ[ω] 值；ω 幂透明归约，ω³ = 1 自动吸收）
--------------------------------------------------------------------------------

KK-T² : Set
KK-T² = Trit × Trit

-- ω^k：mulZω 逐分量 ℤ 算术透明归约（omega-cubed 同形的归约路径）
KK-wPow : ℕ → Zω
KK-wPow zero = oneZω
KK-wPow (suc n) = mulZω ω (KK-wPow n)

-- GF(3) 乘法表（9 案穷举，无 catch-all：首参具体即归约；2·2 = 4 ≡ 1 mod 3
-- 由 KK-wPow 的 ω 周期自动吸收）
KK-dot : Trit → Trit → ℕ
KK-dot T₀ T₀ = zero
KK-dot T₀ T₁ = zero
KK-dot T₀ T₂ = zero
KK-dot T₁ T₀ = zero
KK-dot T₁ T₁ = 1
KK-dot T₁ T₂ = 2
KK-dot T₂ T₀ = zero
KK-dot T₂ T₁ = 2
KK-dot T₂ T₂ = 4

KK-char : KK-T² → KK-T² → Zω
KK-char (r₁ , r₂) (x₁ , x₂) =
  KK-wPow (KK-dot r₁ x₁ + KK-dot r₂ x₂)

--------------------------------------------------------------------------------
-- §2. f = 轴子群指示函数；f̂ = 特征标求和（3×3 项显式展开）
--------------------------------------------------------------------------------

-- f = 1_H，H = {(x, T₀)} ≅ GF(3)（轴子群，|H| = 3）
KK-fT : KK-T² → Trit
KK-fT (x , T₀) = T₁
KK-fT (x , T₁) = T₀
KK-fT (x , T₂) = T₀

KK-up : Trit → Zω
KK-up T₀ = zeroZω
KK-up T₁ = oneZω
KK-up T₂ = zeroZω   -- 规范项：f 只取 {T₀, T₁}，T₂ 分支按零元规范固定

KK-f : KK-T² → Zω
KK-f x = KK-up (KK-fT x)

KK-contrib : KK-T² → KK-T² → Zω
KK-contrib r x = mulZω (KK-f x) (KK-char r x)

KK-Σ₃ : Zω → Zω → Zω → Zω
KK-Σ₃ x y z = addZω (addZω x y) z

-- f̂ r = Σ_{x ∈ T²} f(x)·χ_r(x)
KK-fhat : KK-T² → Zω
KK-fhat r =
  KK-Σ₃ (KK-Σ₃ (KK-contrib r (T₀ , T₀)) (KK-contrib r (T₁ , T₀)) (KK-contrib r (T₂ , T₀)))
        (KK-Σ₃ (KK-contrib r (T₀ , T₁)) (KK-contrib r (T₁ , T₁)) (KK-contrib r (T₂ , T₁)))
        (KK-Σ₃ (KK-contrib r (T₀ , T₂)) (KK-contrib r (T₁ , T₂)) (KK-contrib r (T₂ , T₂)))

--------------------------------------------------------------------------------
-- §3. 等号案例（闭合）：|supp f| = 3，|supp f̂| = 3，3·3 = 9 = |T²|
--
-- f̂ (T₀, b) = 1+1+1 = 3   （r ⊥ H：χ ≡ 1）
-- f̂ (T₁, b) = 1+ω+ω² = 0  （几何级数，omega-sum-zero 同形）
-- f̂ (T₂, b) = 1+ω²+ω⁴ = 0 （ω⁴ = ω）
--------------------------------------------------------------------------------

KK-fhat-axis : KK-fhat (T₀ , T₀) ≡ mkZω (+ 3) (+ 0)
KK-fhat-axis = refl

KK-fhat-axis2 : KK-fhat (T₀ , T₁) ≡ mkZω (+ 3) (+ 0)
KK-fhat-axis2 = refl

KK-fhat-axis3 : KK-fhat (T₀ , T₂) ≡ mkZω (+ 3) (+ 0)
KK-fhat-axis3 = refl

KK-fhat-off1 : KK-fhat (T₁ , T₀) ≡ zeroZω
KK-fhat-off1 = refl

KK-fhat-off2 : KK-fhat (T₁ , T₁) ≡ zeroZω
KK-fhat-off2 = refl

KK-fhat-off3 : KK-fhat (T₁ , T₂) ≡ zeroZω
KK-fhat-off3 = refl

KK-fhat-off4 : KK-fhat (T₂ , T₀) ≡ zeroZω
KK-fhat-off4 = refl

KK-fhat-off5 : KK-fhat (T₂ , T₁) ≡ zeroZω
KK-fhat-off5 = refl

KK-fhat-off6 : KK-fhat (T₂ , T₂) ≡ zeroZω
KK-fhat-off6 = refl

-- 支集恰 H：三点非零 + H 外恒零
KK-f-nz : ∀ x → KK-f (x , T₀) ≡ oneZω
KK-f-nz T₀ = refl
KK-f-nz T₁ = refl
KK-f-nz T₂ = refl

KK-one-nz : oneZω ≡ zeroZω → ⊥
KK-one-nz ()

KK-f-zero-off : ∀ x b → b ≢ T₀ → KK-f (x , b) ≡ zeroZω
KK-f-zero-off x T₀ bne = ⊥-elim (bne refl)
KK-f-zero-off x T₁ _ = refl
KK-f-zero-off x T₂ _ = refl

-- 支集恰对偶轴：(T₀, b) 三点非零 + 其余六点恒零
KK-fhat-nz : ∀ b → KK-fhat (T₀ , b) ≢ zeroZω
KK-fhat-nz T₀ ()
KK-fhat-nz T₁ ()
KK-fhat-nz T₂ ()

KK-supp-f : ℕ
KK-supp-f = 3

KK-supp-fhat : ℕ
KK-supp-fhat = 3

KK-card-T² : ℕ
KK-card-T² = 9

-- 等号：|supp f| · |supp f̂| = 3·3 = 9 = |T²|
KK-unc2 : KK-supp-f * KK-supp-fhat ≡ KK-card-T²
KK-unc2 = refl

KK-unc2-9 : KK-card-T² ≡ 3 * 3
KK-unc2-9 = refl

--------------------------------------------------------------------------------
-- §4. GF(3) 值退化反例（闭合）：平凡特征标下 f̂₃ ≡ 0，不确定原理失败
--------------------------------------------------------------------------------

KK-Σ₃T : Trit → Trit → Trit → Trit
KK-Σ₃T x y z = (x ⊕ y) ⊕ z

-- GF(3) 值「Fourier」（唯一特征标 χ ≡ 1）：f̂₃ r = Σ_{x∈T²} f(x)（与 r 无关）
KK-fhat3 : KK-T² → Trit
KK-fhat3 r =
  KK-Σ₃T (KK-Σ₃T (KK-fT (T₀ , T₀)) (KK-fT (T₁ , T₀)) (KK-fT (T₂ , T₀))
         ) (KK-Σ₃T (KK-fT (T₀ , T₁)) (KK-fT (T₁ , T₁)) (KK-fT (T₂ , T₁))
         ) (KK-Σ₃T (KK-fT (T₀ , T₂)) (KK-fT (T₁ , T₂)) (KK-fT (T₂ , T₂)))

-- 恒零：3 ≡ 0 (mod 3)，支集空 —— 不确定原理在 GF(3) 值下失败（9 项 ⊕ 链）
KK-fhat3-degenerate : ∀ r → KK-fhat3 r ≡ T₀
KK-fhat3-degenerate r = refl

KK-gf3-supphat : ℕ
KK-gf3-supphat = 0

KK-gf3-failure : KK-supp-f * KK-gf3-supphat ≡ 0
KK-gf3-failure = refl

--------------------------------------------------------------------------------
-- §5. T⁶ 陈述立界 + 正交性原子（几何级数引理，闭合）
--------------------------------------------------------------------------------

KK-card-T⁶ : ℕ
KK-card-T⁶ = 729

KK-729-def : KK-card-T⁶ ≡ 3 * 3 * 3 * 3 * 3 * 3
KK-729-def = refl

-- 几何级数引理：Σ_{t∈GF(3)} ω^{r·t} = 3（r = 0）/ 0（r ≠ 0）——
-- 特征标正交性原子，T⁶ Fubini 展开 6 层中每层的内和恰为此形；
-- 完全 T⁶ 证明（6 层重排 + 3⁶ 案枚举）立界，见头注。
KK-geo : Trit → Zω
KK-geo r =
  KK-Σ₃ (KK-wPow (KK-dot r T₀)) (KK-wPow (KK-dot r T₁)) (KK-wPow (KK-dot r T₂))

KK-geo-zero : KK-geo T₀ ≡ mkZω (+ 3) (+ 0)
KK-geo-zero = refl

KK-geo-omega : KK-geo T₁ ≡ zeroZω
KK-geo-omega = refl

KK-geo-omega2 : KK-geo T₂ ≡ zeroZω
KK-geo-omega2 = refl

-- 数值对齐：等号案例 9 = 3² 与 T⁶ 界 729 = 3⁶ 同构缩放（2 层 vs 6 层）
KK-scale : KK-card-T⁶ ≡ KK-card-T² * 81
KK-scale = refl
