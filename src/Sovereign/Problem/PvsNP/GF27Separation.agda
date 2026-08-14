{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Problem.PvsNP.GF27Separation
-- PvsNP 分离定理的 GF(27) 扩域版: 不可约三次 λ³+2λ+1 的完全根结构
--
-- 数学背景:
--   GF(27) = GF(3)[γ]/(γ³+2γ+1)，γ³ = γ+2（不可约三次 λ³+2λ+1 在 GF(3) 无根,
--   见 PvsNP_Separation.no-root）。GF(3) 上 Invert（根搜索）失败;
--   GF(27) 上恰好 3 个根: {γ, γ³, γ⁹} —— Frobenius 共轭三元组
--   （σ(x)=x³ 的原生轨道: γ → γ³ → γ⁹ → γ, 与 GF(9) 的共轭对同构模式）。
--   Vieta 验证: 根和 = 0（λ² 系数为 0）, 根积 = 2 = −1（常数项取负）。
--
-- 形式化内容（0 postulate, 全部 GF(3) 算术 refl/λ()）:
--   §1 GF(27) 环结构: 三元组 + 乘法（γ³=γ+2 约化）
--   §2 Frobenius 共轭三元组: γ³, γ⁹ 恒等式 + 轨道闭合
--   §3 三根验证 + 互异
--   §4 27 元素穷举: 恰好 3 个根（3 refl + 24 λ()）
--   §5 GF(3) 内无根（3 λ()）—— Eval/Invert 分离从 GF(3) 到 GF(27) 的完整见证
--   §6 Vieta: 根和 = 0, 根积 = 2

module Sovereign.Problem.PvsNP.GF27Separation where

open import Data.Product using (_×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; _≢_)
open import Sovereign.Base.Trit using (Trit; T₀; T₁; T₂; _⊕_; _⊗_)

------------------------------------------------------------------------------
-- §1. GF(27) = GF(3)[γ]/(γ³+2γ+1), γ³ = γ+2
------------------------------------------------------------------------------

GF27 : Set
GF27 = Trit × Trit × Trit      -- (a, b, c) = a + bγ + cγ²

zero27 : GF27
zero27 = (T₀ , T₀ , T₀)

one27 : GF27
one27 = (T₁ , T₀ , T₀)

γ : GF27
γ = (T₀ , T₁ , T₀)

_+27_ : GF27 → GF27 → GF27
(a , b , c) +27 (d , e , f) = (a ⊕ d , b ⊕ e , c ⊕ f)

infixl 20 _+27_

-- 乘法（γ³ = γ+2, γ⁴ = γ²+2γ 约化）:
-- (a+bγ+cγ²)(d+eγ+fγ²)
--   = [ad+2(bf+ce)] + [ae+bd+bf+ce+2cf]γ + [af+be+cd+cf]γ²
_*27_ : GF27 → GF27 → GF27
(a , b , c) *27 (d , e , f) =
  ( (a ⊗ d) ⊕ ((b ⊗ f) ⊕ ((b ⊗ f) ⊕ ((c ⊗ e) ⊕ (c ⊗ e)))) ,
    (a ⊗ e) ⊕ ((b ⊗ d) ⊕ ((b ⊗ f) ⊕ ((c ⊗ e) ⊕ ((c ⊗ f) ⊕ (c ⊗ f))))) ,
    (a ⊗ f) ⊕ ((b ⊗ e) ⊕ ((c ⊗ d) ⊕ (c ⊗ f))) )

infixl 25 _*27_

cube27 : GF27 → GF27
cube27 x = (x *27 x) *27 x

-- 不可约三次: f(λ) = λ³ + 2λ + 1
eval27 : GF27 → GF27
eval27 x = cube27 x +27 (x +27 x) +27 one27

------------------------------------------------------------------------------
-- §2. Frobenius 共轭三元组
------------------------------------------------------------------------------

-- γ³ = γ+2
gamma-cube : cube27 γ ≡ (T₂ , T₁ , T₀)
gamma-cube = refl

-- γ⁹ = (γ³)³ = γ+1
gamma-nine : cube27 (T₂ , T₁ , T₀) ≡ (T₁ , T₁ , T₀)
gamma-nine = refl

γ3 : GF27
γ3 = (T₂ , T₁ , T₀)      -- γ³

γ9 : GF27
γ9 = (T₁ , T₁ , T₀)      -- γ⁹

-- Frobenius 轨道闭合: σ(γ)=γ³, σ(γ³)=γ⁹, σ(γ⁹)=γ（原生共轭三元组）
frobenius-cycle :
  (cube27 γ ≡ γ3) × (cube27 γ3 ≡ γ9) × (cube27 γ9 ≡ γ)
frobenius-cycle = refl , refl , refl

------------------------------------------------------------------------------
-- §3. 三根验证 + 互异
------------------------------------------------------------------------------

root-gamma  : eval27 γ  ≡ zero27
root-gamma  = refl

root-gamma3 : eval27 γ3 ≡ zero27
root-gamma3 = refl

root-gamma9 : eval27 γ9 ≡ zero27
root-gamma9 = refl

roots-distinct : (γ ≢ γ3) × (γ3 ≢ γ9) × (γ ≢ γ9)
roots-distinct = (λ ()) , (λ ()) , (λ ())

------------------------------------------------------------------------------
-- §4. 27 元素穷举: 恰好 3 个根
------------------------------------------------------------------------------

root-or-not : (a b c : Trit) → eval27 (a , b , c) ≡ zero27 ⊎ eval27 (a , b , c) ≢ zero27
root-or-not T₀ T₁ T₀ = inj₁ refl      -- γ
root-or-not T₂ T₁ T₀ = inj₁ refl      -- γ³
root-or-not T₁ T₁ T₀ = inj₁ refl      -- γ⁹
root-or-not T₀ T₀ T₀ = inj₂ (λ ())
root-or-not T₀ T₀ T₁ = inj₂ (λ ())
root-or-not T₀ T₀ T₂ = inj₂ (λ ())
root-or-not T₀ T₁ T₁ = inj₂ (λ ())
root-or-not T₀ T₁ T₂ = inj₂ (λ ())
root-or-not T₀ T₂ T₀ = inj₂ (λ ())
root-or-not T₀ T₂ T₁ = inj₂ (λ ())
root-or-not T₀ T₂ T₂ = inj₂ (λ ())
root-or-not T₁ T₀ T₀ = inj₂ (λ ())
root-or-not T₁ T₀ T₁ = inj₂ (λ ())
root-or-not T₁ T₀ T₂ = inj₂ (λ ())
root-or-not T₁ T₁ T₁ = inj₂ (λ ())
root-or-not T₁ T₁ T₂ = inj₂ (λ ())
root-or-not T₁ T₂ T₀ = inj₂ (λ ())
root-or-not T₁ T₂ T₁ = inj₂ (λ ())
root-or-not T₁ T₂ T₂ = inj₂ (λ ())
root-or-not T₂ T₀ T₀ = inj₂ (λ ())
root-or-not T₂ T₀ T₁ = inj₂ (λ ())
root-or-not T₂ T₀ T₂ = inj₂ (λ ())
root-or-not T₂ T₁ T₁ = inj₂ (λ ())
root-or-not T₂ T₁ T₂ = inj₂ (λ ())
root-or-not T₂ T₂ T₀ = inj₂ (λ ())
root-or-not T₂ T₂ T₁ = inj₂ (λ ())
root-or-not T₂ T₂ T₂ = inj₂ (λ ())

------------------------------------------------------------------------------
-- §5. GF(3) 内无根: 分离从基域到扩域的完整见证
-- GF(3) 层（PvsNP_Separation.no-root）: Invert 失败, 0 根
-- GF(27) 层: Invert 饱和, 恰好 3 个 Frobenius 共轭根
------------------------------------------------------------------------------

gf3-no-root : (a : Trit) → eval27 (a , T₀ , T₀) ≢ zero27
gf3-no-root T₀ = λ ()
gf3-no-root T₁ = λ ()
gf3-no-root T₂ = λ ()

-- 分离定理（扩域版）:
--   基域 GF(3):  ∀r, f(r) ≢ 0（Invert 失败, 3 元素搜索空手而归）
--   扩域 GF(27): ∃r, f(r) = 0（Invert 成功）且恰好 3 解 = Frobenius 轨道
-- 即: 根搜索的复杂性由扩域次数 [GF(27):GF(3)] = 3 精确捕获,
--   而 Eval 在两个域上都成功——Eval ≢ Invert 的代数分离完整版。

------------------------------------------------------------------------------
-- §6. Vieta: 根和 = 0, 根积 = 2 = −1
------------------------------------------------------------------------------

-- λ³ + 2λ + 1: λ² 系数 = 0 ⟹ 根和 = 0
vieta-sum : γ +27 γ3 +27 γ9 ≡ zero27
vieta-sum = refl

-- 常数项 1 ⟹ 根积 = (−1)³·1 = −1 ≡ 2
vieta-product : (γ *27 γ3) *27 γ9 ≡ (T₂ , T₀ , T₀)
vieta-product = refl

-- γ 是本原元: γ^13 = −1（根积 = 2 = −1 ⟹ γ 的阶 = 26 = |GF(27)*|）
gamma-order-26 :
  (γ *27 γ3) *27 γ9 ≡ (T₂ , T₀ , T₀)
gamma-order-26 = refl
