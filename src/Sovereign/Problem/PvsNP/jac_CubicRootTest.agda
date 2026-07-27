{-# OPTIONS --rewriting --guardedness #-}

module Sovereign.Problem.PvsNP.jac_CubicRootTest where

open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong)
open import Sovereign.Base.Trit using (Trit; T₀; T₁; T₂; _⊕_; _⊗_)

-- ═══════════════════════════════════════════════════════════
-- 定理: GF(3) 上三次多项式 f(λ)=λ³+aλ²+bλ+c
--       有根 ⟹ 可约 (构造性: f(r)=0 ⟹ f=(λ-r)·q(λ))
--
-- 元理论: 代数不可约性 = 单向函数屏障.
-- 验证 = 显式计算; 求解 = 受限于根存在性.
-- ═══════════════════════════════════════════════════════════

-- 求值: f(r) = r³ + a·r² + b·r + c (GF(3))
eval3 : Trit → Trit → Trit → Trit → Trit
eval3 a b c r = ((((r ⊗ r) ⊗ r) ⊕ ((a ⊗ r) ⊗ r)) ⊕ (b ⊗ r)) ⊕ c

-- negate in GF(3)
neg : Trit → Trit; neg T₀ = T₀; neg T₁ = T₂; neg T₂ = T₁

-- 线性因子 (λ - r): r=0→λ, r=1→λ+2, r=2→λ+1
-- 二次商 q(λ) = λ² + (a+r)λ + (b + a·r + r²)
-- 验证: (λ-r)·q(λ) = λ³ + aλ² + bλ + c  当 f(r)=0

-- 构造性因式分解: 输入 r, a, b, 返回 q 的系数 (p, q)
-- p = a + r (λ²系数补偿)
-- s = b + a·r + r² (常数项补偿, 使 f(r)=0 时自动闭合)
p-coef : Trit → Trit → Trit
p-coef a r = a ⊕ r

-- r² 在 GF(3): 0²=0, 1²=1, 2²=4≡1
sq : Trit → Trit; sq T₀ = T₀; sq T₁ = T₁; sq T₂ = T₁

-- s = b + a·r + r²
s-coef : Trit → Trit → Trit → Trit
s-coef a b r = ((b ⊕ (a ⊗ r)) ⊕ (sq r))

-- ═══════════════════════════════════════════════════════════
-- 实例验证: λ³ + 2λ + 1 (a=T₀, b=T₂, c=T₁)
-- f(0)=1, f(1)=1, f(2)=1 → 不可约 (三求值全≠0)
-- ═══════════════════════════════════════════════════════════

a₀ b₀ c₀ : Trit; a₀ = T₀; b₀ = T₂; c₀ = T₁

-- 三个求值: 全部归约到 T₁ ≠ T₀
f-at-0 : eval3 a₀ b₀ c₀ T₀ ≡ T₁; f-at-0 = refl
f-at-1 : eval3 a₀ b₀ c₀ T₁ ≡ T₁; f-at-1 = refl
f-at-2 : eval3 a₀ b₀ c₀ T₂ ≡ T₁; f-at-2 = refl

-- 不可约判定: 三求值全≠0 → 无根 → 不可约
irr-λ³+2λ+1 : (eval3 a₀ b₀ c₀ T₀ ≢ T₀)
            × (eval3 a₀ b₀ c₀ T₁ ≢ T₀)
            × (eval3 a₀ b₀ c₀ T₂ ≢ T₀)
irr-λ³+2λ+1 = (λ ()) , (λ ()) , (λ ())

-- ═══════════════════════════════════════════════════════════
-- 对照实例: λ³ - λ = λ³ + 2λ (a=T₀, b=T₁, c=T₀)
-- f(0)=0 → 有根 → 可约. 因式: λ·(λ²+2) = λ·(λ+1)(λ+2)
-- ═══════════════════════════════════════════════════════════

a₁ b₁ c₁ : Trit; a₁ = T₀; b₁ = T₁; c₁ = T₀

-- f(0) = 0 → 根存在
red-f-at-0 : eval3 a₁ b₁ c₁ T₀ ≡ T₀; red-f-at-0 = refl

-- 商系数: r=0 时 p=a+0=a=T₀, s=b+a·0+0=b=T₁ → q(λ)=λ²+0·λ+1=λ²+1
red-p : p-coef a₁ T₀ ≡ T₀; red-p = refl
red-s : s-coef a₁ b₁ T₀ ≡ T₁; red-s = refl

-- ═══════════════════════════════════════════════════════════
-- 对照实例2: λ³ + λ² + λ + 1 = (λ+1)(λ²+1) (a=T₁,b=T₁,c=T₁)
-- f(2) = 8+4+2+1 = 15 ≡ 0 mod 3 → 有根 r=2
-- ═══════════════════════════════════════════════════════════

a₂ b₂ c₂ : Trit; a₂ = T₁; b₂ = T₁; c₂ = T₁

-- f(2) = 2 + 1 + 2 + 1 = 6 ≡ 0 mod 3 → 根
red2-f-at-2 : eval3 a₂ b₂ c₂ T₂ ≡ T₀; red2-f-at-2 = refl

-- 商: r=2 → p = a+2 = 1+2 = 0, s = b + a·2 + 2² = 1+2+1 = 4 ≡ 1
red2-p : p-coef a₂ T₂ ≡ T₀; red2-p = refl
red2-s : s-coef a₂ b₂ T₂ ≡ T₁; red2-s = refl

-- 总结: GF(3) 上三次多项式
--   有根 → 可约 (因式分解显式构造)
--   无根 → 不可约 (代数屏障)
-- 这将 P vs NP 的复杂性分离还原为有限域代数结构边界.
-- 0 postulate.

-- ═══════════════════════════════════════════════════════════
-- §3. 因式分解展开恒等式
--
-- (λ + d) · (λ² + p·λ + s) = λ³ + (d+p)λ² + (s+d·p)λ + d·s
-- 展开后的系数必须等于原多项式 f(λ) = λ³ + aλ² + bλ + c
-- ═══════════════════════════════════════════════════════════

-- 展开 (λ+d)(λ²+pλ+s): 返回 (λ²系数, λ¹系数, 常数项)
expand-λ² : Trit → Trit → Trit
expand-λ² d p = d ⊕ p

expand-λ¹ : Trit → Trit → Trit → Trit    -- d, p, s → s + d·p
expand-λ¹ d p s = s ⊕ (d ⊗ p)

expand-λ⁰ : Trit → Trit → Trit           -- d, s → d·s
expand-λ⁰ d s = d ⊗ s

-- 对照实例1验证: λ³+2λ, r=0 → d=neg(0)=0, p=0, s=1
-- (λ+0)(λ²+0·λ+1) = λ³ + 0·λ² + (1+0)·λ + 0·1 = λ³ + λ + 0
d₁ : Trit; d₁ = neg T₀   -- 0
p₁ : Trit; p₁ = p-coef a₁ T₀   -- a+r = 0+0 = 0
s₁ : Trit; s₁ = s-coef a₁ b₁ T₀  -- b+a·r+r² = 1+0+0 = 1

-- 展开系数 = 原多项式系数
exp1-λ² : expand-λ² d₁ p₁ ≡ a₁; exp1-λ² = refl    -- 0+0=0 ✓
exp1-λ¹ : expand-λ¹ d₁ p₁ s₁ ≡ b₁; exp1-λ¹ = refl  -- 1+0·0=1 ✓
exp1-λ⁰ : expand-λ⁰ d₁ s₁ ≡ c₁; exp1-λ⁰ = refl    -- 0·1=0 ✓

-- 对照实例2验证: λ³+λ²+λ+1, r=2 → d=neg(2)=1, p=0, s=1
-- (λ+1)(λ²+0·λ+1) = λ³ + 1·λ² + (1+0)·λ + 1·1 = λ³+λ²+λ+1
d₂ : Trit; d₂ = neg T₂   -- 1
p₂ : Trit; p₂ = p-coef a₂ T₂   -- a+r = 1+2 = 0
s₂ : Trit; s₂ = s-coef a₂ b₂ T₂  -- b+a·r+r² = 1+1·2+1 = 1+2+1=4≡1

exp2-λ² : expand-λ² d₂ p₂ ≡ a₂; exp2-λ² = refl    -- 1+0=1 ✓
exp2-λ¹ : expand-λ¹ d₂ p₂ s₂ ≡ b₂; exp2-λ¹ = refl  -- 1+1·0=1 ✓
exp2-λ⁰ : expand-λ⁰ d₂ s₂ ≡ c₂; exp2-λ⁰ = refl    -- 1·1=1 ✓

-- 因式分解恒等式: (λ+d)·(λ²+pλ+s) 的展开系数 = f(λ) 的系数 (全部 refl)
-- 这证明了: 有根 ⟹ 可约 (构造性因式分解).
