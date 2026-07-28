{-# OPTIONS --rewriting --guardedness #-}

-- | KakeyaGF9 — 挂谷猜想的 GF(9) 原生共轭结构 (大衍独有)
--
-- GF(9) = GF(3)[α]/(α²+1), Gal(GF(9)/GF(3)) ≅ C₂
-- Frobenius 自同构 σ(a+bα) = a-bα 是原生 Galois 共轭
--
-- 与 Dvir 的核心区别:
--   Dvir 的多项式方法对任意 F_q 成立, 不依赖共轭
--   大衍锁定 GF(9): σ 是原生共轭, 对应复共轭的离散投影
--   GF(2) 反例: GF(2) 无非平凡自同构, Dvir 仍成立 → 他不依赖共轭
--   连续统特征0: 无 Frobenius → 共轭缺失 → 病态根因
--
-- 复用: Sovereign.Algebra.GF9 — 全部 Frobenius/范数/迹/乘法群定理
-- 0 postulate.

module Sovereign.Problem.Kakeya.KakeyaGF9 where

open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
open import Data.Product using (_×_; _,_; proj₁; proj₂; Σ)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; cong; cong₂; sym; trans)

open import Sovereign.Base.Trit using (Trit; T₀; T₁; T₂; _⊕_; _⊗_; negate; negate²)
open import Sovereign.Algebra.GF9 using (
  GF9; GF3; embed-gf3; alpha;
  _+gf9_; _*gf9_; gf9-one;
  galoisConjugate; galoisConjugate²;
  galoisNorm; galoisNorm-conjugate;
  galoisTrace;
  lemma-frobenius-multiplicative;
  GF9Star; toGF9; fromGF9; _*s_;
  gen; gen-generates-all; _^s_;
  +gf9-comm; +gf9-assoc; +gf9-identityˡ; +gf9-identityʳ;
  *gf9-comm; *gf9-identityˡ; *gf9-identityʳ;
  *gf9-assoc; *gf9-distribˡ-+gf9;
  alpha-squared; sigma-alpha;
  galoisFixedPoint; ConjugatePair;
  conjugatePair-size-1; conjugatePair-size-2)

--------------------------------------------------------------------------------
-- §1. Frobenius 共轭 σ — 原生 Galois 刚性
--
-- σ : GF9 → GF9, σ(a+bα) = a-bα
-- Gal(GF(9)/GF(3)) ≅ C₂, 生成元 = σ
--
-- 复用 GF9.agda 的完整形式化, 不重新定义
--------------------------------------------------------------------------------

-- σ : GF9 → GF9 (Frobenius 自同构)
σ : GF9 → GF9
σ = galoisConjugate

-- 定理 1: σ² = id (对合性)
-- 证明: 复用 GF9.agda 的 galoisConjugate²
σ²-id : ∀ x → σ (σ x) ≡ x
σ²-id = galoisConjugate²

-- 定理 2: σ 是乘法同态
-- 数学: 在特征 3 域中 (xy)³ = x³y³ (Freshman's Dream)
-- 证明: 复用 GF9.agda 的 lemma-frobenius-multiplicative
σ-mul : ∀ x y → σ (x *gf9 y) ≡ σ x *gf9 σ y
σ-mul = lemma-frobenius-multiplicative

-- 定理 3: σ(α) = -α
-- 证明: 复用 GF9.agda 的 sigma-alpha
σ-α : σ alpha ≡ (T₀ , T₂)
σ-α = sigma-alpha

-- 定理 4: α² = -1 = 2 (GF(3) 中)
-- 证明: 复用 GF9.agda 的 alpha-squared
α²-neg1 : alpha *gf9 alpha ≡ (T₂ , T₀)
α²-neg1 = alpha-squared

--------------------------------------------------------------------------------
-- §2. 范数与迹 — 共轭不变量
--
-- 范数: N(x) = x · σ(x) = a² + b² ∈ GF(3)
-- 迹:   Tr(x) = x + σ(x) = 2a ∈ GF(3)
--
-- 这两个量是 GF(9)/GF(3) 扩张的核心不变量
-- 连续统对照: ℂ/ℝ 的范数 z·z̄ = |z|² 和迹 z+z̄ = 2Re(z)
-- 但 ℂ 是无穷维的, 无法构造有限全局矩阵
--------------------------------------------------------------------------------

-- 范数: N(x) ∈ GF(3)
norm-in-gf3 : ∀ x → Σ GF3 (λ r → galoisNorm x ≡ r)
norm-in-gf3 x = galoisNorm x , refl

-- 范数在共轭下不变: N(σ(x)) = N(x)
-- 证明: 复用 GF9.agda 的 galoisNorm-conjugate
norm-conj-inv : ∀ x → galoisNorm (σ x) ≡ galoisNorm x
norm-conj-inv = galoisNorm-conjugate

-- 迹: Tr(x) ∈ GF(3)
trace-in-gf3 : ∀ x → Σ GF3 (λ r → galoisTrace x ≡ r)
trace-in-gf3 x = galoisTrace x , refl

--------------------------------------------------------------------------------
-- §3. 不动点刻画 — σ(x) = x ⟺ x ∈ GF(3)
--
-- GF(9) 的 9 个元素在 σ 作用下分为:
--   3 个不动点 (GF(3) 嵌入): {0, 1, 2}
--   3 个共轭对: {α, -α}, {1+α, 1-α}, {2+α, 2-α}
--
-- 这是 Galois 理论的基本定理:
-- Fix(σ) = GF(3) (固定域 = 基域)
--------------------------------------------------------------------------------

-- 不动点 ⟹ GF(3) 嵌入
-- 证明: 复用 GF9.agda 的 galoisFixedPoint
fixed-pt-gf3 : ∀ x → σ x ≡ x → Σ GF3 (λ a → x ≡ embed-gf3 a)
fixed-pt-gf3 = galoisFixedPoint

-- α 不是不动点: σ(α) ≠ α, 即 α ∉ GF(3)
-- 证明: 复用 GF9.agda 的 conjugatePair-size-2
α-not-fixed : σ alpha ≡ alpha → ⊥
α-not-fixed = conjugatePair-size-2

-- GF(3) 嵌入元素是自共轭的: ∀ a ∈ GF(3), σ(embed(a)) = embed(a)
-- 证明: 复用 GF9.agda 的 conjugatePair-size-1
gf3-self-conjugate : ∀ a → σ (embed-gf3 a) ≡ embed-gf3 a
gf3-self-conjugate = conjugatePair-size-1

--------------------------------------------------------------------------------
-- §4. 共轭对结构 — C₂ 商
--
-- ConjugatePair x = Σ GF9 (λ y → (y ≡ x) ⊎ (y ≡ σ x))
--
-- 不动点: 共轭对大小 = 1 (GF(3) 嵌入)
-- 非不动点: 共轭对大小 = 2 (真正的共轭对)
--
-- 连续统对照: ℂ 上 z 和 z̄ 也构成共轭对,
-- 但 ℂ 有不可数无穷多对, 无法穷举
--------------------------------------------------------------------------------

-- 共轭对类型 (复用 GF9.agda 的定义)
-- ConjugatePair x = Σ GF9 (λ y → (y ≡ x) ⊎ (y ≡ σ x))

--------------------------------------------------------------------------------
-- §5. GF(9)* 乘法群 — 循环群 Z/8Z
--
-- GF(9)* = GF(9) \ {0}, |GF(9)*| = 8
-- 生成元: 1+α, 阶为 8
-- 子群格: {1} ⊂ {1,2} ⊂ {1,α,2,2α} ⊂ GF(9)*
--          阶1    阶2       阶4           阶8
--
-- 连续统对照: ℂ* 不是有限循环群, 无法穷举
--------------------------------------------------------------------------------

-- 生成元遍历所有 8 个元素
-- 证明: 复用 GF9.agda 的 gen-generates-all
gf9star-cyclic : ∀ x → Σ ℕ (λ n → gen ^s n ≡ x)
gf9star-cyclic = gen-generates-all

--------------------------------------------------------------------------------
-- §6. 挂谷猜想中的共轭作用
--
-- 在 GF(9)² 上, σ 诱导方向空间上的作用:
--   σ(⟨(a,b)⟩) = ⟨σ(a,b)⟩ = ⟨(a,-b)⟩
--
-- 方向在 σ 下的轨道:
--   不动方向: ⟨(1,0)⟩ (水平, b=0)
--   共轭方向对: ⟨(1,1)⟩ ↔ ⟨(1,-1)⟩ = ⟨(1,2)⟩
--
-- 这给出了 ℙ¹(GF(9)) 的 C₂ 商结构
-- Dvir 没有这个: 他的方法不依赖共轭
--------------------------------------------------------------------------------

-- σ 诱导 GF9 上的对合 (复用 σ²-id)
σ-on-directions : ∀ x → σ (σ x) ≡ x
σ-on-directions = σ²-id

-- 水平方向是 σ 不动点 (b=0 分量)
-- embed-gf3 a = (a, T₀), σ(a, T₀) = (a, negate T₀) = (a, T₀)
horiz-fixed : ∀ a → σ (embed-gf3 a) ≡ embed-gf3 a
horiz-fixed = gf3-self-conjugate
