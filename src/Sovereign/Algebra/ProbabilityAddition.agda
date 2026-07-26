{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Algebra.ProbabilityAddition
-- 一般概率加法公式: |A∪B| + |A∩B| = |A| + |B|
--
-- 对任意有限集 Fin N, 子集表示为 Fin N → Bool.
-- 基数 card(A) = Σ_{i∈Fin N} (if A(i) then 1 else 0).
--
-- 核心定理:
--   §1. 子集基数定义 + 基本性质
--   §2. 并集、交集、差集
--   §3. 一般加法公式 (容斥原理 N=2):
--       ∀ A B ⊆ Fin N, card(A∪B) + card(A∩B) = card(A) + card(B)
--   §4. T⁶ 实例: N=729, 验证 prob(A∪B) = ...
--
-- 证明策略:
--   逐点贡献分析 — 对每个 i ∈ Fin N, 分 4 种布尔组合:
--     (A=T, B=T): 对 |A∪B|+|A∩B| 贡献 1+1=2, 对 |A|+|B| 贡献 1+1=2
--     (A=T, B=F): 对 |A∪B|+|A∩B| 贡献 1+0=1, 对 |A|+|B| 贡献 1+0=1
--     (A=F, B=T): 对 |A∪B|+|A∩B| 贡献 1+0=1, 对 |A|+|B| 贡献 0+1=1
--     (A=F, B=F): 对 |A∪B|+|A∩B| 贡献 0+0=0, 对 |A|+|B| 贡献 0+0=0
--   每种情况贡献相等, 求和即得.
--
--   形式化: Bool→ℕ 指示函数 + 逐点恒等 + 有限和分配律.
--
-- 0 postulate.

module Sovereign.Algebra.ProbabilityAddition where

open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _≤_; z≤n; s≤s)
open import Data.Nat.Properties using (+-comm; +-assoc; +-identityʳ; +-identityˡ)
open import Data.Fin using (Fin; zero; suc)
open import Data.Bool using (Bool; true; false; not)
  renaming (_∧_ to _&&_; _∨_ to _||_)
open import Data.Bool.Properties using (∨-comm; ∧-comm)
open import Data.Product using (_×_; _,_; Σ; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; cong; cong₂; sym; trans; module ≡-Reasoning)

------------------------------------------------------------------------------
-- §1. 子集基数定义
--
-- 子集 A ⊆ Fin N 表示为 Fin N → Bool.
-- 基数 card(A) = Σ_{i=0}^{N-1} bool→ℕ(A(i)).
------------------------------------------------------------------------------

-- Bool → ℕ 指示函数
bool→ℕ : Bool → ℕ
bool→ℕ true  = 1
bool→ℕ false = 0

-- bool→ℕ 的加法保持性 (关键引理)
-- bool→ℕ(a ∨ b) + bool→ℕ(a ∧ b) = bool→ℕ(a) + bool→ℕ(b)
-- 这是加法公式在单元素层面的本质
bool→ℕ-∨-∧-identity : ∀ (a b : Bool) →
  (bool→ℕ (a || b) + bool→ℕ (a && b)) ≡ (bool→ℕ a + bool→ℕ b)
bool→ℕ-∨-∧-identity true  true  = refl  -- 1+1 = 1+1
bool→ℕ-∨-∧-identity true  false = refl  -- 1+0 = 1+0
bool→ℕ-∨-∧-identity false true  = refl  -- 1+0 = 0+1
bool→ℕ-∨-∧-identity false false = refl  -- 0+0 = 0+0

-- 子集类型
Subset : ℕ → Set
Subset N = Fin N → Bool

-- 基数: 对所有 Fin N 元素求和 bool→ℕ
card : ∀ {N : ℕ} → Subset N → ℕ
card {zero}  A = 0
card {suc N} A = bool→ℕ (A zero) + card (λ i → A (suc i))

------------------------------------------------------------------------------
-- §2. 并集、交集
------------------------------------------------------------------------------

-- 并集: (A ∪ B)(i) = A(i) ∨ B(i)
_∪_ : ∀ {N : ℕ} → Subset N → Subset N → Subset N
(A ∪ B) i = A i || B i

-- 交集: (A ∩ B)(i) = A(i) ∧ B(i)
_∩_ : ∀ {N : ℕ} → Subset N → Subset N → Subset N
(A ∩ B) i = A i && B i

-- 补集: (Aᶜ)(i) = ¬A(i)
complement : ∀ {N : ℕ} → Subset N → Subset N
complement A i = not (A i)

-- 空集
∅ : ∀ {N : ℕ} → Subset N
∅ _ = false

-- 全集
universe : ∀ {N : ℕ} → Subset N
universe _ = true

------------------------------------------------------------------------------
-- §3. 一般加法公式 (容斥原理 N=2)
--
-- ∀ A B ⊆ Fin N,
--   card(A ∪ B) + card(A ∩ B) = card(A) + card(B)
------------------------------------------------------------------------------

-- 四项重排: (a+b) + (c+d) = (a+c) + (b+d)
+-rearrange : (a b c d : ℕ) →
  (a + b) + (c + d) ≡ (a + c) + (b + d)
+-rearrange a b c d = begin
  (a + b) + (c + d)     ≡⟨ +-assoc a b (c + d) ⟩
  a + (b + (c + d))     ≡⟨ cong (a +_) (sym (+-assoc b c d)) ⟩
  a + ((b + c) + d)     ≡⟨ cong (λ x → a + (x + d)) (+-comm b c) ⟩
  a + ((c + b) + d)     ≡⟨ cong (a +_) (+-assoc c b d) ⟩
  a + (c + (b + d))     ≡⟨ sym (+-assoc a c (b + d)) ⟩
  (a + c) + (b + d)     ∎
  where open ≡-Reasoning

-- 主定理: 容斥原理 (一般加法公式)
-- ∀ A B ⊆ Fin N, card(A∪B) + card(A∩B) = card(A) + card(B)
-- 证明: 对 N 归纳
--   N=0: 0+0 = 0+0 (refl)
--   N→N+1: 单元素恒等式 + 归纳假设 + 四项重排
inclusion-exclusion : ∀ {N : ℕ} (A B : Subset N) →
  card (A ∪ B) + card (A ∩ B) ≡ card A + card B
inclusion-exclusion {zero}  A B = refl  -- 0+0 = 0+0
inclusion-exclusion {suc N} A B = begin
  -- 起始: card(A∪B) + card(A∩B)
  -- 展开 card {suc N} = bool→ℕ(head) + card(tail)
  card (A ∪ B) + card (A ∩ B)
    -- 步骤 0: 展开 card 定义
    -- card(A∪B) = bool→ℕ(A₀∨B₀) + card(尾∪)
    -- card(A∩B) = bool→ℕ(A₀∧B₀) + card(尾∩)
    -- 所以 LHS = (bool→ℕ(∨) + card(尾∪)) + (bool→ℕ(∧) + card(尾∩))
    -- 需要重排为 bool→ℕ(∨) + (bool→ℕ(∧) + (card(尾∪) + card(尾∩)))
    ≡⟨ +-rearrange (bool→ℕ (A zero || B zero)) (card (λ i → (A ∪ B) (suc i)))
                   (bool→ℕ (A zero && B zero)) (card (λ i → (A ∩ B) (suc i))) ⟩
  -- 现在: (bool→ℕ(∨) + bool→ℕ(∧)) + (card(尾∪) + card(尾∩))
  (bool→ℕ (A zero || B zero) + bool→ℕ (A zero && B zero))
  + (card (λ i → (A ∪ B) (suc i)) + card (λ i → (A ∩ B) (suc i)))
    -- 步骤 1: 单元素恒等式合并前两项
    ≡⟨ cong (λ x → x + (card (λ i → (A ∪ B) (suc i)) + card (λ i → (A ∩ B) (suc i))))
            (bool→ℕ-∨-∧-identity (A zero) (B zero)) ⟩
  (bool→ℕ (A zero) + bool→ℕ (B zero))
  + (card (λ i → (A ∪ B) (suc i)) + card (λ i → (A ∩ B) (suc i)))
    -- 步骤 2: 归纳假设
    ≡⟨ cong (λ x → (bool→ℕ (A zero) + bool→ℕ (B zero)) + x)
            (inclusion-exclusion {N} (λ i → A (suc i)) (λ i → B (suc i))) ⟩
  (bool→ℕ (A zero) + bool→ℕ (B zero))
  + (card (λ i → A (suc i)) + card (λ i → B (suc i)))
    -- 步骤 3: 四项重排回 (A₀ + card(A尾)) + (B₀ + card(B尾))
    ≡⟨ +-rearrange (bool→ℕ (A zero)) (bool→ℕ (B zero))
                   (card (λ i → A (suc i))) (card (λ i → B (suc i))) ⟩
  (bool→ℕ (A zero) + card (λ i → A (suc i)))
  + (bool→ℕ (B zero) + card (λ i → B (suc i)))
    -- = card(A) + card(B) (by definition of card {suc N})
    ∎
  where open ≡-Reasoning

------------------------------------------------------------------------------
-- §4. 概率版本
--
-- 在 T⁶ = Fin 729 上, 概率 P(A) = card(A) / 729.
-- 加法公式 P(A∪B) = P(A) + P(B) - P(A∩B) 是上述整数版本的除法包装.
-- 由于 GF(3) 框架中除法不是原生操作, 我们保持整数形式.
------------------------------------------------------------------------------

-- T⁶ 样本空间大小
T⁶-size : ℕ
T⁶-size = 729

-- 加法公式在 T⁶ 上的表述 (整数版):
-- card(A∪B) + card(A∩B) = card(A) + card(B)
-- 两边除以 729 即得 P(A∪B) + P(A∩B) = P(A) + P(B)
-- 等价地: P(A∪B) = P(A) + P(B) - P(A∩B)
--
-- 定理已证: inclusion-exclusion {729} A B

------------------------------------------------------------------------------
-- §5. 离散独特性
--
-- 连续版本: P(A∪B) = P(A) + P(B) - P(A∩B)
--   依赖 Lebesgue 测度的可加性.
--
-- 离散版本: card(A∪B) + card(A∩B) = card(A) + card(B)
--   依赖有限集的逐点贡献分析, 无测度论.
--
-- 关键差异:
--   连续: 需要 σ-代数, 可数可加性, Carathéodory 扩张定理
--   离散: 只需要 4-case 布尔穷举 (true/false × true/false)
--
--   连续加法公式的证明依赖 Lebesgue 测度的构造性 (~100 页实分析)
--   离散加法公式的证明是 4-case refl + ℕ 归纳 (~40 行 Agda)
------------------------------------------------------------------------------

------------------------------------------------------------------------------
-- §6. 具体实例验证 (与 ProbThermo.agda 的数值实例对齐)
--
-- 例: A = {0, 1}, B = {1, 2} 在 Fin 3 上
--   A∪B = {0, 1, 2}, A∩B = {1}
--   card(A∪B) + card(A∩B) = 3 + 1 = 4
--   card(A) + card(B) = 2 + 2 = 4 ✓
------------------------------------------------------------------------------

-- 具体子集: A = {0, 1}, B = {1, 2}
A-ex : Subset 3
A-ex zero    = true   -- 0 ∈ A
A-ex (suc zero)  = true   -- 1 ∈ A
A-ex (suc (suc zero)) = false  -- 2 ∉ A

B-ex : Subset 3
B-ex zero    = false  -- 0 ∉ B
B-ex (suc zero)  = true   -- 1 ∈ B
B-ex (suc (suc zero)) = true   -- 2 ∈ B

-- card(A) = 2, card(B) = 2
card-A-ex : card A-ex ≡ 2
card-A-ex = refl

card-B-ex : card B-ex ≡ 2
card-B-ex = refl

-- card(A∪B) = 3, card(A∩B) = 1
card-A∪B-ex : card (A-ex ∪ B-ex) ≡ 3
card-A∪B-ex = refl

card-A∩B-ex : card (A-ex ∩ B-ex) ≡ 1
card-A∩B-ex = refl

-- 加法公式验证: 3 + 1 = 2 + 2 = 4
addition-formula-ex : (card (A-ex ∪ B-ex) + card (A-ex ∩ B-ex)) ≡ 4
addition-formula-ex = refl

-- 等价地: card(A) + card(B) = 4
addition-formula-ex' : (card A-ex + card B-ex) ≡ 4
addition-formula-ex' = refl

------------------------------------------------------------------------------
-- §7. 总结
--
-- 定理: inclusion-exclusion — 对任意 N, 任意 A B ⊆ Fin N,
--   card(A∪B) + card(A∩B) ≡ card(A) + card(B)
--
-- 证明: 对 N 归纳 + 4-case bool→ℕ-∨-∧-identity
--
-- 全部 0 postulate, 构造性证明.
-- 证明长度: ~100 行 Agda (vs 连续版本 ~100 页实分析)
------------------------------------------------------------------------------
