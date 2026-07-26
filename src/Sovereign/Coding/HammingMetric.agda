{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Coding.HammingMetric
-- Hamming 距离的构造性形式化——编码理论度量公理的 0-postulate 证明
--
-- 核心原则:
--   1. 字 = 有限子集, 载体 Fin N → Bool (与 ProbabilityAddition.Subset 同构)
--   2. 距离 = 逐点不等性的计数, d(x,y) = Σ bool→ℕ(xᵢ xor yᵢ)
--   3. 穷举法证点态引理 (策略 A), 代数链 + N 归纳组装全局定理 (策略 B)
--   4. 0 postulate — 全部构造性 refl/≤-trans/s≤s
--
-- 包含:
--   §1. 基础设施: bool→ℕ / Subset / card / δ(逐点距离) / hamming(全局距离)
--   §2. 同一性:   d(x,y)≡0 → x≡y
--   §3. 对称性:   d(x,y)≡d(y,x)
--   §4. 三角不等式: d(x,z) ≤ d(x,y)+d(y,z)   ⭐ 度量公理核心
--   §5. 非负性 + 具体实例 (Fin 3)
--   §6. 离散独特性
--
-- 0 postulate.

module Sovereign.Coding.HammingMetric where

open import Data.Nat using (ℕ; zero; suc; _+_; _≤_; z≤n; s≤s)
open import Data.Nat.Properties using (+-comm; +-assoc; +-identityʳ; ≤-refl; ≤-trans; +-mono-≤; m≤n⇒m≤1+n; m+n≡0⇒m≡0; m+n≡0⇒n≡0)
open import Data.Fin using (Fin; zero; suc)
open import Data.Bool using (Bool; true; false; not; _xor_; _∨_; _∧_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; cong; cong₂; sym; trans; module ≡-Reasoning)

------------------------------------------------------------------------------
-- §1. 基础设施
--
-- bool→ℕ / Subset / card 与 ProbabilityAddition.agda 同构 (自包含, 避免反向范畴依赖).
-- 逐点距离 δ(a,b) = bool→ℕ(a xor b): 相异记 1, 相同记 0.
------------------------------------------------------------------------------

-- Bool → ℕ 指示函数
bool→ℕ : Bool → ℕ
bool→ℕ true  = 1
bool→ℕ false = 0

-- 字类型 = 长度 N 的二元字, 即 Fin N → Bool
Word : ℕ → Set
Word N = Fin N → Bool

-- 基数 (逐点求和), 与 P3 card 同构
card : ∀ {N : ℕ} → Word N → ℕ
card {zero}  w = 0
card {suc N} w = bool→ℕ (w zero) + card (λ i → w (suc i))

-- 逐点距离函数: x xor y 的逐点版本
pointwise-xor : ∀ {N : ℕ} → Word N → Word N → Word N
pointwise-xor x y i = x i xor y i

-- Hamming 距离: 相异位置的个数
hamming : ∀ {N : ℕ} → Word N → Word N → ℕ
hamming {N} x y = card (pointwise-xor x y)

-- 逐点距离 δ (单点 hamming)
δ : Bool → Bool → ℕ
δ a b = bool→ℕ (a xor b)

------------------------------------------------------------------------------
-- §2. δ 的基本性质 (点态引理, 策略 A 穷举)
--
-- 这些是全局定理的"原子", 全部 2×2=4 case refl.
------------------------------------------------------------------------------

-- δ 的同一性: δ(a,b)=0 → a≡b
-- 穷举: a≡b 时 xor=false→0; a≢b 时 xor=true→1≠0
δ≡0⇒≡ : ∀ (a b : Bool) → δ a b ≡ zero → a ≡ b
δ≡0⇒≡ true  true  _  = refl
δ≡0⇒≡ true  false ()
δ≡0⇒≡ false true  ()
δ≡0⇒≡ false false _  = refl

-- δ 的对称性: δ(a,b)=δ(b,a) (xor 交换)
δ-sym : ∀ (a b : Bool) → δ a b ≡ δ b a
δ-sym true  true  = refl
δ-sym true  false = refl
δ-sym false true  = refl
δ-sym false false = refl

-- bool→ℕ 的逆向: bool→ℕ b ≡ 0 → b ≡ false
bool→ℕ≡0⇒false : ∀ (b : Bool) → bool→ℕ b ≡ zero → b ≡ false
bool→ℕ≡0⇒false true  ()
bool→ℕ≡0⇒false false _  = refl

-- δ 的自反性: δ(a,a)=0
δ-refl : ∀ (a : Bool) → δ a a ≡ zero
δ-refl true  = refl
δ-refl false = refl

-- ⭐ δ 的三角不等式 (点态): δ(a,c) ≤ δ(a,b) + δ(b,c)
-- 8-case (2³) 穷举, 每种组合 δ 值精确计算:
--   δ(a,c)=0 时 LHS=0, 用 z≤n
--   δ(a,c)=1 且 RHS=1 时, 用 ≤-refl (1≤1)
--   δ(a,c)=1 且 RHS=2 时, 用 s≤s z≤n (1≤2)
δ-triangle : ∀ (a b c : Bool) → δ a c ≤ (δ a b + δ b c)
δ-triangle true  true  true  = z≤n        -- δ(T,T)=0 ≤ 0+0
δ-triangle true  true  false = ≤-refl     -- δ(T,F)=1 ≤ 0+1=1
δ-triangle true  false true  = z≤n        -- δ(T,T)=0 ≤ 1+1=2
δ-triangle true  false false = s≤s z≤n    -- δ(T,F)=1 ≤ 1+1=2
δ-triangle false true  true  = ≤-refl     -- δ(F,T)=1 ≤ 1+0=1
δ-triangle false true  false = z≤n        -- δ(F,F)=0 ≤ 1+1=2
δ-triangle false false true  = ≤-refl     -- δ(F,T)=1 ≤ 0+1=1
δ-triangle false false false = z≤n        -- δ(F,F)=0 ≤ 0+0

------------------------------------------------------------------------------
-- §3. 同一性 (全局): hamming(x,y)≡0 → x≡y
--
-- 对 N 归纳. base: trivial (Fin 0 空). step: head 的 δ≡0⇒equiv + tail 归纳.
------------------------------------------------------------------------------

-- hamming 自反性: d(x,x)=0
hamming-refl : ∀ {N : ℕ} (x : Word N) → hamming x x ≡ zero
hamming-refl {zero}  x = refl
hamming-refl {suc N} x = begin
  hamming x x                                      ≡⟨⟩
  bool→ℕ (x zero xor x zero) + hamming (λ i → x (suc i)) (λ i → x (suc i))  ≡⟨ cong (_+ hamming (λ i → x (suc i)) (λ i → x (suc i)))
                                                                                       (cong bool→ℕ (xor-self (x zero))) ⟩
  bool→ℕ false + hamming (λ i → x (suc i)) (λ i → x (suc i))               ≡⟨ cong (bool→ℕ false +_) (hamming-refl (λ i → x (suc i))) ⟩
  zero                                                                      ∎
  where
    open ≡-Reasoning
    -- xor 自消: a xor a = false (stdlib 有 _xor_ 的计算规则, 这里显式)
    xor-self : ∀ b → b xor b ≡ false
    xor-self true  = refl
    xor-self false = refl

-- ⭐ 同一性 (逐点方向): hamming(x,y)≡0 → ∀ i, x i ≡ y i
-- 这是度量公理 M2 的构造性内容. 在命题函数外延性下等价于 x ≡ y.
-- 对 N 归纳: head 用 m+n≡0⇒m≡0 提取 δ(x₀,y₀)≡0 → δ≡0⇒equiv; tail 用 m+n≡0⇒n≡0 递归.
hamming≡0⇒pointwise-eq : ∀ {N : ℕ} (x y : Word N) → hamming x y ≡ zero → ∀ (i : Fin N) → x i ≡ y i
hamming≡0⇒pointwise-eq {zero}  x y h ()
hamming≡0⇒pointwise-eq {suc N} x y h zero      = δ≡0⇒≡ (x zero) (y zero) head-zero
  where
    -- 从 h : bool→ℕ(x₀ xor y₀) + hamming tail ≡ 0 提取 head 部分 ≡ 0
    head-zero : δ (x zero) (y zero) ≡ zero
    head-zero = m+n≡0⇒m≡0 (bool→ℕ (x zero xor y zero)) h
hamming≡0⇒pointwise-eq {suc N} x y h (suc i) = hamming≡0⇒pointwise-eq tail-x tail-y tail-zero i
  where
    tail-x = λ j → x (suc j)
    tail-y = λ j → y (suc j)
    -- 从 h 提取 tail 部分 ≡ 0
    tail-zero : hamming tail-x tail-y ≡ zero
    tail-zero = m+n≡0⇒n≡0 (bool→ℕ (x zero xor y zero)) h

------------------------------------------------------------------------------
-- §4. 对称性 (全局): hamming(x,y)≡hamming(y,x)
------------------------------------------------------------------------------

hamming-sym : ∀ {N : ℕ} (x y : Word N) → hamming x y ≡ hamming y x
hamming-sym {zero}  x y = refl
hamming-sym {suc N} x y = begin
  bool→ℕ (x zero xor y zero) + hamming (λ i → x (suc i)) (λ i → y (suc i))
    ≡⟨ cong (_+ hamming (λ i → x (suc i)) (λ i → y (suc i)))
            (cong bool→ℕ (xor-comm (x zero) (y zero))) ⟩
  bool→ℕ (y zero xor x zero) + hamming (λ i → x (suc i)) (λ i → y (suc i))
    ≡⟨ cong (bool→ℕ (y zero xor x zero) +_)
            (hamming-sym (λ i → x (suc i)) (λ i → y (suc i))) ⟩
  bool→ℕ (y zero xor x zero) + hamming (λ i → y (suc i)) (λ i → x (suc i))  ∎
  where
    open ≡-Reasoning
    -- xor 交换 (4-case refl, 点态穷举)
    xor-comm : ∀ (a b : Bool) → a xor b ≡ b xor a
    xor-comm true  true  = refl
    xor-comm true  false = refl
    xor-comm false true  = refl
    xor-comm false false = refl

------------------------------------------------------------------------------
-- §5. ⭐ 三角不等式 (全局): hamming(x,z) ≤ hamming(x,y) + hamming(y,z)
--
-- 证明: 对 N 结构归纳.
--   base N=0: 0 ≤ 0+0 (z≤n)
--   step N→N+1:
--     head: δ-triangle (x₀,z₀) ≤ δ(x₀,y₀) + δ(y₀,z₀)      [点态引理]
--     tail: hamming(x₊,z₊) ≤ hamming(x₊,y₊) + hamming(y₊,z₊)  [归纳假设]
--     组合: ≤-trans / ≤-step 把 head 的不等式与 tail 相加
------------------------------------------------------------------------------

-- 四项重排: (a+b)+(c+d) ≡ (a+c)+(b+d)  [与 ProbabilityAddition.+-rearrange 同构]
+-rearrange : (a b c d : ℕ) → (a + b) + (c + d) ≡ (a + c) + (b + d)
+-rearrange a b c d = begin
  (a + b) + (c + d)     ≡⟨ +-assoc a b (c + d) ⟩
  a + (b + (c + d))     ≡⟨ cong (a +_) (sym (+-assoc b c d)) ⟩
  a + ((b + c) + d)     ≡⟨ cong (λ x → a + (x + d)) (+-comm b c) ⟩
  a + ((c + b) + d)     ≡⟨ cong (a +_) (+-assoc c b d) ⟩
  a + (c + (b + d))     ≡⟨ sym (+-assoc a c (b + d)) ⟩
  (a + c) + (b + d)     ∎
  where open ≡-Reasoning

-- ≤ 的右边可替换: a ≤ b, b≡c → a ≤ c
≤-respʳ-≡ : ∀ {m n o : ℕ} → m ≤ n → n ≡ o → m ≤ o
≤-respʳ-≡ p refl = p

-- 主定理: Hamming 三角不等式
hamming-triangle : ∀ {N : ℕ} (x y z : Word N) →
  hamming x z ≤ (hamming x y + hamming y z)
hamming-triangle {zero}  x y z = z≤n
hamming-triangle {suc N} x y z =
  -- +-mono-≤ 给出 δ(x₀,z₀)+H(x₊,z₊) ≤ (δ(x₀,y₀)+δ(y₀,z₀)) + (H(x₊,y₊)+H(y₊,z₊))
  -- 需重排 RHS 为 (δ(x₀,y₀)+H(x₊,y₊)) + (δ(y₀,z₀)+H(y₊,z₊)) = hamming x y + hamming y z
  ≤-respʳ-≡ (+-mono-≤ (δ-triangle (x zero) (y zero) (z zero))
                      (hamming-triangle (λ i → x (suc i)) (λ i → y (suc i)) (λ i → z (suc i))))
            (+-rearrange (δ (x zero) (y zero)) (δ (y zero) (z zero))
                         (hamming (λ i → x (suc i)) (λ i → y (suc i)))
                         (hamming (λ i → y (suc i)) (λ i → z (suc i))))

------------------------------------------------------------------------------
-- §6. 非负性 + 具体实例
------------------------------------------------------------------------------

-- 非负性: 0 ≤ hamming(x,y) (ℕ 自然非负, z≤n 直接适用)
hamming-nonneg : ∀ {N : ℕ} (x y : Word N) → zero ≤ hamming x y
hamming-nonneg x y = z≤n

-- 具体实例: Fin 3 上的三个字
-- x = 100, y = 110, z = 011
x-ex : Word 3
x-ex zero              = true
x-ex (suc zero)        = false
x-ex (suc (suc zero))  = false

y-ex : Word 3
y-ex zero              = true
y-ex (suc zero)        = true
y-ex (suc (suc zero))  = false

z-ex : Word 3
z-ex zero              = false
z-ex (suc zero)        = true
z-ex (suc (suc zero))  = true

-- d(x,y) = 1 (仅第 2 位不同)
hamming-xy : hamming x-ex y-ex ≡ 1
hamming-xy = refl

-- d(x,z) = 3 (全不同)
hamming-xz : hamming x-ex z-ex ≡ 3
hamming-xz = refl

-- d(y,z) = 2 (第 1,3 位不同)
hamming-yz : hamming y-ex z-ex ≡ 2
hamming-yz = refl

-- 三角不等式实例验证: d(x,z)=3 ≤ d(x,y)+d(y,z)=1+2=3 ✓ (紧界)
triangle-ex : hamming x-ex z-ex ≤ (hamming x-ex y-ex + hamming y-ex z-ex)
triangle-ex = hamming-triangle x-ex y-ex z-ex

-- 紧界实例: 3 ≤ 1+2 = 3, 取等
triangle-ex-tight : (hamming x-ex y-ex + hamming y-ex z-ex) ≡ 3
triangle-ex-tight = refl

------------------------------------------------------------------------------
-- §7. 离散独特性
--
-- 连续版本 (度量空间的一般理论):
--   三角不等式依赖实数 ≤ 的稠密性 + Archimedes 公理.
--
-- 离散版本 (Hamming):
--   三角不等式只需 8-case 布尔穷举 + ℕ 归纳.
--   δ 最大值为 1, 所以点态 ≤ 是有限可判定的, 无需任何极限/测度论.
--
--   连续度量公理的证明需要拓扑/分析工具 (~50 页)
--   Hamming 度量公理的证明是 8-case refl + ℕ 归纳 (~80 行 Agda)
--
-- 这是"离散 > 连续"的又一例证: 有限论域让度量的本质(逐点比较)完全显式化.
------------------------------------------------------------------------------

------------------------------------------------------------------------------
-- §8. 总结
--
-- 已证度量四公理 (对任意有限字 Fin N → Bool):
--   (M1) 非负性:     0 ≤ d(x,y)                    [hamming-nonneg]
--   (M2) 同一性:     d(x,y)=0 ⟺ ∀i, x i≡y i          [hamming-refl + hamming≡0⇒pointwise-eq]
--                    (在命题函数外延性下等价于 x≡y)
--   (M3) 对称性:     d(x,y)=d(y,x)                 [hamming-sym]
--   (M4) 三角不等式: d(x,z)≤d(x,y)+d(y,z)          [hamming-triangle] ⭐
--
-- 全部 0 postulate, 构造性证明.
-- 核心引理 δ-triangle 是 8-case 布尔穷举, hamming-triangle 对 N 归纳组装.
------------------------------------------------------------------------------
