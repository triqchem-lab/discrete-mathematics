{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Physics.DiscreteStatMech — 离散统计力学 (MSC 82)
--
-- 补强版 (2026-08), 七层, 0 postulate:
--   §1 计数型熵 S = W: n 位 GF(3) 寄存器的微态数 W(n) = 3ⁿ, 熵取微态数本身
--      (无对数计数型, GF(3) 上最自然的熵), 含乘法律 W(n+m) = W(n)·W(m).
--   §2 配分函数族 z2 → z3 → z4 (Trit 模 3 闭链, 全部 refl).
--   §3 Boltzmann 归一化 (模 3 周期闭合) + 特征 3 湮灭一般化 trit-triple-zero.
--   §4 ℚ 熵:
--      诚实口径: ℚ 上无一般对数, 全定义域香农熵不可在 ℚ 内表达 —
--      (a) 以二阶 Tsallis(碰撞)熵 tsallis2/tsallis3 为 ℚ 代理,
--          均匀分布熵最大定理对代理严格成立 (Fin 2 / Fin 3, 完整 ≤ 证明);
--      (b) 香农熵本体给出二进实例 (log₂ 仅在 {1, 1/2} 上定义):
--          H(1/2,1/2) = 1 最大, H(1,0) = 0.
--   §5 配分函数 = 状态和 (H≡0 桥接): Z = W, 复合系统乘法性, GF(3) 迹为零.
--   §6 内能: 二能级/三能级均匀系能量期望 (ℚ 精确, 均分形式 2U₂=1, 3U₃=2).
--   §7 T⁶ 微正则桥接: W 6 = 729 = T⁶ 格点数 (对齐 Structology.T6 t6≃fin729).
--  方法: 多项式恒等式 (tsallis*-gap) 由 stdlib 验证过的环求解器
--  Data.Rational.Solver 落链 — 求解器产出真实证明项, 非 postulate;
--  序关系部分手证 (平方非负 + 单调性), 无 with, 无 funext.

module Sovereign.Physics.DiscreteStatMech where

open import Data.Nat using (ℕ; zero; suc; z≤n)
  renaming (_+_ to _+ℕ_; _*_ to _*ℕ_; _^_ to _^ℕ_)
open import Data.Nat.Properties using (^-distribˡ-+-*)
open import Data.Integer using (ℤ; +_; +≤+; +0; +[1+_]; -[1+_])
open import Data.Sum using ([_,_]′)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂; subst; module ≡-Reasoning)
open ≡-Reasoning
open import Data.Rational using (ℚ; _+_; _*_; _-_; -_; _/_; _≤_; 0ℚ; 1ℚ)
open import Data.Rational.Base using (mkℚ; *≤*; nonNegative)
open import Data.Rational.Properties
  using (+-assoc; +-comm; +-identityˡ; +-identityʳ; +-inverseʳ;
         *-zeroʳ; *-identityʳ; neg-distrib-+; neg-distribˡ-*; neg-distribʳ-*;
         ≤-refl; ≤-trans; ≤-reflexive; ≤-total;
         +-mono-≤; +-monoʳ-≤; *-monoˡ-≤-nonNeg; neg-antimono-≤)
open import Data.Rational.Solver using (module +-*-Solver)
open +-*-Solver using (solve; con; _:+_; _:*_; :-_; _:-_; _:=_)
open import Sovereign.Base.Trit using (Trit; T₀; T₁; T₂; _⊕_)

--------------------------------------------------------------------------------
-- §0. ℚ 常数
--------------------------------------------------------------------------------

2ℚ : ℚ
2ℚ = 1ℚ + 1ℚ

3ℚ : ℚ
3ℚ = 2ℚ + 1ℚ

half : ℚ
half = (+ 1) / 2

third : ℚ
third = (+ 1) / 3

--------------------------------------------------------------------------------
-- §1. 计数型熵 S = W (GF(3) 自然计数, 无对数)
--   n 位三进制寄存器: 微态数 W(n) = 3ⁿ; 计数型熵直接取微态数 S = W.
--------------------------------------------------------------------------------

W : ℕ → ℕ
W n = 3 ^ℕ n

countEntropy : ℕ → ℕ
countEntropy = W

W-ok0 : W 0 ≡ 1
W-ok0 = refl

W-ok1 : W 1 ≡ 3
W-ok1 = refl

W-ok2 : W 2 ≡ 9
W-ok2 = refl

W-ok3 : W 3 ≡ 27
W-ok3 = refl

W-ok4 : W 4 ≡ 81
W-ok4 = refl

W-ok5 : W 5 ≡ 243
W-ok5 = refl

-- 步进律: W(n+1) = 3·W(n) (定义式, 每增一位乘 3)
W-suc : ∀ n → W (suc n) ≡ 3 *ℕ W n
W-suc n = refl

-- 乘法律: 并置系统的熵相乘 (W(n+m) = W(n)·W(m) — 状态空间直积)
W-add : ∀ n m → W (n +ℕ m) ≡ W n *ℕ W m
W-add n m = ^-distribˡ-+-* 3 n m

countEntropy-mult : ∀ n m → countEntropy (n +ℕ m) ≡ countEntropy n *ℕ countEntropy m
countEntropy-mult n m = W-add n m

--------------------------------------------------------------------------------
-- §2. 配分函数族 z2 → z3 → z4 (Trit 模 3 闭链)
--   z2 = 1+1 = 2, z3 = 1+1+1 = 0, z4 = 1+1+1+1 = 1 (模 3 周期 3 闭合)
--------------------------------------------------------------------------------

z2 : Trit
z2 = T₁ ⊕ T₁   -- 1+1 = 2 = T₂

z2-ok : z2 ≡ T₂
z2-ok = refl

z3 : Trit
z3 = (T₁ ⊕ T₁) ⊕ T₁   -- 1+1+1 = 3 ≡ 0

z3-ok : z3 ≡ T₀
z3-ok = refl

z4 : Trit
z4 = (T₁ ⊕ T₁) ⊕ (T₁ ⊕ T₁)   -- 1+1+1+1 = 4 ≡ 1

z4-ok : z4 ≡ T₁
z4-ok = refl

-- 模 3 闭链: 2+2 ≡ 1 (z4 闭合), 2+2+2 ≡ 0 (z3 闭合)
z2-double : z2 ⊕ z2 ≡ T₁
z2-double = refl

z2-triple : (z2 ⊕ z2) ⊕ z2 ≡ T₀
z2-triple = refl

--------------------------------------------------------------------------------
-- §3. Boltzmann 归一化 (模 3 周期)
--------------------------------------------------------------------------------

norm-z2 : (T₁ ⊕ T₁) ⊕ (T₁ ⊕ T₁) ≡ T₁   -- (1+1)+(1+1)=4≡1
norm-z2 = refl

norm-z3 : ((T₁ ⊕ T₁) ⊕ T₁) ⊕ ((T₁ ⊕ T₁) ⊕ T₁) ≡ T₀   -- (1+1+1)+(1+1+1)=6≡0
norm-z3 = refl

-- 特征 3 湮灭 (一般化): 任意 Trit 三重自加归零 — 模 3 周期闭合的根源
-- (Boltzmann 归一化之所以以 3 为周期闭合, 正因 GF(3) 特征为 3)
trit-triple-zero : ∀ t → t ⊕ (t ⊕ t) ≡ T₀
trit-triple-zero T₀ = refl
trit-triple-zero T₁ = refl
trit-triple-zero T₂ = refl

--------------------------------------------------------------------------------
-- §4. ℚ 熵 — 序关系基础引理
--------------------------------------------------------------------------------

0≤1 : 0ℚ ≤ 1ℚ
0≤1 = *≤* (+≤+ (z≤n {1}))

0≤2 : 0ℚ ≤ 2ℚ
0≤2 = ≤-trans (≤-reflexive (sym (+-identityˡ 0ℚ))) (+-mono-≤ 0≤1 0≤1)

-- ℚ 双负 (stdlib 2.4 未导出, 本地三情形)
negneg : ∀ p → - (- p) ≡ p
negneg (mkℚ +0 d prf) = refl
negneg (mkℚ +[1+ n ] d prf) = refl
negneg (mkℚ -[1+ n ] d prf) = refl

-- 负积消负: (-x)·(-x) ≡ x·x
neg-square : ∀ x → (- x) * (- x) ≡ x * x
neg-square x = begin
  (- x) * (- x)
    ≡⟨ sym (neg-distribʳ-* (- x) x) ⟩
  - ((- x) * x)
    ≡⟨ cong -_ (sym (neg-distribˡ-* x x)) ⟩
  - (- (x * x))
    ≡⟨ negneg (x * x) ⟩
  x * x ∎

-- 平方非负: 0 ≤ x·x (全序二分, 无 with)
square-nonneg : ∀ x → 0ℚ ≤ x * x
square-nonneg x = [ nn x , np x ]′ (≤-total 0ℚ x)
  where
  nn : ∀ y → 0ℚ ≤ y → 0ℚ ≤ y * y
  nn y 0≤y = ≤-trans (≤-reflexive (sym (*-zeroʳ y)))
                     (*-monoˡ-≤-nonNeg y {{nonNegative 0≤y}} 0≤y)
  np : ∀ y → y ≤ 0ℚ → 0ℚ ≤ y * y
  np y y≤0 = subst (λ t → 0ℚ ≤ t) (neg-square y)
                   (nn (- y) (neg-antimono-≤ y≤0))

-- 三平方和非负: 0 ≤ a² + (b² + (a+b)²)
sq-nonneg3 : ∀ a b → 0ℚ ≤ a * a + (b * b + ((a + b) * (a + b)))
sq-nonneg3 a b = ≤-trans
  (≤-trans (square-nonneg a) (≤-reflexive (sym (+-identityʳ (a * a)))))
  (+-monoʳ-≤ (a * a)
    (≤-trans (≤-trans (square-nonneg b) (≤-reflexive (sym (+-identityʳ (b * b)))))
             (+-monoʳ-≤ (b * b) (square-nonneg (a + b)))))

--------------------------------------------------------------------------------
-- §4a. 二阶 Tsallis(碰撞)熵: S₂ = 1 − Σ pᵢ² — 香农熵的 ℚ 代理
--   均匀分布熵最大 (Fin 2): S₂(p) ≤ S₂(1/2,1/2), p 为归一化二项分布 (p, 1−p)
--------------------------------------------------------------------------------

tsallis2 : ℚ → ℚ
tsallis2 p = 1ℚ - (p * p + ((1ℚ - p) * (1ℚ - p)))

tsallis2-uniform : ℚ
tsallis2-uniform = 1ℚ - (half * half + (half * half))

-- 间隙恒等式: S₂(均匀) = S₂(p) + 2·(p−1/2)² (手算: p²+(1−p)²−1/2 = 2(p−1/2)²)
-- 多项式恒等式由验证过的环求解器落链 (真实证明项, 非 postulate)
tsallis2-gap : ∀ p →
  tsallis2-uniform ≡ tsallis2 p + 2ℚ * ((p - half) * (p - half))
tsallis2-gap p = solve 1
  (λ p → con tsallis2-uniform :=
    (con 1ℚ :- (p :* p :+ ((con 1ℚ :- p) :* (con 1ℚ :- p))))
    :+ (con 2ℚ :* ((p :- con half) :* (p :- con half))))
  refl p

-- 间隙非负: 0 ≤ 2·(p−1/2)²
tsallis2-gap-nonneg : ∀ p → 0ℚ ≤ 2ℚ * ((p - half) * (p - half))
tsallis2-gap-nonneg p = ≤-trans
  (≤-reflexive (sym (*-zeroʳ 2ℚ)))
  (*-monoˡ-≤-nonNeg 2ℚ {{nonNegative 0≤2}} (square-nonneg (p - half)))

-- 均匀分布熵最大 (Fin 2, 完整 ≤ 证明)
tsallis2-max : ∀ p → tsallis2 p ≤ tsallis2-uniform
tsallis2-max p = ≤-trans
  (≤-trans (≤-reflexive (sym (+-identityʳ (tsallis2 p))))
           (+-monoʳ-≤ (tsallis2 p) (tsallis2-gap-nonneg p)))
  (≤-reflexive (sym (tsallis2-gap p)))

-- 碰撞概率下界 (Rényi-2 读数): Σpᵢ² ≥ 1/2 在均匀分布取最小
collision-min2 : ∀ p → 1ℚ - tsallis2-uniform ≤ 1ℚ - tsallis2 p
collision-min2 p = +-monoʳ-≤ 1ℚ (neg-antimono-≤ (tsallis2-max p))

--------------------------------------------------------------------------------
-- §4b. 三原子分布 (Fin 3): 偏移参数化 p=1/3+a, q=1/3+b, r=1/3−a−b
--   间隙 = a² + b² + (a+b)² (手算展开: 交叉项全消)
--------------------------------------------------------------------------------

tsallis3 : ℚ → ℚ → ℚ
tsallis3 a b =
  1ℚ - ((third + a) * (third + a)
    + ((third + b) * (third + b) + (third - a - b) * (third - a - b)))

tsallis3-uniform : ℚ
tsallis3-uniform = 1ℚ - (third * third + (third * third + third * third))

tsallis3-gap : ∀ a b →
  tsallis3-uniform ≡ tsallis3 a b + (a * a + (b * b + ((a + b) * (a + b))))
tsallis3-gap a b = solve 2
  (λ a b → con tsallis3-uniform :=
    (con 1ℚ :- (((con third :+ a) :* (con third :+ a))
      :+ (((con third :+ b) :* (con third :+ b))
        :+ (((con third :- a) :- b) :* ((con third :- a) :- b)))))
    :+ (a :* a :+ (b :* b :+ ((a :+ b) :* (a :+ b)))))
  refl a b

-- 均匀分布熵最大 (Fin 3, 三平方和间隙)
tsallis3-max : ∀ a b → tsallis3 a b ≤ tsallis3-uniform
tsallis3-max a b = ≤-trans
  (≤-trans (≤-reflexive (sym (+-identityʳ (tsallis3 a b))))
           (+-monoʳ-≤ (tsallis3 a b) (sq-nonneg3 a b)))
  (≤-reflexive (sym (tsallis3-gap a b)))

collision-min3 : ∀ a b → 1ℚ - tsallis3-uniform ≤ 1ℚ - tsallis3 a b
collision-min3 a b = +-monoʳ-≤ 1ℚ (neg-antimono-≤ (tsallis3-max a b))

--------------------------------------------------------------------------------
-- §4c. 香农熵二进实例 (log₂ 仅在 {1, 1/2} 上定义, 全函数约定: 其余归 0ℚ)
--   shannon2(p) = −[p·log₂p + (1−p)·log₂(1−p)] — 二进权重上的精确实例
--------------------------------------------------------------------------------

log2dy : ℚ → ℚ
log2dy (mkℚ +[1+ 0 ] zero _) = 0ℚ          -- log₂(1/1) = 0
log2dy (mkℚ +[1+ 0 ] (suc zero) _) = - 1ℚ -- log₂(1/2) = −1
log2dy _ = 0ℚ

shannon2 : ℚ → ℚ
shannon2 p = - (p * log2dy p + ((1ℚ - p) * log2dy (1ℚ - p)))

-- 均匀二进分布 (1/2, 1/2): H = 1
shannon2-uniform : shannon2 half ≡ 1ℚ
shannon2-uniform = begin
  shannon2 half
    ≡⟨ refl ⟩
  - ((half * (- 1ℚ)) + ((1ℚ - half) * (- 1ℚ)))
    ≡⟨ cong₂ (λ x y → - (x + y)) half-neg1 oneMinusHalf-neg1 ⟩
  - ((- half) + (- (1ℚ - half)))
    ≡⟨ cong -_ (sym (neg-distrib-+ half (1ℚ - half))) ⟩
  - (- (half + (1ℚ - half)))
    ≡⟨ cong (λ t → - (- t)) half+oneMinusHalf≡1 ⟩
  - (- 1ℚ)
    ≡⟨ negneg 1ℚ ⟩
  1ℚ ∎
  where
  half-neg1 : half * (- 1ℚ) ≡ - half
  half-neg1 = begin
    half * (- 1ℚ)
      ≡⟨ sym (neg-distribʳ-* half 1ℚ) ⟩
    - (half * 1ℚ)
      ≡⟨ cong -_ (*-identityʳ half) ⟩
    - half ∎
  oneMinusHalf-neg1 : (1ℚ - half) * (- 1ℚ) ≡ - (1ℚ - half)
  oneMinusHalf-neg1 = begin
    (1ℚ - half) * (- 1ℚ)
      ≡⟨ sym (neg-distribʳ-* (1ℚ - half) 1ℚ) ⟩
    - ((1ℚ - half) * 1ℚ)
      ≡⟨ cong -_ (*-identityʳ (1ℚ - half)) ⟩
    - (1ℚ - half) ∎
  half+oneMinusHalf≡1 : half + (1ℚ - half) ≡ 1ℚ
  half+oneMinusHalf≡1 = begin
    half + (1ℚ - half)
      ≡⟨ refl ⟩
    half + (1ℚ + (- half))
      ≡⟨ sym (+-assoc half 1ℚ (- half)) ⟩
    (half + 1ℚ) + (- half)
      ≡⟨ cong (λ t → t + (- half)) (+-comm half 1ℚ) ⟩
    (1ℚ + half) + (- half)
      ≡⟨ +-assoc 1ℚ half (- half) ⟩
    1ℚ + (half + (- half))
      ≡⟨ cong (λ t → 1ℚ + t) (+-inverseʳ half) ⟩
    1ℚ + 0ℚ
      ≡⟨ +-identityʳ 1ℚ ⟩
    1ℚ ∎

-- 退化分布 (1, 0): H = 0
shannon2-degenerate : shannon2 1ℚ ≡ 0ℚ
shannon2-degenerate = begin
  shannon2 1ℚ
    ≡⟨ refl ⟩
  - ((1ℚ * 0ℚ) + ((1ℚ - 1ℚ) * 0ℚ))
    ≡⟨ cong₂ (λ x y → - (x + y)) (*-zeroʳ 1ℚ) (*-zeroʳ (1ℚ - 1ℚ)) ⟩
  - (0ℚ + 0ℚ)
    ≡⟨ cong -_ (+-identityˡ 0ℚ) ⟩
  - 0ℚ
    ≡⟨ refl ⟩
  0ℚ ∎

-- 二进香农熵最大值: H(1,0) = 0 ≤ 1 = H(1/2,1/2) — 均匀最大
dyadic-max2 : shannon2 1ℚ ≤ shannon2 half
dyadic-max2 = ≤-trans (≤-reflexive shannon2-degenerate)
              (≤-trans 0≤1 (≤-reflexive (sym shannon2-uniform)))

--------------------------------------------------------------------------------
-- §5. 配分函数 = 状态和 (H ≡ 0 桥接, 2026-08 补强)
--   平凡哈密顿量下配分函数退化为微态计数: Z = Σ_states 1 = W.
--   复合系统张量积 ⟹ 乘法性; GF(3) 特征 ⟹ n≥1 时迹为零.
--------------------------------------------------------------------------------

Z : ℕ → ℕ
Z = W

Z-is-W : ∀ n → Z n ≡ W n
Z-is-W n = refl

-- GF(3) 迹: Z(suc n) = 3·W(n) ⟹ mod 3 = 0 (特征 3 湮灭, 承 §3 trit-triple-zero)
Z-suc : ∀ n → Z (suc n) ≡ 3 *ℕ W n
Z-suc n = refl

-- 复合系统: 状态空间直积 ⟹ 配分函数相乘
Z-mult : ∀ n m → Z (n +ℕ m) ≡ Z n *ℕ Z m
Z-mult n m = W-add n m

--------------------------------------------------------------------------------
-- §6. 内能: 离散能级系统均匀分布能量期望 (ℚ 精确, 无浮点)
--   U = Σᵢ pᵢ·Eᵢ; 均匀分布 pᵢ = 1/n.
--------------------------------------------------------------------------------

-- 二能级系统 {0, 1}: U₂ = (0+1)·(1/2)
U2 : ℚ
U2 = (0ℚ + 1ℚ) * half

-- 三能级系统 {0, 1, 2}: U₃ = (0+1+2)·(1/3)
U3-level : ℚ
U3-level = (0ℚ + (1ℚ + 1ℚ)) * third

-- 二能级均匀期望 = 1/2 (能级均值)
U2-half : U2 ≡ half
U2-half = refl

-- 均分形式: 2·U₂ = 1 (能级跨度 1 的一半)
two-U2≡1 : 2ℚ * U2 ≡ 1ℚ
two-U2≡1 = refl

-- 三能级均匀期望: U₃ = 2·(1/3) (能级和 0+1+2 = 2)
U3-two-thirds : U3-level ≡ third + third
U3-two-thirds = refl

-- 3·U₃ = 2 (能级总和)
three-U3≡2 : 3ℚ * U3-level ≡ 2ℚ
three-U3≡2 = refl

--------------------------------------------------------------------------------
-- §7. T⁶ 微正则桥接 (2026-08 补强)
--   T⁶ = (GF(3))⁶ 格点数 = 3⁶ = 729 (对齐 Structology.T6 的 t6≃fin729,
--   同构定理在结构学侧, 此处只锁计数事实; 环面动力学解读属命名层).
--------------------------------------------------------------------------------

W6-729 : W 6 ≡ 729
W6-729 = refl

-- T⁶ 微正则熵 (计数型 S = W): S(T⁶) = 729
S-T6 : countEntropy 6 ≡ 729
S-T6 = refl

-- 复合环面: T⁶⁺¹ 微态数 = 3·729 = 2187 (步进律实例)
S-T6-step : W 7 ≡ 3 *ℕ 729
S-T6-step = refl

-- 0 postulate.
