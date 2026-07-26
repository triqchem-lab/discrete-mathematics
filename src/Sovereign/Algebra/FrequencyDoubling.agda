{-# OPTIONS --rewriting #-}

-- | Sovereign.Algebra.FrequencyDoubling
-- 倍频量子纠缠链的代数结构: Z/3Z → Z/6Z → Z/12Z → Z/24Z
--
-- 倍频链:
--   3 ×2 = 6   (Z/3Z → Z/6Z)
--   6 ×2 = 12  (Z/6Z → Z/12Z)
--   12 ×2 = 24 (Z/12Z → Z/24Z)
--   24 → dr(24) = 6 (数字根回绕)
--
-- 环同态链:
--   double-3-6   : Z/3Z → Z/6Z,   x ↦ 2x mod 6
--   double-6-12  : Z/6Z → Z/12Z,  x ↦ 2x mod 12
--   double-12-24 : Z/12Z → Z/24Z, x ↦ 2x mod 24
--
-- 代数性质:
--   每个倍频映射是加法群同态（保持加法）
--   每个倍频映射是单射（信息保持）
--   每个倍频映射不是满射（奇数元素不在像中）
--
-- 量子纠缠:
--   测量 x mod 3 确定 2x mod 6, 4x mod 12, 8x mod 24
--
-- 0 postulate — 全部构造性证明

module Sovereign.Algebra.FrequencyDoubling where

open import Data.Nat using (ℕ; _*_; _%_)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; trans; sym; cong)
open import Relation.Nullary using (¬_)
import Sovereign.RootMath.DigitalRoot as DR
open import Sovereign.Algebra.Duodecimal
  using (Duodec; d0; d1; d2; d3; d4; d5; d6; d7; d8; d9; d10; d11;
         toℕ₁₂; _+12_; +12-order)
open import Sovereign.Base.Trit
  using (Trit; T₀; T₁; T₂; _⊕_; tritToℕ)
open import Sovereign.Algebra.VortexRoot
  using (VortexRoot; root3; root6; root12; vortexValue; next)

-- 不等式（本地定义，避免标准库版本差异）
_≢_ : {A : Set} → A → A → Set
x ≢ y = ¬ (x ≡ y)

--------------------------------------------------------------------------------
-- 1. Z/6Z 加法群 — 倍频链的二次谐波环
--------------------------------------------------------------------------------

data Mod6 : Set where
  s0 s1 s2 s3 s4 s5 : Mod6

-- 到 ℕ 的本源表示
toℕ₆ : Mod6 → ℕ
toℕ₆ s0 = 0; toℕ₆ s1 = 1; toℕ₆ s2 = 2
toℕ₆ s3 = 3; toℕ₆ s4 = 4; toℕ₆ s5 = 5

-- 循环后继: +1 mod 6
+1₆ : Mod6 → Mod6
+1₆ s0 = s1; +1₆ s1 = s2; +1₆ s2 = s3
+1₆ s3 = s4; +1₆ s4 = s5; +1₆ s5 = s0

-- 加法 mod 6: sk +6 y = +1₆^k (y)
_+6_ : Mod6 → Mod6 → Mod6
s0 +6 y = y
s1 +6 y = +1₆ y
s2 +6 y = +1₆ (+1₆ y)
s3 +6 y = +1₆ (+1₆ (+1₆ y))
s4 +6 y = +1₆ (+1₆ (+1₆ (+1₆ y)))
s5 +6 y = +1₆ (+1₆ (+1₆ (+1₆ (+1₆ y))))

-- +1₆ 周期 6
+1₆^6-id : ∀ x → +1₆ (+1₆ (+1₆ (+1₆ (+1₆ (+1₆ x))))) ≡ x
+1₆^6-id s0 = refl; +1₆^6-id s1 = refl; +1₆^6-id s2 = refl
+1₆^6-id s3 = refl; +1₆^6-id s4 = refl; +1₆^6-id s5 = refl

-- 加法群阶 = 6
+6-order : ℕ
+6-order = 6

--------------------------------------------------------------------------------
-- 2. Z/24Z 加法群 — 倍频链的四次谐波环（回绕到 6）
--------------------------------------------------------------------------------

data Mod24 : Set where
  t0 t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15 t16 t17 t18 t19 t20 t21 t22 t23 : Mod24

-- 到 ℕ 的本源表示
toℕ₂₄ : Mod24 → ℕ
toℕ₂₄ t0 = 0;  toℕ₂₄ t1 = 1;  toℕ₂₄ t2 = 2;  toℕ₂₄ t3 = 3
toℕ₂₄ t4 = 4;  toℕ₂₄ t5 = 5;  toℕ₂₄ t6 = 6;  toℕ₂₄ t7 = 7
toℕ₂₄ t8 = 8;  toℕ₂₄ t9 = 9;  toℕ₂₄ t10 = 10; toℕ₂₄ t11 = 11
toℕ₂₄ t12 = 12; toℕ₂₄ t13 = 13; toℕ₂₄ t14 = 14; toℕ₂₄ t15 = 15
toℕ₂₄ t16 = 16; toℕ₂₄ t17 = 17; toℕ₂₄ t18 = 18; toℕ₂₄ t19 = 19
toℕ₂₄ t20 = 20; toℕ₂₄ t21 = 21; toℕ₂₄ t22 = 22; toℕ₂₄ t23 = 23

-- 循环后继: +1 mod 24
+1₂₄ : Mod24 → Mod24
+1₂₄ t0 = t1;  +1₂₄ t1 = t2;  +1₂₄ t2 = t3;  +1₂₄ t3 = t4
+1₂₄ t4 = t5;  +1₂₄ t5 = t6;  +1₂₄ t6 = t7;  +1₂₄ t7 = t8
+1₂₄ t8 = t9;  +1₂₄ t9 = t10; +1₂₄ t10 = t11; +1₂₄ t11 = t12
+1₂₄ t12 = t13; +1₂₄ t13 = t14; +1₂₄ t14 = t15; +1₂₄ t15 = t16
+1₂₄ t16 = t17; +1₂₄ t17 = t18; +1₂₄ t18 = t19; +1₂₄ t19 = t20
+1₂₄ t20 = t21; +1₂₄ t21 = t22; +1₂₄ t22 = t23; +1₂₄ t23 = t0

-- 加法 mod 24: tk +24 y = +1₂₄^k (y)
_+24_ : Mod24 → Mod24 → Mod24
t0  +24 y = y
t1  +24 y = +1₂₄ y
t2  +24 y = +1₂₄ (+1₂₄ y)
t3  +24 y = +1₂₄ (+1₂₄ (+1₂₄ y))
t4  +24 y = +1₂₄ (+1₂₄ (+1₂₄ (+1₂₄ y)))
t5  +24 y = +1₂₄ (+1₂₄ (+1₂₄ (+1₂₄ (+1₂₄ y))))
t6  +24 y = +1₂₄ (+1₂₄ (+1₂₄ (+1₂₄ (+1₂₄ (+1₂₄ y)))))
t7  +24 y = +1₂₄ (+1₂₄ (+1₂₄ (+1₂₄ (+1₂₄ (+1₂₄ (+1₂₄ y))))))
t8  +24 y = +1₂₄ (+1₂₄ (+1₂₄ (+1₂₄ (+1₂₄ (+1₂₄ (+1₂₄ (+1₂₄ y)))))))
t9  +24 y = +1₂₄ (+1₂₄ (+1₂₄ (+1₂₄ (+1₂₄ (+1₂₄ (+1₂₄ (+1₂₄ (+1₂₄ y))))))))
t10 +24 y = +1₂₄ (+1₂₄ (+1₂₄ (+1₂₄ (+1₂₄ (+1₂₄ (+1₂₄ (+1₂₄ (+1₂₄ (+1₂₄ y)))))))))
t11 +24 y = +1₂₄ (+1₂₄ (+1₂₄ (+1₂₄ (+1₂₄ (+1₂₄ (+1₂₄ (+1₂₄ (+1₂₄ (+1₂₄ (+1₂₄ y))))))))))
t12 +24 y = +1₂₄ (+1₂₄ (+1₂₄ (+1₂₄ (+1₂₄ (+1₂₄ (+1₂₄ (+1₂₄ (+1₂₄ (+1₂₄ (+1₂₄ (+1₂₄ y)))))))))))
t13 +24 y = +1₂₄ (+1₂₄ (+1₂₄ (+1₂₄ (+1₂₄ (+1₂₄ (+1₂₄ (+1₂₄ (+1₂₄ (+1₂₄ (+1₂₄ (+1₂₄ (+1₂₄ y))))))))))))
t14 +24 y = +1₂₄ (+1₂₄ (+1₂₄ (+1₂₄ (+1₂₄ (+1₂₄ (+1₂₄ (+1₂₄ (+1₂₄ (+1₂₄ (+1₂₄ (+1₂₄ (+1₂₄ (+1₂₄ y)))))))))))))
t15 +24 y = +1₂₄ (+1₂₄ (+1₂₄ (+1₂₄ (+1₂₄ (+1₂₄ (+1₂₄ (+1₂₄ (+1₂₄ (+1₂₄ (+1₂₄ (+1₂₄ (+1₂₄ (+1₂₄ (+1₂₄ y))))))))))))))
t16 +24 y = +1₂₄ (+1₂₄ (+1₂₄ (+1₂₄ (+1₂₄ (+1₂₄ (+1₂₄ (+1₂₄ (+1₂₄ (+1₂₄ (+1₂₄ (+1₂₄ (+1₂₄ (+1₂₄ (+1₂₄ (+1₂₄ y)))))))))))))))
t17 +24 y = +1₂₄ (+1₂₄ (+1₂₄ (+1₂₄ (+1₂₄ (+1₂₄ (+1₂₄ (+1₂₄ (+1₂₄ (+1₂₄ (+1₂₄ (+1₂₄ (+1₂₄ (+1₂₄ (+1₂₄ (+1₂₄ (+1₂₄ y))))))))))))))))
t18 +24 y = +1₂₄ (+1₂₄ (+1₂₄ (+1₂₄ (+1₂₄ (+1₂₄ (+1₂₄ (+1₂₄ (+1₂₄ (+1₂₄ (+1₂₄ (+1₂₄ (+1₂₄ (+1₂₄ (+1₂₄ (+1₂₄ (+1₂₄ (+1₂₄ y)))))))))))))))))
t19 +24 y = +1₂₄ (+1₂₄ (+1₂₄ (+1₂₄ (+1₂₄ (+1₂₄ (+1₂₄ (+1₂₄ (+1₂₄ (+1₂₄ (+1₂₄ (+1₂₄ (+1₂₄ (+1₂₄ (+1₂₄ (+1₂₄ (+1₂₄ (+1₂₄ (+1₂₄ y))))))))))))))))))
t20 +24 y = +1₂₄ (+1₂₄ (+1₂₄ (+1₂₄ (+1₂₄ (+1₂₄ (+1₂₄ (+1₂₄ (+1₂₄ (+1₂₄ (+1₂₄ (+1₂₄ (+1₂₄ (+1₂₄ (+1₂₄ (+1₂₄ (+1₂₄ (+1₂₄ (+1₂₄ (+1₂₄ y)))))))))))))))))))
t21 +24 y = +1₂₄ (+1₂₄ (+1₂₄ (+1₂₄ (+1₂₄ (+1₂₄ (+1₂₄ (+1₂₄ (+1₂₄ (+1₂₄ (+1₂₄ (+1₂₄ (+1₂₄ (+1₂₄ (+1₂₄ (+1₂₄ (+1₂₄ (+1₂₄ (+1₂₄ (+1₂₄ (+1₂₄ y))))))))))))))))))))
t22 +24 y = +1₂₄ (+1₂₄ (+1₂₄ (+1₂₄ (+1₂₄ (+1₂₄ (+1₂₄ (+1₂₄ (+1₂₄ (+1₂₄ (+1₂₄ (+1₂₄ (+1₂₄ (+1₂₄ (+1₂₄ (+1₂₄ (+1₂₄ (+1₂₄ (+1₂₄ (+1₂₄ (+1₂₄ (+1₂₄ y)))))))))))))))))))))
t23 +24 y = +1₂₄ (+1₂₄ (+1₂₄ (+1₂₄ (+1₂₄ (+1₂₄ (+1₂₄ (+1₂₄ (+1₂₄ (+1₂₄ (+1₂₄ (+1₂₄ (+1₂₄ (+1₂₄ (+1₂₄ (+1₂₄ (+1₂₄ (+1₂₄ (+1₂₄ (+1₂₄ (+1₂₄ (+1₂₄ (+1₂₄ y))))))))))))))))))))))

-- +1₂₄ 周期 24
+1₂₄^24-id : ∀ x →
  +1₂₄ (+1₂₄ (+1₂₄ (+1₂₄ (+1₂₄ (+1₂₄ (+1₂₄ (+1₂₄ (+1₂₄ (+1₂₄ (+1₂₄ (+1₂₄
  (+1₂₄ (+1₂₄ (+1₂₄ (+1₂₄ (+1₂₄ (+1₂₄ (+1₂₄ (+1₂₄ (+1₂₄ (+1₂₄ (+1₂₄ (+1₂₄
  x))))))))))))))))))))))) ≡ x
+1₂₄^24-id t0 = refl;  +1₂₄^24-id t1 = refl;  +1₂₄^24-id t2 = refl;  +1₂₄^24-id t3 = refl
+1₂₄^24-id t4 = refl;  +1₂₄^24-id t5 = refl;  +1₂₄^24-id t6 = refl;  +1₂₄^24-id t7 = refl
+1₂₄^24-id t8 = refl;  +1₂₄^24-id t9 = refl;  +1₂₄^24-id t10 = refl; +1₂₄^24-id t11 = refl
+1₂₄^24-id t12 = refl; +1₂₄^24-id t13 = refl; +1₂₄^24-id t14 = refl; +1₂₄^24-id t15 = refl
+1₂₄^24-id t16 = refl; +1₂₄^24-id t17 = refl; +1₂₄^24-id t18 = refl; +1₂₄^24-id t19 = refl
+1₂₄^24-id t20 = refl; +1₂₄^24-id t21 = refl; +1₂₄^24-id t22 = refl; +1₂₄^24-id t23 = refl

-- 加法群阶 = 24
+24-order : ℕ
+24-order = 24

--------------------------------------------------------------------------------
-- 3. 倍频映射（环同态）
--------------------------------------------------------------------------------

-- Z/3Z → Z/6Z: x ↦ 2x mod 6
double-3-6 : Trit → Mod6
double-3-6 T₀ = s0  -- 0 → 0
double-3-6 T₁ = s2  -- 1 → 2
double-3-6 T₂ = s4  -- 2 → 4

-- Z/6Z → Z/12Z: x ↦ 2x mod 12
double-6-12 : Mod6 → Duodec
double-6-12 s0 = d0   -- 0 → 0
double-6-12 s1 = d2   -- 1 → 2
double-6-12 s2 = d4   -- 2 → 4
double-6-12 s3 = d6   -- 3 → 6
double-6-12 s4 = d8   -- 4 → 8
double-6-12 s5 = d10  -- 5 → 10

-- Z/12Z → Z/24Z: x ↦ 2x mod 24
double-12-24 : Duodec → Mod24
double-12-24 d0 = t0;   double-12-24 d1 = t2;   double-12-24 d2 = t4;   double-12-24 d3 = t6
double-12-24 d4 = t8;   double-12-24 d5 = t10;  double-12-24 d6 = t12;  double-12-24 d7 = t14
double-12-24 d8 = t16;  double-12-24 d9 = t18;  double-12-24 d10 = t20; double-12-24 d11 = t22

--------------------------------------------------------------------------------
-- 4. 数字根回绕
--------------------------------------------------------------------------------

-- dr(24) = 2+4 = 6（回绕到二次谐波）
dr-24 : DR.digitalRoot 24 ≡ 6
dr-24 = refl

-- 倍频链的数字根序列: dr(3)=3, dr(6)=6, dr(12)=3, dr(24)=6
dr-3 : DR.digitalRoot 3 ≡ 3
dr-3 = refl

dr-6 : DR.digitalRoot 6 ≡ 6
dr-6 = refl

dr-12 : DR.digitalRoot 12 ≡ 3
dr-12 = refl

-- 回绕等价: dr(24) ≡ dr(6)（24 和 6 在数字根下不可区分）
dr-24≡dr-6 : DR.digitalRoot 24 ≡ DR.digitalRoot 6
dr-24≡dr-6 = refl

-- 倍频链在数字根下的周期 2（从 6 开始）
-- 6 → dr(12)=3 → dr(24)=6 → dr(48)=3 → ...
dr-period-2 : DR.digitalRoot (12 * 2) ≡ DR.digitalRoot 6
dr-period-2 = refl

--------------------------------------------------------------------------------
-- 5. 量子纠缠 — 测量一个确定全链
--------------------------------------------------------------------------------

-- 倍频映射与 ℕ 投影的兼容性
-- 知道 x mod 3 → 知道 2x mod 6
entangle-3-6 : ∀ x → toℕ₆ (double-3-6 x) ≡ (2 * tritToℕ x) % 6
entangle-3-6 T₀ = refl
entangle-3-6 T₁ = refl
entangle-3-6 T₂ = refl

-- 知道 x mod 6 → 知道 2x mod 12
entangle-6-12 : ∀ x → toℕ₁₂ (double-6-12 x) ≡ (2 * toℕ₆ x) % 12
entangle-6-12 s0 = refl
entangle-6-12 s1 = refl
entangle-6-12 s2 = refl
entangle-6-12 s3 = refl
entangle-6-12 s4 = refl
entangle-6-12 s5 = refl

-- 知道 x mod 12 → 知道 2x mod 24
entangle-12-24 : ∀ x → toℕ₂₄ (double-12-24 x) ≡ (2 * toℕ₁₂ x) % 24
entangle-12-24 d0 = refl;  entangle-12-24 d1 = refl;  entangle-12-24 d2 = refl;  entangle-12-24 d3 = refl
entangle-12-24 d4 = refl;  entangle-12-24 d5 = refl;  entangle-12-24 d6 = refl;  entangle-12-24 d7 = refl
entangle-12-24 d8 = refl;  entangle-12-24 d9 = refl;  entangle-12-24 d10 = refl; entangle-12-24 d11 = refl

-- 链组合: 测量 Z/3Z 确定 Z/12Z 的像（4x mod 12）
chain-3→12 : Trit → Duodec
chain-3→12 x = double-6-12 (double-3-6 x)

chain-3→12-ℕ : ∀ x → toℕ₁₂ (chain-3→12 x) ≡ (4 * tritToℕ x) % 12
chain-3→12-ℕ T₀ = refl  -- 0 ≡ 0
chain-3→12-ℕ T₁ = refl  -- 4 ≡ 4
chain-3→12-ℕ T₂ = refl  -- 8 ≡ 8

-- 链组合: 测量 Z/3Z 确定 Z/24Z 的像（8x mod 24）
chain-3→24 : Trit → Mod24
chain-3→24 x = double-12-24 (double-6-12 (double-3-6 x))

chain-3→24-ℕ : ∀ x → toℕ₂₄ (chain-3→24 x) ≡ (8 * tritToℕ x) % 24
chain-3→24-ℕ T₀ = refl  -- 0 ≡ 0
chain-3→24-ℕ T₁ = refl  -- 8 ≡ 8
chain-3→24-ℕ T₂ = refl  -- 16 ≡ 16

--------------------------------------------------------------------------------
-- 6. 涡旋根连接 — VortexRoot ↔ 倍频环同态链
--------------------------------------------------------------------------------

-- 涡旋根的倍频值对应环的阶
-- root3 → Z/3Z (阶 3)
vortex-ring-3 : vortexValue root3 ≡ 3
vortex-ring-3 = refl

-- root6 → Z/6Z (阶 6)
vortex-ring-6 : vortexValue root6 ≡ +6-order
vortex-ring-6 = refl

-- root12 → Z/12Z (阶 12)
vortex-ring-12 : vortexValue root12 ≡ +12-order
vortex-ring-12 = refl

-- 倍频链步进与涡旋根 next 的对应
-- next root3 = root6 ↔ double-3-6 : Z/3Z → Z/6Z
vortex-next-3→6 : next root3 ≡ root6
vortex-next-3→6 = refl

-- next root6 = root12 ↔ double-6-12 : Z/6Z → Z/12Z
vortex-next-6→12 : next root6 ≡ root12
vortex-next-6→12 = refl

-- next root12 = root6 (回绕) ↔ Z/24Z → dr → Z/6Z
vortex-next-12→6 : next root12 ≡ root6
vortex-next-12→6 = refl

-- 24 = 2 × 12，是 Z/12Z 的倍频扩张（Merkaba 手征双四面体）
merkaba-order : 12 * 2 ≡ +24-order
merkaba-order = refl

--------------------------------------------------------------------------------
-- 7. 代数性质
--------------------------------------------------------------------------------

-- 7a. 同态性 — 每个倍频映射保持加法

-- Z/3Z → Z/6Z 同态 (9 case 穷举 refl)
double-3-6-homo : ∀ x y → double-3-6 (x ⊕ y) ≡ double-3-6 x +6 double-3-6 y
double-3-6-homo T₀ T₀ = refl; double-3-6-homo T₀ T₁ = refl; double-3-6-homo T₀ T₂ = refl
double-3-6-homo T₁ T₀ = refl; double-3-6-homo T₁ T₁ = refl; double-3-6-homo T₁ T₂ = refl
double-3-6-homo T₂ T₀ = refl; double-3-6-homo T₂ T₁ = refl; double-3-6-homo T₂ T₂ = refl

-- Z/6Z → Z/12Z 同态 (36 case 穷举 refl)
double-6-12-homo : ∀ x y → double-6-12 (x +6 y) ≡ double-6-12 x +12 double-6-12 y
double-6-12-homo s0 s0 = refl; double-6-12-homo s0 s1 = refl; double-6-12-homo s0 s2 = refl
double-6-12-homo s0 s3 = refl; double-6-12-homo s0 s4 = refl; double-6-12-homo s0 s5 = refl
double-6-12-homo s1 s0 = refl; double-6-12-homo s1 s1 = refl; double-6-12-homo s1 s2 = refl
double-6-12-homo s1 s3 = refl; double-6-12-homo s1 s4 = refl; double-6-12-homo s1 s5 = refl
double-6-12-homo s2 s0 = refl; double-6-12-homo s2 s1 = refl; double-6-12-homo s2 s2 = refl
double-6-12-homo s2 s3 = refl; double-6-12-homo s2 s4 = refl; double-6-12-homo s2 s5 = refl
double-6-12-homo s3 s0 = refl; double-6-12-homo s3 s1 = refl; double-6-12-homo s3 s2 = refl
double-6-12-homo s3 s3 = refl; double-6-12-homo s3 s4 = refl; double-6-12-homo s3 s5 = refl
double-6-12-homo s4 s0 = refl; double-6-12-homo s4 s1 = refl; double-6-12-homo s4 s2 = refl
double-6-12-homo s4 s3 = refl; double-6-12-homo s4 s4 = refl; double-6-12-homo s4 s5 = refl
double-6-12-homo s5 s0 = refl; double-6-12-homo s5 s1 = refl; double-6-12-homo s5 s2 = refl
double-6-12-homo s5 s3 = refl; double-6-12-homo s5 s4 = refl; double-6-12-homo s5 s5 = refl

-- Z/12Z → Z/24Z 同态 (144 case 穷举 refl)
double-12-24-homo : ∀ x y → double-12-24 (x +12 y) ≡ double-12-24 x +24 double-12-24 y
double-12-24-homo d0 d0 = refl; double-12-24-homo d0 d1 = refl; double-12-24-homo d0 d2 = refl; double-12-24-homo d0 d3 = refl
double-12-24-homo d0 d4 = refl; double-12-24-homo d0 d5 = refl; double-12-24-homo d0 d6 = refl; double-12-24-homo d0 d7 = refl
double-12-24-homo d0 d8 = refl; double-12-24-homo d0 d9 = refl; double-12-24-homo d0 d10 = refl; double-12-24-homo d0 d11 = refl
double-12-24-homo d1 d0 = refl; double-12-24-homo d1 d1 = refl; double-12-24-homo d1 d2 = refl; double-12-24-homo d1 d3 = refl
double-12-24-homo d1 d4 = refl; double-12-24-homo d1 d5 = refl; double-12-24-homo d1 d6 = refl; double-12-24-homo d1 d7 = refl
double-12-24-homo d1 d8 = refl; double-12-24-homo d1 d9 = refl; double-12-24-homo d1 d10 = refl; double-12-24-homo d1 d11 = refl
double-12-24-homo d2 d0 = refl; double-12-24-homo d2 d1 = refl; double-12-24-homo d2 d2 = refl; double-12-24-homo d2 d3 = refl
double-12-24-homo d2 d4 = refl; double-12-24-homo d2 d5 = refl; double-12-24-homo d2 d6 = refl; double-12-24-homo d2 d7 = refl
double-12-24-homo d2 d8 = refl; double-12-24-homo d2 d9 = refl; double-12-24-homo d2 d10 = refl; double-12-24-homo d2 d11 = refl
double-12-24-homo d3 d0 = refl; double-12-24-homo d3 d1 = refl; double-12-24-homo d3 d2 = refl; double-12-24-homo d3 d3 = refl
double-12-24-homo d3 d4 = refl; double-12-24-homo d3 d5 = refl; double-12-24-homo d3 d6 = refl; double-12-24-homo d3 d7 = refl
double-12-24-homo d3 d8 = refl; double-12-24-homo d3 d9 = refl; double-12-24-homo d3 d10 = refl; double-12-24-homo d3 d11 = refl
double-12-24-homo d4 d0 = refl; double-12-24-homo d4 d1 = refl; double-12-24-homo d4 d2 = refl; double-12-24-homo d4 d3 = refl
double-12-24-homo d4 d4 = refl; double-12-24-homo d4 d5 = refl; double-12-24-homo d4 d6 = refl; double-12-24-homo d4 d7 = refl
double-12-24-homo d4 d8 = refl; double-12-24-homo d4 d9 = refl; double-12-24-homo d4 d10 = refl; double-12-24-homo d4 d11 = refl
double-12-24-homo d5 d0 = refl; double-12-24-homo d5 d1 = refl; double-12-24-homo d5 d2 = refl; double-12-24-homo d5 d3 = refl
double-12-24-homo d5 d4 = refl; double-12-24-homo d5 d5 = refl; double-12-24-homo d5 d6 = refl; double-12-24-homo d5 d7 = refl
double-12-24-homo d5 d8 = refl; double-12-24-homo d5 d9 = refl; double-12-24-homo d5 d10 = refl; double-12-24-homo d5 d11 = refl
double-12-24-homo d6 d0 = refl; double-12-24-homo d6 d1 = refl; double-12-24-homo d6 d2 = refl; double-12-24-homo d6 d3 = refl
double-12-24-homo d6 d4 = refl; double-12-24-homo d6 d5 = refl; double-12-24-homo d6 d6 = refl; double-12-24-homo d6 d7 = refl
double-12-24-homo d6 d8 = refl; double-12-24-homo d6 d9 = refl; double-12-24-homo d6 d10 = refl; double-12-24-homo d6 d11 = refl
double-12-24-homo d7 d0 = refl; double-12-24-homo d7 d1 = refl; double-12-24-homo d7 d2 = refl; double-12-24-homo d7 d3 = refl
double-12-24-homo d7 d4 = refl; double-12-24-homo d7 d5 = refl; double-12-24-homo d7 d6 = refl; double-12-24-homo d7 d7 = refl
double-12-24-homo d7 d8 = refl; double-12-24-homo d7 d9 = refl; double-12-24-homo d7 d10 = refl; double-12-24-homo d7 d11 = refl
double-12-24-homo d8 d0 = refl; double-12-24-homo d8 d1 = refl; double-12-24-homo d8 d2 = refl; double-12-24-homo d8 d3 = refl
double-12-24-homo d8 d4 = refl; double-12-24-homo d8 d5 = refl; double-12-24-homo d8 d6 = refl; double-12-24-homo d8 d7 = refl
double-12-24-homo d8 d8 = refl; double-12-24-homo d8 d9 = refl; double-12-24-homo d8 d10 = refl; double-12-24-homo d8 d11 = refl
double-12-24-homo d9 d0 = refl; double-12-24-homo d9 d1 = refl; double-12-24-homo d9 d2 = refl; double-12-24-homo d9 d3 = refl
double-12-24-homo d9 d4 = refl; double-12-24-homo d9 d5 = refl; double-12-24-homo d9 d6 = refl; double-12-24-homo d9 d7 = refl
double-12-24-homo d9 d8 = refl; double-12-24-homo d9 d9 = refl; double-12-24-homo d9 d10 = refl; double-12-24-homo d9 d11 = refl
double-12-24-homo d10 d0 = refl; double-12-24-homo d10 d1 = refl; double-12-24-homo d10 d2 = refl; double-12-24-homo d10 d3 = refl
double-12-24-homo d10 d4 = refl; double-12-24-homo d10 d5 = refl; double-12-24-homo d10 d6 = refl; double-12-24-homo d10 d7 = refl
double-12-24-homo d10 d8 = refl; double-12-24-homo d10 d9 = refl; double-12-24-homo d10 d10 = refl; double-12-24-homo d10 d11 = refl
double-12-24-homo d11 d0 = refl; double-12-24-homo d11 d1 = refl; double-12-24-homo d11 d2 = refl; double-12-24-homo d11 d3 = refl
double-12-24-homo d11 d4 = refl; double-12-24-homo d11 d5 = refl; double-12-24-homo d11 d6 = refl; double-12-24-homo d11 d7 = refl
double-12-24-homo d11 d8 = refl; double-12-24-homo d11 d9 = refl; double-12-24-homo d11 d10 = refl; double-12-24-homo d11 d11 = refl

--------------------------------------------------------------------------------
-- 7b. 单射性 — 倍频映射是单射（信息保持）
--------------------------------------------------------------------------------

-- 左逆: 从偶数元素恢复原像（奇数元素映射到任意值）

halve-6-3 : Mod6 → Trit
halve-6-3 s0 = T₀; halve-6-3 s1 = T₀; halve-6-3 s2 = T₁
halve-6-3 s3 = T₀; halve-6-3 s4 = T₂; halve-6-3 s5 = T₀

halve-6-3-double : ∀ x → halve-6-3 (double-3-6 x) ≡ x
halve-6-3-double T₀ = refl; halve-6-3-double T₁ = refl; halve-6-3-double T₂ = refl

double-3-6-inj : ∀ x y → double-3-6 x ≡ double-3-6 y → x ≡ y
double-3-6-inj x y p =
  trans (sym (halve-6-3-double x)) (trans (cong halve-6-3 p) (halve-6-3-double y))

halve-12-6 : Duodec → Mod6
halve-12-6 d0 = s0;  halve-12-6 d1 = s0;  halve-12-6 d2 = s1;  halve-12-6 d3 = s0
halve-12-6 d4 = s2;  halve-12-6 d5 = s0;  halve-12-6 d6 = s3;  halve-12-6 d7 = s0
halve-12-6 d8 = s4;  halve-12-6 d9 = s0;  halve-12-6 d10 = s5; halve-12-6 d11 = s0

halve-12-6-double : ∀ x → halve-12-6 (double-6-12 x) ≡ x
halve-12-6-double s0 = refl; halve-12-6-double s1 = refl; halve-12-6-double s2 = refl
halve-12-6-double s3 = refl; halve-12-6-double s4 = refl; halve-12-6-double s5 = refl

double-6-12-inj : ∀ x y → double-6-12 x ≡ double-6-12 y → x ≡ y
double-6-12-inj x y p =
  trans (sym (halve-12-6-double x)) (trans (cong halve-12-6 p) (halve-12-6-double y))

halve-24-12 : Mod24 → Duodec
halve-24-12 t0 = d0;   halve-24-12 t1 = d0;   halve-24-12 t2 = d1;   halve-24-12 t3 = d0
halve-24-12 t4 = d2;   halve-24-12 t5 = d0;   halve-24-12 t6 = d3;   halve-24-12 t7 = d0
halve-24-12 t8 = d4;   halve-24-12 t9 = d0;   halve-24-12 t10 = d5;  halve-24-12 t11 = d0
halve-24-12 t12 = d6;  halve-24-12 t13 = d0;  halve-24-12 t14 = d7;  halve-24-12 t15 = d0
halve-24-12 t16 = d8;  halve-24-12 t17 = d0;  halve-24-12 t18 = d9;  halve-24-12 t19 = d0
halve-24-12 t20 = d10; halve-24-12 t21 = d0;  halve-24-12 t22 = d11; halve-24-12 t23 = d0

halve-24-12-double : ∀ x → halve-24-12 (double-12-24 x) ≡ x
halve-24-12-double d0 = refl;  halve-24-12-double d1 = refl;  halve-24-12-double d2 = refl;  halve-24-12-double d3 = refl
halve-24-12-double d4 = refl;  halve-24-12-double d5 = refl;  halve-24-12-double d6 = refl;  halve-24-12-double d7 = refl
halve-24-12-double d8 = refl;  halve-24-12-double d9 = refl;  halve-24-12-double d10 = refl; halve-24-12-double d11 = refl

double-12-24-inj : ∀ x y → double-12-24 x ≡ double-12-24 y → x ≡ y
double-12-24-inj x y p =
  trans (sym (halve-24-12-double x)) (trans (cong halve-24-12 p) (halve-24-12-double y))

--------------------------------------------------------------------------------
-- 7c. 非满射性 — 奇数元素不在像中（信息丢失于奇数位置）
--------------------------------------------------------------------------------

-- s1 (奇数) 不在 double-3-6 的像中
s1-not-in-image : ∀ x → double-3-6 x ≢ s1
s1-not-in-image T₀ = λ ()
s1-not-in-image T₁ = λ ()
s1-not-in-image T₂ = λ ()

-- d1 (奇数) 不在 double-6-12 的像中
d1-not-in-image : ∀ x → double-6-12 x ≢ d1
d1-not-in-image s0 = λ ()
d1-not-in-image s1 = λ ()
d1-not-in-image s2 = λ ()
d1-not-in-image s3 = λ ()
d1-not-in-image s4 = λ ()
d1-not-in-image s5 = λ ()

-- t1 (奇数) 不在 double-12-24 的像中
t1-not-in-image : ∀ x → double-12-24 x ≢ t1
t1-not-in-image d0 = λ ();  t1-not-in-image d1 = λ ();  t1-not-in-image d2 = λ ();  t1-not-in-image d3 = λ ()
t1-not-in-image d4 = λ ();  t1-not-in-image d5 = λ ();  t1-not-in-image d6 = λ ();  t1-not-in-image d7 = λ ()
t1-not-in-image d8 = λ ();  t1-not-in-image d9 = λ ();  t1-not-in-image d10 = λ (); t1-not-in-image d11 = λ ()

--------------------------------------------------------------------------------
-- 8. 倍频链总结
--------------------------------------------------------------------------------

-- 倍频链的完整代数结构:
--   Z/3Z →[×2] Z/6Z →[×2] Z/12Z →[×2] Z/24Z →[dr] Z/6Z (回绕)
--
-- 每个映射是单射群同态，不是满射
-- 像集 = 偶数元素（信息编码在偶数位置）
-- 数字根回绕: dr(24) = 6，链在 {6, 12} 上周期 2
--
-- 量子纠缠: 测量 x mod 3 确定全链
--   2x mod 6  (entangle-3-6)
--   4x mod 12 (chain-3→12-ℕ)
--   8x mod 24 (chain-3→24-ℕ)

-- 倍频链的像集恰好是偶数元素
-- double-3-6 的像 = {s0, s2, s4}（Z/6Z 中的偶数）
-- double-6-12 的像 = {d0, d2, d4, d6, d8, d10}（Z/12Z 中的偶数）
-- double-12-24 的像 = {t0, t2, ..., t22}（Z/24Z 中的偶数）

-- 像集封闭性验证: 偶数 + 偶数 = 偶数（在像集中封闭）
image-even-closed-3-6 : ∀ x y →
  toℕ₆ (double-3-6 x) % 2 ≡ 0 × toℕ₆ (double-3-6 (x ⊕ y)) % 2 ≡ 0
image-even-closed-3-6 T₀ T₀ = refl , refl
image-even-closed-3-6 T₀ T₁ = refl , refl
image-even-closed-3-6 T₀ T₂ = refl , refl
image-even-closed-3-6 T₁ T₀ = refl , refl
image-even-closed-3-6 T₁ T₁ = refl , refl
image-even-closed-3-6 T₁ T₂ = refl , refl
image-even-closed-3-6 T₂ T₀ = refl , refl
image-even-closed-3-6 T₂ T₁ = refl , refl
image-even-closed-3-6 T₂ T₂ = refl , refl
