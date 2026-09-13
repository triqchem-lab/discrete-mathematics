{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Applied.PacketShiftArithmetic
--
-- 数学背景：递归波包估计中的「移位余量」线性算术。
-- 原文件为 Lean 4 源 `Euler/PacketShiftArithmetic.lean`（命名空间
-- EulerPacketShiftArithmetic），其中 10 条定理全部由 `omega` 自动证明。
-- 本模块把该文件逐条迁移到 Agda。
--
-- 核心原则：
--   1. Lean 的 `a - b` 在 ℕ 上是**截断减法** `∸`，不是有符号减法；
--      因此每条定理都必须先建立下界（如 `1 ≤ i → 80 ≤ 100*i`）才能做等式变换。
--   2. Agda 没有 `omega`，改用「减法工具库 + ≡-Reasoning 代数链」：
--        ∸-shift      (a ∸ x) + c ≡ (a + c) ∸ x              （x ≤ a）
--        ∸-add        (a ∸ x) + (b ∸ y) ≡ (a + b) ∸ (x + y)  （x ≤ a, y ≤ b）
--        ∸-cancel-add (m + n) ∸ (k + n) ≡ m ∸ k               （k ≤ m）
--      这三条把每条定理的 LHS 归约成 `100*(i+j) ∸ c` 的规范形。
--   3. 定义保持与 Lean 完全一致（`100*p-80` 用 `100 * p ∸ 80`），不改成无截断形式；
--      截断被下界假设「消去」，因此每条定理是**等式**或一步 `∸-mono`。
--   4. 0 postulate / 0 hole：全部结论由 Data.Nat.Properties 的引理组合而成。
--
-- 包含：H/M/HF/MF 四个移位函数；减法工具 3 条；Lean 原文件 10 条定理逐条迁移；
--       具体点对抗验证 8 条。

module Sovereign.Applied.PacketShiftArithmetic where

open import Data.Nat using (ℕ; _+_; _*_; _∸_; _≤_; s≤s; z≤n)
open import Data.Nat.Properties using (
  +-comm; +-assoc; +-identityʳ; *-distribˡ-+; *-distribʳ-+; *-distribˡ-∸; *-monoʳ-≤;
  +-∸-assoc; ∸-+-assoc; ∸-mono; m∸n+n≡m; m+n∸n≡m; n∸n≡0;
  m≤m+n; ≤-trans; ≤-refl; ≤-reflexive; +-mono-≤; +-monoʳ-≤; m+n≤o⇒m≤o∸n)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; subst; module ≡-Reasoning)

--------------------------------------------------------------------------------
-- §1. 四个移位函数（与 Lean 定义逐字对应）
--------------------------------------------------------------------------------

-- Lean: def highShift (p : ℕ) : ℕ := 100*p-80
H : ℕ → ℕ
H p = 100 * p ∸ 80

-- Lean: def meanShift (p : ℕ) : ℕ := 100*p-140
M : ℕ → ℕ
M p = 100 * p ∸ 140

-- Lean: def highForceShift (p : ℕ) : ℕ := highShift p-10
HF : ℕ → ℕ
HF p = H p ∸ 10

-- Lean: def meanForceShift (p : ℕ) : ℕ := meanShift p-10
MF : ℕ → ℕ
MF p = M p ∸ 10

--------------------------------------------------------------------------------
-- §2. 减法工具库（Agda 替代 omega 的三条核心引理）
--------------------------------------------------------------------------------

-- 减法加常数外提：x ≤ a ⟹ (a ∸ x) + c ≡ (a + c) ∸ x
-- 直观：先减再加 = 先加再减（下界保证不截断）
∸-shift : ∀ a x c → x ≤ a → (a ∸ x) + c ≡ (a + c) ∸ x
∸-shift a x c x≤a = sym (begin
  (a + c) ∸ x
    ≡⟨ cong (_∸ x) (cong (_+ c) (sym (m∸n+n≡m {m = a} {n = x} x≤a))) ⟩
  (((a ∸ x) + x) + c) ∸ x
    ≡⟨ cong (_∸ x) (+-assoc (a ∸ x) x c) ⟩
  ((a ∸ x) + (x + c)) ∸ x
    ≡⟨ +-∸-assoc (a ∸ x) (m≤m+n x c) ⟩
  (a ∸ x) + ((x + c) ∸ x)
    ≡⟨ cong ((a ∸ x) +_) (trans (cong (_∸ x) (+-comm x c)) (m+n∸n≡m c x)) ⟩
  (a ∸ x) + c
  ∎)
  where open ≡-Reasoning

-- 两减法合并：x ≤ a，y ≤ b ⟹ (a ∸ x) + (b ∸ y) ≡ (a + b) ∸ (x + y)
∸-add : ∀ a b x y → x ≤ a → y ≤ b → (a ∸ x) + (b ∸ y) ≡ (a + b) ∸ (x + y)
∸-add a b x y x≤a y≤b = begin
  (a ∸ x) + (b ∸ y)
    ≡⟨ +-comm (a ∸ x) (b ∸ y) ⟩
  (b ∸ y) + (a ∸ x)
    ≡⟨ ∸-shift b y (a ∸ x) y≤b ⟩
  (b + (a ∸ x)) ∸ y
    ≡⟨ cong (_∸ y) (+-comm b (a ∸ x)) ⟩
  ((a ∸ x) + b) ∸ y
    ≡⟨ cong (_∸ y) (∸-shift a x b x≤a) ⟩
  ((a + b) ∸ x) ∸ y
    ≡⟨ ∸-+-assoc (a + b) x y ⟩
  (a + b) ∸ (x + y)
  ∎
  where open ≡-Reasoning

-- 同增同减相消：k ≤ m ⟹ (m + n) ∸ (k + n) ≡ m ∸ k
∸-cancel-add : ∀ m n k → k ≤ m → (m + n) ∸ (k + n) ≡ m ∸ k
∸-cancel-add m n k k≤m = begin
  (m + n) ∸ (k + n)
    ≡⟨ cong (_∸ (k + n)) (cong (_+ n) (sym (m∸n+n≡m {m = m} {n = k} k≤m))) ⟩
  (((m ∸ k) + k) + n) ∸ (k + n)
    ≡⟨ cong (_∸ (k + n)) (+-assoc (m ∸ k) k n) ⟩
  ((m ∸ k) + (k + n)) ∸ (k + n)
    ≡⟨ +-∸-assoc (m ∸ k) {n = k + n} {o = k + n} ≤-refl ⟩
  (m ∸ k) + ((k + n) ∸ (k + n))
    ≡⟨ cong ((m ∸ k) +_) (n∸n≡0 (k + n)) ⟩
  (m ∸ k) + 0
    ≡⟨ +-identityʳ (m ∸ k) ⟩
  m ∸ k
  ∎
  where open ≡-Reasoning

-- 两个被加项各自改写（避免裸 cong₂ 在 _+_ 上留下元变量）
cong₂-add : ∀ {a b c d} → a ≡ b → c ≡ d → a + c ≡ b + d
cong₂-add refl refl = refl

--------------------------------------------------------------------------------
-- §3. 规范形引理：MF/HF 化到单层减法
--------------------------------------------------------------------------------

-- MF p ≡ 100*p ∸ 150
MF-lemma : ∀ p → MF p ≡ 100 * p ∸ 150
MF-lemma p = ∸-+-assoc (100 * p) 140 10

-- HF p ≡ 100*p ∸ 90
HF-lemma : ∀ p → HF p ≡ 100 * p ∸ 90
HF-lemma p = ∸-+-assoc (100 * p) 80 10

-- 带 `+ 2 + 8` 的 LHS 与带 `+ 10` 的 LHS 相等（≡-Reasoning 起手步）
-- 注意：Agda 的 `_+_` 是内建 primNatPlus，对变量第一元不归约，
-- 因此 `a + b + 2 + 8` 与 `a + b + 10` **不**定义性相等，须用 +-assoc 归组。
+2+8≡+10 : ∀ a b → a + b + 2 + 8 ≡ a + b + 10
+2+8≡+10 a b = +-assoc (a + b) 2 8

-- 单被加项版本（previous_linear_room 用）
+2+8≡+10' : ∀ a → a + 2 + 8 ≡ a + 10
+2+8≡+10' a = +-assoc a 2 8

--------------------------------------------------------------------------------
-- §4. 下界工具：由「元素个数下界」推出「移位值下界」
--------------------------------------------------------------------------------

-- 常数下界：m ≤ m + n（Agda 会归一化右端，故可当具体数值界使用）
80≤100 : 80 ≤ 100
80≤100 = m≤m+n 80 20

140≤200 : 140 ≤ 200
140≤200 = m≤m+n 140 60

150≤200 : 150 ≤ 200
150≤200 = m≤m+n 150 50

160≤200 : 160 ≤ 200
160≤200 = m≤m+n 160 40

180≤200 : 180 ≤ 200
180≤200 = m≤m+n 180 20

170≤200 : 170 ≤ 200
170≤200 = m≤m+n 170 30

210≤300 : 210 ≤ 300
210≤300 = m≤m+n 210 90

220≤300 : 220 ≤ 300
220≤300 = m≤m+n 220 80

250≤300 : 250 ≤ 300
250≤300 = m≤m+n 250 50

260≤300 : 260 ≤ 300
260≤300 = m≤m+n 260 40

270≤300 : 270 ≤ 300
270≤300 = m≤m+n 270 30

360≤400 : 360 ≤ 400
360≤400 = m≤m+n 360 40

-- 减法对减数单调（被减数固定）：d ≤ c ⟹ m ∸ c ≤ m ∸ d
-- 包装 ∸-mono 以免 Agda 对内建 _∸_ 做逆推（内建函数不可逆推）
∸-mono-r : ∀ m c d → d ≤ c → m ∸ c ≤ m ∸ d
∸-mono-r m c d d≤c = ∸-mono {x = m} {y = m} {u = c} {v = d} ≤-refl d≤c

-- 100 的单调性
100*mono : ∀ {a b} → a ≤ b → 100 * a ≤ 100 * b
100*mono a≤b = *-monoʳ-≤ 100 a≤b

-- 1 ≤ i ⟹ 80 ≤ 100*i
80≤100i : ∀ i → 1 ≤ i → 80 ≤ 100 * i
80≤100i i 1≤i = ≤-trans 80≤100 (100*mono 1≤i)

-- 2 ≤ i ⟹ 140 ≤ 100*i
140≤100i : ∀ i → 2 ≤ i → 140 ≤ 100 * i
140≤100i i 2≤i = ≤-trans 140≤200 (100*mono 2≤i)

-- 2 ≤ i ⟹ 180 ≤ 100*i
180≤100i : ∀ i → 2 ≤ i → 180 ≤ 100 * i
180≤100i i 2≤i = ≤-trans 180≤200 (100*mono 2≤i)

-- d ≤ i+j 且 c ≤ 100*d ⟹ c ≤ 100*(i+j)
boundij : ∀ i j d c → d ≤ i + j → c ≤ 100 * d → c ≤ 100 * (i + j)
boundij i j d c d≤ij c≤100d = ≤-trans c≤100d (100*mono d≤ij)

-- 2 ≤ 3（用于把 2 ≤ i 提升为 3 ≤ i+j 的分量）
2≤3 : 2 ≤ 3
2≤3 = s≤s (s≤s z≤n)

3≤4 : 3 ≤ 4
3≤4 = s≤s (s≤s (s≤s z≤n))

--------------------------------------------------------------------------------
-- §5. Lean 原文件 10 条定理逐条迁移
--------------------------------------------------------------------------------

-- Lean: theorem primary_shift : highShift 1 = 20 := rfl
primary_shift : H 1 ≡ 20
primary_shift = refl

-- Lean: slow_high_high_room (i j p) (hi : 1 ≤ i) (hj : 1 ≤ j) (hp : i+j=p) :
--   highShift i + highShift j + 2 + 8 ≤ meanForceShift p
-- 下界：80 ≤ 100i, 80 ≤ 100j；i+j ≥ 2 ⟹ 100(i+j) ≥ 200 ≥ 160, 150
slow_high_high_room-core : ∀ i j → 1 ≤ i → 1 ≤ j → H i + H j + 2 + 8 ≤ MF (i + j)
slow_high_high_room-core i j hi hj = ≤-reflexive (begin
  H i + H j + 2 + 8
    ≡⟨ +2+8≡+10 (H i) (H j) ⟩
  H i + H j + 10
    ≡⟨ cong (_+ 10) (∸-add (100 * i) (100 * j) 80 80 (80≤100i i hi) (80≤100i j hj)) ⟩
  (100 * i + 100 * j) ∸ 160 + 10
    ≡⟨ cong (λ z → (z ∸ 160) + 10) (sym (*-distribˡ-+ 100 i j)) ⟩
  (100 * (i + j) ∸ 160) + 10
    ≡⟨ ∸-shift (100 * (i + j)) 160 10
         (boundij i j 2 160 (+-mono-≤ hi hj) 160≤200) ⟩
  (100 * (i + j) + 10) ∸ 160
    ≡⟨ ∸-cancel-add (100 * (i + j)) 10 150
         (boundij i j 2 150 (+-mono-≤ hi hj) 150≤200) ⟩
  100 * (i + j) ∸ 150
    ≡⟨ sym (MF-lemma (i + j)) ⟩
  MF (i + j)
  ∎)
  where open ≡-Reasoning

slow_high_high_room : ∀ i j p → 1 ≤ i → 1 ≤ j → i + j ≡ p
                    → H i + H j + 2 + 8 ≤ MF p
slow_high_high_room i j p hi hj hp =
  subst (λ z → H i + H j + 2 + 8 ≤ MF z) hp (slow_high_high_room-core i j hi hj)

-- Lean: slow_mean_high_room (hi : 2 ≤ i) (hj : 1 ≤ j) (hp : i+j=p) :
--   meanShift i + highShift j + 2 + 8 ≤ meanForceShift p
-- 下界：140 ≤ 100i, 80 ≤ 100j；i+j ≥ 3 ⟹ 100(i+j) ≥ 300
slow_mean_high_room-core : ∀ i j → 2 ≤ i → 1 ≤ j → M i + H j + 2 + 8 ≤ MF (i + j)
slow_mean_high_room-core i j hi hj = ≤-trans
  (≤-reflexive (begin
    M i + H j + 2 + 8
      ≡⟨ +2+8≡+10 (M i) (H j) ⟩
    M i + H j + 10
      ≡⟨ cong (_+ 10) (∸-add (100 * i) (100 * j) 140 80 (140≤100i i hi) (80≤100i j hj)) ⟩
    (100 * i + 100 * j) ∸ 220 + 10
      ≡⟨ cong (λ z → (z ∸ 220) + 10) (sym (*-distribˡ-+ 100 i j)) ⟩
    (100 * (i + j) ∸ 220) + 10
      ≡⟨ ∸-shift (100 * (i + j)) 220 10
           (boundij i j 3 220 (+-mono-≤ hi hj) 220≤300) ⟩
    (100 * (i + j) + 10) ∸ 220
      ≡⟨ ∸-cancel-add (100 * (i + j)) 10 210
           (boundij i j 3 210 (+-mono-≤ hi hj) 210≤300) ⟩
    100 * (i + j) ∸ 210
    ∎))
  (≤-trans
    (∸-mono-r (100 * (i + j)) 210 150 (m≤m+n 150 60))
    (≤-reflexive (sym (MF-lemma (i + j)))))
  where open ≡-Reasoning

slow_mean_high_room : ∀ i j p → 2 ≤ i → 1 ≤ j → i + j ≡ p
                    → M i + H j + 2 + 8 ≤ MF p
slow_mean_high_room i j p hi hj hp =
  subst (λ z → M i + H j + 2 + 8 ≤ MF z) hp (slow_mean_high_room-core i j hi hj)

-- Lean: slow_mean_mean_room (hi : 2 ≤ i) (hj : 2 ≤ j) (hp : i+j=p) :
--   meanShift i + meanShift j + 2 + 8 ≤ meanForceShift p
-- 下界：140 ≤ 100i, 140 ≤ 100j；i+j ≥ 4 ⟹ 100(i+j) ≥ 400
slow_mean_mean_room-core : ∀ i j → 2 ≤ i → 2 ≤ j → M i + M j + 2 + 8 ≤ MF (i + j)
slow_mean_mean_room-core i j hi hj = ≤-trans
  (≤-reflexive (begin
    M i + M j + 2 + 8
      ≡⟨ +2+8≡+10 (M i) (M j) ⟩
    M i + M j + 10
      ≡⟨ cong (_+ 10) (∸-add (100 * i) (100 * j) 140 140 (140≤100i i hi) (140≤100i j hj)) ⟩
    (100 * i + 100 * j) ∸ 280 + 10
      ≡⟨ cong (λ z → (z ∸ 280) + 10) (sym (*-distribˡ-+ 100 i j)) ⟩
    (100 * (i + j) ∸ 280) + 10
      ≡⟨ ∸-shift (100 * (i + j)) 280 10
           (boundij i j 4 280 (+-mono-≤ hi hj) (m≤m+n 280 120)) ⟩
    (100 * (i + j) + 10) ∸ 280
      ≡⟨ ∸-cancel-add (100 * (i + j)) 10 270
           (boundij i j 3 270 (≤-trans 3≤4 (+-mono-≤ hi hj)) 270≤300) ⟩
    100 * (i + j) ∸ 270
    ∎))
  (≤-trans
    (∸-mono-r (100 * (i + j)) 270 150 (m≤m+n 150 120))
    (≤-reflexive (sym (MF-lemma (i + j)))))
  where open ≡-Reasoning

slow_mean_mean_room : ∀ i j p → 2 ≤ i → 2 ≤ j → i + j ≡ p
                    → M i + M j + 2 + 8 ≤ MF p
slow_mean_mean_room i j p hi hj hp =
  subst (λ z → M i + M j + 2 + 8 ≤ MF z) hp (slow_mean_mean_room-core i j hi hj)

-- 修正子引理：H (i ∸ 1) ≡ 100*i ∸ 180
-- 用 *-distribˡ-∸ 把 100*(i∸1) 化为 100*i ∸ 100，再 ∸-+-assoc 合并
H-pred : ∀ i → H (i ∸ 1) ≡ 100 * i ∸ 180
H-pred i = begin
  H (i ∸ 1)
    ≡⟨ cong (_∸ 80) (*-distribˡ-∸ 100 i 1) ⟩
  (100 * i ∸ 100) ∸ 80
    ≡⟨ ∸-+-assoc (100 * i) 100 80 ⟩
  100 * i ∸ 180
  ∎
  where open ≡-Reasoning

-- 修正子引理：HF (k ∸ 1) ≡ 100*k ∸ 190
HF-pred : ∀ k → HF (k ∸ 1) ≡ 100 * k ∸ 190
HF-pred k = begin
  HF (k ∸ 1)
    ≡⟨ cong (λ z → (z ∸ 80) ∸ 10) (*-distribˡ-∸ 100 k 1) ⟩
  ((100 * k ∸ 100) ∸ 80) ∸ 10
    ≡⟨ cong (_∸ 10) (∸-+-assoc (100 * k) 100 80) ⟩
  (100 * k ∸ 180) ∸ 10
    ≡⟨ ∸-+-assoc (100 * k) 180 10 ⟩
  100 * k ∸ 190
  ∎
  where open ≡-Reasoning

-- 修正子引理：MF (k ∸ 1) ≡ 100*k ∸ 250
MF-pred : ∀ k → MF (k ∸ 1) ≡ 100 * k ∸ 250
MF-pred k = begin
  MF (k ∸ 1)
    ≡⟨ cong (λ z → (z ∸ 140) ∸ 10) (*-distribˡ-∸ 100 k 1) ⟩
  ((100 * k ∸ 100) ∸ 140) ∸ 10
    ≡⟨ cong (_∸ 10) (∸-+-assoc (100 * k) 100 140) ⟩
  (100 * k ∸ 240) ∸ 10
    ≡⟨ ∸-+-assoc (100 * k) 240 10 ⟩
  100 * k ∸ 250
  ∎
  where open ≡-Reasoning

-- fast 三定理的换元引理：i+j ≡ p+1 ⟹ (i+j) ∸ 1 ≡ p
pred-ij : ∀ i j p → i + j ≡ p + 1 → (i + j) ∸ 1 ≡ p
pred-ij i j p hp = trans (cong (_∸ 1) hp) (m+n∸n≡m p 1)

-- Lean: fast_mean_high_room (hi : 2 ≤ i) (hj : 1 ≤ j) (hp : i+j=p+1) :
--   meanShift i + highShift j + 2 + 8 ≤ highForceShift p
-- 注意 RHS 是 HF p，而 i+j = p+1 ⟹ p = (i+j)∸1，故核心命题用 (i+j)∸1 表述
fast_mean_high_room-core : ∀ i j → 2 ≤ i → 1 ≤ j
                         → M i + H j + 2 + 8 ≤ HF ((i + j) ∸ 1)
fast_mean_high_room-core i j hi hj = ≤-trans
  (≤-reflexive (begin
    M i + H j + 2 + 8
      ≡⟨ +2+8≡+10 (M i) (H j) ⟩
    M i + H j + 10
      ≡⟨ cong (_+ 10) (∸-add (100 * i) (100 * j) 140 80 (140≤100i i hi) (80≤100i j hj)) ⟩
    (100 * i + 100 * j) ∸ 220 + 10
      ≡⟨ cong (λ z → (z ∸ 220) + 10) (sym (*-distribˡ-+ 100 i j)) ⟩
    (100 * (i + j) ∸ 220) + 10
      ≡⟨ ∸-shift (100 * (i + j)) 220 10
           (boundij i j 3 220 (+-mono-≤ hi hj) 220≤300) ⟩
    (100 * (i + j) + 10) ∸ 220
      ≡⟨ ∸-cancel-add (100 * (i + j)) 10 210
           (boundij i j 3 210 (+-mono-≤ hi hj) 210≤300) ⟩
    100 * (i + j) ∸ 210
    ∎))
  (≤-trans
    (∸-mono-r (100 * (i + j)) 210 190 (m≤m+n 190 20))
    (≤-reflexive (sym (HF-pred (i + j)))))
  where open ≡-Reasoning

fast_mean_high_room : ∀ i j p → 2 ≤ i → 1 ≤ j → i + j ≡ p + 1
                    → M i + H j + 2 + 8 ≤ HF p
fast_mean_high_room i j p hi hj hp =
  subst (λ z → M i + H j + 2 + 8 ≤ HF z) (pred-ij i j p hp)
        (fast_mean_high_room-core i j hi hj)

-- Lean: fast_corrector_high_room (hi : 2 ≤ i) (hj : 1 ≤ j) (hp : i+j=p+1) :
--   highShift (i-1) + highShift j + 2 + 8 ≤ meanForceShift p
fast_corrector_high_room-core : ∀ i j → 2 ≤ i → 1 ≤ j
                              → H (i ∸ 1) + H j + 2 + 8 ≤ MF ((i + j) ∸ 1)
fast_corrector_high_room-core i j hi hj = ≤-reflexive (begin
  H (i ∸ 1) + H j + 2 + 8
    ≡⟨ +2+8≡+10 (H (i ∸ 1)) (H j) ⟩
  H (i ∸ 1) + H j + 10
    ≡⟨ cong (_+ 10) (cong₂-add (H-pred i) refl) ⟩
  (100 * i ∸ 180) + (100 * j ∸ 80) + 10
    ≡⟨ cong (_+ 10) (∸-add (100 * i) (100 * j) 180 80 (180≤100i i hi) (80≤100i j hj)) ⟩
  (100 * i + 100 * j) ∸ 260 + 10
    ≡⟨ cong (λ z → (z ∸ 260) + 10) (sym (*-distribˡ-+ 100 i j)) ⟩
  (100 * (i + j) ∸ 260) + 10
    ≡⟨ ∸-shift (100 * (i + j)) 260 10
         (boundij i j 3 260 (+-mono-≤ hi hj) 260≤300) ⟩
  (100 * (i + j) + 10) ∸ 260
    ≡⟨ ∸-cancel-add (100 * (i + j)) 10 250
         (boundij i j 3 250 (+-mono-≤ hi hj) 250≤300) ⟩
  100 * (i + j) ∸ 250
    ≡⟨ sym (MF-pred (i + j)) ⟩
  MF ((i + j) ∸ 1)
  ∎)
  where open ≡-Reasoning

fast_corrector_high_room : ∀ i j p → 2 ≤ i → 1 ≤ j → i + j ≡ p + 1
                         → H (i ∸ 1) + H j + 2 + 8 ≤ MF p
fast_corrector_high_room i j p hi hj hp =
  subst (λ z → H (i ∸ 1) + H j + 2 + 8 ≤ MF z) (pred-ij i j p hp)
        (fast_corrector_high_room-core i j hi hj)

-- Lean: fast_corrector_corrector_room (hi : 2 ≤ i) (hj : 2 ≤ j) (hp : i+j=p+1) :
--   highShift (i-1) + highShift (j-1) + 2 + 8 ≤ meanForceShift p
fast_corrector_corrector_room-core : ∀ i j → 2 ≤ i → 2 ≤ j
                                   → H (i ∸ 1) + H (j ∸ 1) + 2 + 8 ≤ MF ((i + j) ∸ 1)
fast_corrector_corrector_room-core i j hi hj = ≤-trans
  (≤-reflexive (begin
    H (i ∸ 1) + H (j ∸ 1) + 2 + 8
      ≡⟨ +2+8≡+10 (H (i ∸ 1)) (H (j ∸ 1)) ⟩
    H (i ∸ 1) + H (j ∸ 1) + 10
      ≡⟨ cong (_+ 10) (cong₂-add (H-pred i) (H-pred j)) ⟩
    (100 * i ∸ 180) + (100 * j ∸ 180) + 10
      ≡⟨ cong (_+ 10) (∸-add (100 * i) (100 * j) 180 180 (180≤100i i hi) (180≤100i j hj)) ⟩
    (100 * i + 100 * j) ∸ 360 + 10
      ≡⟨ cong (λ z → (z ∸ 360) + 10) (sym (*-distribˡ-+ 100 i j)) ⟩
    (100 * (i + j) ∸ 360) + 10
      ≡⟨ ∸-shift (100 * (i + j)) 360 10
           (boundij i j 4 360 (+-mono-≤ hi hj) 360≤400) ⟩
    (100 * (i + j) + 10) ∸ 360
      ≡⟨ ∸-cancel-add (100 * (i + j)) 10 350
           (boundij i j 4 350 (+-mono-≤ hi hj) (m≤m+n 350 50)) ⟩
    100 * (i + j) ∸ 350
    ∎))
  (≤-trans
    (∸-mono-r (100 * (i + j)) 350 250 (m≤m+n 250 100))
    (≤-reflexive (sym (MF-pred (i + j)))))
  where open ≡-Reasoning

fast_corrector_corrector_room : ∀ i j p → 2 ≤ i → 2 ≤ j → i + j ≡ p + 1
                              → H (i ∸ 1) + H (j ∸ 1) + 2 + 8 ≤ MF p
fast_corrector_corrector_room i j p hi hj hp =
  subst (λ z → H (i ∸ 1) + H (j ∸ 1) + 2 + 8 ≤ MF z) (pred-ij i j p hp)
        (fast_corrector_corrector_room-core i j hi hj)

-- Lean: previous_linear_room (p) (hp : 2 ≤ p) :
--   highShift (p-1) + 2 + 8 ≤ meanForceShift p
previous_linear_room : ∀ p → 2 ≤ p → H (p ∸ 1) + 2 + 8 ≤ MF p
previous_linear_room p hp = ≤-trans
  (≤-reflexive (begin
    H (p ∸ 1) + 2 + 8
      ≡⟨ +2+8≡+10' (H (p ∸ 1)) ⟩
    H (p ∸ 1) + 10
      ≡⟨ cong (_+ 10) (H-pred p) ⟩
    (100 * p ∸ 180) + 10
      ≡⟨ ∸-shift (100 * p) 180 10 (≤-trans 180≤200 (100*mono hp)) ⟩
    (100 * p + 10) ∸ 180
      ≡⟨ ∸-cancel-add (100 * p) 10 170 (≤-trans 170≤200 (100*mono hp)) ⟩
    100 * p ∸ 170
    ∎))
  (≤-trans
    (∸-mono-r (100 * p) 170 150 (m≤m+n 150 20))
    (≤-reflexive (sym (MF-lemma p))))
  where open ≡-Reasoning

-- Lean: mean_force_le_high_force (p) : meanForceShift p ≤ highForceShift p
mean_force_le_high_force : ∀ p → MF p ≤ HF p
mean_force_le_high_force p = ≤-trans
  (≤-reflexive (MF-lemma p))
  (≤-trans
    (∸-mono-r (100 * p) 150 90 (m≤m+n 90 60))
    (≤-reflexive (sym (HF-lemma p))))

-- Lean: force_shift_dominates_grade (p) (hp : 2 ≤ p) :
--   25*p ≤ meanForceShift p ∧ 25*p ≤ highForceShift p
-- 25*p + 150 ≤ 25*p + 75*p = 100*p，再用 m+n≤o⇒m≤o∸n
25p+150≤100p : ∀ p → 2 ≤ p → 25 * p + 150 ≤ 100 * p
25p+150≤100p p hp = ≤-trans
  (+-monoʳ-≤ (25 * p) 75*mono)
  (≤-reflexive 25p+75p≡100p)
  where
    open ≡-Reasoning
    75*mono : 150 ≤ 75 * p
    75*mono = *-monoʳ-≤ 75 hp
    25p+75p≡100p : 25 * p + 75 * p ≡ 100 * p
    25p+75p≡100p = sym (*-distribʳ-+ p 25 75)

force_shift_dominates_grade : ∀ p → 2 ≤ p → 25 * p ≤ MF p × 25 * p ≤ HF p
force_shift_dominates_grade p hp =
  ( grade≤MF , ≤-trans grade≤MF (mean_force_le_high_force p) )
  where
    grade≤100p∸150 : 25 * p ≤ 100 * p ∸ 150
    grade≤100p∸150 = m+n≤o⇒m≤o∸n (25 * p) {n = 150} {o = 100 * p} (25p+150≤100p p hp)

    grade≤MF : 25 * p ≤ MF p
    grade≤MF = subst (λ z → 25 * p ≤ z) (sym (MF-lemma p)) grade≤100p∸150

--------------------------------------------------------------------------------
-- §6. 对抗验证：具体点上的独立 refl 计算（与定理实例交叉比对）
--------------------------------------------------------------------------------

_H2 : H 2 ≡ 120
_H2 = refl

_H3 : H 3 ≡ 220
_H3 = refl

_M2 : M 2 ≡ 60
_M2 = refl

_MF3 : MF 3 ≡ 150
_MF3 = refl

_HF3 : HF 3 ≡ 210
_HF3 = refl

-- slow_high_high_room 在 (i,j,p)=(1,2,3)：H 1 + H 2 + 2 + 8 = 20 + 120 + 10 = 150 ≤ 150
_room-1-2 : H 1 + H 2 + 2 + 8 ≤ MF 3
_room-1-2 = ≤-refl

-- mean_force_le_high_force 在 p=3：MF 3 = 150 ≤ 210 = HF 3
_grade-3 : 25 * 3 ≤ MF 3 × 25 * 3 ≤ HF 3
_grade-3 = (m≤m+n 75 75 , m≤m+n 75 135)

-- previous_linear_room 在 p=2：H 1 + 10 = 30 ≤ MF 2 = 50
_prev-2 : H (2 ∸ 1) + 2 + 8 ≤ MF 2
_prev-2 = m≤m+n 30 20
