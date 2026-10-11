{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Analysis.UniformProb
-- 离散均匀概率空间——符号形定理层（计数承载）+ GF(3)² 实例核对层
--
-- 数学背景：Ω = Fin n 均匀样本空间，事件 = 谓词 (Fin n → Bool)，概率以**计数承载**
--   （单点权重 1、总量 n）——避开有理数机件（宪法禁浮点）。三定理符号形：
--   ① normalization（∑μ ≡ total 形）：全空间计数 ≡ n；
--   ② additivity：互斥事件并的计数 = 两计数之和；
--   ③ independence（乘法形）：积空间 Fin m × Fin n 上独立事件的计数 = 计数积。
--   原 GF(3)² 七件数值 refl 点（9/3/3 网格演示）降为**核对层**（演示件非定理），
--   与符号定理逐点对账（9 = 3×3 积空间实例）。
--
-- 核心原则：
--   1. 计数承载：μ 以 ℕ 计数形（weight=1/total=n），禁有理数/浮点（宪法禁令）；
--   2. 符号定理优先（全称 n/m 形），数值点只作实例核对（不冒充定理——深度审核判据）；
--   3. 诚实边界：离散均匀分布实例核——非测度论概率（无可数可加性/期望/条件概率理论）；
--   4. 归纳边界遵守（Fin 构造子归纳；Boolean 辅件 ≤4 case；每证明项链 ≤3）。
--
-- 包含：count/countP 计数核、normalization/additivity/independence 三符号定理、
--       if-or/if-dist/count-∧-const/+4swap 计数代数辅件、GF(3)² 核对层（原七点 + 三符号对账）

module Sovereign.Application.UniformProb where

open import Data.Nat using (ℕ; zero; suc; _*_; _+_)
open import Data.Nat.Properties using (+-assoc; +-comm)
open import Data.Bool using (Bool; true; false; _∨_; _∧_; if_then_else_)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂; module ≡-Reasoning)

-- ────────────────────────────────────────────────────────────────────
-- §1 计数核（基础件层）
--   count  ：Fin n 上谓词的真值计数（归纳于 n）
--   countP ：积空间 Fin m × Fin n 上谓词的真值计数（归纳于 m）
-- ────────────────────────────────────────────────────────────────────

count : ∀ {n} → (Fin n → Bool) → ℕ
count {zero} _ = 0
count {suc n} p = (if p fzero then 1 else 0) + count (λ i → p (fsuc i))

countP : ∀ {m n} → (Fin m × Fin n → Bool) → ℕ
countP {zero} _ = 0
countP {suc m} {n} p = count (λ j → p (fzero , j)) + countP (λ x → p (fsuc (proj₁ x) , proj₂ x))

-- ────────────────────────────────────────────────────────────────────
-- §2 计数代数辅件（主引理层）
-- ────────────────────────────────────────────────────────────────────

-- 互斥布尔并的指示计数可加：a ∧ b ≡ false ⟹ 1_{a∨b} ≡ 1_a + 1_b
if-or : (a b : Bool) → (a ∧ b) ≡ false
      → (if (a ∨ b) then 1 else 0) ≡ (if a then 1 else 0) + (if b then 1 else 0)
if-or true true ()
if-or true false _ = refl
if-or false true _ = refl
if-or false false _ = refl

-- 四项交换：(a+b)+(c+d) ≡ (a+c)+(b+d)（代数重排——策略 B 推导链）
+4swap : (a b c d : ℕ) → (a + b) + (c + d) ≡ (a + c) + (b + d)
+4swap a b c d = begin
  (a + b) + (c + d)  ≡⟨ +-assoc a b (c + d) ⟩       -- (A+B)+C → A+(B+C) [结合律]
  a + (b + (c + d))  ≡⟨ cong (a +_) (sym (+-assoc b c d)) ⟩  -- 内层反用结合 [→(B+C)+D]
  a + ((b + c) + d)  ≡⟨ cong (λ w → a + (w + d)) (+-comm b c) ⟩  -- 中段换序 [交换律]
  a + ((c + b) + d)  ≡⟨ cong (a +_) (+-assoc c b d) ⟩  -- 内层再结合 [→C+(B+D)]
  a + (c + (b + d))  ≡⟨ sym (+-assoc a c (b + d)) ⟩   -- 整体反用结合 [→(A+C)+B+D]
  (a + c) + (b + d)  ∎
  where open ≡-Reasoning

-- 常布尔与计数抽取：a ∧ B 的计数 = a=真 ? |B| : 0
count-∧-const : ∀ {n} (a : Bool) (B : Fin n → Bool)
             → count (λ j → a ∧ B j) ≡ (if a then count B else 0)
count-∧-const {zero} true B = refl
count-∧-const {zero} false B = refl
count-∧-const {suc n} true B = refl          -- true ∧ x = x（定义相等直接闭合）
count-∧-const {suc n} false B = count-∧-const false (λ i → B (fsuc i))

-- 布尔分支分配：(a ? c : 0) + r·c ≡ ((a ? 1 : 0) + r)·c
if-dist : (a : Bool) (c r : ℕ)
        → (if a then c else 0) + r * c ≡ ((if a then 1 else 0) + r) * c
if-dist true c r = refl
if-dist false c r = refl

-- ────────────────────────────────────────────────────────────────────
-- §3 符号形定理（组合层）
-- ────────────────────────────────────────────────────────────────────

-- ① normalization：全空间计数 ≡ n（∑μ ≡ total）
normalization : ∀ (n : ℕ) → count {n} (λ _ → true) ≡ n
normalization zero = refl
normalization (suc n) = cong suc (normalization n)   -- 1 + IH ≡ suc n（1+x = suc x 定义相等）

-- ② additivity：互斥事件并的计数 = 计数和
additivity : ∀ {n} (A B : Fin n → Bool)
           → (∀ x → (A x ∧ B x) ≡ false)
           → count (λ x → A x ∨ B x) ≡ count A + count B
additivity {zero} A B disj = refl
additivity {suc n} A B disj =
  -- LHS 归约：(1_{a∨b}) + |A'∨B'| —[if-or | IH]→ (1_a+1_b) + (|A'|+|B'|)
  -- RHS 展开：(1_a+|A'|) + (1_b+|B'|) —[+4swap]→ 同上
  trans (cong₂ _+_ (if-or (A fzero) (B fzero) (disj fzero))
                   (additivity (λ i → A (fsuc i)) (λ i → B (fsuc i)) (λ i → disj (fsuc i))))
        (+4swap (if A fzero then 1 else 0) (if B fzero then 1 else 0)
                (count (λ i → A (fsuc i))) (count (λ i → B (fsuc i))))

-- ③ independence：积空间独立事件的计数 = 计数积（乘法形）
independence : ∀ {m n} (A : Fin m → Bool) (B : Fin n → Bool)
             → countP (λ x → A (proj₁ x) ∧ B (proj₂ x)) ≡ count A * count B
independence {zero} A B = refl
independence {suc m} {n} A B =
  -- LHS 归约：|(a∧B)| + |A'×B| —[count-∧-const | IH]→ (a ? |B| : 0) + |A'|·|B|
  -- —[if-dist]→ ((a ? 1 : 0) + |A'|)·|B| ≡ |A|·|B|（count 展开定义相等）
  trans (cong₂ _+_ (count-∧-const (A fzero) B)
                   (independence (λ i → A (fsuc i)) B))
        (if-dist (A fzero) (count B) (count (λ i → A (fsuc i))))

-- ────────────────────────────────────────────────────────────────────
-- §4 核对层（GF(3)² 实例——原七数值点降级为演示件对账，非定理）
--   9/3/3 网格 = Fin 3 × Fin 3 积空间实例；原点保留原文供对账
-- ────────────────────────────────────────────────────────────────────

-- 原七点（演示件——数值 refl，仅作实例对账）
check-omega-size : 9 ≡ 9 ; check-omega-size = refl
check-event-a-size : 3 * 1 ≡ 3 ; check-event-a-size = refl
check-event-b-size : 3 * 1 ≡ 3 ; check-event-b-size = refl
check-total-prob : 9 * 1 ≡ 1 * 9 ; check-total-prob = refl
check-additivity-pt : 3 + 3 ≡ 6 ; check-additivity-pt = refl
check-independence-pt : 1 * 9 ≡ 3 * 3 ; check-independence-pt = refl
check-uniformity : 9 * 1 ≡ 9 ; check-uniformity = refl

-- 两点互斥事件（核对 additivity）
a2 : Fin 2 → Bool
a2 fzero = true
a2 (fsuc i) = false

b2 : Fin 2 → Bool
b2 fzero = false
b2 (fsuc i) = true

disj2 : ∀ x → (a2 x ∧ b2 x) ≡ false
disj2 fzero = refl
disj2 (fsuc i) = refl

-- 符号对账三件（原 9/3/3 = n=3 形实例）
check-normalization-3 : count {3} (λ _ → true) ≡ 3
check-normalization-3 = normalization 3
  -- 对账 check-omega-size：9 点网格 = 两因子 normalization 3 的乘积形

check-additivity-2 : count (λ x → a2 x ∨ b2 x) ≡ 2
check-additivity-2 = additivity a2 b2 disj2
  -- 对账 check-additivity-pt：3 + 3 ≡ 6 的两点形（1 + 1 ≡ 2）

check-independence-33 : countP {3} {3} (λ x → true ∧ true) ≡ 9
check-independence-33 = independence {3} {3} (λ _ → true) (λ _ → true)
  -- 对账 check-independence-pt：1·9 ≡ 3·3 的交叉形 = |Ω₃|·|Ω₃| ≡ 3·3（乘法形实例）

-- 0 postulate / 0 hole（剥注释终检）。
