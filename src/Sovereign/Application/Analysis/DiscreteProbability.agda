{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Application.Analysis.DiscreteProbability
-- DiscreteProbability — 离散概率论 (MSC 62)
-- GF(3) 上的有限概率空间: 6 个事件的离散分布.
-- 0 postulate.

-- | 离散概率实例核
--
-- 核心原则：离散概率实例核——离散基座实例核（非一般定理，诚实边界随引用）
--          穷举/归纳边界遵守（≤27 case 或具名链，trans ≤3）
--          代数污染禁令（禁 Float/Double/超越函数）
--
-- 包含：§1-3 旧面（uniform/twoPoint/expectation/marginal）+
--       §4 概率空间 record ｜§5 条件概率（乘法特征形）｜§6 期望线性/方差（定点）
--       §7 Markov 链（id-stable 实例）｜§8 UniformProb 三定理对账

module Sovereign.Application.Analysis.DiscreteProbability where

open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_)
open import Data.Product using (_×_; _,_)
open import Data.Nat.Properties using (*-identityˡ; *-identityʳ; *-zeroʳ; *-distribʳ-+; +-assoc; +-comm; +-identityʳ)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.Bool using (Bool; true; false; _∧_; if_then_else_)
open import Sovereign.Application.Analysis.UniformProb using (count; normalization)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; trans; sym)
open import Sovereign.Base.Trit using (Trit; T₀; T₁; T₂; _⊕_; _⊗_)

-- §1. 有限概率空间 -----------------------------------------------
-- Ω = {T₀, T₁, T₂} 三元素样本空间.
-- 概率分布: p : Trit → ℕ, Σp(x) = 3 (归一化到 GF(3) 单位).

-- 均匀分布: p(x) = 1
uniform : Trit → ℕ; uniform _ = 1
uniform-norm : uniform T₀ + uniform T₁ + uniform T₂ ≡ 3
uniform-norm = refl

-- 两点分布: p(T₀)=2, p(T₁)=1, p(T₂)=0
twoPoint : Trit → ℕ
twoPoint T₀ = 2; twoPoint T₁ = 1; twoPoint T₂ = 0

twoPoint-norm : twoPoint T₀ + twoPoint T₁ + twoPoint T₂ ≡ 3
twoPoint-norm = refl

-- §2. 期望与方差 (离散版) -----------------------------------------
-- E[X] = Σ x(i)·p(i)/N (离散加权平均, 无 Lebesgue 积分)
expectation : (Trit → ℕ) → (Trit → ℕ) → ℕ
expectation X p = (X T₀ * p T₀) + (X T₁ * p T₁) + (X T₂ * p T₂)

-- 恒等随机变量的期望
id-expect-uniform : expectation (λ {T₀ → 0; T₁ → 1; T₂ → 2}) uniform ≡ 3
id-expect-uniform = refl

-- §3. 联合分布 (T⁶ 上的乘积空间) ----------------------------------
-- Ω₁×Ω₂ = GF3 × GF3 (9 元素).
-- 联合分布穷举可计算, 边缘化 = 求和.

-- 边缘分布验证
marginal : (Trit × Trit → ℕ) → Trit → ℕ
marginal p x = p (x , T₀) + p (x , T₁) + p (x , T₂)

-- 独立乘积分布边缘化 = 均匀分布各分量
indep-prod : (Trit × Trit) → ℕ
indep-prod _ = 1
marginal-indep : marginal indep-prod T₀ ≡ 3
marginal-indep = refl

-- 经典概率依赖 σ-代数和 Lebesgue 积分.
-- 离散替代: GF(3)ⁿ 上的穷举求和, 所有分布完全可计算.
-- 0 postulate.

-- 一般 ∀ 定理：均匀分布下期望 = 求和（uniform t = 1 ⟹ X t * 1 ≡ X t）
expectation-uniform-sum : ∀ (X : Trit → ℕ) →
  expectation X uniform ≡ (X T₀ + X T₁) + X T₂
expectation-uniform-sum X =
  trans (cong (λ w → (w + (X T₁ * 1)) + (X T₂ * 1)) (*-identityʳ (X T₀)))
  (trans (cong (λ w → (X T₀ + w) + (X T₂ * 1)) (*-identityʳ (X T₁)))
         (cong ((X T₀ + X T₁) +_) (*-identityʳ (X T₂))))

-- ════════════════════════════════════════════════════════════════
-- §4 概率空间 record（关系入定义：载体索引 + 权重 + 归一化见证）
-- ════════════════════════════════════════════════════════════════

wsum : ∀ {n} → (Fin n → ℕ) → ℕ
wsum {zero} _ = 0
wsum {suc n} f = f fzero + wsum (λ i → f (fsuc i))

record ProbSpace (n : ℕ) : Set where
  field
    w     : Fin n → ℕ
    total : ℕ
    norm  : wsum w ≡ total

uniform3 : Fin 3 → ℕ
uniform3 _ = 1

ps3 : ProbSpace 3
ps3 = record { w = uniform3 ; total = 3 ; norm = refl }

-- ════════════════════════════════════════════════════════════════
-- §5 条件概率（乘法特征形——ℕ 无除法：条件权重以「未除形」见证
--   condEq c = (c·w(B) ≡ w(A∩B))，除法语义以乘法特征呈现，禁浮点不破）
-- ════════════════════════════════════════════════════════════════

cond-num : ∀ {n} → (A B : Fin n → Bool) → ℕ
cond-num A B = count (λ i → A i ∧ B i)

condEq : ∀ {n} → (A B : Fin n → Bool) → ℕ → Set
condEq A B c = (c * count B ≡ cond-num A B)

-- 条件概率定义（核心件）：全概率形——P(Ω|B)=1（c=1 见证）
cond-omega : ∀ {n} (B : Fin n → Bool) → condEq (λ _ → true) B 1
cond-omega B = *-identityˡ (count B)

-- 条件概率乘法合成形（链式法则雏形）：cond-num A B 于全真 B = w(A)
cond-true : ∀ {n} (A : Fin n → Bool) → cond-num A (λ _ → true) ≡ count A
cond-true A = count-ext (λ i → A i ∧ true) A (λ i → and-true-r (A i))
  where
  and-true-r : ∀ b → b ∧ true ≡ b
  and-true-r true = refl
  and-true-r false = refl
  -- 谓词逐点相等 ⟹ count 相等（count 的合同性——同 n 下逐点形）
  count-ext : ∀ {n} (A B : Fin n → Bool) → (∀ i → A i ≡ B i) → count A ≡ count B
  count-ext {zero} A B _ = refl
  count-ext {suc n} A B eq = cong₂ _+_ (cong (λ z → if z then 1 else 0) (eq fzero))
    (count-ext (λ i → A (fsuc i)) (λ i → B (fsuc i)) (λ i → eq (fsuc i)))
  -- if 需要入域件名（Data.Bool 的 if_then_else_）

-- 实例核对（Fin 2 谓词——cond-num 计数形）
boolT : Fin 2 → Bool
boolT _ = true
boolA : Fin 2 → Bool
boolA fzero = true
boolA (fsuc fzero) = false
boolA (fsuc (fsuc ()))
check-cond-num : cond-num boolA boolT ≡ 1
check-cond-num = refl

-- ════════════════════════════════════════════════════════════════
-- §6 期望线性 + 方差（定点 ℕ——禁浮点）
-- ════════════════════════════════════════════════════════════════

-- 六项换位具名件（附录 14 rearrange 形）
swap-four : ∀ a b c d → (a + b) + (c + d) ≡ (a + c) + (b + d)
swap-four a b c d =
  trans (+-assoc a b (c + d))
  (trans (cong (a +_) (trans (sym (+-assoc b c d)) (trans (cong (_+ d) (+-comm b c)) (+-assoc c b d))))
         (sym (+-assoc a c (b + d))))

re-arrange : ∀ a b c d e f →
  ((a + b) + ((c + d) + (e + f))) ≡ ((a + c) + e) + ((b + d) + f)
re-arrange a b c d e f =
  trans (sym (+-assoc (a + b) (c + d) (e + f)))
  (trans (cong (_+ (e + f)) (swap-four a b c d))
         (swap-four (a + c) (b + d) e f))

-- 期望线性（核心件）：E[X+Y] ≡ E[X]+E[Y]（分配展开 + 六项换位）
expect-add : ∀ (X Y p : Trit → ℕ) →
  expectation (λ t → X t + Y t) p ≡ expectation X p + expectation Y p
expect-add X Y p =
  trans (cong (_+ (X T₂ + Y T₂) * p T₂)
              (cong₂ _+_ (*-distribʳ-+ (p T₀) (X T₀) (Y T₀)) (*-distribʳ-+ (p T₁) (X T₁) (Y T₁))))
  (trans (cong (((X T₀ * p T₀ + Y T₀ * p T₀) + (X T₁ * p T₁ + Y T₁ * p T₁)) +_)
               (*-distribʳ-+ (p T₂) (X T₂) (Y T₂)))
  (trans (+-assoc (X T₀ * p T₀ + Y T₀ * p T₀) (X T₁ * p T₁ + Y T₁ * p T₁) (X T₂ * p T₂ + Y T₂ * p T₂))
         (re-arrange (X T₀ * p T₀) (Y T₀ * p T₀) (X T₁ * p T₁) (Y T₁ * p T₁) (X T₂ * p T₂) (Y T₂ * p T₂))))

-- 二阶矩与方差（∸ 形：经典定义的 ℕ 适配）
moment2 : (Trit → ℕ) → (Trit → ℕ) → ℕ
moment2 X p = expectation (λ t → X t * X t) p

variance : (Trit → ℕ) → (Trit → ℕ) → ℕ
variance X p = moment2 X p ∸ (expectation X p * expectation X p)

check-var-id : variance (λ {T₀ → 0; T₁ → 1; T₂ → 2}) uniform ≡ 0
check-var-id = refl

-- ════════════════════════════════════════════════════════════════
-- §7 Markov 链（转移权重阵——定点；逐点形式纪律：∀ y 形不用函数等式）
--   马尔可夫性质（注记）：P(Xₙ₊₁|Xₙ, past) = P(Xₙ₊₁|Xₙ)——条件形以 §5 乘法特征承载
-- ════════════════════════════════════════════════════════════════

trans-id : Trit → Trit → ℕ
trans-id T₀ T₀ = 1
trans-id T₁ T₁ = 1
trans-id T₂ T₂ = 1
trans-id _ _ = 0

step-dist : (Trit → ℕ) → (Trit → Trit → ℕ) → Trit → ℕ
step-dist μ P y = μ T₀ * P T₀ y + (μ T₁ * P T₁ y + μ T₂ * P T₂ y)

-- 稳定性（逐点形）：id 转移阵下任意分布逐点稳定
step-id-pt : ∀ (μ : Trit → ℕ) (y : Trit) → step-dist μ trans-id y ≡ μ y
step-id-pt μ T₀ =
  trans (cong (μ T₀ * trans-id T₀ T₀ +_)
              (trans (cong₂ _+_ (*-zeroʳ (μ T₁)) (*-zeroʳ (μ T₂))) refl))
  (trans (cong (_+ 0) (*-identityʳ (μ T₀))) (+-identityʳ (μ T₀)))
step-id-pt μ T₁ =
  trans (cong (_+ (μ T₁ * trans-id T₁ T₁ + μ T₂ * trans-id T₂ T₁)) (*-zeroʳ (μ T₀)))
  (trans (cong (0 +_) (trans (cong₂ _+_ (*-identityʳ (μ T₁)) (*-zeroʳ (μ T₂))) (+-identityʳ (μ T₁))))
         refl)
step-id-pt μ T₂ =
  trans (cong (_+ (μ T₁ * trans-id T₁ T₂ + μ T₂ * trans-id T₂ T₂)) (*-zeroʳ (μ T₀)))
  (trans (cong (0 +_) (trans (cong₂ _+_ (*-zeroʳ (μ T₁)) (*-identityʳ (μ T₂))) refl))
         refl)

-- ════════════════════════════════════════════════════════════════
-- §8 UniformProb 三定理对账（衔接件——ffda3b74 面）
-- ════════════════════════════════════════════════════════════════

check-count3 : count {3} (λ _ → true) ≡ 3
check-count3 = refl

check-uniform-count : uniform T₀ + uniform T₁ + uniform T₂ ≡ count {3} (λ _ → true)
check-uniform-count = refl

check-norm3 : count {3} (λ _ → true) ≡ 3
check-norm3 = normalization 3
