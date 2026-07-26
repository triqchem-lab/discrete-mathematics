{-# OPTIONS --rewriting #-}
module Sovereign.Analysis.NormEquivalence where

--------------------------------------------------------------------------------
-- 范数等价定理: 有限维 GF(3)ⁿ 上所有范数等价
--
-- 核心定理:
--   在有限维 GF(3)ⁿ 上, L² 范数 (二次型 Q(x)=⟨x,x⟩) 和最大范数等价:
--   ∃ C₁ C₂ → C₁·‖x‖∞ ≤₃ Q(x) ≤₃ C₂·‖x‖∞
--
-- 证明策略 (穷举法):
--   GF(3)ⁿ 是有限集 (3ⁿ 个元素), 范数只取 {T₀, T₁, T₂} 三个值:
--   1. 单位球面 S = {x : ‖x‖∞ ≡ T₁} 是有限集 (= 所有非零向量)
--   2. Q 在 S 上取有限个值 (n=1: {T₁}; n=2: {T₁,T₂})
--   3. C₁ = min Q|_S, C₂ = max Q|_S
--   4. 由齐次性 (Q(a·x) = |a|·Q(x)) 推广到所有向量
--
-- 关键发现:
--   • n=1: Q 是正定范数, 等价常数 C₁=C₂=T₁ (Q ≡ ‖·‖∞)
--   • n=2: Q 是正定范数, 等价常数 C₁=T₁, C₂=T₂
--   • n≥3: Q 不是范数 (存在各向同性向量), 等价性不成立
--   • 一般定理: 有限 GF(3)ⁿ 上所有正定范数拓扑等价 (同一零集)
--
-- 依赖:
--   Sovereign.Algebra.FunctionalDiscrete — GF(3)ⁿ 离散泛函分析
--
-- 0 postulate — 全部构造性证明
--------------------------------------------------------------------------------

open import Data.Nat using (ℕ; zero; suc)
open import Data.Vec using (Vec; []; _∷_)
open import Data.Product using (Σ; _,_; _×_; proj₁; proj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; cong; cong₂; sym; trans; subst)

open import Sovereign.Base.Trit using (
  Trit; T₀; T₁; T₂; _⊕_; _⊗_;
  ⊗-identityˡ; ⊗-zeroˡ; ⊗-zeroʳ)

open import Sovereign.Algebra.FunctionalDiscrete using (
  _+v_; _·v_; 0⃗;
  discrete-norm; abs-gf3; max-abs;
  quadratic-form;
  norm-zero→vec-zero; norm-of-zero; norm-two-valued;
  vec-zero→norm-zero;
  isotropic-example; isotropic-nonzero;
  scalar-one;
  quadratic-zero)

--------------------------------------------------------------------------------
-- §1. GF(3) 序关系 — 范数比较的基础
--
-- 在 GF(3) = {T₀, T₁, T₂} 上定义自然全序 T₀ ≤ T₁ ≤ T₂
-- (对应 ℕ 中的 0 ≤ 1 ≤ 2)
-- 这是范数等价性中 "≤" 的离散版本
--------------------------------------------------------------------------------

data _≤₃_ : Trit → Trit → Set where
  le00 : T₀ ≤₃ T₀
  le01 : T₀ ≤₃ T₁
  le02 : T₀ ≤₃ T₂
  le11 : T₁ ≤₃ T₁
  le12 : T₁ ≤₃ T₂
  le22 : T₂ ≤₃ T₂

-- 自反性
≤₃-refl : ∀ x → x ≤₃ x
≤₃-refl T₀ = le00
≤₃-refl T₁ = le11
≤₃-refl T₂ = le22

-- 传递性 (10 个合法组合, 由索引约束自动排除不可能情况)
≤₃-trans : ∀ x y z → x ≤₃ y → y ≤₃ z → x ≤₃ z
≤₃-trans _ _ _ le00 le00 = le00
≤₃-trans _ _ _ le00 le01 = le01
≤₃-trans _ _ _ le00 le02 = le02
≤₃-trans _ _ _ le01 le11 = le01
≤₃-trans _ _ _ le01 le12 = le02
≤₃-trans _ _ _ le02 le22 = le02
≤₃-trans _ _ _ le11 le11 = le11
≤₃-trans _ _ _ le11 le12 = le12
≤₃-trans _ _ _ le12 le22 = le12
≤₃-trans _ _ _ le22 le22 = le22

-- 反对称性
≤₃-antisym : ∀ x y → x ≤₃ y → y ≤₃ x → x ≡ y
≤₃-antisym _ _ le00 le00 = refl
≤₃-antisym _ _ le01 ()
≤₃-antisym _ _ le02 ()
≤₃-antisym _ _ le11 le11 = refl
≤₃-antisym _ _ le12 ()
≤₃-antisym _ _ le22 le22 = refl

-- 全序性: 任意两个元素可比较 (9 case)
≤₃-total : ∀ x y → x ≤₃ y ⊎ y ≤₃ x
≤₃-total T₀ T₀ = inj₁ le00
≤₃-total T₀ T₁ = inj₁ le01
≤₃-total T₀ T₂ = inj₁ le02
≤₃-total T₁ T₀ = inj₂ le01
≤₃-total T₁ T₁ = inj₁ le11
≤₃-total T₁ T₂ = inj₁ le12
≤₃-total T₂ T₀ = inj₂ le02
≤₃-total T₂ T₁ = inj₂ le12
≤₃-total T₂ T₂ = inj₁ le22

--------------------------------------------------------------------------------
-- §2. 范数等价性定义
--
-- 经典定义: ∃ C₁ C₂ > 0, ∀ x: C₁·‖x‖₁ ≤ ‖x‖₂ ≤ C₂·‖x‖₁
-- GF(3) 版本: 用 ≤₃ 替代 ≤, 用 C ≢ T₀ 替代 C > 0
--------------------------------------------------------------------------------

-- 范数等价: N₁ 是参考范数 (‖·‖∞), N₂ 是目标范数 (Q)
-- ∃ C₁ C₂ ≢ T₀, ∀ x: C₁⊗N₁(x) ≤₃ N₂(x) ≤₃ C₂⊗N₁(x)
NormEquivalent : ∀ n → (Vec Trit n → Trit) → (Vec Trit n → Trit) → Set
NormEquivalent n N₁ N₂ =
  Σ Trit (λ C₁ → Σ Trit (λ C₂ →
    (C₁ ≢ T₀) × (C₂ ≢ T₀) ×
    (∀ x → (C₁ ⊗ N₁ x) ≤₃ N₂ x) ×
    (∀ x → N₂ x ≤₃ (C₂ ⊗ N₁ x))))

-- Trit 不等性辅助 (构造器不相交)
T₁≢T₀ : T₁ ≡ T₀ → ⊥
T₁≢T₀ ()

T₂≢T₀ : T₂ ≡ T₀ → ⊥
T₂≢T₀ ()

--------------------------------------------------------------------------------
-- §3. 代数辅助引理 — abs-gf3 和平方运算
--------------------------------------------------------------------------------

-- |a⊗x| = |a|⊗|x| (绝对值的乘法性, 9 case refl)
abs-gf3-multiplicative : ∀ a x → abs-gf3 (a ⊗ x) ≡ abs-gf3 a ⊗ abs-gf3 x
abs-gf3-multiplicative T₀ T₀ = refl
abs-gf3-multiplicative T₀ T₁ = refl
abs-gf3-multiplicative T₀ T₂ = refl
abs-gf3-multiplicative T₁ T₀ = refl
abs-gf3-multiplicative T₁ T₁ = refl
abs-gf3-multiplicative T₁ T₂ = refl
abs-gf3-multiplicative T₂ T₀ = refl
abs-gf3-multiplicative T₂ T₁ = refl
abs-gf3-multiplicative T₂ T₂ = refl

-- |x| 只取 T₀ 或 T₁ (值域约束)
abs-gf3-two-valued : ∀ x → abs-gf3 x ≡ T₀ ⊎ abs-gf3 x ≡ T₁
abs-gf3-two-valued T₀ = inj₁ refl
abs-gf3-two-valued T₁ = inj₂ refl
abs-gf3-two-valued T₂ = inj₂ refl

-- a² = |a| (GF(3) 中平方等于绝对值: 0²=0, 1²=1, 2²=1)
sq-eq-abs : ∀ a → a ⊗ a ≡ abs-gf3 a
sq-eq-abs T₀ = refl
sq-eq-abs T₁ = refl
sq-eq-abs T₂ = refl

-- (T₂⊗x)² = x² (negate 不改变平方: (-x)² = x²)
sq-negate : ∀ x → (T₂ ⊗ x) ⊗ (T₂ ⊗ x) ≡ x ⊗ x
sq-negate T₀ = refl
sq-negate T₁ = refl
sq-negate T₂ = refl

--------------------------------------------------------------------------------
-- §4. 齐次性证明 — 范数等价中 "由齐次性推广" 的关键
--
-- Q(a·x) = |a|·Q(x) 和 ‖a·x‖∞ = |a|·‖x‖∞
--------------------------------------------------------------------------------

-- T₀ 标量乘任意向量得零向量
scalar-T₀-zero : ∀ n (xs : Vec Trit n) → T₀ ·v xs ≡ 0⃗ n
scalar-T₀-zero zero [] = refl
scalar-T₀-zero (suc n) (x ∷ xs) =
  cong₂ _∷_ (⊗-zeroˡ x) (scalar-T₀-zero n xs)

-- Q(T₂·x) = Q(x): negate 不改变二次型 (对维度归纳)
Q-negate-invariant : ∀ n (xs : Vec Trit n) →
  quadratic-form n (T₂ ·v xs) ≡ quadratic-form n xs
Q-negate-invariant zero [] = refl
Q-negate-invariant (suc n) (x ∷ xs) =
  cong₂ _⊕_ (sq-negate x) (Q-negate-invariant n xs)

-- 二次型齐次性: Q(a·x) = |a| ⊗ Q(x)
Q-homogeneous : ∀ n a (xs : Vec Trit n) →
  quadratic-form n (a ·v xs) ≡ abs-gf3 a ⊗ quadratic-form n xs
Q-homogeneous n T₀ xs =
  trans (cong (quadratic-form n) (scalar-T₀-zero n xs))
    (trans (quadratic-zero n) (sym (⊗-zeroˡ (quadratic-form n xs))))
Q-homogeneous n T₁ xs =
  trans (cong (quadratic-form n) (scalar-one n xs))
    (sym (⊗-identityˡ (quadratic-form n xs)))
Q-homogeneous n T₂ xs =
  trans (Q-negate-invariant n xs)
    (sym (⊗-identityˡ (quadratic-form n xs)))

-- max-abs 的标量分配: c ∈ {T₀, T₁} 时 max(c·u, c·v) = c·max(u,v)
-- (需要对 u,v 穷举, 因为 _⊗_ 的模式匹配顺序阻止 T₁⊗u 的归约)
max-abs-scale : ∀ c u v → c ≡ T₀ ⊎ c ≡ T₁ →
  max-abs (c ⊗ u) (c ⊗ v) ≡ c ⊗ max-abs u v
max-abs-scale T₀ u v _ = refl
max-abs-scale T₁ T₀ T₀ _ = refl
max-abs-scale T₁ T₀ T₁ _ = refl
max-abs-scale T₁ T₀ T₂ _ = refl
max-abs-scale T₁ T₁ T₀ _ = refl
max-abs-scale T₁ T₁ T₁ _ = refl
max-abs-scale T₁ T₁ T₂ _ = refl
max-abs-scale T₁ T₂ T₀ _ = refl
max-abs-scale T₁ T₂ T₁ _ = refl
max-abs-scale T₁ T₂ T₂ _ = refl
max-abs-scale T₂ u v (inj₁ ())
max-abs-scale T₂ u v (inj₂ ())

-- sup-范数齐次性: ‖a·x‖∞ = |a| ⊗ ‖x‖∞
discrete-norm-homogeneous : ∀ n a (xs : Vec Trit n) →
  discrete-norm n (a ·v xs) ≡ abs-gf3 a ⊗ discrete-norm n xs
discrete-norm-homogeneous zero a [] = sym (⊗-zeroʳ (abs-gf3 a))
discrete-norm-homogeneous (suc n) a (x ∷ xs) =
  trans (cong₂ max-abs (abs-gf3-multiplicative a x)
                       (discrete-norm-homogeneous n a xs))
        (max-abs-scale (abs-gf3 a) (abs-gf3 x) (discrete-norm n xs)
                       (abs-gf3-two-valued a))

--------------------------------------------------------------------------------
-- §5. 单位球面与正定性
--
-- 单位球面 S = {x : ‖x‖∞ ≡ T₁} = GF(3)ⁿ \ {0⃗}
-- (因为 sup-范数只取 {T₀, T₁}, 非零向量恰好在球面上)
--------------------------------------------------------------------------------

-- 单位球面成员
OnUnitSphere : ∀ n → Vec Trit n → Set
OnUnitSphere n x = discrete-norm n x ≡ T₁

-- 非零 → 在球面上
nonzero→on-sphere : ∀ n (xs : Vec Trit n) → xs ≢ 0⃗ n → OnUnitSphere n xs
nonzero→on-sphere n xs neq with norm-two-valued n xs
... | inj₁ p = ⊥-elim (neq (norm-zero→vec-zero n xs p))
... | inj₂ p = p

-- 在球面上 → 非零
on-sphere→nonzero : ∀ n (xs : Vec Trit n) → OnUnitSphere n xs → xs ≢ 0⃗ n
on-sphere→nonzero n xs p q =
  T₁≢T₀ (trans (sym p) (vec-zero→norm-zero n xs q))

--------------------------------------------------------------------------------
-- §6. 二次型在 n=1 的正定性 (穷举 3 个向量)
--
-- GF(3)¹ = {T₀, T₁, T₂}, Q(x) = x²:
--   Q(T₀) = T₀ (零向量)
--   Q(T₁) = T₁ (非零)
--   Q(T₂) = T₁ (非零)
-- Q 是正定的: Q(x)=T₀ → x=0⃗
--------------------------------------------------------------------------------

Q-definite-1 : ∀ (x : Vec Trit 1) → quadratic-form 1 x ≡ T₀ → x ≡ 0⃗ 1
Q-definite-1 (T₀ ∷ []) _ = refl
Q-definite-1 (T₁ ∷ []) ()
Q-definite-1 (T₂ ∷ []) ()

-- Q 在单位球面上恒等于 T₁ (n=1: min = max = T₁)
Q-on-sphere-1 : ∀ x → OnUnitSphere 1 x → quadratic-form 1 x ≡ T₁
Q-on-sphere-1 (T₀ ∷ []) ()
Q-on-sphere-1 (T₁ ∷ []) _ = refl
Q-on-sphere-1 (T₂ ∷ []) _ = refl

--------------------------------------------------------------------------------
-- §7. 二次型在 n=2 的正定性 (穷举 9 个向量)
--
-- GF(3)² = {(x₀,x₁) : xᵢ ∈ {T₀,T₁,T₂}}, Q(x) = x₀² + x₁²:
--   Q(T₀,T₀) = T₀         (零向量)
--   Q(T₀,T₁) = T₁         (非零)
--   Q(T₀,T₂) = T₁         (非零)
--   Q(T₁,T₀) = T₁         (非零)
--   Q(T₁,T₁) = T₁⊕T₁ = T₂ (非零)
--   Q(T₁,T₂) = T₁⊕T₁ = T₂ (非零)
--   Q(T₂,T₀) = T₁         (非零)
--   Q(T₂,T₁) = T₁⊕T₁ = T₂ (非零)
--   Q(T₂,T₂) = T₁⊕T₁ = T₂ (非零)
-- Q 是正定的: Q(x)=T₀ → x=0⃗
-- Q 在球面上取 {T₁, T₂}: min = T₁, max = T₂
--------------------------------------------------------------------------------

Q-definite-2 : ∀ (x : Vec Trit 2) → quadratic-form 2 x ≡ T₀ → x ≡ 0⃗ 2
Q-definite-2 (T₀ ∷ T₀ ∷ []) _ = refl
Q-definite-2 (T₀ ∷ T₁ ∷ []) ()
Q-definite-2 (T₀ ∷ T₂ ∷ []) ()
Q-definite-2 (T₁ ∷ T₀ ∷ []) ()
Q-definite-2 (T₁ ∷ T₁ ∷ []) ()
Q-definite-2 (T₁ ∷ T₂ ∷ []) ()
Q-definite-2 (T₂ ∷ T₀ ∷ []) ()
Q-definite-2 (T₂ ∷ T₁ ∷ []) ()
Q-definite-2 (T₂ ∷ T₂ ∷ []) ()

-- Q 在单位球面上取 {T₁, T₂} (n=2: min = T₁, max = T₂)
Q-on-sphere-2 : ∀ x → OnUnitSphere 2 x →
  quadratic-form 2 x ≡ T₁ ⊎ quadratic-form 2 x ≡ T₂
Q-on-sphere-2 (T₀ ∷ T₀ ∷ []) ()
Q-on-sphere-2 (T₀ ∷ T₁ ∷ []) _ = inj₁ refl
Q-on-sphere-2 (T₀ ∷ T₂ ∷ []) _ = inj₁ refl
Q-on-sphere-2 (T₁ ∷ T₀ ∷ []) _ = inj₁ refl
Q-on-sphere-2 (T₁ ∷ T₁ ∷ []) _ = inj₂ refl
Q-on-sphere-2 (T₁ ∷ T₂ ∷ []) _ = inj₂ refl
Q-on-sphere-2 (T₂ ∷ T₀ ∷ []) _ = inj₁ refl
Q-on-sphere-2 (T₂ ∷ T₁ ∷ []) _ = inj₂ refl
Q-on-sphere-2 (T₂ ∷ T₂ ∷ []) _ = inj₂ refl

--------------------------------------------------------------------------------
-- §8. 核心定理: n=1 范数等价
--
-- C₁ = C₂ = T₁: T₁·‖x‖∞ ≤₃ Q(x) ≤₃ T₁·‖x‖∞
-- 即 ‖x‖∞ ≤₃ Q(x) ≤₃ ‖x‖∞ (在 n=1 时两范数完全一致)
--------------------------------------------------------------------------------

norm-equiv-1 : NormEquivalent 1 (discrete-norm 1) (quadratic-form 1)
norm-equiv-1 = T₁ , T₁ , T₁≢T₀ , T₁≢T₀ , lower , upper
  where
    -- 下界: T₁ ⊗ ‖x‖∞ ≤₃ Q(x)
    lower : ∀ x → (T₁ ⊗ discrete-norm 1 x) ≤₃ quadratic-form 1 x
    lower (T₀ ∷ []) = le00  -- T₀ ≤₃ T₀
    lower (T₁ ∷ []) = le11  -- T₁ ≤₃ T₁
    lower (T₂ ∷ []) = le11  -- T₁ ≤₃ T₁
    -- 上界: Q(x) ≤₃ T₁ ⊗ ‖x‖∞
    upper : ∀ x → quadratic-form 1 x ≤₃ (T₁ ⊗ discrete-norm 1 x)
    upper (T₀ ∷ []) = le00  -- T₀ ≤₃ T₀
    upper (T₁ ∷ []) = le11  -- T₁ ≤₃ T₁
    upper (T₂ ∷ []) = le11  -- T₁ ≤₃ T₁

--------------------------------------------------------------------------------
-- §9. 核心定理: n=2 范数等价
--
-- C₁ = T₁, C₂ = T₂: T₁·‖x‖∞ ≤₃ Q(x) ≤₃ T₂·‖x‖∞
-- 下界: 非零向量 Q(x) ≥ T₁ (正定性)
-- 上界: 非零向量 Q(x) ≤ T₂ (值域约束)
--------------------------------------------------------------------------------

norm-equiv-2 : NormEquivalent 2 (discrete-norm 2) (quadratic-form 2)
norm-equiv-2 = T₁ , T₂ , T₁≢T₀ , T₂≢T₀ , lower , upper
  where
    -- 下界: T₁ ⊗ ‖x‖∞ ≤₃ Q(x)
    -- 零向量: T₀ ≤₃ T₀; 非零向量: T₁ ≤₃ Q(x) (Q ∈ {T₁,T₂})
    lower : ∀ x → (T₁ ⊗ discrete-norm 2 x) ≤₃ quadratic-form 2 x
    lower (T₀ ∷ T₀ ∷ []) = le00  -- T₀ ≤₃ T₀
    lower (T₀ ∷ T₁ ∷ []) = le11  -- T₁ ≤₃ T₁
    lower (T₀ ∷ T₂ ∷ []) = le11  -- T₁ ≤₃ T₁
    lower (T₁ ∷ T₀ ∷ []) = le11  -- T₁ ≤₃ T₁
    lower (T₁ ∷ T₁ ∷ []) = le12  -- T₁ ≤₃ T₂
    lower (T₁ ∷ T₂ ∷ []) = le12  -- T₁ ≤₃ T₂
    lower (T₂ ∷ T₀ ∷ []) = le11  -- T₁ ≤₃ T₁
    lower (T₂ ∷ T₁ ∷ []) = le12  -- T₁ ≤₃ T₂
    lower (T₂ ∷ T₂ ∷ []) = le12  -- T₁ ≤₃ T₂
    -- 上界: Q(x) ≤₃ T₂ ⊗ ‖x‖∞
    -- 零向量: T₀ ≤₃ T₀; 非零向量: Q(x) ≤₃ T₂ (值域上界)
    upper : ∀ x → quadratic-form 2 x ≤₃ (T₂ ⊗ discrete-norm 2 x)
    upper (T₀ ∷ T₀ ∷ []) = le00  -- T₀ ≤₃ T₀
    upper (T₀ ∷ T₁ ∷ []) = le12  -- T₁ ≤₃ T₂
    upper (T₀ ∷ T₂ ∷ []) = le12  -- T₁ ≤₃ T₂
    upper (T₁ ∷ T₀ ∷ []) = le12  -- T₁ ≤₃ T₂
    upper (T₁ ∷ T₁ ∷ []) = le22  -- T₂ ≤₃ T₂
    upper (T₁ ∷ T₂ ∷ []) = le22  -- T₂ ≤₃ T₂
    upper (T₂ ∷ T₀ ∷ []) = le12  -- T₁ ≤₃ T₂
    upper (T₂ ∷ T₁ ∷ []) = le22  -- T₂ ≤₃ T₂
    upper (T₂ ∷ T₂ ∷ []) = le22  -- T₂ ≤₃ T₂

--------------------------------------------------------------------------------
-- §10. 各向同性反例: n=3 时 Q 不是范数
--
-- (T₁,T₁,T₁) 的二次型: Q = T₁⊕T₁⊕T₁ = T₂⊕T₁ = T₀
-- 但该向量非零 → Q 不满足正定性 → 范数等价不成立
--
-- 物理意义: GF(3) 中 1+1+1=3≡0, 三维等幅叠加相消
-- 这是 GF(3) 内积空间与 ℝⁿ 内积空间的本质区别
--------------------------------------------------------------------------------

Q-not-norm-3 : Σ (Vec Trit 3) (λ x → x ≢ 0⃗ 3 × quadratic-form 3 x ≡ T₀)
Q-not-norm-3 = (T₁ ∷ T₁ ∷ T₁ ∷ []) , (λ ()) , refl

-- 等价性失败的直接证据:
-- 存在非零向量使 Q=T₀, 但 ‖·‖∞=T₁, 所以不存在 C₁ 使 C₁·T₁ ≤₃ T₀
norm-equiv-fails-3 : ¬ NormEquivalent 3 (discrete-norm 3) (quadratic-form 3)
-- C₁ = T₀: 违反 C₁ ≢ T₀
norm-equiv-fails-3 (T₀ , C₂ , C₁≠0 , C₂≠0 , lower , upper) = C₁≠0 refl
-- C₁ = T₁: 下界要求 T₁ ≤₃ Q(v) = T₀, 不可能
norm-equiv-fails-3 (T₁ , C₂ , C₁≠0 , C₂≠0 , lower , upper) =
  ⊥-elim (helper (lower (T₁ ∷ T₁ ∷ T₁ ∷ [])))
  where
    helper : (T₁ ⊗ discrete-norm 3 (T₁ ∷ T₁ ∷ T₁ ∷ []))
           ≤₃ quadratic-form 3 (T₁ ∷ T₁ ∷ T₁ ∷ []) → ⊥
    helper ()
-- C₁ = T₂: 下界要求 T₂ ≤₃ Q(v) = T₀, 不可能
norm-equiv-fails-3 (T₂ , C₂ , C₁≠0 , C₂≠0 , lower , upper) =
  ⊥-elim (helper (lower (T₁ ∷ T₁ ∷ T₁ ∷ [])))
  where
    helper : (T₂ ⊗ discrete-norm 3 (T₁ ∷ T₁ ∷ T₁ ∷ []))
           ≤₃ quadratic-form 3 (T₁ ∷ T₁ ∷ T₁ ∷ []) → ⊥
    helper ()

--------------------------------------------------------------------------------
-- §11. 一般定理: 有限 GF(3)ⁿ 上所有正定范数拓扑等价
--
-- 定理: 若 N₁, N₂ 都是正定的 (N(x)=T₀ → x=0⃗) 且保零 (N(0⃗)=T₀),
--       则它们有相同的零集: N₁(x)≡T₀ ↔ N₂(x)≡T₀
--
-- 证明: 纯粹由正定性推出, 不依赖范数的具体形式
--   N₁(x)=T₀ → x=0⃗ (正定) → N₂(x)=N₂(0⃗)=T₀ (保零)
--   反向同理
--
-- 意义: 有限离散空间上, 正定性是范数的唯一拓扑不变量
--       所有范数诱导相同的离散拓扑 → Hilbert/Banach 区别消失
--------------------------------------------------------------------------------

all-norms-topologically-equivalent : ∀ n (N₁ N₂ : Vec Trit n → Trit) →
  (∀ x → N₁ x ≡ T₀ → x ≡ 0⃗ n) →   -- N₁ 正定
  (∀ x → N₂ x ≡ T₀ → x ≡ 0⃗ n) →   -- N₂ 正定
  N₁ (0⃗ n) ≡ T₀ →                   -- N₁ 保零
  N₂ (0⃗ n) ≡ T₀ →                   -- N₂ 保零
  ∀ x → (N₁ x ≡ T₀ → N₂ x ≡ T₀) × (N₂ x ≡ T₀ → N₁ x ≡ T₀)
all-norms-topologically-equivalent n N₁ N₂ def₁ def₂ zero₁ zero₂ x =
  (λ p → subst (λ v → N₂ v ≡ T₀) (sym (def₁ x p)) zero₂) ,
  (λ p → subst (λ v → N₁ v ≡ T₀) (sym (def₂ x p)) zero₁)

-- 推论: sup-范数和 Q 在 n=1 拓扑等价
sup-Q-topo-equiv-1 : ∀ x →
  (discrete-norm 1 x ≡ T₀ → quadratic-form 1 x ≡ T₀) ×
  (quadratic-form 1 x ≡ T₀ → discrete-norm 1 x ≡ T₀)
sup-Q-topo-equiv-1 = all-norms-topologically-equivalent 1
  (discrete-norm 1) (quadratic-form 1)
  (norm-zero→vec-zero 1) Q-definite-1
  (norm-of-zero 1) (quadratic-zero 1)

-- 推论: sup-范数和 Q 在 n=2 拓扑等价
sup-Q-topo-equiv-2 : ∀ x →
  (discrete-norm 2 x ≡ T₀ → quadratic-form 2 x ≡ T₀) ×
  (quadratic-form 2 x ≡ T₀ → discrete-norm 2 x ≡ T₀)
sup-Q-topo-equiv-2 = all-norms-topologically-equivalent 2
  (discrete-norm 2) (quadratic-form 2)
  (norm-zero→vec-zero 2) Q-definite-2
  (norm-of-zero 2) (quadratic-zero 2)

--------------------------------------------------------------------------------
-- §12. 总结: 离散范数等价的核心定理
--------------------------------------------------------------------------------

-- 核心定理列表 (全部 0 postulate, 构造性证明):
--
-- 1. ≤₃ 全序: GF(3) 上的自然序 T₀ ≤ T₁ ≤ T₂ (自反/传递/反对称/全序)
-- 2. Q-homogeneous: Q(a·x) = |a|·Q(x) (二次型齐次性)
-- 3. discrete-norm-homogeneous: ‖a·x‖∞ = |a|·‖x‖∞ (sup-范数齐次性)
-- 4. Q-definite-1/2: Q 在 n=1,2 正定 (穷举 3/9 case)
-- 5. norm-equiv-1: n=1 范数等价, C₁=C₂=T₁ (Q ≡ ‖·‖∞)
-- 6. norm-equiv-2: n=2 范数等价, C₁=T₁, C₂=T₂
-- 7. norm-equiv-fails-3: n=3 等价性失败 (各向同性向量)
-- 8. all-norms-topologically-equivalent: 有限 GF(3)ⁿ 上所有正定范数拓扑等价
--
-- 与连续泛函分析的投影关系:
--   连续: 有限维 ℝⁿ 上所有范数等价 (需要紧致性/完备性)
--   离散: 有限 GF(3)ⁿ 上所有正定范数等价 (仅需有限性/穷举)
--   投影方向: 离散穷举 (本体) → 连续紧致性论证 (影子)
--   信息丢失: GF(3) 的代数结构 (各向同性, 退化内积)
--------------------------------------------------------------------------------
