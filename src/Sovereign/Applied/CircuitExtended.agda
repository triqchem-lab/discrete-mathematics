{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Applied.CircuitExtended
-- 应用层：扩展电路理论 (三值逻辑门)
--
-- 层级: 应用数学 (电性文明投影)
-- GF(3) 合法身份: 模 3 整数算术 + 格运算
--
-- 定理清单:
--   1. AND = min (_∧T_), OR = max (_∨T_): 引用 DomainProofs
--   2. NOT: T₀→T₂, T₁→T₁, T₂→T₀ (3 case 穷举)
--   3. De Morgan 定律: NOT(x∧y)≡NOT(x)∨NOT(y), NOT(x∨y)≡NOT(x)∧NOT(y)
--   4. AND = GLB, OR = LUB: 格论刻画 (≤T 全序)
--   5. 常数生成: T₀(AND零元), T₂(OR零元), T₁(门构造)
--   6. 函数完备性: {∧T, ∨T, NOT, ⊕, 常数} 生成全部 3³=27 个单变量函数
--      选择子分解: f(x) = ∨_a (Δ_a(x) ∧ f(a))
--
-- 0 postulate, 全部构造性证明, 穷举法优先

module Sovereign.Applied.CircuitExtended where

open import Data.Nat using (ℕ; _*_)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Sovereign.Base.Trit using (Trit; T₀; T₁; T₂; negate; _⊕_)
open import Sovereign.Applied.DomainProofs using (_∧T_; _∨T_; _≤T_; le-00; le-01; le-02; le-11; le-12; le-22)

--------------------------------------------------------------------------------
-- 1. 三值逻辑门: AND = min, OR = max
-- 经典二值逻辑: AND/OR 在 {0,1} 上
-- 三值扩展: AND = min (取小), OR = max (取大)
-- 基于 Trit 全序 T₀ < T₁ < T₂ 的分配格
-- (完整格公理证明见 DomainProofs.agda)
--------------------------------------------------------------------------------

-- AND 门实例: T₁ ∧T T₂ = T₁ (取小)
and-gate-example : T₁ ∧T T₂ ≡ T₁
and-gate-example = refl

-- OR 门实例: T₁ ∨T T₂ = T₂ (取大)
or-gate-example : T₁ ∨T T₂ ≡ T₂
or-gate-example = refl

-- AND 零元: T₀ ∧T x = T₀ (短路)
and-zero : ∀ (x : Trit) → T₀ ∧T x ≡ T₀
and-zero T₀ = refl
and-zero T₁ = refl
and-zero T₂ = refl

-- OR 单位: T₀ ∨T x = x (恒通)
or-identity : ∀ (x : Trit) → T₀ ∨T x ≡ x
or-identity T₀ = refl
or-identity T₁ = refl
or-identity T₂ = refl

--------------------------------------------------------------------------------
-- 2. NOT 门: 三值取反
-- 经典: NOT(0)=1, NOT(1)=0
-- 三值: NOT(T₀)=T₂, NOT(T₁)=T₁, NOT(T₂)=T₀
-- 即 negate: GF(3) 加法逆元 (-x mod 3)
--------------------------------------------------------------------------------

not-gate : Trit → Trit
not-gate T₀ = T₂
not-gate T₁ = T₁
not-gate T₂ = T₀

-- NOT 门验证 (3 case)
not-T₀ : not-gate T₀ ≡ T₂
not-T₀ = refl

not-T₁ : not-gate T₁ ≡ T₁
not-T₁ = refl

not-T₂ : not-gate T₂ ≡ T₀
not-T₂ = refl

-- NOT 是对合: NOT(NOT(x)) = x
not-involution : ∀ (x : Trit) → not-gate (not-gate x) ≡ x
not-involution T₀ = refl
not-involution T₁ = refl
not-involution T₂ = refl

--------------------------------------------------------------------------------
-- 3. De Morgan 定律: NOT 与 AND/OR 的对偶性
-- 三值 Kleene 否定满足 De Morgan 律
-- 证明: 9 case 穷举 refl
--------------------------------------------------------------------------------

-- De Morgan 第一定律: NOT(x ∧ y) ≡ NOT(x) ∨ NOT(y)
de-morgan-∧ : ∀ x y → not-gate (x ∧T y) ≡ not-gate x ∨T not-gate y
de-morgan-∧ T₀ T₀ = refl
de-morgan-∧ T₀ T₁ = refl
de-morgan-∧ T₀ T₂ = refl
de-morgan-∧ T₁ T₀ = refl
de-morgan-∧ T₁ T₁ = refl
de-morgan-∧ T₁ T₂ = refl
de-morgan-∧ T₂ T₀ = refl
de-morgan-∧ T₂ T₁ = refl
de-morgan-∧ T₂ T₂ = refl

-- De Morgan 第二定律: NOT(x ∨ y) ≡ NOT(x) ∧ NOT(y)
de-morgan-∨ : ∀ x y → not-gate (x ∨T y) ≡ not-gate x ∧T not-gate y
de-morgan-∨ T₀ T₀ = refl
de-morgan-∨ T₀ T₁ = refl
de-morgan-∨ T₀ T₂ = refl
de-morgan-∨ T₁ T₀ = refl
de-morgan-∨ T₁ T₁ = refl
de-morgan-∨ T₁ T₂ = refl
de-morgan-∨ T₂ T₀ = refl
de-morgan-∨ T₂ T₁ = refl
de-morgan-∨ T₂ T₂ = refl

--------------------------------------------------------------------------------
-- 4. AND = min, OR = max: 格论刻画
-- _∧T_ 是最大下界 (GLB/meet), _∨T_ 是最小上界 (LUB/join)
-- 基于 DomainProofs 中的全序 ≤T
--------------------------------------------------------------------------------

-- AND 下界性: x ∧T y ≤T x
and-lowerˡ : ∀ x y → (x ∧T y) ≤T x
and-lowerˡ T₀ T₀ = le-00
and-lowerˡ T₀ T₁ = le-00
and-lowerˡ T₀ T₂ = le-00
and-lowerˡ T₁ T₀ = le-01
and-lowerˡ T₁ T₁ = le-11
and-lowerˡ T₁ T₂ = le-11
and-lowerˡ T₂ T₀ = le-02
and-lowerˡ T₂ T₁ = le-12
and-lowerˡ T₂ T₂ = le-22

-- AND 下界性: x ∧T y ≤T y
and-lowerʳ : ∀ x y → (x ∧T y) ≤T y
and-lowerʳ T₀ T₀ = le-00
and-lowerʳ T₀ T₁ = le-01
and-lowerʳ T₀ T₂ = le-02
and-lowerʳ T₁ T₀ = le-00
and-lowerʳ T₁ T₁ = le-11
and-lowerʳ T₁ T₂ = le-12
and-lowerʳ T₂ T₀ = le-00
and-lowerʳ T₂ T₁ = le-11
and-lowerʳ T₂ T₂ = le-22

-- AND 最大性 (GLB): z ≤T x → z ≤T y → z ≤T x ∧T y
and-glb : ∀ x y z → z ≤T x → z ≤T y → z ≤T (x ∧T y)
-- z = T₀
and-glb T₀ y .T₀ le-00 _ = le-00
and-glb T₁ T₀ .T₀ le-01 le-00 = le-00
and-glb T₁ T₁ .T₀ le-01 le-01 = le-01
and-glb T₁ T₂ .T₀ le-01 le-02 = le-01
and-glb T₂ T₀ .T₀ le-02 le-00 = le-00
and-glb T₂ T₁ .T₀ le-02 le-01 = le-01
and-glb T₂ T₂ .T₀ le-02 le-02 = le-02
-- z = T₁
and-glb T₁ T₁ .T₁ le-11 le-11 = le-11
and-glb T₁ T₂ .T₁ le-11 le-12 = le-11
and-glb T₂ T₁ .T₁ le-12 le-11 = le-11
and-glb T₂ T₂ .T₁ le-12 le-12 = le-12
-- z = T₂
and-glb T₂ T₂ .T₂ le-22 le-22 = le-22

-- OR 上界性: x ≤T x ∨T y
or-upperˡ : ∀ x y → x ≤T (x ∨T y)
or-upperˡ T₀ T₀ = le-00
or-upperˡ T₀ T₁ = le-01
or-upperˡ T₀ T₂ = le-02
or-upperˡ T₁ T₀ = le-11
or-upperˡ T₁ T₁ = le-11
or-upperˡ T₁ T₂ = le-12
or-upperˡ T₂ T₀ = le-22
or-upperˡ T₂ T₁ = le-22
or-upperˡ T₂ T₂ = le-22

-- OR 上界性: y ≤T x ∨T y
or-upperʳ : ∀ x y → y ≤T (x ∨T y)
or-upperʳ T₀ T₀ = le-00
or-upperʳ T₀ T₁ = le-11
or-upperʳ T₀ T₂ = le-22
or-upperʳ T₁ T₀ = le-01
or-upperʳ T₁ T₁ = le-11
or-upperʳ T₁ T₂ = le-22
or-upperʳ T₂ T₀ = le-02
or-upperʳ T₂ T₁ = le-12
or-upperʳ T₂ T₂ = le-22

-- OR 最小性 (LUB): x ≤T z → y ≤T z → x ∨T y ≤T z
or-lub : ∀ x y z → x ≤T z → y ≤T z → (x ∨T y) ≤T z
or-lub T₀ y z _ q = q
or-lub T₁ T₀ .T₁ le-11 le-01 = le-11
or-lub T₁ T₀ .T₂ le-12 le-02 = le-12
or-lub T₁ T₁ .T₁ le-11 le-11 = le-11
or-lub T₁ T₁ .T₂ le-12 le-12 = le-12
or-lub T₁ T₂ .T₁ le-11 ()
or-lub T₁ T₂ .T₂ le-12 le-22 = le-22
or-lub T₂ y .T₂ le-22 _ = le-22

--------------------------------------------------------------------------------
-- 5. 常数生成: 从门电路构造常数函数
--------------------------------------------------------------------------------

-- OR 零元: T₂ ∨T x ≡ T₂ (对偶于 and-zero)
or-annihilator : ∀ x → T₂ ∨T x ≡ T₂
or-annihilator T₀ = refl
or-annihilator T₁ = refl
or-annihilator T₂ = refl

-- T₁ 常数由门构造: (x ∧T T₁) ∨T (NOT(x) ∧T T₁) ≡ T₁
-- 物理意义: T₁ 是 AND/OR 格的中间元素, 截断后取 OR 恒等于 T₁
const-T₁-via-gates : ∀ x → (x ∧T T₁) ∨T (not-gate x ∧T T₁) ≡ T₁
const-T₁-via-gates T₀ = refl
const-T₁-via-gates T₁ = refl
const-T₁-via-gates T₂ = refl

-- 常数生成总结:
--   const-T₀(x) = T₀ ∧T x ≡ T₀       (and-zero, 已有)
--   const-T₁(x) = 上述门构造 ≡ T₁     (const-T₁-via-gates)
--   const-T₂(x) = T₂ ∨T x ≡ T₂       (or-annihilator)
--   id(x)       = NOT(NOT(x)) ≡ x     (not-involution, 已有)

--------------------------------------------------------------------------------
-- 6. 三值逻辑函数完备性
-- 定理: {∧T, ∨T, NOT, ⊕, 常数} 生成全部 3³ = 27 个单变量函数
-- 证明: 构造选择子 Δ_a, 用选择子分解任意真值表
--   f(x) = (Δ₀(x) ∧T f(T₀)) ∨T (Δ₁(x) ∧T f(T₁)) ∨T (Δ₂(x) ∧T f(T₂))
-- 注: ⊕ (GF(3) 加法) 是必需的——仅 {∧T, ∨T, NOT, 常数} 生成 11 个正则函数
--------------------------------------------------------------------------------

-- 6a. 选择子: sel_a(x) = T₁ 当 x = a, T₀ 否则
-- 门构造: sel_a(x) = (x ⊕ ā) ∧T NOT(x ⊕ ā)

sel₀ : Trit → Trit
sel₀ T₀ = T₁
sel₀ T₁ = T₀
sel₀ T₂ = T₀

sel₁ : Trit → Trit
sel₁ T₀ = T₀
sel₁ T₁ = T₁
sel₁ T₂ = T₀

sel₂ : Trit → Trit
sel₂ T₀ = T₀
sel₂ T₁ = T₀
sel₂ T₂ = T₁

-- 选择子的门电路构造 (穷举验证)
sel₀-gate : ∀ x → sel₀ x ≡ (x ⊕ T₁) ∧T not-gate (x ⊕ T₁)
sel₀-gate T₀ = refl
sel₀-gate T₁ = refl
sel₀-gate T₂ = refl

sel₁-gate : ∀ x → sel₁ x ≡ x ∧T not-gate x
sel₁-gate T₀ = refl
sel₁-gate T₁ = refl
sel₁-gate T₂ = refl

sel₂-gate : ∀ x → sel₂ x ≡ (x ⊕ T₂) ∧T not-gate (x ⊕ T₂)
sel₂-gate T₀ = refl
sel₂-gate T₁ = refl
sel₂-gate T₂ = refl

-- 6b. 完全选择子: Δ_a(x) = sel_a(x) ⊕ sel_a(x)
-- GF(3) 倍频: T₁ ⊕ T₁ = T₂, T₀ ⊕ T₀ = T₀
-- Δ_a(x) = T₂ 当 x = a, T₀ 否则

Δ₀ : Trit → Trit
Δ₀ x = sel₀ x ⊕ sel₀ x

Δ₁ : Trit → Trit
Δ₁ x = sel₁ x ⊕ sel₁ x

Δ₂ : Trit → Trit
Δ₂ x = sel₂ x ⊕ sel₂ x

-- 完全选择子验证 (9 case)
Δ₀-select : Δ₀ T₀ ≡ T₂
Δ₀-select = refl

Δ₀-reject₁ : Δ₀ T₁ ≡ T₀
Δ₀-reject₁ = refl

Δ₀-reject₂ : Δ₀ T₂ ≡ T₀
Δ₀-reject₂ = refl

Δ₁-reject₀ : Δ₁ T₀ ≡ T₀
Δ₁-reject₀ = refl

Δ₁-select : Δ₁ T₁ ≡ T₂
Δ₁-select = refl

Δ₁-reject₂ : Δ₁ T₂ ≡ T₀
Δ₁-reject₂ = refl

Δ₂-reject₀ : Δ₂ T₀ ≡ T₀
Δ₂-reject₀ = refl

Δ₂-reject₁ : Δ₂ T₁ ≡ T₀
Δ₂-reject₁ = refl

Δ₂-select : Δ₂ T₂ ≡ T₂
Δ₂-select = refl

-- 6c. 真值表与选择子分解

-- 单变量函数由真值表 (f(T₀), f(T₁), f(T₂)) 唯一确定
-- 3³ = 27 个真值表 ↔ 27 个函数
TruthTable : Set
TruthTable = Trit × Trit × Trit

tt-fun : TruthTable → Trit → Trit
tt-fun (a , b , _) T₀ = a
tt-fun (_ , b , _) T₁ = b
tt-fun (_ , _ , c) T₂ = c

-- 选择子分解: f(x) = (Δ₀(x) ∧T a) ∨T (Δ₁(x) ∧T b)) ∨T (Δ₂(x) ∧T c)
decompose : TruthTable → Trit → Trit
decompose (a , b , c) x =
  ((Δ₀ x ∧T a) ∨T (Δ₁ x ∧T b)) ∨T (Δ₂ x ∧T c)

-- 6d. 完备性定理: 选择子分解精确重构任意真值表
-- 证明: 9 case (对每个 x, 只需 case split 对应的输出值)
-- x = T₀: Δ₀(T₀) = T₂ 选中 a, Δ₁(T₀) = Δ₂(T₀) = T₀ 屏蔽 b, c
-- x = T₁: Δ₁(T₁) = T₂ 选中 b, Δ₀(T₁) = Δ₂(T₁) = T₀ 屏蔽 a, c
-- x = T₂: Δ₂(T₂) = T₂ 选中 c, Δ₀(T₂) = Δ₁(T₂) = T₀ 屏蔽 a, b
completeness : ∀ tt x → decompose tt x ≡ tt-fun tt x
completeness (T₀ , b , c) T₀ = refl
completeness (T₁ , b , c) T₀ = refl
completeness (T₂ , b , c) T₀ = refl
completeness (a , T₀ , c) T₁ = refl
completeness (a , T₁ , c) T₁ = refl
completeness (a , T₂ , c) T₁ = refl
completeness (a , b , T₀) T₂ = refl
completeness (a , b , T₁) T₂ = refl
completeness (a , b , T₂) T₂ = refl

-- 6e. 函数计数: 3³ = 27
function-count : ℕ
function-count = 3 * 3 * 3

function-count-27 : function-count ≡ 27
function-count-27 = refl
