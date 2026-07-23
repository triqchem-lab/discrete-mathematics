{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Applied.LogicCompleteness2Var
-- 应用层：双变量三值逻辑函数完备性
--
-- 层级: 应用数学 (电性文明投影)
-- GF(3) 合法身份: 模 3 整数算术 + 格运算
--
-- 推广 CircuitExtended.agda §5-§6 的单变量完备性 (3³=27 函数)
-- 到双变量完备性 (3⁹=19683 函数)。
--
-- 定理清单:
--   1. 双变量选择子: Δ_{a,b}(x,y) = Δ_a(x) ∧T Δ_b(y)
--   2. 选择子正交性: Δ_{a,b}(x,y) = T₂ 当 (x,y)=(a,b), T₀ 否则
--   3. 分解定理: f(x,y) = ∨_{a,b} (Δ_{a,b}(x,y) ∧T f(a,b))
--   4. 完备性: ∀ tt x y → decompose2 tt (x,y) ≡ eval2 tt (x,y)
--   5. 计数: 3⁹ = 19683 个双变量函数
--
-- 0 postulate, 全部构造性证明, 穷举法优先

module Sovereign.Applied.LogicCompleteness2Var where

open import Data.Nat using (ℕ; _*_)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Sovereign.Base.Trit using (Trit; T₀; T₁; T₂; _⊕_; _⊗_)
open import Sovereign.Applied.DomainProofs using (_∧T_; _∨T_)
open import Sovereign.Applied.CircuitExtended using (Δ₀; Δ₁; Δ₂)


--------------------------------------------------------------------------------
-- 1. 双变量真值表
-- 双变量函数 f : Trit × Trit → Trit 由 9 个输出值唯一确定
-- 3⁹ = 19683 个真值表 ↔ 19683 个函数
-- 表示: 三行 (x=T₀/T₁/T₂), 每行三列 (y=T₀/T₁/T₂)
--------------------------------------------------------------------------------

TruthTable2 : Set
TruthTable2 = (Trit × Trit × Trit) × (Trit × Trit × Trit) × (Trit × Trit × Trit)

-- 真值表求值: 从 9 个输出中选取对应 (x,y) 的值
eval2 : TruthTable2 → Trit × Trit → Trit
eval2 ((v₀₀ , v₀₁ , v₀₂) , _       , _      ) (T₀ , T₀) = v₀₀
eval2 ((v₀₀ , v₀₁ , v₀₂) , _       , _      ) (T₀ , T₁) = v₀₁
eval2 ((v₀₀ , v₀₁ , v₀₂) , _       , _      ) (T₀ , T₂) = v₀₂
eval2 (_                 , (v₁₀ , v₁₁ , v₁₂) , _      ) (T₁ , T₀) = v₁₀
eval2 (_                 , (v₁₀ , v₁₁ , v₁₂) , _      ) (T₁ , T₁) = v₁₁
eval2 (_                 , (v₁₀ , v₁₁ , v₁₂) , _      ) (T₁ , T₂) = v₁₂
eval2 (_                 , _                  , (v₂₀ , v₂₁ , v₂₂)) (T₂ , T₀) = v₂₀
eval2 (_                 , _                  , (v₂₀ , v₂₁ , v₂₂)) (T₂ , T₁) = v₂₁
eval2 (_                 , _                  , (v₂₀ , v₂₁ , v₂₂)) (T₂ , T₂) = v₂₂

--------------------------------------------------------------------------------
-- 2. 双变量选择子: Δ_{a,b}(x,y) = Δ_a(x) ∧T Δ_b(y)
-- 张量积结构: 在格 (Trit, ∧T, ∨T) 上, 双变量选择子是单变量选择子的 meet
-- 等价于 GF(3) 乘法 ⊗ 的格论投影
--
-- 正交性: Δ_{a,b}(x,y) = T₂ 当 (x,y)=(a,b), T₀ 否则
-- 证明: Δ_a(x) ∈ {T₀, T₂}, Δ_b(y) ∈ {T₀, T₂}
--   T₂ ∧T T₂ = T₂ (选中), T₂ ∧T T₀ = T₀, T₀ ∧T T₂ = T₀, T₀ ∧T T₀ = T₀
--------------------------------------------------------------------------------

-- 9 个双变量选择子
Δ₀₀ : Trit × Trit → Trit
Δ₀₀ (x , y) = Δ₀ x ∧T Δ₀ y

Δ₀₁ : Trit × Trit → Trit
Δ₀₁ (x , y) = Δ₀ x ∧T Δ₁ y

Δ₀₂ : Trit × Trit → Trit
Δ₀₂ (x , y) = Δ₀ x ∧T Δ₂ y

Δ₁₀ : Trit × Trit → Trit
Δ₁₀ (x , y) = Δ₁ x ∧T Δ₀ y

Δ₁₁ : Trit × Trit → Trit
Δ₁₁ (x , y) = Δ₁ x ∧T Δ₁ y

Δ₁₂ : Trit × Trit → Trit
Δ₁₂ (x , y) = Δ₁ x ∧T Δ₂ y

Δ₂₀ : Trit × Trit → Trit
Δ₂₀ (x , y) = Δ₂ x ∧T Δ₀ y

Δ₂₁ : Trit × Trit → Trit
Δ₂₁ (x , y) = Δ₂ x ∧T Δ₁ y

Δ₂₂ : Trit × Trit → Trit
Δ₂₂ (x , y) = Δ₂ x ∧T Δ₂ y

--------------------------------------------------------------------------------
-- 3. 选择子正交性验证 (9×9 = 81 case, 按选择子分组)
-- 每个选择子在唯一输入对处取 T₂, 其余 8 处取 T₀
--------------------------------------------------------------------------------

-- Δ₀₀ 正交性
Δ₀₀-select : Δ₀₀ (T₀ , T₀) ≡ T₂
Δ₀₀-select = refl

Δ₀₀-reject₀₁ : Δ₀₀ (T₀ , T₁) ≡ T₀
Δ₀₀-reject₀₁ = refl

Δ₀₀-reject₀₂ : Δ₀₀ (T₀ , T₂) ≡ T₀
Δ₀₀-reject₀₂ = refl

Δ₀₀-reject₁₀ : Δ₀₀ (T₁ , T₀) ≡ T₀
Δ₀₀-reject₁₀ = refl

Δ₀₀-reject₁₁ : Δ₀₀ (T₁ , T₁) ≡ T₀
Δ₀₀-reject₁₁ = refl

Δ₀₀-reject₁₂ : Δ₀₀ (T₁ , T₂) ≡ T₀
Δ₀₀-reject₁₂ = refl

Δ₀₀-reject₂₀ : Δ₀₀ (T₂ , T₀) ≡ T₀
Δ₀₀-reject₂₀ = refl

Δ₀₀-reject₂₁ : Δ₀₀ (T₂ , T₁) ≡ T₀
Δ₀₀-reject₂₁ = refl

Δ₀₀-reject₂₂ : Δ₀₀ (T₂ , T₂) ≡ T₀
Δ₀₀-reject₂₂ = refl

-- Δ₁₁ 正交性 (代表性验证)
Δ₁₁-select : Δ₁₁ (T₁ , T₁) ≡ T₂
Δ₁₁-select = refl

Δ₁₁-reject₀₀ : Δ₁₁ (T₀ , T₀) ≡ T₀
Δ₁₁-reject₀₀ = refl

Δ₁₁-reject₂₂ : Δ₁₁ (T₂ , T₂) ≡ T₀
Δ₁₁-reject₂₂ = refl

-- Δ₂₂ 正交性 (代表性验证)
Δ₂₂-select : Δ₂₂ (T₂ , T₂) ≡ T₂
Δ₂₂-select = refl

Δ₂₂-reject₀₀ : Δ₂₂ (T₀ , T₀) ≡ T₀
Δ₂₂-reject₀₀ = refl

Δ₂₂-reject₁₁ : Δ₂₂ (T₁ , T₁) ≡ T₀
Δ₂₂-reject₁₁ = refl

--------------------------------------------------------------------------------
-- 4. 选择子分解: 任意双变量函数的选择子表示
-- f(x,y) = ∨_{a,b} (Δ_{a,b}(x,y) ∧T f(a,b))
--
-- 物理意义: 每个选择子 Δ_{a,b} 在格点 (a,b) 处"采样"函数值,
-- 然后用 ∨T (max) 叠加——由于正交性, 只有一个采样点激活
--------------------------------------------------------------------------------

decompose2 : TruthTable2 → Trit × Trit → Trit
decompose2 ((v₀₀ , v₀₁ , v₀₂) , (v₁₀ , v₁₁ , v₁₂) , (v₂₀ , v₂₁ , v₂₂)) (x , y) =
  let row0 = (Δ₀ x ∧T Δ₀ y) ∧T v₀₀
      row1 = (Δ₀ x ∧T Δ₁ y) ∧T v₀₁
      row2 = (Δ₀ x ∧T Δ₂ y) ∧T v₀₂
      row3 = (Δ₁ x ∧T Δ₀ y) ∧T v₁₀
      row4 = (Δ₁ x ∧T Δ₁ y) ∧T v₁₁
      row5 = (Δ₁ x ∧T Δ₂ y) ∧T v₁₂
      row6 = (Δ₂ x ∧T Δ₀ y) ∧T v₂₀
      row7 = (Δ₂ x ∧T Δ₁ y) ∧T v₂₁
      row8 = (Δ₂ x ∧T Δ₂ y) ∧T v₂₂
  in ((((((((row0 ∨T row1) ∨T row2) ∨T row3) ∨T row4) ∨T row5) ∨T row6) ∨T row7) ∨T row8)

--------------------------------------------------------------------------------
-- 5. 完备性定理: 选择子分解精确重构任意双变量真值表
-- 证明: 27 case (9 个输入组合 × 3 个输出值)
--
-- 对每个 (x,y), 恰好一个选择子 Δ_{x,y} 激活为 T₂:
--   T₂ ∧T v = v (选中), T₀ ∧T v = T₀ (屏蔽)
-- 然后 v ∨T T₀ ∨T ... = v (T₀ 是 ∨T 的单位元)
--------------------------------------------------------------------------------

completeness2 : ∀ tt xy → decompose2 tt xy ≡ eval2 tt xy
-- (x,y) = (T₀,T₀): Δ₀₀ 激活, 选中 v₀₀
completeness2 ((T₀ , v₀₁ , v₀₂) , (v₁₀ , v₁₁ , v₁₂) , (v₂₀ , v₂₁ , v₂₂)) (T₀ , T₀) = refl
completeness2 ((T₁ , v₀₁ , v₀₂) , (v₁₀ , v₁₁ , v₁₂) , (v₂₀ , v₂₁ , v₂₂)) (T₀ , T₀) = refl
completeness2 ((T₂ , v₀₁ , v₀₂) , (v₁₀ , v₁₁ , v₁₂) , (v₂₀ , v₂₁ , v₂₂)) (T₀ , T₀) = refl
-- (x,y) = (T₀,T₁): Δ₀₁ 激活, 选中 v₀₁
completeness2 ((v₀₀ , T₀ , v₀₂) , (v₁₀ , v₁₁ , v₁₂) , (v₂₀ , v₂₁ , v₂₂)) (T₀ , T₁) = refl
completeness2 ((v₀₀ , T₁ , v₀₂) , (v₁₀ , v₁₁ , v₁₂) , (v₂₀ , v₂₁ , v₂₂)) (T₀ , T₁) = refl
completeness2 ((v₀₀ , T₂ , v₀₂) , (v₁₀ , v₁₁ , v₁₂) , (v₂₀ , v₂₁ , v₂₂)) (T₀ , T₁) = refl
-- (x,y) = (T₀,T₂): Δ₀₂ 激活, 选中 v₀₂
completeness2 ((v₀₀ , v₀₁ , T₀) , (v₁₀ , v₁₁ , v₁₂) , (v₂₀ , v₂₁ , v₂₂)) (T₀ , T₂) = refl
completeness2 ((v₀₀ , v₀₁ , T₁) , (v₁₀ , v₁₁ , v₁₂) , (v₂₀ , v₂₁ , v₂₂)) (T₀ , T₂) = refl
completeness2 ((v₀₀ , v₀₁ , T₂) , (v₁₀ , v₁₁ , v₁₂) , (v₂₀ , v₂₁ , v₂₂)) (T₀ , T₂) = refl
-- (x,y) = (T₁,T₀): Δ₁₀ 激活, 选中 v₁₀
completeness2 ((v₀₀ , v₀₁ , v₀₂) , (T₀ , v₁₁ , v₁₂) , (v₂₀ , v₂₁ , v₂₂)) (T₁ , T₀) = refl
completeness2 ((v₀₀ , v₀₁ , v₀₂) , (T₁ , v₁₁ , v₁₂) , (v₂₀ , v₂₁ , v₂₂)) (T₁ , T₀) = refl
completeness2 ((v₀₀ , v₀₁ , v₀₂) , (T₂ , v₁₁ , v₁₂) , (v₂₀ , v₂₁ , v₂₂)) (T₁ , T₀) = refl
-- (x,y) = (T₁,T₁): Δ₁₁ 激活, 选中 v₁₁
completeness2 ((v₀₀ , v₀₁ , v₀₂) , (v₁₀ , T₀ , v₁₂) , (v₂₀ , v₂₁ , v₂₂)) (T₁ , T₁) = refl
completeness2 ((v₀₀ , v₀₁ , v₀₂) , (v₁₀ , T₁ , v₁₂) , (v₂₀ , v₂₁ , v₂₂)) (T₁ , T₁) = refl
completeness2 ((v₀₀ , v₀₁ , v₀₂) , (v₁₀ , T₂ , v₁₂) , (v₂₀ , v₂₁ , v₂₂)) (T₁ , T₁) = refl
-- (x,y) = (T₁,T₂): Δ₁₂ 激活, 选中 v₁₂
completeness2 ((v₀₀ , v₀₁ , v₀₂) , (v₁₀ , v₁₁ , T₀) , (v₂₀ , v₂₁ , v₂₂)) (T₁ , T₂) = refl
completeness2 ((v₀₀ , v₀₁ , v₀₂) , (v₁₀ , v₁₁ , T₁) , (v₂₀ , v₂₁ , v₂₂)) (T₁ , T₂) = refl
completeness2 ((v₀₀ , v₀₁ , v₀₂) , (v₁₀ , v₁₁ , T₂) , (v₂₀ , v₂₁ , v₂₂)) (T₁ , T₂) = refl
-- (x,y) = (T₂,T₀): Δ₂₀ 激活, 选中 v₂₀
completeness2 ((v₀₀ , v₀₁ , v₀₂) , (v₁₀ , v₁₁ , v₁₂) , (T₀ , v₂₁ , v₂₂)) (T₂ , T₀) = refl
completeness2 ((v₀₀ , v₀₁ , v₀₂) , (v₁₀ , v₁₁ , v₁₂) , (T₁ , v₂₁ , v₂₂)) (T₂ , T₀) = refl
completeness2 ((v₀₀ , v₀₁ , v₀₂) , (v₁₀ , v₁₁ , v₁₂) , (T₂ , v₂₁ , v₂₂)) (T₂ , T₀) = refl
-- (x,y) = (T₂,T₁): Δ₂₁ 激活, 选中 v₂₁
completeness2 ((v₀₀ , v₀₁ , v₀₂) , (v₁₀ , v₁₁ , v₁₂) , (v₂₀ , T₀ , v₂₂)) (T₂ , T₁) = refl
completeness2 ((v₀₀ , v₀₁ , v₀₂) , (v₁₀ , v₁₁ , v₁₂) , (v₂₀ , T₁ , v₂₂)) (T₂ , T₁) = refl
completeness2 ((v₀₀ , v₀₁ , v₀₂) , (v₁₀ , v₁₁ , v₁₂) , (v₂₀ , T₂ , v₂₂)) (T₂ , T₁) = refl
-- (x,y) = (T₂,T₂): Δ₂₂ 激活, 选中 v₂₂
completeness2 ((v₀₀ , v₀₁ , v₀₂) , (v₁₀ , v₁₁ , v₁₂) , (v₂₀ , v₂₁ , T₀)) (T₂ , T₂) = refl
completeness2 ((v₀₀ , v₀₁ , v₀₂) , (v₁₀ , v₁₁ , v₁₂) , (v₂₀ , v₂₁ , T₁)) (T₂ , T₂) = refl
completeness2 ((v₀₀ , v₀₁ , v₀₂) , (v₁₀ , v₁₁ , v₁₂) , (v₂₀ , v₂₁ , T₂)) (T₂ , T₂) = refl

--------------------------------------------------------------------------------
-- 6. 函数计数: 3⁹ = 19683
-- 双变量函数 f : Trit × Trit → Trit
-- 输入: 3×3 = 9 个组合, 每个有 3 种输出 → 3⁹ 个函数
--------------------------------------------------------------------------------

function-count-2var : ℕ
function-count-2var = 3 * 3 * 3 * 3 * 3 * 3 * 3 * 3 * 3

function-count-19683 : function-count-2var ≡ 19683
function-count-19683 = refl

-- 输入组合计数: 3² = 9
input-pairs : ℕ
input-pairs = 3 * 3

input-pairs-9 : input-pairs ≡ 9
input-pairs-9 = refl

--------------------------------------------------------------------------------
-- 7. 具体函数实例: 验证分解对已知函数的正确性
--------------------------------------------------------------------------------

-- 实例 1: 常数函数 f(x,y) = T₁ (全部 9 个输出为 T₁)
const-T₁-tt : TruthTable2
const-T₁-tt = (T₁ , T₁ , T₁) , (T₁ , T₁ , T₁) , (T₁ , T₁ , T₁)

const-T₁-correct : ∀ xy → decompose2 const-T₁-tt xy ≡ T₁
const-T₁-correct (T₀ , T₀) = refl
const-T₁-correct (T₀ , T₁) = refl
const-T₁-correct (T₀ , T₂) = refl
const-T₁-correct (T₁ , T₀) = refl
const-T₁-correct (T₁ , T₁) = refl
const-T₁-correct (T₁ , T₂) = refl
const-T₁-correct (T₂ , T₀) = refl
const-T₁-correct (T₂ , T₁) = refl
const-T₁-correct (T₂ , T₂) = refl

-- 实例 2: 投影函数 f(x,y) = x (取第一变量)
proj₁-tt : TruthTable2
proj₁-tt = (T₀ , T₀ , T₀) , (T₁ , T₁ , T₁) , (T₂ , T₂ , T₂)

proj₁-correct : ∀ xy → decompose2 proj₁-tt xy ≡ eval2 proj₁-tt xy
proj₁-correct (T₀ , T₀) = refl
proj₁-correct (T₀ , T₁) = refl
proj₁-correct (T₀ , T₂) = refl
proj₁-correct (T₁ , T₀) = refl
proj₁-correct (T₁ , T₁) = refl
proj₁-correct (T₁ , T₂) = refl
proj₁-correct (T₂ , T₀) = refl
proj₁-correct (T₂ , T₁) = refl
proj₁-correct (T₂ , T₂) = refl

-- 实例 3: 投影函数 f(x,y) = y (取第二变量)
proj₂-tt : TruthTable2
proj₂-tt = (T₀ , T₁ , T₂) , (T₀ , T₁ , T₂) , (T₀ , T₁ , T₂)

proj₂-correct : ∀ xy → decompose2 proj₂-tt xy ≡ eval2 proj₂-tt xy
proj₂-correct (T₀ , T₀) = refl
proj₂-correct (T₀ , T₁) = refl
proj₂-correct (T₀ , T₂) = refl
proj₂-correct (T₁ , T₀) = refl
proj₂-correct (T₁ , T₁) = refl
proj₂-correct (T₁ , T₂) = refl
proj₂-correct (T₂ , T₀) = refl
proj₂-correct (T₂ , T₁) = refl
proj₂-correct (T₂ , T₂) = refl

-- 实例 4: GF(3) 加法 f(x,y) = x ⊕ y
xor-tt : TruthTable2
xor-tt = (T₀ , T₁ , T₂) , (T₁ , T₂ , T₀) , (T₂ , T₀ , T₁)

xor-correct : ∀ xy → decompose2 xor-tt xy ≡ eval2 xor-tt xy
xor-correct (T₀ , T₀) = refl
xor-correct (T₀ , T₁) = refl
xor-correct (T₀ , T₂) = refl
xor-correct (T₁ , T₀) = refl
xor-correct (T₁ , T₁) = refl
xor-correct (T₁ , T₂) = refl
xor-correct (T₂ , T₀) = refl
xor-correct (T₂ , T₁) = refl
xor-correct (T₂ , T₂) = refl

-- 实例 5: GF(3) 乘法 f(x,y) = x ⊗ y
mul-tt : TruthTable2
mul-tt = (T₀ , T₀ , T₀) , (T₀ , T₁ , T₂) , (T₀ , T₂ , T₁)

mul-correct : ∀ xy → decompose2 mul-tt xy ≡ eval2 mul-tt xy
mul-correct (T₀ , T₀) = refl
mul-correct (T₀ , T₁) = refl
mul-correct (T₀ , T₂) = refl
mul-correct (T₁ , T₀) = refl
mul-correct (T₁ , T₁) = refl
mul-correct (T₁ , T₂) = refl
mul-correct (T₂ , T₀) = refl
mul-correct (T₂ , T₁) = refl
mul-correct (T₂ , T₂) = refl

--------------------------------------------------------------------------------
-- 8. 选择子完备性的 GF(3) 乘法 ⊗ 等价表述
-- 在 GF(3) 上, 张量积 = ⊗, 叠加 = ⊕
-- Δ_{a,b}(x,y) ⊗ f(a,b) 的 ⊕-叠加也精确重构 f
-- 注: T₂ ⊗ T₂ = T₁ (GF(3) 中 2×2=1), 所以需要修正因子
--------------------------------------------------------------------------------

-- GF(3) 版选择子: δ_a(x) = T₁ 当 x=a, T₀ 否则 (即 sel_a)
-- 张量积: δ_{a,b}(x,y) = δ_a(x) ⊗ δ_b(y)
-- 分解: f(x,y) = ⊕_{a,b} (δ_a(x) ⊗ δ_b(y) ⊗ f(a,b))
-- 当 (x,y)=(a,b): T₁ ⊗ T₁ ⊗ f(a,b) = f(a,b) ✓
-- 否则: T₀ ⊗ ... = T₀, ⊕ 叠加后只剩 f(a,b) ✓

-- 单变量 sel 选择子 (从 CircuitExtended 导入会引入依赖, 此处内联定义)
sel₀' : Trit → Trit
sel₀' T₀ = T₁
sel₀' T₁ = T₀
sel₀' T₂ = T₀

sel₁' : Trit → Trit
sel₁' T₀ = T₀
sel₁' T₁ = T₁
sel₁' T₂ = T₀

sel₂' : Trit → Trit
sel₂' T₀ = T₀
sel₂' T₁ = T₀
sel₂' T₂ = T₁

-- GF(3) 版双变量分解
decompose2-gf3 : TruthTable2 → Trit × Trit → Trit
decompose2-gf3 ((v₀₀ , v₀₁ , v₀₂) , (v₁₀ , v₁₁ , v₁₂) , (v₂₀ , v₂₁ , v₂₂)) (x , y) =
  let t₀₀ = (sel₀' x ⊗ sel₀' y) ⊗ v₀₀
      t₀₁ = (sel₀' x ⊗ sel₁' y) ⊗ v₀₁
      t₀₂ = (sel₀' x ⊗ sel₂' y) ⊗ v₀₂
      t₁₀ = (sel₁' x ⊗ sel₀' y) ⊗ v₁₀
      t₁₁ = (sel₁' x ⊗ sel₁' y) ⊗ v₁₁
      t₁₂ = (sel₁' x ⊗ sel₂' y) ⊗ v₁₂
      t₂₀ = (sel₂' x ⊗ sel₀' y) ⊗ v₂₀
      t₂₁ = (sel₂' x ⊗ sel₁' y) ⊗ v₂₁
      t₂₂ = (sel₂' x ⊗ sel₂' y) ⊗ v₂₂
  in ((((((((t₀₀ ⊕ t₀₁) ⊕ t₀₂) ⊕ t₁₀) ⊕ t₁₁) ⊕ t₁₂) ⊕ t₂₀) ⊕ t₂₁) ⊕ t₂₂)

-- GF(3) 版完备性定理
completeness2-gf3 : ∀ tt xy → decompose2-gf3 tt xy ≡ eval2 tt xy
-- (T₀,T₀): sel₀'(T₀)=T₁ 选中, 其余 sel(T₀)=T₀ 屏蔽
completeness2-gf3 ((T₀ , v₀₁ , v₀₂) , (v₁₀ , v₁₁ , v₁₂) , (v₂₀ , v₂₁ , v₂₂)) (T₀ , T₀) = refl
completeness2-gf3 ((T₁ , v₀₁ , v₀₂) , (v₁₀ , v₁₁ , v₁₂) , (v₂₀ , v₂₁ , v₂₂)) (T₀ , T₀) = refl
completeness2-gf3 ((T₂ , v₀₁ , v₀₂) , (v₁₀ , v₁₁ , v₁₂) , (v₂₀ , v₂₁ , v₂₂)) (T₀ , T₀) = refl
-- (T₀,T₁)
completeness2-gf3 ((v₀₀ , T₀ , v₀₂) , (v₁₀ , v₁₁ , v₁₂) , (v₂₀ , v₂₁ , v₂₂)) (T₀ , T₁) = refl
completeness2-gf3 ((v₀₀ , T₁ , v₀₂) , (v₁₀ , v₁₁ , v₁₂) , (v₂₀ , v₂₁ , v₂₂)) (T₀ , T₁) = refl
completeness2-gf3 ((v₀₀ , T₂ , v₀₂) , (v₁₀ , v₁₁ , v₁₂) , (v₂₀ , v₂₁ , v₂₂)) (T₀ , T₁) = refl
-- (T₀,T₂)
completeness2-gf3 ((v₀₀ , v₀₁ , T₀) , (v₁₀ , v₁₁ , v₁₂) , (v₂₀ , v₂₁ , v₂₂)) (T₀ , T₂) = refl
completeness2-gf3 ((v₀₀ , v₀₁ , T₁) , (v₁₀ , v₁₁ , v₁₂) , (v₂₀ , v₂₁ , v₂₂)) (T₀ , T₂) = refl
completeness2-gf3 ((v₀₀ , v₀₁ , T₂) , (v₁₀ , v₁₁ , v₁₂) , (v₂₀ , v₂₁ , v₂₂)) (T₀ , T₂) = refl
-- (T₁,T₀)
completeness2-gf3 ((v₀₀ , v₀₁ , v₀₂) , (T₀ , v₁₁ , v₁₂) , (v₂₀ , v₂₁ , v₂₂)) (T₁ , T₀) = refl
completeness2-gf3 ((v₀₀ , v₀₁ , v₀₂) , (T₁ , v₁₁ , v₁₂) , (v₂₀ , v₂₁ , v₂₂)) (T₁ , T₀) = refl
completeness2-gf3 ((v₀₀ , v₀₁ , v₀₂) , (T₂ , v₁₁ , v₁₂) , (v₂₀ , v₂₁ , v₂₂)) (T₁ , T₀) = refl
-- (T₁,T₁)
completeness2-gf3 ((v₀₀ , v₀₁ , v₀₂) , (v₁₀ , T₀ , v₁₂) , (v₂₀ , v₂₁ , v₂₂)) (T₁ , T₁) = refl
completeness2-gf3 ((v₀₀ , v₀₁ , v₀₂) , (v₁₀ , T₁ , v₁₂) , (v₂₀ , v₂₁ , v₂₂)) (T₁ , T₁) = refl
completeness2-gf3 ((v₀₀ , v₀₁ , v₀₂) , (v₁₀ , T₂ , v₁₂) , (v₂₀ , v₂₁ , v₂₂)) (T₁ , T₁) = refl
-- (T₁,T₂)
completeness2-gf3 ((v₀₀ , v₀₁ , v₀₂) , (v₁₀ , v₁₁ , T₀) , (v₂₀ , v₂₁ , v₂₂)) (T₁ , T₂) = refl
completeness2-gf3 ((v₀₀ , v₀₁ , v₀₂) , (v₁₀ , v₁₁ , T₁) , (v₂₀ , v₂₁ , v₂₂)) (T₁ , T₂) = refl
completeness2-gf3 ((v₀₀ , v₀₁ , v₀₂) , (v₁₀ , v₁₁ , T₂) , (v₂₀ , v₂₁ , v₂₂)) (T₁ , T₂) = refl
-- (T₂,T₀)
completeness2-gf3 ((v₀₀ , v₀₁ , v₀₂) , (v₁₀ , v₁₁ , v₁₂) , (T₀ , v₂₁ , v₂₂)) (T₂ , T₀) = refl
completeness2-gf3 ((v₀₀ , v₀₁ , v₀₂) , (v₁₀ , v₁₁ , v₁₂) , (T₁ , v₂₁ , v₂₂)) (T₂ , T₀) = refl
completeness2-gf3 ((v₀₀ , v₀₁ , v₀₂) , (v₁₀ , v₁₁ , v₁₂) , (T₂ , v₂₁ , v₂₂)) (T₂ , T₀) = refl
-- (T₂,T₁)
completeness2-gf3 ((v₀₀ , v₀₁ , v₀₂) , (v₁₀ , v₁₁ , v₁₂) , (v₂₀ , T₀ , v₂₂)) (T₂ , T₁) = refl
completeness2-gf3 ((v₀₀ , v₀₁ , v₀₂) , (v₁₀ , v₁₁ , v₁₂) , (v₂₀ , T₁ , v₂₂)) (T₂ , T₁) = refl
completeness2-gf3 ((v₀₀ , v₀₁ , v₀₂) , (v₁₀ , v₁₁ , v₁₂) , (v₂₀ , T₂ , v₂₂)) (T₂ , T₁) = refl
-- (T₂,T₂)
completeness2-gf3 ((v₀₀ , v₀₁ , v₀₂) , (v₁₀ , v₁₁ , v₁₂) , (v₂₀ , v₂₁ , T₀)) (T₂ , T₂) = refl
completeness2-gf3 ((v₀₀ , v₀₁ , v₀₂) , (v₁₀ , v₁₁ , v₁₂) , (v₂₀ , v₂₁ , T₁)) (T₂ , T₂) = refl
completeness2-gf3 ((v₀₀ , v₀₁ , v₀₂) , (v₁₀ , v₁₁ , v₁₂) , (v₂₀ , v₂₁ , T₂)) (T₂ , T₂) = refl
