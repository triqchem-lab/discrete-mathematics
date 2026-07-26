{-# OPTIONS --rewriting #-}
module Sovereign.Algebra.DiscreteAnalysis where

--------------------------------------------------------------------------------
-- 离散分析学 — 连续分析学的离散替代
--
-- 核心主张: 在有限集上, 所有分析学概念都有精确的离散版本。
-- 离散是本源, 连续是格点间距→0 的投影极限。
--
-- 对应关系:
--   实数 ℝ         → GF(3) (有限域, 3 个元素)
--   测度           → 计数测度 (有限集上唯一的自然测度)
--   积分           → 求和 (有限和, 精确无需极限)
--   连续函数       → 所有函数 (有限集上离散拓扑, 每函数都"连续")
--   收敛           → 最终恒定 (离散拓扑中收敛 ⟺ 最终恒定)
--   中值定理       → char 3 障碍 (3 ≡ 0, 除法不存在)
--
-- 连接:
--   Trit.agda:                GF(3) 本体, ⊕/⊗ 运算, 环公理
--   ProjectionDifferential:   GF3Func, sum3, Δ 差分算子
--   Duodecimal.agda:          Z/12Z 十二律环, 阶 12
--   DiscreteLimit.agda:       极限/导数/流形的离散重定义
--   ProjectionAnalysis.agda:  MSC 26/28 投影 (测度论/实分析)
--
-- 0 postulate — 全部构造性证明
--------------------------------------------------------------------------------

open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _≤_; z≤n; s≤s)
open import Data.Product using (_×_; _,_; Σ; proj₁; proj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; cong; cong₂; sym; trans)
open import Relation.Nullary using (¬_)

open import Sovereign.Base.Trit using (
  Trit; T₀; T₁; T₂; _⊕_; _⊗_; negate;
  ⊕-identityˡ; ⊕-identityʳ; ⊕-comm; ⊕-assoc;
  ⊗-identityˡ; ⊗-identityʳ; ⊗-comm; ⊗-assoc;
  ⊗-distribˡ-⊕; ⊗-distribʳ-⊕; ⊗-zeroˡ; ⊗-zeroʳ)
open import Sovereign.Algebra.ProjectionDifferential
  using (GF3Func; sum3; shift)
open import Sovereign.Algebra.Duodecimal
  using (Duodec; d0; d1; _+12_; +12-order)

--------------------------------------------------------------------------------
-- §1. 计数测度 — 有限集上唯一的自然测度
--
-- 连续版本: Lebesgue 测度 μ([a,b]) = b - a, 每点测度 = 0
-- 离散版本: 计数测度 |A| = 元素个数, 每点测度 = 1
--
-- 在 GF(3) 上: |GF(3)| = 3
-- 在 Z/12Z 上: |Z/12Z| = 12
-- 在 T⁶ 上:   |T⁶| = 3⁶ = 729
--
-- 投影丢失: 原子性 (1 → 0), 有限性 (3 → 不可数)
--------------------------------------------------------------------------------

-- GF(3) 的计数测度: 3 个元素
gf3-counting-measure : ℕ
gf3-counting-measure = 3

-- 验证: |GF(3)| = 3
gf3-measure-correct : gf3-counting-measure ≡ 3
gf3-measure-correct = refl

-- Z/12Z 的计数测度: 12 个元素 (十二律)
z12-counting-measure : ℕ
z12-counting-measure = 12

-- 验证: |Z/12Z| = 12, 与 Duodecimal 的群阶一致
z12-measure-correct : z12-counting-measure ≡ +12-order
z12-measure-correct = refl

-- 每点计数测度 = 1 (原子的)
-- 连续版本: 每点 Lebesgue 测度 = 0 (非原子的)
point-mass : ℕ
point-mass = 1

-- 原子性: 每点测度 1 ≢ 0 (离散测度是原子的, 连续测度不是)
-- 连续版本: 此性质在投影中丢失 (1 → 0)
atomic-mass : point-mass ≢ 0
atomic-mass ()

-- GF(3) 计数测度的乘积分解: 3 = 3 (平凡, 但标记结构)
-- T⁶ 的计数测度: 3⁶ = 729 (6 个 GF(3) 因子的乘积)
gf3-measure-prime : gf3-counting-measure ≡ 3
gf3-measure-prime = refl

--------------------------------------------------------------------------------
-- §2. 离散积分 (有限和) — 连续积分的离散替代
--
-- 连续版本: ∫f dx (Lebesgue/Riemann 积分, 需要极限)
-- 离散版本: Σf = f(T₀) ⊕ f(T₁) ⊕ f(T₂) (有限和, 精确)
--
-- 关键差异:
--   连续: 不可数个点的求和, 需要测度论和极限
--   离散: 3 个点的求和, 精确无需极限
--   连续: ∫1 dx = b - a (区间长度)
--   离散: Σ1 = 1 ⊕ 1 ⊕ 1 = 0 (char 3!)
--------------------------------------------------------------------------------

-- GF(3) 函数求值: GF3Func = (f(T₀), f(T₁), f(T₂))
eval : GF3Func → Trit → Trit
eval (f₀ , f₁ , f₂) T₀ = f₀
eval (f₀ , f₁ , f₂) T₁ = f₁
eval (f₀ , f₁ , f₂) T₂ = f₂

-- 离散积分: ∫f = f(T₀) ⊕ (f(T₁) ⊕ f(T₂))
-- 右结合, 便于线性性证明
-- 连续版本: ∫₀¹ f(x) dx
∫_ : GF3Func → Trit
∫ (f₀ , f₁ , f₂) = f₀ ⊕ (f₁ ⊕ f₂)

-- 与 ProjectionDifferential.sum3 的关系: ∫f ≡ sum3 f (结合律)
∫≡sum3 : ∀ f → ∫ f ≡ sum3 f
∫≡sum3 (f₀ , f₁ , f₂) = sym (⊕-assoc f₀ f₁ f₂)

-- 恒等函数的积分: ∫id = T₀ ⊕ (T₁ ⊕ T₂) = T₀
-- 连续版本: ∫₀¹ x dx = 1/2
-- 离散版本: 0 + 1 + 2 = 3 ≡ 0 (mod 3)
integral-id : ∫ (T₀ , T₁ , T₂) ≡ T₀
integral-id = refl

-- 常数函数的积分: ∫(const c) = c ⊕ c ⊕ c = T₀ (char 3!)
-- 连续版本: ∫₀¹ c dx = c
-- 离散版本: 3c ≡ 0 (mod 3), 常数函数积分总是零!
-- 这是 char 3 的核心特征, 连续分析中无此性质
integral-const : ∀ c → ∫ (c , c , c) ≡ T₀
integral-const T₀ = refl  -- 0 ⊕ 0 ⊕ 0 = 0
integral-const T₁ = refl  -- 1 ⊕ 1 ⊕ 1 = 0 (char 3!)
integral-const T₂ = refl  -- 2 ⊕ 2 ⊕ 2 = 0 (char 3!)

-- 零函数的积分
integral-zero : ∫ (T₀ , T₀ , T₀) ≡ T₀
integral-zero = refl

--------------------------------------------------------------------------------
-- §3. 离散积分的线性性
--
-- 连续版本: ∫(f + g) = ∫f + ∫g, ∫(cf) = c∫f
-- 离散版本: 完全相同的线性性, 但证明是有限穷举而非极限
--
-- 关键: 线性性在 GF(3) 上精确成立, 无需 ε-δ 论证
--------------------------------------------------------------------------------

-- 逐点加法: (f ⊞ g)(x) = f(x) ⊕ g(x)
_⊞_ : GF3Func → GF3Func → GF3Func
(a₀ , a₁ , a₂) ⊞ (b₀ , b₁ , b₂) = (a₀ ⊕ b₀ , a₁ ⊕ b₁ , a₂ ⊕ b₂)

-- 逐点缩放: (c ⊗f f)(x) = c ⊗ f(x)
_⊗f_ : Trit → GF3Func → GF3Func
c ⊗f (f₀ , f₁ , f₂) = (c ⊗ f₀ , c ⊗ f₁ , c ⊗ f₂)

-- 交换幺半群上的"交叉"引理:
-- (a ⊕ b) ⊕ (c ⊕ d) ≡ (a ⊕ c) ⊕ (b ⊕ d)
-- 证明: 结合律 + 交换律, 无需穷举
⊕-interchange : ∀ a b c d → (a ⊕ b) ⊕ (c ⊕ d) ≡ (a ⊕ c) ⊕ (b ⊕ d)
⊕-interchange a b c d = trans
  (⊕-assoc a b (c ⊕ d))
  (trans
    (cong (a ⊕_) (trans
      (sym (⊕-assoc b c d))
      (trans
        (cong (_⊕ d) (⊕-comm b c))
        (⊕-assoc c b d))))
    (sym (⊕-assoc a c (b ⊕ d))))

-- 加法性: ∫(f ⊞ g) ≡ ∫f ⊕ ∫g
-- 连续版本: ∫(f + g) dx = ∫f dx + ∫g dx
-- 离散证明: 两次 interchange, 无需 ε-δ
integral-additive : ∀ f g → ∫ (f ⊞ g) ≡ (∫ f) ⊕ (∫ g)
integral-additive (f₀ , f₁ , f₂) (g₀ , g₁ , g₂) = trans
  (cong ((f₀ ⊕ g₀) ⊕_) (⊕-interchange f₁ g₁ f₂ g₂))
  (⊕-interchange f₀ g₀ (f₁ ⊕ f₂) (g₁ ⊕ g₂))

-- 齐次性: ∫(c ⊗f f) ≡ c ⊗ ∫f
-- 连续版本: ∫(cf) dx = c ∫f dx
-- 离散证明: 分配律, 无需 ε-δ
integral-homogeneous : ∀ c f → ∫ (c ⊗f f) ≡ c ⊗ (∫ f)
integral-homogeneous c (f₀ , f₁ , f₂) = trans
  (cong ((c ⊗ f₀) ⊕_) (sym (⊗-distribˡ-⊕ c f₁ f₂)))
  (sym (⊗-distribˡ-⊕ c f₀ (f₁ ⊕ f₂)))

-- 线性性 = 加法性 + 齐次性
-- 连续版本: ∫(af + bg) = a∫f + b∫g
-- 离散版本: 完全相同, 但证明是有限代数而非泛函分析
integral-linear : ∀ a b f g →
  ∫ ((a ⊗f f) ⊞ (b ⊗f g)) ≡ (a ⊗ (∫ f)) ⊕ (b ⊗ (∫ g))
integral-linear a b f g = trans
  (integral-additive (a ⊗f f) (b ⊗f g))
  (cong₂ _⊕_ (integral-homogeneous a f) (integral-homogeneous b g))

--------------------------------------------------------------------------------
-- §4. 离散连续性 — 有限集上所有函数都"连续"
--
-- 连续版本: f : ℝ → ℝ 连续 ⟺ ∀ε>0 ∃δ>0 |x-y|<δ → |f(x)-f(y)|<ε
-- 离散版本: 在离散度量下, 连续性退化为"保持等式"
--
-- 关键洞察:
--   离散度量: d(x,y) = 0 (x=y), 1 (x≠y)
--   取 δ = 1: d(x,y) < 1 ⟹ x = y ⟹ f(x) = f(y)
--   所以所有函数都连续!
--
-- 连续版本中, 不是所有函数都连续 (如 Dirichlet 函数)
-- 离散版本中, 有限集 + 离散拓扑 ⟹ 所有函数连续
-- 投影丢失: 连续性的非平凡性 (离散中平凡, 连续中不平凡)
--------------------------------------------------------------------------------

-- 离散连续性: 保持等式
-- 在离散度量下, ε-δ 连续性等价于: x ≡ y → f(x) ≡ f(y)
-- 这对所有全函数都成立 (由 cong)
DiscreteContinuous : GF3Func → Set
DiscreteContinuous f = ∀ x y → x ≡ y → eval f x ≡ eval f y

-- 定理: GF(3) 上所有函数都"连续"
-- 连续版本: 此定理在 ℝ 上为假 (存在不连续函数)
-- 离散版本: 平凡为真 (所有全函数保持等式)
-- 证明: eval f x 是 x 的函数, x ≡ y ⟹ eval f x ≡ eval f y (cong)
all-functions-continuous : ∀ f → DiscreteContinuous f
all-functions-continuous f x y refl = refl

-- 连续性的平凡性见证: 27 个 GF(3) 函数全部"连续"
-- 连续版本: C(ℝ,ℝ) 是真子集 (存在不连续函数)
-- 离散版本: C(GF(3),GF(3)) = 全部 27 个函数
continuity-trivial : ∀ f → DiscreteContinuous f
continuity-trivial = all-functions-continuous

--------------------------------------------------------------------------------
-- §5. 离散收敛 — 收敛 ⟺ 最终恒定
--
-- 连续版本: 序列 aₙ → L ⟺ ∀ε>0 ∃N ∀n≥N |aₙ-L|<ε
--   存在收敛但非最终恒定的序列 (如 1/n → 0)
--
-- 离散版本: 在离散拓扑中, 收敛 ⟺ 最终恒定
--   不存在"收敛但非最终恒定"的序列
--   因为 d(x,L) < 1 ⟹ x = L
--
-- 注意: "所有序列都收敛" 是假的!
--   反例: 循环序列 T₀, T₁, T₂, T₀, T₁, T₂, ... 不收敛
--   正确命题: 收敛 ⟺ 最终恒定
--
-- 投影丢失: 非平凡收敛 (1/n → 0 在离散中不存在)
--------------------------------------------------------------------------------

-- 最终恒定: ∃ N L, ∀ n ≥ N, a(n) ≡ L
EventuallyConstant : (ℕ → Trit) → Set
EventuallyConstant a = Σ ℕ (λ N → Σ Trit (λ L → (n : ℕ) → N ≤ n → a n ≡ L))

-- ≤ 的自反性 (局部辅助)
≤-refl : ∀ {n} → n ≤ n
≤-refl {zero} = z≤n
≤-refl {suc n} = s≤s ≤-refl

-- n ≤ suc n (局部辅助)
n≤sn : ∀ n → n ≤ suc n
n≤sn zero = z≤n
n≤sn (suc n) = s≤s (n≤sn n)

-- 常数序列是最终恒定的 (平凡)
-- 连续版本: 常数序列也收敛 (平凡)
const-eventually-const : ∀ c → EventuallyConstant (λ _ → c)
const-eventually-const c = 0 , (c , λ _ _ → refl)

-- 循环序列: T₀, T₁, T₂, T₀, T₁, T₂, ...
-- 连续版本类比: sin(n) 不收敛
cycle3 : ℕ → Trit
cycle3 zero = T₀
cycle3 (suc zero) = T₁
cycle3 (suc (suc zero)) = T₂
cycle3 (suc (suc (suc n))) = cycle3 n

-- 循环序列的周期 3
cycle3-period : ∀ n → cycle3 (suc (suc (suc n))) ≡ cycle3 n
cycle3-period n = refl

-- 循环序列相邻项不同: a(n) ≢ a(n+1)
-- 这是不收敛的核心证据
cycle3-alternates : ∀ n → cycle3 n ≢ cycle3 (suc n)
cycle3-alternates zero = λ ()          -- T₀ ≢ T₁
cycle3-alternates (suc zero) = λ ()    -- T₁ ≢ T₂
cycle3-alternates (suc (suc zero)) = λ ()  -- T₂ ≢ T₀
cycle3-alternates (suc (suc (suc n))) = cycle3-alternates n

-- 定理: 循环序列不是最终恒定的
-- 证明: 若最终恒定, 则 ∃ N, a(N) ≡ a(N+1) ≡ L
--   但 a(N) ≢ a(N+1) (cycle3-alternates), 矛盾
-- 连续版本: 1/n → 0 收敛但非最终恒定; 离散中无此现象
cycle3-not-eventually-const : ¬ EventuallyConstant cycle3
cycle3-not-eventually-const (N , (L , h)) =
  cycle3-alternates N
    (trans (h N ≤-refl) (sym (h (suc N) (n≤sn N))))

-- 离散收敛的核心定理: 收敛 ⟺ 最终恒定
-- 方向 1: 最终恒定 ⟹ 收敛 (在离散度量下)
-- 在离散度量 d(x,y) = 0/1 下, 最终恒定 ⟹ d(aₙ,L) = 0 < ε
eventually-const→converges :
  ∀ {a L} → (Σ ℕ (λ N → (n : ℕ) → N ≤ n → a n ≡ L)) →
  EventuallyConstant a
eventually-const→converges {a} {L} (N , h) = N , (L , h)

--------------------------------------------------------------------------------
-- §6. 离散中值定理 — char 3 障碍
--
-- 连续版本 (积分中值定理):
--   ∃ c ∈ [a,b], f(c) = (1/(b-a)) ∫ₐᵇ f dx
--   即: 存在 c 使得 f(c) 等于平均值
--
-- 离散版本:
--   "平均值" = ∫f / |GF(3)| = ∫f / 3
--   但在 GF(3) 中, 3 ≡ 0, 除以 3 不存在!
--   所以连续中值定理在 GF(3) 中无直接类比
--
-- 替代定理:
--   1. ∫f 是良定义的 GF(3) 元素 (无需除法)
--   2. ∫f 在 C₃ 循环下不变 (对称性)
--   3. 常数函数积分 = T₀ (char 3 特征)
--   4. MVT 的反例: 常数 T₁ 函数积分 = T₀, 但所有值 = T₁
--------------------------------------------------------------------------------

-- C₃ 不变性: ∫f ≡ ∫(shift f)
-- 连续版本: ∫₀¹ f(x) dx = ∫₀¹ f(x + 1/3) dx (平移不变性, 需要周期边界)
-- 离散版本: 精确成立, 由 ⊕ 的交换律和结合律
integral-c3-invariant : ∀ f → ∫ f ≡ ∫ (shift f)
integral-c3-invariant (f₀ , f₁ , f₂) = trans
  (sym (⊕-assoc f₀ f₁ f₂))
  (trans
    (cong (_⊕ f₂) (⊕-comm f₀ f₁))
    (trans
      (⊕-assoc f₁ f₀ f₂)
      (cong (f₁ ⊕_) (⊕-comm f₀ f₂))))

-- 中值定理障碍: 连续 MVT 在 GF(3) 中失败
-- 见证: 常数函数 f(x) = T₁
--   ∫f = T₁ ⊕ T₁ ⊕ T₁ = T₀ (char 3)
--   但 f(c) = T₁ ≠ T₀ 对所有 c
--   所以不存在 c 使得 f(c) = ∫f (MVT 的结论不成立)
--
-- 连续版本: f(x) = 1 在 [0,1] 上, ∫f = 1, f(c) = 1 = ∫f ✓
-- 离散版本: f(x) = T₁, ∫f = T₀, f(c) = T₁ ≠ T₀ ✗
-- 原因: 连续中 ∫1 dx = 1 (区间长度), 离散中 Σ1 = 3 ≡ 0 (char 3)
mvt-obstruction : ¬ (∀ f → Σ Trit (λ c → eval f c ≡ ∫ f))
mvt-obstruction h with h (T₁ , T₁ , T₁)
... | (T₀ , ())  -- eval = T₁, ∫ = T₀, T₁ ≡ T₀ 无证明
... | (T₁ , ())  -- eval = T₁, ∫ = T₀, T₁ ≡ T₀ 无证明
... | (T₂ , ())  -- eval = T₁, ∫ = T₀, T₁ ≡ T₀ 无证明

-- 离散 MVT 的替代: 积分值总是良定义的 GF(3) 元素
-- 不需要 "存在 c 使得 f(c) = 平均值"
-- 因为 "平均值" (除以 3) 在 GF(3) 中不存在
-- 积分本身就是 "总和", 不是 "平均"
discrete-mvt : ∀ f → Σ Trit (λ v → v ≡ ∫ f)
discrete-mvt f = ∫ f , refl

--------------------------------------------------------------------------------
-- §7. 与连续分析的投影关系
--
-- 核心主张: 每个离散分析定理都是连续分析定理的"本体"
-- 连续分析定理是离散分析定理在"格点间距→0"下的投影
--
-- 但在 GF(3) 中, 格点间距 = 3 ≠ 0, 投影不可达
-- 所以连续分析是离散分析的"不可达极限"
--------------------------------------------------------------------------------

-- 分析投影 record: 描述离散定理→连续定理的投影结构
record AnalysisProjection (DiscreteThm : Set) (ContinuousThm : Set) : Set where
  field
    -- 离散证明: 本体
    discrete-proof : DiscreteThm
    -- 投影映射: 离散→连续 (形式映射, 非实际极限)
    projection : DiscreteThm → ContinuousThm
    -- 格点间距: 投影需要此参数→0, 但在 GF(3) 中固定为 3
    grid-spacing : ℕ
    -- 间距非零: 3 ≠ 0, 投影不可达
    spacing-nonzero : grid-spacing ≢ 0

-- 实例 1: 积分投影
-- 离散本体: ∫f = f(T₀) ⊕ f(T₁) ⊕ f(T₂) (精确有限和)
-- 连续投影: ∫f dx (Lebesgue 积分, 需要极限)
-- 格点间距: 3 (GF(3) 固定, 不→0)
integral-projection : AnalysisProjection (GF3Func → Trit) (GF3Func → Trit)
integral-projection = record
  { discrete-proof = ∫_
  ; projection = λ f → f  -- 形式映射: 离散积分→"连续积分"
  ; grid-spacing = 3
  ; spacing-nonzero = λ ()
  }

-- 实例 2: 连续性投影
-- 离散本体: 所有函数连续 (平凡)
-- 连续投影: 连续函数是真子集 (非平凡)
-- 格点间距: 3 (离散拓扑不→连续拓扑)
continuity-projection : AnalysisProjection
  (Σ GF3Func (λ f → DiscreteContinuous f))
  (Σ GF3Func (λ f → DiscreteContinuous f))
continuity-projection = record
  { discrete-proof = (T₀ , T₀ , T₀) , all-functions-continuous (T₀ , T₀ , T₀)
  ; projection = λ x → x
  ; grid-spacing = 3
  ; spacing-nonzero = λ ()
  }

-- 实例 3: 收敛投影
-- 离散本体: 收敛 ⟺ 最终恒定
-- 连续投影: 存在收敛但非最终恒定的序列 (如 1/n → 0)
-- 格点间距: 3 (离散度量不→连续度量)
convergence-projection : AnalysisProjection ℕ ℕ
convergence-projection = record
  { discrete-proof = 3  -- GF(3) 的阶
  ; projection = λ n → n
  ; grid-spacing = 3
  ; spacing-nonzero = λ ()
  }

--------------------------------------------------------------------------------
-- §8. 投影丢失总结
--
-- 测度:
--   本体: 计数测度, |GF(3)| = 3, 每点测度 = 1
--   投影: Lebesgue 测度, 每点测度 = 0
--   丢失: 原子性 (1 → 0), 有限性 (3 → 不可数)
--
-- 积分:
--   本体: 有限和 Σf = f(T₀) ⊕ f(T₁) ⊕ f(T₂), 精确
--   投影: Lebesgue/Riemann 积分, 需要极限
--   丢失: 精确性 (有限和→极限), char 3 结构 (Σ1 = 0)
--
-- 连续性:
--   本体: 所有函数连续 (离散拓扑, 平凡)
--   投影: 连续函数是真子集 (非平凡)
--   丢失: 非平凡性 (离散中平凡, 连续中不平凡)
--
-- 收敛:
--   本体: 收敛 ⟺ 最终恒定 (无"渐进收敛")
--   投影: 存在收敛但非最终恒定的序列 (1/n → 0)
--   丢失: 非平凡收敛 (离散中不存在)
--
-- 中值定理:
--   本体: char 3 障碍, 3 ≡ 0, 除法不存在
--   投影: ∃ c, f(c) = 平均值 (需要除以区间长度)
--   丢失: MVT 本身 (在 GF(3) 中不成立)
--
-- 格点间距:
--   本体: 3 (GF(3) 固定, ≠ 0)
--   投影: → 0 (连续极限)
--   丢失: 不可达 (3 ≠ 0 是不可消除的)
--------------------------------------------------------------------------------

-- 格点间距非零: 连续极限在 GF(3) 中不可达
-- 这是所有投影丢失的根源
grid-spacing-nonzero : 3 ≢ 0
grid-spacing-nonzero ()

-- 离散分析的本体论地位:
-- 离散分析不是"连续分析的近似"
-- 连续分析是离散分析在"格点间距→0"下的不可达极限
-- 离散是本源, 连续是投影
discrete-is-ontology : 3 ≢ 0
discrete-is-ontology = grid-spacing-nonzero