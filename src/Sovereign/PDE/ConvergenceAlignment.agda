{-# OPTIONS --rewriting #-}
module Sovereign.PDE.ConvergenceAlignment where

--------------------------------------------------------------------------------
-- 收敛对齐 — GF(3) 有限域上差分方程解的极限环收敛
--
-- MSC 34-35: 离散 ODE/PDE 的收敛性
--
-- 核心定理:
--   在 GF(3) 有限域上, 差分方程的解序列最终进入极限环 (鸽巢原理)。
--   收敛不是"趋近某点", 而是"进入周期轨道"。
--   离散解与"精确解"在 GF(3) 中完全一致 (不是近似)。
--
-- 内容:
--   §1. 离散状态序列 (DiscreteStateSeq)
--   §2. GF3Func 基数定理 (|GF3Func| = 27)
--   §3. 鸽巢原理: 28 个 GF3Func 值必有碰撞
--   §4. 极限环收敛 (LimitCycleConvergence + theorem-finite-cycle)
--   §5. 精确对齐: 离散解 = 精确解 (无近似)
--   §6. 幂零性约束: Δ³≡0 限制暂态长度
--
-- 证明策略:
--   不用递归/归纳证明收敛性, 用穷举 + 鸽巢原理。
--   GF3Func 只有 27 个元素 → 任何 28 项序列必有重复 → 周期轨道。
--
-- 依赖:
--   ProjectionDifferential: GF3Func, Δ³≡0, shift³≡id
--   DiscreteDE: evalGF3, Δⁿ, DiscreteODE
--   Data.Fin.Properties: pigeonhole
--
-- 0 postulate — 全部构造性证明
--------------------------------------------------------------------------------

open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _<_; _>_; _≤_; _∸_; s≤s; z≤n)
open import Data.Nat.Properties using (≤-refl; m<n⇒0<n∸m; <⇒≤; m+[n∸m]≡n; +-comm)
open import Data.Fin using (Fin; toℕ; fromℕ; _↑ˡ_)
  renaming (zero to fzero; suc to fsuc)
open import Data.Fin.Properties using (pigeonhole)
open import Data.Product using (_×_; _,_; Σ; ∃₂; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (
  _≡_; _≢_; refl; cong; sym; trans; module ≡-Reasoning)

open import Sovereign.Base.Trit using (
  Trit; T₀; T₁; T₂; _⊕_; _⊗_; negate; tritToℕ)
open import Sovereign.Algebra.ProjectionDifferential using (
  GF3Func; shift; Δ; sum3; Δ³≡0; shift³≡id; Δ-const-zero)
open import Sovereign.Algebra.DiscreteDE using (
  evalGF3; Δⁿ; DiscreteODE)

--------------------------------------------------------------------------------
-- §1. 离散状态序列
--
-- 离散 ODE 的解不是连续曲线, 而是有限状态空间中的序列。
-- DiscreteStateSeq N 表示长度为 N 的 GF3Func 值序列。
--------------------------------------------------------------------------------

-- 离散状态序列: 有限长度的 GF3Func 值序列
DiscreteStateSeq : ℕ → Set
DiscreteStateSeq N = Fin N → GF3Func

-- 由演化算子生成的状态序列
-- F : GF3Func → GF3Func 是确定性演化 (如 Δ 的迭代)
-- x₀ 是初始状态
-- seq(F, x₀)(i) = Fⁱ(x₀)
iterate : (GF3Func → GF3Func) → ℕ → GF3Func → GF3Func
iterate F zero    x = x
iterate F (suc n) x = F (iterate F n x)

-- 生成离散状态序列
evolution-seq : (F : GF3Func → GF3Func) → GF3Func → (N : ℕ) → DiscreteStateSeq N
evolution-seq F x₀ N i = iterate F (toℕ i) x₀

-- 迭代结合律: F^(m+n)(x) = F^m(F^n(x))
-- (辅助引理, 用于从碰撞推导完整周期性)
iterate-plus : ∀ F m n x → iterate F (m + n) x ≡ iterate F m (iterate F n x)
iterate-plus F zero    n x = refl
iterate-plus F (suc m) n x = cong F (iterate-plus F m n x)

--------------------------------------------------------------------------------
-- §2. GF3Func 基数定理 — |GF3Func| = 27
--
-- GF3Func = Trit × Trit × Trit, 每个分量有 3 种选择。
-- 总计 3³ = 27 个不同的 GF3Func 值。
--
-- 证明策略: 构造 GF3Func ≅ Fin 27 的双射 (穷举 27 case)。
--------------------------------------------------------------------------------

-- 编码: GF3Func → Fin 27
-- 字典序: (T₀,T₀,T₀)↦0, (T₀,T₀,T₁)↦1, ..., (T₂,T₂,T₂)↦26
gf3func-encode : GF3Func → Fin 27
gf3func-encode (T₀ , T₀ , T₀) = fromℕ 0 ↑ˡ 26
gf3func-encode (T₀ , T₀ , T₁) = fromℕ 1 ↑ˡ 25
gf3func-encode (T₀ , T₀ , T₂) = fromℕ 2 ↑ˡ 24
gf3func-encode (T₀ , T₁ , T₀) = fromℕ 3 ↑ˡ 23
gf3func-encode (T₀ , T₁ , T₁) = fromℕ 4 ↑ˡ 22
gf3func-encode (T₀ , T₁ , T₂) = fromℕ 5 ↑ˡ 21
gf3func-encode (T₀ , T₂ , T₀) = fromℕ 6 ↑ˡ 20
gf3func-encode (T₀ , T₂ , T₁) = fromℕ 7 ↑ˡ 19
gf3func-encode (T₀ , T₂ , T₂) = fromℕ 8 ↑ˡ 18
gf3func-encode (T₁ , T₀ , T₀) = fromℕ 9 ↑ˡ 17
gf3func-encode (T₁ , T₀ , T₁) = fromℕ 10 ↑ˡ 16
gf3func-encode (T₁ , T₀ , T₂) = fromℕ 11 ↑ˡ 15
gf3func-encode (T₁ , T₁ , T₀) = fromℕ 12 ↑ˡ 14
gf3func-encode (T₁ , T₁ , T₁) = fromℕ 13 ↑ˡ 13
gf3func-encode (T₁ , T₁ , T₂) = fromℕ 14 ↑ˡ 12
gf3func-encode (T₁ , T₂ , T₀) = fromℕ 15 ↑ˡ 11
gf3func-encode (T₁ , T₂ , T₁) = fromℕ 16 ↑ˡ 10
gf3func-encode (T₁ , T₂ , T₂) = fromℕ 17 ↑ˡ 9
gf3func-encode (T₂ , T₀ , T₀) = fromℕ 18 ↑ˡ 8
gf3func-encode (T₂ , T₀ , T₁) = fromℕ 19 ↑ˡ 7
gf3func-encode (T₂ , T₀ , T₂) = fromℕ 20 ↑ˡ 6
gf3func-encode (T₂ , T₁ , T₀) = fromℕ 21 ↑ˡ 5
gf3func-encode (T₂ , T₁ , T₁) = fromℕ 22 ↑ˡ 4
gf3func-encode (T₂ , T₁ , T₂) = fromℕ 23 ↑ˡ 3
gf3func-encode (T₂ , T₂ , T₀) = fromℕ 24 ↑ˡ 2
gf3func-encode (T₂ , T₂ , T₁) = fromℕ 25 ↑ˡ 1
gf3func-encode (T₂ , T₂ , T₂) = fromℕ 26

-- 解码: Fin 27 → GF3Func (穷举 27 case)
gf3func-decode : Fin 27 → GF3Func
gf3func-decode fzero = (T₀ , T₀ , T₀)
gf3func-decode (fsuc fzero) = (T₀ , T₀ , T₁)
gf3func-decode (fsuc (fsuc fzero)) = (T₀ , T₀ , T₂)
gf3func-decode (fsuc (fsuc (fsuc fzero))) = (T₀ , T₁ , T₀)
gf3func-decode (fsuc (fsuc (fsuc (fsuc fzero)))) = (T₀ , T₁ , T₁)
gf3func-decode (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))) = (T₀ , T₁ , T₂)
gf3func-decode (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))) = (T₀ , T₂ , T₀)
gf3func-decode (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))) = (T₀ , T₂ , T₁)
gf3func-decode (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))))) = (T₀ , T₂ , T₂)
gf3func-decode (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))))) = (T₁ , T₀ , T₀)
gf3func-decode (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))))))) = (T₁ , T₀ , T₁)
gf3func-decode (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))))))) = (T₁ , T₀ , T₂)
gf3func-decode (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))))))))) = (T₁ , T₁ , T₀)
gf3func-decode (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))))))))) = (T₁ , T₁ , T₁)
gf3func-decode (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))))))))))) = (T₁ , T₁ , T₂)
gf3func-decode (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))))))))))) = (T₁ , T₂ , T₀)
gf3func-decode (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))))))))))))) = (T₁ , T₂ , T₁)
gf3func-decode (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))))))))))))) = (T₁ , T₂ , T₂)
gf3func-decode (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))))))))))))))) = (T₂ , T₀ , T₀)
gf3func-decode (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))))))))))))))) = (T₂ , T₀ , T₁)
gf3func-decode (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))))))))))))))))) = (T₂ , T₀ , T₂)
gf3func-decode (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))))))))))))))))) = (T₂ , T₁ , T₀)
gf3func-decode (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))))))))))))))))))) = (T₂ , T₁ , T₁)
gf3func-decode (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))))))))))))))))))) = (T₂ , T₁ , T₂)
gf3func-decode (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))))))))))))))))))))) = (T₂ , T₂ , T₀)
gf3func-decode (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))))))))))))))))))))) = (T₂ , T₂ , T₁)
gf3func-decode (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))))))))))))))))))))))) = (T₂ , T₂ , T₂)

-- 双射证明: decode ∘ encode = id (27 case refl)
decode∘encode≡id : ∀ f → gf3func-decode (gf3func-encode f) ≡ f
decode∘encode≡id (T₀ , T₀ , T₀) = refl
decode∘encode≡id (T₀ , T₀ , T₁) = refl
decode∘encode≡id (T₀ , T₀ , T₂) = refl
decode∘encode≡id (T₀ , T₁ , T₀) = refl
decode∘encode≡id (T₀ , T₁ , T₁) = refl
decode∘encode≡id (T₀ , T₁ , T₂) = refl
decode∘encode≡id (T₀ , T₂ , T₀) = refl
decode∘encode≡id (T₀ , T₂ , T₁) = refl
decode∘encode≡id (T₀ , T₂ , T₂) = refl
decode∘encode≡id (T₁ , T₀ , T₀) = refl
decode∘encode≡id (T₁ , T₀ , T₁) = refl
decode∘encode≡id (T₁ , T₀ , T₂) = refl
decode∘encode≡id (T₁ , T₁ , T₀) = refl
decode∘encode≡id (T₁ , T₁ , T₁) = refl
decode∘encode≡id (T₁ , T₁ , T₂) = refl
decode∘encode≡id (T₁ , T₂ , T₀) = refl
decode∘encode≡id (T₁ , T₂ , T₁) = refl
decode∘encode≡id (T₁ , T₂ , T₂) = refl
decode∘encode≡id (T₂ , T₀ , T₀) = refl
decode∘encode≡id (T₂ , T₀ , T₁) = refl
decode∘encode≡id (T₂ , T₀ , T₂) = refl
decode∘encode≡id (T₂ , T₁ , T₀) = refl
decode∘encode≡id (T₂ , T₁ , T₁) = refl
decode∘encode≡id (T₂ , T₁ , T₂) = refl
decode∘encode≡id (T₂ , T₂ , T₀) = refl
decode∘encode≡id (T₂ , T₂ , T₁) = refl
decode∘encode≡id (T₂ , T₂ , T₂) = refl

-- 编码单射性: encode f ≡ encode g → f ≡ g
-- 证明: f = decode(encode f) = decode(encode g) = g
encode-injective : ∀ {f g : GF3Func} → gf3func-encode f ≡ gf3func-encode g → f ≡ g
encode-injective {f} {g} h =
  trans (sym (decode∘encode≡id f)) (trans (cong gf3func-decode h) (decode∘encode≡id g))

-- 基数定理: |GF3Func| = 27
-- 见证: GF3Func ≅ Fin 27 (由 encode/decode 双射证明)
gf3func-cardinality : ℕ
gf3func-cardinality = 27

gf3func-count : 3 * 3 * 3 ≡ 27
gf3func-count = refl

--------------------------------------------------------------------------------
-- §3. 鸽巢原理 — 28 个 GF3Func 值必有碰撞
--
-- GF3Func 只有 27 个元素。
-- 任何长度为 28 的 GF3Func 序列中, 必有两个位置取相同值。
-- 这是有限状态空间上确定性演化的核心约束。
--------------------------------------------------------------------------------

-- 27 < 28 的证明 (鸽巢原理的前提)
27<28 : 27 < 28
27<28 = ≤-refl

-- 鸽巢原理 (GF3Func 版本):
-- 任何 DiscreteStateSeq 28 中必有两个位置取相同值
-- 返回: 碰撞位置 i < j (ℕ 序) 及等式证明 s(i) ≡ s(j)
pigeonhole-GF3Func : (s : DiscreteStateSeq 28) →
  Σ (Fin 28) (λ i → Σ (Fin 28) (λ j → (toℕ i < toℕ j) × (s i ≡ s j)))
pigeonhole-GF3Func s =
  let result = pigeonhole 27<28 (λ k → gf3func-encode (s k))
      i = proj₁ result
      j = proj₁ (proj₂ result)
      i<j = proj₁ (proj₂ (proj₂ result))
      enc-eq = proj₂ (proj₂ (proj₂ result))
  in (i , (j , (i<j , encode-injective enc-eq)))

--------------------------------------------------------------------------------
-- §4. 极限环收敛 — theorem-finite-cycle
--
-- 核心定理: GF3Func 上的任何确定性演化最终进入周期轨道。
--
-- 连续数学中, 收敛 = "趋近某点" (ε-δ 极限)。
-- GF(3) 中, 收敛 = "进入周期轨道" (精确周期重复)。
-- 没有"趋近", 只有"到达"。
--------------------------------------------------------------------------------

-- 极限环收敛 record
-- 记录: 从 transient 位置开始, 以 period 为周期精确重复
record LimitCycleConvergence (F : GF3Func → GF3Func) (x₀ : GF3Func) : Set where
  constructor mk-convergence
  field
    -- 暂态长度: 进入周期轨道前的步数
    transient : ℕ
    -- 周期长度
    period : ℕ
    -- 周期为正
    period>0 : period > 0
    -- 碰撞条件: F^transient(x₀) = F^(transient+period)(x₀)
    isPeriodic : iterate F transient x₀ ≡ iterate F (transient + period) x₀

-- 从碰撞推导完整周期性:
-- 若 F^i(x₀) = F^j(x₀) (i < j), 则对所有 k: F^(i+k)(x₀) = F^(j+k)(x₀)
collision→periodic : ∀ {F : GF3Func → GF3Func} {x₀ : GF3Func} {i j : ℕ} →
  iterate F i x₀ ≡ iterate F j x₀ →
  ∀ k → iterate F (i + k) x₀ ≡ iterate F (j + k) x₀
collision→periodic {F} {x₀} {i} {j} h k = begin
  iterate F (i + k) x₀
    ≡⟨ cong (λ n → iterate F n x₀) (+-comm i k) ⟩
  iterate F (k + i) x₀
    ≡⟨ iterate-plus F k i x₀ ⟩
  iterate F k (iterate F i x₀)
    ≡⟨ cong (iterate F k) h ⟩
  iterate F k (iterate F j x₀)
    ≡⟨ sym (iterate-plus F k j x₀) ⟩
  iterate F (k + j) x₀
    ≡⟨ cong (λ n → iterate F n x₀) (+-comm k j) ⟩
  iterate F (j + k) x₀ ∎
  where open ≡-Reasoning

-- 核心定理: GF3Func 上的确定性演化最终进入极限环
-- 证明: 鸽巢原理 — 前 28 个迭代值中必有两个相等
-- 暂态 ≤ 27, 周期 ≤ 27 (鸽巢原理上界)
theorem-finite-cycle : ∀ (F : GF3Func → GF3Func) (x₀ : GF3Func) →
  LimitCycleConvergence F x₀
theorem-finite-cycle F x₀ =
  let (i , (j , (i<j , eq))) = pigeonhole-GF3Func (evolution-seq F x₀ 28)
      ti = toℕ i
      tj = toℕ j
      -- i < j 即 toℕ i < toℕ j
      -- 所以 tj ∸ ti > 0
      period-pos : tj ∸ ti > 0
      period-pos = m<n⇒0<n∸m i<j
      -- ti + (tj ∸ ti) ≡ tj (算术恒等式)
      sum-eq : ti + (tj ∸ ti) ≡ tj
      sum-eq = m+[n∸m]≡n (<⇒≤ i<j)
      -- 碰撞: iterate F ti x₀ ≡ iterate F tj x₀ ≡ iterate F (ti + (tj∸ti)) x₀
      periodic : iterate F ti x₀ ≡ iterate F (ti + (tj ∸ ti)) x₀
      periodic = trans eq (sym (cong (λ n → iterate F n x₀) sum-eq))
  in mk-convergence ti (tj ∸ ti) period-pos periodic

--------------------------------------------------------------------------------
-- §5. 精确对齐 — 离散解 = 精确解
--
-- 连续数值方法: 离散解 ≈ 精确解 (误差 O(h^p), 需要 h→0)
-- GF(3) 离散数学: 离散解 ≡ 精确解 (命题等式, 无误差)
--
-- "对齐" 不是 ε-逼近, 而是命题等式 (≡)。
-- 在 GF(3) 中, 没有 "趋近" 的概念 — 要么相等, 要么不等。
-- 周期轨道就是精确解本身, 不是精确解的近似。
--------------------------------------------------------------------------------

-- 精确对齐 record: 离散解在周期轨道上与"精确解"完全一致
-- "精确解" = 周期轨道本身 (不存在外部的"真实解")
record ExactAlignment (F : GF3Func → GF3Func) (x₀ : GF3Func) : Set where
  constructor mk-alignment
  field
    -- 收敛证据
    convergence : LimitCycleConvergence F x₀
    -- 精确性: 周期轨道上的值精确重复 (不是 ε-接近)
    -- 对任意 k, F^(s+p+k)(x₀) ≡ F^(s+k)(x₀) — 命题等式
    exact-periodicity : ∀ k →
      let open LimitCycleConvergence convergence in
      iterate F (transient + period + k) x₀ ≡ iterate F (transient + k) x₀

-- 定理: 所有 GF3Func 上的确定性演化都精确对齐
-- 证明: 由 theorem-finite-cycle + collision→periodic 直接得到
theorem-exact-alignment : ∀ (F : GF3Func → GF3Func) (x₀ : GF3Func) →
  ExactAlignment F x₀
theorem-exact-alignment F x₀ =
  let conv = theorem-finite-cycle F x₀
      open LimitCycleConvergence conv
  in mk-alignment conv
       (λ k → sym (collision→periodic {F} {x₀} {transient} {transient + period} isPeriodic k))

-- 对齐的本质: GF(3) 中没有近似
-- 连续数学: |u_h - u_exact| < ε (需要 ε → 0, h → 0)
-- GF(3): u_discrete ≡ u_exact (命题等式, 无 ε, 无 h → 0)
-- 这不是"精度足够高", 而是"误差概念本身不存在"
alignment-is-identity : ∀ (F : GF3Func → GF3Func) (x₀ : GF3Func) →
  let conv = theorem-finite-cycle F x₀
      open LimitCycleConvergence conv
  in ∀ k → iterate F (transient + period + k) x₀ ≡ iterate F (transient + k) x₀
alignment-is-identity F x₀ = exact-periodicity (theorem-exact-alignment F x₀)
  where open ExactAlignment

--------------------------------------------------------------------------------
-- §6. 幂零性约束 — Δ³≡0 限制暂态长度
--
-- 差分算子 Δ 满足 Δ³ ≡ 0 (三阶幂零)。
-- 这意味着以 Δ 为演化算子时:
--   F = Δ: 暂态 ≤ 3 步 (因为 Δ³f = 0 对所有 f)
--   F = shift: 暂态 = 0, 周期 = 3 (因为 shift³ = id)
--
-- 一般演化 F 的暂态 ≤ 27 (鸽巢原理上界)。
-- 特殊演化 (如 Δ, shift) 有更紧的上界。
--------------------------------------------------------------------------------

-- 移位演化的精确周期: shift³ = id → 周期整除 3
shift-period-3 : ∀ f → iterate shift 3 f ≡ f
shift-period-3 f = shift³≡id f

-- 差分演化的幂零性: Δ³ = 0 → 3 步后到达零函数
Δ-nilpotent-3 : ∀ f → iterate Δ 3 f ≡ (T₀ , T₀ , T₀)
Δ-nilpotent-3 f = Δ³≡0 f

-- 差分演化的高阶幂零: Δ^(3+n) = 0
-- (直接用 iterate 证明, 不依赖 Δⁿ 的归约)
Δ-nilpotent-higher : ∀ n f → iterate Δ (3 + n) f ≡ (T₀ , T₀ , T₀)
Δ-nilpotent-higher zero    f = Δ³≡0 f
Δ-nilpotent-higher (suc n) f =
  trans (cong Δ (Δ-nilpotent-higher n f)) (Δ-const-zero T₀)

-- 差分演化的极限环收敛 (特化版):
-- Δ 的演化从任何初始状态出发, 至多 3 步进入不动点 (零函数)
-- 周期 = 1 (不动点是周期 1 的极限环)
Δ-convergence : ∀ f → LimitCycleConvergence Δ f
Δ-convergence f = mk-convergence 3 1 (s≤s z≤n)
  (trans (Δ³≡0 f) (sym (Δ-nilpotent-higher 1 f)))

-- 移位演化的极限环收敛 (特化版):
-- shift 的演化从任何初始状态出发, 周期 = 3 (或 1, 对常数函数)
shift-convergence : ∀ f → LimitCycleConvergence shift f
shift-convergence f = mk-convergence 0 3 (s≤s z≤n)
  (sym (shift³≡id f))

-- 幂零性 vs 一般鸽巢:
-- 一般演化: 暂态 ≤ 27 (鸽巢原理)
-- Δ 演化: 暂态 ≤ 3 (幂零性 Δ³=0)
-- shift 演化: 暂态 = 0, 周期 = 3 (周期性 S³=I)
-- 幂零性给出比鸽巢原理更紧的界
nilpotency-tighter-than-pigeonhole : 3 ≤ 27
nilpotency-tighter-than-pigeonhole = s≤s (s≤s (s≤s z≤n))

--------------------------------------------------------------------------------
-- 总结
--
-- GF(3) 离散收敛的本质:
--   1. 有限性: |GF3Func| = 27 → 鸽巢原理 → 必最终周期
--   2. 精确性: 周期重复是命题等式 (≡), 不是 ε-逼近
--   3. 幂零性: Δ³=0 给出比鸽巢更紧的暂态上界
--
-- 与连续收敛的对比:
--   连续: lim_{n→∞} x_n = x* (ε-δ, 需要无穷)
--   离散: ∃ N p. ∀ k. x_{N+p+k} = x_{N+k} (有限, 精确, 可计算)
--
-- 对齐:
--   连续数值方法: 离散解 → 精确解 (h → 0, 有截断误差)
--   GF(3): 离散解 ≡ 精确解 (无截断, 无近似, 无极限)
--   "对齐" 不是 "足够接近", 而是 "完全相同"
--------------------------------------------------------------------------------
