{-# OPTIONS --rewriting --guardedness #-}

-- | Entanglement — GF(3) 离散量子纠缠
--
-- 连续统病态: ℂ²⊗ℂ² 上的纠缠态涉及连续参数 (Bloch 球)
-- 离散自愈: GF(3)²⊗GF(3)² 只有 81 个态, 纠缠可穷举
--
-- 核心结构:
--   §1. 离散量子态: GF(3)² (qutrit)
--   §2. 张量积: GF(3)² ⊗ GF(3)² = GF(3)⁴
--   §3. 纠缠态: 不可分解为 |a⟩⊗|b⟩ 的态
--   §4. Bell 态: GF(3) 上的最大纠缠态
--
-- 复用: Sovereign.Base.Trit (GF(3) 运算)
-- 0 postulate.

module Sovereign.Quantum.Entanglement where

open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
open import Data.Product using (_×_; _,_; proj₁; proj₂; Σ)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong; sym)

open import Sovereign.Base.Trit using (Trit; T₀; T₁; T₂; _⊕_; _⊗_; negate)

--------------------------------------------------------------------------------
-- §1. 离散量子态 (qutrit)
--
-- 连续: |ψ⟩ = α|0⟩ + β|1⟩, α,β ∈ ℂ, |α|²+|β|²=1
-- 离散: |ψ⟩ = a|0⟩ + b|1⟩ + c|2⟩, a,b,c ∈ GF(3)
--
-- GF(3) 上的 qutrit: 3 个基态 |0⟩, |1⟩, |2⟩
--------------------------------------------------------------------------------

-- 计算基态
data Basis3 : Set where
  ∣0⟩ : Basis3
  ∣1⟩ : Basis3
  ∣2⟩ : Basis3

-- 基态互异
0≢1 : ∣0⟩ ≢ ∣1⟩
0≢1 ()

0≢2 : ∣0⟩ ≢ ∣2⟩
0≢2 ()

1≢2 : ∣1⟩ ≢ ∣2⟩
1≢2 ()

-- 单 qutrit 态: GF(3)³ 中的向量 (振幅)
Qutrit : Set
Qutrit = Trit × Trit × Trit

-- 基态嵌入
ket0 : Qutrit
ket0 = T₁ , T₀ , T₀

ket1 : Qutrit
ket1 = T₀ , T₁ , T₀

ket2 : Qutrit
ket2 = T₀ , T₀ , T₁

--------------------------------------------------------------------------------
-- §2. 双 qutrit 张量积
--
-- 连续: ℂ³ ⊗ ℂ³ = ℂ⁹ (9 维)
-- 离散: GF(3)³ ⊗ GF(3)³ = GF(3)⁹ (9 个分量)
--
-- 可分离态: |a⟩⊗|b⟩ = (a₁b₁, a₁b₂, ..., a₃b₃)
--------------------------------------------------------------------------------

-- 双 qutrit 态: 9 个 GF(3) 分量
TwoQutrit : Set
TwoQutrit = Trit × Trit × Trit × Trit × Trit × Trit × Trit × Trit × Trit

-- 张量积: |a⟩⊗|b⟩
tensor : Qutrit → Qutrit → TwoQutrit
tensor (a₁ , a₂ , a₃) (b₁ , b₂ , b₃) =
  (a₁ ⊗ b₁) , (a₁ ⊗ b₂) , (a₁ ⊗ b₃) ,
  (a₂ ⊗ b₁) , (a₂ ⊗ b₂) , (a₂ ⊗ b₃) ,
  (a₃ ⊗ b₁) , (a₃ ⊗ b₂) , (a₃ ⊗ b₃)

-- |0⟩⊗|0⟩ = (1,0,0,0,0,0,0,0,0)
ket00 : TwoQutrit
ket00 = tensor ket0 ket0

ket00-ok : ket00 ≡ (T₁ , T₀ , T₀ , T₀ , T₀ , T₀ , T₀ , T₀ , T₀)
ket00-ok = refl

--------------------------------------------------------------------------------
-- §3. 可分离性判定
--
-- 态 |Ψ⟩ 可分离 ⟺ ∃ |a⟩,|b⟩ 使得 |Ψ⟩ = |a⟩⊗|b⟩
-- 不可分离 ⟹ 纠缠
--
-- GF(3) 上: 可分离性可通过秩判定 (矩阵秩 ≤ 1)
--------------------------------------------------------------------------------

-- 可分离态的类型
Separable : TwoQutrit → Set
Separable Ψ = Σ Qutrit (λ a → Σ Qutrit (λ b → Ψ ≡ tensor a b))

-- |0⟩⊗|0⟩ 是可分离的
ket00-separable : Separable ket00
ket00-separable = ket0 , ket0 , refl

--------------------------------------------------------------------------------
-- §4. Bell 态 (GF(3) 版本)
--
-- 连续: |Φ⁺⟩ = (|00⟩+|11⟩)/√2
-- 离散 GF(3): |Φ⟩ = |00⟩+|11⟩+|22⟩ (无归一化, GF(3) 无 √2)
--
-- 这是 GF(3) 上的最大纠缠态
--------------------------------------------------------------------------------

-- GF(3) Bell 态: |00⟩+|11⟩+|22⟩
bell-gf3 : TwoQutrit
bell-gf3 = (T₁ , T₀ , T₀ , T₀ , T₁ , T₀ , T₀ , T₀ , T₁)

-- Bell 态不是 |0⟩⊗|0⟩ (第5个分量: T₁ vs T₀)
bell-not-00 : bell-gf3 ≢ ket00
bell-not-00 eq = T₁≢T₀ (cong proj5 eq)
  where
    proj5 : TwoQutrit → Trit
    proj5 (_ , _ , _ , _ , x , _ , _ , _ , _) = x
    T₁≢T₀ : T₁ ≡ T₀ → ⊥
    T₁≢T₀ ()
