{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Algebra.RingTheory.TritStdlibRing
-- M24-a: GF(3)（Trit）作为标准库的交换环, 以及 Trit 上的环求解器
--
-- 数学背景
--   Trit = {T₀, T₁, T₂} 在 ⊕ / ⊗ / negate 下是 GF(3)。Base/Trit 已把全部环律逐 case 证毕
--   （0 postulate）, 只是散放着的引理。这里把它们装进标准库的 CommutativeRing 包,
--   再按 Data/Integer/Solver 的办法接上标准库的 ring solver。
--
-- 为什么有这一件
--   · TensorRankHK2GF3（Hopcroft–Kerr 的 2×2 排除论证）的残差恒等式要反复做
--     「加法单位 / 乘法单位 / 取反 / 分配」的重排。Trit 的 ⊕ 与 ⊗ 只在两个变元都是字面量时才归约;
--     中性项（如 u z）一出现, x ⊗ T₀、T₁ ⊗ x、x ⊕ T₀ 都得手写, 而且每一步都得对上实际的归约形状。
--   · 库内已有先例把纯算术重排交给标准库的 ring solver（ListBounds / GF3HammingCount / Ring3pow11,
--     用的是 ℕ 的实例）。这里给 Trit 建同一个东西。
--   · 先查后写: UniversalAlgebra 里已有本库自己的 trit-ring : Ring Trit, 但那是本库的 Ring 记录
--     （无乘法交换律, 见 Matrix2Inverse 头注）, 不是标准库的包, 求解器用不上; 所以另建这一件。
--
-- 内容
--   §1 可判定相等 _≟ₜ_
--   §2 ★ trit-comring : CommutativeRing 0ℓ 0ℓ —— 每个字段都取自 Base/Trit 已证的律
--   §3 ★ 求解器 TritSolver（Algebra.Solver.Ring.Simple 的实例）+ 一条冒烟测试
--
-- 诚实边界
--   · 依赖标准库的 Algebra.{Bundles, Structures, Solver}。求解器用反射生成证明项, 仍由内核检查,
--     不引入公理; 但这确实是对标准库的依赖, 与库内 ℕ 求解器的用法同一种性质。
--   · 求解器只认 ⊕ / ⊗ / negate 与字面量: 它证的是「整系数环恒等式」, 不知道 3 = 0。
--     δc、sumFin、Fin 的结构都不在它的语言里, 那些仍要手写。
--   · 它不改进任何数学结论; 只是把已经成立的等式写短。
--
-- 0 postulate / 0 REWRITE 规则 / 0 洞
module Sovereign.Algebra.RingTheory.TritStdlibRing where

open import Algebra.Bundles using (CommutativeRing)
open import Algebra.Structures using
  (IsCommutativeRing; IsRing; IsAbelianGroup; IsGroup; IsMonoid; IsSemigroup; IsMagma)
open import Data.Product using (_×_; _,_)
open import Level using (0ℓ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂)
open import Relation.Binary.PropositionalEquality.Properties using (isEquivalence)
open import Relation.Binary.Structures using (IsEquivalence)
open import Relation.Nullary using (Dec; yes; no)
import Algebra.Solver.Ring.Simple as Solver

open import Sovereign.Base.Trit using
  (Trit; T₀; T₁; T₂; _⊕_; _⊗_; negate
  ; ⊕-identityˡ; ⊕-identityʳ; ⊕-comm; ⊕-assoc; ⊕-inverse
  ; ⊗-identityˡ; ⊗-identityʳ; ⊗-comm; ⊗-assoc; ⊗-distribˡ-⊕; ⊗-distribʳ-⊕)

--------------------------------------------------------------------------------
-- §1 可判定相等
--------------------------------------------------------------------------------

infix 4 _≟ₜ_

_≟ₜ_ : (a b : Trit) → Dec (a ≡ b)
T₀ ≟ₜ T₀ = yes refl
T₀ ≟ₜ T₁ = no (λ ())
T₀ ≟ₜ T₂ = no (λ ())
T₁ ≟ₜ T₀ = no (λ ())
T₁ ≟ₜ T₁ = yes refl
T₁ ≟ₜ T₂ = no (λ ())
T₂ ≟ₜ T₀ = no (λ ())
T₂ ≟ₜ T₁ = no (λ ())
T₂ ≟ₜ T₂ = yes refl

--------------------------------------------------------------------------------
-- §2 Trit 作为标准库的交换环
--------------------------------------------------------------------------------

-- 左逆: −x ⊕ x ≡ 0（Trit 模块证的是右逆 x ⊕ −x ≡ 0）
⊕-inverseˡ : ∀ x → (negate x) ⊕ x ≡ T₀
⊕-inverseˡ x = trans (⊕-comm (negate x) x) (⊕-inverse x)

-- ★ GF(3) 的交换环结构: 逐字段取 Base/Trit 的律
trit-comring : CommutativeRing 0ℓ 0ℓ
trit-comring = record
  { Carrier = Trit
  ; _≈_ = _≡_
  ; _+_ = _⊕_
  ; _*_ = _⊗_
  ; -_ = negate
  ; 0# = T₀
  ; 1# = T₁
  ; isCommutativeRing = record
      { isRing = record
          { +-isAbelianGroup = record
              { isGroup = record
                  { isMonoid = record
                      { isSemigroup = record
                          { isMagma = record
                              { isEquivalence = isEquivalence
                              ; ∙-cong = cong₂ _⊕_ }
                          ; assoc = ⊕-assoc }
                      ; identity = ⊕-identityˡ , ⊕-identityʳ }
                  ; inverse = ⊕-inverseˡ , ⊕-inverse
                  ; ⁻¹-cong = cong negate }
              ; comm = ⊕-comm }
          ; *-cong = cong₂ _⊗_
          ; *-assoc = ⊗-assoc
          ; *-identity = ⊗-identityˡ , ⊗-identityʳ
          ; distrib = ⊗-distribˡ-⊕ , (λ x y z → ⊗-distribʳ-⊕ y z x) }
      ; *-comm = ⊗-comm } }

--------------------------------------------------------------------------------
-- §3 Trit 上的环求解器
--------------------------------------------------------------------------------

import Algebra.Solver.Ring.AlmostCommutativeRing as ACR

-- ★ 求解器: TritSolver.solve n (λ x₁ … xₙ → 左 ::= 右) refl
--   表达式语法: _:+_ _:*_ :-_ con（字面量）; 变量由宏填入
--   用法: open import … using (module TritSolver), 再 open TritSolver using (_:+_; _:*_; :-_) renaming (con to conₜ)
module TritSolver = Solver (ACR.fromCommutativeRing trit-comring) _≟ₜ_

open TritSolver using (_:=_; _:+_; _:*_; :-_) renaming (con to conₜ)

-- 冒烟测试: (a ⊕ b) ⊗ (c ⊕ 1) ⊕ −(a ⊗ c) ≡ a ⊕ b ⊕ (b ⊗ c)
smoke : ∀ a b c →
  (((a ⊕ b) ⊗ (c ⊕ T₁)) ⊕ negate (a ⊗ c)) ≡ ((a ⊕ b) ⊕ (b ⊗ c))
smoke a b c =
  TritSolver.solve 3
    (λ x y z → ((x :+ y) :* (z :+ conₜ T₁)) :+ :- (x :* z) := (x :+ y) :+ (y :* z))
    refl a b c
