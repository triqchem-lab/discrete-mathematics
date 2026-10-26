{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Synthesis.Representation.SL2SetoidGroup
-- **SL(2,F₃) 的 setoid 群**：载体 = `Σ Mat2 (det ≡ 1)`，等价 = 首分量相等（忽略 det 证明）。
--
-- 为什么用 setoid 而不是严格 `GroupData`（B 路决策，2026-10-26）：
--   `SL2` 必然带证明字段 `det M ≡ 1`。Agda 里两条记录的相等要求**所有字段**相等——
--   包括证明字段；两个不同来源的 `det≡1` 证明并不定义性相等（无 proof irrelevance），
--   于是 `assoc : (g·h)·k ≡ g·(h·k)` 因证明分量不同而证不出。
--   把等价取成「首分量相等」即绕过该问题：所有群律只在矩阵分量上陈述。
--   载体/等价关系/运算/laws 打包成 `_PN15.SetoidGroupData`（复用库内已有 record，
--   不另造同构 record——两份同名 record 会造成两套不可互证的 API）。
--
-- 定理清单：det-one-* 用于封闭性；恒等式/结合律/逆律全部落在首分量。
--
-- 策略：代数链（每条 ≤3 步）+ 复用（mat-assoc/mat-idˡ/ʳ 来自 Matrix2Laws）
-- 0 postulate / 0 hole。

module Sovereign.Synthesis.Representation.SL2SetoidGroup where

open import Data.Fin using (Fin; zero; suc)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂)

-- 复用 pn-proofs 的 setoid 群 record（唯一一份，不重复定义）
open import _PN15 using (SetoidGroupData)

open import Sovereign.Synthesis.Representation.SL23Cayley using (Mat2; mulMat2; mul3)
open import Sovereign.Synthesis.Representation.Fin3Semiring using
  ( I2; mat-assoc; mat-idˡ; mat-idʳ )
open import Sovereign.Synthesis.Representation.Matrix2Inverse using
  ( det3; adj; det-adj; det-one-mul; det-one-adj )
open import Sovereign.Synthesis.Representation.Matrix2DetMul using (det-mul3)

--------------------------------------------------------------------------------
-- 1. 载体：行列式为 1 的 2×2 矩阵
--------------------------------------------------------------------------------

SL2 : Set
SL2 = Σ Mat2 (λ M → det3 M ≡ suc zero)

-- 等价：只看矩阵分量（det 证明被忽略）
-- ⚠ 用**投影**而非 Σ 模式匹配定义：模式匹配版 `_≈s_ a c` 在中性变量上不归约，
--   会让 `sl2-cong` 的假设 `h1` 类型卡住（UnsolvedMetaVariables 的根因）。
_≈s_ : SL2 → SL2 → Set
_≈s_ g h = proj₁ g ≡ proj₁ h

--------------------------------------------------------------------------------
-- 2. 运算与单位/逆
--------------------------------------------------------------------------------

sl2-mul : SL2 → SL2 → SL2
sl2-mul (M , p) (N , q) =
  mulMat2 M N , trans (det-mul3 M N) (cong₂ mul3 p q)

sl2-e : SL2
sl2-e = I2 , refl

sl2-inv : SL2 → SL2
sl2-inv (M , p) = adj M , trans (det-adj M) p

--------------------------------------------------------------------------------
-- 3. 群律（全部落在首分量）
--------------------------------------------------------------------------------

sl2-assoc : ∀ x y z → (sl2-mul (sl2-mul x y) z) ≈s (sl2-mul x (sl2-mul y z))
sl2-assoc (M , _) (N , _) (K , _) = mat-assoc M N K

sl2-unitˡ : ∀ x → (sl2-mul sl2-e x) ≈s x
sl2-unitˡ (M , _) = mat-idˡ M

sl2-unitʳ : ∀ x → (sl2-mul x sl2-e) ≈s x
sl2-unitʳ (M , _) = mat-idʳ M

sl2-invˡ : ∀ x → (sl2-mul (sl2-inv x) x) ≈s sl2-e
sl2-invˡ (M , p) = det-one-adj M p

sl2-invʳ : ∀ x → (sl2-mul x (sl2-inv x)) ≈s sl2-e
sl2-invʳ (M , p) = det-one-mul M p

sl2-cong : ∀ {a b c d : SL2} → a ≈s c → b ≈s d → (sl2-mul a b) ≈s (sl2-mul c d)
sl2-cong {_} {_} {_} {_} h1 h2 = cong₂ mulMat2 h1 h2

--------------------------------------------------------------------------------
-- 4. 装配成 SetoidGroupData
--------------------------------------------------------------------------------

SL2-setoid-group : SetoidGroupData
SetoidGroupData.Carrier   SL2-setoid-group = SL2
SetoidGroupData._≈_       SL2-setoid-group = _≈s_
SetoidGroupData.refl≈     SL2-setoid-group = refl
SetoidGroupData.sym≈      SL2-setoid-group = sym
SetoidGroupData.trans≈    SL2-setoid-group = trans
SetoidGroupData._⋆_       SL2-setoid-group = sl2-mul
SetoidGroupData.⋆-cong    SL2-setoid-group {a} {b} {c} {d} h1 h2 =
  sl2-cong {a} {b} {c} {d} h1 h2
SetoidGroupData.e₀        SL2-setoid-group = sl2-e
SetoidGroupData.ι         SL2-setoid-group = sl2-inv
SetoidGroupData.unitˡ     SL2-setoid-group = sl2-unitˡ
SetoidGroupData.unitʳ     SL2-setoid-group = sl2-unitʳ
SetoidGroupData.invˡ      SL2-setoid-group = sl2-invˡ
SetoidGroupData.invʳ      SL2-setoid-group = sl2-invʳ
SetoidGroupData.assoc     SL2-setoid-group = sl2-assoc
