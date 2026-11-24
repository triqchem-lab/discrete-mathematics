{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Application.Problems.RH.TraceTableF3
-- F₃ 非奇异曲线的迹集 = 恰 7 值（M1 · A1.6）
--
-- 数学背景:
--   Hasse（A1.5，HasseForm = 1 ≤ #E ≤ 7）⟹ t = 4 − #E ∈ {−3,…,3}。
--   本模块把这个「恰 7 值」钉成两个方向 + 值的区分性：
--   · 全覆盖  trace-in-Tr3 : ∀ c → IsNonSing c → Σ Tr3 (λ v → tℤ c ≡ val v)
--     （27 构造子分派；9 奇异分支 ⊥-elim，18 非奇异分支 refl）
--   · 实现    trace-witness : ∀ (v : Tr3) → Σ CurveF3 (λ c → IsNonSing c × tℤ c ≡ val v)
--     （7 值各给一条见证曲线：c021/c101/c201/c010/c102/c202/c022）
--   · 区分性  val-inj : val a ≡ val b → a ≡ b（49 案：7 对角 refl + 42 吸收）
--   两方向 + 单射 ⟹ 「迹集 = Tr3 恰 7 值」；Tr3 的 3∣值分类（超奇异面）归 A3.1。
--
-- 诚实边界: 本件只陈述「迹值落点」，不断言「每个值恰对应一个同构类」
--   （那是 Waterhouse 分类，q=3 时值与类一一对应，见 A3.2；此处不冒充）。
--   迹以 ℤ 承载（tℤ，见 CountF3）；值类型 Tr3 是枚举，不承载算术。

module Sovereign.Application.Problems.RH.TraceTableF3 where

open import Data.Empty using (⊥-elim)
open import Data.Integer using (ℤ; +_; -[1+_])
open import Data.Product using (Σ; _×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Sovereign.Base.Trit using (Trit; T₀; T₁; T₂)
open import Sovereign.Application.Problems.RH.CurveF3
open import Sovereign.Application.Problems.RH.CountF3

--------------------------------------------------------------------------------
-- §1. 迹值类型 Tr3 与嵌入 val
--------------------------------------------------------------------------------

data Tr3 : Set where
  trM3 trM2 trM1 trZ trP1 trP2 trP3 : Tr3

val : Tr3 → ℤ
val trM3 = -[1+ 2 ]   -- −3
val trM2 = -[1+ 1 ]   -- −2
val trM1 = -[1+ 0 ]   -- −1
val trZ  = + 0
val trP1 = + 1
val trP2 = + 2
val trP3 = + 3

-- val 单射（49 案：对角 refl，非对角 λ()）
val-inj : ∀ (a b : Tr3) → val a ≡ val b → a ≡ b
val-inj trM3 trM3 e = refl
val-inj trM3 trM2 ()
val-inj trM3 trM1 ()
val-inj trM3 trZ  ()
val-inj trM3 trP1 ()
val-inj trM3 trP2 ()
val-inj trM3 trP3 ()
val-inj trM2 trM3 ()
val-inj trM2 trM2 e = refl
val-inj trM2 trM1 ()
val-inj trM2 trZ  ()
val-inj trM2 trP1 ()
val-inj trM2 trP2 ()
val-inj trM2 trP3 ()
val-inj trM1 trM3 ()
val-inj trM1 trM2 ()
val-inj trM1 trM1 e = refl
val-inj trM1 trZ  ()
val-inj trM1 trP1 ()
val-inj trM1 trP2 ()
val-inj trM1 trP3 ()
val-inj trZ  trM3 ()
val-inj trZ  trM2 ()
val-inj trZ  trM1 ()
val-inj trZ  trZ  e = refl
val-inj trZ  trP1 ()
val-inj trZ  trP2 ()
val-inj trZ  trP3 ()
val-inj trP1 trM3 ()
val-inj trP1 trM2 ()
val-inj trP1 trM1 ()
val-inj trP1 trZ  ()
val-inj trP1 trP1 e = refl
val-inj trP1 trP2 ()
val-inj trP1 trP3 ()
val-inj trP2 trM3 ()
val-inj trP2 trM2 ()
val-inj trP2 trM1 ()
val-inj trP2 trZ  ()
val-inj trP2 trP1 ()
val-inj trP2 trP2 e = refl
val-inj trP2 trP3 ()
val-inj trP3 trM3 ()
val-inj trP3 trM2 ()
val-inj trP3 trM1 ()
val-inj trP3 trZ  ()
val-inj trP3 trP1 ()
val-inj trP3 trP2 ()
val-inj trP3 trP3 e = refl

--------------------------------------------------------------------------------
-- §2. 全覆盖: 每条非奇异曲线的迹都落在 Tr3
--------------------------------------------------------------------------------

trace-in-Tr3 : ∀ (c : CurveF3) → IsNonSing c → Σ Tr3 (λ v → tℤ c ≡ val v)
trace-in-Tr3 (mkC T₀ T₀ T₀) h = ⊥-elim (h refl)
trace-in-Tr3 (mkC T₀ T₀ T₁) h = ⊥-elim (h refl)
trace-in-Tr3 (mkC T₀ T₀ T₂) h = ⊥-elim (h refl)
trace-in-Tr3 (mkC T₀ T₁ T₀) h = ( trZ , refl )    -- t = 0
trace-in-Tr3 (mkC T₀ T₁ T₁) h = ( trZ , refl )    -- t = 0
trace-in-Tr3 (mkC T₀ T₁ T₂) h = ( trZ , refl )    -- t = 0
trace-in-Tr3 (mkC T₀ T₂ T₀) h = ( trZ , refl )    -- t = 0
trace-in-Tr3 (mkC T₀ T₂ T₁) h = ( trM3 , refl )   -- t = −3
trace-in-Tr3 (mkC T₀ T₂ T₂) h = ( trP3 , refl )   -- t = +3
trace-in-Tr3 (mkC T₁ T₀ T₀) h = ⊥-elim (h refl)
trace-in-Tr3 (mkC T₁ T₀ T₁) h = ( trM2 , refl )   -- t = −2
trace-in-Tr3 (mkC T₁ T₀ T₂) h = ( trP1 , refl )   -- t = +1
trace-in-Tr3 (mkC T₁ T₁ T₀) h = ⊥-elim (h refl)
trace-in-Tr3 (mkC T₁ T₁ T₁) h = ( trM2 , refl )   -- t = −2
trace-in-Tr3 (mkC T₁ T₁ T₂) h = ( trP1 , refl )   -- t = +1
trace-in-Tr3 (mkC T₁ T₂ T₀) h = ( trM2 , refl )   -- t = −2
trace-in-Tr3 (mkC T₁ T₂ T₁) h = ( trP1 , refl )   -- t = +1
trace-in-Tr3 (mkC T₁ T₂ T₂) h = ⊥-elim (h refl)
trace-in-Tr3 (mkC T₂ T₀ T₀) h = ⊥-elim (h refl)
trace-in-Tr3 (mkC T₂ T₀ T₁) h = ( trM1 , refl )   -- t = −1
trace-in-Tr3 (mkC T₂ T₀ T₂) h = ( trP2 , refl )   -- t = +2
trace-in-Tr3 (mkC T₂ T₁ T₀) h = ⊥-elim (h refl)
trace-in-Tr3 (mkC T₂ T₁ T₁) h = ( trM1 , refl )   -- t = −1
trace-in-Tr3 (mkC T₂ T₁ T₂) h = ( trP2 , refl )   -- t = +2
trace-in-Tr3 (mkC T₂ T₂ T₀) h = ( trP2 , refl )   -- t = +2
trace-in-Tr3 (mkC T₂ T₂ T₁) h = ⊥-elim (h refl)
trace-in-Tr3 (mkC T₂ T₂ T₂) h = ( trM1 , refl )   -- t = −1

--------------------------------------------------------------------------------
-- §3. 实现: 每个迹值都有非奇异曲线实现（见证表）
--------------------------------------------------------------------------------

trace-witness : ∀ (v : Tr3) → Σ CurveF3 (λ c → IsNonSing c × tℤ c ≡ val v)
trace-witness trM3 = ( c021 , ns-c021 , refl )   -- E₂（BSD 短形）
trace-witness trM2 = ( c101 , ns-c101 , refl )
trace-witness trM1 = ( c201 , ns-c201 , refl )
trace-witness trZ  = ( c010 , ns-c010 , refl )
trace-witness trP1 = ( c102 , ns-c102 , refl )
trace-witness trP2 = ( c202 , ns-c202 , refl )
trace-witness trP3 = ( c022 , ns-c022 , refl )   -- E₆（BSD 短形）
