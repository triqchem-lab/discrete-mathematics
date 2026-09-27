{-# OPTIONS --rewriting --guardedness #-}
-- | Sovereign.Algebra.ProjectionFidelity
-- 投影函子保真度通用判据（QUAD.T6 模板化；24 号 :16 尺子）
--
-- 数学背景:
--   24-four-poles-vs-presentation-group.md:16 判据统一: 每个「极」= 一个投影
--   + 一条保真度命题，尺子 =「是否存在保单位单射（无损往返）」（:83 分档:
--   正档 = 存在性无损 / 否定档 = 不存在单射）。
--   【按用户审阅收窄】模板仅适用于**群/环同态型投影**（crt12、toDuodec）；
--   **非**同态型（A₄ 轨道商、∥_∥₂ 截断、R₁₂ 乘法）须**各自定义**保真度判据
--   （见 QUAD.T7），不得强行套用本模板。
-- 核心原则:
--   1. 判据 = 无损往返: 存在 retraction s，s ∘ f = id（保单位单射）
--   2. 判据推论: 无损往返 ⇒ 单射（保真度的「单射」半）
--   3. 两实例: CRT 加法侧投影 (π3,π4)（section = crt12）与 toDuodec（双向无损）
module Sovereign.Algebra.ProjectionFidelity where

open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans)
open import Relation.Nullary using (¬_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Fin using (Fin)
open import Sovereign.Base.Trit using (Trit)
open import Sovereign.Algebra.Duodecimal using (Duodec; π3; π4; crt12; crt12-roundtrip)
open import Sovereign.Algebra.GroupTheory.DuodecClock using
  (DuodecPoint; toDuodec; fromDuodec; duodec-clock-roundtrip; clock-duodec-roundtrip)

-- 通用判据（正档）：投影 f 保真 = 无损往返（保单位单射）
record Lossless {S T : Set} (f : S → T) : Set where
  field
    retraction : T → S
    roundtrip : ∀ x → retraction (f x) ≡ x

-- 判据推论：无损往返 ⇒ 单射（像相等 ⇒ 源相等）
lossless-injective : ∀ {S T} (f : S → T) → Lossless f → ∀ x y → f x ≡ f y → x ≡ y
lossless-injective f L x y p =
  trans (sym (Lossless.roundtrip L x))
        (trans (cong (Lossless.retraction L) p) (Lossless.roundtrip L y))

-- 否定档（24 号 :83）：非单射 ⇒ 无损往返不存在
-- （用于非同态型的各自判据对照；本模板不为非同态型实例化）
NotLossless : ∀ {S T : Set} (f : S → T) → Set
NotLossless f = ¬ (∀ x y → f x ≡ f y → x ≡ y)

-- 两档互斥（判据自洽）
lossless-excludes-collapse : ∀ {S T : Set} (f : S → T) → Lossless f → ¬ (NotLossless f)
lossless-excludes-collapse f L notInj = notInj (lossless-injective f L)

-- ============ 实例化（≥2 处；仅群/环同态型） ============

-- 实例 1（正档）：CRT 加法侧投影 (π3,π4) : Duodec → Trit × Fin 4，section = crt12
-- （无损往返见证 = Duodecimal.crt12-roundtrip；与 ABCL1.additive-dim-passes 同义）
crt12-proj : Duodec → Trit × Fin 4
crt12-proj n = π3 n , π4 n

lossless-crt12 : Lossless crt12-proj
lossless-crt12 = record
  { retraction = λ p → crt12 (proj₁ p) (proj₂ p)
  ; roundtrip = crt12-roundtrip
  }

-- 实例 2（正档）：toDuodec（群同构型投影），section = fromDuodec
-- （⚠ 展示层有损——生成方式信息不随 toDuodec 保留；本判据只量映射层无损往返，
--   展示层保真另论（24 号 T7 更正线））
lossless-toDuodec : Lossless toDuodec
lossless-toDuodec = record
  { retraction = fromDuodec
  ; roundtrip = clock-duodec-roundtrip
  }

-- 附：反向亦无损（群同构双向）
lossless-fromDuodec : Lossless fromDuodec
lossless-fromDuodec = record
  { retraction = toDuodec
  ; roundtrip = duodec-clock-roundtrip
  }
