{-# OPTIONS --rewriting --guardedness #-}
------------------------------------------------------------------------
-- | Sovereign.Problem.Sqrt2.GF9Sqrt2
-- 方案 A：x² = 2 在 GF(9) 中的解集恰为 {α, σ(α)} —— Frobenius 共轭对
--
-- 数学背景:
--   GF(9) = GF(3)[α]/(α²+1)，α² = 2（char 3 下 2 = 1 的加法逆元，
--   即惯例记号 "-1"；元素集仍是标准三进制 {0,1,2}）。
--   方程 x² = 2 在 GF(9) 中恰有两个根 α 与 σ(α) = α³ = 2α，
--   构成一个 Frobenius 共轭对；GF(3) 基域内三候选 {0,1,2} 全灭。
--   与序世界的 √2 无理性（Sqrt2Irrational）互为对照：
--   同一方程，有限域可解、有理数域无解。
--
-- 证明风格（对齐 docs/duodecimal/12 号 §2.4 裁定）:
--   结构由 GF9.agda 的既有定义承载（alpha / galoisConjugate / *gf9），
--   本模块的穷举是定义性等式的核对（refl / 荒谬模式），不构造新数学对象。
--
-- 依赖: Sovereign.Algebra.GF9（只读导入，不改基础设施）；0 postulate。
------------------------------------------------------------------------

module Sovereign.Problem.Sqrt2.GF9Sqrt2 where

open import Data.Empty using (⊥)
open import Data.Product using (_×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans; sym)
open import Sovereign.Base.Trit using (Trit; T₀; T₁; T₂)
open import Sovereign.Algebra.GF9

gf9-two : GF9
gf9-two = T₂ , T₀

------------------------------------------------------------------------
-- 1. 存在性：α 与 σ(α) 都是根

root-alpha : alpha *gf9 alpha ≡ gf9-two
root-alpha = alpha-squared

root-sigma-alpha : galoisConjugate alpha *gf9 galoisConjugate alpha ≡ gf9-two
root-sigma-alpha = refl

------------------------------------------------------------------------
-- 2. 完备性：解集 ⊆ {α, σ(α)}（9 case 穷举，非根情形平方范型直接冲突）

sqr2-complete : ∀ x → x *gf9 x ≡ gf9-two
             → (x ≡ alpha) ⊎ (x ≡ galoisConjugate alpha)
sqr2-complete (T₀ , T₀) ()
sqr2-complete (T₀ , T₁) _ = inj₁ refl
sqr2-complete (T₀ , T₂) _ = inj₂ refl
sqr2-complete (T₁ , T₀) ()
sqr2-complete (T₁ , T₁) ()
sqr2-complete (T₁ , T₂) ()
sqr2-complete (T₂ , T₀) ()
sqr2-complete (T₂ , T₁) ()
sqr2-complete (T₂ , T₂) ()

------------------------------------------------------------------------
-- 3. GF(3) 基域：三个候选根全灭（三元核对）

gf3-no-root : ∀ a → embed-gf3 a *gf9 embed-gf3 a ≡ gf9-two → ⊥
gf3-no-root T₀ ()
gf3-no-root T₁ ()
gf3-no-root T₂ ()

------------------------------------------------------------------------
-- 4. Frobenius 结构：根对在 σ 下封闭、相异，且 σ(α) = α³

root-frobenius-closed : ∀ x → x *gf9 x ≡ gf9-two
                     → galoisConjugate x *gf9 galoisConjugate x ≡ gf9-two
root-frobenius-closed x xroot =
  trans (sym (galoisConjugate-mul x x)) (trans (cong galoisConjugate xroot) refl)

sigma-alpha-is-cube : galoisConjugate alpha ≡ alpha *gf9 (alpha *gf9 alpha)
sigma-alpha-is-cube = frobenius-alpha-is-cube

roots-distinct : alpha ≢ galoisConjugate alpha
roots-distinct = alpha-distinct-neg-alpha
