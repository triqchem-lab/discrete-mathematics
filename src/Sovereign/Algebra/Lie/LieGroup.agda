{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Algebra.Lie.LieGroup
-- 离散李群 — 指数映射与有限群载体 (0 postulate)
--
-- 与 jac_LieGroup (Jacobian 家族) 分开的独立建立; D₄ 部分为有意重复。
--
-- 结构:
--   §1 离散指数映射 (一维): exp_C4 : Z/4 → Z[i] 单位群 C₄ (生成元 i)
--      + 单参子群律 exp(t+s) = exp(t)·exp(s) (16 项穷举)
--   §2 exp_C6 : Z/6 → Z[ω] 单位群 C₆ (生成元 1+ω) + 单参子群律 (36 项)
--   §3 D₄ 离散李群 ({±I,±αI}×C₂ 半直积, 扭结 σ(α)=−α):
--      生成关系 + 64 项封闭表 — 与 jac_LieGroup §3c 同构重复
--
-- 对应关系 (离散李群-李代数):
--   连续: exp: g → G, 单参子群 exp((t+s)X) = exp(tX)exp(sX)
--   离散: exp_C4/exp_C6 为有限周期单参子群 (C₄/C₆), 同态律逐项 refl

module Sovereign.Algebra.Lie.LieGroup where

open import Data.Fin using (Fin; toℕ) renaming (zero to fz; suc to fs)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Sovereign.Base.Trit using (Trit; T₀; T₁; T₂; _⊕_; _⊗_; negate)
open import Sovereign.Algebra.GF9 using
  (GF9; galoisConjugate; alpha; _*gf9_; _+gf9_)
import Sovereign.RootMath.Gaussian as G
import Sovereign.RootMath.Eisenstein as Eis

--------------------------------------------------------------------------------
-- §1. 离散指数映射 exp_C4: Z/4 → C₄ (Z[i] 单位群, 生成元 i)
--------------------------------------------------------------------------------

next4g : Fin 4 → Fin 4
next4g fz = fs fz
next4g (fs fz) = fs (fs fz)
next4g (fs (fs fz)) = fs (fs (fs fz))
next4g (fs (fs (fs fz))) = fz

infixl 6 _+4g_
_+4g_ : Fin 4 → Fin 4 → Fin 4
_+4g_ fz y = y
_+4g_ (fs fz) y = next4g y
_+4g_ (fs (fs fz)) y = next4g (next4g y)
_+4g_ (fs (fs (fs fz))) y = next4g (next4g (next4g y))

-- exp_C4(t) = i^t (t ∈ Z/4): 1, i, −1, −i
expC4 : Fin 4 → G.Gaussian
expC4 fz = G.unit1
expC4 (fs fz) = G.uniti
expC4 (fs (fs fz)) = G.unitm1
expC4 (fs (fs (fs fz))) = G.unitmi

-- 单参子群律: exp(t+s) = exp(t)·exp(s) (16 项穷举)
expC4-hom : ∀ t s → expC4 (t +4g s) ≡ expC4 t G.*ᵢ expC4 s
expC4-hom fz fz = refl
expC4-hom fz (fs fz) = refl
expC4-hom fz (fs (fs fz)) = refl
expC4-hom fz (fs (fs (fs fz))) = refl
expC4-hom (fs fz) fz = refl
expC4-hom (fs fz) (fs fz) = refl
expC4-hom (fs fz) (fs (fs fz)) = refl
expC4-hom (fs fz) (fs (fs (fs fz))) = refl
expC4-hom (fs (fs fz)) fz = refl
expC4-hom (fs (fs fz)) (fs fz) = refl
expC4-hom (fs (fs fz)) (fs (fs fz)) = refl
expC4-hom (fs (fs fz)) (fs (fs (fs fz))) = refl
expC4-hom (fs (fs (fs fz))) fz = refl
expC4-hom (fs (fs (fs fz))) (fs fz) = refl
expC4-hom (fs (fs (fs fz))) (fs (fs fz)) = refl
expC4-hom (fs (fs (fs fz))) (fs (fs (fs fz))) = refl

--------------------------------------------------------------------------------
-- §2. exp_C6: Z/6 → C₆ (Z[ω] 单位群, 生成元 1+ω)
--------------------------------------------------------------------------------

next6g : Fin 6 → Fin 6
next6g fz = fs fz
next6g (fs fz) = fs (fs fz)
next6g (fs (fs fz)) = fs (fs (fs fz))
next6g (fs (fs (fs fz))) = fs (fs (fs (fs fz)))
next6g (fs (fs (fs (fs fz)))) = fs (fs (fs (fs (fs fz))))
next6g (fs (fs (fs (fs (fs fz))))) = fz

infixl 6 _+6g_
_+6g_ : Fin 6 → Fin 6 → Fin 6
_+6g_ fz y = y
_+6g_ (fs fz) y = next6g y
_+6g_ (fs (fs fz)) y = next6g (next6g y)
_+6g_ (fs (fs (fs fz))) y = next6g (next6g (next6g y))
_+6g_ (fs (fs (fs (fs fz)))) y = next6g (next6g (next6g (next6g y)))
_+6g_ (fs (fs (fs (fs (fs fz))))) y = next6g (next6g (next6g (next6g (next6g y))))

-- exp_C6(t) = (1+ω)^t: 1, 1+ω, ω, −1, ω², −ω
expC6 : Fin 6 → Eis.Eisenstein
expC6 fz = Eis.unit1
expC6 (fs fz) = Eis.unitmω2
expC6 (fs (fs fz)) = Eis.unitω
expC6 (fs (fs (fs fz))) = Eis.unitm1
expC6 (fs (fs (fs (fs fz)))) = Eis.unitω2
expC6 (fs (fs (fs (fs (fs fz))))) = Eis.unitmω
-- 单参子群律: exp(t+s) = exp(t)·exp(s) (36 项穷举)
expC6-hom : ∀ t s → expC6 (t +6g s) ≡ expC6 t Eis.*ᵉ expC6 s
expC6-hom fz fz = refl
expC6-hom fz (fs fz) = refl
expC6-hom fz (fs (fs fz)) = refl
expC6-hom fz (fs (fs (fs fz))) = refl
expC6-hom fz (fs (fs (fs (fs fz)))) = refl
expC6-hom fz (fs (fs (fs (fs (fs fz))))) = refl
expC6-hom (fs fz) fz = refl
expC6-hom (fs fz) (fs fz) = refl
expC6-hom (fs fz) (fs (fs fz)) = refl
expC6-hom (fs fz) (fs (fs (fs fz))) = refl
expC6-hom (fs fz) (fs (fs (fs (fs fz)))) = refl
expC6-hom (fs fz) (fs (fs (fs (fs (fs fz))))) = refl
expC6-hom (fs (fs fz)) fz = refl
expC6-hom (fs (fs fz)) (fs fz) = refl
expC6-hom (fs (fs fz)) (fs (fs fz)) = refl
expC6-hom (fs (fs fz)) (fs (fs (fs fz))) = refl
expC6-hom (fs (fs fz)) (fs (fs (fs (fs fz)))) = refl
expC6-hom (fs (fs fz)) (fs (fs (fs (fs (fs fz))))) = refl
expC6-hom (fs (fs (fs fz))) fz = refl
expC6-hom (fs (fs (fs fz))) (fs fz) = refl
expC6-hom (fs (fs (fs fz))) (fs (fs fz)) = refl
expC6-hom (fs (fs (fs fz))) (fs (fs (fs fz))) = refl
expC6-hom (fs (fs (fs fz))) (fs (fs (fs (fs fz)))) = refl
expC6-hom (fs (fs (fs fz))) (fs (fs (fs (fs (fs fz))))) = refl
expC6-hom (fs (fs (fs (fs fz)))) fz = refl
expC6-hom (fs (fs (fs (fs fz)))) (fs fz) = refl
expC6-hom (fs (fs (fs (fs fz)))) (fs (fs fz)) = refl
expC6-hom (fs (fs (fs (fs fz)))) (fs (fs (fs fz))) = refl
expC6-hom (fs (fs (fs (fs fz)))) (fs (fs (fs (fs fz)))) = refl
expC6-hom (fs (fs (fs (fs fz)))) (fs (fs (fs (fs (fs fz))))) = refl
expC6-hom (fs (fs (fs (fs (fs fz))))) fz = refl
expC6-hom (fs (fs (fs (fs (fs fz))))) (fs fz) = refl
expC6-hom (fs (fs (fs (fs (fs fz))))) (fs (fs fz)) = refl
expC6-hom (fs (fs (fs (fs (fs fz))))) (fs (fs (fs fz))) = refl
expC6-hom (fs (fs (fs (fs (fs fz))))) (fs (fs (fs (fs fz)))) = refl
expC6-hom (fs (fs (fs (fs (fs fz))))) (fs (fs (fs (fs (fs fz))))) = refl

--------------------------------------------------------------------------------
-- §3. D₄ 离散李群: {±I, ±αI} × C₂ 半直积 (扭结 σ(α) = −α)
--     — 与 jac_LieGroup §3c 同构重复 (独立载体, 有意为之)
--------------------------------------------------------------------------------

Mat2G : Set
Mat2G = (GF9 × GF9) × (GF9 × GF9)

gf9z : GF9
gf9z = T₀ , T₀

gf9one : GF9
gf9one = T₁ , T₀

neg-gf9 : GF9 → GF9
neg-gf9 (a , b) = negate a , negate b

m2mul : Mat2G → Mat2G → Mat2G
m2mul ((a , b) , (c , d)) ((e1 , f1) , (g1 , h1)) =
  (((a *gf9 e1) +gf9 (b *gf9 g1)) , ((a *gf9 f1) +gf9 (b *gf9 h1))) ,
  (((c *gf9 e1) +gf9 (d *gf9 g1)) , ((c *gf9 f1) +gf9 (d *gf9 h1)))

sigm2 : Fin 2 → Mat2G → Mat2G
sigm2 fz A = A
sigm2 (fs fz) ((a , b) , (c , d)) =
  ((galoisConjugate a , galoisConjugate b) , (galoisConjugate c , galoisConjugate d))

SDElem : Set
SDElem = Mat2G × Fin 2

neg2g : Fin 2 → Fin 2
neg2g fz = fs fz
neg2g (fs fz) = fz

infixl 6 _+2g_
_+2g_ : Fin 2 → Fin 2 → Fin 2
_+2g_ fz y = y
_+2g_ (fs fz) y = neg2g y

infixl 20 _⋊g·_
_⋊g·_ : SDElem → SDElem → SDElem
(A , t) ⋊g· (B , s) = (m2mul A (sigm2 t B) , t +2g s)

mI2 mNegI2 mαI2 mNegαI2 : Mat2G
mI2     = (gf9one , gf9z) , (gf9z , gf9one)
mNegI2  = (neg-gf9 gf9one , gf9z) , (gf9z , neg-gf9 gf9one)
mαI2    = (alpha , gf9z) , (gf9z , alpha)
mNegαI2 = (neg-gf9 alpha , gf9z) , (gf9z , neg-gf9 alpha)

sdE  sdS  sdM  sdMS  sdA  sdAS  sdMA  sdMAS : SDElem
sdE   = mI2 , fz
sdS   = mI2 , fs fz
sdM   = mNegI2 , fz
sdMS  = mNegI2 , fs fz
sdA   = mαI2 , fz
sdAS  = mαI2 , fs fz
sdMA  = mNegαI2 , fz
sdMAS = mNegαI2 , fs fz

-- 生成关系 (D₄): a = (αI₂,0) 阶 4, b = (I₂,1) 阶 2, b a b⁻¹ = σ(a) = a⁻¹
gen-a-square : sdA ⋊g· sdA ≡ sdM
gen-a-square = refl

gen-a-order4 : sdA ⋊g· sdA ⋊g· sdA ⋊g· sdA ≡ sdE
gen-a-order4 = refl

gen-b-order2 : sdS ⋊g· sdS ≡ sdE
gen-b-order2 = refl

-- 半直积扭结: (αI₂,1)² = (αI₂·σ(αI₂), 0) = (−α²I₂, 0) = (I₂, 0)
twist-order2 : sdAS ⋊g· sdAS ≡ sdE
twist-order2 = refl

-- D₄ 共轭关系: b a b⁻¹ = σ(a) = −αI₂
d4-conjugation : sdS ⋊g· sdA ⋊g· sdS ≡ sdMA
d4-conjugation = refl

-- 封闭性全表 (8×8 = 64 项)
sdE-cl-sdE : sdE ⋊g· sdE ≡ sdE
sdE-cl-sdE = refl

sdE-cl-sdS : sdE ⋊g· sdS ≡ sdS
sdE-cl-sdS = refl

sdE-cl-sdM : sdE ⋊g· sdM ≡ sdM
sdE-cl-sdM = refl

sdE-cl-sdMS : sdE ⋊g· sdMS ≡ sdMS
sdE-cl-sdMS = refl

sdE-cl-sdA : sdE ⋊g· sdA ≡ sdA
sdE-cl-sdA = refl

sdE-cl-sdAS : sdE ⋊g· sdAS ≡ sdAS
sdE-cl-sdAS = refl

sdE-cl-sdMA : sdE ⋊g· sdMA ≡ sdMA
sdE-cl-sdMA = refl

sdE-cl-sdMAS : sdE ⋊g· sdMAS ≡ sdMAS
sdE-cl-sdMAS = refl

sdS-cl-sdE : sdS ⋊g· sdE ≡ sdS
sdS-cl-sdE = refl

sdS-cl-sdS : sdS ⋊g· sdS ≡ sdE
sdS-cl-sdS = refl

sdS-cl-sdM : sdS ⋊g· sdM ≡ sdMS
sdS-cl-sdM = refl

sdS-cl-sdMS : sdS ⋊g· sdMS ≡ sdM
sdS-cl-sdMS = refl

sdS-cl-sdA : sdS ⋊g· sdA ≡ sdMAS
sdS-cl-sdA = refl

sdS-cl-sdAS : sdS ⋊g· sdAS ≡ sdMA
sdS-cl-sdAS = refl

sdS-cl-sdMA : sdS ⋊g· sdMA ≡ sdAS
sdS-cl-sdMA = refl

sdS-cl-sdMAS : sdS ⋊g· sdMAS ≡ sdA
sdS-cl-sdMAS = refl

sdM-cl-sdE : sdM ⋊g· sdE ≡ sdM
sdM-cl-sdE = refl

sdM-cl-sdS : sdM ⋊g· sdS ≡ sdMS
sdM-cl-sdS = refl

sdM-cl-sdM : sdM ⋊g· sdM ≡ sdE
sdM-cl-sdM = refl

sdM-cl-sdMS : sdM ⋊g· sdMS ≡ sdS
sdM-cl-sdMS = refl

sdM-cl-sdA : sdM ⋊g· sdA ≡ sdMA
sdM-cl-sdA = refl

sdM-cl-sdAS : sdM ⋊g· sdAS ≡ sdMAS
sdM-cl-sdAS = refl

sdM-cl-sdMA : sdM ⋊g· sdMA ≡ sdA
sdM-cl-sdMA = refl

sdM-cl-sdMAS : sdM ⋊g· sdMAS ≡ sdAS
sdM-cl-sdMAS = refl

sdMS-cl-sdE : sdMS ⋊g· sdE ≡ sdMS
sdMS-cl-sdE = refl

sdMS-cl-sdS : sdMS ⋊g· sdS ≡ sdM
sdMS-cl-sdS = refl

sdMS-cl-sdM : sdMS ⋊g· sdM ≡ sdS
sdMS-cl-sdM = refl

sdMS-cl-sdMS : sdMS ⋊g· sdMS ≡ sdE
sdMS-cl-sdMS = refl

sdMS-cl-sdA : sdMS ⋊g· sdA ≡ sdAS
sdMS-cl-sdA = refl

sdMS-cl-sdAS : sdMS ⋊g· sdAS ≡ sdA
sdMS-cl-sdAS = refl

sdMS-cl-sdMA : sdMS ⋊g· sdMA ≡ sdMAS
sdMS-cl-sdMA = refl

sdMS-cl-sdMAS : sdMS ⋊g· sdMAS ≡ sdMA
sdMS-cl-sdMAS = refl

sdA-cl-sdE : sdA ⋊g· sdE ≡ sdA
sdA-cl-sdE = refl

sdA-cl-sdS : sdA ⋊g· sdS ≡ sdAS
sdA-cl-sdS = refl

sdA-cl-sdM : sdA ⋊g· sdM ≡ sdMA
sdA-cl-sdM = refl

sdA-cl-sdMS : sdA ⋊g· sdMS ≡ sdMAS
sdA-cl-sdMS = refl

sdA-cl-sdA : sdA ⋊g· sdA ≡ sdM
sdA-cl-sdA = refl

sdA-cl-sdAS : sdA ⋊g· sdAS ≡ sdMS
sdA-cl-sdAS = refl

sdA-cl-sdMA : sdA ⋊g· sdMA ≡ sdE
sdA-cl-sdMA = refl

sdA-cl-sdMAS : sdA ⋊g· sdMAS ≡ sdS
sdA-cl-sdMAS = refl

sdAS-cl-sdE : sdAS ⋊g· sdE ≡ sdAS
sdAS-cl-sdE = refl

sdAS-cl-sdS : sdAS ⋊g· sdS ≡ sdA
sdAS-cl-sdS = refl

sdAS-cl-sdM : sdAS ⋊g· sdM ≡ sdMAS
sdAS-cl-sdM = refl

sdAS-cl-sdMS : sdAS ⋊g· sdMS ≡ sdMA
sdAS-cl-sdMS = refl

sdAS-cl-sdA : sdAS ⋊g· sdA ≡ sdS
sdAS-cl-sdA = refl

sdAS-cl-sdAS : sdAS ⋊g· sdAS ≡ sdE
sdAS-cl-sdAS = refl

sdAS-cl-sdMA : sdAS ⋊g· sdMA ≡ sdMS
sdAS-cl-sdMA = refl

sdAS-cl-sdMAS : sdAS ⋊g· sdMAS ≡ sdM
sdAS-cl-sdMAS = refl

sdMA-cl-sdE : sdMA ⋊g· sdE ≡ sdMA
sdMA-cl-sdE = refl

sdMA-cl-sdS : sdMA ⋊g· sdS ≡ sdMAS
sdMA-cl-sdS = refl

sdMA-cl-sdM : sdMA ⋊g· sdM ≡ sdA
sdMA-cl-sdM = refl

sdMA-cl-sdMS : sdMA ⋊g· sdMS ≡ sdAS
sdMA-cl-sdMS = refl

sdMA-cl-sdA : sdMA ⋊g· sdA ≡ sdE
sdMA-cl-sdA = refl

sdMA-cl-sdAS : sdMA ⋊g· sdAS ≡ sdS
sdMA-cl-sdAS = refl

sdMA-cl-sdMA : sdMA ⋊g· sdMA ≡ sdM
sdMA-cl-sdMA = refl

sdMA-cl-sdMAS : sdMA ⋊g· sdMAS ≡ sdMS
sdMA-cl-sdMAS = refl

sdMAS-cl-sdE : sdMAS ⋊g· sdE ≡ sdMAS
sdMAS-cl-sdE = refl

sdMAS-cl-sdS : sdMAS ⋊g· sdS ≡ sdMA
sdMAS-cl-sdS = refl

sdMAS-cl-sdM : sdMAS ⋊g· sdM ≡ sdAS
sdMAS-cl-sdM = refl

sdMAS-cl-sdMS : sdMAS ⋊g· sdMS ≡ sdA
sdMAS-cl-sdMS = refl

sdMAS-cl-sdA : sdMAS ⋊g· sdA ≡ sdMS
sdMAS-cl-sdA = refl

sdMAS-cl-sdAS : sdMAS ⋊g· sdAS ≡ sdM
sdMAS-cl-sdAS = refl

sdMAS-cl-sdMA : sdMAS ⋊g· sdMA ≡ sdS
sdMAS-cl-sdMA = refl

sdMAS-cl-sdMAS : sdMAS ⋊g· sdMAS ≡ sdE
sdMAS-cl-sdMAS = refl

-- 0 postulate.
