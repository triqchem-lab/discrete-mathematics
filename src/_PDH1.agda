{-# OPTIONS --rewriting --guardedness #-}

-- | _PDH1
-- 离散 Hurewicz dim-1 先行（方案 C 混合——DH-1/2/3 三段）
--
-- 数学背景：dim-1 离散 Hurewicz 映射 h₁ : π₁ᵈ → H₁ 的 GF(3) 形。
--   代码为镜：npos/nneg 计数对 = φ 的边链数据（设计洞见）；
--   目标图 Gskel two-chain（无三角 ⇒ AHomotopy=对角，计数精确不变）。
--   H₁^FAb(Gskel two-chain) ≅ (ℕ,+)（对角生成）——h₁ 即 rounds 计数；
--   GF(3) 面 = 模 3 投影 h₁₃ := trit3 ∘ h₁。
-- 诚实边界：
-- 1. Thm 5.4 GF(3) 类比 ≠ 文献 ℤ 版（commutator/abelianization 形另述——本件为
--    「模 3 边链投影」形：核 = 3·子幺半群类）
-- 2. n≥2 留 DH-4；一般图（有三角）的计数不变性由 ∂(三角) 承载——立界
-- 包含：§0 基础件（npos-++/trit3/分3）｜§1 DH-1（h₁ 下降+同态）｜
--       §2 DH-2（满+核特征）｜§3 DH-3（Z¹ 锯齿对照）｜§4 核对层

module _PDH1 where

open import Data.Nat using (ℕ; zero; suc) renaming (_+_ to _+ℕ_; _*_ to _*ℕ_)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.Product using (Σ; _,_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Cubical.Foundations.Prelude
  using (_≡_; refl; sym; cong; cong₂; funExt; isSet; _∙_; subst)
open import Cubical.Data.Nat using () renaming (isSetℕ to isSetNat)
open import Cubical.HITs.SetQuotients using (_/_; [_])
open import Cubical.HITs.SetQuotients.Properties
  using (elimProp2) renaming (elimProp to elimProp/q)

open import Sovereign.Base.Trit using (Trit; T₀; T₁; T₂)
open import Sovereign.Topology.BarceloAHomotopy
  using (DiGraph; Walk; nil; cons; _++w_; AHomotopy)
open import _PPI2 using (π₁ᵈ; _⊞ᵈ_; π₁ᵈ-rec)
open import Sovereign.Synthesis.McCordPi0 using (two-chain)
open import _PPI4 using (Gskel)
open import _PPI4c using (AStep-sk-empty; ah-diag-sk)
open import _PPI4g using (npos; nneg; loopK; loopK-+; npos-loopK)
open import _PPI4i using (unloop0; walk01; walk10)

--------------------------------------------------------------------------------
-- §0 基础件：npos 可加 / trit3（模 3 投影）/ 分 3 分解
--------------------------------------------------------------------------------

-- npos 对拼接可加（npos 结构三条 + 对首参归纳）
npos-++ : ∀ {u v w} (p : Walk (Gskel two-chain) u v) (q : Walk (Gskel two-chain) v w)
  → npos (p ++w q) ≡ npos p +ℕ npos q
npos-++ (nil _) q = refl
npos-++ (cons (inj₁ e) p) q = cong suc (npos-++ p q)
npos-++ (cons (inj₂ e) p) q = npos-++ p q

-- trit3：ℕ → Trit 的 3-周期截取（GF(3) 值形）
trit3 : ℕ → Trit
trit3 zero = T₀
trit3 (suc zero) = T₁
trit3 (suc (suc zero)) = T₂
trit3 (suc (suc (suc k))) = trit3 k

-- 构造子分离（Path 版 λ() 替代——discriminate 三件）
T₁≢T₀ : T₁ ≡ T₀ → ⊥
T₁≢T₀ p = subst P (sym p) tt
  where
  P : Trit → Set
  P T₀ = ⊤
  P T₁ = ⊥
  P T₂ = ⊤

T₂≢T₀ : T₂ ≡ T₀ → ⊥
T₂≢T₀ p = subst P (sym p) tt
  where
  P : Trit → Set
  P T₀ = ⊤
  P T₁ = ⊤
  P T₂ = ⊥

-- 3m：递归三倍（suc³ 形——defeq 友好）
3m : ℕ → ℕ
3m zero = zero
3m (suc m) = suc (suc (suc (3m m)))

-- 分 3 分解：trit3 k ≡ T₀ ⟹ k = 3m
div3 : ∀ k → trit3 k ≡ T₀ → Σ ℕ (λ m → k ≡ 3m m)
div3 zero h = 0 , refl
div3 (suc zero) h = ⊥-elim (T₁≢T₀ h)
div3 (suc (suc zero)) h = ⊥-elim (T₂≢T₀ h)
div3 (suc (suc (suc k))) h with div3 k h
... | m , eq = suc m , cong (λ x → suc (suc (suc x))) eq

-- 3m 的 trit3 消失
trit3-3m : ∀ m → trit3 (3m m) ≡ T₀
trit3-3m zero = refl
trit3-3m (suc m) = trit3-3m m

--------------------------------------------------------------------------------
-- §1 DH-1：h₁（dim-1 离散 Hurewicz——walk 计数的商面下降）
--------------------------------------------------------------------------------

-- 钉形辅助件（[_] 隐式 R 由期望类型固定——meta 防御）
[_]G : Walk (Gskel two-chain) fzero fzero → π₁ᵈ (Gskel two-chain) fzero
[_]G w = [ w ]

QK : ℕ → π₁ᵈ (Gskel two-chain) fzero
QK k = [ loopK k ]
--------------------------------------------------------------------------------

-- walk 级：h̃₁ = npos（计数 = 边链 (e01+e10) 坐标）
-- 合同性：AHomotopy 精确保计数（ah-diag-sk：Gskel 无三角 ⇒ 对角化定理）
h̃₁-resp : ∀ {w1 w2 : Walk (Gskel two-chain) fzero fzero}
  → AHomotopy (Gskel two-chain) w1 w2 → npos w1 ≡ npos w2
h̃₁-resp h = cong npos (ah-diag-sk h)

-- DH-1 主件：h₁（商面下降——isSetNat 承载）
h₁ : π₁ᵈ (Gskel two-chain) fzero → ℕ
h₁ = π₁ᵈ-rec isSetNat (λ w → npos w) (λ _ _ h → h̃₁-resp h)

-- 同态性（walk 级）
h̃₁-++ : ∀ (w w' : Walk (Gskel two-chain) fzero fzero)
  → npos (w ++w w') ≡ npos w +ℕ npos w'
h̃₁-++ = npos-++

-- 同态性（商面）：h₁ 保 ⊞ᵈ
h₁-hom : ∀ (q q' : π₁ᵈ (Gskel two-chain) fzero) → h₁ (q ⊞ᵈ q') ≡ h₁ q +ℕ h₁ q'
h₁-hom = elimProp2 (λ _ _ → isSetNat _ _) go
  where
  go : ∀ w w' → h₁ ([ w ] ⊞ᵈ [ w' ]) ≡ h₁ [ w ] +ℕ h₁ [ w' ]
  go w w' = h̃₁-++ w w'

--------------------------------------------------------------------------------
-- §2 DH-2：满性 + 核特征（Thm 5.4 GF(3) 类比——诚实标注）
--------------------------------------------------------------------------------

-- 满性：h₁ 像 = 全 ℕ（⟨[w2]⟩ 生成——gskel-classify 同源）
h₁-surj : ∀ m → Σ (π₁ᵈ (Gskel two-chain) fzero) (λ q → h₁ q ≡ m)
h₁-surj m = [ loopK m ] , npos-loopK m

-- 核（ℕ 面）：h₁ q ≡ 0 ⟹ q ≡ [nil]（walk 级经 unloop0 桥）
ker-h₁-walk : ∀ (w : Walk (Gskel two-chain) fzero fzero)
  → npos w ≡ zero → [ w ] ≡ [ nil fzero ]
ker-h₁-walk w h =
  cong [_]G (unloop0 w) ∙ cong QK h

-- GF(3) 投影面：h₁₃ = trit3 ∘ h₁（模 3 边链投影——组合定义免二次下降）
h₁₃ : π₁ᵈ (Gskel two-chain) fzero → Trit
h₁₃ q = trit3 (h₁ q)

-- 诚实边界（Thm 5.4 类比的精确定位）：
--   文献 Thm 5.4（Gao-Yang 2024，ℤ 版）：Hurewicz 映射满 + Ker = 换位子（abelianization 核）。
--   本件 GF(3) 形：h₁₃ 满 + Ker = 3·子幺半群类（模 3 投影核）——**非 commutator 形**；
--   两形关系（ℤ 版商面 mod 3 化 ⟶ 本件）留 DH-4 对照定理。

-- h₁₃ 满
h₁₃-surj : ∀ t → Σ (π₁ᵈ (Gskel two-chain) fzero) (λ q → h₁₃ q ≡ t)
h₁₃-surj T₀ = [ loopK 0 ] , refl
h₁₃-surj T₁ = [ loopK 1 ] , refl
h₁₃-surj T₂ = [ loopK 2 ] , refl

-- 核特征（GF(3) 面，walk 级双向）
ker-h₁₃-→ : ∀ (w : Walk (Gskel two-chain) fzero fzero)
  → trit3 (npos w) ≡ T₀ → Σ ℕ (λ m → npos w ≡ 3m m)
ker-h₁₃-→ w h = div3 (npos w) h

ker-h₁₃-← : ∀ m → h₁₃ [ loopK (3m m) ] ≡ T₀
ker-h₁₃-← m = cong trit3 (npos-loopK (3m m)) ∙ trit3-3m m

--------------------------------------------------------------------------------
-- §3 DH-3：Z¹ 锯齿对照件（Gskel 型图桥）
--------------------------------------------------------------------------------

-- 锯齿闭合成环族：saw-cycle k = walk01 k（0→1，奇长 2k+1）++w walk10 k（1→0）
saw-cycle : ℕ → Walk (Gskel two-chain) fzero fzero
saw-cycle k = walk01 k ++w walk10 k

-- 计数桥：h₁ 沿锯齿 = 两段 npos 之和（npos-++ 直得）
saw-count : ∀ k → npos (saw-cycle k) ≡ npos (walk01 k) +ℕ npos (walk10 k)
saw-count k = npos-++ (walk01 k) (walk10 k)

-- 计数↔生成元桥：任意闭 walk（锯齿族含）↔ loopK 计数形（unloop0——Gskel 分类桥）
saw-bridge : ∀ k → [ saw-cycle k ] ≡ [ loopK (npos (saw-cycle k)) ]
saw-bridge k = cong [_]G (unloop0 (saw-cycle k))

-- 锯齿像（GF(3) 面）
saw-h₁₃ : ∀ k → h₁₃ [ saw-cycle k ] ≡ trit3 (npos (walk01 k) +ℕ npos (walk10 k))
saw-h₁₃ k = cong trit3 (saw-count k)

--------------------------------------------------------------------------------
-- §4 核对层
--------------------------------------------------------------------------------

check-h1-loopK : ∀ k → h₁ [ loopK k ] ≡ k
check-h1-loopK k = npos-loopK k

check-h1-nil : h₁ [ nil fzero ] ≡ zero
check-h1-nil = refl

check-h13-0 : h₁₃ [ loopK 0 ] ≡ T₀
check-h13-0 = refl

check-h13-1 : h₁₃ [ loopK 1 ] ≡ T₁
check-h13-1 = refl

check-h13-2 : h₁₃ [ loopK 2 ] ≡ T₂
check-h13-2 = refl

check-h13-3 : h₁₃ [ loopK 3 ] ≡ T₀
check-h13-3 = refl

check-ker3 : ∀ m → h₁₃ [ loopK (3m m) ] ≡ T₀
check-ker3 = ker-h₁₃-←
