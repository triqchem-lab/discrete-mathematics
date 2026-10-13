{-# OPTIONS --cubical --rewriting --guardedness #-}

-- | _PPI4d —— (d) v2-2：Gskel 偶长分离（≥3 类两两可分）
--
-- 数学背景（v2 路线第 2 段）：
--   v2-1 已证 Gskel two-chain 上 AHomotopy = 对角 ⇒ π₁ 类 = walk 本身。
--   本段给 ≥3 个两两不同类的闭 walk：w0 = nil（len 0）、w2 = 0→1→0（len 2）、
--   w4 = (0→1→0)²（len 4）——用长度分离器族（Sz / twoB）两两分开。
--   附带偶长结构（Gskel 边必跨顶点 ⇒ 闭 walk 交替 ⇒ len 为偶）——
--   「偶长分离」名副其实，并为 v2-4 的自由幺半群图景（π₁ᵈ(Gskel) ≅ (ℕ,+)）供料。
--
-- 核心原则：
-- 1. 分离器走 Bool 后像（isZeroB 系）——Cubical ≡ 反驳安全（K 禁用）
-- 2. 双世界钉参（KEdge ≢ = Builtin）+ 模式细化（#52 教训）
-- 3. 零洞零 postulate
--
-- 包含：e01/e10 边实例｜w0/w2/w4｜Sz/twoB 分离器｜两两 ¬∼ 三件｜边取向二件｜even2-len
module _PPI4d where

open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_×_; _,_; ∃-syntax)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using () renaming (refl to reflᴱ; _≡_ to _≡ᴱ_)
open import Cubical.Foundations.Prelude using (_≡_; refl; cong)
open import Sovereign.Topology.BarceloAHomotopy
  using (DiGraph; Walk; nil; cons; AHomotopy)
open import Sovereign.Synthesis.McCordPi0 using (two-chain; ⊑₂-01)
open import _PPI4 using (Gskel)
open import _PPI2 using (len; true≢false)
open import _PPI4c using (edgeGskel-neq; ah-diag-sk)

private
  module DG = DiGraph

--------------------------------------------------------------------------------
-- §1 边实例（Gskel two-chain 两条非平凡边）
--------------------------------------------------------------------------------

e01 : DG.edge (Gskel two-chain) fzero (fsuc fzero)
e01 = inj₁ (⊑₂-01 , λ ())

e10 : DG.edge (Gskel two-chain) (fsuc fzero) fzero
e10 = inj₂ (⊑₂-01 , λ ())

--------------------------------------------------------------------------------
-- §2 三个闭 walk（len 0/2/4）
--------------------------------------------------------------------------------

w0 : Walk (Gskel two-chain) fzero fzero
w0 = nil fzero

w2 : Walk (Gskel two-chain) fzero fzero
w2 = cons e01 (cons e10 (nil fzero))

w4 : Walk (Gskel two-chain) fzero fzero
w4 = cons e01 (cons e10 (cons e01 (cons e10 (nil fzero))))

--------------------------------------------------------------------------------
-- §3 分离器族（Bool 后像——Cubical 安全反驳）
--------------------------------------------------------------------------------

isZeroB : ℕ → Bool
isZeroB zero = true
isZeroB (suc _) = false

_∸_ : ℕ → ℕ → ℕ
n ∸ zero = n
zero ∸ suc _ = zero
suc n ∸ suc k = n ∸ k

-- Sz：零长探测（w0 ↦ true；w2/w4 ↦ false）
Sz : Walk (Gskel two-chain) fzero fzero → Bool
Sz w = isZeroB (len w)

-- twoB：≥4 探测（w0/w2 ↦ true；w4 ↦ false）
twoB : Walk (Gskel two-chain) fzero fzero → Bool
twoB w = isZeroB (len w ∸ 2)

-- 两两 ¬∼（对角化归约后 Bool 反驳）
w0≁w2 : AHomotopy (Gskel two-chain) w0 w2 → ⊥
w0≁w2 h = true≢false (cong Sz (ah-diag-sk h))

w0≁w4 : AHomotopy (Gskel two-chain) w0 w4 → ⊥
w0≁w4 h = true≢false (cong Sz (ah-diag-sk h))

w2≁w4 : AHomotopy (Gskel two-chain) w2 w4 → ⊥
w2≁w4 h = true≢false (cong twoB (ah-diag-sk h))

--------------------------------------------------------------------------------
-- §4 偶长结构（Gskel 边必跨顶点 ⇒ 闭 walk 交替 ⇒ len 偶）
--------------------------------------------------------------------------------

-- 边取向二件（Fin 2 模式细化）
edge-0 : ∀ {y : Fin 2} → DG.edge (Gskel two-chain) fzero y → y ≡ fsuc fzero
edge-0 {fzero} e = ⊥-elim (edgeGskel-neq fzero fzero e reflᴱ)
edge-0 {fsuc fzero} _ = refl

edge-1 : ∀ {y : Fin 2} → DG.edge (Gskel two-chain) (fsuc fzero) y → y ≡ fzero
edge-1 {fzero} _ = refl
edge-1 {fsuc fzero} e = ⊥-elim (edgeGskel-neq (fsuc fzero) (fsuc fzero) e reflᴱ)

data Even : ℕ → Set where
  even0  : Even zero
  evenSS : ∀ {n} → Even n → Even (suc (suc n))

-- 偶长定理：Gskel two-chain 闭 walk 的长度必为偶
--   （分派器形免 Cubical ≡ 搬运——nil 形尾与终点索引冲突的 case 由构造子索引自动消解）
even2-len : ∀ (w : Walk (Gskel two-chain) fzero fzero) → Even (len w)
even2-len (nil fzero) = even0
even2-len (cons {v = fzero} e _) = ⊥-elim (edgeGskel-neq fzero fzero e reflᴱ)
even2-len (cons {v = fsuc fzero} e b) = go b
  where
  go : (t : Walk (Gskel two-chain) (fsuc fzero) fzero) → Even (suc (len t))
  go (cons {v = fzero} e' b') = evenSS (even2-len b')
  go (cons {v = fsuc fzero} e' _) = ⊥-elim (edgeGskel-neq (fsuc fzero) (fsuc fzero) e' reflᴱ)
