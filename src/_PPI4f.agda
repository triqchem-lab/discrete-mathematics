{-# OPTIONS --cubical --rewriting --guardedness #-}

-- | _PPI4f —— (d) v2-4：幂等汇合 + 无同构（分水岭定稿）
--
-- 数学背景（v2 路线第 4 段·收口件）：
--   Gcmp 侧：[loop] 幂等（自环双段 slide 并类）+ 分类引理（v2-3：恰两类）；
--   Gskel 侧：仅 [nil] 幂等（gskel-idem——len 分析 + 对角化归约）。
--   MonoidIso 输运幂等元 ⇒ to [loop] = [nil]_B = to [nil]_A ⇒ [loop] ≡ [nil]_A
--   ⇒ selfloop-quot-≠ 矛盾 ⇒ **无 MonoidIso**。
--   分水岭定稿：π₁ᵈ(Gcmp two-chain) = 2 元幂等幺半群；π₁ᵈ(Gskel two-chain) ⊇ ⟨[w2]⟩ ≅ (ℕ,+)
--   ——「对称图（可比闭包）vs 有向骨架」的群/幂等幺半群分界（Barcelo 分水岭组合定理形）。
--
-- 核心原则：
-- 1. rec-β 判定成立（b2 群 ⊞ᵈ-unitˡ = refl 实证）——⊞-rep 走判定展开零引理
-- 2. 幂等分析走 len（对角化归约 ah-diag-sk + len-++ + add-suc-≢ 小归纳）
-- 3. 零洞零 postulate
--
-- 包含：loop-squash（自环幂等）｜lenq/len-++/n+n⇒0 小件｜gskel-idem（B 侧幂等唯一）｜
--       no-π₁-iso（主件）｜分水岭定稿注记
module _PPI4f where

open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.Sum using (inj₁; inj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using () renaming (refl to reflᴱ)
open import Cubical.Foundations.Prelude using (_≡_; refl; sym; cong; _∙_)
open import Cubical.Foundations.HLevels using (isProp; isPropΠ)
open import Cubical.HITs.SetQuotients using ([_]; squash/; eq/; elimProp)
open import Cubical.Data.Nat using (isSetℕ)
open import Sovereign.Synthesis.McCordCore using (cmpEdge)
open import Sovereign.Synthesis.McCordPi0 using (two-chain)
open import Sovereign.Synthesis.BarceloAHomotopy
  using (DiGraph; Walk; nil; cons; _++w_; AHomotopy; slide; expand; refl'; trans'; gen)
open import _PPI using (Loop)
open import _PPI2 using (π₁ᵈ; len; _⊞ᵈ_; π₁ᵈ-rec; true≢false)
open import _PPI4 using (Gskel; Gcmp; MonoidIso)
open import _PPI4b using (loop-e; selfloop-walk; selfloop-quot-≠)
open import _PPI4c using (ah-diag-sk)

private
  module DG = DiGraph
  module MI = MonoidIso

--------------------------------------------------------------------------------
-- §1 Gcmp 侧：[loop] 幂等（自环双段 slide 并类）
--------------------------------------------------------------------------------

loop-squash : _≡_ {A = π₁ᵈ (Gcmp two-chain) fzero}
  ([ selfloop-walk ] ⊞ᵈ [ selfloop-walk ]) [ selfloop-walk ]
loop-squash = eq/ (selfloop-walk ++w selfloop-walk) selfloop-walk
  (gen (slide (nil fzero) (nil fzero) loop-e loop-e loop-e))

--------------------------------------------------------------------------------
-- §2 Gskel 侧小件（len 分析——对角化归约）
--------------------------------------------------------------------------------

isZeroB : ℕ → Bool
isZeroB zero = true
isZeroB (suc _) = false

snotz-len : ∀ {n : ℕ} → suc n ≡ zero → ⊥
snotz-len p = true≢false (sym (cong isZeroB p))

suc-inj : ∀ {a b : ℕ} → suc a ≡ suc b → a ≡ b
suc-inj = cong predℕ
  where predℕ : ℕ → ℕ
        predℕ zero = zero
        predℕ (suc n) = n

-- len 长度保持（Gskel 上 len 是商不变量——ah-diag-sk 归约）
lenq : π₁ᵈ (Gskel two-chain) fzero → ℕ
lenq = π₁ᵈ-rec isSetℕ (λ ℓ → len ℓ) (λ ℓ ℓ' r → cong len (ah-diag-sk r))

len-++ : ∀ {u v w} (b : Walk (Gskel two-chain) u v) (ℓ : Walk (Gskel two-chain) v w)
       → len (b ++w ℓ) ≡ len b + len ℓ
len-++ (nil _) _ = refl
len-++ (cons e b) ℓ = cong suc (len-++ b ℓ)

-- 小归纳：m + suc k ≢ m
add-suc-≢ : ∀ m k → (m + suc k) ≡ m → ⊥
add-suc-≢ zero k p = snotz-len p
add-suc-≢ (suc m) k p = add-suc-≢ m k (suc-inj p)

n+n⇒0 : ∀ n → (n + n) ≡ n → n ≡ 0
n+n⇒0 zero _ = refl
n+n⇒0 (suc m) p = ⊥-elim (add-suc-≢ m m (suc-inj p))

len-zero-nil : ∀ (ℓ : Walk (Gskel two-chain) fzero fzero) → len ℓ ≡ zero → ℓ ≡ nil fzero
len-zero-nil (nil fzero) _ = refl
len-zero-nil (cons e b) p = ⊥-elim (snotz-len p)

--------------------------------------------------------------------------------
-- §3 B 侧幂等唯一：q ⊞ q ≡ q ⇒ q ≡ [nil]（elimProp 归约到代表元）
--------------------------------------------------------------------------------

gskel-idem : ∀ (q : π₁ᵈ (Gskel two-chain) fzero)
  → _≡_ {A = π₁ᵈ (Gskel two-chain) fzero} (q ⊞ᵈ q) q
  → q ≡ [ nil fzero ]
gskel-idem = elimProp (λ _ → isPropΠ (λ _ → squash/ _ _)) rep
  where
  rep : (ℓ : Loop (Gskel two-chain) fzero)
      → _≡_ {A = π₁ᵈ (Gskel two-chain) fzero} ([ ℓ ] ⊞ᵈ [ ℓ ]) [ ℓ ]
      → [ ℓ ] ≡ [ nil fzero ]
  rep ℓ eq = cong [_] (len-zero-nil ℓ (n+n⇒0 (len ℓ) step3))
    where
    -- eq 展开为 [ℓ ++w ℓ] ≡ [ℓ]（rec-β 判定成立——b2 群 refl 实证同款）
    step1 : len (ℓ ++w ℓ) ≡ len ℓ
    step1 = cong lenq eq
    step2 : len (ℓ ++w ℓ) ≡ len ℓ + len ℓ
    step2 = len-++ ℓ ℓ
    step3 : len ℓ + len ℓ ≡ len ℓ
    step3 = sym step2 ∙ step1

--------------------------------------------------------------------------------
-- §4 主件：无 MonoidIso（幂等输运矛盾）
--------------------------------------------------------------------------------

loop-idem-A : _≡_ {A = π₁ᵈ (Gcmp two-chain) fzero}
  ([ selfloop-walk ] ⊞ᵈ [ selfloop-walk ]) [ selfloop-walk ]
loop-idem-A = loop-squash

no-π₁-iso : MonoidIso (π₁ᵈ (Gcmp two-chain) fzero) (π₁ᵈ (Gskel two-chain) fzero)
                      _⊞ᵈ_ [ nil fzero ] _⊞ᵈ_ [ nil fzero ]
  → ⊥
no-π₁-iso m = selfloop-quot-≠ (sym goal-eq)
  where
  open MI m
  x : π₁ᵈ (Gcmp two-chain) fzero
  x = [ selfloop-walk ]

  to-x-idem : _≡_ {A = π₁ᵈ (Gskel two-chain) fzero} (to x ⊞ᵈ to x) (to x)
  to-x-idem = sym (to-· x x) ∙ cong to loop-idem-A

  to-x-nil : to x ≡ [ nil fzero ]
  to-x-nil = gskel-idem (to x) to-x-idem

  goal-eq : x ≡ [ nil fzero ]
  goal-eq = sym (from∘to x) ∙ cong from to-x-nil ∙ from-e

--------------------------------------------------------------------------------
-- §5 分水岭定稿（台账陈述——组合定理形）
--------------------------------------------------------------------------------
-- π₁ᵈ(Gcmp two-chain) fzero = 2 元幂等幺半群（{[nil],[loop]}，[loop]⊞[loop]=[loop]——
--   v2-3 分类引理 + loop-squash）；
-- π₁ᵈ(Gskel two-chain) fzero ⊇ ⟨[w2]⟩ ≅ (ℕ,+)（w2 = 0→1→0 生成——v2-2 偶长分离 +
--   even2-len；无挠、仅 [nil] 幂等——gskel-idem）；
-- ⇒ 无 MonoidIso（no-π₁-iso——幂等元输运矛盾）。
-- 本体论边界：「对称图（可比闭包 Gcmp）vs 有向骨架（Gskel）」——逆元存在性分水岭
--   （b2 群 flip 判据）的组合定理形；backtrack（修正案 A）路线下 Gskel 升群、分水岭形态改变。
