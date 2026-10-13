{-# OPTIONS --cubical --rewriting --guardedness #-}

-- | _PPI3d —— SimplexExt 实例供给（_PPI3c 立界的实例面）
--
-- 数学背景：_PPI3c 将 record 级 ∂ 复合律的缺口显式前提化为 SimplexExt（record 外延性）。
-- 本模块供给**可构造实例**：k ≤ 1（单顶点/空单形）时 vchain 域空缺 ⇒ ext 零前提可证；
-- 并给出通用组装件 record-≡（J 动机形）与双 ≡ 桥 funExt≡，供 k ≥ 2 实例续建。
--
-- 核心原则：
--   1. 双 ≡ 桥（CRT 先例同款）：PropEq ≡（SimplexExt 世界）↔ Cubical Path（funExt 载体）；
--   2. 缺口显式前提化纪律延续：k ≥ 2 需 Strict 点态命题性（按 P 供证）——立界不硬证；
--   3. 复用优先：s₃/lt-irrel（_PPI3c）、Simplex/face（_PPI3）零重证。
--
-- 包含：toCE/frCE/funExt≡（桥）· J'/record-≡（组装件）· no-<ᵢ-1/isPropW1（vchain 空缺命题性）
--       · ext-k1（k=1 通用实例）· 实例层核对
module _PPI3d where

open import Data.Fin using (Fin; toℕ) renaming (zero to fzero; suc to fsuc)
open import Data.Nat using (ℕ; zero; suc; _≤_; z≤n; s≤s)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong; cong₂; subst)
open import Relation.Nullary using (¬_)
open import Cubical.Foundations.Prelude using (funExt) renaming (_≡_ to _≡ₚ_)
open import Cubical.Data.Equality as CE using (eqToPath; pathToEq)
open import Sovereign.Topology.AlexandroffFinite using (FinitePoset)
open import Sovereign.Synthesis.OrderComplex using (Strict; lin3)
open import Sovereign.Synthesis.McCordPi0 using (two-chain)
open import _PPI3 using (Simplex; face; _<ᵢ_; unskip; shift)
open import _PPI3c using (s₃; SimplexExt; face-face-comm-rec; ≤-irrel)

-- ────────────────────────────────────────────────────────────────────
-- ③ 基础件层：双 ≡ 桥 + J 组装件
-- ────────────────────────────────────────────────────────────────────

-- BUILTIN ≡ → Cubical.Data.Equality ≡（构造子直映）
toCE : {A : Set} {x y : A} → x ≡ y → x CE.≡ y
toCE refl = CE.refl

frCE : {A : Set} {x y : A} → x CE.≡ y → x ≡ y
frCE CE.refl = refl

-- 函数外延性（SimplexExt 世界）——经 Path funExt 往返（CRT 双 ≡ 桥同款）
funExt≡ : {A : Set} {B : A → Set} {f g : (x : A) → B x}
        → (∀ x → f x ≡ g x) → f ≡ g
funExt≡ h = frCE (pathToEq (funExt (λ x → eqToPath (toCE (h x)))))

-- J（BUILTIN ≡ 版——p 为变量故可 refl 分解）
J' : {A : Set} {x : A} (P : (y : A) → x ≡ y → Set)
   → P x refl → {y : A} (p : x ≡ y) → P y p
J' P pr refl = pr

-- vchain 族型（Simplex 第二域的依赖形）
W : ∀ {n k} (P : FinitePoset n) → (Fin k → Fin n) → Set
W {n} {k} P v = (i j : Fin k) → i <ᵢ j → Strict P (v i) (v j)

-- 组装件：record 级相等的 J 动机形（vert 路径 + vchain 运输对齐）
--   base 案 subst refl ≡ id（defeq）⇒ cong 直得；步案由 J' 搬运
record-≡ : ∀ {n k} {P : FinitePoset n} (s t : Simplex P k)
         (p : Simplex.vert s ≡ Simplex.vert t)
         (q : subst (W P) p (Simplex.vchain s) ≡ Simplex.vchain t)
         → s ≡ t
record-≡ {P = P} s t p q =
  J' (λ v r → (w : W P v) → subst (W P) r (Simplex.vchain s) ≡ w
            → record { vert = Simplex.vert s ; vchain = Simplex.vchain s }
            ≡ record { vert = v ; vchain = w })
     (λ w q' → cong (λ z → record { vert = Simplex.vert s ; vchain = z }) q')
     p (Simplex.vchain t) q

-- ────────────────────────────────────────────────────────────────────
-- ④ 主件层：k ≤ 1 的 vchain 空缺命题性 + 通用实例
-- ────────────────────────────────────────────────────────────────────

-- Fin 1 上无 <ᵢ 对（suc 0 ≤ 0 空）
no-<ᵢ-1 : (i j : Fin 1) → i <ᵢ j → ⊥
no-<ᵢ-1 fzero fzero ()
no-<ᵢ-1 (fsuc ()) _ _
no-<ᵢ-1 _ (fsuc ()) _

-- k = 1 时 vchain 族空缺 ⇒ 族上任意两点相等（命题性直得）
isPropW1 : ∀ {n} {P : FinitePoset n} {v : Fin 1 → Fin n}
         → (a b : W P v) → a ≡ b
isPropW1 {n} {P} {v} a b =
  funExt≡ (λ i → funExt≡ (λ j → funExt≡ (λ lt → ⊥-elim (no-<ᵢ-1 i j lt))))

-- 通用实例（k = 1 全 P 零前提）：SimplexExt 的结论在单顶点层可构造
ext-k1 : ∀ {n} {P : FinitePoset n} (s t : Simplex P 1)
       → (∀ x → Simplex.vert s x ≡ Simplex.vert t x)
       → s ≡ t
ext-k1 {n} {P} s t ve = record-≡ s t (funExt≡ ve)
  (isPropW1 {P = P} (subst (W P) (funExt≡ ve) (Simplex.vchain s)) (Simplex.vchain t))

-- ────────────────────────────────────────────────────────────────────
-- ⑤ 核对层（具体实例——two-chain/lin3 单顶点对）
-- ────────────────────────────────────────────────────────────────────

-- two-chain 的单顶点 Simplex（vchain 空缺形）
vertA : Simplex two-chain 1
vertA = record { vert = λ _ → fzero ; vchain = λ i j lt → ⊥-elim (no-<ᵢ-1 i j lt) }

vchainB : W two-chain (λ _ → fzero)
vchainB i j lt = ⊥-elim (no-<ᵢ-1 i j lt)

vertB : Simplex two-chain 1
vertB = record { vert = λ _ → fzero ; vchain = vchainB }

-- 实例核对：vert 层 refl 喂入 ⇒ record 级相等（vchain 句法相异仍证出）
check-ext-two-chain : vertA ≡ vertB
check-ext-two-chain = ext-k1 vertA vertB (λ x → refl)

-- lin3 单顶点实例（s₃ 的顶点层面）
vertL : Simplex lin3 1
vertL = record { vert = λ _ → fsuc fzero ; vchain = λ i j lt → ⊥-elim (no-<ᵢ-1 i j lt) }

vertL' : Simplex lin3 1
vertL' = record { vert = λ x → fsuc fzero ; vchain = λ i j lt → ⊥-elim (no-<ᵢ-1 i j lt) }

check-ext-lin3 : vertL ≡ vertL'
check-ext-lin3 = ext-k1 vertL vertL' (λ x → refl)

-- 桥件核对（funExt≡ 恒等形）
check-funext : (λ (x : Fin 1) → fzero {1}) ≡ (λ _ → fzero {1})
check-funext = funExt≡ (λ x → refl)

-- ────────────────────────────────────────────────────────────────────
-- ⑥ 扩展层：lin3 全 k 实例（Strict 点态命题性直供——⊑ = toℕ ≤ 故 ≤-irrel）
-- ────────────────────────────────────────────────────────────────────

isProp⊥' : (x y : ⊥) → x ≡ y
isProp⊥' () _

-- Strict lin3 点态命题性：⊑ 分量 ≤-irrel + ≢ 分量空函数命题性
isPropStrict-lin3 : ∀ {x y} (r s : Strict lin3 x y) → r ≡ s
isPropStrict-lin3 (a , b) (c , d) =
  cong₂ _,_ (≤-irrel a c) (funExt≡ (λ p → ⊥-elim (b p)))

isPropW-lin3 : ∀ {k} {v : Fin k → Fin 3} (a b : W lin3 v) → a ≡ b
isPropW-lin3 a b =
  funExt≡ (λ i → funExt≡ (λ j → funExt≡ (λ lt → isPropStrict-lin3 (a i j lt) (b i j lt))))

-- ★ 通用实例升级：lin3 上 SimplexExt **全 k 零前提成立**（ce 前提免费）
ext-lin3 : ∀ {k} (s t : Simplex lin3 k)
         → (∀ x → Simplex.vert s x ≡ Simplex.vert t x) → s ≡ t
ext-lin3 s t ve = record-≡ s t (funExt≡ ve)
  (isPropW-lin3 (subst (W lin3) (funExt≡ ve) (Simplex.vchain s)) (Simplex.vchain t))

-- SimplexExt 值形（face-face-comm-rec 接口形——ce 前提免费供）
ext-lin3-full : SimplexExt lin3
ext-lin3-full s t ve ce = ext-lin3 s t ve

-- ★ 主核对：s₃ 的 record 级 ∂ 复合律（face-face-comm-rec 终获实例）
ffr-rec-s3 : (A B : Fin 3) (lt : A <ᵢ B)
           → face lin3 (face lin3 s₃ B) (unskip B A lt)
           ≡ face lin3 (face lin3 s₃ A) (shift A B lt)
ffr-rec-s3 A B lt = face-face-comm-rec lin3 ext-lin3-full s₃ A B lt

-- 具体对核对（(0,1) 双删面 record 级相等——refl 通道不可及而 ext 通道供出）
check-ffr-rec-01 : face lin3 (face lin3 s₃ (fsuc fzero)) (unskip (fsuc fzero) fzero (s≤s z≤n))
                ≡ face lin3 (face lin3 s₃ fzero) (shift fzero (fsuc fzero) (s≤s z≤n))
check-ffr-rec-01 = ffr-rec-s3 fzero (fsuc fzero) (s≤s z≤n)
