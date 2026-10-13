{-# OPTIONS --rewriting --guardedness #-}

-- | _PPI3c —— face-face-comm record 级提升（a3 立界件转工时件）
--
-- 数学背景：∂ 复合律（半单纯关系）的 record 级形——vert 逐点形（_PPI3 ⑩.2）
-- 提升为 Simplex 值相等。世界缺口定谳：_PPI3 属 PropEq 世界（无 funExt——
-- 任务书假设的「Cubical funExt 件」与模块世界不符，双≡世界陷阱）；
-- 但**内容侧零缺口**：vert 点对点（既有）+ vchain 点对点（本件 ffr-vc-out，
-- subst₂ 对齐形——三元组代数 + <ᵢ 命题性，无需 Strict 证明无关！）
-- ⇒ record 级律的**最小缺口 = 外延性单缺口**（显式前提化 SimplexExt）。
--
-- 核心原则：
--   1. 复用优先：skip-comm2/face-face-comm/_<ᵢ_/skip 系（_PPI3）零重证；
--   2. 缺口显式前提化（关系入定义纪律的假设可见形态）——SimplexExt 单前提，
--      注记其 ≈ fe+vchain 提升的打包；不 postulate、不硬证；
--   3. 机件层全无前提：≤-irrel/lt-irrel（<ᵢ 命题性）+ subst 系搬运代数。
--
-- 包含：≤-irrel/lt-irrel · subst₂/subst₂-cong2（搬运代数）· vc-move（vchain 顶点搬运）
--       · ffr-vc-out（vchain 点对点，subst₂ 形）· SimplexExt（单前提）
--       · face-face-comm-rec（record 级 ∂ 复合律——ext 应用）· 核对层
module _PPI3c where

-- ────────────────────────────────────────────────────────────────────
-- ② 导入区
-- ────────────────────────────────────────────────────────────────────
open import Data.Nat using (ℕ; zero; suc; _≤_; z≤n; s≤s)
open import Data.Fin using (Fin; toℕ) renaming (zero to fzero; suc to fsuc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (_×_; Σ; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import Relation.Nullary using (¬_)
open import Sovereign.Topology.AlexandroffFinite using (FinitePoset)
open import Sovereign.Synthesis.OrderComplex using (Strict; lin3; lin3-down-instance)
open import _PPI3 using (Simplex; face; face-face-comm; _<ᵢ_; skip; skip-<; unskip; shift; skip-comm2)

-- ────────────────────────────────────────────────────────────────────
-- ③ 基础件层：<ᵢ 命题性 + 搬运代数（全无前提）
-- ────────────────────────────────────────────────────────────────────

-- ≤ 证明无关（<ᵢ = suc (toℕ·) ≤ toℕ· 故同一证法——零前提）
≤-irrel : ∀ {m n} (p q : m ≤ n) → p ≡ q
≤-irrel z≤n z≤n = refl
≤-irrel (s≤s p) (s≤s q) = cong s≤s (≤-irrel p q)

lt-irrel : ∀ {k} {i j : Fin k} (p q : i <ᵢ j) → p ≡ q
lt-irrel = ≤-irrel




-- 双函子搬运拉回：subst₂ C (cong f p) (cong g q) ≡ subst₂ (λ i j → C (f i) (g j)) p q
subst₂ : ∀ {A B : Set} (C : A → B → Set) {a₁ a₂ : A} {b₁ b₂ : B}
  → a₁ ≡ a₂ → b₁ ≡ b₂ → C a₁ b₁ → C a₂ b₂
subst₂ C refl refl x = x

subst₂-cong2 : ∀ {A A' B B' : Set} {C : A' → B' → Set}
  {f : A → A'} {g : B → B'} {a₁ a₂ : A} {b₁ b₂ : B}
  (p : a₁ ≡ a₂) (q : b₁ ≡ b₂) (x : C (f a₁) (g b₁))
  → subst₂ C (cong f p) (cong g q) x
  ≡ subst₂ (λ i j → C (f i) (g j)) p q x
subst₂-cong2 refl refl x = refl



-- ────────────────────────────────────────────────────────────────────
-- ④ 主件层：vchain 点对点（内容侧零缺口）+ record 级 ∂ 复合律
-- ────────────────────────────────────────────────────────────────────

-- vchain 顶点搬运（免路径代数的关键形——J 形双 refl + lt-irrel 收口）：
--   索引对 (i,j) 沿 (p,q) 搬运时 vchain 输出相等（唯差在 <ᵢ 证明——命题性消解）
vc-move : ∀ {n} (P : FinitePoset n) {k} (s : Simplex P k)
  {i i' j j' : Fin k} (p : i ≡ i') (q : j ≡ j')
  (l : i <ᵢ j) (l' : i' <ᵢ j')
  → subst₂ (λ a b → Strict P (Simplex.vert s a) (Simplex.vert s b)) p q
      (Simplex.vchain s i j l)
  ≡ Simplex.vchain s i' j' l'
vc-move P s refl refl l l' = cong (Simplex.vchain s _ _) (lt-irrel l l')

-- ∂ 复合律 vchain 点对点（subst₂ 对齐形——内容侧全无前提）：
--   双删复合面的 vchain 场沿 skip-comm2 对齐后逐点相等
ffr-vc-out : ∀ {n} (P : FinitePoset n) {k} (s : Simplex P (suc (suc k)))
  (A B : Fin (suc (suc k))) (lt : A <ᵢ B)
  (j₁ j₂ : Fin k) (lt' : j₁ <ᵢ j₂)
  → subst₂ (λ i j → Strict P i j)
      (cong (Simplex.vert s) (skip-comm2 A B lt j₁))
      (cong (Simplex.vert s) (skip-comm2 A B lt j₂))
      (Simplex.vchain (face P (face P s B) (unskip B A lt)) j₁ j₂ lt')
  ≡ Simplex.vchain (face P (face P s A) (shift A B lt)) j₁ j₂ lt'
ffr-vc-out P s A B lt j₁ j₂ lt' =
  trans (subst₂-cong2 (skip-comm2 A B lt j₁) (skip-comm2 A B lt j₂)
          (Simplex.vchain (face P (face P s B) (unskip B A lt)) j₁ j₂ lt'))
        (vc-move P s (skip-comm2 A B lt j₁) (skip-comm2 A B lt j₂)
          (skip-< B (skip-< (unskip B A lt) lt'))
          (skip-< A (skip-< (shift A B lt) lt')))

-- ────────────────────────────────────────────────────────────────────
-- ⑤ 组合层：SimplexExt 单前提 + record 级 ∂ 复合律
-- ────────────────────────────────────────────────────────────────────

-- Simplex 记录层外延性（唯一缺口的显式前提化——世界缺口定谳见模块头）：
--   语义 = vert 层 funExt + vchain 层点对点提升的打包；本世界不可导故前提化，
--   不 postulate、不硬证（关系入定义纪律的假设可见形态）
SimplexExt : ∀ {n} (P : FinitePoset n) → Set
SimplexExt P = {k : ℕ} (s t : Simplex P k)
  (ve : ∀ x → Simplex.vert s x ≡ Simplex.vert t x)
  (ce : ∀ (j₁ j₂ : Fin k) (lt : j₁ <ᵢ j₂) →
    subst₂ (λ i j → Strict P i j) (ve j₁) (ve j₂) (Simplex.vchain s j₁ j₂ lt)
    ≡ Simplex.vchain t j₁ j₂ lt)
  → s ≡ t

-- record 级 ∂ 复合律（半单纯关系 record 形——ext 应用 + 内容侧两件合成）
face-face-comm-rec : ∀ {n} (P : FinitePoset n) (ext : SimplexExt P)
  {k} (s : Simplex P (suc (suc k)))
  (A B : Fin (suc (suc k))) (lt : A <ᵢ B)
  → face P (face P s B) (unskip B A lt) ≡ face P (face P s A) (shift A B lt)
face-face-comm-rec P ext s A B lt =
  ext (face P (face P s B) (unskip B A lt))
      (face P (face P s A) (shift A B lt))
      (face-face-comm P s A B lt)
      (ffr-vc-out P s A B lt)

-- ────────────────────────────────────────────────────────────────────
-- ⑥ 核对层（lin3 三链小例——内容侧 refl 级）
-- ────────────────────────────────────────────────────────────────────

-- lin3 的规范 2-单形（顶点 (0,1,2)——链性由 lin3-down-instance 三边供证）
s₃ : Simplex lin3 3
s₃ = record { vert = tri-v3 ; vchain = chain3 }
  where
  tri-v3 : Fin 3 → Fin 3
  tri-v3 fzero = fzero
  tri-v3 (fsuc fzero) = fsuc fzero
  tri-v3 (fsuc (fsuc fzero)) = fsuc (fsuc fzero)
  no-s≤0 : ∀ {m} → ¬ (suc m ≤ zero)
  no-s≤0 ()
  ≤-peel : ∀ {m n} → suc m ≤ suc n → m ≤ n
  ≤-peel (s≤s p) = p
  chain3 : (i j : Fin 3) → i <ᵢ j → Strict lin3 (tri-v3 i) (tri-v3 j)
  chain3 fzero fzero lt = ⊥-elim (no-s≤0 lt)
  chain3 fzero (fsuc fzero) lt = proj₁ lin3-down-instance
  chain3 fzero (fsuc (fsuc fzero)) lt = proj₁ (proj₂ lin3-down-instance)
  chain3 (fsuc fzero) fzero lt = ⊥-elim (no-s≤0 lt)
  chain3 (fsuc fzero) (fsuc fzero) lt = ⊥-elim (no-s≤0 (≤-peel lt))
  chain3 (fsuc fzero) (fsuc (fsuc fzero)) lt = proj₂ (proj₂ lin3-down-instance)
  chain3 (fsuc (fsuc fzero)) fzero lt = ⊥-elim (no-s≤0 lt)
  chain3 (fsuc (fsuc fzero)) (fsuc fzero) lt = ⊥-elim (no-s≤0 (≤-peel lt))
  chain3 (fsuc (fsuc fzero)) (fsuc (fsuc fzero)) lt = ⊥-elim (no-s≤0 (≤-peel (≤-peel lt)))

-- 核对 1：<ᵢ 命题性 refl 级（≤-irrel 定义相等）
check-irrel : lt-irrel {3} {fzero} {fsuc fzero} (s≤s z≤n) (s≤s z≤n) ≡ refl
check-irrel = refl

-- 核对 2：lin3 双删复合面 vert 级收口（A=0,B=1——两侧均退到顶点 2）
check-ffr-v :
  Simplex.vert (face lin3 (face lin3 s₃ (fsuc fzero))
                 (unskip (fsuc fzero) fzero (s≤s z≤n))) fzero
  ≡ fsuc (fsuc fzero)
check-ffr-v = refl

-- 核对 3：单向件（record 相等 ⟹ vert 逐点——无前提）
face-face-comm-rec→vert : ∀ {n} (P : FinitePoset n) {k}
  (s : Simplex P (suc (suc k))) (A B : Fin (suc (suc k))) (lt : A <ᵢ B)
  (e : face P (face P s B) (unskip B A lt) ≡ face P (face P s A) (shift A B lt))
  (x : Fin k)
  → Simplex.vert (face P (face P s B) (unskip B A lt)) x
  ≡ Simplex.vert (face P (face P s A) (shift A B lt)) x
face-face-comm-rec→vert P s A B lt e x = cong (λ s' → Simplex.vert s' x) e
