{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Algebra.LinearAlgebra.GF3Dim
-- 有限 GF(3) 向量空间的**维数**基础（T4 的 b_n 组装配件，2026-10-20）
--
-- 设计原则
--   本库**不假设函数外延**（funext）⇒ 所有子空间陈述用**点态**形式：
--     组合 `Comb v c x = Σ_i c i ⊗ v i x`（逐点求和）
--     张成 `Span d v p  = Σ c, ∀ x, p x ≡ Comb v c x`
--   于是「`V` 由 `d` 个向量张成」是**可判定结构**，不需要商空间。
--
-- 本模块提供（§1–§4）
--   §1 组合 `Comb`
--   §2 张成 `Span`
--   §3 基本性质（零组合、单点组合）
--   §4 指示函数（`CoeffN n` 的标准基向量）与「按下标取值」的判据
--
-- 尚未提供（下一步）
--   秩-零化度 ⇒ `dim(ker F ∩ V_nA)` 的计数 —— 这是 b_n 组装的最后一步。
--
-- 0 postulate / 0 hole

module Sovereign.Algebra.LinearAlgebra.GF3Dim where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.Product using (_×_; _,_; Σ; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using
  (_≡_; _≢_; refl; cong; cong₂; sym; trans)

open import Sovereign.Base.Trit using
  (Trit; T₀; T₁; T₂; _⊕_; _⊗_; negate; ⊗-zeroˡ; ⊗-identityʳ; ⊕-identityˡ)
open import Sovereign.Algebra.LinearAlgebra.GF3LaplacianN using (Torus; sumFin; sumFin-cong; sumFin-zero)

CoeffN : ℕ → Set
CoeffN n = Torus n → Trit

--------------------------------------------------------------------------------
-- §1. 组合（逐点求和形式，避开 funext）
--------------------------------------------------------------------------------

Comb : ∀ {n} {d : ℕ} → (Fin d → CoeffN n) → (Fin d → Trit) → CoeffN n
Comb v c x = sumFin (λ i → c i ⊗ v i x)

--------------------------------------------------------------------------------
-- §2. 张成
--------------------------------------------------------------------------------

Span : ∀ {n} → (d : ℕ) → (Fin d → CoeffN n) → CoeffN n → Set
Span d v p = Σ (Fin d → Trit) (λ c → ∀ x → p x ≡ Comb v c x)

--------------------------------------------------------------------------------
-- §3. 基本性质
--------------------------------------------------------------------------------

-- 零组合给出零函数
comb-zero : ∀ {n d} (v : Fin d → CoeffN n) (x : Torus n) →
  Comb v (λ _ → T₀) x ≡ T₀
comb-zero {d = d} v x =
  trans (sumFin-cong {n = d} (λ i → ⊗-zeroˡ (v i x))) (sumFin-zero {d})

-- 零函数在任意张成里（取零组合）
zero-in-span : ∀ {n d} (v : Fin d → CoeffN n) →
  Span d v (λ _ → T₀)
zero-in-span v = (λ _ → T₀) , (λ x → sym (comb-zero v x))

-- 注：单个生成元 `v i` 落在张成里需要「δ 组合」，即 `c j = (i ≡ j ? T₁ : T₀)`，
--     依赖 `Fin d` 的可判定相等（下一步 §4 处理）。

--------------------------------------------------------------------------------
-- §4. 指示函数（标准基向量）与「取第 i 个系数」
--------------------------------------------------------------------------------

open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (yes; no; Dec)
open import Data.Fin.Properties using (_≟_; fsuc-injective)

-- δ 组合：`δc i j = T₁` 当 `i ≡ j`，否则 `T₀`
δc : ∀ {d} → Fin d → (Fin d → Trit)
δc i j with i ≟ j
... | yes _ = T₁
... | no  _ = T₀

-- 自身取 T₁
δc-self : ∀ {d} (i : Fin d) → δc i i ≡ T₁
δc-self i with i ≟ i
... | yes _ = refl
... | no ¬p = ⊥-elim (¬p refl)

-- 不同取 T₀
δc-neq : ∀ {d} (i j : Fin d) → i ≢ j → δc i j ≡ T₀
δc-neq i j ne with i ≟ j
... | yes p = ⊥-elim (ne p)
... | no  _ = refl

-- 零组合的逐点形式（`sumFin` 的零崩溃）
sumFin-zero' : ∀ {d} → sumFin {d} (λ _ → T₀) ≡ T₀
sumFin-zero' {d} = sumFin-zero {d}

--------------------------------------------------------------------------------
-- §5. δ 的三条分支引理
--------------------------------------------------------------------------------

δc-fzero-suc : ∀ {m} (j : Fin m) → δc {suc m} fzero (fsuc j) ≡ T₀
δc-fzero-suc j = refl

δc-suc-fzero : ∀ {m} (i : Fin m) → δc {suc m} (fsuc i) fzero ≡ T₀
δc-suc-fzero i = refl

-- ★ 关键：fsuc 在两侧对齐（stdlib 的 Fin 判定相等按构造子递归）
δc-fsuc : ∀ {m} (i j : Fin m) → δc {suc m} (fsuc i) (fsuc j) ≡ δc i j
δc-fsuc i j with i ≟ j
... | yes _ = refl
... | no  _ = refl

--------------------------------------------------------------------------------
-- §6. ★ 核心引理：δ 组合在 i 处取回 f i
--------------------------------------------------------------------------------

open import Sovereign.Base.Trit using (⊗-identityˡ; ⊗-identityʳ; ⊗-zeroˡ; ⊗-zeroʳ; ⊕-identityʳ; negate; negate²)

sumFin-δ : ∀ {d} (f : Fin d → Trit) (i : Fin d) →
  sumFin (λ j → δc i j ⊗ f j) ≡ f i
sumFin-δ {suc m} f fzero =
  trans (cong₂ _⊕_ (trans (cong (λ z → z ⊗ f fzero) (δc-self {suc m} fzero)) (⊗-identityˡ (f fzero)))
                   tail-zero)
        (⊕-identityʳ (f fzero))
  where
    tail-zero : sumFin {m} (λ j → δc {suc m} fzero (fsuc j) ⊗ f (fsuc j)) ≡ T₀
    tail-zero =
      trans (sumFin-cong {n = m} (λ j → cong (λ z → z ⊗ f (fsuc j)) (δc-fzero-suc j)))
            (sumFin-zero {m})
sumFin-δ {suc m} f (fsuc i) =
  trans (cong₂ _⊕_
          (trans (cong (λ z → z ⊗ f fzero) (δc-suc-fzero i))
                 (⊗-zeroˡ (f fzero)))
          (trans (sumFin-cong {n = m} (λ j → cong (λ z → z ⊗ f (fsuc j)) (δc-fsuc i j)))
                 (sumFin-δ {m} (λ j → f (fsuc j)) i)))
        (⊕-identityˡ (f (fsuc i)))

--------------------------------------------------------------------------------
-- §7. 每个生成元落在自己的张成里（用 §6 的 δ 对偶）
--------------------------------------------------------------------------------

gen-in-span : ∀ {n d} (v : Fin d → CoeffN n) (i : Fin d) → Span d v (v i)
gen-in-span v i = δc i , (λ x → sym (sumFin-δ {d = _} (λ j → v j x) i))

--------------------------------------------------------------------------------
-- §8. ★ 线性无关：组合的「系数」可由取值唯一恢复
--
-- 若 `v` 在每个下标处都有「分离点」（其他生成元在该点为零），则
-- `Comb v c ≡ Comb v c'` 推出 `c i ≡ c' i`。
--------------------------------------------------------------------------------

-- 分离性：(i 处有 x 使 v i x ≠ T₀，而 j ≠ i 时 v j x ≡ T₀) 的逐点形式
Separated : ∀ {n d} (v : Fin d → CoeffN n) → Set
Separated {n} {d} v =
  ∀ (i : Fin d) → Σ (Torus n) (λ x → (v i x ≢ T₀)
    × (∀ (j : Fin d) → j ≢ i → v j x ≡ T₀))

--------------------------------------------------------------------------------
-- §9. 分离点上的组合只留一项（复用 GF3Barrier 的 `sumFin-single`）
--------------------------------------------------------------------------------

open import Sovereign.Algebra.LinearAlgebra.GF3Barrier using (sumFin-single; trit-zero; T₁≢T₀; T₂≢T₀)
comb-sep : ∀ {n d} (v : Fin d → CoeffN n) (sep : Separated v)
  (c : Fin d → Trit) (i : Fin d) →
  Comb v c (proj₁ (sep i)) ≡ c i ⊗ v i (proj₁ (sep i))
comb-sep v sep c i =
  sumFin-single i (λ j → c j ⊗ v j (proj₁ (sep i)))
                 (c i ⊗ v i (proj₁ (sep i))) refl
                 (λ j i≠j → trans (cong (λ z → c j ⊗ z) (proj₂ (proj₂ (sep i)) j (λ e → i≠j (sym e))))
                                  (⊗-zeroʳ (c j)))

--------------------------------------------------------------------------------
-- §10. Trit 消去：非零因子可消
--------------------------------------------------------------------------------

-- T₂ 乘 = 取负（char 3）
T₂-mul-neg : ∀ a → T₂ ⊗ a ≡ negate a
T₂-mul-neg T₀ = refl
T₂-mul-neg T₁ = refl
T₂-mul-neg T₂ = refl

⊗-cancel : ∀ (t : Trit) → t ≢ T₀ → (a b : Trit) → t ⊗ a ≡ t ⊗ b → a ≡ b
⊗-cancel T₀ ne _ _ _ = ⊥-elim (ne refl)
⊗-cancel T₁ _ a b eq = trans (sym (⊗-identityˡ a)) (trans eq (⊗-identityˡ b))
⊗-cancel T₂ _ a b eq =
  trans (sym (negate² a))
        (trans (cong negate eq') (negate² b))
  where
    eq' : negate a ≡ negate b
    eq' = trans (sym (T₂-mul-neg a)) (trans eq (T₂-mul-neg b))
