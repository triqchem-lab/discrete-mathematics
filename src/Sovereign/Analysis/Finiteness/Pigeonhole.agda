{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Analysis.Finiteness.Pigeonhole
-- 任务书第一层·1.2：鸽巢原理双向等价（Dirichlet 1834）
--
-- 数学背景：n+1 物入 n 盒必有碰撞；逆否 = 单射基数下界。
--   正向 m < n ⟹ 无单射 Fin n → Fin m：复用 stdlib Data.Fin.Properties.pigeonhole
--   （构造性，对 n 归纳 + any?/punchOut）。
--   反向 m ≥ n ⟹ 存在单射：fromℕ< 沿可判定序嵌入，不引入排中律。
--
-- 与库内件的关系：FiniteDynamics.pigeonhole-fin 是 stdlib pigeonhole 的 suc n→n
--   特形包装（供 injSurj 用）；本层用泛形（任意 m<n）。PigeonholeStandard 是
--   GF 侧 Inj/Surj 词汇包装，本层不重复引入。
--
-- ⚠ 反证法纪律：反证只在 ¬ 前提内消去；本 iff 是**鸽巢双向**，不是完备性声明，
--   不外推任何「完备」结论（M8 判据 5：检查结论过三问）。
--
-- 0 postulate / 0 hole。
module Sovereign.Analysis.Finiteness.Pigeonhole where

open import Data.Nat using (ℕ; _<_; _≤_)
open import Data.Nat.Properties using (≤-trans; _<?_; ≰⇒>; ≤-pred; <-irrefl)
open import Data.Fin using (Fin; toℕ; fromℕ<)
open import Data.Fin.Properties using (pigeonhole; toℕ<n; toℕ-injective; toℕ-fromℕ<)
open import Data.Product using (_×_; _,_; Σ)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; cong; sym; trans)
open import Function.Definitions using (Injective)
open import Function.Bundles using (_⇔_; mk⇔)

-- 正向：m < n ⟹ 不存在单射 Fin n → Fin m
pigeonhole→ : ∀ {m n : ℕ} → m < n → (f : Fin n → Fin m) → ¬ (Injective _≡_ _≡_ f)
pigeonhole→ {m} {n} m<n f f-inj = go (pigeonhole m<n f)
  where
    go : Σ (Fin n) (λ i → Σ (Fin n) (λ j → toℕ i < toℕ j × f i ≡ f j)) → ⊥
    go (i , j , i<j , fi≡fj) = <-irrefl (cong toℕ (f-inj fi≡fj)) i<j

-- 反向：m ≥ n ⟹ 存在单射 Fin n → Fin m
pigeonhole← : ∀ {m n : ℕ} → ¬ (m < n) → Σ (Fin n → Fin m) (λ f → Injective _≡_ _≡_ f)
pigeonhole← {m} {n} ¬m<n = (λ i → fromℕ< {m = toℕ i} {n = m} (toℕ<m i)) , inj
  where
    -- ¬(m < n) ⟹ n ≤ m：≰⇒> 走可判定序（不引三歧比较；修 :94 实证版）
    n≤m : n ≤ m
    n≤m = ≤-pred (≰⇒> ¬m<n)
    toℕ<m : (i : Fin n) → toℕ i < m
    toℕ<m i = ≤-trans (toℕ<n i) n≤m
    -- roundtrip 用 toℕ-fromℕ<（界来自 p : toℕ i < m，不是 Fin 界；修 :99 实证版）
    inj : Injective _≡_ _≡_ (λ i → fromℕ< {m = toℕ i} {n = m} (toℕ<m i))
    inj {i} {j} eq = toℕ-injective (trans (sym (toℕ-fromℕ< (toℕ<m i)))
                                  (trans (cong toℕ eq) (toℕ-fromℕ< (toℕ<m j))))

-- 双向等价
pigeonhole-iff : ∀ {m n : ℕ} → (m < n) ⇔ (¬ (Σ (Fin n → Fin m) (λ f → Injective _≡_ _≡_ f)))
pigeonhole-iff {m} {n} = mk⇔ fwd bwd
  where
    fwd : m < n → ¬ (Σ (Fin n → Fin m) (λ f → Injective _≡_ _≡_ f))
    fwd m<n (f , f-inj) = pigeonhole→ m<n f f-inj
    -- 反向走 ℕ 序可判定性（m <? n），不引入排中律；hole 修法实证版
    bwd : ¬ (Σ (Fin n → Fin m) (λ f → Injective _≡_ _≡_ f)) → m < n
    bwd ¬∃inj with m <? n
    ... | yes m<n = m<n
    ... | no ¬m<n = ⊥-elim (¬∃inj (pigeonhole← ¬m<n))
