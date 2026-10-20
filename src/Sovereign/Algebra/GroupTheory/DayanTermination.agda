{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Algebra.GroupTheory.DayanTermination
-- 大衍求一术 S-D3 终止性定理——right-top 递减 + 良基归纳
--
-- 数学内容：
--   终止性由 right-top 的严格递减保证：
--     right-top (dayan-step s) = right-bottom s % right-top s < right-top s
--   这是 stdlib 的 m%n < n（当 n > 0）。
--   ℕ 的良基归纳给出算法终止。
--
-- 0 postulate / 0 hole。
module Sovereign.Algebra.GroupTheory.DayanTermination where

open import Data.Nat using (ℕ; zero; suc; _*_; _+_; _∸_; _/_; _%_; _<_; _≤_; _>_; s≤s; z≤n; _≟_; NonZero)
open import Data.Nat.DivMod using (m%n<n)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; subst; cong; cong₂; module ≡-Reasoning)
open import Data.Product using (Σ; ∃; _,_; proj₁; proj₂)
open import Relation.Nullary using (¬_; yes; no)
open import Data.Empty using (⊥; ⊥-elim)

--------------------------------------------------------------------------------
-- §1. DayanState 引入
--------------------------------------------------------------------------------

open import Sovereign.Algebra.GroupTheory.DayanState
  using (DayanState; dayan; dayan-init; dayan-step; dayan-terminates;
         left-top; left-bottom; right-top; right-bottom)

--------------------------------------------------------------------------------
-- §2. 终止性度量——right-top
--------------------------------------------------------------------------------

termination-measure : DayanState → ℕ
termination-measure = right-top

--------------------------------------------------------------------------------
-- §3. 步后 right-top 递减
--
--   dayan-step 中 new_rt = right-bottom s % right-top s
--   由 stdlib 的 m%n<n：当 right-top s > 0 时，new_rt < right-top s
--------------------------------------------------------------------------------

-- 修正：只在未终止（right-top > 0）时证明递减
step-decreases : (s : DayanState) → right-top s > 0 →
                 termination-measure (dayan-step s) < termination-measure s
step-decreases s rt>0 with right-top s | rt>0
... | zero | ()
... | suc rt-1 | _ = m%n<n (right-bottom s) (suc rt-1)
-- 当 right-top = suc rt-1 > 0 时，dayan-step 返回 new_rt = right-bottom s % suc rt-1
-- 由 m%n<n：< suc rt-1

--------------------------------------------------------------------------------
-- §4. 终止性——ℕ 良基归纳
--
--   right-top 严格递减 + ℕ 良基 ⟹ 算法在有限步内终止。
--   终止条件：right-top = 1（奇一而止）。
--
--   完整终止性证明需要良基递归（Acc）或 fuel 参数化——roadmap。
--------------------------------------------------------------------------------

-- fuel 参数化的迭代（dayan-step 已改用模式匹配，不需要 NonZero 约束）
dayan-iterate-fuel : ℕ → DayanState → DayanState
dayan-iterate-fuel zero s = s
dayan-iterate-fuel (suc n) s = dayan-iterate-fuel n (dayan-step s)

-- 终止性陈述（fuel 版）
-- ∃ A P = Σ A P，其中 P : A → Set
termination-statement : Set
termination-statement =
  ∀ (奇 定 : ℕ) →
  Σ ℕ (λ fuel → dayan-terminates (dayan-iterate-fuel fuel (dayan-init 奇 定)))

--------------------------------------------------------------------------------
-- §5. S-D3 完成度
--
--   ✅ step-decreases：right-top 严格递减（m%n<n）
--   ⚠ termination-statement：需要良基递归或 fuel（roadmap）
--
--   step-decreases 已闭合——这正是 L2 step-invariant 的 NonZero 约束来源。
--   当 right-top s > 0 时，dayan-step 可执行，且 right-top 递减。
--   ℕ 的良基性保证算法终止。
--------------------------------------------------------------------------------

--------------------------------------------------------------------------------
-- §6. 终止性的可证形式（2026-10-20）
--
-- 原 `termination-statement`（无互素前提）**是假命题** ✗：
--   迭代的 `right-top` 是欧几里得链 `奇, 定%奇, 奇%(定%奇), …`，极限是 `gcd 奇 定`。
--   当 `gcd = 2`（如 奇=2,定=4）时链停在 2，永不 ≡ 1。
--
-- 本节证明**不需要互素前提**的那一半：`right-top` 必在有限步内归零（算法停机）。
-- 工具：`step-decreases`（已证严格递减）+ `<-rec`（ℕ 强归纳，wf 已内建）。
--------------------------------------------------------------------------------

open import Data.Nat.Induction using (<-rec)

dayan-reaches-zero :
  ∀ (s : DayanState) → Σ ℕ (λ fuel → right-top (dayan-iterate-fuel fuel s) ≡ 0)
dayan-reaches-zero st = <-rec P ih (right-top st) st refl
  where
    P : ℕ → Set
    P rt = ∀ (st : DayanState) → right-top st ≡ rt →
             Σ ℕ (λ fuel → right-top (dayan-iterate-fuel fuel st) ≡ 0)

    ih : ∀ rt → (∀ {rt′} → rt′ < rt → P rt′) → P rt
    ih zero    _   st eq = zero , eq
    ih (suc m) rec st eq =
      let pos : right-top st > 0
          pos = subst (λ z → z > 0) (sym eq) (s≤s z≤n)
          dec : right-top (dayan-step st) < suc m
          dec = subst (λ z → right-top (dayan-step st) < z) eq (step-decreases st pos)
          ih′ : Σ ℕ (λ fuel → right-top (dayan-iterate-fuel fuel (dayan-step st)) ≡ 0)
          ih′ = rec dec (dayan-step st) refl
      in suc (proj₁ ih′) , proj₂ ih′

-- 推论：任何初始状态都停机（归零），无需互素前提
dayan-halts :
  ∀ (奇 定 : ℕ) → Σ ℕ (λ fuel → right-top (dayan-iterate-fuel fuel (dayan-init 奇 定)) ≡ 0)
dayan-halts 奇 定 = dayan-reaches-zero (dayan-init 奇 定)

--------------------------------------------------------------------------------
-- §7. 互素时的成功终止（T1 后半，2026-10-20）
--------------------------------------------------------------------------------

open import Data.Nat.GCD using (gcd; gcd-greatest; gcd[m,n]∣m; gcd[m,n]∣n)
open import Data.Nat.Divisibility using (_∣_; ∣-antisym; ∣1⇒≡1; ∣n∣m%n⇒∣m; %-presˡ-∣)

-- 欧几里得步：`gcd (b % a) a ≡ gcd a b`
-- （stdlib 把这个等式藏在 `gcd′` 的递归内部，未导出；这里用 `∣-antisym` + `gcd-greatest` 自证）
gcd-step : ∀ a b → .{{_ : NonZero a}} → gcd (b % a) a ≡ gcd a b
gcd-step a b = ∣-antisym
    (gcd-greatest fwd1 fwd2)
    (gcd-greatest back1 back2)
  where
    fwd1 : gcd (b % a) a ∣ a
    fwd1 = gcd[m,n]∣n (b % a) a

    fwd2 : gcd (b % a) a ∣ b
    fwd2 = ∣n∣m%n⇒∣m (gcd[m,n]∣n (b % a) a) (gcd[m,n]∣m (b % a) a)

    back1 : gcd a b ∣ b % a
    back1 = %-presˡ-∣ (gcd[m,n]∣n a b) (gcd[m,n]∣m a b)

    back2 : gcd a b ∣ a
    back2 = gcd[m,n]∣m a b

--------------------------------------------------------------------------------
-- §8. 停步处的值（T1 后半的第二块）
--
-- 若 `rb % rt ≡ 0` 且 `gcd rt rb ≡ 1`，则 `rt ≡ 1`：
--   ① `rb ≡ rb % rt + (rb / rt) * rt` ⇒ `rt ∣ rb`
--   ② `rt ∣ rt` 且 `rt ∣ rb` ⇒ `rt ∣ gcd rt rb`     （gcd-greatest）
--   ③ 由 `gcd rt rb ≡ 1` ⇒ `rt ∣ 1` ⇒ `rt ≡ 1`      （∣1⇒≡1）
--------------------------------------------------------------------------------

open import Data.Nat.GCD using (gcd-comm)
open import Data.Nat.Divisibility using (∣-refl; m∣m*n; ∣-trans)
open import Data.Nat.DivMod using (m≡m%n+[m/n]*n)
open import Data.Nat.Properties using (<-irrefl; +-identityˡ; *-comm)
open import Relation.Binary.PropositionalEquality using (module ≡-Reasoning)

hits-base : ∀ rt rb → .{{_ : NonZero rt}} → gcd rt rb ≡ 1 → rb % rt ≡ 0 → rt ≡ 1
hits-base rt rb g1 r0 = ∣1⇒≡1 (subst (λ z → rt ∣ z) g1 (gcd-greatest ∣-refl rt∣rb))
  where
    open ≡-Reasoning

    -- `rt * (rb / rt) ≡ rb`
    key : rt * (rb / rt) ≡ rb
    key = begin
        rt * (rb / rt)
      ≡⟨ *-comm rt (rb / rt) ⟩
        (rb / rt) * rt
      ≡⟨ sym (+-identityˡ ((rb / rt) * rt)) ⟩
        0 + (rb / rt) * rt
      ≡⟨ cong (λ z → z + (rb / rt) * rt) (sym r0) ⟩
        rb % rt + (rb / rt) * rt
      ≡⟨ sym (m≡m%n+[m/n]*n rb rt) ⟩
        rb
      ∎

    rt∣rb : rt ∣ rb
    rt∣rb = subst (λ z → rt ∣ z) key (m∣m*n {rt} (rb / rt))

--------------------------------------------------------------------------------
-- §9. `dayan-step` 的显式展开 + gcd 不变量（2026-10-20）
--
-- `dayan-step` 的定义体用了 `let`（`rt`/`q`/`r`/`diff`）⇒ 对构造子输入**也不归约** ✗。
-- 因此必须显式给出展开引理（`let` 在 rhs，`refl` 可证）。
--------------------------------------------------------------------------------

open import Data.Nat.Properties using (<-cmp)
open import Relation.Binary.Definitions using (tri<; tri≈; tri>)

dayan-step-unfold :
  ∀ lt lb rt rb →
    dayan-step (dayan lt lb (suc rt) rb)
      ≡ dayan (((rb / suc rt) * lt) ∸ lb) lt (rb % suc rt) (suc rt)
dayan-step-unfold lt lb rt rb = refl

-- 一步之后 gcd 不变（`right-top > 0` 时）
gcd-preserved :
  ∀ (s : DayanState) → right-top s > 0 →
    gcd (right-top (dayan-step s)) (right-bottom (dayan-step s))
      ≡ gcd (right-top s) (right-bottom s)
gcd-preserved (dayan lt lb (suc rt) rb) _ =
  trans (cong₂ gcd (cong right-top (dayan-step-unfold lt lb rt rb))
                   (cong right-bottom (dayan-step-unfold lt lb rt rb)))
        (gcd-step (suc rt) rb)

-- `≠ 0` 的余数必为正（stdlib 无 `≢0⇒0<`，用 `<-cmp` 拼）
mod-pos : ∀ {n m : ℕ} → m % suc n ≢ 0 → m % suc n > 0
mod-pos {n} {m} h with <-cmp 0 (m % suc n)
... | tri< a _ _  = a
... | tri≈ _ eq _ = ⊥-elim (h (sym eq))
... | tri> _ _ ()

--------------------------------------------------------------------------------
-- §10. 互素时必取到 1（T1 后半收口）
--------------------------------------------------------------------------------

dayan-hits-one :
  ∀ (s : DayanState) → right-top s > 0 →
    gcd (right-top s) (right-bottom s) ≡ 1 →
    Σ ℕ (λ f → right-top (dayan-iterate-fuel f s) ≡ 1)
dayan-hits-one st pos g1 = <-rec P ih (right-top st) st refl pos g1
  where
    P : ℕ → Set
    P rt = ∀ (st : DayanState) → right-top st ≡ rt → right-top st > 0 →
             gcd (right-top st) (right-bottom st) ≡ 1 →
             Σ ℕ (λ f → right-top (dayan-iterate-fuel f st) ≡ 1)

    ih : ∀ rt → (∀ {rt′} → rt′ < rt → P rt′) → P rt
    ih zero _ (dayan lt lb .zero rb) refl pos _ = ⊥-elim (<-irrefl refl pos)
    ih (suc m) rec (dayan lt lb .(suc m) rb) refl pos g1
      with rb % suc m ≟ 0
    ... | yes r0 = 0 , hits-base (suc m) rb g1 r0
    ... | no r≢0 =
      let step-rt : right-top (dayan-step (dayan lt lb (suc m) rb)) ≡ rb % suc m
          step-rt = cong right-top (dayan-step-unfold lt lb m rb)
          ih′ = rec (step-decreases (dayan lt lb (suc m) rb) pos)
                    (dayan-step (dayan lt lb (suc m) rb))
                    refl
                    (subst (λ z → z > 0) (sym step-rt) (mod-pos {m} {rb} r≢0))
                    (trans (gcd-preserved (dayan lt lb (suc m) rb) pos) g1)
      in suc (proj₁ ih′) , proj₂ ih′

-- 主定理：互素 + 奇数非零 ⇒ 成功终止（秦九韶「奇一而止」）
-- `奇 > 0` 是原文自带前提：十二律「奇数」本义即奇数（≥ 1）；反例 奇=0,定=1 说明不可省
dayan-termination :
  ∀ (奇 定 : ℕ) → 奇 > 0 → gcd 奇 定 ≡ 1 →
    Σ ℕ (λ fuel → right-top (dayan-iterate-fuel fuel (dayan-init 奇 定)) ≡ 1)
dayan-termination 奇 定 奇>0 g1 = dayan-hits-one (dayan-init 奇 定) 奇>0 g1
