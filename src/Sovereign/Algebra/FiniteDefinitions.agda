{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Algebra.FiniteDefinitions
-- P1-2：有限性定义蕴含关系（Dedekind/Tarski/型有限）
--
-- 任务书 1.3：Tarski-Kuratowski 有限性定义
--   形式化"有限性定义动物园"——型有限/Dedekind/Tarski 三定义的蕴含关系。
--
-- ⚠ 修正记录（2026-10-11，statement_wrong 处置——1.3 批发现，零消费者核实后换形）：
--   ① NoInfDescChain 原定义
--      `NoInfDescChain A = (f : ℕ → A) → ¬ (∀ n → f (suc n) ≡ f n × f (suc n) ≢ f n)`
--      自相矛盾平凡真——逐点 eq∧neq 矛盾 ⟹ 括号内 ∀ n 恒假 ⟹ ¬ 型恒真 ⟹ 任意 A 成立
--      （无数学内容）。已修为 Tarski 离散真形「ℕ 序列必重复（无单射）」——
--      与 _PFT.SeqRepeats 同形（真 Tarski 离散形），语义对照见 §1 注。
--   ② P1-2-type 原为 Set₁ 声明件（仅类型声明、无证明体）——已收全为真定理 P1-2
--      （两半全证：DedekindFinite 走 InjSurj.dedekind-finite-A；NoInfDescChain 走 §2 主件）。
--   消费者核实：修复时本模块零代码消费者（仅 _PFT 注释面引用）——换形零涟漪。
--
-- 0 postulate / 0 hole。
module Sovereign.Algebra.FiniteDefinitions where

open import Data.Nat using (ℕ; suc; _<_) renaming (s≤s to s≤sℕ)
open import Data.Nat.Properties using (<-irrefl; ≤-refl)
open import Data.Fin using (Fin; toℕ)
open import Data.Fin.Properties using (pigeonhole; toℕ-injective)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import Relation.Nullary using (¬_)
open import Data.Product using (_×_; _,_; ∃₂)
open import Data.Empty using (⊥)

open import Sovereign.Algebra.InjSurj
  using (Injective; Surjective; DedekindFinite; Finite; dedekind-finite-A; injective-to)

--------------------------------------------------------------------------------
-- §1. Tarski 有限性——修正形（真 Tarski 离散形）
--
--   原「无限严格递降链」定义（NoInfDescChain 旧形）因逐点 eq∧neq 自相矛盾而平凡真，
--   已废弃。修正形取其真内容：有限集上任意 ℕ 序列必重复（无单射 ℕ → A）——
--   即 Tarski「真子集链有限」的离散对应（无限严格递降链 ⟹ ℕ 单射序列，反之亦然）。
--------------------------------------------------------------------------------

-- 修正形：ℕ 序列必重复（Tarski 离散形；与 _PFT.SeqRepeats 同形）
NoInfDescChain : Set → Set
NoInfDescChain A = (f : ℕ → A) → ¬ (Injective f)

--------------------------------------------------------------------------------
-- §2. 型有限 ⟹ 序列重复（修正形主件）
--
--   证明：Finite A 为 A ≃ Fin n（to/from 双向），to 单（injective-to）。
--   若 f : ℕ → A 单射，则 g = to ∘ f ∘ toℕ : Fin (suc n) → Fin n 单射——
--   与 stdlib pigeonhole（Fin (suc n) → Fin n 必有碰撞）矛盾。
--------------------------------------------------------------------------------

finite→noInfDesc : ∀ {A : Set} (fin : Finite A) → NoInfDescChain A
finite→noInfDesc {A} fin f f-inj = go (pigeonhole (s≤sℕ ≤-refl) g)
  where
  g : Fin (suc (Finite.n fin)) → Fin (Finite.n fin)
  g i = Finite.to fin (f (toℕ i))

  go : (∃₂ {A = Fin (suc (Finite.n fin))} {B = λ _ → Fin (suc (Finite.n fin))}
        (λ i j → (toℕ i < toℕ j) × (g i ≡ g j))) → ⊥
  go (i , j , i<j , gi≡gj) = <-irrefl (cong toℕ i≡j) i<j
    where
    -- g i ≡ g j ⟹（to 单）f(toℕ i) ≡ f(toℕ j) ⟹（f 单）toℕ i ≡ toℕ j ⟹（toℕ 单）i ≡ j
    step1 : Finite.to fin (f (toℕ i)) ≡ Finite.to fin (f (toℕ j))
    step1 = gi≡gj

    step2 : f (toℕ i) ≡ f (toℕ j)
    step2 = injective-to {n = Finite.n fin} fin step1

    step3 : toℕ i ≡ toℕ j
    step3 = f-inj step2

    i≡j : i ≡ j
    i≡j = toℕ-injective step3

--------------------------------------------------------------------------------
-- §3. P1-2（收全真形——原 P1-2-type 声明件的证明体）
--
--   型有限 ⟹ Dedekind 有限 × 序列重复（Tarski 离散形）。
--   语义对照注记：原声明件的 NoInfDescChain 半边为平凡真旧形（⚠ 修正记录①）；
--   本定理两半均为真内容（dedekind-finite-A 已证件 + §2 主件）。
--------------------------------------------------------------------------------

P1-2 : ∀ {A : Set} → Finite A → DedekindFinite A × NoInfDescChain A
P1-2 fin = dedekind-finite-A fin , finite→noInfDesc fin

--------------------------------------------------------------------------------
-- §4. 对照核对（签名即用法示例——P1-2 实例化核对件）
--------------------------------------------------------------------------------

check-p12-fin2 : Finite (Fin 2) → DedekindFinite (Fin 2) × NoInfDescChain (Fin 2)
check-p12-fin2 fin = P1-2 fin
