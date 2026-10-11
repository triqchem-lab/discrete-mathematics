{-# OPTIONS --rewriting --guardedness #-}

-- | _PFT（任务书 1.3 施工探针——有限性定义动物园）
-- 数学背景：Dedekind 1888（单射自映射必满射）/ Tarski-Kuratowski 1920-1924
--   （真子集关系良基 / 非空子集族极小元）/ 型有限（Finite A = Σ n, A ≃ Fin n）
--   ——三定义经典下等价，构造性下分叉：型有限 ⟹ 其余可证，反向需经典逻辑。
-- 核心原则：
-- 1. 对账表锚定已有证（不重证）：finite→dedekindFinite / dedekind-finite-A /
--    pigeonhole-iff / tarski-min 四锚。
-- 2. 缺口引理：型有限 → 序列重复（真 Tarski 离散形 SeqRepeats）——本件主证。
-- 3. 诚实边界：Dedekind→型有限、Tarski 形→型有限**构造性不成立/未证**——只注记。
-- 4. ⚠ statement_wrong 注记：FiniteDefinitions.NoInfDescChain 原定义
--   （逐点 eq∧neq）自相矛盾平凡真——本件用修正形 SeqRepeats 并在对账表标出。
-- 包含：动物园对账锚 / SeqRepeats（修正形）/ finite→seqRepeats / P1-2 修正版
--       / Fin 2 核对层 / 三定义等价图注记
module _PFT where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Nat.Properties using (n<1+n; <-irrefl)
open import Data.Fin using (Fin; toℕ)
open import Data.Fin.Properties using (pigeonhole; toℕ-injective)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import Relation.Nullary using (¬_)
open import Data.Product using (_×_; _,_)

open import Sovereign.Algebra.InjSurj
  using (Injective; DedekindFinite; Finite; dedekind-finite-A; injective-to)

--------------------------------------------------------------------------------
-- §1 动物园对账表（四锚——已证面 grep 汇总，不重证）
--------------------------------------------------------------------------------
-- ① 型有限 → Dedekind 有限（已证双份）：
--    InjSurj.dedekind-finite-A    : Finite A → DedekindFinite A        （:179）
--    Finiteness.Dedekind.finite→dedekindFinite（:35——FiniteDynamics.injSurj 路）
-- ② 鸽巢双向（已证）：Finiteness.Pigeonhole.pigeonhole-iff（:62）
--    pigeonhole→ : m < n → (Fin n → Fin m) → ¬ Injective（否定向）
--    pigeonhole← : ¬ (m < n) → Σ (Fin n → Fin m) Injective（肯定向）
-- ③ Tarski 极小元（已证实例）：Finiteness.Tarski.tarski-min
--    （Fin n 非空可判定子集族有 toℕ 最小元）
-- ④ Trit 实例（已证）：InjSurj.trit-dedekind / dedekind-fin0
-- ⚠ 修正件：FiniteDefinitions.NoInfDescChain = (f : ℕ → A) → ¬ (∀ n → f(suc n) ≡ f n × f(suc n) ≢ f n)
--    ——逐点 eq∧neq 矛盾 ⟹ 任意 A 平凡成立（无内容）；真 Tarski 离散形见 §2 SeqRepeats。

--------------------------------------------------------------------------------
-- §2 缺口引理——真 Tarski 离散形
--------------------------------------------------------------------------------

-- 序列重复性：任何 ℕ→A 序列必有重复值（无限递降链不可能的序列形）
SeqRepeats : Set → Set
SeqRepeats A = ∀ (f : ℕ → A) → ¬ (Injective f)

-- §2.1 主件：型有限 → 序列重复
-- 策略：f : ℕ → A 抽出前 suc N 项得 g : Fin (suc N) → Fin N（经 to）；
--       stdlib pigeonhole（N < suc N）否定 g 的单射性；
--       f 单射 + to 单射（injective-to）+ toℕ 单射 ⟹ g 单射 ⟹ ⊥。
g-of : ∀ {A : Set} (fin : Finite A) (f : ℕ → A) → Fin (suc (Finite.n fin)) → Fin (Finite.n fin)
g-of fin f i = Finite.to fin (f (toℕ i))

-- g 的单射性传递链：g i ≡ g j ⟹ to(f(ℕi)) ≡ to(f(ℕj)) ⟹ f(ℕi) ≡ f(ℕj) ⟹ ℕi ≡ ℕj ⟹ i ≡ j
g-of-inj : ∀ {A : Set} (fin : Finite A) (f : ℕ → A) →
           Injective f → Injective (g-of fin f)
g-of-inj fin f f-inj {i} {j} eq =
  toℕ-injective (f-inj {toℕ i} {toℕ j}
    (injective-to {n = Finite.n fin} fin eq))

-- 主定理：型有限 ⟹ 序列重复（真 Tarski 离散形——任务书 1.3 缺口引理）
-- 证：stdlib pigeonhole（见证形）给出碰撞对 (i , j , i<j , g i ≡ g j)；
--     g-of-inj 把碰撞化为 i ≡ j ⟹ <-irrefl 矛盾。
finite→seqRepeats : ∀ {A : Set} → Finite A → SeqRepeats A
finite→seqRepeats {A} fin f f-inj
  with pigeonhole (n<1+n (Finite.n fin)) (g-of fin f)
... | i , j , i<j , eq = <-irrefl (cong toℕ (g-of-inj fin f f-inj eq)) i<j

--------------------------------------------------------------------------------
-- §3 P1-2 修正版（原 FiniteDefinitions.P1-2-type 为声明件——此处补全）
--------------------------------------------------------------------------------
--   原声明件的 NoInfDescChain 半边平凡真（§1 ⚠ 注记）；本件用修正形 SeqRepeats 收全。
P1-2 : ∀ {A : Set} → Finite A → DedekindFinite A × SeqRepeats A
P1-2 fin = dedekind-finite-A fin , finite→seqRepeats fin

--------------------------------------------------------------------------------
-- §4 核对层（Fin 2 小例）
--------------------------------------------------------------------------------
fin2 : Finite (Fin 2)
fin2 = record { n = 2 ; to = λ x → x ; from = λ x → x
              ; to-from = λ _ → refl ; from-to = λ _ → refl }

-- Fin 2 的序列重复性（P1-2 的 n=2 实例化——核对件）
check-seq-fin2 : SeqRepeats (Fin 2)
check-seq-fin2 = finite→seqRepeats fin2

-- P1-2 于 Fin 2（组合核对）
check-p12-fin2 : DedekindFinite (Fin 2) × SeqRepeats (Fin 2)
check-p12-fin2 = P1-2 fin2

--------------------------------------------------------------------------------
-- §5 三定义等价图注记（诚实边界）
--------------------------------------------------------------------------------
--             ┌────────────── 经典逻辑下三角等价 ──────────────┐
--   型有限 ⇄ Dedekind 有限 ⇄ Tarski 良基有限（真子集链/极小元）
--             └──────────────────────────────────────────────┘
--   构造性已证方向（本库）：
--     型有限 → Dedekind 有限   ①dedekind-finite-A ②finite→dedekindFinite
--     型有限 → 序列重复        finite→seqRepeats（本件——真 Tarski 离散形）
--     型有限 → 极小元实例      tarski-min（Fin n 可判定族）
--     鸽巢双向                pigeonhole-iff
--   构造性不成立/未证方向（诚实边界——只注记不硬证）：
--     Dedekind 有限 → 型有限   （经典等价；构造性反例模型存在——需经典逻辑）
--     序列重复/良基 → 型有限   （同上——Tarski 定义的经典等价依赖排中）
--   本库口径：框架锁定型有限（Fin n 载体），动物园的「跨定义等价」只在经典侧成立
--   ——构造性侧以「型有限为出发点的单向蕴含包」为准（§3 P1-2 即其打包形）。
