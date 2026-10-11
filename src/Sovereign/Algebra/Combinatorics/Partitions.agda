{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Algebra.Combinatorics.Partitions
-- 整数分拆（降序部值表形）与共轭分拆
--
-- 数学背景：n 的分拆 = 降序正整数序列 λ₁ ≥ λ₂ ≥ … ≥ λᵣ > 0 且 Σλᵢ = n。
--   本模块用**部值表形**（List ℕ 降序判定走 Bool 通道——免函数外延）。
--   共轭分拆（Ferrers 图转置）：λ*ⱼ = #{i | λᵢ ≥ j}——conj xs = 各层计数表。
--   与多重集关系：分拆 = 部值多重集（toMulti：部值 → 重数，Multisets.Multi 衔接）。
--
-- 核心原则：
-- 1. 部值表形定义（Partition record：parts/lsum≡/desc?≡true——关系入定义）
-- 2. 共轭 = 计数表生成（countGE/upTo 自含件）；对合性小例全形（refl 级）+ 一般形立界
-- 3. p(n) 小值 = **显式分拆枚举**（n≤4 全体列单 + sum 核对）——计数完备性立界
-- 4. toMulti 衔接 Multisets.Multi（分拆 = 部值多重集——§5(iii) 语义锚兑现）
-- 5. 核对层全 refl/Bool 通道（免 funext）
--
-- 包含：lsum · upTo · maxL · ge? · countGE · conj · Partition
--       · toMulti · p4 全体五件 · 共轭对合小例 · 核对层

module Sovereign.Algebra.Combinatorics.Partitions where

open import Data.Nat using (ℕ; zero; suc; _+_; _∸_; _≤?_)
open import Data.Nat.Properties using (+-identityʳ)
open import Data.Bool using (Bool; true; false; _∧_)
open import Data.List using (List; []; _∷_; map)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.Fin using (toℕ)
open import Data.Product using (_×_; _,_)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong)
open import Sovereign.Algebra.Combinatorics.Multisets using (Multi)

------------------------------------------------------------------------
-- §1 基础件层：表运算（lsum/upTo/maxL/ge?/countGE）
------------------------------------------------------------------------

-- 表求和
lsum : List ℕ → ℕ
lsum [] = 0
lsum (x ∷ xs) = x + lsum xs

-- 表尾接元素（前置件——upTo 用）
_∷ʳ_ : List ℕ → ℕ → List ℕ
[] ∷ʳ y = y ∷ []
(x ∷ xs) ∷ʳ y = x ∷ (xs ∷ʳ y)

-- 升段枚举 [1, 2, …, m]（共轭生成的层索引表）
upTo : ℕ → List ℕ
upTo zero = []
upTo (suc m) = upTo m ∷ʳ suc m

-- 表最大值（空表取零）
maxL : List ℕ → ℕ
maxL [] = 0
maxL (x ∷ xs) = max2 x (maxL xs)
  where
  max2 : ℕ → ℕ → ℕ
  max2 zero b = b
  max2 (suc a) zero = suc a
  max2 (suc a) (suc b) = suc (max2 a b)

-- a ≥ b 的 Bool 判定（Bool 通道——核对层免证明项）
ge? : ℕ → ℕ → Bool
ge? a b with b ≤? a
... | yes _ = true
... | no  _ = false

-- 计数：表中 ≥ j 的元素个数
countGE : ℕ → List ℕ → ℕ
countGE j [] = 0
countGE j (x ∷ xs) = cond+ (ge? x j) 1 (countGE j xs)
  where
  cond+ : Bool → ℕ → ℕ → ℕ
  cond+ true a b = a + b
  cond+ false _ b = b

------------------------------------------------------------------------
-- §2 共轭（Ferrers 转置）
------------------------------------------------------------------------

-- 共轭分拆：各层（≥j 层）计数表——升段生成保证降序
conj : List ℕ → List ℕ
conj xs = map (λ j → countGE j xs) (upTo (maxL xs))

------------------------------------------------------------------------
-- §3 分拆定义层（关系入定义——Bool 通道判序）
------------------------------------------------------------------------

-- 降序判定（相邻项 a ≥ b）
desc? : List ℕ → Bool
desc? [] = true
desc? (x ∷ []) = true
desc? (x ∷ (y ∷ ys)) = andb (ge? x y) (desc? (y ∷ ys))
  where
  andb : Bool → Bool → Bool
  andb true b = b
  andb false _ = false

-- n 的分拆：降序部值表 + 权和 = n
record Partition (n : ℕ) : Set where
  field
    parts  : List ℕ
    lsum≡  : lsum parts ≡ n
    desc≡  : desc? parts ≡ true

------------------------------------------------------------------------
-- §4 与多重集关系（语义锚：分拆 = 部值多重集）
------------------------------------------------------------------------

-- 部值计数（值 v 在表中重数）
countVal : ℕ → List ℕ → ℕ
countVal v [] = 0
countVal v (x ∷ xs) with v ≤? x | x ≤? v
... | yes _ | yes _ = suc (countVal v xs)
... | _    | _    = countVal v xs

-- toMulti：分拆 → Multi (suc n)（部值 ∈ [0..n] 重数面——Multisets 衔接）
toMulti : ∀ {n} → List ℕ → Multi (suc n)
toMulti {n} xs i = countVal (toℕ i) xs

------------------------------------------------------------------------
-- §5 核对层（全 refl/Bool 通道——p(n) 小值 + 共轭对合小例）
------------------------------------------------------------------------

-- p(2)=2 全体：[2],[1,1]
p2-a : Partition 2
Partition.parts p2-a = 2 ∷ []
Partition.lsum≡ p2-a = refl
Partition.desc≡ p2-a = refl

p2-b : Partition 2
Partition.parts p2-b = 1 ∷ 1 ∷ []
Partition.lsum≡ p2-b = refl
Partition.desc≡ p2-b = refl

-- p(4)=5 全体：[4],[3,1],[2,2],[2,1,1],[1,1,1,1]（显式枚举——完备性立界 §6）
p4-a : Partition 4
Partition.parts p4-a = 4 ∷ []
Partition.lsum≡ p4-a = refl
Partition.desc≡ p4-a = refl

p4-b : Partition 4
Partition.parts p4-b = 3 ∷ 1 ∷ []
Partition.lsum≡ p4-b = refl
Partition.desc≡ p4-b = refl

p4-c : Partition 4
Partition.parts p4-c = 2 ∷ 2 ∷ []
Partition.lsum≡ p4-c = refl
Partition.desc≡ p4-c = refl

p4-d : Partition 4
Partition.parts p4-d = 2 ∷ 1 ∷ 1 ∷ []
Partition.lsum≡ p4-d = refl
Partition.desc≡ p4-d = refl

p4-e : Partition 4
Partition.parts p4-e = 1 ∷ 1 ∷ 1 ∷ 1 ∷ []
Partition.lsum≡ p4-e = refl
Partition.desc≡ p4-e = refl

-- 共轭对合小例（refl 级——计算通道）：
--   conj [3,1] = [2,1,1]；conj [2,1,1] = [3,1]（对合对）
check-conj-31 : conj (3 ∷ 1 ∷ []) ≡ 2 ∷ 1 ∷ 1 ∷ []
check-conj-31 = refl

check-conj-211 : conj (2 ∷ 1 ∷ 1 ∷ []) ≡ 3 ∷ 1 ∷ []
check-conj-211 = refl

check-conj-inv-31 : conj (conj (3 ∷ 1 ∷ [])) ≡ 3 ∷ 1 ∷ []
check-conj-inv-31 = refl

check-conj-inv-211 : conj (conj (2 ∷ 1 ∷ 1 ∷ [])) ≡ 2 ∷ 1 ∷ 1 ∷ []
check-conj-inv-211 = refl

-- 自共轭例：[2,2] 转置不变；[4]↔[1,1,1,1] 对合对
check-conj-22 : conj (2 ∷ 2 ∷ []) ≡ 2 ∷ 2 ∷ []
check-conj-22 = refl

check-conj-4 : conj (4 ∷ []) ≡ 1 ∷ 1 ∷ 1 ∷ 1 ∷ []
check-conj-4 = refl

check-conj-inv-4 : conj (conj (4 ∷ [])) ≡ 4 ∷ []
check-conj-inv-4 = refl

-- toMulti 衔接核对：[2,1] 的部值重数面（1 ↦ 1、2 ↦ 1）
check-tomulti-21-1 : toMulti {2} (2 ∷ 1 ∷ []) (fsuc fzero) ≡ 1
check-tomulti-21-1 = refl

check-tomulti-21-2 : toMulti {2} (2 ∷ 1 ∷ []) (fsuc (fsuc fzero)) ≡ 1
check-tomulti-21-2 = refl

check-tomulti-111 : toMulti {2} (1 ∷ 1 ∷ 1 ∷ []) (fsuc fzero) ≡ 3
check-tomulti-111 = refl

-- 求和/序核对
check-lsum-4 : lsum (3 ∷ 1 ∷ []) ≡ 4
check-lsum-4 = refl

check-desc-211 : desc? (2 ∷ 1 ∷ 1 ∷ []) ≡ true
check-desc-211 = refl

------------------------------------------------------------------------
-- §6 立界注记（诚实边界——不设空壳签名）
-- (i) 共轭对合一般定理（conj∘conj ≡ id 于全体降序表——需降序性归一化
--     与 lsum 引理链 ~60-100 行；小例面即 §5 六件 refl 级）；
-- (ii) p(n) 枚举完备性（无其余分拆的分类证明——pair-class-2 式归纳
--     对一般 n,k 为 ~100+ 行分类链）；
-- (iii) Ferrers 双射一般形（分拆 ↔ 共轭对合类）——随 (i)；
-- (iv) toMulti 的满/单刻画（分拆 = 部值多重集 + 降序约束的严格双向）
--     ——函数外延面立界（Multisets §5(i) 同源）。
------------------------------------------------------------------------
