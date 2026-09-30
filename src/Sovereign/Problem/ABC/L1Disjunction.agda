{-# OPTIONS --rewriting --guardedness #-}
-- | Sovereign.Problem.ABC.L1Disjunction
--
-- L1 断层定理（ABC/README §四「定理（待建）」的形式化）：
--
--   存在两个互素三元组，(i) 模 12 同余类完全相同、(ii) rad(abc) 完全相同、
--   (iii) 但 q = c/rad(abc) 一个 < 1、一个 > 1。
--
--   见证对（README 已核算）：
--     w₁ = (3, 5, 8)      : 3+5=8 ✓ 互素 ✓ rad(3·5·8)=rad(120)=30   q=8/30<1 ✓
--     w₂ = (3, 125, 128)  : 3+125=128 ✓ 互素 ✓ rad(3·125·128)=30  q=128/30>1 ✓
--     （125 ≡ 5 (12)、128 ≡ 8 (12) ⇒ 三同余类一致；rad 同为 30）
--
-- 数学意义：**任何固定模投影 + rad 的观测都无法判定 abc 质量 q 是否跨过 1**——
-- 两见证的观测元组完全相同而 q 分居 1 两侧 ⇒ 观测层面的「盲区」（L1 断层）。
--
-- 设计注：范数核 rad 以**参数 + 两值事实**给出（rad 120 ≡ 30 / rad 480000 ≡ 30）
-- ——盲区定理只需这两值；完整 rad 实现（质因数分解式）列 roadmap，不阻塞本定理。
--
-- 0 postulate / 0 hole；见证算术全部 refl 可核。
module Sovereign.Problem.ABC.L1Disjunction where

open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _%_; _≡ᵇ_; _<_; _≤_; _<ᵇ_)
open import Data.Nat.GCD using (gcd)
open import Data.Bool using (Bool; true; false)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans)

--------------------------------------------------------------------------------
-- 1. 观测元组：固定模 12 同余类 + rad 值（「固定模投影」的形式）
--------------------------------------------------------------------------------

obs4 : ℕ → ℕ → ℕ → ℕ → ℕ × ℕ × ℕ × ℕ
obs4 a b c r = (a % 12 , b % 12 , c % 12 , r)

--------------------------------------------------------------------------------
-- 2. 见证算术（全部 refl 可核）
--------------------------------------------------------------------------------

-- (i) 加法
w1-add : 3 + 5 ≡ 8
w1-add = refl

w2-add : 3 + 125 ≡ 128
w2-add = refl

-- (i') 互素（两两 gcd = 1）
w1-coprime : gcd 3 5 ≡ 1 × gcd 3 8 ≡ 1 × gcd 5 8 ≡ 1
w1-coprime = refl , refl , refl

w2-coprime : gcd 3 125 ≡ 1 × gcd 3 128 ≡ 1 × gcd 125 128 ≡ 1
w2-coprime = refl , refl , refl

-- (ii) 模 12 同余类一致
w-same-mod12 : (3 % 12 ≡ 3 % 12) × (5 % 12 ≡ 125 % 12) × (8 % 12 ≡ 128 % 12)
w-same-mod12 = refl , refl , refl

-- (iii) q 分居 1 两侧（q = c/rad ≷ 1 ⟺ c ≷ rad；用 <? 真值承载）
w1-q-below : (8 <ᵇ 30) ≡ true
w1-q-below = refl

w2-q-above : (30 <ᵇ 128) ≡ true
w2-q-above = refl

--------------------------------------------------------------------------------
-- 3. 观测盲区（L1 断层定理核心）
--------------------------------------------------------------------------------

-- 任取范数核 rad，只要两见证的 rad 同为 30：
--   两见证的**观测元组完全相同** ⇒ 一切以观测为输入的判定器给出同一答案，
--   而 q 分居 1 两侧 ⇒ **固定模投影 + rad 观测不可判 abc 质量**。
l1-obs-blind :
  ∀ (rad : ℕ → ℕ) (r1 : rad 120 ≡ 30) (r2 : rad 480000 ≡ 30)
  {X : Set} (f : ℕ × ℕ × ℕ × ℕ → X) →
  f (obs4 3 5 8 (rad 120)) ≡ f (obs4 3 125 128 (rad 480000))
l1-obs-blind rad r1 r2 f =
  cong f (trans (cong (obs4 3 5 8) r1) (sym (cong (obs4 3 125 128) r2)))

-- 判定器形式：任何基于观测的 q≷1 判定器必同时答错一侧。
l1-no-decider :
  ∀ (rad : ℕ → ℕ) (r1 : rad 120 ≡ 30) (r2 : rad 480000 ≡ 30) →
  (dec : ℕ × ℕ × ℕ × ℕ → Bool) →
  dec (obs4 3 5 8 (rad 120)) ≡ dec (obs4 3 125 128 (rad 480000))
l1-no-decider rad r1 r2 dec = l1-obs-blind rad r1 r2 dec

-- 语义注（非证明，锚定 README）：dec 同值 ⇒ 若判 w₁ 为 q<1 则 w₂（实 q>1）误判；
-- 反之亦然。盲区 = 观测层面不可分辨，不是三元组不可区分（a,b,c 本体可辨）。

--------------------------------------------------------------------------------
-- 4. 断层定理打包（Σ 形态：见证对 + 四组性质）
--------------------------------------------------------------------------------

L1-pack : Set
L1-pack =
  (3 + 5 ≡ 8) × (3 + 125 ≡ 128)
  × (gcd 3 5 ≡ 1 × gcd 3 8 ≡ 1 × gcd 5 8 ≡ 1)
  × (gcd 3 125 ≡ 1 × gcd 3 128 ≡ 1 × gcd 125 128 ≡ 1)
  × ((3 % 12 ≡ 3 % 12) × (5 % 12 ≡ 125 % 12) × (8 % 12 ≡ 128 % 12))
  × ((8 <ᵇ 30) ≡ true) × ((30 <ᵇ 128) ≡ true)

l1-disjunction : L1-pack
l1-disjunction =
  w1-add , w2-add , w1-coprime , w2-coprime , w-same-mod12 , w1-q-below , w2-q-above

--------------------------------------------------------------------------------
-- 5. 具体实例化：完整范数核 rad 落地参数化盲区定理（追加节）
--    rad 的可计算定义在 L1Rad：rad 120 ≡ 30 / rad 480000 ≡ 30 均 refl 可核，
--    由此把 §3 的「任取 rad」参数化事实收敛为**具体 rad 的实例**。
--    既有签名一律不变；本节只做实例化与交叉核证。
--------------------------------------------------------------------------------

open import Sovereign.Problem.ABC.L1Rad using (rad; rad-120; rad-480000)

-- 参数化事实的具体应用：l1-obs-blind rad rad-120 rad-480000
l1-rad-blind : {X : Set} (f : ℕ × ℕ × ℕ × ℕ → X) →
  f (obs4 3 5 8 (rad 120)) ≡ f (obs4 3 125 128 (rad 480000))
l1-rad-blind f = l1-obs-blind rad rad-120 rad-480000 f

-- 判定器形式的具体实例：任何以观测为输入的 q ≷ 1 判定器在两见证上同值
l1-rad-no-decider : (dec : ℕ × ℕ × ℕ × ℕ → Bool) →
  dec (obs4 3 5 8 (rad 120)) ≡ dec (obs4 3 125 128 (rad 480000))
l1-rad-no-decider dec = l1-rad-blind dec

-- 恒等观测器实例（参数化定理的直接应用注记）
l1-rad-blind-id : obs4 3 5 8 (rad 120) ≡ obs4 3 125 128 (rad 480000)
l1-rad-blind-id = l1-rad-blind (λ z → z)

-- 对抗验证（独立第二路径）：观测元组逐位归一为同一 (3,5,8,30)，refl 直接核证。
-- 与 l1-rad-blind-id 同命题、不同证明来源 ⇒ 实例化无论证空洞。
l1-rad-obs-same : obs4 3 5 8 (rad 120) ≡ obs4 3 125 128 (rad 480000)
l1-rad-obs-same = refl

-- 归一化后的同值结论（两观测元组均为 (3,5,8,30)）
l1-rad-dec-same : (dec : ℕ × ℕ × ℕ × ℕ → Bool) →
  dec (obs4 3 5 8 30) ≡ dec (obs4 3 125 128 30)
l1-rad-dec-same dec = refl
