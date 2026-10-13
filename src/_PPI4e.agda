{-# OPTIONS --cubical --rewriting --guardedness #-}

-- | _PPI4e —— (d) v2-3（核心）：Gcmp 分类引理（fzero 闭 walk 全部 ∼ nil 或 ∼ loop）
--
-- 数学背景（v2 路线第 3 段·核心件）：
--   Gcmp two-chain 的边 = cmpEdge = 可比关系（x⊑y ⊎ y⊑x——含反身自环）⇒ 任意两点
--   间有捷径边 ⇒ slide 可把任意 ≥2 段 walk 收缩一格 ⇒ 递推至 len ≤ 1。
--   分类定理：每个 fzero 闭 walk AHomotopy-等价于 nil 或 selfloop-walk（二类完备）。
--   互斥性由 _PPI4b 的 selfloop-≁nil 提供（nil 孤立点）⇒ 恰两类。
--
-- 核心原则：
-- 1. 递推走 k = len 索引形（终止性结构于 k——Cubical ≡ 不可 pattern 精化的规避）
-- 2. 矛盾消解走 Bool 后像（isZeroB 系——K 禁用）
-- 3. 零洞零 postulate
--
-- 包含：cmp-total（可比全性）｜selfloop-merge（自环并类）｜step-down（收缩步）｜
--       gcmp-classify（分类主件）｜§5 三性闸门核对（完备/互斥/构造）
module _PPI4e where

open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_×_; _,_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using () renaming (refl to reflᴱ)
open import Cubical.Foundations.Prelude using (_≡_; refl; sym; cong; _∙_)
open import Sovereign.Topology.AlexandroffFinite using (FinitePoset)
open import Sovereign.Topology.McCordCore using (cmpEdge)
open import Sovereign.Synthesis.McCordPi0 using (two-chain; _⊑₂_; ⊑₂-00; ⊑₂-01; ⊑₂-11)
open import Sovereign.Topology.BarceloAHomotopy
  using (DiGraph; Walk; nil; cons; AStep; AHomotopy; slide; expand; refl'; symm; trans'; gen)
open import _PPI4 using (Gcmp)
open import _PPI2 using (len; true≢false)
open import _PPI4b using (loop-e; selfloop-walk; selfloop-≁nil)

private
  module DG = DiGraph
  module FP = FinitePoset

--------------------------------------------------------------------------------
-- §1 可比全性（two-chain 上任意两点有捷径边）
--------------------------------------------------------------------------------

cmp-total : ∀ (x y : Fin 2) → cmpEdge two-chain x y
cmp-total fzero fzero = inj₁ ⊑₂-00
cmp-total fzero (fsuc fzero) = inj₁ ⊑₂-01
cmp-total (fsuc fzero) fzero = inj₂ ⊑₂-01
cmp-total (fsuc fzero) (fsuc fzero) = inj₁ ⊑₂-11

--------------------------------------------------------------------------------
-- §2 自环并类（任意自环单段 ∼ selfloop-walk——expand 抬高 + slide 落回）
--------------------------------------------------------------------------------

selfloop-merge : ∀ (e : cmpEdge two-chain fzero fzero)
  → AHomotopy (Gcmp two-chain) (cons e (nil fzero)) selfloop-walk
selfloop-merge e =
  trans' (gen (expand (nil fzero) (nil fzero) (cmp-total fzero (fsuc fzero)) (cmp-total (fsuc fzero) fzero) e))
         (gen (slide (nil fzero) (nil fzero) (cmp-total fzero (fsuc fzero)) (cmp-total (fsuc fzero) fzero) loop-e))

--------------------------------------------------------------------------------
-- §3 收缩步（≥2 段 walk → 短一格）
--------------------------------------------------------------------------------

step-down : ∀ {y z : Fin 2}
  (e1 : cmpEdge two-chain fzero y) (e2 : cmpEdge two-chain y z)
  (b : Walk (Gcmp two-chain) z fzero)
  → AHomotopy (Gcmp two-chain) (cons e1 (cons e2 b)) (cons (cmp-total fzero z) b)
step-down e1 e2 b = gen (slide (nil fzero) b e1 e2 (cmp-total fzero _))

--------------------------------------------------------------------------------
-- §4 主件：分类引理（k = len 索引递推——终止性结构于 k）
--------------------------------------------------------------------------------

suc-inj : ∀ {a b : ℕ} → suc a ≡ suc b → a ≡ b
suc-inj = cong predℕ
  where predℕ : ℕ → ℕ
        predℕ zero = zero
        predℕ (suc n) = n

isZeroB : ℕ → Bool
isZeroB zero = true
isZeroB (suc _) = false

snotz-len : ∀ {n : ℕ} → suc n ≡ zero → ⊥
snotz-len p = true≢false (sym (cong isZeroB p))

znots-len : ∀ {k : ℕ} → zero ≡ suc k → ⊥
znots-len p = snotz-len (sym p)

map⊎ : ∀ {A B C D : Set} → (A → C) → (B → D) → A ⊎ B → C ⊎ D
map⊎ f _ (inj₁ a) = inj₁ (f a)
map⊎ _ g (inj₂ b) = inj₂ (g b)

gcmp-classify : ∀ (w : Walk (Gcmp two-chain) fzero fzero)
  → AHomotopy (Gcmp two-chain) w (nil fzero) ⊎ AHomotopy (Gcmp two-chain) w selfloop-walk
gcmp-classify w = go (len w) w refl
  where
  go : ∀ k (w : Walk (Gcmp two-chain) fzero fzero) → len w ≡ k
     → AHomotopy (Gcmp two-chain) w (nil fzero) ⊎ AHomotopy (Gcmp two-chain) w selfloop-walk
  go zero (nil fzero) _ = inj₁ (refl' (nil fzero))
  go zero (cons e b) p = ⊥-elim (snotz-len p)
  go (suc k) (nil fzero) p = ⊥-elim (znots-len p)
  go (suc k) (cons e (nil fzero)) _ = inj₂ (selfloop-merge e)
  go (suc k) (cons {v = y} e1 (cons {v = z} e2 b)) p =
    map⊎ (λ h' → trans' (step-down e1 e2 b) h')
         (λ h' → trans' (step-down e1 e2 b) h')
         (go k (cons (cmp-total fzero z) b) (suc-inj p))

--------------------------------------------------------------------------------
-- §5 三性闸门核对（完备/互斥/构造——裁决指定：过闸才进 v2-4）
--------------------------------------------------------------------------------

-- 构造性例 1（nil 形）：分类落 inj₁（nil 自证）
cls-ex-nil : gcmp-classify (nil fzero) ≡ inj₁ (refl' (nil fzero))
cls-ex-nil = refl

-- 构造性例 2（单边自环）：分类落 inj₂（selfloop-merge 见证）
cls-ex-loop : gcmp-classify selfloop-walk ≡ inj₂ (selfloop-merge loop-e)
cls-ex-loop = refl

-- 构造性例 3（双边 0→1→0）：收缩一步 → 自环 → 落 inj₂（slide 并类见证）
w2c : Walk (Gcmp two-chain) fzero fzero
w2c = cons (cmp-total fzero (fsuc fzero)) (cons (cmp-total (fsuc fzero) fzero) (nil fzero))

cls-ex-two : AHomotopy (Gcmp two-chain) w2c selfloop-walk
cls-ex-two = trans' (step-down (cmp-total fzero (fsuc fzero)) (cmp-total (fsuc fzero) fzero) (nil fzero))
                    (selfloop-merge (cmp-total fzero fzero))

-- 构造性例 4（三边）：两次收缩 → 自环
w3c : Walk (Gcmp two-chain) fzero fzero
w3c = cons (cmp-total fzero (fsuc fzero))
       (cons (cmp-total (fsuc fzero) fzero)
         (cons (cmp-total fzero fzero) (nil fzero)))

cls-ex-three : AHomotopy (Gcmp two-chain) w3c selfloop-walk
cls-ex-three = trans' (step-down (cmp-total fzero (fsuc fzero)) (cmp-total (fsuc fzero) fzero)
                                 (cons (cmp-total fzero fzero) (nil fzero)))
                      (trans' (step-down (cmp-total fzero fzero) (cmp-total fzero fzero) (nil fzero))
                              (selfloop-merge (cmp-total fzero fzero)))

-- 互斥性：两类不交（nil 孤立点——_PPI4b 反证件直引）
cls-disjoint : ∀ (w : Walk (Gcmp two-chain) fzero fzero)
  → AHomotopy (Gcmp two-chain) w (nil fzero) → AHomotopy (Gcmp two-chain) w selfloop-walk → ⊥
cls-disjoint w h1 h2 = selfloop-≁nil (trans' (symm h2) h1)

-- 完备性 = gcmp-classify 本体（全部 fzero 闭 walk 二分）
-- 构造性 = 例 1-4 全部见证为构造子/引理项（无公理、无 case 爆炸）
