{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Topology.AlexandroffFinite
-- 任务书第二层·2.1：Alexandroff 离散空间（1937）的有限构造性实例
--
-- 数学背景：Alexandroff, "Diskrete Räume"（Mat. Sb. 2(44):3, 1937, 501–519；
--   本地原文 docs/文献/pdf/Alexandroff1937_Diskrete-Raeume.pdf）定义「离散空间」=
--   任意多个开集的交仍为开集的拓扑空间，并证明这类空间与偏序集是同一回事。
--   本模块给出有限载体（Fin n）上的构造性对应物：
--     偏序集 →（specialization 序的 upsets 作为开集）→ Alexandroff 拓扑公理；
--     下闭包算子的幂等性（cl-⊆ 引理）；
--     **任意**下闭包族/上闭包族之交仍闭（Alexandroff 定义性质本身）。
--
-- ⚠ 范围（诚实边界）：
--   1. Alexandroff 1937 的「同一回事」在无穷处依赖幂集装置；本库只做有限载体 +
--      可判定序的**本源侧构造**（Fin n 由 fzero/fsuc 生成，结构 = 生成方式）。
--      McCord 弱同伦等价方向（概要卡 §4）与链复形方向（∂∂=0，接 jac_Topology
--      边界矩阵）是 roadmap，不入本模块。
--   2. 谓词以 Set 值函数表示；集合相等一律**逐点双蕴含**（无 funext，不合并为
--      函数等式——NSE.T15 / GaoYangRigidLock 同纪律）。
--
-- 0 postulate / 0 hole。
module Sovereign.Topology.AlexandroffFinite where

open import Data.Nat using (ℕ)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.Fin.Properties using (_≟_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_×_; _,_)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans)

--------------------------------------------------------------------------------
-- §1. 有限偏序集（载体 Fin n，可判定序）
--------------------------------------------------------------------------------

record FinitePoset (n : ℕ) : Set₁ where
  field
    _⊑_       : Fin n → Fin n → Set
    ⊑-dec     : ∀ a b → Dec (a ⊑ b)
    ⊑-refl    : ∀ a → a ⊑ a
    ⊑-trans   : ∀ a b c → a ⊑ b → b ⊑ c → a ⊑ c
    ⊑-antisym : ∀ a b → a ⊑ b → b ⊑ a → a ≡ b

-- 上下闭包（Alexandroff 拓扑里点 x 的最小开邻域 = downset x / 最大闭包 = upset x）
downset : ∀ {n} (P : FinitePoset n) (x : Fin n) → Fin n → Set
downset P x y = FinitePoset._⊑_ P y x

upset : ∀ {n} (P : FinitePoset n) (x : Fin n) → Fin n → Set
upset P x y = FinitePoset._⊑_ P x y

IsDownset : ∀ {n} (P : FinitePoset n) (U : Fin n → Set) → Set
IsDownset P U = ∀ x y → U x → FinitePoset._⊑_ P y x → U y

IsUpset : ∀ {n} (P : FinitePoset n) (U : Fin n → Set) → Set
IsUpset P U = ∀ x y → U x → FinitePoset._⊑_ P x y → U y

--------------------------------------------------------------------------------
-- §2. Alexandroff 性质：任意下闭包/上闭包族之交仍闭
--     （这是「任意多个开集的交仍开」的可判定有限形态）
--------------------------------------------------------------------------------

downset-inter : ∀ {n m} (P : FinitePoset n) (U : Fin m → Fin n → Set) →
  (∀ i → IsDownset P (U i)) →
  IsDownset P (λ z → ∀ i → U i z)
downset-inter P U dU x y hx hy i = dU i x y (hx i) hy

upset-inter : ∀ {n m} (P : FinitePoset n) (U : Fin m → Fin n → Set) →
  (∀ i → IsUpset P (U i)) →
  IsUpset P (λ z → ∀ i → U i z)
upset-inter P U uU x y hx hy i = uU i x y (hx i) hy

-- 下闭包算子的幂等性核：由「cl z ⊆ cl x」得 z ⊑ x（取 witness z 自己，refl）
downset-cl-⊆ : ∀ {n} (P : FinitePoset n) (x z : Fin n) →
  (∀ w → FinitePoset._⊑_ P w z → FinitePoset._⊑_ P w x) →
  FinitePoset._⊑_ P z x
downset-cl-⊆ P x z h = h z (FinitePoset.⊑-refl P z)

--------------------------------------------------------------------------------
-- §3. 偏序集 → Alexandroff 拓扑公理（开集 = upsets）
--
-- 公理：∅ 与全集是开；两开集之并是开；任意开集族之交是开（Alexandroff 性质）。
-- 有限交（含二交）由任意交取 m = 2 获得。
--------------------------------------------------------------------------------

top-∅ : ∀ {n} (P : FinitePoset n) → IsUpset P (λ _ → ⊥)
top-∅ P x y ()

top-all : ∀ {n} (P : FinitePoset n) → IsUpset P (λ _ → ⊤)
top-all P x y _ _ = _

top-∪ : ∀ {n} (P : FinitePoset n) (U V : Fin n → Set) →
  IsUpset P U → IsUpset P V → IsUpset P (λ z → U z ⊎ V z)
top-∪ P U V uU uV x y (inj₁ hx) hxy = inj₁ (uU x y hx hxy)
top-∪ P U V uU uV x y (inj₂ hx) hxy = inj₂ (uV x y hx hxy)

top-∩ : ∀ {n m} (P : FinitePoset n) (Us : Fin m → Fin n → Set) →
  (∀ i → IsUpset P (Us i)) →
  IsUpset P (λ z → ∀ i → Us i z)
top-∩ P Us = upset-inter P Us

--------------------------------------------------------------------------------
-- §4. 具体点对抗（对抗验证协议 §6）：2-链 0 ⊑ 1
--
-- 序谓词 a ⊑ b = (a ≡ 0) ⊎ (b ≡ 1)，四条定律逐 case refl/消去；
-- 用 downset-cl-⊆ 实例推出 0 ⊑ 1（幂等核的非平凡使用）。
--------------------------------------------------------------------------------

chain2-⊑ : Fin 2 → Fin 2 → Set
chain2-⊑ a b = (a ≡ fzero) ⊎ (b ≡ fsuc fzero)

chain2-⊑-dec : ∀ a b → Dec (chain2-⊑ a b)
chain2-⊑-dec a b with a ≟ fzero
... | yes a≡0 = yes (inj₁ a≡0)
... | no ¬a≡0 with b ≟ fsuc fzero
...   | yes b≡1 = yes (inj₂ b≡1)
...   | no ¬b≡1 = no h
  where
    h : chain2-⊑ a b → ⊥
    h (inj₁ a≡0) = ¬a≡0 a≡0
    h (inj₂ b≡1) = ¬b≡1 b≡1

chain2-⊑-refl : ∀ a → chain2-⊑ a a
chain2-⊑-refl fzero = inj₁ refl
chain2-⊑-refl (fsuc fzero) = inj₂ refl

chain2-⊑-trans : ∀ a b c → chain2-⊑ a b → chain2-⊑ b c → chain2-⊑ a c
chain2-⊑-trans a b c (inj₁ a≡0) _ = inj₁ a≡0
chain2-⊑-trans a b c (inj₂ b≡1) (inj₂ c≡1) = inj₂ c≡1
chain2-⊑-trans a b c (inj₂ b≡1) (inj₁ b≡0) =
  ⊥-elim (absurd10 (trans (sym b≡1) b≡0))
  where
    absurd10 : fsuc fzero ≡ fzero → ⊥
    absurd10 ()

chain2-⊑-antisym : ∀ a b → chain2-⊑ a b → chain2-⊑ b a → a ≡ b
chain2-⊑-antisym fzero fzero (inj₁ a≡0) _ = a≡0
chain2-⊑-antisym fzero fzero (inj₂ ()) _
chain2-⊑-antisym fzero (fsuc fzero) _ (inj₁ ())
chain2-⊑-antisym fzero (fsuc fzero) _ (inj₂ a≡1) = a≡1
chain2-⊑-antisym (fsuc fzero) fzero (inj₁ ()) _
chain2-⊑-antisym (fsuc fzero) fzero (inj₂ ()) _
chain2-⊑-antisym (fsuc fzero) (fsuc fzero) _ (inj₁ ())
chain2-⊑-antisym (fsuc fzero) (fsuc fzero) _ (inj₂ a≡1) = a≡1

chain2 : FinitePoset 2
chain2 = record
  { _⊑_       = chain2-⊑
  ; ⊑-dec     = chain2-⊑-dec
  ; ⊑-refl    = chain2-⊑-refl
  ; ⊑-trans   = chain2-⊑-trans
  ; ⊑-antisym = chain2-⊑-antisym
  }

-- 幂等核实例：从「0 的下闭包 ⊆ 1 的下闭包」机械得 0 ⊑ 1
chain2-0⊑1 : chain2-⊑ fzero (fsuc fzero)
chain2-0⊑1 = downset-cl-⊆ chain2 (fsuc fzero) fzero h
  where
    h : ∀ w → chain2-⊑ w fzero → chain2-⊑ w (fsuc fzero)
    h w (inj₁ w≡0) = inj₁ w≡0
    h w (inj₂ ())

-- Alexandroff 性质实例：2-链上开集族之交仍是 upset（族交 = ∀ i 形式，与 top-∩ 精确同型）
chain2-upsets-inter :
  IsUpset chain2 (λ z → ∀ i → chain2-⊑ (fsuc fzero) z)
chain2-upsets-inter =
  top-∩ {m = 1} chain2 (λ _ z → chain2-⊑ (fsuc fzero) z) (λ _ → id-up)
  where
    id-up : IsUpset chain2 (λ z → chain2-⊑ (fsuc fzero) z)
    id-up x y hx hxy = chain2-⊑-trans (fsuc fzero) x y hx hxy
