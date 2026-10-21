{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Algebra.LinearAlgebra.GF3Count
-- 函数空间的**计数**基础（T4 的秩-零化度前置件，2026-10-20）
--
-- 数学背景
--   秩-零化度的核心是 `|V| = 3^(dim V)`。要让这句话有意义，先得有
--   「`(Fin d → Trit)` 有多少元素」的**结构**说法 —— 本模块给两件：
--
--     ① `split-fun : (Fin (suc d) → Trit) ≅ Trit × (Fin d → Trit)`
--        （按首元素拆分 —— 这是「一位三值」的精确表述）
--     ② `sizeOf : ℕ → ℕ`（递归计数），以及 `sizeOf d ≡ 3 ^ d`
--
--   ⇒ `|(Fin d → Trit)|` 的递归结构 = `3^d`，无需 base-3 编码 ✗
--
-- 为什么这样设计
--   直接证 `(Fin d → Trit) ↔ Fin (3^d)` 需要 base-3 数字分解（要 div/mod），
--   而**递归拆分**给出的计数已经足够支撑「维数 ↔ 基数」的归纳论证 ✓。
--
-- 0 postulate / 0 hole

module Sovereign.Algebra.LinearAlgebra.GF3Count where

open import Data.Nat using (ℕ; zero; suc; _*_; _^_; _+_)
open import Data.Fin using (Fin; zero′) renaming (zero to fzero; suc to fsuc)
open import Data.Product using (_×_; _,_; proj₁; proj₂; Σ)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; cong; cong₂; sym; trans)

open import Sovereign.Base.Trit using (Trit; T₀; T₁; T₂)

--------------------------------------------------------------------------------
-- §1. 递归计数
--------------------------------------------------------------------------------

-- `Fin d → Trit` 的元素个数（递归版：空类型 1 个元素，加一位乘 3）
sizeOf : ℕ → ℕ
sizeOf zero    = 1
sizeOf (suc d) = 3 * sizeOf d

-- ★ 与 `3^d` 一致（`3^(suc d) = 3 * 3^d` 是定义相等）
sizeOf-3 : ∀ d → sizeOf d ≡ 3 ^ d
sizeOf-3 zero    = refl
sizeOf-3 (suc d) = cong (3 *_) (sizeOf-3 d)

--------------------------------------------------------------------------------
-- §2. 按首元素拆分（「一位三值」的结构表述）
--------------------------------------------------------------------------------

-- 首元素
hd : ∀ {d} → (Fin (suc d) → Trit) → Trit
hd f = f fzero

-- 尾函数
tl : ∀ {d} → (Fin (suc d) → Trit) → (Fin d → Trit)
tl f i = f (fsuc i)

-- 拼回
cons : ∀ {d} → Trit → (Fin d → Trit) → (Fin (suc d) → Trit)
cons a g fzero    = a
cons a g (fsuc i) = g i

-- 拆了再拼 = 原函数（点态）
cons-hd-tl : ∀ {d} (f : Fin (suc d) → Trit) (x : Fin (suc d)) →
  cons (hd f) (tl f) x ≡ f x
cons-hd-tl f fzero = refl
cons-hd-tl f (fsuc i) = refl

-- 拼了再拆 = 原对
hd-cons : ∀ {d} (a : Trit) (g : Fin d → Trit) → hd (cons a g) ≡ a
hd-cons a g = refl

tl-cons : ∀ {d} (a : Trit) (g : Fin d → Trit) (i : Fin d) → tl (cons a g) i ≡ g i
tl-cons a g i = refl

--------------------------------------------------------------------------------
-- §3. ★ 拆分同构（双向，点态）
--------------------------------------------------------------------------------

-- 正向：函数 ↦ (首元素, 尾函数)
splitF : ∀ {d} → (Fin (suc d) → Trit) → Trit × (Fin d → Trit)
splitF f = hd f , tl f

-- 反向：(首元素, 尾函数) ↦ 函数
joinF : ∀ {d} → Trit × (Fin d → Trit) → (Fin (suc d) → Trit)
joinF (a , g) = cons a g

-- 先拆后拼复原（点态）
split-join : ∀ {d} (p : Trit × (Fin d → Trit)) →
  (let (a , g) = p in hd (joinF p) ≡ a × (∀ i → tl (joinF p) i ≡ g i))
split-join (a , g) = refl , (λ i → refl)

-- 先拼后拆复原（点态）
join-split : ∀ {d} (f : Fin (suc d) → Trit) (x : Fin (suc d)) →
  joinF (splitF f) x ≡ f x
join-split f x = cons-hd-tl f x

--------------------------------------------------------------------------------
-- §4. ★★ base-3 编码：`Fin (3^d) ≅ (Fin d → Trit)`
--
-- 用 stdlib 的 `Data.Fin.Properties.*↔×`（`Fin (m * n) ↔ Fin m × Fin n`，**无需 funext**）
-- 递归构造：
--   `Fin (3^(d+1)) = Fin (3 * 3^d) ↪ Fin 3 × Fin (3^d) ↪ Fin 3 × (Fin d → Trit)`
--   再按「首元素 / 尾函数」拼成函数。
--
-- **不用** stdlib 的 `^↔→`（它需要 `Extensionality` ✗）；往返只在**点态**陈述 ✓。
--------------------------------------------------------------------------------

open import Data.Fin using (remQuot; combine)
open import Data.Fin.Properties using (combine-remQuot; remQuot-combine)
open import Data.Nat using (_∸_)

-- `Fin 3` 与 `Trit` 的三对互逆
fin3→trit : Fin 3 → Trit
fin3→trit fzero             = T₀
fin3→trit (fsuc fzero)      = T₁
fin3→trit (fsuc (fsuc x))   = T₂

trit→fin3 : Trit → Fin 3
trit→fin3 T₀ = fzero
trit→fin3 T₁ = fsuc fzero
trit→fin3 T₂ = fsuc (fsuc fzero)

trit→fin3→trit : ∀ t → fin3→trit (trit→fin3 t) ≡ t
trit→fin3→trit T₀ = refl
trit→fin3→trit T₁ = refl
trit→fin3→trit T₂ = refl

fin3→trit→fin3 : ∀ i → trit→fin3 (fin3→trit i) ≡ i
fin3→trit→fin3 fzero           = refl
fin3→trit→fin3 (fsuc fzero)    = refl
fin3→trit→fin3 (fsuc (fsuc fzero)) = refl

--------------------------------------------------------------------------------
-- §5. 编解码（互递归定义）
--------------------------------------------------------------------------------

-- 编码：函数 ↦ Fin (3^d)
fromFun : ∀ d → (Fin d → Trit) → Fin (3 ^ d)
fromFun zero f = fzero
fromFun (suc d) f =
  combine (trit→fin3 (hd f)) (fromFun d (tl f))

-- 解码：Fin (3^d) ↦ 函数
toFun : ∀ d → Fin (3 ^ d) → (Fin d → Trit)
toFun zero k = λ ()
toFun (suc d) k =
  cons (fin3→trit (proj₁ (remQuot {3} (3 ^ d) k)))
       (toFun d (proj₂ (remQuot {3} (3 ^ d) k)))

--------------------------------------------------------------------------------
-- §6. ★★ 往返（点态陈述，不需要 funext）
--------------------------------------------------------------------------------

-- 解了再编 = 原下标
fromFun-toFun : ∀ d (k : Fin (3 ^ d)) → fromFun d (toFun d k) ≡ k
fromFun-toFun zero k = lemma-fin1 k
  where
    lemma-fin1 : (k : Fin 1) → fzero ≡ k
    lemma-fin1 fzero = refl
fromFun-toFun (suc d) k =
  trans (cong₂ combine (trans (cong trit→fin3 (hd-cons-part k))
                              (fin3→trit→fin3 (proj₁ (remQuot {3} (3 ^ d) k))))
                        (fromFun-toFun d (proj₂ (remQuot {3} (3 ^ d) k))))
        (combine-remQuot {n = 3} (3 ^ d) k)
  where
    -- `hd (toFun (suc d) k)` 的定义展开
    hd-cons-part : ∀ (k : Fin (3 ^ suc d)) →
      hd (toFun (suc d) k) ≡ fin3→trit (proj₁ (remQuot {3} (3 ^ d) k))
    hd-cons-part k = refl

-- 两条投影引理（`remQuot` 与 `combine` 互逆）
proj1-remQuot : ∀ {d} (f : Fin (suc d) → Trit) →
  proj₁ (remQuot {3} (3 ^ d) (combine (trit→fin3 (hd f)) (fromFun d (tl f))))
  ≡ trit→fin3 (hd f)
proj1-remQuot {d} f =
  cong proj₁ (remQuot-combine {n = 3} {k = 3 ^ d} (trit→fin3 (hd f)) (fromFun d (tl f)))

proj2-remQuot : ∀ {d} (f : Fin (suc d) → Trit) →
  proj₂ (remQuot {3} (3 ^ d) (combine (trit→fin3 (hd f)) (fromFun d (tl f))))
  ≡ fromFun d (tl f)
proj2-remQuot {d} f =
  cong proj₂ (remQuot-combine {n = 3} {k = 3 ^ d} (trit→fin3 (hd f)) (fromFun d (tl f)))

-- 编了再解 = 原函数（点态）
toFun-fromFun : ∀ d (f : Fin d → Trit) (x : Fin d) →
  toFun d (fromFun d f) x ≡ f x
toFun-fromFun zero f ()
toFun-fromFun (suc d) f fzero =
  trans (cong (λ z → fin3→trit z) (proj1-remQuot f))
        (trit→fin3→trit (hd f))
toFun-fromFun (suc d) f (fsuc i) =
  trans (cong (λ z → toFun d z i) (proj2-remQuot f))
        (toFun-fromFun d (tl f) i)
