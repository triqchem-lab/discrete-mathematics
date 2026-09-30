{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Structology.A4GenWords
-- A₄ 的生成元词表示 + 离散路径桥 — 把 12×12 同态穷举符号化为
--   生成元对引理 (≤27 案) + 词归纳传播
--
-- 核心原则:
--   1. A₄ = ⟨gs, gt⟩, gs = Rot 3 0 = (0 1 2), gt = Rot 0 0 = (1 2 3)
--      (精确整数计算验证: 右乘追加 BFS 覆盖 12/12, 词值 = 有序乘积,
--       与 ev 的右嵌套求值逐条一致 — 见 wordOf 表)
--   2. ev : Word → A4 把词右嵌套求值 ev (c ▸ w) = gen c ⊗ ev w;
--      ev-wordOf : ∀ g → ev (wordOf g) ≡ g  (12 案 refl, 全具体归约)
--   3. 离散类型 (Fin 1..4, A4) 的 Cubical 路径 → 命题相等桥 pathToEq*:
--      由 A4Group.assoc / fromPerm-perm (Cubical Path) 得到命题相等
--      ⊗-assocₚ / fromPerm-permₚ, 供 PropEq 模块做词归纳传播
--   4. 单引理 refl ≤27; 0 postulate / 0 hole
--
-- 包含: Gen/gen, Word/ev/wordOf/ev-wordOf, pathToEqFin1..4, pathToEqA4,
--       ⊗-assocₚ, fromPerm-permₚ

module Sovereign.Structology.A4GenWords where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin using (Fin; zero; suc)
open import Data.Nat using (ℕ) renaming (suc to sucℕ)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; cong₂)

-- Cubical 路径 (只用于桥接层; 本模块下游全部使用命题相等)
import Cubical.Foundations.Prelude as C

open import Sovereign.Structology.A4Group
  using (A4; Id; Rot; Flip; _⊗_; perm; fromPerm; fromPerm-perm; assoc)

--------------------------------------------------------------------------------
-- §1. 离散类型桥: Cubical 路径 → 命题相等
--   离散类型 (有限 data) 的任意路径都连接定义相等的项;
--   对角线 refl, 非对角线经构造子消去族 (⊤/⊥) 归谬。
--------------------------------------------------------------------------------

-- 顶层构造子消去族 (泛化 n, 供 Fin (suc n) 使用)
zeroF : ∀ {n} → Fin (sucℕ n) → Set
zeroF zero    = ⊤
zeroF (suc _) = ⊥

-- Fin 1 (仅 zero 一个构造子)
pathToEqFin1 : ∀ {a b : Fin 1} → C._≡_ a b → a ≡ b
pathToEqFin1 {zero} {zero} p = refl

-- Fin 2
predFin2 : Fin 2 → Fin 1
predFin2 zero    = zero
predFin2 (suc k) = k

pathToEqFin2 : ∀ {a b : Fin 2} → C._≡_ a b → a ≡ b
pathToEqFin2 {zero}    {zero}    p = refl
pathToEqFin2 {zero}    {suc b}   p = ⊥-elim (C.subst zeroF p tt)
pathToEqFin2 {suc a}   {zero}    p = ⊥-elim (C.subst zeroF (C.sym p) tt)
pathToEqFin2 {suc a}   {suc b}   p = cong suc (pathToEqFin1 (C.cong predFin2 p))

-- Fin 3
predFin3 : Fin 3 → Fin 2
predFin3 zero    = zero
predFin3 (suc k) = k

pathToEqFin3 : ∀ {a b : Fin 3} → C._≡_ a b → a ≡ b
pathToEqFin3 {zero}    {zero}    p = refl
pathToEqFin3 {zero}    {suc b}   p = ⊥-elim (C.subst zeroF p tt)
pathToEqFin3 {suc a}   {zero}    p = ⊥-elim (C.subst zeroF (C.sym p) tt)
pathToEqFin3 {suc a}   {suc b}   p = cong suc (pathToEqFin2 (C.cong predFin3 p))

-- Fin 4
predFin4 : Fin 4 → Fin 3
predFin4 zero    = zero
predFin4 (suc k) = k

pathToEqFin4 : ∀ {a b : Fin 4} → C._≡_ a b → a ≡ b
pathToEqFin4 {zero}    {zero}    p = refl
pathToEqFin4 {zero}    {suc b}   p = ⊥-elim (C.subst zeroF p tt)
pathToEqFin4 {suc a}   {zero}    p = ⊥-elim (C.subst zeroF (C.sym p) tt)
pathToEqFin4 {suc a}   {suc b}   p = cong suc (pathToEqFin3 (C.cong predFin4 p))

-- A₄ 构造子消去族
isId : A4 → Set
isId Id         = ⊤
isId (Rot _ _)  = ⊥
isId (Flip _)   = ⊥

isRot : A4 → Set
isRot Id        = ⊥
isRot (Rot _ _) = ⊤
isRot (Flip _)  = ⊥

-- Rot / Flip 的索引投影 (用于把 A₄ 路径降到 Fin 路径)
rotFst : A4 → Fin 4
rotFst (Rot i _) = i
rotFst _         = zero

rotSnd : A4 → Fin 2
rotSnd (Rot _ j) = j
rotSnd _         = zero

flipFst : A4 → Fin 3
flipFst (Flip k) = k
flipFst _        = zero

-- A₄ 路径桥 (9 案: 3 个对角线 + 6 个非对角线归谬)
pathToEqA4 : ∀ {a b : A4} → C._≡_ a b → a ≡ b
pathToEqA4 {Id}        {Id}        p = refl
pathToEqA4 {Id}        {Rot i j}   p = ⊥-elim (C.subst isId p tt)
pathToEqA4 {Id}        {Flip k}    p = ⊥-elim (C.subst isId p tt)
pathToEqA4 {Rot i j}   {Id}        p = ⊥-elim (C.subst isId (C.sym p) tt)
pathToEqA4 {Rot i j}   {Rot i′ j′} p =
  cong₂ Rot (pathToEqFin4 (C.cong rotFst p)) (pathToEqFin2 (C.cong rotSnd p))
pathToEqA4 {Rot i j}   {Flip k}    p = ⊥-elim (C.subst isRot p tt)
pathToEqA4 {Flip k}    {Id}        p = ⊥-elim (C.subst isId (C.sym p) tt)
pathToEqA4 {Flip k}    {Rot i j}   p = ⊥-elim (C.subst isRot (C.sym p) tt)
pathToEqA4 {Flip k}    {Flip k′}   p = cong Flip (pathToEqFin3 (C.cong flipFst p))

--------------------------------------------------------------------------------
-- §2. 命题相等版群律 (经桥接, 供 PropEq 模块做词归纳)
--------------------------------------------------------------------------------

-- 结合律: A4Group.assoc (Cubical) → 命题相等
⊗-assocₚ : ∀ (x y z : A4) → (x ⊗ y) ⊗ z ≡ x ⊗ (y ⊗ z)
⊗-assocₚ x y z = pathToEqA4 (assoc x y z)

-- fromPerm ∘ perm ≡ id: A4Group.fromPerm-perm (Cubical) → 命题相等
fromPerm-permₚ : ∀ (x : A4) → fromPerm (perm x) ≡ x
fromPerm-permₚ x = pathToEqA4 (fromPerm-perm x)

--------------------------------------------------------------------------------
-- §3. 生成元词: A₄ = ⟨gs, gt⟩
--   gs = Rot 3 0 = (0 1 2), gt = Rot 0 0 = (1 2 3)
--   词值 = 有序乘积 (结合律保证右嵌套 = 左嵌套)
--------------------------------------------------------------------------------

data Gen : Set where
  gs gt : Gen

gen : Gen → A4
gen gs = Rot (suc (suc (suc zero))) zero   -- (0 1 2)
gen gt = Rot zero zero                     -- (1 2 3)

infixr 5 _▸_

data Word : Set where
  ε   : Word
  _▸_ : Gen → Word → Word

ev : Word → A4
ev ε       = Id
ev (c ▸ w) = gen c ⊗ ev w

-- 12 个元素的规范词 (精确整数计算求得最短词, 逐条经 ev 校验)
wordOf : A4 → Word
wordOf Id                                = ε
wordOf (Rot zero zero)                   = gt ▸ ε
wordOf (Rot zero (suc zero))             = gt ▸ gt ▸ ε
wordOf (Rot (suc zero) zero)             = gs ▸ gs ▸ gt ▸ ε
wordOf (Rot (suc zero) (suc zero))       = gt ▸ gt ▸ gs ▸ ε
wordOf (Rot (suc (suc zero)) zero)       = gs ▸ gt ▸ gt ▸ ε
wordOf (Rot (suc (suc zero)) (suc zero)) = gt ▸ gs ▸ gs ▸ ε
wordOf (Rot (suc (suc (suc zero))) zero) = gs ▸ ε
wordOf (Rot (suc (suc (suc zero))) (suc zero)) = gs ▸ gs ▸ ε
wordOf (Flip zero)                       = gs ▸ gt ▸ ε
wordOf (Flip (suc zero))                 = gt ▸ gs ▸ ε
wordOf (Flip (suc (suc zero)))           = gs ▸ gt ▸ gt ▸ gs ▸ ε

-- 覆盖引理: 每个元素都由自己的规范词求值得到 (12 案 refl, 全具体归约)
ev-wordOf : ∀ (g : A4) → ev (wordOf g) ≡ g
ev-wordOf Id                                = refl
ev-wordOf (Rot zero zero)                   = refl
ev-wordOf (Rot zero (suc zero))             = refl
ev-wordOf (Rot (suc zero) zero)             = refl
ev-wordOf (Rot (suc zero) (suc zero))       = refl
ev-wordOf (Rot (suc (suc zero)) zero)       = refl
ev-wordOf (Rot (suc (suc zero)) (suc zero)) = refl
ev-wordOf (Rot (suc (suc (suc zero))) zero) = refl
ev-wordOf (Rot (suc (suc (suc zero))) (suc zero)) = refl
ev-wordOf (Flip zero)                       = refl
ev-wordOf (Flip (suc zero))                 = refl
ev-wordOf (Flip (suc (suc zero)))           = refl

-- 0 postulate.
