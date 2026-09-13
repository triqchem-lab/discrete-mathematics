{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Algebra.Representation.Maschke
--
-- 数学背景：Maschke 定理（有限域版）。
--   设有限群 G 作用在有限域 F 上的向量空间 V 上，若 char F ∤ |G|，
--   则任意 G-不变子空间 U ≤ V 都有 G-不变补 W（V = U ⊕ W）。
--   证明机制：平均投影 p = (1/|G|) Σ_{g∈G} ρ(g)。p 是 G-不变的幂等线性映射，
--   其像 im p = V^G（不动点集），核 ker p 即所求不变补。
--
-- 本模块先做**具体实例**（降低风险），再给**抽象分裂引理**（一般化）：
--   载体：C₃ = Fin 3（加法群 Z/3），域：GF(2) = Fin 2（char 2 ∤ 3）
--   表示：正则表示 ρ(g) = 3×3 循环置换矩阵（GF(2) 上）
--   不变子空间：U = span{(1,1,1)}（即 im p）
--   不变补：W = ker p = {(x₀,x₁,x₂) | x₀+x₁+x₂ = 0}（2 维）
--
-- 核心原则：
--   1. **1/|G| 必须显式**：GF(2) 上 3 ≡ 1（mod 2），故 1/|G| = 1/3 = 1；
--      这正是 char F ∤ |G| 的具体内容（`char2∤3`），平均投影才存在。
--   2. 投影 p 的三条性质（线性 / 幂等 / 与 ρ 交换）各自独立证明，
--      再由抽象引理一次性给出「分裂 + 两块都 G-不变 + 直和」。
--   3. 0 postulate / 0 hole：全部构造性闭合，算术用 `+₂` 的交换群律符号推导，
--      不对 F₂³ 做 64-case 穷举（>27 case 属暴力计算）。
--
-- 包含：GF(2) 加法群 C₂ 公理；V₃ = GF(2)³ 的向量空间公理；循环置换 σ 与
--       正则表示 ρ（含 9-case 同态性）；平均投影 p 的线性/幂等/交换性；
--       抽象分裂引理 `invariant-projection-splits`；具体 Maschke 结论包。

module Sovereign.Algebra.Representation.Maschke where

open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.Nat using (ℕ)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong; cong₂; module ≡-Reasoning)

infixl 6 _+₂_
infixl 6 _+ᵥ_

--------------------------------------------------------------------------------
-- §1. 基域 GF(2) = Fin 2（特征 2 的素域）
--------------------------------------------------------------------------------

-- 域载体：GF(2) 的两个元素
F2 : Set
F2 = Fin 2

O : F2
O = fzero

I : F2
I = fsuc fzero

-- 加法 = XOR（GF(2) 的加法群 ≅ C₂）
-- 定义按第一元分派，使 `O +₂ b ≡ b` 定义性成立
_+₂_ : F2 → F2 → F2
_+₂_ fzero b = b
_+₂_ (fsuc fzero) fzero = fsuc fzero
_+₂_ (fsuc fzero) (fsuc fzero) = fzero

-- 乘法（唯一非平凡情形：I 是单位元）
_*₂_ : F2 → F2 → F2
_*₂_ fzero _ = fzero
_*₂_ (fsuc fzero) b = b

+₂-idˡ : ∀ a → O +₂ a ≡ a
+₂-idˡ a = refl

+₂-idʳ : ∀ a → a +₂ O ≡ a
+₂-idʳ fzero = refl
+₂-idʳ (fsuc fzero) = refl

+₂-self : ∀ a → a +₂ a ≡ O
+₂-self fzero = refl
+₂-self (fsuc fzero) = refl

+₂-comm : ∀ a b → a +₂ b ≡ b +₂ a
+₂-comm fzero fzero = refl
+₂-comm fzero (fsuc fzero) = refl
+₂-comm (fsuc fzero) fzero = refl
+₂-comm (fsuc fzero) (fsuc fzero) = refl

+₂-assoc : ∀ a b c → (a +₂ b) +₂ c ≡ a +₂ (b +₂ c)
+₂-assoc fzero b c = refl
+₂-assoc (fsuc fzero) fzero c = refl
+₂-assoc (fsuc fzero) (fsuc fzero) fzero = refl
+₂-assoc (fsuc fzero) (fsuc fzero) (fsuc fzero) = refl

-- 中间换位：(x +₂ y) +₂ z ≡ (x +₂ z) +₂ y
+₂-mid : ∀ x y z → (x +₂ y) +₂ z ≡ (x +₂ z) +₂ y
+₂-mid x y z = begin
  (x +₂ y) +₂ z
    ≡⟨ +₂-assoc x y z ⟩
  x +₂ (y +₂ z)
    ≡⟨ cong (x +₂_) (+₂-comm y z) ⟩
  x +₂ (z +₂ y)
    ≡⟨ sym (+₂-assoc x z y) ⟩
  (x +₂ z) +₂ y
  ∎
  where open ≡-Reasoning

-- 四元换位（交换群的重排核心引理）
+₂-shuffle : ∀ a b c d → (a +₂ b) +₂ (c +₂ d) ≡ (a +₂ c) +₂ (b +₂ d)
+₂-shuffle a b c d = begin
  (a +₂ b) +₂ (c +₂ d)
    ≡⟨ +₂-assoc a b (c +₂ d) ⟩
  a +₂ (b +₂ (c +₂ d))
    ≡⟨ cong (a +₂_) (sym (+₂-assoc b c d)) ⟩
  a +₂ ((b +₂ c) +₂ d)
    ≡⟨ cong (a +₂_) (cong (_+₂ d) (+₂-comm b c)) ⟩
  a +₂ ((c +₂ b) +₂ d)
    ≡⟨ cong (a +₂_) (+₂-assoc c b d) ⟩
  a +₂ (c +₂ (b +₂ d))
    ≡⟨ sym (+₂-assoc a c (b +₂ d)) ⟩
  (a +₂ c) +₂ (b +₂ d)
  ∎
  where open ≡-Reasoning

--------------------------------------------------------------------------------
-- §2. 抽象 F₂-向量空间（特征 2 的加性群 = 初等阿贝尔 2-群）
--------------------------------------------------------------------------------

record F2Space (V : Set) : Set where
  field
    _+ᵥ_ : V → V → V
    0⃗ : V
    +ᵥ-assoc : ∀ u v w → (u +ᵥ v) +ᵥ w ≡ u +ᵥ (v +ᵥ w)
    +ᵥ-comm : ∀ u v → u +ᵥ v ≡ v +ᵥ u
    +ᵥ-idˡ : ∀ v → 0⃗ +ᵥ v ≡ v
    +ᵥ-self : ∀ v → v +ᵥ v ≡ 0⃗

--------------------------------------------------------------------------------
-- §3. 抽象分裂引理：G-不变幂等投影 ⟹ V = im p ⊕ ker p，两块都 G-不变
--------------------------------------------------------------------------------

module AbstractSplitting {V G : Set} (S : F2Space V) where
  open F2Space S

  -- 派生：右单位
  +ᵥ-idʳ : ∀ v → v +ᵥ 0⃗ ≡ v
  +ᵥ-idʳ v = trans (+ᵥ-comm v 0⃗) (+ᵥ-idˡ v)

  -- 抽象 Maschke 分裂引理
  invariant-projection-splits :
    ∀ (act : G → V → V) (p : V → V)
    → (∀ v w → p (v +ᵥ w) ≡ p v +ᵥ p w)                  -- p 线性
    → (∀ v → p (p v) ≡ p v)                               -- p 幂等
    → (∀ g v w → act g (v +ᵥ w) ≡ act g v +ᵥ act g w)     -- 作用线性
    → (∀ g v → p (act g v) ≡ act g (p v))                 -- p 与作用交换
    → (∀ v → v ≡ p v +ᵥ (v +ᵥ p v))                       -- V = im p + ker p
      × (∀ v → p (v +ᵥ p v) ≡ 0⃗)                          -- 第二块 ⊆ ker p
      × (∀ g v → act g (v +ᵥ p v) ≡ act g v +ᵥ p (act g v))  -- 第二块 G-不变
      × (∀ g v → p (act g (p v)) ≡ act g (p v))            -- 第一块 G-不变
      × (∀ u → p u ≡ u → p u ≡ 0⃗ → u ≡ 0⃗)                 -- 直和：im p ∩ ker p = 0
  invariant-projection-splits act p p-lin p-idem act-lin p-eq = split , ker , inv , im-inv , direct
    where
      open ≡-Reasoning

      -- p 0⃗ ≡ 0⃗（幂等 + 线性）
      p-zero-step : p 0⃗ +ᵥ p 0⃗ ≡ p 0⃗
      p-zero-step = trans (sym (p-lin 0⃗ 0⃗)) (cong p (+ᵥ-idˡ 0⃗))

      p-zero : p 0⃗ ≡ 0⃗
      p-zero = begin
        p 0⃗
          ≡⟨ sym (+ᵥ-idʳ (p 0⃗)) ⟩
        p 0⃗ +ᵥ 0⃗
          ≡⟨ cong (p 0⃗ +ᵥ_) (sym (+ᵥ-self (p 0⃗))) ⟩
        p 0⃗ +ᵥ (p 0⃗ +ᵥ p 0⃗)
          ≡⟨ cong (p 0⃗ +ᵥ_) p-zero-step ⟩
        p 0⃗ +ᵥ p 0⃗
          ≡⟨ +ᵥ-self (p 0⃗) ⟩
        0⃗
        ∎

      split : ∀ v → v ≡ p v +ᵥ (v +ᵥ p v)
      split v = sym (begin
        p v +ᵥ (v +ᵥ p v)
          ≡⟨ sym (+ᵥ-assoc (p v) v (p v)) ⟩
        (p v +ᵥ v) +ᵥ p v
          ≡⟨ cong (_+ᵥ p v) (+ᵥ-comm (p v) v) ⟩
        (v +ᵥ p v) +ᵥ p v
          ≡⟨ +ᵥ-assoc v (p v) (p v) ⟩
        v +ᵥ (p v +ᵥ p v)
          ≡⟨ cong (v +ᵥ_) (+ᵥ-self (p v)) ⟩
        v +ᵥ 0⃗
          ≡⟨ +ᵥ-idʳ v ⟩
        v
        ∎)

      ker : ∀ v → p (v +ᵥ p v) ≡ 0⃗
      ker v = trans (p-lin v (p v))
                    (trans (cong (p v +ᵥ_) (p-idem v)) (+ᵥ-self (p v)))

      inv : ∀ g v → act g (v +ᵥ p v) ≡ act g v +ᵥ p (act g v)
      inv g v = trans (act-lin g v (p v)) (cong (act g v +ᵥ_) (sym (p-eq g v)))

      im-inv : ∀ g v → p (act g (p v)) ≡ act g (p v)
      im-inv g v = trans (p-eq g (p v)) (cong (act g) (p-idem v))

      direct : ∀ u → p u ≡ u → p u ≡ 0⃗ → u ≡ 0⃗
      direct u pu≡u pu≡0 = trans (sym pu≡u) pu≡0

--------------------------------------------------------------------------------
-- §4. 具体载体 V₃ = GF(2)³
--------------------------------------------------------------------------------

record V3 : Set where
  constructor v3
  field x0 x1 x2 : F2

open V3

v3-ext : ∀ {a b c a' b' c'} → a ≡ a' → b ≡ b' → c ≡ c' → v3 a b c ≡ v3 a' b' c'
v3-ext refl refl refl = refl

0⃗ : V3
0⃗ = v3 O O O

-- 全一向量 1⃗（span{1⃗} 的生成元）
1⃗ : V3
1⃗ = v3 I I I

_+ᵥ_ : V3 → V3 → V3
v3 a b c +ᵥ v3 a' b' c' = v3 (a +₂ a') (b +₂ b') (c +₂ c')

-- 标量乘（F₂ 上的向量空间结构）
_·ᵥ_ : F2 → V3 → V3
fzero ·ᵥ _ = 0⃗
fsuc fzero ·ᵥ v = v

-- 坐标和（GF(2) 上的线性泛函）
sum : V3 → F2
sum (v3 a b c) = a +₂ (b +₂ c)

--------------------------------------------------------------------------------
-- §5. V₃ 的向量空间公理
--------------------------------------------------------------------------------

+ᵥ-assoc : ∀ u v w → (u +ᵥ v) +ᵥ w ≡ u +ᵥ (v +ᵥ w)
+ᵥ-assoc (v3 a b c) (v3 a' b' c') (v3 a'' b'' c'') =
  v3-ext (+₂-assoc a a' a'') (+₂-assoc b b' b'') (+₂-assoc c c' c'')

+ᵥ-comm : ∀ u v → u +ᵥ v ≡ v +ᵥ u
+ᵥ-comm (v3 a b c) (v3 a' b' c') =
  v3-ext (+₂-comm a a') (+₂-comm b b') (+₂-comm c c')

+ᵥ-idˡ : ∀ v → 0⃗ +ᵥ v ≡ v
+ᵥ-idˡ (v3 a b c) = v3-ext (+₂-idˡ a) (+₂-idˡ b) (+₂-idˡ c)

+ᵥ-self : ∀ v → v +ᵥ v ≡ 0⃗
+ᵥ-self (v3 a b c) = v3-ext (+₂-self a) (+₂-self b) (+₂-self c)

-- 向量空间结构实例（供抽象分裂引理使用）
V3Space : F2Space V3
V3Space = record
  { _+ᵥ_ = _+ᵥ_
  ; 0⃗ = 0⃗
  ; +ᵥ-assoc = +ᵥ-assoc
  ; +ᵥ-comm = +ᵥ-comm
  ; +ᵥ-idˡ = +ᵥ-idˡ
  ; +ᵥ-self = +ᵥ-self
  }

-- 坐标和的可加性（符号推导，不用 64-case 穷举）
sum-add : ∀ v w → sum (v +ᵥ w) ≡ sum v +₂ sum w
sum-add (v3 a b c) (v3 a' b' c') = begin
  (a +₂ a') +₂ ((b +₂ b') +₂ (c +₂ c'))
    ≡⟨ cong ((a +₂ a') +₂_) (+₂-shuffle b b' c c') ⟩
  (a +₂ a') +₂ ((b +₂ c) +₂ (b' +₂ c'))
    ≡⟨ sym (+₂-assoc (a +₂ a') (b +₂ c) (b' +₂ c')) ⟩
  ((a +₂ a') +₂ (b +₂ c)) +₂ (b' +₂ c')
    ≡⟨ cong (_+₂ (b' +₂ c')) (+₂-mid a a' (b +₂ c)) ⟩
  ((a +₂ (b +₂ c)) +₂ a') +₂ (b' +₂ c')
    ≡⟨ +₂-assoc (a +₂ (b +₂ c)) a' (b' +₂ c') ⟩
  (a +₂ (b +₂ c)) +₂ (a' +₂ (b' +₂ c'))
  ∎
  where open ≡-Reasoning

--------------------------------------------------------------------------------
-- §6. 平均投影 p = (1/|G|) Σ_g ρ(g)
--------------------------------------------------------------------------------

-- 群阶 |G| = 3 在 GF(2) 中的像
|G|₂ : F2
|G|₂ = I +₂ (I +₂ I)

-- GF(2) 上 3 ≡ 1：这是「char F ∤ |G|」的具体内容
|G|₂≡I : |G|₂ ≡ I
|G|₂≡I = refl

-- 逆元 1/|G| = 1/3 = 1
inv-|G| : F2
inv-|G| = I

-- (1/|G|)·|G| = 1（平均投影存在性的关键等式）
inv-|G|-spec : inv-|G| *₂ |G|₂ ≡ I
inv-|G|-spec = refl

-- char 2 ∤ 3：3 ≠ 0 in GF(2)
char2∤3 : |G|₂ ≢ O
char2∤3 = λ ()

-- 投影 p（GF(2) 上 1/3 = 1，故 p 就是平均算子本身）
p : V3 → V3
p (v3 a b c) = v3 (a +₂ (b +₂ c)) (a +₂ (b +₂ c)) (a +₂ (b +₂ c))

sum-p : ∀ v → sum (p v) ≡ sum v
sum-p (v3 a b c) = begin
  (a +₂ (b +₂ c)) +₂ ((a +₂ (b +₂ c)) +₂ (a +₂ (b +₂ c)))
    ≡⟨ cong ((a +₂ (b +₂ c)) +₂_) (+₂-self (a +₂ (b +₂ c))) ⟩
  (a +₂ (b +₂ c)) +₂ O
    ≡⟨ +₂-idʳ (a +₂ (b +₂ c)) ⟩
  a +₂ (b +₂ c)
  ∎
  where open ≡-Reasoning

p-idem : ∀ v → p (p v) ≡ p v
p-idem (v3 a b c) = v3-ext lem lem lem
  where
    lem : (a +₂ (b +₂ c)) +₂ ((a +₂ (b +₂ c)) +₂ (a +₂ (b +₂ c)))
        ≡ a +₂ (b +₂ c)
    lem = begin
      s +₂ (s +₂ s)
        ≡⟨ cong (s +₂_) (+₂-self s) ⟩
      s +₂ O
        ≡⟨ +₂-idʳ s ⟩
      s
      ∎
      where
        s = a +₂ (b +₂ c)
        open ≡-Reasoning

p-linear : ∀ v w → p (v +ᵥ w) ≡ p v +ᵥ p w
p-linear v w = cong (λ z → v3 z z z) (sum-add v w)

p-zero : p 0⃗ ≡ 0⃗
p-zero = refl

--------------------------------------------------------------------------------
-- §7. 循环置换 σ 与正则表示 ρ : C₃ → GL(V₃)
--------------------------------------------------------------------------------

σ : V3 → V3
σ (v3 a b c) = v3 c a b

σ³ : ∀ v → σ (σ (σ v)) ≡ v
σ³ (v3 a b c) = refl

-- σ 保持坐标和（符号推导）
sum-σ : ∀ v → sum (σ v) ≡ sum v
sum-σ (v3 a b c) = begin
  c +₂ (a +₂ b)
    ≡⟨ cong (c +₂_) (+₂-comm a b) ⟩
  c +₂ (b +₂ a)
    ≡⟨ sym (+₂-assoc c b a) ⟩
  (c +₂ b) +₂ a
    ≡⟨ cong (_+₂ a) (+₂-comm c b) ⟩
  (b +₂ c) +₂ a
    ≡⟨ +₂-comm (b +₂ c) a ⟩
  a +₂ (b +₂ c)
  ∎
  where open ≡-Reasoning

-- σ 固定 p 的像（全等坐标向量）
σ-fix : ∀ v → σ (p v) ≡ p v
σ-fix (v3 a b c) = refl

p-σ : ∀ v → p (σ v) ≡ p v
p-σ v = trans (cong (λ z → v3 z z z) (sum-σ v)) (sym (σ-fix v))

-- C₃ = Z/3 的加法（Fin 3 上）
_+₃_ : Fin 3 → Fin 3 → Fin 3
_+₃_ fzero b = b
_+₃_ (fsuc fzero) fzero = fsuc fzero
_+₃_ (fsuc fzero) (fsuc fzero) = fsuc (fsuc fzero)
_+₃_ (fsuc fzero) (fsuc (fsuc fzero)) = fzero
_+₃_ (fsuc (fsuc fzero)) fzero = fsuc (fsuc fzero)
_+₃_ (fsuc (fsuc fzero)) (fsuc fzero) = fzero
_+₃_ (fsuc (fsuc fzero)) (fsuc (fsuc fzero)) = fsuc fzero

-- 正则表示 ρ(g) = 循环置换矩阵
ρ : Fin 3 → V3 → V3
ρ fzero v = v
ρ (fsuc fzero) v = σ v
ρ (fsuc (fsuc fzero)) v = σ (σ v)

-- ρ 是群同态（9 case refl）
ρ-homo : ∀ g h v → ρ (g +₃ h) v ≡ ρ g (ρ h v)
ρ-homo fzero h v = refl
ρ-homo (fsuc fzero) fzero v = refl
ρ-homo (fsuc fzero) (fsuc fzero) v = refl
ρ-homo (fsuc fzero) (fsuc (fsuc fzero)) v = refl
ρ-homo (fsuc (fsuc fzero)) fzero v = refl
ρ-homo (fsuc (fsuc fzero)) (fsuc fzero) v = refl
ρ-homo (fsuc (fsuc fzero)) (fsuc (fsuc fzero)) v = refl

-- ρ(g) 线性
ρ-add : ∀ g v w → ρ g (v +ᵥ w) ≡ ρ g v +ᵥ ρ g w
ρ-add fzero v w = refl
ρ-add (fsuc fzero) (v3 a b c) (v3 a' b' c') = refl
ρ-add (fsuc (fsuc fzero)) (v3 a b c) (v3 a' b' c') = refl

ρ-zero : ∀ g → ρ g 0⃗ ≡ 0⃗
ρ-zero fzero = refl
ρ-zero (fsuc fzero) = refl
ρ-zero (fsuc (fsuc fzero)) = refl

-- ρ(g) 保持坐标和（故 ker p 是 G-不变子空间）
sum-ρ : ∀ g v → sum (ρ g v) ≡ sum v
sum-ρ fzero v = refl
sum-ρ (fsuc fzero) v = sum-σ v
sum-ρ (fsuc (fsuc fzero)) v = trans (sum-σ (σ v)) (sum-σ v)

-- p 与 ρ 交换（平均投影的等变性）
p-equiv : ∀ g v → p (ρ g v) ≡ ρ g (p v)
p-equiv fzero v = refl
p-equiv (fsuc fzero) v = p-σ v
p-equiv (fsuc (fsuc fzero)) v = trans (p-σ (σ v)) (cong σ (p-σ v))

-- ρ(g) 固定 p 的像（U = span{1⃗} 是 G-不变子空间）
ρ-fix-p : ∀ g v → ρ g (p v) ≡ p v
ρ-fix-p fzero v = refl
ρ-fix-p (fsuc fzero) v = σ-fix v
ρ-fix-p (fsuc (fsuc fzero)) v = refl

--------------------------------------------------------------------------------
-- §8. 平均投影 = Σ_g ρ(g)（因 1/3 = 1）
--------------------------------------------------------------------------------

avg : V3 → V3
avg v = ρ fzero v +ᵥ ρ (fsuc fzero) v +ᵥ ρ (fsuc (fsuc fzero)) v

-- 平均算子在 GF(2) 上恰等于 p（1/|G| = 1）
avg≡p : ∀ v → avg v ≡ p v
avg≡p (v3 a b c) = v3-ext c0 c1 c2
  where
    open ≡-Reasoning
    c0 : (a +₂ c) +₂ b ≡ a +₂ (b +₂ c)
    c0 = begin
      (a +₂ c) +₂ b
        ≡⟨ +₂-assoc a c b ⟩
      a +₂ (c +₂ b)
        ≡⟨ cong (a +₂_) (+₂-comm c b) ⟩
      a +₂ (b +₂ c)
      ∎
    c1 : (b +₂ a) +₂ c ≡ a +₂ (b +₂ c)
    c1 = begin
      (b +₂ a) +₂ c
        ≡⟨ +₂-assoc b a c ⟩
      b +₂ (a +₂ c)
        ≡⟨ cong (b +₂_) (+₂-comm a c) ⟩
      b +₂ (c +₂ a)
        ≡⟨ sym (+₂-assoc b c a) ⟩
      (b +₂ c) +₂ a
        ≡⟨ +₂-comm (b +₂ c) a ⟩
      a +₂ (b +₂ c)
      ∎
    c2 : (c +₂ b) +₂ a ≡ a +₂ (b +₂ c)
    c2 = begin
      (c +₂ b) +₂ a
        ≡⟨ +₂-assoc c b a ⟩
      c +₂ (b +₂ a)
        ≡⟨ cong (c +₂_) (+₂-comm b a) ⟩
      c +₂ (a +₂ b)
        ≡⟨ sym (+₂-assoc c a b) ⟩
      (c +₂ a) +₂ b
        ≡⟨ cong (_+₂ b) (+₂-comm c a) ⟩
      (a +₂ c) +₂ b
        ≡⟨ +₂-assoc a c b ⟩
      a +₂ (c +₂ b)
        ≡⟨ cong (a +₂_) (+₂-comm c b) ⟩
      a +₂ (b +₂ c)
      ∎

--------------------------------------------------------------------------------
-- §9. 具体 Maschke 结论
--------------------------------------------------------------------------------

-- 补空间 W = ker p = {v | sum v ≡ O}
sum-compl : ∀ v → sum (v +ᵥ p v) ≡ O
sum-compl v = begin
  sum (v +ᵥ p v)
    ≡⟨ sum-add v (p v) ⟩
  sum v +₂ sum (p v)
    ≡⟨ cong (sum v +₂_) (sum-p v) ⟩
  sum v +₂ sum v
    ≡⟨ +₂-self (sum v) ⟩
  O
  ∎
  where open ≡-Reasoning

-- ker p 的刻画
p-ker : ∀ v → sum v ≡ O → p v ≡ 0⃗
p-ker (v3 a b c) e = cong (λ z → v3 z z z) e

ker-p : ∀ v → p v ≡ 0⃗ → sum v ≡ O
ker-p (v3 a b c) e = trans (sym (sum-p (v3 a b c))) (trans (cong sum e) refl)

-- ker p 是 G-不变子空间
ker-invariant : ∀ g v → sum v ≡ O → sum (ρ g v) ≡ O
ker-invariant g v e = trans (sum-ρ g v) e

-- U ∩ W = {0}
im-ker-zero : ∀ u → p u ≡ u → sum u ≡ O → u ≡ 0⃗
im-ker-zero u pu≡u su≡O = trans (sym pu≡u) (p-ker u su≡O)

-- 抽象分裂引理在具体实例上的实例化
concrete-splitting :
  (∀ v → v ≡ p v +ᵥ (v +ᵥ p v))
  × (∀ v → p (v +ᵥ p v) ≡ 0⃗)
  × (∀ g v → ρ g (v +ᵥ p v) ≡ ρ g v +ᵥ p (ρ g v))
  × (∀ g v → p (ρ g (p v)) ≡ ρ g (p v))
  × (∀ u → p u ≡ u → p u ≡ 0⃗ → u ≡ 0⃗)
concrete-splitting = AbstractSplitting.invariant-projection-splits V3Space ρ p p-linear p-idem ρ-add p-equiv

-- **Maschke 定理（具体实例）**：
--   C₃ 在 GF(2)³ 上的正则表示中，不变子空间 U = span{1⃗} = im p
--   有 G-不变补 W = ker p（2 维），且 V = U ⊕ W。
maschke-C3-GF2 :
  (∀ g v → ρ g (p v) ≡ p v)                            -- U 是 G-不变
  × (∀ v → v ≡ p v +ᵥ (v +ᵥ p v))                      -- V = U + W
  × (∀ v → p (v +ᵥ p v) ≡ 0⃗)                          -- W ⊆ ker p
  × (∀ g v → sum (ρ g (v +ᵥ p v)) ≡ sum (v +ᵥ p v))    -- W 是 G-不变
  × (∀ v → sum (v +ᵥ p v) ≡ O)                         -- W 由「坐标和为 0」刻画（2 维）
  × (∀ u → p u ≡ u → sum u ≡ O → u ≡ 0⃗)                -- U ∩ W = {0}
maschke-C3-GF2 = ρ-fix-p , split , ker , inv , compl , direct
  where
    split = proj₁ concrete-splitting
    ker = proj₁ (proj₂ concrete-splitting)
    inv : ∀ g v → sum (ρ g (v +ᵥ p v)) ≡ sum (v +ᵥ p v)
    inv g v = sum-ρ g (v +ᵥ p v)
    compl = sum-compl
    direct = im-ker-zero

--------------------------------------------------------------------------------
-- §10. 对抗验证：具体点上的独立 refl 计算
--------------------------------------------------------------------------------

-- 投影在全一向量上不动：p 1⃗ = 1⃗
_p-1⃗ : p 1⃗ ≡ 1⃗
_p-1⃗ = refl

-- 投影在 0 上为 0
_p-0⃗ : p 0⃗ ≡ 0⃗
_p-0⃗ = refl

-- 幂等性在 e₀ = (1,0,0) 上的实例
_p-idem-e0 : p (p (v3 I O O)) ≡ p (v3 I O O)
_p-idem-e0 = refl

-- 等变性在 g=1, v=(1,0,0) 上的实例
_p-equiv-1 : p (ρ (fsuc fzero) (v3 I O O)) ≡ ρ (fsuc fzero) (p (v3 I O O))
_p-equiv-1 = refl

-- 补空间实例：v = (1,0,0)，v + p v = (0,1,1)，其坐标和为 0
_compl-e0 : sum ((v3 I O O) +ᵥ p (v3 I O O)) ≡ O
_compl-e0 = refl

-- 平均投影实例：avg (1,0,0) = (1,1,1) = p (1,0,0)
_avg-e0 : avg (v3 I O O) ≡ p (v3 I O O)
_avg-e0 = refl

-- 1/|G| 实例：(1/3)·3 = 1
_inv-|G| : inv-|G| *₂ |G|₂ ≡ I
_inv-|G| = refl

-- 3 ≠ 0（char 2 ∤ 3）的否定证明
_3≠0 : |G|₂ ≢ O
_3≠0 = char2∤3
