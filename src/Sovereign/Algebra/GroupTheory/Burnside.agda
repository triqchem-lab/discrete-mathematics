{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Algebra.GroupTheory.Burnside
--
-- Burnside（Cauchy–Frobenius）引理的**双重计数**这一步：
--       Σ_{g : G} |Fix g|  ≡  Σ_{x : X} |Stab x|
-- 它是 Burnside 恒等式  n × #orbits ≡ Σ_g |Fix g|  的第一块（第二块 = 共轭不变 + 轨道划分）。
--
-- 数学背景：
--   两边都在数同一个集合 —— 「对 (g, x) 且 g·x = x」的二元组个数：
--   按 g 分行数是 Σ_g |Fix g|，按 x 分列数是 Σ_x |Stab x|。
--   因此本模块证的是一个**求和交换引理**（Fubini），而不是两个数碰巧相等。
--
-- 为什么不能直接写 refl：
--   |Fix g| 与 |Stab x| 都是 CosetAuto.enum 的 size 字段，是**算出来的**（对具体作用
--   归一化到具体数字），而 enum 的 size 由 with 分支定义；要在符号层面交换求和次序，
--   必须先把 size 的结构暴露出来 —— §2 的 size-suc / size-as-count 就是干这个的。
--
-- 核心原则：
--   1. 两个计数都是算出来的（§5 实测：C₄ 正则 4 = 4，C₄ 奇偶 4 = 4）
--   2. 交换次序靠三条结构引理，不靠 hunch：size-suc（展开 enum 一步）、
--      size-as-count（size = 命中计数）、sumFin-+（求和分配）
--   3. 0 postulate / 0 hole；无 funExt
--
-- 包含：sumFin / sumFin-cong / +-interchange' / sumFin-+ / bit
--       size-suc / size-as-count / sum-swap（Fubini）
--       fixSize / stabSize / fixCount / stabCount / burnside-double-count

module Sovereign.Algebra.GroupTheory.Burnside where

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.Fin.Properties using (_≟_; cantor-schröder-bernstein)
open import Function.Definitions using (Injective)
open import Data.Nat.Properties using (+-assoc; +-comm)
open import Relation.Nullary.Decidable using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; subst; module ≡-Reasoning)

open import Sovereign.Algebra.GroupTheory.Lagrange using (FinGroup)
open import Sovereign.Algebra.GroupTheory.CosetAuto using (SubEnum; enum)
open import Sovereign.Algebra.GroupTheory.OrbitStabilizer using (Action)

--------------------------------------------------------------------------------
-- §1. 有限求和（Fin n → ℕ）
--------------------------------------------------------------------------------

sumFin : ∀ {n} → (Fin n → ℕ) → ℕ
sumFin {zero}  f = zero
sumFin {suc n} f = f fzero + sumFin (λ i → f (fsuc i))

sumFin-cong : ∀ {n} {f g : Fin n → ℕ} → (∀ i → f i ≡ g i) → sumFin f ≡ sumFin g
sumFin-cong {zero}  h = refl
sumFin-cong {suc n} {f} {g} h =
  trans (cong (f fzero +_) (sumFin-cong (λ i → h (fsuc i))))
        (cong (_+ sumFin (λ i → g (fsuc i))) (h fzero))

-- (a + b) + (c + d) ≡ (a + c) + (b + d)
+-interchange' : ∀ a b c d → (a + b) + (c + d) ≡ (a + c) + (b + d)
+-interchange' a b c d = begin
  (a + b) + (c + d)   ≡⟨ +-assoc a b (c + d) ⟩
  a + (b + (c + d))   ≡⟨ cong (a +_) (sym (+-assoc b c d)) ⟩
  a + ((b + c) + d)   ≡⟨ cong (a +_) (cong (_+ d) (+-comm b c)) ⟩
  a + ((c + b) + d)   ≡⟨ cong (a +_) (+-assoc c b d) ⟩
  a + (c + (b + d))   ≡⟨ sym (+-assoc a c (b + d)) ⟩
  (a + c) + (b + d)   ∎
  where open ≡-Reasoning

sumFin-+ : ∀ {n} (f g : Fin n → ℕ) → sumFin (λ i → f i + g i) ≡ sumFin f + sumFin g
sumFin-+ {zero}  f g = refl
sumFin-+ {suc n} f g =
  trans (cong ((f fzero + g fzero) +_)
              (sumFin-+ (λ i → f (fsuc i)) (λ i → g (fsuc i))))
        (+-interchange' (f fzero) (g fzero)
                        (sumFin (λ i → f (fsuc i))) (sumFin (λ i → g (fsuc i))))

-- 全零求和为 0（对索引个数归纳；不能靠 refl：sumFin 对变量索引不归约）
sumFin-zero : ∀ {n} (f : Fin n → ℕ) → (∀ i → f i ≡ 0) → sumFin f ≡ 0
sumFin-zero {zero}  f h = refl
sumFin-zero {suc n} f h =
  trans (cong (_+ sumFin (λ i → f (fsuc i))) (h fzero))
        (sumFin-zero (λ i → f (fsuc i)) (λ i → h (fsuc i)))

-- 判定结果的 0/1 编码
bit : ∀ {A : Set} → Dec A → ℕ
bit (yes _) = 1
bit (no _)  = 0

--------------------------------------------------------------------------------
-- §2. enum 的 size 结构（承重：把 with 分支暴露成等式）
--------------------------------------------------------------------------------

-- 展开一步：Fin (suc n) 上的枚举 = 「fzero 是否命中」+ 尾部枚举
size-suc : ∀ {n} (P : Fin (suc n) → Set) (dec : ∀ i → Dec (P i))
         → SubEnum.size (enum P dec)
         ≡ bit (dec fzero) + SubEnum.size (enum (λ i → P (fsuc i)) (λ i → dec (fsuc i)))
size-suc P dec with dec fzero
... | yes _ = refl
... | no _  = refl

-- size 就是命中计数
size-as-count : ∀ {n} (P : Fin n → Set) (dec : ∀ i → Dec (P i))
              → SubEnum.size (enum P dec) ≡ sumFin (λ i → bit (dec i))
size-as-count {zero}  P dec = refl
size-as-count {suc n} P dec =
  trans (size-suc P dec)
        (cong (bit (dec fzero) +_)
              (size-as-count (λ i → P (fsuc i)) (λ i → dec (fsuc i))))

--------------------------------------------------------------------------------
-- §3. Fubini：按行求和 ≡ 按列求和
--------------------------------------------------------------------------------

-- 列分解：按 x 求和 = 「fzero 行命中数」+「去掉 fzero 行后的列和」
col-decomp : ∀ {n p} (P : Fin (suc n) → Fin p → Set) (dec : ∀ g x → Dec (P g x))
           → sumFin (λ x → SubEnum.size (enum (λ g → P g x) (λ g → dec g x)))
           ≡ SubEnum.size (enum (P fzero) (dec fzero))
             + sumFin (λ x → SubEnum.size (enum (λ g → P (fsuc g) x)
                                                 (λ g → dec (fsuc g) x)))
col-decomp {n} {p} P dec = begin
  sumFin (λ x → SubEnum.size (enum (λ g → P g x) (λ g → dec g x)))
    ≡⟨ sumFin-cong (λ x → size-suc (λ g → P g x) (λ g → dec g x)) ⟩
  sumFin (λ x → bit (dec fzero x)
                + SubEnum.size (enum (λ g → P (fsuc g) x) (λ g → dec (fsuc g) x)))
    ≡⟨ sumFin-+ (λ x → bit (dec fzero x))
                (λ x → SubEnum.size (enum (λ g → P (fsuc g) x)
                                           (λ g → dec (fsuc g) x))) ⟩
  sumFin (λ x → bit (dec fzero x))
    + sumFin (λ x → SubEnum.size (enum (λ g → P (fsuc g) x)
                                        (λ g → dec (fsuc g) x)))
    ≡⟨ cong (_+ sumFin (λ x → SubEnum.size (enum (λ g → P (fsuc g) x)
                                                 (λ g → dec (fsuc g) x))))
            (sym (size-as-count (P fzero) (dec fzero))) ⟩
  SubEnum.size (enum (P fzero) (dec fzero))
    + sumFin (λ x → SubEnum.size (enum (λ g → P (fsuc g) x)
                                        (λ g → dec (fsuc g) x)))
    ∎
  where open ≡-Reasoning

sum-swap : ∀ {n p} (P : Fin n → Fin p → Set) (dec : ∀ g x → Dec (P g x))
         → sumFin (λ g → SubEnum.size (enum (P g) (λ x → dec g x)))
         ≡ sumFin (λ x → SubEnum.size (enum (λ g → P g x) (λ g → dec g x)))
sum-swap {zero} P dec =
  sym (sumFin-zero (λ x → SubEnum.size (enum (λ g → P g x) (λ g → dec g x)))
                   (λ x → refl))
sum-swap {suc n} {p} P dec = begin
  sumFin (λ g → SubEnum.size (enum (P g) (λ x → dec g x)))
    ≡⟨⟩
  SubEnum.size (enum (P fzero) (dec fzero))
    + sumFin (λ g → SubEnum.size (enum (P (fsuc g)) (λ x → dec (fsuc g) x)))
    ≡⟨ cong (SubEnum.size (enum (P fzero) (dec fzero)) +_)
            (sum-swap {n} {p} (λ g x → P (fsuc g) x) (λ g x → dec (fsuc g) x)) ⟩
  SubEnum.size (enum (P fzero) (dec fzero))
    + sumFin (λ x → SubEnum.size (enum (λ g → P (fsuc g) x) (λ g → dec (fsuc g) x)))
    ≡⟨ sym (col-decomp P dec) ⟩
  sumFin (λ x → SubEnum.size (enum (λ g → P g x) (λ g → dec g x)))
    ∎
  where open ≡-Reasoning

--------------------------------------------------------------------------------
-- §4. 两个计数与等式
--------------------------------------------------------------------------------

fixSize : ∀ {n p} (G : FinGroup n) (A : Action G (Fin p)) (g : Fin n) → ℕ
fixSize G A g = SubEnum.size (enum (λ x → Action._·_ A g x ≡ x) (λ x → Action._·_ A g x ≟ x))

stabSize : ∀ {n p} (G : FinGroup n) (A : Action G (Fin p)) (x : Fin p) → ℕ
stabSize G A x = SubEnum.size (enum (λ g → Action._·_ A g x ≡ x) (λ g → Action._·_ A g x ≟ x))

fixCount : ∀ {n p} (G : FinGroup n) (A : Action G (Fin p)) → ℕ
fixCount G A = sumFin (fixSize G A)

stabCount : ∀ {n p} (G : FinGroup n) (A : Action G (Fin p)) → ℕ
stabCount G A = sumFin (stabSize G A)

-- 双重计数：Σ_g |Fix g| ≡ Σ_x |Stab x|
burnside-double-count : ∀ {n p} (G : FinGroup n) (A : Action G (Fin p))
                      → fixCount G A ≡ stabCount G A
burnside-double-count G A =
  sum-swap (λ g x → Action._·_ A g x ≡ x) (λ g x → Action._·_ A g x ≟ x)

--------------------------------------------------------------------------------
-- §5. 块 2：共轭不变 |Stab (g·x)| ≡ |Stab x|
--
-- 数学内容：h 固定 x  ⟺  (g ⊙ h ⊙ g⁻¹) 固定 (g · x)。
-- 于是共轭给出两个稳定子枚举之间的双射；用 stdlib 的 cantor-schröder-bernstein
-- （双向单射 ⇒ 基数相等）收口 —— 不自己写基数搬运。
-- 群代数（assoc / inverseˡʳ / identityˡʳ / inv-inv）全部复用 FinGroup record 内已有的引理。
--------------------------------------------------------------------------------

module ConjStab {n p} (G : FinGroup n) (A : Action G (Fin p)) (g : Fin n) (x : Fin p) where
  open FinGroup G
  open Action A
  open ≡-Reasoning

  -- 共轭：h ↦ g ⊙ h ⊙ g⁻¹
  conj : Fin n → Fin n → Fin n
  conj a h = (a ⊙ h) ⊙ inv a

  -- g⁻¹ · (g · x) ≡ x
  gx-fix : ∀ a y → inv a · (a · y) ≡ y
  gx-fix a y =
    trans (sym (·-⊙ (inv a) a y)) (trans (cong (_· y) (inverseˡ a)) (·-ε y))

  -- 正向：h 固定 x ⟹ 共轭元固定 a · x
  conj-stabˡ : ∀ a h y → h · y ≡ y → conj a h · (a · y) ≡ a · y
  conj-stabˡ a h y p = begin
    ((a ⊙ h) ⊙ inv a) · (a · y)   ≡⟨ ·-⊙ (a ⊙ h) (inv a) (a · y) ⟩
    (a ⊙ h) · (inv a · (a · y))   ≡⟨ ·-⊙ a h (inv a · (a · y)) ⟩
    a · (h · (inv a · (a · y)))   ≡⟨ cong (a ·_) (cong (h ·_) (gx-fix a y)) ⟩
    a · (h · y)                   ≡⟨ cong (a ·_) p ⟩
    a · y                         ∎

  -- 反向：h 固定 a · x ⟹ 共轭元（用 a⁻¹）固定 x
  conj-stabʳ : ∀ a h y → h · (a · y) ≡ a · y → conj (inv a) h · y ≡ y
  conj-stabʳ a h y p =
    subst (λ z → conj (inv a) h · z ≡ z) (gx-fix a y)
          (conj-stabˡ (inv a) h (a · y) p)

  -- 共轭的逆：conj (inv a) (conj a h) ≡ h
  conj-inv : ∀ a h → conj (inv a) (conj a h) ≡ h
  conj-inv a h = begin
    (inv a ⊙ ((a ⊙ h) ⊙ inv a)) ⊙ inv (inv a)
      ≡⟨ cong (λ z → (inv a ⊙ ((a ⊙ h) ⊙ inv a)) ⊙ z) (inv-inv a) ⟩
    (inv a ⊙ ((a ⊙ h) ⊙ inv a)) ⊙ a
      ≡⟨ assoc (inv a) ((a ⊙ h) ⊙ inv a) a ⟩
    inv a ⊙ (((a ⊙ h) ⊙ inv a) ⊙ a)
      ≡⟨ cong (inv a ⊙_) (assoc (a ⊙ h) (inv a) a) ⟩
    inv a ⊙ ((a ⊙ h) ⊙ (inv a ⊙ a))
      ≡⟨ cong (inv a ⊙_) (cong ((a ⊙ h) ⊙_) (inverseˡ a)) ⟩
    inv a ⊙ ((a ⊙ h) ⊙ ε)
      ≡⟨ cong (inv a ⊙_) (identityʳ (a ⊙ h)) ⟩
    inv a ⊙ (a ⊙ h)
      ≡⟨ sym (assoc (inv a) a h) ⟩
    (inv a ⊙ a) ⊙ h
      ≡⟨ cong (_⊙ h) (inverseˡ a) ⟩
    ε ⊙ h
      ≡⟨ identityˡ h ⟩
    h ∎

  -- 另一方向：conj a (conj (inv a) h) ≡ h
  conj-invʳ : ∀ a h → conj a (conj (inv a) h) ≡ h
  conj-invʳ a h =
    subst (λ z → conj z (conj (inv a) h) ≡ h) (inv-inv a) (conj-inv (inv a) h)

  -- 稳定子枚举：x 处与 g·x 处
  Es : SubEnum n (λ h → h · x ≡ x)
  Es = enum (λ h → h · x ≡ x) (λ h → h · x ≟ x)

  Esg : SubEnum n (λ h → h · (g · x) ≡ g · x)
  Esg = enum (λ h → h · (g · x) ≡ g · x) (λ h → h · (g · x) ≟ g · x)

  φ : Fin (SubEnum.size Esg) → Fin (SubEnum.size Es)
  φ r = SubEnum.index Es (conj (inv g) (SubEnum.toFin Esg r))
                        (conj-stabʳ g (SubEnum.toFin Esg r) x (SubEnum.toFin-P Esg r))

  ψ : Fin (SubEnum.size Es) → Fin (SubEnum.size Esg)
  ψ s = SubEnum.index Esg (conj g (SubEnum.toFin Es s))
                         (conj-stabˡ g (SubEnum.toFin Es s) x (SubEnum.toFin-P Es s))

  -- toFin 侧的像（index-ok 的具名形式，避免 trans 深层嵌套）
  φ-toFin : ∀ r → SubEnum.toFin Es (φ r) ≡ conj (inv g) (SubEnum.toFin Esg r)
  φ-toFin r = SubEnum.index-ok Es _ _

  ψ-toFin : ∀ s → SubEnum.toFin Esg (ψ s) ≡ conj g (SubEnum.toFin Es s)
  ψ-toFin s = SubEnum.index-ok Esg _ _

  -- 共轭像的相等（拆出来的中间步）
  conj-image-eq : ∀ {r s} → SubEnum.toFin Es (φ r) ≡ SubEnum.toFin Es (φ s)
                → conj (inv g) (SubEnum.toFin Esg r) ≡ conj (inv g) (SubEnum.toFin Esg s)
  conj-image-eq {r} {s} eq =
    trans (sym (φ-toFin r)) (trans eq (φ-toFin s))

  conj-image-eq' : ∀ {r s} → SubEnum.toFin Esg (ψ r) ≡ SubEnum.toFin Esg (ψ s)
                 → conj g (SubEnum.toFin Es r) ≡ conj g (SubEnum.toFin Es s)
  conj-image-eq' {r} {s} eq =
    trans (sym (ψ-toFin r)) (trans eq (ψ-toFin s))

  -- 两条单射：共轭像相等 ⟹ 用 conj-inv 约掉 ⟹ toFin 单射
  φ-inj : Injective _≡_ _≡_ φ
  φ-inj {r} {s} eq =
    SubEnum.toFin-inj Esg
      (trans (sym (conj-invʳ g (SubEnum.toFin Esg r)))
             (trans (cong (conj g) (conj-image-eq {r} {s} (cong (SubEnum.toFin Es) eq)))
                    (conj-invʳ g (SubEnum.toFin Esg s))))

  ψ-inj : Injective _≡_ _≡_ ψ
  ψ-inj {r} {s} eq =
    SubEnum.toFin-inj Es
      (trans (sym (conj-inv g (SubEnum.toFin Es r)))
             (trans (cong (conj (inv g)) (conj-image-eq' {r} {s} (cong (SubEnum.toFin Esg) eq)))
                    (conj-inv g (SubEnum.toFin Es s))))

  -- 块 2 主结论（模块内形式）
  conj-stab-size : SubEnum.size Esg ≡ SubEnum.size Es
  conj-stab-size = cantor-schröder-bernstein φ-inj ψ-inj

-- 块 2（顶层入口）：|Stab (g·x)| ≡ |Stab x|
stabSize-conj : ∀ {n p} (G : FinGroup n) (A : Action G (Fin p)) (g : Fin n) (x : Fin p)
              → stabSize G A (Action._·_ A g x) ≡ stabSize G A x
stabSize-conj G A g x = ConjStab.conj-stab-size G A g x
