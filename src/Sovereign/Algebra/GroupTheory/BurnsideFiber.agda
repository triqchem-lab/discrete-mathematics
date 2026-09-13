{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Algebra.GroupTheory.BurnsideFiber
--
-- 有限纤维分解（Burnside 块 3 的通用承重件）：
--       Σ_x f (L x)  ≡  Σ_y |L⁻¹(y)| · f y
--
-- 数学背景：
--   L : Fin p → Fin m 把有限集按「标签」分层。左边按元素 x 累加，右边按标签 y 累加、
--   每个标签贡献 |L⁻¹(y)| 份 f y。两边都在累加同一个东西——「(x, y) 且 L x ≡ y」
--   的二元组上的 f y——所以这是**求和次序重排**，不是两个数碰巧相等。
--
-- 为什么 Burnside 需要它（而不是除法）：
--   Burnside 的整除性 n ∣ Σ_x |Stab x| 是**结论**，不是前提。若写成
--   #orbits = Σ_x |Stab x| / n，Agda 会要求先交出整除见证；而 ℕ 的 _/_ 是截断除法，
--   没有见证就无法把除法形式回推成乘法形式——证明链断在第一步。
--   本引理把「按 x 求和」重排成「按轨道标签求和」，于是每个轨道贡献恰为
--   |Orbit| · |Stab| ≡ n（orbit-stabilizer-auto 的乘法形式），整除性自动落地。
--   所以「绕开除法」不是技巧，是必然。
--
-- 归约实测（先用 src/ProbeReduce.agda 逐条打表，不猜）：
--   0 * n、1 * n、bit (fzero ≟ fzero)、bit (fsuc y ≟ fzero)、0 + n 都**定义性地**归约；
--   **唯 n + 0 卡住**——_+_ 匹配第一参数，变量头不归约。故 sumFin-single 必须显式接
--   +-identityʳ。这正是本项目「归约卡住先查被调函数的定义形式」纪律的又一实例。
--
-- 核心原则：
--   1. 只复用 Burnside §1–§2（sumFin / size-as-count）与 stdlib，不重造求和的秤
--   2. 对 p 结构归纳；每步一个具名引理（sumFin-single / fiberSize-suc / *-distribʳ-+），
--      trans 嵌套浅，无 4 层深链
--   3. 0 postulate / 0 hole；无 funExt（全部是等式）
--
-- 包含：sumFin-const / bit-suc / sumFin-single / fiberSize / fiberSize-count /
--       fiberSize-suc / sumFin-fiber

module Sovereign.Algebra.GroupTheory.BurnsideFiber where

open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
open import Data.Nat.Properties using (+-identityʳ; *-distribʳ-+)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.Fin.Properties using (_≟_)
open import Relation.Nullary.Decidable using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; module ≡-Reasoning)

open import Sovereign.Algebra.GroupTheory.Burnside
  using (sumFin; sumFin-cong; sumFin-+; sumFin-zero; bit; size-as-count)
open import Sovereign.Algebra.GroupTheory.CosetAuto using (SubEnum; enum)

--------------------------------------------------------------------------------
-- §1. 常数求和与单点指示
--------------------------------------------------------------------------------

sumFin-const : ∀ {m} (c : ℕ) → sumFin (λ (_ : Fin m) → c) ≡ m * c
sumFin-const {zero}  c = refl
sumFin-const {suc m} c = cong (c +_) (sumFin-const {m} c)

-- suc/suc 分支保持判定结果（Fin._≟_ 在 suc/suc 上定义性地保持 cong fsuc）
bit-suc : ∀ {m} (y y0 : Fin m) → bit (fsuc y ≟ fsuc y0) ≡ bit (y ≟ y0)
bit-suc y y0 with y ≟ y0
... | yes _ = refl
... | no _  = refl

sumFin-single : ∀ {m} (y0 : Fin m) (f : Fin m → ℕ)
              → sumFin (λ y → bit (y ≟ y0) * f y) ≡ f y0
sumFin-single {zero}  () f
sumFin-single {suc m} fzero f = begin
  sumFin (λ y → bit (y ≟ fzero) * f y)
    ≡⟨ cong (_+ sumFin (λ y → bit (fsuc y ≟ fzero) * f (fsuc y)))
            (+-identityʳ (f fzero)) ⟩
  f fzero + sumFin (λ y → bit (fsuc y ≟ fzero) * f (fsuc y))
    ≡⟨ cong (f fzero +_)
            (sumFin-zero (λ y → bit (fsuc y ≟ fzero) * f (fsuc y))
                         (λ y → refl)) ⟩
  f fzero + 0
    ≡⟨ +-identityʳ (f fzero) ⟩
  f fzero
    ∎
  where open ≡-Reasoning
sumFin-single {suc m} (fsuc y0) f =
  trans (sumFin-cong (λ y → cong (_* f (fsuc y)) (bit-suc y y0)))
        (sumFin-single y0 (λ y → f (fsuc y)))

--------------------------------------------------------------------------------
-- §2. 纤维大小与分解
--------------------------------------------------------------------------------

-- 纤维大小 |L⁻¹(y)|：判定写成 y ≟ L x（与 sumFin-single 的 y ≟ y0 同向）
fiberSize : ∀ {p m} (L : Fin p → Fin m) (y : Fin m) → ℕ
fiberSize L y = SubEnum.size (enum (λ x → y ≡ L x) (λ x → y ≟ L x))

fiberSize-count : ∀ {p m} (L : Fin p → Fin m) (y : Fin m)
                → fiberSize L y ≡ sumFin (λ x → bit (y ≟ L x))
fiberSize-count L y = size-as-count (λ x → y ≡ L x) (λ x → y ≟ L x)

fiberSize-suc : ∀ {p m} (L : Fin (suc p) → Fin m) (y : Fin m)
              → fiberSize L y
              ≡ bit (y ≟ L fzero) + fiberSize (λ i → L (fsuc i)) y
fiberSize-suc {p} L y =
  trans (fiberSize-count L y)
        (sym (cong (bit (y ≟ L fzero) +_)
                   (fiberSize-count (λ i → L (fsuc i)) y)))

-- 主引理：Σ_x f (L x) ≡ Σ_y |L⁻¹(y)| · f y（对 p 结构归纳，四个具名步骤）
sumFin-fiber : ∀ {p m} (L : Fin p → Fin m) (f : Fin m → ℕ)
             → sumFin (λ x → f (L x)) ≡ sumFin (λ y → fiberSize L y * f y)
sumFin-fiber {zero} L f =
  sym (sumFin-zero (λ y → fiberSize L y * f y) (λ y → refl))
sumFin-fiber {suc p} L f = sym (begin
  sumFin (λ y → fiberSize L y * f y)
    ≡⟨ sumFin-cong (λ y → cong (_* f y) (fiberSize-suc L y)) ⟩
  sumFin (λ y → (bit (y ≟ L fzero) + fiberSize (λ i → L (fsuc i)) y) * f y)
    ≡⟨ sumFin-cong (λ y → *-distribʳ-+ (f y) (bit (y ≟ L fzero))
                                            (fiberSize (λ i → L (fsuc i)) y)) ⟩
  sumFin (λ y → bit (y ≟ L fzero) * f y
                + fiberSize (λ i → L (fsuc i)) y * f y)
    ≡⟨ sumFin-+ (λ y → bit (y ≟ L fzero) * f y)
                (λ y → fiberSize (λ i → L (fsuc i)) y * f y) ⟩
  sumFin (λ y → bit (y ≟ L fzero) * f y)
    + sumFin (λ y → fiberSize (λ i → L (fsuc i)) y * f y)
    ≡⟨ cong (_+ sumFin (λ y → fiberSize (λ i → L (fsuc i)) y * f y))
            (sumFin-single (L fzero) f) ⟩
  f (L fzero) + sumFin (λ y → fiberSize (λ i → L (fsuc i)) y * f y)
    ≡⟨ cong (f (L fzero) +_) (sym (sumFin-fiber (λ i → L (fsuc i)) f)) ⟩
  f (L fzero) + sumFin (λ i → f (L (fsuc i)))
    ≡⟨⟩
  sumFin (λ x → f (L x))
    ∎)
  where open ≡-Reasoning
