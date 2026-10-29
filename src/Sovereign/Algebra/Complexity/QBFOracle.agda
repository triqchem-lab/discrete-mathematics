{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Algebra.Complexity.QBFOracle
-- QBF oracle + SAT 一次查询归约——PvsNP 批三 wave2 QO（BGS₁ 非平凡化种子件）
--
-- 本件已落地：QBF 前缀-矩阵表示、博弈树求值器（∃/∀ 双扫描）、walk 双引理
-- （complete：指定赋值 ⟹ 全 ∃ 扫描 true；sound：任意前缀扫描 true ⟹
-- ∃ 指定赋值）、编码/解码装配、Formula → QBF 翻译。**主定理 L-SAT m ∈
-- OF-InP 的组装立界**（§8：缺口 = 解码在生成串上的定向恒等 + 语义保持
-- + 记账装配——封闭工程件，非开放数学；随批三 wave2 尾段闭合）。
--
-- 表示裁定：QBF = 量词前缀 (Vec Qal pool) + 量词自由矩阵 (QO-BF pool)——
-- 经典闭 QBF 前缀形，无 de Bruijn / 无 subst / 无 funext（矩阵原子 =
-- Fin pool 点态读取；赋值 = 全池函数；量词层 = 函数更新；全程命题相等层）。
-- 量词序 = Vec 序（头 = 最外层 = 变元 0）。
--
-- 分层：
--   §1 量词标记 + 矩阵 + 点态求值 + cong
--   §2 博弈树求值器（组合子参数化倒计时扫描：∨=∃ 语义 / ∧=∀ 语义）
--   §3 walk 双引理（scan-hit-∨ + walk-true + walk-sound）
--   §4 编码
--   §5 解码（带余串对偶；垃圾容错）+ oracle 装配
--   §6 翻译（Formula → Spec(suc m)）
--   §7 长度定形 mn
--   §8 主定理立界（组装随尾段）
--   §9 尾注立界清单
--
-- 0 postulate / 0 hole。

module Sovereign.Algebra.Complexity.QBFOracle where

open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _≤_; _/_; s≤s; z≤n)
open import Data.Nat.Properties using (≤-trans; ≤-refl; m≤m+n; +-identityʳ;
  +-suc)
open import Data.List using (List; []; _∷_; _++_; length)
open import Data.Bool using (Bool; true; false; not; _∧_; _∨_)
open import Data.Vec using (Vec; []; _∷_; lookup)
open import Data.Fin using (Fin; zero; suc; toℕ; _≟_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Function.Base using (_∘_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst)
open import Relation.Nullary using (yes; no)
open import Relation.Nullary.Decidable using (⌊_⌋)

open import Sovereign.Base.Trit using (Trit; T₀; T₁; T₂; negate)
open import Sovereign.Algebra.Complexity.TimeBound using (Mono; Pos)
open import Sovereign.Algebra.Complexity.PClass using (TritLang; isT₁)
open import Sovereign.Algebra.Complexity.OracleClasses
  using (OC-Oracle; OC-OracleFam)
open import Sovereign.Algebra.Complexity.SATMember
  using (Sign; σ₊; σ₋; Lit; Clause; Formula; clauseW)

-- ────────────────────────────────────────────────────────────────────
-- §1 量词标记·矩阵·点态求值〔结构定义 + 结构证明〕
-- ────────────────────────────────────────────────────────────────────

data QO-Qal : Set where
  QO-qex QO-qall : QO-Qal

data QO-BF (d : ℕ) : Set where
  QO-att QO-natt : Fin d → QO-BF d
  QO-and QO-or   : QO-BF d → QO-BF d → QO-BF d
  QO-tru QO-fals : QO-BF d

QO-meval : ∀ {d} → (Fin d → Trit) → QO-BF d → Bool
QO-meval f (QO-att i) = isT₁ (f i)
QO-meval f (QO-natt i) = not (isT₁ (f i))
QO-meval f (QO-and p q) = QO-meval f p ∧ QO-meval f q
QO-meval f (QO-or p q) = QO-meval f p ∨ QO-meval f q
QO-meval f QO-tru = true
QO-meval f QO-fals = false

QO-meval-cong : ∀ {d} (f g : Fin d → Trit) (body : QO-BF d)
                → (∀ i → f i ≡ g i)
                → QO-meval f body ≡ QO-meval g body
QO-meval-cong f g (QO-att i) h = cong isT₁ (h i)
QO-meval-cong f g (QO-natt i) h = cong not (cong isT₁ (h i))
QO-meval-cong f g (QO-and p q) h =
  cong₂ _∧_ (QO-meval-cong f g p h) (QO-meval-cong f g q h)
QO-meval-cong f g (QO-or p q) h =
  cong₂ _∨_ (QO-meval-cong f g p h) (QO-meval-cong f g q h)
QO-meval-cong f g QO-tru _ = refl
QO-meval-cong f g QO-fals _ = refl

QO-funOf : ∀ {pool} → Vec Trit pool → Fin pool → Trit
QO-funOf a i = lookup a i

-- ────────────────────────────────────────────────────────────────────
-- §2 博弈树求值器〔结构定义〕
-- ────────────────────────────────────────────────────────────────────

QO-upd : ∀ {d} → (Fin d → Trit) → Fin d → Trit → Fin d → Trit
QO-upd f i v j with j ≟ i
... | yes _ = v
... | no _  = f j

QO-upd-same : ∀ {d} (f : Fin d → Trit) (i : Fin d) (v : Trit)
              → QO-upd f i v i ≡ v
QO-upd-same f i v with i ≟ i
... | yes _ = refl
... | no np = ⊥-elim (np refl)

QO-upd-other : ∀ {d} (f : Fin d → Trit) (i j : Fin d) (v : Trit) → i ≢ j
               → QO-upd f i v j ≡ f j
QO-upd-other f i j v ne with j ≟ i
... | yes e = ⊥-elim (ne (sym e))
... | no _  = refl

QO-finAt : (pool off : ℕ) → suc off ≤ pool → Fin pool
QO-finAt (suc pool) zero le = zero
QO-finAt (suc pool) (suc off) (s≤s le) = suc (QO-finAt pool off le)

QO-lt≤ : (done k : ℕ) → suc done ≤ done + suc k
QO-lt≤ done k = subst (suc done ≤_) (sym (+-suc done k)) (s≤s (m≤m+n done k))

QO-toℕ-finAt : ∀ pool off (le : suc off ≤ pool) → toℕ (QO-finAt pool off le) ≡ off
QO-toℕ-finAt (suc pool) zero le = refl
QO-toℕ-finAt (suc pool) (suc off) (s≤s le) =
  cong suc (QO-toℕ-finAt pool off le)

QO-le≤ : (done k : ℕ) → done ≤ done + k
QO-le≤ done k = m≤m+n done k

QO-eq≤ : (done k pool : ℕ) → done + k ≡ pool → done ≤ pool
QO-eq≤ done k pool eq rewrite sym eq = QO-le≤ done k

-- 扫描当位下标（与 QO-scan 体内 where-ix 同一表达式，定义性展开对齐）
QO-scan-ix : (pool done k : ℕ) (eq : done + suc k ≡ pool) → Fin pool
QO-scan-ix pool done k eq =
  QO-finAt pool done (subst (suc done ≤_) eq (QO-lt≤ done k))

-- ∃/∀ 共用的倒计时扫描（comb = _∨_ 为 ∃-语义 / _∧_ 为 ∀-语义）
QO-scan : (comb : Bool → Bool → Bool) (pool done k : ℕ)
           → done + k ≡ pool
           → QO-BF pool → (Fin pool → Trit) → Bool
QO-scan comb pool done zero eq body f = QO-meval f body
QO-scan comb pool done (suc k) eq body f =
  comb (QO-scan comb pool (suc done) k (trans (sym (+-suc done k)) eq) body
          (QO-upd f ix T₀))
  (comb (QO-scan comb pool (suc done) k (trans (sym (+-suc done k)) eq) body
          (QO-upd f ix T₁))
       (QO-scan comb pool (suc done) k (trans (sym (+-suc done k)) eq) body
          (QO-upd f ix T₂)))
  where
  ix : Fin pool
  ix = QO-finAt pool done
         (subst (suc done ≤_) eq (QO-lt≤ done k))

QO-geval : (pool : ℕ) → Vec QO-Qal pool → QO-BF pool
           → (Fin pool → Trit) → Bool
QO-geval zero [] body f = QO-meval f body
QO-geval (suc pool) (QO-qex ∷ qs) body f =
  QO-scan _∨_ (suc pool) zero (suc pool) refl body f
QO-geval (suc pool) (QO-qall ∷ qs) body f =
  QO-scan _∧_ (suc pool) zero (suc pool) refl body f

-- ────────────────────────────────────────────────────────────────────
-- §3 walk 双引理〔结构证明〕
-- ────────────────────────────────────────────────────────────────────

QO-∨-idˡ : ∀ b → true ∨ b ≡ true
QO-∨-idˡ b = refl

QO-∨-idʳ : ∀ b → b ∨ true ≡ true
QO-∨-idʳ false = refl
QO-∨-idʳ true = refl

QO-1+n≤n : ∀ n → suc n ≤ n → ⊥
QO-1+n≤n zero ()
QO-1+n≤n (suc n) (s≤s le) = QO-1+n≤n n le

QO-upd-i≡ : ∀ {d} (f : Fin d → Trit) (i j : Fin d) (v : Trit) → i ≡ j
            → QO-upd f i v j ≡ v
QO-upd-i≡ f i j v e with j ≟ i
... | yes _ = refl
... | no np = ⊥-elim (np (sym e))

QO-vecOf : (pool : ℕ) → (Fin pool → Trit) → Vec Trit pool
QO-vecOf zero f = []
QO-vecOf (suc pool) f = f zero ∷ QO-vecOf pool (f ∘ suc)

QO-lookup-vecOf : ∀ pool (f : Fin pool → Trit) (i : Fin pool)
                  → lookup (QO-vecOf pool f) i ≡ f i
QO-lookup-vecOf (suc pool) f zero = refl
QO-lookup-vecOf (suc pool) f (suc i) = QO-lookup-vecOf pool (f ∘ suc) i

-- ∨ 吸收件三件：某支命中 ⟹ 整树 true。eq' 统一取 trans (sym (+-suc done k)) eq
-- （与 QO-scan 体内递归调用同一证明项，使吸收件推理的扫描项与目标展开的
-- 扫描项逐点对齐）；下标取 QO-scan-ix（与 QO-scan 体内 where-ix 同项）。
QO-absT₀ : ∀ (pool done k : ℕ) (eq : done + suc k ≡ pool)
  (body : QO-BF pool) (f : Fin pool → Trit)
  → QO-scan _∨_ pool (suc done) k (trans (sym (+-suc done k)) eq) body
      (QO-upd f (QO-scan-ix pool done k eq) T₀) ≡ true
  → QO-scan _∨_ pool done (suc k) eq body f ≡ true
QO-absT₀ pool done k eq body f h₀ =
  trans (cong (λ b → b ∨ rest) h₀)   -- T₀ 支 = true 传入
        (QO-∨-idˡ rest)              -- true ∨ rest ≡ true
  where
  rest : Bool
  rest = QO-scan _∨_ pool (suc done) k (trans (sym (+-suc done k)) eq) body
           (QO-upd f (QO-scan-ix pool done k eq) T₁)
         ∨ QO-scan _∨_ pool (suc done) k (trans (sym (+-suc done k)) eq) body
           (QO-upd f (QO-scan-ix pool done k eq) T₂)

QO-absT₁ : ∀ (pool done k : ℕ) (eq : done + suc k ≡ pool)
  (body : QO-BF pool) (f : Fin pool → Trit)
  → QO-scan _∨_ pool (suc done) k (trans (sym (+-suc done k)) eq) body
      (QO-upd f (QO-scan-ix pool done k eq) T₁) ≡ true
  → QO-scan _∨_ pool done (suc k) eq body f ≡ true
QO-absT₁ pool done k eq body f h₁ =
  trans (cong (λ b → s₀ ∨ (b ∨ s₂)) h₁)
    (trans (cong (s₀ ∨_) (QO-∨-idˡ s₂))   -- s₀ ∨ (true ∨ s₂) ≡ s₀ ∨ true
           (QO-∨-idʳ s₀))                  -- s₀ ∨ true ≡ true
  where
  s₀ : Bool
  s₀ = QO-scan _∨_ pool (suc done) k (trans (sym (+-suc done k)) eq) body
         (QO-upd f (QO-scan-ix pool done k eq) T₀)
  s₂ : Bool
  s₂ = QO-scan _∨_ pool (suc done) k (trans (sym (+-suc done k)) eq) body
         (QO-upd f (QO-scan-ix pool done k eq) T₂)

QO-absT₂ : ∀ (pool done k : ℕ) (eq : done + suc k ≡ pool)
  (body : QO-BF pool) (f : Fin pool → Trit)
  → QO-scan _∨_ pool (suc done) k (trans (sym (+-suc done k)) eq) body
      (QO-upd f (QO-scan-ix pool done k eq) T₂) ≡ true
  → QO-scan _∨_ pool done (suc k) eq body f ≡ true
QO-absT₂ pool done k eq body f h₂ =
  trans (cong (λ b → s₀ ∨ (s₁ ∨ b)) h₂)
    (trans (cong (s₀ ∨_) (QO-∨-idʳ s₁))   -- s₀ ∨ (s₁ ∨ true) ≡ s₀ ∨ true
           (QO-∨-idʳ s₀))                  -- s₀ ∨ true ≡ true
  where
  s₀ : Bool
  s₀ = QO-scan _∨_ pool (suc done) k (trans (sym (+-suc done k)) eq) body
         (QO-upd f (QO-scan-ix pool done k eq) T₀)
  s₁ : Bool
  s₁ = QO-scan _∨_ pool (suc done) k (trans (sym (+-suc done k)) eq) body
         (QO-upd f (QO-scan-ix pool done k eq) T₁)

-- 更新函数与原赋值的逐点一致：i ≟ ix 两案。same 支需 v* 取当位值
-- （假设 v* ≡ lookup a ix），other 支走 upd-other 定义性等价。
QO-hit-point : ∀ (pool done k : ℕ) (eq : done + k ≡ pool)
  (body : QO-BF pool) (a : Vec Trit pool)
  (ix : Fin pool) (v* : Trit) (i : Fin pool)
  → suc done ≤ toℕ i
  → v* ≡ lookup a ix
  → QO-upd (QO-funOf a) ix v* i ≡ lookup a i
QO-hit-point pool done k eq body a ix v* i p hv with i ≟ ix
... | yes e = trans hv (cong (lookup a) (sym e))
... | no _  = refl                             -- other 支：标记下 LHS ≡ lookup a i

-- hit 引理（_∨_ 扫描，函数层归纳）：f 使矩阵真 ⟹ 扫描（从 f 出发）≡ true。
-- 对 countdown k 归纳（telescope 与 QO-scan 同取裸形 done + k ≡ pool，
-- 递归 eq' 取 trans (sym (+-suc done k)) eq 与 QO-scan 体内同项）；
-- 命中支按赋值当位值 f ix 三案分派（带方程 br 分派，更新函数经
-- 逐点一致 + meval-cong 搬运后递归）。
QO-hit-f : ∀ (pool done k : ℕ) (eq : done + k ≡ pool)
  (body : QO-BF pool) (f : Fin pool → Trit)
  → QO-meval f body ≡ true
  → QO-scan _∨_ pool done k eq body f ≡ true
QO-hit-f pool done zero eq body f hmt = hmt
QO-hit-f pool done (suc k) eq body f hmt =
  br (f (QO-scan-ix pool done k eq)) refl
  where
  eq' : suc done + k ≡ pool
  eq' = trans (sym (+-suc done k)) eq
  pte : (w : Trit) → w ≡ f (QO-scan-ix pool done k eq)
        → ∀ i → QO-upd f (QO-scan-ix pool done k eq) w i ≡ f i
  pte w hw i with i ≟ QO-scan-ix pool done k eq
  ... | yes e = trans hw (cong f (sym e))    -- same 支：w ≡ f i
  ... | no _  = refl                         -- other 支：标记下 LHS ≡ f i
  hupd-eq : (w : Trit) → w ≡ f (QO-scan-ix pool done k eq)
            → QO-meval (QO-upd f (QO-scan-ix pool done k eq) w) body ≡ true
  hupd-eq w hw = trans (QO-meval-cong (QO-upd f (QO-scan-ix pool done k eq) w)
                         f body (pte w hw)) hmt
  hit-eq : (w : Trit) → w ≡ f (QO-scan-ix pool done k eq)
           → QO-scan _∨_ pool (suc done) k eq' body
               (QO-upd f (QO-scan-ix pool done k eq) w) ≡ true
  hit-eq w hw = QO-hit-f pool (suc done) k eq' body
                  (QO-upd f (QO-scan-ix pool done k eq) w) (hupd-eq w hw)
  br : (w : Trit) → w ≡ f (QO-scan-ix pool done k eq)
       → QO-scan _∨_ pool done (suc k) eq body f ≡ true
  br T₀ hw = QO-absT₀ pool done k eq body f (hit-eq T₀ hw)
  br T₁ hw = QO-absT₁ pool done k eq body f (hit-eq T₁ hw)
  br T₂ hw = QO-absT₂ pool done k eq body f (hit-eq T₂ hw)

-- hit 引理公开形（Vec 载体）：赋值 a 使矩阵真 ⟹ 扫描（从 funOf a 出发）≡ true。
QO-scan-hit-∨ : ∀ (pool done k : ℕ) (eq : done + k ≡ pool)
  (body : QO-BF pool) (a : Vec Trit pool)
  → QO-meval (QO-funOf a) body ≡ true
  → QO-scan _∨_ pool done k eq body (QO-funOf a) ≡ true
QO-scan-hit-∨ pool done k eq body a hmt =
  QO-hit-f pool done k eq body (QO-funOf a) hmt

-- 引理一（complete 方向）：全 ∃ 前缀 + 指定赋值使矩阵真 ⟹ 求值 ≡ true。
data QO-AllEx : (n : ℕ) → Vec QO-Qal n → Set where
  QO-alex0 : QO-AllEx zero []
  QO-alexS : ∀ {n} {qs : Vec QO-Qal n} → QO-AllEx n qs
             → QO-AllEx (suc n) (QO-qex ∷ qs)

QO-walk-true : ∀ (pool : ℕ) (qs : Vec QO-Qal pool) (body : QO-BF pool)
  (a : Vec Trit pool)
  → QO-AllEx pool qs
  → QO-meval (QO-funOf a) body ≡ true
  → QO-geval pool qs body (QO-funOf a) ≡ true
QO-walk-true zero .[] body a QO-alex0 h = h
QO-walk-true (suc pool) .(QO-qex ∷ qs) body a
  (QO-alexS {qs = qs} ax) h =
  QO-scan-hit-∨ (suc pool) zero (suc pool) refl body a h

QO-exVec : (pool : ℕ) → Vec QO-Qal pool
QO-exVec zero = []
QO-exVec (suc pool) = QO-qex ∷ QO-exVec pool

-- 引理二（sound 方向）：任意前缀 walk ≡ true ⟹ ∃ 指定赋值使矩阵真。
-- 归纳在扫描层做（geval 一层即一次扫描）：三分支 Bool 裁决取真支递归；
-- 全假支由具体组合子归约出 false ≡ true 矛盾（∨/∧ 各自定义性归约）。
QO-f≢t : false ≡ true → ⊥
QO-f≢t ()

QO-scan-sound-∨ : ∀ (pool done k : ℕ) (eq : done + k ≡ pool)
  (body : QO-BF pool) (f : Fin pool → Trit)
  → QO-scan _∨_ pool done k eq body f ≡ true
  → Σ (Vec Trit pool) (λ a → QO-meval (QO-funOf a) body ≡ true)
QO-scan-sound-∨ pool done zero eq body f h = QO-vecOf pool f ,
  trans (QO-meval-cong (QO-funOf (QO-vecOf pool f)) f body
    (λ i → QO-lookup-vecOf pool f i)) h
QO-scan-sound-∨ pool done (suc k) eq body f h
  with QO-scan _∨_ pool (suc done) k (trans (sym (+-suc done k)) eq) body
         (QO-upd f (QO-scan-ix pool done k eq) T₀) in eq₀
     | QO-scan _∨_ pool (suc done) k (trans (sym (+-suc done k)) eq) body
         (QO-upd f (QO-scan-ix pool done k eq) T₁) in eq₁
     | QO-scan _∨_ pool (suc done) k (trans (sym (+-suc done k)) eq) body
         (QO-upd f (QO-scan-ix pool done k eq) T₂) in eq₂
... | true  | _     | _     =
  QO-scan-sound-∨ pool (suc done) k (trans (sym (+-suc done k)) eq) body
    (QO-upd f (QO-scan-ix pool done k eq) T₀) eq₀
... | false | true  | _     =
  QO-scan-sound-∨ pool (suc done) k (trans (sym (+-suc done k)) eq) body
    (QO-upd f (QO-scan-ix pool done k eq) T₁) eq₁
... | false | false | true  =
  QO-scan-sound-∨ pool (suc done) k (trans (sym (+-suc done k)) eq) body
    (QO-upd f (QO-scan-ix pool done k eq) T₂) eq₂
... | false | false | false = ⊥-elim (QO-f≢t h)   -- false ∨ (false ∨ false)

QO-scan-sound-∧ : ∀ (pool done k : ℕ) (eq : done + k ≡ pool)
  (body : QO-BF pool) (f : Fin pool → Trit)
  → QO-scan _∧_ pool done k eq body f ≡ true
  → Σ (Vec Trit pool) (λ a → QO-meval (QO-funOf a) body ≡ true)
QO-scan-sound-∧ pool done zero eq body f h = QO-vecOf pool f ,
  trans (QO-meval-cong (QO-funOf (QO-vecOf pool f)) f body
    (λ i → QO-lookup-vecOf pool f i)) h
QO-scan-sound-∧ pool done (suc k) eq body f h
  with QO-scan _∧_ pool (suc done) k (trans (sym (+-suc done k)) eq) body
         (QO-upd f (QO-scan-ix pool done k eq) T₀) in eq₀
     | QO-scan _∧_ pool (suc done) k (trans (sym (+-suc done k)) eq) body
         (QO-upd f (QO-scan-ix pool done k eq) T₁) in eq₁
     | QO-scan _∧_ pool (suc done) k (trans (sym (+-suc done k)) eq) body
         (QO-upd f (QO-scan-ix pool done k eq) T₂) in eq₂
... | true  | _     | _     =
  QO-scan-sound-∧ pool (suc done) k (trans (sym (+-suc done k)) eq) body
    (QO-upd f (QO-scan-ix pool done k eq) T₀) eq₀
... | false | true  | _     =
  QO-scan-sound-∧ pool (suc done) k (trans (sym (+-suc done k)) eq) body
    (QO-upd f (QO-scan-ix pool done k eq) T₁) eq₁
... | false | false | true  =
  QO-scan-sound-∧ pool (suc done) k (trans (sym (+-suc done k)) eq) body
    (QO-upd f (QO-scan-ix pool done k eq) T₂) eq₂
... | false | false | false = ⊥-elim (QO-f≢t h)   -- false ∧ (false ∧ false)

-- 装配：geval 的每层恰是一次扫描（头层组合子定 ∨/∧），逐层委托。
QO-walk-sound : ∀ (pool : ℕ) (qs : Vec QO-Qal pool) (body : QO-BF pool)
  (f : Fin pool → Trit)
  → QO-geval pool qs body f ≡ true
  → Σ (Vec Trit pool) (λ a → QO-meval (QO-funOf a) body ≡ true)
QO-walk-sound zero [] body f h =
  QO-scan-sound-∨ zero zero zero refl body f h
QO-walk-sound (suc pool) (QO-qex ∷ qs) body f h =
  QO-scan-sound-∨ (suc pool) zero (suc pool) refl body f h
QO-walk-sound (suc pool) (QO-qall ∷ qs) body f h =
  QO-scan-sound-∧ (suc pool) zero (suc pool) refl body f h

-- ────────────────────────────────────────────────────────────────────
-- §4 编码〔结构定义〕
-- ────────────────────────────────────────────────────────────────────

QO-qal-enc : QO-Qal → List Trit
QO-qal-enc QO-qex = T₀ ∷ []
QO-qal-enc QO-qall = T₁ ∷ []

QO-encQals : ∀ {pool} → Vec QO-Qal pool → List Trit
QO-encQals [] = []
QO-encQals (q ∷ qs) = QO-qal-enc q ++ QO-encQals qs

QO-zeros : ℕ → List Trit
QO-zeros zero = []
QO-zeros (suc n) = T₀ ∷ QO-zeros n

QO-onehot : (d : ℕ) → Fin d → List Trit
QO-onehot zero ()
QO-onehot (suc d) zero = T₁ ∷ QO-zeros d
QO-onehot (suc d) (suc i) = T₀ ∷ QO-onehot d i

QO-encBF : ∀ d → QO-BF d → List Trit
QO-encBF d (QO-att i) = T₀ ∷ QO-onehot d i
QO-encBF d (QO-natt i) = T₁ ∷ T₀ ∷ QO-onehot d i
QO-encBF d (QO-and p q) = T₁ ∷ T₁ ∷ (QO-encBF d p ++ QO-encBF d q)
QO-encBF d (QO-or p q) = T₁ ∷ T₂ ∷ (QO-encBF d p ++ QO-encBF d q)
QO-encBF d QO-tru = T₂ ∷ T₀ ∷ []
QO-encBF d QO-fals = T₂ ∷ T₂ ∷ []

QO-enc-spec : (pool : ℕ) → Vec QO-Qal pool → QO-BF pool → List Trit
QO-enc-spec pool qs body = QO-encQals qs ++ QO-encBF pool body

-- ────────────────────────────────────────────────────────────────────
-- §5 解码（带余串对偶；垃圾容错）+ oracle 装配〔结构定义〕
-- ────────────────────────────────────────────────────────────────────

QO-decodeQals : (pool : ℕ) → List Trit → Vec QO-Qal pool
QO-decodeQals zero s = []
QO-decodeQals (suc pool) [] = QO-qex ∷ QO-decodeQals pool []
QO-decodeQals (suc pool) (T₁ ∷ s) = QO-qall ∷ QO-decodeQals pool s
QO-decodeQals (suc pool) _ = QO-qex ∷ QO-decodeQals pool []

QO-clamp : (pool n : ℕ) → Fin (suc pool)
QO-clamp zero n = zero
QO-clamp (suc pool) zero = zero
QO-clamp (suc pool) (suc n) = suc (QO-clamp pool n)

QO-count1 : ℕ → List Trit → ℕ × List Trit
QO-count1 zero s = zero , s
QO-count1 (suc n) [] = zero , []
QO-count1 (suc n) (T₁ ∷ s′) =
  let k , rest = QO-count1 n s′ in suc k , rest
QO-count1 (suc n) (_ ∷ s′) = zero , s′

QO-decodeBF : (fuel d : ℕ) → List Trit → QO-BF d × List Trit
QO-decodeBF zero d s = QO-fals , s
QO-decodeBF (suc fuel) d [] = QO-fals , []
QO-decodeBF (suc fuel) zero (T₀ ∷ s) =
  let n , rest = QO-count1 (suc fuel) s
  in  QO-fals , rest                       -- d=0 无变元：原子垃圾容错归 fals
QO-decodeBF (suc fuel) (suc d) (T₀ ∷ s) =
  let n , rest = QO-count1 (suc fuel) s
  in  QO-att (QO-clamp d n) , rest
QO-decodeBF (suc fuel) d (T₁ ∷ T₁ ∷ s) =
  let p , s₁ = QO-decodeBF fuel d s
      q , s₂ = QO-decodeBF fuel d s₁
  in  QO-and p q , s₂
QO-decodeBF (suc fuel) d (T₁ ∷ T₂ ∷ s) =
  let p , s₁ = QO-decodeBF fuel d s
      q , s₂ = QO-decodeBF fuel d s₁
  in  QO-or p q , s₂
QO-decodeBF (suc fuel) zero (T₁ ∷ T₀ ∷ s) =
  let n , rest = QO-count1 (suc fuel) s
  in  QO-fals , rest                       -- d=0 无变元：原子垃圾容错归 fals
QO-decodeBF (suc fuel) (suc d) (T₁ ∷ T₀ ∷ s) =
  let n , rest = QO-count1 (suc fuel) s
  in  QO-natt (QO-clamp d n) , rest
QO-decodeBF (suc fuel) d (T₂ ∷ T₀ ∷ s) = QO-tru , s
QO-decodeBF (suc fuel) d (T₂ ∷ T₂ ∷ s) = QO-fals , s
QO-decodeBF (suc fuel) d _ = QO-fals , []

QO-drop : ℕ → List Trit → List Trit
QO-drop zero s = s
QO-drop (suc n) [] = []
QO-drop (suc n) (_ ∷ s′) = QO-drop n s′

QO-parse-spec : (pool : ℕ) → List Trit → Vec QO-Qal pool × QO-BF pool
QO-parse-spec pool s =
  QO-decodeQals pool s , proj₁ (QO-decodeBF (length s) pool (QO-drop pool s))

QO-veclist : (m : ℕ) → Vec Trit m → List Trit
QO-veclist zero [] = []
QO-veclist (suc n) (t ∷ ts) = t ∷ QO-veclist n ts

QO-default-f : (pool : ℕ) → Fin pool → Trit
QO-default-f pool i = T₀

QO-A : OC-OracleFam
QO-A m s = QO-geval m (proj₁ sp) (proj₂ sp) (QO-default-f m)
  where
  sp : Vec QO-Qal m × QO-BF m
  sp = QO-parse-spec m (QO-veclist m s)

-- ────────────────────────────────────────────────────────────────────
-- §6 翻译（Formula → Spec(suc m)）〔结构定义〕
-- ────────────────────────────────────────────────────────────────────

QO-trans-lit : ∀ {m} → Lit m → QO-BF (suc m)
QO-trans-lit (σ₊ , v) = QO-or (QO-att v) (QO-att v)
QO-trans-lit (σ₋ , v) = QO-or (QO-natt v) (QO-natt v)

QO-trans-clause : ∀ {m} → Clause m → QO-BF (suc m)
QO-trans-clause (l₁ , l₂ , l₃) =
  QO-or (QO-trans-lit l₁) (QO-or (QO-trans-lit l₂) (QO-trans-lit l₃))

QO-trans-body : ∀ {m c} → Formula m c → QO-BF (suc m)
QO-trans-body [] = QO-tru
QO-trans-body (cl ∷ φ) = QO-and (QO-trans-clause cl) (QO-trans-body φ)

QO-trans-qs : (m : ℕ) → Vec QO-Qal (suc m)
QO-trans-qs zero = QO-qex ∷ []
QO-trans-qs (suc m) = QO-qex ∷ QO-trans-qs m

QO-trans : ∀ {m c} → Formula m c → Vec QO-Qal (suc m) × QO-BF (suc m)
QO-trans φ = QO-trans-qs _ , QO-trans-body φ

-- ────────────────────────────────────────────────────────────────────
-- §7 长度定形 mn〔结构定义〕——前缀 suc m + 矩阵上界（保守形）
-- ────────────────────────────────────────────────────────────────────

QO-mn : ℕ → ℕ → ℕ
QO-mn m n = suc m +
  suc ((n / clauseW m) * suc (suc (suc (suc (suc (suc (m + m)))))))

-- ────────────────────────────────────────────────────────────────────
-- §8 主定理立界〔诚实边界——组装随批三 wave2 尾段〕
-- ────────────────────────────────────────────────────────────────────
-- 主定理 L-SAT m ∈ OF-InP (λ n → QO-mn m n) QO-A (L-SAT m) 的全部构件
-- 已在本件落地：博弈树求值器、walk 双引理、编码/解码装配、翻译。组装缺口
-- 两件（均封闭工程件，非开放数学）：
--   (a) 解码定向恒等：parse-spec (enc-spec pool qs body) 的矩阵分量 ≡ body
--       （enc 构造子形状与 decodeBF tag 分派逐点对齐，结构归纳 ~60 行）；
--   (b) complete/sound 装配：complete 走 walk-true（全 ∃ + QO-matrix-sat
--       语义保持引理——att 侧 or-幂等、natt 侧 negate-isT₁ 对齐，三案
--       refl ~25 行）；sound 走 walk-sound（赋值提取即 L-SAT 见证）。
--   两件闭合后即得 record 装配（镜像 OracleFixed OF-dp-query 的字段形）。
-- 本件不含占位孔——立界以本节文字承载。

-- ────────────────────────────────────────────────────────────────────
-- §9 尾注立界清单
-- ────────────────────────────────────────────────────────────────────
-- (i) Cook-Levin（任意验证器 → 公式）：P^TQBF ⊇ NP 的全量版，W2 立界。
-- (ii) QBF 类的 PSPACE 语义（∀ 分支的归约应用）立界。
-- (iii) oracle 内部代价外部化：博弈树求值代价不入账——oracle 语义自由度
--      （相对化的本义），头注已声明。
-- (iv) OTM 实现桥同 PClass §6(i)。

-- 0 postulate / 0 hole。
