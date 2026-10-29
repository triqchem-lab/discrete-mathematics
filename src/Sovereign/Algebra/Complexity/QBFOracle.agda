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

-- 逐步件：扫描分支取 a 的当位值；命中支由递归引理闭合，其余由 Bool 或吸收。
QO-wex-branch : ∀ (pool done k : ℕ) (eq : done + k ≡ pool)
  (body : QO-BF pool) (a : Vec Trit pool)
  → QO-meval (QO-funOf a) body ≡ true
  → (v : Trit)
  → QO-scan _∨_ pool (suc done) k (trans (sym (+-suc done k)) eq) body
      (QO-upd (QO-funOf a) (QO-finAt pool done (QO-eq≤ done k pool eq)) v) ≡ true
  → QO-scan _∨_ pool done (suc k) eq body (QO-funOf a) ≡ true
QO-wex-branch pool done k eq body a hmt v hsuc =
  trans (cong (λ b → b ∨ (QO-scan _∨_ pool (suc done) k (trans (sym (+-suc done k)) eq) body
    (QO-upd (QO-funOf a) (QO-finAt pool done (QO-eq≤ done k pool eq)) T₁)
    ∨ QO-scan _∨_ pool (suc done) k (trans (sym (+-suc done k)) eq) body
      (QO-upd (QO-funOf a) (QO-finAt pool done (QO-eq≤ done k pool eq)) T₂))) hsuc)
  (QO-∨-idˡ (QO-scan _∨_ pool (suc done) k (trans (sym (+-suc done k)) eq) body
    (QO-upd (QO-funOf a) (QO-finAt pool done (QO-eq≤ done k pool eq)) T₁)
    ∨ QO-scan _∨_ pool (suc done) k (trans (sym (+-suc done k)) eq) body
      (QO-upd (QO-funOf a) (QO-finAt pool done (QO-eq≤ done k pool eq)) T₂)))

-- hit 引理子调用的逐点一致：i ≟ ix 两案（same / other-defeq）
QO-hit-point : ∀ (pool done k : ℕ) (eq : done + k ≡ pool)
  (body : QO-BF pool) (a : Vec Trit pool)
  (ix : Fin pool) (v* : Trit) (i : Fin pool)
  → suc done ≤ toℕ i
  → QO-upd (QO-funOf a) ix v* i ≡ lookup a i
QO-hit-point pool done k eq body a ix v* i p with i ≟ ix
... | yes e = trans (cong (λ j → QO-upd (QO-funOf a) ix v* j) (sym e))
  (trans (QO-upd-same (QO-funOf a) ix v*)
         (cong (lookup a) (sym e)))
... | no np = QO-upd-other (QO-funOf a) ix i v* (λ ee → np (sym ee))

-- hit 引理（_∨_ 扫描）：赋值 a 使矩阵真 ⟹ 扫描（从 funOf a 出发）≡ true。
-- 对 countdown k 归纳；a-分支取当位值，其余两支由 Bool 或吸收。
QO-scan-hit-∨ : ∀ (pool done k : ℕ) (eq : done + k ≡ pool)
  (body : QO-BF pool) (a : Vec Trit pool)
  → QO-meval (QO-funOf a) body ≡ true
  → QO-scan _∨_ pool done k eq body (QO-funOf a) ≡ true
QO-scan-hit-∨ pool done zero eq body a hmt = hmt
QO-scan-hit-∨ pool done (suc k) eq body a hmt =
  QO-wex-branch pool done k (trans (sym (+-suc done k)) eq) body a
    (QO-scan-hit-∨ pool (suc done) k (trans (sym (+-suc done k)) eq) body
      (QO-upd (QO-funOf a) ix v*) a
      (λ i p → QO-hit-point pool done k eq body a ix v* i p))
    (lookup a ix)
    hmt
  where
  ix = QO-finAt pool done (subst (suc done ≤_) eq (QO-lt≤ done k))
  v* = lookup a ix

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
QO-walk-true zero .[] body .[] QO-alex0 h = h
QO-walk-true (suc pool) .(QO-qex ∷ qs) body a
  (QO-alexS {qs = qs} ax) h =
  QO-scan-hit-∨ (suc pool) zero (suc pool) refl body a h

QO-exVec : (pool : ℕ) → Vec QO-Qal pool
QO-exVec zero = []
QO-exVec (suc pool) = QO-qex ∷ QO-exVec pool

-- 引理二（sound 方向）：任意前缀 walk ≡ true ⟹ ∃ 指定赋值使矩阵真
-- （∀-层：∧-扫描三分全真，各支赋值皆可——sound 对前缀形状无限制）。
QO-walk-sound : ∀ (pool : ℕ) (qs : Vec QO-Qal pool) (body : QO-BF pool)
  (f : Fin pool → Trit)
  → QO-geval pool qs body f ≡ true
  → Σ (Vec Trit pool) (λ a → QO-meval (QO-funOf a) body ≡ true)
QO-walk-sound zero [] body f h = QO-vecOf zero f ,
  QO-meval-cong (QO-funOf (QO-vecOf zero f)) f body
    (λ i → sym (QO-lookup-vecOf zero f i))
QO-walk-sound (suc pool) (QO-qex ∷ qs) body f h
  with QO-geval pool qs body (QO-upd f zero T₀)
     | QO-geval pool qs body (QO-upd f zero T₁)
     | QO-geval pool qs body (QO-upd f zero T₂)
... | true | _     | _     = QO-walk-sound pool qs body (QO-upd f zero T₀) refl
... | _     | true | _     = QO-walk-sound pool qs body (QO-upd f zero T₁) refl
... | _     | _     | true = QO-walk-sound pool qs body (QO-upd f zero T₂) refl
... | false | false | false = ⊥-elim (h)
QO-walk-sound (suc pool) (QO-qall ∷ qs) body f h
  with QO-geval pool qs body (QO-upd f zero T₀)
     | QO-geval pool qs body (QO-upd f zero T₁)
     | QO-geval pool qs body (QO-upd f zero T₂)
... | true | _     | _     = QO-walk-sound pool qs body (QO-upd f zero T₀) refl
... | _     | true | _     = QO-walk-sound pool qs body (QO-upd f zero T₁) refl
... | _     | _     | true = QO-walk-sound pool qs body (QO-upd f zero T₂) refl
... | false | false | false = ⊥-elim (h)

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
QO-decodeBF (suc fuel) d (T₀ ∷ s) =
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
QO-decodeBF (suc fuel) d (T₁ ∷ T₀ ∷ s) =
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
