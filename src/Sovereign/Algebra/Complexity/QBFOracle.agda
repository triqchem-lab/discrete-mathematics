{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Algebra.Complexity.QBFOracle
-- QBF oracle + SAT 一次查询归约——PvsNP 批三 wave2 QO（BGS₁ 非平凡化种子件）
--
-- 本件已落地：QBF 前缀-矩阵表示、博弈树求值器（∃/∀ 双扫描）、walk 双引理
-- （complete：指定赋值 ⟹ 全 ∃ 扫描 true；sound：任意前缀扫描 true ⟹
-- ∃ 指定赋值）、编码/解码装配、Formula → QBF 翻译、**主定理闭合**：
-- L-SAT m ∈ OF-InP (λ n → QO-mn m n) (QO-A m) (L-SAT m)（§8 全链 +
-- 核对层，含 x₉ 实例端到端核查）。
--
-- §8 组装期修正的构件级缺陷（五处，全部根因定位后改定义，非打补丁）：
--   (1) decodeBF 原子下标读取：QO-count1（前导 T₁ 计数）对 onehot 编码
--       产生 0↔1 翻转 → 改 QO-scan1（首个 T₁ 定位）+ QO-drop 定宽消耗；
--   (2) decodeQals 第 4 子句 `_` 递归到 []——多量词前缀解析丢弃尾串 →
--       按字符命名递归（T₀/T₁/T₂ 三案）；
--   (3) natt 语义：not ∘ isT₁ 与 SATMember 的 σ₋ 文字（isT₁ ∘ negate，
--       negate 为 GF(3) 加法逆：-T₀=T₀）在 T₀ 处分叉（true ≠ false）；
--       {x=T₁, x≠T₁} 生成的布尔代数无法分离 T₀/T₂，必须改
--       QO-meval (natt i) = isT₁ (negate (f i))；
--   (4) QO-A 把查询长兼作 QBF 变元池——原子 onehot 宽 = 池 ⟹ 编码长
--       ≥ 池 × 原子数 > 池，结构性不可满足 → 池固定为公式池 suc m 的族；
--   (5) QO-mn 每子句预算 2m+6 < 实际编码宽（文字 ≤ m+3，子句 ≤ 3m+13，
--       连账 3m+15）→ QO-bodyW 重定形。
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
--   §8 主定理闭合（解码定向恒等 + 语义保持 + record 装配 + 核对层）
--   §9 尾注立界清单
--
-- 0 postulate / 0 hole。

module Sovereign.Algebra.Complexity.QBFOracle where

open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _≤_; _<_; _/_; s≤s; z≤n;
  _∸_; pred)
open import Data.Nat.Properties using (≤-trans; ≤-refl; ≤-reflexive; m≤m+n;
  +-identityʳ; +-suc; +-assoc; +-comm; n≤1+n; m+[n∸m]≡n; +-monoˡ-≤;
  +-monoʳ-≤; ≤∧≢⇒<)
open import Data.List using (List; []; _∷_; _++_; length)
open import Data.List.Properties using (length-++; ++-assoc)
open import Data.Bool using (Bool; true; false; not; _∧_; _∨_)
open import Data.Vec using (Vec; []; _∷_; lookup)
open import Data.Fin using (Fin; zero; suc; toℕ; _≟_)
open import Data.Fin.Properties using (toℕ<n; toℕ-injective)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Function.Base using (_∘_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst)
open import Relation.Nullary using (yes; no)
open import Relation.Nullary.Decidable using (⌊_⌋)

open import Sovereign.Base.Trit using (Trit; T₀; T₁; T₂; negate)
open import Sovereign.Algebra.Complexity.TimeBound using (Mono; Pos)
open import Sovereign.Algebra.Complexity.PClass using (TritLang)
open import Sovereign.Algebra.Complexity.OracleClasses
  using (OC-Oracle; OC-OracleFam; OC-CountedQ; oc-cqQuery; oc-cqConst;
         oc-value)
open import Sovereign.Algebra.Complexity.OracleFixed using (OF-InP)
open import Sovereign.Algebra.Complexity.SATMember
  using (Sign; σ₊; σ₋; Lit; Clause; Formula; clauseW; Asg; decFormula;
         evalLit; satClause; satFormula; isT₁; L-SAT; x₉; check-sat₁)

-- ────────────────────────────────────────────────────────────────────
-- §1 量词标记·矩阵·点态求值〔结构定义 + 结构证明〕
-- ────────────────────────────────────────────────────────────────────

data QO-Qal : Set where
  QO-qex QO-qall : QO-Qal

data QO-BF (d : ℕ) : Set where
  QO-att QO-natt : Fin d → QO-BF d
  QO-and QO-or   : QO-BF d → QO-BF d → QO-BF d
  QO-tru QO-fals : QO-BF d

-- natt = GF(3) 文字取反（isT₁ ∘ negate）：与 SATMember 的 σ₋ 文字语义
-- 逐字对齐。旧 not ∘ isT₁ 在 T₀ 处分叉（not∘isT₁ T₀ = true，而
-- isT₁ (negate T₀) = isT₁ T₀ = false——见头注缺陷 (3)）。
QO-meval : ∀ {d} → (Fin d → Trit) → QO-BF d → Bool
QO-meval f (QO-att i) = isT₁ (f i)
QO-meval f (QO-natt i) = isT₁ (negate (f i))
QO-meval f (QO-and p q) = QO-meval f p ∧ QO-meval f q
QO-meval f (QO-or p q) = QO-meval f p ∨ QO-meval f q
QO-meval f QO-tru = true
QO-meval f QO-fals = false

QO-meval-cong : ∀ {d} (f g : Fin d → Trit) (body : QO-BF d)
                → (∀ i → f i ≡ g i)
                → QO-meval f body ≡ QO-meval g body
QO-meval-cong f g (QO-att i) h = cong isT₁ (h i)
QO-meval-cong f g (QO-natt i) h = cong isT₁ (cong negate (h i))
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
QO-decodeQals (suc pool) (T₀ ∷ s) = QO-qex ∷ QO-decodeQals pool s
QO-decodeQals (suc pool) (T₁ ∷ s) = QO-qall ∷ QO-decodeQals pool s
QO-decodeQals (suc pool) (T₂ ∷ s) = QO-qex ∷ QO-decodeQals pool s
-- 旧第 4 子句 `_` 递归到 []：多量词前缀在首个非 T₁ 字符后丢弃尾串
-- （两个 qex 的编码 [T₀, T₀] 只读出第一个）——见头注缺陷 (2)。

QO-clamp : (pool n : ℕ) → Fin (suc pool)
QO-clamp zero n = zero
QO-clamp (suc pool) zero = zero
QO-clamp (suc pool) (suc n) = suc (QO-clamp pool n)

-- 首个 T₁ 定位（onehot 下标读取：T₀ᵢ ∷ T₁ ∷ 余 ↦ (i, T₁ 后余串)）。
-- 旧 QO-count1（前导 T₁ 计数）对 onehot 产生 0↔1 翻转
-- （i=0 编码 T₁ ∷ zeros，count1 得 1；i≥1 前导 T₀ 即停，count1 得 0）
-- ——见头注缺陷 (1)。
QO-drop : ℕ → List Trit → List Trit
QO-drop zero s = s
QO-drop (suc n) [] = []
QO-drop (suc n) (_ ∷ s′) = QO-drop n s′

QO-scan1 : List Trit → ℕ × List Trit
QO-scan1 [] = zero , []
QO-scan1 (T₀ ∷ s) = let k , r = QO-scan1 s in suc k , r
QO-scan1 (T₁ ∷ s) = zero , s
QO-scan1 (T₂ ∷ s) = let k , r = QO-scan1 s in suc k , r

QO-decodeBF : (fuel d : ℕ) → List Trit → QO-BF d × List Trit
QO-decodeBF zero d s = QO-fals , s
QO-decodeBF (suc fuel) d [] = QO-fals , []
QO-decodeBF (suc fuel) d (T₁ ∷ T₁ ∷ s) =
  let p , s₁ = QO-decodeBF fuel d s
      q , s₂ = QO-decodeBF fuel d s₁
  in  QO-and p q , s₂
QO-decodeBF (suc fuel) d (T₁ ∷ T₂ ∷ s) =
  let p , s₁ = QO-decodeBF fuel d s
      q , s₂ = QO-decodeBF fuel d s₁
  in  QO-or p q , s₂
QO-decodeBF (suc fuel) d (T₂ ∷ T₀ ∷ s) = QO-tru , s
QO-decodeBF (suc fuel) d (T₂ ∷ T₂ ∷ s) = QO-fals , s
QO-decodeBF (suc fuel) zero (T₀ ∷ s) =
  let n , rest = QO-scan1 s
  in  QO-fals , rest                       -- d=0 无变元：原子垃圾容错归 fals
QO-decodeBF (suc fuel) (suc d) (T₀ ∷ s) =
  let n , _ = QO-scan1 s
  in  QO-att (QO-clamp d n) , QO-drop (suc d) s
QO-decodeBF (suc fuel) zero (T₁ ∷ T₀ ∷ s) =
  let n , rest = QO-scan1 s
  in  QO-fals , rest                       -- d=0 无变元：原子垃圾容错归 fals
QO-decodeBF (suc fuel) (suc d) (T₁ ∷ T₀ ∷ s) =
  let n , _ = QO-scan1 s
  in  QO-natt (QO-clamp d n) , QO-drop (suc d) s
QO-decodeBF (suc fuel) d _ = QO-fals , []
-- 子句序：T₂ 案（d 多态）置于 T₀/T₁ 的 d-分裂案之前——否则 case tree 在
-- 字符串分派前分裂 d，d 为变元时 T₂ 的定义性归约卡死（§8.3 往返引理依赖）。
-- 原子余串消耗 = onehot 窗宽 = 池宽 suc d（QO-drop (suc d)，非 d）。

QO-parse-spec : (pool : ℕ) → List Trit → Vec QO-Qal pool × QO-BF pool
QO-parse-spec pool s =
  QO-decodeQals pool s , proj₁ (QO-decodeBF (length s) pool (QO-drop pool s))

QO-veclist : (m : ℕ) → Vec Trit m → List Trit
QO-veclist zero [] = []
QO-veclist (suc n) (t ∷ ts) = t ∷ QO-veclist n ts

-- 定长装配（零填充）：查询串 → 定长向量（§8 查询装配用）
QO-padTo : (N : ℕ) → List Trit → Vec Trit N
QO-padTo zero _ = []
QO-padTo (suc N) [] = T₀ ∷ QO-padTo N []
QO-padTo (suc N) (t ∷ s) = t ∷ QO-padTo N s

QO-default-f : (pool : ℕ) → Fin pool → Trit
QO-default-f pool i = T₀

-- oracle 族：查询长 len 仅作域界；QBF 变元池固定为公式池 suc m。
-- 旧 QO-A 把 len 兼作池——原子 onehot 宽 = 池 ⟹ 编码长 ≥ 池 × 原子数 > 池，
-- 结构性不可满足（头注缺陷 (4)）。
QO-A : (m : ℕ) → OC-OracleFam
QO-A m len s =
  let s′ = QO-veclist len s
  in  QO-geval (suc m) (QO-decodeQals (suc m) s′)
        (proj₁ (QO-decodeBF len (suc m) (QO-drop (suc m) s′)))
        (QO-default-f (suc m))

-- ────────────────────────────────────────────────────────────────────
-- §6 翻译（Formula → Spec(suc m)）〔结构定义〕
-- ────────────────────────────────────────────────────────────────────

-- 直接原子翻译：meval ∘ trans-lit ≡ isT₁ ∘ evalLit 逐字 refl（§8.6）。
-- 旧 or-倍增（or (att v) (att v)）无语义必要，删除以收窄编码宽。
QO-trans-lit : ∀ {m} → Lit m → QO-BF (suc m)
QO-trans-lit (σ₊ , v) = QO-att v
QO-trans-lit (σ₋ , v) = QO-natt v

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
-- §7 长度定形 mn〔结构定义〕——前缀 suc m + 矩阵每子句连账上界
-- ────────────────────────────────────────────────────────────────────

-- 每子句连账：文字 att ≤ 1+suc m、natt ≤ 2+suc m（QO-litUB = m+3）；
-- 子句 = 2 or-标 ×2 + 3 文字 ≤ 3m+13（QO-clauseUB）；合取每子句 +2 →
-- QO-bodyW m = suc (suc clauseUB) ≥ 2 + clauseUB。旧 2m+6 不足（头注 (5)）。
QO-litUB : ℕ → ℕ
QO-litUB m = suc (suc (suc m))

QO-clauseUB : ℕ → ℕ
QO-clauseUB m = suc (suc (QO-litUB m + suc (suc (QO-litUB m + QO-litUB m))))

QO-bodyW : ℕ → ℕ
QO-bodyW m = suc (suc (QO-clauseUB m))

QO-mn : ℕ → ℕ → ℕ
QO-mn m n = suc m + suc (suc ((n / clauseW m) * QO-bodyW m))

-- ────────────────────────────────────────────────────────────────────
-- §8 主定理闭合：L-SAT m ∈ OF-InP (λ n → QO-mn m n) (QO-A m) (L-SAT m)
-- ────────────────────────────────────────────────────────────────────
-- 组装链：decFormula 解码 → QO-trans 翻译 → enc-spec 编码 → 查询串装配
-- （零填充定长）→ QO-A 求值（geval）→ walk-true / walk-sound 双向。

-- §8.1 账目算术助手〔结构证明〕

QO-+mono : ∀ a b c d → a ≤ b → c ≤ d → a + c ≤ b + d
QO-+mono a b c d a≤b c≤d = ≤-trans (+-monoˡ-≤ c a≤b) (+-monoʳ-≤ b c≤d)

-- suc 单调逆（std-lib 2.4 的 Data.Nat.Properties 未导出 s≤s⁻¹，库内自备）
QO-s≤s⁻¹ : ∀ {m n : ℕ} → suc m ≤ suc n → m ≤ n
QO-s≤s⁻¹ (s≤s m≤n) = m≤n

-- 非零 ≤ 0 否证（tru/fals 的燃料 ≥ 2 收账用；cubical 模式下 ≤ 1 的
-- ShouldBeEmpty 不可判定，走显式 s≤s 分解）
QO-suc≤zero : ∀ n → suc n ≤ zero → ⊥
QO-suc≤zero n ()

-- 结合律 ≤ 桥（自述类型：≤-reflexive ∘ sym ∘ +-assoc 的方向在复合位置
-- 会被 unifier 反转，独立命名后类型自给）
QO-assoc≤ : ∀ a b c → a + (b + c) ≤ (a + b) + c
QO-assoc≤ a b c = ≤-reflexive (sym (+-assoc a b c))

-- §8.2 表级小引理〔结构证明〕

QO-nil-of-len : (q : List Trit) → length q ≡ zero → q ≡ []
QO-nil-of-len [] _ = refl
QO-nil-of-len (t ∷ q) ()

QO-drop-app : (pool : ℕ) (q r : List Trit) → length q ≡ pool
              → QO-drop pool (q ++ r) ≡ r
QO-drop-app zero [] _ _ = refl
QO-drop-app zero (t ∷ q) r ()
QO-drop-app (suc pool) [] r ()
QO-drop-app (suc pool) (t ∷ q′) r e =
  QO-drop-app pool q′ r (cong pred e)

QO-veclist-pad : (N : ℕ) (L : List Trit) → length L ≡ N
                 → QO-veclist N (QO-padTo N L) ≡ L
QO-veclist-pad zero [] _ = refl
QO-veclist-pad zero (t ∷ L) ()
QO-veclist-pad (suc N) (t ∷ L) e = cong (t ∷_) (QO-veclist-pad N L (cong pred e))

QO-len-zeros : ∀ n → length (QO-zeros n) ≡ n
QO-len-zeros zero = refl
QO-len-zeros (suc n) = cong suc (QO-len-zeros n)

QO-len-onehot : ∀ d (i : Fin d) → length (QO-onehot d i) ≡ d
QO-len-onehot (suc d) zero = cong suc (QO-len-zeros d)
QO-len-onehot (suc d) (suc i) = cong suc (QO-len-onehot d i)

QO-len-qal : ∀ (q : QO-Qal) → length (QO-qal-enc q) ≡ 1
QO-len-qal QO-qex = refl
QO-len-qal QO-qall = refl

QO-len-encQals : ∀ pool (qs : Vec QO-Qal pool) → length (QO-encQals qs) ≡ pool
QO-len-encQals zero [] = refl
QO-len-encQals (suc pool) (q ∷ qs) =
  trans (length-++ (QO-qal-enc q) {ys = QO-encQals qs})
  (trans (cong (λ z → z + length (QO-encQals qs)) (QO-len-qal q))
         (cong suc (QO-len-encQals pool qs)))
-- 每量词恰一字符（QO-len-qal），length-++ 后接归纳。

-- §8.3 编解码定向恒等〔结构证明〕

QO-scan1-onehot : ∀ d (i : Fin d) (r : List Trit)
                  → proj₁ (QO-scan1 (QO-onehot d i ++ r)) ≡ toℕ i
QO-scan1-onehot (suc d) zero r = refl
QO-scan1-onehot (suc d) (suc i) r = cong suc (QO-scan1-onehot d i r)

QO-clamp-id : ∀ d (i : Fin (suc d)) → QO-clamp d (toℕ i) ≡ i
QO-clamp-id zero zero = refl
QO-clamp-id (suc d) zero = refl
QO-clamp-id zero (suc ())
QO-clamp-id (suc d) (suc i) = cong suc (QO-clamp-id d i)

QO-decodeQals-enc : ∀ (pool : ℕ) (qs : Vec QO-Qal pool) (r : List Trit)
                    → QO-decodeQals pool (QO-encQals qs ++ r) ≡ qs
QO-decodeQals-enc zero [] r = refl
QO-decodeQals-enc (suc pool) (QO-qex ∷ qs) r =
  cong (QO-qex ∷_) (QO-decodeQals-enc pool qs r)
QO-decodeQals-enc (suc pool) (QO-qall ∷ qs) r =
  cong (QO-qall ∷_) (QO-decodeQals-enc pool qs r)

-- 原子余串 = QO-drop 池宽（onehot 定宽消耗）。
--
-- §8.3a 计长镜像〔结构定义〕——与 encBF 构造子同形的 spec-length。
-- 账目算术全部在其上定义性归约：length (xs ++ ys) 与 length xs + length ys
-- 仅命题相等（length-++），作 cong 重写目标会卡 unifier 方向；lenB 的二叉
-- 方程定义性，ℕ-收账直接闭合（s≤s⁻¹ 两步）。
QO-lenB : (d : ℕ) → QO-BF d → ℕ
QO-lenB d (QO-att _) = suc d
QO-lenB d (QO-natt _) = suc (suc d)
QO-lenB d (QO-and p q) = suc (suc (QO-lenB d p + QO-lenB d q))
QO-lenB d (QO-or p q) = suc (suc (QO-lenB d p + QO-lenB d q))
QO-lenB d QO-tru = suc (suc zero)
QO-lenB d QO-fals = suc (suc zero)

QO-len-encBF : ∀ d (b : QO-BF d) → length (QO-encBF d b) ≡ QO-lenB d b
QO-len-encBF d (QO-att i) = cong suc (QO-len-onehot d i)
QO-len-encBF d (QO-natt i) = cong (λ z → suc (suc z)) (QO-len-onehot d i)
QO-len-encBF d (QO-and p q) =
  trans (cong (λ z → suc (suc z))
              (length-++ (QO-encBF d p) {ys = QO-encBF d q}))
        (cong (λ z → suc (suc z))
              (cong₂ _+_ (QO-len-encBF d p) (QO-len-encBF d q)))
QO-len-encBF d (QO-or p q) =
  trans (cong (λ z → suc (suc z))
              (length-++ (QO-encBF d p) {ys = QO-encBF d q}))
        (cong (λ z → suc (suc z))
              (cong₂ _+_ (QO-len-encBF d p) (QO-len-encBF d q)))
QO-len-encBF d QO-tru = refl
QO-len-encBF d QO-fals = refl

-- 矩阵往返：encBF 的构造子形状与 decodeBF 的 tag 分派逐点对齐；
-- 燃料条件 = lenB + 尾长 ≤ fuel（二叉节点递归共享同额燃料，
-- 经 len-encBF 从 length 型账目换算；子句收账见各案 where 块）。
QO-decodeBF-enc : ∀ d (b : QO-BF d) (tail : List Trit) (fuel : ℕ)
  → QO-lenB d b + length tail ≤ fuel
  → QO-decodeBF fuel d (QO-encBF d b ++ tail) ≡ (b , tail)
QO-decodeBF-enc d QO-tru tail zero ()
QO-decodeBF-enc d QO-tru tail (suc zero) (s≤s h) =
  ⊥-elim (QO-suc≤zero (length tail) h)
QO-decodeBF-enc d QO-tru tail (suc (suc f)) e = refl
QO-decodeBF-enc d QO-fals tail zero ()
QO-decodeBF-enc d QO-fals tail (suc zero) (s≤s h) =
  ⊥-elim (QO-suc≤zero (length tail) h)
QO-decodeBF-enc d QO-fals tail (suc (suc f)) e = refl
QO-decodeBF-enc (suc d) (QO-att i) tail zero ()
QO-decodeBF-enc (suc d) (QO-att i) tail (suc f) e =
  trans (cong (λ n → (QO-att (QO-clamp d n) ,
                      QO-drop (suc d) (QO-onehot (suc d) i ++ tail)))
              (QO-scan1-onehot (suc d) i tail))
        (cong₂ _,_ (cong QO-att (QO-clamp-id d i))
                   (QO-drop-app (suc d) (QO-onehot (suc d) i) tail
                                (QO-len-onehot (suc d) i)))
QO-decodeBF-enc (suc d) (QO-natt i) tail zero ()
QO-decodeBF-enc (suc d) (QO-natt i) tail (suc f) e =
  trans (cong (λ n → (QO-natt (QO-clamp d n) ,
                      QO-drop (suc d) (QO-onehot (suc d) i ++ tail)))
              (QO-scan1-onehot (suc d) i tail))
        (cong₂ _,_ (cong QO-natt (QO-clamp-id d i))
                   (QO-drop-app (suc d) (QO-onehot (suc d) i) tail
                                (QO-len-onehot (suc d) i)))
QO-decodeBF-enc d (QO-and p q) tail zero ()
QO-decodeBF-enc d (QO-and p q) tail (suc f) e =
  trans (cong (λ s → QO-decodeBF (suc f) d (T₁ ∷ T₁ ∷ s))
              (++-assoc (QO-encBF d p) (QO-encBF d q) tail))
        (trans (cong (λ pr → (QO-and (proj₁ pr)
                              (proj₁ (QO-decodeBF f d (proj₂ pr))) ,
                              proj₂ (QO-decodeBF f d (proj₂ pr))))
                     ihp)
               (cong (λ pr → (QO-and p (proj₁ pr) , proj₂ pr)) ihq))
  where
  e₀ : QO-lenB d (QO-and p q) + length tail ≤ suc f
  e₀ = e
  ihp-fuel : QO-lenB d p + (QO-lenB d q + length tail) ≤ f
  ihp-fuel =
    ≤-trans (QO-assoc≤ (QO-lenB d p) (QO-lenB d q) (length tail))
            (≤-trans (n≤1+n ((QO-lenB d p + QO-lenB d q) + length tail))
                     (QO-s≤s⁻¹ e₀))
  ihq-fuel : QO-lenB d q + length tail ≤ f
  ihq-fuel =
    ≤-trans (QO-+mono (QO-lenB d q) (QO-lenB d p + QO-lenB d q)
                      (length tail) (length tail)
                      (≤-trans (m≤m+n (QO-lenB d q) (QO-lenB d p))
                               (≤-reflexive (+-comm (QO-lenB d q)
                                                    (QO-lenB d p))))
                      ≤-refl)
            (≤-trans (n≤1+n ((QO-lenB d p + QO-lenB d q) + length tail))
                     (QO-s≤s⁻¹ e₀))
  ihp-fuel′ : QO-lenB d p + length (QO-encBF d q ++ tail) ≤ f
  ihp-fuel′ =
    subst (λ z → QO-lenB d p + z ≤ f)
          (sym (trans (length-++ (QO-encBF d q) {ys = tail})
                      (cong (λ z → z + length tail)
                            (QO-len-encBF d q))))
          ihp-fuel
  ihp : QO-decodeBF f d (QO-encBF d p ++ (QO-encBF d q ++ tail))
        ≡ (p , QO-encBF d q ++ tail)
  ihp = QO-decodeBF-enc d p (QO-encBF d q ++ tail) f ihp-fuel′
  ihq : QO-decodeBF f d (QO-encBF d q ++ tail) ≡ (q , tail)
  ihq = QO-decodeBF-enc d q tail f ihq-fuel
QO-decodeBF-enc d (QO-or p q) tail zero ()
QO-decodeBF-enc d (QO-or p q) tail (suc f) e =
  trans (cong (λ s → QO-decodeBF (suc f) d (T₁ ∷ T₂ ∷ s))
              (++-assoc (QO-encBF d p) (QO-encBF d q) tail))
        (trans (cong (λ pr → (QO-or (proj₁ pr)
                              (proj₁ (QO-decodeBF f d (proj₂ pr))) ,
                              proj₂ (QO-decodeBF f d (proj₂ pr))))
                     ihp)
               (cong (λ pr → (QO-or p (proj₁ pr) , proj₂ pr)) ihq))
  where
  e₀ : QO-lenB d (QO-or p q) + length tail ≤ suc f
  e₀ = e
  ihp-fuel : QO-lenB d p + (QO-lenB d q + length tail) ≤ f
  ihp-fuel =
    ≤-trans (QO-assoc≤ (QO-lenB d p) (QO-lenB d q) (length tail))
            (≤-trans (n≤1+n ((QO-lenB d p + QO-lenB d q) + length tail))
                     (QO-s≤s⁻¹ e₀))
  ihq-fuel : QO-lenB d q + length tail ≤ f
  ihq-fuel =
    ≤-trans (QO-+mono (QO-lenB d q) (QO-lenB d p + QO-lenB d q)
                      (length tail) (length tail)
                      (≤-trans (m≤m+n (QO-lenB d q) (QO-lenB d p))
                               (≤-reflexive (+-comm (QO-lenB d q)
                                                    (QO-lenB d p))))
                      ≤-refl)
            (≤-trans (n≤1+n ((QO-lenB d p + QO-lenB d q) + length tail))
                     (QO-s≤s⁻¹ e₀))
  ihp-fuel′ : QO-lenB d p + length (QO-encBF d q ++ tail) ≤ f
  ihp-fuel′ =
    subst (λ z → QO-lenB d p + z ≤ f)
          (sym (trans (length-++ (QO-encBF d q) {ys = tail})
                      (cong (λ z → z + length tail)
                            (QO-len-encBF d q))))
          ihp-fuel
  ihp : QO-decodeBF f d (QO-encBF d p ++ (QO-encBF d q ++ tail))
        ≡ (p , QO-encBF d q ++ tail)
  ihp = QO-decodeBF-enc d p (QO-encBF d q ++ tail) f ihp-fuel′
  ihq : QO-decodeBF f d (QO-encBF d q ++ tail) ≡ (q , tail)
  ihq = QO-decodeBF-enc d q tail f ihq-fuel

-- §8.4 编码宽上界〔结构证明〕——lenB 口径（与 clauseUB/bodyW 的 suc-链
-- 定义形逐字对齐，零 length-++ 桥）。

QO-lenB-trans-lit : ∀ m (l : Lit m)
  → QO-lenB (suc m) (QO-trans-lit l) ≤ QO-litUB m
QO-lenB-trans-lit m (σ₊ , v) = n≤1+n (suc (suc m))
QO-lenB-trans-lit m (σ₋ , v) = ≤-refl

QO-lenB-trans-clause : ∀ m (cl : Clause m)
  → QO-lenB (suc m) (QO-trans-clause cl) ≤ QO-clauseUB m
QO-lenB-trans-clause m (l₁ , l₂ , l₃) =
  s≤s (s≤s
    (QO-+mono (QO-lenB (suc m) (QO-trans-lit l₁))
              (QO-litUB m)
              (suc (suc (QO-lenB (suc m) (QO-trans-lit l₂)
                         + QO-lenB (suc m) (QO-trans-lit l₃))))
              (suc (suc (QO-litUB m + QO-litUB m)))
              (QO-lenB-trans-lit m l₁)
              (s≤s (s≤s
                (QO-+mono (QO-lenB (suc m) (QO-trans-lit l₂))
                          (QO-litUB m)
                          (QO-lenB (suc m) (QO-trans-lit l₃))
                          (QO-litUB m)
                          (QO-lenB-trans-lit m l₂)
                          (QO-lenB-trans-lit m l₃))))))
-- or 标 ×2 连账：lenB (or l₁ (or l₂ l₃)) 定义性 = suc (suc (|l₁| + suc (suc
-- (|l₂| + |l₃|))))，与 QO-clauseUB 定义形逐字对齐（零算术桥）。

QO-lenB-trans-body : ∀ m c (φ : Formula m c)
  → QO-lenB (suc m) (QO-trans-body φ) ≤ suc (suc (c * QO-bodyW m))
QO-lenB-trans-body m zero [] = ≤-refl
QO-lenB-trans-body m (suc c) (cl ∷ φ) =
  ≤-trans (s≤s (s≤s
    (QO-+mono (QO-lenB (suc m) (QO-trans-clause cl))
              (QO-clauseUB m)
              (QO-lenB (suc m) (QO-trans-body φ))
              (suc (suc (c * QO-bodyW m)))
              (QO-lenB-trans-clause m cl)
              (QO-lenB-trans-body m c φ))))
          (≤-reflexive
            (cong (λ z → suc (suc z))
                  (trans (+-suc (QO-clauseUB m) (suc (c * QO-bodyW m)))
                         (cong suc (+-suc (QO-clauseUB m)
                                          (c * QO-bodyW m))))))
-- 合取标 ×2 与 QO-bodyW = suc (suc clauseUB) 的定义形逐字对齐：
-- clauseUB + suc (suc (c·W)) ≡ suc (suc (clauseUB + c·W)) [+-suc ×2]
--                            ≡ W + c·W ≡ suc c · W（后者定义性）。

-- 长度口径（len-encBF 换算）：下游 len-spec / fuel-ok 消费。
QO-len-trans-body : ∀ m c (φ : Formula m c)
  → length (QO-encBF (suc m) (QO-trans-body φ)) ≤ suc (suc (c * QO-bodyW m))
QO-len-trans-body m c φ =
  ≤-trans (≤-reflexive (QO-len-encBF (suc m) (QO-trans-body φ)))
          (QO-lenB-trans-body m c φ)


-- §8.5 查询装配与 oracle 求值定向恒等〔结构证明〕

QO-spec : (m n : ℕ) → Vec Trit n → List Trit
QO-spec m n x =
  QO-enc-spec (suc m) (QO-trans-qs m) (QO-trans-body (decFormula m n x))

QO-pad-list : (m n : ℕ) → Vec Trit n → List Trit
QO-pad-list m n x = QO-zeros (QO-mn m n ∸ length (QO-spec m n x))

QO-query-list : (m n : ℕ) → Vec Trit n → List Trit
QO-query-list m n x = QO-spec m n x ++ QO-pad-list m n x

QO-len-spec : ∀ m n (x : Vec Trit n) → length (QO-spec m n x) ≤ QO-mn m n
QO-len-spec m n x =
  ≤-trans (≤-reflexive
            (trans (length-++ (QO-encQals (QO-trans-qs m))
                   {ys = QO-encBF (suc m)
                             (QO-trans-body (decFormula m n x))})
                   (cong (λ z → z + length (QO-encBF (suc m)
                                                (QO-trans-body
                                                  (decFormula m n x))))
                         (QO-len-encQals (suc m) (QO-trans-qs m)))))
          (QO-+mono (suc m) (suc m)
                    (length (QO-encBF (suc m)
                                      (QO-trans-body (decFormula m n x))))
                    (suc (suc ((n / clauseW m) * QO-bodyW m)))
                    ≤-refl
                    (QO-len-trans-body m (n / clauseW m)
                                       (decFormula m n x)))

-- lenB ≤ spec：lenB + 前缀 ≤ 编码总长（len-encQals/len-encBF/length-++ 链）
QO-len-spec≥ : ∀ m n (y : Vec Trit n)
  → QO-lenB (suc m) (QO-trans-body (decFormula m n y)) ≤ length (QO-spec m n y)
QO-len-spec≥ m n y =
  ≤-trans (m≤m+n (QO-lenB (suc m) (QO-trans-body (decFormula m n y))) (suc m))
          (≤-reflexive (sym eq))
  where
  eq : length (QO-spec m n y)
     ≡ QO-lenB (suc m) (QO-trans-body (decFormula m n y)) + suc m
  eq =
    trans (length-++ (QO-encQals (QO-trans-qs m))
                     {ys = QO-encBF (suc m)
                               (QO-trans-body (decFormula m n y))})
    (trans (cong (λ z → length (QO-encQals (QO-trans-qs m)) + z)
                 (QO-len-encBF (suc m)
                               (QO-trans-body (decFormula m n y))))
    (trans (cong (λ z → z + QO-lenB (suc m)
                                       (QO-trans-body (decFormula m n y)))
                 (QO-len-encQals (suc m) (QO-trans-qs m)))
           (sym (+-comm (QO-lenB (suc m)
                                 (QO-trans-body (decFormula m n y)))
                        (suc m)))))

QO-len-query-list : ∀ m n (x : Vec Trit n)
                    → length (QO-query-list m n x) ≡ QO-mn m n
QO-len-query-list m n x =
  trans (length-++ (QO-spec m n x) {ys = QO-pad-list m n x})
  (trans (cong (λ z → length (QO-spec m n x) + z)
               (QO-len-zeros (QO-mn m n ∸ length (QO-spec m n x))))
        (m+[n∸m]≡n (QO-len-spec m n x)))

-- 加法形长度恒等（fuel-ok 末端消费：|spec| + |pad| ≡ mn）
QO-len-sum : ∀ m n (x : Vec Trit n)
  → length (QO-spec m n x) + length (QO-pad-list m n x) ≡ QO-mn m n
QO-len-sum m n x =
  trans (cong (λ z → length (QO-spec m n x) + z)
              (QO-len-zeros (QO-mn m n ∸ length (QO-spec m n x))))
        (m+[n∸m]≡n (QO-len-spec m n x))

QO-decodeQ-query : ∀ m n (x : Vec Trit n)
                   → QO-decodeQals (suc m) (QO-query-list m n x)
                     ≡ QO-trans-qs m
QO-decodeQ-query m n x =
  trans (cong (λ s → QO-decodeQals (suc m) s)
              (++-assoc (QO-encQals (QO-trans-qs m))
                        (QO-encBF (suc m) (QO-trans-body (decFormula m n x)))
                        (QO-pad-list m n x)))
        (QO-decodeQals-enc (suc m) (QO-trans-qs m)
          (QO-encBF (suc m) (QO-trans-body (decFormula m n x))
            ++ QO-pad-list m n x))

QO-drop-query : ∀ m n (x : Vec Trit n)
                → QO-drop (suc m) (QO-query-list m n x)
                  ≡ QO-encBF (suc m) (QO-trans-body (decFormula m n x))
                    ++ QO-pad-list m n x
QO-drop-query m n x =
  trans (cong (λ s → QO-drop (suc m) s)
              (++-assoc (QO-encQals (QO-trans-qs m))
                        (QO-encBF (suc m) (QO-trans-body (decFormula m n x)))
                        (QO-pad-list m n x)))
        (QO-drop-app (suc m) (QO-encQals (QO-trans-qs m))
          (QO-encBF (suc m) (QO-trans-body (decFormula m n x))
            ++ QO-pad-list m n x)
          (QO-len-encQals (suc m) (QO-trans-qs m)))

QO-query : (m n : ℕ) → Vec Trit n → Vec Trit (QO-mn m n)
QO-query m n x = QO-padTo (QO-mn m n) (QO-query-list m n x)

QO-A-enc : ∀ m n (x : Vec Trit n)
  → QO-A m (QO-mn m n) (QO-query m n x)
    ≡ QO-geval (suc m) (QO-trans-qs m)
               (QO-trans-body (decFormula m n x)) (QO-default-f (suc m))
QO-A-enc m n x =
  trans (cong (λ s → QO-geval (suc m) (QO-decodeQals (suc m) s)
                        (proj₁ (QO-decodeBF (QO-mn m n) (suc m)
                                            (QO-drop (suc m) s)))
                        (QO-default-f (suc m)))
              (QO-veclist-pad (QO-mn m n) (QO-query-list m n x)
                              (QO-len-query-list m n x)))
  (trans (cong (λ qs → QO-geval (suc m) qs
                        (proj₁ (QO-decodeBF (QO-mn m n) (suc m)
                                            (QO-drop (suc m)
                                                     (QO-query-list m n x))))
                        (QO-default-f (suc m)))
              (QO-decodeQ-query m n x))
  (trans (cong (λ s → QO-geval (suc m) (QO-trans-qs m)
                        (proj₁ (QO-decodeBF (QO-mn m n) (suc m) s))
                        (QO-default-f (suc m)))
              (QO-drop-query m n x))
  (cong (λ b → QO-geval (suc m) (QO-trans-qs m) b (QO-default-f (suc m)))
        (cong proj₁ (QO-decodeBF-enc (suc m)
                       (QO-trans-body (decFormula m n x))
                       (QO-pad-list m n x) (QO-mn m n) (fuel-ok m n x))))))
  where
  fuel-ok : ∀ m′ n′ (y : Vec Trit n′)
            → QO-lenB (suc m′) (QO-trans-body (decFormula m′ n′ y))
              + length (QO-pad-list m′ n′ y) ≤ QO-mn m′ n′
  fuel-ok m′ n′ y =
    ≤-trans (QO-+mono (QO-lenB (suc m′)
                                (QO-trans-body (decFormula m′ n′ y)))
                      (length (QO-spec m′ n′ y))
                      (length (QO-pad-list m′ n′ y))
                      (length (QO-pad-list m′ n′ y))
                      (QO-len-spec≥ m′ n′ y)
                      ≤-refl)
            (≤-reflexive (QO-len-sum m′ n′ y))

-- §8.6 语义保持〔refl 枚举〕——meval ∘ trans ≡ SATMember 语义

QO-meval-trans-lit : ∀ m (a : Asg m) (l : Lit m)
  → QO-meval (QO-funOf a) (QO-trans-lit l) ≡ isT₁ (evalLit a l)
QO-meval-trans-lit m a (σ₊ , v) = refl
QO-meval-trans-lit m a (σ₋ , v) = refl

QO-meval-trans-clause : ∀ m (a : Asg m) (cl : Clause m)
  → QO-meval (QO-funOf a) (QO-trans-clause cl) ≡ satClause a cl
QO-meval-trans-clause m a (l₁ , l₂ , l₃) =
  cong₂ _∨_ (QO-meval-trans-lit m a l₁)
             (cong₂ _∨_ (QO-meval-trans-lit m a l₂)
                        (QO-meval-trans-lit m a l₃))

QO-meval-trans-body : ∀ m c (a : Asg m) (φ : Formula m c)
  → QO-meval (QO-funOf a) (QO-trans-body φ) ≡ satFormula a φ
QO-meval-trans-body m zero a [] = refl
QO-meval-trans-body m (suc c) a (cl ∷ φ) =
  cong₂ _∧_ (QO-meval-trans-clause m a cl) (QO-meval-trans-body m c a φ)

QO-alex-trans : ∀ m → QO-AllEx (suc m) (QO-trans-qs m)
QO-alex-trans zero = QO-alexS QO-alex0
QO-alex-trans (suc m) = QO-alexS (QO-alex-trans m)

-- §8.6b 扫描起点无关〔结构证明〕——walk-true（funOf a 起扫）与 oracle
-- （default-f 起扫）之桥：全量扫描每位 T₀/T₁/T₂ 三支覆盖全部赋值，起点
-- 函数仅前缀 done 位被查询，故前缀逐点一致即扫描结果一致。
QO-scan-irr : ∀ (comb : Bool → Bool → Bool) (pool done k : ℕ)
  (eq : done + k ≡ pool) (body : QO-BF pool) (f g : Fin pool → Trit)
  → (∀ i → toℕ i < done → f i ≡ g i)
  → QO-scan comb pool done k eq body f ≡ QO-scan comb pool done k eq body g
QO-scan-irr comb pool done zero eq body f g ph =
  QO-meval-cong f g body
    (λ i → ph i (≤-trans (subst (λ w → toℕ i < w) (sym eq) (toℕ<n i))
                         (≤-reflexive (+-identityʳ done))))
QO-scan-irr comb pool done (suc k) eq body f g ph =
  cong₂ comb (br T₀) (cong₂ comb (br T₁) (br T₂))
  where
  eq′ : suc done + k ≡ pool
  eq′ = trans (sym (+-suc done k)) eq
  ix : Fin pool
  ix = QO-scan-ix pool done k eq
  ph′ : (v : Trit) (i : Fin pool) → toℕ i < suc done
       → QO-upd f ix v i ≡ QO-upd g ix v i
  ph′ v i h with i ≟ ix
  ... | yes e = refl
  ... | no np =
    ph i (≤∧≢⇒< (QO-s≤s⁻¹ h)
                 (λ e′ → np (toℕ-injective
                              (trans e′
                               (sym (QO-toℕ-finAt pool done
                                      (subst (suc done ≤_) eq
                                       (QO-lt≤ done k))))))))
  br : (v : Trit)
     → QO-scan comb pool (suc done) k eq′ body (QO-upd f ix v)
       ≡ QO-scan comb pool (suc done) k eq′ body (QO-upd g ix v)
  br v = QO-scan-irr comb pool (suc done) k eq′ body (QO-upd f ix v)
                     (QO-upd g ix v) (ph′ v)

QO-geval-start-irr : ∀ (pool : ℕ) (qs : Vec QO-Qal pool) (body : QO-BF pool)
                     (f g : Fin pool → Trit)
  → QO-geval pool qs body f ≡ QO-geval pool qs body g
QO-geval-start-irr zero [] body f g = QO-meval-cong f g body (λ ())
QO-geval-start-irr (suc pool) (QO-qex ∷ qs) body f g =
  QO-scan-irr _∨_ (suc pool) zero (suc pool) refl body f g (λ i ())
QO-geval-start-irr (suc pool) (QO-qall ∷ qs) body f g =
  QO-scan-irr _∧_ (suc pool) zero (suc pool) refl body f g (λ i ())

-- §8.7 主定理 record（镜像 OracleFixed OF-dp-query 的字段形）

QO-decider : (m n : ℕ) → Vec Trit n → OC-Oracle (QO-mn m n) → OC-CountedQ
QO-decider m n x A′ = oc-cqQuery (A′ (QO-query m n x)) (oc-cqConst false)

qbf-inp : (m : ℕ) → OF-InP (λ n → QO-mn m n) (QO-A m) (L-SAT m)
qbf-inp m = record
  { of-p        = λ _ → 2
  ; of-p-mono   = λ _ → ≤-refl
  ; of-p-pos    = λ _ → s≤s z≤n
  ; of-q        = λ _ → 1
  ; of-q-mono   = λ _ → ≤-refl
  ; of-q-pos    = λ _ → s≤s z≤n
  ; of-decider  = QO-decider m
  ; of-complete = λ n x A′ agree (a , eq) →
      trans (agree (QO-query m n x))
            (trans (QO-A-enc m n x)
            (trans (QO-geval-start-irr (suc m) (QO-trans-qs m)
                          (QO-trans-body (decFormula m n x))
                          (QO-default-f (suc m)) (QO-funOf a))
                   (QO-walk-true (suc m) (QO-trans-qs m)
                                 (QO-trans-body (decFormula m n x))
                                 a (QO-alex-trans m)
                                 (trans (QO-meval-trans-body m
                                           (n / clauseW m) a
                                           (decFormula m n x))
                                        eq))))
  ; of-sound    = λ n x A′ agree v →
      let a′ , hmt =
            QO-walk-sound (suc m) (QO-trans-qs m)
                          (QO-trans-body (decFormula m n x))
                          (QO-default-f (suc m))
                          (trans (sym (QO-A-enc m n x))
                                 (trans (sym (agree (QO-query m n x))) v))
      in  a′ , trans (sym (QO-meval-trans-body m (n / clauseW m) a′
                            (decFormula m n x)))
                     hmt
  ; of-cost     = λ _ _ _ _ → ≤-refl
  ; of-qcount   = λ _ _ _ _ → ≤-refl }
-- complete：agree 换回 QO-A → QO-A-enc 换回 geval（全 ∃ 前缀 + 指定赋值）
-- → walk-true 接 meval-trans-body 反向 + 成员证据 eq。
-- sound：同链反向得 geval ≡ true → walk-sound 提取赋值 a′ →
-- meval-trans-body 正向改写为 satFormula a′ φ ≡ true，即 L-SAT 见证。
-- cost/qcount：oc-steps (cqQuery _ (cqConst _)) = 2 ≤ 2、oc-queries = 1 ≤ 1
-- （均定义性归约，≤-refl 直取）。

-- §8.8 核对层〔refl 枚举 + 端到端实例〕

check-decode-att₀ :
  proj₁ (QO-decodeBF 20 2 (QO-encBF 2 (QO-att zero))) ≡ QO-att zero
check-decode-att₀ = refl

check-decode-natt₁ :
  proj₁ (QO-decodeBF 20 2 (QO-encBF 2 (QO-natt (suc zero))))
    ≡ QO-natt (suc zero)
check-decode-natt₁ = refl

check-decode-and :
  proj₁ (QO-decodeBF 20 2 (QO-encBF 2 (QO-and QO-tru (QO-att zero))))
    ≡ QO-and QO-tru (QO-att zero)
check-decode-and = refl

check-decodeqals₂ :
  QO-decodeQals 2 (QO-encQals (QO-qex ∷ QO-qall ∷ []) ++ (T₂ ∷ []))
    ≡ (QO-qex ∷ QO-qall ∷ [])
check-decodeqals₂ = refl

check-meval-natt-T₂ : QO-meval (λ _ → T₂) (QO-natt {d = 1} zero) ≡ true
check-meval-natt-T₂ = refl

check-geval-trans :
  QO-geval 1 (QO-trans-qs 0)
    (QO-trans-body (((σ₊ , zero) , (σ₋ , zero) , (σ₋ , zero)) ∷ []))
    (QO-funOf (T₁ ∷ [])) ≡ true
check-geval-trans = refl

-- 端到端：x₉（SATMember §6 实例）经 decider 全链（解码→翻译→编码→
-- 定长装配→oracle→walk-true）判定为真，见证取 check-sat₁ 的赋值。
check-of-complete-x₉ :
  oc-value (OF-InP.of-decider (qbf-inp 1) 9 x₉ (QO-A 1 (QO-mn 1 9))) ≡ true
check-of-complete-x₉ =
  OF-InP.of-complete (qbf-inp 1) 9 x₉ (QO-A 1 (QO-mn 1 9)) (λ _ → refl)
    (T₁ ∷ T₀ ∷ [] , check-sat₁)

-- ────────────────────────────────────────────────────────────────────
-- §9 尾注立界清单
-- ────────────────────────────────────────────────────────────────────
-- (i) Cook-Levin（任意验证器 → 公式）：P^TQBF ⊇ NP 的全量版，W2 立界。
-- (ii) QBF 类的 PSPACE 语义（∀ 分支的归约应用）立界。
-- (iii) oracle 内部代价外部化：博弈树求值代价不入账——oracle 语义自由度
--      （相对化的本义），头注已声明。
-- (iv) OTM 实现桥同 PClass §6(i)。

-- 0 postulate / 0 hole。
