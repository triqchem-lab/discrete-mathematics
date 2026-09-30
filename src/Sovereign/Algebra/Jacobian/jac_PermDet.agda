{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Algebra.Jacobian.jac_PermDet
-- 置换矩阵 det ≢ d0 —— 「结构代理 ⟺ 真行列式」桥的正向
--
-- 数学背景:
--   jac_NMatrix 的 DetNonzero 是结构代理 (无全零行 ∧ 列互异), 不是算出来的
--   行列式. 本模块把「真行列式」一侧接上: 置换矩阵 (每列恰一个 d1, 列像互异,
--   经 Perm = 双射 + 显式逆) 的 Laplace 行列式 det ≢ d0 —— 结构判定不虚报的
--   类型级证据 (jac_FunctionTable §6 gap 第一击).
--   ⚠ 另一半「同列 → det = 0」需列反对称性 (交换两列变号), 留 roadmap;
--     本模块亦不主张可逆性 (R₁₂ 零因子红线, det≢0 是元素级事实).
--
-- 证明路线 (0 postulate):
--   · 有限和机件: sumD-zero / sumD-ext / sumD-single (单点支集求和).
--   · 列/行机件: punch / unpunch 互逆 (punch-cancel / unpunch-cancel),
--     predF (去零后继逆) 与其同余与 suc-predF.
--   · 主定理对 n 归纳: 行 0 展开后仅 j* = bwd zero 一项存活
--     (其余项经 toD-no 落 d0, 单点支集求和收拢); 剩余子式由 minorPerm
--     给出 n-1 置换矩阵, 归纳闭合; sgn 单位性 (sgn-val ∈ {d1,d11}) 保非零.
--------------------------------------------------------------------------------

module Sovereign.Algebra.Jacobian.jac_PermDet where

open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; cong; cong₂; trans; subst)
open import Data.Product using (_×_; _,_; Σ; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat using (ℕ) renaming (zero to nzero; suc to nsuc)
open import Data.Fin using (Fin; zero; suc)
open import Data.Fin.Properties using (_≟_)
open import Relation.Nullary using (Dec; yes; no)

open import Sovereign.Base.Trit using (Trit; T₀; T₁; T₂)
open import Sovereign.Algebra.Duodecimal
  using (Duodec; d0; d1; d2; d3; d4; d5; d6; d7; d8; d9; d10; d11; _+12_; _*12_; neg12)
open import Sovereign.Algebra.Jacobian.jac_CRTDet
  using (Mat; det; punch; minor; sgn; sumD)
open import Sovereign.Algebra.Jacobian.jac_Discrete using (GF3²)
open import Sovereign.Algebra.Jacobian.jac_Pigeonhole using (encode9; decode9)
open import Sovereign.Algebra.Jacobian.jac_NMatrix
  using (funcTable; toTrit; DetNonzero; NoZeroRow; ColDistinct; hit⇒; ⇐hit)

_↔_ : Set → Set → Set
A ↔ B = (A → B) × (B → A)

suc≢zero : ∀ {n} {x : Fin n} → suc x ≡ zero → ⊥
suc≢zero ()

--------------------------------------------------------------------------------
-- §1. Duodec 表事实 (12 case refl 拆子) ---------------------------------
--------------------------------------------------------------------------------

x+12d0 : ∀ x → x +12 d0 ≡ x
x+12d0 d0 = refl;  x+12d0 d1 = refl;  x+12d0 d2 = refl;  x+12d0 d3 = refl
x+12d0 d4 = refl;  x+12d0 d5 = refl;  x+12d0 d6 = refl;  x+12d0 d7 = refl
x+12d0 d8 = refl;  x+12d0 d9 = refl;  x+12d0 d10 = refl; x+12d0 d11 = refl

x*12d0 : ∀ x → x *12 d0 ≡ d0
x*12d0 d0 = refl;  x*12d0 d1 = refl;  x*12d0 d2 = refl;  x*12d0 d3 = refl
x*12d0 d4 = refl;  x*12d0 d5 = refl;  x*12d0 d6 = refl;  x*12d0 d7 = refl
x*12d0 d8 = refl;  x*12d0 d9 = refl;  x*12d0 d10 = refl; x*12d0 d11 = refl

d11*12≡neg : ∀ y → d11 *12 y ≡ neg12 y
d11*12≡neg d0 = refl;  d11*12≡neg d1 = refl;  d11*12≡neg d2 = refl;  d11*12≡neg d3 = refl
d11*12≡neg d4 = refl;  d11*12≡neg d5 = refl;  d11*12≡neg d6 = refl;  d11*12≡neg d7 = refl
d11*12≡neg d8 = refl;  d11*12≡neg d9 = refl;  d11*12≡neg d10 = refl; d11*12≡neg d11 = refl

neg12-invol : ∀ x → neg12 (neg12 x) ≡ x
neg12-invol d0 = refl;  neg12-invol d1 = refl;  neg12-invol d2 = refl;  neg12-invol d3 = refl
neg12-invol d4 = refl;  neg12-invol d5 = refl;  neg12-invol d6 = refl;  neg12-invol d7 = refl
neg12-invol d8 = refl;  neg12-invol d9 = refl;  neg12-invol d10 = refl; neg12-invol d11 = refl

-- sgn 单位性: sgn j ∈ {d1, d11}
sgn-val : ∀ {k} (j : Fin k) → sgn j ≡ d1 ⊎ sgn j ≡ d11
sgn-val zero = inj₁ refl
sgn-val (suc j) with sgn-val j
... | inj₁ e = inj₂ (cong neg12 e)
... | inj₂ e = inj₁ (cong neg12 e)

-- 单位 × 非零 ≠ 0
mul-unit-≢ : ∀ s x → (s ≡ d1 ⊎ s ≡ d11) → x ≢ d0 → s *12 x ≢ d0
mul-unit-≢ .d1  x (inj₁ refl) x≢ eq = x≢ eq
mul-unit-≢ .d11 x (inj₂ refl) x≢ eq =
  x≢ (trans (sym (neg12-invol x)) (cong neg12 (trans (sym (d11*12≡neg x)) eq)))

--------------------------------------------------------------------------------
-- §2. 有限和机件 --------------------------------------------------------
--------------------------------------------------------------------------------

sumD-zero : ∀ {k} (f : Fin k → Duodec) → (∀ i → f i ≡ d0) → sumD f ≡ d0
sumD-zero {nzero} f _ = refl
sumD-zero {nsuc k} f p = cong₂ _+12_ (p zero) (sumD-zero (λ i → f (suc i)) (λ i → p (suc i)))

sumD-ext : ∀ {k} (f g : Fin k → Duodec) → (∀ i → f i ≡ g i) → sumD f ≡ sumD g
sumD-ext {nzero} f g _ = refl
sumD-ext {nsuc k} f g p =
  cong₂ _+12_ (p zero) (sumD-ext (λ i → f (suc i)) (λ i → g (suc i)) (λ i → p (suc i)))

-- 单点支集求和: 只有 j* 处非零的和 = 该项
sumD-single : ∀ {k} (f : Fin k → Duodec) (j* : Fin k)
  → (∀ j → j ≢ j* → f j ≡ d0) → sumD f ≡ f j*
sumD-single {nzero} f ()
sumD-single {nsuc k} f zero p =
  trans (cong (f zero +12_) (sumD-zero (λ i → f (suc i)) (λ i → p (suc i) (λ ()))))
        (x+12d0 (f zero))
sumD-single {nsuc k} f (suc j*) p =
  trans (cong (_+12 sumD (λ i → f (suc i))) (p zero (λ ())))
        (sumD-single (λ i → f (suc i)) j* (λ j q → p (suc j) (λ { refl → q refl })))

--------------------------------------------------------------------------------
-- §3. punch / unpunch 机件 ----------------------------------------------
--------------------------------------------------------------------------------

suc-inj : ∀ {n} {a b : Fin n} → suc a ≡ suc b → a ≡ b
suc-inj refl = refl

punch-skip : ∀ {n} (j : Fin (nsuc n)) (c : Fin n) → punch j c ≢ j
punch-skip zero c = λ ()
punch-skip (suc j) zero = λ ()
punch-skip (suc j) (suc c) e = punch-skip j c (suc-inj e)

unpunch : ∀ {n} (j : Fin (nsuc n)) (x : Fin (nsuc n)) → x ≢ j → Fin n
unpunch zero zero p = ⊥-elim (p refl)
unpunch zero (suc y) _ = y
unpunch {nsuc m} (suc j) zero _ = zero
unpunch {nsuc m} (suc j) (suc y) p = suc (unpunch j y (λ { refl → p refl }))
unpunch {nzero} (suc ())

punch-cancel : ∀ {n} (j : Fin (nsuc n)) (x : Fin (nsuc n)) (p : x ≢ j)
  → punch j (unpunch j x p) ≡ x
punch-cancel zero zero p = ⊥-elim (p refl)
punch-cancel zero (suc y) _ = refl
punch-cancel {nsuc m} (suc j) zero _ = refl
punch-cancel {nsuc m} (suc j) (suc y) p = cong suc (punch-cancel j y (λ { refl → p refl }))
punch-cancel {nzero} (suc ())

unpunch-cancel : ∀ {n} (j : Fin (nsuc n)) (c : Fin n) (p : punch j c ≢ j)
  → unpunch j (punch j c) p ≡ c
unpunch-cancel zero c _ = refl
unpunch-cancel (suc j) zero _ = refl
unpunch-cancel (suc j) (suc c) p = cong suc (unpunch-cancel j c (λ e → p (cong suc e)))

-- (unpunch-cong 以 subst 依赖动机替代 —— 证明参数依赖使 refl 失效, 见 bwd′-fwd′)

predF : ∀ {n} (x : Fin (nsuc n)) → x ≢ zero → Fin n
predF zero p = ⊥-elim (p refl)
predF (suc y) _ = y

suc-predF : ∀ {n} (x : Fin (nsuc n)) (p : x ≢ zero) → suc (predF x p) ≡ x
suc-predF zero p = ⊥-elim (p refl)
suc-predF (suc y) _ = refl

predF-cong : ∀ {n} (x y : Fin (nsuc n)) (p : x ≢ zero) (q : y ≢ zero)
  → x ≡ y → predF x p ≡ predF y q
predF-cong zero zero p q e = ⊥-elim (p refl)
predF-cong zero (suc y) p q ()
predF-cong (suc x) zero p q ()
predF-cong (suc x) (suc y) p q refl = refl

predF-eq : ∀ {n} (x : Fin (nsuc n)) (p : x ≢ zero) (r : Fin n)
  → (x ≡ suc r) ↔ (predF x p ≡ r)
predF-eq zero p r = ⊥-elim (p refl)
predF-eq (suc y) p r = (λ { refl → refl }) , (λ e → cong suc e)

-- toD: Dec → Duodec (d1/d0), 与 jac_NMatrix.toTrit 同型
toD : ∀ {A : Set} → Dec A → Duodec
toD (yes _) = d1
toD (no  _) = d0

toD-yes : ∀ {A : Set} (d : Dec A) → A → toD d ≡ d1
toD-yes (yes _) _ = refl
toD-yes (no ¬a) a = ⊥-elim (¬a a)

toD-no : ∀ {A : Set} (d : Dec A) → (A → ⊥) → toD d ≡ d0
toD-no (yes a) ¬a = ⊥-elim (¬a a)
toD-no (no _) _ = refl

toD-cong : ∀ {A B : Set} (d : Dec A) (e : Dec B) → (A ↔ B) → toD d ≡ toD e
toD-cong (yes a) (yes b) _ = refl
toD-cong (yes a) (no ¬b) iff = ⊥-elim (¬b (proj₁ iff a))
toD-cong (no ¬a) (yes b) iff = ⊥-elim (¬a (proj₂ iff b))
toD-cong (no _) (no _) _ = refl

--------------------------------------------------------------------------------
-- §4. 置换矩阵与子式置换 ------------------------------------------------
--------------------------------------------------------------------------------

record Perm (n : ℕ) : Set where
  field
    fwd     : Fin n → Fin n
    bwd     : Fin n → Fin n
    fwd-bwd : ∀ i → fwd (bwd i) ≡ i
    bwd-fwd : ∀ i → bwd (fwd i) ≡ i

-- 置换矩阵: (r, c) 处 = d1 当 fwd c ≡ r, 否则 d0
permMat : ∀ {n} → Perm n → Mat n
permMat p r c = toD (Perm.fwd p c ≟ r)

-- 点wise 相等 → det 相等 (对 n 归纳, 无 funext)
det-ext : ∀ {n} (M M′ : Mat n) → (∀ r c → M r c ≡ M′ r c) → det M ≡ det M′
det-ext {nzero} M M′ _ = refl
det-ext {nsuc n} M M′ p =
  sumD-ext _ _ (λ j → cong (sgn j *12_)
    (cong₂ _*12_ (p zero j)
      (det-ext (minor M j) (minor M′ j) (λ r c → p (suc r) (punch j c)))))

-- 子式仍是置换矩阵: 删行 0 与列 j* 后的 (n-1) 置换
minorPerm : ∀ {n} (p : Perm (nsuc n)) → Perm n
minorPerm {n} p = record
  { fwd     = λ c → predF (Perm.fwd p (punch j* c)) (fwd-punch-ne c)
  ; bwd     = λ r → unpunch j* (Perm.bwd p (suc r)) (bwd-suc-ne r)
  ; fwd-bwd = fwd′-bwd′
  ; bwd-fwd = bwd′-fwd′
  }
  where
    j* : Fin (nsuc n)
    j* = Perm.bwd p zero

    fwd-punch-ne : ∀ c → Perm.fwd p (punch j* c) ≢ zero
    fwd-punch-ne c e =
      punch-skip j* c (trans (sym (Perm.bwd-fwd p (punch j* c))) (cong (Perm.bwd p) e))

    bwd-suc-ne : ∀ r → Perm.bwd p (suc r) ≢ j*
    bwd-suc-ne r e = suc≢zero (inj-bwd (trans e refl))
      where inj-bwd : ∀ {a b : Fin (nsuc n)} → Perm.bwd p a ≡ Perm.bwd p b → a ≡ b
            inj-bwd {a} {b} e′ = trans (sym (Perm.fwd-bwd p a)) (trans (cong (Perm.fwd p) e′) (Perm.fwd-bwd p b))

    fwd′-bwd′ : ∀ r → predF (Perm.fwd p (punch j* (unpunch j* (Perm.bwd p (suc r)) (bwd-suc-ne r)))) (fwd-punch-ne _) ≡ r
    fwd′-bwd′ r = predF-cong _ (suc r) _ (λ ()) e
      where e : Perm.fwd p (punch j* (unpunch j* (Perm.bwd p (suc r)) (bwd-suc-ne r))) ≡ suc r
            e = trans (cong (Perm.fwd p) (punch-cancel j* (Perm.bwd p (suc r)) (bwd-suc-ne r)))
                      (Perm.fwd-bwd p (suc r))

    bwd′-fwd′ : ∀ c → unpunch j* (Perm.bwd p (suc (predF (Perm.fwd p (punch j* c)) (fwd-punch-ne c)))) (bwd-suc-ne _) ≡ c
    bwd′-fwd′ c = subst (λ z → (w : z ≢ j*) → unpunch j* z w ≡ c) (sym e) (unpunch-cancel j* c) (bwd-suc-ne _)
      where e : Perm.bwd p (suc (predF (Perm.fwd p (punch j* c)) (fwd-punch-ne c))) ≡ punch j* c
            e = trans (cong (Perm.bwd p) (suc-predF (Perm.fwd p (punch j* c)) (fwd-punch-ne c)))
                      (Perm.bwd-fwd p (punch j* c))

-- 子式点wise 相等: minor (permMat p) j* ≡ permMat (minorPerm p)
minor-pt : ∀ {n} (p : Perm (nsuc n)) (r c : Fin n)
  → minor (permMat p) (Perm.bwd p zero) r c ≡ permMat (minorPerm p) r c
minor-pt p r c = toD-cong _ _ (predF-eq _ _ r)

--------------------------------------------------------------------------------
-- §5. 主定理: 置换矩阵 det ≢ d0 -----------------------------------------
--------------------------------------------------------------------------------

det-perm-nonzero : ∀ {n} (p : Perm n) → det (permMat p) ≢ d0
det-perm-nonzero {nzero} p = λ ()
det-perm-nonzero {nsuc n} p eq = contr
  where
    j* : Fin (nsuc n)
    j* = Perm.bwd p zero

    M : Mat (nsuc n)
    M = permMat p

    fwd-ne : ∀ j → j ≢ j* → Perm.fwd p j ≢ zero
    fwd-ne j q e = q (trans (sym (Perm.bwd-fwd p j)) (cong (Perm.bwd p) e))

    hit : M zero j* ≡ d1
    hit = toD-yes (Perm.fwd p j* ≟ zero) (Perm.fwd-bwd p zero)

    term-zero : ∀ j → j ≢ j* → sgn j *12 (M zero j *12 det (minor M j)) ≡ d0
    term-zero j q =
      trans (cong (sgn j *12_) (cong₂ _*12_ (toD-no (Perm.fwd p j ≟ zero) (fwd-ne j q)) refl))
            (x*12d0 (sgn j))

    e-det : det M ≡ sgn j* *12 det (minor M j*)
    e-det =
      trans (sumD-single (λ j → sgn j *12 (M zero j *12 det (minor M j))) j* term-zero)
            (cong (sgn j* *12_) (cong₂ _*12_ hit refl))

    e-minor : det (minor M j*) ≡ det (permMat (minorPerm p))
    e-minor = det-ext (minor M j*) (permMat (minorPerm p)) (minor-pt p)

    x≢0 : det (permMat (minorPerm p)) ≢ d0
    x≢0 = det-perm-nonzero (minorPerm p)

    minor≢0 : det (minor M j*) ≢ d0
    minor≢0 e = x≢0 (trans (sym e-minor) e)

    contr : ⊥
    contr = mul-unit-≢ (sgn j*) (det (minor M j*)) (sgn-val j*) minor≢0 (trans (sym e-det) eq)

--------------------------------------------------------------------------------
-- §6. 结构 → 置换: 由 (单射 + 满射数据) 造 Perm ------------------------
--
-- 关键推导: 满射作 Σ 数据携带时不需要构造逆搜索 ——
--   bwd i = proj₁ (surj i); bwd-fwd 由单射闭合. 这消掉全部搜索机件.
--------------------------------------------------------------------------------

InjF : ∀ {n} → (Fin n → Fin n) → Set
InjF ρ = ∀ a b → ρ a ≡ ρ b → a ≡ b

SurjF : ∀ {n} → (Fin n → Fin n) → Set
SurjF {n} ρ = ∀ i → Σ (Fin n) (λ j → ρ j ≡ i)

permFrom : ∀ {n} (ρ : Fin n → Fin n) → InjF ρ → SurjF ρ → Perm n
permFrom ρ ρ-inj ρ-surj = record
  { fwd     = ρ
  ; bwd     = λ i → proj₁ (ρ-surj i)
  ; fwd-bwd = λ i → proj₂ (ρ-surj i)
  ; bwd-fwd = λ j → ρ-inj (proj₁ (ρ-surj (ρ j))) j (proj₂ (ρ-surj (ρ j)))
  }

-- 列基向量条件: 第 c 列在行 ρ c 处 = d1, 其余行 = d0
ColBasis : ∀ {n} → Mat n → (Fin n → Fin n) → Set
ColBasis M ρ = ∀ c → (M (ρ c) c ≡ d1) × (∀ r → r ≢ ρ c → M r c ≡ d0)

colbasis-ptwise : ∀ {n} (M : Mat n) (ρ : Fin n → Fin n) (ρ-inj : InjF ρ) (ρ-surj : SurjF ρ)
  → ColBasis M ρ → ∀ r c → M r c ≡ permMat (permFrom ρ ρ-inj ρ-surj) r c
colbasis-ptwise M ρ ρ-inj ρ-surj cb r c with r ≟ ρ c
... | yes e = trans (trans (cong (λ x → M x c) e) (proj₁ (cb c)))
                    (sym (toD-yes (ρ c ≟ r) (sym e)))
... | no ¬e = trans (proj₂ (cb c) r ¬e)
                    (sym (toD-no (ρ c ≟ r) (λ q → ¬e (sym q))))

-- 桥正向 (一般 N): 列基向量 + 列像互异 ⇒ 真 det ≢ d0
det-struct-nonzero : ∀ {n} (M : Mat n) (ρ : Fin n → Fin n)
  (ρ-inj : InjF ρ) (ρ-surj : SurjF ρ) → ColBasis M ρ → det M ≢ d0
det-struct-nonzero M ρ ρ-inj ρ-surj cb e =
  det-perm-nonzero (permFrom ρ ρ-inj ρ-surj)
    (trans (sym (det-ext M _ (colbasis-ptwise M ρ ρ-inj ρ-surj cb))) e)

--------------------------------------------------------------------------------
-- §7. 9 点推论: jac_NMatrix 结构代理 → 真 det ------------------------
--
-- DetNonzero (funcTable F) = NoZeroRow ∧ ColDistinct
--   → ρF F j = encode9 (F (decode9 j)) 单射 (ColDistinct) + 满射 (NoZeroRow)
--   → ColBasis (embT∘funcTable F) (ρF F)  (hit⇒ / ⇐hit 胶合)
--   → det (embT∘funcTable F) ≢ d0        (§6 桥 + §5)
-- 这就是「结构代理不虚报」在 9 点域的落地闭合.
--------------------------------------------------------------------------------

embT : Trit → Duodec
embT T₀ = d0
embT T₁ = d1
embT T₂ = d2

toT-no : ∀ {A : Set} (d : Dec A) → (A → ⊥) → toTrit d ≡ T₀
toT-no (yes a) ¬a = ⊥-elim (¬a a)
toT-no (no _) _ = refl

toT-cong : ∀ {A B : Set} (d : Dec A) (e : Dec B) → (A ↔ B) → toTrit d ≡ toTrit e
toT-cong (yes _) (yes _) _ = refl
toT-cong (yes a) (no ¬b) iff = ⊥-elim (¬b (proj₁ iff a))
toT-cong (no ¬a) (yes b) iff = ⊥-elim (¬a (proj₂ iff b))
toT-cong (no _) (no _) _ = refl

ρF : (GF3² → GF3²) → Fin 9 → Fin 9
ρF F j = encode9 (F (decode9 j))

ρF-inj : ∀ F → ColDistinct (funcTable F) → InjF (ρF F)
ρF-inj F cd j₁ j₂ e =
  cd j₁ j₂ (λ i → toT-cong (ρF F j₁ ≟ i) (ρF F j₂ ≟ i)
    ((λ q → trans (sym e) q) , (λ q → trans e q)))

ρF-surj : ∀ F → NoZeroRow (funcTable F) → SurjF (ρF F)
ρF-surj F nzr i with nzr i
... | j , hit = j , hit⇒ F i j hit

colbasisF : ∀ F → ColBasis (λ r c → embT (funcTable F r c)) (ρF F)
colbasisF F c = (cong embT (⇐hit F (ρF F c) c refl)) , rest
  where
    rest : ∀ r → r ≢ ρF F c → embT (funcTable F r c) ≡ d0
    rest r ¬e = cong embT (toT-no (ρF F c ≟ r) (λ q → ¬e (sym q)))

det-funcTable-nonzero : ∀ (F : GF3² → GF3²) → DetNonzero (funcTable F)
  → det (λ r c → embT (funcTable F r c)) ≢ d0
det-funcTable-nonzero F (nzr , cd) =
  det-struct-nonzero (λ r c → embT (funcTable F r c)) (ρF F) (ρF-inj F cd) (ρF-surj F nzr) (colbasisF F)

-- ── 对抗验证 (独立 refl, 不经主定理链) ────────────────────────────────
-- ① 1×1 单位置换: det = d1
-- ② 2×2 对换:     det = d11 (= -1, 符号恰为奇置换负号)
p1 : Perm (nsuc nzero)
p1 = permFrom (λ _ → zero) (λ { zero zero _ → refl }) (λ { zero → zero , refl })

det-p1 : det (permMat p1) ≡ d1
det-p1 = refl

p2 : Perm (nsuc (nsuc nzero))
p2 = permFrom (λ { zero → suc zero ; (suc zero) → zero })
              (λ { zero zero _ → refl ; zero (suc zero) () ; (suc zero) zero () ; (suc zero) (suc zero) _ → refl })
              (λ { zero → suc zero , refl ; (suc zero) → zero , refl })

det-p2 : det (permMat p2) ≡ d11
det-p2 = refl
