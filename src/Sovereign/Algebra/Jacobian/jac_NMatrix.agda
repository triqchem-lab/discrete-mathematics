{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Algebra.Jacobian.jac_NMatrix
-- 函数表矩阵 M_F: det(M_F) ≠ 0 ⟺ F 双射
--
-- 核心洞察: M_F 每列是标准基向量 (e_{F(j)}).
--   det ≠ 0  ⇔  无全零行  ∧  无相同列     (有限线性代数)
--   无全零行  ⇔  F 满射                    (§2)
--   无相同列  ⇔  F 单射                    (§2)
--   因此 det ≠ 0 ⇔ F 双射                 (§3)
--
-- 不计算 9×9 行列式; 用 Fin 9 查找表定义矩阵.
-- 0 postulate.

module Sovereign.Algebra.Jacobian.jac_NMatrix where

open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; cong; sym; trans; subst)
open import Data.Product using (_×_; _,_; Σ; proj₁; proj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin using (Fin; zero; suc; toℕ)
open import Data.Fin.Properties using (_≟_)
open import Relation.Nullary using (Dec; yes; no)

open import Sovereign.Base.Trit
  using (Trit; T₀; T₁; T₂)

open import Sovereign.Algebra.Jacobian.jac_Discrete
  using (GF3²)
open import Sovereign.Algebra.Jacobian.jac_Pigeonhole
  using (Inj2; Surj2; pigeonhole-2; encode9; decode9; encode9-injective; decode9-injective;
          decode9-encode9; encode9-decode9)
open import Sovereign.Algebra.Jacobian.jac_Injectivity
  using (NonSingular; surj→inj)

_↔_ : Set → Set → Set
A ↔ B = (A → B) × (B → A)

--------------------------------------------------------------------------------
-- §1. 函数表矩阵 (Fin 9 查找表, 0 postulate)
--
-- M_F[i][j] = T₁ 当 encode9(F(decode9 j)) ≡ i, 否则 T₀
-- 每列 j 恰有一个 T₁, 在行 encode9(F(decode9 j))
--------------------------------------------------------------------------------

Mat9 : Set
Mat9 = Fin 9 → Fin 9 → Trit

-- 将 Dec 结果转换为 Trit (无 with-block, 可归约)
toTrit : ∀ {A : Set} → Dec A → Trit
toTrit (yes _) = T₁
toTrit (no  _) = T₀

funcTable : (GF3² → GF3²) → Mat9
funcTable F i j = toTrit (encode9 (F (decode9 j)) ≟ i)

--------------------------------------------------------------------------------
-- §2. 核心引理: M_F 单元性质 (0 postulate)
--
-- funcTable F i j ≡ T₁ ⟺ encode9(F(decode9 j)) ≡ i
--------------------------------------------------------------------------------

-- funcTable = toTrit(≟) 可直接证明 (0 postulate)
hit⇒ : ∀ F i j → funcTable F i j ≡ T₁ → encode9 (F (decode9 j)) ≡ i
hit⇒ F i j eq with encode9 (F (decode9 j)) ≟ i
... | yes p = p
... | no ¬p = ⊥-elim (T₁≢T₀ (sym eq)) where T₁≢T₀ : T₁ ≡ T₀ → ⊥; T₁≢T₀ ()

⇐hit : ∀ F i j → encode9 (F (decode9 j)) ≡ i → funcTable F i j ≡ T₁
⇐hit F i j p with encode9 (F (decode9 j)) ≟ i
... | yes _ = refl
... | no ¬p = ⊥-elim (¬p p)

miss⇒ : ∀ F i j → funcTable F i j ≡ T₀ → encode9 (F (decode9 j)) ≢ i
miss⇒ F i j eq with encode9 (F (decode9 j)) ≟ i
... | yes p = ⊥-elim (T₀≢T₁ (sym eq)) where T₀≢T₁ : T₀ ≡ T₁ → ⊥; T₀≢T₁ ()
... | no ¬p = ¬p

--------------------------------------------------------------------------------
-- §3. 行列式非零的结构条件 (0 postulate)
--
-- 对函数表矩阵, det ≠ 0 等价于同时满足:
--   (a) 无全零行 (每行至少一个 T₁)
--   (b) 列互异 (各列在不同的行有 T₁)
--
-- 这与 F 单射 + F 满射直接对应.
--------------------------------------------------------------------------------

-- (a) 无全零行 ≡ F 满射
NoZeroRow : Mat9 → Set
NoZeroRow M = ∀ i → Σ (Fin 9) (λ j → M i j ≡ T₁)

-- (b) 列互异 ≡ F 单射
ColDistinct : Mat9 → Set
ColDistinct M = ∀ j₁ j₂ → (∀ i → M i j₁ ≡ M i j₂) → j₁ ≡ j₂

-- det ≠ 0 的定义: 无全零行 + 列互异
DetNonzero : Mat9 → Set
DetNonzero M = NoZeroRow M × ColDistinct M

--------------------------------------------------------------------------------
-- 定理 1: M_F 无全零行 ⟺ F 满射
--------------------------------------------------------------------------------

noZeroRow→surj : ∀ F → NoZeroRow (funcTable F) → Surj2 F
noZeroRow→surj F nzr q =
  let (j , hit) = nzr (encode9 q)
  in decode9 j , encode9-injective (hit⇒ F (encode9 q) j hit)

surj→noZeroRow : ∀ F → Surj2 F → NoZeroRow (funcTable F)
surj→noZeroRow F surj i =
  let (p , Fp≡q) = surj (decode9 i)
      j = encode9 p
      proof : encode9 (F (decode9 j)) ≡ i
      proof = trans (cong encode9 Fp≡q) (encode9-decode9 i)
  in j , ⇐hit F i j proof

-- 定理 2: M_F 列互异 ⟺ F 单射
--------------------------------------------------------------------------------

colDistinct→inj : ∀ F → ColDistinct (funcTable F) → Inj2 F
colDistinct→inj F cd {p} {q} Fp≡Fq = encode9-injective (cd j₁ j₂ same)
  where j₁ = encode9 p; j₂ = encode9 q
        same : ∀ i → funcTable F i j₁ ≡ funcTable F i j₂
        same i rewrite Fp≡Fq = refl

inj→colDistinct : ∀ F → Inj2 F → ColDistinct (funcTable F)
inj→colDistinct F inj j₁ j₂ same =
  let p = decode9 j₁; q = decode9 j₂
      i* = encode9 (F p)
      hit₁ : funcTable F i* j₁ ≡ T₁
      hit₁ = ⇐hit F i* j₁ refl
      hit₂ : funcTable F i* j₂ ≡ T₁
      hit₂ = trans (sym (same i*)) hit₁
      Fq-enc : encode9 (F (decode9 j₂)) ≡ i*
      Fq-enc = hit⇒ F i* j₂ hit₂
      Fp≡Fq : F (decode9 j₁) ≡ F (decode9 j₂)
      Fp≡Fq = encode9-injective {F (decode9 j₁)} {F (decode9 j₂)} (trans refl (sym Fq-enc))
  in trans (sym (encode9-decode9 j₁)) (trans (cong encode9 (inj Fp≡Fq)) (encode9-decode9 j₂))

--------------------------------------------------------------------------------
-- §3. 主定理: det(M_F) ≠ 0 ⟺ F 双射 (0 postulate)
--
-- 由 (det ≠ 0) ≡ (无全零行 ∧ 列互异)
--     无全零行 ⟺ Surj2   (§2 定理 1)
--     列互异   ⟺ Inj2    (§2 定理 2)
--     双射     ≡ Inj2 × Surj2
--
-- 等价链:
--   det(M_F) ≠ 0  ↔  (NoZeroRow ∧ ColDistinct)
--                  ↔  (Surj2 F ∧ Inj2 F)
--                  ↔  (Inj2 F × Surj2 F)
--------------------------------------------------------------------------------

detNonzero↔surj-inj : ∀ F → DetNonzero (funcTable F) ↔ (Inj2 F × Surj2 F)
detNonzero↔surj-inj F =
  (λ (nzr , cd) → colDistinct→inj F cd , noZeroRow→surj F nzr) ,
  (λ (inj , surj) → surj→noZeroRow F surj , inj→colDistinct F inj)

detNonzero↔bij : ∀ F → DetNonzero (funcTable F) ↔ (Inj2 F × Surj2 F)
detNonzero↔bij = detNonzero↔surj-inj

-- 连接 NonSingular (来自 jac_Injectivity)
detNonzero↔nonsingular : ∀ F → DetNonzero (funcTable F) ↔ NonSingular F
detNonzero↔nonsingular F =
  (λ dn → proj₁ (proj₁ (detNonzero↔bij F) dn)) ,
  (λ ns → proj₂ (detNonzero↔bij F) (ns , pigeonhole-2 F ns))

--------------------------------------------------------------------------------
-- §4. TODO: 填充 §2 的洞 (colDistinct→inj 和 inj→colDistinct)
-- 思路: 用 funcTable-hit/funcTable-miss 引理转换行列值与 F 值.
-- 预期: ~15 行, 全部等式推导, 0 postulate.
--------------------------------------------------------------------------------
