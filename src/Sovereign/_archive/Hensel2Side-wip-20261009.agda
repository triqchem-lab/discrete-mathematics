--------------------------------------------------------------------------------
-- | Sovereign.Algebra.Hensel2Side
-- 2 侧 Hensel 分类：x² ≡ 1 (mod 2^k) 的解结构。
--
-- 数学背景（与 Hensel3Side 同构、但有本质差异）：
--   3 侧：3∣x²∸1 → 3∣(x∸1) ⊎ 3∣suc(x)（二分，素性直接收缩）。
--   2 侧：二分对 2 的幂不成立（x=2¹⁵+1 反例）——正确结构是「四分」：
--     x² ≡ 1 (mod 2^k) (k≥3) ⟺ x ≡ ±1 或 ±(1+2^(k-1)) (mod 2^k)，恰 4 解。
--   论证骨架：
--     (1) x 偶 → x²∸1 奇 → 2^k ∤ x²∸1（k≥1），故解必奇。
--     (2) x 奇 → x∸1 与 suc x 均偶且差 2 → 恰一个被 4 整除、
--         另一个 ≡ 2 (mod 4)（即 2-adic 赋值恰 1）。
--     (3) 赋值恰 1 的因子「除一次」：2^k ∣ a·b ∧ 2∥a → 2^(k-1) ∣ b。
--     (4) 剩余幂次经素性二分（相邻互素）落到 x∸1 或 suc x 上。
--
-- 本模块当前闭合：pow2、two-odd-branch（2^k∣偶无解）、素性二分迭代引理。
--------------------------------------------------------------------------------

{-# OPTIONS --rewriting --guardedness #-}

module Sovereign.Algebra.Hensel2Side where

open import Data.Nat using (ℕ; zero; suc; _*_; _+_; _∸_; _≤_; _%_; s≤s; z≤n)
open import Data.Nat.Divisibility using (_∣_; divides; ∣1⇒≡1; 1∣_; ∣-refl; ∣⇒≤; ∣-trans; m∣m*n; n∣m*n; ∣m+n∣n⇒∣m; _∣?_; *-cancelˡ-∣; *-monoʳ-∣)
open import Data.Nat.Coprimality using (Coprime; coprime-divisor; coprime?)
open import Data.Nat.Properties using (*-suc; *-comm; *-zeroʳ; *-identityʳ; *-identityˡ; *-assoc; *-cancelˡ-∣; *-cancelˡ-≡; ≤-antisym; m≤m+n; ≤-trans; ≤-reflexive; 1+n≢n; suc-injective; _≟_; ≤⇒≤ᵇ; +-comm; +-assoc; +-identityʳ)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂; ∃-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (¬_; yes; no; Dec)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst; module ≡-Reasoning)
open import Sovereign.Algebra.Hensel3Side using (px)

--------------------------------------------------------------------------------
-- §1. 2 的幂
--------------------------------------------------------------------------------

pow2 : ℕ → ℕ
pow2 zero = 1
pow2 (suc k) = 2 * pow2 k

--------------------------------------------------------------------------------
-- §2. 相邻互素与 2 的整除基础件
--------------------------------------------------------------------------------

-- 相邻互素：d∣a ∧ d∣suc(a) → d∣1（suc a 定义性 = 1 + a，经 ∣m+n∣n⇒∣m）
coprime-suc-a : ∀ a → Coprime a (suc a)
coprime-suc-a a (d∣a , d∣suc-a) = ∣1⇒≡1 (∣m+n∣n⇒∣m d∣suc-a d∣a)

-- Coprime 的参数对称（定义形状对称，交换字段即可）
coprime-2-a : ∀ a → Coprime a 2 → Coprime 2 a
coprime-2-a a c (d∣2 , d∣a) = c (d∣a , d∣2)

-- 2 ∣ pow2 (suc k)（定义性：pow2 (suc k) = 2 * pow2 k）
2∣pow2-suc : ∀ k → 2 ∣ pow2 (suc k)
2∣pow2-suc k = m∣m*n {m = 2} (pow2 k)

--------------------------------------------------------------------------------
-- §3. 素性迭代引理（2 侧核心收缩，仿 Hensel3Side 的 core）
--   pow2 k ∣ a·b ∧ Coprime a 2 → pow2 k ∣ b
--   对 k 归纳：suc 层先经 coprime-divisor 剥掉一个 2，再递归剩余幂次
--------------------------------------------------------------------------------

-- 半幂剥离：2·pow2 k ∣ a·b → pow2 k ∣ a·b（经 divides 字段 + *-assoc 重排）
pow2-half : ∀ k a b → 2 * pow2 k ∣ a * b → pow2 k ∣ a * b
pow2-half k a b (divides q eq) = divides (q * 2) (trans eq (sym (*-assoc q 2 (pow2 k))))

--------------------------------------------------------------------------------
-- §3. irred2：2 的整除分类（与 irred3 同构的四值判定器）
--   d ∣ 2 → d ≡ 1 ⊎ d ≡ 2（d=0 封闭 clash / d≥3 经 ∣⇒≤ 与 ≤⇒≤ᵇ）
--------------------------------------------------------------------------------

zero-2 : zero ∣ 2 → zero ≡ 2
zero-2 (divides q eq) = sym (trans eq (*-zeroʳ q))

zero-2-clash : 2 ≡ zero → ⊥
zero-2-clash ()

irred2 : ∀ d → d ∣ 2 → d ≡ 1 ⊎ d ≡ 2
irred2 d h with ∣⇒≤ h
... | dle with d ≟ zero
...   | yes d0 = ⊥-elim (zero-2-clash (sym (zero-2 (subst (λ w → w ∣ 2) d0 h))))
...   | no nd0 with d ≟ 1
...     | yes d1 = inj₁ d1
...     | no nd1 with d ≟ 2
...       | yes d2 = inj₂ d2
...       | no nd2 with d
...         | zero = ⊥-elim (nd0 refl)
...         | suc zero = ⊥-elim (nd1 refl)
...         | suc (suc zero) = ⊥-elim (nd2 refl)
...         | suc (suc (suc m)) = ⊥-elim (≤⇒≤ᵇ (≤-trans (s≤s (s≤s (s≤s z≤n))) dle))

--------------------------------------------------------------------------------
-- §4. 奇性传递链：¬2∣a → Coprime d 2 → div-pow2 → Coprime a (pow2 k)
--------------------------------------------------------------------------------

-- ¬2∣d → Coprime d 2（irred2 分类：d∣2 → d≡1 ✓ / d≡2 → 2∣d 矛盾）
coprime-d-2 : ∀ d → ¬ (2 ∣ d) → Coprime d 2
coprime-d-2 d nt2 {e} (e∣d , e∣2) with irred2 e e∣2
...   | inj₁ e≡1 = e≡1
...   | inj₂ e≡2 = ⊥-elim (nt2 (subst (λ w → w ∣ d) e≡2 e∣d))

-- d ∣ 2^k → d ≡ 1 ⊎ 2 ∣ d（对 k 归纳；suc 层经 coprime-divisor 剥一个 2）
div-pow2 : ∀ k d → d ∣ pow2 k → d ≡ 1 ⊎ 2 ∣ d
div-pow2 zero d h = inj₁ (∣1⇒≡1 h)
div-pow2 (suc k) d h with 2 ∣? d
...   | yes t = inj₂ t
...   | no nt2 = inj₁-sum
      where
        rec = div-pow2 k d (coprime-divisor (coprime-d-2 d nt2) h)
        inj₁-sum : d ≡ 1 ⊎ 2 ∣ d
        inj₁-sum with rec
        ...   | inj₁ e = inj₁ e
        ...   | inj₂ t2 = ⊥-elim (nt2 t2)



-- ¬2∣a → Coprime a (pow2 k)（经 div-pow2 分类）
coprime-a-pow2 : ∀ k a → ¬ (2 ∣ a) → Coprime a (pow2 k)
coprime-a-pow2 k a nt2 {e} (e∣a , e∣pow2) with div-pow2 k e e∣pow2
...   | inj₁ e≡1 = e≡1
...   | inj₂ 2∣e = ⊥-elim (nt2 (∣-trans 2∣e e∣a))

--------------------------------------------------------------------------------
-- §5. 素性迭代主引理（强化假设版，coprime-divisor 一步收缩）
--------------------------------------------------------------------------------

pow2-∣-iter : ∀ k a b → Coprime a (pow2 k) → pow2 k ∣ a * b → pow2 k ∣ b
pow2-∣-iter k a b c h = coprime-divisor (coprime-2-a-aux k a c) h
  where coprime-2-a-aux : ∀ k a → Coprime a (pow2 k) → Coprime (pow2 k) a
        coprime-2-a-aux k a c (d∣pow2 , d∣a) = c (d∣a , d∣pow2)

--------------------------------------------------------------------------------
-- §6. 奇偶两侧收缩（四分的数学核心）
--   奇 a：pow2 k ∣ a·suc(a) → pow2 k ∣ suc(a)（a 与 pow2 k 互素，iter 直接收缩）
--   偶 a：pow2 k ∣ a·suc(a) → pow2 k ∣ a（suc(a) 奇，与 pow2 k 互素，同上）
--   ——两引理合取即「赋值落到相邻 pair 的某一侧」，是 mod-4 赋值分析的代数核心
--------------------------------------------------------------------------------

2∣1-clash : 2 ∣ 1 → ⊥
2∣1-clash (divides zero ())            -- 1 ≡ 0 封闭 clash
2∣1-clash (divides (suc zero) ())      -- 1 ≡ 2 封闭 clash
2∣1-clash (divides (suc (suc q)) ())   -- 1 ≡ (2+q)·2 深度 clash

two-odd-b : ∀ k a → ¬ (2 ∣ a) → pow2 k ∣ a * suc a → pow2 k ∣ suc a
two-odd-b k a nt2 h = pow2-∣-iter k a (suc a) (coprime-a-pow2 k a nt2) h

two-even-a : ∀ k a → 2 ∣ a → pow2 k ∣ a * suc a → pow2 k ∣ a
two-even-a k a h2∣a h = pow2-∣-iter k (suc a) a (coprime-suc-pow2 h2∣a) (subst (λ w → pow2 k ∣ w) (*-comm a (suc a)) h)
  where
    -- suc a 奇（a 偶）→ Coprime (suc a) (pow2 k)：需 ¬2∣suc a
    -- a 偶 → suc a 奇：2∣suc a ∧ 2∣a → 2∣suc a ∸ a = 1 → 1 ≡ 2 clash
    coprime-suc-pow2 : 2 ∣ a → Coprime (suc a) (pow2 k)
    coprime-suc-pow2 h2∣a = coprime-a-pow2 k (suc a) (suc-a-odd h2∣a)
      where
        suc-a-odd : 2 ∣ a → ¬ (2 ∣ suc a)
        suc-a-odd h2∣a (divides q eq) = 2∣1-clash (∣m+n∣n⇒∣m (divides q eq) h2∣a)

--------------------------------------------------------------------------------
-- §7. 2 侧主定理分裂件（全幂保持，无半幂弱化）
--   x∸1 奇 → x∸1 与 pow2 k 互素 → pow2 k∣(x∸1)·suc x 全部落 suc x 侧
--   suc x 奇 → 同理全落 x∸1 侧
--------------------------------------------------------------------------------

two-side-odd-a : ∀ k x → pow2 k ∣ x * x ∸ 1 → ¬ (2 ∣ x ∸ 1) → pow2 k ∣ suc x
two-side-odd-a k x h nt2 =
  pow2-∣-iter k (x ∸ 1) (suc x) (coprime-a-pow2 k (x ∸ 1) nt2) h1
  where h1 : pow2 k ∣ (x ∸ 1) * suc x
        h1 = subst (λ w → pow2 k ∣ w) (sym (px x)) h

two-side-odd-b : ∀ k x → pow2 k ∣ x * x ∸ 1 → ¬ (2 ∣ suc x) → pow2 k ∣ x ∸ 1
two-side-odd-b k x h nt2 =
  pow2-∣-iter k (suc x) (x ∸ 1) (coprime-a-pow2 k (suc x) nt2) h2
  where
    h1 : pow2 k ∣ (x ∸ 1) * suc x
    h1 = subst (λ w → pow2 k ∣ w) (sym (px x)) h
    h2 : pow2 k ∣ suc x * (x ∸ 1)
    h2 = subst (λ w → pow2 k ∣ w) (*-comm (x ∸ 1) (suc x)) h1

--------------------------------------------------------------------------------
-- §8. 双重消二（偶-偶分支核心）
--   2∣a → 2∣b → pow2 (suc (suc k)) ∣ a·b
--   → Σ ha , Σ hb , (a ≡ 2·ha × b ≡ 2·hb × pow2 k ∣ ha·hb)
--   证明：两 divides 字段取半值，subst 进 h 后 *-cancelˡ-∣ 两次
--------------------------------------------------------------------------------

-- 半值对重排：(qa·2)·(qb·2) ≡ 2·(2·(qa·qb))
rearr : ∀ qa qb → (qa * 2) * (qb * 2) ≡ 2 * (2 * (qa * qb))
rearr qa qb =
  (qa * 2) * (qb * 2)
    ≡⟨ cong (λ w → w * (qb * 2)) (*-comm qa 2) ⟩
  (2 * qa) * (qb * 2)
    ≡⟨ *-assoc 2 qa (qb * 2) ⟩
  2 * (qa * (qb * 2))
    ≡⟨ cong (λ w → 2 * (qa * w)) (*-comm qb 2) ⟩
  2 * (qa * (2 * qb))
    ≡⟨ cong (λ w → 2 * w) (sym (*-assoc qa 2 qb)) ⟩
  2 * ((qa * 2) * qb)
    ≡⟨ cong (λ w → 2 * (w * qb)) (*-comm qa 2) ⟩
  2 * ((2 * qa) * qb)
    ≡⟨ cong (λ w → 2 * w) (*-assoc 2 qa qb) ⟩
  2 * (2 * (qa * qb))
  ∎
  where open ≡-Reasoning

two-cancel-twice : ∀ k a b → 2 ∣ a → 2 ∣ b → pow2 (suc (suc k)) ∣ a * b
                 → Σ ℕ (λ ha → Σ ℕ (λ hb → (a ≡ ha * 2) × (b ≡ hb * 2) × pow2 k ∣ ha * hb))
two-cancel-twice k a b (divides qa eqa) (divides qb eqb) h =
  qa , qb , eqa , eqb , *-cancelˡ-∣ 2 (*-cancelˡ-∣ 2 h3)
  where
    open ≡-Reasoning
    -- 半值替换：a ≡ 2·qa → pow2 (suc (suc k)) ∣ (2·qa) * b
    h1 : pow2 (suc (suc k)) ∣ (qa * 2) * b
    h1 = subst (λ w → pow2 (suc (suc k)) ∣ w * b) eqa h
    -- b 半值替换：→ pow2 (suc (suc k)) ∣ (2·qa) * (2·qb)
    h2 : pow2 (suc (suc k)) ∣ (qa * 2) * (qb * 2)
    h2 = subst (λ w → pow2 (suc (suc k)) ∣ (qa * 2) * w) eqb h1
    -- 重排成 2·(2·(...)) 形以消二：*(2·qa)*(2·qb) = 2·(2·(qa·qb)) 的链
    -- 重排 + 双消二：pow2 (suc(suc k)) ≡ 2·pow2 (suc k) 定义性，h2 经 rearr 后逐层消
    h3 : pow2 (suc (suc k)) ∣ 2 * (2 * (qa * qb))
    h3 = subst (λ w → pow2 (suc (suc k)) ∣ w) (rearr qa qb) h2

--------------------------------------------------------------------------------
-- §9. 相邻识别：x∸1 ≡ ha·2 ∧ suc x ≡ hb·2 → hb ≡ suc ha
--   x 分裂（zero 不可达 / suc m 半值替换）+ 2·suc ha ≡ suc (suc (2·ha)) 算术链
--------------------------------------------------------------------------------

2*suc≡suc2* : ∀ ha → 2 * suc ha ≡ suc (suc (2 * ha))
2*suc≡suc2* ha =
  trans refl
  (trans (cong (λ w → suc ha + w) (*-identityˡ (suc ha)))
  (trans (cong suc (+-comm ha (suc ha)))
  (trans (cong suc (cong suc (sym (+-identityʳ (ha + ha)))))
  (cong suc (cong suc (+-assoc ha ha zero))))))

--------------------------------------------------------------------------------
-- §10. 相邻识别主引理
--------------------------------------------------------------------------------

adjacent-half : ∀ x ha hb → x ∸ 1 ≡ ha * 2 → suc x ≡ hb * 2 → hb ≡ suc ha
adjacent-half x ha hb eqa eqb with x
...   | zero = ⊥-elim (2∣1-clash hb2∣1)
  where
    hb2∣1 : 2 ∣ 1
    hb2∣1 = divides hb eqb
...   | suc m = *-cancelˡ-≡ hb (suc ha) 2 hb2≡2suc
  where
    m≡2ha : m ≡ ha * 2
    m≡2ha = eqa
    hb2≡suc2 : hb * 2 ≡ suc (suc (ha * 2))
    hb2≡suc2 = sym (subst (λ w → w ≡ hb * 2) (cong (λ w → suc (suc w)) m≡2ha) eqb)
    hb2≡2suc : 2 * hb ≡ 2 * suc ha
    hb2≡2suc = trans (*-comm 2 hb) (trans hb2≡suc2 (trans (cong (λ w → suc (suc w)) (*-comm ha 2)) (sym (2*suc≡suc2* ha))))

--------------------------------------------------------------------------------
-- §11. 2 侧二分主定理
--------------------------------------------------------------------------------

h1'-lemma : ∀ x → pow2 16 ∣ x * x ∸ 1 → pow2 16 ∣ (x ∸ 1) * suc x
h1'-lemma x h = subst (λ w → pow2 16 ∣ w) (sym (px x)) h

coprime-hb-pow2 : ∀ x ha hb → 2 ∣ ha → x ∸ 1 ≡ ha * 2 → suc x ≡ hb * 2 → Coprime hb (pow2 14)
coprime-hb-pow2 x ha hb h2∣ha eqa eqb = coprime-a-pow2 14 hb (odd-hb x ha hb h2∣ha eqa eqb)
  where
    odd-hb : ∀ x ha hb → 2 ∣ ha → x ∸ 1 ≡ ha * 2 → suc x ≡ hb * 2 → ¬ (2 ∣ hb)
    odd-hb x ha hb h2∣ha eqa eqb h2∣hb = 2∣1-clash h2∣1
      where
        hb≡sucha : hb ≡ suc ha
        hb≡sucha = adjacent-half _ ha hb eqa eqb
        h2∣suc-ha : 2 ∣ suc ha
        h2∣suc-ha = subst (λ w → 2 ∣ w) hb≡sucha h2∣hb
        h2∣1 : 2 ∣ 1
        h2∣1 = ∣m+n∣n⇒∣m h2∣suc-ha h2∣ha

-- 乘二保整除：pow2 k ∣ q → 2·pow2 k ∣ q·2
pow2-∣-mul-r : ∀ k q → pow2 k ∣ q → 2 * pow2 k ∣ q * 2
pow2-∣-mul-r k q (divides q₁ eq₁) =
  divides q₁ (trans (cong (λ w → w * 2) eq₁)
  (trans (*-assoc q₁ (pow2 k) 2) (cong (λ w → q₁ * w) (*-comm (pow2 k) 2))))

--------------------------------------------------------------------------------
-- §12. 2 侧四分合成（2^16 层）
--   x² ≡ 1 (mod 2^16) → 四种情形：
--   ① 2^16∣x∸1（x ≡ 1 类）② 2^16∣suc x（x ≡ -1 类）
--   ③ 2^15∣x∸1 ∧ 2^16∤x∸1（x ≡ 1+2^15 类）④ 2^15∣suc x ∧ 2^16∤suc x（x ≡ -1+2^15 类）
--   组装：two-side 的 2^15 二分 + pow2 16 ∣? 判定器逐侧分裂
--------------------------------------------------------------------------------

two-parity : ∀ x ha hb → Dec (2 ∣ ha) → pow2 14 ∣ ha * hb → x ∸ 1 ≡ ha * 2 → suc x ≡ hb * 2
           → pow2 15 ∣ x ∸ 1 ⊎ pow2 15 ∣ suc x
two-parity x ha hb (yes t2) h14 eqa eqb = inj₁ two-even-ha-side
  where
    h∣ha : pow2 14 ∣ ha
    h∣ha = pow2-∣-iter 14 hb ha coprime-hb h14c
      where
        coprime-hb : Coprime hb (pow2 14)
        coprime-hb = coprime-hb-pow2 x ha hb t2 eqa eqb
        h14c : pow2 14 ∣ hb * ha
        h14c = subst (λ w → pow2 14 ∣ w) (*-comm ha hb) h14
    two-even-ha-side : pow2 15 ∣ x ∸ 1
    two-even-ha-side = ha-form
      where ha-form : 2 * pow2 14 ∣ x ∸ 1
            ha-form = subst (λ w → 2 * pow2 14 ∣ w) (sym eqa) (pow2-∣-mul-r 14 ha h∣ha)
two-parity x ha hb (no nt2) h14 eqa eqb = inj₂ two-odd-hb-side
  where
    h∣hb : pow2 14 ∣ hb
    h∣hb = pow2-∣-iter 14 ha hb (coprime-a-pow2 14 ha nt2) h14
    two-odd-hb-side : pow2 15 ∣ suc x
    two-odd-hb-side = hb-form
      where hb-form : 2 * pow2 14 ∣ suc x
            hb-form = subst (λ w → 2 * pow2 14 ∣ w) (sym eqb) (pow2-∣-mul-r 14 hb h∣hb)

--------------------------------------------------------------------------------
-- §12. 2 侧四分合成（2^16 层）
--   x² ≡ 1 (mod 2^16) → 四种情形：
--   ① 2^16∣x∸1（x ≡ 1 类）② 2^16∣suc x（x ≡ -1 类）
--   ③ 2^15∣x∸1 ∧ 2^16∤x∸1（x ≡ 1+2^15 类）④ 2^15∣suc x ∧ 2^16∤suc x（x ≡ -1+2^15 类）
--   组装：two-side 的 2^15 二分 + pow2 16 ∣? 判定器逐侧分裂
--------------------------------------------------------------------------------

even-even : ∀ x → pow2 16 ∣ x * x ∸ 1 → 2 ∣ x ∸ 1 → 2 ∣ suc x
          → pow2 15 ∣ x ∸ 1 ⊎ pow2 15 ∣ suc x
even-even x h t2 t2s = aux x t2 t2s (h1'-lemma x h)
  where
    aux : ∀ x → 2 ∣ x ∸ 1 → 2 ∣ suc x → pow2 16 ∣ (x ∸ 1) * suc x
        → pow2 15 ∣ x ∸ 1 ⊎ pow2 15 ∣ suc x
    aux x t2 t2s h1 with two-cancel-twice 14 (x ∸ 1) (suc x) t2 t2s h1
    ...   | (ha , hb , eqa , eqb , h14) = two-parity x ha hb t2 h14 eqa eqb

two-even-branch : ∀ x → pow2 16 ∣ x * x ∸ 1 → 2 ∣ x ∸ 1
                → pow2 15 ∣ x ∸ 1 ⊎ pow2 15 ∣ suc x
two-even-branch x h t2 with 2 ∣? suc x
...   | no nt2s = inj₁ (two-side-odd-b 16 x h nt2s)
...   | yes t2s = even-even x h t2 t2s


two-side : ∀ x → pow2 16 ∣ x * x ∸ 1 → pow2 15 ∣ x ∸ 1 ⊎ pow2 15 ∣ suc x
two-side x h with 2 ∣? (x ∸ 1)
...   | no nt2 = inj₂ (two-side-odd-a 16 x h nt2)
...   | yes t2 = two-even-branch x h t2

-- ⚠ 工具链限制（prover_limits: agda-pow2-div-dec-mod-helper-explosion）：
--   `pow2 16 ∣? 符号参数` 将 pow2 16 归约为 65536 深 unary 项，mod-helper 符号循环 → 24G 堆爆。
--   因此四分定理取「判定器外置」形式：Dec 结果由调用方（对具体 x 数值可安全计算）供给。
fourfold′ : ∀ x → pow2 16 ∣ x * x ∸ 1
          → Dec (pow2 16 ∣ x ∸ 1) → Dec (pow2 16 ∣ suc x)
          → (pow2 16 ∣ x ∸ 1)
          ⊎ (pow2 16 ∣ suc x)
          ⊎ (pow2 15 ∣ x ∸ 1 × ¬ pow2 16 ∣ x ∸ 1)
          ⊎ (pow2 15 ∣ suc x × ¬ pow2 16 ∣ suc x)
fourfold′ x h (yes t16) _ = inj₁ t16
fourfold′ x h (no _) (yes t16s) = inj₂ (inj₁ t16s)
fourfold′ x h (no n16a) (no n16b) with two-side x h
...   | inj₁ t15 = inj₂ (inj₂ (inj₁ (t15 , n16a)))
...   | inj₂ t15 = inj₂ (inj₂ (inj₂ (t15 , n16b)))
