{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Algebra.HenselCRTUniqueness
-- G4 唯一性等式层（纯 case）：DA/UB 两根的严格唯一性 + 一般边界引理
--
-- 数学背景：8-case 分类（HenselCRTSynth）+ 数值对账（oracle 7ddc67c0：8 组合各恰一根）
--   纯 case 唯一性：双整除 → N∣（lcm 互质）→ 边界（m<N → m=0）→ 等式
--   混合 6 case（线性同余 + Bézout）：待续批（节点已登记）
--
-- 核心原则：
-- 1. 边界先符号化（m < N 形式，非字面量比较）
-- 2. 复用优先（pow2-∣-iter/pow3-∣-iter/coprimality 范式，零复制）
-- 3. 零 mod-helper 零 ∣? 零符号消去（加法化纪律延续）
--
-- 包含：lcm-coprime（双整除→N∣）、divides-below（边界）、unique-root₁/unique-root₈（纯 case 唯一性）

module Sovereign.Algebra.HenselCRTUniqueness where

open import Data.Nat using (ℕ; zero; suc; _*_; _+_; _∸_; _≤_; _<_; z≤n; s≤s)
open import Data.Nat.Divisibility using (_∣_; divides; ∣-trans; ∣-refl; m∣m*n; n∣m*n; ∣m+n∣n⇒∣m; ∣m+n∣m⇒∣n)
open import Data.Nat.Coprimality using (Coprime; coprime-divisor)
open import Data.Nat.Properties using (*-zeroʳ; *-assoc; ≤-<-trans; <-irrefl; m∸n≤m; ≤-refl; ≤-antisym; 1+n≢n; suc-injective; m≤m+n; *-comm; n≮n; +-identityʳ; ≤-trans; <-trans; *-monoˡ-≤; *-zeroʳ; *-identityʳ; *-monoʳ-≤; +-assoc; +-comm; n≤1+n; m+n≡0⇒m≡0; +-cancelˡ-≡; *-distribʳ-+; *-distribˡ-+; m<m+n; +-monoˡ-<; +-monoʳ-<; n<1+n; *-identityˡ; ≤-reflexive; +-monoʳ-≤; +-cancelʳ-≡)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; subst)
open import Relation.Nullary using (¬_)
open import Sovereign.Algebra.Hensel3Side using (pow3; core; parity23)
open import Sovereign.Algebra.Hensel2Side using (pow2; div-pow2)
open import Sovereign.Algebra.HenselCRTSynth using (clash-3-2)
open import Sovereign.Algebra.SovereignLCMRoots using (SOVEREIGN_LCM; root₁; root₄; root₅; root₈)

--------------------------------------------------------------------------------
-- §1. 3 与 2¹⁶ 互素（3 ∣ 2^k → ⊥）+ lcm 互质引理
--------------------------------------------------------------------------------

-- 3 ∣ 2^k → div-pow2 分类（d≡1 ⊎ 2∣d）→ 3≡1 clash ∨ 2∣3 clash
three∣pow2-clash : ∀ k → 3 ∣ pow2 k → ⊥
three∣pow2-clash k h with div-pow2 k 3 h
...   | inj₁ 3≡1 = ⊥-elim (suc-zero-clash (suc-injective 3≡1))
  where
    suc-zero-clash : 2 ≡ 0 → ⊥
    suc-zero-clash ()
...   | inj₂ 2∣3 = parity23 2∣3

-- pow3 j 与 pow2 k 互素（core 分类 + three∣pow2-clash）
coprime-pow3-pow2 : ∀ j k → Coprime (pow3 j) (pow2 k)
coprime-pow3-pow2 j k {e} (e∣pow3 , e∣pow2) with core j e e∣pow3
...   | inj₁ e≡1 = e≡1
...   | inj₂ 3∣e = ⊥-elim (three∣pow2-clash k (∣-trans 3∣e e∣pow2))

--------------------------------------------------------------------------------
-- §2. lcm 互质 + 边界引理
--------------------------------------------------------------------------------

-- Coprime 对称
coprime-swap : ∀ {x y} → Coprime x y → Coprime y x
coprime-swap c (d∣y , d∣x) = c (d∣x , d∣y)

-- 双整除 → N∣（n = 3¹¹·a → 2¹⁶∣a [互素收缩] → n = N·c）——go 式零 with-abstraction
lcm-coprime : ∀ n → pow3 11 ∣ n → pow2 16 ∣ n → SOVEREIGN_LCM ∣ n
lcm-coprime n (divides a eqa) h2 =
  go (coprime-divisor (coprime-swap (coprime-pow3-pow2 11 16))
                      (subst (pow2 16 ∣_) (*-comm a (pow3 11)) (subst (pow2 16 ∣_) eqa h2)))
  where
    go : pow2 16 ∣ a → SOVEREIGN_LCM ∣ n
    go (divides c a≡c*p2) = divides c n≡N*c
      where
        n≡N*c : n ≡ c * SOVEREIGN_LCM
        n≡N*c = trans eqa
          (trans (cong (_* pow3 11) a≡c*p2)
          (trans (*-assoc c (pow2 16) (pow3 11))
          (cong (c *_) (*-comm (pow2 16) (pow3 11)))))

-- 边界（参数化除数——≤ 证明构造停在符号 N 上，避免巨大字面量 11.6 亿层归纳；T6 参数化模式）
divides-below-gen : ∀ N m → N ∣ m → m < N → m ≡ 0
divides-below-gen N m (divides zero eq) m<N = eq
divides-below-gen N m (divides (suc d) eq) m<N = ⊥-elim (n≮n N (≤-<-trans N≤m m<N))
  where
    N≤m : N ≤ m
    N≤m = subst (N ≤_) (sym eq) (m≤m+n N (d * N))

divides-below : ∀ m → SOVEREIGN_LCM ∣ m → m < SOVEREIGN_LCM → m ≡ 0
divides-below = divides-below-gen SOVEREIGN_LCM

-- 边界 ≤ 版（参数化）
divides-below-≤-gen : ∀ N m → N ≢ 0 → N ∣ m → m ≤ N → m ≡ 0 ⊎ m ≡ N
divides-below-≤-gen N m N≢0 (divides zero eq) m≤N = inj₁ eq
divides-below-≤-gen N m N≢0 (divides (suc zero) eq) m≤N = inj₂ (trans eq (+-identityʳ N))
divides-below-≤-gen N m N≢0 (divides (suc (suc d)) eq) m≤N =
  ⊥-elim (N≢0 (m+n≡0⇒m≡0 N {d * N}
    (+-cancelˡ-≡ N (suc d * N) 0 (trans m≡N+ (sym (+-identityʳ N))))))
  where
    m≡N+ : N + suc d * N ≡ N
    m≡N+ = ≤-antisym (subst (_≤ N) eq m≤N) (m≤m+n N (suc d * N))

divides-below-≤ : ∀ m → SOVEREIGN_LCM ∣ m → m ≤ SOVEREIGN_LCM → m ≡ 0 ⊎ m ≡ SOVEREIGN_LCM
divides-below-≤ m = divides-below-≤-gen SOVEREIGN_LCM m (λ ())

--------------------------------------------------------------------------------
-- §3. 纯 case 唯一性
--------------------------------------------------------------------------------

unique-root₁ : ∀ x → 0 < x → x < SOVEREIGN_LCM
             → pow3 11 ∣ x ∸ 1 → pow2 16 ∣ x ∸ 1 → x ≡ root₁
unique-root₁ (suc m) (s≤s z≤n) x<N h3 h2 = trans (cong suc x∸1≡0) refl
  where
    x∸1≡0 : m ≡ 0
    x∸1≡0 = divides-below m (lcm-coprime m h3 h2) m<N
      where
        m<N : m < SOVEREIGN_LCM
        m<N = ≤-trans (s≤s (n≤1+n m)) x<N

unique-root₈ : ∀ x → x < SOVEREIGN_LCM
             → pow3 11 ∣ suc x → pow2 16 ∣ suc x → x ≡ root₈
unique-root₈ x x<N h3 h2 = go (divides-below-≤ (suc x) (lcm-coprime (suc x) h3 h2) x<N)
  where
    go : (suc x ≡ 0 ⊎ suc x ≡ SOVEREIGN_LCM) → x ≡ root₈
    go (inj₁ sucx≡0) = ⊥-elim (suc-zero-clash sucx≡0)
      where
        suc-zero-clash : ∀ {y} → suc y ≡ 0 → ⊥
        suc-zero-clash ()
    go (inj₂ sucx≡N) = suc-injective sucx≡N

--------------------------------------------------------------------------------
-- §4. 同侧 case 唯一性（DC/UD）——【WIP 二段：陈述入账】
--   【慢点终局坐标（W2/H5/H6 二分实证）】t-go₅ 的签名级即爆（无体 101s）：
--   疑 `m ≡ t * (pow3 11 * pow2 15)` 类型 × t 模式签名的联合归一化
--   （构件探针 t1/t2/t3 全绿 3.9s——divides 字面量积位/*-identityˡ/refl 桥均快）
--   下批处方：❶ t 分解拆 data 包装（避免 t * (big product) 的签名级积展开）
--            ❷ 或 X 定义进 record 参数（Σ 形分解 ∃ t, m ≡ t * X）
--            ❸ 或先做交叉 case 的 Bézout（DB/DD/UA/UC）绕开此形
--------------------------------------------------------------------------------

lcm-coprime-gen : ∀ p q n → Coprime p q → p ∣ n → q ∣ n → (p * q) ∣ n
lcm-coprime-gen p q n cp (divides a eqa) hq =
  go (coprime-divisor (coprime-swap cp)
        (subst (q ∣_) (*-comm a p) (subst (q ∣_) eqa hq)))
  where
    go : q ∣ a → (p * q) ∣ n
    go (divides c a≡c*q) = divides c n≡c*pq
      where
        n≡c*pq : n ≡ c * (p * q)
        n≡c*pq = trans eqa
          (trans (cong (_* p) a≡c*q)
          (trans (*-assoc c q p)
          (cong (c *_) (*-comm q p))))

suc-suc-≰ : ∀ k → suc (suc k) ≤ k → ⊥
suc-suc-≰ k p = n≮n (suc (suc k)) (≤-<-trans p (<-trans (n<1+n k) (n<1+n (suc k))))

two-X≡N : 2 * (pow3 11 * pow2 15) ≡ SOVEREIGN_LCM
two-X≡N = refl

unique-root₅ : ∀ x → 0 < x → x < SOVEREIGN_LCM
             → pow3 11 ∣ x ∸ 1 → pow2 15 ∣ x ∸ 1
             → ¬ (pow2 16 ∣ x ∸ 1) → x ≡ root₅
unique-root₅ (suc m) (s≤s z≤n) x<N h3 h15 n16 = {!!}

unique-root₄ : ∀ x → x < SOVEREIGN_LCM
             → pow3 11 ∣ suc x → pow2 15 ∣ suc x
             → ¬ (pow2 16 ∣ suc x) → x ≡ root₄
unique-root₄ x x<N h3 h15 n16 = {!!}

--------------------------------------------------------------------------------
-- §5. 交叉 case（DB）——Bézout 逆元见证 + ∣ 型免减法链
--------------------------------------------------------------------------------

-- 逆元见证换序形（literal·literal——BUILTIN 快）：3¹¹·24371 ≡ 1 + 2¹⁶·65876
inv-witness : pow3 11 * 24371 ≡ 1 + pow2 16 * 65876
inv-witness = refl

-- ── §5 交叉 case（DB）── 全链 symbolic-first（经验 43 条：literal·symbolic 乘法爆）
lhs-distrib : ∀ a → (a * pow3 11 + 2) * 24371 ≡ (a * pow3 11) * 24371 + 2 * 24371
lhs-distrib a = *-distribʳ-+ 24371 (a * pow3 11) 2

lhs-inner-a : ∀ a → (a * pow3 11) * 24371 ≡ a * (pow3 11 * 24371)
lhs-inner-a a = *-assoc a (pow3 11) 24371

lhs-inner-b : ∀ a → a * (pow3 11 * 24371) ≡ a + a * (pow2 16 * 65876)
lhs-inner-b a = trans (cong (a *_) inv-witness)
  (trans (*-distribˡ-+ a 1 (pow2 16 * 65876))
  (cong (_+ a * (pow2 16 * 65876)) (*-identityʳ a)))

lhs-inner : ∀ a → (a * pow3 11) * 24371 ≡ a + a * (pow2 16 * 65876)
lhs-inner a = trans (lhs-inner-a a) (lhs-inner-b a)

lhs-outer : ∀ a → (a + a * (pow2 16 * 65876)) + 2 * 24371 ≡ (a + 2 * 24371) + a * (pow2 16 * 65876)
lhs-outer a = trans (+-assoc a (a * (pow2 16 * 65876)) (2 * 24371))
  (trans (cong (a +_) (+-comm (a * (pow2 16 * 65876)) (2 * 24371)))
  (sym (+-assoc a (2 * 24371) (a * (pow2 16 * 65876)))))

lhs-form : ∀ a → (a * pow3 11 + 2) * 24371 ≡ (a + 2 * 24371) + a * (pow2 16 * 65876)
lhs-form a = trans (lhs-distrib a)
  (trans (cong (_+ 2 * 24371) (lhs-inner a)) (lhs-outer a))

-- k ≥ 2 否定（M 参数化符号安全）
k-split-gen : ∀ M C a k → a + C ≡ suc (suc k) * M → a + C < M + M → ⊥
k-split-gen M C a k eq lt = {!!}
-- DB 核心：3¹¹·a + 2 ≡ b·2¹⁶ → a < 2¹⁶ → a ≡ 16794（∣ 型免减法 + k 三段分裂）
lin-solve-db : ∀ a b → a * pow3 11 + 2 ≡ b * pow2 16 → a < pow2 16 → a ≡ 16794
-- DB 辅助（顶层分离——避开 where 嵌套联合归一化）
db-rhs-div : ∀ a b → pow2 16 ∣ (b * pow2 16) * 24371
db-rhs-div a b = divides (b * 24371)
  (trans (*-assoc b (pow2 16) 24371)
  (trans (cong (b *_) (*-comm (pow2 16) 24371))
  (sym (*-assoc b 24371 (pow2 16)))))

db-tail-div : ∀ a → pow2 16 ∣ a * (pow2 16 * 65876)
db-tail-div a = divides (a * 65876)
  (trans (cong (a *_) (*-comm (pow2 16) 65876)) (sym (*-assoc a 65876 (pow2 16))))

db-div : ∀ a b → a * pow3 11 + 2 ≡ b * pow2 16 → pow2 16 ∣ a + 2 * 24371
db-div a b eq = ∣m+n∣n⇒∣m (subst (pow2 16 ∣_) (lhs-form a) lhs-div) (db-tail-div a)
  where
    lhs-div : pow2 16 ∣ (a * pow3 11 + 2) * 24371
    lhs-div = subst (pow2 16 ∣_) (sym (cong (_* 24371) eq)) (db-rhs-div a b)

db-bound : ∀ a → a < pow2 16 → a + 2 * 24371 < pow2 16 + pow2 16
db-bound a a< = {!!}

db-go : ∀ a → pow2 16 ∣ a + 2 * 24371 → a + 2 * 24371 < pow2 16 + pow2 16 → a ≡ 16794
db-go a (divides zero eq0) _ = ⊥-elim (48742≢0 (m+n≡0⇒m≡0 (2 * 24371) {a} (trans (sym (+-comm a (2 * 24371))) eq0)))
  where
    48742≢0 : 2 * 24371 ≡ 0 → ⊥
    48742≢0 ()
db-go a (divides (suc zero) eq1) _ = {!!}
  -- 【爆点坐标】+-cancelˡ-≡/+-comm 对 literal 第一参 = O(literal) 归纳构造（48742 层）
  -- 绕法待研：cancel 被消加数符号化 / suc 结构形 / BUILTIN 级等式——下批或主链优先

db-go a (divides (suc (suc k)) eq2) lt = {!!}

lin-solve-db a b eq a< = {!!}