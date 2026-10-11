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
open import Data.Nat.Properties using (*-zeroʳ; *-assoc; ≤-<-trans; <-≤-trans; <-irrefl; m∸n≤m; m∸n≡0⇒m≤n; m≤n*m; ≤-refl; ≤-antisym; 1+n≢n; suc-injective; m≤m+n; *-comm; n≮n; +-identityʳ; ≰⇒>; ≤-trans; ≤-step; +-suc; <-trans; *-monoˡ-≤; m≤n+m; *-distribʳ-+; *-zeroʳ; *-identityʳ; *-monoʳ-≤; +-assoc; +-swap; +-comm; n≤1+n; m+n≡0⇒m≡0; +-cancelˡ-≡; *-distribʳ-+; *-distribˡ-+; m<m+n; +-monoˡ-<; +-mono-<; +-monoʳ-<; n<1+n; *-identityˡ; ≤-reflexive; +-monoʳ-≤; +-cancelʳ-≡)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; subst; cong₂)
open import Relation.Nullary using (¬_)
open import Sovereign.Algebra.Hensel3Side using (pow3; core; parity23)
open import Sovereign.Algebra.Hensel2Side using (pow2; div-pow2; two-add)
open import Sovereign.Algebra.HenselCRTSynth using (clash-3-2)
open import Sovereign.Algebra.SovereignLCMRoots using (SOVEREIGN_LCM; root₁; root₃; root₄; root₅; root₈)

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

-- （unique-root₅ / unique-root₄ 的定义移至 §8 unique-root₃-same 之后——需前向引用 unique-root₃-same）

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
k-split-gen M C a k eq lt = n≮n (M + M) (≤-<-trans M+M≤a+C lt)
  where
    M+M≤a+C : M + M ≤ a + C
    M+M≤a+C = subst (M + M ≤_) (sym eq) (+-monoʳ-≤ M (m≤m+n M (k * M)))
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

-- 字面桥（oracle b5bdad33 已验）：2·24371 + 16794 = 2¹⁶ → 2·24371 < 2¹⁶
lit-C+16794 : 2 * 24371 + 16794 ≡ pow2 16
lit-C+16794 = refl

-- 显式 n 包装（避开 m<m+n 隐式 n 的字面合一爆：48742 + ?n ≡?= 65536 逐层剥 suc 二次复杂度）
m<m+n-e : ∀ m n → 0 < n → m < m + n
m<m+n-e m n = m<m+n m {n}

-- 两段拆分（钉死隐式 n，零复合精化）：
lit-C<C+16794 : 2 * 24371 < 2 * 24371 + 16794
lit-C<C+16794 = m<m+n-e (2 * 24371) 16794 (s≤s z≤n)

lit-C<pow2 : 2 * 24371 < pow2 16
lit-C<pow2 = subst (2 * 24371 <_) lit-C+16794 lit-C<C+16794

db-bound : ∀ a → a < pow2 16 → a + 2 * 24371 < pow2 16 + pow2 16
db-bound a a< = +-mono-< a< lit-C<pow2

db-go : ∀ a → pow2 16 ∣ a + 2 * 24371 → a + 2 * 24371 < pow2 16 + pow2 16 → a ≡ 16794
db-go a (divides zero eq0) _ = ⊥-elim (48742≢0 (m+n≡0⇒m≡0 (2 * 24371) {a} (trans (sym (+-comm a (2 * 24371))) eq0)))
  where
    48742≢0 : 2 * 24371 ≡ 0 → ⊥
    48742≢0 ()
db-go a (divides (suc zero) eq1) _ = +-cancelʳ-≡ (2 * 24371) a 16794 (trans eq1 lit-1≡16794+C)
  where
    -- 1·2¹⁶ = 65536 = 16794 + 48742（refl 级）
    lit-1≡16794+C : suc zero * pow2 16 ≡ 16794 + 2 * 24371
    lit-1≡16794+C = refl

db-go a (divides (suc (suc k)) eq2) lt = ⊥-elim (k-split-gen (pow2 16) (2 * 24371) a k eq2 lt)

lin-solve-db a b eq a< = db-go a (db-div a b eq) (db-bound a a<)

-- 线2 尾（mod 形整体构造路线——go 直接吃 db-go，q 形提取整套消去）：
-- 字面桥（refl 级，安全类：字面等式搬运）
lit-N-form : SOVEREIGN_LCM ≡ pow2 16 * pow3 11
lit-N-form = refl

-- t ≥ 3 否定（M **抽象**——内部零字面爆点；调用点一次性字面实例化 = GMP 级安全）
t3-kill : ∀ M b x → 0 < M → suc x ≡ suc (suc (suc b)) * M → suc x ≤ M + M → ⊥
t3-kill M b x M>0 eq le = n≮n (suc x) (subst (suc x <_) (sym eq) (≤-<-trans le (<-≤-trans lt0 big)))
  where
    lt0 : M + M < (M + M) + M
    lt0 = m<m+n-e (M + M) M M>0
    big : (M + M) + M ≤ suc (suc (suc b)) * M
    big = ≤-trans (≤-reflexive (+-assoc M M M))
      (+-monoʳ-≤ M (+-monoʳ-≤ M (m≤m+n M (b * M))))

-- 线2 尾：a < 2¹⁶ 界（顶层拆分——命名引理击败嵌套精化，见 m<m+n-e 教训）
a<-contra : ∀ a → pow2 16 ≤ a → a * pow3 11 < pow2 16 * pow3 11 → ⊥
a<-contra a pow2≤a a3< = n≮n (pow2 16 * pow3 11)
  (≤-<-trans (*-monoˡ-≤ (pow3 11) pow2≤a) a3<)

a<-from : ∀ a → (pow2 16 ≤ a → ⊥) → a < pow2 16
a<-from a f = ≰⇒> f
--------------------------------------------------------------------------------
m≤m+n-f : ∀ a b → a ≤ a + b
m≤m+n-f a zero = ≤-reflexive (sym (+-identityʳ a))
m≤m+n-f a (suc b) = subst (a ≤_) (sym (+-suc a b)) (≤-step (m≤m+n-f a b))

-- §6. DB case 装配（unique-root₃——破局引理串联）
--------------------------------------------------------------------------------

open import Sovereign.Algebra.ModExtract using (mod-extract; plus-cancel; db-mod-extract; ∣-diff; ∸+-cancel; ∸∸-align-suc; suc∸1-form; ∸-to-+)
open import Data.Nat.Properties using (*-distribʳ-∸; *-comm)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Nat.Properties using (+-suc)
n+1≡suc-f : ∀ n → n + 1 ≡ suc n
n+1≡suc-f zero = refl
n+1≡suc-f (suc n) = cong suc (n+1≡suc-f n)

-- q 分裂 + DB case 装配：a ≡ 16794 + q·65536 → x < N → x ≡ root₃
unique-root₃ : ∀ x → 0 < x → x < SOVEREIGN_LCM
             → pow3 11 ∣ x ∸ 1 → pow2 16 ∣ suc x → x ≡ root₃
unique-root₃ (suc m) (s≤s z≤n) x<N (divides a eqa) (divides b eqb) = go (db-div a b eq-ab)
  where
    eq-ab : a * pow3 11 + 2 ≡ b * pow2 16
    eq-ab = trans (sym (cong (_+ 2) eqa)) (trans (two-add m) eqb)
    n≡0 : ∀ m n → m + n ≡ 0 → n ≡ 0
    n≡0 zero n eq = eq
    n≡0 (suc m) n eq = ⊥-elim (suc≠0-f eq)
      where
        suc≠0-f : suc (m + n) ≡ 0 → ⊥
        suc≠0-f ()
    -- mod 形整体构造（2026-10-10 换轨）：go 直接吃 db-go（其内部 k-split-gen 已排除 q≥2），
    -- 本层只需 a < 2¹⁶ 界 + ∸-to-+ 收口；q-split / q 形提取整套消去
    suc-m-form : suc m ≡ 1 + a * pow3 11
    suc-m-form = ∸-to-+ (suc m) 1 (a * pow3 11) eqa (s≤s z≤n)
    a3< : a * pow3 11 < pow2 16 * pow3 11
    a3< = <-trans (subst (_< suc m) eqa (n<1+n m)) (subst (suc m <_) lit-N-form x<N)
    a< : a < pow2 16
    a< = a<-from a (λ pow2≤a → a<-contra a pow2≤a a3<)
    go : pow2 16 ∣ a + 2 * 24371 → suc m ≡ root₃
    go h = trans (subst (λ w → suc m ≡ 1 + w * pow3 11) (db-go a h (db-bound a a<)) suc-m-form) lit-root3
      where
        lit-root3 : 1 + 16794 * pow3 11 ≡ root₃
        lit-root3 = refl

--------------------------------------------------------------------------------
-- §7. CRT 逆向（mod 形整体构造——路径❷）
--   x+1 = b·2¹⁶ 与 root₃+1 = b₀·2¹⁶ → 2¹⁶ ∣ x ∸ root₃（∸ 形——符号引用）
--   3¹¹ 侧：x∸1 = a·3¹¹ 与 root₃∸1 = a₀·3¹¹ → 3¹¹ ∣ x ∸ root₃
--   → SOVEREIGN_LCM ∣ x ∸ root₃ [lcm-coprime] → x ≡ root₃ + t·N → mod-extract → x ≡ root₃
--------------------------------------------------------------------------------

-- 数值锚（refl 级——oracle 7ddc67c0 已验）：root₃ + 1 = 45395·2¹⁶、root₃ ∸ 1 = 16794·3¹¹
root₃+1-anchor : root₃ + 1 ≡ 45395 * pow2 16
root₃+1-anchor = refl

root₃∸1-anchor : root₃ ∸ 1 ≡ 16794 * pow3 11
root₃∸1-anchor = refl

-- 命名字面引理（钉死隐式元——cong (x ∸_) refl 的元炸弹，命名拆分纪律）
suc-root3∸1 : suc (root₃ ∸ 1) ≡ root₃
suc-root3∸1 = refl

suc-x∸1 : ∀ x → suc (suc x ∸ 1) ≡ suc x
suc-x∸1 x = refl

lit-N-form2 : SOVEREIGN_LCM ≡ pow3 11 * pow2 16
lit-N-form2 = refl

lit-root3-sum : root₃ + 8634499073 ≡ SOVEREIGN_LCM
lit-root3-sum = refl

root3<N : root₃ < SOVEREIGN_LCM
root3<N = subst (root₃ <_) lit-root3-sum (m<m+n-e root₃ 8634499073 (s≤s z≤n))

-- CRT 逆向骨架（WIP——∸ 形引理链设计中）：
--   crt-converse : ∀ x → 3¹¹ ∣ x ∸ 1 → 2¹⁶ ∣ suc x → x < N → x ≡ root₃
--   依赖：∸-+-cancel（stdlib）+ 2¹⁶ ∣ x ∸ root₃ 构造 + 3¹¹ ∣ x ∸ root₃ 构造
--     + lcm-coprime（已证）+ mod-extract（已证 85880747/1eb06959）
h3r-gen : ∀ r → r ≡ root₃ → ∀ x' k → x' ≡ k * pow3 11 → pow3 11 ∣ r ∸ suc x'
h3r-gen r r-def x' k eq = subst (pow3 11 ∣_) (sym (cong (r ∸_) suc-x′-form)) (divides (16794 ∸ k) eq-form)
  where
    suc-x′-form : suc x' ≡ pow3 11 * k + 1
    suc-x′-form = trans (cong suc eq) (trans (sym (n+1≡suc-f (k * pow3 11))) (cong (_+ 1) (*-comm k (pow3 11))))
    bridge-gen : ∀ A B → (pow3 11 * A + 1) ∸ (pow3 11 * B + 1) ≡ (A * pow3 11) ∸ (B * pow3 11)
    bridge-gen A B = trans (∸+-cancel (pow3 11 * A) (pow3 11 * B) 1)
      (trans (cong (_∸ (pow3 11 * B)) (*-comm (pow3 11) A))
      (cong (A * pow3 11 ∸_) (*-comm (pow3 11) B)))
    eq-form : r ∸ (pow3 11 * k + 1) ≡ (16794 ∸ k) * pow3 11
    eq-form = trans (cong (_∸ (pow3 11 * k + 1)) r-def)
      (trans (bridge-gen 16794 k) (sym (*-distribʳ-∸ (pow3 11) 16794 k)))

crt-converse : ∀ x → pow3 11 ∣ x ∸ 1 → pow2 16 ∣ suc x → x < SOVEREIGN_LCM → x ≡ root₃
crt-converse zero h3 (divides b eq) x<N = ⊥-elim (one≢b·2¹⁶ b eq)
  where
    one≢b·2¹⁶ : ∀ b → suc zero ≡ b * pow2 16 → ⊥
    one≢b·2¹⁶ zero ()
    one≢b·2¹⁶ (suc b) eq = n≮n (pow2 16) (≤-<-trans big≤1 one<big)
      where
        -- m≤sucn*m（自制——+ 第一参全符号形：suc b·m stuck-safe）
        m≤n+m-f : ∀ a b → b ≤ a + b
        m≤n+m-f zero b = ≤-reflexive refl
        m≤n+m-f (suc a) b = ≤-step (m≤n+m-f a b)
        m≤sucn*m : ∀ b m → m ≤ suc b * m
        m≤sucn*m zero m = ≤-reflexive (sym (+-identityʳ m))
        m≤sucn*m (suc b) m = ≤-trans (m≤sucn*m b m) (m≤n+m-f m (suc b * m))
        big≤1 : pow2 16 ≤ suc zero
        big≤1 = subst (pow2 16 ≤_) (sym eq) (m≤sucn*m b (pow2 16))
        one<big : suc zero < pow2 16
        one<big = s≤s (s≤s z≤n)
crt-converse (suc x') h3 h16 x<N = finish (div2-side (suc x') h16) (div3-side (suc x') h3)
  where
    div2-side : ∀ x → pow2 16 ∣ suc x → pow2 16 ∣ x ∸ root₃
    div2-side x (divides b eq) = subst (pow2 16 ∣_) (∸+-cancel x root₃ 1) (∣-diff side-x side-r)
      where
        side-x : pow2 16 ∣ x + 1
        side-x = divides b (trans (n+1≡suc-f x) eq)
        side-r : pow2 16 ∣ root₃ + 1
        side-r = divides 45395 root₃+1-anchor
    div3-side : ∀ x → pow3 11 ∣ x ∸ 1 → pow3 11 ∣ x ∸ root₃
    div3-side x h3 = subst (pow3 11 ∣_) align (∣-diff h3 (divides 16794 root₃∸1-anchor))
      where
        align : (x ∸ 1) ∸ (root₃ ∸ 1) ≡ x ∸ root₃
        align = trans (∸∸-align-suc x (root₃ ∸ 1)) (cong (x ∸_) suc-root3∸1)
    div2-gen : ∀ y b' → suc y ≡ b' * pow2 16 → pow2 16 ∣ root₃ ∸ y
    div2-gen y b' eqy = subst (pow2 16 ∣_) (∸+-cancel root₃ y 1) (∣-diff side-r side-y)
      where
        side-r : pow2 16 ∣ root₃ + 1
        side-r = divides 45395 root₃+1-anchor
        side-y : pow2 16 ∣ y + 1
        side-y = divides b' (trans (n+1≡suc-f y) eqy)
    -- 反向 3¹¹ 侧（双向截断差路线）
    div3-gen : pow3 11 ∣ root₃ ∸ suc x'
    div3-gen = subst (pow3 11 ∣_) align-r (∣-diff (divides 16794 root₃∸1-anchor) h3)
      where
        align-r : (root₃ ∸ 1) ∸ (suc x' ∸ 1) ≡ root₃ ∸ suc x'
        align-r = trans (∸∸-align-suc root₃ (suc x' ∸ 1)) (cong (root₃ ∸_) (suc-x∸1 x'))
    div2r : pow2 16 ∣ root₃ ∸ suc x'
    div2r = go h16
      where
        go : pow2 16 ∣ suc (suc x') → pow2 16 ∣ root₃ ∸ suc x'
        go (divides b eq) = div2-gen (suc x') b eq
    finish : pow2 16 ∣ suc x' ∸ root₃ → pow3 11 ∣ suc x' ∸ root₃ → suc x' ≡ root₃
    finish h2 h3' = ≤-antisym (m∸n≡0⇒m≤n d1≡0) (m∸n≡0⇒m≤n d2≡0)
      where
        N∣d1 : SOVEREIGN_LCM ∣ suc x' ∸ root₃
        N∣d1 = lcm-coprime (suc x' ∸ root₃) h3' h2
        N∣d2 : SOVEREIGN_LCM ∣ root₃ ∸ suc x'
        N∣d2 = lcm-coprime (root₃ ∸ suc x') div3-gen div2r
        d1< : suc x' ∸ root₃ < SOVEREIGN_LCM
        d1< = ≤-<-trans (m∸n≤m (suc x') root₃) x<N
        d2< : root₃ ∸ suc x' < SOVEREIGN_LCM
        d2< = ≤-<-trans (m∸n≤m root₃ (suc x')) root3<N
        d1≡0 : suc x' ∸ root₃ ≡ 0
        d1≡0 = divides-below (suc x' ∸ root₃) N∣d1 d1<
        d2≡0 : root₃ ∸ suc x' ≡ 0
        d2≡0 = divides-below (root₃ ∸ suc x') N∣d2 d2<

--------------------------------------------------------------------------------
gt1-≢1 : ∀ x → suc 1 ≤ x → x ≡ 1 → ⊥
gt1-≢1 (suc (suc x')) (s≤s (s≤s _)) ()
gt1-≢1 (suc zero) (s≤s ())
gt1-≢1 zero ()

-- §8. DC 同侧 case（unique-root₃-同侧——mod 形范式复制）
--   root₃∸1 = 3¹¹·2¹⁵（同侧整除）——x∸1 被 3¹¹·2¹⁵ 整除 → x ≡ 1 + q·3¹¹·2¹⁵
--   q=0 → x=1（root₁）/ q=1 → x=root₃ / q≥2 → x ≥ N 矛盾（mod-extract 范式）
--------------------------------------------------------------------------------

-- 同侧唯一性（x > 1 排除 root₁）：x ≡ root₃ (mod 3¹¹·2¹⁵)
unique-root₃-same : ∀ x' → 1 < suc x' → suc x' < SOVEREIGN_LCM
                  → (pow3 11 * pow2 15) ∣ suc x' ∸ 1 → suc x' ≡ root₅
unique-root₃-same x' 1<x x<N (divides q eq) = q-split-gen (pow3 11 * pow2 15) q x-form refl
  where
    M : ℕ
    M = pow3 11 * pow2 15
    x-form : suc x' ≡ 1 + q * (pow3 11 * pow2 15)
    x-form = ∸-to-+ (suc x') 1 (q * (pow3 11 * pow2 15)) eq (s≤s z≤n)
    q-split-gen : ∀ M q → suc x' ≡ 1 + q * M → (M ≡ pow3 11 * pow2 15) → suc x' ≡ root₅
    q-split-gen M zero eq0 _ = ⊥-elim (suc1≤1-f (subst (λ w → suc 1 ≤ suc w) (suc-injective eq0) 1<x))
      where
        suc1≤1-f : suc 1 ≤ 1 → ⊥
        suc1≤1-f (s≤s p) = suc0≤0-f p
          where
            suc0≤0-f : suc 0 ≤ 0 → ⊥
            suc0≤0-f ()
    q-split-gen M (suc zero) eq1 M≡ = trans eq1 (trans (cong (1 +_) (*-identityˡ M)) (trans (cong (1 +_) M≡) refl))
    q-split-gen M (suc (suc q)) eq2 M≡ = ⊥-elim (n≮n SOVEREIGN_LCM (≤-<-trans N≤x x<N))
      where
        -- N≡MM（未来态锁定）：M ≡ 3¹¹·2¹⁵（M≡）→ M + M ≡ 3¹¹·2¹⁵ + 3¹¹·2¹⁵
        --   → 字面归约 = 177147·65536 = SOVEREIGN_LCM（refl 级——全字面量）
        N≡MM : SOVEREIGN_LCM ≡ M + M
        N≡MM = sym (trans M+M≡A+A A+A≡N)
          where
            A : ℕ
            A = pow3 11 * pow2 15
            M+M≡A+A : M + M ≡ A + A
            M+M≡A+A = subst (λ w → M + M ≡ w + w) M≡ refl
            A+A≡N : A + A ≡ SOVEREIGN_LCM
            A+A≡N = refl
        -- chain：M + M ≤ M + M + q·M（m≤m+n-f）≤ 1 + (M + (M + q·M))
        chain : M + M ≤ 1 + (M + (M + q * M))
        chain = ≤-step (subst ((M + M) ≤_) (+-assoc M M (q * M)) (m≤m+n-f (M + M) (q * M)))
        N≤x : SOVEREIGN_LCM ≤ suc x'
        N≤x = ≤-trans (≤-reflexive N≡MM) (subst ((M + M) ≤_) (sym eq2) chain)

--------------------------------------------------------------------------------
-- §9. 混合 case（unique-root₅ / unique-root₄）——复用 unique-root₃-same + 四段分裂
--------------------------------------------------------------------------------

unique-root₅ : ∀ x → 0 < x → x < SOVEREIGN_LCM
             → pow3 11 ∣ x ∸ 1 → pow2 15 ∣ x ∸ 1
             → ¬ (pow2 16 ∣ x ∸ 1) → x ≡ root₅
unique-root₅ (suc zero) (s≤s z≤n) x<N h3 h15 n16 = ⊥-elim (n16 (divides 0 refl))
unique-root₅ (suc (suc x'')) (s≤s z≤n) x<N h3 h15 n16 =
  unique-root₃-same (suc x'') (s≤s (s≤s z≤n)) x<N
    (lcm-coprime-gen (pow3 11) (pow2 15) (suc (suc x'') ∸ 1) (coprime-pow3-pow2 11 15) h3 h15)

unique-root₄ : ∀ x → x < SOVEREIGN_LCM
             → pow3 11 ∣ suc x → pow2 15 ∣ suc x
             → ¬ (pow2 16 ∣ suc x) → x ≡ root₄
unique-root₄ x x<N h3 h15 n16 = go (lcm-coprime-gen (pow3 11) (pow2 15) (suc x) (coprime-pow3-pow2 11 15) h3 h15)
  where
    M : ℕ
    M = pow3 11 * pow2 15
    M>0 : 0 < M
    M>0 = s≤s z≤n
    suc≠0-f : ∀ {n} → suc n ≡ 0 → ⊥
    suc≠0-f ()
    split : ∀ t → suc x ≡ t * (pow3 11 * pow2 15) → x ≡ root₄
    split zero eq = ⊥-elim (suc≠0-f eq)
    split (suc zero) eq = suc-injective (trans eq lit-M≡suc-root4)
      where
        lit-M≡suc-root4 : pow3 11 * pow2 15 ≡ suc root₄
        lit-M≡suc-root4 = refl
    split (suc (suc zero)) eq = ⊥-elim (n16 (subst (pow2 16 ∣_) (sym eq) div16∣2M))
      where
        div16∣2M : pow2 16 ∣ 2 * (pow3 11 * pow2 15)
        div16∣2M = subst (pow2 16 ∣_) (sym two-X≡N) (divides (pow3 11) lit-N-form2)
    split (suc (suc (suc t''))) eq = ⊥-elim (t3-kill (pow3 11 * pow2 15) t'' x M>0 eq x<N)
    go : (pow3 11 * pow2 15) ∣ suc x → x ≡ root₄
    go (divides t eq) = split t eq