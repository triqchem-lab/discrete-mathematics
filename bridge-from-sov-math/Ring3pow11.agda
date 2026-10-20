{-# OPTIONS --guardedness #-}

-- | Ring3pow11 — Z/3¹¹ 的表示层形式化：11 trit 小端向量 ↔ ℕ < 177147
--
-- 数学背景
-- ========
-- sov-math 的 C ABI 用 11 个 trit（`Vec (Fin 3) 11`，下标 0 为最不重要位）表示
-- 环 Z/3¹¹（177147 个元素），并提供 `sov_ring_add` / `sov_ring_mul` /
-- `sov_ring_double` / `sov_ring_to_tryte`。表示层已实测全域 177147 双射，
-- 但缺少 Agda 侧的形式化背书（下游只有 `HenselMod177147` 的 x²≡1 根）。
--
-- 本模块交付的是**表示层 + 值语义**的形式化，而不是另造一个抽象环：
--
--   ① 位值映射  `toℕ : Vec (Fin 3) k → ℕ`（Horner，小端：`x ∷ xs ↦ x + 3·toℕ xs`）
--      与数字展开 `repr k n`（`n ↦ [n%3, (n/3)%3, …]`）；
--   ② 双射      `toℕ-repr  : toℕ (repr k n) ≡ n % 3^k`（值落到规范区间）
--                `repr-toℕ  : repr k (toℕ v) ≡ v`（11 trit 全域往返）
--      —— 二者互逆，「177147 个向量 ↔ 177147 个值」即由此得到；
--   ③ 环运算    `add a b = fromℕ (toℕ a + toℕ b)`、`mul a b = fromℕ (toℕ a * toℕ b)`
--      并证明值语义 `toℕ (add a b) ≡ (toℕ a + toℕ b) % 3¹¹`（乘法同）；
--   ④ 环律      `add` / `mul` 的交换律、结合律，加法/乘法单位元，左右分配律。
--
-- 证明策略（真正的技术内容）
-- ========================
-- 全部难点集中在 ②：把「除 3 取商」「模 3 取余」与 Horner 展开对齐。关键是
-- `split3`：`n % (3^k · 3) ≡ (n % 3) + 3 · ((n / 3) % 3^k)`，
-- 即「模 3^(k+1) 的余数 = 最低位 + 3·(高位部分模 3^k)」。
-- 它由 stdlib 的两条带余除法引理拼成：
--   · `[m*n+o]%[p*n]≡[m*n]%[p*n]+o`（余数在缩放模数下的最低位提取）
--   · `m%n*o≡m*o%[n*o]`（被除数与模数同时乘 3 时余数也乘 3）
-- 因此**不需要任何界估计**（stdlib 已在引理内部做完），也不引入 ℤ 或浮点。
-- 环律都由「值语义 + `%` 的归约引理 + `toℕ` 单射（由 ② 得到）」推出，
-- 而不是逐 trit 做进位手算——后者需要 11 层进位传播的不变量，代价远超收益。
--
-- 取舍（诚实边界）
-- ==============
-- `add`/`mul` 定义在**值层**（`fromℕ ∘ ℕ运算`），因此「值语义」由构造得到、
-- 不是逐 trit 算法；本模块证明的是这层定义确实满足环律（交换/结合/单位/分配），
-- 不含「按位进位算法与值语义一致」这条（那需要 carry 不变量，未做）。
--
-- 状态：0 postulate / 0 hole。
module Ring3pow11 where

open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _%_; _∸_; _<_; _≤_; z≤n; s≤s)
open import Data.Nat.Base using (NonZero; >-nonZero)
open import Data.Nat.DivMod using (
         _/_; m%n<n; m<n⇒m%n≡m; n%1≡0; n%n≡0; m%n*o≡m*o%[n*o];
         [m*n+o]%[p*n]≡[m*n]%[p*n]+o; m≡m%n+[m/n]*n; [m+kn]%n≡m%n;
         %-distribˡ-+; %-distribˡ-*; m%n%n≡m%n; m*n%n≡0)
open import Data.Nat.Properties using (
         +-assoc; +-comm; +-identityˡ; +-identityʳ; +-cancelˡ-≡;
         *-assoc; *-comm; *-identityˡ; *-identityʳ;
         *-distribˡ-+; *-distribʳ-+; *-cancelʳ-≡; m∸n+n≡m;
         *-mono-≤; +-mono-≤; ≤-refl; ≤-trans; <⇒≤)
open import Data.Fin using (Fin; fromℕ<) renaming (toℕ to finToℕ)
open import Data.Fin.Properties using (toℕ-fromℕ<; toℕ<n; toℕ-injective)
open import Data.Vec using (Vec; []; _∷_)
open import Data.Empty using (⊥-elim)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst)

-- 局部等式推理链（只用 trans / refl，避免整模块 open stdlib 语法）
infix  1 begin_
infixr 2 _≡⟨_⟩_
infix  3 _∎

begin_ : ∀ {A : Set} {x y : A} → x ≡ y → x ≡ y
begin p = p

_≡⟨_⟩_ : ∀ {A : Set} (x : A) {y z : A} → x ≡ y → y ≡ z → x ≡ z
x ≡⟨ p ⟩ q = trans p q

_∎ : ∀ {A : Set} (x : A) → x ≡ x
x ∎ = refl

--------------------------------------------------------------------------------
-- §1. 3 的幂与正性
--
-- 定义成右乘 3 的形状（`pow3 (suc k) = pow3 k * 3`），使 `split3` 里的模数
-- `pow3 k * 3` 与 `pow3 (suc k)` **定义相等**，归纳步可以不加任何改写。
--------------------------------------------------------------------------------

pow3 : ℕ → ℕ
pow3 zero    = 1
pow3 (suc k) = pow3 k * 3

-- 模数：3¹¹ = 177147
M : ℕ
M = pow3 11

pow3>0 : ∀ k → 0 < pow3 k
pow3>0 zero    = s≤s z≤n
pow3>0 (suc k) = *-mono-≤ (pow3>0 k) (s≤s z≤n)

-- 取模 `modp n k = n % 3^k`：把正性证明 `pow3>0 k` **显式**放进定义，
-- 而不是交给实例搜索。原因（实测）：`NonZero (pow3 k)` 无法作为全局 instance
-- （Agda 拒绝"带显式参数的 instance"；作为实例参数又会让 `NonZero 3` 的求解
-- 留下 `pow3 _ = 3` 的悬空约束）。用 `modp` 后每个出现处的实例项都是同一条
-- 证明项，定义相等判定不会因实例项不同而失败。
modp : ℕ → ℕ → ℕ
modp n k = _%_ n (pow3 k) {{>-nonZero (pow3>0 k)}}

--------------------------------------------------------------------------------
-- §2. 除 3 / 模 3 的两条基本引理
--------------------------------------------------------------------------------

-- (i) 低位（< 3）不改变模 3 余数
mod3-add : ∀ a v → a < 3 → (a + 3 * v) % 3 ≡ a
mod3-add a v a<3 = begin
    (a + 3 * v) % 3   ≡⟨ cong (λ z → (a + z) % 3) (*-comm 3 v) ⟩
    (a + v * 3) % 3   ≡⟨ [m+kn]%n≡m%n a v 3 ⟩
    a % 3             ≡⟨ m<n⇒m%n≡m a<3 ⟩
    a                 ∎

-- (ii) 低位（< 3）不改变除 3 的商
div3-add : ∀ a v → a < 3 → (a + 3 * v) / 3 ≡ v
div3-add a v a<3 = sym (*-cancelʳ-≡ v ((a + 3 * v) / 3) 3 cancel)
  where
    -- a + 3v ≡ (a+3v)%3 + ((a+3v)/3)*3 ≡ a + ((a+3v)/3)*3
    eq1 : a + 3 * v ≡ a + ((a + 3 * v) / 3) * 3
    eq1 = trans (m≡m%n+[m/n]*n (a + 3 * v) 3)
                (cong (λ z → z + ((a + 3 * v) / 3) * 3) (mod3-add a v a<3))
    cancel : v * 3 ≡ ((a + 3 * v) / 3) * 3
    cancel = trans (sym (*-comm 3 v))
                   (+-cancelˡ-≡ a (3 * v) (((a + 3 * v) / 3) * 3) eq1)

--------------------------------------------------------------------------------
-- §3. 核心引理 split3：模 3^(k+1) 的余数 = 最低位 + 3·(高位模 3^k)
--------------------------------------------------------------------------------

split3 : ∀ n k → modp n (suc k) ≡ (n % 3) + 3 * modp (n / 3) k
split3 n k = begin
    modp n (suc k)
  ≡⟨ cong (λ z → modp z (suc k)) step1 ⟩
    modp ((n / 3) * 3 + n % 3) (suc k)
  ≡⟨ [m*n+o]%[p*n]≡[m*n]%[p*n]+o (n / 3) {3} {n % 3} (pow3 k)
       {{>-nonZero (pow3>0 (suc k))}} (m%n<n n 3) ⟩
    modp ((n / 3) * 3) (suc k) + n % 3
  ≡⟨ cong (_+ (n % 3)) step2 ⟩
    modp (n / 3) k * 3 + n % 3
  ≡⟨ +-comm (modp (n / 3) k * 3) (n % 3) ⟩
    n % 3 + modp (n / 3) k * 3
  ≡⟨ cong ((n % 3) +_) (*-comm (modp (n / 3) k) 3) ⟩
    (n % 3) + 3 * modp (n / 3) k ∎
  where
    -- n ≡ (n/3)*3 + n%3（stdlib 给的是 n%3 + (n/3)*3，交换一次）
    step1 : n ≡ (n / 3) * 3 + n % 3
    step1 = trans (m≡m%n+[m/n]*n n 3) (+-comm (n % 3) ((n / 3) * 3))
    -- 被除数与模数同时乘 3 ⇒ 余数乘 3
    step2 : modp ((n / 3) * 3) (suc k) ≡ modp (n / 3) k * 3
    step2 = sym (m%n*o≡m*o%[n*o] (n / 3) (pow3 k) 3
                   {{>-nonZero (pow3>0 k)}} {{>-nonZero (pow3>0 (suc k))}})

--------------------------------------------------------------------------------
-- §4. 位值映射（小端 Horner）与数字展开
--------------------------------------------------------------------------------

-- 小端位值：`x ∷ xs ↦ x + 3 · toℕ xs`
toℕ : ∀ {k} → Vec (Fin 3) k → ℕ
toℕ []       = 0
toℕ (x ∷ xs) = finToℕ x + 3 * toℕ xs

-- 数字展开：`n ↦ [n%3, (n/3)%3, ((n/3)/3)%3, …]`（长度 k）
repr : (k : ℕ) → ℕ → Vec (Fin 3) k
repr zero    n = []
repr (suc k) n = fromℕ< (m%n<n n 3) ∷ repr k (n / 3)

-- 11 trit ↔ ℕ 的两个方向
fromℕ : ℕ → Vec (Fin 3) 11
fromℕ n = repr 11 n

--------------------------------------------------------------------------------
-- §5. 双向往返：`toℕ (repr k n) ≡ n % 3^k` 与 `repr k (toℕ v) ≡ v`
--------------------------------------------------------------------------------

-- ① 展开再取值 = 取模（值落到规范区间 [0, 3^k)）
toℕ-repr : ∀ k n → toℕ (repr k n) ≡ modp n k
toℕ-repr zero n = sym (n%1≡0 n)
toℕ-repr (suc k) n = begin
    finToℕ (fromℕ< (m%n<n n 3)) + 3 * toℕ (repr k (n / 3))
  ≡⟨ cong₂ (λ a b → a + 3 * b) (toℕ-fromℕ< (m%n<n n 3)) (toℕ-repr k (n / 3)) ⟩
    (n % 3) + 3 * modp (n / 3) k
  ≡⟨ sym (split3 n k) ⟩
    modp n (suc k) ∎

-- ② 取值再展开 = 原向量（11 trit 全域往返，无需值域假设）
repr-toℕ : ∀ k (v : Vec (Fin 3) k) → repr k (toℕ v) ≡ v
repr-toℕ zero [] = refl
repr-toℕ (suc k) (x ∷ xs) = cong₂ _∷_ head-eq tail-eq
  where
    a : ℕ
    a = finToℕ x
    V : ℕ
    V = toℕ xs
    a<3 : a < 3
    a<3 = toℕ<n x
    head-eq : fromℕ< (m%n<n (a + 3 * V) 3) ≡ x
    head-eq = toℕ-injective
      (trans (toℕ-fromℕ< (m%n<n (a + 3 * V) 3)) (mod3-add a V a<3))
    tail-eq : repr k ((a + 3 * V) / 3) ≡ xs
    tail-eq = trans (cong (repr k) (div3-add a V a<3)) (repr-toℕ k xs)

--------------------------------------------------------------------------------
-- §6. 环运算 Z/3¹¹：值层定义 + 值语义
--
-- 定义走「值 → 模 → 回表示」：`add a b = fromℕ (toℕ a + toℕ b)`。
-- `fromℕ` 自带取模（`toℕ (fromℕ x) ≡ x % 3¹¹`，见 §5），故值语义是构造给出的；
-- 真正的证明内容是这些运算确实满足环律（§7/§8）。
--------------------------------------------------------------------------------

add : Vec (Fin 3) 11 → Vec (Fin 3) 11 → Vec (Fin 3) 11
add a b = fromℕ (toℕ a + toℕ b)

mul : Vec (Fin 3) 11 → Vec (Fin 3) 11 → Vec (Fin 3) 11
mul a b = fromℕ (toℕ a * toℕ b)

-- 值语义（加法）：结果值 = 两值之和 mod 3¹¹
add-value : ∀ a b → toℕ (add a b) ≡ (toℕ a + toℕ b) % M
add-value a b = toℕ-repr 11 (toℕ a + toℕ b)

-- 值语义（乘法）
mul-value : ∀ a b → toℕ (mul a b) ≡ (toℕ a * toℕ b) % M
mul-value a b = toℕ-repr 11 (toℕ a * toℕ b)

-- `toℕ` 在 11 trit 上单射：由 §5 的往返直接得到
toℕ-inj : ∀ {u v : Vec (Fin 3) 11} → toℕ u ≡ toℕ v → u ≡ v
toℕ-inj {u} {v} e =
  trans (sym (repr-toℕ 11 u)) (trans (cong fromℕ e) (repr-toℕ 11 v))

-- 值域界：任何 11 trit 向量的值都 < 3¹¹
toℕ-bound : ∀ (v : Vec (Fin 3) 11) → toℕ v < M
toℕ-bound v =
  subst (λ z → z < M)
        (sym (trans (cong toℕ (sym (repr-toℕ 11 v))) (toℕ-repr 11 (toℕ v))))
        (m%n<n (toℕ v) M)

--------------------------------------------------------------------------------
-- §7. mod 3¹¹ 的归约引理（把内层 `%` 提到外层，供结合律/分配律使用）
--------------------------------------------------------------------------------

%+-absorbˡ : ∀ x y → (x + y % M) % M ≡ (x + y) % M
%+-absorbˡ x y = begin
    (x + y % M) % M                ≡⟨ %-distribˡ-+ x (y % M) M ⟩
    ((x % M) + ((y % M) % M)) % M  ≡⟨ cong (λ z → ((x % M) + z) % M) (m%n%n≡m%n y M) ⟩
    ((x % M) + (y % M)) % M        ≡⟨ sym (%-distribˡ-+ x y M) ⟩
    (x + y) % M                    ∎

%+-absorbʳ : ∀ x y → (x % M + y) % M ≡ (x + y) % M
%+-absorbʳ x y = begin
    (x % M + y) % M  ≡⟨ cong (_% M) (+-comm (x % M) y) ⟩
    (y + x % M) % M  ≡⟨ %+-absorbˡ y x ⟩
    (y + x) % M      ≡⟨ cong (_% M) (+-comm y x) ⟩
    (x + y) % M      ∎

%*-absorbˡ : ∀ x y → (x * (y % M)) % M ≡ (x * y) % M
%*-absorbˡ x y = begin
    (x * (y % M)) % M                ≡⟨ %-distribˡ-* x (y % M) M ⟩
    ((x % M) * ((y % M) % M)) % M    ≡⟨ cong (λ z → ((x % M) * z) % M) (m%n%n≡m%n y M) ⟩
    ((x % M) * (y % M)) % M          ≡⟨ sym (%-distribˡ-* x y M) ⟩
    (x * y) % M                      ∎

%*-absorbʳ : ∀ x y → (x % M * y) % M ≡ (x * y) % M
%*-absorbʳ x y = begin
    (x % M * y) % M    ≡⟨ cong (_% M) (*-comm (x % M) y) ⟩
    (y * (x % M)) % M  ≡⟨ %*-absorbˡ y x ⟩
    (y * x) % M      ≡⟨ cong (_% M) (*-comm y x) ⟩
    (x * y) % M      ∎

--------------------------------------------------------------------------------
-- §8. 环律
--------------------------------------------------------------------------------

add-comm : ∀ a b → add a b ≡ add b a
add-comm a b = cong fromℕ (+-comm (toℕ a) (toℕ b))

add-assoc : ∀ a b c → add a (add b c) ≡ add (add a b) c
add-assoc a b c = toℕ-inj (begin
    toℕ (add a (add b c))
  ≡⟨ add-value a (add b c) ⟩
    (toℕ a + toℕ (add b c)) % M
  ≡⟨ cong (λ z → (toℕ a + z) % M) (add-value b c) ⟩
    (toℕ a + (toℕ b + toℕ c) % M) % M
  ≡⟨ %+-absorbˡ (toℕ a) (toℕ b + toℕ c) ⟩
    (toℕ a + (toℕ b + toℕ c)) % M
  ≡⟨ cong (_% M) (sym (+-assoc (toℕ a) (toℕ b) (toℕ c))) ⟩
    ((toℕ a + toℕ b) + toℕ c) % M
  ≡⟨ sym (%+-absorbʳ (toℕ a + toℕ b) (toℕ c)) ⟩
    ((toℕ a + toℕ b) % M + toℕ c) % M
  ≡⟨ cong (λ z → (z + toℕ c) % M) (sym (add-value a b)) ⟩
    (toℕ (add a b) + toℕ c) % M
  ≡⟨ sym (add-value (add a b) c) ⟩
    toℕ (add (add a b) c) ∎)

mul-comm : ∀ a b → mul a b ≡ mul b a
mul-comm a b = cong fromℕ (*-comm (toℕ a) (toℕ b))

mul-assoc : ∀ a b c → mul a (mul b c) ≡ mul (mul a b) c
mul-assoc a b c = toℕ-inj (begin
    toℕ (mul a (mul b c))
  ≡⟨ mul-value a (mul b c) ⟩
    (toℕ a * toℕ (mul b c)) % M
  ≡⟨ cong (λ z → (toℕ a * z) % M) (mul-value b c) ⟩
    (toℕ a * ((toℕ b * toℕ c) % M)) % M
  ≡⟨ %*-absorbˡ (toℕ a) (toℕ b * toℕ c) ⟩
    (toℕ a * (toℕ b * toℕ c)) % M
  ≡⟨ cong (_% M) (sym (*-assoc (toℕ a) (toℕ b) (toℕ c))) ⟩
    ((toℕ a * toℕ b) * toℕ c) % M
  ≡⟨ sym (%*-absorbʳ (toℕ a * toℕ b) (toℕ c)) ⟩
    ((toℕ a * toℕ b) % M * toℕ c) % M
  ≡⟨ cong (λ z → (z * toℕ c) % M) (sym (mul-value a b)) ⟩
    (toℕ (mul a b) * toℕ c) % M
  ≡⟨ sym (mul-value (mul a b) c) ⟩
    toℕ (mul (mul a b) c) ∎)

--------------------------------------------------------------------------------
-- §9. 单位元与加法逆元（把上面的交换/结合补成交换环）
--------------------------------------------------------------------------------

zeroV : Vec (Fin 3) 11
zeroV = fromℕ 0

oneV : Vec (Fin 3) 11
oneV = fromℕ 1

zeroV-value : toℕ zeroV ≡ 0
zeroV-value = trans (toℕ-repr 11 0) (m*n%n≡0 0 M)

1<M : 1 < M
1<M = s≤s (s≤s z≤n)

oneV-value : toℕ oneV ≡ 1
oneV-value = trans (toℕ-repr 11 1) (m<n⇒m%n≡m 1<M)

add-identityˡ : ∀ a → add zeroV a ≡ a
add-identityˡ a = toℕ-inj (begin
    toℕ (add zeroV a)
  ≡⟨ add-value zeroV a ⟩
    (toℕ zeroV + toℕ a) % M
  ≡⟨ cong (λ z → (z + toℕ a) % M) zeroV-value ⟩
    (0 + toℕ a) % M
  ≡⟨ m<n⇒m%n≡m (toℕ-bound a) ⟩
    toℕ a ∎)

add-identityʳ : ∀ a → add a zeroV ≡ a
add-identityʳ a = toℕ-inj (begin
    toℕ (add a zeroV)
  ≡⟨ add-value a zeroV ⟩
    (toℕ a + toℕ zeroV) % M
  ≡⟨ cong (λ z → (toℕ a + z) % M) zeroV-value ⟩
    (toℕ a + 0) % M
  ≡⟨ cong (_% M) (+-identityʳ (toℕ a)) ⟩
    toℕ a % M
  ≡⟨ m<n⇒m%n≡m (toℕ-bound a) ⟩
    toℕ a ∎)

mul-identityˡ : ∀ a → mul oneV a ≡ a
mul-identityˡ a = toℕ-inj (begin
    toℕ (mul oneV a)
  ≡⟨ mul-value oneV a ⟩
    (toℕ oneV * toℕ a) % M
  ≡⟨ cong (λ z → (z * toℕ a) % M) oneV-value ⟩
    (1 * toℕ a) % M
  ≡⟨ cong (_% M) (*-identityˡ (toℕ a)) ⟩
    toℕ a % M
  ≡⟨ m<n⇒m%n≡m (toℕ-bound a) ⟩
    toℕ a ∎)

mul-identityʳ : ∀ a → mul a oneV ≡ a
mul-identityʳ a = toℕ-inj (begin
    toℕ (mul a oneV)
  ≡⟨ mul-value a oneV ⟩
    (toℕ a * toℕ oneV) % M
  ≡⟨ cong (λ z → (toℕ a * z) % M) oneV-value ⟩
    (toℕ a * 1) % M
  ≡⟨ cong (_% M) (*-identityʳ (toℕ a)) ⟩
    toℕ a % M
  ≡⟨ m<n⇒m%n≡m (toℕ-bound a) ⟩
    toℕ a ∎)

-- 加法逆元：`neg a = fromℕ (3¹¹ ∸ toℕ a)`，值上相当于 3¹¹ − toℕ a
neg : Vec (Fin 3) 11 → Vec (Fin 3) 11
neg a = fromℕ (M ∸ toℕ a)

add-inverseʳ : ∀ a → add a (neg a) ≡ zeroV
add-inverseʳ a = toℕ-inj (begin
    toℕ (add a (neg a))
  ≡⟨ add-value a (neg a) ⟩
    (toℕ a + toℕ (neg a)) % M
  ≡⟨ cong (λ z → (toℕ a + z) % M) (toℕ-repr 11 (M ∸ toℕ a)) ⟩
    (toℕ a + (M ∸ toℕ a) % M) % M
  ≡⟨ %+-absorbˡ (toℕ a) (M ∸ toℕ a) ⟩
    (toℕ a + (M ∸ toℕ a)) % M
  ≡⟨ cong (_% M) (+-comm (toℕ a) (M ∸ toℕ a)) ⟩
    ((M ∸ toℕ a) + toℕ a) % M
  ≡⟨ cong (_% M) (m∸n+n≡m (<⇒≤ (toℕ-bound a))) ⟩
    M % M
  ≡⟨ n%n≡0 M ⟩
    0
  ≡⟨ sym zeroV-value ⟩
    toℕ zeroV ∎)

-- 分配律（左）：`a * (b + c) ≡ a*b + a*c`（值层经 `*-distribˡ-+` 与 mod 归约）
distribˡ : ∀ a b c → mul a (add b c) ≡ add (mul a b) (mul a c)
distribˡ a b c = toℕ-inj (begin
    toℕ (mul a (add b c))
  ≡⟨ mul-value a (add b c) ⟩
    (toℕ a * toℕ (add b c)) % M
  ≡⟨ cong (λ z → (toℕ a * z) % M) (add-value b c) ⟩
    (toℕ a * ((toℕ b + toℕ c) % M)) % M
  ≡⟨ %*-absorbˡ (toℕ a) (toℕ b + toℕ c) ⟩
    (toℕ a * (toℕ b + toℕ c)) % M
  ≡⟨ cong (_% M) (*-distribˡ-+ (toℕ a) (toℕ b) (toℕ c)) ⟩
    (toℕ a * toℕ b + toℕ a * toℕ c) % M
  ≡⟨ %-distribˡ-+ (toℕ a * toℕ b) (toℕ a * toℕ c) M ⟩
    ((toℕ a * toℕ b) % M + (toℕ a * toℕ c) % M) % M
  ≡⟨ cong₂ (λ x y → (x + y) % M) (sym (mul-value a b)) (sym (mul-value a c)) ⟩
    (toℕ (mul a b) + toℕ (mul a c)) % M
  ≡⟨ sym (add-value (mul a b) (mul a c)) ⟩
    toℕ (add (mul a b) (mul a c)) ∎)

distribʳ : ∀ a b c → mul (add a b) c ≡ add (mul a c) (mul b c)
distribʳ a b c = toℕ-inj (begin
    toℕ (mul (add a b) c)
  ≡⟨ mul-value (add a b) c ⟩
    (toℕ (add a b) * toℕ c) % M
  ≡⟨ cong (λ z → (z * toℕ c) % M) (add-value a b) ⟩
    ((toℕ a + toℕ b) % M * toℕ c) % M
  ≡⟨ %*-absorbʳ (toℕ a + toℕ b) (toℕ c) ⟩
    ((toℕ a + toℕ b) * toℕ c) % M
  ≡⟨ cong (_% M) (*-distribʳ-+ (toℕ c) (toℕ a) (toℕ b)) ⟩
    (toℕ a * toℕ c + toℕ b * toℕ c) % M
  ≡⟨ %-distribˡ-+ (toℕ a * toℕ c) (toℕ b * toℕ c) M ⟩
    ((toℕ a * toℕ c) % M + (toℕ b * toℕ c) % M) % M
  ≡⟨ cong₂ (λ x y → (x + y) % M) (sym (mul-value a c)) (sym (mul-value b c)) ⟩
    (toℕ (mul a c) + toℕ (mul b c)) % M
  ≡⟨ sym (add-value (mul a c) (mul b c)) ⟩
    toℕ (add (mul a c) (mul b c)) ∎)

--------------------------------------------------------------------------------
-- §10. 对抗验证：具体点独立核对（全部 `refl`，走内核计算）
--------------------------------------------------------------------------------

-- 模数与 C ABI 的 177147 一致
M≡177147 : M ≡ 177147
M≡177147 = refl

-- 表示层：小端点值
check-5 : toℕ (fromℕ 5) ≡ 5 ; check-5 = refl
check-177146 : toℕ (fromℕ 177146) ≡ 177146 ; check-177146 = refl
-- 越界值被模吸收
check-wrap : toℕ (fromℕ 177147) ≡ 0 ; check-wrap = refl

-- 加法值语义：(100000 + 100000) mod 177147 = 22853
check-add : toℕ (add (fromℕ 100000) (fromℕ 100000)) ≡ 22853 ; check-add = refl
-- 乘法值语义：(1000 * 1000) mod 177147 = 114265
check-mul : toℕ (mul (fromℕ 1000) (fromℕ 1000)) ≡ 114265 ; check-mul = refl
-- 交换律的具体实例（两侧独立求值到同一范式）
check-add-comm : add (fromℕ 12345) (fromℕ 88888) ≡ add (fromℕ 88888) (fromℕ 12345)
check-add-comm = refl
check-mul-comm : mul (fromℕ 999) (fromℕ 4242) ≡ mul (fromℕ 4242) (fromℕ 999)
check-mul-comm = refl
-- 单位元与逆元
check-add-id : add (fromℕ 77777) zeroV ≡ fromℕ 77777 ; check-add-id = refl
check-neg : add (fromℕ 55555) (neg (fromℕ 55555)) ≡ zeroV ; check-neg = refl
