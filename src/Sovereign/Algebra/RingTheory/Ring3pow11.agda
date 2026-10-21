{-# OPTIONS --rewriting --guardedness #-}

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
-- 两条实现路线（**2026-10-20 已打通**）
-- ================================
-- ① **值层**：`add`/`mul` = `fromℕ ∘ ℕ运算`——「值语义」由构造得到，
--    环律（交换/结合/单位/分配）在 §6-§8 证明。
-- ② **逐位进位算法**（§9-§13，照 stdlib `Data.Nat.Binary` 的
--    `_+_` + `toℕ-homo-+` 范式）：`addCarryV` 沿 `Vec` 递归做「本位和 + 进位」，
--    其与值层的一致性由 **`addCarryV-toℕ`
--    : toℕ (addCarryV c a b) ≡ modp (toℕ a + toℕ b + finToℕ c) k** 给出（归纳证明）。
--    ⇒ **「按位进位算法 ≡ 值语义」已证**（此前本节记为「未做」）。
--
-- 两条路线在表示层焊死（§14）
-- ==========================
-- `addCarry≡add : addCarry a b ≡ add a b`（由 §13 + §5 `toℕ-repr` + `toℕ-inj`），
-- 以及推论 `addCarry-comm`（逐位加法的交换律）。
--
-- 仍未做（诚实边界）
-- ==================
-- `mul` 的**逐位版本**（需要 11 次移位-累加的不变量，未做）。
--
-- 状态：0 postulate / 0 hole。
-- ⚠ **与 `Sovereign.Synthesis.Format.Positional` 的关系（2026-10-20 补记，必读）**
-- ================================================================================
-- 本模块 §9–§23 的「逐位算法 ↔ 值语义」一整套，**泛型版本已存在于**
-- `Sovereign.Synthesis.Format.Positional`（279 行 / 0 postulate），其头注明写
-- 该模块就是为「Z/3¹¹ 环（内核 11 位基 3）」建的。对应关系：
--
--   Positional 已有                     ｜ 本模块重推的
--   ------------------------------------｜----------------------------------------
--   `Raw` / `value`                     ｜ `Vec (Fin 3) k` / `toℕ`
--   `expand` / `expand-spec`            ｜ `repr` / `toℕ-repr`
--   `expand-bound`                      ｜ `toℕ<pow3`
--   `norm` / `norm-spec` / `norm-bound`  ｜ `truncate` / `truncate≡repr`
--   `scale` / `value-scale`             ｜ `scaleV` / `scaleV-toℕ`
--   `conv` / `value-conv`               ｜ `mulGo` 的卷积实质
--   `mulNorm` / `mul-spec`              ｜ **`mulCarry` / `mulCarry-toℕ`**
--   `addRaw` / `value-addRaw`           ｜ `addCarryV` 的值语义
--   `trim` / `trim-bound`               ｜ 归一化
--
-- ⇒ **本模块的独有增量**只有两条（其余是 `List`↔`Vec` 表示差异下的重复）：
--   ① `addCarryV` / `mulCarry` 是**真正的进位递归**（`Positional` 走「先逐位相加再归一」，
--      不是 carry 传播），与 sov-math C ABI 的 `sov_ring_add`/`sov_ring_mul` 实现**同构**；
--   ② `addCarry≡add` / `mulCarry≡mul` 把两套表示焊死（`Positional` 只到值语义 `*-spec`）。
--
-- **后续应当做的**（不要重复推导）：把 §16/§17 的 `repr`/`truncate` 一族改为引用
-- `Positional` 的 `expand-spec`/`norm-spec`，本模块只保留 `Vec` 层适配 + 进位递归。

module Sovereign.Algebra.RingTheory.Ring3pow11 where

open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _^_; _%_; _∸_; _<_; _≤_; z≤n; s≤s)
open import Data.Nat.Base using (NonZero; >-nonZero)
open import Data.Nat.DivMod using (
         _/_; m%n<n; m<n⇒m%n≡m; n%1≡0; n%n≡0; m%n*o≡m*o%[n*o];
         [m*n+o]%[p*n]≡[m*n]%[p*n]+o; m≡m%n+[m/n]*n; [m+kn]%n≡m%n;
         %-distribˡ-+; %-distribˡ-*; m%n%n≡m%n; m*n%n≡0; /-monoˡ-≤)
open import Data.Nat.Properties using (
         +-assoc; +-comm; +-identityˡ; +-identityʳ; +-cancelˡ-≡;
         *-assoc; *-comm; *-identityˡ; *-identityʳ; *-zeroʳ;
         *-distribˡ-+; *-distribʳ-+; *-cancelʳ-≡; m∸n+n≡m;
         *-mono-≤; +-mono-≤; ≤-refl; ≤-trans; <⇒≤; ≤-pred)
open import Data.Fin using (Fin; fromℕ<) renaming (toℕ to finToℕ; zero to fzero; suc to fsuc)
open import Data.Fin.Properties using (toℕ-fromℕ<; toℕ<n; toℕ-injective)
open import Data.Product using (proj₁; proj₂)
open import Data.List as L
open import Data.Vec using (Vec; []; _∷_; map)
open import Data.Nat.Solver using (module +-*-Solver)
open +-*-Solver using (solve; _:*_; _:+_; con; _:=_)
open import Data.Empty using (⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
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

--------------------------------------------------------------------------------
-- §9. 按位进位：值语义 ↔ 逐位加算的桥（2026-10-20 补）
--
-- 动机：`add` 定义在值层（`fromℕ ∘ ℕ加法`），故「按位进位算法与值语义一致」
--   此前未证（见模块头「取舍」）。本节 `modp-add-carry` 正是那条桥的**数学核心**：
--   模 3^(k+1) 的值层和 = 最低位按 3 进位 + 高位继续算。
--   11 位（`add`）的版本由对 k 归纳得到（k ≤ 11 枚举，见 §10 计划）。
--
-- 结构（全部扁平，无嵌套 where——Agda 的 where 存在前向引用限制）：
--   ① pull / mid / dist  —— 纯加法乘法重排（基础件）
--   ② sum-split          —— x + y = 3(x/3 + y/3) + (x%3 + y%3)
--   ③ mod3-sum           —— 低位余数
--   ④ gather             —— 进位重组
--   ⑤ div-carry          —— (x+y)/3 = x/3 + y/3 + 进位
--   ⑥ modp-add-carry     —— 主定理
--------------------------------------------------------------------------------

-- ① 纯算术重排：交给 stdlib 的 ring solver（`Data.Nat.Solver`）
--    来源：agda-stdlib `Data/Nat/Binary/Properties.agda:659` 的 `toℕ-homo-+` 用法
--    （该模块正是「进位算法 + 值语义等价」的范式，见其 `_+_` 定义与同态证明）

-- ①-a  `(a + b·3) + (c + d·3) ≡ (a + c) + 3·(b + d)`
pull3 : ∀ a b c d → (a + b * 3) + (c + d * 3) ≡ (a + c) + 3 * (b + d)
pull3 a b c d = solve 4
  (λ a′ b′ c′ d′ → (a′ :+ b′ :* con 3) :+ (c′ :+ d′ :* con 3)
                 := (a′ :+ c′) :+ con 3 :* (b′ :+ d′)) refl a b c d

-- ②  拆分：`x + y = 3·(x/3 + y/3) + (x%3 + y%3)`
sum-split : ∀ x y → x + y ≡ 3 * ((x / 3) + (y / 3)) + (x % 3 + y % 3)
sum-split x y = begin
    x + y
  ≡⟨ cong₂ _+_ (m≡m%n+[m/n]*n x 3) (m≡m%n+[m/n]*n y 3) ⟩
    (x % 3 + (x / 3) * 3) + (y % 3 + (y / 3) * 3)
  ≡⟨ pull3 (x % 3) (x / 3) (y % 3) (y / 3) ⟩
    (x % 3 + y % 3) + 3 * ((x / 3) + (y / 3))
  ≡⟨ +-comm (x % 3 + y % 3) (3 * ((x / 3) + (y / 3))) ⟩
    3 * ((x / 3) + (y / 3)) + (x % 3 + y % 3)
  ∎

-- ③  低位：和的模 3 余数只看两位的低位和（stdlib 已给）
mod3-sum : ∀ x y → (x + y) % 3 ≡ (x % 3 + y % 3) % 3
mod3-sum x y = %-distribˡ-+ x y 3

-- ④  重组：`3A + (r%3 + (r/3)·3) ≡ 3·(A + r/3) + r%3` —— 同样交给 solver
gather : ∀ A r → 3 * A + (r % 3 + (r / 3) * 3) ≡ 3 * (A + (r / 3)) + r % 3
gather A r = solve 3
  (λ A′ R Q → con 3 :* A′ :+ (R :+ Q :* con 3)
            := con 3 :* (A′ :+ Q) :+ R) refl A (r % 3) (r / 3)

-- ⑤  高位：进位进到高一位 —— `(x+y)/3 = (x/3 + y/3) + 进位`
div-carry : ∀ x y → (x + y) / 3 ≡ ((x / 3) + (y / 3)) + ((x % 3 + y % 3) / 3)
div-carry x y = begin
    (x + y) / 3
  ≡⟨ cong (_/ 3) (sum-split x y) ⟩
    (3 * ((x / 3) + (y / 3)) + (x % 3 + y % 3)) / 3
  ≡⟨ cong (_/ 3) (cong (3 * ((x / 3) + (y / 3)) +_) (m≡m%n+[m/n]*n (x % 3 + y % 3) 3)) ⟩
    (3 * ((x / 3) + (y / 3)) + ((x % 3 + y % 3) % 3 + ((x % 3 + y % 3) / 3) * 3)) / 3
  ≡⟨ cong (_/ 3) (gather ((x / 3) + (y / 3)) (x % 3 + y % 3)) ⟩
    (3 * (((x / 3) + (y / 3)) + ((x % 3 + y % 3) / 3)) + ((x % 3 + y % 3) % 3)) / 3
  ≡⟨ cong (_/ 3) (+-comm (3 * (((x / 3) + (y / 3)) + ((x % 3 + y % 3) / 3))) ((x % 3 + y % 3) % 3)) ⟩
    (((x % 3 + y % 3) % 3) + 3 * (((x / 3) + (y / 3)) + ((x % 3 + y % 3) / 3))) / 3
  ≡⟨ div3-add ((x % 3 + y % 3) % 3) (((x / 3) + (y / 3)) + ((x % 3 + y % 3) / 3))
       (m%n<n (x % 3 + y % 3) 3) ⟩
    ((x / 3) + (y / 3)) + ((x % 3 + y % 3) / 3)
  ∎

-- ⑥  主定理：模 3^(k+1) 的值层加法 = 最低位按 3 进位 + 高位继续
modp-add-carry : ∀ x y k → modp (x + y) (suc k)
  ≡ ((x % 3 + y % 3) % 3)
    + 3 * modp (((x / 3) + (y / 3)) + ((x % 3 + y % 3) / 3)) k
modp-add-carry x y k = begin
    modp (x + y) (suc k)
  ≡⟨ split3 (x + y) k ⟩
    (x + y) % 3 + 3 * modp ((x + y) / 3) k
  ≡⟨ cong₂ (λ a b → a + 3 * modp b k) (mod3-sum x y) (div-carry x y) ⟩
    ((x % 3 + y % 3) % 3) + 3 * modp (((x / 3) + (y / 3)) + ((x % 3 + y % 3) / 3)) k
  ∎

--------------------------------------------------------------------------------
-- §10. 含进位的三项和：逐位加法的归纳核（2026-10-20 续）
--
-- §9 的 `modp-add-carry` 处理「两个数相加」；`Vec` 层逐位加法在第 i 位面对的
-- 却是「x_i + y_i + 进位」**三项**，故需本节推广：
--   ① low3   低位：三项和的模 3 余数（3 的倍数项消失）
--   ② carry3 进位：高位商 = 两个高位商 + 低三位和的进位
--------------------------------------------------------------------------------

-- ① 低位：先把 x + y + c 折成 (x+y) + c，再分别取模
low3 : ∀ x y c → (x + y + c) % 3 ≡ (((x % 3) + (y % 3)) % 3 + (c % 3)) % 3
low3 x y c = begin
    (x + y + c) % 3
  ≡⟨ %-distribˡ-+ (x + y) c 3 ⟩
    ((x + y) % 3 + c % 3) % 3
  ≡⟨ cong (λ z → (z + c % 3) % 3) (%-distribˡ-+ x y 3) ⟩
    (((x % 3) + (y % 3)) % 3 + (c % 3)) % 3
  ∎

-- ② 进位：`(x + 3X + (y + 3Y + c))/3 = X + Y + (x+y+c)/3`
carry3 : ∀ x y c X Y → (x + 3 * X + (y + 3 * Y + c)) / 3
  ≡ X + Y + ((x + y + c) / 3)
carry3 x y c X Y = begin
    (x + 3 * X + (y + 3 * Y + c)) / 3
  ≡⟨ cong (_/ 3) (regroup x y c X Y) ⟩
    ((x + y + c) + 3 * (X + Y)) / 3
  ≡⟨ cong (_/ 3) (+-comm (x + y + c) (3 * (X + Y))) ⟩
    (3 * (X + Y) + (x + y + c)) / 3
  ≡⟨ cong (_/ 3) (cong (3 * (X + Y) +_) (m≡m%n+[m/n]*n (x + y + c) 3)) ⟩
    (3 * (X + Y) + ((x + y + c) % 3 + ((x + y + c) / 3) * 3)) / 3
  ≡⟨ cong (_/ 3) (gather (X + Y) (x + y + c)) ⟩
    (3 * ((X + Y) + ((x + y + c) / 3)) + ((x + y + c) % 3)) / 3
  ≡⟨ cong (_/ 3) (+-comm (3 * ((X + Y) + ((x + y + c) / 3))) ((x + y + c) % 3)) ⟩
    (((x + y + c) % 3) + 3 * ((X + Y) + ((x + y + c) / 3))) / 3
  ≡⟨ div3-add ((x + y + c) % 3) ((X + Y) + ((x + y + c) / 3)) (m%n<n (x + y + c) 3) ⟩
    (X + Y) + ((x + y + c) / 3)
  ∎
  where
    regroup : ∀ x y c X Y → x + 3 * X + (y + 3 * Y + c) ≡ (x + y + c) + 3 * (X + Y)
    regroup x y c X Y = solve 5
      (λ x′ y′ c′ X′ Y′ → x′ :+ con 3 :* X′ :+ (y′ :+ con 3 :* Y′ :+ c′)
                        := (x′ :+ y′ :+ c′) :+ con 3 :* (X′ :+ Y′)) refl x y c X Y

-- ③ 合成（`modp-add-carry3`）—— ✅ **已完成**（见紧接的 §11，634–678 行）。
--    当初的判断「需先补 `mod3-zero-multiple`」是对的，但**不必新证**：
--    库内 `[m+kn]%n≡m%n`（`Data.Nat.DivMod`）直接可用 ⇒ `mod3-zero-multiple` 一行即得，
--    再用 `solve` 把 `3 * X` 挪到末项，`modp-add-carry3` 遂成。
--    ⚠ 此标记原为「⬜ 未完成」，属**过期标注**（文档滞后于代码）。

--------------------------------------------------------------------------------
-- §11. 三项和分解（补 §10 缺口，2026-10-20 续）
--
-- §10 的 `modp-add-carry3` 卡在 `((3*X) % 3)` 的化简上。**库内已有现成引理**
-- `[m+kn]%n≡m%n : (m + k * n) % n ≡ m % n`（Data.Nat.DivMod，模块已 import），
-- 因此不必新证——只需把 `3 * X` 用 `solve` 挪到**最后一项**，直接套用。
--------------------------------------------------------------------------------

-- ① 3 的倍数项在模 3 下消失（库引理 `[m+kn]%n≡m%n` 的实例化）
mod3-zero-multiple : ∀ v X → (v + X * 3) % 3 ≡ v % 3
mod3-zero-multiple v X = [m+kn]%n≡m%n v X 3

-- ② 三项和的低位：把 `3X`、`3Y` 移到末尾后连用两次库引理
low3' : ∀ x y c X Y → (x + 3 * X + (y + 3 * Y + c)) % 3
  ≡ (((x % 3) + (y % 3)) % 3 + (c % 3)) % 3
low3' x y c X Y = begin
    (x + 3 * X + (y + 3 * Y + c)) % 3
  ≡⟨ cong (_% 3) (flatten x y c X Y) ⟩
    ((x + (y + c)) + (X + Y) * 3) % 3
  ≡⟨ mod3-zero-multiple (x + (y + c)) (X + Y) ⟩
    (x + (y + c)) % 3
  ≡⟨ cong (_% 3) (sym (+-assoc x y c)) ⟩
    (x + y + c) % 3
  ≡⟨ low3 x y c ⟩
    (((x % 3) + (y % 3)) % 3 + (c % 3)) % 3
  ∎
  where
    flatten : ∀ x y c X Y → x + 3 * X + (y + 3 * Y + c) ≡ (x + (y + c)) + (X + Y) * 3
    flatten x y c X Y = solve 5
      (λ x′ y′ c′ X′ Y′ → x′ :+ con 3 :* X′ :+ (y′ :+ con 3 :* Y′ :+ c′)
                        := (x′ :+ (y′ :+ c′)) :+ (X′ :+ Y′) :* con 3) refl x y c X Y

-- ③ 合成：模 3^(k+1) 的三项和分解（含进位）—— §10 的缺口
modp-add-carry3 : ∀ x y c X Y k → modp (x + 3 * X + (y + 3 * Y + c)) (suc k)
  ≡ (((x % 3) + (y % 3)) % 3 + (c % 3)) % 3
    + 3 * modp ((X + Y) + ((x + y + c) / 3)) k
modp-add-carry3 x y c X Y k = begin
    modp (x + 3 * X + (y + 3 * Y + c)) (suc k)
  ≡⟨ split3 (x + 3 * X + (y + 3 * Y + c)) k ⟩
    (x + 3 * X + (y + 3 * Y + c)) % 3
      + 3 * modp ((x + 3 * X + (y + 3 * Y + c)) / 3) k
  ≡⟨ cong₂ (λ a b → a + 3 * modp b k) (low3' x y c X Y) (carry3 x y c X Y) ⟩
    (((x % 3) + (y % 3)) % 3 + (c % 3)) % 3
      + 3 * modp ((X + Y) + ((x + y + c) / 3)) k
  ∎

--------------------------------------------------------------------------------
-- §12. 逐位加法的实现（`addCarry`）—— 照 stdlib `Data.Nat.Binary` 范式
--
-- stdlib 的范式（`Data/Nat/Binary/Base.agda:93` + `Properties.agda:650`）：
--   ① 用**模式匹配递归**定义进位加法（`2[1+ x ] + 2[1+ y ] = 2[1+ suc (x + y) ]`）
--   ② 用**归纳**证明 `toℕ-homo-+ : toℕ (x + y) ≡ toℕ x + toℕ y`
-- 本模块的镜像（base 3 / 定长 11 位）：
--   ① `digitOf`/`carryOf` 给单个数位的和与进位（值域由 `Fin 3` 承载，无需再写界）
--   ② `addCarryV` 沿 `Vec` 递归；③ `addCarryV-toℕ` 归纳给出值语义
--------------------------------------------------------------------------------

-- 界：s ≤ 6 ⇒ s / 3 < 3（用于进位的 `Fin 3` 构造）
-- 用 `≤` 而非 `<` 表述，避免 `<` 的 `suc` 包装与字面归约错位（实测踩过 ✗）
carry-bound : ∀ s → s ≤ 6 → s / 3 < 3
carry-bound s s≤6 =
  s≤s {s / 3} {2} (≤-trans {s / 3} {6 / 3} {2} (/-monoˡ-≤ 3 s≤6) (≤-refl {6 / 3}))

-- 三个 trit 各自 ≤ 2 ⇒ 和 ≤ 6（`≤-pred` 把 `< 3` 拆成 `≤ 2`；隐式参数全部显式）
trit-bound : ∀ x y c → finToℕ x + finToℕ y + finToℕ c ≤ 6
trit-bound x y c =
  +-mono-≤ {finToℕ x + finToℕ y} {2 + 2} {finToℕ c} {2}
    (+-mono-≤ {finToℕ x} {2} {finToℕ y} {2}
       (≤-pred {finToℕ x} {2} (toℕ<n x)) (≤-pred {finToℕ y} {2} (toℕ<n y)))
    (≤-pred {finToℕ c} {2} (toℕ<n c))

-- 本位和：`(x + y + c) % 3`
digitOf : Fin 3 → Fin 3 → Fin 3 → Fin 3
digitOf x y c = fromℕ< (m%n<n (finToℕ x + finToℕ y + finToℕ c) 3)

-- 进位：`(x + y + c) / 3`
carryOf : Fin 3 → Fin 3 → Fin 3 → Fin 3
carryOf x y c = fromℕ< (carry-bound (finToℕ x + finToℕ y + finToℕ c) (trit-bound x y c))

-- 本位和的值（构造即得）
digitOf-value : ∀ x y c → finToℕ (digitOf x y c) ≡ (finToℕ x + finToℕ y + finToℕ c) % 3
digitOf-value x y c = toℕ-fromℕ< _

-- 进位的值（构造即得）
carryOf-value : ∀ x y c → finToℕ (carryOf x y c) ≡ (finToℕ x + finToℕ y + finToℕ c) / 3
carryOf-value x y c = toℕ-fromℕ< _

-- 逐位加法：从低位起带进位递归（进位在定长外丢弃 ⇒ 天然模 3^k）
addCarryV : ∀ {k} → Fin 3 → Vec (Fin 3) k → Vec (Fin 3) k → Vec (Fin 3) k
addCarryV c []       []       = []
addCarryV c (x ∷ xs) (y ∷ ys) = digitOf x y c ∷ addCarryV (carryOf x y c) xs ys

-- 11 位版本：进位初值 0
addCarry : Vec (Fin 3) 11 → Vec (Fin 3) 11 → Vec (Fin 3) 11
addCarry = addCarryV fzero

--------------------------------------------------------------------------------
-- §13. 值语义：逐位加法 = 值层加法取模（T6，照 stdlib `Binary/toℕ-homo-+`）
--------------------------------------------------------------------------------

-- ① `n < 3 ⇒ n % 3 ≡ n`（库引理的直用）
mod3-id : ∀ n → n < 3 → n % 3 ≡ n
mod3-id n n<3 = m<n⇒m%n≡m n<3

-- ② 嵌套 mod-3 化简：`(((x%3)+(y%3))%3 + c%3)%3 ≡ (x+y+c)%3`（x,y,c < 3）
post3 : ∀ x y c → x < 3 → y < 3 → c < 3
  → (((x % 3) + (y % 3)) % 3 + (c % 3)) % 3 ≡ (x + y + c) % 3
post3 x y c x<3 y<3 c<3 = begin
    (((x % 3) + (y % 3)) % 3 + (c % 3)) % 3
  ≡⟨ cong (λ z → ((z + (y % 3)) % 3 + (c % 3)) % 3) (mod3-id x x<3) ⟩
    ((x + (y % 3)) % 3 + (c % 3)) % 3
  ≡⟨ cong (λ z → ((x + z) % 3 + (c % 3)) % 3) (mod3-id y y<3) ⟩
    ((x + y) % 3 + (c % 3)) % 3
  ≡⟨ sym (%-distribˡ-+ (x + y) c 3) ⟩
    (x + y + c) % 3
  ∎

-- ③ 主定理：逐位加法的值语义（**归纳**，镜像 stdlib `toℕ-homo-+`）
addCarryV-toℕ : ∀ {k} (c : Fin 3) (a b : Vec (Fin 3) k)
  → toℕ (addCarryV c a b) ≡ modp (toℕ a + toℕ b + finToℕ c) k
addCarryV-toℕ {zero} c [] [] = sym (n%1≡0 (finToℕ c))
addCarryV-toℕ {suc k} c (x ∷ xs) (y ∷ ys) = begin
    finToℕ (digitOf x y c) + 3 * toℕ (addCarryV (carryOf x y c) xs ys)
  ≡⟨ cong₂ (λ p q → p + 3 * q)
       (digitOf-value x y c) (addCarryV-toℕ (carryOf x y c) xs ys) ⟩
    (finToℕ x + finToℕ y + finToℕ c) % 3
      + 3 * modp (toℕ xs + toℕ ys + finToℕ (carryOf x y c)) k
  ≡⟨ cong (λ z → (finToℕ x + finToℕ y + finToℕ c) % 3
                 + 3 * modp (toℕ xs + toℕ ys + z) k) (carryOf-value x y c) ⟩
    (finToℕ x + finToℕ y + finToℕ c) % 3
      + 3 * modp (toℕ xs + toℕ ys + ((finToℕ x + finToℕ y + finToℕ c) / 3)) k
  ≡⟨ cong (λ z → z + 3 * modp ((toℕ xs + toℕ ys)
                                + ((finToℕ x + finToℕ y + finToℕ c) / 3)) k)
       (sym (post3 (finToℕ x) (finToℕ y) (finToℕ c)
                   (toℕ<n x) (toℕ<n y) (toℕ<n c))) ⟩
    (((finToℕ x % 3) + (finToℕ y % 3)) % 3 + (finToℕ c % 3)) % 3
      + 3 * modp ((toℕ xs + toℕ ys) + ((finToℕ x + finToℕ y + finToℕ c) / 3)) k
  ≡⟨ sym (modp-add-carry3 (finToℕ x) (finToℕ y) (finToℕ c) (toℕ xs) (toℕ ys) k) ⟩
    modp (finToℕ x + 3 * toℕ xs + (finToℕ y + 3 * toℕ ys + finToℕ c)) (suc k)
  ≡⟨ cong (λ z → modp z (suc k)) (reshape x xs y ys) ⟩
    modp ((finToℕ x + 3 * toℕ xs) + (finToℕ y + 3 * toℕ ys) + finToℕ c) (suc k)
  ∎
  where
    reshape : ∀ x (xs : Vec (Fin 3) k) y (ys : Vec (Fin 3) k)
      → finToℕ x + 3 * toℕ xs + (finToℕ y + 3 * toℕ ys + finToℕ c)
        ≡ (finToℕ x + 3 * toℕ xs) + (finToℕ y + 3 * toℕ ys) + finToℕ c
    reshape x xs y ys = solve 5
      (λ a A b B c′ → a :+ con 3 :* A :+ (b :+ con 3 :* B :+ c′)
                     := (a :+ con 3 :* A) :+ (b :+ con 3 :* B) :+ c′)
      refl (finToℕ x) (toℕ xs) (finToℕ y) (toℕ ys) (finToℕ c)

--------------------------------------------------------------------------------
-- §14. 两条实现路线一致：`addCarry ≡ add`（§13 的直接推论）
--
-- §6 的 `add` 是**值层**（`fromℕ ∘ ℕ加法`），§12 的 `addCarry` 是**逐位进位算法**。
-- §13 已证逐位算法的值语义；本节的定理把两者在**表示层**焊死：
--   逐位进位加法 ≡ 值层加法（在同一 `Vec (Fin 3) 11` 上逐点相等）。
--------------------------------------------------------------------------------

-- 11 位逐位加法的值语义（进位初值 `fzero`，其值按定义即 0）
addCarry-toℕ : ∀ a b → toℕ (addCarry a b) ≡ modp (toℕ a + toℕ b) 11
addCarry-toℕ a b = begin
    toℕ (addCarry a b)
  ≡⟨ addCarryV-toℕ fzero a b ⟩
    modp (toℕ a + toℕ b + 0) 11
  ≡⟨ cong (λ z → modp z 11) (+-identityʳ (toℕ a + toℕ b)) ⟩
    modp (toℕ a + toℕ b) 11
  ∎

-- 主定理：逐位进位加法与值层加法**表示层相等**
addCarry≡add : ∀ a b → addCarry a b ≡ add a b
addCarry≡add a b =
  toℕ-inj (trans (addCarry-toℕ a b) (sym (toℕ-repr 11 (toℕ a + toℕ b))))

-- 推论：逐位进位加法满足交换律（由 `add` 的交换律 + 上式直接搬过来）
addCarry-comm : ∀ a b → addCarry a b ≡ addCarry b a
addCarry-comm a b = begin
    addCarry a b
  ≡⟨ addCarry≡add a b ⟩
    add a b
  ≡⟨ add-comm a b ⟩
    add b a
  ≡⟨ sym (addCarry≡add b a) ⟩
    addCarry b a
  ∎

--------------------------------------------------------------------------------
-- §15. 逐位乘法的基础件（M1，2026-10-20）
--
-- `mul` 的逐位版本 = 「按 b 的每位缩放 a，再移位累加」。§15 先给**移位**这一件
-- （完整、无洞）；缩放/累加/主定理属后续（M2-M4，未做）。
--------------------------------------------------------------------------------

-- 保守界：`pow3 (suc k) = pow3 k * 3`（定义相等，供下面的重排用）
-- 左移一位：丢掉最低位位置、低位补 0 —— 对定长向量即「乘 3 后取模」
shiftV : ∀ {k} → Vec (Fin 3) (suc k) → Vec (Fin 3) (suc k)
shiftV (x ∷ xs) = fzero ∷ xs

-- 值语义：左移后 = 3 × 原尾部的值
shiftV-toℕ : ∀ {k} (x : Fin 3) (xs : Vec (Fin 3) k)
  → toℕ (shiftV (x ∷ xs)) ≡ 3 * toℕ xs
shiftV-toℕ x xs = refl

-- 全零向量的值（缩放的 0 分支会用到）
allZero : ∀ {k} → Vec (Fin 3) k
allZero {zero}  = []
allZero {suc k} = fzero ∷ allZero {k}

allZero-toℕ : ∀ {k} → toℕ (allZero {k}) ≡ 0
allZero-toℕ {zero}  = refl
allZero-toℕ {suc k} = trans (cong (0 +_) (cong (3 *_) (allZero-toℕ {k}))) refl

--------------------------------------------------------------------------------
-- §16. 逐位乘法的缩放件（M2，2026-10-20）
--
-- `scaleV d a` = 「把 a 整体乘以 trit d」：0 ↦ 全零、1 ↦ a、2 ↦ a + a（逐位进位加法）。
-- 对 `Fin 3` 的**三个构造子**分情形（不是 `with finToℕ` —— 后者会引入不可达分支）。
--------------------------------------------------------------------------------

-- 任意长度的值界：`toℕ v < 3^k`（`toℕ-bound` 的 k=11 版推广）
toℕ<pow3 : ∀ {k} (v : Vec (Fin 3) k) → toℕ v < pow3 k
toℕ<pow3 {k} v =
  subst (λ z → z < pow3 k)
        (sym (trans (cong toℕ (sym (repr-toℕ k v))) (toℕ-repr k (toℕ v))))
        (m%n<n (toℕ v) (pow3 k) {{>-nonZero (pow3>0 k)}})

-- 按 trit 缩放 `scaleV`（⚠ 未落地 —— 两个实测障碍，见 memory/mul-digitwise-handoff.md）：
--   ① `scaleV (fsuc fzero) a = …` 作为**左端模式**解析失败（`NoParseForLHS`，
--      "Operators used in the grammar: None"）——`Fin` 构造子在此模式下不被接受；
--   ② 走 `with finToℕ d` 路线时，第三分支 `suc (suc q)` 需要先由 `toℕ<n d`
--      推出 `q ≡ 0`（`suc (suc q) < 3 ⇒ q = 0`）才能把 `(2+q) * x` 归到 `x + x`。
-- 下轮建议：改用 `Data.Nat.Solver` 之外的「按 `toℕ d` 三段判定」写法，
--   或先证 `fin3-cases : ∀ (d : Fin 3) → (finToℕ d ≡ 0) ⊎ (finToℕ d ≡ 1) ⊎ (finToℕ d ≡ 2)`。

-- `Fin 3` 的三分（推荐的 `scaleV` 路线之所依）：值只能是 0 / 1 / 2
fin3-cases : ∀ (d : Fin 3) → (finToℕ d ≡ 0) ⊎ (finToℕ d ≡ 1) ⊎ (finToℕ d ≡ 2)
fin3-cases fzero = inj₁ refl
fin3-cases (fsuc fzero) = inj₂ (inj₁ refl)
fin3-cases (fsuc (fsuc fzero)) = inj₂ (inj₂ refl)

-- `modp 0 k ≡ 0`（`{{...}}` 前置显式给实例，绕开 m<n⇒m%n≡m 的实例槽被推断抢先填）
modp-zero : ∀ k → modp 0 k ≡ 0
modp-zero k = m<n⇒m%n≡m {{>-nonZero (pow3>0 k)}} (pow3>0 k)

-- `modp (toℕ v) k ≡ toℕ v`（值已在范围内）
modp-id : ∀ {k} (v : Vec (Fin 3) k) → modp (toℕ v) k ≡ toℕ v
modp-id {k} v = m<n⇒m%n≡m {{>-nonZero (pow3>0 k)}} (toℕ<pow3 v)

-- `2 * x ≡ x + x`（`_*_` 的展开带 `+ 0`，需 solver 归一）
two-mul : ∀ x → 2 * x ≡ x + x
two-mul x = solve 1 (λ z → con 2 :* z := z :+ z) refl x

-- 按 trit 缩放（`Fin 3` 三构造子分情形；构造子名：`fzero` / `fsuc`）
scaleV : ∀ {k} → Fin 3 → Vec (Fin 3) k → Vec (Fin 3) k
scaleV fzero               a = allZero
scaleV (fsuc fzero)        a = a
scaleV (fsuc (fsuc fzero)) a = addCarryV fzero a a

-- 值语义：`toℕ (scaleV d a) ≡ (finToℕ d · toℕ a) mod 3^k`
scaleV-toℕ : ∀ {k} (d : Fin 3) (a : Vec (Fin 3) k)
  → toℕ (scaleV d a) ≡ modp (finToℕ d * toℕ a) k
scaleV-toℕ {k} fzero a = trans (allZero-toℕ {k}) (sym (modp-zero k))
scaleV-toℕ {k} (fsuc fzero) a = begin
    toℕ a
  ≡⟨ sym (modp-id a) ⟩
    modp (toℕ a) k
  ≡⟨ cong (λ z → modp z k) (sym (+-identityʳ (toℕ a))) ⟩
    modp (toℕ a + 0) k
  ∎
scaleV-toℕ {k} (fsuc (fsuc fzero)) a = begin
    toℕ (addCarryV fzero a a)
  ≡⟨ addCarryV-toℕ fzero a a ⟩
    modp (toℕ a + toℕ a + 0) k
  ≡⟨ cong (λ z → modp z k) (+-identityʳ (toℕ a + toℕ a)) ⟩
    modp (toℕ a + toℕ a) k
  ≡⟨ cong (λ z → modp z k) (sym (two-mul (toℕ a))) ⟩
    modp (2 * toℕ a) k
  ∎

--------------------------------------------------------------------------------
-- §17. 乘法用的截断与移位（M3 前置件，2026-10-20）
--
-- ⚠ 诊断：`shiftV`（`fzero ∷ xs`，丢**个位**）的语义是「3·(toℕ a / 3)」，
--   **不是** `a·3 mod 3^k`。乘法要的移位必须**截掉最高位**：
--     `shiftMul a = fzero ∷ truncate a`，其值恰为 `a·3 mod 3^k`。
--   两者差一个 `truncate`，若混用会把乘法写成「不乘 3 的乘法」✗。
--------------------------------------------------------------------------------

-- 截掉最高位（长度减一）
truncate : ∀ {k} → Vec (Fin 3) (suc k) → Vec (Fin 3) k
truncate (x ∷ []) = []
truncate (x ∷ (y ∷ ys)) = x ∷ truncate (y ∷ ys)

-- 乘法用的移位：`a ↦ 0, a₀, …, a_{k-2}`（= `a·3 mod 3^k`）
shiftMul : ∀ {k} → Vec (Fin 3) k → Vec (Fin 3) k
shiftMul {zero}  []       = []
shiftMul {suc k} (x ∷ xs) = fzero ∷ truncate (x ∷ xs)

-- 截断 ≡ 「先取模再展开」：`truncate v ≡ repr k (toℕ v)`
-- 证明照 `repr-toℕ` 的结构（`mod3-add` 定首项、`div3-add` 消去除法）
truncate≡repr : ∀ {k} (v : Vec (Fin 3) (suc k)) → truncate v ≡ repr k (toℕ v)
truncate≡repr (x ∷ []) = refl
truncate≡repr {suc j} (x ∷ (y ∷ ys)) = cong₂ _∷_ head-eq tail-eq
  where
    a : ℕ
    a = finToℕ x
    V : ℕ
    V = finToℕ y + 3 * toℕ ys
    a<3 : a < 3
    a<3 = toℕ<n x
    head-eq : x ≡ fromℕ< (m%n<n (a + 3 * V) 3)
    head-eq = toℕ-injective
      (trans (sym (mod3-add a V a<3)) (sym (toℕ-fromℕ< (m%n<n (a + 3 * V) 3))))
    tail-eq : truncate (y ∷ ys) ≡ repr j ((a + 3 * V) / 3)
    tail-eq = trans (truncate≡repr (y ∷ ys)) (sym (cong (repr j) (div3-add a V a<3)))

-- 值语义：截断 = 取模 3^k
truncate-toℕ : ∀ {k} (v : Vec (Fin 3) (suc k)) → toℕ (truncate v) ≡ modp (toℕ v) k
truncate-toℕ {k} v = trans (cong toℕ (truncate≡repr v)) (toℕ-repr k (toℕ v))

-- 乘法移位的值语义：`toℕ (shiftMul a) ≡ (3 · toℕ a) mod 3^k`
shiftMul-toℕ : ∀ {k} (a : Vec (Fin 3) k) → toℕ (shiftMul a) ≡ modp (3 * toℕ a) k
shiftMul-toℕ {zero} [] = sym (n%1≡0 0)
shiftMul-toℕ {suc j} (x ∷ xs) = begin
    3 * toℕ (truncate (x ∷ xs))
  ≡⟨ cong (3 *_) (truncate-toℕ (x ∷ xs)) ⟩
    3 * modp (toℕ (x ∷ xs)) j
  ≡⟨ key ⟩
    modp (3 * toℕ (x ∷ xs)) (suc j)
  ∎
  where
    Y : ℕ
    Y = toℕ (x ∷ xs)
    -- 局部实例：让链中的 `% (pow3 j * 3)` 能解析
    instance
      nzj : NonZero (pow3 j)
      nzj = >-nonZero (pow3>0 j)
      nz3 : NonZero (pow3 j * 3)
      nz3 = >-nonZero (*-mono-≤ {1} {pow3 j} {1} {3} (pow3>0 j) (s≤s z≤n))
    key : 3 * modp Y j ≡ modp (3 * Y) (suc j)
    key = begin
        3 * (Y % pow3 j)
      ≡⟨ *-comm 3 (Y % pow3 j) ⟩
        (Y % pow3 j) * 3
      ≡⟨ m%n*o≡m*o%[n*o] Y (pow3 j) 3 {{>-nonZero (pow3>0 j)}} ⟩
        (Y * 3) % (pow3 j * 3)
      ≡⟨ cong (λ z → modp z (suc j)) (*-comm Y 3) ⟩
        modp (3 * Y) (suc j)
      ∎

--------------------------------------------------------------------------------
-- §18. 逐位乘法的累加器（M3c，2026-10-20）
--
-- 沿 `b` 的低位到高位：`acc ← acc + a·b_i`，每步把 `a` 上移一位（`shiftMul`）。
-- 不变式：`toℕ (go a bs acc) ≡ modp (toℕ a * toℕ bs + toℕ acc) k`。
--------------------------------------------------------------------------------

-- 两条 mod 同余引理（归纳步要用）
modp-add-cong : ∀ a b k → modp (a + b) k ≡ modp (modp a k + modp b k) k
modp-add-cong a b k = %-distribˡ-+ a b (pow3 k) {{>-nonZero (pow3>0 k)}}

modp-mul-cong : ∀ a b k → modp (a * b) k ≡ modp (modp a k * modp b k) k
modp-mul-cong a b k = %-distribˡ-* a b (pow3 k) {{>-nonZero (pow3>0 k)}}

-- 累加器：`a` 每步上移一位，`acc` 累加 `scaleV bᵢ a`
-- `a`/`acc` 长度固定为 `k`；`bs` 沿 `j` 递减（`a` 每步 `shiftMul` 但长度不变）
mulGo : ∀ {k j} → Vec (Fin 3) k → Vec (Fin 3) j → Vec (Fin 3) k → Vec (Fin 3) k
mulGo a []       acc = acc
mulGo a (b ∷ bs) acc = mulGo (shiftMul a) bs (addCarryV fzero acc (scaleV b a))

-- 逐位乘法：11 位版
mulCarry : ∀ {k} → Vec (Fin 3) k → Vec (Fin 3) k → Vec (Fin 3) k
mulCarry {k} a b = mulGo a b (allZero {k})

-- 累加器不变式的**基例**（完整的引理；归纳步见交接文件 M3c 段）
-- 目标全称式：`toℕ (mulGo a bs acc) ≡ modp (toℕ a * toℕ bs + toℕ acc) k`
-- —— 归纳步需要 mod 同余的 6-8 步改写，尚未落成（不留半截定理 ✗）
mulGo-nil : ∀ {k} (a : Vec (Fin 3) k) (acc : Vec (Fin 3) k)
  → toℕ (mulGo a [] acc) ≡ modp (toℕ a * 0 + toℕ acc) k
mulGo-nil {k} a acc = begin
    toℕ acc
  ≡⟨ sym (modp-id acc) ⟩
    modp (toℕ acc) k
  ≡⟨ cong (λ z → modp z k) (sym (+-identityˡ (toℕ acc))) ⟩
    modp (0 + toℕ acc) k
  ≡⟨ cong (λ z → modp (z + toℕ acc) k) (sym (*-zeroʳ (toℕ a))) ⟩
    modp (toℕ a * 0 + toℕ acc) k
  ∎

--------------------------------------------------------------------------------
-- §19. mod 的展平引理（归纳步用）
--
-- 归纳步里到处是 `modp (modp … k + …) k` 这样的嵌套。三条展平引理把它剥成单层，
-- 之后再一次性用 `solve` 做多项式归一。
--------------------------------------------------------------------------------

modp-add-flattenˡ : ∀ x y k → modp (modp x k + y) k ≡ modp (x + y) k
modp-add-flattenˡ x y k = begin
    modp (modp x k + y) k
  ≡⟨ %-distribˡ-+ (modp x k) y (pow3 k) {{>-nonZero (pow3>0 k)}} ⟩
    modp (modp (modp x k) k + modp y k) k
  ≡⟨ cong (λ z → modp (z + modp y k) k) (m%n%n≡m%n x (pow3 k) {{>-nonZero (pow3>0 k)}}) ⟩
    modp (modp x k + modp y k) k
  ≡⟨ sym (modp-add-cong x y k) ⟩
    modp (x + y) k
  ∎

modp-add-flattenʳ : ∀ x y k → modp (x + modp y k) k ≡ modp (x + y) k
modp-add-flattenʳ x y k = begin
    modp (x + modp y k) k
  ≡⟨ %-distribˡ-+ x (modp y k) (pow3 k) {{>-nonZero (pow3>0 k)}} ⟩
    modp (modp x k + modp (modp y k) k) k
  ≡⟨ cong (λ z → modp (modp x k + z) k) (m%n%n≡m%n y (pow3 k) {{>-nonZero (pow3>0 k)}}) ⟩
    modp (modp x k + modp y k) k
  ≡⟨ sym (modp-add-cong x y k) ⟩
    modp (x + y) k
  ∎

modp-mul-flattenˡ : ∀ x y k → modp (modp x k * y) k ≡ modp (x * y) k
modp-mul-flattenˡ x y k = begin
    modp (modp x k * y) k
  ≡⟨ %-distribˡ-* (modp x k) y (pow3 k) {{>-nonZero (pow3>0 k)}} ⟩
    modp (modp (modp x k) k * modp y k) k
  ≡⟨ cong (λ z → modp (z * modp y k) k) (m%n%n≡m%n x (pow3 k) {{>-nonZero (pow3>0 k)}}) ⟩
    modp (modp x k * modp y k) k
  ≡⟨ sym (modp-mul-cong x y k) ⟩
    modp (x * y) k
  ∎

--------------------------------------------------------------------------------
-- §20. mod 同余关系（归纳步的正确抽象）
--
-- `modp` **不是**项层同余：`modp (a + w) k ≡ modp (b + w) k` 需要 `a ≡ b` 的
-- 命题相等，而归纳步只知道 `modp a k ≡ modp b k`。⇒ 引入同余关系
-- `Cong x y k := modp x k ≡ modp y k`，并证它对 `+`/`*` 同余；
-- 归纳步由此变成 `Cong-trans` 链（与 `DayanNatFix` 的 `Cong` 同构）。
--------------------------------------------------------------------------------

Cong : ℕ → ℕ → ℕ → Set
Cong x y k = modp x k ≡ modp y k

Cong-refl : ∀ x k → Cong x x k
Cong-refl x k = refl

Cong-sym : ∀ x y k → Cong x y k → Cong y x k
Cong-sym x y k = sym

Cong-trans : ∀ x y z k → Cong x y k → Cong y z k → Cong x z k
Cong-trans x y z k = trans

Cong-add : ∀ a b c d k → Cong a c k → Cong b d k → Cong (a + b) (c + d) k
Cong-add a b c d k hac hbd = begin
    modp (a + b) k
  ≡⟨ modp-add-cong a b k ⟩
    modp (modp a k + modp b k) k
  ≡⟨ cong (λ z → modp (z + modp b k) k) hac ⟩
    modp (modp c k + modp b k) k
  ≡⟨ cong (λ z → modp (modp c k + z) k) hbd ⟩
    modp (modp c k + modp d k) k
  ≡⟨ sym (modp-add-cong c d k) ⟩
    modp (c + d) k
  ∎

Cong-mul : ∀ a b c d k → Cong a c k → Cong b d k → Cong (a * b) (c * d) k
Cong-mul a b c d k hac hbd = begin
    modp (a * b) k
  ≡⟨ modp-mul-cong a b k ⟩
    modp (modp a k * modp b k) k
  ≡⟨ cong (λ z → modp (z * modp b k) k) hac ⟩
    modp (modp c k * modp b k) k
  ≡⟨ cong (λ z → modp (modp c k * z) k) hbd ⟩
    modp (modp c k * modp d k) k
  ≡⟨ sym (modp-mul-cong c d k) ⟩
    modp (c * d) k
  ∎

--------------------------------------------------------------------------------
-- §21. 归纳步的算术核（M3e）
--
-- `Cong (modp (3A) k * B + modp (C + modp (bA) k) k) (A·(b + 3B) + C) k`
-- 分三步：① 剥 `Q` 的外层 modp；② 把 `modp (3A) k` 换成 `3A`；③ 多项式归一。
--------------------------------------------------------------------------------

-- `Cong (modp x k) x k`（`modp` 的幂等性，做成同余形式）
Cong-id : ∀ x k → Cong (modp x k) x k
Cong-id x k = m%n%n≡m%n x (pow3 k) {{>-nonZero (pow3>0 k)}}

mulGo-key : ∀ A B C b k →
    Cong (modp (3 * A) k * B + modp (C + modp (b * A) k) k)
         (A * (b + 3 * B) + C) k
mulGo-key A B C b k = trans s1 (trans s2 s3)
  where
    s3 : Cong ((3 * A) * B + (C + b * A)) (A * (b + 3 * B) + C) k
    s3 = cong (λ z → modp z k)
              (solve 4 (λ a b′ c d →
                          (con 3 :* a) :* b′ :+ (c :+ d :* a)
                          := a :* (d :+ con 3 :* b′) :+ c) refl A B C b)

    s2 : Cong (modp (3 * A) k * B + (C + b * A)) ((3 * A) * B + (C + b * A)) k
    s2 = Cong-add (modp (3 * A) k * B) (C + b * A) ((3 * A) * B) (C + b * A) k
                  (Cong-mul (modp (3 * A) k) B (3 * A) B k
                            (Cong-id (3 * A) k)
                            (Cong-refl B k))
                  (Cong-refl (C + b * A) k)

    s1 : Cong (modp (3 * A) k * B + modp (C + modp (b * A) k) k)
              (modp (3 * A) k * B + (C + b * A)) k
    s1 = Cong-add (modp (3 * A) k * B) (modp (C + modp (b * A) k) k)
                  (modp (3 * A) k * B) (C + b * A) k
                  (Cong-refl (modp (3 * A) k * B) k) inner
      where
        inner : Cong (modp (C + modp (b * A) k) k) (C + b * A) k
        inner = trans (Cong-id (C + modp (b * A) k) k)
                      (Cong-add C (modp (b * A) k) C (b * A) k
                                (Cong-refl C k)
                                (Cong-id (b * A) k))

--------------------------------------------------------------------------------
-- §22. 累加器不变式（M3f）—— 归纳完成
--------------------------------------------------------------------------------

mulGo-toℕ : ∀ {k j} (a : Vec (Fin 3) k) (bs : Vec (Fin 3) j) (acc : Vec (Fin 3) k)
  → toℕ (mulGo a bs acc) ≡ modp (toℕ a * toℕ bs + toℕ acc) k
mulGo-toℕ {k} a [] acc = mulGo-nil {k} a acc
mulGo-toℕ {k} {suc j} a (b ∷ bs) acc = begin
    toℕ (mulGo (shiftMul a) bs (addCarryV fzero acc (scaleV b a)))
  ≡⟨ mulGo-toℕ (shiftMul a) bs (addCarryV fzero acc (scaleV b a)) ⟩
    modp (toℕ (shiftMul a) * toℕ bs
          + toℕ (addCarryV fzero acc (scaleV b a))) k
  ≡⟨ cong₂ (λ p q → modp (p * toℕ bs + q) k)
           (shiftMul-toℕ a)
           (trans (addCarryV-toℕ fzero acc (scaleV b a))
                  (cong (λ z → modp (toℕ acc + z + 0) k) (scaleV-toℕ b a))) ⟩
    modp (modp (3 * toℕ a) k * toℕ bs
          + modp (toℕ acc + modp (finToℕ b * toℕ a) k + 0) k) k
  ≡⟨ cong (λ z → modp (modp (3 * toℕ a) k * toℕ bs
                        + modp z k) k)
           (+-identityʳ (toℕ acc + modp (finToℕ b * toℕ a) k)) ⟩
    modp (modp (3 * toℕ a) k * toℕ bs
          + modp (toℕ acc + modp (finToℕ b * toℕ a) k) k) k
  ≡⟨ mulGo-key (toℕ a) (toℕ bs) (toℕ acc) (finToℕ b) k ⟩
    modp (toℕ a * (finToℕ b + 3 * toℕ bs) + toℕ acc) k
  ∎

--------------------------------------------------------------------------------
-- §23. 逐位乘法的值语义与主定理（M4）
--------------------------------------------------------------------------------

-- 值语义：逐位乘法 = 值层乘法取模
mulCarry-toℕ : ∀ {k} (a b : Vec (Fin 3) k)
  → toℕ (mulCarry a b) ≡ modp (toℕ a * toℕ b) k
mulCarry-toℕ {k} a b = begin
    toℕ (mulGo a b (allZero {k}))
  ≡⟨ mulGo-toℕ a b (allZero {k}) ⟩
    modp (toℕ a * toℕ b + toℕ (allZero {k})) k
  ≡⟨ cong (λ z → modp (toℕ a * toℕ b + z) k) (allZero-toℕ {k}) ⟩
    modp (toℕ a * toℕ b + 0) k
  ≡⟨ cong (λ z → modp z k) (+-identityʳ (toℕ a * toℕ b)) ⟩
    modp (toℕ a * toℕ b) k
  ∎

-- 主定理：逐位乘法与值层乘法在表示层相等（与 §14 的加法同构）
mulCarry≡mul : ∀ (a b : Vec (Fin 3) 11) → mulCarry a b ≡ mul a b
mulCarry≡mul a b =
  toℕ-inj (trans (mulCarry-toℕ a b) (sym (toℕ-repr 11 (toℕ a * toℕ b))))

--------------------------------------------------------------------------------
-- §24. 与 `Sovereign.Synthesis.Format.Positional` 的一致性（差分互证）
--
-- `Positional`（模块函子，`Raw = List ℕ`，低位在前）已有泛型位值制全套：
-- `expand-spec` / `norm-spec` / `value-addRaw` / `value-scale` / `value-conv` / `mul-spec`。
-- 本节**不重推**它们，而是把本模块的 `Vec` 表示接到 `Raw` 上，并证明：
--   **两套独立形式化（进位递归 vs 卷积+归一）在同一个值上一致**。
-- 这是差分证据（两条独立路径得同一结论），也确立唯一真相源是 `Positional` 的 spec。
--------------------------------------------------------------------------------

open import Sovereign.Synthesis.Format.Positional 3 (s≤s (s≤s z≤n)) as P

-- `Positional` 的 `base ^ n` 与本模块的 `pow3 n` 同值（定义不同形，需桥）
pow-eq : ∀ k → 3 ^ k ≡ pow3 k
pow-eq zero    = refl
pow-eq (suc k) = trans (cong (3 *_) (pow-eq k))
                       (solve 1 (λ a → con 3 :* a := a :* con 3) refl (pow3 k))

-- 适配：`Vec (Fin 3) k` → `P.Raw`（低位在前，逐位取值）
rawOf : ∀ {k} → Vec (Fin 3) k → P.Raw
rawOf {zero}  []       = L.[]
rawOf {suc k} (x ∷ xs) = finToℕ x L.∷ rawOf xs

-- 适配保值：`Positional.value` 与本模块的 `toℕ` 逐点相同
value-rawOf : ∀ {k} (v : Vec (Fin 3) k) → P.value (rawOf v) ≡ toℕ v
value-rawOf {zero}  []       = refl
value-rawOf {suc k} (x ∷ xs) = cong (λ z → finToℕ x + 3 * z) (value-rawOf xs)

-- 值加 `3^k` 的倍数不改变 mod 3^k 余数（`Positional` 的 spec 里带着显式进位）
-- 用 `3 ^ k` 书写，与 `Positional` 的 spec **同形**，链条里不必再插桥
mod-of-plus-mult : ∀ x c k → modp (x + 3 ^ k * c) k ≡ modp x k
mod-of-plus-mult x c k = begin
    modp (x + 3 ^ k * c) k
  ≡⟨ cong (λ z → modp (x + z * c) k) (pow-eq k) ⟩
    modp (x + pow3 k * c) k
  ≡⟨ cong (λ z → modp (x + z) k) (*-comm (pow3 k) c) ⟩
    modp (x + c * pow3 k) k
  ≡⟨ [m+kn]%n≡m%n x c (pow3 k) {{>-nonZero (pow3>0 k)}} ⟩
    modp x k
  ∎

-- ① 加法一致：`Positional.add-spec`（逐位相加+归一）与本模块 `addCarryV`（进位递归）同值
pos-add-agrees : ∀ {k} (a b : Vec (Fin 3) k)
  → modp (P.value (P.addNorm k (rawOf a) (rawOf b))) k ≡ toℕ (addCarryV fzero a b)
pos-add-agrees {k} a b = begin
    modp (P.value (P.addNorm k (rawOf a) (rawOf b))) k
  ≡⟨ sym (mod-of-plus-mult (P.value (P.addNorm k (rawOf a) (rawOf b)))
                            (proj₁ (P.expand k (P.value (P.addRaw (rawOf a) (rawOf b))))) k) ⟩
    modp (P.value (P.addNorm k (rawOf a) (rawOf b))
          + 3 ^ k * proj₁ (P.expand k (P.value (P.addRaw (rawOf a) (rawOf b))))) k
  ≡⟨ cong (λ z → modp z k) (P.add-spec k (rawOf a) (rawOf b)) ⟩
    modp (P.value (rawOf a) + P.value (rawOf b)) k
  ≡⟨ cong (λ z → modp (z + P.value (rawOf b)) k) (value-rawOf a) ⟩
    modp (toℕ a + P.value (rawOf b)) k
  ≡⟨ cong (λ z → modp (toℕ a + z) k) (value-rawOf b) ⟩
    modp (toℕ a + toℕ b) k
  ≡⟨ cong (λ z → modp z k) (sym (+-identityʳ (toℕ a + toℕ b))) ⟩
    modp (toℕ a + toℕ b + 0) k
  ≡⟨ sym (addCarryV-toℕ fzero a b) ⟩
    toℕ (addCarryV fzero a b)
  ∎

-- ② 乘法一致：`Positional.mul-spec`（卷积+归一）与本模块 `mulCarry`（进位递归）同值
pos-mul-agrees : ∀ {k} (a b : Vec (Fin 3) k)
  → modp (P.value (P.mulNorm k (rawOf a) (rawOf b))) k ≡ toℕ (mulCarry a b)
pos-mul-agrees {k} a b = begin
    modp (P.value (P.mulNorm k (rawOf a) (rawOf b))) k
  ≡⟨ sym (mod-of-plus-mult (P.value (P.mulNorm k (rawOf a) (rawOf b)))
                            (proj₁ (P.expand k (P.value (P.conv (rawOf a) (rawOf b))))) k) ⟩
    modp (P.value (P.mulNorm k (rawOf a) (rawOf b))
          + 3 ^ k * proj₁ (P.expand k (P.value (P.conv (rawOf a) (rawOf b))))) k
  ≡⟨ cong (λ z → modp z k) (P.mul-spec k (rawOf a) (rawOf b)) ⟩
    modp (P.value (rawOf a) * P.value (rawOf b)) k
  ≡⟨ cong (λ z → modp (z * P.value (rawOf b)) k) (value-rawOf a) ⟩
    modp (toℕ a * P.value (rawOf b)) k
  ≡⟨ cong (λ z → modp (toℕ a * z) k) (value-rawOf b) ⟩
    modp (toℕ a * toℕ b) k
  ≡⟨ sym (mulCarry-toℕ a b) ⟩
    toℕ (mulCarry a b)
  ∎

--------------------------------------------------------------------------------
-- §25. 值层的 k 一般化（全部由**已完成件**拼，不重证任何数学）
--
-- 事实核查：`repr` / `toℕ-repr` / `repr-toℕ` / `addCarryV-toℕ` / `mulGo-toℕ` /
-- `mulCarry-toℕ` 的签名**本来就是 `∀ {k}`**；只有 `fromℕ` / `add` / `mul` / `toℕ-inj`
-- 被钉在 11 位。因此「推广到任意 k」不需要新数学，只需把这几件换成通用版并借用
-- 已有的值语义引理。`mulCarry≡mul` 于是成为 `mulCarry≡mulG` 在 `k = 11` 的特例。
--------------------------------------------------------------------------------

-- 通用「值 → 表示」（就是早已 `∀ k` 的 `repr`）
fromℕk : ∀ {k} → ℕ → Vec (Fin 3) k
fromℕk {k} n = repr k n

-- 通用值层加法 / 乘法（与 11 位版本在 k=11 处定义相等，见 `addG-at-11`）
addG : ∀ {k} → Vec (Fin 3) k → Vec (Fin 3) k → Vec (Fin 3) k
addG {k} a b = repr k (toℕ a + toℕ b)

mulG : ∀ {k} → Vec (Fin 3) k → Vec (Fin 3) k → Vec (Fin 3) k
mulG {k} a b = repr k (toℕ a * toℕ b)

-- 值语义：一行 —— 就是 `toℕ-repr`
addG-toℕ : ∀ {k} (a b : Vec (Fin 3) k) → toℕ (addG a b) ≡ modp (toℕ a + toℕ b) k
addG-toℕ {k} a b = toℕ-repr k (toℕ a + toℕ b)

mulG-toℕ : ∀ {k} (a b : Vec (Fin 3) k) → toℕ (mulG a b) ≡ modp (toℕ a * toℕ b) k
mulG-toℕ {k} a b = toℕ-repr k (toℕ a * toℕ b)

-- 通用单射：由 `repr-toℕ`（早已 `∀ k`）直接得
toℕ-injG : ∀ {k} {u v : Vec (Fin 3) k} → toℕ u ≡ toℕ v → u ≡ v
toℕ-injG {k} {u} {v} e =
  trans (sym (repr-toℕ k u)) (trans (cong (repr k) e) (repr-toℕ k v))

-- 通用：逐位加法 ≡ 值层加法
addCarry≡addG : ∀ {k} (a b : Vec (Fin 3) k) → addCarryV fzero a b ≡ addG a b
addCarry≡addG {k} a b = toℕ-injG (begin
    toℕ (addCarryV fzero a b)
  ≡⟨ addCarryV-toℕ fzero a b ⟩
    modp (toℕ a + toℕ b + 0) k
  ≡⟨ cong (λ z → modp z k) (+-identityʳ (toℕ a + toℕ b)) ⟩
    modp (toℕ a + toℕ b) k
  ≡⟨ sym (addG-toℕ a b) ⟩
    toℕ (addG a b)
  ∎)

-- 通用：逐位乘法 ≡ 值层乘法（`mulCarry-toℕ` 早已 `∀ {k}`，直接借用）
mulCarry≡mulG : ∀ {k} (a b : Vec (Fin 3) k) → mulCarry a b ≡ mulG a b
mulCarry≡mulG {k} a b = toℕ-injG (trans (mulCarry-toℕ a b) (sym (mulG-toℕ a b)))

-- 11 位是特例（定义相等，故 `refl`）
addG-at-11 : ∀ (a b : Vec (Fin 3) 11) → addG a b ≡ add a b
addG-at-11 a b = refl

mulG-at-11 : ∀ (a b : Vec (Fin 3) 11) → mulG a b ≡ mul a b
mulG-at-11 a b = refl
