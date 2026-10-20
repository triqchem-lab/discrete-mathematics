{-# OPTIONS --rewriting --guardedness #-}

-- | DigitalRootClassic — 经典数字根（digital root）的构造性形式化桥
--
-- 数学背景
-- ========
-- 上游 `Sovereign.Foundation.DigitalRoot` 只给出「模 9 语义」的数字根：
--     digitalRoot n = n % 9                （9 的倍数 ↦ 0，不是 9）
-- 而**经典**数字根的定义是
--     classicRoot 0 = 0
--     classicRoot n = 1 + ((n − 1) % 9)    (n > 0，9 的倍数 ↦ 9)
-- 二者只在「非零的 9 的倍数」上不同（0 对 9），其余情形完全一致。
-- 这个差异正是 sov-math C ABI 实测的 `sov_digital_root` 语义：
--     0 ↦ 0；9 | n 且 n > 0 ↦ 9；其余 ↦ n % 9。
--
-- 本模块把这一层精确化（纯 ℕ，不用 ℤ、不用浮点、不用实数）：
--   ① `classicRoot` 的经典定义与值域界（≤ 9，n > 0 时 > 0）；
--   ② 与上游 `digitalRoot` 的**三分情形**定理：
--        · n = 0            ⇒ classicRoot n ≡ 0
--        · 9 ∣ n, n > 0     ⇒ classicRoot n ≡ 9 且 digitalRoot n ≡ 0
--        · 9 ∤ n, n > 0     ⇒ classicRoot n ≡ digitalRoot n
--   ③ 幂等 `classicRoot (classicRoot n) ≡ classicRoot n`；
--      周期 9 `classicRoot (n + 9) ≡ classicRoot n`（n > 0，n = 0 时为假，已附反例）；
--      同余保持 `classicRoot n % 9 ≡ n % 9`；
--   ④ 与 ABI 语义 `abiRoot` 的逐点一致。
--
-- 证明策略
-- ========
-- 核心是一个 9-余数二分引理 `mod9-suc-cases`：对任意余数 r < 9，
-- `suc r` 要么恰为 9（进位边界），要么严格小于 9（无进位）。
-- 有了它，「suc 之后的余数」与「余数的 succ」之间的等同就被局部化为有限判定，
-- 不引入任何 ℤ 或实数；其余各条都由 stdlib 的 `%-distribˡ-+` / `%-distribˡ-*`
-- 与 `m<n⇒m%n≡m` 代数链给出。
--
-- 状态：0 postulate / 0 hole。
module DigitalRootClassic where

open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _%_; _<_; _≤_; z≤n; s≤s)
open import Data.Nat.DivMod using (
         _/_; m%n<n; m<n⇒m%n≡m; n%n≡0; m*n%n≡0; %-distribˡ-+; %-distribˡ-*;
         m≡m%n+[m/n]*n)
open import Data.Nat.Divisibility.Core using (_∣_; divides)
open import Data.Nat.Properties using (+-identityʳ; *-zeroʳ; ≮⇒≥; ≤-antisym; _≟_; _<?_)
open import Data.Empty using (⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Binary.PropositionalEquality as P using (
         _≡_; _≢_; refl; sym; trans; cong)

-- 局部等式推理链：只用 trans / refl 拼装，
-- 避免对 stdlib 语法模块做整模块 open（显式导入纪律）。
infix  1 begin_
infixr 2 _≡⟨_⟩_
infix  3 _∎

begin_ : ∀ {A : Set} {x y : A} → x ≡ y → x ≡ y
begin p = p

_≡⟨_⟩_ : ∀ {A : Set} (x : A) {y z : A} → x ≡ y → y ≡ z → x ≡ z
x ≡⟨ p ⟩ q = trans p q

_∎ : ∀ {A : Set} (x : A) → x ≡ x
x ∎ = refl

-- 上游模 9 语义的数字根（9 的倍数 ↦ 0）
open import Sovereign.Foundation.DigitalRoot using (digitalRoot)

--------------------------------------------------------------------------------
-- §1. 经典数字根的定义
--------------------------------------------------------------------------------

-- 经典数字根：0 ↦ 0；n > 0 ↦ 1 + ((n − 1) % 9)，即 9 的倍数 ↦ 9。
-- 定义写成 suc 形式，使 `classicRoot (suc k) = suc (k % 9)` 定义等价（可归约）。
classicRoot : ℕ → ℕ
classicRoot zero    = zero
classicRoot (suc k) = suc (k % 9)

classicRoot-zero : classicRoot 0 ≡ 0
classicRoot-zero = refl

classicRoot-suc : ∀ k → classicRoot (suc k) ≡ suc (k % 9)
classicRoot-suc k = refl

-- 值域：经典数字根落在 [0, 9]
classicRoot≤9 : ∀ n → classicRoot n ≤ 9
classicRoot≤9 zero    = z≤n
classicRoot≤9 (suc k) = m%n<n k 9          -- `k % 9 < 9` 即 `suc (k % 9) ≤ 9`

-- n > 0 ⇒ 数字根 > 0（经典版与模 9 版在此分道：后者 9 ↦ 0）
classicRoot-pos : ∀ n → 0 < n → 0 < classicRoot n
classicRoot-pos zero    ()
classicRoot-pos (suc k) _ = s≤s z≤n

-- 数字根为 0 当且仅当 n = 0
classicRoot-zero-iff : ∀ n → classicRoot n ≡ 0 → n ≡ 0
classicRoot-zero-iff zero    _ = refl
classicRoot-zero-iff (suc k) e = ⊥-elim (suc-≢0 e)
  where
    -- `suc x ≢ 0`（构造子不同，空模式匹配）
    suc-≢0 : ∀ {x} → suc x ≢ 0
    suc-≢0 ()

--------------------------------------------------------------------------------
-- §2. 模 9 的两条基础引理
--------------------------------------------------------------------------------

-- 加 9 不改变模 9 余数
mod9-period : ∀ n → (n + 9) % 9 ≡ n % 9
mod9-period n = begin
    (n + 9) % 9              ≡⟨ %-distribˡ-+ n 9 9 ⟩
    ((n % 9) + (9 % 9)) % 9  ≡⟨ cong (λ x → ((n % 9) + x) % 9) (n%n≡0 9) ⟩
    ((n % 9) + 0) % 9        ≡⟨ cong (_% 9) (+-identityʳ (n % 9)) ⟩
    (n % 9) % 9              ≡⟨ m<n⇒m%n≡m (m%n<n n 9) ⟩
    n % 9                    ∎

-- suc 之后取余 = 先取余再 suc 再取余
mod9-step : ∀ k → (suc k) % 9 ≡ (suc (k % 9)) % 9
mod9-step k = %-distribˡ-+ 1 k 9     -- 1 + k ≡ suc k，1 % 9 ≡ 1（均定义等价）

--------------------------------------------------------------------------------
-- §3. 进位边界二分：suc r 要么是 9，要么严格小于 9
--------------------------------------------------------------------------------

-- 对 r < 9，`suc r` 只能落在 9（进位）或 < 9（不进位）
mod9-suc-cases : ∀ r → suc r ≤ 9 → (suc r ≡ 9) ⊎ (suc r < 9)
mod9-suc-cases r h with suc r <? 9
... | yes lt  = inj₂ lt
... | no  nlt = inj₁ (≤-antisym h (≮⇒≥ nlt))

-- 若 `(suc r) % 9 ≡ 0` 且 `suc r ≤ 9`，则必是进位边界 `suc r ≡ 9`
mod9-suc-eq9 : ∀ r → suc r ≤ 9 → (suc r) % 9 ≡ 0 → suc r ≡ 9
mod9-suc-eq9 r h hz with mod9-suc-cases r h
... | inj₁ e  = e
... | inj₂ lt = ⊥-elim (suc-≢0 (trans (sym (m<n⇒m%n≡m lt)) hz))
  where
    suc-≢0 : ∀ {x} → suc x ≢ 0
    suc-≢0 ()

-- 于是：`(suc k) % 9 ≡ 0` ⇒ `suc (k % 9) ≡ 9`（即经典数字根取 9）
mod9-step-value : ∀ k → (suc k) % 9 ≡ 0 → suc (k % 9) ≡ 9
mod9-step-value k hz =
  mod9-suc-eq9 (k % 9) (m%n<n k 9) (trans (sym (mod9-step k)) hz)

-- 反之，非零余数时 suc 不触发进位：`(suc k) % 9 ≡ suc (k % 9)`
mod9-step-nonzero : ∀ k → (suc k) % 9 ≢ 0 → (suc k) % 9 ≡ suc (k % 9)
mod9-step-nonzero k hnz with mod9-suc-cases (k % 9) (m%n<n k 9)
... | inj₂ lt = trans (mod9-step k) (m<n⇒m%n≡m lt)
... | inj₁ e  = ⊥-elim (hnz (trans (mod9-step k) (trans (cong (_% 9) e) (n%n≡0 9))))

--------------------------------------------------------------------------------
-- §4. 整除与「余数为零」的互相转换
--------------------------------------------------------------------------------

-- 9 ∣ n ⇒ n % 9 ≡ 0
div9→mod9-zero : ∀ n → 9 ∣ n → n % 9 ≡ 0
div9→mod9-zero n (divides q eq) = begin
    n % 9                     ≡⟨ cong (_% 9) eq ⟩
    (q * 9) % 9               ≡⟨ %-distribˡ-* q 9 9 ⟩
    ((q % 9) * (9 % 9)) % 9   ≡⟨ cong (λ x → ((q % 9) * x) % 9) (n%n≡0 9) ⟩
    ((q % 9) * 0) % 9         ≡⟨ cong (_% 9) (*-zeroʳ (q % 9)) ⟩
    0 % 9                     ≡⟨ m*n%n≡0 0 9 ⟩
    0                         ∎

-- n % 9 ≡ 0 ⇒ 9 ∣ n（由 n ≡ n % 9 + (n / 9) * 9）
mod9-zero→div9 : ∀ n → n % 9 ≡ 0 → 9 ∣ n
mod9-zero→div9 n h =
  divides (n / 9) (trans (m≡m%n+[m/n]*n n 9) (cong (λ x → x + (n / 9) * 9) h))

--------------------------------------------------------------------------------
-- §5. 与上游 `digitalRoot` 的三分情形
--------------------------------------------------------------------------------

-- 情形 ①：n = 0
classicRoot-at-zero : classicRoot 0 ≡ 0
classicRoot-at-zero = classicRoot-zero

-- 情形 ②：9 ∣ n 且 n > 0 ⇒ 经典数字根取 9
classicRoot-nine : ∀ n → 0 < n → 9 ∣ n → classicRoot n ≡ 9
classicRoot-nine (suc k) _ hd = mod9-step-value k (div9→mod9-zero (suc k) hd)

-- 情形 ②（对照）：同一条件下的模 9 版本取 0
digitalRoot-nine : ∀ n → 9 ∣ n → digitalRoot n ≡ 0
digitalRoot-nine n hd = div9→mod9-zero n hd

-- 情形 ③：9 ∤ n 且 n > 0 ⇒ 两个版本一致
classicRoot≡mod9 : ∀ n → 0 < n → ¬ (9 ∣ n) → classicRoot n ≡ digitalRoot n
classicRoot≡mod9 (suc k) _ hnz =
  sym (mod9-step-nonzero k (λ h → hnz (mod9-zero→div9 (suc k) h)))

-- 反向刻画：经典数字根取 9 ⇒ 9 整除 n（与 `classicRoot-nine` 合起来是充要条件）
classicRoot-nine→div9 : ∀ n → classicRoot n ≡ 9 → 9 ∣ n
classicRoot-nine→div9 zero    ()
classicRoot-nine→div9 (suc k) e = mod9-zero→div9 (suc k)
  (trans (mod9-step k) (trans (cong (_% 9) e) (n%n≡0 9)))

--------------------------------------------------------------------------------
-- §6. 幂等 / 周期 / 同余保持
--------------------------------------------------------------------------------

-- 幂等：数字根落在 [0, 9]，再过一遍不变
classicRoot-idem : ∀ n → classicRoot (classicRoot n) ≡ classicRoot n
classicRoot-idem zero    = refl
classicRoot-idem (suc k) = cong suc (m<n⇒m%n≡m (m%n<n k 9))

-- 周期 9（n > 0；n = 0 时陈述为假，见下）
classicRoot-period : ∀ n → 0 < n → classicRoot (n + 9) ≡ classicRoot n
classicRoot-period (suc k) _ = cong suc (mod9-period k)

-- 侧条件 n > 0 不可去：0 + 9 = 9 ↦ 9，而 0 ↦ 0
classicRoot-period-zero-fails : classicRoot (0 + 9) ≢ classicRoot 0
classicRoot-period-zero-fails ()

-- 同余保持：经典数字根与 n 同余模 9
classicRoot-mod9 : ∀ n → classicRoot n % 9 ≡ n % 9
classicRoot-mod9 zero = refl
classicRoot-mod9 (suc k) with mod9-suc-cases (k % 9) (m%n<n k 9)
... | inj₁ e  = trans (trans (cong (_% 9) e) (n%n≡0 9))
                      (sym (trans (mod9-step k) (trans (cong (_% 9) e) (n%n≡0 9))))
... | inj₂ lt = begin
    (suc (k % 9)) % 9  ≡⟨ m<n⇒m%n≡m lt ⟩
    suc (k % 9)        ≡⟨ sym (trans (mod9-step k) (m<n⇒m%n≡m lt)) ⟩
    (suc k) % 9        ∎

--------------------------------------------------------------------------------
-- §7. 与 sov-math C ABI 语义的逐点一致
--------------------------------------------------------------------------------

-- ABI 实测语义：0 ↦ 0；n > 0 且 9 | n ↦ 9；其余 ↦ n % 9
abiRoot : ℕ → ℕ
abiRoot zero = zero
abiRoot (suc k) with (suc k) % 9 ≟ 0
... | yes _ = 9
... | no  _ = (suc k) % 9

-- ABI 语义与经典数字根逐点相同
abiRoot≡classicRoot : ∀ n → abiRoot n ≡ classicRoot n
abiRoot≡classicRoot zero = refl
abiRoot≡classicRoot (suc k) with (suc k) % 9 ≟ 0
... | yes hz  = sym (mod9-step-value k hz)
... | no  hnz = mod9-step-nonzero k hnz

--------------------------------------------------------------------------------
-- §8. 对抗验证：具体点上的独立核对（全部 `refl`，走内核计算而非本模块的定理）
--
-- 每条都与 §5/§6 的一般定理构成「两条独立路径 → 同一命题」的交叉验证：
-- 定理给出 ∀ 陈述，`refl` 给出该点的独立求值，二者必须一致。
--------------------------------------------------------------------------------

-- 经典数字根的关键点值（9 的倍数 ↦ 9，其余 ↦ n % 9）
check-0    : classicRoot 0    ≡ 0   ; check-0    = refl
check-1    : classicRoot 1    ≡ 1   ; check-1    = refl
check-8    : classicRoot 8    ≡ 8   ; check-8    = refl
check-9    : classicRoot 9    ≡ 9   ; check-9    = refl
check-10   : classicRoot 10   ≡ 1   ; check-10   = refl
check-18   : classicRoot 18   ≡ 9   ; check-18   = refl
check-45   : classicRoot 45   ≡ 9   ; check-45   = refl
check-81   : classicRoot 81   ≡ 9   ; check-81   = refl
check-99   : classicRoot 99   ≡ 9   ; check-99   = refl
check-100  : classicRoot 100  ≡ 1   ; check-100  = refl
check-999  : classicRoot 999  ≡ 9   ; check-999  = refl

-- 大数点：1000000 = 9 * 111111 + 1
check-big  : classicRoot 1000000 ≡ 1 ; check-big  = refl

-- 幂等的具体实例（独立于 `classicRoot-idem` 的一般证明）
check-idem-45 : classicRoot (classicRoot 45) ≡ classicRoot 45 ; check-idem-45 = refl
check-idem-9  : classicRoot (classicRoot 9)  ≡ 9              ; check-idem-9  = refl

-- 周期的具体实例（独立于 `classicRoot-period` 的一般证明）
check-period-45 : classicRoot (45 + 9) ≡ classicRoot 45 ; check-period-45 = refl

-- 同余保持的具体实例（独立于 `classicRoot-mod9` 的一般证明）
check-mod9-999 : classicRoot 999 % 9 ≡ 999 % 9 ; check-mod9-999 = refl

-- 三分定理的实例化：一般定理（classicRoot-nine）与 refl 求值给出同一结论
check-nine-45 : classicRoot 45 ≡ 9
check-nine-45 = classicRoot-nine 45 (s≤s z≤n) (divides 5 refl)
check-nine-81 : classicRoot 81 ≡ 9
check-nine-81 = classicRoot-nine 81 (s≤s z≤n) (divides 9 refl)

-- 上游模 9 版本在同一批点上的对照（9 的倍数 ↦ 0）
check-digital-9   : digitalRoot 9   ≡ 0 ; check-digital-9   = refl
check-digital-45  : digitalRoot 45  ≡ 0 ; check-digital-45  = refl
check-digital-7   : digitalRoot 7   ≡ 7 ; check-digital-7   = refl

-- ABI 语义的点值（独立于 `abiRoot≡classicRoot` 的一般证明）
check-abi-0    : abiRoot 0    ≡ 0 ; check-abi-0    = refl
check-abi-9    : abiRoot 9    ≡ 9 ; check-abi-9    = refl
check-abi-45   : abiRoot 45   ≡ 9 ; check-abi-45   = refl
check-abi-10   : abiRoot 10   ≡ 1 ; check-abi-10   = refl
check-abi-999  : abiRoot 999  ≡ 9 ; check-abi-999  = refl
