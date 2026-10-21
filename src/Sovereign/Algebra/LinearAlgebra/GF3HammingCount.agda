{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Algebra.LinearAlgebra.GF3HammingCount
-- 正确环上的 Hamming 计数（T4 修正版，2026-10-21）
--
-- 数学背景（2026-10-21 人类修正 —— 根本原因）
--   项目基底是**域塔**：GF(3) → GF(9)=GF(3)[x]/(x²+1) → …（不可约多项式 ⇒ **域** ✓，
--   有 Frobenius 自同构 σ(x)=x³ ✓，有 C₄ 相位 ✓，八要素齐 ✓）。
--   此前 T4 用的 `GF(3)[x]/(x³)` 是**幂零 thickening** ✗ —— 商环非域、Frobenius 打到零、
--   无相位、无刚性 ⇒ 八要素缺 ④⑦ ⇒ **不在展示群框架内** ⇒ 「数学基底不一样」= 无法闭合的根本原因。
--
--   正确环：`R_n = Functions((Z/3)^n, GF(3)) = GF(3)[x_j]/(x_j³ − x_j)`（**reduced** ✓）
--   在函数环里 `F = Σ x_j²` 是**点态乘法**（`x_j²` 是非零指示子）：
--        `(F · f)(x) = Hamming(x) mod 3 · f(x)`
--   ⇒ `F` 是**对角算子** ⇒ `a_n = dim ker F = #{x : Hamming(x) ≡ 0 mod 3}`。
--
-- 本模块
--   `C0/C1/C2`：Hamming 重量模 3 余 0/1/2 的点数（递归）
--   前四个值由内核 `refl` 核对
--   `C0#2` / `C0#3` / `C0#4`：`C_r(n+1) = 2·C_r(n) + C_{r−1}(n)` 的展开核对
--
-- ⚠ 未完成（诚实标注）：`total : C0 n + C1 n + C2 n ≡ 3^n` 与闭式
--   `C0(2m+1) = 9^m` 的 ℕ 归纳证明 —— 需要 ℕ 重排引理（本会话未做完）。
--   这两条已被 oracle `448d1d14`（n=1..10，域 88572）验证 ✓，但**不是** Agda 定理。
--
-- 0 postulate / 0 hole

module Sovereign.Algebra.LinearAlgebra.GF3HammingCount where

open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _^_)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; sym; trans)

--------------------------------------------------------------------------------
-- §1. 三个计数（Hamming 重量模 3 的分布）
--------------------------------------------------------------------------------

C0 : ℕ → ℕ
C1 : ℕ → ℕ
C2 : ℕ → ℕ

C0 zero    = 1
C0 (suc n) = C0 n + 2 * C2 n

C1 zero    = 0
C1 (suc n) = C1 n + 2 * C0 n

C2 zero    = 0
C2 (suc n) = C2 n + 2 * C1 n

--------------------------------------------------------------------------------
-- §2. 前几个值（与 oracle `448d1d14` 对照：C0 = 1,1,1,9,33,81,225,729,2241,…）
--------------------------------------------------------------------------------

C0-zero : C0 0 ≡ 1
C0-zero = refl

C0-one : C0 1 ≡ 1
C0-one = refl

C0-two : C0 2 ≡ 1
C0-two = refl

C0-three : C0 3 ≡ 9
C0-three = refl

C0-four : C0 4 ≡ 33
C0-four = refl

C0-five : C0 5 ≡ 81
C0-five = refl

C0-six : C0 6 ≡ 225
C0-six = refl

C0-seven : C0 7 ≡ 729
C0-seven = refl

-- 奇数位闭式的四个实例（`C0 (2m+1) = 9^m`）
C0-odd-0 : C0 1 ≡ 9 ^ 0
C0-odd-0 = refl

C0-odd-1 : C0 3 ≡ 9 ^ 1
C0-odd-1 = refl

C0-odd-2 : C0 5 ≡ 9 ^ 2
C0-odd-2 = refl

C0-odd-3 : C0 7 ≡ 9 ^ 3
C0-odd-3 = refl

--------------------------------------------------------------------------------
-- §3. 递推的展开核对（`C_r(n+1) = 2·C_r(n) + C_{r−1}(n)`）
--------------------------------------------------------------------------------

C0-step : ∀ n → C0 (suc n) ≡ C0 n + 2 * C2 n
C0-step n = refl

C1-step : ∀ n → C1 (suc n) ≡ C1 n + 2 * C0 n
C1-step n = refl

C2-step : ∀ n → C2 (suc n) ≡ C2 n + 2 * C1 n
C2-step n = refl

--------------------------------------------------------------------------------
-- §4. 与 oracle 的对照（结构性事实，已被 oracle 验证；此处只做实例核对）
--------------------------------------------------------------------------------

-- oracle `448d1d14` 断言：a_n = C0 n，且在正确环上 c_n = a_n、q_n = 0。
-- 下列实例确保 `C0` 的定义与 oracle 的计数一致。
oracle-check : (C0 0 + C0 1 + C0 2 + C0 3 ≡ 1 + 1 + 1 + 9)
             × (C0 4 + C0 5 + C0 6 ≡ 33 + 81 + 225)
oracle-check = refl , refl

--------------------------------------------------------------------------------
-- §5. ★ 重排（用 stdlib Ring solver，一行）
--
-- 归纳步：`((a + 2c) + (b + 2a)) + (c + 2b) ≡ 3·((a+b)+c)`（`+` 左结合）
-- 手写需 ~80 行 `+-assoc`/`+-comm` 链 ✗；
-- `Algebra.Solver.Ring.NaturalCoefficients.Default`（ℕ 预实例化）⇒ **一行** ✓
--------------------------------------------------------------------------------

open import Data.Nat.Properties using (+-*-commutativeSemiring)
open import Algebra.Solver.Ring.NaturalCoefficients.Default +-*-commutativeSemiring

shuffle : ∀ a b c →
  ((a + 2 * c) + (b + 2 * a)) + (c + 2 * b) ≡ 3 * ((a + b) + c)
shuffle = solve 3
  (λ a b c → ((a :+ con 2 :* c) :+ (b :+ con 2 :* a)) :+ (c :+ con 2 :* b)
             := con 3 :* ((a :+ b) :+ c))
  refl

--------------------------------------------------------------------------------
-- §6. ★★★ total：`(C0 n + C1 n) + C2 n ≡ 3 ^ n`
--
-- 归纳步的形状与 `shuffle` **完全吻合**：
--   `(C0(suc n) + C1(suc n)) + C2(suc n)`
--   定义展开 ⇒ `((C0 n + 2·C2 n) + (C1 n + 2·C0 n)) + (C2 n + 2·C1 n)`（左结合）
--   `shuffle` 给出 ⇒ `3·((C0 n + C1 n) + C2 n)`
--   归纳假设   ⇒ `3·3^n = 3^(suc n)`（定义相等）
--------------------------------------------------------------------------------

★total : ∀ n → (C0 n + C1 n) + C2 n ≡ 3 ^ n
★total zero    = refl
★total (suc n) =
  trans (cong₂ _+_ (cong₂ _+_ (C0-step n) (C1-step n)) (C2-step n))
        (trans (shuffle (C0 n) (C1 n) (C2 n))
               (trans (cong (3 *_) (★total n)) refl))

--------------------------------------------------------------------------------
-- §7. ★★★ A：`C0 (2m+1) ≡ 9^m`
--
-- 关键：`Data/Nat/Base.agda:296` 给出 **`x ^ suc n = x * x ^ n`（定义）**
-- ⇒ `9 ^ suc m` / `3 ^ (2m+1) = 3 ^ suc (2m)` **直接定义归约** ⇒ `refl` ✓
--   （此前绕道 `^-distribˡ-+-*` 反而卡在 `m + 1` 上 ✗）
--------------------------------------------------------------------------------

open import Data.Nat.Properties using
  ( +-cancelʳ-≡; +-suc; +-identityʳ; *-identityʳ; *-comm
  ; ^-distribˡ-+-*; ^-distribʳ-* )

-- ①a 显式展开（互递归定义不会自动展开 ⇒ 用 `C0-step` 等重写）
C0-2step-rewrite : ∀ n →
  (C0 (suc (suc n)) + 3 * C0 n)
  ≡ ((C0 n + 2 * C2 n) + 2 * (C2 n + 2 * C1 n)) + 3 * C0 n
C0-2step-rewrite n =
  cong₂ _+_ (trans (C0-step (suc n))
                   (cong₂ _+_ (C0-step n) (cong (2 *_) (C2-step n)))) refl

-- ①b 多项式重排（Ring solver）
shuffle2 : ∀ a b c →
  ((a + 2 * c) + 2 * (c + 2 * b)) + 3 * a ≡ 4 * ((a + b) + c)
shuffle2 = solve 3
  (λ a b c → ((a :+ con 2 :* c) :+ con 2 :* (c :+ con 2 :* b)) :+ con 3 :* a
             := con 4 :* ((a :+ b) :+ c))
  refl

-- ① ★ 2-步递推：`C0(n+2) + 3·C0 n ≡ 4·3^n`
C0-two-step : ∀ n → C0 (suc (suc n)) + 3 * C0 n ≡ 4 * 3 ^ n
C0-two-step n =
  trans (C0-2step-rewrite n)
        (trans (shuffle2 (C0 n) (C1 n) (C2 n))
               (cong (4 *_) (★total n)))

--------------------------------------------------------------------------------
-- ② 指数恒等式（全部定义归约 ⇒ refl）
--------------------------------------------------------------------------------

-- ★ `9 ^ suc m ≡ 9 * 9 ^ m`（`x ^ suc n = x * x ^ n` 是定义）
★9-suc : ∀ m → 9 ^ suc m ≡ 9 * 9 ^ m
★9-suc m = refl

-- ★ `3 ^ (2m+1) ≡ 3 * 3^(2m)`（因 `2m+1` 归约为 `suc (2m)`）
★3-pow : ∀ m → 3 ^ (2 * m + 1) ≡ 3 * (3 ^ (2 * m))
★3-pow m =
  cong (3 ^_) (trans (+-suc (2 * m) 0) (cong suc (+-identityʳ (2 * m))))

-- `2 * m ≡ m + m`
2m=m+m : ∀ m → 2 * m ≡ m + m
2m=m+m = solve 1 (λ m → con 2 :* m := m :+ m) refl

-- ★ `9^m ≡ 3^(2m)`（因 `9 = 3 * 3`）
★9-pow : ∀ m → 9 ^ m ≡ 3 ^ (2 * m)
★9-pow m =
  trans (^-distribʳ-* m 3 3)
        (trans (sym (^-distribˡ-+-* 3 m m))
               (cong (3 ^_) (sym (2m=m+m m))))

-- `4 * (3 * x) ≡ 9 * x + 3 * x`（把 `9^m` 当原子）
polysolve : ∀ x → 4 * (3 * x) ≡ 9 * x + 3 * x
polysolve = solve 1 (λ x → con 4 :* (con 3 :* x) := con 9 :* x :+ con 3 :* x) refl

-- ★ `4·3^(2m+1) ≡ 9^(m+1) + 3·9^m`
rhs-eq : ∀ m → 4 * 3 ^ (2 * m + 1) ≡ 9 ^ suc m + 3 * 9 ^ m
rhs-eq m =
  trans (cong (4 *_) (★3-pow m))
        (trans (cong (λ z → 4 * (3 * z)) (sym (★9-pow m)))
               (trans (polysolve (9 ^ m))
                      (cong (λ z → z + 3 * 9 ^ m) (sym (★9-suc m)))))

-- 消去引理：`a + k ≡ b + k ⇒ a ≡ b`
-- ⚠ `+-cancelʳ-≡` 的参数顺序是 `∀ x y z → y + x ≡ z + x → y ≡ z`（x 是被消去的）
cancel : ∀ a b k → a + k ≡ b + k → a ≡ b
cancel a b k = +-cancelʳ-≡ k a b

--------------------------------------------------------------------------------
-- ③ ★★★ 主定理
--------------------------------------------------------------------------------

★C0-odd : ∀ m → C0 (2 * m + 1) ≡ 9 ^ m
★C0-odd zero    = refl
★C0-odd (suc n) =
  cancel (C0 (2 * suc n + 1)) (9 ^ suc n) (3 * C0 (2 * n + 1))
    (trans (cong (λ z → C0 z + 3 * C0 (2 * n + 1)) (idx n))
           (trans (C0-two-step (2 * n + 1))
                  (trans (rhs-eq n)
                         (cong (λ z → 9 ^ suc n + 3 * z) (sym (★C0-odd n))))))
  where
    idx : ∀ k → 2 * suc k + 1 ≡ suc (suc (2 * k + 1))
    idx = solve 1
      (λ k → con 2 :* (con 1 :+ k) :+ con 1 := con 1 :+ (con 1 :+ (con 2 :* k :+ con 1)))
      refl

--------------------------------------------------------------------------------
-- ④ 偶子序列：`E(m) = C0(2m)`
--
-- `E(m+1) + 3·E(m) = 4·9^m`（由 `C0-two-step` + `3^(2m) = 9^m`）
-- 闭式 `E(m) = (9^m + 2·(−3)^m)/3` **有符号** ⇒ ℕ 上必须分奇偶。
--------------------------------------------------------------------------------

-- ★ 偶子序列递推（无符号 ✓）
★C0-even-step : ∀ m → C0 (2 * m + 2) + 3 * C0 (2 * m) ≡ 4 * 9 ^ m
★C0-even-step m =
  trans (cong (λ z → C0 z + 3 * C0 (2 * m)) (idx m))
        (trans (C0-two-step (2 * m))
               (cong (4 *_) (sym (★9-pow m))))
  where
    -- `2 * m + 2 ≡ suc (suc (2 * m))`
    idx : ∀ m → 2 * m + 2 ≡ suc (suc (2 * m))
    idx = solve 1
      (λ m → con 2 :* m :+ con 2 := con 1 :+ (con 1 :+ con 2 :* m))
      refl

-- 偶子序列的前几个值（与 oracle 对照：E = 1, 1, 33, 225, 2241, …）
E-zero : C0 (2 * 0 + 0) ≡ 1
E-zero = refl

E-one : C0 (2 * 1) ≡ 1
E-one = refl

E-two : C0 (2 * 2) ≡ 33
E-two = refl

E-three : C0 (2 * 3) ≡ 225
E-three = refl

--------------------------------------------------------------------------------
-- ⑤ ★★★ 偶子序列闭式（分奇偶，联合归纳，全 ℕ）
--
--   ★E-even k : `3·C0(4k) ≡ 9^(2k) + 2·3^(2k)`
--   ★E-odd  k : `3·C0(4k+2) + 2·3^(2k+1) ≡ 9^(2k+1)`
--
-- 推导（都用 `+` 保持两侧，无减法）：
--   even(k) + C0-even-step(2k)  ⇒ odd(k)
--   odd(k)  + C0-even-step(2k+1) ⇒ even(k+1)
--------------------------------------------------------------------------------

-- `4k ≡ 2k + 2k`
4k=2k+2k : ∀ k → 2 * (2 * k) ≡ 2 * k + 2 * k
4k=2k+2k = solve 1 (λ k → con 2 :* (con 2 :* k) := con 2 :* k :+ con 2 :* k) refl

-- `9^(2k) ≡ 3^(2k) * 3^(2k)`
9^2k : ∀ k → 9 ^ (2 * k) ≡ (3 ^ (2 * k)) * (3 ^ (2 * k))
9^2k k =
  trans (★9-pow (2 * k))
        (trans (cong (3 ^_) (4k=2k+2k k))
               (^-distribˡ-+-* 3 (2 * k) (2 * k)))

-- `3^(2k+2) ≡ 9 * 3^(2k)`
3^2k+2 : ∀ k → 3 ^ (2 * k + 2) ≡ 9 * (3 ^ (2 * k))
3^2k+2 k =
  trans (^-distribˡ-+-* 3 (2 * k) 2)
        (*-comm (3 ^ (2 * k)) (3 ^ 2))

-- 2·3^(2k+1) ≡ 6·3^(2k)
2*3^odd : ∀ k → 2 * (3 ^ (2 * k + 1)) ≡ 6 * (3 ^ (2 * k))
2*3^odd k =
  trans (cong (λ z → 2 * z) (★3-pow k))
        (solve 1 (λ x → con 2 :* (con 3 :* x) := con 6 :* x) refl (3 ^ (2 * k)))

--------------------------------------------------------------------------------
-- ⑤ ⚠ 偶子序列的**闭式**（未完成，诚实标注）
--
-- 目标（分奇偶，全 ℕ）：
--   ★E-even k : `3·C0(4k) ≡ 9^(2k) + 2·3^(2k)`
--   ★E-odd  k : `3·C0(4k+2) + 2·3^(2k+1) ≡ 9^(2k+1)`
--   联合归纳（even(k) + C0-even-step(2k) ⇒ odd(k)；odd(k) + C0-even-step(2k+1) ⇒ even(k+1)）
--
-- ✅ 已完成的前置（都在上面，全部编译通过）：
--   ★C0-even-step : `C0(2m+2) + 3·C0(2m) ≡ 4·9^m`        ✓
--   9^2k          : `9^(2k) ≡ 3^(2k) · 3^(2k)`             ✓
--   3^2k+2        : `3^(2k+2) ≡ 9 · 3^(2k)`                ✓
--   2*3^odd       : `2·3^(2k+1) ≡ 6·3^(2k)`                ✓
--   E-zero/one/two/three : 前四个偶值 refl 核对             ✓
--
-- ❌ 缺口：联合归纳的 ℕ 记账（`solve` 在 `2*(2*k)` 形状上不匹配）
--   实例已被 oracle `448d1d14` 验证（n=1..10），**不是** Agda 定理
--------------------------------------------------------------------------------
