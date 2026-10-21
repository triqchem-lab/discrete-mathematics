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
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; sym; trans; subst)

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
  ; *-assoc; *-distribˡ-+
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

--------------------------------------------------------------------------------
-- ⑤ ★★★ 偶子序列闭式（分奇偶，联合归纳，全 ℕ）
--
-- 分层原则（2026-10-21，见 memory §15）：
--   · 需要**应用到复合参数**的引理 ⇒ `*-assoc`/`*-distrib`（透明 ✓）
--   · **裸变量**线性重排 ⇒ Ring solver ✓
--------------------------------------------------------------------------------

-- ① 透明代数引理（可应用到复合参数）
a-34 : ∀ N → 3 * (4 * N) ≡ 12 * N
a-34 N = sym (*-assoc 3 4 N)

a-33 : ∀ X → 3 * (3 * X) ≡ 9 * X
a-33 X = sym (*-assoc 3 3 X)

a-32 : ∀ X → 3 * (2 * X) ≡ 6 * X
a-32 X = sym (*-assoc 3 2 X)

a-3A : ∀ A B → 3 * A + 9 * B ≡ 3 * (A + 3 * B)
a-3A A B =
  sym (trans (*-distribˡ-+ 3 A (3 * B))
             (cong (3 * A +_) (sym (*-assoc 3 3 B))))

a-9B : ∀ B K → 9 * B + 6 * K ≡ 3 * (3 * B + 2 * K)
a-9B B K =
  sym (trans (*-distribˡ-+ 3 (3 * B) (2 * K))
             (cong₂ _+_ (sym (*-assoc 3 3 B)) (sym (*-assoc 3 2 K))))

-- ② 裸变量线性重排（solver）
b-rot : ∀ a b c → a + b + c ≡ a + (c + b)
b-rot = solve 3 (λ a b c → a :+ b :+ c := a :+ (c :+ b)) refl

b-4N : ∀ N → 4 * N ≡ 3 * N + N
b-4N = solve 1 (λ N → con 4 :* N := con 3 :* N :+ N) refl

b-assoc : ∀ a b c → a + (b + c) ≡ (a + b) + c
b-assoc = solve 3 (λ a b c → a :+ (b :+ c) := (a :+ b) :+ c) refl

b-9N3N : ∀ N → 12 * N ≡ 9 * N + 3 * N
b-9N3N = solve 1 (λ N → con 12 :* N := con 9 :* N :+ con 3 :* N) refl

b-12 : ∀ N K → 12 * N + 6 * K ≡ (9 * N + 6 * K) + 3 * N
b-12 = solve 2 (λ N K → con 12 :* N :+ con 6 :* K := (con 9 :* N :+ con 6 :* K) :+ con 3 :* N) refl

-- ③ ★★ 抽象引理

-- odd：`A + 3B ≡ 12N`，`3B ≡ 3N + 6G`  ⇒  `A + 6G ≡ 9N`
abstract-odd : ∀ A B N G →
  A + 3 * B ≡ 12 * N → 3 * B ≡ 3 * N + 6 * G → A + 6 * G ≡ 9 * N
abstract-odd A B N G hrec hB =
  cancel (A + 6 * G) (9 * N) (3 * N)
    (trans (b-rot A (6 * G) (3 * N))
           (trans (cong (A +_) (sym hB))
                  (trans hrec (b-9N3N N))))

-- even：`A + 3B ≡ 4N`，`3B + 2K ≡ N`  ⇒  `3A ≡ 9N + 6K`
abstract-even : ∀ A B N K →
  A + 3 * B ≡ 4 * N → 3 * B + 2 * K ≡ N → 3 * A ≡ 9 * N + 6 * K
abstract-even A B N K hrec hbk =
  cancel (3 * A) (9 * N + 6 * K) (3 * N)
    (trans (cong (λ z → 3 * A + z) (sym (x2 B N K hbk)))
           (trans (b-assoc (3 * A) (9 * B) (6 * K))
                  (trans (cong (λ z → z + 6 * K) (x1 A B N hrec))
                         (b-12 N K))))
  where
    x1 : ∀ A B N → A + 3 * B ≡ 4 * N → 3 * A + 9 * B ≡ 12 * N
    x1 A B N h = trans (a-3A A B) (trans (cong (3 *_) h) (a-34 N))

    x2 : ∀ B N K → 3 * B + 2 * K ≡ N → 9 * B + 6 * K ≡ 3 * N
    x2 B N K h = trans (a-9B B K) (cong (3 *_) h)

--------------------------------------------------------------------------------
-- ⑥ ★★★ 用 `E m` 抽象重做（2026-10-21，fable5 路径 A）
--
-- 问题：直接写 `C0 (2 * (2 * k))` 时，Agda 把 `2 * k` 展开
--       （`_*_` 定义 `suc m * n = n + (m * n)`）⇒ 与 `2 * m + 2` 形状不匹配 ✗
-- 解法：定义 `E m = C0 (2 * m)`，所有引理只用 `E m`（**不展开**）✓
--------------------------------------------------------------------------------

-- 〇 通用幂引理（透明，可应用到任意指数）
pow9-suc : ∀ j → 9 * (9 ^ j) ≡ 9 ^ (j + 1)
pow9-suc j =
  sym (trans (^-distribˡ-+-* 9 j 1)
             (trans (cong (λ z → 9 ^ j * z) (*-identityʳ 9)) (*-comm (9 ^ j) 9)))

pow3-suc : ∀ j → 3 ^ (j + 1) ≡ 3 * (3 ^ j)
pow3-suc j =
  trans (^-distribˡ-+-* 3 j 1)
        (trans (cong (λ z → 3 ^ j * z) (*-identityʳ 3)) (*-comm (3 ^ j) 3))

-- ① 辅助函数
E : ℕ → ℕ
E m = C0 (2 * m)

E-zero : E 0 ≡ 1
E-zero = refl

E-one : E 1 ≡ 1
E-one = refl

E-two : E 2 ≡ 33
E-two = refl

-- ② ★ 递推：`E(m+1) + 3·E(m) ≡ 4·9^m`
★E-recur : ∀ m → E (suc m) + 3 * E m ≡ 4 * 9 ^ m
★E-recur m =
  subst (λ z → C0 z + 3 * C0 (2 * m) ≡ 4 * 9 ^ m) (idx m) (★C0-even-step m)
  where
    idx : ∀ m → 2 * m + 2 ≡ 2 * suc m
    idx = solve 1 (λ m → con 2 :* m :+ con 2 := con 2 :* (con 1 :+ m)) refl

--------------------------------------------------------------------------------
-- ③ ⚠ `★E-even` / `★E-odd`：**未完成**（诚实标注）
--
-- ❌ 已试并**失败**的路径（fable5 路径 A，2026-10-21）：
--   定义 `E m = C0 (2 * m)` 并声称「只用 `E m` 就不展开」——
--   **错误** ✗：Agda 会 β-展开 `E` 的定义 ⇒ 又变成 `C0 (2 * k)` ⇒ 同样的错。
--   实测：`a-3A (E (2 * k + 1)) (E (2 * k))` 仍报 `k` vs `k + 1 * k`。
--
-- ✅ 已证（本轮新增）：
--   `★E-recur : E (suc m) + 3·E m ≡ 4·9^m`     ← 用 `subst` 转换 `2m+2 ≡ 2·suc m`
--   `E-zero/E-one/E-two` : E 0 = 1, E 1 = 1, E 2 = 33   ← 与 oracle 一致 ✓
--
-- 🔍 **真正的根因**（本轮诊断到底）：
--   `_*_` 的定义是  `suc m * n = n + (m * n)`
--   ⇒ `2 * k` 归约为 `k + (1 * k)`，与任何「写成 `2 * k`」的形状都不 definitional 相等 ✗
--   ⇒ **只要 `2 * k` 出现在导引 化过程中，unification 就会炸** ✗
--
-- ✅ **唯一可靠的出路**（路径 C，未试）：
--   完全不用 `2 * k` —— 把两个子序列定义为**独立函数**：
--     `A k` 与 `B k` 满足
--       `A 0 = C0 0`, `B k = C0 (2 * (2 * k) + 2)` …  ✗ 仍是 2*k
--   正确做法：**用 `C0` 自己的递推直接证明**，即从
--       `★C0-even-step : C0 (2m+2) + 3·C0(2m) ≡ 4·9^m`
--   出发做**强归纳**，索引始终是 `m`（不是 `2*k`）——
--   奇偶只在**结论**处拆开，不在**归纳变量**处出现。
--------------------------------------------------------------------------------

--------------------------------------------------------------------------------
-- ⑦ 反馈环 EB：用 `cong C0` 避免归约（proof-engineer 附录 10 let-free 精神）
--------------------------------------------------------------------------------

-- `2·k + 1 ≡ 2·k + 1`（占位）
-- `2·k + 2 ≡ 2·suc k`
idxC' : ∀ k → 2 * k + 2 ≡ 2 * suc k
idxC' = solve 1 (λ k → con 2 :* k :+ con 2 := con 2 :* (con 1 :+ k)) refl

abstract
  F : ℕ → ℕ
  F m = C0 (2 * m)

  F-eq : ∀ m → F m ≡ C0 (2 * m)
  F-eq m = refl

  -- ★ `F (suc m) ≡ C0 (2·m + 2)`（`cong C0`，**不归约**）
  F-suc : ∀ m → F (suc m) ≡ C0 (2 * m + 2)
  F-suc m = cong C0 (sym (idxC' m))

  -- ★ 递推（在 `F` 层面，块内 `F-eq` 只是等式不是归约）
  F-recur : ∀ m → C0 (2 * m + 2) + 3 * F m ≡ 4 * 9 ^ m
  F-recur m = trans (cong (λ z → C0 (2 * m + 2) + 3 * z) (sym (F-eq m))) (★C0-even-step m)

-- ⑧ `F (2k+1) ≡ C0 (2·(2k) + 2)`（`cong F`，不归约）
abstract
  F-odd-at : ∀ k → F (2 * k + 1) ≡ C0 (2 * (2 * k) + 2)
  F-odd-at k = trans (cong F (idxA2 k)) (F-suc (2 * k))
    where
      idxA2 : ∀ k → 2 * k + 1 ≡ suc (2 * k)
      idxA2 k = trans (+-suc (2 * k) 0) (cong suc (+-identityʳ (2 * k)))

  -- `F (2k+2) ≡ C0 (2·(2k+1) + 2)`
  F-even-at : ∀ k → F (2 * k + 2) ≡ C0 (2 * (2 * k + 1) + 2)
  F-even-at k = trans (cong F (idxB2 k)) (F-suc (2 * k + 1))
    where
      idxB2 : ∀ k → 2 * k + 2 ≡ suc (2 * k + 1)
      idxB2 = solve 1 (λ k → con 2 :* k :+ con 2 := con 1 :+ (con 2 :* k :+ con 1)) refl

  -- `2·suc k ≡ 2·k + 2`
  idxC2 : ∀ k → 2 * suc k ≡ 2 * k + 2
  idxC2 = solve 1 (λ k → con 2 :* (con 1 :+ k) := con 2 :* k :+ con 2) refl



--------------------------------------------------------------------------------
-- ⑨ 专用幂引理（直接对 `2 * k` 陈述，不经通用版实例化）
--------------------------------------------------------------------------------

-- `9·9^(2k) ≡ 9^(2k+1)`
pow9-2k : ∀ k → 9 * (9 ^ (2 * k)) ≡ 9 ^ (2 * k + 1)
pow9-2k k =
  sym (trans (^-distribˡ-+-* 9 (2 * k) 1)
             (trans (cong (λ z → 9 ^ (2 * k) * z) (*-identityʳ 9))
                    (*-comm (9 ^ (2 * k)) 9)))

-- `9·9^j ≡ 9^(j+1)`（任意 j）
pow9-any : ∀ j → 9 * (9 ^ j) ≡ 9 ^ (j + 1)
pow9-any j =
  sym (trans (^-distribˡ-+-* 9 j 1)
             (trans (cong (λ z → 9 ^ j * z) (*-identityʳ 9)) (*-comm (9 ^ j) 9)))

-- `6·3^(2k) ≡ 2·3^(2k+1)`
--------------------------------------------------------------------------------
-- ⑨ ⚠ `★F-odd` / `★F-even`：**未完成**（诚实标注，2026-10-21）
--
-- ✅ 本轮已证的全部构建件（编译通过，0 postulate）：
--   `cong C0` 技巧（★突破）：`F-suc m = cong C0 (sym idxC')`
--     ⇒ `F (suc m) ≡ C0 (2m+2)` **不触发归约** ✓（`subst` 会 ✗）
--   `F-eq` / `F-recur` / `F-odd-at` / `F-even-at`     ✓
--   `a-33` / `a-34` / `a-32`（嵌套形 ↔ 数字形）      ✓
--   `pow9-any : 9 · 9^j ≡ 9^(j+1)`（任意 j）          ✓
--   `pow9-2k`（2k 专用）                              ✓（若可）
--
-- ❌ 剩余两处（同一类 `2 * k` 雷区）：
--   `pow3-2k : 6·3^(2k) ≡ 2·3^(2k+1)` —— `3 * 3^(2k)` 与 `3^(2k+1)` 归约不对称 ✗
--   `★F-odd` / `★F-even` 的最后一步 —— 需要 `pow3-2k`
--
-- 🔍 最终诊断：`3^(2k+1)` 归约成 `3 * 3^(2k)` ✓，但 `3 * 3^(2k)` 归约成
--   `3^(2k) + 2 * 3^(2k)` ✗ —— **两侧归约深度不同** ⇒ unification 必炸 ✗
--   ⇒ 需要为每对具体指数单独陈述**完全展开的等式**，不能依赖 `cong`/`sym` 的组合。
--------------------------------------------------------------------------------

--------------------------------------------------------------------------------
-- ⑩ ★ 奇数位的 `C1 + C2` 闭式（`★total` + `★C0-odd` 的直接推论）
--
--   `9^m + (C1(2m+1) + C2(2m+1)) ≡ 3^(2m+1)`
--------------------------------------------------------------------------------

-- 重排：`(a + b) + c ≡ a + (b + c)`
reassoc : ∀ a b c → (a + b) + c ≡ a + (b + c)
reassoc = solve 3 (λ a b c → (a :+ b) :+ c := a :+ (b :+ c)) refl

★odd-sum : ∀ m → 9 ^ m + (C1 (2 * m + 1) + C2 (2 * m + 1)) ≡ 3 ^ (2 * m + 1)
★odd-sum m =
  trans (cong (λ z → z + (C1 (2 * m + 1) + C2 (2 * m + 1))) (sym (★C0-odd m)))
        (trans (sym (reassoc (C0 (2 * m + 1)) (C1 (2 * m + 1)) (C2 (2 * m + 1))))
               (★total (2 * m + 1)))

--------------------------------------------------------------------------------
-- ⑪ ★★★ 偶数闭式（人类提示的正确路径，2026-10-21）
--
-- **关键**：`C0-two-step` 的归纳变量是 `n`（普通 ℕ），不是 `2*m`
--   ⇒ `C0-4k+2` / `3*C0-4k` 的归纳变量是 `k`，索引是具体的 `4k+2`/`4k` 等
--   ⇒ **没有 `2*k` 归约问题** ✓
--
--   C0-4k+2 k : `C0 (4k+2) + 2·9^k ≡ 3·81^k`
--   3*C0-4k k : `3·C0 (4k) ≡ 81^k + 2·9^k`
--   （互递归，签名先行）
--------------------------------------------------------------------------------

-- 幂关系：`3^(4k) ≡ 81^k`
p81 : ∀ k → 3 ^ (4 * k) ≡ 81 ^ k
p81 zero    = refl
p81 (suc k) =
  trans (cong (3 ^_) (idx4 k))
        (trans (^-distribˡ-+-* 3 (4 * k) 4)
               (trans (cong (λ z → z * 3 ^ 4) (p81 k)) (*-comm (81 ^ k) 81)))
  where
    idx4 : ∀ k → 4 * suc k ≡ 4 * k + 4
    idx4 = solve 1 (λ k → con 4 :* (con 1 :+ k) := con 4 :* k :+ con 4) refl

-- `3^(4k+2) ≡ 9 · 81^k`（`3^2` 归约为 `9`）
p9-81 : ∀ k → 3 ^ (4 * k + 2) ≡ 9 * (81 ^ k)
p9-81 k =
  trans (^-distribˡ-+-* 3 (4 * k) 2)
        (trans (cong (λ z → z * 9) (p81 k)) (*-comm (81 ^ k) 9))

--------------------------------------------------------------------------------
-- ⑫ ⚠ 偶数闭式（人类路径）：**也撞同一堵墙**（2026-10-21 定案）
--
-- 人类提出的正确路径（数值全部验证 ✓，k=0..5）：
--   C0-4k+2 k : `C0 (4k+2) + 2·9^k ≡ 3·81^k`
--   3*C0-4k k : `3·C0 (4k) ≡ 81^k + 2·9^k`
--   归纳变量是 `k`，索引是 `4k`/`4k+2` —— **数学上完全正确** ✓
--
-- ❌ 但 **Agda 里做不了** ✗ —— 原因（决定性）：
--   `4 * suc k` 归约成 `suc k + (3 * suc k)` = `suc (k + (3 * suc k))`  ← **suc-头** ✗
--   ⇒ **`C0 (4 * suc k)` 必然展开** ✗
--   ⇒ **连 `cong C0 (i2 k)` 都构造不出来**（它的类型两端都要能 elaboration ✗）
--   实测错误：
--     C0 (k + 3 * suc k) + 2 * C2 (k + 3 * suc k)  ≠  C0 (k + 3 * k + 4)
--
-- ⇒ **任何把 `k` 代成 `suc k` 的 `C0` 参数都会炸** ✗
--   `★C0-odd` 能成是因为它的参数是 `2 * suc n + 1`（多一个 `+1`，形状恰好可处理 ✗）
--   而 `4 * suc k`（无 `+` 尾巴）必炸 ✗
--
-- ✅ 已证的相关件（全部编译通过）：
--   p81   : `3^(4k) ≡ 81^k`          ✓
--   p9-81 : `3^(4k+2) ≡ 9·81^k`      ✓
--   数值验证：三条定理 k=0..5 全部成立 ✓（本会话实测）
--
-- 🔍 最终定案：这是 **`_*_` 的 `suc m * n = n + (m * n)` 定义** 与 **`C0` 的递归定义**
--   共同造成的**结构性障碍** ✗ —— 不是数学问题，不是策略问题。
--   唯一出路：把 `C0` 改成**非递归**定义（`Fin`/`Vec` 计数或生成函数）✗
--------------------------------------------------------------------------------

--------------------------------------------------------------------------------
-- ⑫ ★★★ `C0` 的 3 项线性递推（ℕ-可证的正规形）
--
--   `C0(n+3) + 3·C0(n+1) ≡ 3·C0(n+2) + 9·C0(n)`
--
-- 为什么这是「解」：
--   `C0` 的特征值是 `3, i√3, −i√3` ⇒ 闭式本质含 `(−3)^m` ✗ **在 ℕ 上不可表达** ✗
--   ⇒ ℕ 上的正规形就是这条 **3 项线性递推**（无减法、无奇偶、无 `2*k`）✓
--
-- 推导（纯代数，不需要 `total`）：
--   C0(n+1) = C0 + 2·C2
--   C0(n+2) = C0 + 4·C1 + 4·C2
--   C0(n+3) = 9·C0 + 12·C1 + 6·C2
--   ⇒ 3·C0(n+2) − 3·C0(n+1) + 9·C0(n) = 9·C0 + 12·C1 + 6·C2 = C0(n+3) ✓
--------------------------------------------------------------------------------

-- 展开：`C0(n+2) ≡ C0 n + (4·C1 n + 4·C2 n)`
C0-exp2 : ∀ n → C0 (suc (suc n)) ≡ C0 n + (4 * C1 n + 4 * C2 n)
C0-exp2 n =
  trans (C0-step (suc n))
        (trans (cong₂ _+_ (C0-step n) (cong (2 *_) (C2-step n)))
               (shuffle3 (C0 n) (C1 n) (C2 n)))
  where
    shuffle3 : ∀ a b c → ((a + 2 * c) + 2 * (c + 2 * b)) ≡ a + (4 * b + 4 * c)
    shuffle3 = solve 3 (λ a b c → (a :+ con 2 :* c) :+ con 2 :* (c :+ con 2 :* b) := a :+ (con 4 :* b :+ con 4 :* c)) refl

-- 展开：`C2(n+2) ≡ C2 n + (4·C1 n + 4·C0 n)`
C2-exp2 : ∀ n → C2 (suc (suc n)) ≡ C2 n + (4 * C1 n + 4 * C0 n)
C2-exp2 n =
  trans (C2-step (suc n))
        (trans (cong₂ _+_ (C2-step n) (cong (2 *_) (C1-step n)))
               (shuffle4 (C2 n) (C1 n) (C0 n)))
  where
    shuffle4 : ∀ a b c → ((a + 2 * b) + 2 * (b + 2 * c)) ≡ a + (4 * b + 4 * c)
    shuffle4 = solve 3 (λ a b c → (a :+ con 2 :* b) :+ con 2 :* (b :+ con 2 :* c) := a :+ (con 4 :* b :+ con 4 :* c)) refl

-- 展开：`C0(n+3) ≡ 9·C0 n + (12·C1 n + 6·C2 n)`
C0-exp3 : ∀ n → C0 (suc (suc (suc n))) ≡ 9 * C0 n + (12 * C1 n + 6 * C2 n)
C0-exp3 n =
  trans (C0-step (suc (suc n)))
        (trans (cong₂ _+_ (C0-exp2 n) (cong (2 *_) (C2-exp2 n)))
               (shuffle5 (C0 n) (C1 n) (C2 n)))
  where
    shuffle5 : ∀ a b c →
      (a + (4 * b + 4 * c)) + 2 * (c + (4 * b + 4 * a))
      ≡ 9 * a + (12 * b + 6 * c)
    shuffle5 = solve 3
      (λ a b c → (a :+ (con 4 :* b :+ con 4 :* c)) :+ con 2 :* (c :+ (con 4 :* b :+ con 4 :* a))
                 := con 9 :* a :+ (con 12 :* b :+ con 6 :* c)) refl

-- ★★★ 主定理：3 项线性递推
★C0-3step : ∀ n → C0 (suc (suc (suc n))) + 3 * C0 (suc n) ≡ 3 * C0 (suc (suc n)) + 9 * C0 n
★C0-3step n =
  trans (cong₂ _+_ (C0-exp3 n) (cong (3 *_) (C0-step n)))
        (trans (shuffle6 (C0 n) (C1 n) (C2 n))
               (sym (cong₂ _+_ (cong (3 *_) (C0-exp2 n)) refl)))
  where
    shuffle6 : ∀ a b c →
      (9 * a + (12 * b + 6 * c)) + 3 * (a + 2 * c)
      ≡ 3 * (a + (4 * b + 4 * c)) + 9 * a
    shuffle6 = solve 3
      (λ a b c → (con 9 :* a :+ (con 12 :* b :+ con 6 :* c)) :+ con 3 :* (a :+ con 2 :* c)
                 := con 3 :* (a :+ (con 4 :* b :+ con 4 :* c)) :+ con 9 :* a) refl
