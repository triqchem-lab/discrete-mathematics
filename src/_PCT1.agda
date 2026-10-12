{-# OPTIONS --rewriting --guardedness #-}

-- | _PCT1
-- Church-Turing 单方向批：μ-递归 ⟹ TM 可模拟（定理侧——论题不碰）
--
-- 数学背景：部分递归函数由五生成元（零 Z / 后继 S / 投影 P / 复合 C / μ 算子）
-- 递归生成；本件承载单方向定理的构造性前件：
--   ① PrimRec 关系入定义（五生成元即定义本体——非外来公理）
--   ② 元组 → 纸带一元编码（enc1/encodeTup）
--   ③ 基本函数的纸带级模拟件 + 编码一致性（simZ/simS/simP）
--   ④ 复合步（definitional）+ μ 搜索步（良基归纳 nat-strong-ind）
--   ⑤ 核对层（后继/复合/μ 小实例）
--
-- 核心原则：
--   1. 论题 vs 定理区分：Church-Turing 是论题（不碰）；本件只做
--      定理侧「μ-递归函数类可被 TM 模拟」的构造前件；
--   2. μ 的部分性由燃料形承载（停机性不可判定——无总化 eval）；
--   3. 纸带级模拟 ≠ 机器级模拟——机器级全构（状态图装配）为立界件；
--   4. μ 步的搜索窗界限由良基归纳给出（见证 y ≤ z < y+k）。
--
-- 包含：PrimRec · peval/pevalAll · μiter/μstep · enc1/encodeTup · simZ/simS/simP
--       · μiter-bounds（良基归纳）· 核对层

module _PCT1 where

open import Data.Nat using (ℕ; zero; suc; _+_; _∸_; _<_; _≤_; z≤n; s≤s)
open import Data.Nat.Properties using (≤-refl; ≤-step; ≤-trans; n≤1+n; +-suc; m≤m+n)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.List using (List; []; _∷_; _++_)
open import Data.Vec using (Vec) renaming ([] to vnil; _∷_ to _v∷_; _++_ to _++v_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (_×_; _,_; proj₁; proj₂; Σ-syntax)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; cong)
open import Sovereign.Algebra.Automata.TuringMachine using (AB; z; o)
open import Sovereign.Foundation.WellFounded using (nat-strong-ind)

-- ────────────────────────────────────────────────────────────────────
-- §1 PrimRec：部分递归函数（关系入定义——五生成元即定义本体）
--   PrimRec n = n 元部分递归函数的生成式；语义由 peval 燃料形给出。
-- ────────────────────────────────────────────────────────────────────

data PrimRec : ℕ → Set where
  zeroₙ : ∀ {n} → PrimRec (suc n)                        -- Z(x⃗) = 0
  sucₙ  : PrimRec 1                                      -- S(x) = suc x
  projₙ : ∀ {n} → (i : Fin n) → PrimRec n                -- Pⁿᵢ(x⃗) = xᵢ
  compₙ : ∀ {n k} → PrimRec k → Vec (PrimRec n) k → PrimRec n
  μₙ    : ∀ {n} → PrimRec (suc n) → PrimRec n            -- μy[f(x⃗,y) = 0]

-- 变元取值（Fin 索引 → Vec 投影）
lookupV : ∀ {n} → Vec ℕ n → Fin n → ℕ
lookupV (x v∷ _)  fzero    = x
lookupV (_ v∷ xs) (fsuc i) = lookupV xs i

-- Maybe 单子粘合（复合步用）
bindM : ∀ {A B : Set} → Maybe A → (A → Maybe B) → Maybe B
bindM (just x) g = g x
bindM nothing  g = nothing

mutual
  -- 燃料形语义（μ 的部分性由燃料承载——无总化 eval）
  peval : ∀ {n} → PrimRec n → Vec ℕ n → ℕ → Maybe ℕ
  peval zeroₙ        xs        k = just 0
  peval sucₙ        (x v∷ vnil) k = just (suc x)
  peval (projₙ i)    xs        k = just (lookupV xs i)
  peval (compₙ f gs) xs        k = bindM (pevalAll gs xs k) (λ ys → peval f ys k)
  peval (μₙ f)       xs        k = μiter f xs k 0

  -- 复合步：逐个求值内层元（Vec 折叠）
  pevalAll : ∀ {n k} → Vec (PrimRec n) k → Vec ℕ n → ℕ → Maybe (Vec ℕ k)
  pevalAll vnil       xs k = just vnil
  pevalAll (g v∷ gs) xs k = bindM (peval g xs k) (λ y →
                            bindM (pevalAll gs xs k) (λ ys → just (y v∷ ys)))

  -- μ 搜索：窗口 [y, y+k) 内找最小零点
  μiter : ∀ {n} → PrimRec (suc n) → Vec ℕ n → ℕ → ℕ → Maybe ℕ
  μiter f xs zero    y = nothing
  μiter f xs (suc k) y = μstep (peval f (y v∷ xs) k) f xs k y

  -- μ 单步分派（顶层辅助形——where 签名视域病预防）
  μstep : ∀ {n} → Maybe ℕ → PrimRec (suc n) → Vec ℕ n → ℕ → ℕ → Maybe ℕ
  μstep (just zero)    f xs k y = just y
  μstep (just (suc r)) f xs k y = μiter f xs k (suc y)
  μstep nothing        f xs k y = nothing

-- ────────────────────────────────────────────────────────────────────
-- §2 元组 → 纸带一元编码（AB 字母表：o=1 符号，z=空白/分隔）
-- ────────────────────────────────────────────────────────────────────

enc1 : ℕ → List AB
enc1 zero    = []
enc1 (suc n) = o ∷ enc1 n

encodeTup : List ℕ → List AB
encodeTup []       = []
encodeTup (x ∷ xs) = enc1 x ++ (z ∷ encodeTup xs)

-- ────────────────────────────────────────────────────────────────────
-- §3 基本函数的纸带级模拟件 + 编码一致性
--   （纸带级变换 ≠ 机器级全构——状态图装配为立界件）
-- ────────────────────────────────────────────────────────────────────

simZ : List AB → List AB          -- Z 纸带面：输出清为零元
simZ _ = []

simS : List AB → List AB          -- S 纸带面：尾部追加一（单变元一元形）
simS t = t ++ (o ∷ [])

simP : (i : ℕ) → List AB → List AB  -- P 纸带面（单变元恒等；多变元取块随立界）
simP _ t = t

-- 编码/模拟一致性（refl 级）
check-enc0 : enc1 0 ≡ []
check-enc0 = refl

check-enc2 : enc1 2 ≡ o ∷ o ∷ []
check-enc2 = refl

check-tup : encodeTup (1 ∷ 2 ∷ []) ≡ o ∷ z ∷ o ∷ o ∷ z ∷ []
check-tup = refl

check-simS : simS (enc1 2) ≡ enc1 3
check-simS = refl

check-simZ : simZ (enc1 2) ≡ enc1 0
check-simZ = refl

-- ────────────────────────────────────────────────────────────────────
-- §4 μ 步良基归纳：搜索窗界限（见证 y ≤ w < y+k）
--   （nat-strong-ind——任务点④的 WellFounded 归纳步）
-- ────────────────────────────────────────────────────────────────────

nothing≢just : ∀ {A : Set} {a : A} → nothing ≡ just a → ⊥
nothing≢just ()

-- 加法换序桥（motive 全式形——算符段教训）
ysuc-bridge : ∀ y k → suc (y + k) ≡ y + suc k
ysuc-bridge y k = sym (+-suc y k)

-- 单步分派的界限（case on Maybe 见证——免 with 抽象）
μstep-bounds : ∀ {n} (r : Maybe ℕ) (f : PrimRec (suc n)) (xs : Vec ℕ n) (k : ℕ)
            → (∀ m → m < suc k → ∀ y w → μiter f xs m y ≡ just w → (y ≤ w) × (w < y + m))
            → ∀ y w → μstep r f xs k y ≡ just w → (y ≤ w) × (w < y + suc k)
μstep-bounds (just zero) f xs k ih y .y refl =
  ≤-refl , subst (λ t → y < t) (ysuc-bridge y k) (s≤s (m≤m+n y k))
μstep-bounds (just (suc r)) f xs k ih y w eq =
  let lelt = ih k (s≤s ≤-refl) (suc y) w eq
  in ≤-trans (n≤1+n y) (proj₁ lelt) , subst (λ t → w < t) (ysuc-bridge y k) (proj₂ lelt)
μstep-bounds nothing f xs k ih y w eq = ⊥-elim (nothing≢just eq)

-- 主件：μiter 找到的见证在搜索窗内（良基归纳 on k）
μiter-bounds : ∀ {n} (f : PrimRec (suc n)) (xs : Vec ℕ n) (k y w : ℕ)
             → μiter f xs k y ≡ just w → (y ≤ w) × (w < y + k)
μiter-bounds {n} f xs =
  nat-strong-ind (λ k → ∀ y w → μiter f xs k y ≡ just w → (y ≤ w) × (w < y + k))
                 (λ k ih → step k ih)
  where
  step : ∀ k → (∀ m → m < k → ∀ y w → μiter f xs m y ≡ just w → (y ≤ w) × (w < y + m))
       → ∀ y w → μiter f xs k y ≡ just w → (y ≤ w) × (w < y + k)
  step zero    ih y w ()
  step (suc k) ih y w eq = μstep-bounds (peval f (y v∷ xs) k) f xs k ih y w eq

-- μ 首步见证（零点即停）
μiter-zero : ∀ {n} (f : PrimRec (suc n)) (xs : Vec ℕ n) (k y : ℕ)
           → peval f (y v∷ xs) k ≡ just 0 → μiter f xs (suc k) y ≡ just y
μiter-zero f xs k y eq rewrite eq = refl

-- ────────────────────────────────────────────────────────────────────
-- §5 核对层（后继 / 复合 / μ 小实例——refl 级）
-- ────────────────────────────────────────────────────────────────────

check-suc : peval sucₙ (2 v∷ vnil) 3 ≡ just 3
check-suc = refl

check-comp : peval (compₙ sucₙ (sucₙ v∷ vnil)) (2 v∷ vnil) 3 ≡ just 4
check-comp = refl

check-proj : peval (projₙ (fsuc fzero)) (5 v∷ 7 v∷ vnil) 3 ≡ just 7
check-proj = refl

check-mu : peval (μₙ zeroₙ) vnil 3 ≡ just 0
check-mu = refl

-- ────────────────────────────────────────────────────────────────────
-- §6 立界（诚实边界——无空壳签名）
--   (i) 机器级全构：五生成元的 TM 状态图装配（纸带级 → stepH 级桥）
--   (ii) 复合/μ 的机器级模拟（simC/simμ 状态图版）
--   (iii) 论题侧（Church-Turing 等价）永不碰——本件只交定理侧前件
--   (iv) μiter 完备性（窗口内存在 ⟹ 找到——需 peval 燃料单调性件）
-- ────────────────────────────────────────────────────────────────────
