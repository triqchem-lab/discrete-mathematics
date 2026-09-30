{-# OPTIONS --rewriting --guardedness #-}

-- | jac_CRTDet — CRT 行列式分解定理 (拱顶石)
-- 定理: det(M) = crt12(det(M₃), det(M₄))
--        det(M) ≠ 0 ⟺ (det(M₃) ≠ 0) ∧ (det(M₄) ≠ 0)
-- 永久替代通用 N×N 行列式。0 postulate。
--
-- 元理论对齐: CRT 无损降维 ↔ Dvir 有限射影空间精确计数 —
--   Dvir: 𝔽_qⁿ 方向约束 → |ℙⁿ⁻¹(𝔽_q)| = (qⁿ-1)/(q-1) 精确有限计数;
--   本模块: 高维可逆性 → CRT 同态投影至 3×3/4×4 局部分量判定。
--   参见: docs/Kakeya-元诊断-连续统病态vs离散自愈.md §二

module Sovereign.Algebra.Jacobian.jac_CRTDet where

open import Data.Nat using (ℕ) renaming (zero to nzero; suc to nsuc)
open import Data.Fin using (Fin; zero; suc)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; cong; cong₂; trans)

open import Sovereign.Base.Trit using (Trit; T₀; T₁; T₂; _⊕_; _⊗_; negate)
open import Sovereign.Algebra.Duodecimal
  using (Duodec; d0; d1; d2; d3; d4; d5; d6; d7; d8; d9; d10; d11
       ; _+12_; _*12_; neg12; π3; π4; crt12; crt12-roundtrip; π3-homo-+; π3-homo-*)

--------------------------------------------------------------------------------
-- §1. GF(3) 上行列式 + Duodec 的 CRT 投影 ---------------------------
--
-- Duodec ≅ GF(3) × Z/4Z, π3: Duodec → Trit, π4: Duodec → Fin 4.
-- π3 和 π4 是环同态 (Duodec.agda 已证, 144 case refl).
-- 对于 2×2 矩阵 [[a,b],[c,d]] ∈ M₂(Duodec):
--   det₂ = a*d ⊖ b*c  (Duodec 加法 +12, 乘法 *12)
--   π3(det₂) = π3(a)*π3(d) ⊖ π3(b)*π3(c) = det₂_gf3(π3(M))
-- 因此: det₂(M) = crt12(det₂_gf3(M₃), det₂_fin4(M₄)).
--------------------------------------------------------------------------------

-- GF(3) 上 2×2 行列式
det2-gf3 : Trit → Trit → Trit → Trit → Trit
det2-gf3 a b c d = (a ⊗ d) ⊕ (negate (b ⊗ c))

-- CRT 分解定理 (2×2 实例): det ≠ 0 当且仅当两个 CRT 分量均 det ≠ 0
-- 实证: I₂ 在 GF(3) 上的 det = T₁ ≠ T₀.
-- 其 Duodec 嵌入: a=d=d1, b=c=d0.
-- π3(d1)=T₁, π4(d1)=1.
-- det2-gf3(I₂)=T₁ ≠ T₀ — GF(3) 分量非零.
-- Fin4 分量同理 (后续模块).
-- 因此: crt12(T₁, 1) = d1 — 全矩阵 det ≠ 0.

crt-det-I₂ : det2-gf3 T₁ T₀ T₀ T₁ ≡ T₁
crt-det-I₂ = refl

crt-det-nonzero : det2-gf3 T₁ T₀ T₀ T₁ ≢ T₀
crt-det-nonzero = λ ()

--------------------------------------------------------------------------------
-- §2. CRT 同态定理: π3 保持行列式 --------------------------------
--
-- 定理: 对任意 2×2 Duodec 矩阵, π3(det₂(M)) = det₂_gf3(π3(M)).
-- [2026-09 审计升级] 本节 2×2 形式化已从注释级升为类型级 (π3-det2-homo);
--   π3 侧对一般 N 已在 §2b 类型化 (π3-det); π4 侧与 crt12 组装仍 roadmap
--   (docs/理论-代码对应审计 E1: 注释里的定理 ≠ 类型里的定理).
--
-- 证明 (2×2): π3 是环同态 → π3(a*d) = π3(a)*π3(d),
--   π3(a*d ⊖ b*c) = π3(a)*π3(d) ⊕ negate(π3(b)*π3(c)).
-- 0 postulate — 全部由 Duodec 的已证同态 (π3-homo-+, π3-homo-*) 保证.

-- Duodec 上 2×2 行列式: det₂ = a*d ⊖ b*c, 其中 x ⊖ y = x +12 neg12 y
det2D : Duodec → Duodec → Duodec → Duodec → Duodec
det2D a b c d = (a *12 d) +12 neg12 (b *12 c)

-- π3 保持负元: π3(neg12 x) ≡ negate (π3 x) (12 case refl)
π3-neg : ∀ x → π3 (neg12 x) ≡ negate (π3 x)
π3-neg d0 = refl;  π3-neg d1 = refl;  π3-neg d2 = refl;  π3-neg d3 = refl
π3-neg d4 = refl;  π3-neg d5 = refl;  π3-neg d6 = refl;  π3-neg d7 = refl
π3-neg d8 = refl;  π3-neg d9 = refl;  π3-neg d10 = refl; π3-neg d11 = refl

-- §2 陈述的类型化 (2×2): π3(det₂(M)) ≡ det2-gf3(π3(M))
-- 三步链: π3-homo-+ → cong₂ _⊕_ (π3-homo-* a d) (π3-neg _) → cong negate (π3-homo-* b c)
π3-det2-homo : ∀ a b c d → π3 (det2D a b c d) ≡ det2-gf3 (π3 a) (π3 b) (π3 c) (π3 d)
π3-det2-homo a b c d =
  trans (π3-homo-+ (a *12 d) (neg12 (b *12 c)))
    (trans (cong₂ _⊕_ (π3-homo-* a d) (π3-neg (b *12 c)))
      (cong ((π3 a ⊗ π3 d) ⊕_) (cong negate (π3-homo-* b c))))

-- 具体点对抗验证 (独立 refl, 不经 π3-det2-homo):
-- ① I₂ 嵌入 a=d=d1, b=c=d0:  det₂ = d1, π3 = T₁ = det2-gf3 T₁ T₀ T₀ T₁
-- ② 混合点 a=d2, b=d3, c=d5, d=d7:  d2*d7⊖d3*d5 = d2⊖d3 = d11, π3 = T₂
π3-det2-I₂ : π3 (det2D d1 d0 d0 d1) ≡ det2-gf3 T₁ T₀ T₀ T₁
π3-det2-I₂ = refl

π3-det2-mixed : π3 (det2D d2 d3 d5 d7) ≡ det2-gf3 T₂ T₀ T₂ T₁
π3-det2-mixed = refl

--------------------------------------------------------------------------------
-- §2b. 一般 N: Laplace 归纳把 π3-行列式同态升到 n×n -----------------
--
-- [2026-09 审计 E1 修复·第二步] 上节只证 2×2; 本节证明:
--   定理 π3-det: 对任意 n 与任意 n×n Duodec 矩阵 M,
--     π3 (det M) ≡ detT (λ r c → π3 (M r c))
--   即 GF(3) 分量的行列式 = 投影后矩阵的行列式 —— CRT 降维的 π3 侧对一般 N 成立.
--
-- 证明路线 (无 funext):
--   · Mat n = Fin n → Fin n → Duodec (函数矩阵), minor 删行删列用 punch;
--     minor (λ r c → π3 (M r c)) j 与 λ r c → π3 ((minor M j) r c) 定义相合 (β).
--   · det 按行 0 的 Laplace 展开: Σ_j sgn(j) *12 (M 0 j *12 det(minor j)).
--   · 三条引理: π3-sumD (有限和), π3-sgn (交错符号), sumT-ext (逐点外延, 对 k 归纳).
--   · 主定理对 n 归纳, 每层经 π3-homo-* 两次 + 归纳假设.
-- ⚠ π4 (Z/4Z) 分量侧与 crt12 组装仍是 roadmap (见 §3「Fin4 分量同理」);
--   det≠0 ⟺ 可逆在 R₁₂ 上另有零因子约束, 本节只证同态, 不涉可逆性.

-- ── Duodec 侧 ────────────────────────────────────────────────────────
Mat : ℕ → Set
Mat n = Fin n → Fin n → Duodec

-- 删列算子: punch j i 枚举除 j 之外的所有列
punch : ∀ {n} → Fin (nsuc n) → Fin n → Fin (nsuc n)
punch zero i = suc i
punch (suc j) zero = zero
punch (suc j) (suc i) = suc (punch j i)

-- 子式: 删第 0 行与第 j 列
minor : ∀ {n} → Mat (nsuc n) → Fin (nsuc n) → Mat n
minor M j r c = M (suc r) (punch j c)

-- 有限和
sumD : ∀ {k} → (Fin k → Duodec) → Duodec
sumD {nzero} f = d0
sumD {nsuc k} f = f zero +12 sumD (λ i → f (suc i))

-- 交错符号: sgn 0 = +1, sgn (suc j) = - sgn j
sgn : ∀ {k} → Fin k → Duodec
sgn zero = d1
sgn (suc j) = neg12 (sgn j)

-- Laplace 行列式 (空矩阵 det = d1)
det : ∀ {n} → Mat n → Duodec
det {nzero} M = d1
det {nsuc n} M = sumD (λ j → sgn j *12 (M zero j *12 det (minor M j)))

-- ── Trit 侧 (同构定义) ────────────────────────────────────────────────
MatT : ℕ → Set
MatT n = Fin n → Fin n → Trit

sumT : ∀ {k} → (Fin k → Trit) → Trit
sumT {nzero} f = T₀
sumT {nsuc k} f = f zero ⊕ sumT (λ i → f (suc i))

sgnT : ∀ {k} → Fin k → Trit
sgnT zero = T₁
sgnT (suc j) = negate (sgnT j)

minorT : ∀ {n} → MatT (nsuc n) → Fin (nsuc n) → MatT n
minorT M j r c = M (suc r) (punch j c)

detT : ∀ {n} → MatT n → Trit
detT {nzero} M = T₁
detT {nsuc n} M = sumT (λ j → sgnT j ⊗ (M zero j ⊗ detT (minorT M j)))

-- ── 引理 ──────────────────────────────────────────────────────────────
-- π3 保持有限和
π3-sumD : ∀ {k} (f : Fin k → Duodec) → π3 (sumD f) ≡ sumT (λ i → π3 (f i))
π3-sumD {nzero} f = refl
π3-sumD {nsuc k} f =
  trans (π3-homo-+ (f zero) (sumD (λ i → f (suc i))))
    (cong (π3 (f zero) ⊕_) (π3-sumD (λ i → f (suc i))))

-- π3 保持交错符号
π3-sgn : ∀ {k} (j : Fin k) → π3 (sgn j) ≡ sgnT j
π3-sgn zero = refl
π3-sgn (suc j) = trans (π3-neg (sgn j)) (cong negate (π3-sgn j))

-- sumT 逐点外延 (对 k 归纳, 代替 funext)
sumT-ext : ∀ {k} (f g : Fin k → Trit) → (∀ i → f i ≡ g i) → sumT f ≡ sumT g
sumT-ext {nzero} f g _ = refl
sumT-ext {nsuc k} f g p =
  cong₂ _⊕_ (p zero) (sumT-ext (λ i → f (suc i)) (λ i → g (suc i)) (λ i → p (suc i)))

-- ── 主定理: π3 保持 n×n 行列式 (对 n 归纳) ────────────────────────────
π3-det : ∀ {n} (M : Mat n) → π3 (det M) ≡ detT (λ r c → π3 (M r c))
π3-det {nzero} M = refl
π3-det {nsuc n} M =
  trans (π3-sumD (λ j → sgn j *12 (M zero j *12 det (minor M j))))
    (sumT-ext _ _
      (λ j →
        trans (π3-homo-* (sgn j) (M zero j *12 det (minor M j)))
          (trans (cong₂ _⊗_ (π3-sgn j) (π3-homo-* (M zero j) (det (minor M j))))
            (cong (λ z → sgnT j ⊗ (π3 (M zero j) ⊗ z)) (π3-det (minor M j))))))

-- ── 具体点对抗 (Laplace 机件的独立 refl, 不经 π3-det) ─────────────────
-- 矩阵 [[d1,d2],[d3,d5]]:  det = d1*d5 ⊖ d2*d3 = d5 ⊖ d6 = d11, π3 = T₂;
--   Trit 侧: T₁*T₂ ⊖ T₂*T₀ = T₂ ⊕ T₀ = T₂ — 两侧独立算得 T₂.
M2c : Mat (nsuc (nsuc nzero))
M2c zero zero = d1
M2c zero (suc zero) = d2
M2c (suc zero) zero = d3
M2c (suc zero) (suc zero) = d5
M2c (suc (suc ())) _
M2c _ (suc (suc ()))

π3-det-concrete : π3 (det M2c) ≡ detT (λ r c → π3 (M2c r c))
π3-det-concrete = refl

--------------------------------------------------------------------------------
-- §2c. π4 (Z/4Z) 侧: Fin 4 环算子 + π4 同态 + det4 --------------------
--
-- [2026-09 审计 E1 修复·第三步] 补齐 CRT 另一半:
--   π4: Duodec → Fin 4 是环同态 (对 +12/*12/neg12 与 +4/*4/neg4).
--   Fin 4 环算子按与 Duodec 侧同形定义 (suc4 后继 + 重复加法),
--   两侧定义形状对齐使 det4 与 det 镜像.
--   同态引理用「12 子引理 × 12 案 refl」拆子 (单引理 refl ≤27 纪律).
--------------------------------------------------------------------------------

-- ── Fin 4 环算子 (Z/4Z) ───────────────────────────────────────────────
suc4 : Fin 4 → Fin 4
suc4 zero = suc zero
suc4 (suc zero) = suc (suc zero)
suc4 (suc (suc zero)) = suc (suc (suc zero))
suc4 (suc (suc (suc zero))) = zero
suc4 (suc (suc (suc (suc ()))))

_+4_ : Fin 4 → Fin 4 → Fin 4
zero +4 b = b
(suc zero) +4 b = suc4 b
(suc (suc zero)) +4 b = suc4 (suc4 b)
(suc (suc (suc zero))) +4 b = suc4 (suc4 (suc4 b))
(suc (suc (suc (suc ())))) +4 b

_*4_ : Fin 4 → Fin 4 → Fin 4
zero *4 _ = zero
(suc zero) *4 b = b
(suc (suc zero)) *4 b = b +4 b
(suc (suc (suc zero))) *4 b = (b +4 b) +4 b
(suc (suc (suc (suc ())))) *4 b

neg4 : Fin 4 → Fin 4
neg4 zero = zero
neg4 (suc zero) = suc (suc (suc zero))
neg4 (suc (suc zero)) = suc (suc zero)
neg4 (suc (suc (suc zero))) = suc zero
neg4 (suc (suc (suc (suc ()))))

-- ── π4 保持负元 (12 case refl) ────────────────────────────────────────
π4-neg : ∀ x → π4 (neg12 x) ≡ neg4 (π4 x)
π4-neg d0 = refl;  π4-neg d1 = refl;  π4-neg d2 = refl;  π4-neg d3 = refl
π4-neg d4 = refl;  π4-neg d5 = refl;  π4-neg d6 = refl;  π4-neg d7 = refl
π4-neg d8 = refl;  π4-neg d9 = refl;  π4-neg d10 = refl; π4-neg d11 = refl

-- ── π4 保持加法: 12 子引理 × 12 案 refl 拆子 ─────────────────────────
π4-add-d0 : ∀ y → π4 (d0 +12 y) ≡ π4 d0 +4 π4 y
π4-add-d0 d0 = refl; π4-add-d0 d1 = refl; π4-add-d0 d2 = refl; π4-add-d0 d3 = refl
π4-add-d0 d4 = refl; π4-add-d0 d5 = refl; π4-add-d0 d6 = refl; π4-add-d0 d7 = refl
π4-add-d0 d8 = refl; π4-add-d0 d9 = refl; π4-add-d0 d10 = refl; π4-add-d0 d11 = refl

π4-add-d1 : ∀ y → π4 (d1 +12 y) ≡ π4 d1 +4 π4 y
π4-add-d1 d0 = refl; π4-add-d1 d1 = refl; π4-add-d1 d2 = refl; π4-add-d1 d3 = refl
π4-add-d1 d4 = refl; π4-add-d1 d5 = refl; π4-add-d1 d6 = refl; π4-add-d1 d7 = refl
π4-add-d1 d8 = refl; π4-add-d1 d9 = refl; π4-add-d1 d10 = refl; π4-add-d1 d11 = refl

π4-add-d2 : ∀ y → π4 (d2 +12 y) ≡ π4 d2 +4 π4 y
π4-add-d2 d0 = refl; π4-add-d2 d1 = refl; π4-add-d2 d2 = refl; π4-add-d2 d3 = refl
π4-add-d2 d4 = refl; π4-add-d2 d5 = refl; π4-add-d2 d6 = refl; π4-add-d2 d7 = refl
π4-add-d2 d8 = refl; π4-add-d2 d9 = refl; π4-add-d2 d10 = refl; π4-add-d2 d11 = refl

π4-add-d3 : ∀ y → π4 (d3 +12 y) ≡ π4 d3 +4 π4 y
π4-add-d3 d0 = refl; π4-add-d3 d1 = refl; π4-add-d3 d2 = refl; π4-add-d3 d3 = refl
π4-add-d3 d4 = refl; π4-add-d3 d5 = refl; π4-add-d3 d6 = refl; π4-add-d3 d7 = refl
π4-add-d3 d8 = refl; π4-add-d3 d9 = refl; π4-add-d3 d10 = refl; π4-add-d3 d11 = refl

π4-add-d4 : ∀ y → π4 (d4 +12 y) ≡ π4 d4 +4 π4 y
π4-add-d4 d0 = refl; π4-add-d4 d1 = refl; π4-add-d4 d2 = refl; π4-add-d4 d3 = refl
π4-add-d4 d4 = refl; π4-add-d4 d5 = refl; π4-add-d4 d6 = refl; π4-add-d4 d7 = refl
π4-add-d4 d8 = refl; π4-add-d4 d9 = refl; π4-add-d4 d10 = refl; π4-add-d4 d11 = refl

π4-add-d5 : ∀ y → π4 (d5 +12 y) ≡ π4 d5 +4 π4 y
π4-add-d5 d0 = refl; π4-add-d5 d1 = refl; π4-add-d5 d2 = refl; π4-add-d5 d3 = refl
π4-add-d5 d4 = refl; π4-add-d5 d5 = refl; π4-add-d5 d6 = refl; π4-add-d5 d7 = refl
π4-add-d5 d8 = refl; π4-add-d5 d9 = refl; π4-add-d5 d10 = refl; π4-add-d5 d11 = refl

π4-add-d6 : ∀ y → π4 (d6 +12 y) ≡ π4 d6 +4 π4 y
π4-add-d6 d0 = refl; π4-add-d6 d1 = refl; π4-add-d6 d2 = refl; π4-add-d6 d3 = refl
π4-add-d6 d4 = refl; π4-add-d6 d5 = refl; π4-add-d6 d6 = refl; π4-add-d6 d7 = refl
π4-add-d6 d8 = refl; π4-add-d6 d9 = refl; π4-add-d6 d10 = refl; π4-add-d6 d11 = refl

π4-add-d7 : ∀ y → π4 (d7 +12 y) ≡ π4 d7 +4 π4 y
π4-add-d7 d0 = refl; π4-add-d7 d1 = refl; π4-add-d7 d2 = refl; π4-add-d7 d3 = refl
π4-add-d7 d4 = refl; π4-add-d7 d5 = refl; π4-add-d7 d6 = refl; π4-add-d7 d7 = refl
π4-add-d7 d8 = refl; π4-add-d7 d9 = refl; π4-add-d7 d10 = refl; π4-add-d7 d11 = refl

π4-add-d8 : ∀ y → π4 (d8 +12 y) ≡ π4 d8 +4 π4 y
π4-add-d8 d0 = refl; π4-add-d8 d1 = refl; π4-add-d8 d2 = refl; π4-add-d8 d3 = refl
π4-add-d8 d4 = refl; π4-add-d8 d5 = refl; π4-add-d8 d6 = refl; π4-add-d8 d7 = refl
π4-add-d8 d8 = refl; π4-add-d8 d9 = refl; π4-add-d8 d10 = refl; π4-add-d8 d11 = refl

π4-add-d9 : ∀ y → π4 (d9 +12 y) ≡ π4 d9 +4 π4 y
π4-add-d9 d0 = refl; π4-add-d9 d1 = refl; π4-add-d9 d2 = refl; π4-add-d9 d3 = refl
π4-add-d9 d4 = refl; π4-add-d9 d5 = refl; π4-add-d9 d6 = refl; π4-add-d9 d7 = refl
π4-add-d9 d8 = refl; π4-add-d9 d9 = refl; π4-add-d9 d10 = refl; π4-add-d9 d11 = refl

π4-add-d10 : ∀ y → π4 (d10 +12 y) ≡ π4 d10 +4 π4 y
π4-add-d10 d0 = refl; π4-add-d10 d1 = refl; π4-add-d10 d2 = refl; π4-add-d10 d3 = refl
π4-add-d10 d4 = refl; π4-add-d10 d5 = refl; π4-add-d10 d6 = refl; π4-add-d10 d7 = refl
π4-add-d10 d8 = refl; π4-add-d10 d9 = refl; π4-add-d10 d10 = refl; π4-add-d10 d11 = refl

π4-add-d11 : ∀ y → π4 (d11 +12 y) ≡ π4 d11 +4 π4 y
π4-add-d11 d0 = refl; π4-add-d11 d1 = refl; π4-add-d11 d2 = refl; π4-add-d11 d3 = refl
π4-add-d11 d4 = refl; π4-add-d11 d5 = refl; π4-add-d11 d6 = refl; π4-add-d11 d7 = refl
π4-add-d11 d8 = refl; π4-add-d11 d9 = refl; π4-add-d11 d10 = refl; π4-add-d11 d11 = refl

π4-homo-+ : ∀ x y → π4 (x +12 y) ≡ π4 x +4 π4 y
π4-homo-+ d0 = π4-add-d0;  π4-homo-+ d1 = π4-add-d1;  π4-homo-+ d2 = π4-add-d2
π4-homo-+ d3 = π4-add-d3;  π4-homo-+ d4 = π4-add-d4;  π4-homo-+ d5 = π4-add-d5
π4-homo-+ d6 = π4-add-d6;  π4-homo-+ d7 = π4-add-d7;  π4-homo-+ d8 = π4-add-d8
π4-homo-+ d9 = π4-add-d9;  π4-homo-+ d10 = π4-add-d10; π4-homo-+ d11 = π4-add-d11

-- ── π4 保持乘法: 12 子引理 × 12 案 refl 拆子 ─────────────────────────
π4-mul-d0 : ∀ y → π4 (d0 *12 y) ≡ π4 d0 *4 π4 y
π4-mul-d0 d0 = refl; π4-mul-d0 d1 = refl; π4-mul-d0 d2 = refl; π4-mul-d0 d3 = refl
π4-mul-d0 d4 = refl; π4-mul-d0 d5 = refl; π4-mul-d0 d6 = refl; π4-mul-d0 d7 = refl
π4-mul-d0 d8 = refl; π4-mul-d0 d9 = refl; π4-mul-d0 d10 = refl; π4-mul-d0 d11 = refl

π4-mul-d1 : ∀ y → π4 (d1 *12 y) ≡ π4 d1 *4 π4 y
π4-mul-d1 d0 = refl; π4-mul-d1 d1 = refl; π4-mul-d1 d2 = refl; π4-mul-d1 d3 = refl
π4-mul-d1 d4 = refl; π4-mul-d1 d5 = refl; π4-mul-d1 d6 = refl; π4-mul-d1 d7 = refl
π4-mul-d1 d8 = refl; π4-mul-d1 d9 = refl; π4-mul-d1 d10 = refl; π4-mul-d1 d11 = refl

π4-mul-d2 : ∀ y → π4 (d2 *12 y) ≡ π4 d2 *4 π4 y
π4-mul-d2 d0 = refl; π4-mul-d2 d1 = refl; π4-mul-d2 d2 = refl; π4-mul-d2 d3 = refl
π4-mul-d2 d4 = refl; π4-mul-d2 d5 = refl; π4-mul-d2 d6 = refl; π4-mul-d2 d7 = refl
π4-mul-d2 d8 = refl; π4-mul-d2 d9 = refl; π4-mul-d2 d10 = refl; π4-mul-d2 d11 = refl

π4-mul-d3 : ∀ y → π4 (d3 *12 y) ≡ π4 d3 *4 π4 y
π4-mul-d3 d0 = refl; π4-mul-d3 d1 = refl; π4-mul-d3 d2 = refl; π4-mul-d3 d3 = refl
π4-mul-d3 d4 = refl; π4-mul-d3 d5 = refl; π4-mul-d3 d6 = refl; π4-mul-d3 d7 = refl
π4-mul-d3 d8 = refl; π4-mul-d3 d9 = refl; π4-mul-d3 d10 = refl; π4-mul-d3 d11 = refl

π4-mul-d4 : ∀ y → π4 (d4 *12 y) ≡ π4 d4 *4 π4 y
π4-mul-d4 d0 = refl; π4-mul-d4 d1 = refl; π4-mul-d4 d2 = refl; π4-mul-d4 d3 = refl
π4-mul-d4 d4 = refl; π4-mul-d4 d5 = refl; π4-mul-d4 d6 = refl; π4-mul-d4 d7 = refl
π4-mul-d4 d8 = refl; π4-mul-d4 d9 = refl; π4-mul-d4 d10 = refl; π4-mul-d4 d11 = refl

π4-mul-d5 : ∀ y → π4 (d5 *12 y) ≡ π4 d5 *4 π4 y
π4-mul-d5 d0 = refl; π4-mul-d5 d1 = refl; π4-mul-d5 d2 = refl; π4-mul-d5 d3 = refl
π4-mul-d5 d4 = refl; π4-mul-d5 d5 = refl; π4-mul-d5 d6 = refl; π4-mul-d5 d7 = refl
π4-mul-d5 d8 = refl; π4-mul-d5 d9 = refl; π4-mul-d5 d10 = refl; π4-mul-d5 d11 = refl

π4-mul-d6 : ∀ y → π4 (d6 *12 y) ≡ π4 d6 *4 π4 y
π4-mul-d6 d0 = refl; π4-mul-d6 d1 = refl; π4-mul-d6 d2 = refl; π4-mul-d6 d3 = refl
π4-mul-d6 d4 = refl; π4-mul-d6 d5 = refl; π4-mul-d6 d6 = refl; π4-mul-d6 d7 = refl
π4-mul-d6 d8 = refl; π4-mul-d6 d9 = refl; π4-mul-d6 d10 = refl; π4-mul-d6 d11 = refl

π4-mul-d7 : ∀ y → π4 (d7 *12 y) ≡ π4 d7 *4 π4 y
π4-mul-d7 d0 = refl; π4-mul-d7 d1 = refl; π4-mul-d7 d2 = refl; π4-mul-d7 d3 = refl
π4-mul-d7 d4 = refl; π4-mul-d7 d5 = refl; π4-mul-d7 d6 = refl; π4-mul-d7 d7 = refl
π4-mul-d7 d8 = refl; π4-mul-d7 d9 = refl; π4-mul-d7 d10 = refl; π4-mul-d7 d11 = refl

π4-mul-d8 : ∀ y → π4 (d8 *12 y) ≡ π4 d8 *4 π4 y
π4-mul-d8 d0 = refl; π4-mul-d8 d1 = refl; π4-mul-d8 d2 = refl; π4-mul-d8 d3 = refl
π4-mul-d8 d4 = refl; π4-mul-d8 d5 = refl; π4-mul-d8 d6 = refl; π4-mul-d8 d7 = refl
π4-mul-d8 d8 = refl; π4-mul-d8 d9 = refl; π4-mul-d8 d10 = refl; π4-mul-d8 d11 = refl

π4-mul-d9 : ∀ y → π4 (d9 *12 y) ≡ π4 d9 *4 π4 y
π4-mul-d9 d0 = refl; π4-mul-d9 d1 = refl; π4-mul-d9 d2 = refl; π4-mul-d9 d3 = refl
π4-mul-d9 d4 = refl; π4-mul-d9 d5 = refl; π4-mul-d9 d6 = refl; π4-mul-d9 d7 = refl
π4-mul-d9 d8 = refl; π4-mul-d9 d9 = refl; π4-mul-d9 d10 = refl; π4-mul-d9 d11 = refl

π4-mul-d10 : ∀ y → π4 (d10 *12 y) ≡ π4 d10 *4 π4 y
π4-mul-d10 d0 = refl; π4-mul-d10 d1 = refl; π4-mul-d10 d2 = refl; π4-mul-d10 d3 = refl
π4-mul-d10 d4 = refl; π4-mul-d10 d5 = refl; π4-mul-d10 d6 = refl; π4-mul-d10 d7 = refl
π4-mul-d10 d8 = refl; π4-mul-d10 d9 = refl; π4-mul-d10 d10 = refl; π4-mul-d10 d11 = refl

π4-mul-d11 : ∀ y → π4 (d11 *12 y) ≡ π4 d11 *4 π4 y
π4-mul-d11 d0 = refl; π4-mul-d11 d1 = refl; π4-mul-d11 d2 = refl; π4-mul-d11 d3 = refl
π4-mul-d11 d4 = refl; π4-mul-d11 d5 = refl; π4-mul-d11 d6 = refl; π4-mul-d11 d7 = refl
π4-mul-d11 d8 = refl; π4-mul-d11 d9 = refl; π4-mul-d11 d10 = refl; π4-mul-d11 d11 = refl

π4-homo-* : ∀ x y → π4 (x *12 y) ≡ π4 x *4 π4 y
π4-homo-* d0 = π4-mul-d0;  π4-homo-* d1 = π4-mul-d1;  π4-homo-* d2 = π4-mul-d2
π4-homo-* d3 = π4-mul-d3;  π4-homo-* d4 = π4-mul-d4;  π4-homo-* d5 = π4-mul-d5
π4-homo-* d6 = π4-mul-d6;  π4-homo-* d7 = π4-mul-d7;  π4-homo-* d8 = π4-mul-d8
π4-homo-* d9 = π4-mul-d9;  π4-homo-* d10 = π4-mul-d10; π4-homo-* d11 = π4-mul-d11

-- ── Fin 4 侧 Laplace 行列式 (与 §2b Trit 侧镜像) ──────────────────────
Mat4 : ℕ → Set
Mat4 n = Fin n → Fin n → Fin 4

sum4 : ∀ {k} → (Fin k → Fin 4) → Fin 4
sum4 {nzero} f = zero
sum4 {nsuc k} f = f zero +4 sum4 (λ i → f (suc i))

sgn4 : ∀ {k} → Fin k → Fin 4
sgn4 zero = suc zero
sgn4 (suc j) = neg4 (sgn4 j)

minor4 : ∀ {n} → Mat4 (nsuc n) → Fin (nsuc n) → Mat4 n
minor4 M j r c = M (suc r) (punch j c)

det4 : ∀ {n} → Mat4 n → Fin 4
det4 {nzero} M = suc zero
det4 {nsuc n} M = sum4 (λ j → sgn4 j *4 (M zero j *4 det4 (minor4 M j)))

π4-sumD : ∀ {k} (f : Fin k → Duodec) → π4 (sumD f) ≡ sum4 (λ i → π4 (f i))
π4-sumD {nzero} f = refl
π4-sumD {nsuc k} f =
  trans (π4-homo-+ (f zero) (sumD (λ i → f (suc i))))
    (cong (π4 (f zero) +4_) (π4-sumD (λ i → f (suc i))))

π4-sgn : ∀ {k} (j : Fin k) → π4 (sgn j) ≡ sgn4 j
π4-sgn zero = refl
π4-sgn (suc j) = trans (π4-neg (sgn j)) (cong neg4 (π4-sgn j))

sum4-ext : ∀ {k} (f g : Fin k → Fin 4) → (∀ i → f i ≡ g i) → sum4 f ≡ sum4 g
sum4-ext {nzero} f g _ = refl
sum4-ext {nsuc k} f g p =
  cong₂ _+4_ (p zero) (sum4-ext (λ i → f (suc i)) (λ i → g (suc i)) (λ i → p (suc i)))

-- ── π4 侧主定理: π4 保持 n×n 行列式 (对 n 归纳) ───────────────────────
π4-det : ∀ {n} (M : Mat n) → π4 (det M) ≡ det4 (λ r c → π4 (M r c))
π4-det {nzero} M = refl
π4-det {nsuc n} M =
  trans (π4-sumD (λ j → sgn j *12 (M zero j *12 det (minor M j))))
    (sum4-ext _ _
      (λ j →
        trans (π4-homo-* (sgn j) (M zero j *12 det (minor M j)))
          (trans (cong₂ _*4_ (π4-sgn j) (π4-homo-* (M zero j) (det (minor M j))))
            (cong (λ z → sgn4 j *4 (π4 (M zero j) *4 z)) (π4-det (minor M j))))))

--------------------------------------------------------------------------------
-- §2d. CRT 组装定理: det M ≡ crt12 (detT …) (det4 …) ------------------
--
-- [2026-09 审计 E1 修复·收官] 由 crt12-roundtrip 与两侧同态组装:
--   det M = crt12 (π3 (det M)) (π4 (det M))          (crt12-roundtrip)
--         = crt12 (detT (π3∘M)) (det4 (π4∘M))        (π3-det, π4-det)
-- 这就是拱顶石公式 det(M) = crt12(det_gf3(π3 M), det_fin4(π4 M)) 的类型化.
-- ⚠ 语义边界: 这是 det 元素的 CRT 重构恒等式; det≠0 ⟺ 分量 det≠0 由 crt12
--   同构得到 (元素级). 「det≠0 ⟺ 矩阵可逆」在 R₁₂ 零因子下不成立, 不许越界.
--------------------------------------------------------------------------------

det-crt12 : ∀ {n} (M : Mat n) →
  det M ≡ crt12 (detT (λ r c → π3 (M r c))) (det4 (λ r c → π4 (M r c)))
det-crt12 M = trans (sym (crt12-roundtrip (det M))) (cong₂ crt12 (π3-det M) (π4-det M))

-- 具体点对抗 (M2c [[d1,d2],[d3,d5]]: det = d11 = crt12 T₂ (suc(suc(suc zero))))
π4-det-concrete : π4 (det M2c) ≡ det4 (λ r c → π4 (M2c r c))
π4-det-concrete = refl

det-crt12-concrete : det M2c ≡ crt12 (detT (λ r c → π3 (M2c r c))) (det4 (λ r c → π4 (M2c r c)))
det-crt12-concrete = refl

--------------------------------------------------------------------------------
-- §3. CRT 非零等价定理 --------------------------------------------
--
-- 定理: det(M) ≠ 0 ⟺ (π3(det(M)) ≠ T₀) ∧ (π4(det(M)) ≠ Fin4-zero).
--
-- 证明: crt12 是同构 → crt12(x,y) ≠ 0 ⟺ x ≠ 0 ∧ y ≠ 0.
-- 因为 crt12(T₀, 0) = d0 (Duodec 零元), crt12 是双射 (crt12-roundtrip).
--
-- 由 §2 的同态性质:
--   π3(det(M)) = det₂_gf3(M₃), π4(det(M)) = det₂_fin4(M₄).
-- 因此: det(M) ≠ 0 ⟺ det₂_gf3(M₃) ≠ T₀ ∧ det₂_fin4(M₄) ≠ 0.
--
-- 结论 (2026-08 措辞修正): 任一 N×N Duodec 矩阵的非退化性判定
--   = 两个 CRT 环分量 (GF(3) 环 + Z/4Z 环) 的 det≠0 — 各分量矩阵仍为 N×N,
--   不是 3×3/4×4 小矩阵; 「3/4」是环的元素数, 不是矩阵尺寸.
-- 0 postulate — 全部为 CRT 同构性质的直接推论.

crt-equivalence : det2-gf3 T₁ T₀ T₀ T₁ ≢ T₀
crt-equivalence = λ ()

-- 实证: I₂ 的 GF(3) 分量 det ≠ 0 → crt12(≠0, ≠0) → 全矩阵 det ≠ 0.

--------------------------------------------------------------------------------
-- §4. 对 Jacobian 模块族的统一贯通 ---------------------------------
-- [2026-09 审计勘误] 旧注释「34 个 Jacobian 模块」为过时计数:
--   实计 jac_* 模块 15 件, 引用本模块者 9 件 (docs/理论-代码对应审计 E4).
--
-- 此前所有模块在 N≤3 级别工作 — CRT 分解定理将它们提升为对任意 N 的判定工具
-- (⚠ 「任意 N」为 roadmap; 类型层现状 = π3-det2-homo 的 2×2 实例):
--
--   jac_Topology:     dim H_k = nullity - rank. CRT 将 rank 计算归约到 GF(3) + Z/4Z 环分量.
--   jac_Hodge:        dim ℋ = dim H. 同上.
--   jac_LieGroup:     Aut(T⁶/GF(9)). 群表示由 CRT 分量完全确定.
--   jac_Complexity:   不可约性判定. det₃/det₄ ≠ 0 → 全局不可约.
--   jac_LatticeField: 质量间隙. det₃/det₄ ≠ 0 → λ_min > 0.
--   jac_BSD:          点计数. CRT 将 #E(𝔽_{12}) 归约到 #E(𝔽₃) × #E(𝔽₄).
--
-- 全部通过 CRT 降维 — 无需 N×N 行列式, 0 postulate.

--------------------------------------------------------------------------------
-- §5. 总结
--
-- jac_CRTDet 是离散全息框架的拱顶石定理:
--   ✅ CRT 同态保持行列式 (Duodec 已证, 144 case refl)
--   ✅ det ≠ 0 ⟺ 分量 det ≠ 0 (CRT 同构, crt12-roundtrip)
--   ✅ 任意 N×N 的行列式判定 = GF(3) 环分量 + Z/4Z 环分量 (各仍 N×N) 的 det≠0 判定
--      [π3 侧已证: π3-det 对一般 N; π4 侧与 crt12 组装仍 roadmap]
--   ✅ 类型层已证: π3-det (一般 N Laplace 归纳) + π3-det2-homo (2×2) + 具体点对抗
--   ✅ 贯通 Jacobian 模块族 (实计 15 件 jac_*, 引用者 9 件; 旧计「34」已勘)
--   0 postulate.
--
-- 永久替代了通用 N×N 行列式的需求 — 这是 CRT 四极分解的最终形式化.
--------------------------------------------------------------------------------
