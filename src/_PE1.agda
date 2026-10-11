{-# OPTIONS --rewriting --guardedness #-}

-- | _PE1 — E1 收官: 一般 N 的 CRT 行列式分解 (组装定理 + 非零等价)
--
-- 数学背景: 拱顶石公式 det(M) = crt12(det(M₃), det(M₄)) 的通用 N 形。
--   E1 实况勘正 (2026-10-11 深审): 两侧同态 **已证** ——
--   π3-det (jac_CRTDet:178, 一般 N Laplace 归纳) + π4-det (jac_CRTDet 尾段, 一般 N)。
--   真缺口只有 **组装定理项** (§2d 注释描述了证明但无项) —— 本件收官。
--
-- 核心原则:
-- 1. 复用优先 (det/detT/det4/π3-det/π4-det 零重证)
-- 2. 语义边界照 §2d: det 元素级 CRT 重构恒等式; det≠0 ⟺ 分量 det≠0 (元素级);
--    「det≠0 ⟺ 可逆」在 R₁₂ 零因子下不成立 —— 不许越界。
-- 3. 双通道核对 (det 直算 vs CRT 分量重构) 防空壳。
--
-- 包含: crt-det-general (组装主定理) / det-zero-split·merge (非零等价) /
--       具体点核对 ×7 (I₂/I₃/m2 双通道)

module _PE1 where

open import Data.Nat using (ℕ)
open import Data.Fin using (Fin; zero; suc)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; cong; cong₂; trans)

open import Sovereign.Base.Trit using (Trit; T₀; T₁; T₂)
open import Sovereign.Algebra.Duodecimal
  using (Duodec; d0; d1; d2; d3; d4; d10; π3; π4; crt12; crt12-roundtrip; crt12-inv-π4)
open import Sovereign.Algebra.Jacobian.jac_CRTDet
  using (Mat; det; detT; det4; det2D; π3-det; π4-det)

--------------------------------------------------------------------------------
-- §0. 基础件: π3 侧 crt 逆 + 零元投影 ------------------------------------------
--------------------------------------------------------------------------------

-- crt12 的 π3 侧逆 (12-case 表; Duodecimal 仅导出 π4 侧)
crt12-inv-π3 : ∀ a b → π3 (crt12 a b) ≡ a
crt12-inv-π3 T₀ zero                    = refl
crt12-inv-π3 T₀ (suc zero)              = refl
crt12-inv-π3 T₀ (suc (suc zero))        = refl
crt12-inv-π3 T₀ (suc (suc (suc zero)))  = refl
crt12-inv-π3 T₁ zero                    = refl
crt12-inv-π3 T₁ (suc zero)              = refl
crt12-inv-π3 T₁ (suc (suc zero))        = refl
crt12-inv-π3 T₁ (suc (suc (suc zero)))  = refl
crt12-inv-π3 T₂ zero                    = refl
crt12-inv-π3 T₂ (suc zero)              = refl
crt12-inv-π3 T₂ (suc (suc zero))        = refl
crt12-inv-π3 T₂ (suc (suc (suc zero)))  = refl

π3-d0 : π3 d0 ≡ T₀
π3-d0 = refl

π4-d0 : π4 d0 ≡ zero
π4-d0 = refl

--------------------------------------------------------------------------------
-- §1. 组装定理 (E1 主件): det M ≡ crt12 (detT (π3∘M)) (det4 (π4∘M)) -------------
--------------------------------------------------------------------------------

crt-det-general : ∀ {n} (M : Mat n) →
  det M ≡ crt12 (detT (λ r c → π3 (M r c))) (det4 (λ r c → π4 (M r c)))
crt-det-general M =
  trans (sym (crt12-roundtrip (det M)))          -- det M ≡ crt12 (π3 (det M)) (π4 (det M))
    (cong₂ crt12 (π3-det M) (π4-det M))          -- 两侧同态搬运到分量 det

--------------------------------------------------------------------------------
-- §2. 非零等价 (元素级; 语义边界见头注) ----------------------------------------
--------------------------------------------------------------------------------

-- crt12 在零点的单射性: crt12 a b ≡ d0 → a ≡ T₀ × b ≡ zero
crt12-inj-zero : ∀ a b → crt12 a b ≡ d0 → (a ≡ T₀) × (b ≡ zero)
crt12-inj-zero a b e =
    trans (sym (crt12-inv-π3 a b)) (trans (cong π3 e) π3-d0)
  , trans (sym (crt12-inv-π4 a b)) (trans (cong π4 e) π4-d0)

det-zero-split : ∀ {n} (M : Mat n) → det M ≡ d0 →
  (detT (λ r c → π3 (M r c)) ≡ T₀) × (det4 (λ r c → π4 (M r c)) ≡ zero)
det-zero-split M e = crt12-inj-zero _ _ (trans (sym (crt-det-general M)) e)

det-zero-merge : ∀ {n} (M : Mat n) →
  (detT (λ r c → π3 (M r c)) ≡ T₀) × (det4 (λ r c → π4 (M r c)) ≡ zero) → det M ≡ d0
det-zero-merge M (p , q) = trans (crt-det-general M) (trans (cong₂ crt12 p q) refl)

-- 推论: 任一分量 det ≠ 0 → 全矩阵 det ≠ 0 (拱顶石公式的判定用法)
det-nonzero-π3 : ∀ {n} (M : Mat n) → detT (λ r c → π3 (M r c)) ≢ T₀ → det M ≢ d0
det-nonzero-π3 M h e = h (proj₁ (det-zero-split M e))

det-nonzero-π4 : ∀ {n} (M : Mat n) → det4 (λ r c → π4 (M r c)) ≢ zero → det M ≢ d0
det-nonzero-π4 M h e = h (proj₂ (det-zero-split M e))

--------------------------------------------------------------------------------
-- §3. 具体点核对 (双通道: det 直算 vs CRT 分量重构) ----------------------------
--------------------------------------------------------------------------------

-- I₂
i2 : Mat 2
i2 zero zero = d1
i2 zero (suc zero) = d0
i2 (suc zero) zero = d0
i2 (suc zero) (suc zero) = d1

check-det-i2 : det i2 ≡ d1
check-det-i2 = refl

check-crt-i2 : crt12 (detT (λ r c → π3 (i2 r c))) (det4 (λ r c → π4 (i2 r c))) ≡ d1
check-crt-i2 = refl

-- 非平凡 2×2: [[1,2],[3,4]] — det = 1·4 ⊖ 2·3 = 10 (mod 12)
m2 : Mat 2
m2 zero zero = d1
m2 zero (suc zero) = d2
m2 (suc zero) zero = d3
m2 (suc zero) (suc zero) = d4

check-det-m2 : det m2 ≡ d10
check-det-m2 = refl

check-det2D-m2 : det2D d1 d2 d3 d4 ≡ d10
check-det2D-m2 = refl

check-agree-m2 : det m2 ≡ det2D d1 d2 d3 d4
check-agree-m2 = trans check-det-m2 (sym check-det2D-m2)

-- CRT 分量面: π3 分量 det = T₁ (GF(3) 上 1·1 ⊖ 2·0)、π4 分量 det = 2 (Z/4 上 1·0 ⊖ 2·3)
check-π3-m2 : detT (λ r c → π3 (m2 r c)) ≡ T₁
check-π3-m2 = refl

check-π4-m2 : det4 (λ r c → π4 (m2 r c)) ≡ suc (suc zero)
check-π4-m2 = refl

-- 3×3 单位阵
i3 : Mat 3
i3 zero zero = d1
i3 zero (suc zero) = d0
i3 zero (suc (suc zero)) = d0
i3 (suc zero) zero = d0
i3 (suc zero) (suc zero) = d1
i3 (suc zero) (suc (suc zero)) = d0
i3 (suc (suc zero)) zero = d0
i3 (suc (suc zero)) (suc zero) = d0
i3 (suc (suc zero)) (suc (suc zero)) = d1

check-det-i3 : det i3 ≡ d1
check-det-i3 = refl

check-crt-i3 : crt12 (detT (λ r c → π3 (i3 r c))) (det4 (λ r c → π4 (i3 r c))) ≡ d1
check-crt-i3 = refl

--------------------------------------------------------------------------------
-- §4. 语义边界 (照 §2d; 不许越界) ----------------------------------------------
-- det M ≡ crt12 … 是 **元素级 CRT 重构恒等式**;
-- det≠0 ⟺ 分量 det≠0 为元素级推论 (crt12 双射);
-- 「det≠0 ⟺ 矩阵可逆」在 R₁₂ 零因子下不成立 (2×6=0) —— 禁止越界声称。
--------------------------------------------------------------------------------
