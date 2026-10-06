{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Algebra.CRTDetGeneral
-- P0-2：一般 N 的 CRT 行列式分解定理
--
-- 任务书 3.1：McClellan 精确线性系统求解
--   核心主张：det M = crt12 (π3-det M) (π4-det M)
--   即 Duodec 上的行列式 = CRT 重构（GF(3) 分量 × Z/4Z 分量）
--
-- 证明路线（3 步 trans）：
--   ① crt12-roundtrip: crt12 (π3 x) (π4 x) ≡ x
--   ② π3-det: π3 (det M) ≡ detT (π3-M M)
--   ③ π4-det: π4 (det M) ≡ detT4 (π4-M M)
--   ⟹ det M ≡ crt12 (detT (π3-M M)) (detT4 (π4-M M))
--
-- 0 postulate / 0 hole。
module Sovereign.Algebra.CRTDetGeneral where

open import Data.Nat using (ℕ) renaming (zero to nzero; suc to nsuc)
open import Data.Fin using (Fin)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; trans; cong₂; sym)

open import Sovereign.Base.Trit using (Trit)
open import Sovereign.Algebra.Duodecimal
  using (Duodec; π3; π4; crt12; crt12-roundtrip)
open import Sovereign.Algebra.Jacobian.jac_CRTDet
  using (Mat; det; MatT; detT; π3-det)
open import Sovereign.Algebra.Jacobian.jac_CRTDet4
  using (detT4; π4-det)

-- π3 侧构造函数（构造 MatT = Fin n → Fin n → Trit）
π3-M : ∀ {n} → Mat n → MatT n
π3-M M r c = π3 (M r c)

-- π4 侧构造函数（构造函数矩阵 → Fin 4 矩阵）
π4-M : ∀ {n} → Mat n → (Fin n → Fin n → Fin 4)
π4-M M r c = π4 (M r c)

--------------------------------------------------------------------------------
-- §1. 一般 N CRT 行列式分解定理
--
--   证明：3 步 trans 链
--   ① crt12-roundtrip (det M) : crt12 (π3-det M) (π4-det M) ≡ det M
--   ② cong₂ crt12 (π3-det M) (π4-det M) : crt12 (π3-det) (π4-det) ≡ crt12 detT detT4
--   ③ 反向组合：det M ≡ crt12 detT detT4
--------------------------------------------------------------------------------

crt-det-general : ∀ {n} (M : Mat n) →
  det M ≡ crt12 (detT (π3-M M)) (detT4 (π4-M M))
crt-det-general {n} M =
  trans (sym (crt12-roundtrip (det M)))
        (cong₂ crt12 (π3-det M) (π4-det M))
-- crt12 (π3-det M) (π4-det M) ≡ det M  [roundtrip]
-- ⟹ det M ≡ crt12 (detT (π3-M M)) (detT4 (π4-M M))  [cong₂ + π3-det + π4-det]

--------------------------------------------------------------------------------
-- §2. det ≠ 0 ⟺ CRT 分量非零
--
--   由 crt12 是双射（crt12-roundtrip）+ 枚举：
--   crt12 x y ≡ d0 ⟺ x ≡ T₀ ∧ y ≡ 0  （12 case 枚举）
--   ⟹ det M ≠ 0 ⟺ π3(det M) ≠ T₀ ∧ π4(det M) ≠ 0
--
--   形式化：∁(det ≠ d0) ⟺ ∁(π3-det ≠ T₀) ∧ ∁(π4-det ≠ 0)
--   即 det = d0 ⟺ π3-det = T₀ ∧ π4-det = 0
--------------------------------------------------------------------------------

-- CRT 零点判据 roadmap：
--   crt12 x y ≡ d0 ⟺ x ≡ T₀ ∧ y ≡ 0（12 case 枚举太长，留 roadmap）
--   2×2 实例已证：crt-det-nonzero = λ ()
--   一般 N 版：det = d0 ⟺ π3(det) = T₀ ∧ π4(det) = 0（依赖上方零点判据）

--------------------------------------------------------------------------------
-- §3. P0-2 完成度
--
--   ✅ crt-det-general：一般 N 的 CRT 行列式分解（3 步 trans 链）
--   ✅ π3-M / π4-M 构造函数
--   ⚠ crt12-zero：CRT 零点判据（12 case 枚举——roadmap）
--   ⚠ det ≠ 0 ⟺ CRT 分量非零（完整版——roadmap）
--
--   核心贡献：一般 N 的 CRT 行列式分解已从注释级升级为类型级定理。
--   CRT 零点判据（det ≠ 0 ⟺ 分量非零）留 12 case 枚举 roadmap。
--   
--   路径 A（已选）：先闭合 det M ≡ crt12(π3-det, π4-det) 的分解定理
--   路径 B（备选）：直接做 12 case 枚举的 CRT 零点判据（更长但更完整）
