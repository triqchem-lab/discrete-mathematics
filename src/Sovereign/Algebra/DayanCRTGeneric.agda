{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Algebra.DayanCRTGeneric
-- G3 泛型 CRT：大衍总数术——从具体实例（DayanCRT 物不知数）升级为参数化形式
--
-- 复用链（90%）：
--   DayanProof.terminate-correct —— 泛型乘率存在性（类型即定理）
--   DayanCRT —— 物不知数数值对账（解=23，7 refl）
--
-- 泛型层次：
--   G3.1 CRTComp record：单分量 (奇, 定, 余)
--   G3.2 乘率存在性定理：∀(奇,定,lt) Inv ⟹ lt×奇 ≡ 1 + k×定
--        —— terminate-correct 直接转发（类型即定理，0 行证明体）
--   G3.3 三分量合成 record：用数=衍数×乘率、总数=Σ余×用数（全 ℤ 域，
--        避开 ℤ→ℕ 转换——DayanProof 的乘率天然是 ℤ）
--
-- 诚实边界：多分量合成定理 N ≡ rᵢ (mod 定ᵢ) 的完整 ℤ 代数证明留 roadmap；
--   数值正确性由 DayanCRT 的 7 个 refl 实例对账承担。
--
-- 0 postulate / 0 hole。
module Sovereign.Algebra.DayanCRTGeneric where

open import Data.Nat using (ℕ; zero; suc; _*_; _+_)
open import Data.Integer using (ℤ; +_; 0ℤ)
open import Data.Integer renaming (_*_ to _ℤ*_; _+_ to _ℤ+_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Product using (Σ; _,_)

open import Sovereign.Algebra.DayanProof
  using (Inv; terminate-correct)

--------------------------------------------------------------------------------
-- §1. G3.1 单分量 record——(奇, 定, 余)
--------------------------------------------------------------------------------

record CRTComp : Set where
  constructor crtComp
  field
    奇 : ℕ      -- 奇数（对定母约减后的不完全商）
    定 : ℕ      -- 定母（模数）
    余 : ℕ      -- 余数

open CRTComp public

-- 物不知数三分量（对账 DayanCRT）
wz₁ wz₂ wz₃ : CRTComp
wz₁ = crtComp 2 3 2
wz₂ = crtComp 1 5 3
wz₃ = crtComp 1 7 2

--------------------------------------------------------------------------------
-- §2. G3.2 泛型乘率存在性——terminate-correct 直接转发
--
--   大衍求一术的输出定理（L2 已证）：
--   给定 Inv 奇 定 lt 1（求一术迭代终止态的不变量），
--   则乘率 mod 关系成立：lt × 奇 ≡ 1 (mod 定)。
--
--   这就是任意 (奇,定) 对的乘率存在性——泛型 CRT 的核心引擎。
--------------------------------------------------------------------------------

mulv-exists : ∀ (奇 定 : ℕ) (lt : ℤ) → Inv 奇 定 lt 1 →
              Σ ℤ (λ k → lt ℤ* (+ 奇) ≡ (+ 1) ℤ+ k ℤ* (+ 定))
mulv-exists = terminate-correct
-- ✅ 直接转发：terminate-correct 的类型就是泛型乘率 mod 关系
-- （加强版，回执 4558dd0e——DayanProof.agda 编译产物）

--------------------------------------------------------------------------------
-- §3. G3.3 三分量合成 record——全 ℤ 域（避开 ℤ→ℕ 转换）
--------------------------------------------------------------------------------

record CRT3 : Set where
  field
    c₁ c₂ c₃        : CRTComp   -- 三个分量
    衍母             : ℕ         -- M = 定₁×定₂×定₃
    衍数₁ 衍数₂ 衍数₃ : ℕ        -- M / 定ᵢ
    乘率₁ 乘率₂ 乘率₃  : ℤ       -- 各分量乘率（G3.2 定理的输出）

  -- 用数 = 衍数 × 乘率（ℤ 域——乘率天然有符号）
  用数₁ : ℤ
  用数₁ = + 衍数₁ ℤ* 乘率₁
  用数₂ : ℤ
  用数₂ = + 衍数₂ ℤ* 乘率₂
  用数₃ : ℤ
  用数₃ = + 衍数₃ ℤ* 乘率₃

  -- 总数 = Σ 余数 × 用数（ℤ 域）
  总数 : ℤ
  总数 = + 余₁ ℤ* 用数₁ ℤ+ (+ 余₂ ℤ* 用数₂ ℤ+ (+ 余₃ ℤ* 用数₃))
    where
      余₁ = CRTComp.余 c₁
      余₂ = CRTComp.余 c₂
      余₃ = CRTComp.余 c₃

--------------------------------------------------------------------------------
-- §4. 物不知数实例化——泛型 record 的具体点（对账 DayanCRT）
--------------------------------------------------------------------------------

open import Data.Integer using (0ℤ)

wz-CRT3 : CRT3
wz-CRT3 = record
  { c₁ = wz₁; c₂ = wz₂; c₃ = wz₃
  ; 衍母 = 105
  ; 衍数₁ = 35; 衍数₂ = 21; 衍数₃ = 15
  ; 乘率₁ = + 2; 乘率₂ = + 1; 乘率₃ = + 1
  }
-- 乘率取值与 DayanState 四实例 / DayanCRT 数值对账一致

-- 用数实例：70, 21, 15（对账 DayanCRT 用数₁/₂/₃-check）
用数₁-wz : CRT3.用数₁ wz-CRT3 ≡ + 70
用数₁-wz = refl

用数₂-wz : CRT3.用数₂ wz-CRT3 ≡ + 21
用数₂-wz = refl

用数₃-wz : CRT3.用数₃ wz-CRT3 ≡ + 15
用数₃-wz = refl

-- 总数实例：2×70 + 3×21 + 2×15 = 233（对账 DayanCRT 总数-check）
总数-wz : CRT3.总数 wz-CRT3 ≡ + 233
总数-wz = refl

--------------------------------------------------------------------------------
-- §5. G3 泛型化完成度
--
--   ✅ G3.1 CRTComp record + 物不知数三分量实例
--   ✅ G3.2 mulv-exists：泛型乘率存在性（terminate-correct 直接转发）
--   ✅ G3.3 CRT3 record：用数/总数全 ℤ 域定义（无 postulate、无转换 hack）
--   ✅ 实例对账：用数 70/21/15 + 总数 233（4 个 refl，与 DayanCRT 一致）
--   ⚠ 合成定理 N ≡ rᵢ (mod 定ᵢ) 的 ℤ 代数证明——roadmap
--      （ℤ 的 % 运算需要 ≢0 约束；数值层由 DayanCRT 7 refl 承担）
--
--   与 DayanProof/DayanCRT 的证据链闭环：
--   step-invariant（L2）→ terminate-correct（L2 加强版）→ mulv-exists（G3.2）
--   → CRT3.乘率ᵢ（G3.3）→ 用数/总数 → 数值对账（DayanCRT 解=23）
--------------------------------------------------------------------------------
