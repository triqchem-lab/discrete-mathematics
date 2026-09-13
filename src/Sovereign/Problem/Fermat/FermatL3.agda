{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Problem.Fermat.FermatL3
-- 费马大定理的离散基座 — L3 GF(9)× 周期层
--
-- 数学背景 (13-flt-analysis.md 验证 2):
--   GF(9)× ≅ C₈ (|GF(9)×| = 9−1 = 8): 每个单位 x 满足 x⁸ = 1.
--   故指数 n 的信息只通过 n mod 8 被感知 (相位轴周期).
--   φ = 1+2α 是 8 阶本原元 (GF9.agda phi-to-8: φ⁸=1; phi-not-order-4: φ⁴≠1).
--
--   联合 L1 (GF(3)× 周期 2) 得幂的律全貌:
--     ⊕ 轴周期 2 (GF(3)×) × ⊗ 轴周期 8 (GF(9)×) → 联合 12 = LCM(3,4) 进制
--   十二进制裁决: 指数维度在离散基座上坍缩为 (奇偶, mod 8) —
--   不足以区分 n = 2 与 n ≥ 3, 那个区分在 Archimedes 序 (连续统) 中.
--
-- 本层主定理 (全部 0 postulate):
--   gf9-pow8        : ∀ x → x ≢ 0 → x⁸ = 1        (C₈ 周期, 9 case 穷举)
--   phi-3-11/11-19  : φ³ = φ¹¹ = φ¹⁹              (mod 8 平移不变实例,
--                                                  φ 阶恰 8, 非平凡)
--   c8-summary      : C₈ 周期汇总 (§2 × §3 × §4 打包, 本层主定理单一入口)
--
-- 依赖: GF9 (gf9-pow, phi, alpha), FermatL0 (幂定义层)

module Sovereign.Problem.Fermat.FermatL3 where

open import Data.Product using (_×_; _,_)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Sovereign.Base.Trit using (Trit; T₀; T₁; T₂)
open import Sovereign.Algebra.GF9 using
  (GF9; gf9-zero; gf9-one; gf9-pow; phi; alpha)

--------------------------------------------------------------------------------
-- §1. GF(9) 上的不等号 (局部, 同 ≢₃ 惯例)
--------------------------------------------------------------------------------

_≢₉_ : GF9 → GF9 → Set
x ≢₉ y = x ≡ y → ⊥

--------------------------------------------------------------------------------
-- §2. C₈ 周期主定理: 每个单位 x 满足 x⁸ = 1
--------------------------------------------------------------------------------

-- 9 case 穷举 (8 非零元素 + 零占位).
-- GF(9)× 的 8 个元素: 1, 2, α, 2α, 1+α, 1+2α, 2+α, 2+2α — 全部 x⁸ = 1.
gf9-pow8 : ∀ x → x ≢₉ gf9-zero → gf9-pow x 8 ≡ gf9-one
gf9-pow8 (T₀ , T₀) neq = ⊥-elim (neq refl)   -- 零被排除
gf9-pow8 (T₁ , T₀) _   = refl                -- 1⁸ = 1
gf9-pow8 (T₂ , T₀) _   = refl                -- 2⁸ = 1 (2 的阶 2)
gf9-pow8 (T₀ , T₁) _   = refl                -- α⁸ = 1 (α 的阶 4 | 8)
gf9-pow8 (T₀ , T₂) _   = refl                -- (2α)⁸ = 1
gf9-pow8 (T₁ , T₁) _   = refl                -- (1+α)⁸ = 1 (本原元, 阶 8)
gf9-pow8 (T₁ , T₂) _   = refl                -- φ = 1+2α, 阶 8
gf9-pow8 (T₂ , T₁) _   = refl                -- (2+α)⁸ = 1
gf9-pow8 (T₂ , T₂) _   = refl                -- (2+2α)⁸ = 1

--------------------------------------------------------------------------------
-- §3. mod 8 平移不变实例: φ³ = φ¹¹ = φ¹⁹
--
-- φ = 1+2α 的阶恰为 8 (GF9.agda: phi-to-8 φ⁸=1, phi-not-order-4 φ⁴≠1),
-- 故 φ³ = φ¹¹ 非平凡 (不能由更小周期推出): 3 ≡ 11 ≡ 19 (mod 8).
-- 对照 13-flt-analysis.md §4.2 python 核验 (2026-09-05):
--   生成元 a: a³ = a¹¹ = a¹⁹  (n 只通过 mod 8 被感知)
--------------------------------------------------------------------------------

phi-3-11 : gf9-pow phi 3 ≡ gf9-pow phi 11
phi-3-11 = refl   -- 归约: φ³ = φ¹¹ = (T₀, T₁) 即 α 分量 (2α 的像, 逐项核对)

phi-11-19 : gf9-pow phi 11 ≡ gf9-pow phi 19
phi-11-19 = refl   -- 归约: φ¹¹ = φ¹⁹ = 同上

-- α 同像实例 (α 阶 4, 8 平移亦不变): α³ = α¹¹
alpha-3-11 : gf9-pow alpha 3 ≡ gf9-pow alpha 11
alpha-3-11 = refl

--------------------------------------------------------------------------------
-- §4. C₈ 周期汇总 (本层主定理)
--------------------------------------------------------------------------------

-- 8 阶本原元实例: φ = 1+2α 满足 φ⁸ = 1 (C₈ 的生成元证据之一;
-- 阶恰为 8 的完整证明在 GF9.agda: phi-to-8 φ⁸=1, phi-not-order-4 φ⁴≠1)
phi-pow8 : gf9-pow phi 8 ≡ gf9-one
phi-pow8 = refl

-- C₈ 周期语义 (已证内容汇总, 对应 13-flt-analysis.md 定理 D):
--   ∀ x → x ≢ 0 → gf9-pow x 8 ≡ gf9-one      = gf9-pow8 (§2)
--   生成元 φ: φ⁸ = 1, φ⁴ ≠ 1 (GF9.agda 引用) = phi-pow8 + phi-not-order-4
--   mod 8 平移不变: φ³ = φ¹¹ = φ¹⁹           = phi-3-11/phi-11-19 (§3)

-- 汇总: 幂的律全貌 (L1 × L3) —— 本层主定理的单一入口
--   GF(3)×: x^(2k) = 1,  x^(2k+1) = x       (周期 2, 奇偶坍缩; 见 FermatL1)
--   GF(9)×: x⁸ = 1 ∀ x ≠ 0                  (周期 8, C₈)
--   生成元 φ 阶恰 8: φ⁸ = 1 且 φ⁴ ≠ 1 (后者见 GF9.agda phi-not-order-4)
--   mod 8 平移不变: φ³ = φ¹¹ = φ¹⁹
--   联合 12 = LCM(3,4) 进制: 指数维度在此坐标系中无 Archimedes 序内容
--   裁决引用: docs/duodecimal/13-flt-analysis.md §8.3
--
-- 注 (2026-09-10): 此处原是被 {- -} 注释掉的「汇总」文本 —— 头注释承诺了 c8-summary
-- 而文件里只有注释块, 从未成为定义（由 engineering/tests/doc_code_drift.py 扫出）。
-- 现按项目惯例（对照 LCMVortexConnection.lcm-summary / CommAlgBridge.*-summary）
-- 落成真定义；元组用显式括号, 因为 _,_ 无 fixity 声明（默认非结合）。
c8-summary :
    (∀ x → x ≢₉ gf9-zero → gf9-pow x 8 ≡ gf9-one)   -- C₈ 周期 (§2)
  × (gf9-pow phi 8 ≡ gf9-one)                        -- 生成元 φ 的 8 阶证据 (§4)
  × (gf9-pow phi 3 ≡ gf9-pow phi 11)                 -- mod 8 平移不变 (§3)
  × (gf9-pow phi 11 ≡ gf9-pow phi 19)                -- mod 8 平移不变 (§3)
c8-summary = gf9-pow8 , (phi-pow8 , (phi-3-11 , phi-11-19))
