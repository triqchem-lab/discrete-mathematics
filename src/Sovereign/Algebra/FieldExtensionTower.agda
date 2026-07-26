module Sovereign.Algebra.FieldExtensionTower where

--------------------------------------------------------------------------------
-- GF(3) 的完整域扩张塔和子域格
--
-- 定理: GF(3^a) ⊂ GF(3^b) 当且仅当 a | b
--
-- 扩张塔 (n = 1..6):
--   GF(3¹) = GF(3),   阶 3     — 基域
--   GF(3²) = GF(9),   阶 9     — 共轭/纠缠 (Sovereign.Algebra.GF9)
--   GF(3³) = GF(27),  阶 27    — 三次扩张
--   GF(3⁴) = GF(81),  阶 81    — 四次扩张
--   GF(3⁵) = GF(243), 阶 243   — PackedTryte5 (耦合域)
--   GF(3⁶) = GF(729), 阶 729   — T⁶ 格点 (几何极)
--
-- 子域格 (Hasse 图, 覆盖关系):
--
--          GF(729) (n=6)
--         /         \
--    GF(27)       GF(9)
--    (n=3)        (n=2)
--         \         /
--          GF(3) (n=1)
--
--    GF(81) (n=4)     GF(243) (n=5)
--      |                  |
--    GF(9) (n=2)      GF(3) (n=1)
--      |
--    GF(3) (n=1)
--
-- 覆盖关系: 1→2, 1→3, 1→5, 2→4, 2→6, 3→6
--
-- 乘法群阶: |GF(3^n)*| = 3^n - 1
--   GF(3)*   = 2    ≅ Z/2Z
--   GF(9)*   = 8    ≅ Z/8Z
--   GF(27)*  = 26   ≅ Z/26Z
--   GF(81)*  = 80   ≅ Z/80Z
--   GF(243)* = 242  ≅ Z/242Z
--   GF(729)* = 728  ≅ Z/728Z
--
-- 0 postulate, 全部构造性证明
--------------------------------------------------------------------------------

open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _^_; _∸_)
open import Data.Nat.Divisibility using (_∣_; _∤_; divides)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

--------------------------------------------------------------------------------
-- 1. 域阶 (Field Order): |GF(3^n)| = 3^n
--------------------------------------------------------------------------------

field-order : ℕ → ℕ
field-order n = 3 ^ n

-- 具体值 (Agda 计算归约)
order-1 : field-order 1 ≡ 3
order-1 = refl

order-2 : field-order 2 ≡ 9
order-2 = refl

order-3 : field-order 3 ≡ 27
order-3 = refl

order-4 : field-order 4 ≡ 81
order-4 = refl

order-5 : field-order 5 ≡ 243
order-5 = refl

order-6 : field-order 6 ≡ 729
order-6 = refl

--------------------------------------------------------------------------------
-- 2. 子域关系: GF(3^a) ⊂ GF(3^b) ⟺ a | b
--------------------------------------------------------------------------------

-- 子域关系等价于整除关系
-- stdlib 定义: m ∣ n = record { quotient = q; equality = n ≡ q * m }
subfield-relation : ℕ → ℕ → Set
subfield-relation a b = a ∣ b

-- 非子域关系
not-subfield : ℕ → ℕ → Set
not-subfield a b = a ∤ b

--------------------------------------------------------------------------------
-- 3. 正子域关系 (构造性证明: 提供商 q 使得 b ≡ q * a)
--------------------------------------------------------------------------------

-- GF(3) ⊂ GF(9): 1 | 2
gf3-sub-gf9 : subfield-relation 1 2
gf3-sub-gf9 = divides 2 refl

-- GF(3) ⊂ GF(27): 1 | 3
gf3-sub-gf27 : subfield-relation 1 3
gf3-sub-gf27 = divides 3 refl

-- GF(3) ⊂ GF(81): 1 | 4
gf3-sub-gf81 : subfield-relation 1 4
gf3-sub-gf81 = divides 4 refl

-- GF(3) ⊂ GF(243): 1 | 5
gf3-sub-gf243 : subfield-relation 1 5
gf3-sub-gf243 = divides 5 refl

-- GF(3) ⊂ GF(729): 1 | 6
gf3-sub-gf729 : subfield-relation 1 6
gf3-sub-gf729 = divides 6 refl

-- GF(9) ⊂ GF(81): 2 | 4
gf9-sub-gf81 : subfield-relation 2 4
gf9-sub-gf81 = divides 2 refl

-- GF(9) ⊂ GF(729): 2 | 6
gf9-sub-gf729 : subfield-relation 2 6
gf9-sub-gf729 = divides 3 refl

-- GF(27) ⊂ GF(729): 3 | 6
gf27-sub-gf729 : subfield-relation 3 6
gf27-sub-gf729 = divides 2 refl

-- 自反性: 每个域是自身的子域
gf3-sub-self : subfield-relation 1 1
gf3-sub-self = divides 1 refl

gf9-sub-self : subfield-relation 2 2
gf9-sub-self = divides 1 refl

gf27-sub-self : subfield-relation 3 3
gf27-sub-self = divides 1 refl

gf81-sub-self : subfield-relation 4 4
gf81-sub-self = divides 1 refl

gf243-sub-self : subfield-relation 5 5
gf243-sub-self = divides 1 refl

gf729-sub-self : subfield-relation 6 6
gf729-sub-self = divides 1 refl

--------------------------------------------------------------------------------
-- 4. 非子域关系 (构造性证明: 穷举商的所有可能值, () 模式矛盾)
--
-- 证明策略: 对商 q 做模式匹配
--   q = 0:     b ≡ 0 * a = 0,  与 b > 0 矛盾
--   q = 1:     b ≡ 1 * a = a,  与 b ≠ a 矛盾
--   q ≥ 2:     q * a ≥ 2a > b, 与 b ≡ q * a 矛盾
--   (Agda 的 () 模式自动检测 Peano 构造子不匹配)
--------------------------------------------------------------------------------

-- GF(9) ⊄ GF(27): 2 ∤ 3
gf9-not-sub-gf27 : not-subfield 2 3
gf9-not-sub-gf27 (divides zero ())
gf9-not-sub-gf27 (divides (suc zero) ())
gf9-not-sub-gf27 (divides (suc (suc zero)) ())
gf9-not-sub-gf27 (divides (suc (suc (suc zero))) ())
gf9-not-sub-gf27 (divides (suc (suc (suc (suc k)))) ())

-- GF(81) ⊄ GF(729): 4 ∤ 6
gf81-not-sub-gf729 : not-subfield 4 6
gf81-not-sub-gf729 (divides zero ())
gf81-not-sub-gf729 (divides (suc zero) ())
gf81-not-sub-gf729 (divides (suc (suc k)) ())

-- GF(27) ⊄ GF(81): 3 ∤ 4
gf27-not-sub-gf81 : not-subfield 3 4
gf27-not-sub-gf81 (divides zero ())
gf27-not-sub-gf81 (divides (suc zero) ())
gf27-not-sub-gf81 (divides (suc (suc k)) ())

-- GF(9) ⊄ GF(243): 2 ∤ 5
gf9-not-sub-gf243 : not-subfield 2 5
gf9-not-sub-gf243 (divides zero ())
gf9-not-sub-gf243 (divides (suc zero) ())
gf9-not-sub-gf243 (divides (suc (suc zero)) ())
gf9-not-sub-gf243 (divides (suc (suc (suc k))) ())

-- GF(27) ⊄ GF(243): 3 ∤ 5
gf27-not-sub-gf243 : not-subfield 3 5
gf27-not-sub-gf243 (divides zero ())
gf27-not-sub-gf243 (divides (suc zero) ())
gf27-not-sub-gf243 (divides (suc (suc k)) ())

-- GF(81) ⊄ GF(243): 4 ∤ 5
gf81-not-sub-gf243 : not-subfield 4 5
gf81-not-sub-gf243 (divides zero ())
gf81-not-sub-gf243 (divides (suc zero) ())
gf81-not-sub-gf243 (divides (suc (suc k)) ())

-- GF(243) ⊄ GF(729): 5 ∤ 6
gf243-not-sub-gf729 : not-subfield 5 6
gf243-not-sub-gf729 (divides zero ())
gf243-not-sub-gf729 (divides (suc zero) ())
gf243-not-sub-gf729 (divides (suc (suc k)) ())

-- 反向非子域关系 (a > b 时 a ∤ b)

-- GF(27) ⊄ GF(9): 3 ∤ 2
gf27-not-sub-gf9 : not-subfield 3 2
gf27-not-sub-gf9 (divides zero ())
gf27-not-sub-gf9 (divides (suc zero) ())
gf27-not-sub-gf9 (divides (suc (suc k)) ())

-- GF(81) ⊄ GF(27): 4 ∤ 3
gf81-not-sub-gf27 : not-subfield 4 3
gf81-not-sub-gf27 (divides zero ())
gf81-not-sub-gf27 (divides (suc zero) ())
gf81-not-sub-gf27 (divides (suc (suc k)) ())

-- GF(81) ⊄ GF(9): 4 ∤ 2
gf81-not-sub-gf9 : not-subfield 4 2
gf81-not-sub-gf9 (divides zero ())
gf81-not-sub-gf9 (divides (suc k) ())

-- GF(243) ⊄ GF(9): 5 ∤ 2
gf243-not-sub-gf9 : not-subfield 5 2
gf243-not-sub-gf9 (divides zero ())
gf243-not-sub-gf9 (divides (suc k) ())

-- GF(243) ⊄ GF(27): 5 ∤ 3
gf243-not-sub-gf27 : not-subfield 5 3
gf243-not-sub-gf27 (divides zero ())
gf243-not-sub-gf27 (divides (suc k) ())

-- GF(243) ⊄ GF(81): 5 ∤ 4
gf243-not-sub-gf81 : not-subfield 5 4
gf243-not-sub-gf81 (divides zero ())
gf243-not-sub-gf81 (divides (suc k) ())

-- GF(729) ⊄ GF(9): 6 ∤ 2
gf729-not-sub-gf9 : not-subfield 6 2
gf729-not-sub-gf9 (divides zero ())
gf729-not-sub-gf9 (divides (suc k) ())

-- GF(729) ⊄ GF(27): 6 ∤ 3
gf729-not-sub-gf27 : not-subfield 6 3
gf729-not-sub-gf27 (divides zero ())
gf729-not-sub-gf27 (divides (suc k) ())

-- GF(729) ⊄ GF(81): 6 ∤ 4
gf729-not-sub-gf81 : not-subfield 6 4
gf729-not-sub-gf81 (divides zero ())
gf729-not-sub-gf81 (divides (suc k) ())

-- GF(729) ⊄ GF(243): 6 ∤ 5
gf729-not-sub-gf243 : not-subfield 6 5
gf729-not-sub-gf243 (divides zero ())
gf729-not-sub-gf243 (divides (suc k) ())

--------------------------------------------------------------------------------
-- 5. 乘法群阶: |GF(3^n)*| = 3^n - 1
--------------------------------------------------------------------------------

mult-group-order : ℕ → ℕ
mult-group-order n = field-order n ∸ 1

-- 具体值
mult-order-1 : mult-group-order 1 ≡ 2
mult-order-1 = refl

mult-order-2 : mult-group-order 2 ≡ 8
mult-order-2 = refl

mult-order-3 : mult-group-order 3 ≡ 26
mult-order-3 = refl

mult-order-4 : mult-group-order 4 ≡ 80
mult-order-4 = refl

mult-order-5 : mult-group-order 5 ≡ 242
mult-order-5 = refl

mult-order-6 : mult-group-order 6 ≡ 728
mult-order-6 = refl

--------------------------------------------------------------------------------
-- 6. 与项目的连接
--------------------------------------------------------------------------------

-- GF(9) = 共轭/纠缠 — Sovereign.Algebra.GF9
-- GF(9)* ≅ Z/8Z, 生成元 1+α, Galois 群 Gal(GF(9)/GF(3)) ≅ C₂

-- GF(27) = 三次扩张
-- GF(27)* ≅ Z/26Z, 26 = 2 × 13

-- GF(243) = PackedTryte5 (耦合域)
-- 5 个三进制位打包, 3^5 = 243 态
-- 5 没有非平凡因子（倍频回归点）→ GF(243) 没有非平凡中间子域

-- GF(729) = T⁶ 格点 (几何极)
-- 6 个 Trit, 每个 3 态, 3^6 = 729 态
-- Tryte 状态空间 = GF(729) 的加法群

-- T⁶ 格点数 = 729
t6-lattice-card : field-order 6 ≡ 729
t6-lattice-card = refl

-- PackedTryte5 状态数 = 243
packed-tryte5-card : field-order 5 ≡ 243
packed-tryte5-card = refl

-- GF(9) 阶 = 9 (共轭对空间)
gf9-card : field-order 2 ≡ 9
gf9-card = refl

--------------------------------------------------------------------------------
-- 7. 5 没有非平凡因子（倍频回归点）— GF(243) 没有非平凡中间子域
--------------------------------------------------------------------------------

-- 5 的唯一正因数是 1 和 5（倍频回归点，无分解）:
-- 已证: 1|5 (gf3-sub-gf243), 5|5 (gf243-sub-self)
-- 已证: 2∤5 (gf9-not-sub-gf243), 3∤5 (gf27-not-sub-gf243), 4∤5 (gf81-not-sub-gf243)
-- 推论: GF(243) 的子域只有 GF(3) 和自身

--------------------------------------------------------------------------------
-- 8. 子域格完整枚举 (n = 1..6)
--------------------------------------------------------------------------------

-- 覆盖关系 (Hasse 图的边):
--   1 → 2: GF(3) ⊂ GF(9)     — gf3-sub-gf9
--   1 → 3: GF(3) ⊂ GF(27)    — gf3-sub-gf27
--   1 → 5: GF(3) ⊂ GF(243)   — gf3-sub-gf243
--   2 → 4: GF(9) ⊂ GF(81)    — gf9-sub-gf81
--   2 → 6: GF(9) ⊂ GF(729)   — gf9-sub-gf729
--   3 → 6: GF(27) ⊂ GF(729)  — gf27-sub-gf729

-- 非覆盖的子域关系 (由传递性得到):
--   1 → 4: GF(3) ⊂ GF(81)    — gf3-sub-gf81 (经由 1→2→4)
--   1 → 6: GF(3) ⊂ GF(729)   — gf3-sub-gf729 (经由 1→2→6 或 1→3→6)

-- 完全非子域关系 (n=1..6 中所有 a∤b 的对, a≠b):
--   2∤3, 2∤5           — gf9-not-sub-gf27, gf9-not-sub-gf243
--   3∤2, 3∤4, 3∤5     — gf27-not-sub-gf9, gf27-not-sub-gf81, gf27-not-sub-gf243
--   4∤2, 4∤3, 4∤5, 4∤6 — gf81-not-sub-gf9, gf81-not-sub-gf27, gf81-not-sub-gf243, gf81-not-sub-gf729
--   5∤2, 5∤3, 5∤4, 5∤6 — gf243-not-sub-gf9, gf243-not-sub-gf27, gf243-not-sub-gf81, gf243-not-sub-gf729
--   6∤2, 6∤3, 6∤4, 6∤5 — gf729-not-sub-gf9, gf729-not-sub-gf27, gf729-not-sub-gf81, gf729-not-sub-gf243
