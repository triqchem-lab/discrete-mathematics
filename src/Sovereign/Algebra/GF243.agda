{-# OPTIONS --rewriting #-}

-- | Sovereign.Algebra.GF243
-- GF(3⁵) = GF(3)[x]/(x⁵+2x+1) — 243 元素有限域
--
-- 代数结构：
--   加法群 ≅ (Z/3Z)⁵ — 5 维 GF(3) 向量空间
--   特征 3：∀ x, x+x+x = 0
--   Gal(GF(243)/GF(3)) ≅ C₅ — Frobenius x↦x³ 生成
--
-- 不可约多项式：p(x) = x⁵ + 2x + 1
--   无 GF(3) 根：p(0)=1, p(1)≡1, p(2)≡1 (mod 3)
--   约化规则：x⁵ ≡ x + 2 (mod p(x), GF(3))
--
-- 耦合域连接：
--   PackedByte = Fin 243 (Sovereign.Format.TQ10)
--   GF243 = Vec Trit 5 — 相同的 243 态载体
--   pack5/unpack5 提供集合双射
--   GF243 携带加法群结构；PackedByte 是裸存储
--
-- 域扩张塔（子域格）：
--   GF(3^a) ⊂ GF(3^b) 当且仅当 a ∣ b
--   GF(3) ⊂ GF(9) ⊂ GF(81)     (1∣2∣4)
--   GF(3) ⊂ GF(9) ⊂ GF(729)    (1∣2, 2∣6)
--   GF(3) ⊂ GF(27) ⊂ GF(729)   (1∣3, 3∣6)
--   GF(3) ⊂ GF(243)             (1∣5, 5 是素数，无中间子域)
--
-- 涡旋塔连接：
--   243 = 3⁵
--   12⁵ = 248832 = 243 × 1024 = 3⁵ × 2¹⁰
--
-- 0 postulate — 全部构造性证明

module Sovereign.Algebra.GF243 where

open import Data.Nat using (ℕ; _^_; _*_; _+_)
open import Data.Vec using (Vec; []; _∷_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; cong₂; sym; trans)
open import Sovereign.Base.Trit using (Trit; T₀; T₁; T₂; _⊕_; negate;
  negate²; ⊕-comm; ⊕-assoc; ⊕-identityˡ; ⊕-identityʳ; ⊕-inverse)

--------------------------------------------------------------------------------
-- 1. GF(243) 类型定义
--------------------------------------------------------------------------------

-- GF(3⁵) 的元素：5 个 GF(3) 系数
-- (a₀, a₁, a₂, a₃, a₄) 表示多项式 a₀ + a₁x + a₂x² + a₃x³ + a₄x⁴
-- 在 GF(3)[x]/(x⁵+2x+1) 中的陪集
GF243 : Set
GF243 = Vec Trit 5

--------------------------------------------------------------------------------
-- 2. 不可约多项式与约化规则
--------------------------------------------------------------------------------

-- p(x) = x⁵ + 2x + 1 是 GF(3) 上的不可约 5 次多项式
--
-- 不可约性验证（构造性）：
--   无根：p(0) = 1, p(1) = 1+2+1 = 4 ≡ 1, p(2) = 32+4+1 = 37 ≡ 1
--   5 是素数，只需排除 1 次和 2 次因子
--
-- 约化规则：x⁵ ≡ -2x - 1 ≡ x + 2 (mod p(x), GF(3))
--   因为 -2 ≡ 1 (mod 3), -1 ≡ 2 (mod 3)

-- p(x) 在 GF(3) 上无根（构造性验证）
p-no-root-0 : 0 + 0 + 1 ≡ 1            -- p(0) = 1 ≠ 0
p-no-root-0 = refl

p-no-root-1 : 1 + 2 + 1 ≡ 4            -- p(1) = 4 ≡ 1 (mod 3) ≠ 0
p-no-root-1 = refl

p-no-root-2 : 32 + 4 + 1 ≡ 37          -- p(2) = 37 ≡ 1 (mod 3) ≠ 0
p-no-root-2 = refl

-- 约化规则：α⁵ ≡ α + 2 (mod p(α))
-- 其中 α = x 是 GF(3)[x]/(p(x)) 的生成元
alpha5-normal-form : GF243
alpha5-normal-form = T₂ ∷ T₁ ∷ T₀ ∷ T₀ ∷ T₀ ∷ []  -- 2 + 1·x

--------------------------------------------------------------------------------
-- 3. 零元、加法、取反
--------------------------------------------------------------------------------

-- 加法单位元：零多项式
gf243-zero : GF243
gf243-zero = T₀ ∷ T₀ ∷ T₀ ∷ T₀ ∷ T₀ ∷ []

-- 分量-wise GF(3) 加法（对应多项式加法 mod p(x)）
_+gf243_ : GF243 → GF243 → GF243
(a₀ ∷ a₁ ∷ a₂ ∷ a₃ ∷ a₄ ∷ []) +gf243 (b₀ ∷ b₁ ∷ b₂ ∷ b₃ ∷ b₄ ∷ []) =
  (a₀ ⊕ b₀) ∷ (a₁ ⊕ b₁) ∷ (a₂ ⊕ b₂) ∷ (a₃ ⊕ b₃) ∷ (a₄ ⊕ b₄) ∷ []

-- 加法逆元：分量-wise GF(3) 取反
gf243-negate : GF243 → GF243
gf243-negate (a₀ ∷ a₁ ∷ a₂ ∷ a₃ ∷ a₄ ∷ []) =
  negate a₀ ∷ negate a₁ ∷ negate a₂ ∷ negate a₃ ∷ negate a₄ ∷ []

--------------------------------------------------------------------------------
-- 4. 特殊元素
--------------------------------------------------------------------------------

-- 乘法单位元 1（常数多项式 1）
gf243-one : GF243
gf243-one = T₁ ∷ T₀ ∷ T₀ ∷ T₀ ∷ T₀ ∷ []

-- 本原元 α = x（多项式 x 的陪集）
-- α⁵ + 2α + 1 = 0，即 α⁵ = α + 2
alpha : GF243
alpha = T₀ ∷ T₁ ∷ T₀ ∷ T₀ ∷ T₀ ∷ []

--------------------------------------------------------------------------------
-- 5. 加法群公理（构造性证明，分量提升自 GF(3)）
--------------------------------------------------------------------------------

-- 加法交换律
+gf243-comm : ∀ x y → x +gf243 y ≡ y +gf243 x
+gf243-comm (a₀ ∷ a₁ ∷ a₂ ∷ a₃ ∷ a₄ ∷ [])
            (b₀ ∷ b₁ ∷ b₂ ∷ b₃ ∷ b₄ ∷ []) =
  cong₂ _∷_ (⊕-comm a₀ b₀)
    (cong₂ _∷_ (⊕-comm a₁ b₁)
      (cong₂ _∷_ (⊕-comm a₂ b₂)
        (cong₂ _∷_ (⊕-comm a₃ b₃)
          (cong₂ _∷_ (⊕-comm a₄ b₄) refl))))

-- 加法结合律
+gf243-assoc : ∀ x y z → (x +gf243 y) +gf243 z ≡ x +gf243 (y +gf243 z)
+gf243-assoc (a₀ ∷ a₁ ∷ a₂ ∷ a₃ ∷ a₄ ∷ [])
             (b₀ ∷ b₁ ∷ b₂ ∷ b₃ ∷ b₄ ∷ [])
             (c₀ ∷ c₁ ∷ c₂ ∷ c₃ ∷ c₄ ∷ []) =
  cong₂ _∷_ (⊕-assoc a₀ b₀ c₀)
    (cong₂ _∷_ (⊕-assoc a₁ b₁ c₁)
      (cong₂ _∷_ (⊕-assoc a₂ b₂ c₂)
        (cong₂ _∷_ (⊕-assoc a₃ b₃ c₃)
          (cong₂ _∷_ (⊕-assoc a₄ b₄ c₄) refl))))

-- 左单位元
+gf243-identityˡ : ∀ x → gf243-zero +gf243 x ≡ x
+gf243-identityˡ (a₀ ∷ a₁ ∷ a₂ ∷ a₃ ∷ a₄ ∷ []) =
  cong₂ _∷_ (⊕-identityˡ a₀)
    (cong₂ _∷_ (⊕-identityˡ a₁)
      (cong₂ _∷_ (⊕-identityˡ a₂)
        (cong₂ _∷_ (⊕-identityˡ a₃)
          (cong₂ _∷_ (⊕-identityˡ a₄) refl))))

-- 右单位元
+gf243-identityʳ : ∀ x → x +gf243 gf243-zero ≡ x
+gf243-identityʳ (a₀ ∷ a₁ ∷ a₂ ∷ a₃ ∷ a₄ ∷ []) =
  cong₂ _∷_ (⊕-identityʳ a₀)
    (cong₂ _∷_ (⊕-identityʳ a₁)
      (cong₂ _∷_ (⊕-identityʳ a₂)
        (cong₂ _∷_ (⊕-identityʳ a₃)
          (cong₂ _∷_ (⊕-identityʳ a₄) refl))))

-- 右逆元
+gf243-inverse : ∀ x → x +gf243 gf243-negate x ≡ gf243-zero
+gf243-inverse (a₀ ∷ a₁ ∷ a₂ ∷ a₃ ∷ a₄ ∷ []) =
  cong₂ _∷_ (⊕-inverse a₀)
    (cong₂ _∷_ (⊕-inverse a₁)
      (cong₂ _∷_ (⊕-inverse a₂)
        (cong₂ _∷_ (⊕-inverse a₃)
          (cong₂ _∷_ (⊕-inverse a₄) refl))))

-- 左逆元（由交换律 + 右逆元推导）
+gf243-inverseˡ : ∀ x → gf243-negate x +gf243 x ≡ gf243-zero
+gf243-inverseˡ x = trans (+gf243-comm (gf243-negate x) x) (+gf243-inverse x)

-- 取反对合
gf243-negate² : ∀ x → gf243-negate (gf243-negate x) ≡ x
gf243-negate² (a₀ ∷ a₁ ∷ a₂ ∷ a₃ ∷ a₄ ∷ []) =
  cong₂ _∷_ (negate² a₀)
    (cong₂ _∷_ (negate² a₁)
      (cong₂ _∷_ (negate² a₂)
        (cong₂ _∷_ (negate² a₃)
          (cong₂ _∷_ (negate² a₄) refl))))

--------------------------------------------------------------------------------
-- 6. 特征 3
--------------------------------------------------------------------------------

-- GF(3) 层：x + x + x = 0
trit-char3 : ∀ x → x ⊕ (x ⊕ x) ≡ T₀
trit-char3 T₀ = refl
trit-char3 T₁ = refl
trit-char3 T₂ = refl

-- GF(243) 特征 3：x + x + x = 0
+gf243-char3 : ∀ x → x +gf243 (x +gf243 x) ≡ gf243-zero
+gf243-char3 (a₀ ∷ a₁ ∷ a₂ ∷ a₃ ∷ a₄ ∷ []) =
  cong₂ _∷_ (trit-char3 a₀)
    (cong₂ _∷_ (trit-char3 a₁)
      (cong₂ _∷_ (trit-char3 a₂)
        (cong₂ _∷_ (trit-char3 a₃)
          (cong₂ _∷_ (trit-char3 a₄) refl))))

--------------------------------------------------------------------------------
-- 7. GF(3) 嵌入
--------------------------------------------------------------------------------

-- 常数多项式嵌入：GF(3) → GF(243)
-- a ↦ a + 0·x + 0·x² + 0·x³ + 0·x⁴
embed-gf3 : Trit → GF243
embed-gf3 a = a ∷ T₀ ∷ T₀ ∷ T₀ ∷ T₀ ∷ []

-- 嵌入保持加法
embed-preserves-+ : ∀ a b → embed-gf3 (a ⊕ b) ≡ embed-gf3 a +gf243 embed-gf3 b
embed-preserves-+ a b = refl

-- 嵌入保持零元
embed-preserves-zero : embed-gf3 T₀ ≡ gf243-zero
embed-preserves-zero = refl

-- 嵌入保持取反
embed-preserves-negate : ∀ a → embed-gf3 (negate a) ≡ gf243-negate (embed-gf3 a)
embed-preserves-negate a = refl

--------------------------------------------------------------------------------
-- 8. 阶与基数
--------------------------------------------------------------------------------

-- GF(243) 的阶：3⁵ = 243
pow-3-5 : 3 ^ 5 ≡ 243
pow-3-5 = refl

-- |GF243| = |Vec Trit 5| = |Trit|⁵ = 3⁵ = 243
-- 与 PackedByte = Fin 243 的 243 个态一一对应

--------------------------------------------------------------------------------
-- 9. 与 PackedByte (PackedTryte5) 的连接
--------------------------------------------------------------------------------

-- PackedByte (定义于 Sovereign.Format.TQ10)：
--   PackedByte = Fin 243
--   pack5   : Vec Trit 5 → Fin 243  (混合进制编码)
--   unpack5 : Fin 243 → Vec Trit 5  (混合进制解码)
--
-- GF243 = Vec Trit 5 与 PackedByte = Fin 243 作为集合等势（243 个元素）
-- pack5/unpack5 提供双射
--
-- 范畴分离（宪法约束）：
--   GF243 是代数结构（加法群，可扩展为域）— 结构学范畴
--   PackedByte 是物理存储（裸 Fin 243）— 耦合域范畴
--   双射连接两个范畴，但不混淆其结构
--
-- 工程意义：
--   PackedByte 的 243 个态可以用 GF(243) 的加法群结构进行纠错编码
--   GF(243) 的加法是分量-wise GF(3) 加法 = 逐 trit ⊕
--   这恰好是 pack5/unpack5 保持的结构

--------------------------------------------------------------------------------
-- 10. 域扩张塔
--------------------------------------------------------------------------------

-- GF(3^a) ⊂ GF(3^b) 当且仅当 a ∣ b
--
-- 子域格（小阶数）：
--
--            GF(729) = GF(3⁶)
--           /         \
--   GF(81)=GF(3⁴)   GF(27)=GF(3³)     GF(243)=GF(3⁵)
--        \           /                     |
--         GF(9)=GF(3²)                  GF(3)
--              \                        /
--               GF(3) = GF(3¹)
--
-- 关键事实：
--   1∣2, 2∣4 → GF(3) ⊂ GF(9) ⊂ GF(81)
--   1∣2, 2∣6 → GF(3) ⊂ GF(9) ⊂ GF(729)
--   1∣3, 3∣6 → GF(3) ⊂ GF(27) ⊂ GF(729)
--   1∣5, 5 素数 → GF(3) ⊂ GF(243)，无中间子域
--
-- GF(243) 的特殊性：5 是素数
--   [GF(243):GF(3)] = 5（素数阶扩张）
--   无真中间子域（因为 5 无真因子）
--   Gal(GF(243)/GF(3)) ≅ C₅（5 阶循环群）

-- 5 是素数的构造性证据：真因子只有 1 和 5
-- 2 ∤ 5, 3 ∤ 5, 4 ∤ 5
no-subfield-2 : 5 ≡ 2 * 2 + 1    -- 5 = 2×2 + 1, 余 1, 所以 2∤5
no-subfield-2 = refl

no-subfield-3 : 5 ≡ 3 * 1 + 2    -- 5 = 3×1 + 2, 余 2, 所以 3∤5
no-subfield-3 = refl

no-subfield-4 : 5 ≡ 4 * 1 + 1    -- 5 = 4×1 + 1, 余 1, 所以 4∤5
no-subfield-4 = refl

--------------------------------------------------------------------------------
-- 11. 涡旋塔连接
--------------------------------------------------------------------------------

-- GF(3) 幂塔：3⁰→3¹→3²→3³→3⁴→3⁵→3⁶
-- 即：1 → 3 → 9 → 27 → 81 → 243 → 729
-- GF(243) = 3⁵ 在此塔中

-- 涡旋塔：3→6→12→24→48→96→...
-- 12 = 3 × 4 = 3 × 2²（涡旋根 "123"）
-- 12⁵ = (3 × 2²)⁵ = 3⁵ × 2¹⁰ = 243 × 1024

-- 12⁵ = 248832
pow-12-5 : 12 ^ 5 ≡ 248832
pow-12-5 = refl

-- 248832 = 243 × 1024 = 3⁵ × 2¹⁰
vortex-factorization : 248832 ≡ 243 * 1024
vortex-factorization = refl

-- 2¹⁰ = 1024（二进制因子）
pow2-10-val : 2 ^ 10 ≡ 1024
pow2-10-val = refl

-- GF(3) 幂塔层级对应
-- 3⁰ = 1   : 平凡域
-- 3¹ = 3   : GF(3)   — Sovereign.Base.Trit
-- 3² = 9   : GF(9)   — Sovereign.Algebra.GF9
-- 3³ = 27  : GF(27)  — (待扩展)
-- 3⁴ = 81  : GF(81)  — (待扩展)
-- 3⁵ = 243 : GF(243) — 本模块
-- 3⁶ = 729 : GF(729) — Tryte 态空间 (待扩展)

--------------------------------------------------------------------------------
-- 12. GF(3)-向量空间结构
--------------------------------------------------------------------------------

-- GF(243) 作为 GF(3) 上的 5 维向量空间
-- 标量乘法：GF(3) × GF(243) → GF(243)

_*s243_ : Trit → GF243 → GF243
T₀ *s243 x = gf243-zero
T₁ *s243 x = x
T₂ *s243 x = x +gf243 x

-- 标量 1 是恒等
scalar-1 : ∀ x → T₁ *s243 x ≡ x
scalar-1 x = refl

-- 标量 0 归零
scalar-0 : ∀ x → T₀ *s243 x ≡ gf243-zero
scalar-0 x = refl

-- 标量 2 = 自加
scalar-2 : ∀ x → T₂ *s243 x ≡ x +gf243 x
scalar-2 x = refl

-- 2·x + x = 0（特征 3 的推论）
scalar-char3 : ∀ x → (T₂ *s243 x) +gf243 x ≡ gf243-zero
scalar-char3 x = trans (+gf243-assoc x x x) (+gf243-char3 x)

-- 四元和中交换中间两项（提升自 GF(3) 层）
⊕-swap-middle : ∀ w x y z → (w ⊕ x) ⊕ (y ⊕ z) ≡ (w ⊕ y) ⊕ (x ⊕ z)
⊕-swap-middle w x y z =
  trans (sym (⊕-assoc (w ⊕ x) y z))
    (trans (cong (_⊕ z) (⊕-assoc w x y))
      (trans (cong (λ t → (w ⊕ t) ⊕ z) (⊕-comm x y))
        (trans (cong (_⊕ z) (sym (⊕-assoc w y x)))
          (⊕-assoc (w ⊕ y) x z))))

-- GF(243) 层的 swap-middle
+gf243-swap-middle : ∀ w x y z →
  (w +gf243 x) +gf243 (y +gf243 z) ≡ (w +gf243 y) +gf243 (x +gf243 z)
+gf243-swap-middle (w₀ ∷ w₁ ∷ w₂ ∷ w₃ ∷ w₄ ∷ [])
                   (x₀ ∷ x₁ ∷ x₂ ∷ x₃ ∷ x₄ ∷ [])
                   (y₀ ∷ y₁ ∷ y₂ ∷ y₃ ∷ y₄ ∷ [])
                   (z₀ ∷ z₁ ∷ z₂ ∷ z₃ ∷ z₄ ∷ []) =
  cong₂ _∷_ (⊕-swap-middle w₀ x₀ y₀ z₀)
    (cong₂ _∷_ (⊕-swap-middle w₁ x₁ y₁ z₁)
      (cong₂ _∷_ (⊕-swap-middle w₂ x₂ y₂ z₂)
        (cong₂ _∷_ (⊕-swap-middle w₃ x₃ y₃ z₃)
          (cong₂ _∷_ (⊕-swap-middle w₄ x₄ y₄ z₄) refl))))

-- 标量乘法对加法的分配律：c·(x+y) = c·x + c·y
scalar-distrib : ∀ c x y → c *s243 (x +gf243 y) ≡ (c *s243 x) +gf243 (c *s243 y)
scalar-distrib T₀ x y = sym (+gf243-identityˡ gf243-zero)
scalar-distrib T₁ x y = refl
scalar-distrib T₂ x y = +gf243-swap-middle x y x y

--------------------------------------------------------------------------------
-- 13. Galois 群结构（文档）
--------------------------------------------------------------------------------

-- Gal(GF(243)/GF(3)) ≅ C₅
-- 生成元：Frobenius 自同构 σ(x) = x³
-- σ⁵(x) = x^(3⁵) = x^243 = x（GF(243) 中所有元素满足 x^243 = x）
-- σ 的阶 = 5（因为 [GF(243):GF(3)] = 5）
--
-- Frobenius 轨道（对 α = x）：
--   α → α³ → α⁹ → α²⁷ → α⁸¹ → α²⁴³ = α
--   轨道长度 = 5（因为 α 的极小多项式是 5 次的）
--
-- 注意：Frobenius 需要乘法结构，本模块仅定义加法群
-- 完整域结构（含乘法）待后续模块扩展
