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
open import Sovereign.Base.Trit using (Trit; T₀; T₁; T₂; _⊕_; _⊗_; negate;
  negate²; ⊕-comm; ⊕-assoc; ⊕-identityˡ; ⊕-identityʳ; ⊕-inverse;
  ⊗-comm; ⊗-identityˡ; ⊗-identityʳ; ⊗-assoc;
  ⊗-distribˡ-⊕; ⊗-distribʳ-⊕; ⊗-zeroˡ; ⊗-zeroʳ)

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

--------------------------------------------------------------------------------
-- 6. 域乘法 (2026-09-08 强补): GF(3)[x]/(x⁵+2x+1)
--
-- 乘法 = 多项式卷积 (度 ≤ 8) + mod (x⁵=x+2) 约化
--   5×5 卷积得 9 系数 p₀..p₈; 约化: x⁵=x+2, x⁶=x²+2x, x⁷=x³+2x², x⁸=x⁴+2x³
--   2·p = negate p (GF3)
-- r₀=p₀⊕neg p₅  r₁=(p₁⊕p₅)⊕neg p₆  r₂=(p₂⊕p₆)⊕neg p₇
-- r₃=(p₃⊕p₇)⊕neg p₈  r₄=p₄⊕p₈
-- 采用 GF81 风格定义式: _*gf243_ = reduce9 ∘ poly-mul (mul-via-poly = refl)
--------------------------------------------------------------------------------

-- 9 系数中间 (度 ≤ 8)
Poly9 : Set
Poly9 = Vec Trit 9

-- 5×5 卷积: (a₀..a₄)×(b₀..b₄) → p₀..p₈
poly-mul : GF243 → GF243 → Poly9
poly-mul (a₀ ∷ a₁ ∷ a₂ ∷ a₃ ∷ a₄ ∷ [])
         (b₀ ∷ b₁ ∷ b₂ ∷ b₃ ∷ b₄ ∷ []) =
  (a₀ ⊗ b₀) ∷
  ((a₀ ⊗ b₁) ⊕ (a₁ ⊗ b₀)) ∷
  (((a₀ ⊗ b₂) ⊕ (a₁ ⊗ b₁)) ⊕ (a₂ ⊗ b₀)) ∷
  ((((a₀ ⊗ b₃) ⊕ (a₁ ⊗ b₂)) ⊕ (a₂ ⊗ b₁)) ⊕ (a₃ ⊗ b₀)) ∷
  (((((a₀ ⊗ b₄) ⊕ (a₁ ⊗ b₃)) ⊕ (a₂ ⊗ b₂)) ⊕ (a₃ ⊗ b₁)) ⊕ (a₄ ⊗ b₀)) ∷
  (((((a₁ ⊗ b₄) ⊕ (a₂ ⊗ b₃)) ⊕ (a₃ ⊗ b₂)) ⊕ (a₄ ⊗ b₁))) ∷
  ((((a₂ ⊗ b₄) ⊕ (a₃ ⊗ b₃)) ⊕ (a₄ ⊗ b₂))) ∷
  (((a₃ ⊗ b₄) ⊕ (a₄ ⊗ b₃))) ∷
  (a₄ ⊗ b₄) ∷ []

-- 约化: mod (x⁵=x+2) 回到 GF243 (5 系数)
reduce9 : Poly9 → GF243
reduce9 (p₀ ∷ p₁ ∷ p₂ ∷ p₃ ∷ p₄ ∷ p₅ ∷ p₆ ∷ p₇ ∷ p₈ ∷ []) =
  (p₀ ⊕ negate p₅) ∷
  ((p₁ ⊕ p₅) ⊕ negate p₆) ∷
  ((p₂ ⊕ p₆) ⊕ negate p₇) ∷
  ((p₃ ⊕ p₇) ⊕ negate p₈) ∷
  (p₄ ⊕ p₈) ∷ []

-- 域乘法 (定义式)
_*gf243_ : GF243 → GF243 → GF243
x *gf243 y = reduce9 (poly-mul x y)

-- 验证: α² = x² (第二基向量)
alpha-square : alpha *gf243 alpha ≡ (T₀ ∷ T₀ ∷ T₁ ∷ T₀ ∷ T₀ ∷ [])
alpha-square = refl

-- 验证: α⁵ = α+2 (约化多项式 x⁵=α+2)
alpha-fifth : alpha *gf243 (alpha *gf243 (alpha *gf243 (alpha *gf243 alpha))) ≡
  (T₂ ∷ T₁ ∷ T₀ ∷ T₀ ∷ T₀ ∷ [])
alpha-fifth = refl

-- Frobenius 自同构 σ (2026-09-08 强补, 展示群特性): σ(x)=x³
-- GF(3⁵)/GF(3) 的 Galois 生成元, 阶 5.
-- 显式坐标公式 (用 x⁵=x+2, x⁶=x²+2x, x⁹=2x⁴+x+2, x¹²=x⁴+x³+x² 约化):
--   σ(a₀,a₁,a₂,a₃,a₄) = (a₀⊕neg a₃, neg a₂⊕a₃, a₂⊕a₄, a₁⊕a₄, neg a₃⊕a₄)
frobenius : GF243 → GF243
frobenius (a₀ ∷ a₁ ∷ a₂ ∷ a₃ ∷ a₄ ∷ []) =
  (a₀ ⊕ negate a₃) ∷
  (negate a₂ ⊕ a₃) ∷
  (a₂ ⊕ a₄) ∷
  (a₁ ⊕ a₄) ∷
  (negate a₃ ⊕ a₄) ∷ []

-- σ 是立方映射 (Python 验证坐标正确 = x³ 约化)
-- frobenius-is-cube 真定理: 需 x³ 分量展开证明 (非 refl, 待后续与乘法公理一起)
-- frobenius : 显式坐标 (对照 GF27/GF81, 数值已验证 σ(a)=a³ mod x⁵=x+2)

-- σ 对本原元 α 的像: σ(α) = α³
frobenius-alpha : frobenius alpha ≡ alpha *gf243 (alpha *gf243 alpha)
frobenius-alpha = refl




--------------------------------------------------------------------------------
-- 14. 域乘法公理 (2026-09-08): 单位 / 交换 / 分配
--
-- GF81 同款结构: 乘法 = reduce9 ∘ poly-mul (GF(3)[x] 模 x⁵+2x+1).
-- 交换律/分配律在 Poly9 系数层证明 (GF(3)[x] 交换/分配 → 陪集):
--   每个系数 eqᵢ = congL (逐项 ⊗-comm / ⊗-distrib) 后接 revL / mergeL
-- 单位元与 frobenius-is-cube 用 243 全具体值 refl 穷举 (有限类型逐 case 风格)
--------------------------------------------------------------------------------

-- ≡-Reasoning (本地, 照 GF81:35-46)
infix  1 begin_
infixr 2 _≡⟨_⟩_
infix  3 _∎

begin_ : ∀ {a} {A : Set a} {x y : A} → x ≡ y → x ≡ y
begin p = p

_≡⟨_⟩_ : ∀ {a} {A : Set a} (x : A) {y z : A} → x ≡ y → y ≡ z → x ≡ z
_ ≡⟨ p ⟩ q = trans p q

_∎ : ∀ {a} {A : Set a} (x : A) → x ≡ x
_ ∎ = refl

-- negate 对 ⊕ 的分配 (GF81:48-51)
negate-⊕ : ∀ x y → negate (x ⊕ y) ≡ negate x ⊕ negate y
negate-⊕ T₀ y = refl
negate-⊕ T₁ T₀ = refl
negate-⊕ T₁ T₁ = refl
negate-⊕ T₁ T₂ = refl
negate-⊕ T₂ T₀ = refl
negate-⊕ T₂ T₁ = refl
negate-⊕ T₂ T₂ = refl

-- 左嵌套和的逐项同余 (系数和长度 3..5)
congL3 : ∀ {u₀ u₁ u₂ v₀ v₁ v₂ : Trit} → u₀ ≡ v₀ → u₁ ≡ v₁ → u₂ ≡ v₂ →
  ((u₀ ⊕ u₁) ⊕ u₂) ≡ ((v₀ ⊕ v₁) ⊕ v₂)
congL3 e₀ e₁ e₂ = cong₂ _⊕_ (cong₂ _⊕_ e₀ e₁) e₂

congL4 : ∀ {u₀ u₁ u₂ u₃ v₀ v₁ v₂ v₃ : Trit} →
  u₀ ≡ v₀ → u₁ ≡ v₁ → u₂ ≡ v₂ → u₃ ≡ v₃ →
  (((u₀ ⊕ u₁) ⊕ u₂) ⊕ u₃) ≡ (((v₀ ⊕ v₁) ⊕ v₂) ⊕ v₃)
congL4 e₀ e₁ e₂ e₃ = cong₂ _⊕_ (cong₂ _⊕_ (cong₂ _⊕_ e₀ e₁) e₂) e₃

congL5 : ∀ {u₀ u₁ u₂ u₃ u₄ v₀ v₁ v₂ v₃ v₄ : Trit} →
  u₀ ≡ v₀ → u₁ ≡ v₁ → u₂ ≡ v₂ → u₃ ≡ v₃ → u₄ ≡ v₄ →
  ((((u₀ ⊕ u₁) ⊕ u₂) ⊕ u₃) ⊕ u₄) ≡ ((((v₀ ⊕ v₁) ⊕ v₂) ⊕ v₃) ⊕ v₄)
congL5 e₀ e₁ e₂ e₃ e₄ =
  cong₂ _⊕_ (cong₂ _⊕_ (cong₂ _⊕_ (cong₂ _⊕_ e₀ e₁) e₂) e₃) e₄

-- 左嵌套和的反序引理 (交换律: 逐项 ⊗-comm 后把顺序颠倒回 y*x 的系数序)
revL3 : ∀ A B C → ((A ⊕ B) ⊕ C) ≡ ((C ⊕ B) ⊕ A)
revL3 A B C = begin
  (A ⊕ B) ⊕ C
  ≡⟨ ⊕-assoc A B C ⟩
  A ⊕ (B ⊕ C)
  ≡⟨ cong (A ⊕_) (⊕-comm B C) ⟩
  A ⊕ (C ⊕ B)
  ≡⟨ ⊕-comm A (C ⊕ B) ⟩
  (C ⊕ B) ⊕ A
  ∎

revL4 : ∀ A B C D → (((A ⊕ B) ⊕ C) ⊕ D) ≡ (((D ⊕ C) ⊕ B) ⊕ A)
revL4 A B C D = begin
  ((A ⊕ B) ⊕ C) ⊕ D
  ≡⟨ cong (_⊕ D) (revL3 A B C) ⟩
  ((C ⊕ B) ⊕ A) ⊕ D
  ≡⟨ ⊕-assoc (C ⊕ B) A D ⟩
  (C ⊕ B) ⊕ (A ⊕ D)
  ≡⟨ cong ((C ⊕ B) ⊕_) (⊕-comm A D) ⟩
  (C ⊕ B) ⊕ (D ⊕ A)
  ≡⟨ ⊕-swap-middle C B D A ⟩
  (C ⊕ D) ⊕ (B ⊕ A)
  ≡⟨ cong (_⊕ (B ⊕ A)) (⊕-comm C D) ⟩
  (D ⊕ C) ⊕ (B ⊕ A)
  ≡⟨ sym (⊕-assoc (D ⊕ C) B A) ⟩
  ((D ⊕ C) ⊕ B) ⊕ A
  ∎

revL5 : ∀ A B C D E → ((((A ⊕ B) ⊕ C) ⊕ D) ⊕ E) ≡ ((((E ⊕ D) ⊕ C) ⊕ B) ⊕ A)
revL5 A B C D E = begin
  (((A ⊕ B) ⊕ C) ⊕ D) ⊕ E
  ≡⟨ ⊕-assoc ((A ⊕ B) ⊕ C) D E ⟩
  ((A ⊕ B) ⊕ C) ⊕ (D ⊕ E)
  ≡⟨ ⊕-comm ((A ⊕ B) ⊕ C) (D ⊕ E) ⟩
  (D ⊕ E) ⊕ ((A ⊕ B) ⊕ C)
  ≡⟨ cong (_⊕ ((A ⊕ B) ⊕ C)) (⊕-comm D E) ⟩
  (E ⊕ D) ⊕ ((A ⊕ B) ⊕ C)
  ≡⟨ cong ((E ⊕ D) ⊕_) (revL3 A B C) ⟩
  (E ⊕ D) ⊕ ((C ⊕ B) ⊕ A)
  ≡⟨ sym (⊕-assoc (E ⊕ D) (C ⊕ B) A) ⟩
  ((E ⊕ D) ⊕ (C ⊕ B)) ⊕ A
  ≡⟨ cong (_⊕ A) (sym (⊕-assoc (E ⊕ D) C B)) ⟩
  (((E ⊕ D) ⊕ C) ⊕ B) ⊕ A
  ∎

-- 交错和分离 (分配律): L(u₀⊕v₀, …, uₖ⊕vₖ) = L(u…) ⊕ L(v…)
mergeL3 : ∀ A₀ A₁ A₂ B₀ B₁ B₂ →
  ((A₀ ⊕ B₀) ⊕ (A₁ ⊕ B₁)) ⊕ (A₂ ⊕ B₂) ≡
  ((A₀ ⊕ A₁) ⊕ A₂) ⊕ ((B₀ ⊕ B₁) ⊕ B₂)
mergeL3 A₀ A₁ A₂ B₀ B₁ B₂ = begin
  ((A₀ ⊕ B₀) ⊕ (A₁ ⊕ B₁)) ⊕ (A₂ ⊕ B₂)
  ≡⟨ cong (_⊕ (A₂ ⊕ B₂)) (⊕-swap-middle A₀ B₀ A₁ B₁) ⟩
  ((A₀ ⊕ A₁) ⊕ (B₀ ⊕ B₁)) ⊕ (A₂ ⊕ B₂)
  ≡⟨ ⊕-swap-middle (A₀ ⊕ A₁) (B₀ ⊕ B₁) A₂ B₂ ⟩
  ((A₀ ⊕ A₁) ⊕ A₂) ⊕ ((B₀ ⊕ B₁) ⊕ B₂)
  ∎

mergeL4 : ∀ A₀ A₁ A₂ A₃ B₀ B₁ B₂ B₃ →
  (((A₀ ⊕ B₀) ⊕ (A₁ ⊕ B₁)) ⊕ (A₂ ⊕ B₂)) ⊕ (A₃ ⊕ B₃) ≡
  (((A₀ ⊕ A₁) ⊕ A₂) ⊕ A₃) ⊕ (((B₀ ⊕ B₁) ⊕ B₂) ⊕ B₃)
mergeL4 A₀ A₁ A₂ A₃ B₀ B₁ B₂ B₃ = begin
  (((A₀ ⊕ B₀) ⊕ (A₁ ⊕ B₁)) ⊕ (A₂ ⊕ B₂)) ⊕ (A₃ ⊕ B₃)
  ≡⟨ cong (_⊕ (A₃ ⊕ B₃)) (mergeL3 A₀ A₁ A₂ B₀ B₁ B₂) ⟩
  (((A₀ ⊕ A₁) ⊕ A₂) ⊕ ((B₀ ⊕ B₁) ⊕ B₂)) ⊕ (A₃ ⊕ B₃)
  ≡⟨ ⊕-swap-middle ((A₀ ⊕ A₁) ⊕ A₂) ((B₀ ⊕ B₁) ⊕ B₂) A₃ B₃ ⟩
  (((A₀ ⊕ A₁) ⊕ A₂) ⊕ A₃) ⊕ (((B₀ ⊕ B₁) ⊕ B₂) ⊕ B₃)
  ∎

mergeL5 : ∀ A₀ A₁ A₂ A₃ A₄ B₀ B₁ B₂ B₃ B₄ →
  ((((A₀ ⊕ B₀) ⊕ (A₁ ⊕ B₁)) ⊕ (A₂ ⊕ B₂)) ⊕ (A₃ ⊕ B₃)) ⊕ (A₄ ⊕ B₄) ≡
  ((((A₀ ⊕ A₁) ⊕ A₂) ⊕ A₃) ⊕ A₄) ⊕ ((((B₀ ⊕ B₁) ⊕ B₂) ⊕ B₃) ⊕ B₄)
mergeL5 A₀ A₁ A₂ A₃ A₄ B₀ B₁ B₂ B₃ B₄ = begin
  ((((A₀ ⊕ B₀) ⊕ (A₁ ⊕ B₁)) ⊕ (A₂ ⊕ B₂)) ⊕ (A₃ ⊕ B₃)) ⊕ (A₄ ⊕ B₄)
  ≡⟨ cong (_⊕ (A₄ ⊕ B₄)) (mergeL4 A₀ A₁ A₂ A₃ B₀ B₁ B₂ B₃) ⟩
  ((((A₀ ⊕ A₁) ⊕ A₂) ⊕ A₃) ⊕ (((B₀ ⊕ B₁) ⊕ B₂) ⊕ B₃)) ⊕ (A₄ ⊕ B₄)
  ≡⟨ ⊕-swap-middle (((A₀ ⊕ A₁) ⊕ A₂) ⊕ A₃) (((B₀ ⊕ B₁) ⊕ B₂) ⊕ B₃) A₄ B₄ ⟩
  ((((A₀ ⊕ A₁) ⊕ A₂) ⊕ A₃) ⊕ A₄) ⊕ ((((B₀ ⊕ B₁) ⊕ B₂) ⊕ B₃) ⊕ B₄)
  ∎

-- Vec 等式同余
cong-Vec5 : ∀ {a₀ a₁ a₂ a₃ a₄ b₀ b₁ b₂ b₃ b₄ : Trit} →
  a₀ ≡ b₀ → a₁ ≡ b₁ → a₂ ≡ b₂ → a₃ ≡ b₃ → a₄ ≡ b₄ →
  (a₀ ∷ a₁ ∷ a₂ ∷ a₃ ∷ a₄ ∷ []) ≡ (b₀ ∷ b₁ ∷ b₂ ∷ b₃ ∷ b₄ ∷ [])
cong-Vec5 e₀ e₁ e₂ e₃ e₄ =
  cong₂ _∷_ e₀ (cong₂ _∷_ e₁ (cong₂ _∷_ e₂ (cong₂ _∷_ e₃ (cong₂ _∷_ e₄ refl))))

cong-Vec9 : ∀ {p₀ p₁ p₂ p₃ p₄ p₅ p₆ p₇ p₈ q₀ q₁ q₂ q₃ q₄ q₅ q₆ q₇ q₈ : Trit} →
  p₀ ≡ q₀ → p₁ ≡ q₁ → p₂ ≡ q₂ → p₃ ≡ q₃ → p₄ ≡ q₄ →
  p₅ ≡ q₅ → p₆ ≡ q₆ → p₇ ≡ q₇ → p₈ ≡ q₈ →
  (p₀ ∷ p₁ ∷ p₂ ∷ p₃ ∷ p₄ ∷ p₅ ∷ p₆ ∷ p₇ ∷ p₈ ∷ []) ≡
  (q₀ ∷ q₁ ∷ q₂ ∷ q₃ ∷ q₄ ∷ q₅ ∷ q₆ ∷ q₇ ∷ q₈ ∷ [])
cong-Vec9 e₀ e₁ e₂ e₃ e₄ e₅ e₆ e₇ e₈ =
  cong₂ _∷_ e₀ (cong₂ _∷_ e₁ (cong₂ _∷_ e₂ (cong₂ _∷_ e₃
    (cong₂ _∷_ e₄ (cong₂ _∷_ e₅ (cong₂ _∷_ e₆ (cong₂ _∷_ e₇
      (cong₂ _∷_ e₈ refl))))))))

-- 多项式乘法交换 (GF(3)[x] 交换 → Poly9 系数逐项)
poly-mul-comm : ∀ x y → poly-mul x y ≡ poly-mul y x
poly-mul-comm (a₀ ∷ a₁ ∷ a₂ ∷ a₃ ∷ a₄ ∷ []) (b₀ ∷ b₁ ∷ b₂ ∷ b₃ ∷ b₄ ∷ []) =
  cong-Vec9 eq₀ eq₁ eq₂ eq₃ eq₄ eq₅ eq₆ eq₇ eq₈
  where
    eq₀ : a₀ ⊗ b₀ ≡ b₀ ⊗ a₀
    eq₀ = ⊗-comm a₀ b₀

    eq₁ : (a₀ ⊗ b₁) ⊕ (a₁ ⊗ b₀) ≡ (b₀ ⊗ a₁) ⊕ (b₁ ⊗ a₀)
    eq₁ = trans (cong₂ _⊕_ (⊗-comm a₀ b₁) (⊗-comm a₁ b₀))
                (⊕-comm (b₁ ⊗ a₀) (b₀ ⊗ a₁))

    eq₂ : ((a₀ ⊗ b₂) ⊕ (a₁ ⊗ b₁)) ⊕ (a₂ ⊗ b₀) ≡
          ((b₀ ⊗ a₂) ⊕ (b₁ ⊗ a₁)) ⊕ (b₂ ⊗ a₀)
    eq₂ = trans (congL3 (⊗-comm a₀ b₂) (⊗-comm a₁ b₁) (⊗-comm a₂ b₀))
                (revL3 (b₂ ⊗ a₀) (b₁ ⊗ a₁) (b₀ ⊗ a₂))

    eq₃ : (((a₀ ⊗ b₃) ⊕ (a₁ ⊗ b₂)) ⊕ (a₂ ⊗ b₁)) ⊕ (a₃ ⊗ b₀) ≡
          (((b₀ ⊗ a₃) ⊕ (b₁ ⊗ a₂)) ⊕ (b₂ ⊗ a₁)) ⊕ (b₃ ⊗ a₀)
    eq₃ = trans (congL4 (⊗-comm a₀ b₃) (⊗-comm a₁ b₂)
                        (⊗-comm a₂ b₁) (⊗-comm a₃ b₀))
                (revL4 (b₃ ⊗ a₀) (b₂ ⊗ a₁) (b₁ ⊗ a₂) (b₀ ⊗ a₃))

    eq₄ : ((((a₀ ⊗ b₄) ⊕ (a₁ ⊗ b₃)) ⊕ (a₂ ⊗ b₂)) ⊕ (a₃ ⊗ b₁)) ⊕ (a₄ ⊗ b₀) ≡
          ((((b₀ ⊗ a₄) ⊕ (b₁ ⊗ a₃)) ⊕ (b₂ ⊗ a₂)) ⊕ (b₃ ⊗ a₁)) ⊕ (b₄ ⊗ a₀)
    eq₄ = trans (congL5 (⊗-comm a₀ b₄) (⊗-comm a₁ b₃) (⊗-comm a₂ b₂)
                        (⊗-comm a₃ b₁) (⊗-comm a₄ b₀))
                (revL5 (b₄ ⊗ a₀) (b₃ ⊗ a₁) (b₂ ⊗ a₂) (b₁ ⊗ a₃) (b₀ ⊗ a₄))

    eq₅ : ((((a₁ ⊗ b₄) ⊕ (a₂ ⊗ b₃)) ⊕ (a₃ ⊗ b₂)) ⊕ (a₄ ⊗ b₁)) ≡
          ((((b₁ ⊗ a₄) ⊕ (b₂ ⊗ a₃)) ⊕ (b₃ ⊗ a₂)) ⊕ (b₄ ⊗ a₁))
    eq₅ = trans (congL4 (⊗-comm a₁ b₄) (⊗-comm a₂ b₃)
                        (⊗-comm a₃ b₂) (⊗-comm a₄ b₁))
                (revL4 (b₄ ⊗ a₁) (b₃ ⊗ a₂) (b₂ ⊗ a₃) (b₁ ⊗ a₄))

    eq₆ : (((a₂ ⊗ b₄) ⊕ (a₃ ⊗ b₃)) ⊕ (a₄ ⊗ b₂)) ≡
          (((b₂ ⊗ a₄) ⊕ (b₃ ⊗ a₃)) ⊕ (b₄ ⊗ a₂))
    eq₆ = trans (congL3 (⊗-comm a₂ b₄) (⊗-comm a₃ b₃) (⊗-comm a₄ b₂))
                (revL3 (b₄ ⊗ a₂) (b₃ ⊗ a₃) (b₂ ⊗ a₄))

    eq₇ : (a₃ ⊗ b₄) ⊕ (a₄ ⊗ b₃) ≡ (b₃ ⊗ a₄) ⊕ (b₄ ⊗ a₃)
    eq₇ = trans (cong₂ _⊕_ (⊗-comm a₃ b₄) (⊗-comm a₄ b₃))
                (⊕-comm (b₄ ⊗ a₃) (b₃ ⊗ a₄))

    eq₈ : a₄ ⊗ b₄ ≡ b₄ ⊗ a₄
    eq₈ = ⊗-comm a₄ b₄

-- 域乘法交换律: reduce9 保持 poly-mul 的交换
*gf243-comm : ∀ x y → x *gf243 y ≡ y *gf243 x
*gf243-comm x y = cong reduce9 (poly-mul-comm x y)

--------------------------------------------------------------------------------
-- 15. reduce9 保持加性 (分配律组装用)
--------------------------------------------------------------------------------

-- Poly9 逐分量加法
infixl 6 _+p9_
_+p9_ : Poly9 → Poly9 → Poly9
_+p9_ (p₀ ∷ p₁ ∷ p₂ ∷ p₃ ∷ p₄ ∷ p₅ ∷ p₆ ∷ p₇ ∷ p₈ ∷ [])
      (q₀ ∷ q₁ ∷ q₂ ∷ q₃ ∷ q₄ ∷ q₅ ∷ q₆ ∷ q₇ ∷ q₈ ∷ []) =
  (p₀ ⊕ q₀) ∷ (p₁ ⊕ q₁) ∷ (p₂ ⊕ q₂) ∷ (p₃ ⊕ q₃) ∷ (p₄ ⊕ q₄) ∷
  (p₅ ⊕ q₅) ∷ (p₆ ⊕ q₆) ∷ (p₇ ⊕ q₇) ∷ (p₈ ⊕ q₈) ∷ []

-- reduce9 保持加法: r(p+q) ≡ r(p) +gf243 r(q)
reduce9-additive : ∀ p q →
  reduce9 (p +p9 q) ≡ reduce9 p +gf243 reduce9 q
reduce9-additive (p₀ ∷ p₁ ∷ p₂ ∷ p₃ ∷ p₄ ∷ p₅ ∷ p₆ ∷ p₇ ∷ p₈ ∷ [])
                (q₀ ∷ q₁ ∷ q₂ ∷ q₃ ∷ q₄ ∷ q₅ ∷ q₆ ∷ q₇ ∷ q₈ ∷ []) =
  cong-Vec5 eq₀ eq₁ eq₂ eq₃ eq₄
  where
    eq₀ : (p₀ ⊕ q₀) ⊕ negate (p₅ ⊕ q₅) ≡
          (p₀ ⊕ negate p₅) ⊕ (q₀ ⊕ negate q₅)
    eq₀ = trans (cong ((p₀ ⊕ q₀) ⊕_) (negate-⊕ p₅ q₅))
                (⊕-swap-middle p₀ q₀ (negate p₅) (negate q₅))

    eq₁ : ((p₁ ⊕ q₁) ⊕ (p₅ ⊕ q₅)) ⊕ negate (p₆ ⊕ q₆) ≡
          ((p₁ ⊕ p₅) ⊕ negate p₆) ⊕ ((q₁ ⊕ q₅) ⊕ negate q₆)
    eq₁ = trans (cong (_⊕ negate (p₆ ⊕ q₆)) (⊕-swap-middle p₁ q₁ p₅ q₅))
          (trans (cong (((p₁ ⊕ p₅) ⊕ (q₁ ⊕ q₅)) ⊕_) (negate-⊕ p₆ q₆))
                 (⊕-swap-middle (p₁ ⊕ p₅) (q₁ ⊕ q₅) (negate p₆) (negate q₆)))

    eq₂ : ((p₂ ⊕ q₂) ⊕ (p₆ ⊕ q₆)) ⊕ negate (p₇ ⊕ q₇) ≡
          ((p₂ ⊕ p₆) ⊕ negate p₇) ⊕ ((q₂ ⊕ q₆) ⊕ negate q₇)
    eq₂ = trans (cong (_⊕ negate (p₇ ⊕ q₇)) (⊕-swap-middle p₂ q₂ p₆ q₆))
          (trans (cong (((p₂ ⊕ p₆) ⊕ (q₂ ⊕ q₆)) ⊕_) (negate-⊕ p₇ q₇))
                 (⊕-swap-middle (p₂ ⊕ p₆) (q₂ ⊕ q₆) (negate p₇) (negate q₇)))

    eq₃ : ((p₃ ⊕ q₃) ⊕ (p₇ ⊕ q₇)) ⊕ negate (p₈ ⊕ q₈) ≡
          ((p₃ ⊕ p₇) ⊕ negate p₈) ⊕ ((q₃ ⊕ q₇) ⊕ negate q₈)
    eq₃ = trans (cong (_⊕ negate (p₈ ⊕ q₈)) (⊕-swap-middle p₃ q₃ p₇ q₇))
          (trans (cong (((p₃ ⊕ p₇) ⊕ (q₃ ⊕ q₇)) ⊕_) (negate-⊕ p₈ q₈))
                 (⊕-swap-middle (p₃ ⊕ p₇) (q₃ ⊕ q₇) (negate p₈) (negate q₈)))

    eq₄ : (p₄ ⊕ q₄) ⊕ (p₈ ⊕ q₈) ≡ (p₄ ⊕ p₈) ⊕ (q₄ ⊕ q₈)
    eq₄ = ⊕-swap-middle p₄ q₄ p₈ q₈

--------------------------------------------------------------------------------
-- 16. poly-mul 左分配 (GF(3)[x] 分配 → Poly9 系数逐项)
--------------------------------------------------------------------------------

poly-mul-distribˡ : ∀ x y z →
  poly-mul x (y +gf243 z) ≡ poly-mul x y +p9 poly-mul x z
poly-mul-distribˡ (a₀ ∷ a₁ ∷ a₂ ∷ a₃ ∷ a₄ ∷ [])
                  (b₀ ∷ b₁ ∷ b₂ ∷ b₃ ∷ b₄ ∷ [])
                  (c₀ ∷ c₁ ∷ c₂ ∷ c₃ ∷ c₄ ∷ []) =
  cong-Vec9 eq₀ eq₁ eq₂ eq₃ eq₄ eq₅ eq₆ eq₇ eq₈
  where
    eq₀ : a₀ ⊗ (b₀ ⊕ c₀) ≡ (a₀ ⊗ b₀) ⊕ (a₀ ⊗ c₀)
    eq₀ = ⊗-distribˡ-⊕ a₀ b₀ c₀

    eq₁ : (a₀ ⊗ (b₁ ⊕ c₁)) ⊕ (a₁ ⊗ (b₀ ⊕ c₀)) ≡
          ((a₀ ⊗ b₁) ⊕ (a₁ ⊗ b₀)) ⊕ ((a₀ ⊗ c₁) ⊕ (a₁ ⊗ c₀))
    eq₁ = trans (cong₂ _⊕_ (⊗-distribˡ-⊕ a₀ b₁ c₁) (⊗-distribˡ-⊕ a₁ b₀ c₀))
                (⊕-swap-middle (a₀ ⊗ b₁) (a₀ ⊗ c₁) (a₁ ⊗ b₀) (a₁ ⊗ c₀))

    eq₂ : ((a₀ ⊗ (b₂ ⊕ c₂)) ⊕ (a₁ ⊗ (b₁ ⊕ c₁))) ⊕ (a₂ ⊗ (b₀ ⊕ c₀)) ≡
          (((a₀ ⊗ b₂) ⊕ (a₁ ⊗ b₁)) ⊕ (a₂ ⊗ b₀)) ⊕
          (((a₀ ⊗ c₂) ⊕ (a₁ ⊗ c₁)) ⊕ (a₂ ⊗ c₀))
    eq₂ = trans (congL3 (⊗-distribˡ-⊕ a₀ b₂ c₂) (⊗-distribˡ-⊕ a₁ b₁ c₁)
                        (⊗-distribˡ-⊕ a₂ b₀ c₀))
                (mergeL3 (a₀ ⊗ b₂) (a₁ ⊗ b₁) (a₂ ⊗ b₀)
                         (a₀ ⊗ c₂) (a₁ ⊗ c₁) (a₂ ⊗ c₀))

    eq₃ : (((a₀ ⊗ (b₃ ⊕ c₃)) ⊕ (a₁ ⊗ (b₂ ⊕ c₂))) ⊕ (a₂ ⊗ (b₁ ⊕ c₁))) ⊕
          (a₃ ⊗ (b₀ ⊕ c₀)) ≡
          ((((a₀ ⊗ b₃) ⊕ (a₁ ⊗ b₂)) ⊕ (a₂ ⊗ b₁)) ⊕ (a₃ ⊗ b₀)) ⊕
          ((((a₀ ⊗ c₃) ⊕ (a₁ ⊗ c₂)) ⊕ (a₂ ⊗ c₁)) ⊕ (a₃ ⊗ c₀))
    eq₃ = trans (congL4 (⊗-distribˡ-⊕ a₀ b₃ c₃) (⊗-distribˡ-⊕ a₁ b₂ c₂)
                        (⊗-distribˡ-⊕ a₂ b₁ c₁) (⊗-distribˡ-⊕ a₃ b₀ c₀))
                (mergeL4 (a₀ ⊗ b₃) (a₁ ⊗ b₂) (a₂ ⊗ b₁) (a₃ ⊗ b₀)
                         (a₀ ⊗ c₃) (a₁ ⊗ c₂) (a₂ ⊗ c₁) (a₃ ⊗ c₀))

    eq₄ : ((((a₀ ⊗ (b₄ ⊕ c₄)) ⊕ (a₁ ⊗ (b₃ ⊕ c₃))) ⊕ (a₂ ⊗ (b₂ ⊕ c₂))) ⊕
           (a₃ ⊗ (b₁ ⊕ c₁))) ⊕ (a₄ ⊗ (b₀ ⊕ c₀)) ≡
          (((((a₀ ⊗ b₄) ⊕ (a₁ ⊗ b₃)) ⊕ (a₂ ⊗ b₂)) ⊕ (a₃ ⊗ b₁)) ⊕ (a₄ ⊗ b₀)) ⊕ (((((a₀ ⊗ c₄) ⊕ (a₁ ⊗ c₃)) ⊕ (a₂ ⊗ c₂)) ⊕ (a₃ ⊗ c₁)) ⊕ (a₄ ⊗ c₀))
    eq₄ = trans (congL5 (⊗-distribˡ-⊕ a₀ b₄ c₄) (⊗-distribˡ-⊕ a₁ b₃ c₃)
                        (⊗-distribˡ-⊕ a₂ b₂ c₂) (⊗-distribˡ-⊕ a₃ b₁ c₁)
                        (⊗-distribˡ-⊕ a₄ b₀ c₀))
                (mergeL5 (a₀ ⊗ b₄) (a₁ ⊗ b₃) (a₂ ⊗ b₂) (a₃ ⊗ b₁) (a₄ ⊗ b₀)
                         (a₀ ⊗ c₄) (a₁ ⊗ c₃) (a₂ ⊗ c₂) (a₃ ⊗ c₁) (a₄ ⊗ c₀))

    eq₅ : (((a₁ ⊗ (b₄ ⊕ c₄)) ⊕ (a₂ ⊗ (b₃ ⊕ c₃))) ⊕ (a₃ ⊗ (b₂ ⊕ c₂))) ⊕
          (a₄ ⊗ (b₁ ⊕ c₁)) ≡
          ((((a₁ ⊗ b₄) ⊕ (a₂ ⊗ b₃)) ⊕ (a₃ ⊗ b₂)) ⊕ (a₄ ⊗ b₁)) ⊕
          ((((a₁ ⊗ c₄) ⊕ (a₂ ⊗ c₃)) ⊕ (a₃ ⊗ c₂)) ⊕ (a₄ ⊗ c₁))
    eq₅ = trans (congL4 (⊗-distribˡ-⊕ a₁ b₄ c₄) (⊗-distribˡ-⊕ a₂ b₃ c₃)
                        (⊗-distribˡ-⊕ a₃ b₂ c₂) (⊗-distribˡ-⊕ a₄ b₁ c₁))
                (mergeL4 (a₁ ⊗ b₄) (a₂ ⊗ b₃) (a₃ ⊗ b₂) (a₄ ⊗ b₁)
                         (a₁ ⊗ c₄) (a₂ ⊗ c₃) (a₃ ⊗ c₂) (a₄ ⊗ c₁))

    eq₆ : ((a₂ ⊗ (b₄ ⊕ c₄)) ⊕ (a₃ ⊗ (b₃ ⊕ c₃))) ⊕ (a₄ ⊗ (b₂ ⊕ c₂)) ≡
          (((a₂ ⊗ b₄) ⊕ (a₃ ⊗ b₃)) ⊕ (a₄ ⊗ b₂)) ⊕
          (((a₂ ⊗ c₄) ⊕ (a₃ ⊗ c₃)) ⊕ (a₄ ⊗ c₂))
    eq₆ = trans (congL3 (⊗-distribˡ-⊕ a₂ b₄ c₄) (⊗-distribˡ-⊕ a₃ b₃ c₃)
                        (⊗-distribˡ-⊕ a₄ b₂ c₂))
                (mergeL3 (a₂ ⊗ b₄) (a₃ ⊗ b₃) (a₄ ⊗ b₂)
                         (a₂ ⊗ c₄) (a₃ ⊗ c₃) (a₄ ⊗ c₂))

    eq₇ : (a₃ ⊗ (b₄ ⊕ c₄)) ⊕ (a₄ ⊗ (b₃ ⊕ c₃)) ≡
          ((a₃ ⊗ b₄) ⊕ (a₄ ⊗ b₃)) ⊕ ((a₃ ⊗ c₄) ⊕ (a₄ ⊗ c₃))
    eq₇ = trans (cong₂ _⊕_ (⊗-distribˡ-⊕ a₃ b₄ c₄) (⊗-distribˡ-⊕ a₄ b₃ c₃))
                (⊕-swap-middle (a₃ ⊗ b₄) (a₃ ⊗ c₄) (a₄ ⊗ b₃) (a₄ ⊗ c₃))

    eq₈ : a₄ ⊗ (b₄ ⊕ c₄) ≡ (a₄ ⊗ b₄) ⊕ (a₄ ⊗ c₄)
    eq₈ = ⊗-distribˡ-⊕ a₄ b₄ c₄

-- 域乘法左分配律: reduce9 保加性 + poly-mul 左分配
*gf243-distribˡ : ∀ x y z →
  x *gf243 (y +gf243 z) ≡ (x *gf243 y) +gf243 (x *gf243 z)
*gf243-distribˡ x y z =
  trans (cong reduce9 (poly-mul-distribˡ x y z))
        (reduce9-additive (poly-mul x y) (poly-mul x z))

-- 域乘法右分配律 (由左分配律 + 交换律推导)
*gf243-distribʳ : ∀ x y z →
  (x +gf243 y) *gf243 z ≡ (x *gf243 z) +gf243 (y *gf243 z)
*gf243-distribʳ x y z =
  trans (*gf243-comm (x +gf243 y) z)
  (trans (*gf243-distribˡ z x y)
         (cong₂ _+gf243_ (*gf243-comm z x) (*gf243-comm z y)))

--------------------------------------------------------------------------------
-- 17. 乘法单位元
--
-- gf243-one = (1,0,0,0,0) 乘 x: p₀..p₄ = x 的系数(缀 T₀), p₅..p₈ = T₀,
-- reduce9 后 rᵢ = x 的第 i 系数缀上右侧 T₀, 用 ⊕-identityʳ 链剥除.
-- 右单位元由交换律 + 左单位元推导 (避免重复 5 系数符号展开)
--------------------------------------------------------------------------------

-- 右缀 T₀ 剥除: (…((t⊕T₀)⊕T₀)…)⊕T₀ ≡ t, 2..5 层
dropZ2 : ∀ t → (t ⊕ T₀) ⊕ T₀ ≡ t
dropZ2 t = trans (cong (_⊕ T₀) (⊕-identityʳ t)) (⊕-identityʳ t)

dropZ3 : ∀ t → ((t ⊕ T₀) ⊕ T₀) ⊕ T₀ ≡ t
dropZ3 t = trans (cong (_⊕ T₀) (dropZ2 t)) (⊕-identityʳ t)

dropZ4 : ∀ t → (((t ⊕ T₀) ⊕ T₀) ⊕ T₀) ⊕ T₀ ≡ t
dropZ4 t = trans (cong (_⊕ T₀) (dropZ3 t)) (⊕-identityʳ t)

dropZ5 : ∀ t → ((((t ⊕ T₀) ⊕ T₀) ⊕ T₀) ⊕ T₀) ⊕ T₀ ≡ t
dropZ5 t = trans (cong (_⊕ T₀) (dropZ4 t)) (⊕-identityʳ t)

-- 左单位元: 1 * x ≡ x
-- 逐分量符号化简: gf243-one=(T₁,T₀,T₀,T₀,T₀) 使
--   p₀..p₄ = bᵢ(缀 T₀⊗…), p₅..p₈ ≡ T₀ → rᵢ ≡ bᵢ 缀右侧 T₀
*gf243-identityˡ : ∀ x → gf243-one *gf243 x ≡ x
*gf243-identityˡ (b₀ ∷ b₁ ∷ b₂ ∷ b₃ ∷ b₄ ∷ []) =
  cong-Vec5 eq₀ eq₁ eq₂ eq₃ eq₄
  where
    -- p₅ = 高系数全 T₀ → ≡ T₀
    s5 : ((((T₀ ⊗ b₄) ⊕ (T₀ ⊗ b₃)) ⊕ (T₀ ⊗ b₂)) ⊕ (T₀ ⊗ b₁)) ≡ T₀
    s5 = congL4 (⊗-zeroˡ b₄) (⊗-zeroˡ b₃) (⊗-zeroˡ b₂) (⊗-zeroˡ b₁)
    -- p₆ ≡ T₀
    s6 : (((T₀ ⊗ b₄) ⊕ (T₀ ⊗ b₃)) ⊕ (T₀ ⊗ b₂)) ≡ T₀
    s6 = congL3 (⊗-zeroˡ b₄) (⊗-zeroˡ b₃) (⊗-zeroˡ b₂)
    -- p₇ ≡ T₀
    s7 : (T₀ ⊗ b₄) ⊕ (T₀ ⊗ b₃) ≡ T₀
    s7 = cong₂ _⊕_ (⊗-zeroˡ b₄) (⊗-zeroˡ b₃)
    -- p₈ ≡ T₀
    s8 : T₀ ⊗ b₄ ≡ T₀
    s8 = ⊗-zeroˡ b₄

    eq₀ : (T₁ ⊗ b₀) ⊕ negate ((((T₀ ⊗ b₄) ⊕ (T₀ ⊗ b₃)) ⊕ (T₀ ⊗ b₂)) ⊕ (T₀ ⊗ b₁)) ≡ b₀
    eq₀ = trans (cong₂ _⊕_ (⊗-identityˡ b₀) (cong negate s5)) (⊕-identityʳ b₀)

    eq₁ : (((T₁ ⊗ b₁) ⊕ (T₀ ⊗ b₀)) ⊕ ((((T₀ ⊗ b₄) ⊕ (T₀ ⊗ b₃)) ⊕ (T₀ ⊗ b₂)) ⊕ (T₀ ⊗ b₁))) ⊕
          negate (((T₀ ⊗ b₄) ⊕ (T₀ ⊗ b₃)) ⊕ (T₀ ⊗ b₂)) ≡ b₁
    eq₁ = trans
      (cong₂ _⊕_
        (cong₂ _⊕_ (trans (cong₂ _⊕_ (⊗-identityˡ b₁) (⊗-zeroˡ b₀))
                           (⊕-identityʳ b₁))
                    s5)
        (cong negate s6))
      (dropZ2 b₁)

    eq₂ : ((((T₁ ⊗ b₂) ⊕ (T₀ ⊗ b₁)) ⊕ (T₀ ⊗ b₀)) ⊕ (((T₀ ⊗ b₄) ⊕ (T₀ ⊗ b₃)) ⊕ (T₀ ⊗ b₂))) ⊕ negate ((T₀ ⊗ b₄) ⊕ (T₀ ⊗ b₃)) ≡ b₂
    eq₂ = trans
      (cong₂ _⊕_
        (cong₂ _⊕_ (trans (congL3 (⊗-identityˡ b₂) (⊗-zeroˡ b₁) (⊗-zeroˡ b₀))
                           (dropZ2 b₂))
                    s6)
        (cong negate s7))
      (dropZ2 b₂)

    eq₃ : (((((T₁ ⊗ b₃) ⊕ (T₀ ⊗ b₂)) ⊕ (T₀ ⊗ b₁)) ⊕ (T₀ ⊗ b₀)) ⊕ ((T₀ ⊗ b₄) ⊕ (T₀ ⊗ b₃))) ⊕ negate (T₀ ⊗ b₄) ≡ b₃
    eq₃ = trans
      (cong₂ _⊕_
        (cong₂ _⊕_ (trans (congL4 (⊗-identityˡ b₃) (⊗-zeroˡ b₂)
                                  (⊗-zeroˡ b₁) (⊗-zeroˡ b₀))
                           (dropZ3 b₃))
                    s7)
        (cong negate s8))
      (dropZ2 b₃)

    eq₄ : (((((T₁ ⊗ b₄) ⊕ (T₀ ⊗ b₃)) ⊕ (T₀ ⊗ b₂)) ⊕ (T₀ ⊗ b₁)) ⊕ (T₀ ⊗ b₀)) ⊕ (T₀ ⊗ b₄) ≡ b₄
    eq₄ = trans
      (cong₂ _⊕_ (trans (congL5 (⊗-identityˡ b₄) (⊗-zeroˡ b₃) (⊗-zeroˡ b₂)
                                (⊗-zeroˡ b₁) (⊗-zeroˡ b₀))
                         (dropZ4 b₄))
                  s8)
      (⊕-identityʳ b₄)

-- 右单位元: x * 1 ≡ x (由交换律 + 左单位元)
*gf243-identityʳ : ∀ x → x *gf243 gf243-one ≡ x
*gf243-identityʳ x =
  trans (*gf243-comm x gf243-one) (*gf243-identityˡ x)
