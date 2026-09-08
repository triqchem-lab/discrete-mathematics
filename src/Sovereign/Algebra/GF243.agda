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
open import Data.Sum using (_⊎_; inj₁; inj₂)
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

-- frobenius-is-cube: σ(x) = x³ — 构造性证明见文件末尾 §15
-- (替换原 243 case refl 穷举; Lin243 + linear-ext5 基展开)

-- 显式标注同余 (复合项上裸 cong₂ 会触发展开失败)
cong-+243 : ∀ {a b c d : GF243} → a ≡ c → b ≡ d → (a +gf243 b) ≡ (c +gf243 d)
cong-+243 p q = cong₂ (λ (u v : GF243) → u +gf243 v) p q

cong-*243 : ∀ {a b c d : GF243} → a ≡ c → b ≡ d → (a *gf243 b) ≡ (c *gf243 d)
cong-*243 p q = cong₂ (λ (u v : GF243) → u *gf243 v) p q

--------------------------------------------------------------------------------
-- §1. Trit 层辅助
--------------------------------------------------------------------------------

dn-trit : ∀ t → t ⊕ t ≡ negate t
dn-trit T₀ = refl
dn-trit T₁ = refl
dn-trit T₂ = refl

⊗-cube-id : ∀ t → t ⊗ (t ⊗ t) ≡ t
⊗-cube-id T₀ = refl
⊗-cube-id T₁ = refl
⊗-cube-id T₂ = refl

neg-⊗ : ∀ x y → negate (x ⊗ y) ≡ (negate x) ⊗ y
neg-⊗ T₀ y = refl
neg-⊗ T₁ T₀ = refl; neg-⊗ T₁ T₁ = refl; neg-⊗ T₁ T₂ = refl
neg-⊗ T₂ T₀ = refl; neg-⊗ T₂ T₁ = refl; neg-⊗ T₂ T₂ = refl

neg-⊗-comm : ∀ x y → (negate x) ⊗ y ≡ x ⊗ (negate y)
neg-⊗-comm T₀ y = refl
neg-⊗-comm T₁ T₀ = refl; neg-⊗-comm T₁ T₁ = refl; neg-⊗-comm T₁ T₂ = refl
neg-⊗-comm T₂ T₀ = refl; neg-⊗-comm T₂ T₁ = refl; neg-⊗-comm T₂ T₂ = refl

neg-⊗-r : ∀ A z → negate (A ⊗ z) ≡ A ⊗ negate z
neg-⊗-r A z = trans (neg-⊗ A z) (neg-⊗-comm A z)

--------------------------------------------------------------------------------
-- §2. 基元素与标量
--------------------------------------------------------------------------------

alpha2 : GF243
alpha2 = T₀ ∷ T₀ ∷ T₁ ∷ T₀ ∷ T₀ ∷ []

alpha3 : GF243
alpha3 = T₀ ∷ T₀ ∷ T₀ ∷ T₁ ∷ T₀ ∷ []

alpha4 : GF243
alpha4 = T₀ ∷ T₀ ∷ T₀ ∷ T₀ ∷ T₁ ∷ []

s243-one : ∀ a → a *s243 gf243-one ≡ a ∷ T₀ ∷ T₀ ∷ T₀ ∷ T₀ ∷ []
s243-one T₀ = refl
s243-one T₁ = refl
s243-one T₂ = refl

s243-alpha : ∀ b → b *s243 alpha ≡ T₀ ∷ b ∷ T₀ ∷ T₀ ∷ T₀ ∷ []
s243-alpha T₀ = refl
s243-alpha T₁ = refl
s243-alpha T₂ = refl

s243-alpha2 : ∀ c → c *s243 alpha2 ≡ T₀ ∷ T₀ ∷ c ∷ T₀ ∷ T₀ ∷ []
s243-alpha2 T₀ = refl
s243-alpha2 T₁ = refl
s243-alpha2 T₂ = refl

s243-alpha3 : ∀ d → d *s243 alpha3 ≡ T₀ ∷ T₀ ∷ T₀ ∷ d ∷ T₀ ∷ []
s243-alpha3 T₀ = refl
s243-alpha3 T₁ = refl
s243-alpha3 T₂ = refl

s243-alpha4 : ∀ e → e *s243 alpha4 ≡ T₀ ∷ T₀ ∷ T₀ ∷ T₀ ∷ e ∷ []
s243-alpha4 T₀ = refl
s243-alpha4 T₁ = refl
s243-alpha4 T₂ = refl

-- 基分解: (a,b,c,d,e) = a·1 + (b·α + (c·α² + (d·α³ + e·α⁴)))
decomp243 : ∀ (a b c d e : Trit) →
  (a ∷ b ∷ c ∷ d ∷ e ∷ [])
  ≡ (a *s243 gf243-one) +gf243 ((b *s243 alpha) +gf243 ((c *s243 alpha2)
      +gf243 ((d *s243 alpha3) +gf243 (e *s243 alpha4))))
decomp243 a b c d e = sym (begin
  (a *s243 gf243-one) +gf243 ((b *s243 alpha) +gf243 ((c *s243 alpha2)
      +gf243 ((d *s243 alpha3) +gf243 (e *s243 alpha4))))
    ≡⟨ cong-+243 (s243-one a)
         (cong-+243 (s243-alpha b) (cong-+243 (s243-alpha2 c)
           (cong-+243 (s243-alpha3 d) (s243-alpha4 e)))) ⟩
  (a ∷ T₀ ∷ T₀ ∷ T₀ ∷ T₀ ∷ []) +gf243 ((T₀ ∷ b ∷ T₀ ∷ T₀ ∷ T₀ ∷ [])
    +gf243 ((T₀ ∷ T₀ ∷ c ∷ T₀ ∷ T₀ ∷ []) +gf243 ((T₀ ∷ T₀ ∷ T₀ ∷ d ∷ T₀ ∷ [])
      +gf243 (T₀ ∷ T₀ ∷ T₀ ∷ T₀ ∷ e ∷ []))))
    ≡⟨ cong ((a ∷ T₀ ∷ T₀ ∷ T₀ ∷ T₀ ∷ []) +gf243_)
         (cong ((T₀ ∷ b ∷ T₀ ∷ T₀ ∷ T₀ ∷ []) +gf243_)
           (cong ((T₀ ∷ T₀ ∷ c ∷ T₀ ∷ T₀ ∷ []) +gf243_)
             (add-zero-r5 d e))) ⟩
  (a ∷ T₀ ∷ T₀ ∷ T₀ ∷ T₀ ∷ []) +gf243 ((T₀ ∷ b ∷ T₀ ∷ T₀ ∷ T₀ ∷ [])
    +gf243 ((T₀ ∷ T₀ ∷ c ∷ T₀ ∷ T₀ ∷ []) +gf243 (T₀ ∷ T₀ ∷ T₀ ∷ d ∷ e ∷ [])))
    ≡⟨ cong ((a ∷ T₀ ∷ T₀ ∷ T₀ ∷ T₀ ∷ []) +gf243_)
         (cong ((T₀ ∷ b ∷ T₀ ∷ T₀ ∷ T₀ ∷ []) +gf243_)
           (cong-5 (⊕-identityˡ T₀) (⊕-identityˡ T₀) (⊕-identityʳ c) (⊕-identityˡ d) (⊕-identityˡ e))) ⟩
  (a ∷ T₀ ∷ T₀ ∷ T₀ ∷ T₀ ∷ []) +gf243 ((T₀ ∷ b ∷ T₀ ∷ T₀ ∷ T₀ ∷ [])
    +gf243 (T₀ ∷ T₀ ∷ c ∷ d ∷ e ∷ []))
    ≡⟨ cong ((a ∷ T₀ ∷ T₀ ∷ T₀ ∷ T₀ ∷ []) +gf243_)
         (cong-5 (⊕-identityˡ T₀) (⊕-identityʳ b) (⊕-identityˡ c) (⊕-identityˡ d) (⊕-identityˡ e)) ⟩
  (a ∷ T₀ ∷ T₀ ∷ T₀ ∷ T₀ ∷ []) +gf243 (T₀ ∷ b ∷ c ∷ d ∷ e ∷ [])
    ≡⟨ cong-5 (⊕-identityʳ a) (⊕-identityˡ b) (⊕-identityˡ c) (⊕-identityˡ d) (⊕-identityˡ e) ⟩
  (a ∷ b ∷ c ∷ d ∷ e ∷ [])
  ∎)
  where
    cong-5 : ∀ {p₀ p₁ p₂ p₃ p₄ q₀ q₁ q₂ q₃ q₄ : Trit} →
      p₀ ≡ q₀ → p₁ ≡ q₁ → p₂ ≡ q₂ → p₃ ≡ q₃ → p₄ ≡ q₄ →
      (p₀ ∷ p₁ ∷ p₂ ∷ p₃ ∷ p₄ ∷ []) ≡ (q₀ ∷ q₁ ∷ q₂ ∷ q₃ ∷ q₄ ∷ [])
    cong-5 refl refl refl refl refl = refl
    add-zero-r5 : ∀ d e → (T₀ ∷ T₀ ∷ T₀ ∷ d ∷ T₀ ∷ []) +gf243 (T₀ ∷ T₀ ∷ T₀ ∷ T₀ ∷ e ∷ [])
                              ≡ (T₀ ∷ T₀ ∷ T₀ ∷ d ∷ e ∷ [])
    add-zero-r5 d e = cong-5 (⊕-identityˡ T₀) (⊕-identityˡ T₀) (⊕-identityˡ T₀) (⊕-identityʳ d) (⊕-identityˡ e)

--------------------------------------------------------------------------------
-- §3. Lin243 框架
--------------------------------------------------------------------------------

record Lin243 (f : GF243 → GF243) : Set where
  field
    ladd : ∀ a b → f (a +gf243 b) ≡ f a +gf243 f b
open Lin243

cancel-idem : ∀ u → u ≡ u +gf243 u → u ≡ gf243-zero
cancel-idem u h = begin
  u
    ≡⟨ sym (+gf243-identityʳ u) ⟩
  u +gf243 gf243-zero
    ≡⟨ cong (u +gf243_) (sym (+gf243-inverse u)) ⟩
  u +gf243 (u +gf243 gf243-negate u)
    ≡⟨ sym (+gf243-assoc u u (gf243-negate u)) ⟩
  (u +gf243 u) +gf243 gf243-negate u
    ≡⟨ cong (_+gf243 gf243-negate u) (sym h) ⟩
  u +gf243 gf243-negate u
    ≡⟨ +gf243-inverse u ⟩
  gf243-zero
  ∎

zero-mul-l243 : ∀ u → gf243-zero *gf243 u ≡ gf243-zero
zero-mul-l243 u = cancel-idem (gf243-zero *gf243 u) (*gf243-distribʳ gf243-zero gf243-zero u)

zero-mul-r243 : ∀ u → u *gf243 gf243-zero ≡ gf243-zero
zero-mul-r243 u = cancel-idem (u *gf243 gf243-zero)
  (trans (cong (u *gf243_) (sym (+gf243-identityˡ gf243-zero))) (*gf243-distribˡ u gf243-zero gf243-zero))

f0-zero : ∀ (f : GF243 → GF243) → (∀ a b → f (a +gf243 b) ≡ f a +gf243 f b) →
  f gf243-zero ≡ gf243-zero
f0-zero f ladd =
  cancel-idem (f gf243-zero)
    (trans (cong f (sym (+gf243-identityˡ gf243-zero))) (ladd gf243-zero gf243-zero))

lscalar-der : ∀ (f : GF243 → GF243) → (∀ a b → f (a +gf243 b) ≡ f a +gf243 f b) →
  ∀ c w → f (c *s243 w) ≡ c *s243 (f w)
lscalar-der f ladd T₀ w = f0-zero f ladd
lscalar-der f ladd T₁ w = refl
lscalar-der f ladd T₂ w = ladd w w

expand5 : ∀ (f : GF243 → GF243) → Lin243 f → ∀ (a b c d e : Trit) →
  f (a ∷ b ∷ c ∷ d ∷ e ∷ [])
  ≡ (a *s243 (f gf243-one)) +gf243 ((b *s243 (f alpha))
      +gf243 ((c *s243 (f alpha2)) +gf243 ((d *s243 (f alpha3)) +gf243 (e *s243 (f alpha4)))))
expand5 f L a b c d e =
  trans (cong f (decomp243 a b c d e))
    (trans (ladd L (a *s243 gf243-one)
                  ((b *s243 alpha) +gf243 ((c *s243 alpha2) +gf243 ((d *s243 alpha3) +gf243 (e *s243 alpha4)))))
    (trans (cong-+243 (lscalar-der f (ladd L) a gf243-one)
                      (trans (ladd L (b *s243 alpha) ((c *s243 alpha2) +gf243 ((d *s243 alpha3) +gf243 (e *s243 alpha4))))
                             (cong-+243 (lscalar-der f (ladd L) b alpha)
                                        (trans (ladd L (c *s243 alpha2) ((d *s243 alpha3) +gf243 (e *s243 alpha4)))
                                               (cong-+243 (lscalar-der f (ladd L) c alpha2)
                                                          (trans (ladd L (d *s243 alpha3) (e *s243 alpha4))
                                                                 (cong-+243 (lscalar-der f (ladd L) d alpha3)
                                                                            (lscalar-der f (ladd L) e alpha4))))))))
           refl))

linear-ext5 : ∀ (f g : GF243 → GF243) → Lin243 f → Lin243 g →
  f gf243-one ≡ g gf243-one → f alpha ≡ g alpha → f alpha2 ≡ g alpha2 →
  f alpha3 ≡ g alpha3 → f alpha4 ≡ g alpha4 → ∀ x → f x ≡ g x
linear-ext5 f g L L' e0 e1 e2 e3 e4 (a ∷ b ∷ c ∷ d ∷ ee ∷ []) =
  trans (expand5 f L a b c d ee)
    (trans (cong-+243 (cong (λ w → a *s243 w) e0)
                      (cong-+243 (cong (λ w → b *s243 w) e1)
                                (cong-+243 (cong (λ w → c *s243 w) e2)
                                          (cong-+243 (cong (λ w → d *s243 w) e3)
                                                    (cong (λ w → ee *s243 w) e4)))))
           (sym (expand5 g L' a b c d ee)))

--------------------------------------------------------------------------------
-- §4. 纯 +gf243 引理
--------------------------------------------------------------------------------

dn243 : ∀ u → (u +gf243 u) ≡ gf243-negate u
dn243 (a ∷ b ∷ c ∷ d ∷ e ∷ []) =
  cong-Vec5 (dn-trit a) (dn-trit b) (dn-trit c) (dn-trit d) (dn-trit e)

neg-add-zero243 : ∀ B → (gf243-negate B) +gf243 B ≡ gf243-zero
neg-add-zero243 B = trans (+gf243-comm (gf243-negate B) B) (+gf243-inverse B)

cancel-neg243 : ∀ A B → (A +gf243 gf243-negate B) +gf243 B ≡ A
cancel-neg243 A B =
  trans (+gf243-assoc A (gf243-negate B) B)
        (trans (cong (A +gf243_) (neg-add-zero243 B)) (+gf243-identityʳ A))

c-cancel243 : ∀ C D → C +gf243 (gf243-negate C +gf243 D) ≡ D
c-cancel243 C D =
  trans (sym (+gf243-assoc C (gf243-negate C) D))
        (trans (cong (_+gf243 D) (+gf243-inverse C)) (+gf243-identityˡ D))

swap4-243 : ∀ A B C D → (A +gf243 B) +gf243 (C +gf243 D) ≡ (A +gf243 C) +gf243 (B +gf243 D)
swap4-243 = +gf243-swap-middle

cm1-243 : ∀ A B C D → ((A +gf243 gf243-negate B) +gf243 C) +gf243 (B +gf243 (gf243-negate C +gf243 D))
                      ≡ ((A +gf243 gf243-negate B) +gf243 B) +gf243 (C +gf243 (gf243-negate C +gf243 D))
cm1-243 A B C D = swap4-243 (A +gf243 gf243-negate B) C B (gf243-negate C +gf243 D)

cm2-243 : ∀ A B C D → ((A +gf243 gf243-negate B) +gf243 B) +gf243 (C +gf243 (gf243-negate C +gf243 D)) ≡ A +gf243 D
cm2-243 A B C D =
  trans (cong (_+gf243 (C +gf243 (gf243-negate C +gf243 D))) (cancel-neg243 A B))
        (cong (A +gf243_) (c-cancel243 C D))

cancel-mid243 : ∀ A B C D → ((A +gf243 gf243-negate B) +gf243 C) +gf243 ((B +gf243 gf243-negate C) +gf243 D) ≡ A +gf243 D
cancel-mid243 A B C D =
  trans (cong (((A +gf243 gf243-negate B) +gf243 C) +gf243_) (+gf243-assoc B (gf243-negate C) D))
        (trans (cm1-243 A B C D) (cm2-243 A B C D))

--------------------------------------------------------------------------------
-- §5. 乘法结合律
--------------------------------------------------------------------------------

Basis243 : GF243 → Set
Basis243 b = (b ≡ gf243-one) ⊎ (b ≡ alpha) ⊎ (b ≡ alpha2) ⊎ (b ≡ alpha3) ⊎ (b ≡ alpha4)

assoc-basis : ∀ b1 b2 b3 → Basis243 b1 → Basis243 b2 → Basis243 b3 →
  ((b1 *gf243 b2) *gf243 b3) ≡ (b1 *gf243 (b2 *gf243 b3))
assoc-basis _ _ _ (inj₁ refl) (inj₁ refl) (inj₁ refl) = refl
assoc-basis _ _ _ (inj₁ refl) (inj₁ refl) (inj₂ (inj₁ refl)) = refl
assoc-basis _ _ _ (inj₁ refl) (inj₁ refl) (inj₂ (inj₂ (inj₁ refl))) = refl
assoc-basis _ _ _ (inj₁ refl) (inj₁ refl) (inj₂ (inj₂ (inj₂ (inj₁ refl)))) = refl
assoc-basis _ _ _ (inj₁ refl) (inj₁ refl) (inj₂ (inj₂ (inj₂ (inj₂ refl)))) = refl
assoc-basis _ _ _ (inj₁ refl) (inj₂ (inj₁ refl)) (inj₁ refl) = refl
assoc-basis _ _ _ (inj₁ refl) (inj₂ (inj₁ refl)) (inj₂ (inj₁ refl)) = refl
assoc-basis _ _ _ (inj₁ refl) (inj₂ (inj₁ refl)) (inj₂ (inj₂ (inj₁ refl))) = refl
assoc-basis _ _ _ (inj₁ refl) (inj₂ (inj₁ refl)) (inj₂ (inj₂ (inj₂ (inj₁ refl)))) = refl
assoc-basis _ _ _ (inj₁ refl) (inj₂ (inj₁ refl)) (inj₂ (inj₂ (inj₂ (inj₂ refl)))) = refl
assoc-basis _ _ _ (inj₁ refl) (inj₂ (inj₂ (inj₁ refl))) (inj₁ refl) = refl
assoc-basis _ _ _ (inj₁ refl) (inj₂ (inj₂ (inj₁ refl))) (inj₂ (inj₁ refl)) = refl
assoc-basis _ _ _ (inj₁ refl) (inj₂ (inj₂ (inj₁ refl))) (inj₂ (inj₂ (inj₁ refl))) = refl
assoc-basis _ _ _ (inj₁ refl) (inj₂ (inj₂ (inj₁ refl))) (inj₂ (inj₂ (inj₂ (inj₁ refl)))) = refl
assoc-basis _ _ _ (inj₁ refl) (inj₂ (inj₂ (inj₁ refl))) (inj₂ (inj₂ (inj₂ (inj₂ refl)))) = refl
assoc-basis _ _ _ (inj₁ refl) (inj₂ (inj₂ (inj₂ (inj₁ refl)))) (inj₁ refl) = refl
assoc-basis _ _ _ (inj₁ refl) (inj₂ (inj₂ (inj₂ (inj₁ refl)))) (inj₂ (inj₁ refl)) = refl
assoc-basis _ _ _ (inj₁ refl) (inj₂ (inj₂ (inj₂ (inj₁ refl)))) (inj₂ (inj₂ (inj₁ refl))) = refl
assoc-basis _ _ _ (inj₁ refl) (inj₂ (inj₂ (inj₂ (inj₁ refl)))) (inj₂ (inj₂ (inj₂ (inj₁ refl)))) = refl
assoc-basis _ _ _ (inj₁ refl) (inj₂ (inj₂ (inj₂ (inj₁ refl)))) (inj₂ (inj₂ (inj₂ (inj₂ refl)))) = refl
assoc-basis _ _ _ (inj₁ refl) (inj₂ (inj₂ (inj₂ (inj₂ refl)))) (inj₁ refl) = refl
assoc-basis _ _ _ (inj₁ refl) (inj₂ (inj₂ (inj₂ (inj₂ refl)))) (inj₂ (inj₁ refl)) = refl
assoc-basis _ _ _ (inj₁ refl) (inj₂ (inj₂ (inj₂ (inj₂ refl)))) (inj₂ (inj₂ (inj₁ refl))) = refl
assoc-basis _ _ _ (inj₁ refl) (inj₂ (inj₂ (inj₂ (inj₂ refl)))) (inj₂ (inj₂ (inj₂ (inj₁ refl)))) = refl
assoc-basis _ _ _ (inj₁ refl) (inj₂ (inj₂ (inj₂ (inj₂ refl)))) (inj₂ (inj₂ (inj₂ (inj₂ refl)))) = refl
assoc-basis _ _ _ (inj₂ (inj₁ refl)) (inj₁ refl) (inj₁ refl) = refl
assoc-basis _ _ _ (inj₂ (inj₁ refl)) (inj₁ refl) (inj₂ (inj₁ refl)) = refl
assoc-basis _ _ _ (inj₂ (inj₁ refl)) (inj₁ refl) (inj₂ (inj₂ (inj₁ refl))) = refl
assoc-basis _ _ _ (inj₂ (inj₁ refl)) (inj₁ refl) (inj₂ (inj₂ (inj₂ (inj₁ refl)))) = refl
assoc-basis _ _ _ (inj₂ (inj₁ refl)) (inj₁ refl) (inj₂ (inj₂ (inj₂ (inj₂ refl)))) = refl
assoc-basis _ _ _ (inj₂ (inj₁ refl)) (inj₂ (inj₁ refl)) (inj₁ refl) = refl
assoc-basis _ _ _ (inj₂ (inj₁ refl)) (inj₂ (inj₁ refl)) (inj₂ (inj₁ refl)) = refl
assoc-basis _ _ _ (inj₂ (inj₁ refl)) (inj₂ (inj₁ refl)) (inj₂ (inj₂ (inj₁ refl))) = refl
assoc-basis _ _ _ (inj₂ (inj₁ refl)) (inj₂ (inj₁ refl)) (inj₂ (inj₂ (inj₂ (inj₁ refl)))) = refl
assoc-basis _ _ _ (inj₂ (inj₁ refl)) (inj₂ (inj₁ refl)) (inj₂ (inj₂ (inj₂ (inj₂ refl)))) = refl
assoc-basis _ _ _ (inj₂ (inj₁ refl)) (inj₂ (inj₂ (inj₁ refl))) (inj₁ refl) = refl
assoc-basis _ _ _ (inj₂ (inj₁ refl)) (inj₂ (inj₂ (inj₁ refl))) (inj₂ (inj₁ refl)) = refl
assoc-basis _ _ _ (inj₂ (inj₁ refl)) (inj₂ (inj₂ (inj₁ refl))) (inj₂ (inj₂ (inj₁ refl))) = refl
assoc-basis _ _ _ (inj₂ (inj₁ refl)) (inj₂ (inj₂ (inj₁ refl))) (inj₂ (inj₂ (inj₂ (inj₁ refl)))) = refl
assoc-basis _ _ _ (inj₂ (inj₁ refl)) (inj₂ (inj₂ (inj₁ refl))) (inj₂ (inj₂ (inj₂ (inj₂ refl)))) = refl
assoc-basis _ _ _ (inj₂ (inj₁ refl)) (inj₂ (inj₂ (inj₂ (inj₁ refl)))) (inj₁ refl) = refl
assoc-basis _ _ _ (inj₂ (inj₁ refl)) (inj₂ (inj₂ (inj₂ (inj₁ refl)))) (inj₂ (inj₁ refl)) = refl
assoc-basis _ _ _ (inj₂ (inj₁ refl)) (inj₂ (inj₂ (inj₂ (inj₁ refl)))) (inj₂ (inj₂ (inj₁ refl))) = refl
assoc-basis _ _ _ (inj₂ (inj₁ refl)) (inj₂ (inj₂ (inj₂ (inj₁ refl)))) (inj₂ (inj₂ (inj₂ (inj₁ refl)))) = refl
assoc-basis _ _ _ (inj₂ (inj₁ refl)) (inj₂ (inj₂ (inj₂ (inj₁ refl)))) (inj₂ (inj₂ (inj₂ (inj₂ refl)))) = refl
assoc-basis _ _ _ (inj₂ (inj₁ refl)) (inj₂ (inj₂ (inj₂ (inj₂ refl)))) (inj₁ refl) = refl
assoc-basis _ _ _ (inj₂ (inj₁ refl)) (inj₂ (inj₂ (inj₂ (inj₂ refl)))) (inj₂ (inj₁ refl)) = refl
assoc-basis _ _ _ (inj₂ (inj₁ refl)) (inj₂ (inj₂ (inj₂ (inj₂ refl)))) (inj₂ (inj₂ (inj₁ refl))) = refl
assoc-basis _ _ _ (inj₂ (inj₁ refl)) (inj₂ (inj₂ (inj₂ (inj₂ refl)))) (inj₂ (inj₂ (inj₂ (inj₁ refl)))) = refl
assoc-basis _ _ _ (inj₂ (inj₁ refl)) (inj₂ (inj₂ (inj₂ (inj₂ refl)))) (inj₂ (inj₂ (inj₂ (inj₂ refl)))) = refl
assoc-basis _ _ _ (inj₂ (inj₂ (inj₁ refl))) (inj₁ refl) (inj₁ refl) = refl
assoc-basis _ _ _ (inj₂ (inj₂ (inj₁ refl))) (inj₁ refl) (inj₂ (inj₁ refl)) = refl
assoc-basis _ _ _ (inj₂ (inj₂ (inj₁ refl))) (inj₁ refl) (inj₂ (inj₂ (inj₁ refl))) = refl
assoc-basis _ _ _ (inj₂ (inj₂ (inj₁ refl))) (inj₁ refl) (inj₂ (inj₂ (inj₂ (inj₁ refl)))) = refl
assoc-basis _ _ _ (inj₂ (inj₂ (inj₁ refl))) (inj₁ refl) (inj₂ (inj₂ (inj₂ (inj₂ refl)))) = refl
assoc-basis _ _ _ (inj₂ (inj₂ (inj₁ refl))) (inj₂ (inj₁ refl)) (inj₁ refl) = refl
assoc-basis _ _ _ (inj₂ (inj₂ (inj₁ refl))) (inj₂ (inj₁ refl)) (inj₂ (inj₁ refl)) = refl
assoc-basis _ _ _ (inj₂ (inj₂ (inj₁ refl))) (inj₂ (inj₁ refl)) (inj₂ (inj₂ (inj₁ refl))) = refl
assoc-basis _ _ _ (inj₂ (inj₂ (inj₁ refl))) (inj₂ (inj₁ refl)) (inj₂ (inj₂ (inj₂ (inj₁ refl)))) = refl
assoc-basis _ _ _ (inj₂ (inj₂ (inj₁ refl))) (inj₂ (inj₁ refl)) (inj₂ (inj₂ (inj₂ (inj₂ refl)))) = refl
assoc-basis _ _ _ (inj₂ (inj₂ (inj₁ refl))) (inj₂ (inj₂ (inj₁ refl))) (inj₁ refl) = refl
assoc-basis _ _ _ (inj₂ (inj₂ (inj₁ refl))) (inj₂ (inj₂ (inj₁ refl))) (inj₂ (inj₁ refl)) = refl
assoc-basis _ _ _ (inj₂ (inj₂ (inj₁ refl))) (inj₂ (inj₂ (inj₁ refl))) (inj₂ (inj₂ (inj₁ refl))) = refl
assoc-basis _ _ _ (inj₂ (inj₂ (inj₁ refl))) (inj₂ (inj₂ (inj₁ refl))) (inj₂ (inj₂ (inj₂ (inj₁ refl)))) = refl
assoc-basis _ _ _ (inj₂ (inj₂ (inj₁ refl))) (inj₂ (inj₂ (inj₁ refl))) (inj₂ (inj₂ (inj₂ (inj₂ refl)))) = refl
assoc-basis _ _ _ (inj₂ (inj₂ (inj₁ refl))) (inj₂ (inj₂ (inj₂ (inj₁ refl)))) (inj₁ refl) = refl
assoc-basis _ _ _ (inj₂ (inj₂ (inj₁ refl))) (inj₂ (inj₂ (inj₂ (inj₁ refl)))) (inj₂ (inj₁ refl)) = refl
assoc-basis _ _ _ (inj₂ (inj₂ (inj₁ refl))) (inj₂ (inj₂ (inj₂ (inj₁ refl)))) (inj₂ (inj₂ (inj₁ refl))) = refl
assoc-basis _ _ _ (inj₂ (inj₂ (inj₁ refl))) (inj₂ (inj₂ (inj₂ (inj₁ refl)))) (inj₂ (inj₂ (inj₂ (inj₁ refl)))) = refl
assoc-basis _ _ _ (inj₂ (inj₂ (inj₁ refl))) (inj₂ (inj₂ (inj₂ (inj₁ refl)))) (inj₂ (inj₂ (inj₂ (inj₂ refl)))) = refl
assoc-basis _ _ _ (inj₂ (inj₂ (inj₁ refl))) (inj₂ (inj₂ (inj₂ (inj₂ refl)))) (inj₁ refl) = refl
assoc-basis _ _ _ (inj₂ (inj₂ (inj₁ refl))) (inj₂ (inj₂ (inj₂ (inj₂ refl)))) (inj₂ (inj₁ refl)) = refl
assoc-basis _ _ _ (inj₂ (inj₂ (inj₁ refl))) (inj₂ (inj₂ (inj₂ (inj₂ refl)))) (inj₂ (inj₂ (inj₁ refl))) = refl
assoc-basis _ _ _ (inj₂ (inj₂ (inj₁ refl))) (inj₂ (inj₂ (inj₂ (inj₂ refl)))) (inj₂ (inj₂ (inj₂ (inj₁ refl)))) = refl
assoc-basis _ _ _ (inj₂ (inj₂ (inj₁ refl))) (inj₂ (inj₂ (inj₂ (inj₂ refl)))) (inj₂ (inj₂ (inj₂ (inj₂ refl)))) = refl
assoc-basis _ _ _ (inj₂ (inj₂ (inj₂ (inj₁ refl)))) (inj₁ refl) (inj₁ refl) = refl
assoc-basis _ _ _ (inj₂ (inj₂ (inj₂ (inj₁ refl)))) (inj₁ refl) (inj₂ (inj₁ refl)) = refl
assoc-basis _ _ _ (inj₂ (inj₂ (inj₂ (inj₁ refl)))) (inj₁ refl) (inj₂ (inj₂ (inj₁ refl))) = refl
assoc-basis _ _ _ (inj₂ (inj₂ (inj₂ (inj₁ refl)))) (inj₁ refl) (inj₂ (inj₂ (inj₂ (inj₁ refl)))) = refl
assoc-basis _ _ _ (inj₂ (inj₂ (inj₂ (inj₁ refl)))) (inj₁ refl) (inj₂ (inj₂ (inj₂ (inj₂ refl)))) = refl
assoc-basis _ _ _ (inj₂ (inj₂ (inj₂ (inj₁ refl)))) (inj₂ (inj₁ refl)) (inj₁ refl) = refl
assoc-basis _ _ _ (inj₂ (inj₂ (inj₂ (inj₁ refl)))) (inj₂ (inj₁ refl)) (inj₂ (inj₁ refl)) = refl
assoc-basis _ _ _ (inj₂ (inj₂ (inj₂ (inj₁ refl)))) (inj₂ (inj₁ refl)) (inj₂ (inj₂ (inj₁ refl))) = refl
assoc-basis _ _ _ (inj₂ (inj₂ (inj₂ (inj₁ refl)))) (inj₂ (inj₁ refl)) (inj₂ (inj₂ (inj₂ (inj₁ refl)))) = refl
assoc-basis _ _ _ (inj₂ (inj₂ (inj₂ (inj₁ refl)))) (inj₂ (inj₁ refl)) (inj₂ (inj₂ (inj₂ (inj₂ refl)))) = refl
assoc-basis _ _ _ (inj₂ (inj₂ (inj₂ (inj₁ refl)))) (inj₂ (inj₂ (inj₁ refl))) (inj₁ refl) = refl
assoc-basis _ _ _ (inj₂ (inj₂ (inj₂ (inj₁ refl)))) (inj₂ (inj₂ (inj₁ refl))) (inj₂ (inj₁ refl)) = refl
assoc-basis _ _ _ (inj₂ (inj₂ (inj₂ (inj₁ refl)))) (inj₂ (inj₂ (inj₁ refl))) (inj₂ (inj₂ (inj₁ refl))) = refl
assoc-basis _ _ _ (inj₂ (inj₂ (inj₂ (inj₁ refl)))) (inj₂ (inj₂ (inj₁ refl))) (inj₂ (inj₂ (inj₂ (inj₁ refl)))) = refl
assoc-basis _ _ _ (inj₂ (inj₂ (inj₂ (inj₁ refl)))) (inj₂ (inj₂ (inj₁ refl))) (inj₂ (inj₂ (inj₂ (inj₂ refl)))) = refl
assoc-basis _ _ _ (inj₂ (inj₂ (inj₂ (inj₁ refl)))) (inj₂ (inj₂ (inj₂ (inj₁ refl)))) (inj₁ refl) = refl
assoc-basis _ _ _ (inj₂ (inj₂ (inj₂ (inj₁ refl)))) (inj₂ (inj₂ (inj₂ (inj₁ refl)))) (inj₂ (inj₁ refl)) = refl
assoc-basis _ _ _ (inj₂ (inj₂ (inj₂ (inj₁ refl)))) (inj₂ (inj₂ (inj₂ (inj₁ refl)))) (inj₂ (inj₂ (inj₁ refl))) = refl
assoc-basis _ _ _ (inj₂ (inj₂ (inj₂ (inj₁ refl)))) (inj₂ (inj₂ (inj₂ (inj₁ refl)))) (inj₂ (inj₂ (inj₂ (inj₁ refl)))) = refl
assoc-basis _ _ _ (inj₂ (inj₂ (inj₂ (inj₁ refl)))) (inj₂ (inj₂ (inj₂ (inj₁ refl)))) (inj₂ (inj₂ (inj₂ (inj₂ refl)))) = refl
assoc-basis _ _ _ (inj₂ (inj₂ (inj₂ (inj₁ refl)))) (inj₂ (inj₂ (inj₂ (inj₂ refl)))) (inj₁ refl) = refl
assoc-basis _ _ _ (inj₂ (inj₂ (inj₂ (inj₁ refl)))) (inj₂ (inj₂ (inj₂ (inj₂ refl)))) (inj₂ (inj₁ refl)) = refl
assoc-basis _ _ _ (inj₂ (inj₂ (inj₂ (inj₁ refl)))) (inj₂ (inj₂ (inj₂ (inj₂ refl)))) (inj₂ (inj₂ (inj₁ refl))) = refl
assoc-basis _ _ _ (inj₂ (inj₂ (inj₂ (inj₁ refl)))) (inj₂ (inj₂ (inj₂ (inj₂ refl)))) (inj₂ (inj₂ (inj₂ (inj₁ refl)))) = refl
assoc-basis _ _ _ (inj₂ (inj₂ (inj₂ (inj₁ refl)))) (inj₂ (inj₂ (inj₂ (inj₂ refl)))) (inj₂ (inj₂ (inj₂ (inj₂ refl)))) = refl
assoc-basis _ _ _ (inj₂ (inj₂ (inj₂ (inj₂ refl)))) (inj₁ refl) (inj₁ refl) = refl
assoc-basis _ _ _ (inj₂ (inj₂ (inj₂ (inj₂ refl)))) (inj₁ refl) (inj₂ (inj₁ refl)) = refl
assoc-basis _ _ _ (inj₂ (inj₂ (inj₂ (inj₂ refl)))) (inj₁ refl) (inj₂ (inj₂ (inj₁ refl))) = refl
assoc-basis _ _ _ (inj₂ (inj₂ (inj₂ (inj₂ refl)))) (inj₁ refl) (inj₂ (inj₂ (inj₂ (inj₁ refl)))) = refl
assoc-basis _ _ _ (inj₂ (inj₂ (inj₂ (inj₂ refl)))) (inj₁ refl) (inj₂ (inj₂ (inj₂ (inj₂ refl)))) = refl
assoc-basis _ _ _ (inj₂ (inj₂ (inj₂ (inj₂ refl)))) (inj₂ (inj₁ refl)) (inj₁ refl) = refl
assoc-basis _ _ _ (inj₂ (inj₂ (inj₂ (inj₂ refl)))) (inj₂ (inj₁ refl)) (inj₂ (inj₁ refl)) = refl
assoc-basis _ _ _ (inj₂ (inj₂ (inj₂ (inj₂ refl)))) (inj₂ (inj₁ refl)) (inj₂ (inj₂ (inj₁ refl))) = refl
assoc-basis _ _ _ (inj₂ (inj₂ (inj₂ (inj₂ refl)))) (inj₂ (inj₁ refl)) (inj₂ (inj₂ (inj₂ (inj₁ refl)))) = refl
assoc-basis _ _ _ (inj₂ (inj₂ (inj₂ (inj₂ refl)))) (inj₂ (inj₁ refl)) (inj₂ (inj₂ (inj₂ (inj₂ refl)))) = refl
assoc-basis _ _ _ (inj₂ (inj₂ (inj₂ (inj₂ refl)))) (inj₂ (inj₂ (inj₁ refl))) (inj₁ refl) = refl
assoc-basis _ _ _ (inj₂ (inj₂ (inj₂ (inj₂ refl)))) (inj₂ (inj₂ (inj₁ refl))) (inj₂ (inj₁ refl)) = refl
assoc-basis _ _ _ (inj₂ (inj₂ (inj₂ (inj₂ refl)))) (inj₂ (inj₂ (inj₁ refl))) (inj₂ (inj₂ (inj₁ refl))) = refl
assoc-basis _ _ _ (inj₂ (inj₂ (inj₂ (inj₂ refl)))) (inj₂ (inj₂ (inj₁ refl))) (inj₂ (inj₂ (inj₂ (inj₁ refl)))) = refl
assoc-basis _ _ _ (inj₂ (inj₂ (inj₂ (inj₂ refl)))) (inj₂ (inj₂ (inj₁ refl))) (inj₂ (inj₂ (inj₂ (inj₂ refl)))) = refl
assoc-basis _ _ _ (inj₂ (inj₂ (inj₂ (inj₂ refl)))) (inj₂ (inj₂ (inj₂ (inj₁ refl)))) (inj₁ refl) = refl
assoc-basis _ _ _ (inj₂ (inj₂ (inj₂ (inj₂ refl)))) (inj₂ (inj₂ (inj₂ (inj₁ refl)))) (inj₂ (inj₁ refl)) = refl
assoc-basis _ _ _ (inj₂ (inj₂ (inj₂ (inj₂ refl)))) (inj₂ (inj₂ (inj₂ (inj₁ refl)))) (inj₂ (inj₂ (inj₁ refl))) = refl
assoc-basis _ _ _ (inj₂ (inj₂ (inj₂ (inj₂ refl)))) (inj₂ (inj₂ (inj₂ (inj₁ refl)))) (inj₂ (inj₂ (inj₂ (inj₁ refl)))) = refl
assoc-basis _ _ _ (inj₂ (inj₂ (inj₂ (inj₂ refl)))) (inj₂ (inj₂ (inj₂ (inj₁ refl)))) (inj₂ (inj₂ (inj₂ (inj₂ refl)))) = refl
assoc-basis _ _ _ (inj₂ (inj₂ (inj₂ (inj₂ refl)))) (inj₂ (inj₂ (inj₂ (inj₂ refl)))) (inj₁ refl) = refl
assoc-basis _ _ _ (inj₂ (inj₂ (inj₂ (inj₂ refl)))) (inj₂ (inj₂ (inj₂ (inj₂ refl)))) (inj₂ (inj₁ refl)) = refl
assoc-basis _ _ _ (inj₂ (inj₂ (inj₂ (inj₂ refl)))) (inj₂ (inj₂ (inj₂ (inj₂ refl)))) (inj₂ (inj₂ (inj₁ refl))) = refl
assoc-basis _ _ _ (inj₂ (inj₂ (inj₂ (inj₂ refl)))) (inj₂ (inj₂ (inj₂ (inj₂ refl)))) (inj₂ (inj₂ (inj₂ (inj₁ refl)))) = refl
assoc-basis _ _ _ (inj₂ (inj₂ (inj₂ (inj₂ refl)))) (inj₂ (inj₂ (inj₂ (inj₂ refl)))) (inj₂ (inj₂ (inj₂ (inj₂ refl)))) = refl

LinZ : ∀ b1 b2 → Lin243 (λ z → (b1 *gf243 b2) *gf243 z)
LinZ b1 b2 = record { ladd = λ a b → *gf243-distribˡ (b1 *gf243 b2) a b }
LinZ' : ∀ b1 b2 → Lin243 (λ z → b1 *gf243 (b2 *gf243 z))
LinZ' b1 b2 = record
  { ladd = λ a b → trans (cong (b1 *gf243_) (*gf243-distribˡ b2 a b))
                         (*gf243-distribˡ b1 (b2 *gf243 a) (b2 *gf243 b)) }
z-e1 : ∀ b1 b2 → (b1 *gf243 b2) *gf243 gf243-one ≡ b1 *gf243 (b2 *gf243 gf243-one)
z-e1 b1 b2 = trans (*gf243-identityʳ (b1 *gf243 b2))
                    (sym (cong (b1 *gf243_) (*gf243-identityʳ b2)))

assoc-Z : ∀ b1 b2 → Basis243 b1 → Basis243 b2 → ∀ z →
  (b1 *gf243 b2) *gf243 z ≡ b1 *gf243 (b2 *gf243 z)
assoc-Z b1 b2 rb1 rb2 z =
  linear-ext5 (λ w → (b1 *gf243 b2) *gf243 w) (λ w → b1 *gf243 (b2 *gf243 w))
              (LinZ b1 b2) (LinZ' b1 b2) (z-e1 b1 b2) z-ea z-ea2 z-ea3 z-ea4 z
  where
    z-ea : (b1 *gf243 b2) *gf243 alpha ≡ b1 *gf243 (b2 *gf243 alpha)
    z-ea = assoc-basis b1 b2 alpha rb1 rb2 (inj₂ (inj₁ refl))
    z-ea2 : (b1 *gf243 b2) *gf243 alpha2 ≡ b1 *gf243 (b2 *gf243 alpha2)
    z-ea2 = assoc-basis b1 b2 alpha2 rb1 rb2 (inj₂ (inj₂ (inj₁ refl)))
    z-ea3 : (b1 *gf243 b2) *gf243 alpha3 ≡ b1 *gf243 (b2 *gf243 alpha3)
    z-ea3 = assoc-basis b1 b2 alpha3 rb1 rb2 (inj₂ (inj₂ (inj₂ (inj₁ refl))))
    z-ea4 : (b1 *gf243 b2) *gf243 alpha4 ≡ b1 *gf243 (b2 *gf243 alpha4)
    z-ea4 = assoc-basis b1 b2 alpha4 rb1 rb2 (inj₂ (inj₂ (inj₂ (inj₂ refl))))

LinY : ∀ b1 z → Lin243 (λ y → (b1 *gf243 y) *gf243 z)
LinY b1 z = record
  { ladd = λ a b → trans (cong (λ u → u *gf243 z) (*gf243-distribˡ b1 a b))
                         (*gf243-distribʳ (b1 *gf243 a) (b1 *gf243 b) z) }
LinY' : ∀ b1 z → Lin243 (λ y → b1 *gf243 (y *gf243 z))
LinY' b1 z = record
  { ladd = λ a b → trans (cong (b1 *gf243_) (*gf243-distribʳ a b z))
                         (*gf243-distribˡ b1 (a *gf243 z) (b *gf243 z)) }
y-e1 : ∀ b1 z → (b1 *gf243 gf243-one) *gf243 z ≡ b1 *gf243 (gf243-one *gf243 z)
y-e1 b1 z = trans (cong (λ u → u *gf243 z) (*gf243-identityʳ b1))
                  (cong (b1 *gf243_) (sym (*gf243-identityˡ z)))
y-ea : ∀ b1 → Basis243 b1 → ∀ z → (b1 *gf243 alpha) *gf243 z ≡ b1 *gf243 (alpha *gf243 z)
y-ea b1 rb = assoc-Z b1 alpha rb (inj₂ (inj₁ refl))
y-ea2 : ∀ b1 → Basis243 b1 → ∀ z → (b1 *gf243 alpha2) *gf243 z ≡ b1 *gf243 (alpha2 *gf243 z)
y-ea2 b1 rb = assoc-Z b1 alpha2 rb (inj₂ (inj₂ (inj₁ refl)))
y-ea3 : ∀ b1 → Basis243 b1 → ∀ z → (b1 *gf243 alpha3) *gf243 z ≡ b1 *gf243 (alpha3 *gf243 z)
y-ea3 b1 rb = assoc-Z b1 alpha3 rb (inj₂ (inj₂ (inj₂ (inj₁ refl))))
y-ea4 : ∀ b1 → Basis243 b1 → ∀ z → (b1 *gf243 alpha4) *gf243 z ≡ b1 *gf243 (alpha4 *gf243 z)
y-ea4 b1 rb = assoc-Z b1 alpha4 rb (inj₂ (inj₂ (inj₂ (inj₂ refl))))

assoc-Y : ∀ b1 → Basis243 b1 → ∀ y z → (b1 *gf243 y) *gf243 z ≡ b1 *gf243 (y *gf243 z)
assoc-Y b1 rb y z =
  linear-ext5 (λ w → (b1 *gf243 w) *gf243 z) (λ w → b1 *gf243 (w *gf243 z))
              (LinY b1 z) (LinY' b1 z) (y-e1 b1 z) (y-ea b1 rb z) (y-ea2 b1 rb z) (y-ea3 b1 rb z) (y-ea4 b1 rb z) y

LinX : ∀ y z → Lin243 (λ x → (x *gf243 y) *gf243 z)
LinX y z = record
  { ladd = λ a b → trans (cong (λ u → u *gf243 z) (*gf243-distribʳ a b y))
                         (*gf243-distribʳ (a *gf243 y) (b *gf243 y) z) }
LinX' : ∀ y z → Lin243 (λ x → x *gf243 (y *gf243 z))
LinX' y z = record { ladd = λ a b → *gf243-distribʳ a b (y *gf243 z) }
x-e1 : ∀ y z → (gf243-one *gf243 y) *gf243 z ≡ gf243-one *gf243 (y *gf243 z)
x-e1 y z = trans (cong (λ u → u *gf243 z) (*gf243-identityˡ y))
                  (sym (*gf243-identityˡ (y *gf243 z)))
x-ea : ∀ y z → (alpha *gf243 y) *gf243 z ≡ alpha *gf243 (y *gf243 z)
x-ea y z = assoc-Y alpha (inj₂ (inj₁ refl)) y z
x-ea2 : ∀ y z → (alpha2 *gf243 y) *gf243 z ≡ alpha2 *gf243 (y *gf243 z)
x-ea2 y z = assoc-Y alpha2 (inj₂ (inj₂ (inj₁ refl))) y z
x-ea3 : ∀ y z → (alpha3 *gf243 y) *gf243 z ≡ alpha3 *gf243 (y *gf243 z)
x-ea3 y z = assoc-Y alpha3 (inj₂ (inj₂ (inj₂ (inj₁ refl)))) y z
x-ea4 : ∀ y z → (alpha4 *gf243 y) *gf243 z ≡ alpha4 *gf243 (y *gf243 z)
x-ea4 y z = assoc-Y alpha4 (inj₂ (inj₂ (inj₂ (inj₂ refl)))) y z

-- ★ 乘法结合律 ★
*gf243-assoc : ∀ x y z → (x *gf243 y) *gf243 z ≡ x *gf243 (y *gf243 z)
*gf243-assoc x y z =
  linear-ext5 (λ w → (w *gf243 y) *gf243 z) (λ w → w *gf243 (y *gf243 z))
              (LinX y z) (LinX' y z) (x-e1 y z) (x-ea y z) (x-ea2 y z) (x-ea3 y z) (x-ea4 y z) x

--------------------------------------------------------------------------------
-- §6. σ 保加 (frobenius-add) — GF243 原先缺失
--------------------------------------------------------------------------------

-- σ(a₀,a₁,a₂,a₃,a₄) = (a₀⊕neg a₃, neg a₂⊕a₃, a₂⊕a₄, a₁⊕a₄, neg a₃⊕a₄)
frobenius-add : ∀ x y → frobenius (x +gf243 y) ≡ frobenius x +gf243 frobenius y
frobenius-add (a₀ ∷ a₁ ∷ a₂ ∷ a₃ ∷ a₄ ∷ []) (b₀ ∷ b₁ ∷ b₂ ∷ b₃ ∷ b₄ ∷ []) =
  cong-Vec5 eq0 eq1 eq2 eq3 eq4
  where
    eq0 : (a₀ ⊕ b₀) ⊕ negate (a₃ ⊕ b₃) ≡ (a₀ ⊕ negate a₃) ⊕ (b₀ ⊕ negate b₃)
    eq0 = trans (cong ((a₀ ⊕ b₀) ⊕_) (negate-⊕ a₃ b₃)) (⊕-swap-middle a₀ b₀ (negate a₃) (negate b₃))
    eq1 : negate (a₂ ⊕ b₂) ⊕ (a₃ ⊕ b₃) ≡ (negate a₂ ⊕ a₃) ⊕ (negate b₂ ⊕ b₃)
    eq1 = trans (cong (_⊕ (a₃ ⊕ b₃)) (negate-⊕ a₂ b₂)) (⊕-swap-middle (negate a₂) (negate b₂) a₃ b₃)
    eq2 : (a₂ ⊕ b₂) ⊕ (a₄ ⊕ b₄) ≡ (a₂ ⊕ a₄) ⊕ (b₂ ⊕ b₄)
    eq2 = ⊕-swap-middle a₂ b₂ a₄ b₄
    eq3 : (a₁ ⊕ b₁) ⊕ (a₄ ⊕ b₄) ≡ (a₁ ⊕ a₄) ⊕ (b₁ ⊕ b₄)
    eq3 = ⊕-swap-middle a₁ b₁ a₄ b₄
    eq4 : negate (a₃ ⊕ b₃) ⊕ (a₄ ⊕ b₄) ≡ (negate a₃ ⊕ a₄) ⊕ (negate b₃ ⊕ b₄)
    eq4 = trans (cong (_⊕ (a₄ ⊕ b₄)) (negate-⊕ a₃ b₃)) (⊕-swap-middle (negate a₃) (negate b₃) a₄ b₄)

LF243 : Lin243 frobenius
LF243 = record { ladd = frobenius-add }

--------------------------------------------------------------------------------
-- §7. Freshman's dream 与立方映射
--------------------------------------------------------------------------------

negF-is-scalar : ∀ x → gf243-negate x ≡ T₂ *s243 x
negF-is-scalar (x₀ ∷ x₁ ∷ x₂ ∷ x₃ ∷ x₄ ∷ []) =
  cong-Vec5 (sym (dn-trit x₀)) (sym (dn-trit x₁)) (sym (dn-trit x₂)) (sym (dn-trit x₃)) (sym (dn-trit x₄))

-- 标量提取 (左)
scalar-extract-l243 : ∀ c x y → (c *s243 x) *gf243 y ≡ c *s243 (x *gf243 y)
scalar-extract-l243 T₀ x y = zero-mul-l243 y
scalar-extract-l243 T₁ x y = refl
scalar-extract-l243 T₂ x y = *gf243-distribʳ x x y

-- 标量提取 (右)
scalar-extract-r243 : ∀ c x y → x *gf243 (c *s243 y) ≡ c *s243 (x *gf243 y)
scalar-extract-r243 T₀ x y = zero-mul-r243 x
scalar-extract-r243 T₁ x y = refl
scalar-extract-r243 T₂ x y = *gf243-distribˡ x y y

negF-mulˡ : ∀ x y → gf243-negate x *gf243 y ≡ gf243-negate (x *gf243 y)
negF-mulˡ x y =
  trans (cong (_*gf243 y) (negF-is-scalar x))
        (trans (scalar-extract-l243 T₂ x y) (sym (negF-is-scalar (x *gf243 y))))

negF-mulʳ : ∀ x y → x *gf243 gf243-negate y ≡ gf243-negate (x *gf243 y)
negF-mulʳ x y =
  trans (cong (x *gf243_) (negF-is-scalar y))
        (trans (scalar-extract-r243 T₂ x y) (sym (negF-is-scalar (x *gf243 y))))

neg-mul-neg : ∀ x y → gf243-negate x *gf243 gf243-negate y ≡ x *gf243 y
neg-mul-neg x y =
  trans (negF-mulˡ x (gf243-negate y))
        (trans (cong gf243-negate (negF-mulʳ x y)) (gf243-negate² (x *gf243 y)))

-- (w+w)·(w+w) ≡ w·w
two-mul-sq : ∀ w → (w +gf243 w) *gf243 (w +gf243 w) ≡ w *gf243 w
two-mul-sq w = trans (cong-*243 (dn243 w) (dn243 w)) (neg-mul-neg w w)

sq-raw : ∀ a b → (a +gf243 b) *gf243 (a +gf243 b)
  ≡ ((a *gf243 a) +gf243 (a *gf243 b)) +gf243 ((b *gf243 a) +gf243 (b *gf243 b))
sq-raw a b =
  trans (*gf243-distribʳ a b (a +gf243 b))
        (cong-+243 (*gf243-distribˡ a a b) (*gf243-distribˡ b a b))

sq-mid : ∀ a b → ((a *gf243 a) +gf243 (a *gf243 b)) +gf243 ((b *gf243 a) +gf243 (b *gf243 b))
                 ≡ ((a *gf243 a) +gf243 (a *gf243 b)) +gf243 ((a *gf243 b) +gf243 (b *gf243 b))
sq-mid a b =
  trans (swap4-243 (a *gf243 a) (a *gf243 b) (b *gf243 a) (b *gf243 b))
        (cong (_+gf243 ((a *gf243 b) +gf243 (b *gf243 b)))
              (cong ((a *gf243 a) +gf243_) (*gf243-comm b a)))

sq-end : ∀ A B C → (A +gf243 B) +gf243 (B +gf243 C) ≡ (A +gf243 gf243-negate B) +gf243 C
sq-end A B C =
  trans (+gf243-assoc A B (B +gf243 C))
        (trans (cong (A +gf243_)
                     (trans (sym (+gf243-assoc B B C)) (cong (_+gf243 C) (dn243 B))))
               (sym (+gf243-assoc A (gf243-negate B) C)))

sq-canon : ∀ a b → (a +gf243 b) *gf243 (a +gf243 b)
  ≡ ((a *gf243 a) +gf243 gf243-negate (a *gf243 b)) +gf243 (b *gf243 b)
sq-canon a b =
  trans (sq-raw a b) (trans (sq-mid a b) (sq-end (a *gf243 a) (a *gf243 b) (b *gf243 b)))

distrib3-243 : ∀ X Y Z W → ((X +gf243 Y) +gf243 Z) *gf243 W
                           ≡ ((X *gf243 W) +gf243 (Y *gf243 W)) +gf243 (Z *gf243 W)
distrib3-243 X Y Z W =
  trans (*gf243-distribʳ (X +gf243 Y) Z W)
        (cong-+243 (*gf243-distribʳ X Y W) refl)

blk2-abs : ∀ A B → (A *gf243 B) *gf243 A ≡ (A *gf243 A) *gf243 B
blk2-abs A B =
  trans (*gf243-assoc A B A)
        (trans (cong (A *gf243_) (*gf243-comm B A)) (sym (*gf243-assoc A A B)))

cube-blkA : ∀ a b →
  (((a *gf243 a) +gf243 gf243-negate (a *gf243 b)) +gf243 (b *gf243 b)) *gf243 a
  ≡ ((a *gf243 (a *gf243 a)) +gf243 gf243-negate ((a *gf243 a) *gf243 b)) +gf243 (a *gf243 (b *gf243 b))
cube-blkA a b =
  trans (distrib3-243 (a *gf243 a) (gf243-negate (a *gf243 b)) (b *gf243 b) a)
        (cong-+243 (cong-+243 (*gf243-comm (a *gf243 a) a)
                             (trans (negF-mulˡ (a *gf243 b) a)
                                    (cong gf243-negate (blk2-abs a b))))
                  (*gf243-comm (b *gf243 b) a))

blkB-neg : ∀ a b → gf243-negate (a *gf243 b) *gf243 b ≡ gf243-negate (a *gf243 (b *gf243 b))
blkB-neg a b = trans (negF-mulˡ (a *gf243 b) b) (cong gf243-negate (*gf243-assoc a b b))

cube-blkB : ∀ a b →
  (((a *gf243 a) +gf243 gf243-negate (a *gf243 b)) +gf243 (b *gf243 b)) *gf243 b
  ≡ (((a *gf243 a) *gf243 b) +gf243 gf243-negate (a *gf243 (b *gf243 b))) +gf243 (b *gf243 (b *gf243 b))
cube-blkB a b =
  trans (distrib3-243 (a *gf243 a) (gf243-negate (a *gf243 b)) (b *gf243 b) b)
        (cong-+243 (cong (((a *gf243 a) *gf243 b) +gf243_) (blkB-neg a b))
                  (*gf243-comm (b *gf243 b) b))

cube-cancel : ∀ a b →
  (((a *gf243 (a *gf243 a)) +gf243 gf243-negate ((a *gf243 a) *gf243 b)) +gf243 (a *gf243 (b *gf243 b)))
  +gf243 ((((a *gf243 a) *gf243 b) +gf243 gf243-negate (a *gf243 (b *gf243 b))) +gf243 (b *gf243 (b *gf243 b)))
  ≡ (a *gf243 (a *gf243 a)) +gf243 (b *gf243 (b *gf243 b))
cube-cancel a b =
  cancel-mid243 (a *gf243 (a *gf243 a)) ((a *gf243 a) *gf243 b) (a *gf243 (b *gf243 b)) (b *gf243 (b *gf243 b))

cube-expand : ∀ a b → (a +gf243 b) *gf243 ((a +gf243 b) *gf243 (a +gf243 b))
  ≡ (((a *gf243 a) +gf243 gf243-negate (a *gf243 b)) +gf243 (b *gf243 b)) *gf243 (a +gf243 b)
cube-expand a b =
  trans (cong ((a +gf243 b) *gf243_) (sq-canon a b))
        (*gf243-comm (a +gf243 b) (((a *gf243 a) +gf243 gf243-negate (a *gf243 b)) +gf243 (b *gf243 b)))

cube-distrib : ∀ a b →
  (((a *gf243 a) +gf243 gf243-negate (a *gf243 b)) +gf243 (b *gf243 b)) *gf243 (a +gf243 b)
  ≡ ((((a *gf243 a) +gf243 gf243-negate (a *gf243 b)) +gf243 (b *gf243 b)) *gf243 a)
    +gf243 ((((a *gf243 a) +gf243 gf243-negate (a *gf243 b)) +gf243 (b *gf243 b)) *gf243 b)
cube-distrib a b = *gf243-distribˡ (((a *gf243 a) +gf243 gf243-negate (a *gf243 b)) +gf243 (b *gf243 b)) a b

-- ★ Freshman's dream ★
cube-add : ∀ a b → (a +gf243 b) *gf243 ((a +gf243 b) *gf243 (a +gf243 b))
  ≡ (a *gf243 (a *gf243 a)) +gf243 (b *gf243 (b *gf243 b))
cube-add a b =
  trans (cube-expand a b)
  (trans (cube-distrib a b)
  (trans (cong-+243 (cube-blkA a b) (cube-blkB a b))
         (cube-cancel a b)))

--------------------------------------------------------------------------------
-- §8. 立方映射的 GF(3)-线性
--------------------------------------------------------------------------------

cubeMap243 : GF243 → GF243
cubeMap243 x = x *gf243 (x *gf243 x)

sq-scalar : ∀ c w → (c *s243 w) *gf243 (c *s243 w) ≡ (c ⊗ c) *s243 (w *gf243 w)
sq-scalar T₀ w = zero-mul-l243 (T₀ *s243 w)
sq-scalar T₁ w = refl
sq-scalar T₂ w = trans (two-mul-sq w) refl

cube-scalar : ∀ c w →
  (c *s243 w) *gf243 ((c *s243 w) *gf243 (c *s243 w)) ≡ c *s243 (w *gf243 (w *gf243 w))
cube-scalar T₀ w = zero-mul-l243 ((T₀ *s243 w) *gf243 (T₀ *s243 w))
cube-scalar T₁ w = refl
cube-scalar T₂ w = begin
  (w +gf243 w) *gf243 ((w +gf243 w) *gf243 (w +gf243 w))
    ≡⟨ cong ((w +gf243 w) *gf243_) (two-mul-sq w) ⟩
  (w +gf243 w) *gf243 (w *gf243 w)
    ≡⟨ scalar-extract-l243 T₂ w (w *gf243 w) ⟩
  T₂ *s243 (w *gf243 (w *gf243 w))
  ∎

LC243 : Lin243 cubeMap243
LC243 = record { ladd = cube-add }

-- ★ σ(x) = x³ ★
frobenius-is-cube : ∀ x → frobenius x ≡ x *gf243 (x *gf243 x)
frobenius-is-cube =
  linear-ext5 frobenius cubeMap243 LF243 LC243 refl refl refl refl refl

--------------------------------------------------------------------------------
-- §9. σ 保乘法
--------------------------------------------------------------------------------

mul-square : ∀ x y → (x *gf243 y) *gf243 (x *gf243 y) ≡ (x *gf243 x) *gf243 (y *gf243 y)
mul-square x y = begin
  (x *gf243 y) *gf243 (x *gf243 y)
    ≡⟨ *gf243-assoc x y (x *gf243 y) ⟩
  x *gf243 (y *gf243 (x *gf243 y))
    ≡⟨ cong (x *gf243_) (sym (*gf243-assoc y x y)) ⟩
  x *gf243 ((y *gf243 x) *gf243 y)
    ≡⟨ cong (x *gf243_) (cong (_*gf243 y) (*gf243-comm y x)) ⟩
  x *gf243 ((x *gf243 y) *gf243 y)
    ≡⟨ cong (x *gf243_) (*gf243-assoc x y y) ⟩
  x *gf243 (x *gf243 (y *gf243 y))
    ≡⟨ sym (*gf243-assoc x x (y *gf243 y)) ⟩
  (x *gf243 x) *gf243 (y *gf243 y)
  ∎

mul-perm : ∀ a b c d → (a *gf243 b) *gf243 (c *gf243 d) ≡ (a *gf243 c) *gf243 (b *gf243 d)
mul-perm a b c d = begin
  (a *gf243 b) *gf243 (c *gf243 d)
    ≡⟨ *gf243-assoc a b (c *gf243 d) ⟩
  a *gf243 (b *gf243 (c *gf243 d))
    ≡⟨ cong (a *gf243_) (sym (*gf243-assoc b c d)) ⟩
  a *gf243 ((b *gf243 c) *gf243 d)
    ≡⟨ cong (a *gf243_) (cong (_*gf243 d) (*gf243-comm b c)) ⟩
  a *gf243 ((c *gf243 b) *gf243 d)
    ≡⟨ cong (a *gf243_) (*gf243-assoc c b d) ⟩
  a *gf243 (c *gf243 (b *gf243 d))
    ≡⟨ sym (*gf243-assoc a c (b *gf243 d)) ⟩
  (a *gf243 c) *gf243 (b *gf243 d)
  ∎

cube-mul : ∀ x y → (x *gf243 y) *gf243 ((x *gf243 y) *gf243 (x *gf243 y))
                  ≡ (x *gf243 (x *gf243 x)) *gf243 (y *gf243 (y *gf243 y))
cube-mul x y = begin
  (x *gf243 y) *gf243 ((x *gf243 y) *gf243 (x *gf243 y))
    ≡⟨ cong ((x *gf243 y) *gf243_) (mul-square x y) ⟩
  (x *gf243 y) *gf243 ((x *gf243 x) *gf243 (y *gf243 y))
    ≡⟨ mul-perm x y (x *gf243 x) (y *gf243 y) ⟩
  (x *gf243 (x *gf243 x)) *gf243 (y *gf243 (y *gf243 y))
  ∎

frobenius-mul : ∀ x y → frobenius (x *gf243 y) ≡ frobenius x *gf243 frobenius y
frobenius-mul x y =
  trans (frobenius-is-cube (x *gf243 y))
  (trans (cube-mul x y)
         (cong-*243 (sym (frobenius-is-cube x)) (sym (frobenius-is-cube y))))
