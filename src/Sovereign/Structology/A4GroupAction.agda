{-# OPTIONS --rewriting --cubical --guardedness #-}

-- | Sovereign.Structology.A4GroupAction
-- A₄ 群作用 — 正则表示、消去律、传递/自由、非交换（与十二进制严格分离）
--
-- A₄ = 正四面体旋转群 = 交错群 Alt(4)，12 阶非交换，是三代费米子对称群。
-- 结构: A₄ ≅ V₄ ⋊ C₃（半直积，非直积）
--   · V₄ = 克莱因四元群（3 个二重对换 Flip + 单位元 Id，A₄ 的正规子群）
--   · C₃ = 商群 A₄/V₄（三进制归零的三角循环）
--
-- ⚠️ 概念分离（防「传统污染」）:
--   本模块只研究 A₄ 自身的群作用，不引用十二进制（Duodec/Z/12 的联合周期）。
--   A₄ 与 Z/12 同为 12 阶但不同构：A₄ 非交换，Z/12 交换。
--   禁挂「A₄ ≅ Z/12」或「A₄ 是十二进制」，禁「对偶」一词——只说「不同构」。
--   唯一的交叉是 §5 的「无单射同态」否定性引理（证明不能嵌入，而非建立同构）。
--
-- 核心定理（0 postulate，L2 符号证明 + 有限穷举兜底）:
--   §1  消去律（右/左）—— 由逆元 + 结合律导出，全称符号证明
--   §2  正则作用（左乘）自由 + 传递 —— Cayley 正则表示实例
--   §3  正则表示忠实（作用在单位元处决定群元）
--   §4  V₄ 子群注记（二重对换 Flip 均为 2 阶）—— V₄ ⋊ C₃ 的 V₄
--   §5  A₄ 非交换（两个 3-循环/对换不交换的逐点见证）
--   §6  A₄ → Z/12 无单射同态（非交换 vs 交换，交换性矛盾）

module Sovereign.Structology.A4GroupAction where

open import Data.Nat using (ℕ; _*_)
open import Data.Fin using (Fin; zero; suc)
open import Data.Empty using (⊥)
open import Data.Product.Base using (Σ; _,_; _×_; Σ-syntax; proj₁; proj₂)
open import Data.Unit using (⊤; tt)
-- proof-engineer 模式6: 与 A4Group.agda 同源, 用 Cubical Path 相等 (非 PropEq),
-- 使 assoc/identity 的 Cubical _≡_ 透传, 避免跨库 UnequalTerms (A4 vs A4 i)。
open import Cubical.Foundations.Prelude using (_≡_; refl; cong; sym; _∙_; subst)

open import Sovereign.Structology.A4Group
  using (A4; Id; Rot; Flip; perm; _⊗_; assoc; identity)
open import Sovereign.Algebra.Duodecimal
  using (Duodec; d0; d1; d2; d3; d4; d5; d6; d7; d8; d9; d10; d11; _+12_)

--------------------------------------------------------------------------------
-- §1. 消去律 —— 由逆元 + 结合律导出（全称符号证明，非穷举）
--------------------------------------------------------------------------------

-- 逆元（扁平类型 12 case，与 A4Group.inverse 同构；避开 Σ 宇宙投影元变量）
a4-inv : A4 → A4
a4-inv Id                  = Id
a4-inv (Rot i zero)        = Rot i (suc zero)
a4-inv (Rot i (suc zero))  = Rot i zero
a4-inv (Flip j)            = Flip j

-- 右逆: x ⊗ a4-inv x ≡ Id（12 case refl）
a4-inv-right : ∀ x → x ⊗ a4-inv x ≡ Id
a4-inv-right Id = refl
a4-inv-right (Rot zero zero) = refl
a4-inv-right (Rot zero (suc zero)) = refl
a4-inv-right (Rot (suc zero) zero) = refl
a4-inv-right (Rot (suc zero) (suc zero)) = refl
a4-inv-right (Rot (suc (suc zero)) zero) = refl
a4-inv-right (Rot (suc (suc zero)) (suc zero)) = refl
a4-inv-right (Rot (suc (suc (suc zero))) zero) = refl
a4-inv-right (Rot (suc (suc (suc zero))) (suc zero)) = refl
a4-inv-right (Flip zero) = refl
a4-inv-right (Flip (suc zero)) = refl
a4-inv-right (Flip (suc (suc zero))) = refl

-- 左逆: a4-inv x ⊗ x ≡ Id（12 case refl）
a4-inv-left : ∀ x → a4-inv x ⊗ x ≡ Id
a4-inv-left Id = refl
a4-inv-left (Rot zero zero) = refl
a4-inv-left (Rot zero (suc zero)) = refl
a4-inv-left (Rot (suc zero) zero) = refl
a4-inv-left (Rot (suc zero) (suc zero)) = refl
a4-inv-left (Rot (suc (suc zero)) zero) = refl
a4-inv-left (Rot (suc (suc zero)) (suc zero)) = refl
a4-inv-left (Rot (suc (suc (suc zero))) zero) = refl
a4-inv-left (Rot (suc (suc (suc zero))) (suc zero)) = refl
a4-inv-left (Flip zero) = refl
a4-inv-left (Flip (suc zero)) = refl
a4-inv-left (Flip (suc (suc zero))) = refl

-- 右消去: g ⊗ a ≡ a ⟹ g ≡ Id
right-cancel : ∀ g a → g ⊗ a ≡ a → g ≡ Id
right-cancel g a eq =
  sym (proj₂ (identity g)) ∙
  cong (g ⊗_) (sym (a4-inv-right a)) ∙
  sym (assoc g a (a4-inv a)) ∙
  cong (_⊗ a4-inv a) eq ∙
  a4-inv-right a

-- 左消去: a ⊗ g ≡ a ⟹ g ≡ Id
left-cancel : ∀ g a → a ⊗ g ≡ a → g ≡ Id
left-cancel g a eq =
  sym (proj₁ (identity g)) ∙
  cong (_⊗ g) (sym (a4-inv-left a)) ∙
  assoc (a4-inv a) a g ∙
  cong (a4-inv a ⊗_) eq ∙
  a4-inv-left a

--------------------------------------------------------------------------------
-- §2. 正则作用（左乘）: 自由 + 传递 —— Cayley 正则表示实例
--------------------------------------------------------------------------------

-- 自由作用: g ⊗ x ≡ x ⟹ g ≡ Id（稳定子平凡）
regular-free : ∀ g x → g ⊗ x ≡ x → g ≡ Id
regular-free = right-cancel

-- 传递作用: 任意 x y，存在 g 使 g ⊗ x ≡ y（取 g = y ⊗ x⁻¹）
regular-transitive : ∀ x y → Σ A4 (λ g → g ⊗ x ≡ y)
regular-transitive x y = g , eq
  where
    g = y ⊗ a4-inv x
    eq : g ⊗ x ≡ y
    eq = assoc y (a4-inv x) x ∙ cong (y ⊗_) (a4-inv-left x) ∙ proj₂ (identity y)

-- 轨道-稳定子（数值注记）: |A₄| = |orbit| · |stab| = 12 · 1 = 12
orbit-stabilizer-identity : 12 ≡ 12 * 1
orbit-stabilizer-identity = refl

--------------------------------------------------------------------------------
-- §3. 正则表示忠实 —— 作用在单位元处决定群元
--------------------------------------------------------------------------------

-- 左乘作用在 Id 处忠实: g ⊗ Id ≡ h ⊗ Id ⟹ g ≡ h
regular-faithful : ∀ g h → g ⊗ Id ≡ h ⊗ Id → g ≡ h
regular-faithful g h p =
  sym (proj₂ (identity g)) ∙ p ∙ proj₂ (identity h)

--------------------------------------------------------------------------------
-- §4. V₄ 子群注记 —— 二重对换 Flip 均为 2 阶（V₄ ⋊ C₃ 的 V₄）
--------------------------------------------------------------------------------

-- 每个 Flip（二重对换）自逆、阶 2: Flip j ⊗ Flip j ≡ Id（∀ j 全称, 3 case 穷举域 Fin 3）
flip-order-2 : ∀ j → Flip j ⊗ Flip j ≡ Id
flip-order-2 zero                   = refl
flip-order-2 (suc zero)             = refl
flip-order-2 (suc (suc zero))       = refl

-- Rot 恒非单位元（∀ i d 全称符号, subst 携真值法: Rot 构子谓词 ⊤, Id 谓词 ⊥）
rot-not-id : ∀ i d → Rot i d ≡ Id → ⊥
rot-not-id i d p = subst isRot p tt
  where
    isRot : A4 → Set
    isRot Id          = ⊥
    isRot (Rot _ _)   = ⊤
    isRot (Flip _)    = ⊥

-- 8 个 Rot 均非 2 阶: Rot i d ⊗ Rot i d ≡ Rot i (1-d) ≢ Id
-- （8 case 穷举域 Fin 4 × Fin 2; 每次归约后借 rot-not-id 否定）
-- 与 flip-order-2 及 Id 合成 A₄ 的 2 阶元分类: 恰为 V₄ = {Id, Flip 0, Flip 1, Flip 2}，
-- 8 个 Rot 为 3 阶 —— 这正是 A₄ ≅ V₄ ⋊ C₃ 的元素阶结构 (1, 2,2,2, 3,…,3)。
rot-not-order-2 : ∀ i d → Rot i d ⊗ Rot i d ≡ Id → ⊥
rot-not-order-2 zero zero p = rot-not-id zero (suc zero) p
rot-not-order-2 zero (suc zero) p = rot-not-id zero zero p
rot-not-order-2 (suc zero) zero p = rot-not-id (suc zero) (suc zero) p
rot-not-order-2 (suc zero) (suc zero) p = rot-not-id (suc zero) zero p
rot-not-order-2 (suc (suc zero)) zero p = rot-not-id (suc (suc zero)) (suc zero) p
rot-not-order-2 (suc (suc zero)) (suc zero) p = rot-not-id (suc (suc zero)) zero p
rot-not-order-2 (suc (suc (suc zero))) zero p = rot-not-id (suc (suc (suc zero))) (suc zero) p
rot-not-order-2 (suc (suc (suc zero))) (suc zero) p = rot-not-id (suc (suc (suc zero))) zero p

--------------------------------------------------------------------------------
-- §5. A₄ 非交换 —— 两个 3-循环/对换不交换的逐点见证
--------------------------------------------------------------------------------

-- perm 在顶点 0 处的取值（非交换见证）
-- Rot zero zero = (1 2 3), Flip zero = (0 1)(2 3)
rot-flip-at-zero : perm (Rot zero zero ⊗ Flip zero) zero ≡ suc (suc zero)
rot-flip-at-zero = refl

flip-rot-at-zero : perm (Flip zero ⊗ Rot zero zero) zero ≡ suc zero
flip-rot-at-zero = refl

-- Fin 4 构造子互异（Cubical 下 Path 空性检查受限, 用 subst 携真值法: ⊤ → ⊥）
fin4-2≢1 : suc (suc zero) ≡ suc zero → ⊥
fin4-2≢1 p = subst P p tt
  where
    P : Fin 4 → Set
    P zero                   = ⊥
    P (suc zero)             = ⊥
    P (suc (suc zero))       = ⊤
    P (suc (suc (suc zero))) = ⊥

-- A₄ 非交换: Rot 0 0 ⊗ Flip 0 ≠ Flip 0 ⊗ Rot 0 0
non-abelian-witness : Rot zero zero ⊗ Flip zero ≡ Flip zero ⊗ Rot zero zero → ⊥
non-abelian-witness p = fin4-2≢1 q
  where
    q : suc (suc zero) ≡ suc zero
    q = sym rot-flip-at-zero ∙ cong (λ g → perm g zero) p ∙ flip-rot-at-zero

-- 全称否定: A₄ 不满足全称交换律（L2: 由反例 witness 经符号推理导出 ∀ 层的否定）
not-commutative : (∀ x y → x ⊗ y ≡ y ⊗ x) → ⊥
not-commutative all-comm = non-abelian-witness (all-comm (Rot zero zero) (Flip zero))

--------------------------------------------------------------------------------
-- §6. A₄ → Z/12 无单射同态 —— 非交换 vs 交换，交换性矛盾
--------------------------------------------------------------------------------

-- Z/12 加法交换律 (Cubical Path 版本, 144 case refl; 由
-- /home/yanli/work/math cpp 生成验证。PropEq 的 +12-comm 与 Path 宇宙层级
-- 不兼容, 故本地重证, 内容与 Duodecim.+12-comm 一致)
+12-commᶜ : ∀ x y → x +12 y ≡ y +12 x
+12-commᶜ d0 d0 = refl; +12-commᶜ d0 d1 = refl; +12-commᶜ d0 d2 = refl; +12-commᶜ d0 d3 = refl; +12-commᶜ d0 d4 = refl; +12-commᶜ d0 d5 = refl; +12-commᶜ d0 d6 = refl; +12-commᶜ d0 d7 = refl; +12-commᶜ d0 d8 = refl; +12-commᶜ d0 d9 = refl; +12-commᶜ d0 d10 = refl; +12-commᶜ d0 d11 = refl
+12-commᶜ d1 d0 = refl; +12-commᶜ d1 d1 = refl; +12-commᶜ d1 d2 = refl; +12-commᶜ d1 d3 = refl; +12-commᶜ d1 d4 = refl; +12-commᶜ d1 d5 = refl; +12-commᶜ d1 d6 = refl; +12-commᶜ d1 d7 = refl; +12-commᶜ d1 d8 = refl; +12-commᶜ d1 d9 = refl; +12-commᶜ d1 d10 = refl; +12-commᶜ d1 d11 = refl
+12-commᶜ d2 d0 = refl; +12-commᶜ d2 d1 = refl; +12-commᶜ d2 d2 = refl; +12-commᶜ d2 d3 = refl; +12-commᶜ d2 d4 = refl; +12-commᶜ d2 d5 = refl; +12-commᶜ d2 d6 = refl; +12-commᶜ d2 d7 = refl; +12-commᶜ d2 d8 = refl; +12-commᶜ d2 d9 = refl; +12-commᶜ d2 d10 = refl; +12-commᶜ d2 d11 = refl
+12-commᶜ d3 d0 = refl; +12-commᶜ d3 d1 = refl; +12-commᶜ d3 d2 = refl; +12-commᶜ d3 d3 = refl; +12-commᶜ d3 d4 = refl; +12-commᶜ d3 d5 = refl; +12-commᶜ d3 d6 = refl; +12-commᶜ d3 d7 = refl; +12-commᶜ d3 d8 = refl; +12-commᶜ d3 d9 = refl; +12-commᶜ d3 d10 = refl; +12-commᶜ d3 d11 = refl
+12-commᶜ d4 d0 = refl; +12-commᶜ d4 d1 = refl; +12-commᶜ d4 d2 = refl; +12-commᶜ d4 d3 = refl; +12-commᶜ d4 d4 = refl; +12-commᶜ d4 d5 = refl; +12-commᶜ d4 d6 = refl; +12-commᶜ d4 d7 = refl; +12-commᶜ d4 d8 = refl; +12-commᶜ d4 d9 = refl; +12-commᶜ d4 d10 = refl; +12-commᶜ d4 d11 = refl
+12-commᶜ d5 d0 = refl; +12-commᶜ d5 d1 = refl; +12-commᶜ d5 d2 = refl; +12-commᶜ d5 d3 = refl; +12-commᶜ d5 d4 = refl; +12-commᶜ d5 d5 = refl; +12-commᶜ d5 d6 = refl; +12-commᶜ d5 d7 = refl; +12-commᶜ d5 d8 = refl; +12-commᶜ d5 d9 = refl; +12-commᶜ d5 d10 = refl; +12-commᶜ d5 d11 = refl
+12-commᶜ d6 d0 = refl; +12-commᶜ d6 d1 = refl; +12-commᶜ d6 d2 = refl; +12-commᶜ d6 d3 = refl; +12-commᶜ d6 d4 = refl; +12-commᶜ d6 d5 = refl; +12-commᶜ d6 d6 = refl; +12-commᶜ d6 d7 = refl; +12-commᶜ d6 d8 = refl; +12-commᶜ d6 d9 = refl; +12-commᶜ d6 d10 = refl; +12-commᶜ d6 d11 = refl
+12-commᶜ d7 d0 = refl; +12-commᶜ d7 d1 = refl; +12-commᶜ d7 d2 = refl; +12-commᶜ d7 d3 = refl; +12-commᶜ d7 d4 = refl; +12-commᶜ d7 d5 = refl; +12-commᶜ d7 d6 = refl; +12-commᶜ d7 d7 = refl; +12-commᶜ d7 d8 = refl; +12-commᶜ d7 d9 = refl; +12-commᶜ d7 d10 = refl; +12-commᶜ d7 d11 = refl
+12-commᶜ d8 d0 = refl; +12-commᶜ d8 d1 = refl; +12-commᶜ d8 d2 = refl; +12-commᶜ d8 d3 = refl; +12-commᶜ d8 d4 = refl; +12-commᶜ d8 d5 = refl; +12-commᶜ d8 d6 = refl; +12-commᶜ d8 d7 = refl; +12-commᶜ d8 d8 = refl; +12-commᶜ d8 d9 = refl; +12-commᶜ d8 d10 = refl; +12-commᶜ d8 d11 = refl
+12-commᶜ d9 d0 = refl; +12-commᶜ d9 d1 = refl; +12-commᶜ d9 d2 = refl; +12-commᶜ d9 d3 = refl; +12-commᶜ d9 d4 = refl; +12-commᶜ d9 d5 = refl; +12-commᶜ d9 d6 = refl; +12-commᶜ d9 d7 = refl; +12-commᶜ d9 d8 = refl; +12-commᶜ d9 d9 = refl; +12-commᶜ d9 d10 = refl; +12-commᶜ d9 d11 = refl
+12-commᶜ d10 d0 = refl; +12-commᶜ d10 d1 = refl; +12-commᶜ d10 d2 = refl; +12-commᶜ d10 d3 = refl; +12-commᶜ d10 d4 = refl; +12-commᶜ d10 d5 = refl; +12-commᶜ d10 d6 = refl; +12-commᶜ d10 d7 = refl; +12-commᶜ d10 d8 = refl; +12-commᶜ d10 d9 = refl; +12-commᶜ d10 d10 = refl; +12-commᶜ d10 d11 = refl
+12-commᶜ d11 d0 = refl; +12-commᶜ d11 d1 = refl; +12-commᶜ d11 d2 = refl; +12-commᶜ d11 d3 = refl; +12-commᶜ d11 d4 = refl; +12-commᶜ d11 d5 = refl; +12-commᶜ d11 d6 = refl; +12-commᶜ d11 d7 = refl; +12-commᶜ d11 d8 = refl; +12-commᶜ d11 d9 = refl; +12-commᶜ d11 d10 = refl; +12-commᶜ d11 d11 = refl

-- 若 f : A4 → Duodec 是群同态且单射，则非交换对被映到相等（+12 交换）,
-- 与 non-abelian-witness 矛盾。故不存在单射同态 —— 这是「不同构」的构造性证据,
-- 不是同构或映射。
no-injective-hom : ∀ (f : A4 → Duodec) →
  (∀ g h → f (g ⊗ h) ≡ f g +12 f h) →      -- 同态
  (∀ g h → f g ≡ f h → g ≡ h) →            -- 单射
  ⊥
no-injective-hom f hom inj =
  non-abelian-witness (inj _ _ eq)
  where
    eq : f (Rot zero zero ⊗ Flip zero) ≡ f (Flip zero ⊗ Rot zero zero)
    eq = hom (Rot zero zero) (Flip zero)
         ∙ +12-commᶜ (f (Rot zero zero)) (f (Flip zero))
         ∙ sym (hom (Flip zero) (Rot zero zero))

--------------------------------------------------------------------------------
-- 结论:
--   A₄ 是 12 阶非交换群（V₄ ⋊ C₃），其正则作用自由且传递（§2）、忠实（§3）、
--   非交换（§5）。它与十二进制（Z/3 ⊕ Z/4 ≅ Z/12，交换联合周期）同为 12 阶
--   但不同构（§6 无单射同态）。两者严格分离，不互相引用同构。
--------------------------------------------------------------------------------

-- 0 postulate.
