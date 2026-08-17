{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Structology.GF9AffineMagicSquare
-- GF(9) 幻方链推广: a≠b 判据在特征 3 的形态 (0 postulate)
--
-- 【特征分离】(对照 GF4AffineMagicSquare 的特征 2 统一判据)
--   GF(4) 特征 2: a≠b 统一判据 ⟺ 正交 + 两对角闭合 (Freshman's Dream 合并)
--   GF(9) 特征 3: 判据分裂为三:
--     正交   ⟺ λ₁ ≠ λ₂        (斜率差非零, 无零因子)
--     主对角 ⟺ λ ≠ -1          (L_λ(i,i) = (λ+1)·i 为置换)
--     副对角 ⟺ λ ≠ 1           (空间副对角 j=8-i ⟺ (2,2)⊖i,
--                               值 = (λ-1)·i + (2,2) 为置换)
--
-- 【完全幻方实例】λ₁=α, λ₂=2α (均 ∉ {1,-1}):
--   正交 (81 对互异) + 叠加 M = 9·L₁+L₂+1 十线全 369 (1..81 完整)
--   81 格表的十线数据由 Rust 锁定 (表过大不入证明层):
--   sov-math/sov-validation/src/gf9_diag.rs [3]/[6]
--   Agda 侧锁定: 判据代数核 (无零因子 orth-kernel)、对角 transversal
--   (显式置换表)、退化反例 (λ=1/λ=-1)、幻常数算术。
--
-- 【命名层锚点】三进制「矢量对称幻方」实例: L_α/L_2α 两环同步旋转,
--   完全闭合是动态过程的不变量 (本体定义见 GF4AffineMagicSquare 头注释)。

module Sovereign.Structology.GF9AffineMagicSquare where

open import Data.Nat using (ℕ; _+_; _*_)
open import Data.Vec using (Vec; []; _∷_)
open import Data.Product using (_,_)
open import Data.Empty using (⊥-elim)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; cong; module ≡-Reasoning)
open ≡-Reasoning

open import Sovereign.Base.Trit using (T₀; T₁; T₂; negate)
open import Sovereign.Algebra.GF9
  using (GF9; alpha; gf9-one; gf9-zero; embed-gf3; _+gf9_; _*gf9_;
         +gf9-assoc; +gf9-comm; *gf9-distribˡ-+gf9; *gf9-distribʳ-+gf9;
         *gf9-identityˡ)

--------------------------------------------------------------------------------
-- §1. 常数与减法 (idx 编码: idx(a,b) = 3a+b)
--------------------------------------------------------------------------------

twoAlpha : GF9
twoAlpha = T₀ , T₂

negGF9 : GF9 → GF9
negGF9 (a , b) = negate a , negate b

subGF9 : GF9 → GF9 → GF9
subGF9 x y = x +gf9 negGF9 y

-- 空间副对角截距: j = 8-i ⟺ (2,2)⊖i (特征 3 仿射, 斜率 -1)
anti-c : GF9
anti-c = T₂ , T₂

-- 九个域元素 (按 idx 序)
e0 e1 e2 e3 e4 e5 e6 e7 e8 : GF9
e0 = T₀ , T₀
e1 = T₀ , T₁
e2 = T₀ , T₂
e3 = T₁ , T₀
e4 = T₁ , T₁
e5 = T₁ , T₂
e6 = T₂ , T₀
e7 = T₂ , T₁
e8 = T₂ , T₂

--------------------------------------------------------------------------------
-- §2. 正交判据代数核: 斜率差非零 ⟹ 无零因子
--------------------------------------------------------------------------------

onePlusAlpha : GF9
onePlusAlpha = alpha +gf9 gf9-one        -- (1,1)

alphaMinusOne : GF9
alphaMinusOne = subGF9 alpha gf9-one     -- (2,1)

-- 实例斜率差: α ⊖ 2α = 2α ≠ 0
orth-diff : GF9
orth-diff = subGF9 alpha twoAlpha

orth-diff-val : orth-diff ≡ twoAlpha
orth-diff-val = refl

orth-diff-nonzero : orth-diff ≢ gf9-zero
orth-diff-nonzero = λ()

-- 无零因子 (实例级, 9 case): 正交性的代数核 —
-- λ₁≠λ₂ ⟹ (λ₁-λ₂)·(i-i') = 0 ⟹ i-i' = 0 ⟹ (i,j) 由叠加值唯一决定
orth-kernel : ∀ x → x ≢ gf9-zero → (orth-diff *gf9 x) ≢ gf9-zero
orth-kernel (T₀ , T₀) ne = ⊥-elim (ne refl)
orth-kernel (T₀ , T₁) _ = λ()
orth-kernel (T₀ , T₂) _ = λ()
orth-kernel (T₁ , T₀) _ = λ()
orth-kernel (T₁ , T₁) _ = λ()
orth-kernel (T₁ , T₂) _ = λ()
orth-kernel (T₂ , T₀) _ = λ()
orth-kernel (T₂ , T₁) _ = λ()
orth-kernel (T₂ , T₂) _ = λ()

--------------------------------------------------------------------------------
-- §3. 对角 transversal: λ=α 实例 (值域 = 全部 9 元素 ⟹ 置换)
--------------------------------------------------------------------------------

-- λ=α 主对角: L_α(i,i) = (α+1)·i
diag-alpha : Vec GF9 9
diag-alpha =
  (onePlusAlpha *gf9 e0) ∷ (onePlusAlpha *gf9 e1) ∷ (onePlusAlpha *gf9 e2) ∷
  (onePlusAlpha *gf9 e3) ∷ (onePlusAlpha *gf9 e4) ∷ (onePlusAlpha *gf9 e5) ∷
  (onePlusAlpha *gf9 e6) ∷ (onePlusAlpha *gf9 e7) ∷ (onePlusAlpha *gf9 e8) ∷ []

-- 右侧显式列出全部 9 个域元素各一次 ⟹ transversal (Rust [6] 一致)
diag-alpha-perm : diag-alpha ≡
  e0 ∷ e7 ∷ e5 ∷ e4 ∷ e2 ∷ e6 ∷ e8 ∷ e3 ∷ e1 ∷ []
diag-alpha-perm = refl

-- λ=α 副对角: (α⊖1)·i + (2,2)
anti-alpha : Vec GF9 9
anti-alpha =
  ((alphaMinusOne *gf9 e0) +gf9 anti-c) ∷ ((alphaMinusOne *gf9 e1) +gf9 anti-c) ∷
  ((alphaMinusOne *gf9 e2) +gf9 anti-c) ∷ ((alphaMinusOne *gf9 e3) +gf9 anti-c) ∷
  ((alphaMinusOne *gf9 e4) +gf9 anti-c) ∷ ((alphaMinusOne *gf9 e5) +gf9 anti-c) ∷
  ((alphaMinusOne *gf9 e6) +gf9 anti-c) ∷ ((alphaMinusOne *gf9 e7) +gf9 anti-c) ∷
  ((alphaMinusOne *gf9 e8) +gf9 anti-c) ∷ []

anti-alpha-perm : anti-alpha ≡
  e8 ∷ e4 ∷ e0 ∷ e3 ∷ e2 ∷ e7 ∷ e1 ∷ e6 ∷ e5 ∷ []
anti-alpha-perm = refl

--------------------------------------------------------------------------------
-- §4. 退化反例: 特征 3 判据分裂的实证
--------------------------------------------------------------------------------

-- λ=1: 副对角值 = (1⊖1)·i + (2,2) = (2,2) 恒常 ⟹ 非 transversal
anti-degen-1 : ∀ x → ((subGF9 gf9-one gf9-one *gf9 x) +gf9 anti-c) ≡ anti-c
anti-degen-1 x = refl

-- λ=-1=2: 主对角值 = (2+1)·i = 0·i = 0 恒常 ⟹ 非 transversal
main-degen-2 : ∀ x → ((embed-gf3 T₂ +gf9 gf9-one) *gf9 x) ≡ gf9-zero
main-degen-2 x = refl

--------------------------------------------------------------------------------
-- §5. 判据分裂实例: 正交成立而对角退化
--------------------------------------------------------------------------------

-- (λ₁,λ₂) = (1, 2): 斜率差 1⊖2 = 2 ≠ 0 ⟹ 正交
sep-diff : subGF9 gf9-one (embed-gf3 T₂) ≡ embed-gf3 T₂
sep-diff = refl

sep-diff-nonzero : subGF9 gf9-one (embed-gf3 T₂) ≢ gf9-zero
sep-diff-nonzero = λ()

-- 但 λ₁=1 ⟹ 副对角退化 (anti-degen-1), λ₂=2 ⟹ 主对角退化 (main-degen-2)
-- ⟹ 特征 3 下正交与对角闭合是独立条件 (对照 GF(4): a≠b 一条判据统管)

--------------------------------------------------------------------------------
-- §6. 幻常数算术 (Rust [3] 十线 369 的算术核)
--------------------------------------------------------------------------------

-- 任意 transversal 的 idx 元素和 (0+1+...+8)
idx-sum-36 : 0 + 1 + 2 + 3 + 4 + 5 + 6 + 7 + 8 ≡ 36
idx-sum-36 = refl

-- 幻常数 (1-81 编码): 9·36 + 36 + 9 = 369 = 9·(81+1)/2
magic-constant-369 : 9 * 36 + 36 + 9 ≡ 369
magic-constant-369 = refl

--------------------------------------------------------------------------------
-- §7. 动态矢量轨线生成法则 (观测层, 会话裁定 #14)
--   环同步转动 (i,j) ↦ (i+t, j+t) 经 L_λ(i,j) = λ·i+j 投影为
--   值环上步长 (λ+1) 的平移: L_λ(i+t, j+t) ≡ L_λ(i,j) + (λ+1)·t
--   闭合判据: λ+1 ≠ 0 ⟺ λ ≠ -1 ⟹ 主对角 transversal (与 §3 分类一致)
--------------------------------------------------------------------------------

-- 内交换: x + (y + z) ≡ y + (x + z)
+gf9-inner-swap : ∀ x y z → x +gf9 (y +gf9 z) ≡ y +gf9 (x +gf9 z)
+gf9-inner-swap x y z = begin
  x +gf9 (y +gf9 z)
    ≡⟨ sym (+gf9-assoc x y z) ⟩
  (x +gf9 y) +gf9 z
    ≡⟨ cong (_+gf9 z) (+gf9-comm x y) ⟩
  (y +gf9 x) +gf9 z
    ≡⟨ +gf9-assoc y x z ⟩
  y +gf9 (x +gf9 z) ∎

-- 轨线生成法则 (一般斜率形): 步长 = μ+1
trajectory-Lλ : ∀ μ i j t →
  (μ *gf9 (i +gf9 t)) +gf9 (j +gf9 t)
  ≡ ((μ *gf9 i) +gf9 j) +gf9 ((μ +gf9 gf9-one) *gf9 t)
trajectory-Lλ μ i j t = begin
  (μ *gf9 (i +gf9 t)) +gf9 (j +gf9 t)
    ≡⟨ cong (_+gf9 (j +gf9 t)) (*gf9-distribˡ-+gf9 μ i t) ⟩
  ((μ *gf9 i) +gf9 (μ *gf9 t)) +gf9 (j +gf9 t)
    ≡⟨ +gf9-assoc (μ *gf9 i) (μ *gf9 t) (j +gf9 t) ⟩
  (μ *gf9 i) +gf9 ((μ *gf9 t) +gf9 (j +gf9 t))
    ≡⟨ cong ((μ *gf9 i) +gf9_) (+gf9-inner-swap (μ *gf9 t) j t) ⟩
  (μ *gf9 i) +gf9 (j +gf9 ((μ *gf9 t) +gf9 t))
    ≡⟨ sym (+gf9-assoc (μ *gf9 i) j ((μ *gf9 t) +gf9 t)) ⟩
  ((μ *gf9 i) +gf9 j) +gf9 ((μ *gf9 t) +gf9 t)
    ≡⟨ cong (λ u → ((μ *gf9 i) +gf9 j) +gf9 ((μ *gf9 t) +gf9 u))
            (sym (*gf9-identityˡ t)) ⟩
  ((μ *gf9 i) +gf9 j) +gf9 ((μ *gf9 t) +gf9 (gf9-one *gf9 t))
    ≡⟨ cong (((μ *gf9 i) +gf9 j) +gf9_)
            (sym (*gf9-distribʳ-+gf9 μ gf9-one t)) ⟩
  ((μ *gf9 i) +gf9 j) +gf9 ((μ +gf9 gf9-one) *gf9 t) ∎

-- λ=α 实例步长非零: α+1 = (1,1) ≠ 0 ⟹ 主对角闭合 (承 §3 diag-alpha-perm)
trajectory-step-alpha : (alpha +gf9 gf9-one) ≢ gf9-zero
trajectory-step-alpha ()

-- 0 postulate.
