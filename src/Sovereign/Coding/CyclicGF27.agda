{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Coding.CyclicGF27
-- GF(27) 根结构 → 长度 26 三元循环码 (P1-2, wiki 94B)
--
-- 数学背景:
--   GF(27) = GF(3)[γ]/(γ³+2γ+1), γ 为本原元 (阶 26, 见 GF27Separation)。
--   g(x) = x³+2x+1 的三个根 = {γ, γ³, γ⁹} (Frobenius 共轭三元组, 已证)。
--   三元循环码 C = { c ∈ GF(3)²⁶ | c(γ) = 0 }, 其中 c(γ) = Σₖ cₖγᵏ。
--   由 char 3 的 freshman's dream (x+y)³ = x³+y³: c(γ)=0 ⟹ c(γ³) = c(γ)³ = 0,
--   同理 c(γ⁹) = 0 —— 一个校验子自动覆盖三个共轭根。
--   循环性: shift(c)(γ) = γ·c(γ) (γ²⁶=1 处理回绕) ⟹ C 对循环移位封闭。
--
-- 宪法原则 (全离散, 无除法):
--   1. γ 幂 = ℕ 递归 (右乘), 校验子 = 显式左结合和。
--   2. freshman's dream (cube-sum) / Frobenius 乘法性 (cube-mul) / γ-结合·分配
--      为 27² = 729 case 穷举 (策略 A, 生成表) —— 与 BCHGF9 的 81 case 同款。
--   3. +27 公理为结构证明 (Trit ⊕ 公理), 0 postulate。
--
-- 包含:
--   §1 GF(27) 基本律: +27-comm/assoc, 零律, 幺律 (结构) + *27-comm (729 穷举)
--   §2 freshman's dream: cube-mul/cube-sum (729 穷举) + γ-结合/分配 (729 穷举)
--   §3 校验子机器: evalγ/γPow/γ3Pow/γ9Pow + 零消去/拆分/移位
--   §4 三根定理: c(γ)=0 ⟹ c(γ³)=c(γ⁹)=0 (Frobenius 立方提升)
--   §5 循环码: 循环移位封闭 + γ 阶 26 + g 的三根见证
--
-- 0 postulate。

module Sovereign.Coding.CyclicGF27 where

open import Data.Nat using (ℕ; zero; suc; _+_; _∸_; _<_; s≤s)
open import Data.Nat.Properties
  using (m∸n+n≡m; +-comm; +-assoc; +-suc; +-identityʳ; <-trans; ≤-refl; m<n⇒m<1+n; n<1+n)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; _≢_; cong; cong₂; sym; trans; subst; module ≡-Reasoning)
open ≡-Reasoning
open import Sovereign.Base.Trit
  using (Trit; T₀; T₁; T₂; _⊗_; _⊕_;
         ⊕-comm; ⊕-assoc; ⊕-identityˡ; ⊕-identityʳ;
         ⊗-comm; ⊗-identityˡ; ⊗-identityʳ; ⊗-zeroˡ; ⊗-zeroʳ)
open import Sovereign.Problem.PvsNP.GF27Separation
  using (GF27; zero27; one27; γ; _+27_; _*27_; cube27; γ3; γ9;
         root-gamma; root-gamma3; root-gamma9; gamma-cube; frobenius-cycle)

-- 本地 Trit 别名 + 分层 fixity (⊕/⊗ 同级 20, 混用须分层)
_+₃_ : Trit → Trit → Trit
x +₃ y = x ⊕ y

infixl 21 _+₃_

-- 本地 GF27 别名 (规避 _+27_/_*27_ 同级解析歧义)
_+₉_ : GF27 → GF27 → GF27
x +₉ y = x +27 y

_*₉_ : GF27 → GF27 → GF27
x *₉ y = x *27 y

infixl 21 _+₉_
infixl 22 _*₉_

emb : Trit → GF27
emb t = t , T₀ , T₀

-- 本地三元 cong (stdlib 无 cong₃)
cong₃ : ∀ {A B C D : Set} {x y : A} {u v : B} {r s : C} (f : A → B → C → D) →
  x ≡ y → u ≡ v → r ≡ s → f x u r ≡ f y v s
cong₃ f refl refl refl = refl

--------------------------------------------------------------------------------
-- §1. GF(27) 基本律
--------------------------------------------------------------------------------

+27-comm : ∀ x y → x +₉ y ≡ y +₉ x
+27-comm (a , b , c) (d , e , f) = cong₃ (λ p q r → p , q , r) (⊕-comm a d) (⊕-comm b e) (⊕-comm c f)

+27-assoc : ∀ x y z → (x +₉ y) +₉ z ≡ x +₉ (y +₉ z)
+27-assoc (a , b , c) (d , e , f) (g , h , i) = cong₃ (λ p q r → p , q , r) (⊕-assoc a d g) (⊕-assoc b e h) (⊕-assoc c f i)

+27-identityʳ : ∀ x → x +₉ zero27 ≡ x
+27-identityʳ (a , b , c) = cong₃ (λ p q r → p , q , r) (⊕-identityʳ a) (⊕-identityʳ b) (⊕-identityʳ c)

-- 4 项交换 (GF27 层)
shuffle4 : ∀ A B C D → (A +₉ B) +₉ (C +₉ D) ≡ (A +₉ C) +₉ (B +₉ D)
shuffle4 A B C D = begin
  (A +₉ B) +₉ (C +₉ D)
    ≡⟨ +27-assoc A B (C +₉ D) ⟩
  A +₉ (B +₉ (C +₉ D))
    ≡⟨ cong (A +₉_) (sym (+27-assoc B C D)) ⟩
  A +₉ ((B +₉ C) +₉ D)
    ≡⟨ cong (λ t → A +₉ (t +₉ D)) (+27-comm B C) ⟩
  A +₉ ((C +₉ B) +₉ D)
    ≡⟨ cong (A +₉_) (+27-assoc C B D) ⟩
  A +₉ (C +₉ (B +₉ D))
    ≡⟨ sym (+27-assoc A C (B +₉ D)) ⟩
  (A +₉ C) +₉ (B +₉ D)
  ∎

-- 交换律 (729 case, 生成)
*27-comm : ∀ x y → x *₉ y ≡ y *₉ x
*27-comm (T₀ , T₀ , T₀) (T₀ , T₀ , T₀) = refl
*27-comm (T₀ , T₀ , T₀) (T₀ , T₀ , T₁) = refl
*27-comm (T₀ , T₀ , T₀) (T₀ , T₀ , T₂) = refl
*27-comm (T₀ , T₀ , T₀) (T₀ , T₁ , T₀) = refl
*27-comm (T₀ , T₀ , T₀) (T₀ , T₁ , T₁) = refl
*27-comm (T₀ , T₀ , T₀) (T₀ , T₁ , T₂) = refl
*27-comm (T₀ , T₀ , T₀) (T₀ , T₂ , T₀) = refl
*27-comm (T₀ , T₀ , T₀) (T₀ , T₂ , T₁) = refl
*27-comm (T₀ , T₀ , T₀) (T₀ , T₂ , T₂) = refl
*27-comm (T₀ , T₀ , T₀) (T₁ , T₀ , T₀) = refl
*27-comm (T₀ , T₀ , T₀) (T₁ , T₀ , T₁) = refl
*27-comm (T₀ , T₀ , T₀) (T₁ , T₀ , T₂) = refl
*27-comm (T₀ , T₀ , T₀) (T₁ , T₁ , T₀) = refl
*27-comm (T₀ , T₀ , T₀) (T₁ , T₁ , T₁) = refl
*27-comm (T₀ , T₀ , T₀) (T₁ , T₁ , T₂) = refl
*27-comm (T₀ , T₀ , T₀) (T₁ , T₂ , T₀) = refl
*27-comm (T₀ , T₀ , T₀) (T₁ , T₂ , T₁) = refl
*27-comm (T₀ , T₀ , T₀) (T₁ , T₂ , T₂) = refl
*27-comm (T₀ , T₀ , T₀) (T₂ , T₀ , T₀) = refl
*27-comm (T₀ , T₀ , T₀) (T₂ , T₀ , T₁) = refl
*27-comm (T₀ , T₀ , T₀) (T₂ , T₀ , T₂) = refl
*27-comm (T₀ , T₀ , T₀) (T₂ , T₁ , T₀) = refl
*27-comm (T₀ , T₀ , T₀) (T₂ , T₁ , T₁) = refl
*27-comm (T₀ , T₀ , T₀) (T₂ , T₁ , T₂) = refl
*27-comm (T₀ , T₀ , T₀) (T₂ , T₂ , T₀) = refl
*27-comm (T₀ , T₀ , T₀) (T₂ , T₂ , T₁) = refl
*27-comm (T₀ , T₀ , T₀) (T₂ , T₂ , T₂) = refl
*27-comm (T₀ , T₀ , T₁) (T₀ , T₀ , T₀) = refl
*27-comm (T₀ , T₀ , T₁) (T₀ , T₀ , T₁) = refl
*27-comm (T₀ , T₀ , T₁) (T₀ , T₀ , T₂) = refl
*27-comm (T₀ , T₀ , T₁) (T₀ , T₁ , T₀) = refl
*27-comm (T₀ , T₀ , T₁) (T₀ , T₁ , T₁) = refl
*27-comm (T₀ , T₀ , T₁) (T₀ , T₁ , T₂) = refl
*27-comm (T₀ , T₀ , T₁) (T₀ , T₂ , T₀) = refl
*27-comm (T₀ , T₀ , T₁) (T₀ , T₂ , T₁) = refl
*27-comm (T₀ , T₀ , T₁) (T₀ , T₂ , T₂) = refl
*27-comm (T₀ , T₀ , T₁) (T₁ , T₀ , T₀) = refl
*27-comm (T₀ , T₀ , T₁) (T₁ , T₀ , T₁) = refl
*27-comm (T₀ , T₀ , T₁) (T₁ , T₀ , T₂) = refl
*27-comm (T₀ , T₀ , T₁) (T₁ , T₁ , T₀) = refl
*27-comm (T₀ , T₀ , T₁) (T₁ , T₁ , T₁) = refl
*27-comm (T₀ , T₀ , T₁) (T₁ , T₁ , T₂) = refl
*27-comm (T₀ , T₀ , T₁) (T₁ , T₂ , T₀) = refl
*27-comm (T₀ , T₀ , T₁) (T₁ , T₂ , T₁) = refl
*27-comm (T₀ , T₀ , T₁) (T₁ , T₂ , T₂) = refl
*27-comm (T₀ , T₀ , T₁) (T₂ , T₀ , T₀) = refl
*27-comm (T₀ , T₀ , T₁) (T₂ , T₀ , T₁) = refl
*27-comm (T₀ , T₀ , T₁) (T₂ , T₀ , T₂) = refl
*27-comm (T₀ , T₀ , T₁) (T₂ , T₁ , T₀) = refl
*27-comm (T₀ , T₀ , T₁) (T₂ , T₁ , T₁) = refl
*27-comm (T₀ , T₀ , T₁) (T₂ , T₁ , T₂) = refl
*27-comm (T₀ , T₀ , T₁) (T₂ , T₂ , T₀) = refl
*27-comm (T₀ , T₀ , T₁) (T₂ , T₂ , T₁) = refl
*27-comm (T₀ , T₀ , T₁) (T₂ , T₂ , T₂) = refl
*27-comm (T₀ , T₀ , T₂) (T₀ , T₀ , T₀) = refl
*27-comm (T₀ , T₀ , T₂) (T₀ , T₀ , T₁) = refl
*27-comm (T₀ , T₀ , T₂) (T₀ , T₀ , T₂) = refl
*27-comm (T₀ , T₀ , T₂) (T₀ , T₁ , T₀) = refl
*27-comm (T₀ , T₀ , T₂) (T₀ , T₁ , T₁) = refl
*27-comm (T₀ , T₀ , T₂) (T₀ , T₁ , T₂) = refl
*27-comm (T₀ , T₀ , T₂) (T₀ , T₂ , T₀) = refl
*27-comm (T₀ , T₀ , T₂) (T₀ , T₂ , T₁) = refl
*27-comm (T₀ , T₀ , T₂) (T₀ , T₂ , T₂) = refl
*27-comm (T₀ , T₀ , T₂) (T₁ , T₀ , T₀) = refl
*27-comm (T₀ , T₀ , T₂) (T₁ , T₀ , T₁) = refl
*27-comm (T₀ , T₀ , T₂) (T₁ , T₀ , T₂) = refl
*27-comm (T₀ , T₀ , T₂) (T₁ , T₁ , T₀) = refl
*27-comm (T₀ , T₀ , T₂) (T₁ , T₁ , T₁) = refl
*27-comm (T₀ , T₀ , T₂) (T₁ , T₁ , T₂) = refl
*27-comm (T₀ , T₀ , T₂) (T₁ , T₂ , T₀) = refl
*27-comm (T₀ , T₀ , T₂) (T₁ , T₂ , T₁) = refl
*27-comm (T₀ , T₀ , T₂) (T₁ , T₂ , T₂) = refl
*27-comm (T₀ , T₀ , T₂) (T₂ , T₀ , T₀) = refl
*27-comm (T₀ , T₀ , T₂) (T₂ , T₀ , T₁) = refl
*27-comm (T₀ , T₀ , T₂) (T₂ , T₀ , T₂) = refl
*27-comm (T₀ , T₀ , T₂) (T₂ , T₁ , T₀) = refl
*27-comm (T₀ , T₀ , T₂) (T₂ , T₁ , T₁) = refl
*27-comm (T₀ , T₀ , T₂) (T₂ , T₁ , T₂) = refl
*27-comm (T₀ , T₀ , T₂) (T₂ , T₂ , T₀) = refl
*27-comm (T₀ , T₀ , T₂) (T₂ , T₂ , T₁) = refl
*27-comm (T₀ , T₀ , T₂) (T₂ , T₂ , T₂) = refl
*27-comm (T₀ , T₁ , T₀) (T₀ , T₀ , T₀) = refl
*27-comm (T₀ , T₁ , T₀) (T₀ , T₀ , T₁) = refl
*27-comm (T₀ , T₁ , T₀) (T₀ , T₀ , T₂) = refl
*27-comm (T₀ , T₁ , T₀) (T₀ , T₁ , T₀) = refl
*27-comm (T₀ , T₁ , T₀) (T₀ , T₁ , T₁) = refl
*27-comm (T₀ , T₁ , T₀) (T₀ , T₁ , T₂) = refl
*27-comm (T₀ , T₁ , T₀) (T₀ , T₂ , T₀) = refl
*27-comm (T₀ , T₁ , T₀) (T₀ , T₂ , T₁) = refl
*27-comm (T₀ , T₁ , T₀) (T₀ , T₂ , T₂) = refl
*27-comm (T₀ , T₁ , T₀) (T₁ , T₀ , T₀) = refl
*27-comm (T₀ , T₁ , T₀) (T₁ , T₀ , T₁) = refl
*27-comm (T₀ , T₁ , T₀) (T₁ , T₀ , T₂) = refl
*27-comm (T₀ , T₁ , T₀) (T₁ , T₁ , T₀) = refl
*27-comm (T₀ , T₁ , T₀) (T₁ , T₁ , T₁) = refl
*27-comm (T₀ , T₁ , T₀) (T₁ , T₁ , T₂) = refl
*27-comm (T₀ , T₁ , T₀) (T₁ , T₂ , T₀) = refl
*27-comm (T₀ , T₁ , T₀) (T₁ , T₂ , T₁) = refl
*27-comm (T₀ , T₁ , T₀) (T₁ , T₂ , T₂) = refl
*27-comm (T₀ , T₁ , T₀) (T₂ , T₀ , T₀) = refl
*27-comm (T₀ , T₁ , T₀) (T₂ , T₀ , T₁) = refl
*27-comm (T₀ , T₁ , T₀) (T₂ , T₀ , T₂) = refl
*27-comm (T₀ , T₁ , T₀) (T₂ , T₁ , T₀) = refl
*27-comm (T₀ , T₁ , T₀) (T₂ , T₁ , T₁) = refl
*27-comm (T₀ , T₁ , T₀) (T₂ , T₁ , T₂) = refl
*27-comm (T₀ , T₁ , T₀) (T₂ , T₂ , T₀) = refl
*27-comm (T₀ , T₁ , T₀) (T₂ , T₂ , T₁) = refl
*27-comm (T₀ , T₁ , T₀) (T₂ , T₂ , T₂) = refl
*27-comm (T₀ , T₁ , T₁) (T₀ , T₀ , T₀) = refl
*27-comm (T₀ , T₁ , T₁) (T₀ , T₀ , T₁) = refl
*27-comm (T₀ , T₁ , T₁) (T₀ , T₀ , T₂) = refl
*27-comm (T₀ , T₁ , T₁) (T₀ , T₁ , T₀) = refl
*27-comm (T₀ , T₁ , T₁) (T₀ , T₁ , T₁) = refl
*27-comm (T₀ , T₁ , T₁) (T₀ , T₁ , T₂) = refl
*27-comm (T₀ , T₁ , T₁) (T₀ , T₂ , T₀) = refl
*27-comm (T₀ , T₁ , T₁) (T₀ , T₂ , T₁) = refl
*27-comm (T₀ , T₁ , T₁) (T₀ , T₂ , T₂) = refl
*27-comm (T₀ , T₁ , T₁) (T₁ , T₀ , T₀) = refl
*27-comm (T₀ , T₁ , T₁) (T₁ , T₀ , T₁) = refl
*27-comm (T₀ , T₁ , T₁) (T₁ , T₀ , T₂) = refl
*27-comm (T₀ , T₁ , T₁) (T₁ , T₁ , T₀) = refl
*27-comm (T₀ , T₁ , T₁) (T₁ , T₁ , T₁) = refl
*27-comm (T₀ , T₁ , T₁) (T₁ , T₁ , T₂) = refl
*27-comm (T₀ , T₁ , T₁) (T₁ , T₂ , T₀) = refl
*27-comm (T₀ , T₁ , T₁) (T₁ , T₂ , T₁) = refl
*27-comm (T₀ , T₁ , T₁) (T₁ , T₂ , T₂) = refl
*27-comm (T₀ , T₁ , T₁) (T₂ , T₀ , T₀) = refl
*27-comm (T₀ , T₁ , T₁) (T₂ , T₀ , T₁) = refl
*27-comm (T₀ , T₁ , T₁) (T₂ , T₀ , T₂) = refl
*27-comm (T₀ , T₁ , T₁) (T₂ , T₁ , T₀) = refl
*27-comm (T₀ , T₁ , T₁) (T₂ , T₁ , T₁) = refl
*27-comm (T₀ , T₁ , T₁) (T₂ , T₁ , T₂) = refl
*27-comm (T₀ , T₁ , T₁) (T₂ , T₂ , T₀) = refl
*27-comm (T₀ , T₁ , T₁) (T₂ , T₂ , T₁) = refl
*27-comm (T₀ , T₁ , T₁) (T₂ , T₂ , T₂) = refl
*27-comm (T₀ , T₁ , T₂) (T₀ , T₀ , T₀) = refl
*27-comm (T₀ , T₁ , T₂) (T₀ , T₀ , T₁) = refl
*27-comm (T₀ , T₁ , T₂) (T₀ , T₀ , T₂) = refl
*27-comm (T₀ , T₁ , T₂) (T₀ , T₁ , T₀) = refl
*27-comm (T₀ , T₁ , T₂) (T₀ , T₁ , T₁) = refl
*27-comm (T₀ , T₁ , T₂) (T₀ , T₁ , T₂) = refl
*27-comm (T₀ , T₁ , T₂) (T₀ , T₂ , T₀) = refl
*27-comm (T₀ , T₁ , T₂) (T₀ , T₂ , T₁) = refl
*27-comm (T₀ , T₁ , T₂) (T₀ , T₂ , T₂) = refl
*27-comm (T₀ , T₁ , T₂) (T₁ , T₀ , T₀) = refl
*27-comm (T₀ , T₁ , T₂) (T₁ , T₀ , T₁) = refl
*27-comm (T₀ , T₁ , T₂) (T₁ , T₀ , T₂) = refl
*27-comm (T₀ , T₁ , T₂) (T₁ , T₁ , T₀) = refl
*27-comm (T₀ , T₁ , T₂) (T₁ , T₁ , T₁) = refl
*27-comm (T₀ , T₁ , T₂) (T₁ , T₁ , T₂) = refl
*27-comm (T₀ , T₁ , T₂) (T₁ , T₂ , T₀) = refl
*27-comm (T₀ , T₁ , T₂) (T₁ , T₂ , T₁) = refl
*27-comm (T₀ , T₁ , T₂) (T₁ , T₂ , T₂) = refl
*27-comm (T₀ , T₁ , T₂) (T₂ , T₀ , T₀) = refl
*27-comm (T₀ , T₁ , T₂) (T₂ , T₀ , T₁) = refl
*27-comm (T₀ , T₁ , T₂) (T₂ , T₀ , T₂) = refl
*27-comm (T₀ , T₁ , T₂) (T₂ , T₁ , T₀) = refl
*27-comm (T₀ , T₁ , T₂) (T₂ , T₁ , T₁) = refl
*27-comm (T₀ , T₁ , T₂) (T₂ , T₁ , T₂) = refl
*27-comm (T₀ , T₁ , T₂) (T₂ , T₂ , T₀) = refl
*27-comm (T₀ , T₁ , T₂) (T₂ , T₂ , T₁) = refl
*27-comm (T₀ , T₁ , T₂) (T₂ , T₂ , T₂) = refl
*27-comm (T₀ , T₂ , T₀) (T₀ , T₀ , T₀) = refl
*27-comm (T₀ , T₂ , T₀) (T₀ , T₀ , T₁) = refl
*27-comm (T₀ , T₂ , T₀) (T₀ , T₀ , T₂) = refl
*27-comm (T₀ , T₂ , T₀) (T₀ , T₁ , T₀) = refl
*27-comm (T₀ , T₂ , T₀) (T₀ , T₁ , T₁) = refl
*27-comm (T₀ , T₂ , T₀) (T₀ , T₁ , T₂) = refl
*27-comm (T₀ , T₂ , T₀) (T₀ , T₂ , T₀) = refl
*27-comm (T₀ , T₂ , T₀) (T₀ , T₂ , T₁) = refl
*27-comm (T₀ , T₂ , T₀) (T₀ , T₂ , T₂) = refl
*27-comm (T₀ , T₂ , T₀) (T₁ , T₀ , T₀) = refl
*27-comm (T₀ , T₂ , T₀) (T₁ , T₀ , T₁) = refl
*27-comm (T₀ , T₂ , T₀) (T₁ , T₀ , T₂) = refl
*27-comm (T₀ , T₂ , T₀) (T₁ , T₁ , T₀) = refl
*27-comm (T₀ , T₂ , T₀) (T₁ , T₁ , T₁) = refl
*27-comm (T₀ , T₂ , T₀) (T₁ , T₁ , T₂) = refl
*27-comm (T₀ , T₂ , T₀) (T₁ , T₂ , T₀) = refl
*27-comm (T₀ , T₂ , T₀) (T₁ , T₂ , T₁) = refl
*27-comm (T₀ , T₂ , T₀) (T₁ , T₂ , T₂) = refl
*27-comm (T₀ , T₂ , T₀) (T₂ , T₀ , T₀) = refl
*27-comm (T₀ , T₂ , T₀) (T₂ , T₀ , T₁) = refl
*27-comm (T₀ , T₂ , T₀) (T₂ , T₀ , T₂) = refl
*27-comm (T₀ , T₂ , T₀) (T₂ , T₁ , T₀) = refl
*27-comm (T₀ , T₂ , T₀) (T₂ , T₁ , T₁) = refl
*27-comm (T₀ , T₂ , T₀) (T₂ , T₁ , T₂) = refl
*27-comm (T₀ , T₂ , T₀) (T₂ , T₂ , T₀) = refl
*27-comm (T₀ , T₂ , T₀) (T₂ , T₂ , T₁) = refl
*27-comm (T₀ , T₂ , T₀) (T₂ , T₂ , T₂) = refl
*27-comm (T₀ , T₂ , T₁) (T₀ , T₀ , T₀) = refl
*27-comm (T₀ , T₂ , T₁) (T₀ , T₀ , T₁) = refl
*27-comm (T₀ , T₂ , T₁) (T₀ , T₀ , T₂) = refl
*27-comm (T₀ , T₂ , T₁) (T₀ , T₁ , T₀) = refl
*27-comm (T₀ , T₂ , T₁) (T₀ , T₁ , T₁) = refl
*27-comm (T₀ , T₂ , T₁) (T₀ , T₁ , T₂) = refl
*27-comm (T₀ , T₂ , T₁) (T₀ , T₂ , T₀) = refl
*27-comm (T₀ , T₂ , T₁) (T₀ , T₂ , T₁) = refl
*27-comm (T₀ , T₂ , T₁) (T₀ , T₂ , T₂) = refl
*27-comm (T₀ , T₂ , T₁) (T₁ , T₀ , T₀) = refl
*27-comm (T₀ , T₂ , T₁) (T₁ , T₀ , T₁) = refl
*27-comm (T₀ , T₂ , T₁) (T₁ , T₀ , T₂) = refl
*27-comm (T₀ , T₂ , T₁) (T₁ , T₁ , T₀) = refl
*27-comm (T₀ , T₂ , T₁) (T₁ , T₁ , T₁) = refl
*27-comm (T₀ , T₂ , T₁) (T₁ , T₁ , T₂) = refl
*27-comm (T₀ , T₂ , T₁) (T₁ , T₂ , T₀) = refl
*27-comm (T₀ , T₂ , T₁) (T₁ , T₂ , T₁) = refl
*27-comm (T₀ , T₂ , T₁) (T₁ , T₂ , T₂) = refl
*27-comm (T₀ , T₂ , T₁) (T₂ , T₀ , T₀) = refl
*27-comm (T₀ , T₂ , T₁) (T₂ , T₀ , T₁) = refl
*27-comm (T₀ , T₂ , T₁) (T₂ , T₀ , T₂) = refl
*27-comm (T₀ , T₂ , T₁) (T₂ , T₁ , T₀) = refl
*27-comm (T₀ , T₂ , T₁) (T₂ , T₁ , T₁) = refl
*27-comm (T₀ , T₂ , T₁) (T₂ , T₁ , T₂) = refl
*27-comm (T₀ , T₂ , T₁) (T₂ , T₂ , T₀) = refl
*27-comm (T₀ , T₂ , T₁) (T₂ , T₂ , T₁) = refl
*27-comm (T₀ , T₂ , T₁) (T₂ , T₂ , T₂) = refl
*27-comm (T₀ , T₂ , T₂) (T₀ , T₀ , T₀) = refl
*27-comm (T₀ , T₂ , T₂) (T₀ , T₀ , T₁) = refl
*27-comm (T₀ , T₂ , T₂) (T₀ , T₀ , T₂) = refl
*27-comm (T₀ , T₂ , T₂) (T₀ , T₁ , T₀) = refl
*27-comm (T₀ , T₂ , T₂) (T₀ , T₁ , T₁) = refl
*27-comm (T₀ , T₂ , T₂) (T₀ , T₁ , T₂) = refl
*27-comm (T₀ , T₂ , T₂) (T₀ , T₂ , T₀) = refl
*27-comm (T₀ , T₂ , T₂) (T₀ , T₂ , T₁) = refl
*27-comm (T₀ , T₂ , T₂) (T₀ , T₂ , T₂) = refl
*27-comm (T₀ , T₂ , T₂) (T₁ , T₀ , T₀) = refl
*27-comm (T₀ , T₂ , T₂) (T₁ , T₀ , T₁) = refl
*27-comm (T₀ , T₂ , T₂) (T₁ , T₀ , T₂) = refl
*27-comm (T₀ , T₂ , T₂) (T₁ , T₁ , T₀) = refl
*27-comm (T₀ , T₂ , T₂) (T₁ , T₁ , T₁) = refl
*27-comm (T₀ , T₂ , T₂) (T₁ , T₁ , T₂) = refl
*27-comm (T₀ , T₂ , T₂) (T₁ , T₂ , T₀) = refl
*27-comm (T₀ , T₂ , T₂) (T₁ , T₂ , T₁) = refl
*27-comm (T₀ , T₂ , T₂) (T₁ , T₂ , T₂) = refl
*27-comm (T₀ , T₂ , T₂) (T₂ , T₀ , T₀) = refl
*27-comm (T₀ , T₂ , T₂) (T₂ , T₀ , T₁) = refl
*27-comm (T₀ , T₂ , T₂) (T₂ , T₀ , T₂) = refl
*27-comm (T₀ , T₂ , T₂) (T₂ , T₁ , T₀) = refl
*27-comm (T₀ , T₂ , T₂) (T₂ , T₁ , T₁) = refl
*27-comm (T₀ , T₂ , T₂) (T₂ , T₁ , T₂) = refl
*27-comm (T₀ , T₂ , T₂) (T₂ , T₂ , T₀) = refl
*27-comm (T₀ , T₂ , T₂) (T₂ , T₂ , T₁) = refl
*27-comm (T₀ , T₂ , T₂) (T₂ , T₂ , T₂) = refl
*27-comm (T₁ , T₀ , T₀) (T₀ , T₀ , T₀) = refl
*27-comm (T₁ , T₀ , T₀) (T₀ , T₀ , T₁) = refl
*27-comm (T₁ , T₀ , T₀) (T₀ , T₀ , T₂) = refl
*27-comm (T₁ , T₀ , T₀) (T₀ , T₁ , T₀) = refl
*27-comm (T₁ , T₀ , T₀) (T₀ , T₁ , T₁) = refl
*27-comm (T₁ , T₀ , T₀) (T₀ , T₁ , T₂) = refl
*27-comm (T₁ , T₀ , T₀) (T₀ , T₂ , T₀) = refl
*27-comm (T₁ , T₀ , T₀) (T₀ , T₂ , T₁) = refl
*27-comm (T₁ , T₀ , T₀) (T₀ , T₂ , T₂) = refl
*27-comm (T₁ , T₀ , T₀) (T₁ , T₀ , T₀) = refl
*27-comm (T₁ , T₀ , T₀) (T₁ , T₀ , T₁) = refl
*27-comm (T₁ , T₀ , T₀) (T₁ , T₀ , T₂) = refl
*27-comm (T₁ , T₀ , T₀) (T₁ , T₁ , T₀) = refl
*27-comm (T₁ , T₀ , T₀) (T₁ , T₁ , T₁) = refl
*27-comm (T₁ , T₀ , T₀) (T₁ , T₁ , T₂) = refl
*27-comm (T₁ , T₀ , T₀) (T₁ , T₂ , T₀) = refl
*27-comm (T₁ , T₀ , T₀) (T₁ , T₂ , T₁) = refl
*27-comm (T₁ , T₀ , T₀) (T₁ , T₂ , T₂) = refl
*27-comm (T₁ , T₀ , T₀) (T₂ , T₀ , T₀) = refl
*27-comm (T₁ , T₀ , T₀) (T₂ , T₀ , T₁) = refl
*27-comm (T₁ , T₀ , T₀) (T₂ , T₀ , T₂) = refl
*27-comm (T₁ , T₀ , T₀) (T₂ , T₁ , T₀) = refl
*27-comm (T₁ , T₀ , T₀) (T₂ , T₁ , T₁) = refl
*27-comm (T₁ , T₀ , T₀) (T₂ , T₁ , T₂) = refl
*27-comm (T₁ , T₀ , T₀) (T₂ , T₂ , T₀) = refl
*27-comm (T₁ , T₀ , T₀) (T₂ , T₂ , T₁) = refl
*27-comm (T₁ , T₀ , T₀) (T₂ , T₂ , T₂) = refl
*27-comm (T₁ , T₀ , T₁) (T₀ , T₀ , T₀) = refl
*27-comm (T₁ , T₀ , T₁) (T₀ , T₀ , T₁) = refl
*27-comm (T₁ , T₀ , T₁) (T₀ , T₀ , T₂) = refl
*27-comm (T₁ , T₀ , T₁) (T₀ , T₁ , T₀) = refl
*27-comm (T₁ , T₀ , T₁) (T₀ , T₁ , T₁) = refl
*27-comm (T₁ , T₀ , T₁) (T₀ , T₁ , T₂) = refl
*27-comm (T₁ , T₀ , T₁) (T₀ , T₂ , T₀) = refl
*27-comm (T₁ , T₀ , T₁) (T₀ , T₂ , T₁) = refl
*27-comm (T₁ , T₀ , T₁) (T₀ , T₂ , T₂) = refl
*27-comm (T₁ , T₀ , T₁) (T₁ , T₀ , T₀) = refl
*27-comm (T₁ , T₀ , T₁) (T₁ , T₀ , T₁) = refl
*27-comm (T₁ , T₀ , T₁) (T₁ , T₀ , T₂) = refl
*27-comm (T₁ , T₀ , T₁) (T₁ , T₁ , T₀) = refl
*27-comm (T₁ , T₀ , T₁) (T₁ , T₁ , T₁) = refl
*27-comm (T₁ , T₀ , T₁) (T₁ , T₁ , T₂) = refl
*27-comm (T₁ , T₀ , T₁) (T₁ , T₂ , T₀) = refl
*27-comm (T₁ , T₀ , T₁) (T₁ , T₂ , T₁) = refl
*27-comm (T₁ , T₀ , T₁) (T₁ , T₂ , T₂) = refl
*27-comm (T₁ , T₀ , T₁) (T₂ , T₀ , T₀) = refl
*27-comm (T₁ , T₀ , T₁) (T₂ , T₀ , T₁) = refl
*27-comm (T₁ , T₀ , T₁) (T₂ , T₀ , T₂) = refl
*27-comm (T₁ , T₀ , T₁) (T₂ , T₁ , T₀) = refl
*27-comm (T₁ , T₀ , T₁) (T₂ , T₁ , T₁) = refl
*27-comm (T₁ , T₀ , T₁) (T₂ , T₁ , T₂) = refl
*27-comm (T₁ , T₀ , T₁) (T₂ , T₂ , T₀) = refl
*27-comm (T₁ , T₀ , T₁) (T₂ , T₂ , T₁) = refl
*27-comm (T₁ , T₀ , T₁) (T₂ , T₂ , T₂) = refl
*27-comm (T₁ , T₀ , T₂) (T₀ , T₀ , T₀) = refl
*27-comm (T₁ , T₀ , T₂) (T₀ , T₀ , T₁) = refl
*27-comm (T₁ , T₀ , T₂) (T₀ , T₀ , T₂) = refl
*27-comm (T₁ , T₀ , T₂) (T₀ , T₁ , T₀) = refl
*27-comm (T₁ , T₀ , T₂) (T₀ , T₁ , T₁) = refl
*27-comm (T₁ , T₀ , T₂) (T₀ , T₁ , T₂) = refl
*27-comm (T₁ , T₀ , T₂) (T₀ , T₂ , T₀) = refl
*27-comm (T₁ , T₀ , T₂) (T₀ , T₂ , T₁) = refl
*27-comm (T₁ , T₀ , T₂) (T₀ , T₂ , T₂) = refl
*27-comm (T₁ , T₀ , T₂) (T₁ , T₀ , T₀) = refl
*27-comm (T₁ , T₀ , T₂) (T₁ , T₀ , T₁) = refl
*27-comm (T₁ , T₀ , T₂) (T₁ , T₀ , T₂) = refl
*27-comm (T₁ , T₀ , T₂) (T₁ , T₁ , T₀) = refl
*27-comm (T₁ , T₀ , T₂) (T₁ , T₁ , T₁) = refl
*27-comm (T₁ , T₀ , T₂) (T₁ , T₁ , T₂) = refl
*27-comm (T₁ , T₀ , T₂) (T₁ , T₂ , T₀) = refl
*27-comm (T₁ , T₀ , T₂) (T₁ , T₂ , T₁) = refl
*27-comm (T₁ , T₀ , T₂) (T₁ , T₂ , T₂) = refl
*27-comm (T₁ , T₀ , T₂) (T₂ , T₀ , T₀) = refl
*27-comm (T₁ , T₀ , T₂) (T₂ , T₀ , T₁) = refl
*27-comm (T₁ , T₀ , T₂) (T₂ , T₀ , T₂) = refl
*27-comm (T₁ , T₀ , T₂) (T₂ , T₁ , T₀) = refl
*27-comm (T₁ , T₀ , T₂) (T₂ , T₁ , T₁) = refl
*27-comm (T₁ , T₀ , T₂) (T₂ , T₁ , T₂) = refl
*27-comm (T₁ , T₀ , T₂) (T₂ , T₂ , T₀) = refl
*27-comm (T₁ , T₀ , T₂) (T₂ , T₂ , T₁) = refl
*27-comm (T₁ , T₀ , T₂) (T₂ , T₂ , T₂) = refl
*27-comm (T₁ , T₁ , T₀) (T₀ , T₀ , T₀) = refl
*27-comm (T₁ , T₁ , T₀) (T₀ , T₀ , T₁) = refl
*27-comm (T₁ , T₁ , T₀) (T₀ , T₀ , T₂) = refl
*27-comm (T₁ , T₁ , T₀) (T₀ , T₁ , T₀) = refl
*27-comm (T₁ , T₁ , T₀) (T₀ , T₁ , T₁) = refl
*27-comm (T₁ , T₁ , T₀) (T₀ , T₁ , T₂) = refl
*27-comm (T₁ , T₁ , T₀) (T₀ , T₂ , T₀) = refl
*27-comm (T₁ , T₁ , T₀) (T₀ , T₂ , T₁) = refl
*27-comm (T₁ , T₁ , T₀) (T₀ , T₂ , T₂) = refl
*27-comm (T₁ , T₁ , T₀) (T₁ , T₀ , T₀) = refl
*27-comm (T₁ , T₁ , T₀) (T₁ , T₀ , T₁) = refl
*27-comm (T₁ , T₁ , T₀) (T₁ , T₀ , T₂) = refl
*27-comm (T₁ , T₁ , T₀) (T₁ , T₁ , T₀) = refl
*27-comm (T₁ , T₁ , T₀) (T₁ , T₁ , T₁) = refl
*27-comm (T₁ , T₁ , T₀) (T₁ , T₁ , T₂) = refl
*27-comm (T₁ , T₁ , T₀) (T₁ , T₂ , T₀) = refl
*27-comm (T₁ , T₁ , T₀) (T₁ , T₂ , T₁) = refl
*27-comm (T₁ , T₁ , T₀) (T₁ , T₂ , T₂) = refl
*27-comm (T₁ , T₁ , T₀) (T₂ , T₀ , T₀) = refl
*27-comm (T₁ , T₁ , T₀) (T₂ , T₀ , T₁) = refl
*27-comm (T₁ , T₁ , T₀) (T₂ , T₀ , T₂) = refl
*27-comm (T₁ , T₁ , T₀) (T₂ , T₁ , T₀) = refl
*27-comm (T₁ , T₁ , T₀) (T₂ , T₁ , T₁) = refl
*27-comm (T₁ , T₁ , T₀) (T₂ , T₁ , T₂) = refl
*27-comm (T₁ , T₁ , T₀) (T₂ , T₂ , T₀) = refl
*27-comm (T₁ , T₁ , T₀) (T₂ , T₂ , T₁) = refl
*27-comm (T₁ , T₁ , T₀) (T₂ , T₂ , T₂) = refl
*27-comm (T₁ , T₁ , T₁) (T₀ , T₀ , T₀) = refl
*27-comm (T₁ , T₁ , T₁) (T₀ , T₀ , T₁) = refl
*27-comm (T₁ , T₁ , T₁) (T₀ , T₀ , T₂) = refl
*27-comm (T₁ , T₁ , T₁) (T₀ , T₁ , T₀) = refl
*27-comm (T₁ , T₁ , T₁) (T₀ , T₁ , T₁) = refl
*27-comm (T₁ , T₁ , T₁) (T₀ , T₁ , T₂) = refl
*27-comm (T₁ , T₁ , T₁) (T₀ , T₂ , T₀) = refl
*27-comm (T₁ , T₁ , T₁) (T₀ , T₂ , T₁) = refl
*27-comm (T₁ , T₁ , T₁) (T₀ , T₂ , T₂) = refl
*27-comm (T₁ , T₁ , T₁) (T₁ , T₀ , T₀) = refl
*27-comm (T₁ , T₁ , T₁) (T₁ , T₀ , T₁) = refl
*27-comm (T₁ , T₁ , T₁) (T₁ , T₀ , T₂) = refl
*27-comm (T₁ , T₁ , T₁) (T₁ , T₁ , T₀) = refl
*27-comm (T₁ , T₁ , T₁) (T₁ , T₁ , T₁) = refl
*27-comm (T₁ , T₁ , T₁) (T₁ , T₁ , T₂) = refl
*27-comm (T₁ , T₁ , T₁) (T₁ , T₂ , T₀) = refl
*27-comm (T₁ , T₁ , T₁) (T₁ , T₂ , T₁) = refl
*27-comm (T₁ , T₁ , T₁) (T₁ , T₂ , T₂) = refl
*27-comm (T₁ , T₁ , T₁) (T₂ , T₀ , T₀) = refl
*27-comm (T₁ , T₁ , T₁) (T₂ , T₀ , T₁) = refl
*27-comm (T₁ , T₁ , T₁) (T₂ , T₀ , T₂) = refl
*27-comm (T₁ , T₁ , T₁) (T₂ , T₁ , T₀) = refl
*27-comm (T₁ , T₁ , T₁) (T₂ , T₁ , T₁) = refl
*27-comm (T₁ , T₁ , T₁) (T₂ , T₁ , T₂) = refl
*27-comm (T₁ , T₁ , T₁) (T₂ , T₂ , T₀) = refl
*27-comm (T₁ , T₁ , T₁) (T₂ , T₂ , T₁) = refl
*27-comm (T₁ , T₁ , T₁) (T₂ , T₂ , T₂) = refl
*27-comm (T₁ , T₁ , T₂) (T₀ , T₀ , T₀) = refl
*27-comm (T₁ , T₁ , T₂) (T₀ , T₀ , T₁) = refl
*27-comm (T₁ , T₁ , T₂) (T₀ , T₀ , T₂) = refl
*27-comm (T₁ , T₁ , T₂) (T₀ , T₁ , T₀) = refl
*27-comm (T₁ , T₁ , T₂) (T₀ , T₁ , T₁) = refl
*27-comm (T₁ , T₁ , T₂) (T₀ , T₁ , T₂) = refl
*27-comm (T₁ , T₁ , T₂) (T₀ , T₂ , T₀) = refl
*27-comm (T₁ , T₁ , T₂) (T₀ , T₂ , T₁) = refl
*27-comm (T₁ , T₁ , T₂) (T₀ , T₂ , T₂) = refl
*27-comm (T₁ , T₁ , T₂) (T₁ , T₀ , T₀) = refl
*27-comm (T₁ , T₁ , T₂) (T₁ , T₀ , T₁) = refl
*27-comm (T₁ , T₁ , T₂) (T₁ , T₀ , T₂) = refl
*27-comm (T₁ , T₁ , T₂) (T₁ , T₁ , T₀) = refl
*27-comm (T₁ , T₁ , T₂) (T₁ , T₁ , T₁) = refl
*27-comm (T₁ , T₁ , T₂) (T₁ , T₁ , T₂) = refl
*27-comm (T₁ , T₁ , T₂) (T₁ , T₂ , T₀) = refl
*27-comm (T₁ , T₁ , T₂) (T₁ , T₂ , T₁) = refl
*27-comm (T₁ , T₁ , T₂) (T₁ , T₂ , T₂) = refl
*27-comm (T₁ , T₁ , T₂) (T₂ , T₀ , T₀) = refl
*27-comm (T₁ , T₁ , T₂) (T₂ , T₀ , T₁) = refl
*27-comm (T₁ , T₁ , T₂) (T₂ , T₀ , T₂) = refl
*27-comm (T₁ , T₁ , T₂) (T₂ , T₁ , T₀) = refl
*27-comm (T₁ , T₁ , T₂) (T₂ , T₁ , T₁) = refl
*27-comm (T₁ , T₁ , T₂) (T₂ , T₁ , T₂) = refl
*27-comm (T₁ , T₁ , T₂) (T₂ , T₂ , T₀) = refl
*27-comm (T₁ , T₁ , T₂) (T₂ , T₂ , T₁) = refl
*27-comm (T₁ , T₁ , T₂) (T₂ , T₂ , T₂) = refl
*27-comm (T₁ , T₂ , T₀) (T₀ , T₀ , T₀) = refl
*27-comm (T₁ , T₂ , T₀) (T₀ , T₀ , T₁) = refl
*27-comm (T₁ , T₂ , T₀) (T₀ , T₀ , T₂) = refl
*27-comm (T₁ , T₂ , T₀) (T₀ , T₁ , T₀) = refl
*27-comm (T₁ , T₂ , T₀) (T₀ , T₁ , T₁) = refl
*27-comm (T₁ , T₂ , T₀) (T₀ , T₁ , T₂) = refl
*27-comm (T₁ , T₂ , T₀) (T₀ , T₂ , T₀) = refl
*27-comm (T₁ , T₂ , T₀) (T₀ , T₂ , T₁) = refl
*27-comm (T₁ , T₂ , T₀) (T₀ , T₂ , T₂) = refl
*27-comm (T₁ , T₂ , T₀) (T₁ , T₀ , T₀) = refl
*27-comm (T₁ , T₂ , T₀) (T₁ , T₀ , T₁) = refl
*27-comm (T₁ , T₂ , T₀) (T₁ , T₀ , T₂) = refl
*27-comm (T₁ , T₂ , T₀) (T₁ , T₁ , T₀) = refl
*27-comm (T₁ , T₂ , T₀) (T₁ , T₁ , T₁) = refl
*27-comm (T₁ , T₂ , T₀) (T₁ , T₁ , T₂) = refl
*27-comm (T₁ , T₂ , T₀) (T₁ , T₂ , T₀) = refl
*27-comm (T₁ , T₂ , T₀) (T₁ , T₂ , T₁) = refl
*27-comm (T₁ , T₂ , T₀) (T₁ , T₂ , T₂) = refl
*27-comm (T₁ , T₂ , T₀) (T₂ , T₀ , T₀) = refl
*27-comm (T₁ , T₂ , T₀) (T₂ , T₀ , T₁) = refl
*27-comm (T₁ , T₂ , T₀) (T₂ , T₀ , T₂) = refl
*27-comm (T₁ , T₂ , T₀) (T₂ , T₁ , T₀) = refl
*27-comm (T₁ , T₂ , T₀) (T₂ , T₁ , T₁) = refl
*27-comm (T₁ , T₂ , T₀) (T₂ , T₁ , T₂) = refl
*27-comm (T₁ , T₂ , T₀) (T₂ , T₂ , T₀) = refl
*27-comm (T₁ , T₂ , T₀) (T₂ , T₂ , T₁) = refl
*27-comm (T₁ , T₂ , T₀) (T₂ , T₂ , T₂) = refl
*27-comm (T₁ , T₂ , T₁) (T₀ , T₀ , T₀) = refl
*27-comm (T₁ , T₂ , T₁) (T₀ , T₀ , T₁) = refl
*27-comm (T₁ , T₂ , T₁) (T₀ , T₀ , T₂) = refl
*27-comm (T₁ , T₂ , T₁) (T₀ , T₁ , T₀) = refl
*27-comm (T₁ , T₂ , T₁) (T₀ , T₁ , T₁) = refl
*27-comm (T₁ , T₂ , T₁) (T₀ , T₁ , T₂) = refl
*27-comm (T₁ , T₂ , T₁) (T₀ , T₂ , T₀) = refl
*27-comm (T₁ , T₂ , T₁) (T₀ , T₂ , T₁) = refl
*27-comm (T₁ , T₂ , T₁) (T₀ , T₂ , T₂) = refl
*27-comm (T₁ , T₂ , T₁) (T₁ , T₀ , T₀) = refl
*27-comm (T₁ , T₂ , T₁) (T₁ , T₀ , T₁) = refl
*27-comm (T₁ , T₂ , T₁) (T₁ , T₀ , T₂) = refl
*27-comm (T₁ , T₂ , T₁) (T₁ , T₁ , T₀) = refl
*27-comm (T₁ , T₂ , T₁) (T₁ , T₁ , T₁) = refl
*27-comm (T₁ , T₂ , T₁) (T₁ , T₁ , T₂) = refl
*27-comm (T₁ , T₂ , T₁) (T₁ , T₂ , T₀) = refl
*27-comm (T₁ , T₂ , T₁) (T₁ , T₂ , T₁) = refl
*27-comm (T₁ , T₂ , T₁) (T₁ , T₂ , T₂) = refl
*27-comm (T₁ , T₂ , T₁) (T₂ , T₀ , T₀) = refl
*27-comm (T₁ , T₂ , T₁) (T₂ , T₀ , T₁) = refl
*27-comm (T₁ , T₂ , T₁) (T₂ , T₀ , T₂) = refl
*27-comm (T₁ , T₂ , T₁) (T₂ , T₁ , T₀) = refl
*27-comm (T₁ , T₂ , T₁) (T₂ , T₁ , T₁) = refl
*27-comm (T₁ , T₂ , T₁) (T₂ , T₁ , T₂) = refl
*27-comm (T₁ , T₂ , T₁) (T₂ , T₂ , T₀) = refl
*27-comm (T₁ , T₂ , T₁) (T₂ , T₂ , T₁) = refl
*27-comm (T₁ , T₂ , T₁) (T₂ , T₂ , T₂) = refl
*27-comm (T₁ , T₂ , T₂) (T₀ , T₀ , T₀) = refl
*27-comm (T₁ , T₂ , T₂) (T₀ , T₀ , T₁) = refl
*27-comm (T₁ , T₂ , T₂) (T₀ , T₀ , T₂) = refl
*27-comm (T₁ , T₂ , T₂) (T₀ , T₁ , T₀) = refl
*27-comm (T₁ , T₂ , T₂) (T₀ , T₁ , T₁) = refl
*27-comm (T₁ , T₂ , T₂) (T₀ , T₁ , T₂) = refl
*27-comm (T₁ , T₂ , T₂) (T₀ , T₂ , T₀) = refl
*27-comm (T₁ , T₂ , T₂) (T₀ , T₂ , T₁) = refl
*27-comm (T₁ , T₂ , T₂) (T₀ , T₂ , T₂) = refl
*27-comm (T₁ , T₂ , T₂) (T₁ , T₀ , T₀) = refl
*27-comm (T₁ , T₂ , T₂) (T₁ , T₀ , T₁) = refl
*27-comm (T₁ , T₂ , T₂) (T₁ , T₀ , T₂) = refl
*27-comm (T₁ , T₂ , T₂) (T₁ , T₁ , T₀) = refl
*27-comm (T₁ , T₂ , T₂) (T₁ , T₁ , T₁) = refl
*27-comm (T₁ , T₂ , T₂) (T₁ , T₁ , T₂) = refl
*27-comm (T₁ , T₂ , T₂) (T₁ , T₂ , T₀) = refl
*27-comm (T₁ , T₂ , T₂) (T₁ , T₂ , T₁) = refl
*27-comm (T₁ , T₂ , T₂) (T₁ , T₂ , T₂) = refl
*27-comm (T₁ , T₂ , T₂) (T₂ , T₀ , T₀) = refl
*27-comm (T₁ , T₂ , T₂) (T₂ , T₀ , T₁) = refl
*27-comm (T₁ , T₂ , T₂) (T₂ , T₀ , T₂) = refl
*27-comm (T₁ , T₂ , T₂) (T₂ , T₁ , T₀) = refl
*27-comm (T₁ , T₂ , T₂) (T₂ , T₁ , T₁) = refl
*27-comm (T₁ , T₂ , T₂) (T₂ , T₁ , T₂) = refl
*27-comm (T₁ , T₂ , T₂) (T₂ , T₂ , T₀) = refl
*27-comm (T₁ , T₂ , T₂) (T₂ , T₂ , T₁) = refl
*27-comm (T₁ , T₂ , T₂) (T₂ , T₂ , T₂) = refl
*27-comm (T₂ , T₀ , T₀) (T₀ , T₀ , T₀) = refl
*27-comm (T₂ , T₀ , T₀) (T₀ , T₀ , T₁) = refl
*27-comm (T₂ , T₀ , T₀) (T₀ , T₀ , T₂) = refl
*27-comm (T₂ , T₀ , T₀) (T₀ , T₁ , T₀) = refl
*27-comm (T₂ , T₀ , T₀) (T₀ , T₁ , T₁) = refl
*27-comm (T₂ , T₀ , T₀) (T₀ , T₁ , T₂) = refl
*27-comm (T₂ , T₀ , T₀) (T₀ , T₂ , T₀) = refl
*27-comm (T₂ , T₀ , T₀) (T₀ , T₂ , T₁) = refl
*27-comm (T₂ , T₀ , T₀) (T₀ , T₂ , T₂) = refl
*27-comm (T₂ , T₀ , T₀) (T₁ , T₀ , T₀) = refl
*27-comm (T₂ , T₀ , T₀) (T₁ , T₀ , T₁) = refl
*27-comm (T₂ , T₀ , T₀) (T₁ , T₀ , T₂) = refl
*27-comm (T₂ , T₀ , T₀) (T₁ , T₁ , T₀) = refl
*27-comm (T₂ , T₀ , T₀) (T₁ , T₁ , T₁) = refl
*27-comm (T₂ , T₀ , T₀) (T₁ , T₁ , T₂) = refl
*27-comm (T₂ , T₀ , T₀) (T₁ , T₂ , T₀) = refl
*27-comm (T₂ , T₀ , T₀) (T₁ , T₂ , T₁) = refl
*27-comm (T₂ , T₀ , T₀) (T₁ , T₂ , T₂) = refl
*27-comm (T₂ , T₀ , T₀) (T₂ , T₀ , T₀) = refl
*27-comm (T₂ , T₀ , T₀) (T₂ , T₀ , T₁) = refl
*27-comm (T₂ , T₀ , T₀) (T₂ , T₀ , T₂) = refl
*27-comm (T₂ , T₀ , T₀) (T₂ , T₁ , T₀) = refl
*27-comm (T₂ , T₀ , T₀) (T₂ , T₁ , T₁) = refl
*27-comm (T₂ , T₀ , T₀) (T₂ , T₁ , T₂) = refl
*27-comm (T₂ , T₀ , T₀) (T₂ , T₂ , T₀) = refl
*27-comm (T₂ , T₀ , T₀) (T₂ , T₂ , T₁) = refl
*27-comm (T₂ , T₀ , T₀) (T₂ , T₂ , T₂) = refl
*27-comm (T₂ , T₀ , T₁) (T₀ , T₀ , T₀) = refl
*27-comm (T₂ , T₀ , T₁) (T₀ , T₀ , T₁) = refl
*27-comm (T₂ , T₀ , T₁) (T₀ , T₀ , T₂) = refl
*27-comm (T₂ , T₀ , T₁) (T₀ , T₁ , T₀) = refl
*27-comm (T₂ , T₀ , T₁) (T₀ , T₁ , T₁) = refl
*27-comm (T₂ , T₀ , T₁) (T₀ , T₁ , T₂) = refl
*27-comm (T₂ , T₀ , T₁) (T₀ , T₂ , T₀) = refl
*27-comm (T₂ , T₀ , T₁) (T₀ , T₂ , T₁) = refl
*27-comm (T₂ , T₀ , T₁) (T₀ , T₂ , T₂) = refl
*27-comm (T₂ , T₀ , T₁) (T₁ , T₀ , T₀) = refl
*27-comm (T₂ , T₀ , T₁) (T₁ , T₀ , T₁) = refl
*27-comm (T₂ , T₀ , T₁) (T₁ , T₀ , T₂) = refl
*27-comm (T₂ , T₀ , T₁) (T₁ , T₁ , T₀) = refl
*27-comm (T₂ , T₀ , T₁) (T₁ , T₁ , T₁) = refl
*27-comm (T₂ , T₀ , T₁) (T₁ , T₁ , T₂) = refl
*27-comm (T₂ , T₀ , T₁) (T₁ , T₂ , T₀) = refl
*27-comm (T₂ , T₀ , T₁) (T₁ , T₂ , T₁) = refl
*27-comm (T₂ , T₀ , T₁) (T₁ , T₂ , T₂) = refl
*27-comm (T₂ , T₀ , T₁) (T₂ , T₀ , T₀) = refl
*27-comm (T₂ , T₀ , T₁) (T₂ , T₀ , T₁) = refl
*27-comm (T₂ , T₀ , T₁) (T₂ , T₀ , T₂) = refl
*27-comm (T₂ , T₀ , T₁) (T₂ , T₁ , T₀) = refl
*27-comm (T₂ , T₀ , T₁) (T₂ , T₁ , T₁) = refl
*27-comm (T₂ , T₀ , T₁) (T₂ , T₁ , T₂) = refl
*27-comm (T₂ , T₀ , T₁) (T₂ , T₂ , T₀) = refl
*27-comm (T₂ , T₀ , T₁) (T₂ , T₂ , T₁) = refl
*27-comm (T₂ , T₀ , T₁) (T₂ , T₂ , T₂) = refl
*27-comm (T₂ , T₀ , T₂) (T₀ , T₀ , T₀) = refl
*27-comm (T₂ , T₀ , T₂) (T₀ , T₀ , T₁) = refl
*27-comm (T₂ , T₀ , T₂) (T₀ , T₀ , T₂) = refl
*27-comm (T₂ , T₀ , T₂) (T₀ , T₁ , T₀) = refl
*27-comm (T₂ , T₀ , T₂) (T₀ , T₁ , T₁) = refl
*27-comm (T₂ , T₀ , T₂) (T₀ , T₁ , T₂) = refl
*27-comm (T₂ , T₀ , T₂) (T₀ , T₂ , T₀) = refl
*27-comm (T₂ , T₀ , T₂) (T₀ , T₂ , T₁) = refl
*27-comm (T₂ , T₀ , T₂) (T₀ , T₂ , T₂) = refl
*27-comm (T₂ , T₀ , T₂) (T₁ , T₀ , T₀) = refl
*27-comm (T₂ , T₀ , T₂) (T₁ , T₀ , T₁) = refl
*27-comm (T₂ , T₀ , T₂) (T₁ , T₀ , T₂) = refl
*27-comm (T₂ , T₀ , T₂) (T₁ , T₁ , T₀) = refl
*27-comm (T₂ , T₀ , T₂) (T₁ , T₁ , T₁) = refl
*27-comm (T₂ , T₀ , T₂) (T₁ , T₁ , T₂) = refl
*27-comm (T₂ , T₀ , T₂) (T₁ , T₂ , T₀) = refl
*27-comm (T₂ , T₀ , T₂) (T₁ , T₂ , T₁) = refl
*27-comm (T₂ , T₀ , T₂) (T₁ , T₂ , T₂) = refl
*27-comm (T₂ , T₀ , T₂) (T₂ , T₀ , T₀) = refl
*27-comm (T₂ , T₀ , T₂) (T₂ , T₀ , T₁) = refl
*27-comm (T₂ , T₀ , T₂) (T₂ , T₀ , T₂) = refl
*27-comm (T₂ , T₀ , T₂) (T₂ , T₁ , T₀) = refl
*27-comm (T₂ , T₀ , T₂) (T₂ , T₁ , T₁) = refl
*27-comm (T₂ , T₀ , T₂) (T₂ , T₁ , T₂) = refl
*27-comm (T₂ , T₀ , T₂) (T₂ , T₂ , T₀) = refl
*27-comm (T₂ , T₀ , T₂) (T₂ , T₂ , T₁) = refl
*27-comm (T₂ , T₀ , T₂) (T₂ , T₂ , T₂) = refl
*27-comm (T₂ , T₁ , T₀) (T₀ , T₀ , T₀) = refl
*27-comm (T₂ , T₁ , T₀) (T₀ , T₀ , T₁) = refl
*27-comm (T₂ , T₁ , T₀) (T₀ , T₀ , T₂) = refl
*27-comm (T₂ , T₁ , T₀) (T₀ , T₁ , T₀) = refl
*27-comm (T₂ , T₁ , T₀) (T₀ , T₁ , T₁) = refl
*27-comm (T₂ , T₁ , T₀) (T₀ , T₁ , T₂) = refl
*27-comm (T₂ , T₁ , T₀) (T₀ , T₂ , T₀) = refl
*27-comm (T₂ , T₁ , T₀) (T₀ , T₂ , T₁) = refl
*27-comm (T₂ , T₁ , T₀) (T₀ , T₂ , T₂) = refl
*27-comm (T₂ , T₁ , T₀) (T₁ , T₀ , T₀) = refl
*27-comm (T₂ , T₁ , T₀) (T₁ , T₀ , T₁) = refl
*27-comm (T₂ , T₁ , T₀) (T₁ , T₀ , T₂) = refl
*27-comm (T₂ , T₁ , T₀) (T₁ , T₁ , T₀) = refl
*27-comm (T₂ , T₁ , T₀) (T₁ , T₁ , T₁) = refl
*27-comm (T₂ , T₁ , T₀) (T₁ , T₁ , T₂) = refl
*27-comm (T₂ , T₁ , T₀) (T₁ , T₂ , T₀) = refl
*27-comm (T₂ , T₁ , T₀) (T₁ , T₂ , T₁) = refl
*27-comm (T₂ , T₁ , T₀) (T₁ , T₂ , T₂) = refl
*27-comm (T₂ , T₁ , T₀) (T₂ , T₀ , T₀) = refl
*27-comm (T₂ , T₁ , T₀) (T₂ , T₀ , T₁) = refl
*27-comm (T₂ , T₁ , T₀) (T₂ , T₀ , T₂) = refl
*27-comm (T₂ , T₁ , T₀) (T₂ , T₁ , T₀) = refl
*27-comm (T₂ , T₁ , T₀) (T₂ , T₁ , T₁) = refl
*27-comm (T₂ , T₁ , T₀) (T₂ , T₁ , T₂) = refl
*27-comm (T₂ , T₁ , T₀) (T₂ , T₂ , T₀) = refl
*27-comm (T₂ , T₁ , T₀) (T₂ , T₂ , T₁) = refl
*27-comm (T₂ , T₁ , T₀) (T₂ , T₂ , T₂) = refl
*27-comm (T₂ , T₁ , T₁) (T₀ , T₀ , T₀) = refl
*27-comm (T₂ , T₁ , T₁) (T₀ , T₀ , T₁) = refl
*27-comm (T₂ , T₁ , T₁) (T₀ , T₀ , T₂) = refl
*27-comm (T₂ , T₁ , T₁) (T₀ , T₁ , T₀) = refl
*27-comm (T₂ , T₁ , T₁) (T₀ , T₁ , T₁) = refl
*27-comm (T₂ , T₁ , T₁) (T₀ , T₁ , T₂) = refl
*27-comm (T₂ , T₁ , T₁) (T₀ , T₂ , T₀) = refl
*27-comm (T₂ , T₁ , T₁) (T₀ , T₂ , T₁) = refl
*27-comm (T₂ , T₁ , T₁) (T₀ , T₂ , T₂) = refl
*27-comm (T₂ , T₁ , T₁) (T₁ , T₀ , T₀) = refl
*27-comm (T₂ , T₁ , T₁) (T₁ , T₀ , T₁) = refl
*27-comm (T₂ , T₁ , T₁) (T₁ , T₀ , T₂) = refl
*27-comm (T₂ , T₁ , T₁) (T₁ , T₁ , T₀) = refl
*27-comm (T₂ , T₁ , T₁) (T₁ , T₁ , T₁) = refl
*27-comm (T₂ , T₁ , T₁) (T₁ , T₁ , T₂) = refl
*27-comm (T₂ , T₁ , T₁) (T₁ , T₂ , T₀) = refl
*27-comm (T₂ , T₁ , T₁) (T₁ , T₂ , T₁) = refl
*27-comm (T₂ , T₁ , T₁) (T₁ , T₂ , T₂) = refl
*27-comm (T₂ , T₁ , T₁) (T₂ , T₀ , T₀) = refl
*27-comm (T₂ , T₁ , T₁) (T₂ , T₀ , T₁) = refl
*27-comm (T₂ , T₁ , T₁) (T₂ , T₀ , T₂) = refl
*27-comm (T₂ , T₁ , T₁) (T₂ , T₁ , T₀) = refl
*27-comm (T₂ , T₁ , T₁) (T₂ , T₁ , T₁) = refl
*27-comm (T₂ , T₁ , T₁) (T₂ , T₁ , T₂) = refl
*27-comm (T₂ , T₁ , T₁) (T₂ , T₂ , T₀) = refl
*27-comm (T₂ , T₁ , T₁) (T₂ , T₂ , T₁) = refl
*27-comm (T₂ , T₁ , T₁) (T₂ , T₂ , T₂) = refl
*27-comm (T₂ , T₁ , T₂) (T₀ , T₀ , T₀) = refl
*27-comm (T₂ , T₁ , T₂) (T₀ , T₀ , T₁) = refl
*27-comm (T₂ , T₁ , T₂) (T₀ , T₀ , T₂) = refl
*27-comm (T₂ , T₁ , T₂) (T₀ , T₁ , T₀) = refl
*27-comm (T₂ , T₁ , T₂) (T₀ , T₁ , T₁) = refl
*27-comm (T₂ , T₁ , T₂) (T₀ , T₁ , T₂) = refl
*27-comm (T₂ , T₁ , T₂) (T₀ , T₂ , T₀) = refl
*27-comm (T₂ , T₁ , T₂) (T₀ , T₂ , T₁) = refl
*27-comm (T₂ , T₁ , T₂) (T₀ , T₂ , T₂) = refl
*27-comm (T₂ , T₁ , T₂) (T₁ , T₀ , T₀) = refl
*27-comm (T₂ , T₁ , T₂) (T₁ , T₀ , T₁) = refl
*27-comm (T₂ , T₁ , T₂) (T₁ , T₀ , T₂) = refl
*27-comm (T₂ , T₁ , T₂) (T₁ , T₁ , T₀) = refl
*27-comm (T₂ , T₁ , T₂) (T₁ , T₁ , T₁) = refl
*27-comm (T₂ , T₁ , T₂) (T₁ , T₁ , T₂) = refl
*27-comm (T₂ , T₁ , T₂) (T₁ , T₂ , T₀) = refl
*27-comm (T₂ , T₁ , T₂) (T₁ , T₂ , T₁) = refl
*27-comm (T₂ , T₁ , T₂) (T₁ , T₂ , T₂) = refl
*27-comm (T₂ , T₁ , T₂) (T₂ , T₀ , T₀) = refl
*27-comm (T₂ , T₁ , T₂) (T₂ , T₀ , T₁) = refl
*27-comm (T₂ , T₁ , T₂) (T₂ , T₀ , T₂) = refl
*27-comm (T₂ , T₁ , T₂) (T₂ , T₁ , T₀) = refl
*27-comm (T₂ , T₁ , T₂) (T₂ , T₁ , T₁) = refl
*27-comm (T₂ , T₁ , T₂) (T₂ , T₁ , T₂) = refl
*27-comm (T₂ , T₁ , T₂) (T₂ , T₂ , T₀) = refl
*27-comm (T₂ , T₁ , T₂) (T₂ , T₂ , T₁) = refl
*27-comm (T₂ , T₁ , T₂) (T₂ , T₂ , T₂) = refl
*27-comm (T₂ , T₂ , T₀) (T₀ , T₀ , T₀) = refl
*27-comm (T₂ , T₂ , T₀) (T₀ , T₀ , T₁) = refl
*27-comm (T₂ , T₂ , T₀) (T₀ , T₀ , T₂) = refl
*27-comm (T₂ , T₂ , T₀) (T₀ , T₁ , T₀) = refl
*27-comm (T₂ , T₂ , T₀) (T₀ , T₁ , T₁) = refl
*27-comm (T₂ , T₂ , T₀) (T₀ , T₁ , T₂) = refl
*27-comm (T₂ , T₂ , T₀) (T₀ , T₂ , T₀) = refl
*27-comm (T₂ , T₂ , T₀) (T₀ , T₂ , T₁) = refl
*27-comm (T₂ , T₂ , T₀) (T₀ , T₂ , T₂) = refl
*27-comm (T₂ , T₂ , T₀) (T₁ , T₀ , T₀) = refl
*27-comm (T₂ , T₂ , T₀) (T₁ , T₀ , T₁) = refl
*27-comm (T₂ , T₂ , T₀) (T₁ , T₀ , T₂) = refl
*27-comm (T₂ , T₂ , T₀) (T₁ , T₁ , T₀) = refl
*27-comm (T₂ , T₂ , T₀) (T₁ , T₁ , T₁) = refl
*27-comm (T₂ , T₂ , T₀) (T₁ , T₁ , T₂) = refl
*27-comm (T₂ , T₂ , T₀) (T₁ , T₂ , T₀) = refl
*27-comm (T₂ , T₂ , T₀) (T₁ , T₂ , T₁) = refl
*27-comm (T₂ , T₂ , T₀) (T₁ , T₂ , T₂) = refl
*27-comm (T₂ , T₂ , T₀) (T₂ , T₀ , T₀) = refl
*27-comm (T₂ , T₂ , T₀) (T₂ , T₀ , T₁) = refl
*27-comm (T₂ , T₂ , T₀) (T₂ , T₀ , T₂) = refl
*27-comm (T₂ , T₂ , T₀) (T₂ , T₁ , T₀) = refl
*27-comm (T₂ , T₂ , T₀) (T₂ , T₁ , T₁) = refl
*27-comm (T₂ , T₂ , T₀) (T₂ , T₁ , T₂) = refl
*27-comm (T₂ , T₂ , T₀) (T₂ , T₂ , T₀) = refl
*27-comm (T₂ , T₂ , T₀) (T₂ , T₂ , T₁) = refl
*27-comm (T₂ , T₂ , T₀) (T₂ , T₂ , T₂) = refl
*27-comm (T₂ , T₂ , T₁) (T₀ , T₀ , T₀) = refl
*27-comm (T₂ , T₂ , T₁) (T₀ , T₀ , T₁) = refl
*27-comm (T₂ , T₂ , T₁) (T₀ , T₀ , T₂) = refl
*27-comm (T₂ , T₂ , T₁) (T₀ , T₁ , T₀) = refl
*27-comm (T₂ , T₂ , T₁) (T₀ , T₁ , T₁) = refl
*27-comm (T₂ , T₂ , T₁) (T₀ , T₁ , T₂) = refl
*27-comm (T₂ , T₂ , T₁) (T₀ , T₂ , T₀) = refl
*27-comm (T₂ , T₂ , T₁) (T₀ , T₂ , T₁) = refl
*27-comm (T₂ , T₂ , T₁) (T₀ , T₂ , T₂) = refl
*27-comm (T₂ , T₂ , T₁) (T₁ , T₀ , T₀) = refl
*27-comm (T₂ , T₂ , T₁) (T₁ , T₀ , T₁) = refl
*27-comm (T₂ , T₂ , T₁) (T₁ , T₀ , T₂) = refl
*27-comm (T₂ , T₂ , T₁) (T₁ , T₁ , T₀) = refl
*27-comm (T₂ , T₂ , T₁) (T₁ , T₁ , T₁) = refl
*27-comm (T₂ , T₂ , T₁) (T₁ , T₁ , T₂) = refl
*27-comm (T₂ , T₂ , T₁) (T₁ , T₂ , T₀) = refl
*27-comm (T₂ , T₂ , T₁) (T₁ , T₂ , T₁) = refl
*27-comm (T₂ , T₂ , T₁) (T₁ , T₂ , T₂) = refl
*27-comm (T₂ , T₂ , T₁) (T₂ , T₀ , T₀) = refl
*27-comm (T₂ , T₂ , T₁) (T₂ , T₀ , T₁) = refl
*27-comm (T₂ , T₂ , T₁) (T₂ , T₀ , T₂) = refl
*27-comm (T₂ , T₂ , T₁) (T₂ , T₁ , T₀) = refl
*27-comm (T₂ , T₂ , T₁) (T₂ , T₁ , T₁) = refl
*27-comm (T₂ , T₂ , T₁) (T₂ , T₁ , T₂) = refl
*27-comm (T₂ , T₂ , T₁) (T₂ , T₂ , T₀) = refl
*27-comm (T₂ , T₂ , T₁) (T₂ , T₂ , T₁) = refl
*27-comm (T₂ , T₂ , T₁) (T₂ , T₂ , T₂) = refl
*27-comm (T₂ , T₂ , T₂) (T₀ , T₀ , T₀) = refl
*27-comm (T₂ , T₂ , T₂) (T₀ , T₀ , T₁) = refl
*27-comm (T₂ , T₂ , T₂) (T₀ , T₀ , T₂) = refl
*27-comm (T₂ , T₂ , T₂) (T₀ , T₁ , T₀) = refl
*27-comm (T₂ , T₂ , T₂) (T₀ , T₁ , T₁) = refl
*27-comm (T₂ , T₂ , T₂) (T₀ , T₁ , T₂) = refl
*27-comm (T₂ , T₂ , T₂) (T₀ , T₂ , T₀) = refl
*27-comm (T₂ , T₂ , T₂) (T₀ , T₂ , T₁) = refl
*27-comm (T₂ , T₂ , T₂) (T₀ , T₂ , T₂) = refl
*27-comm (T₂ , T₂ , T₂) (T₁ , T₀ , T₀) = refl
*27-comm (T₂ , T₂ , T₂) (T₁ , T₀ , T₁) = refl
*27-comm (T₂ , T₂ , T₂) (T₁ , T₀ , T₂) = refl
*27-comm (T₂ , T₂ , T₂) (T₁ , T₁ , T₀) = refl
*27-comm (T₂ , T₂ , T₂) (T₁ , T₁ , T₁) = refl
*27-comm (T₂ , T₂ , T₂) (T₁ , T₁ , T₂) = refl
*27-comm (T₂ , T₂ , T₂) (T₁ , T₂ , T₀) = refl
*27-comm (T₂ , T₂ , T₂) (T₁ , T₂ , T₁) = refl
*27-comm (T₂ , T₂ , T₂) (T₁ , T₂ , T₂) = refl
*27-comm (T₂ , T₂ , T₂) (T₂ , T₀ , T₀) = refl
*27-comm (T₂ , T₂ , T₂) (T₂ , T₀ , T₁) = refl
*27-comm (T₂ , T₂ , T₂) (T₂ , T₀ , T₂) = refl
*27-comm (T₂ , T₂ , T₂) (T₂ , T₁ , T₀) = refl
*27-comm (T₂ , T₂ , T₂) (T₂ , T₁ , T₁) = refl
*27-comm (T₂ , T₂ , T₂) (T₂ , T₁ , T₂) = refl
*27-comm (T₂ , T₂ , T₂) (T₂ , T₂ , T₀) = refl
*27-comm (T₂ , T₂ , T₂) (T₂ , T₂ , T₁) = refl
*27-comm (T₂ , T₂ , T₂) (T₂ , T₂ , T₂) = refl

-- 零律
*27-zeroˡ : ∀ x → zero27 *₉ x ≡ zero27
*27-zeroˡ (a , b , c) = cong₃ (λ p q r → p , q , r)
  (trans (cong₂ _+₃_ (⊗-zeroˡ a) (trans (cong₂ _+₃_ (⊗-zeroˡ c) (⊗-zeroˡ c)) (trans (⊕-identityʳ T₀) (⊕-identityʳ T₀))))
         (⊕-identityʳ T₀))
  (trans (cong₂ _+₃_ (⊗-zeroˡ a) (trans (cong₂ _+₃_ (⊗-zeroˡ b) (trans (cong₂ _+₃_ (⊗-zeroˡ c) (trans (cong₂ _+₃_ (⊗-zeroˡ c) (⊗-zeroˡ c)) (⊕-identityʳ T₀))) (⊕-identityʳ T₀))) (⊕-identityʳ T₀)))
         (⊕-identityʳ T₀))
  (trans (cong₂ _+₃_ (⊗-zeroˡ c) (trans (cong₂ _+₃_ (⊗-zeroˡ b) (trans (cong₂ _+₃_ (⊗-zeroˡ a) (trans (cong₂ _+₃_ (⊗-zeroˡ c) (⊗-zeroˡ c)) (⊕-identityʳ T₀))) (⊕-identityʳ T₀))) (⊕-identityʳ T₀)))
         (⊕-identityʳ T₀))

*27-zeroʳ : ∀ x → x *₉ zero27 ≡ zero27
*27-zeroʳ x = trans (*27-comm x zero27) (*27-zeroˡ x)

-- 幺律
*27-identityˡ : ∀ x → one27 *₉ x ≡ x
*27-identityˡ (a , b , c) = cong₃ (λ p q r → p , q , r)
  (trans (cong₂ _+₃_ (⊗-identityˡ a) (zeros4 c c b)) (⊕-identityʳ a))
  (trans (cong₂ _+₃_ (⊗-identityˡ b) (zeros5 a c b c)) (⊕-identityʳ b))
  (trans (cong₂ _+₃_ (⊗-identityˡ c) (zeros3 b a c)) (⊕-identityʳ c))
  where
    zeros4 : ∀ p q r → (T₀ ⊗ p) ⊕ ((T₀ ⊗ q) ⊕ ((T₀ ⊗ r) ⊕ (T₀ ⊗ r))) ≡ T₀
    zeros4 p q r = begin
      (T₀ ⊗ p) ⊕ ((T₀ ⊗ q) ⊕ ((T₀ ⊗ r) ⊕ (T₀ ⊗ r)))
        ≡⟨ cong₂ _+₃_ (⊗-zeroˡ p) (cong₂ _+₃_ (⊗-zeroˡ q) (cong₂ _+₃_ (⊗-zeroˡ r) (⊗-zeroˡ r))) ⟩
      T₀ ⊕ (T₀ ⊕ (T₀ ⊕ T₀))
        ≡⟨ ⊕-identityʳ (T₀ ⊕ (T₀ ⊕ T₀)) ⟩
      T₀ ⊕ (T₀ ⊕ T₀)
        ≡⟨ ⊕-identityʳ (T₀ ⊕ T₀) ⟩
      T₀ ⊕ T₀
        ≡⟨ ⊕-identityʳ T₀ ⟩
      T₀
      ∎
    zeros5 : ∀ p q r s → (T₀ ⊗ p) ⊕ ((T₀ ⊗ q) ⊕ ((T₀ ⊗ r) ⊕ ((T₀ ⊗ s) ⊕ (T₀ ⊗ s)))) ≡ T₀
    zeros5 p q r s = begin
      (T₀ ⊗ p) ⊕ ((T₀ ⊗ q) ⊕ ((T₀ ⊗ r) ⊕ ((T₀ ⊗ s) ⊕ (T₀ ⊗ s))))
        ≡⟨ cong₂ _+₃_ (⊗-zeroˡ p) (cong₂ _+₃_ (⊗-zeroˡ q) (cong₂ _+₃_ (⊗-zeroˡ r) (cong₂ _+₃_ (⊗-zeroˡ s) (⊗-zeroˡ s)))) ⟩
      T₀ ⊕ (T₀ ⊕ (T₀ ⊕ (T₀ ⊕ T₀)))
        ≡⟨ ⊕-identityʳ (T₀ ⊕ (T₀ ⊕ (T₀ ⊕ T₀))) ⟩
      T₀ ⊕ (T₀ ⊕ (T₀ ⊕ T₀))
        ≡⟨ ⊕-identityʳ (T₀ ⊕ (T₀ ⊕ T₀)) ⟩
      T₀ ⊕ (T₀ ⊕ T₀)
        ≡⟨ ⊕-identityʳ (T₀ ⊕ T₀) ⟩
      T₀ ⊕ T₀
        ≡⟨ ⊕-identityʳ T₀ ⟩
      T₀
      ∎
    zeros3 : ∀ p q r → (T₀ ⊗ p) ⊕ ((T₀ ⊗ q) ⊕ (T₀ ⊗ r)) ≡ T₀
    zeros3 p q r = begin
      (T₀ ⊗ p) ⊕ ((T₀ ⊗ q) ⊕ (T₀ ⊗ r))
        ≡⟨ cong₂ _+₃_ (⊗-zeroˡ p) (cong₂ _+₃_ (⊗-zeroˡ q) (⊗-zeroˡ r)) ⟩
      T₀ ⊕ (T₀ ⊕ T₀)
        ≡⟨ ⊕-identityʳ (T₀ ⊕ T₀) ⟩
      T₀ ⊕ T₀
        ≡⟨ ⊕-identityʳ T₀ ⟩
      T₀
      ∎

*27-identityʳ : ∀ x → x *₉ one27 ≡ x
*27-identityʳ (a , b , c) = cong₃ (λ p q r → p , q , r)
  (trans (cong₂ _+₃_ (⊗-identityʳ a) (zeros4r b b c)) (⊕-identityʳ a))
  (comp2-idr a b c)
  (comp3-idr a b c)
  where
    zeros4r : ∀ p q r → (p ⊗ T₀) ⊕ ((q ⊗ T₀) ⊕ ((r ⊗ T₀) ⊕ (r ⊗ T₀))) ≡ T₀
    zeros4r p q r = begin
      (p ⊗ T₀) ⊕ ((q ⊗ T₀) ⊕ ((r ⊗ T₀) ⊕ (r ⊗ T₀)))
        ≡⟨ cong₂ _+₃_ (⊗-zeroʳ p) (cong₂ _+₃_ (⊗-zeroʳ q) (cong₂ _+₃_ (⊗-zeroʳ r) (⊗-zeroʳ r))) ⟩
      T₀ ⊕ (T₀ ⊕ (T₀ ⊕ T₀))
        ≡⟨ ⊕-identityʳ (T₀ ⊕ (T₀ ⊕ T₀)) ⟩
      T₀ ⊕ (T₀ ⊕ T₀)
        ≡⟨ ⊕-identityʳ (T₀ ⊕ T₀) ⟩
      T₀ ⊕ T₀
        ≡⟨ ⊕-identityʳ T₀ ⟩
      T₀
      ∎
    zeros5r : ∀ p q r s → (p ⊗ T₀) ⊕ ((q ⊗ T₀) ⊕ ((r ⊗ T₀) ⊕ ((s ⊗ T₀) ⊕ (s ⊗ T₀)))) ≡ T₀
    zeros5r p q r s = begin
      (p ⊗ T₀) ⊕ ((q ⊗ T₀) ⊕ ((r ⊗ T₀) ⊕ ((s ⊗ T₀) ⊕ (s ⊗ T₀))))
        ≡⟨ cong₂ _+₃_ (⊗-zeroʳ p) (cong₂ _+₃_ (⊗-zeroʳ q) (cong₂ _+₃_ (⊗-zeroʳ r) (cong₂ _+₃_ (⊗-zeroʳ s) (⊗-zeroʳ s)))) ⟩
      T₀ ⊕ (T₀ ⊕ (T₀ ⊕ (T₀ ⊕ T₀)))
        ≡⟨ ⊕-identityʳ (T₀ ⊕ (T₀ ⊕ (T₀ ⊕ T₀))) ⟩
      T₀ ⊕ (T₀ ⊕ (T₀ ⊕ T₀))
        ≡⟨ ⊕-identityʳ (T₀ ⊕ (T₀ ⊕ T₀)) ⟩
      T₀ ⊕ (T₀ ⊕ T₀)
        ≡⟨ ⊕-identityʳ (T₀ ⊕ T₀) ⟩
      T₀ ⊕ T₀
        ≡⟨ ⊕-identityʳ T₀ ⟩
      T₀
      ∎
    comp2-idr : ∀ a b c → (a ⊗ T₀) ⊕ ((b ⊗ T₁) ⊕ ((b ⊗ T₀) ⊕ ((c ⊗ T₀) ⊕ ((c ⊗ T₀) ⊕ (c ⊗ T₀))))) ≡ b
    comp2-idr a b c = begin
      (a ⊗ T₀) ⊕ ((b ⊗ T₁) ⊕ ((b ⊗ T₀) ⊕ ((c ⊗ T₀) ⊕ ((c ⊗ T₀) ⊕ (c ⊗ T₀)))))
        ≡⟨ cong₂ _+₃_ (⊗-zeroʳ a) (cong₂ _+₃_ (⊗-identityʳ b) (zeros4r b c c)) ⟩
      T₀ ⊕ (b ⊕ T₀)
        ≡⟨ sym (⊕-assoc T₀ b T₀) ⟩
      (T₀ ⊕ b) ⊕ T₀
        ≡⟨ cong (_⊕ T₀) (⊕-comm T₀ b) ⟩
      (b ⊕ T₀) ⊕ T₀
        ≡⟨ ⊕-assoc b T₀ T₀ ⟩
      b ⊕ (T₀ ⊕ T₀)
        ≡⟨ cong (b ⊕_) (⊕-identityʳ T₀) ⟩
      b ⊕ T₀
        ≡⟨ ⊕-identityʳ b ⟩
      b
      ∎
    comp3-idr : ∀ a b c → (a ⊗ T₀) ⊕ ((b ⊗ T₀) ⊕ ((c ⊗ T₁) ⊕ (c ⊗ T₀))) ≡ c
    comp3-idr a b c = begin
      (a ⊗ T₀) ⊕ ((b ⊗ T₀) ⊕ ((c ⊗ T₁) ⊕ (c ⊗ T₀)))
        ≡⟨ cong₂ _+₃_ (⊗-zeroʳ a) (cong₂ _+₃_ (⊗-zeroʳ b) (cong₂ _+₃_ (⊗-identityʳ c) (⊗-zeroʳ c))) ⟩
      T₀ ⊕ (T₀ ⊕ (c ⊕ T₀))
        ≡⟨ cong (T₀ ⊕_) (sym (⊕-assoc T₀ c T₀)) ⟩
      T₀ ⊕ ((T₀ ⊕ c) ⊕ T₀)
        ≡⟨ cong (T₀ ⊕_) (cong (_⊕ T₀) (⊕-comm T₀ c)) ⟩
      T₀ ⊕ ((c ⊕ T₀) ⊕ T₀)
        ≡⟨ cong (T₀ ⊕_) (⊕-assoc c T₀ T₀) ⟩
      T₀ ⊕ (c ⊕ (T₀ ⊕ T₀))
        ≡⟨ cong (T₀ ⊕_) (cong (c ⊕_) (⊕-identityʳ T₀)) ⟩
      T₀ ⊕ (c ⊕ T₀)
        ≡⟨ sym (⊕-assoc T₀ c T₀) ⟩
      (T₀ ⊕ c) ⊕ T₀
        ≡⟨ cong (_⊕ T₀) (⊕-comm T₀ c) ⟩
      (c ⊕ T₀) ⊕ T₀
        ≡⟨ ⊕-assoc c T₀ T₀ ⟩
      c ⊕ (T₀ ⊕ T₀)
        ≡⟨ cong (c ⊕_) (⊕-identityʳ T₀) ⟩
      c ⊕ T₀
        ≡⟨ ⊕-identityʳ c ⟩
      c
      ∎
    zeros3r : ∀ p q r → (p ⊗ T₀) ⊕ ((q ⊗ T₀) ⊕ (r ⊗ T₀)) ≡ T₀
    zeros3r p q r = begin
      (p ⊗ T₀) ⊕ ((q ⊗ T₀) ⊕ (r ⊗ T₀))
        ≡⟨ cong₂ _+₃_ (⊗-zeroʳ p) (cong₂ _+₃_ (⊗-zeroʳ q) (⊗-zeroʳ r)) ⟩
      T₀ ⊕ (T₀ ⊕ T₀)
        ≡⟨ ⊕-identityʳ (T₀ ⊕ T₀) ⟩
      T₀ ⊕ T₀
        ≡⟨ ⊕-identityʳ T₀ ⟩
      T₀
      ∎

--------------------------------------------------------------------------------
-- §2. freshman's dream 与 γ-结合/分配 (729 case 穷举)
--------------------------------------------------------------------------------

-- Frobenius 乘法性: (xy)³ = x³y³
cube-mul : ∀ x y → cube27 (x *₉ y) ≡ (cube27 x) *₉ (cube27 y)
cube-mul (T₀ , T₀ , T₀) (T₀ , T₀ , T₀) = refl
cube-mul (T₀ , T₀ , T₀) (T₀ , T₀ , T₁) = refl
cube-mul (T₀ , T₀ , T₀) (T₀ , T₀ , T₂) = refl
cube-mul (T₀ , T₀ , T₀) (T₀ , T₁ , T₀) = refl
cube-mul (T₀ , T₀ , T₀) (T₀ , T₁ , T₁) = refl
cube-mul (T₀ , T₀ , T₀) (T₀ , T₁ , T₂) = refl
cube-mul (T₀ , T₀ , T₀) (T₀ , T₂ , T₀) = refl
cube-mul (T₀ , T₀ , T₀) (T₀ , T₂ , T₁) = refl
cube-mul (T₀ , T₀ , T₀) (T₀ , T₂ , T₂) = refl
cube-mul (T₀ , T₀ , T₀) (T₁ , T₀ , T₀) = refl
cube-mul (T₀ , T₀ , T₀) (T₁ , T₀ , T₁) = refl
cube-mul (T₀ , T₀ , T₀) (T₁ , T₀ , T₂) = refl
cube-mul (T₀ , T₀ , T₀) (T₁ , T₁ , T₀) = refl
cube-mul (T₀ , T₀ , T₀) (T₁ , T₁ , T₁) = refl
cube-mul (T₀ , T₀ , T₀) (T₁ , T₁ , T₂) = refl
cube-mul (T₀ , T₀ , T₀) (T₁ , T₂ , T₀) = refl
cube-mul (T₀ , T₀ , T₀) (T₁ , T₂ , T₁) = refl
cube-mul (T₀ , T₀ , T₀) (T₁ , T₂ , T₂) = refl
cube-mul (T₀ , T₀ , T₀) (T₂ , T₀ , T₀) = refl
cube-mul (T₀ , T₀ , T₀) (T₂ , T₀ , T₁) = refl
cube-mul (T₀ , T₀ , T₀) (T₂ , T₀ , T₂) = refl
cube-mul (T₀ , T₀ , T₀) (T₂ , T₁ , T₀) = refl
cube-mul (T₀ , T₀ , T₀) (T₂ , T₁ , T₁) = refl
cube-mul (T₀ , T₀ , T₀) (T₂ , T₁ , T₂) = refl
cube-mul (T₀ , T₀ , T₀) (T₂ , T₂ , T₀) = refl
cube-mul (T₀ , T₀ , T₀) (T₂ , T₂ , T₁) = refl
cube-mul (T₀ , T₀ , T₀) (T₂ , T₂ , T₂) = refl
cube-mul (T₀ , T₀ , T₁) (T₀ , T₀ , T₀) = refl
cube-mul (T₀ , T₀ , T₁) (T₀ , T₀ , T₁) = refl
cube-mul (T₀ , T₀ , T₁) (T₀ , T₀ , T₂) = refl
cube-mul (T₀ , T₀ , T₁) (T₀ , T₁ , T₀) = refl
cube-mul (T₀ , T₀ , T₁) (T₀ , T₁ , T₁) = refl
cube-mul (T₀ , T₀ , T₁) (T₀ , T₁ , T₂) = refl
cube-mul (T₀ , T₀ , T₁) (T₀ , T₂ , T₀) = refl
cube-mul (T₀ , T₀ , T₁) (T₀ , T₂ , T₁) = refl
cube-mul (T₀ , T₀ , T₁) (T₀ , T₂ , T₂) = refl
cube-mul (T₀ , T₀ , T₁) (T₁ , T₀ , T₀) = refl
cube-mul (T₀ , T₀ , T₁) (T₁ , T₀ , T₁) = refl
cube-mul (T₀ , T₀ , T₁) (T₁ , T₀ , T₂) = refl
cube-mul (T₀ , T₀ , T₁) (T₁ , T₁ , T₀) = refl
cube-mul (T₀ , T₀ , T₁) (T₁ , T₁ , T₁) = refl
cube-mul (T₀ , T₀ , T₁) (T₁ , T₁ , T₂) = refl
cube-mul (T₀ , T₀ , T₁) (T₁ , T₂ , T₀) = refl
cube-mul (T₀ , T₀ , T₁) (T₁ , T₂ , T₁) = refl
cube-mul (T₀ , T₀ , T₁) (T₁ , T₂ , T₂) = refl
cube-mul (T₀ , T₀ , T₁) (T₂ , T₀ , T₀) = refl
cube-mul (T₀ , T₀ , T₁) (T₂ , T₀ , T₁) = refl
cube-mul (T₀ , T₀ , T₁) (T₂ , T₀ , T₂) = refl
cube-mul (T₀ , T₀ , T₁) (T₂ , T₁ , T₀) = refl
cube-mul (T₀ , T₀ , T₁) (T₂ , T₁ , T₁) = refl
cube-mul (T₀ , T₀ , T₁) (T₂ , T₁ , T₂) = refl
cube-mul (T₀ , T₀ , T₁) (T₂ , T₂ , T₀) = refl
cube-mul (T₀ , T₀ , T₁) (T₂ , T₂ , T₁) = refl
cube-mul (T₀ , T₀ , T₁) (T₂ , T₂ , T₂) = refl
cube-mul (T₀ , T₀ , T₂) (T₀ , T₀ , T₀) = refl
cube-mul (T₀ , T₀ , T₂) (T₀ , T₀ , T₁) = refl
cube-mul (T₀ , T₀ , T₂) (T₀ , T₀ , T₂) = refl
cube-mul (T₀ , T₀ , T₂) (T₀ , T₁ , T₀) = refl
cube-mul (T₀ , T₀ , T₂) (T₀ , T₁ , T₁) = refl
cube-mul (T₀ , T₀ , T₂) (T₀ , T₁ , T₂) = refl
cube-mul (T₀ , T₀ , T₂) (T₀ , T₂ , T₀) = refl
cube-mul (T₀ , T₀ , T₂) (T₀ , T₂ , T₁) = refl
cube-mul (T₀ , T₀ , T₂) (T₀ , T₂ , T₂) = refl
cube-mul (T₀ , T₀ , T₂) (T₁ , T₀ , T₀) = refl
cube-mul (T₀ , T₀ , T₂) (T₁ , T₀ , T₁) = refl
cube-mul (T₀ , T₀ , T₂) (T₁ , T₀ , T₂) = refl
cube-mul (T₀ , T₀ , T₂) (T₁ , T₁ , T₀) = refl
cube-mul (T₀ , T₀ , T₂) (T₁ , T₁ , T₁) = refl
cube-mul (T₀ , T₀ , T₂) (T₁ , T₁ , T₂) = refl
cube-mul (T₀ , T₀ , T₂) (T₁ , T₂ , T₀) = refl
cube-mul (T₀ , T₀ , T₂) (T₁ , T₂ , T₁) = refl
cube-mul (T₀ , T₀ , T₂) (T₁ , T₂ , T₂) = refl
cube-mul (T₀ , T₀ , T₂) (T₂ , T₀ , T₀) = refl
cube-mul (T₀ , T₀ , T₂) (T₂ , T₀ , T₁) = refl
cube-mul (T₀ , T₀ , T₂) (T₂ , T₀ , T₂) = refl
cube-mul (T₀ , T₀ , T₂) (T₂ , T₁ , T₀) = refl
cube-mul (T₀ , T₀ , T₂) (T₂ , T₁ , T₁) = refl
cube-mul (T₀ , T₀ , T₂) (T₂ , T₁ , T₂) = refl
cube-mul (T₀ , T₀ , T₂) (T₂ , T₂ , T₀) = refl
cube-mul (T₀ , T₀ , T₂) (T₂ , T₂ , T₁) = refl
cube-mul (T₀ , T₀ , T₂) (T₂ , T₂ , T₂) = refl
cube-mul (T₀ , T₁ , T₀) (T₀ , T₀ , T₀) = refl
cube-mul (T₀ , T₁ , T₀) (T₀ , T₀ , T₁) = refl
cube-mul (T₀ , T₁ , T₀) (T₀ , T₀ , T₂) = refl
cube-mul (T₀ , T₁ , T₀) (T₀ , T₁ , T₀) = refl
cube-mul (T₀ , T₁ , T₀) (T₀ , T₁ , T₁) = refl
cube-mul (T₀ , T₁ , T₀) (T₀ , T₁ , T₂) = refl
cube-mul (T₀ , T₁ , T₀) (T₀ , T₂ , T₀) = refl
cube-mul (T₀ , T₁ , T₀) (T₀ , T₂ , T₁) = refl
cube-mul (T₀ , T₁ , T₀) (T₀ , T₂ , T₂) = refl
cube-mul (T₀ , T₁ , T₀) (T₁ , T₀ , T₀) = refl
cube-mul (T₀ , T₁ , T₀) (T₁ , T₀ , T₁) = refl
cube-mul (T₀ , T₁ , T₀) (T₁ , T₀ , T₂) = refl
cube-mul (T₀ , T₁ , T₀) (T₁ , T₁ , T₀) = refl
cube-mul (T₀ , T₁ , T₀) (T₁ , T₁ , T₁) = refl
cube-mul (T₀ , T₁ , T₀) (T₁ , T₁ , T₂) = refl
cube-mul (T₀ , T₁ , T₀) (T₁ , T₂ , T₀) = refl
cube-mul (T₀ , T₁ , T₀) (T₁ , T₂ , T₁) = refl
cube-mul (T₀ , T₁ , T₀) (T₁ , T₂ , T₂) = refl
cube-mul (T₀ , T₁ , T₀) (T₂ , T₀ , T₀) = refl
cube-mul (T₀ , T₁ , T₀) (T₂ , T₀ , T₁) = refl
cube-mul (T₀ , T₁ , T₀) (T₂ , T₀ , T₂) = refl
cube-mul (T₀ , T₁ , T₀) (T₂ , T₁ , T₀) = refl
cube-mul (T₀ , T₁ , T₀) (T₂ , T₁ , T₁) = refl
cube-mul (T₀ , T₁ , T₀) (T₂ , T₁ , T₂) = refl
cube-mul (T₀ , T₁ , T₀) (T₂ , T₂ , T₀) = refl
cube-mul (T₀ , T₁ , T₀) (T₂ , T₂ , T₁) = refl
cube-mul (T₀ , T₁ , T₀) (T₂ , T₂ , T₂) = refl
cube-mul (T₀ , T₁ , T₁) (T₀ , T₀ , T₀) = refl
cube-mul (T₀ , T₁ , T₁) (T₀ , T₀ , T₁) = refl
cube-mul (T₀ , T₁ , T₁) (T₀ , T₀ , T₂) = refl
cube-mul (T₀ , T₁ , T₁) (T₀ , T₁ , T₀) = refl
cube-mul (T₀ , T₁ , T₁) (T₀ , T₁ , T₁) = refl
cube-mul (T₀ , T₁ , T₁) (T₀ , T₁ , T₂) = refl
cube-mul (T₀ , T₁ , T₁) (T₀ , T₂ , T₀) = refl
cube-mul (T₀ , T₁ , T₁) (T₀ , T₂ , T₁) = refl
cube-mul (T₀ , T₁ , T₁) (T₀ , T₂ , T₂) = refl
cube-mul (T₀ , T₁ , T₁) (T₁ , T₀ , T₀) = refl
cube-mul (T₀ , T₁ , T₁) (T₁ , T₀ , T₁) = refl
cube-mul (T₀ , T₁ , T₁) (T₁ , T₀ , T₂) = refl
cube-mul (T₀ , T₁ , T₁) (T₁ , T₁ , T₀) = refl
cube-mul (T₀ , T₁ , T₁) (T₁ , T₁ , T₁) = refl
cube-mul (T₀ , T₁ , T₁) (T₁ , T₁ , T₂) = refl
cube-mul (T₀ , T₁ , T₁) (T₁ , T₂ , T₀) = refl
cube-mul (T₀ , T₁ , T₁) (T₁ , T₂ , T₁) = refl
cube-mul (T₀ , T₁ , T₁) (T₁ , T₂ , T₂) = refl
cube-mul (T₀ , T₁ , T₁) (T₂ , T₀ , T₀) = refl
cube-mul (T₀ , T₁ , T₁) (T₂ , T₀ , T₁) = refl
cube-mul (T₀ , T₁ , T₁) (T₂ , T₀ , T₂) = refl
cube-mul (T₀ , T₁ , T₁) (T₂ , T₁ , T₀) = refl
cube-mul (T₀ , T₁ , T₁) (T₂ , T₁ , T₁) = refl
cube-mul (T₀ , T₁ , T₁) (T₂ , T₁ , T₂) = refl
cube-mul (T₀ , T₁ , T₁) (T₂ , T₂ , T₀) = refl
cube-mul (T₀ , T₁ , T₁) (T₂ , T₂ , T₁) = refl
cube-mul (T₀ , T₁ , T₁) (T₂ , T₂ , T₂) = refl
cube-mul (T₀ , T₁ , T₂) (T₀ , T₀ , T₀) = refl
cube-mul (T₀ , T₁ , T₂) (T₀ , T₀ , T₁) = refl
cube-mul (T₀ , T₁ , T₂) (T₀ , T₀ , T₂) = refl
cube-mul (T₀ , T₁ , T₂) (T₀ , T₁ , T₀) = refl
cube-mul (T₀ , T₁ , T₂) (T₀ , T₁ , T₁) = refl
cube-mul (T₀ , T₁ , T₂) (T₀ , T₁ , T₂) = refl
cube-mul (T₀ , T₁ , T₂) (T₀ , T₂ , T₀) = refl
cube-mul (T₀ , T₁ , T₂) (T₀ , T₂ , T₁) = refl
cube-mul (T₀ , T₁ , T₂) (T₀ , T₂ , T₂) = refl
cube-mul (T₀ , T₁ , T₂) (T₁ , T₀ , T₀) = refl
cube-mul (T₀ , T₁ , T₂) (T₁ , T₀ , T₁) = refl
cube-mul (T₀ , T₁ , T₂) (T₁ , T₀ , T₂) = refl
cube-mul (T₀ , T₁ , T₂) (T₁ , T₁ , T₀) = refl
cube-mul (T₀ , T₁ , T₂) (T₁ , T₁ , T₁) = refl
cube-mul (T₀ , T₁ , T₂) (T₁ , T₁ , T₂) = refl
cube-mul (T₀ , T₁ , T₂) (T₁ , T₂ , T₀) = refl
cube-mul (T₀ , T₁ , T₂) (T₁ , T₂ , T₁) = refl
cube-mul (T₀ , T₁ , T₂) (T₁ , T₂ , T₂) = refl
cube-mul (T₀ , T₁ , T₂) (T₂ , T₀ , T₀) = refl
cube-mul (T₀ , T₁ , T₂) (T₂ , T₀ , T₁) = refl
cube-mul (T₀ , T₁ , T₂) (T₂ , T₀ , T₂) = refl
cube-mul (T₀ , T₁ , T₂) (T₂ , T₁ , T₀) = refl
cube-mul (T₀ , T₁ , T₂) (T₂ , T₁ , T₁) = refl
cube-mul (T₀ , T₁ , T₂) (T₂ , T₁ , T₂) = refl
cube-mul (T₀ , T₁ , T₂) (T₂ , T₂ , T₀) = refl
cube-mul (T₀ , T₁ , T₂) (T₂ , T₂ , T₁) = refl
cube-mul (T₀ , T₁ , T₂) (T₂ , T₂ , T₂) = refl
cube-mul (T₀ , T₂ , T₀) (T₀ , T₀ , T₀) = refl
cube-mul (T₀ , T₂ , T₀) (T₀ , T₀ , T₁) = refl
cube-mul (T₀ , T₂ , T₀) (T₀ , T₀ , T₂) = refl
cube-mul (T₀ , T₂ , T₀) (T₀ , T₁ , T₀) = refl
cube-mul (T₀ , T₂ , T₀) (T₀ , T₁ , T₁) = refl
cube-mul (T₀ , T₂ , T₀) (T₀ , T₁ , T₂) = refl
cube-mul (T₀ , T₂ , T₀) (T₀ , T₂ , T₀) = refl
cube-mul (T₀ , T₂ , T₀) (T₀ , T₂ , T₁) = refl
cube-mul (T₀ , T₂ , T₀) (T₀ , T₂ , T₂) = refl
cube-mul (T₀ , T₂ , T₀) (T₁ , T₀ , T₀) = refl
cube-mul (T₀ , T₂ , T₀) (T₁ , T₀ , T₁) = refl
cube-mul (T₀ , T₂ , T₀) (T₁ , T₀ , T₂) = refl
cube-mul (T₀ , T₂ , T₀) (T₁ , T₁ , T₀) = refl
cube-mul (T₀ , T₂ , T₀) (T₁ , T₁ , T₁) = refl
cube-mul (T₀ , T₂ , T₀) (T₁ , T₁ , T₂) = refl
cube-mul (T₀ , T₂ , T₀) (T₁ , T₂ , T₀) = refl
cube-mul (T₀ , T₂ , T₀) (T₁ , T₂ , T₁) = refl
cube-mul (T₀ , T₂ , T₀) (T₁ , T₂ , T₂) = refl
cube-mul (T₀ , T₂ , T₀) (T₂ , T₀ , T₀) = refl
cube-mul (T₀ , T₂ , T₀) (T₂ , T₀ , T₁) = refl
cube-mul (T₀ , T₂ , T₀) (T₂ , T₀ , T₂) = refl
cube-mul (T₀ , T₂ , T₀) (T₂ , T₁ , T₀) = refl
cube-mul (T₀ , T₂ , T₀) (T₂ , T₁ , T₁) = refl
cube-mul (T₀ , T₂ , T₀) (T₂ , T₁ , T₂) = refl
cube-mul (T₀ , T₂ , T₀) (T₂ , T₂ , T₀) = refl
cube-mul (T₀ , T₂ , T₀) (T₂ , T₂ , T₁) = refl
cube-mul (T₀ , T₂ , T₀) (T₂ , T₂ , T₂) = refl
cube-mul (T₀ , T₂ , T₁) (T₀ , T₀ , T₀) = refl
cube-mul (T₀ , T₂ , T₁) (T₀ , T₀ , T₁) = refl
cube-mul (T₀ , T₂ , T₁) (T₀ , T₀ , T₂) = refl
cube-mul (T₀ , T₂ , T₁) (T₀ , T₁ , T₀) = refl
cube-mul (T₀ , T₂ , T₁) (T₀ , T₁ , T₁) = refl
cube-mul (T₀ , T₂ , T₁) (T₀ , T₁ , T₂) = refl
cube-mul (T₀ , T₂ , T₁) (T₀ , T₂ , T₀) = refl
cube-mul (T₀ , T₂ , T₁) (T₀ , T₂ , T₁) = refl
cube-mul (T₀ , T₂ , T₁) (T₀ , T₂ , T₂) = refl
cube-mul (T₀ , T₂ , T₁) (T₁ , T₀ , T₀) = refl
cube-mul (T₀ , T₂ , T₁) (T₁ , T₀ , T₁) = refl
cube-mul (T₀ , T₂ , T₁) (T₁ , T₀ , T₂) = refl
cube-mul (T₀ , T₂ , T₁) (T₁ , T₁ , T₀) = refl
cube-mul (T₀ , T₂ , T₁) (T₁ , T₁ , T₁) = refl
cube-mul (T₀ , T₂ , T₁) (T₁ , T₁ , T₂) = refl
cube-mul (T₀ , T₂ , T₁) (T₁ , T₂ , T₀) = refl
cube-mul (T₀ , T₂ , T₁) (T₁ , T₂ , T₁) = refl
cube-mul (T₀ , T₂ , T₁) (T₁ , T₂ , T₂) = refl
cube-mul (T₀ , T₂ , T₁) (T₂ , T₀ , T₀) = refl
cube-mul (T₀ , T₂ , T₁) (T₂ , T₀ , T₁) = refl
cube-mul (T₀ , T₂ , T₁) (T₂ , T₀ , T₂) = refl
cube-mul (T₀ , T₂ , T₁) (T₂ , T₁ , T₀) = refl
cube-mul (T₀ , T₂ , T₁) (T₂ , T₁ , T₁) = refl
cube-mul (T₀ , T₂ , T₁) (T₂ , T₁ , T₂) = refl
cube-mul (T₀ , T₂ , T₁) (T₂ , T₂ , T₀) = refl
cube-mul (T₀ , T₂ , T₁) (T₂ , T₂ , T₁) = refl
cube-mul (T₀ , T₂ , T₁) (T₂ , T₂ , T₂) = refl
cube-mul (T₀ , T₂ , T₂) (T₀ , T₀ , T₀) = refl
cube-mul (T₀ , T₂ , T₂) (T₀ , T₀ , T₁) = refl
cube-mul (T₀ , T₂ , T₂) (T₀ , T₀ , T₂) = refl
cube-mul (T₀ , T₂ , T₂) (T₀ , T₁ , T₀) = refl
cube-mul (T₀ , T₂ , T₂) (T₀ , T₁ , T₁) = refl
cube-mul (T₀ , T₂ , T₂) (T₀ , T₁ , T₂) = refl
cube-mul (T₀ , T₂ , T₂) (T₀ , T₂ , T₀) = refl
cube-mul (T₀ , T₂ , T₂) (T₀ , T₂ , T₁) = refl
cube-mul (T₀ , T₂ , T₂) (T₀ , T₂ , T₂) = refl
cube-mul (T₀ , T₂ , T₂) (T₁ , T₀ , T₀) = refl
cube-mul (T₀ , T₂ , T₂) (T₁ , T₀ , T₁) = refl
cube-mul (T₀ , T₂ , T₂) (T₁ , T₀ , T₂) = refl
cube-mul (T₀ , T₂ , T₂) (T₁ , T₁ , T₀) = refl
cube-mul (T₀ , T₂ , T₂) (T₁ , T₁ , T₁) = refl
cube-mul (T₀ , T₂ , T₂) (T₁ , T₁ , T₂) = refl
cube-mul (T₀ , T₂ , T₂) (T₁ , T₂ , T₀) = refl
cube-mul (T₀ , T₂ , T₂) (T₁ , T₂ , T₁) = refl
cube-mul (T₀ , T₂ , T₂) (T₁ , T₂ , T₂) = refl
cube-mul (T₀ , T₂ , T₂) (T₂ , T₀ , T₀) = refl
cube-mul (T₀ , T₂ , T₂) (T₂ , T₀ , T₁) = refl
cube-mul (T₀ , T₂ , T₂) (T₂ , T₀ , T₂) = refl
cube-mul (T₀ , T₂ , T₂) (T₂ , T₁ , T₀) = refl
cube-mul (T₀ , T₂ , T₂) (T₂ , T₁ , T₁) = refl
cube-mul (T₀ , T₂ , T₂) (T₂ , T₁ , T₂) = refl
cube-mul (T₀ , T₂ , T₂) (T₂ , T₂ , T₀) = refl
cube-mul (T₀ , T₂ , T₂) (T₂ , T₂ , T₁) = refl
cube-mul (T₀ , T₂ , T₂) (T₂ , T₂ , T₂) = refl
cube-mul (T₁ , T₀ , T₀) (T₀ , T₀ , T₀) = refl
cube-mul (T₁ , T₀ , T₀) (T₀ , T₀ , T₁) = refl
cube-mul (T₁ , T₀ , T₀) (T₀ , T₀ , T₂) = refl
cube-mul (T₁ , T₀ , T₀) (T₀ , T₁ , T₀) = refl
cube-mul (T₁ , T₀ , T₀) (T₀ , T₁ , T₁) = refl
cube-mul (T₁ , T₀ , T₀) (T₀ , T₁ , T₂) = refl
cube-mul (T₁ , T₀ , T₀) (T₀ , T₂ , T₀) = refl
cube-mul (T₁ , T₀ , T₀) (T₀ , T₂ , T₁) = refl
cube-mul (T₁ , T₀ , T₀) (T₀ , T₂ , T₂) = refl
cube-mul (T₁ , T₀ , T₀) (T₁ , T₀ , T₀) = refl
cube-mul (T₁ , T₀ , T₀) (T₁ , T₀ , T₁) = refl
cube-mul (T₁ , T₀ , T₀) (T₁ , T₀ , T₂) = refl
cube-mul (T₁ , T₀ , T₀) (T₁ , T₁ , T₀) = refl
cube-mul (T₁ , T₀ , T₀) (T₁ , T₁ , T₁) = refl
cube-mul (T₁ , T₀ , T₀) (T₁ , T₁ , T₂) = refl
cube-mul (T₁ , T₀ , T₀) (T₁ , T₂ , T₀) = refl
cube-mul (T₁ , T₀ , T₀) (T₁ , T₂ , T₁) = refl
cube-mul (T₁ , T₀ , T₀) (T₁ , T₂ , T₂) = refl
cube-mul (T₁ , T₀ , T₀) (T₂ , T₀ , T₀) = refl
cube-mul (T₁ , T₀ , T₀) (T₂ , T₀ , T₁) = refl
cube-mul (T₁ , T₀ , T₀) (T₂ , T₀ , T₂) = refl
cube-mul (T₁ , T₀ , T₀) (T₂ , T₁ , T₀) = refl
cube-mul (T₁ , T₀ , T₀) (T₂ , T₁ , T₁) = refl
cube-mul (T₁ , T₀ , T₀) (T₂ , T₁ , T₂) = refl
cube-mul (T₁ , T₀ , T₀) (T₂ , T₂ , T₀) = refl
cube-mul (T₁ , T₀ , T₀) (T₂ , T₂ , T₁) = refl
cube-mul (T₁ , T₀ , T₀) (T₂ , T₂ , T₂) = refl
cube-mul (T₁ , T₀ , T₁) (T₀ , T₀ , T₀) = refl
cube-mul (T₁ , T₀ , T₁) (T₀ , T₀ , T₁) = refl
cube-mul (T₁ , T₀ , T₁) (T₀ , T₀ , T₂) = refl
cube-mul (T₁ , T₀ , T₁) (T₀ , T₁ , T₀) = refl
cube-mul (T₁ , T₀ , T₁) (T₀ , T₁ , T₁) = refl
cube-mul (T₁ , T₀ , T₁) (T₀ , T₁ , T₂) = refl
cube-mul (T₁ , T₀ , T₁) (T₀ , T₂ , T₀) = refl
cube-mul (T₁ , T₀ , T₁) (T₀ , T₂ , T₁) = refl
cube-mul (T₁ , T₀ , T₁) (T₀ , T₂ , T₂) = refl
cube-mul (T₁ , T₀ , T₁) (T₁ , T₀ , T₀) = refl
cube-mul (T₁ , T₀ , T₁) (T₁ , T₀ , T₁) = refl
cube-mul (T₁ , T₀ , T₁) (T₁ , T₀ , T₂) = refl
cube-mul (T₁ , T₀ , T₁) (T₁ , T₁ , T₀) = refl
cube-mul (T₁ , T₀ , T₁) (T₁ , T₁ , T₁) = refl
cube-mul (T₁ , T₀ , T₁) (T₁ , T₁ , T₂) = refl
cube-mul (T₁ , T₀ , T₁) (T₁ , T₂ , T₀) = refl
cube-mul (T₁ , T₀ , T₁) (T₁ , T₂ , T₁) = refl
cube-mul (T₁ , T₀ , T₁) (T₁ , T₂ , T₂) = refl
cube-mul (T₁ , T₀ , T₁) (T₂ , T₀ , T₀) = refl
cube-mul (T₁ , T₀ , T₁) (T₂ , T₀ , T₁) = refl
cube-mul (T₁ , T₀ , T₁) (T₂ , T₀ , T₂) = refl
cube-mul (T₁ , T₀ , T₁) (T₂ , T₁ , T₀) = refl
cube-mul (T₁ , T₀ , T₁) (T₂ , T₁ , T₁) = refl
cube-mul (T₁ , T₀ , T₁) (T₂ , T₁ , T₂) = refl
cube-mul (T₁ , T₀ , T₁) (T₂ , T₂ , T₀) = refl
cube-mul (T₁ , T₀ , T₁) (T₂ , T₂ , T₁) = refl
cube-mul (T₁ , T₀ , T₁) (T₂ , T₂ , T₂) = refl
cube-mul (T₁ , T₀ , T₂) (T₀ , T₀ , T₀) = refl
cube-mul (T₁ , T₀ , T₂) (T₀ , T₀ , T₁) = refl
cube-mul (T₁ , T₀ , T₂) (T₀ , T₀ , T₂) = refl
cube-mul (T₁ , T₀ , T₂) (T₀ , T₁ , T₀) = refl
cube-mul (T₁ , T₀ , T₂) (T₀ , T₁ , T₁) = refl
cube-mul (T₁ , T₀ , T₂) (T₀ , T₁ , T₂) = refl
cube-mul (T₁ , T₀ , T₂) (T₀ , T₂ , T₀) = refl
cube-mul (T₁ , T₀ , T₂) (T₀ , T₂ , T₁) = refl
cube-mul (T₁ , T₀ , T₂) (T₀ , T₂ , T₂) = refl
cube-mul (T₁ , T₀ , T₂) (T₁ , T₀ , T₀) = refl
cube-mul (T₁ , T₀ , T₂) (T₁ , T₀ , T₁) = refl
cube-mul (T₁ , T₀ , T₂) (T₁ , T₀ , T₂) = refl
cube-mul (T₁ , T₀ , T₂) (T₁ , T₁ , T₀) = refl
cube-mul (T₁ , T₀ , T₂) (T₁ , T₁ , T₁) = refl
cube-mul (T₁ , T₀ , T₂) (T₁ , T₁ , T₂) = refl
cube-mul (T₁ , T₀ , T₂) (T₁ , T₂ , T₀) = refl
cube-mul (T₁ , T₀ , T₂) (T₁ , T₂ , T₁) = refl
cube-mul (T₁ , T₀ , T₂) (T₁ , T₂ , T₂) = refl
cube-mul (T₁ , T₀ , T₂) (T₂ , T₀ , T₀) = refl
cube-mul (T₁ , T₀ , T₂) (T₂ , T₀ , T₁) = refl
cube-mul (T₁ , T₀ , T₂) (T₂ , T₀ , T₂) = refl
cube-mul (T₁ , T₀ , T₂) (T₂ , T₁ , T₀) = refl
cube-mul (T₁ , T₀ , T₂) (T₂ , T₁ , T₁) = refl
cube-mul (T₁ , T₀ , T₂) (T₂ , T₁ , T₂) = refl
cube-mul (T₁ , T₀ , T₂) (T₂ , T₂ , T₀) = refl
cube-mul (T₁ , T₀ , T₂) (T₂ , T₂ , T₁) = refl
cube-mul (T₁ , T₀ , T₂) (T₂ , T₂ , T₂) = refl
cube-mul (T₁ , T₁ , T₀) (T₀ , T₀ , T₀) = refl
cube-mul (T₁ , T₁ , T₀) (T₀ , T₀ , T₁) = refl
cube-mul (T₁ , T₁ , T₀) (T₀ , T₀ , T₂) = refl
cube-mul (T₁ , T₁ , T₀) (T₀ , T₁ , T₀) = refl
cube-mul (T₁ , T₁ , T₀) (T₀ , T₁ , T₁) = refl
cube-mul (T₁ , T₁ , T₀) (T₀ , T₁ , T₂) = refl
cube-mul (T₁ , T₁ , T₀) (T₀ , T₂ , T₀) = refl
cube-mul (T₁ , T₁ , T₀) (T₀ , T₂ , T₁) = refl
cube-mul (T₁ , T₁ , T₀) (T₀ , T₂ , T₂) = refl
cube-mul (T₁ , T₁ , T₀) (T₁ , T₀ , T₀) = refl
cube-mul (T₁ , T₁ , T₀) (T₁ , T₀ , T₁) = refl
cube-mul (T₁ , T₁ , T₀) (T₁ , T₀ , T₂) = refl
cube-mul (T₁ , T₁ , T₀) (T₁ , T₁ , T₀) = refl
cube-mul (T₁ , T₁ , T₀) (T₁ , T₁ , T₁) = refl
cube-mul (T₁ , T₁ , T₀) (T₁ , T₁ , T₂) = refl
cube-mul (T₁ , T₁ , T₀) (T₁ , T₂ , T₀) = refl
cube-mul (T₁ , T₁ , T₀) (T₁ , T₂ , T₁) = refl
cube-mul (T₁ , T₁ , T₀) (T₁ , T₂ , T₂) = refl
cube-mul (T₁ , T₁ , T₀) (T₂ , T₀ , T₀) = refl
cube-mul (T₁ , T₁ , T₀) (T₂ , T₀ , T₁) = refl
cube-mul (T₁ , T₁ , T₀) (T₂ , T₀ , T₂) = refl
cube-mul (T₁ , T₁ , T₀) (T₂ , T₁ , T₀) = refl
cube-mul (T₁ , T₁ , T₀) (T₂ , T₁ , T₁) = refl
cube-mul (T₁ , T₁ , T₀) (T₂ , T₁ , T₂) = refl
cube-mul (T₁ , T₁ , T₀) (T₂ , T₂ , T₀) = refl
cube-mul (T₁ , T₁ , T₀) (T₂ , T₂ , T₁) = refl
cube-mul (T₁ , T₁ , T₀) (T₂ , T₂ , T₂) = refl
cube-mul (T₁ , T₁ , T₁) (T₀ , T₀ , T₀) = refl
cube-mul (T₁ , T₁ , T₁) (T₀ , T₀ , T₁) = refl
cube-mul (T₁ , T₁ , T₁) (T₀ , T₀ , T₂) = refl
cube-mul (T₁ , T₁ , T₁) (T₀ , T₁ , T₀) = refl
cube-mul (T₁ , T₁ , T₁) (T₀ , T₁ , T₁) = refl
cube-mul (T₁ , T₁ , T₁) (T₀ , T₁ , T₂) = refl
cube-mul (T₁ , T₁ , T₁) (T₀ , T₂ , T₀) = refl
cube-mul (T₁ , T₁ , T₁) (T₀ , T₂ , T₁) = refl
cube-mul (T₁ , T₁ , T₁) (T₀ , T₂ , T₂) = refl
cube-mul (T₁ , T₁ , T₁) (T₁ , T₀ , T₀) = refl
cube-mul (T₁ , T₁ , T₁) (T₁ , T₀ , T₁) = refl
cube-mul (T₁ , T₁ , T₁) (T₁ , T₀ , T₂) = refl
cube-mul (T₁ , T₁ , T₁) (T₁ , T₁ , T₀) = refl
cube-mul (T₁ , T₁ , T₁) (T₁ , T₁ , T₁) = refl
cube-mul (T₁ , T₁ , T₁) (T₁ , T₁ , T₂) = refl
cube-mul (T₁ , T₁ , T₁) (T₁ , T₂ , T₀) = refl
cube-mul (T₁ , T₁ , T₁) (T₁ , T₂ , T₁) = refl
cube-mul (T₁ , T₁ , T₁) (T₁ , T₂ , T₂) = refl
cube-mul (T₁ , T₁ , T₁) (T₂ , T₀ , T₀) = refl
cube-mul (T₁ , T₁ , T₁) (T₂ , T₀ , T₁) = refl
cube-mul (T₁ , T₁ , T₁) (T₂ , T₀ , T₂) = refl
cube-mul (T₁ , T₁ , T₁) (T₂ , T₁ , T₀) = refl
cube-mul (T₁ , T₁ , T₁) (T₂ , T₁ , T₁) = refl
cube-mul (T₁ , T₁ , T₁) (T₂ , T₁ , T₂) = refl
cube-mul (T₁ , T₁ , T₁) (T₂ , T₂ , T₀) = refl
cube-mul (T₁ , T₁ , T₁) (T₂ , T₂ , T₁) = refl
cube-mul (T₁ , T₁ , T₁) (T₂ , T₂ , T₂) = refl
cube-mul (T₁ , T₁ , T₂) (T₀ , T₀ , T₀) = refl
cube-mul (T₁ , T₁ , T₂) (T₀ , T₀ , T₁) = refl
cube-mul (T₁ , T₁ , T₂) (T₀ , T₀ , T₂) = refl
cube-mul (T₁ , T₁ , T₂) (T₀ , T₁ , T₀) = refl
cube-mul (T₁ , T₁ , T₂) (T₀ , T₁ , T₁) = refl
cube-mul (T₁ , T₁ , T₂) (T₀ , T₁ , T₂) = refl
cube-mul (T₁ , T₁ , T₂) (T₀ , T₂ , T₀) = refl
cube-mul (T₁ , T₁ , T₂) (T₀ , T₂ , T₁) = refl
cube-mul (T₁ , T₁ , T₂) (T₀ , T₂ , T₂) = refl
cube-mul (T₁ , T₁ , T₂) (T₁ , T₀ , T₀) = refl
cube-mul (T₁ , T₁ , T₂) (T₁ , T₀ , T₁) = refl
cube-mul (T₁ , T₁ , T₂) (T₁ , T₀ , T₂) = refl
cube-mul (T₁ , T₁ , T₂) (T₁ , T₁ , T₀) = refl
cube-mul (T₁ , T₁ , T₂) (T₁ , T₁ , T₁) = refl
cube-mul (T₁ , T₁ , T₂) (T₁ , T₁ , T₂) = refl
cube-mul (T₁ , T₁ , T₂) (T₁ , T₂ , T₀) = refl
cube-mul (T₁ , T₁ , T₂) (T₁ , T₂ , T₁) = refl
cube-mul (T₁ , T₁ , T₂) (T₁ , T₂ , T₂) = refl
cube-mul (T₁ , T₁ , T₂) (T₂ , T₀ , T₀) = refl
cube-mul (T₁ , T₁ , T₂) (T₂ , T₀ , T₁) = refl
cube-mul (T₁ , T₁ , T₂) (T₂ , T₀ , T₂) = refl
cube-mul (T₁ , T₁ , T₂) (T₂ , T₁ , T₀) = refl
cube-mul (T₁ , T₁ , T₂) (T₂ , T₁ , T₁) = refl
cube-mul (T₁ , T₁ , T₂) (T₂ , T₁ , T₂) = refl
cube-mul (T₁ , T₁ , T₂) (T₂ , T₂ , T₀) = refl
cube-mul (T₁ , T₁ , T₂) (T₂ , T₂ , T₁) = refl
cube-mul (T₁ , T₁ , T₂) (T₂ , T₂ , T₂) = refl
cube-mul (T₁ , T₂ , T₀) (T₀ , T₀ , T₀) = refl
cube-mul (T₁ , T₂ , T₀) (T₀ , T₀ , T₁) = refl
cube-mul (T₁ , T₂ , T₀) (T₀ , T₀ , T₂) = refl
cube-mul (T₁ , T₂ , T₀) (T₀ , T₁ , T₀) = refl
cube-mul (T₁ , T₂ , T₀) (T₀ , T₁ , T₁) = refl
cube-mul (T₁ , T₂ , T₀) (T₀ , T₁ , T₂) = refl
cube-mul (T₁ , T₂ , T₀) (T₀ , T₂ , T₀) = refl
cube-mul (T₁ , T₂ , T₀) (T₀ , T₂ , T₁) = refl
cube-mul (T₁ , T₂ , T₀) (T₀ , T₂ , T₂) = refl
cube-mul (T₁ , T₂ , T₀) (T₁ , T₀ , T₀) = refl
cube-mul (T₁ , T₂ , T₀) (T₁ , T₀ , T₁) = refl
cube-mul (T₁ , T₂ , T₀) (T₁ , T₀ , T₂) = refl
cube-mul (T₁ , T₂ , T₀) (T₁ , T₁ , T₀) = refl
cube-mul (T₁ , T₂ , T₀) (T₁ , T₁ , T₁) = refl
cube-mul (T₁ , T₂ , T₀) (T₁ , T₁ , T₂) = refl
cube-mul (T₁ , T₂ , T₀) (T₁ , T₂ , T₀) = refl
cube-mul (T₁ , T₂ , T₀) (T₁ , T₂ , T₁) = refl
cube-mul (T₁ , T₂ , T₀) (T₁ , T₂ , T₂) = refl
cube-mul (T₁ , T₂ , T₀) (T₂ , T₀ , T₀) = refl
cube-mul (T₁ , T₂ , T₀) (T₂ , T₀ , T₁) = refl
cube-mul (T₁ , T₂ , T₀) (T₂ , T₀ , T₂) = refl
cube-mul (T₁ , T₂ , T₀) (T₂ , T₁ , T₀) = refl
cube-mul (T₁ , T₂ , T₀) (T₂ , T₁ , T₁) = refl
cube-mul (T₁ , T₂ , T₀) (T₂ , T₁ , T₂) = refl
cube-mul (T₁ , T₂ , T₀) (T₂ , T₂ , T₀) = refl
cube-mul (T₁ , T₂ , T₀) (T₂ , T₂ , T₁) = refl
cube-mul (T₁ , T₂ , T₀) (T₂ , T₂ , T₂) = refl
cube-mul (T₁ , T₂ , T₁) (T₀ , T₀ , T₀) = refl
cube-mul (T₁ , T₂ , T₁) (T₀ , T₀ , T₁) = refl
cube-mul (T₁ , T₂ , T₁) (T₀ , T₀ , T₂) = refl
cube-mul (T₁ , T₂ , T₁) (T₀ , T₁ , T₀) = refl
cube-mul (T₁ , T₂ , T₁) (T₀ , T₁ , T₁) = refl
cube-mul (T₁ , T₂ , T₁) (T₀ , T₁ , T₂) = refl
cube-mul (T₁ , T₂ , T₁) (T₀ , T₂ , T₀) = refl
cube-mul (T₁ , T₂ , T₁) (T₀ , T₂ , T₁) = refl
cube-mul (T₁ , T₂ , T₁) (T₀ , T₂ , T₂) = refl
cube-mul (T₁ , T₂ , T₁) (T₁ , T₀ , T₀) = refl
cube-mul (T₁ , T₂ , T₁) (T₁ , T₀ , T₁) = refl
cube-mul (T₁ , T₂ , T₁) (T₁ , T₀ , T₂) = refl
cube-mul (T₁ , T₂ , T₁) (T₁ , T₁ , T₀) = refl
cube-mul (T₁ , T₂ , T₁) (T₁ , T₁ , T₁) = refl
cube-mul (T₁ , T₂ , T₁) (T₁ , T₁ , T₂) = refl
cube-mul (T₁ , T₂ , T₁) (T₁ , T₂ , T₀) = refl
cube-mul (T₁ , T₂ , T₁) (T₁ , T₂ , T₁) = refl
cube-mul (T₁ , T₂ , T₁) (T₁ , T₂ , T₂) = refl
cube-mul (T₁ , T₂ , T₁) (T₂ , T₀ , T₀) = refl
cube-mul (T₁ , T₂ , T₁) (T₂ , T₀ , T₁) = refl
cube-mul (T₁ , T₂ , T₁) (T₂ , T₀ , T₂) = refl
cube-mul (T₁ , T₂ , T₁) (T₂ , T₁ , T₀) = refl
cube-mul (T₁ , T₂ , T₁) (T₂ , T₁ , T₁) = refl
cube-mul (T₁ , T₂ , T₁) (T₂ , T₁ , T₂) = refl
cube-mul (T₁ , T₂ , T₁) (T₂ , T₂ , T₀) = refl
cube-mul (T₁ , T₂ , T₁) (T₂ , T₂ , T₁) = refl
cube-mul (T₁ , T₂ , T₁) (T₂ , T₂ , T₂) = refl
cube-mul (T₁ , T₂ , T₂) (T₀ , T₀ , T₀) = refl
cube-mul (T₁ , T₂ , T₂) (T₀ , T₀ , T₁) = refl
cube-mul (T₁ , T₂ , T₂) (T₀ , T₀ , T₂) = refl
cube-mul (T₁ , T₂ , T₂) (T₀ , T₁ , T₀) = refl
cube-mul (T₁ , T₂ , T₂) (T₀ , T₁ , T₁) = refl
cube-mul (T₁ , T₂ , T₂) (T₀ , T₁ , T₂) = refl
cube-mul (T₁ , T₂ , T₂) (T₀ , T₂ , T₀) = refl
cube-mul (T₁ , T₂ , T₂) (T₀ , T₂ , T₁) = refl
cube-mul (T₁ , T₂ , T₂) (T₀ , T₂ , T₂) = refl
cube-mul (T₁ , T₂ , T₂) (T₁ , T₀ , T₀) = refl
cube-mul (T₁ , T₂ , T₂) (T₁ , T₀ , T₁) = refl
cube-mul (T₁ , T₂ , T₂) (T₁ , T₀ , T₂) = refl
cube-mul (T₁ , T₂ , T₂) (T₁ , T₁ , T₀) = refl
cube-mul (T₁ , T₂ , T₂) (T₁ , T₁ , T₁) = refl
cube-mul (T₁ , T₂ , T₂) (T₁ , T₁ , T₂) = refl
cube-mul (T₁ , T₂ , T₂) (T₁ , T₂ , T₀) = refl
cube-mul (T₁ , T₂ , T₂) (T₁ , T₂ , T₁) = refl
cube-mul (T₁ , T₂ , T₂) (T₁ , T₂ , T₂) = refl
cube-mul (T₁ , T₂ , T₂) (T₂ , T₀ , T₀) = refl
cube-mul (T₁ , T₂ , T₂) (T₂ , T₀ , T₁) = refl
cube-mul (T₁ , T₂ , T₂) (T₂ , T₀ , T₂) = refl
cube-mul (T₁ , T₂ , T₂) (T₂ , T₁ , T₀) = refl
cube-mul (T₁ , T₂ , T₂) (T₂ , T₁ , T₁) = refl
cube-mul (T₁ , T₂ , T₂) (T₂ , T₁ , T₂) = refl
cube-mul (T₁ , T₂ , T₂) (T₂ , T₂ , T₀) = refl
cube-mul (T₁ , T₂ , T₂) (T₂ , T₂ , T₁) = refl
cube-mul (T₁ , T₂ , T₂) (T₂ , T₂ , T₂) = refl
cube-mul (T₂ , T₀ , T₀) (T₀ , T₀ , T₀) = refl
cube-mul (T₂ , T₀ , T₀) (T₀ , T₀ , T₁) = refl
cube-mul (T₂ , T₀ , T₀) (T₀ , T₀ , T₂) = refl
cube-mul (T₂ , T₀ , T₀) (T₀ , T₁ , T₀) = refl
cube-mul (T₂ , T₀ , T₀) (T₀ , T₁ , T₁) = refl
cube-mul (T₂ , T₀ , T₀) (T₀ , T₁ , T₂) = refl
cube-mul (T₂ , T₀ , T₀) (T₀ , T₂ , T₀) = refl
cube-mul (T₂ , T₀ , T₀) (T₀ , T₂ , T₁) = refl
cube-mul (T₂ , T₀ , T₀) (T₀ , T₂ , T₂) = refl
cube-mul (T₂ , T₀ , T₀) (T₁ , T₀ , T₀) = refl
cube-mul (T₂ , T₀ , T₀) (T₁ , T₀ , T₁) = refl
cube-mul (T₂ , T₀ , T₀) (T₁ , T₀ , T₂) = refl
cube-mul (T₂ , T₀ , T₀) (T₁ , T₁ , T₀) = refl
cube-mul (T₂ , T₀ , T₀) (T₁ , T₁ , T₁) = refl
cube-mul (T₂ , T₀ , T₀) (T₁ , T₁ , T₂) = refl
cube-mul (T₂ , T₀ , T₀) (T₁ , T₂ , T₀) = refl
cube-mul (T₂ , T₀ , T₀) (T₁ , T₂ , T₁) = refl
cube-mul (T₂ , T₀ , T₀) (T₁ , T₂ , T₂) = refl
cube-mul (T₂ , T₀ , T₀) (T₂ , T₀ , T₀) = refl
cube-mul (T₂ , T₀ , T₀) (T₂ , T₀ , T₁) = refl
cube-mul (T₂ , T₀ , T₀) (T₂ , T₀ , T₂) = refl
cube-mul (T₂ , T₀ , T₀) (T₂ , T₁ , T₀) = refl
cube-mul (T₂ , T₀ , T₀) (T₂ , T₁ , T₁) = refl
cube-mul (T₂ , T₀ , T₀) (T₂ , T₁ , T₂) = refl
cube-mul (T₂ , T₀ , T₀) (T₂ , T₂ , T₀) = refl
cube-mul (T₂ , T₀ , T₀) (T₂ , T₂ , T₁) = refl
cube-mul (T₂ , T₀ , T₀) (T₂ , T₂ , T₂) = refl
cube-mul (T₂ , T₀ , T₁) (T₀ , T₀ , T₀) = refl
cube-mul (T₂ , T₀ , T₁) (T₀ , T₀ , T₁) = refl
cube-mul (T₂ , T₀ , T₁) (T₀ , T₀ , T₂) = refl
cube-mul (T₂ , T₀ , T₁) (T₀ , T₁ , T₀) = refl
cube-mul (T₂ , T₀ , T₁) (T₀ , T₁ , T₁) = refl
cube-mul (T₂ , T₀ , T₁) (T₀ , T₁ , T₂) = refl
cube-mul (T₂ , T₀ , T₁) (T₀ , T₂ , T₀) = refl
cube-mul (T₂ , T₀ , T₁) (T₀ , T₂ , T₁) = refl
cube-mul (T₂ , T₀ , T₁) (T₀ , T₂ , T₂) = refl
cube-mul (T₂ , T₀ , T₁) (T₁ , T₀ , T₀) = refl
cube-mul (T₂ , T₀ , T₁) (T₁ , T₀ , T₁) = refl
cube-mul (T₂ , T₀ , T₁) (T₁ , T₀ , T₂) = refl
cube-mul (T₂ , T₀ , T₁) (T₁ , T₁ , T₀) = refl
cube-mul (T₂ , T₀ , T₁) (T₁ , T₁ , T₁) = refl
cube-mul (T₂ , T₀ , T₁) (T₁ , T₁ , T₂) = refl
cube-mul (T₂ , T₀ , T₁) (T₁ , T₂ , T₀) = refl
cube-mul (T₂ , T₀ , T₁) (T₁ , T₂ , T₁) = refl
cube-mul (T₂ , T₀ , T₁) (T₁ , T₂ , T₂) = refl
cube-mul (T₂ , T₀ , T₁) (T₂ , T₀ , T₀) = refl
cube-mul (T₂ , T₀ , T₁) (T₂ , T₀ , T₁) = refl
cube-mul (T₂ , T₀ , T₁) (T₂ , T₀ , T₂) = refl
cube-mul (T₂ , T₀ , T₁) (T₂ , T₁ , T₀) = refl
cube-mul (T₂ , T₀ , T₁) (T₂ , T₁ , T₁) = refl
cube-mul (T₂ , T₀ , T₁) (T₂ , T₁ , T₂) = refl
cube-mul (T₂ , T₀ , T₁) (T₂ , T₂ , T₀) = refl
cube-mul (T₂ , T₀ , T₁) (T₂ , T₂ , T₁) = refl
cube-mul (T₂ , T₀ , T₁) (T₂ , T₂ , T₂) = refl
cube-mul (T₂ , T₀ , T₂) (T₀ , T₀ , T₀) = refl
cube-mul (T₂ , T₀ , T₂) (T₀ , T₀ , T₁) = refl
cube-mul (T₂ , T₀ , T₂) (T₀ , T₀ , T₂) = refl
cube-mul (T₂ , T₀ , T₂) (T₀ , T₁ , T₀) = refl
cube-mul (T₂ , T₀ , T₂) (T₀ , T₁ , T₁) = refl
cube-mul (T₂ , T₀ , T₂) (T₀ , T₁ , T₂) = refl
cube-mul (T₂ , T₀ , T₂) (T₀ , T₂ , T₀) = refl
cube-mul (T₂ , T₀ , T₂) (T₀ , T₂ , T₁) = refl
cube-mul (T₂ , T₀ , T₂) (T₀ , T₂ , T₂) = refl
cube-mul (T₂ , T₀ , T₂) (T₁ , T₀ , T₀) = refl
cube-mul (T₂ , T₀ , T₂) (T₁ , T₀ , T₁) = refl
cube-mul (T₂ , T₀ , T₂) (T₁ , T₀ , T₂) = refl
cube-mul (T₂ , T₀ , T₂) (T₁ , T₁ , T₀) = refl
cube-mul (T₂ , T₀ , T₂) (T₁ , T₁ , T₁) = refl
cube-mul (T₂ , T₀ , T₂) (T₁ , T₁ , T₂) = refl
cube-mul (T₂ , T₀ , T₂) (T₁ , T₂ , T₀) = refl
cube-mul (T₂ , T₀ , T₂) (T₁ , T₂ , T₁) = refl
cube-mul (T₂ , T₀ , T₂) (T₁ , T₂ , T₂) = refl
cube-mul (T₂ , T₀ , T₂) (T₂ , T₀ , T₀) = refl
cube-mul (T₂ , T₀ , T₂) (T₂ , T₀ , T₁) = refl
cube-mul (T₂ , T₀ , T₂) (T₂ , T₀ , T₂) = refl
cube-mul (T₂ , T₀ , T₂) (T₂ , T₁ , T₀) = refl
cube-mul (T₂ , T₀ , T₂) (T₂ , T₁ , T₁) = refl
cube-mul (T₂ , T₀ , T₂) (T₂ , T₁ , T₂) = refl
cube-mul (T₂ , T₀ , T₂) (T₂ , T₂ , T₀) = refl
cube-mul (T₂ , T₀ , T₂) (T₂ , T₂ , T₁) = refl
cube-mul (T₂ , T₀ , T₂) (T₂ , T₂ , T₂) = refl
cube-mul (T₂ , T₁ , T₀) (T₀ , T₀ , T₀) = refl
cube-mul (T₂ , T₁ , T₀) (T₀ , T₀ , T₁) = refl
cube-mul (T₂ , T₁ , T₀) (T₀ , T₀ , T₂) = refl
cube-mul (T₂ , T₁ , T₀) (T₀ , T₁ , T₀) = refl
cube-mul (T₂ , T₁ , T₀) (T₀ , T₁ , T₁) = refl
cube-mul (T₂ , T₁ , T₀) (T₀ , T₁ , T₂) = refl
cube-mul (T₂ , T₁ , T₀) (T₀ , T₂ , T₀) = refl
cube-mul (T₂ , T₁ , T₀) (T₀ , T₂ , T₁) = refl
cube-mul (T₂ , T₁ , T₀) (T₀ , T₂ , T₂) = refl
cube-mul (T₂ , T₁ , T₀) (T₁ , T₀ , T₀) = refl
cube-mul (T₂ , T₁ , T₀) (T₁ , T₀ , T₁) = refl
cube-mul (T₂ , T₁ , T₀) (T₁ , T₀ , T₂) = refl
cube-mul (T₂ , T₁ , T₀) (T₁ , T₁ , T₀) = refl
cube-mul (T₂ , T₁ , T₀) (T₁ , T₁ , T₁) = refl
cube-mul (T₂ , T₁ , T₀) (T₁ , T₁ , T₂) = refl
cube-mul (T₂ , T₁ , T₀) (T₁ , T₂ , T₀) = refl
cube-mul (T₂ , T₁ , T₀) (T₁ , T₂ , T₁) = refl
cube-mul (T₂ , T₁ , T₀) (T₁ , T₂ , T₂) = refl
cube-mul (T₂ , T₁ , T₀) (T₂ , T₀ , T₀) = refl
cube-mul (T₂ , T₁ , T₀) (T₂ , T₀ , T₁) = refl
cube-mul (T₂ , T₁ , T₀) (T₂ , T₀ , T₂) = refl
cube-mul (T₂ , T₁ , T₀) (T₂ , T₁ , T₀) = refl
cube-mul (T₂ , T₁ , T₀) (T₂ , T₁ , T₁) = refl
cube-mul (T₂ , T₁ , T₀) (T₂ , T₁ , T₂) = refl
cube-mul (T₂ , T₁ , T₀) (T₂ , T₂ , T₀) = refl
cube-mul (T₂ , T₁ , T₀) (T₂ , T₂ , T₁) = refl
cube-mul (T₂ , T₁ , T₀) (T₂ , T₂ , T₂) = refl
cube-mul (T₂ , T₁ , T₁) (T₀ , T₀ , T₀) = refl
cube-mul (T₂ , T₁ , T₁) (T₀ , T₀ , T₁) = refl
cube-mul (T₂ , T₁ , T₁) (T₀ , T₀ , T₂) = refl
cube-mul (T₂ , T₁ , T₁) (T₀ , T₁ , T₀) = refl
cube-mul (T₂ , T₁ , T₁) (T₀ , T₁ , T₁) = refl
cube-mul (T₂ , T₁ , T₁) (T₀ , T₁ , T₂) = refl
cube-mul (T₂ , T₁ , T₁) (T₀ , T₂ , T₀) = refl
cube-mul (T₂ , T₁ , T₁) (T₀ , T₂ , T₁) = refl
cube-mul (T₂ , T₁ , T₁) (T₀ , T₂ , T₂) = refl
cube-mul (T₂ , T₁ , T₁) (T₁ , T₀ , T₀) = refl
cube-mul (T₂ , T₁ , T₁) (T₁ , T₀ , T₁) = refl
cube-mul (T₂ , T₁ , T₁) (T₁ , T₀ , T₂) = refl
cube-mul (T₂ , T₁ , T₁) (T₁ , T₁ , T₀) = refl
cube-mul (T₂ , T₁ , T₁) (T₁ , T₁ , T₁) = refl
cube-mul (T₂ , T₁ , T₁) (T₁ , T₁ , T₂) = refl
cube-mul (T₂ , T₁ , T₁) (T₁ , T₂ , T₀) = refl
cube-mul (T₂ , T₁ , T₁) (T₁ , T₂ , T₁) = refl
cube-mul (T₂ , T₁ , T₁) (T₁ , T₂ , T₂) = refl
cube-mul (T₂ , T₁ , T₁) (T₂ , T₀ , T₀) = refl
cube-mul (T₂ , T₁ , T₁) (T₂ , T₀ , T₁) = refl
cube-mul (T₂ , T₁ , T₁) (T₂ , T₀ , T₂) = refl
cube-mul (T₂ , T₁ , T₁) (T₂ , T₁ , T₀) = refl
cube-mul (T₂ , T₁ , T₁) (T₂ , T₁ , T₁) = refl
cube-mul (T₂ , T₁ , T₁) (T₂ , T₁ , T₂) = refl
cube-mul (T₂ , T₁ , T₁) (T₂ , T₂ , T₀) = refl
cube-mul (T₂ , T₁ , T₁) (T₂ , T₂ , T₁) = refl
cube-mul (T₂ , T₁ , T₁) (T₂ , T₂ , T₂) = refl
cube-mul (T₂ , T₁ , T₂) (T₀ , T₀ , T₀) = refl
cube-mul (T₂ , T₁ , T₂) (T₀ , T₀ , T₁) = refl
cube-mul (T₂ , T₁ , T₂) (T₀ , T₀ , T₂) = refl
cube-mul (T₂ , T₁ , T₂) (T₀ , T₁ , T₀) = refl
cube-mul (T₂ , T₁ , T₂) (T₀ , T₁ , T₁) = refl
cube-mul (T₂ , T₁ , T₂) (T₀ , T₁ , T₂) = refl
cube-mul (T₂ , T₁ , T₂) (T₀ , T₂ , T₀) = refl
cube-mul (T₂ , T₁ , T₂) (T₀ , T₂ , T₁) = refl
cube-mul (T₂ , T₁ , T₂) (T₀ , T₂ , T₂) = refl
cube-mul (T₂ , T₁ , T₂) (T₁ , T₀ , T₀) = refl
cube-mul (T₂ , T₁ , T₂) (T₁ , T₀ , T₁) = refl
cube-mul (T₂ , T₁ , T₂) (T₁ , T₀ , T₂) = refl
cube-mul (T₂ , T₁ , T₂) (T₁ , T₁ , T₀) = refl
cube-mul (T₂ , T₁ , T₂) (T₁ , T₁ , T₁) = refl
cube-mul (T₂ , T₁ , T₂) (T₁ , T₁ , T₂) = refl
cube-mul (T₂ , T₁ , T₂) (T₁ , T₂ , T₀) = refl
cube-mul (T₂ , T₁ , T₂) (T₁ , T₂ , T₁) = refl
cube-mul (T₂ , T₁ , T₂) (T₁ , T₂ , T₂) = refl
cube-mul (T₂ , T₁ , T₂) (T₂ , T₀ , T₀) = refl
cube-mul (T₂ , T₁ , T₂) (T₂ , T₀ , T₁) = refl
cube-mul (T₂ , T₁ , T₂) (T₂ , T₀ , T₂) = refl
cube-mul (T₂ , T₁ , T₂) (T₂ , T₁ , T₀) = refl
cube-mul (T₂ , T₁ , T₂) (T₂ , T₁ , T₁) = refl
cube-mul (T₂ , T₁ , T₂) (T₂ , T₁ , T₂) = refl
cube-mul (T₂ , T₁ , T₂) (T₂ , T₂ , T₀) = refl
cube-mul (T₂ , T₁ , T₂) (T₂ , T₂ , T₁) = refl
cube-mul (T₂ , T₁ , T₂) (T₂ , T₂ , T₂) = refl
cube-mul (T₂ , T₂ , T₀) (T₀ , T₀ , T₀) = refl
cube-mul (T₂ , T₂ , T₀) (T₀ , T₀ , T₁) = refl
cube-mul (T₂ , T₂ , T₀) (T₀ , T₀ , T₂) = refl
cube-mul (T₂ , T₂ , T₀) (T₀ , T₁ , T₀) = refl
cube-mul (T₂ , T₂ , T₀) (T₀ , T₁ , T₁) = refl
cube-mul (T₂ , T₂ , T₀) (T₀ , T₁ , T₂) = refl
cube-mul (T₂ , T₂ , T₀) (T₀ , T₂ , T₀) = refl
cube-mul (T₂ , T₂ , T₀) (T₀ , T₂ , T₁) = refl
cube-mul (T₂ , T₂ , T₀) (T₀ , T₂ , T₂) = refl
cube-mul (T₂ , T₂ , T₀) (T₁ , T₀ , T₀) = refl
cube-mul (T₂ , T₂ , T₀) (T₁ , T₀ , T₁) = refl
cube-mul (T₂ , T₂ , T₀) (T₁ , T₀ , T₂) = refl
cube-mul (T₂ , T₂ , T₀) (T₁ , T₁ , T₀) = refl
cube-mul (T₂ , T₂ , T₀) (T₁ , T₁ , T₁) = refl
cube-mul (T₂ , T₂ , T₀) (T₁ , T₁ , T₂) = refl
cube-mul (T₂ , T₂ , T₀) (T₁ , T₂ , T₀) = refl
cube-mul (T₂ , T₂ , T₀) (T₁ , T₂ , T₁) = refl
cube-mul (T₂ , T₂ , T₀) (T₁ , T₂ , T₂) = refl
cube-mul (T₂ , T₂ , T₀) (T₂ , T₀ , T₀) = refl
cube-mul (T₂ , T₂ , T₀) (T₂ , T₀ , T₁) = refl
cube-mul (T₂ , T₂ , T₀) (T₂ , T₀ , T₂) = refl
cube-mul (T₂ , T₂ , T₀) (T₂ , T₁ , T₀) = refl
cube-mul (T₂ , T₂ , T₀) (T₂ , T₁ , T₁) = refl
cube-mul (T₂ , T₂ , T₀) (T₂ , T₁ , T₂) = refl
cube-mul (T₂ , T₂ , T₀) (T₂ , T₂ , T₀) = refl
cube-mul (T₂ , T₂ , T₀) (T₂ , T₂ , T₁) = refl
cube-mul (T₂ , T₂ , T₀) (T₂ , T₂ , T₂) = refl
cube-mul (T₂ , T₂ , T₁) (T₀ , T₀ , T₀) = refl
cube-mul (T₂ , T₂ , T₁) (T₀ , T₀ , T₁) = refl
cube-mul (T₂ , T₂ , T₁) (T₀ , T₀ , T₂) = refl
cube-mul (T₂ , T₂ , T₁) (T₀ , T₁ , T₀) = refl
cube-mul (T₂ , T₂ , T₁) (T₀ , T₁ , T₁) = refl
cube-mul (T₂ , T₂ , T₁) (T₀ , T₁ , T₂) = refl
cube-mul (T₂ , T₂ , T₁) (T₀ , T₂ , T₀) = refl
cube-mul (T₂ , T₂ , T₁) (T₀ , T₂ , T₁) = refl
cube-mul (T₂ , T₂ , T₁) (T₀ , T₂ , T₂) = refl
cube-mul (T₂ , T₂ , T₁) (T₁ , T₀ , T₀) = refl
cube-mul (T₂ , T₂ , T₁) (T₁ , T₀ , T₁) = refl
cube-mul (T₂ , T₂ , T₁) (T₁ , T₀ , T₂) = refl
cube-mul (T₂ , T₂ , T₁) (T₁ , T₁ , T₀) = refl
cube-mul (T₂ , T₂ , T₁) (T₁ , T₁ , T₁) = refl
cube-mul (T₂ , T₂ , T₁) (T₁ , T₁ , T₂) = refl
cube-mul (T₂ , T₂ , T₁) (T₁ , T₂ , T₀) = refl
cube-mul (T₂ , T₂ , T₁) (T₁ , T₂ , T₁) = refl
cube-mul (T₂ , T₂ , T₁) (T₁ , T₂ , T₂) = refl
cube-mul (T₂ , T₂ , T₁) (T₂ , T₀ , T₀) = refl
cube-mul (T₂ , T₂ , T₁) (T₂ , T₀ , T₁) = refl
cube-mul (T₂ , T₂ , T₁) (T₂ , T₀ , T₂) = refl
cube-mul (T₂ , T₂ , T₁) (T₂ , T₁ , T₀) = refl
cube-mul (T₂ , T₂ , T₁) (T₂ , T₁ , T₁) = refl
cube-mul (T₂ , T₂ , T₁) (T₂ , T₁ , T₂) = refl
cube-mul (T₂ , T₂ , T₁) (T₂ , T₂ , T₀) = refl
cube-mul (T₂ , T₂ , T₁) (T₂ , T₂ , T₁) = refl
cube-mul (T₂ , T₂ , T₁) (T₂ , T₂ , T₂) = refl
cube-mul (T₂ , T₂ , T₂) (T₀ , T₀ , T₀) = refl
cube-mul (T₂ , T₂ , T₂) (T₀ , T₀ , T₁) = refl
cube-mul (T₂ , T₂ , T₂) (T₀ , T₀ , T₂) = refl
cube-mul (T₂ , T₂ , T₂) (T₀ , T₁ , T₀) = refl
cube-mul (T₂ , T₂ , T₂) (T₀ , T₁ , T₁) = refl
cube-mul (T₂ , T₂ , T₂) (T₀ , T₁ , T₂) = refl
cube-mul (T₂ , T₂ , T₂) (T₀ , T₂ , T₀) = refl
cube-mul (T₂ , T₂ , T₂) (T₀ , T₂ , T₁) = refl
cube-mul (T₂ , T₂ , T₂) (T₀ , T₂ , T₂) = refl
cube-mul (T₂ , T₂ , T₂) (T₁ , T₀ , T₀) = refl
cube-mul (T₂ , T₂ , T₂) (T₁ , T₀ , T₁) = refl
cube-mul (T₂ , T₂ , T₂) (T₁ , T₀ , T₂) = refl
cube-mul (T₂ , T₂ , T₂) (T₁ , T₁ , T₀) = refl
cube-mul (T₂ , T₂ , T₂) (T₁ , T₁ , T₁) = refl
cube-mul (T₂ , T₂ , T₂) (T₁ , T₁ , T₂) = refl
cube-mul (T₂ , T₂ , T₂) (T₁ , T₂ , T₀) = refl
cube-mul (T₂ , T₂ , T₂) (T₁ , T₂ , T₁) = refl
cube-mul (T₂ , T₂ , T₂) (T₁ , T₂ , T₂) = refl
cube-mul (T₂ , T₂ , T₂) (T₂ , T₀ , T₀) = refl
cube-mul (T₂ , T₂ , T₂) (T₂ , T₀ , T₁) = refl
cube-mul (T₂ , T₂ , T₂) (T₂ , T₀ , T₂) = refl
cube-mul (T₂ , T₂ , T₂) (T₂ , T₁ , T₀) = refl
cube-mul (T₂ , T₂ , T₂) (T₂ , T₁ , T₁) = refl
cube-mul (T₂ , T₂ , T₂) (T₂ , T₁ , T₂) = refl
cube-mul (T₂ , T₂ , T₂) (T₂ , T₂ , T₀) = refl
cube-mul (T₂ , T₂ , T₂) (T₂ , T₂ , T₁) = refl
cube-mul (T₂ , T₂ , T₂) (T₂ , T₂ , T₂) = refl

-- freshman's dream (char 3): (x+y)³ = x³ + y³
cube-sum : ∀ x y → cube27 (x +₉ y) ≡ (cube27 x) +₉ (cube27 y)
cube-sum (T₀ , T₀ , T₀) (T₀ , T₀ , T₀) = refl
cube-sum (T₀ , T₀ , T₀) (T₀ , T₀ , T₁) = refl
cube-sum (T₀ , T₀ , T₀) (T₀ , T₀ , T₂) = refl
cube-sum (T₀ , T₀ , T₀) (T₀ , T₁ , T₀) = refl
cube-sum (T₀ , T₀ , T₀) (T₀ , T₁ , T₁) = refl
cube-sum (T₀ , T₀ , T₀) (T₀ , T₁ , T₂) = refl
cube-sum (T₀ , T₀ , T₀) (T₀ , T₂ , T₀) = refl
cube-sum (T₀ , T₀ , T₀) (T₀ , T₂ , T₁) = refl
cube-sum (T₀ , T₀ , T₀) (T₀ , T₂ , T₂) = refl
cube-sum (T₀ , T₀ , T₀) (T₁ , T₀ , T₀) = refl
cube-sum (T₀ , T₀ , T₀) (T₁ , T₀ , T₁) = refl
cube-sum (T₀ , T₀ , T₀) (T₁ , T₀ , T₂) = refl
cube-sum (T₀ , T₀ , T₀) (T₁ , T₁ , T₀) = refl
cube-sum (T₀ , T₀ , T₀) (T₁ , T₁ , T₁) = refl
cube-sum (T₀ , T₀ , T₀) (T₁ , T₁ , T₂) = refl
cube-sum (T₀ , T₀ , T₀) (T₁ , T₂ , T₀) = refl
cube-sum (T₀ , T₀ , T₀) (T₁ , T₂ , T₁) = refl
cube-sum (T₀ , T₀ , T₀) (T₁ , T₂ , T₂) = refl
cube-sum (T₀ , T₀ , T₀) (T₂ , T₀ , T₀) = refl
cube-sum (T₀ , T₀ , T₀) (T₂ , T₀ , T₁) = refl
cube-sum (T₀ , T₀ , T₀) (T₂ , T₀ , T₂) = refl
cube-sum (T₀ , T₀ , T₀) (T₂ , T₁ , T₀) = refl
cube-sum (T₀ , T₀ , T₀) (T₂ , T₁ , T₁) = refl
cube-sum (T₀ , T₀ , T₀) (T₂ , T₁ , T₂) = refl
cube-sum (T₀ , T₀ , T₀) (T₂ , T₂ , T₀) = refl
cube-sum (T₀ , T₀ , T₀) (T₂ , T₂ , T₁) = refl
cube-sum (T₀ , T₀ , T₀) (T₂ , T₂ , T₂) = refl
cube-sum (T₀ , T₀ , T₁) (T₀ , T₀ , T₀) = refl
cube-sum (T₀ , T₀ , T₁) (T₀ , T₀ , T₁) = refl
cube-sum (T₀ , T₀ , T₁) (T₀ , T₀ , T₂) = refl
cube-sum (T₀ , T₀ , T₁) (T₀ , T₁ , T₀) = refl
cube-sum (T₀ , T₀ , T₁) (T₀ , T₁ , T₁) = refl
cube-sum (T₀ , T₀ , T₁) (T₀ , T₁ , T₂) = refl
cube-sum (T₀ , T₀ , T₁) (T₀ , T₂ , T₀) = refl
cube-sum (T₀ , T₀ , T₁) (T₀ , T₂ , T₁) = refl
cube-sum (T₀ , T₀ , T₁) (T₀ , T₂ , T₂) = refl
cube-sum (T₀ , T₀ , T₁) (T₁ , T₀ , T₀) = refl
cube-sum (T₀ , T₀ , T₁) (T₁ , T₀ , T₁) = refl
cube-sum (T₀ , T₀ , T₁) (T₁ , T₀ , T₂) = refl
cube-sum (T₀ , T₀ , T₁) (T₁ , T₁ , T₀) = refl
cube-sum (T₀ , T₀ , T₁) (T₁ , T₁ , T₁) = refl
cube-sum (T₀ , T₀ , T₁) (T₁ , T₁ , T₂) = refl
cube-sum (T₀ , T₀ , T₁) (T₁ , T₂ , T₀) = refl
cube-sum (T₀ , T₀ , T₁) (T₁ , T₂ , T₁) = refl
cube-sum (T₀ , T₀ , T₁) (T₁ , T₂ , T₂) = refl
cube-sum (T₀ , T₀ , T₁) (T₂ , T₀ , T₀) = refl
cube-sum (T₀ , T₀ , T₁) (T₂ , T₀ , T₁) = refl
cube-sum (T₀ , T₀ , T₁) (T₂ , T₀ , T₂) = refl
cube-sum (T₀ , T₀ , T₁) (T₂ , T₁ , T₀) = refl
cube-sum (T₀ , T₀ , T₁) (T₂ , T₁ , T₁) = refl
cube-sum (T₀ , T₀ , T₁) (T₂ , T₁ , T₂) = refl
cube-sum (T₀ , T₀ , T₁) (T₂ , T₂ , T₀) = refl
cube-sum (T₀ , T₀ , T₁) (T₂ , T₂ , T₁) = refl
cube-sum (T₀ , T₀ , T₁) (T₂ , T₂ , T₂) = refl
cube-sum (T₀ , T₀ , T₂) (T₀ , T₀ , T₀) = refl
cube-sum (T₀ , T₀ , T₂) (T₀ , T₀ , T₁) = refl
cube-sum (T₀ , T₀ , T₂) (T₀ , T₀ , T₂) = refl
cube-sum (T₀ , T₀ , T₂) (T₀ , T₁ , T₀) = refl
cube-sum (T₀ , T₀ , T₂) (T₀ , T₁ , T₁) = refl
cube-sum (T₀ , T₀ , T₂) (T₀ , T₁ , T₂) = refl
cube-sum (T₀ , T₀ , T₂) (T₀ , T₂ , T₀) = refl
cube-sum (T₀ , T₀ , T₂) (T₀ , T₂ , T₁) = refl
cube-sum (T₀ , T₀ , T₂) (T₀ , T₂ , T₂) = refl
cube-sum (T₀ , T₀ , T₂) (T₁ , T₀ , T₀) = refl
cube-sum (T₀ , T₀ , T₂) (T₁ , T₀ , T₁) = refl
cube-sum (T₀ , T₀ , T₂) (T₁ , T₀ , T₂) = refl
cube-sum (T₀ , T₀ , T₂) (T₁ , T₁ , T₀) = refl
cube-sum (T₀ , T₀ , T₂) (T₁ , T₁ , T₁) = refl
cube-sum (T₀ , T₀ , T₂) (T₁ , T₁ , T₂) = refl
cube-sum (T₀ , T₀ , T₂) (T₁ , T₂ , T₀) = refl
cube-sum (T₀ , T₀ , T₂) (T₁ , T₂ , T₁) = refl
cube-sum (T₀ , T₀ , T₂) (T₁ , T₂ , T₂) = refl
cube-sum (T₀ , T₀ , T₂) (T₂ , T₀ , T₀) = refl
cube-sum (T₀ , T₀ , T₂) (T₂ , T₀ , T₁) = refl
cube-sum (T₀ , T₀ , T₂) (T₂ , T₀ , T₂) = refl
cube-sum (T₀ , T₀ , T₂) (T₂ , T₁ , T₀) = refl
cube-sum (T₀ , T₀ , T₂) (T₂ , T₁ , T₁) = refl
cube-sum (T₀ , T₀ , T₂) (T₂ , T₁ , T₂) = refl
cube-sum (T₀ , T₀ , T₂) (T₂ , T₂ , T₀) = refl
cube-sum (T₀ , T₀ , T₂) (T₂ , T₂ , T₁) = refl
cube-sum (T₀ , T₀ , T₂) (T₂ , T₂ , T₂) = refl
cube-sum (T₀ , T₁ , T₀) (T₀ , T₀ , T₀) = refl
cube-sum (T₀ , T₁ , T₀) (T₀ , T₀ , T₁) = refl
cube-sum (T₀ , T₁ , T₀) (T₀ , T₀ , T₂) = refl
cube-sum (T₀ , T₁ , T₀) (T₀ , T₁ , T₀) = refl
cube-sum (T₀ , T₁ , T₀) (T₀ , T₁ , T₁) = refl
cube-sum (T₀ , T₁ , T₀) (T₀ , T₁ , T₂) = refl
cube-sum (T₀ , T₁ , T₀) (T₀ , T₂ , T₀) = refl
cube-sum (T₀ , T₁ , T₀) (T₀ , T₂ , T₁) = refl
cube-sum (T₀ , T₁ , T₀) (T₀ , T₂ , T₂) = refl
cube-sum (T₀ , T₁ , T₀) (T₁ , T₀ , T₀) = refl
cube-sum (T₀ , T₁ , T₀) (T₁ , T₀ , T₁) = refl
cube-sum (T₀ , T₁ , T₀) (T₁ , T₀ , T₂) = refl
cube-sum (T₀ , T₁ , T₀) (T₁ , T₁ , T₀) = refl
cube-sum (T₀ , T₁ , T₀) (T₁ , T₁ , T₁) = refl
cube-sum (T₀ , T₁ , T₀) (T₁ , T₁ , T₂) = refl
cube-sum (T₀ , T₁ , T₀) (T₁ , T₂ , T₀) = refl
cube-sum (T₀ , T₁ , T₀) (T₁ , T₂ , T₁) = refl
cube-sum (T₀ , T₁ , T₀) (T₁ , T₂ , T₂) = refl
cube-sum (T₀ , T₁ , T₀) (T₂ , T₀ , T₀) = refl
cube-sum (T₀ , T₁ , T₀) (T₂ , T₀ , T₁) = refl
cube-sum (T₀ , T₁ , T₀) (T₂ , T₀ , T₂) = refl
cube-sum (T₀ , T₁ , T₀) (T₂ , T₁ , T₀) = refl
cube-sum (T₀ , T₁ , T₀) (T₂ , T₁ , T₁) = refl
cube-sum (T₀ , T₁ , T₀) (T₂ , T₁ , T₂) = refl
cube-sum (T₀ , T₁ , T₀) (T₂ , T₂ , T₀) = refl
cube-sum (T₀ , T₁ , T₀) (T₂ , T₂ , T₁) = refl
cube-sum (T₀ , T₁ , T₀) (T₂ , T₂ , T₂) = refl
cube-sum (T₀ , T₁ , T₁) (T₀ , T₀ , T₀) = refl
cube-sum (T₀ , T₁ , T₁) (T₀ , T₀ , T₁) = refl
cube-sum (T₀ , T₁ , T₁) (T₀ , T₀ , T₂) = refl
cube-sum (T₀ , T₁ , T₁) (T₀ , T₁ , T₀) = refl
cube-sum (T₀ , T₁ , T₁) (T₀ , T₁ , T₁) = refl
cube-sum (T₀ , T₁ , T₁) (T₀ , T₁ , T₂) = refl
cube-sum (T₀ , T₁ , T₁) (T₀ , T₂ , T₀) = refl
cube-sum (T₀ , T₁ , T₁) (T₀ , T₂ , T₁) = refl
cube-sum (T₀ , T₁ , T₁) (T₀ , T₂ , T₂) = refl
cube-sum (T₀ , T₁ , T₁) (T₁ , T₀ , T₀) = refl
cube-sum (T₀ , T₁ , T₁) (T₁ , T₀ , T₁) = refl
cube-sum (T₀ , T₁ , T₁) (T₁ , T₀ , T₂) = refl
cube-sum (T₀ , T₁ , T₁) (T₁ , T₁ , T₀) = refl
cube-sum (T₀ , T₁ , T₁) (T₁ , T₁ , T₁) = refl
cube-sum (T₀ , T₁ , T₁) (T₁ , T₁ , T₂) = refl
cube-sum (T₀ , T₁ , T₁) (T₁ , T₂ , T₀) = refl
cube-sum (T₀ , T₁ , T₁) (T₁ , T₂ , T₁) = refl
cube-sum (T₀ , T₁ , T₁) (T₁ , T₂ , T₂) = refl
cube-sum (T₀ , T₁ , T₁) (T₂ , T₀ , T₀) = refl
cube-sum (T₀ , T₁ , T₁) (T₂ , T₀ , T₁) = refl
cube-sum (T₀ , T₁ , T₁) (T₂ , T₀ , T₂) = refl
cube-sum (T₀ , T₁ , T₁) (T₂ , T₁ , T₀) = refl
cube-sum (T₀ , T₁ , T₁) (T₂ , T₁ , T₁) = refl
cube-sum (T₀ , T₁ , T₁) (T₂ , T₁ , T₂) = refl
cube-sum (T₀ , T₁ , T₁) (T₂ , T₂ , T₀) = refl
cube-sum (T₀ , T₁ , T₁) (T₂ , T₂ , T₁) = refl
cube-sum (T₀ , T₁ , T₁) (T₂ , T₂ , T₂) = refl
cube-sum (T₀ , T₁ , T₂) (T₀ , T₀ , T₀) = refl
cube-sum (T₀ , T₁ , T₂) (T₀ , T₀ , T₁) = refl
cube-sum (T₀ , T₁ , T₂) (T₀ , T₀ , T₂) = refl
cube-sum (T₀ , T₁ , T₂) (T₀ , T₁ , T₀) = refl
cube-sum (T₀ , T₁ , T₂) (T₀ , T₁ , T₁) = refl
cube-sum (T₀ , T₁ , T₂) (T₀ , T₁ , T₂) = refl
cube-sum (T₀ , T₁ , T₂) (T₀ , T₂ , T₀) = refl
cube-sum (T₀ , T₁ , T₂) (T₀ , T₂ , T₁) = refl
cube-sum (T₀ , T₁ , T₂) (T₀ , T₂ , T₂) = refl
cube-sum (T₀ , T₁ , T₂) (T₁ , T₀ , T₀) = refl
cube-sum (T₀ , T₁ , T₂) (T₁ , T₀ , T₁) = refl
cube-sum (T₀ , T₁ , T₂) (T₁ , T₀ , T₂) = refl
cube-sum (T₀ , T₁ , T₂) (T₁ , T₁ , T₀) = refl
cube-sum (T₀ , T₁ , T₂) (T₁ , T₁ , T₁) = refl
cube-sum (T₀ , T₁ , T₂) (T₁ , T₁ , T₂) = refl
cube-sum (T₀ , T₁ , T₂) (T₁ , T₂ , T₀) = refl
cube-sum (T₀ , T₁ , T₂) (T₁ , T₂ , T₁) = refl
cube-sum (T₀ , T₁ , T₂) (T₁ , T₂ , T₂) = refl
cube-sum (T₀ , T₁ , T₂) (T₂ , T₀ , T₀) = refl
cube-sum (T₀ , T₁ , T₂) (T₂ , T₀ , T₁) = refl
cube-sum (T₀ , T₁ , T₂) (T₂ , T₀ , T₂) = refl
cube-sum (T₀ , T₁ , T₂) (T₂ , T₁ , T₀) = refl
cube-sum (T₀ , T₁ , T₂) (T₂ , T₁ , T₁) = refl
cube-sum (T₀ , T₁ , T₂) (T₂ , T₁ , T₂) = refl
cube-sum (T₀ , T₁ , T₂) (T₂ , T₂ , T₀) = refl
cube-sum (T₀ , T₁ , T₂) (T₂ , T₂ , T₁) = refl
cube-sum (T₀ , T₁ , T₂) (T₂ , T₂ , T₂) = refl
cube-sum (T₀ , T₂ , T₀) (T₀ , T₀ , T₀) = refl
cube-sum (T₀ , T₂ , T₀) (T₀ , T₀ , T₁) = refl
cube-sum (T₀ , T₂ , T₀) (T₀ , T₀ , T₂) = refl
cube-sum (T₀ , T₂ , T₀) (T₀ , T₁ , T₀) = refl
cube-sum (T₀ , T₂ , T₀) (T₀ , T₁ , T₁) = refl
cube-sum (T₀ , T₂ , T₀) (T₀ , T₁ , T₂) = refl
cube-sum (T₀ , T₂ , T₀) (T₀ , T₂ , T₀) = refl
cube-sum (T₀ , T₂ , T₀) (T₀ , T₂ , T₁) = refl
cube-sum (T₀ , T₂ , T₀) (T₀ , T₂ , T₂) = refl
cube-sum (T₀ , T₂ , T₀) (T₁ , T₀ , T₀) = refl
cube-sum (T₀ , T₂ , T₀) (T₁ , T₀ , T₁) = refl
cube-sum (T₀ , T₂ , T₀) (T₁ , T₀ , T₂) = refl
cube-sum (T₀ , T₂ , T₀) (T₁ , T₁ , T₀) = refl
cube-sum (T₀ , T₂ , T₀) (T₁ , T₁ , T₁) = refl
cube-sum (T₀ , T₂ , T₀) (T₁ , T₁ , T₂) = refl
cube-sum (T₀ , T₂ , T₀) (T₁ , T₂ , T₀) = refl
cube-sum (T₀ , T₂ , T₀) (T₁ , T₂ , T₁) = refl
cube-sum (T₀ , T₂ , T₀) (T₁ , T₂ , T₂) = refl
cube-sum (T₀ , T₂ , T₀) (T₂ , T₀ , T₀) = refl
cube-sum (T₀ , T₂ , T₀) (T₂ , T₀ , T₁) = refl
cube-sum (T₀ , T₂ , T₀) (T₂ , T₀ , T₂) = refl
cube-sum (T₀ , T₂ , T₀) (T₂ , T₁ , T₀) = refl
cube-sum (T₀ , T₂ , T₀) (T₂ , T₁ , T₁) = refl
cube-sum (T₀ , T₂ , T₀) (T₂ , T₁ , T₂) = refl
cube-sum (T₀ , T₂ , T₀) (T₂ , T₂ , T₀) = refl
cube-sum (T₀ , T₂ , T₀) (T₂ , T₂ , T₁) = refl
cube-sum (T₀ , T₂ , T₀) (T₂ , T₂ , T₂) = refl
cube-sum (T₀ , T₂ , T₁) (T₀ , T₀ , T₀) = refl
cube-sum (T₀ , T₂ , T₁) (T₀ , T₀ , T₁) = refl
cube-sum (T₀ , T₂ , T₁) (T₀ , T₀ , T₂) = refl
cube-sum (T₀ , T₂ , T₁) (T₀ , T₁ , T₀) = refl
cube-sum (T₀ , T₂ , T₁) (T₀ , T₁ , T₁) = refl
cube-sum (T₀ , T₂ , T₁) (T₀ , T₁ , T₂) = refl
cube-sum (T₀ , T₂ , T₁) (T₀ , T₂ , T₀) = refl
cube-sum (T₀ , T₂ , T₁) (T₀ , T₂ , T₁) = refl
cube-sum (T₀ , T₂ , T₁) (T₀ , T₂ , T₂) = refl
cube-sum (T₀ , T₂ , T₁) (T₁ , T₀ , T₀) = refl
cube-sum (T₀ , T₂ , T₁) (T₁ , T₀ , T₁) = refl
cube-sum (T₀ , T₂ , T₁) (T₁ , T₀ , T₂) = refl
cube-sum (T₀ , T₂ , T₁) (T₁ , T₁ , T₀) = refl
cube-sum (T₀ , T₂ , T₁) (T₁ , T₁ , T₁) = refl
cube-sum (T₀ , T₂ , T₁) (T₁ , T₁ , T₂) = refl
cube-sum (T₀ , T₂ , T₁) (T₁ , T₂ , T₀) = refl
cube-sum (T₀ , T₂ , T₁) (T₁ , T₂ , T₁) = refl
cube-sum (T₀ , T₂ , T₁) (T₁ , T₂ , T₂) = refl
cube-sum (T₀ , T₂ , T₁) (T₂ , T₀ , T₀) = refl
cube-sum (T₀ , T₂ , T₁) (T₂ , T₀ , T₁) = refl
cube-sum (T₀ , T₂ , T₁) (T₂ , T₀ , T₂) = refl
cube-sum (T₀ , T₂ , T₁) (T₂ , T₁ , T₀) = refl
cube-sum (T₀ , T₂ , T₁) (T₂ , T₁ , T₁) = refl
cube-sum (T₀ , T₂ , T₁) (T₂ , T₁ , T₂) = refl
cube-sum (T₀ , T₂ , T₁) (T₂ , T₂ , T₀) = refl
cube-sum (T₀ , T₂ , T₁) (T₂ , T₂ , T₁) = refl
cube-sum (T₀ , T₂ , T₁) (T₂ , T₂ , T₂) = refl
cube-sum (T₀ , T₂ , T₂) (T₀ , T₀ , T₀) = refl
cube-sum (T₀ , T₂ , T₂) (T₀ , T₀ , T₁) = refl
cube-sum (T₀ , T₂ , T₂) (T₀ , T₀ , T₂) = refl
cube-sum (T₀ , T₂ , T₂) (T₀ , T₁ , T₀) = refl
cube-sum (T₀ , T₂ , T₂) (T₀ , T₁ , T₁) = refl
cube-sum (T₀ , T₂ , T₂) (T₀ , T₁ , T₂) = refl
cube-sum (T₀ , T₂ , T₂) (T₀ , T₂ , T₀) = refl
cube-sum (T₀ , T₂ , T₂) (T₀ , T₂ , T₁) = refl
cube-sum (T₀ , T₂ , T₂) (T₀ , T₂ , T₂) = refl
cube-sum (T₀ , T₂ , T₂) (T₁ , T₀ , T₀) = refl
cube-sum (T₀ , T₂ , T₂) (T₁ , T₀ , T₁) = refl
cube-sum (T₀ , T₂ , T₂) (T₁ , T₀ , T₂) = refl
cube-sum (T₀ , T₂ , T₂) (T₁ , T₁ , T₀) = refl
cube-sum (T₀ , T₂ , T₂) (T₁ , T₁ , T₁) = refl
cube-sum (T₀ , T₂ , T₂) (T₁ , T₁ , T₂) = refl
cube-sum (T₀ , T₂ , T₂) (T₁ , T₂ , T₀) = refl
cube-sum (T₀ , T₂ , T₂) (T₁ , T₂ , T₁) = refl
cube-sum (T₀ , T₂ , T₂) (T₁ , T₂ , T₂) = refl
cube-sum (T₀ , T₂ , T₂) (T₂ , T₀ , T₀) = refl
cube-sum (T₀ , T₂ , T₂) (T₂ , T₀ , T₁) = refl
cube-sum (T₀ , T₂ , T₂) (T₂ , T₀ , T₂) = refl
cube-sum (T₀ , T₂ , T₂) (T₂ , T₁ , T₀) = refl
cube-sum (T₀ , T₂ , T₂) (T₂ , T₁ , T₁) = refl
cube-sum (T₀ , T₂ , T₂) (T₂ , T₁ , T₂) = refl
cube-sum (T₀ , T₂ , T₂) (T₂ , T₂ , T₀) = refl
cube-sum (T₀ , T₂ , T₂) (T₂ , T₂ , T₁) = refl
cube-sum (T₀ , T₂ , T₂) (T₂ , T₂ , T₂) = refl
cube-sum (T₁ , T₀ , T₀) (T₀ , T₀ , T₀) = refl
cube-sum (T₁ , T₀ , T₀) (T₀ , T₀ , T₁) = refl
cube-sum (T₁ , T₀ , T₀) (T₀ , T₀ , T₂) = refl
cube-sum (T₁ , T₀ , T₀) (T₀ , T₁ , T₀) = refl
cube-sum (T₁ , T₀ , T₀) (T₀ , T₁ , T₁) = refl
cube-sum (T₁ , T₀ , T₀) (T₀ , T₁ , T₂) = refl
cube-sum (T₁ , T₀ , T₀) (T₀ , T₂ , T₀) = refl
cube-sum (T₁ , T₀ , T₀) (T₀ , T₂ , T₁) = refl
cube-sum (T₁ , T₀ , T₀) (T₀ , T₂ , T₂) = refl
cube-sum (T₁ , T₀ , T₀) (T₁ , T₀ , T₀) = refl
cube-sum (T₁ , T₀ , T₀) (T₁ , T₀ , T₁) = refl
cube-sum (T₁ , T₀ , T₀) (T₁ , T₀ , T₂) = refl
cube-sum (T₁ , T₀ , T₀) (T₁ , T₁ , T₀) = refl
cube-sum (T₁ , T₀ , T₀) (T₁ , T₁ , T₁) = refl
cube-sum (T₁ , T₀ , T₀) (T₁ , T₁ , T₂) = refl
cube-sum (T₁ , T₀ , T₀) (T₁ , T₂ , T₀) = refl
cube-sum (T₁ , T₀ , T₀) (T₁ , T₂ , T₁) = refl
cube-sum (T₁ , T₀ , T₀) (T₁ , T₂ , T₂) = refl
cube-sum (T₁ , T₀ , T₀) (T₂ , T₀ , T₀) = refl
cube-sum (T₁ , T₀ , T₀) (T₂ , T₀ , T₁) = refl
cube-sum (T₁ , T₀ , T₀) (T₂ , T₀ , T₂) = refl
cube-sum (T₁ , T₀ , T₀) (T₂ , T₁ , T₀) = refl
cube-sum (T₁ , T₀ , T₀) (T₂ , T₁ , T₁) = refl
cube-sum (T₁ , T₀ , T₀) (T₂ , T₁ , T₂) = refl
cube-sum (T₁ , T₀ , T₀) (T₂ , T₂ , T₀) = refl
cube-sum (T₁ , T₀ , T₀) (T₂ , T₂ , T₁) = refl
cube-sum (T₁ , T₀ , T₀) (T₂ , T₂ , T₂) = refl
cube-sum (T₁ , T₀ , T₁) (T₀ , T₀ , T₀) = refl
cube-sum (T₁ , T₀ , T₁) (T₀ , T₀ , T₁) = refl
cube-sum (T₁ , T₀ , T₁) (T₀ , T₀ , T₂) = refl
cube-sum (T₁ , T₀ , T₁) (T₀ , T₁ , T₀) = refl
cube-sum (T₁ , T₀ , T₁) (T₀ , T₁ , T₁) = refl
cube-sum (T₁ , T₀ , T₁) (T₀ , T₁ , T₂) = refl
cube-sum (T₁ , T₀ , T₁) (T₀ , T₂ , T₀) = refl
cube-sum (T₁ , T₀ , T₁) (T₀ , T₂ , T₁) = refl
cube-sum (T₁ , T₀ , T₁) (T₀ , T₂ , T₂) = refl
cube-sum (T₁ , T₀ , T₁) (T₁ , T₀ , T₀) = refl
cube-sum (T₁ , T₀ , T₁) (T₁ , T₀ , T₁) = refl
cube-sum (T₁ , T₀ , T₁) (T₁ , T₀ , T₂) = refl
cube-sum (T₁ , T₀ , T₁) (T₁ , T₁ , T₀) = refl
cube-sum (T₁ , T₀ , T₁) (T₁ , T₁ , T₁) = refl
cube-sum (T₁ , T₀ , T₁) (T₁ , T₁ , T₂) = refl
cube-sum (T₁ , T₀ , T₁) (T₁ , T₂ , T₀) = refl
cube-sum (T₁ , T₀ , T₁) (T₁ , T₂ , T₁) = refl
cube-sum (T₁ , T₀ , T₁) (T₁ , T₂ , T₂) = refl
cube-sum (T₁ , T₀ , T₁) (T₂ , T₀ , T₀) = refl
cube-sum (T₁ , T₀ , T₁) (T₂ , T₀ , T₁) = refl
cube-sum (T₁ , T₀ , T₁) (T₂ , T₀ , T₂) = refl
cube-sum (T₁ , T₀ , T₁) (T₂ , T₁ , T₀) = refl
cube-sum (T₁ , T₀ , T₁) (T₂ , T₁ , T₁) = refl
cube-sum (T₁ , T₀ , T₁) (T₂ , T₁ , T₂) = refl
cube-sum (T₁ , T₀ , T₁) (T₂ , T₂ , T₀) = refl
cube-sum (T₁ , T₀ , T₁) (T₂ , T₂ , T₁) = refl
cube-sum (T₁ , T₀ , T₁) (T₂ , T₂ , T₂) = refl
cube-sum (T₁ , T₀ , T₂) (T₀ , T₀ , T₀) = refl
cube-sum (T₁ , T₀ , T₂) (T₀ , T₀ , T₁) = refl
cube-sum (T₁ , T₀ , T₂) (T₀ , T₀ , T₂) = refl
cube-sum (T₁ , T₀ , T₂) (T₀ , T₁ , T₀) = refl
cube-sum (T₁ , T₀ , T₂) (T₀ , T₁ , T₁) = refl
cube-sum (T₁ , T₀ , T₂) (T₀ , T₁ , T₂) = refl
cube-sum (T₁ , T₀ , T₂) (T₀ , T₂ , T₀) = refl
cube-sum (T₁ , T₀ , T₂) (T₀ , T₂ , T₁) = refl
cube-sum (T₁ , T₀ , T₂) (T₀ , T₂ , T₂) = refl
cube-sum (T₁ , T₀ , T₂) (T₁ , T₀ , T₀) = refl
cube-sum (T₁ , T₀ , T₂) (T₁ , T₀ , T₁) = refl
cube-sum (T₁ , T₀ , T₂) (T₁ , T₀ , T₂) = refl
cube-sum (T₁ , T₀ , T₂) (T₁ , T₁ , T₀) = refl
cube-sum (T₁ , T₀ , T₂) (T₁ , T₁ , T₁) = refl
cube-sum (T₁ , T₀ , T₂) (T₁ , T₁ , T₂) = refl
cube-sum (T₁ , T₀ , T₂) (T₁ , T₂ , T₀) = refl
cube-sum (T₁ , T₀ , T₂) (T₁ , T₂ , T₁) = refl
cube-sum (T₁ , T₀ , T₂) (T₁ , T₂ , T₂) = refl
cube-sum (T₁ , T₀ , T₂) (T₂ , T₀ , T₀) = refl
cube-sum (T₁ , T₀ , T₂) (T₂ , T₀ , T₁) = refl
cube-sum (T₁ , T₀ , T₂) (T₂ , T₀ , T₂) = refl
cube-sum (T₁ , T₀ , T₂) (T₂ , T₁ , T₀) = refl
cube-sum (T₁ , T₀ , T₂) (T₂ , T₁ , T₁) = refl
cube-sum (T₁ , T₀ , T₂) (T₂ , T₁ , T₂) = refl
cube-sum (T₁ , T₀ , T₂) (T₂ , T₂ , T₀) = refl
cube-sum (T₁ , T₀ , T₂) (T₂ , T₂ , T₁) = refl
cube-sum (T₁ , T₀ , T₂) (T₂ , T₂ , T₂) = refl
cube-sum (T₁ , T₁ , T₀) (T₀ , T₀ , T₀) = refl
cube-sum (T₁ , T₁ , T₀) (T₀ , T₀ , T₁) = refl
cube-sum (T₁ , T₁ , T₀) (T₀ , T₀ , T₂) = refl
cube-sum (T₁ , T₁ , T₀) (T₀ , T₁ , T₀) = refl
cube-sum (T₁ , T₁ , T₀) (T₀ , T₁ , T₁) = refl
cube-sum (T₁ , T₁ , T₀) (T₀ , T₁ , T₂) = refl
cube-sum (T₁ , T₁ , T₀) (T₀ , T₂ , T₀) = refl
cube-sum (T₁ , T₁ , T₀) (T₀ , T₂ , T₁) = refl
cube-sum (T₁ , T₁ , T₀) (T₀ , T₂ , T₂) = refl
cube-sum (T₁ , T₁ , T₀) (T₁ , T₀ , T₀) = refl
cube-sum (T₁ , T₁ , T₀) (T₁ , T₀ , T₁) = refl
cube-sum (T₁ , T₁ , T₀) (T₁ , T₀ , T₂) = refl
cube-sum (T₁ , T₁ , T₀) (T₁ , T₁ , T₀) = refl
cube-sum (T₁ , T₁ , T₀) (T₁ , T₁ , T₁) = refl
cube-sum (T₁ , T₁ , T₀) (T₁ , T₁ , T₂) = refl
cube-sum (T₁ , T₁ , T₀) (T₁ , T₂ , T₀) = refl
cube-sum (T₁ , T₁ , T₀) (T₁ , T₂ , T₁) = refl
cube-sum (T₁ , T₁ , T₀) (T₁ , T₂ , T₂) = refl
cube-sum (T₁ , T₁ , T₀) (T₂ , T₀ , T₀) = refl
cube-sum (T₁ , T₁ , T₀) (T₂ , T₀ , T₁) = refl
cube-sum (T₁ , T₁ , T₀) (T₂ , T₀ , T₂) = refl
cube-sum (T₁ , T₁ , T₀) (T₂ , T₁ , T₀) = refl
cube-sum (T₁ , T₁ , T₀) (T₂ , T₁ , T₁) = refl
cube-sum (T₁ , T₁ , T₀) (T₂ , T₁ , T₂) = refl
cube-sum (T₁ , T₁ , T₀) (T₂ , T₂ , T₀) = refl
cube-sum (T₁ , T₁ , T₀) (T₂ , T₂ , T₁) = refl
cube-sum (T₁ , T₁ , T₀) (T₂ , T₂ , T₂) = refl
cube-sum (T₁ , T₁ , T₁) (T₀ , T₀ , T₀) = refl
cube-sum (T₁ , T₁ , T₁) (T₀ , T₀ , T₁) = refl
cube-sum (T₁ , T₁ , T₁) (T₀ , T₀ , T₂) = refl
cube-sum (T₁ , T₁ , T₁) (T₀ , T₁ , T₀) = refl
cube-sum (T₁ , T₁ , T₁) (T₀ , T₁ , T₁) = refl
cube-sum (T₁ , T₁ , T₁) (T₀ , T₁ , T₂) = refl
cube-sum (T₁ , T₁ , T₁) (T₀ , T₂ , T₀) = refl
cube-sum (T₁ , T₁ , T₁) (T₀ , T₂ , T₁) = refl
cube-sum (T₁ , T₁ , T₁) (T₀ , T₂ , T₂) = refl
cube-sum (T₁ , T₁ , T₁) (T₁ , T₀ , T₀) = refl
cube-sum (T₁ , T₁ , T₁) (T₁ , T₀ , T₁) = refl
cube-sum (T₁ , T₁ , T₁) (T₁ , T₀ , T₂) = refl
cube-sum (T₁ , T₁ , T₁) (T₁ , T₁ , T₀) = refl
cube-sum (T₁ , T₁ , T₁) (T₁ , T₁ , T₁) = refl
cube-sum (T₁ , T₁ , T₁) (T₁ , T₁ , T₂) = refl
cube-sum (T₁ , T₁ , T₁) (T₁ , T₂ , T₀) = refl
cube-sum (T₁ , T₁ , T₁) (T₁ , T₂ , T₁) = refl
cube-sum (T₁ , T₁ , T₁) (T₁ , T₂ , T₂) = refl
cube-sum (T₁ , T₁ , T₁) (T₂ , T₀ , T₀) = refl
cube-sum (T₁ , T₁ , T₁) (T₂ , T₀ , T₁) = refl
cube-sum (T₁ , T₁ , T₁) (T₂ , T₀ , T₂) = refl
cube-sum (T₁ , T₁ , T₁) (T₂ , T₁ , T₀) = refl
cube-sum (T₁ , T₁ , T₁) (T₂ , T₁ , T₁) = refl
cube-sum (T₁ , T₁ , T₁) (T₂ , T₁ , T₂) = refl
cube-sum (T₁ , T₁ , T₁) (T₂ , T₂ , T₀) = refl
cube-sum (T₁ , T₁ , T₁) (T₂ , T₂ , T₁) = refl
cube-sum (T₁ , T₁ , T₁) (T₂ , T₂ , T₂) = refl
cube-sum (T₁ , T₁ , T₂) (T₀ , T₀ , T₀) = refl
cube-sum (T₁ , T₁ , T₂) (T₀ , T₀ , T₁) = refl
cube-sum (T₁ , T₁ , T₂) (T₀ , T₀ , T₂) = refl
cube-sum (T₁ , T₁ , T₂) (T₀ , T₁ , T₀) = refl
cube-sum (T₁ , T₁ , T₂) (T₀ , T₁ , T₁) = refl
cube-sum (T₁ , T₁ , T₂) (T₀ , T₁ , T₂) = refl
cube-sum (T₁ , T₁ , T₂) (T₀ , T₂ , T₀) = refl
cube-sum (T₁ , T₁ , T₂) (T₀ , T₂ , T₁) = refl
cube-sum (T₁ , T₁ , T₂) (T₀ , T₂ , T₂) = refl
cube-sum (T₁ , T₁ , T₂) (T₁ , T₀ , T₀) = refl
cube-sum (T₁ , T₁ , T₂) (T₁ , T₀ , T₁) = refl
cube-sum (T₁ , T₁ , T₂) (T₁ , T₀ , T₂) = refl
cube-sum (T₁ , T₁ , T₂) (T₁ , T₁ , T₀) = refl
cube-sum (T₁ , T₁ , T₂) (T₁ , T₁ , T₁) = refl
cube-sum (T₁ , T₁ , T₂) (T₁ , T₁ , T₂) = refl
cube-sum (T₁ , T₁ , T₂) (T₁ , T₂ , T₀) = refl
cube-sum (T₁ , T₁ , T₂) (T₁ , T₂ , T₁) = refl
cube-sum (T₁ , T₁ , T₂) (T₁ , T₂ , T₂) = refl
cube-sum (T₁ , T₁ , T₂) (T₂ , T₀ , T₀) = refl
cube-sum (T₁ , T₁ , T₂) (T₂ , T₀ , T₁) = refl
cube-sum (T₁ , T₁ , T₂) (T₂ , T₀ , T₂) = refl
cube-sum (T₁ , T₁ , T₂) (T₂ , T₁ , T₀) = refl
cube-sum (T₁ , T₁ , T₂) (T₂ , T₁ , T₁) = refl
cube-sum (T₁ , T₁ , T₂) (T₂ , T₁ , T₂) = refl
cube-sum (T₁ , T₁ , T₂) (T₂ , T₂ , T₀) = refl
cube-sum (T₁ , T₁ , T₂) (T₂ , T₂ , T₁) = refl
cube-sum (T₁ , T₁ , T₂) (T₂ , T₂ , T₂) = refl
cube-sum (T₁ , T₂ , T₀) (T₀ , T₀ , T₀) = refl
cube-sum (T₁ , T₂ , T₀) (T₀ , T₀ , T₁) = refl
cube-sum (T₁ , T₂ , T₀) (T₀ , T₀ , T₂) = refl
cube-sum (T₁ , T₂ , T₀) (T₀ , T₁ , T₀) = refl
cube-sum (T₁ , T₂ , T₀) (T₀ , T₁ , T₁) = refl
cube-sum (T₁ , T₂ , T₀) (T₀ , T₁ , T₂) = refl
cube-sum (T₁ , T₂ , T₀) (T₀ , T₂ , T₀) = refl
cube-sum (T₁ , T₂ , T₀) (T₀ , T₂ , T₁) = refl
cube-sum (T₁ , T₂ , T₀) (T₀ , T₂ , T₂) = refl
cube-sum (T₁ , T₂ , T₀) (T₁ , T₀ , T₀) = refl
cube-sum (T₁ , T₂ , T₀) (T₁ , T₀ , T₁) = refl
cube-sum (T₁ , T₂ , T₀) (T₁ , T₀ , T₂) = refl
cube-sum (T₁ , T₂ , T₀) (T₁ , T₁ , T₀) = refl
cube-sum (T₁ , T₂ , T₀) (T₁ , T₁ , T₁) = refl
cube-sum (T₁ , T₂ , T₀) (T₁ , T₁ , T₂) = refl
cube-sum (T₁ , T₂ , T₀) (T₁ , T₂ , T₀) = refl
cube-sum (T₁ , T₂ , T₀) (T₁ , T₂ , T₁) = refl
cube-sum (T₁ , T₂ , T₀) (T₁ , T₂ , T₂) = refl
cube-sum (T₁ , T₂ , T₀) (T₂ , T₀ , T₀) = refl
cube-sum (T₁ , T₂ , T₀) (T₂ , T₀ , T₁) = refl
cube-sum (T₁ , T₂ , T₀) (T₂ , T₀ , T₂) = refl
cube-sum (T₁ , T₂ , T₀) (T₂ , T₁ , T₀) = refl
cube-sum (T₁ , T₂ , T₀) (T₂ , T₁ , T₁) = refl
cube-sum (T₁ , T₂ , T₀) (T₂ , T₁ , T₂) = refl
cube-sum (T₁ , T₂ , T₀) (T₂ , T₂ , T₀) = refl
cube-sum (T₁ , T₂ , T₀) (T₂ , T₂ , T₁) = refl
cube-sum (T₁ , T₂ , T₀) (T₂ , T₂ , T₂) = refl
cube-sum (T₁ , T₂ , T₁) (T₀ , T₀ , T₀) = refl
cube-sum (T₁ , T₂ , T₁) (T₀ , T₀ , T₁) = refl
cube-sum (T₁ , T₂ , T₁) (T₀ , T₀ , T₂) = refl
cube-sum (T₁ , T₂ , T₁) (T₀ , T₁ , T₀) = refl
cube-sum (T₁ , T₂ , T₁) (T₀ , T₁ , T₁) = refl
cube-sum (T₁ , T₂ , T₁) (T₀ , T₁ , T₂) = refl
cube-sum (T₁ , T₂ , T₁) (T₀ , T₂ , T₀) = refl
cube-sum (T₁ , T₂ , T₁) (T₀ , T₂ , T₁) = refl
cube-sum (T₁ , T₂ , T₁) (T₀ , T₂ , T₂) = refl
cube-sum (T₁ , T₂ , T₁) (T₁ , T₀ , T₀) = refl
cube-sum (T₁ , T₂ , T₁) (T₁ , T₀ , T₁) = refl
cube-sum (T₁ , T₂ , T₁) (T₁ , T₀ , T₂) = refl
cube-sum (T₁ , T₂ , T₁) (T₁ , T₁ , T₀) = refl
cube-sum (T₁ , T₂ , T₁) (T₁ , T₁ , T₁) = refl
cube-sum (T₁ , T₂ , T₁) (T₁ , T₁ , T₂) = refl
cube-sum (T₁ , T₂ , T₁) (T₁ , T₂ , T₀) = refl
cube-sum (T₁ , T₂ , T₁) (T₁ , T₂ , T₁) = refl
cube-sum (T₁ , T₂ , T₁) (T₁ , T₂ , T₂) = refl
cube-sum (T₁ , T₂ , T₁) (T₂ , T₀ , T₀) = refl
cube-sum (T₁ , T₂ , T₁) (T₂ , T₀ , T₁) = refl
cube-sum (T₁ , T₂ , T₁) (T₂ , T₀ , T₂) = refl
cube-sum (T₁ , T₂ , T₁) (T₂ , T₁ , T₀) = refl
cube-sum (T₁ , T₂ , T₁) (T₂ , T₁ , T₁) = refl
cube-sum (T₁ , T₂ , T₁) (T₂ , T₁ , T₂) = refl
cube-sum (T₁ , T₂ , T₁) (T₂ , T₂ , T₀) = refl
cube-sum (T₁ , T₂ , T₁) (T₂ , T₂ , T₁) = refl
cube-sum (T₁ , T₂ , T₁) (T₂ , T₂ , T₂) = refl
cube-sum (T₁ , T₂ , T₂) (T₀ , T₀ , T₀) = refl
cube-sum (T₁ , T₂ , T₂) (T₀ , T₀ , T₁) = refl
cube-sum (T₁ , T₂ , T₂) (T₀ , T₀ , T₂) = refl
cube-sum (T₁ , T₂ , T₂) (T₀ , T₁ , T₀) = refl
cube-sum (T₁ , T₂ , T₂) (T₀ , T₁ , T₁) = refl
cube-sum (T₁ , T₂ , T₂) (T₀ , T₁ , T₂) = refl
cube-sum (T₁ , T₂ , T₂) (T₀ , T₂ , T₀) = refl
cube-sum (T₁ , T₂ , T₂) (T₀ , T₂ , T₁) = refl
cube-sum (T₁ , T₂ , T₂) (T₀ , T₂ , T₂) = refl
cube-sum (T₁ , T₂ , T₂) (T₁ , T₀ , T₀) = refl
cube-sum (T₁ , T₂ , T₂) (T₁ , T₀ , T₁) = refl
cube-sum (T₁ , T₂ , T₂) (T₁ , T₀ , T₂) = refl
cube-sum (T₁ , T₂ , T₂) (T₁ , T₁ , T₀) = refl
cube-sum (T₁ , T₂ , T₂) (T₁ , T₁ , T₁) = refl
cube-sum (T₁ , T₂ , T₂) (T₁ , T₁ , T₂) = refl
cube-sum (T₁ , T₂ , T₂) (T₁ , T₂ , T₀) = refl
cube-sum (T₁ , T₂ , T₂) (T₁ , T₂ , T₁) = refl
cube-sum (T₁ , T₂ , T₂) (T₁ , T₂ , T₂) = refl
cube-sum (T₁ , T₂ , T₂) (T₂ , T₀ , T₀) = refl
cube-sum (T₁ , T₂ , T₂) (T₂ , T₀ , T₁) = refl
cube-sum (T₁ , T₂ , T₂) (T₂ , T₀ , T₂) = refl
cube-sum (T₁ , T₂ , T₂) (T₂ , T₁ , T₀) = refl
cube-sum (T₁ , T₂ , T₂) (T₂ , T₁ , T₁) = refl
cube-sum (T₁ , T₂ , T₂) (T₂ , T₁ , T₂) = refl
cube-sum (T₁ , T₂ , T₂) (T₂ , T₂ , T₀) = refl
cube-sum (T₁ , T₂ , T₂) (T₂ , T₂ , T₁) = refl
cube-sum (T₁ , T₂ , T₂) (T₂ , T₂ , T₂) = refl
cube-sum (T₂ , T₀ , T₀) (T₀ , T₀ , T₀) = refl
cube-sum (T₂ , T₀ , T₀) (T₀ , T₀ , T₁) = refl
cube-sum (T₂ , T₀ , T₀) (T₀ , T₀ , T₂) = refl
cube-sum (T₂ , T₀ , T₀) (T₀ , T₁ , T₀) = refl
cube-sum (T₂ , T₀ , T₀) (T₀ , T₁ , T₁) = refl
cube-sum (T₂ , T₀ , T₀) (T₀ , T₁ , T₂) = refl
cube-sum (T₂ , T₀ , T₀) (T₀ , T₂ , T₀) = refl
cube-sum (T₂ , T₀ , T₀) (T₀ , T₂ , T₁) = refl
cube-sum (T₂ , T₀ , T₀) (T₀ , T₂ , T₂) = refl
cube-sum (T₂ , T₀ , T₀) (T₁ , T₀ , T₀) = refl
cube-sum (T₂ , T₀ , T₀) (T₁ , T₀ , T₁) = refl
cube-sum (T₂ , T₀ , T₀) (T₁ , T₀ , T₂) = refl
cube-sum (T₂ , T₀ , T₀) (T₁ , T₁ , T₀) = refl
cube-sum (T₂ , T₀ , T₀) (T₁ , T₁ , T₁) = refl
cube-sum (T₂ , T₀ , T₀) (T₁ , T₁ , T₂) = refl
cube-sum (T₂ , T₀ , T₀) (T₁ , T₂ , T₀) = refl
cube-sum (T₂ , T₀ , T₀) (T₁ , T₂ , T₁) = refl
cube-sum (T₂ , T₀ , T₀) (T₁ , T₂ , T₂) = refl
cube-sum (T₂ , T₀ , T₀) (T₂ , T₀ , T₀) = refl
cube-sum (T₂ , T₀ , T₀) (T₂ , T₀ , T₁) = refl
cube-sum (T₂ , T₀ , T₀) (T₂ , T₀ , T₂) = refl
cube-sum (T₂ , T₀ , T₀) (T₂ , T₁ , T₀) = refl
cube-sum (T₂ , T₀ , T₀) (T₂ , T₁ , T₁) = refl
cube-sum (T₂ , T₀ , T₀) (T₂ , T₁ , T₂) = refl
cube-sum (T₂ , T₀ , T₀) (T₂ , T₂ , T₀) = refl
cube-sum (T₂ , T₀ , T₀) (T₂ , T₂ , T₁) = refl
cube-sum (T₂ , T₀ , T₀) (T₂ , T₂ , T₂) = refl
cube-sum (T₂ , T₀ , T₁) (T₀ , T₀ , T₀) = refl
cube-sum (T₂ , T₀ , T₁) (T₀ , T₀ , T₁) = refl
cube-sum (T₂ , T₀ , T₁) (T₀ , T₀ , T₂) = refl
cube-sum (T₂ , T₀ , T₁) (T₀ , T₁ , T₀) = refl
cube-sum (T₂ , T₀ , T₁) (T₀ , T₁ , T₁) = refl
cube-sum (T₂ , T₀ , T₁) (T₀ , T₁ , T₂) = refl
cube-sum (T₂ , T₀ , T₁) (T₀ , T₂ , T₀) = refl
cube-sum (T₂ , T₀ , T₁) (T₀ , T₂ , T₁) = refl
cube-sum (T₂ , T₀ , T₁) (T₀ , T₂ , T₂) = refl
cube-sum (T₂ , T₀ , T₁) (T₁ , T₀ , T₀) = refl
cube-sum (T₂ , T₀ , T₁) (T₁ , T₀ , T₁) = refl
cube-sum (T₂ , T₀ , T₁) (T₁ , T₀ , T₂) = refl
cube-sum (T₂ , T₀ , T₁) (T₁ , T₁ , T₀) = refl
cube-sum (T₂ , T₀ , T₁) (T₁ , T₁ , T₁) = refl
cube-sum (T₂ , T₀ , T₁) (T₁ , T₁ , T₂) = refl
cube-sum (T₂ , T₀ , T₁) (T₁ , T₂ , T₀) = refl
cube-sum (T₂ , T₀ , T₁) (T₁ , T₂ , T₁) = refl
cube-sum (T₂ , T₀ , T₁) (T₁ , T₂ , T₂) = refl
cube-sum (T₂ , T₀ , T₁) (T₂ , T₀ , T₀) = refl
cube-sum (T₂ , T₀ , T₁) (T₂ , T₀ , T₁) = refl
cube-sum (T₂ , T₀ , T₁) (T₂ , T₀ , T₂) = refl
cube-sum (T₂ , T₀ , T₁) (T₂ , T₁ , T₀) = refl
cube-sum (T₂ , T₀ , T₁) (T₂ , T₁ , T₁) = refl
cube-sum (T₂ , T₀ , T₁) (T₂ , T₁ , T₂) = refl
cube-sum (T₂ , T₀ , T₁) (T₂ , T₂ , T₀) = refl
cube-sum (T₂ , T₀ , T₁) (T₂ , T₂ , T₁) = refl
cube-sum (T₂ , T₀ , T₁) (T₂ , T₂ , T₂) = refl
cube-sum (T₂ , T₀ , T₂) (T₀ , T₀ , T₀) = refl
cube-sum (T₂ , T₀ , T₂) (T₀ , T₀ , T₁) = refl
cube-sum (T₂ , T₀ , T₂) (T₀ , T₀ , T₂) = refl
cube-sum (T₂ , T₀ , T₂) (T₀ , T₁ , T₀) = refl
cube-sum (T₂ , T₀ , T₂) (T₀ , T₁ , T₁) = refl
cube-sum (T₂ , T₀ , T₂) (T₀ , T₁ , T₂) = refl
cube-sum (T₂ , T₀ , T₂) (T₀ , T₂ , T₀) = refl
cube-sum (T₂ , T₀ , T₂) (T₀ , T₂ , T₁) = refl
cube-sum (T₂ , T₀ , T₂) (T₀ , T₂ , T₂) = refl
cube-sum (T₂ , T₀ , T₂) (T₁ , T₀ , T₀) = refl
cube-sum (T₂ , T₀ , T₂) (T₁ , T₀ , T₁) = refl
cube-sum (T₂ , T₀ , T₂) (T₁ , T₀ , T₂) = refl
cube-sum (T₂ , T₀ , T₂) (T₁ , T₁ , T₀) = refl
cube-sum (T₂ , T₀ , T₂) (T₁ , T₁ , T₁) = refl
cube-sum (T₂ , T₀ , T₂) (T₁ , T₁ , T₂) = refl
cube-sum (T₂ , T₀ , T₂) (T₁ , T₂ , T₀) = refl
cube-sum (T₂ , T₀ , T₂) (T₁ , T₂ , T₁) = refl
cube-sum (T₂ , T₀ , T₂) (T₁ , T₂ , T₂) = refl
cube-sum (T₂ , T₀ , T₂) (T₂ , T₀ , T₀) = refl
cube-sum (T₂ , T₀ , T₂) (T₂ , T₀ , T₁) = refl
cube-sum (T₂ , T₀ , T₂) (T₂ , T₀ , T₂) = refl
cube-sum (T₂ , T₀ , T₂) (T₂ , T₁ , T₀) = refl
cube-sum (T₂ , T₀ , T₂) (T₂ , T₁ , T₁) = refl
cube-sum (T₂ , T₀ , T₂) (T₂ , T₁ , T₂) = refl
cube-sum (T₂ , T₀ , T₂) (T₂ , T₂ , T₀) = refl
cube-sum (T₂ , T₀ , T₂) (T₂ , T₂ , T₁) = refl
cube-sum (T₂ , T₀ , T₂) (T₂ , T₂ , T₂) = refl
cube-sum (T₂ , T₁ , T₀) (T₀ , T₀ , T₀) = refl
cube-sum (T₂ , T₁ , T₀) (T₀ , T₀ , T₁) = refl
cube-sum (T₂ , T₁ , T₀) (T₀ , T₀ , T₂) = refl
cube-sum (T₂ , T₁ , T₀) (T₀ , T₁ , T₀) = refl
cube-sum (T₂ , T₁ , T₀) (T₀ , T₁ , T₁) = refl
cube-sum (T₂ , T₁ , T₀) (T₀ , T₁ , T₂) = refl
cube-sum (T₂ , T₁ , T₀) (T₀ , T₂ , T₀) = refl
cube-sum (T₂ , T₁ , T₀) (T₀ , T₂ , T₁) = refl
cube-sum (T₂ , T₁ , T₀) (T₀ , T₂ , T₂) = refl
cube-sum (T₂ , T₁ , T₀) (T₁ , T₀ , T₀) = refl
cube-sum (T₂ , T₁ , T₀) (T₁ , T₀ , T₁) = refl
cube-sum (T₂ , T₁ , T₀) (T₁ , T₀ , T₂) = refl
cube-sum (T₂ , T₁ , T₀) (T₁ , T₁ , T₀) = refl
cube-sum (T₂ , T₁ , T₀) (T₁ , T₁ , T₁) = refl
cube-sum (T₂ , T₁ , T₀) (T₁ , T₁ , T₂) = refl
cube-sum (T₂ , T₁ , T₀) (T₁ , T₂ , T₀) = refl
cube-sum (T₂ , T₁ , T₀) (T₁ , T₂ , T₁) = refl
cube-sum (T₂ , T₁ , T₀) (T₁ , T₂ , T₂) = refl
cube-sum (T₂ , T₁ , T₀) (T₂ , T₀ , T₀) = refl
cube-sum (T₂ , T₁ , T₀) (T₂ , T₀ , T₁) = refl
cube-sum (T₂ , T₁ , T₀) (T₂ , T₀ , T₂) = refl
cube-sum (T₂ , T₁ , T₀) (T₂ , T₁ , T₀) = refl
cube-sum (T₂ , T₁ , T₀) (T₂ , T₁ , T₁) = refl
cube-sum (T₂ , T₁ , T₀) (T₂ , T₁ , T₂) = refl
cube-sum (T₂ , T₁ , T₀) (T₂ , T₂ , T₀) = refl
cube-sum (T₂ , T₁ , T₀) (T₂ , T₂ , T₁) = refl
cube-sum (T₂ , T₁ , T₀) (T₂ , T₂ , T₂) = refl
cube-sum (T₂ , T₁ , T₁) (T₀ , T₀ , T₀) = refl
cube-sum (T₂ , T₁ , T₁) (T₀ , T₀ , T₁) = refl
cube-sum (T₂ , T₁ , T₁) (T₀ , T₀ , T₂) = refl
cube-sum (T₂ , T₁ , T₁) (T₀ , T₁ , T₀) = refl
cube-sum (T₂ , T₁ , T₁) (T₀ , T₁ , T₁) = refl
cube-sum (T₂ , T₁ , T₁) (T₀ , T₁ , T₂) = refl
cube-sum (T₂ , T₁ , T₁) (T₀ , T₂ , T₀) = refl
cube-sum (T₂ , T₁ , T₁) (T₀ , T₂ , T₁) = refl
cube-sum (T₂ , T₁ , T₁) (T₀ , T₂ , T₂) = refl
cube-sum (T₂ , T₁ , T₁) (T₁ , T₀ , T₀) = refl
cube-sum (T₂ , T₁ , T₁) (T₁ , T₀ , T₁) = refl
cube-sum (T₂ , T₁ , T₁) (T₁ , T₀ , T₂) = refl
cube-sum (T₂ , T₁ , T₁) (T₁ , T₁ , T₀) = refl
cube-sum (T₂ , T₁ , T₁) (T₁ , T₁ , T₁) = refl
cube-sum (T₂ , T₁ , T₁) (T₁ , T₁ , T₂) = refl
cube-sum (T₂ , T₁ , T₁) (T₁ , T₂ , T₀) = refl
cube-sum (T₂ , T₁ , T₁) (T₁ , T₂ , T₁) = refl
cube-sum (T₂ , T₁ , T₁) (T₁ , T₂ , T₂) = refl
cube-sum (T₂ , T₁ , T₁) (T₂ , T₀ , T₀) = refl
cube-sum (T₂ , T₁ , T₁) (T₂ , T₀ , T₁) = refl
cube-sum (T₂ , T₁ , T₁) (T₂ , T₀ , T₂) = refl
cube-sum (T₂ , T₁ , T₁) (T₂ , T₁ , T₀) = refl
cube-sum (T₂ , T₁ , T₁) (T₂ , T₁ , T₁) = refl
cube-sum (T₂ , T₁ , T₁) (T₂ , T₁ , T₂) = refl
cube-sum (T₂ , T₁ , T₁) (T₂ , T₂ , T₀) = refl
cube-sum (T₂ , T₁ , T₁) (T₂ , T₂ , T₁) = refl
cube-sum (T₂ , T₁ , T₁) (T₂ , T₂ , T₂) = refl
cube-sum (T₂ , T₁ , T₂) (T₀ , T₀ , T₀) = refl
cube-sum (T₂ , T₁ , T₂) (T₀ , T₀ , T₁) = refl
cube-sum (T₂ , T₁ , T₂) (T₀ , T₀ , T₂) = refl
cube-sum (T₂ , T₁ , T₂) (T₀ , T₁ , T₀) = refl
cube-sum (T₂ , T₁ , T₂) (T₀ , T₁ , T₁) = refl
cube-sum (T₂ , T₁ , T₂) (T₀ , T₁ , T₂) = refl
cube-sum (T₂ , T₁ , T₂) (T₀ , T₂ , T₀) = refl
cube-sum (T₂ , T₁ , T₂) (T₀ , T₂ , T₁) = refl
cube-sum (T₂ , T₁ , T₂) (T₀ , T₂ , T₂) = refl
cube-sum (T₂ , T₁ , T₂) (T₁ , T₀ , T₀) = refl
cube-sum (T₂ , T₁ , T₂) (T₁ , T₀ , T₁) = refl
cube-sum (T₂ , T₁ , T₂) (T₁ , T₀ , T₂) = refl
cube-sum (T₂ , T₁ , T₂) (T₁ , T₁ , T₀) = refl
cube-sum (T₂ , T₁ , T₂) (T₁ , T₁ , T₁) = refl
cube-sum (T₂ , T₁ , T₂) (T₁ , T₁ , T₂) = refl
cube-sum (T₂ , T₁ , T₂) (T₁ , T₂ , T₀) = refl
cube-sum (T₂ , T₁ , T₂) (T₁ , T₂ , T₁) = refl
cube-sum (T₂ , T₁ , T₂) (T₁ , T₂ , T₂) = refl
cube-sum (T₂ , T₁ , T₂) (T₂ , T₀ , T₀) = refl
cube-sum (T₂ , T₁ , T₂) (T₂ , T₀ , T₁) = refl
cube-sum (T₂ , T₁ , T₂) (T₂ , T₀ , T₂) = refl
cube-sum (T₂ , T₁ , T₂) (T₂ , T₁ , T₀) = refl
cube-sum (T₂ , T₁ , T₂) (T₂ , T₁ , T₁) = refl
cube-sum (T₂ , T₁ , T₂) (T₂ , T₁ , T₂) = refl
cube-sum (T₂ , T₁ , T₂) (T₂ , T₂ , T₀) = refl
cube-sum (T₂ , T₁ , T₂) (T₂ , T₂ , T₁) = refl
cube-sum (T₂ , T₁ , T₂) (T₂ , T₂ , T₂) = refl
cube-sum (T₂ , T₂ , T₀) (T₀ , T₀ , T₀) = refl
cube-sum (T₂ , T₂ , T₀) (T₀ , T₀ , T₁) = refl
cube-sum (T₂ , T₂ , T₀) (T₀ , T₀ , T₂) = refl
cube-sum (T₂ , T₂ , T₀) (T₀ , T₁ , T₀) = refl
cube-sum (T₂ , T₂ , T₀) (T₀ , T₁ , T₁) = refl
cube-sum (T₂ , T₂ , T₀) (T₀ , T₁ , T₂) = refl
cube-sum (T₂ , T₂ , T₀) (T₀ , T₂ , T₀) = refl
cube-sum (T₂ , T₂ , T₀) (T₀ , T₂ , T₁) = refl
cube-sum (T₂ , T₂ , T₀) (T₀ , T₂ , T₂) = refl
cube-sum (T₂ , T₂ , T₀) (T₁ , T₀ , T₀) = refl
cube-sum (T₂ , T₂ , T₀) (T₁ , T₀ , T₁) = refl
cube-sum (T₂ , T₂ , T₀) (T₁ , T₀ , T₂) = refl
cube-sum (T₂ , T₂ , T₀) (T₁ , T₁ , T₀) = refl
cube-sum (T₂ , T₂ , T₀) (T₁ , T₁ , T₁) = refl
cube-sum (T₂ , T₂ , T₀) (T₁ , T₁ , T₂) = refl
cube-sum (T₂ , T₂ , T₀) (T₁ , T₂ , T₀) = refl
cube-sum (T₂ , T₂ , T₀) (T₁ , T₂ , T₁) = refl
cube-sum (T₂ , T₂ , T₀) (T₁ , T₂ , T₂) = refl
cube-sum (T₂ , T₂ , T₀) (T₂ , T₀ , T₀) = refl
cube-sum (T₂ , T₂ , T₀) (T₂ , T₀ , T₁) = refl
cube-sum (T₂ , T₂ , T₀) (T₂ , T₀ , T₂) = refl
cube-sum (T₂ , T₂ , T₀) (T₂ , T₁ , T₀) = refl
cube-sum (T₂ , T₂ , T₀) (T₂ , T₁ , T₁) = refl
cube-sum (T₂ , T₂ , T₀) (T₂ , T₁ , T₂) = refl
cube-sum (T₂ , T₂ , T₀) (T₂ , T₂ , T₀) = refl
cube-sum (T₂ , T₂ , T₀) (T₂ , T₂ , T₁) = refl
cube-sum (T₂ , T₂ , T₀) (T₂ , T₂ , T₂) = refl
cube-sum (T₂ , T₂ , T₁) (T₀ , T₀ , T₀) = refl
cube-sum (T₂ , T₂ , T₁) (T₀ , T₀ , T₁) = refl
cube-sum (T₂ , T₂ , T₁) (T₀ , T₀ , T₂) = refl
cube-sum (T₂ , T₂ , T₁) (T₀ , T₁ , T₀) = refl
cube-sum (T₂ , T₂ , T₁) (T₀ , T₁ , T₁) = refl
cube-sum (T₂ , T₂ , T₁) (T₀ , T₁ , T₂) = refl
cube-sum (T₂ , T₂ , T₁) (T₀ , T₂ , T₀) = refl
cube-sum (T₂ , T₂ , T₁) (T₀ , T₂ , T₁) = refl
cube-sum (T₂ , T₂ , T₁) (T₀ , T₂ , T₂) = refl
cube-sum (T₂ , T₂ , T₁) (T₁ , T₀ , T₀) = refl
cube-sum (T₂ , T₂ , T₁) (T₁ , T₀ , T₁) = refl
cube-sum (T₂ , T₂ , T₁) (T₁ , T₀ , T₂) = refl
cube-sum (T₂ , T₂ , T₁) (T₁ , T₁ , T₀) = refl
cube-sum (T₂ , T₂ , T₁) (T₁ , T₁ , T₁) = refl
cube-sum (T₂ , T₂ , T₁) (T₁ , T₁ , T₂) = refl
cube-sum (T₂ , T₂ , T₁) (T₁ , T₂ , T₀) = refl
cube-sum (T₂ , T₂ , T₁) (T₁ , T₂ , T₁) = refl
cube-sum (T₂ , T₂ , T₁) (T₁ , T₂ , T₂) = refl
cube-sum (T₂ , T₂ , T₁) (T₂ , T₀ , T₀) = refl
cube-sum (T₂ , T₂ , T₁) (T₂ , T₀ , T₁) = refl
cube-sum (T₂ , T₂ , T₁) (T₂ , T₀ , T₂) = refl
cube-sum (T₂ , T₂ , T₁) (T₂ , T₁ , T₀) = refl
cube-sum (T₂ , T₂ , T₁) (T₂ , T₁ , T₁) = refl
cube-sum (T₂ , T₂ , T₁) (T₂ , T₁ , T₂) = refl
cube-sum (T₂ , T₂ , T₁) (T₂ , T₂ , T₀) = refl
cube-sum (T₂ , T₂ , T₁) (T₂ , T₂ , T₁) = refl
cube-sum (T₂ , T₂ , T₁) (T₂ , T₂ , T₂) = refl
cube-sum (T₂ , T₂ , T₂) (T₀ , T₀ , T₀) = refl
cube-sum (T₂ , T₂ , T₂) (T₀ , T₀ , T₁) = refl
cube-sum (T₂ , T₂ , T₂) (T₀ , T₀ , T₂) = refl
cube-sum (T₂ , T₂ , T₂) (T₀ , T₁ , T₀) = refl
cube-sum (T₂ , T₂ , T₂) (T₀ , T₁ , T₁) = refl
cube-sum (T₂ , T₂ , T₂) (T₀ , T₁ , T₂) = refl
cube-sum (T₂ , T₂ , T₂) (T₀ , T₂ , T₀) = refl
cube-sum (T₂ , T₂ , T₂) (T₀ , T₂ , T₁) = refl
cube-sum (T₂ , T₂ , T₂) (T₀ , T₂ , T₂) = refl
cube-sum (T₂ , T₂ , T₂) (T₁ , T₀ , T₀) = refl
cube-sum (T₂ , T₂ , T₂) (T₁ , T₀ , T₁) = refl
cube-sum (T₂ , T₂ , T₂) (T₁ , T₀ , T₂) = refl
cube-sum (T₂ , T₂ , T₂) (T₁ , T₁ , T₀) = refl
cube-sum (T₂ , T₂ , T₂) (T₁ , T₁ , T₁) = refl
cube-sum (T₂ , T₂ , T₂) (T₁ , T₁ , T₂) = refl
cube-sum (T₂ , T₂ , T₂) (T₁ , T₂ , T₀) = refl
cube-sum (T₂ , T₂ , T₂) (T₁ , T₂ , T₁) = refl
cube-sum (T₂ , T₂ , T₂) (T₁ , T₂ , T₂) = refl
cube-sum (T₂ , T₂ , T₂) (T₂ , T₀ , T₀) = refl
cube-sum (T₂ , T₂ , T₂) (T₂ , T₀ , T₁) = refl
cube-sum (T₂ , T₂ , T₂) (T₂ , T₀ , T₂) = refl
cube-sum (T₂ , T₂ , T₂) (T₂ , T₁ , T₀) = refl
cube-sum (T₂ , T₂ , T₂) (T₂ , T₁ , T₁) = refl
cube-sum (T₂ , T₂ , T₂) (T₂ , T₁ , T₂) = refl
cube-sum (T₂ , T₂ , T₂) (T₂ , T₂ , T₀) = refl
cube-sum (T₂ , T₂ , T₂) (T₂ , T₂ , T₁) = refl
cube-sum (T₂ , T₂ , T₂) (T₂ , T₂ , T₂) = refl

-- γ 结合: (x·y)·γ = x·(y·γ)
assoc-γ : ∀ x y → (x *₉ y) *₉ γ ≡ x *₉ (y *₉ γ)
assoc-γ (T₀ , T₀ , T₀) (T₀ , T₀ , T₀) = refl
assoc-γ (T₀ , T₀ , T₀) (T₀ , T₀ , T₁) = refl
assoc-γ (T₀ , T₀ , T₀) (T₀ , T₀ , T₂) = refl
assoc-γ (T₀ , T₀ , T₀) (T₀ , T₁ , T₀) = refl
assoc-γ (T₀ , T₀ , T₀) (T₀ , T₁ , T₁) = refl
assoc-γ (T₀ , T₀ , T₀) (T₀ , T₁ , T₂) = refl
assoc-γ (T₀ , T₀ , T₀) (T₀ , T₂ , T₀) = refl
assoc-γ (T₀ , T₀ , T₀) (T₀ , T₂ , T₁) = refl
assoc-γ (T₀ , T₀ , T₀) (T₀ , T₂ , T₂) = refl
assoc-γ (T₀ , T₀ , T₀) (T₁ , T₀ , T₀) = refl
assoc-γ (T₀ , T₀ , T₀) (T₁ , T₀ , T₁) = refl
assoc-γ (T₀ , T₀ , T₀) (T₁ , T₀ , T₂) = refl
assoc-γ (T₀ , T₀ , T₀) (T₁ , T₁ , T₀) = refl
assoc-γ (T₀ , T₀ , T₀) (T₁ , T₁ , T₁) = refl
assoc-γ (T₀ , T₀ , T₀) (T₁ , T₁ , T₂) = refl
assoc-γ (T₀ , T₀ , T₀) (T₁ , T₂ , T₀) = refl
assoc-γ (T₀ , T₀ , T₀) (T₁ , T₂ , T₁) = refl
assoc-γ (T₀ , T₀ , T₀) (T₁ , T₂ , T₂) = refl
assoc-γ (T₀ , T₀ , T₀) (T₂ , T₀ , T₀) = refl
assoc-γ (T₀ , T₀ , T₀) (T₂ , T₀ , T₁) = refl
assoc-γ (T₀ , T₀ , T₀) (T₂ , T₀ , T₂) = refl
assoc-γ (T₀ , T₀ , T₀) (T₂ , T₁ , T₀) = refl
assoc-γ (T₀ , T₀ , T₀) (T₂ , T₁ , T₁) = refl
assoc-γ (T₀ , T₀ , T₀) (T₂ , T₁ , T₂) = refl
assoc-γ (T₀ , T₀ , T₀) (T₂ , T₂ , T₀) = refl
assoc-γ (T₀ , T₀ , T₀) (T₂ , T₂ , T₁) = refl
assoc-γ (T₀ , T₀ , T₀) (T₂ , T₂ , T₂) = refl
assoc-γ (T₀ , T₀ , T₁) (T₀ , T₀ , T₀) = refl
assoc-γ (T₀ , T₀ , T₁) (T₀ , T₀ , T₁) = refl
assoc-γ (T₀ , T₀ , T₁) (T₀ , T₀ , T₂) = refl
assoc-γ (T₀ , T₀ , T₁) (T₀ , T₁ , T₀) = refl
assoc-γ (T₀ , T₀ , T₁) (T₀ , T₁ , T₁) = refl
assoc-γ (T₀ , T₀ , T₁) (T₀ , T₁ , T₂) = refl
assoc-γ (T₀ , T₀ , T₁) (T₀ , T₂ , T₀) = refl
assoc-γ (T₀ , T₀ , T₁) (T₀ , T₂ , T₁) = refl
assoc-γ (T₀ , T₀ , T₁) (T₀ , T₂ , T₂) = refl
assoc-γ (T₀ , T₀ , T₁) (T₁ , T₀ , T₀) = refl
assoc-γ (T₀ , T₀ , T₁) (T₁ , T₀ , T₁) = refl
assoc-γ (T₀ , T₀ , T₁) (T₁ , T₀ , T₂) = refl
assoc-γ (T₀ , T₀ , T₁) (T₁ , T₁ , T₀) = refl
assoc-γ (T₀ , T₀ , T₁) (T₁ , T₁ , T₁) = refl
assoc-γ (T₀ , T₀ , T₁) (T₁ , T₁ , T₂) = refl
assoc-γ (T₀ , T₀ , T₁) (T₁ , T₂ , T₀) = refl
assoc-γ (T₀ , T₀ , T₁) (T₁ , T₂ , T₁) = refl
assoc-γ (T₀ , T₀ , T₁) (T₁ , T₂ , T₂) = refl
assoc-γ (T₀ , T₀ , T₁) (T₂ , T₀ , T₀) = refl
assoc-γ (T₀ , T₀ , T₁) (T₂ , T₀ , T₁) = refl
assoc-γ (T₀ , T₀ , T₁) (T₂ , T₀ , T₂) = refl
assoc-γ (T₀ , T₀ , T₁) (T₂ , T₁ , T₀) = refl
assoc-γ (T₀ , T₀ , T₁) (T₂ , T₁ , T₁) = refl
assoc-γ (T₀ , T₀ , T₁) (T₂ , T₁ , T₂) = refl
assoc-γ (T₀ , T₀ , T₁) (T₂ , T₂ , T₀) = refl
assoc-γ (T₀ , T₀ , T₁) (T₂ , T₂ , T₁) = refl
assoc-γ (T₀ , T₀ , T₁) (T₂ , T₂ , T₂) = refl
assoc-γ (T₀ , T₀ , T₂) (T₀ , T₀ , T₀) = refl
assoc-γ (T₀ , T₀ , T₂) (T₀ , T₀ , T₁) = refl
assoc-γ (T₀ , T₀ , T₂) (T₀ , T₀ , T₂) = refl
assoc-γ (T₀ , T₀ , T₂) (T₀ , T₁ , T₀) = refl
assoc-γ (T₀ , T₀ , T₂) (T₀ , T₁ , T₁) = refl
assoc-γ (T₀ , T₀ , T₂) (T₀ , T₁ , T₂) = refl
assoc-γ (T₀ , T₀ , T₂) (T₀ , T₂ , T₀) = refl
assoc-γ (T₀ , T₀ , T₂) (T₀ , T₂ , T₁) = refl
assoc-γ (T₀ , T₀ , T₂) (T₀ , T₂ , T₂) = refl
assoc-γ (T₀ , T₀ , T₂) (T₁ , T₀ , T₀) = refl
assoc-γ (T₀ , T₀ , T₂) (T₁ , T₀ , T₁) = refl
assoc-γ (T₀ , T₀ , T₂) (T₁ , T₀ , T₂) = refl
assoc-γ (T₀ , T₀ , T₂) (T₁ , T₁ , T₀) = refl
assoc-γ (T₀ , T₀ , T₂) (T₁ , T₁ , T₁) = refl
assoc-γ (T₀ , T₀ , T₂) (T₁ , T₁ , T₂) = refl
assoc-γ (T₀ , T₀ , T₂) (T₁ , T₂ , T₀) = refl
assoc-γ (T₀ , T₀ , T₂) (T₁ , T₂ , T₁) = refl
assoc-γ (T₀ , T₀ , T₂) (T₁ , T₂ , T₂) = refl
assoc-γ (T₀ , T₀ , T₂) (T₂ , T₀ , T₀) = refl
assoc-γ (T₀ , T₀ , T₂) (T₂ , T₀ , T₁) = refl
assoc-γ (T₀ , T₀ , T₂) (T₂ , T₀ , T₂) = refl
assoc-γ (T₀ , T₀ , T₂) (T₂ , T₁ , T₀) = refl
assoc-γ (T₀ , T₀ , T₂) (T₂ , T₁ , T₁) = refl
assoc-γ (T₀ , T₀ , T₂) (T₂ , T₁ , T₂) = refl
assoc-γ (T₀ , T₀ , T₂) (T₂ , T₂ , T₀) = refl
assoc-γ (T₀ , T₀ , T₂) (T₂ , T₂ , T₁) = refl
assoc-γ (T₀ , T₀ , T₂) (T₂ , T₂ , T₂) = refl
assoc-γ (T₀ , T₁ , T₀) (T₀ , T₀ , T₀) = refl
assoc-γ (T₀ , T₁ , T₀) (T₀ , T₀ , T₁) = refl
assoc-γ (T₀ , T₁ , T₀) (T₀ , T₀ , T₂) = refl
assoc-γ (T₀ , T₁ , T₀) (T₀ , T₁ , T₀) = refl
assoc-γ (T₀ , T₁ , T₀) (T₀ , T₁ , T₁) = refl
assoc-γ (T₀ , T₁ , T₀) (T₀ , T₁ , T₂) = refl
assoc-γ (T₀ , T₁ , T₀) (T₀ , T₂ , T₀) = refl
assoc-γ (T₀ , T₁ , T₀) (T₀ , T₂ , T₁) = refl
assoc-γ (T₀ , T₁ , T₀) (T₀ , T₂ , T₂) = refl
assoc-γ (T₀ , T₁ , T₀) (T₁ , T₀ , T₀) = refl
assoc-γ (T₀ , T₁ , T₀) (T₁ , T₀ , T₁) = refl
assoc-γ (T₀ , T₁ , T₀) (T₁ , T₀ , T₂) = refl
assoc-γ (T₀ , T₁ , T₀) (T₁ , T₁ , T₀) = refl
assoc-γ (T₀ , T₁ , T₀) (T₁ , T₁ , T₁) = refl
assoc-γ (T₀ , T₁ , T₀) (T₁ , T₁ , T₂) = refl
assoc-γ (T₀ , T₁ , T₀) (T₁ , T₂ , T₀) = refl
assoc-γ (T₀ , T₁ , T₀) (T₁ , T₂ , T₁) = refl
assoc-γ (T₀ , T₁ , T₀) (T₁ , T₂ , T₂) = refl
assoc-γ (T₀ , T₁ , T₀) (T₂ , T₀ , T₀) = refl
assoc-γ (T₀ , T₁ , T₀) (T₂ , T₀ , T₁) = refl
assoc-γ (T₀ , T₁ , T₀) (T₂ , T₀ , T₂) = refl
assoc-γ (T₀ , T₁ , T₀) (T₂ , T₁ , T₀) = refl
assoc-γ (T₀ , T₁ , T₀) (T₂ , T₁ , T₁) = refl
assoc-γ (T₀ , T₁ , T₀) (T₂ , T₁ , T₂) = refl
assoc-γ (T₀ , T₁ , T₀) (T₂ , T₂ , T₀) = refl
assoc-γ (T₀ , T₁ , T₀) (T₂ , T₂ , T₁) = refl
assoc-γ (T₀ , T₁ , T₀) (T₂ , T₂ , T₂) = refl
assoc-γ (T₀ , T₁ , T₁) (T₀ , T₀ , T₀) = refl
assoc-γ (T₀ , T₁ , T₁) (T₀ , T₀ , T₁) = refl
assoc-γ (T₀ , T₁ , T₁) (T₀ , T₀ , T₂) = refl
assoc-γ (T₀ , T₁ , T₁) (T₀ , T₁ , T₀) = refl
assoc-γ (T₀ , T₁ , T₁) (T₀ , T₁ , T₁) = refl
assoc-γ (T₀ , T₁ , T₁) (T₀ , T₁ , T₂) = refl
assoc-γ (T₀ , T₁ , T₁) (T₀ , T₂ , T₀) = refl
assoc-γ (T₀ , T₁ , T₁) (T₀ , T₂ , T₁) = refl
assoc-γ (T₀ , T₁ , T₁) (T₀ , T₂ , T₂) = refl
assoc-γ (T₀ , T₁ , T₁) (T₁ , T₀ , T₀) = refl
assoc-γ (T₀ , T₁ , T₁) (T₁ , T₀ , T₁) = refl
assoc-γ (T₀ , T₁ , T₁) (T₁ , T₀ , T₂) = refl
assoc-γ (T₀ , T₁ , T₁) (T₁ , T₁ , T₀) = refl
assoc-γ (T₀ , T₁ , T₁) (T₁ , T₁ , T₁) = refl
assoc-γ (T₀ , T₁ , T₁) (T₁ , T₁ , T₂) = refl
assoc-γ (T₀ , T₁ , T₁) (T₁ , T₂ , T₀) = refl
assoc-γ (T₀ , T₁ , T₁) (T₁ , T₂ , T₁) = refl
assoc-γ (T₀ , T₁ , T₁) (T₁ , T₂ , T₂) = refl
assoc-γ (T₀ , T₁ , T₁) (T₂ , T₀ , T₀) = refl
assoc-γ (T₀ , T₁ , T₁) (T₂ , T₀ , T₁) = refl
assoc-γ (T₀ , T₁ , T₁) (T₂ , T₀ , T₂) = refl
assoc-γ (T₀ , T₁ , T₁) (T₂ , T₁ , T₀) = refl
assoc-γ (T₀ , T₁ , T₁) (T₂ , T₁ , T₁) = refl
assoc-γ (T₀ , T₁ , T₁) (T₂ , T₁ , T₂) = refl
assoc-γ (T₀ , T₁ , T₁) (T₂ , T₂ , T₀) = refl
assoc-γ (T₀ , T₁ , T₁) (T₂ , T₂ , T₁) = refl
assoc-γ (T₀ , T₁ , T₁) (T₂ , T₂ , T₂) = refl
assoc-γ (T₀ , T₁ , T₂) (T₀ , T₀ , T₀) = refl
assoc-γ (T₀ , T₁ , T₂) (T₀ , T₀ , T₁) = refl
assoc-γ (T₀ , T₁ , T₂) (T₀ , T₀ , T₂) = refl
assoc-γ (T₀ , T₁ , T₂) (T₀ , T₁ , T₀) = refl
assoc-γ (T₀ , T₁ , T₂) (T₀ , T₁ , T₁) = refl
assoc-γ (T₀ , T₁ , T₂) (T₀ , T₁ , T₂) = refl
assoc-γ (T₀ , T₁ , T₂) (T₀ , T₂ , T₀) = refl
assoc-γ (T₀ , T₁ , T₂) (T₀ , T₂ , T₁) = refl
assoc-γ (T₀ , T₁ , T₂) (T₀ , T₂ , T₂) = refl
assoc-γ (T₀ , T₁ , T₂) (T₁ , T₀ , T₀) = refl
assoc-γ (T₀ , T₁ , T₂) (T₁ , T₀ , T₁) = refl
assoc-γ (T₀ , T₁ , T₂) (T₁ , T₀ , T₂) = refl
assoc-γ (T₀ , T₁ , T₂) (T₁ , T₁ , T₀) = refl
assoc-γ (T₀ , T₁ , T₂) (T₁ , T₁ , T₁) = refl
assoc-γ (T₀ , T₁ , T₂) (T₁ , T₁ , T₂) = refl
assoc-γ (T₀ , T₁ , T₂) (T₁ , T₂ , T₀) = refl
assoc-γ (T₀ , T₁ , T₂) (T₁ , T₂ , T₁) = refl
assoc-γ (T₀ , T₁ , T₂) (T₁ , T₂ , T₂) = refl
assoc-γ (T₀ , T₁ , T₂) (T₂ , T₀ , T₀) = refl
assoc-γ (T₀ , T₁ , T₂) (T₂ , T₀ , T₁) = refl
assoc-γ (T₀ , T₁ , T₂) (T₂ , T₀ , T₂) = refl
assoc-γ (T₀ , T₁ , T₂) (T₂ , T₁ , T₀) = refl
assoc-γ (T₀ , T₁ , T₂) (T₂ , T₁ , T₁) = refl
assoc-γ (T₀ , T₁ , T₂) (T₂ , T₁ , T₂) = refl
assoc-γ (T₀ , T₁ , T₂) (T₂ , T₂ , T₀) = refl
assoc-γ (T₀ , T₁ , T₂) (T₂ , T₂ , T₁) = refl
assoc-γ (T₀ , T₁ , T₂) (T₂ , T₂ , T₂) = refl
assoc-γ (T₀ , T₂ , T₀) (T₀ , T₀ , T₀) = refl
assoc-γ (T₀ , T₂ , T₀) (T₀ , T₀ , T₁) = refl
assoc-γ (T₀ , T₂ , T₀) (T₀ , T₀ , T₂) = refl
assoc-γ (T₀ , T₂ , T₀) (T₀ , T₁ , T₀) = refl
assoc-γ (T₀ , T₂ , T₀) (T₀ , T₁ , T₁) = refl
assoc-γ (T₀ , T₂ , T₀) (T₀ , T₁ , T₂) = refl
assoc-γ (T₀ , T₂ , T₀) (T₀ , T₂ , T₀) = refl
assoc-γ (T₀ , T₂ , T₀) (T₀ , T₂ , T₁) = refl
assoc-γ (T₀ , T₂ , T₀) (T₀ , T₂ , T₂) = refl
assoc-γ (T₀ , T₂ , T₀) (T₁ , T₀ , T₀) = refl
assoc-γ (T₀ , T₂ , T₀) (T₁ , T₀ , T₁) = refl
assoc-γ (T₀ , T₂ , T₀) (T₁ , T₀ , T₂) = refl
assoc-γ (T₀ , T₂ , T₀) (T₁ , T₁ , T₀) = refl
assoc-γ (T₀ , T₂ , T₀) (T₁ , T₁ , T₁) = refl
assoc-γ (T₀ , T₂ , T₀) (T₁ , T₁ , T₂) = refl
assoc-γ (T₀ , T₂ , T₀) (T₁ , T₂ , T₀) = refl
assoc-γ (T₀ , T₂ , T₀) (T₁ , T₂ , T₁) = refl
assoc-γ (T₀ , T₂ , T₀) (T₁ , T₂ , T₂) = refl
assoc-γ (T₀ , T₂ , T₀) (T₂ , T₀ , T₀) = refl
assoc-γ (T₀ , T₂ , T₀) (T₂ , T₀ , T₁) = refl
assoc-γ (T₀ , T₂ , T₀) (T₂ , T₀ , T₂) = refl
assoc-γ (T₀ , T₂ , T₀) (T₂ , T₁ , T₀) = refl
assoc-γ (T₀ , T₂ , T₀) (T₂ , T₁ , T₁) = refl
assoc-γ (T₀ , T₂ , T₀) (T₂ , T₁ , T₂) = refl
assoc-γ (T₀ , T₂ , T₀) (T₂ , T₂ , T₀) = refl
assoc-γ (T₀ , T₂ , T₀) (T₂ , T₂ , T₁) = refl
assoc-γ (T₀ , T₂ , T₀) (T₂ , T₂ , T₂) = refl
assoc-γ (T₀ , T₂ , T₁) (T₀ , T₀ , T₀) = refl
assoc-γ (T₀ , T₂ , T₁) (T₀ , T₀ , T₁) = refl
assoc-γ (T₀ , T₂ , T₁) (T₀ , T₀ , T₂) = refl
assoc-γ (T₀ , T₂ , T₁) (T₀ , T₁ , T₀) = refl
assoc-γ (T₀ , T₂ , T₁) (T₀ , T₁ , T₁) = refl
assoc-γ (T₀ , T₂ , T₁) (T₀ , T₁ , T₂) = refl
assoc-γ (T₀ , T₂ , T₁) (T₀ , T₂ , T₀) = refl
assoc-γ (T₀ , T₂ , T₁) (T₀ , T₂ , T₁) = refl
assoc-γ (T₀ , T₂ , T₁) (T₀ , T₂ , T₂) = refl
assoc-γ (T₀ , T₂ , T₁) (T₁ , T₀ , T₀) = refl
assoc-γ (T₀ , T₂ , T₁) (T₁ , T₀ , T₁) = refl
assoc-γ (T₀ , T₂ , T₁) (T₁ , T₀ , T₂) = refl
assoc-γ (T₀ , T₂ , T₁) (T₁ , T₁ , T₀) = refl
assoc-γ (T₀ , T₂ , T₁) (T₁ , T₁ , T₁) = refl
assoc-γ (T₀ , T₂ , T₁) (T₁ , T₁ , T₂) = refl
assoc-γ (T₀ , T₂ , T₁) (T₁ , T₂ , T₀) = refl
assoc-γ (T₀ , T₂ , T₁) (T₁ , T₂ , T₁) = refl
assoc-γ (T₀ , T₂ , T₁) (T₁ , T₂ , T₂) = refl
assoc-γ (T₀ , T₂ , T₁) (T₂ , T₀ , T₀) = refl
assoc-γ (T₀ , T₂ , T₁) (T₂ , T₀ , T₁) = refl
assoc-γ (T₀ , T₂ , T₁) (T₂ , T₀ , T₂) = refl
assoc-γ (T₀ , T₂ , T₁) (T₂ , T₁ , T₀) = refl
assoc-γ (T₀ , T₂ , T₁) (T₂ , T₁ , T₁) = refl
assoc-γ (T₀ , T₂ , T₁) (T₂ , T₁ , T₂) = refl
assoc-γ (T₀ , T₂ , T₁) (T₂ , T₂ , T₀) = refl
assoc-γ (T₀ , T₂ , T₁) (T₂ , T₂ , T₁) = refl
assoc-γ (T₀ , T₂ , T₁) (T₂ , T₂ , T₂) = refl
assoc-γ (T₀ , T₂ , T₂) (T₀ , T₀ , T₀) = refl
assoc-γ (T₀ , T₂ , T₂) (T₀ , T₀ , T₁) = refl
assoc-γ (T₀ , T₂ , T₂) (T₀ , T₀ , T₂) = refl
assoc-γ (T₀ , T₂ , T₂) (T₀ , T₁ , T₀) = refl
assoc-γ (T₀ , T₂ , T₂) (T₀ , T₁ , T₁) = refl
assoc-γ (T₀ , T₂ , T₂) (T₀ , T₁ , T₂) = refl
assoc-γ (T₀ , T₂ , T₂) (T₀ , T₂ , T₀) = refl
assoc-γ (T₀ , T₂ , T₂) (T₀ , T₂ , T₁) = refl
assoc-γ (T₀ , T₂ , T₂) (T₀ , T₂ , T₂) = refl
assoc-γ (T₀ , T₂ , T₂) (T₁ , T₀ , T₀) = refl
assoc-γ (T₀ , T₂ , T₂) (T₁ , T₀ , T₁) = refl
assoc-γ (T₀ , T₂ , T₂) (T₁ , T₀ , T₂) = refl
assoc-γ (T₀ , T₂ , T₂) (T₁ , T₁ , T₀) = refl
assoc-γ (T₀ , T₂ , T₂) (T₁ , T₁ , T₁) = refl
assoc-γ (T₀ , T₂ , T₂) (T₁ , T₁ , T₂) = refl
assoc-γ (T₀ , T₂ , T₂) (T₁ , T₂ , T₀) = refl
assoc-γ (T₀ , T₂ , T₂) (T₁ , T₂ , T₁) = refl
assoc-γ (T₀ , T₂ , T₂) (T₁ , T₂ , T₂) = refl
assoc-γ (T₀ , T₂ , T₂) (T₂ , T₀ , T₀) = refl
assoc-γ (T₀ , T₂ , T₂) (T₂ , T₀ , T₁) = refl
assoc-γ (T₀ , T₂ , T₂) (T₂ , T₀ , T₂) = refl
assoc-γ (T₀ , T₂ , T₂) (T₂ , T₁ , T₀) = refl
assoc-γ (T₀ , T₂ , T₂) (T₂ , T₁ , T₁) = refl
assoc-γ (T₀ , T₂ , T₂) (T₂ , T₁ , T₂) = refl
assoc-γ (T₀ , T₂ , T₂) (T₂ , T₂ , T₀) = refl
assoc-γ (T₀ , T₂ , T₂) (T₂ , T₂ , T₁) = refl
assoc-γ (T₀ , T₂ , T₂) (T₂ , T₂ , T₂) = refl
assoc-γ (T₁ , T₀ , T₀) (T₀ , T₀ , T₀) = refl
assoc-γ (T₁ , T₀ , T₀) (T₀ , T₀ , T₁) = refl
assoc-γ (T₁ , T₀ , T₀) (T₀ , T₀ , T₂) = refl
assoc-γ (T₁ , T₀ , T₀) (T₀ , T₁ , T₀) = refl
assoc-γ (T₁ , T₀ , T₀) (T₀ , T₁ , T₁) = refl
assoc-γ (T₁ , T₀ , T₀) (T₀ , T₁ , T₂) = refl
assoc-γ (T₁ , T₀ , T₀) (T₀ , T₂ , T₀) = refl
assoc-γ (T₁ , T₀ , T₀) (T₀ , T₂ , T₁) = refl
assoc-γ (T₁ , T₀ , T₀) (T₀ , T₂ , T₂) = refl
assoc-γ (T₁ , T₀ , T₀) (T₁ , T₀ , T₀) = refl
assoc-γ (T₁ , T₀ , T₀) (T₁ , T₀ , T₁) = refl
assoc-γ (T₁ , T₀ , T₀) (T₁ , T₀ , T₂) = refl
assoc-γ (T₁ , T₀ , T₀) (T₁ , T₁ , T₀) = refl
assoc-γ (T₁ , T₀ , T₀) (T₁ , T₁ , T₁) = refl
assoc-γ (T₁ , T₀ , T₀) (T₁ , T₁ , T₂) = refl
assoc-γ (T₁ , T₀ , T₀) (T₁ , T₂ , T₀) = refl
assoc-γ (T₁ , T₀ , T₀) (T₁ , T₂ , T₁) = refl
assoc-γ (T₁ , T₀ , T₀) (T₁ , T₂ , T₂) = refl
assoc-γ (T₁ , T₀ , T₀) (T₂ , T₀ , T₀) = refl
assoc-γ (T₁ , T₀ , T₀) (T₂ , T₀ , T₁) = refl
assoc-γ (T₁ , T₀ , T₀) (T₂ , T₀ , T₂) = refl
assoc-γ (T₁ , T₀ , T₀) (T₂ , T₁ , T₀) = refl
assoc-γ (T₁ , T₀ , T₀) (T₂ , T₁ , T₁) = refl
assoc-γ (T₁ , T₀ , T₀) (T₂ , T₁ , T₂) = refl
assoc-γ (T₁ , T₀ , T₀) (T₂ , T₂ , T₀) = refl
assoc-γ (T₁ , T₀ , T₀) (T₂ , T₂ , T₁) = refl
assoc-γ (T₁ , T₀ , T₀) (T₂ , T₂ , T₂) = refl
assoc-γ (T₁ , T₀ , T₁) (T₀ , T₀ , T₀) = refl
assoc-γ (T₁ , T₀ , T₁) (T₀ , T₀ , T₁) = refl
assoc-γ (T₁ , T₀ , T₁) (T₀ , T₀ , T₂) = refl
assoc-γ (T₁ , T₀ , T₁) (T₀ , T₁ , T₀) = refl
assoc-γ (T₁ , T₀ , T₁) (T₀ , T₁ , T₁) = refl
assoc-γ (T₁ , T₀ , T₁) (T₀ , T₁ , T₂) = refl
assoc-γ (T₁ , T₀ , T₁) (T₀ , T₂ , T₀) = refl
assoc-γ (T₁ , T₀ , T₁) (T₀ , T₂ , T₁) = refl
assoc-γ (T₁ , T₀ , T₁) (T₀ , T₂ , T₂) = refl
assoc-γ (T₁ , T₀ , T₁) (T₁ , T₀ , T₀) = refl
assoc-γ (T₁ , T₀ , T₁) (T₁ , T₀ , T₁) = refl
assoc-γ (T₁ , T₀ , T₁) (T₁ , T₀ , T₂) = refl
assoc-γ (T₁ , T₀ , T₁) (T₁ , T₁ , T₀) = refl
assoc-γ (T₁ , T₀ , T₁) (T₁ , T₁ , T₁) = refl
assoc-γ (T₁ , T₀ , T₁) (T₁ , T₁ , T₂) = refl
assoc-γ (T₁ , T₀ , T₁) (T₁ , T₂ , T₀) = refl
assoc-γ (T₁ , T₀ , T₁) (T₁ , T₂ , T₁) = refl
assoc-γ (T₁ , T₀ , T₁) (T₁ , T₂ , T₂) = refl
assoc-γ (T₁ , T₀ , T₁) (T₂ , T₀ , T₀) = refl
assoc-γ (T₁ , T₀ , T₁) (T₂ , T₀ , T₁) = refl
assoc-γ (T₁ , T₀ , T₁) (T₂ , T₀ , T₂) = refl
assoc-γ (T₁ , T₀ , T₁) (T₂ , T₁ , T₀) = refl
assoc-γ (T₁ , T₀ , T₁) (T₂ , T₁ , T₁) = refl
assoc-γ (T₁ , T₀ , T₁) (T₂ , T₁ , T₂) = refl
assoc-γ (T₁ , T₀ , T₁) (T₂ , T₂ , T₀) = refl
assoc-γ (T₁ , T₀ , T₁) (T₂ , T₂ , T₁) = refl
assoc-γ (T₁ , T₀ , T₁) (T₂ , T₂ , T₂) = refl
assoc-γ (T₁ , T₀ , T₂) (T₀ , T₀ , T₀) = refl
assoc-γ (T₁ , T₀ , T₂) (T₀ , T₀ , T₁) = refl
assoc-γ (T₁ , T₀ , T₂) (T₀ , T₀ , T₂) = refl
assoc-γ (T₁ , T₀ , T₂) (T₀ , T₁ , T₀) = refl
assoc-γ (T₁ , T₀ , T₂) (T₀ , T₁ , T₁) = refl
assoc-γ (T₁ , T₀ , T₂) (T₀ , T₁ , T₂) = refl
assoc-γ (T₁ , T₀ , T₂) (T₀ , T₂ , T₀) = refl
assoc-γ (T₁ , T₀ , T₂) (T₀ , T₂ , T₁) = refl
assoc-γ (T₁ , T₀ , T₂) (T₀ , T₂ , T₂) = refl
assoc-γ (T₁ , T₀ , T₂) (T₁ , T₀ , T₀) = refl
assoc-γ (T₁ , T₀ , T₂) (T₁ , T₀ , T₁) = refl
assoc-γ (T₁ , T₀ , T₂) (T₁ , T₀ , T₂) = refl
assoc-γ (T₁ , T₀ , T₂) (T₁ , T₁ , T₀) = refl
assoc-γ (T₁ , T₀ , T₂) (T₁ , T₁ , T₁) = refl
assoc-γ (T₁ , T₀ , T₂) (T₁ , T₁ , T₂) = refl
assoc-γ (T₁ , T₀ , T₂) (T₁ , T₂ , T₀) = refl
assoc-γ (T₁ , T₀ , T₂) (T₁ , T₂ , T₁) = refl
assoc-γ (T₁ , T₀ , T₂) (T₁ , T₂ , T₂) = refl
assoc-γ (T₁ , T₀ , T₂) (T₂ , T₀ , T₀) = refl
assoc-γ (T₁ , T₀ , T₂) (T₂ , T₀ , T₁) = refl
assoc-γ (T₁ , T₀ , T₂) (T₂ , T₀ , T₂) = refl
assoc-γ (T₁ , T₀ , T₂) (T₂ , T₁ , T₀) = refl
assoc-γ (T₁ , T₀ , T₂) (T₂ , T₁ , T₁) = refl
assoc-γ (T₁ , T₀ , T₂) (T₂ , T₁ , T₂) = refl
assoc-γ (T₁ , T₀ , T₂) (T₂ , T₂ , T₀) = refl
assoc-γ (T₁ , T₀ , T₂) (T₂ , T₂ , T₁) = refl
assoc-γ (T₁ , T₀ , T₂) (T₂ , T₂ , T₂) = refl
assoc-γ (T₁ , T₁ , T₀) (T₀ , T₀ , T₀) = refl
assoc-γ (T₁ , T₁ , T₀) (T₀ , T₀ , T₁) = refl
assoc-γ (T₁ , T₁ , T₀) (T₀ , T₀ , T₂) = refl
assoc-γ (T₁ , T₁ , T₀) (T₀ , T₁ , T₀) = refl
assoc-γ (T₁ , T₁ , T₀) (T₀ , T₁ , T₁) = refl
assoc-γ (T₁ , T₁ , T₀) (T₀ , T₁ , T₂) = refl
assoc-γ (T₁ , T₁ , T₀) (T₀ , T₂ , T₀) = refl
assoc-γ (T₁ , T₁ , T₀) (T₀ , T₂ , T₁) = refl
assoc-γ (T₁ , T₁ , T₀) (T₀ , T₂ , T₂) = refl
assoc-γ (T₁ , T₁ , T₀) (T₁ , T₀ , T₀) = refl
assoc-γ (T₁ , T₁ , T₀) (T₁ , T₀ , T₁) = refl
assoc-γ (T₁ , T₁ , T₀) (T₁ , T₀ , T₂) = refl
assoc-γ (T₁ , T₁ , T₀) (T₁ , T₁ , T₀) = refl
assoc-γ (T₁ , T₁ , T₀) (T₁ , T₁ , T₁) = refl
assoc-γ (T₁ , T₁ , T₀) (T₁ , T₁ , T₂) = refl
assoc-γ (T₁ , T₁ , T₀) (T₁ , T₂ , T₀) = refl
assoc-γ (T₁ , T₁ , T₀) (T₁ , T₂ , T₁) = refl
assoc-γ (T₁ , T₁ , T₀) (T₁ , T₂ , T₂) = refl
assoc-γ (T₁ , T₁ , T₀) (T₂ , T₀ , T₀) = refl
assoc-γ (T₁ , T₁ , T₀) (T₂ , T₀ , T₁) = refl
assoc-γ (T₁ , T₁ , T₀) (T₂ , T₀ , T₂) = refl
assoc-γ (T₁ , T₁ , T₀) (T₂ , T₁ , T₀) = refl
assoc-γ (T₁ , T₁ , T₀) (T₂ , T₁ , T₁) = refl
assoc-γ (T₁ , T₁ , T₀) (T₂ , T₁ , T₂) = refl
assoc-γ (T₁ , T₁ , T₀) (T₂ , T₂ , T₀) = refl
assoc-γ (T₁ , T₁ , T₀) (T₂ , T₂ , T₁) = refl
assoc-γ (T₁ , T₁ , T₀) (T₂ , T₂ , T₂) = refl
assoc-γ (T₁ , T₁ , T₁) (T₀ , T₀ , T₀) = refl
assoc-γ (T₁ , T₁ , T₁) (T₀ , T₀ , T₁) = refl
assoc-γ (T₁ , T₁ , T₁) (T₀ , T₀ , T₂) = refl
assoc-γ (T₁ , T₁ , T₁) (T₀ , T₁ , T₀) = refl
assoc-γ (T₁ , T₁ , T₁) (T₀ , T₁ , T₁) = refl
assoc-γ (T₁ , T₁ , T₁) (T₀ , T₁ , T₂) = refl
assoc-γ (T₁ , T₁ , T₁) (T₀ , T₂ , T₀) = refl
assoc-γ (T₁ , T₁ , T₁) (T₀ , T₂ , T₁) = refl
assoc-γ (T₁ , T₁ , T₁) (T₀ , T₂ , T₂) = refl
assoc-γ (T₁ , T₁ , T₁) (T₁ , T₀ , T₀) = refl
assoc-γ (T₁ , T₁ , T₁) (T₁ , T₀ , T₁) = refl
assoc-γ (T₁ , T₁ , T₁) (T₁ , T₀ , T₂) = refl
assoc-γ (T₁ , T₁ , T₁) (T₁ , T₁ , T₀) = refl
assoc-γ (T₁ , T₁ , T₁) (T₁ , T₁ , T₁) = refl
assoc-γ (T₁ , T₁ , T₁) (T₁ , T₁ , T₂) = refl
assoc-γ (T₁ , T₁ , T₁) (T₁ , T₂ , T₀) = refl
assoc-γ (T₁ , T₁ , T₁) (T₁ , T₂ , T₁) = refl
assoc-γ (T₁ , T₁ , T₁) (T₁ , T₂ , T₂) = refl
assoc-γ (T₁ , T₁ , T₁) (T₂ , T₀ , T₀) = refl
assoc-γ (T₁ , T₁ , T₁) (T₂ , T₀ , T₁) = refl
assoc-γ (T₁ , T₁ , T₁) (T₂ , T₀ , T₂) = refl
assoc-γ (T₁ , T₁ , T₁) (T₂ , T₁ , T₀) = refl
assoc-γ (T₁ , T₁ , T₁) (T₂ , T₁ , T₁) = refl
assoc-γ (T₁ , T₁ , T₁) (T₂ , T₁ , T₂) = refl
assoc-γ (T₁ , T₁ , T₁) (T₂ , T₂ , T₀) = refl
assoc-γ (T₁ , T₁ , T₁) (T₂ , T₂ , T₁) = refl
assoc-γ (T₁ , T₁ , T₁) (T₂ , T₂ , T₂) = refl
assoc-γ (T₁ , T₁ , T₂) (T₀ , T₀ , T₀) = refl
assoc-γ (T₁ , T₁ , T₂) (T₀ , T₀ , T₁) = refl
assoc-γ (T₁ , T₁ , T₂) (T₀ , T₀ , T₂) = refl
assoc-γ (T₁ , T₁ , T₂) (T₀ , T₁ , T₀) = refl
assoc-γ (T₁ , T₁ , T₂) (T₀ , T₁ , T₁) = refl
assoc-γ (T₁ , T₁ , T₂) (T₀ , T₁ , T₂) = refl
assoc-γ (T₁ , T₁ , T₂) (T₀ , T₂ , T₀) = refl
assoc-γ (T₁ , T₁ , T₂) (T₀ , T₂ , T₁) = refl
assoc-γ (T₁ , T₁ , T₂) (T₀ , T₂ , T₂) = refl
assoc-γ (T₁ , T₁ , T₂) (T₁ , T₀ , T₀) = refl
assoc-γ (T₁ , T₁ , T₂) (T₁ , T₀ , T₁) = refl
assoc-γ (T₁ , T₁ , T₂) (T₁ , T₀ , T₂) = refl
assoc-γ (T₁ , T₁ , T₂) (T₁ , T₁ , T₀) = refl
assoc-γ (T₁ , T₁ , T₂) (T₁ , T₁ , T₁) = refl
assoc-γ (T₁ , T₁ , T₂) (T₁ , T₁ , T₂) = refl
assoc-γ (T₁ , T₁ , T₂) (T₁ , T₂ , T₀) = refl
assoc-γ (T₁ , T₁ , T₂) (T₁ , T₂ , T₁) = refl
assoc-γ (T₁ , T₁ , T₂) (T₁ , T₂ , T₂) = refl
assoc-γ (T₁ , T₁ , T₂) (T₂ , T₀ , T₀) = refl
assoc-γ (T₁ , T₁ , T₂) (T₂ , T₀ , T₁) = refl
assoc-γ (T₁ , T₁ , T₂) (T₂ , T₀ , T₂) = refl
assoc-γ (T₁ , T₁ , T₂) (T₂ , T₁ , T₀) = refl
assoc-γ (T₁ , T₁ , T₂) (T₂ , T₁ , T₁) = refl
assoc-γ (T₁ , T₁ , T₂) (T₂ , T₁ , T₂) = refl
assoc-γ (T₁ , T₁ , T₂) (T₂ , T₂ , T₀) = refl
assoc-γ (T₁ , T₁ , T₂) (T₂ , T₂ , T₁) = refl
assoc-γ (T₁ , T₁ , T₂) (T₂ , T₂ , T₂) = refl
assoc-γ (T₁ , T₂ , T₀) (T₀ , T₀ , T₀) = refl
assoc-γ (T₁ , T₂ , T₀) (T₀ , T₀ , T₁) = refl
assoc-γ (T₁ , T₂ , T₀) (T₀ , T₀ , T₂) = refl
assoc-γ (T₁ , T₂ , T₀) (T₀ , T₁ , T₀) = refl
assoc-γ (T₁ , T₂ , T₀) (T₀ , T₁ , T₁) = refl
assoc-γ (T₁ , T₂ , T₀) (T₀ , T₁ , T₂) = refl
assoc-γ (T₁ , T₂ , T₀) (T₀ , T₂ , T₀) = refl
assoc-γ (T₁ , T₂ , T₀) (T₀ , T₂ , T₁) = refl
assoc-γ (T₁ , T₂ , T₀) (T₀ , T₂ , T₂) = refl
assoc-γ (T₁ , T₂ , T₀) (T₁ , T₀ , T₀) = refl
assoc-γ (T₁ , T₂ , T₀) (T₁ , T₀ , T₁) = refl
assoc-γ (T₁ , T₂ , T₀) (T₁ , T₀ , T₂) = refl
assoc-γ (T₁ , T₂ , T₀) (T₁ , T₁ , T₀) = refl
assoc-γ (T₁ , T₂ , T₀) (T₁ , T₁ , T₁) = refl
assoc-γ (T₁ , T₂ , T₀) (T₁ , T₁ , T₂) = refl
assoc-γ (T₁ , T₂ , T₀) (T₁ , T₂ , T₀) = refl
assoc-γ (T₁ , T₂ , T₀) (T₁ , T₂ , T₁) = refl
assoc-γ (T₁ , T₂ , T₀) (T₁ , T₂ , T₂) = refl
assoc-γ (T₁ , T₂ , T₀) (T₂ , T₀ , T₀) = refl
assoc-γ (T₁ , T₂ , T₀) (T₂ , T₀ , T₁) = refl
assoc-γ (T₁ , T₂ , T₀) (T₂ , T₀ , T₂) = refl
assoc-γ (T₁ , T₂ , T₀) (T₂ , T₁ , T₀) = refl
assoc-γ (T₁ , T₂ , T₀) (T₂ , T₁ , T₁) = refl
assoc-γ (T₁ , T₂ , T₀) (T₂ , T₁ , T₂) = refl
assoc-γ (T₁ , T₂ , T₀) (T₂ , T₂ , T₀) = refl
assoc-γ (T₁ , T₂ , T₀) (T₂ , T₂ , T₁) = refl
assoc-γ (T₁ , T₂ , T₀) (T₂ , T₂ , T₂) = refl
assoc-γ (T₁ , T₂ , T₁) (T₀ , T₀ , T₀) = refl
assoc-γ (T₁ , T₂ , T₁) (T₀ , T₀ , T₁) = refl
assoc-γ (T₁ , T₂ , T₁) (T₀ , T₀ , T₂) = refl
assoc-γ (T₁ , T₂ , T₁) (T₀ , T₁ , T₀) = refl
assoc-γ (T₁ , T₂ , T₁) (T₀ , T₁ , T₁) = refl
assoc-γ (T₁ , T₂ , T₁) (T₀ , T₁ , T₂) = refl
assoc-γ (T₁ , T₂ , T₁) (T₀ , T₂ , T₀) = refl
assoc-γ (T₁ , T₂ , T₁) (T₀ , T₂ , T₁) = refl
assoc-γ (T₁ , T₂ , T₁) (T₀ , T₂ , T₂) = refl
assoc-γ (T₁ , T₂ , T₁) (T₁ , T₀ , T₀) = refl
assoc-γ (T₁ , T₂ , T₁) (T₁ , T₀ , T₁) = refl
assoc-γ (T₁ , T₂ , T₁) (T₁ , T₀ , T₂) = refl
assoc-γ (T₁ , T₂ , T₁) (T₁ , T₁ , T₀) = refl
assoc-γ (T₁ , T₂ , T₁) (T₁ , T₁ , T₁) = refl
assoc-γ (T₁ , T₂ , T₁) (T₁ , T₁ , T₂) = refl
assoc-γ (T₁ , T₂ , T₁) (T₁ , T₂ , T₀) = refl
assoc-γ (T₁ , T₂ , T₁) (T₁ , T₂ , T₁) = refl
assoc-γ (T₁ , T₂ , T₁) (T₁ , T₂ , T₂) = refl
assoc-γ (T₁ , T₂ , T₁) (T₂ , T₀ , T₀) = refl
assoc-γ (T₁ , T₂ , T₁) (T₂ , T₀ , T₁) = refl
assoc-γ (T₁ , T₂ , T₁) (T₂ , T₀ , T₂) = refl
assoc-γ (T₁ , T₂ , T₁) (T₂ , T₁ , T₀) = refl
assoc-γ (T₁ , T₂ , T₁) (T₂ , T₁ , T₁) = refl
assoc-γ (T₁ , T₂ , T₁) (T₂ , T₁ , T₂) = refl
assoc-γ (T₁ , T₂ , T₁) (T₂ , T₂ , T₀) = refl
assoc-γ (T₁ , T₂ , T₁) (T₂ , T₂ , T₁) = refl
assoc-γ (T₁ , T₂ , T₁) (T₂ , T₂ , T₂) = refl
assoc-γ (T₁ , T₂ , T₂) (T₀ , T₀ , T₀) = refl
assoc-γ (T₁ , T₂ , T₂) (T₀ , T₀ , T₁) = refl
assoc-γ (T₁ , T₂ , T₂) (T₀ , T₀ , T₂) = refl
assoc-γ (T₁ , T₂ , T₂) (T₀ , T₁ , T₀) = refl
assoc-γ (T₁ , T₂ , T₂) (T₀ , T₁ , T₁) = refl
assoc-γ (T₁ , T₂ , T₂) (T₀ , T₁ , T₂) = refl
assoc-γ (T₁ , T₂ , T₂) (T₀ , T₂ , T₀) = refl
assoc-γ (T₁ , T₂ , T₂) (T₀ , T₂ , T₁) = refl
assoc-γ (T₁ , T₂ , T₂) (T₀ , T₂ , T₂) = refl
assoc-γ (T₁ , T₂ , T₂) (T₁ , T₀ , T₀) = refl
assoc-γ (T₁ , T₂ , T₂) (T₁ , T₀ , T₁) = refl
assoc-γ (T₁ , T₂ , T₂) (T₁ , T₀ , T₂) = refl
assoc-γ (T₁ , T₂ , T₂) (T₁ , T₁ , T₀) = refl
assoc-γ (T₁ , T₂ , T₂) (T₁ , T₁ , T₁) = refl
assoc-γ (T₁ , T₂ , T₂) (T₁ , T₁ , T₂) = refl
assoc-γ (T₁ , T₂ , T₂) (T₁ , T₂ , T₀) = refl
assoc-γ (T₁ , T₂ , T₂) (T₁ , T₂ , T₁) = refl
assoc-γ (T₁ , T₂ , T₂) (T₁ , T₂ , T₂) = refl
assoc-γ (T₁ , T₂ , T₂) (T₂ , T₀ , T₀) = refl
assoc-γ (T₁ , T₂ , T₂) (T₂ , T₀ , T₁) = refl
assoc-γ (T₁ , T₂ , T₂) (T₂ , T₀ , T₂) = refl
assoc-γ (T₁ , T₂ , T₂) (T₂ , T₁ , T₀) = refl
assoc-γ (T₁ , T₂ , T₂) (T₂ , T₁ , T₁) = refl
assoc-γ (T₁ , T₂ , T₂) (T₂ , T₁ , T₂) = refl
assoc-γ (T₁ , T₂ , T₂) (T₂ , T₂ , T₀) = refl
assoc-γ (T₁ , T₂ , T₂) (T₂ , T₂ , T₁) = refl
assoc-γ (T₁ , T₂ , T₂) (T₂ , T₂ , T₂) = refl
assoc-γ (T₂ , T₀ , T₀) (T₀ , T₀ , T₀) = refl
assoc-γ (T₂ , T₀ , T₀) (T₀ , T₀ , T₁) = refl
assoc-γ (T₂ , T₀ , T₀) (T₀ , T₀ , T₂) = refl
assoc-γ (T₂ , T₀ , T₀) (T₀ , T₁ , T₀) = refl
assoc-γ (T₂ , T₀ , T₀) (T₀ , T₁ , T₁) = refl
assoc-γ (T₂ , T₀ , T₀) (T₀ , T₁ , T₂) = refl
assoc-γ (T₂ , T₀ , T₀) (T₀ , T₂ , T₀) = refl
assoc-γ (T₂ , T₀ , T₀) (T₀ , T₂ , T₁) = refl
assoc-γ (T₂ , T₀ , T₀) (T₀ , T₂ , T₂) = refl
assoc-γ (T₂ , T₀ , T₀) (T₁ , T₀ , T₀) = refl
assoc-γ (T₂ , T₀ , T₀) (T₁ , T₀ , T₁) = refl
assoc-γ (T₂ , T₀ , T₀) (T₁ , T₀ , T₂) = refl
assoc-γ (T₂ , T₀ , T₀) (T₁ , T₁ , T₀) = refl
assoc-γ (T₂ , T₀ , T₀) (T₁ , T₁ , T₁) = refl
assoc-γ (T₂ , T₀ , T₀) (T₁ , T₁ , T₂) = refl
assoc-γ (T₂ , T₀ , T₀) (T₁ , T₂ , T₀) = refl
assoc-γ (T₂ , T₀ , T₀) (T₁ , T₂ , T₁) = refl
assoc-γ (T₂ , T₀ , T₀) (T₁ , T₂ , T₂) = refl
assoc-γ (T₂ , T₀ , T₀) (T₂ , T₀ , T₀) = refl
assoc-γ (T₂ , T₀ , T₀) (T₂ , T₀ , T₁) = refl
assoc-γ (T₂ , T₀ , T₀) (T₂ , T₀ , T₂) = refl
assoc-γ (T₂ , T₀ , T₀) (T₂ , T₁ , T₀) = refl
assoc-γ (T₂ , T₀ , T₀) (T₂ , T₁ , T₁) = refl
assoc-γ (T₂ , T₀ , T₀) (T₂ , T₁ , T₂) = refl
assoc-γ (T₂ , T₀ , T₀) (T₂ , T₂ , T₀) = refl
assoc-γ (T₂ , T₀ , T₀) (T₂ , T₂ , T₁) = refl
assoc-γ (T₂ , T₀ , T₀) (T₂ , T₂ , T₂) = refl
assoc-γ (T₂ , T₀ , T₁) (T₀ , T₀ , T₀) = refl
assoc-γ (T₂ , T₀ , T₁) (T₀ , T₀ , T₁) = refl
assoc-γ (T₂ , T₀ , T₁) (T₀ , T₀ , T₂) = refl
assoc-γ (T₂ , T₀ , T₁) (T₀ , T₁ , T₀) = refl
assoc-γ (T₂ , T₀ , T₁) (T₀ , T₁ , T₁) = refl
assoc-γ (T₂ , T₀ , T₁) (T₀ , T₁ , T₂) = refl
assoc-γ (T₂ , T₀ , T₁) (T₀ , T₂ , T₀) = refl
assoc-γ (T₂ , T₀ , T₁) (T₀ , T₂ , T₁) = refl
assoc-γ (T₂ , T₀ , T₁) (T₀ , T₂ , T₂) = refl
assoc-γ (T₂ , T₀ , T₁) (T₁ , T₀ , T₀) = refl
assoc-γ (T₂ , T₀ , T₁) (T₁ , T₀ , T₁) = refl
assoc-γ (T₂ , T₀ , T₁) (T₁ , T₀ , T₂) = refl
assoc-γ (T₂ , T₀ , T₁) (T₁ , T₁ , T₀) = refl
assoc-γ (T₂ , T₀ , T₁) (T₁ , T₁ , T₁) = refl
assoc-γ (T₂ , T₀ , T₁) (T₁ , T₁ , T₂) = refl
assoc-γ (T₂ , T₀ , T₁) (T₁ , T₂ , T₀) = refl
assoc-γ (T₂ , T₀ , T₁) (T₁ , T₂ , T₁) = refl
assoc-γ (T₂ , T₀ , T₁) (T₁ , T₂ , T₂) = refl
assoc-γ (T₂ , T₀ , T₁) (T₂ , T₀ , T₀) = refl
assoc-γ (T₂ , T₀ , T₁) (T₂ , T₀ , T₁) = refl
assoc-γ (T₂ , T₀ , T₁) (T₂ , T₀ , T₂) = refl
assoc-γ (T₂ , T₀ , T₁) (T₂ , T₁ , T₀) = refl
assoc-γ (T₂ , T₀ , T₁) (T₂ , T₁ , T₁) = refl
assoc-γ (T₂ , T₀ , T₁) (T₂ , T₁ , T₂) = refl
assoc-γ (T₂ , T₀ , T₁) (T₂ , T₂ , T₀) = refl
assoc-γ (T₂ , T₀ , T₁) (T₂ , T₂ , T₁) = refl
assoc-γ (T₂ , T₀ , T₁) (T₂ , T₂ , T₂) = refl
assoc-γ (T₂ , T₀ , T₂) (T₀ , T₀ , T₀) = refl
assoc-γ (T₂ , T₀ , T₂) (T₀ , T₀ , T₁) = refl
assoc-γ (T₂ , T₀ , T₂) (T₀ , T₀ , T₂) = refl
assoc-γ (T₂ , T₀ , T₂) (T₀ , T₁ , T₀) = refl
assoc-γ (T₂ , T₀ , T₂) (T₀ , T₁ , T₁) = refl
assoc-γ (T₂ , T₀ , T₂) (T₀ , T₁ , T₂) = refl
assoc-γ (T₂ , T₀ , T₂) (T₀ , T₂ , T₀) = refl
assoc-γ (T₂ , T₀ , T₂) (T₀ , T₂ , T₁) = refl
assoc-γ (T₂ , T₀ , T₂) (T₀ , T₂ , T₂) = refl
assoc-γ (T₂ , T₀ , T₂) (T₁ , T₀ , T₀) = refl
assoc-γ (T₂ , T₀ , T₂) (T₁ , T₀ , T₁) = refl
assoc-γ (T₂ , T₀ , T₂) (T₁ , T₀ , T₂) = refl
assoc-γ (T₂ , T₀ , T₂) (T₁ , T₁ , T₀) = refl
assoc-γ (T₂ , T₀ , T₂) (T₁ , T₁ , T₁) = refl
assoc-γ (T₂ , T₀ , T₂) (T₁ , T₁ , T₂) = refl
assoc-γ (T₂ , T₀ , T₂) (T₁ , T₂ , T₀) = refl
assoc-γ (T₂ , T₀ , T₂) (T₁ , T₂ , T₁) = refl
assoc-γ (T₂ , T₀ , T₂) (T₁ , T₂ , T₂) = refl
assoc-γ (T₂ , T₀ , T₂) (T₂ , T₀ , T₀) = refl
assoc-γ (T₂ , T₀ , T₂) (T₂ , T₀ , T₁) = refl
assoc-γ (T₂ , T₀ , T₂) (T₂ , T₀ , T₂) = refl
assoc-γ (T₂ , T₀ , T₂) (T₂ , T₁ , T₀) = refl
assoc-γ (T₂ , T₀ , T₂) (T₂ , T₁ , T₁) = refl
assoc-γ (T₂ , T₀ , T₂) (T₂ , T₁ , T₂) = refl
assoc-γ (T₂ , T₀ , T₂) (T₂ , T₂ , T₀) = refl
assoc-γ (T₂ , T₀ , T₂) (T₂ , T₂ , T₁) = refl
assoc-γ (T₂ , T₀ , T₂) (T₂ , T₂ , T₂) = refl
assoc-γ (T₂ , T₁ , T₀) (T₀ , T₀ , T₀) = refl
assoc-γ (T₂ , T₁ , T₀) (T₀ , T₀ , T₁) = refl
assoc-γ (T₂ , T₁ , T₀) (T₀ , T₀ , T₂) = refl
assoc-γ (T₂ , T₁ , T₀) (T₀ , T₁ , T₀) = refl
assoc-γ (T₂ , T₁ , T₀) (T₀ , T₁ , T₁) = refl
assoc-γ (T₂ , T₁ , T₀) (T₀ , T₁ , T₂) = refl
assoc-γ (T₂ , T₁ , T₀) (T₀ , T₂ , T₀) = refl
assoc-γ (T₂ , T₁ , T₀) (T₀ , T₂ , T₁) = refl
assoc-γ (T₂ , T₁ , T₀) (T₀ , T₂ , T₂) = refl
assoc-γ (T₂ , T₁ , T₀) (T₁ , T₀ , T₀) = refl
assoc-γ (T₂ , T₁ , T₀) (T₁ , T₀ , T₁) = refl
assoc-γ (T₂ , T₁ , T₀) (T₁ , T₀ , T₂) = refl
assoc-γ (T₂ , T₁ , T₀) (T₁ , T₁ , T₀) = refl
assoc-γ (T₂ , T₁ , T₀) (T₁ , T₁ , T₁) = refl
assoc-γ (T₂ , T₁ , T₀) (T₁ , T₁ , T₂) = refl
assoc-γ (T₂ , T₁ , T₀) (T₁ , T₂ , T₀) = refl
assoc-γ (T₂ , T₁ , T₀) (T₁ , T₂ , T₁) = refl
assoc-γ (T₂ , T₁ , T₀) (T₁ , T₂ , T₂) = refl
assoc-γ (T₂ , T₁ , T₀) (T₂ , T₀ , T₀) = refl
assoc-γ (T₂ , T₁ , T₀) (T₂ , T₀ , T₁) = refl
assoc-γ (T₂ , T₁ , T₀) (T₂ , T₀ , T₂) = refl
assoc-γ (T₂ , T₁ , T₀) (T₂ , T₁ , T₀) = refl
assoc-γ (T₂ , T₁ , T₀) (T₂ , T₁ , T₁) = refl
assoc-γ (T₂ , T₁ , T₀) (T₂ , T₁ , T₂) = refl
assoc-γ (T₂ , T₁ , T₀) (T₂ , T₂ , T₀) = refl
assoc-γ (T₂ , T₁ , T₀) (T₂ , T₂ , T₁) = refl
assoc-γ (T₂ , T₁ , T₀) (T₂ , T₂ , T₂) = refl
assoc-γ (T₂ , T₁ , T₁) (T₀ , T₀ , T₀) = refl
assoc-γ (T₂ , T₁ , T₁) (T₀ , T₀ , T₁) = refl
assoc-γ (T₂ , T₁ , T₁) (T₀ , T₀ , T₂) = refl
assoc-γ (T₂ , T₁ , T₁) (T₀ , T₁ , T₀) = refl
assoc-γ (T₂ , T₁ , T₁) (T₀ , T₁ , T₁) = refl
assoc-γ (T₂ , T₁ , T₁) (T₀ , T₁ , T₂) = refl
assoc-γ (T₂ , T₁ , T₁) (T₀ , T₂ , T₀) = refl
assoc-γ (T₂ , T₁ , T₁) (T₀ , T₂ , T₁) = refl
assoc-γ (T₂ , T₁ , T₁) (T₀ , T₂ , T₂) = refl
assoc-γ (T₂ , T₁ , T₁) (T₁ , T₀ , T₀) = refl
assoc-γ (T₂ , T₁ , T₁) (T₁ , T₀ , T₁) = refl
assoc-γ (T₂ , T₁ , T₁) (T₁ , T₀ , T₂) = refl
assoc-γ (T₂ , T₁ , T₁) (T₁ , T₁ , T₀) = refl
assoc-γ (T₂ , T₁ , T₁) (T₁ , T₁ , T₁) = refl
assoc-γ (T₂ , T₁ , T₁) (T₁ , T₁ , T₂) = refl
assoc-γ (T₂ , T₁ , T₁) (T₁ , T₂ , T₀) = refl
assoc-γ (T₂ , T₁ , T₁) (T₁ , T₂ , T₁) = refl
assoc-γ (T₂ , T₁ , T₁) (T₁ , T₂ , T₂) = refl
assoc-γ (T₂ , T₁ , T₁) (T₂ , T₀ , T₀) = refl
assoc-γ (T₂ , T₁ , T₁) (T₂ , T₀ , T₁) = refl
assoc-γ (T₂ , T₁ , T₁) (T₂ , T₀ , T₂) = refl
assoc-γ (T₂ , T₁ , T₁) (T₂ , T₁ , T₀) = refl
assoc-γ (T₂ , T₁ , T₁) (T₂ , T₁ , T₁) = refl
assoc-γ (T₂ , T₁ , T₁) (T₂ , T₁ , T₂) = refl
assoc-γ (T₂ , T₁ , T₁) (T₂ , T₂ , T₀) = refl
assoc-γ (T₂ , T₁ , T₁) (T₂ , T₂ , T₁) = refl
assoc-γ (T₂ , T₁ , T₁) (T₂ , T₂ , T₂) = refl
assoc-γ (T₂ , T₁ , T₂) (T₀ , T₀ , T₀) = refl
assoc-γ (T₂ , T₁ , T₂) (T₀ , T₀ , T₁) = refl
assoc-γ (T₂ , T₁ , T₂) (T₀ , T₀ , T₂) = refl
assoc-γ (T₂ , T₁ , T₂) (T₀ , T₁ , T₀) = refl
assoc-γ (T₂ , T₁ , T₂) (T₀ , T₁ , T₁) = refl
assoc-γ (T₂ , T₁ , T₂) (T₀ , T₁ , T₂) = refl
assoc-γ (T₂ , T₁ , T₂) (T₀ , T₂ , T₀) = refl
assoc-γ (T₂ , T₁ , T₂) (T₀ , T₂ , T₁) = refl
assoc-γ (T₂ , T₁ , T₂) (T₀ , T₂ , T₂) = refl
assoc-γ (T₂ , T₁ , T₂) (T₁ , T₀ , T₀) = refl
assoc-γ (T₂ , T₁ , T₂) (T₁ , T₀ , T₁) = refl
assoc-γ (T₂ , T₁ , T₂) (T₁ , T₀ , T₂) = refl
assoc-γ (T₂ , T₁ , T₂) (T₁ , T₁ , T₀) = refl
assoc-γ (T₂ , T₁ , T₂) (T₁ , T₁ , T₁) = refl
assoc-γ (T₂ , T₁ , T₂) (T₁ , T₁ , T₂) = refl
assoc-γ (T₂ , T₁ , T₂) (T₁ , T₂ , T₀) = refl
assoc-γ (T₂ , T₁ , T₂) (T₁ , T₂ , T₁) = refl
assoc-γ (T₂ , T₁ , T₂) (T₁ , T₂ , T₂) = refl
assoc-γ (T₂ , T₁ , T₂) (T₂ , T₀ , T₀) = refl
assoc-γ (T₂ , T₁ , T₂) (T₂ , T₀ , T₁) = refl
assoc-γ (T₂ , T₁ , T₂) (T₂ , T₀ , T₂) = refl
assoc-γ (T₂ , T₁ , T₂) (T₂ , T₁ , T₀) = refl
assoc-γ (T₂ , T₁ , T₂) (T₂ , T₁ , T₁) = refl
assoc-γ (T₂ , T₁ , T₂) (T₂ , T₁ , T₂) = refl
assoc-γ (T₂ , T₁ , T₂) (T₂ , T₂ , T₀) = refl
assoc-γ (T₂ , T₁ , T₂) (T₂ , T₂ , T₁) = refl
assoc-γ (T₂ , T₁ , T₂) (T₂ , T₂ , T₂) = refl
assoc-γ (T₂ , T₂ , T₀) (T₀ , T₀ , T₀) = refl
assoc-γ (T₂ , T₂ , T₀) (T₀ , T₀ , T₁) = refl
assoc-γ (T₂ , T₂ , T₀) (T₀ , T₀ , T₂) = refl
assoc-γ (T₂ , T₂ , T₀) (T₀ , T₁ , T₀) = refl
assoc-γ (T₂ , T₂ , T₀) (T₀ , T₁ , T₁) = refl
assoc-γ (T₂ , T₂ , T₀) (T₀ , T₁ , T₂) = refl
assoc-γ (T₂ , T₂ , T₀) (T₀ , T₂ , T₀) = refl
assoc-γ (T₂ , T₂ , T₀) (T₀ , T₂ , T₁) = refl
assoc-γ (T₂ , T₂ , T₀) (T₀ , T₂ , T₂) = refl
assoc-γ (T₂ , T₂ , T₀) (T₁ , T₀ , T₀) = refl
assoc-γ (T₂ , T₂ , T₀) (T₁ , T₀ , T₁) = refl
assoc-γ (T₂ , T₂ , T₀) (T₁ , T₀ , T₂) = refl
assoc-γ (T₂ , T₂ , T₀) (T₁ , T₁ , T₀) = refl
assoc-γ (T₂ , T₂ , T₀) (T₁ , T₁ , T₁) = refl
assoc-γ (T₂ , T₂ , T₀) (T₁ , T₁ , T₂) = refl
assoc-γ (T₂ , T₂ , T₀) (T₁ , T₂ , T₀) = refl
assoc-γ (T₂ , T₂ , T₀) (T₁ , T₂ , T₁) = refl
assoc-γ (T₂ , T₂ , T₀) (T₁ , T₂ , T₂) = refl
assoc-γ (T₂ , T₂ , T₀) (T₂ , T₀ , T₀) = refl
assoc-γ (T₂ , T₂ , T₀) (T₂ , T₀ , T₁) = refl
assoc-γ (T₂ , T₂ , T₀) (T₂ , T₀ , T₂) = refl
assoc-γ (T₂ , T₂ , T₀) (T₂ , T₁ , T₀) = refl
assoc-γ (T₂ , T₂ , T₀) (T₂ , T₁ , T₁) = refl
assoc-γ (T₂ , T₂ , T₀) (T₂ , T₁ , T₂) = refl
assoc-γ (T₂ , T₂ , T₀) (T₂ , T₂ , T₀) = refl
assoc-γ (T₂ , T₂ , T₀) (T₂ , T₂ , T₁) = refl
assoc-γ (T₂ , T₂ , T₀) (T₂ , T₂ , T₂) = refl
assoc-γ (T₂ , T₂ , T₁) (T₀ , T₀ , T₀) = refl
assoc-γ (T₂ , T₂ , T₁) (T₀ , T₀ , T₁) = refl
assoc-γ (T₂ , T₂ , T₁) (T₀ , T₀ , T₂) = refl
assoc-γ (T₂ , T₂ , T₁) (T₀ , T₁ , T₀) = refl
assoc-γ (T₂ , T₂ , T₁) (T₀ , T₁ , T₁) = refl
assoc-γ (T₂ , T₂ , T₁) (T₀ , T₁ , T₂) = refl
assoc-γ (T₂ , T₂ , T₁) (T₀ , T₂ , T₀) = refl
assoc-γ (T₂ , T₂ , T₁) (T₀ , T₂ , T₁) = refl
assoc-γ (T₂ , T₂ , T₁) (T₀ , T₂ , T₂) = refl
assoc-γ (T₂ , T₂ , T₁) (T₁ , T₀ , T₀) = refl
assoc-γ (T₂ , T₂ , T₁) (T₁ , T₀ , T₁) = refl
assoc-γ (T₂ , T₂ , T₁) (T₁ , T₀ , T₂) = refl
assoc-γ (T₂ , T₂ , T₁) (T₁ , T₁ , T₀) = refl
assoc-γ (T₂ , T₂ , T₁) (T₁ , T₁ , T₁) = refl
assoc-γ (T₂ , T₂ , T₁) (T₁ , T₁ , T₂) = refl
assoc-γ (T₂ , T₂ , T₁) (T₁ , T₂ , T₀) = refl
assoc-γ (T₂ , T₂ , T₁) (T₁ , T₂ , T₁) = refl
assoc-γ (T₂ , T₂ , T₁) (T₁ , T₂ , T₂) = refl
assoc-γ (T₂ , T₂ , T₁) (T₂ , T₀ , T₀) = refl
assoc-γ (T₂ , T₂ , T₁) (T₂ , T₀ , T₁) = refl
assoc-γ (T₂ , T₂ , T₁) (T₂ , T₀ , T₂) = refl
assoc-γ (T₂ , T₂ , T₁) (T₂ , T₁ , T₀) = refl
assoc-γ (T₂ , T₂ , T₁) (T₂ , T₁ , T₁) = refl
assoc-γ (T₂ , T₂ , T₁) (T₂ , T₁ , T₂) = refl
assoc-γ (T₂ , T₂ , T₁) (T₂ , T₂ , T₀) = refl
assoc-γ (T₂ , T₂ , T₁) (T₂ , T₂ , T₁) = refl
assoc-γ (T₂ , T₂ , T₁) (T₂ , T₂ , T₂) = refl
assoc-γ (T₂ , T₂ , T₂) (T₀ , T₀ , T₀) = refl
assoc-γ (T₂ , T₂ , T₂) (T₀ , T₀ , T₁) = refl
assoc-γ (T₂ , T₂ , T₂) (T₀ , T₀ , T₂) = refl
assoc-γ (T₂ , T₂ , T₂) (T₀ , T₁ , T₀) = refl
assoc-γ (T₂ , T₂ , T₂) (T₀ , T₁ , T₁) = refl
assoc-γ (T₂ , T₂ , T₂) (T₀ , T₁ , T₂) = refl
assoc-γ (T₂ , T₂ , T₂) (T₀ , T₂ , T₀) = refl
assoc-γ (T₂ , T₂ , T₂) (T₀ , T₂ , T₁) = refl
assoc-γ (T₂ , T₂ , T₂) (T₀ , T₂ , T₂) = refl
assoc-γ (T₂ , T₂ , T₂) (T₁ , T₀ , T₀) = refl
assoc-γ (T₂ , T₂ , T₂) (T₁ , T₀ , T₁) = refl
assoc-γ (T₂ , T₂ , T₂) (T₁ , T₀ , T₂) = refl
assoc-γ (T₂ , T₂ , T₂) (T₁ , T₁ , T₀) = refl
assoc-γ (T₂ , T₂ , T₂) (T₁ , T₁ , T₁) = refl
assoc-γ (T₂ , T₂ , T₂) (T₁ , T₁ , T₂) = refl
assoc-γ (T₂ , T₂ , T₂) (T₁ , T₂ , T₀) = refl
assoc-γ (T₂ , T₂ , T₂) (T₁ , T₂ , T₁) = refl
assoc-γ (T₂ , T₂ , T₂) (T₁ , T₂ , T₂) = refl
assoc-γ (T₂ , T₂ , T₂) (T₂ , T₀ , T₀) = refl
assoc-γ (T₂ , T₂ , T₂) (T₂ , T₀ , T₁) = refl
assoc-γ (T₂ , T₂ , T₂) (T₂ , T₀ , T₂) = refl
assoc-γ (T₂ , T₂ , T₂) (T₂ , T₁ , T₀) = refl
assoc-γ (T₂ , T₂ , T₂) (T₂ , T₁ , T₁) = refl
assoc-γ (T₂ , T₂ , T₂) (T₂ , T₁ , T₂) = refl
assoc-γ (T₂ , T₂ , T₂) (T₂ , T₂ , T₀) = refl
assoc-γ (T₂ , T₂ , T₂) (T₂ , T₂ , T₁) = refl
assoc-γ (T₂ , T₂ , T₂) (T₂ , T₂ , T₂) = refl

-- γ 左分配: γ·(x+y) = γ·x + γ·y
distribˡ-γ : ∀ x y → γ *₉ (x +₉ y) ≡ (γ *₉ x) +₉ (γ *₉ y)
distribˡ-γ (T₀ , T₀ , T₀) (T₀ , T₀ , T₀) = refl
distribˡ-γ (T₀ , T₀ , T₀) (T₀ , T₀ , T₁) = refl
distribˡ-γ (T₀ , T₀ , T₀) (T₀ , T₀ , T₂) = refl
distribˡ-γ (T₀ , T₀ , T₀) (T₀ , T₁ , T₀) = refl
distribˡ-γ (T₀ , T₀ , T₀) (T₀ , T₁ , T₁) = refl
distribˡ-γ (T₀ , T₀ , T₀) (T₀ , T₁ , T₂) = refl
distribˡ-γ (T₀ , T₀ , T₀) (T₀ , T₂ , T₀) = refl
distribˡ-γ (T₀ , T₀ , T₀) (T₀ , T₂ , T₁) = refl
distribˡ-γ (T₀ , T₀ , T₀) (T₀ , T₂ , T₂) = refl
distribˡ-γ (T₀ , T₀ , T₀) (T₁ , T₀ , T₀) = refl
distribˡ-γ (T₀ , T₀ , T₀) (T₁ , T₀ , T₁) = refl
distribˡ-γ (T₀ , T₀ , T₀) (T₁ , T₀ , T₂) = refl
distribˡ-γ (T₀ , T₀ , T₀) (T₁ , T₁ , T₀) = refl
distribˡ-γ (T₀ , T₀ , T₀) (T₁ , T₁ , T₁) = refl
distribˡ-γ (T₀ , T₀ , T₀) (T₁ , T₁ , T₂) = refl
distribˡ-γ (T₀ , T₀ , T₀) (T₁ , T₂ , T₀) = refl
distribˡ-γ (T₀ , T₀ , T₀) (T₁ , T₂ , T₁) = refl
distribˡ-γ (T₀ , T₀ , T₀) (T₁ , T₂ , T₂) = refl
distribˡ-γ (T₀ , T₀ , T₀) (T₂ , T₀ , T₀) = refl
distribˡ-γ (T₀ , T₀ , T₀) (T₂ , T₀ , T₁) = refl
distribˡ-γ (T₀ , T₀ , T₀) (T₂ , T₀ , T₂) = refl
distribˡ-γ (T₀ , T₀ , T₀) (T₂ , T₁ , T₀) = refl
distribˡ-γ (T₀ , T₀ , T₀) (T₂ , T₁ , T₁) = refl
distribˡ-γ (T₀ , T₀ , T₀) (T₂ , T₁ , T₂) = refl
distribˡ-γ (T₀ , T₀ , T₀) (T₂ , T₂ , T₀) = refl
distribˡ-γ (T₀ , T₀ , T₀) (T₂ , T₂ , T₁) = refl
distribˡ-γ (T₀ , T₀ , T₀) (T₂ , T₂ , T₂) = refl
distribˡ-γ (T₀ , T₀ , T₁) (T₀ , T₀ , T₀) = refl
distribˡ-γ (T₀ , T₀ , T₁) (T₀ , T₀ , T₁) = refl
distribˡ-γ (T₀ , T₀ , T₁) (T₀ , T₀ , T₂) = refl
distribˡ-γ (T₀ , T₀ , T₁) (T₀ , T₁ , T₀) = refl
distribˡ-γ (T₀ , T₀ , T₁) (T₀ , T₁ , T₁) = refl
distribˡ-γ (T₀ , T₀ , T₁) (T₀ , T₁ , T₂) = refl
distribˡ-γ (T₀ , T₀ , T₁) (T₀ , T₂ , T₀) = refl
distribˡ-γ (T₀ , T₀ , T₁) (T₀ , T₂ , T₁) = refl
distribˡ-γ (T₀ , T₀ , T₁) (T₀ , T₂ , T₂) = refl
distribˡ-γ (T₀ , T₀ , T₁) (T₁ , T₀ , T₀) = refl
distribˡ-γ (T₀ , T₀ , T₁) (T₁ , T₀ , T₁) = refl
distribˡ-γ (T₀ , T₀ , T₁) (T₁ , T₀ , T₂) = refl
distribˡ-γ (T₀ , T₀ , T₁) (T₁ , T₁ , T₀) = refl
distribˡ-γ (T₀ , T₀ , T₁) (T₁ , T₁ , T₁) = refl
distribˡ-γ (T₀ , T₀ , T₁) (T₁ , T₁ , T₂) = refl
distribˡ-γ (T₀ , T₀ , T₁) (T₁ , T₂ , T₀) = refl
distribˡ-γ (T₀ , T₀ , T₁) (T₁ , T₂ , T₁) = refl
distribˡ-γ (T₀ , T₀ , T₁) (T₁ , T₂ , T₂) = refl
distribˡ-γ (T₀ , T₀ , T₁) (T₂ , T₀ , T₀) = refl
distribˡ-γ (T₀ , T₀ , T₁) (T₂ , T₀ , T₁) = refl
distribˡ-γ (T₀ , T₀ , T₁) (T₂ , T₀ , T₂) = refl
distribˡ-γ (T₀ , T₀ , T₁) (T₂ , T₁ , T₀) = refl
distribˡ-γ (T₀ , T₀ , T₁) (T₂ , T₁ , T₁) = refl
distribˡ-γ (T₀ , T₀ , T₁) (T₂ , T₁ , T₂) = refl
distribˡ-γ (T₀ , T₀ , T₁) (T₂ , T₂ , T₀) = refl
distribˡ-γ (T₀ , T₀ , T₁) (T₂ , T₂ , T₁) = refl
distribˡ-γ (T₀ , T₀ , T₁) (T₂ , T₂ , T₂) = refl
distribˡ-γ (T₀ , T₀ , T₂) (T₀ , T₀ , T₀) = refl
distribˡ-γ (T₀ , T₀ , T₂) (T₀ , T₀ , T₁) = refl
distribˡ-γ (T₀ , T₀ , T₂) (T₀ , T₀ , T₂) = refl
distribˡ-γ (T₀ , T₀ , T₂) (T₀ , T₁ , T₀) = refl
distribˡ-γ (T₀ , T₀ , T₂) (T₀ , T₁ , T₁) = refl
distribˡ-γ (T₀ , T₀ , T₂) (T₀ , T₁ , T₂) = refl
distribˡ-γ (T₀ , T₀ , T₂) (T₀ , T₂ , T₀) = refl
distribˡ-γ (T₀ , T₀ , T₂) (T₀ , T₂ , T₁) = refl
distribˡ-γ (T₀ , T₀ , T₂) (T₀ , T₂ , T₂) = refl
distribˡ-γ (T₀ , T₀ , T₂) (T₁ , T₀ , T₀) = refl
distribˡ-γ (T₀ , T₀ , T₂) (T₁ , T₀ , T₁) = refl
distribˡ-γ (T₀ , T₀ , T₂) (T₁ , T₀ , T₂) = refl
distribˡ-γ (T₀ , T₀ , T₂) (T₁ , T₁ , T₀) = refl
distribˡ-γ (T₀ , T₀ , T₂) (T₁ , T₁ , T₁) = refl
distribˡ-γ (T₀ , T₀ , T₂) (T₁ , T₁ , T₂) = refl
distribˡ-γ (T₀ , T₀ , T₂) (T₁ , T₂ , T₀) = refl
distribˡ-γ (T₀ , T₀ , T₂) (T₁ , T₂ , T₁) = refl
distribˡ-γ (T₀ , T₀ , T₂) (T₁ , T₂ , T₂) = refl
distribˡ-γ (T₀ , T₀ , T₂) (T₂ , T₀ , T₀) = refl
distribˡ-γ (T₀ , T₀ , T₂) (T₂ , T₀ , T₁) = refl
distribˡ-γ (T₀ , T₀ , T₂) (T₂ , T₀ , T₂) = refl
distribˡ-γ (T₀ , T₀ , T₂) (T₂ , T₁ , T₀) = refl
distribˡ-γ (T₀ , T₀ , T₂) (T₂ , T₁ , T₁) = refl
distribˡ-γ (T₀ , T₀ , T₂) (T₂ , T₁ , T₂) = refl
distribˡ-γ (T₀ , T₀ , T₂) (T₂ , T₂ , T₀) = refl
distribˡ-γ (T₀ , T₀ , T₂) (T₂ , T₂ , T₁) = refl
distribˡ-γ (T₀ , T₀ , T₂) (T₂ , T₂ , T₂) = refl
distribˡ-γ (T₀ , T₁ , T₀) (T₀ , T₀ , T₀) = refl
distribˡ-γ (T₀ , T₁ , T₀) (T₀ , T₀ , T₁) = refl
distribˡ-γ (T₀ , T₁ , T₀) (T₀ , T₀ , T₂) = refl
distribˡ-γ (T₀ , T₁ , T₀) (T₀ , T₁ , T₀) = refl
distribˡ-γ (T₀ , T₁ , T₀) (T₀ , T₁ , T₁) = refl
distribˡ-γ (T₀ , T₁ , T₀) (T₀ , T₁ , T₂) = refl
distribˡ-γ (T₀ , T₁ , T₀) (T₀ , T₂ , T₀) = refl
distribˡ-γ (T₀ , T₁ , T₀) (T₀ , T₂ , T₁) = refl
distribˡ-γ (T₀ , T₁ , T₀) (T₀ , T₂ , T₂) = refl
distribˡ-γ (T₀ , T₁ , T₀) (T₁ , T₀ , T₀) = refl
distribˡ-γ (T₀ , T₁ , T₀) (T₁ , T₀ , T₁) = refl
distribˡ-γ (T₀ , T₁ , T₀) (T₁ , T₀ , T₂) = refl
distribˡ-γ (T₀ , T₁ , T₀) (T₁ , T₁ , T₀) = refl
distribˡ-γ (T₀ , T₁ , T₀) (T₁ , T₁ , T₁) = refl
distribˡ-γ (T₀ , T₁ , T₀) (T₁ , T₁ , T₂) = refl
distribˡ-γ (T₀ , T₁ , T₀) (T₁ , T₂ , T₀) = refl
distribˡ-γ (T₀ , T₁ , T₀) (T₁ , T₂ , T₁) = refl
distribˡ-γ (T₀ , T₁ , T₀) (T₁ , T₂ , T₂) = refl
distribˡ-γ (T₀ , T₁ , T₀) (T₂ , T₀ , T₀) = refl
distribˡ-γ (T₀ , T₁ , T₀) (T₂ , T₀ , T₁) = refl
distribˡ-γ (T₀ , T₁ , T₀) (T₂ , T₀ , T₂) = refl
distribˡ-γ (T₀ , T₁ , T₀) (T₂ , T₁ , T₀) = refl
distribˡ-γ (T₀ , T₁ , T₀) (T₂ , T₁ , T₁) = refl
distribˡ-γ (T₀ , T₁ , T₀) (T₂ , T₁ , T₂) = refl
distribˡ-γ (T₀ , T₁ , T₀) (T₂ , T₂ , T₀) = refl
distribˡ-γ (T₀ , T₁ , T₀) (T₂ , T₂ , T₁) = refl
distribˡ-γ (T₀ , T₁ , T₀) (T₂ , T₂ , T₂) = refl
distribˡ-γ (T₀ , T₁ , T₁) (T₀ , T₀ , T₀) = refl
distribˡ-γ (T₀ , T₁ , T₁) (T₀ , T₀ , T₁) = refl
distribˡ-γ (T₀ , T₁ , T₁) (T₀ , T₀ , T₂) = refl
distribˡ-γ (T₀ , T₁ , T₁) (T₀ , T₁ , T₀) = refl
distribˡ-γ (T₀ , T₁ , T₁) (T₀ , T₁ , T₁) = refl
distribˡ-γ (T₀ , T₁ , T₁) (T₀ , T₁ , T₂) = refl
distribˡ-γ (T₀ , T₁ , T₁) (T₀ , T₂ , T₀) = refl
distribˡ-γ (T₀ , T₁ , T₁) (T₀ , T₂ , T₁) = refl
distribˡ-γ (T₀ , T₁ , T₁) (T₀ , T₂ , T₂) = refl
distribˡ-γ (T₀ , T₁ , T₁) (T₁ , T₀ , T₀) = refl
distribˡ-γ (T₀ , T₁ , T₁) (T₁ , T₀ , T₁) = refl
distribˡ-γ (T₀ , T₁ , T₁) (T₁ , T₀ , T₂) = refl
distribˡ-γ (T₀ , T₁ , T₁) (T₁ , T₁ , T₀) = refl
distribˡ-γ (T₀ , T₁ , T₁) (T₁ , T₁ , T₁) = refl
distribˡ-γ (T₀ , T₁ , T₁) (T₁ , T₁ , T₂) = refl
distribˡ-γ (T₀ , T₁ , T₁) (T₁ , T₂ , T₀) = refl
distribˡ-γ (T₀ , T₁ , T₁) (T₁ , T₂ , T₁) = refl
distribˡ-γ (T₀ , T₁ , T₁) (T₁ , T₂ , T₂) = refl
distribˡ-γ (T₀ , T₁ , T₁) (T₂ , T₀ , T₀) = refl
distribˡ-γ (T₀ , T₁ , T₁) (T₂ , T₀ , T₁) = refl
distribˡ-γ (T₀ , T₁ , T₁) (T₂ , T₀ , T₂) = refl
distribˡ-γ (T₀ , T₁ , T₁) (T₂ , T₁ , T₀) = refl
distribˡ-γ (T₀ , T₁ , T₁) (T₂ , T₁ , T₁) = refl
distribˡ-γ (T₀ , T₁ , T₁) (T₂ , T₁ , T₂) = refl
distribˡ-γ (T₀ , T₁ , T₁) (T₂ , T₂ , T₀) = refl
distribˡ-γ (T₀ , T₁ , T₁) (T₂ , T₂ , T₁) = refl
distribˡ-γ (T₀ , T₁ , T₁) (T₂ , T₂ , T₂) = refl
distribˡ-γ (T₀ , T₁ , T₂) (T₀ , T₀ , T₀) = refl
distribˡ-γ (T₀ , T₁ , T₂) (T₀ , T₀ , T₁) = refl
distribˡ-γ (T₀ , T₁ , T₂) (T₀ , T₀ , T₂) = refl
distribˡ-γ (T₀ , T₁ , T₂) (T₀ , T₁ , T₀) = refl
distribˡ-γ (T₀ , T₁ , T₂) (T₀ , T₁ , T₁) = refl
distribˡ-γ (T₀ , T₁ , T₂) (T₀ , T₁ , T₂) = refl
distribˡ-γ (T₀ , T₁ , T₂) (T₀ , T₂ , T₀) = refl
distribˡ-γ (T₀ , T₁ , T₂) (T₀ , T₂ , T₁) = refl
distribˡ-γ (T₀ , T₁ , T₂) (T₀ , T₂ , T₂) = refl
distribˡ-γ (T₀ , T₁ , T₂) (T₁ , T₀ , T₀) = refl
distribˡ-γ (T₀ , T₁ , T₂) (T₁ , T₀ , T₁) = refl
distribˡ-γ (T₀ , T₁ , T₂) (T₁ , T₀ , T₂) = refl
distribˡ-γ (T₀ , T₁ , T₂) (T₁ , T₁ , T₀) = refl
distribˡ-γ (T₀ , T₁ , T₂) (T₁ , T₁ , T₁) = refl
distribˡ-γ (T₀ , T₁ , T₂) (T₁ , T₁ , T₂) = refl
distribˡ-γ (T₀ , T₁ , T₂) (T₁ , T₂ , T₀) = refl
distribˡ-γ (T₀ , T₁ , T₂) (T₁ , T₂ , T₁) = refl
distribˡ-γ (T₀ , T₁ , T₂) (T₁ , T₂ , T₂) = refl
distribˡ-γ (T₀ , T₁ , T₂) (T₂ , T₀ , T₀) = refl
distribˡ-γ (T₀ , T₁ , T₂) (T₂ , T₀ , T₁) = refl
distribˡ-γ (T₀ , T₁ , T₂) (T₂ , T₀ , T₂) = refl
distribˡ-γ (T₀ , T₁ , T₂) (T₂ , T₁ , T₀) = refl
distribˡ-γ (T₀ , T₁ , T₂) (T₂ , T₁ , T₁) = refl
distribˡ-γ (T₀ , T₁ , T₂) (T₂ , T₁ , T₂) = refl
distribˡ-γ (T₀ , T₁ , T₂) (T₂ , T₂ , T₀) = refl
distribˡ-γ (T₀ , T₁ , T₂) (T₂ , T₂ , T₁) = refl
distribˡ-γ (T₀ , T₁ , T₂) (T₂ , T₂ , T₂) = refl
distribˡ-γ (T₀ , T₂ , T₀) (T₀ , T₀ , T₀) = refl
distribˡ-γ (T₀ , T₂ , T₀) (T₀ , T₀ , T₁) = refl
distribˡ-γ (T₀ , T₂ , T₀) (T₀ , T₀ , T₂) = refl
distribˡ-γ (T₀ , T₂ , T₀) (T₀ , T₁ , T₀) = refl
distribˡ-γ (T₀ , T₂ , T₀) (T₀ , T₁ , T₁) = refl
distribˡ-γ (T₀ , T₂ , T₀) (T₀ , T₁ , T₂) = refl
distribˡ-γ (T₀ , T₂ , T₀) (T₀ , T₂ , T₀) = refl
distribˡ-γ (T₀ , T₂ , T₀) (T₀ , T₂ , T₁) = refl
distribˡ-γ (T₀ , T₂ , T₀) (T₀ , T₂ , T₂) = refl
distribˡ-γ (T₀ , T₂ , T₀) (T₁ , T₀ , T₀) = refl
distribˡ-γ (T₀ , T₂ , T₀) (T₁ , T₀ , T₁) = refl
distribˡ-γ (T₀ , T₂ , T₀) (T₁ , T₀ , T₂) = refl
distribˡ-γ (T₀ , T₂ , T₀) (T₁ , T₁ , T₀) = refl
distribˡ-γ (T₀ , T₂ , T₀) (T₁ , T₁ , T₁) = refl
distribˡ-γ (T₀ , T₂ , T₀) (T₁ , T₁ , T₂) = refl
distribˡ-γ (T₀ , T₂ , T₀) (T₁ , T₂ , T₀) = refl
distribˡ-γ (T₀ , T₂ , T₀) (T₁ , T₂ , T₁) = refl
distribˡ-γ (T₀ , T₂ , T₀) (T₁ , T₂ , T₂) = refl
distribˡ-γ (T₀ , T₂ , T₀) (T₂ , T₀ , T₀) = refl
distribˡ-γ (T₀ , T₂ , T₀) (T₂ , T₀ , T₁) = refl
distribˡ-γ (T₀ , T₂ , T₀) (T₂ , T₀ , T₂) = refl
distribˡ-γ (T₀ , T₂ , T₀) (T₂ , T₁ , T₀) = refl
distribˡ-γ (T₀ , T₂ , T₀) (T₂ , T₁ , T₁) = refl
distribˡ-γ (T₀ , T₂ , T₀) (T₂ , T₁ , T₂) = refl
distribˡ-γ (T₀ , T₂ , T₀) (T₂ , T₂ , T₀) = refl
distribˡ-γ (T₀ , T₂ , T₀) (T₂ , T₂ , T₁) = refl
distribˡ-γ (T₀ , T₂ , T₀) (T₂ , T₂ , T₂) = refl
distribˡ-γ (T₀ , T₂ , T₁) (T₀ , T₀ , T₀) = refl
distribˡ-γ (T₀ , T₂ , T₁) (T₀ , T₀ , T₁) = refl
distribˡ-γ (T₀ , T₂ , T₁) (T₀ , T₀ , T₂) = refl
distribˡ-γ (T₀ , T₂ , T₁) (T₀ , T₁ , T₀) = refl
distribˡ-γ (T₀ , T₂ , T₁) (T₀ , T₁ , T₁) = refl
distribˡ-γ (T₀ , T₂ , T₁) (T₀ , T₁ , T₂) = refl
distribˡ-γ (T₀ , T₂ , T₁) (T₀ , T₂ , T₀) = refl
distribˡ-γ (T₀ , T₂ , T₁) (T₀ , T₂ , T₁) = refl
distribˡ-γ (T₀ , T₂ , T₁) (T₀ , T₂ , T₂) = refl
distribˡ-γ (T₀ , T₂ , T₁) (T₁ , T₀ , T₀) = refl
distribˡ-γ (T₀ , T₂ , T₁) (T₁ , T₀ , T₁) = refl
distribˡ-γ (T₀ , T₂ , T₁) (T₁ , T₀ , T₂) = refl
distribˡ-γ (T₀ , T₂ , T₁) (T₁ , T₁ , T₀) = refl
distribˡ-γ (T₀ , T₂ , T₁) (T₁ , T₁ , T₁) = refl
distribˡ-γ (T₀ , T₂ , T₁) (T₁ , T₁ , T₂) = refl
distribˡ-γ (T₀ , T₂ , T₁) (T₁ , T₂ , T₀) = refl
distribˡ-γ (T₀ , T₂ , T₁) (T₁ , T₂ , T₁) = refl
distribˡ-γ (T₀ , T₂ , T₁) (T₁ , T₂ , T₂) = refl
distribˡ-γ (T₀ , T₂ , T₁) (T₂ , T₀ , T₀) = refl
distribˡ-γ (T₀ , T₂ , T₁) (T₂ , T₀ , T₁) = refl
distribˡ-γ (T₀ , T₂ , T₁) (T₂ , T₀ , T₂) = refl
distribˡ-γ (T₀ , T₂ , T₁) (T₂ , T₁ , T₀) = refl
distribˡ-γ (T₀ , T₂ , T₁) (T₂ , T₁ , T₁) = refl
distribˡ-γ (T₀ , T₂ , T₁) (T₂ , T₁ , T₂) = refl
distribˡ-γ (T₀ , T₂ , T₁) (T₂ , T₂ , T₀) = refl
distribˡ-γ (T₀ , T₂ , T₁) (T₂ , T₂ , T₁) = refl
distribˡ-γ (T₀ , T₂ , T₁) (T₂ , T₂ , T₂) = refl
distribˡ-γ (T₀ , T₂ , T₂) (T₀ , T₀ , T₀) = refl
distribˡ-γ (T₀ , T₂ , T₂) (T₀ , T₀ , T₁) = refl
distribˡ-γ (T₀ , T₂ , T₂) (T₀ , T₀ , T₂) = refl
distribˡ-γ (T₀ , T₂ , T₂) (T₀ , T₁ , T₀) = refl
distribˡ-γ (T₀ , T₂ , T₂) (T₀ , T₁ , T₁) = refl
distribˡ-γ (T₀ , T₂ , T₂) (T₀ , T₁ , T₂) = refl
distribˡ-γ (T₀ , T₂ , T₂) (T₀ , T₂ , T₀) = refl
distribˡ-γ (T₀ , T₂ , T₂) (T₀ , T₂ , T₁) = refl
distribˡ-γ (T₀ , T₂ , T₂) (T₀ , T₂ , T₂) = refl
distribˡ-γ (T₀ , T₂ , T₂) (T₁ , T₀ , T₀) = refl
distribˡ-γ (T₀ , T₂ , T₂) (T₁ , T₀ , T₁) = refl
distribˡ-γ (T₀ , T₂ , T₂) (T₁ , T₀ , T₂) = refl
distribˡ-γ (T₀ , T₂ , T₂) (T₁ , T₁ , T₀) = refl
distribˡ-γ (T₀ , T₂ , T₂) (T₁ , T₁ , T₁) = refl
distribˡ-γ (T₀ , T₂ , T₂) (T₁ , T₁ , T₂) = refl
distribˡ-γ (T₀ , T₂ , T₂) (T₁ , T₂ , T₀) = refl
distribˡ-γ (T₀ , T₂ , T₂) (T₁ , T₂ , T₁) = refl
distribˡ-γ (T₀ , T₂ , T₂) (T₁ , T₂ , T₂) = refl
distribˡ-γ (T₀ , T₂ , T₂) (T₂ , T₀ , T₀) = refl
distribˡ-γ (T₀ , T₂ , T₂) (T₂ , T₀ , T₁) = refl
distribˡ-γ (T₀ , T₂ , T₂) (T₂ , T₀ , T₂) = refl
distribˡ-γ (T₀ , T₂ , T₂) (T₂ , T₁ , T₀) = refl
distribˡ-γ (T₀ , T₂ , T₂) (T₂ , T₁ , T₁) = refl
distribˡ-γ (T₀ , T₂ , T₂) (T₂ , T₁ , T₂) = refl
distribˡ-γ (T₀ , T₂ , T₂) (T₂ , T₂ , T₀) = refl
distribˡ-γ (T₀ , T₂ , T₂) (T₂ , T₂ , T₁) = refl
distribˡ-γ (T₀ , T₂ , T₂) (T₂ , T₂ , T₂) = refl
distribˡ-γ (T₁ , T₀ , T₀) (T₀ , T₀ , T₀) = refl
distribˡ-γ (T₁ , T₀ , T₀) (T₀ , T₀ , T₁) = refl
distribˡ-γ (T₁ , T₀ , T₀) (T₀ , T₀ , T₂) = refl
distribˡ-γ (T₁ , T₀ , T₀) (T₀ , T₁ , T₀) = refl
distribˡ-γ (T₁ , T₀ , T₀) (T₀ , T₁ , T₁) = refl
distribˡ-γ (T₁ , T₀ , T₀) (T₀ , T₁ , T₂) = refl
distribˡ-γ (T₁ , T₀ , T₀) (T₀ , T₂ , T₀) = refl
distribˡ-γ (T₁ , T₀ , T₀) (T₀ , T₂ , T₁) = refl
distribˡ-γ (T₁ , T₀ , T₀) (T₀ , T₂ , T₂) = refl
distribˡ-γ (T₁ , T₀ , T₀) (T₁ , T₀ , T₀) = refl
distribˡ-γ (T₁ , T₀ , T₀) (T₁ , T₀ , T₁) = refl
distribˡ-γ (T₁ , T₀ , T₀) (T₁ , T₀ , T₂) = refl
distribˡ-γ (T₁ , T₀ , T₀) (T₁ , T₁ , T₀) = refl
distribˡ-γ (T₁ , T₀ , T₀) (T₁ , T₁ , T₁) = refl
distribˡ-γ (T₁ , T₀ , T₀) (T₁ , T₁ , T₂) = refl
distribˡ-γ (T₁ , T₀ , T₀) (T₁ , T₂ , T₀) = refl
distribˡ-γ (T₁ , T₀ , T₀) (T₁ , T₂ , T₁) = refl
distribˡ-γ (T₁ , T₀ , T₀) (T₁ , T₂ , T₂) = refl
distribˡ-γ (T₁ , T₀ , T₀) (T₂ , T₀ , T₀) = refl
distribˡ-γ (T₁ , T₀ , T₀) (T₂ , T₀ , T₁) = refl
distribˡ-γ (T₁ , T₀ , T₀) (T₂ , T₀ , T₂) = refl
distribˡ-γ (T₁ , T₀ , T₀) (T₂ , T₁ , T₀) = refl
distribˡ-γ (T₁ , T₀ , T₀) (T₂ , T₁ , T₁) = refl
distribˡ-γ (T₁ , T₀ , T₀) (T₂ , T₁ , T₂) = refl
distribˡ-γ (T₁ , T₀ , T₀) (T₂ , T₂ , T₀) = refl
distribˡ-γ (T₁ , T₀ , T₀) (T₂ , T₂ , T₁) = refl
distribˡ-γ (T₁ , T₀ , T₀) (T₂ , T₂ , T₂) = refl
distribˡ-γ (T₁ , T₀ , T₁) (T₀ , T₀ , T₀) = refl
distribˡ-γ (T₁ , T₀ , T₁) (T₀ , T₀ , T₁) = refl
distribˡ-γ (T₁ , T₀ , T₁) (T₀ , T₀ , T₂) = refl
distribˡ-γ (T₁ , T₀ , T₁) (T₀ , T₁ , T₀) = refl
distribˡ-γ (T₁ , T₀ , T₁) (T₀ , T₁ , T₁) = refl
distribˡ-γ (T₁ , T₀ , T₁) (T₀ , T₁ , T₂) = refl
distribˡ-γ (T₁ , T₀ , T₁) (T₀ , T₂ , T₀) = refl
distribˡ-γ (T₁ , T₀ , T₁) (T₀ , T₂ , T₁) = refl
distribˡ-γ (T₁ , T₀ , T₁) (T₀ , T₂ , T₂) = refl
distribˡ-γ (T₁ , T₀ , T₁) (T₁ , T₀ , T₀) = refl
distribˡ-γ (T₁ , T₀ , T₁) (T₁ , T₀ , T₁) = refl
distribˡ-γ (T₁ , T₀ , T₁) (T₁ , T₀ , T₂) = refl
distribˡ-γ (T₁ , T₀ , T₁) (T₁ , T₁ , T₀) = refl
distribˡ-γ (T₁ , T₀ , T₁) (T₁ , T₁ , T₁) = refl
distribˡ-γ (T₁ , T₀ , T₁) (T₁ , T₁ , T₂) = refl
distribˡ-γ (T₁ , T₀ , T₁) (T₁ , T₂ , T₀) = refl
distribˡ-γ (T₁ , T₀ , T₁) (T₁ , T₂ , T₁) = refl
distribˡ-γ (T₁ , T₀ , T₁) (T₁ , T₂ , T₂) = refl
distribˡ-γ (T₁ , T₀ , T₁) (T₂ , T₀ , T₀) = refl
distribˡ-γ (T₁ , T₀ , T₁) (T₂ , T₀ , T₁) = refl
distribˡ-γ (T₁ , T₀ , T₁) (T₂ , T₀ , T₂) = refl
distribˡ-γ (T₁ , T₀ , T₁) (T₂ , T₁ , T₀) = refl
distribˡ-γ (T₁ , T₀ , T₁) (T₂ , T₁ , T₁) = refl
distribˡ-γ (T₁ , T₀ , T₁) (T₂ , T₁ , T₂) = refl
distribˡ-γ (T₁ , T₀ , T₁) (T₂ , T₂ , T₀) = refl
distribˡ-γ (T₁ , T₀ , T₁) (T₂ , T₂ , T₁) = refl
distribˡ-γ (T₁ , T₀ , T₁) (T₂ , T₂ , T₂) = refl
distribˡ-γ (T₁ , T₀ , T₂) (T₀ , T₀ , T₀) = refl
distribˡ-γ (T₁ , T₀ , T₂) (T₀ , T₀ , T₁) = refl
distribˡ-γ (T₁ , T₀ , T₂) (T₀ , T₀ , T₂) = refl
distribˡ-γ (T₁ , T₀ , T₂) (T₀ , T₁ , T₀) = refl
distribˡ-γ (T₁ , T₀ , T₂) (T₀ , T₁ , T₁) = refl
distribˡ-γ (T₁ , T₀ , T₂) (T₀ , T₁ , T₂) = refl
distribˡ-γ (T₁ , T₀ , T₂) (T₀ , T₂ , T₀) = refl
distribˡ-γ (T₁ , T₀ , T₂) (T₀ , T₂ , T₁) = refl
distribˡ-γ (T₁ , T₀ , T₂) (T₀ , T₂ , T₂) = refl
distribˡ-γ (T₁ , T₀ , T₂) (T₁ , T₀ , T₀) = refl
distribˡ-γ (T₁ , T₀ , T₂) (T₁ , T₀ , T₁) = refl
distribˡ-γ (T₁ , T₀ , T₂) (T₁ , T₀ , T₂) = refl
distribˡ-γ (T₁ , T₀ , T₂) (T₁ , T₁ , T₀) = refl
distribˡ-γ (T₁ , T₀ , T₂) (T₁ , T₁ , T₁) = refl
distribˡ-γ (T₁ , T₀ , T₂) (T₁ , T₁ , T₂) = refl
distribˡ-γ (T₁ , T₀ , T₂) (T₁ , T₂ , T₀) = refl
distribˡ-γ (T₁ , T₀ , T₂) (T₁ , T₂ , T₁) = refl
distribˡ-γ (T₁ , T₀ , T₂) (T₁ , T₂ , T₂) = refl
distribˡ-γ (T₁ , T₀ , T₂) (T₂ , T₀ , T₀) = refl
distribˡ-γ (T₁ , T₀ , T₂) (T₂ , T₀ , T₁) = refl
distribˡ-γ (T₁ , T₀ , T₂) (T₂ , T₀ , T₂) = refl
distribˡ-γ (T₁ , T₀ , T₂) (T₂ , T₁ , T₀) = refl
distribˡ-γ (T₁ , T₀ , T₂) (T₂ , T₁ , T₁) = refl
distribˡ-γ (T₁ , T₀ , T₂) (T₂ , T₁ , T₂) = refl
distribˡ-γ (T₁ , T₀ , T₂) (T₂ , T₂ , T₀) = refl
distribˡ-γ (T₁ , T₀ , T₂) (T₂ , T₂ , T₁) = refl
distribˡ-γ (T₁ , T₀ , T₂) (T₂ , T₂ , T₂) = refl
distribˡ-γ (T₁ , T₁ , T₀) (T₀ , T₀ , T₀) = refl
distribˡ-γ (T₁ , T₁ , T₀) (T₀ , T₀ , T₁) = refl
distribˡ-γ (T₁ , T₁ , T₀) (T₀ , T₀ , T₂) = refl
distribˡ-γ (T₁ , T₁ , T₀) (T₀ , T₁ , T₀) = refl
distribˡ-γ (T₁ , T₁ , T₀) (T₀ , T₁ , T₁) = refl
distribˡ-γ (T₁ , T₁ , T₀) (T₀ , T₁ , T₂) = refl
distribˡ-γ (T₁ , T₁ , T₀) (T₀ , T₂ , T₀) = refl
distribˡ-γ (T₁ , T₁ , T₀) (T₀ , T₂ , T₁) = refl
distribˡ-γ (T₁ , T₁ , T₀) (T₀ , T₂ , T₂) = refl
distribˡ-γ (T₁ , T₁ , T₀) (T₁ , T₀ , T₀) = refl
distribˡ-γ (T₁ , T₁ , T₀) (T₁ , T₀ , T₁) = refl
distribˡ-γ (T₁ , T₁ , T₀) (T₁ , T₀ , T₂) = refl
distribˡ-γ (T₁ , T₁ , T₀) (T₁ , T₁ , T₀) = refl
distribˡ-γ (T₁ , T₁ , T₀) (T₁ , T₁ , T₁) = refl
distribˡ-γ (T₁ , T₁ , T₀) (T₁ , T₁ , T₂) = refl
distribˡ-γ (T₁ , T₁ , T₀) (T₁ , T₂ , T₀) = refl
distribˡ-γ (T₁ , T₁ , T₀) (T₁ , T₂ , T₁) = refl
distribˡ-γ (T₁ , T₁ , T₀) (T₁ , T₂ , T₂) = refl
distribˡ-γ (T₁ , T₁ , T₀) (T₂ , T₀ , T₀) = refl
distribˡ-γ (T₁ , T₁ , T₀) (T₂ , T₀ , T₁) = refl
distribˡ-γ (T₁ , T₁ , T₀) (T₂ , T₀ , T₂) = refl
distribˡ-γ (T₁ , T₁ , T₀) (T₂ , T₁ , T₀) = refl
distribˡ-γ (T₁ , T₁ , T₀) (T₂ , T₁ , T₁) = refl
distribˡ-γ (T₁ , T₁ , T₀) (T₂ , T₁ , T₂) = refl
distribˡ-γ (T₁ , T₁ , T₀) (T₂ , T₂ , T₀) = refl
distribˡ-γ (T₁ , T₁ , T₀) (T₂ , T₂ , T₁) = refl
distribˡ-γ (T₁ , T₁ , T₀) (T₂ , T₂ , T₂) = refl
distribˡ-γ (T₁ , T₁ , T₁) (T₀ , T₀ , T₀) = refl
distribˡ-γ (T₁ , T₁ , T₁) (T₀ , T₀ , T₁) = refl
distribˡ-γ (T₁ , T₁ , T₁) (T₀ , T₀ , T₂) = refl
distribˡ-γ (T₁ , T₁ , T₁) (T₀ , T₁ , T₀) = refl
distribˡ-γ (T₁ , T₁ , T₁) (T₀ , T₁ , T₁) = refl
distribˡ-γ (T₁ , T₁ , T₁) (T₀ , T₁ , T₂) = refl
distribˡ-γ (T₁ , T₁ , T₁) (T₀ , T₂ , T₀) = refl
distribˡ-γ (T₁ , T₁ , T₁) (T₀ , T₂ , T₁) = refl
distribˡ-γ (T₁ , T₁ , T₁) (T₀ , T₂ , T₂) = refl
distribˡ-γ (T₁ , T₁ , T₁) (T₁ , T₀ , T₀) = refl
distribˡ-γ (T₁ , T₁ , T₁) (T₁ , T₀ , T₁) = refl
distribˡ-γ (T₁ , T₁ , T₁) (T₁ , T₀ , T₂) = refl
distribˡ-γ (T₁ , T₁ , T₁) (T₁ , T₁ , T₀) = refl
distribˡ-γ (T₁ , T₁ , T₁) (T₁ , T₁ , T₁) = refl
distribˡ-γ (T₁ , T₁ , T₁) (T₁ , T₁ , T₂) = refl
distribˡ-γ (T₁ , T₁ , T₁) (T₁ , T₂ , T₀) = refl
distribˡ-γ (T₁ , T₁ , T₁) (T₁ , T₂ , T₁) = refl
distribˡ-γ (T₁ , T₁ , T₁) (T₁ , T₂ , T₂) = refl
distribˡ-γ (T₁ , T₁ , T₁) (T₂ , T₀ , T₀) = refl
distribˡ-γ (T₁ , T₁ , T₁) (T₂ , T₀ , T₁) = refl
distribˡ-γ (T₁ , T₁ , T₁) (T₂ , T₀ , T₂) = refl
distribˡ-γ (T₁ , T₁ , T₁) (T₂ , T₁ , T₀) = refl
distribˡ-γ (T₁ , T₁ , T₁) (T₂ , T₁ , T₁) = refl
distribˡ-γ (T₁ , T₁ , T₁) (T₂ , T₁ , T₂) = refl
distribˡ-γ (T₁ , T₁ , T₁) (T₂ , T₂ , T₀) = refl
distribˡ-γ (T₁ , T₁ , T₁) (T₂ , T₂ , T₁) = refl
distribˡ-γ (T₁ , T₁ , T₁) (T₂ , T₂ , T₂) = refl
distribˡ-γ (T₁ , T₁ , T₂) (T₀ , T₀ , T₀) = refl
distribˡ-γ (T₁ , T₁ , T₂) (T₀ , T₀ , T₁) = refl
distribˡ-γ (T₁ , T₁ , T₂) (T₀ , T₀ , T₂) = refl
distribˡ-γ (T₁ , T₁ , T₂) (T₀ , T₁ , T₀) = refl
distribˡ-γ (T₁ , T₁ , T₂) (T₀ , T₁ , T₁) = refl
distribˡ-γ (T₁ , T₁ , T₂) (T₀ , T₁ , T₂) = refl
distribˡ-γ (T₁ , T₁ , T₂) (T₀ , T₂ , T₀) = refl
distribˡ-γ (T₁ , T₁ , T₂) (T₀ , T₂ , T₁) = refl
distribˡ-γ (T₁ , T₁ , T₂) (T₀ , T₂ , T₂) = refl
distribˡ-γ (T₁ , T₁ , T₂) (T₁ , T₀ , T₀) = refl
distribˡ-γ (T₁ , T₁ , T₂) (T₁ , T₀ , T₁) = refl
distribˡ-γ (T₁ , T₁ , T₂) (T₁ , T₀ , T₂) = refl
distribˡ-γ (T₁ , T₁ , T₂) (T₁ , T₁ , T₀) = refl
distribˡ-γ (T₁ , T₁ , T₂) (T₁ , T₁ , T₁) = refl
distribˡ-γ (T₁ , T₁ , T₂) (T₁ , T₁ , T₂) = refl
distribˡ-γ (T₁ , T₁ , T₂) (T₁ , T₂ , T₀) = refl
distribˡ-γ (T₁ , T₁ , T₂) (T₁ , T₂ , T₁) = refl
distribˡ-γ (T₁ , T₁ , T₂) (T₁ , T₂ , T₂) = refl
distribˡ-γ (T₁ , T₁ , T₂) (T₂ , T₀ , T₀) = refl
distribˡ-γ (T₁ , T₁ , T₂) (T₂ , T₀ , T₁) = refl
distribˡ-γ (T₁ , T₁ , T₂) (T₂ , T₀ , T₂) = refl
distribˡ-γ (T₁ , T₁ , T₂) (T₂ , T₁ , T₀) = refl
distribˡ-γ (T₁ , T₁ , T₂) (T₂ , T₁ , T₁) = refl
distribˡ-γ (T₁ , T₁ , T₂) (T₂ , T₁ , T₂) = refl
distribˡ-γ (T₁ , T₁ , T₂) (T₂ , T₂ , T₀) = refl
distribˡ-γ (T₁ , T₁ , T₂) (T₂ , T₂ , T₁) = refl
distribˡ-γ (T₁ , T₁ , T₂) (T₂ , T₂ , T₂) = refl
distribˡ-γ (T₁ , T₂ , T₀) (T₀ , T₀ , T₀) = refl
distribˡ-γ (T₁ , T₂ , T₀) (T₀ , T₀ , T₁) = refl
distribˡ-γ (T₁ , T₂ , T₀) (T₀ , T₀ , T₂) = refl
distribˡ-γ (T₁ , T₂ , T₀) (T₀ , T₁ , T₀) = refl
distribˡ-γ (T₁ , T₂ , T₀) (T₀ , T₁ , T₁) = refl
distribˡ-γ (T₁ , T₂ , T₀) (T₀ , T₁ , T₂) = refl
distribˡ-γ (T₁ , T₂ , T₀) (T₀ , T₂ , T₀) = refl
distribˡ-γ (T₁ , T₂ , T₀) (T₀ , T₂ , T₁) = refl
distribˡ-γ (T₁ , T₂ , T₀) (T₀ , T₂ , T₂) = refl
distribˡ-γ (T₁ , T₂ , T₀) (T₁ , T₀ , T₀) = refl
distribˡ-γ (T₁ , T₂ , T₀) (T₁ , T₀ , T₁) = refl
distribˡ-γ (T₁ , T₂ , T₀) (T₁ , T₀ , T₂) = refl
distribˡ-γ (T₁ , T₂ , T₀) (T₁ , T₁ , T₀) = refl
distribˡ-γ (T₁ , T₂ , T₀) (T₁ , T₁ , T₁) = refl
distribˡ-γ (T₁ , T₂ , T₀) (T₁ , T₁ , T₂) = refl
distribˡ-γ (T₁ , T₂ , T₀) (T₁ , T₂ , T₀) = refl
distribˡ-γ (T₁ , T₂ , T₀) (T₁ , T₂ , T₁) = refl
distribˡ-γ (T₁ , T₂ , T₀) (T₁ , T₂ , T₂) = refl
distribˡ-γ (T₁ , T₂ , T₀) (T₂ , T₀ , T₀) = refl
distribˡ-γ (T₁ , T₂ , T₀) (T₂ , T₀ , T₁) = refl
distribˡ-γ (T₁ , T₂ , T₀) (T₂ , T₀ , T₂) = refl
distribˡ-γ (T₁ , T₂ , T₀) (T₂ , T₁ , T₀) = refl
distribˡ-γ (T₁ , T₂ , T₀) (T₂ , T₁ , T₁) = refl
distribˡ-γ (T₁ , T₂ , T₀) (T₂ , T₁ , T₂) = refl
distribˡ-γ (T₁ , T₂ , T₀) (T₂ , T₂ , T₀) = refl
distribˡ-γ (T₁ , T₂ , T₀) (T₂ , T₂ , T₁) = refl
distribˡ-γ (T₁ , T₂ , T₀) (T₂ , T₂ , T₂) = refl
distribˡ-γ (T₁ , T₂ , T₁) (T₀ , T₀ , T₀) = refl
distribˡ-γ (T₁ , T₂ , T₁) (T₀ , T₀ , T₁) = refl
distribˡ-γ (T₁ , T₂ , T₁) (T₀ , T₀ , T₂) = refl
distribˡ-γ (T₁ , T₂ , T₁) (T₀ , T₁ , T₀) = refl
distribˡ-γ (T₁ , T₂ , T₁) (T₀ , T₁ , T₁) = refl
distribˡ-γ (T₁ , T₂ , T₁) (T₀ , T₁ , T₂) = refl
distribˡ-γ (T₁ , T₂ , T₁) (T₀ , T₂ , T₀) = refl
distribˡ-γ (T₁ , T₂ , T₁) (T₀ , T₂ , T₁) = refl
distribˡ-γ (T₁ , T₂ , T₁) (T₀ , T₂ , T₂) = refl
distribˡ-γ (T₁ , T₂ , T₁) (T₁ , T₀ , T₀) = refl
distribˡ-γ (T₁ , T₂ , T₁) (T₁ , T₀ , T₁) = refl
distribˡ-γ (T₁ , T₂ , T₁) (T₁ , T₀ , T₂) = refl
distribˡ-γ (T₁ , T₂ , T₁) (T₁ , T₁ , T₀) = refl
distribˡ-γ (T₁ , T₂ , T₁) (T₁ , T₁ , T₁) = refl
distribˡ-γ (T₁ , T₂ , T₁) (T₁ , T₁ , T₂) = refl
distribˡ-γ (T₁ , T₂ , T₁) (T₁ , T₂ , T₀) = refl
distribˡ-γ (T₁ , T₂ , T₁) (T₁ , T₂ , T₁) = refl
distribˡ-γ (T₁ , T₂ , T₁) (T₁ , T₂ , T₂) = refl
distribˡ-γ (T₁ , T₂ , T₁) (T₂ , T₀ , T₀) = refl
distribˡ-γ (T₁ , T₂ , T₁) (T₂ , T₀ , T₁) = refl
distribˡ-γ (T₁ , T₂ , T₁) (T₂ , T₀ , T₂) = refl
distribˡ-γ (T₁ , T₂ , T₁) (T₂ , T₁ , T₀) = refl
distribˡ-γ (T₁ , T₂ , T₁) (T₂ , T₁ , T₁) = refl
distribˡ-γ (T₁ , T₂ , T₁) (T₂ , T₁ , T₂) = refl
distribˡ-γ (T₁ , T₂ , T₁) (T₂ , T₂ , T₀) = refl
distribˡ-γ (T₁ , T₂ , T₁) (T₂ , T₂ , T₁) = refl
distribˡ-γ (T₁ , T₂ , T₁) (T₂ , T₂ , T₂) = refl
distribˡ-γ (T₁ , T₂ , T₂) (T₀ , T₀ , T₀) = refl
distribˡ-γ (T₁ , T₂ , T₂) (T₀ , T₀ , T₁) = refl
distribˡ-γ (T₁ , T₂ , T₂) (T₀ , T₀ , T₂) = refl
distribˡ-γ (T₁ , T₂ , T₂) (T₀ , T₁ , T₀) = refl
distribˡ-γ (T₁ , T₂ , T₂) (T₀ , T₁ , T₁) = refl
distribˡ-γ (T₁ , T₂ , T₂) (T₀ , T₁ , T₂) = refl
distribˡ-γ (T₁ , T₂ , T₂) (T₀ , T₂ , T₀) = refl
distribˡ-γ (T₁ , T₂ , T₂) (T₀ , T₂ , T₁) = refl
distribˡ-γ (T₁ , T₂ , T₂) (T₀ , T₂ , T₂) = refl
distribˡ-γ (T₁ , T₂ , T₂) (T₁ , T₀ , T₀) = refl
distribˡ-γ (T₁ , T₂ , T₂) (T₁ , T₀ , T₁) = refl
distribˡ-γ (T₁ , T₂ , T₂) (T₁ , T₀ , T₂) = refl
distribˡ-γ (T₁ , T₂ , T₂) (T₁ , T₁ , T₀) = refl
distribˡ-γ (T₁ , T₂ , T₂) (T₁ , T₁ , T₁) = refl
distribˡ-γ (T₁ , T₂ , T₂) (T₁ , T₁ , T₂) = refl
distribˡ-γ (T₁ , T₂ , T₂) (T₁ , T₂ , T₀) = refl
distribˡ-γ (T₁ , T₂ , T₂) (T₁ , T₂ , T₁) = refl
distribˡ-γ (T₁ , T₂ , T₂) (T₁ , T₂ , T₂) = refl
distribˡ-γ (T₁ , T₂ , T₂) (T₂ , T₀ , T₀) = refl
distribˡ-γ (T₁ , T₂ , T₂) (T₂ , T₀ , T₁) = refl
distribˡ-γ (T₁ , T₂ , T₂) (T₂ , T₀ , T₂) = refl
distribˡ-γ (T₁ , T₂ , T₂) (T₂ , T₁ , T₀) = refl
distribˡ-γ (T₁ , T₂ , T₂) (T₂ , T₁ , T₁) = refl
distribˡ-γ (T₁ , T₂ , T₂) (T₂ , T₁ , T₂) = refl
distribˡ-γ (T₁ , T₂ , T₂) (T₂ , T₂ , T₀) = refl
distribˡ-γ (T₁ , T₂ , T₂) (T₂ , T₂ , T₁) = refl
distribˡ-γ (T₁ , T₂ , T₂) (T₂ , T₂ , T₂) = refl
distribˡ-γ (T₂ , T₀ , T₀) (T₀ , T₀ , T₀) = refl
distribˡ-γ (T₂ , T₀ , T₀) (T₀ , T₀ , T₁) = refl
distribˡ-γ (T₂ , T₀ , T₀) (T₀ , T₀ , T₂) = refl
distribˡ-γ (T₂ , T₀ , T₀) (T₀ , T₁ , T₀) = refl
distribˡ-γ (T₂ , T₀ , T₀) (T₀ , T₁ , T₁) = refl
distribˡ-γ (T₂ , T₀ , T₀) (T₀ , T₁ , T₂) = refl
distribˡ-γ (T₂ , T₀ , T₀) (T₀ , T₂ , T₀) = refl
distribˡ-γ (T₂ , T₀ , T₀) (T₀ , T₂ , T₁) = refl
distribˡ-γ (T₂ , T₀ , T₀) (T₀ , T₂ , T₂) = refl
distribˡ-γ (T₂ , T₀ , T₀) (T₁ , T₀ , T₀) = refl
distribˡ-γ (T₂ , T₀ , T₀) (T₁ , T₀ , T₁) = refl
distribˡ-γ (T₂ , T₀ , T₀) (T₁ , T₀ , T₂) = refl
distribˡ-γ (T₂ , T₀ , T₀) (T₁ , T₁ , T₀) = refl
distribˡ-γ (T₂ , T₀ , T₀) (T₁ , T₁ , T₁) = refl
distribˡ-γ (T₂ , T₀ , T₀) (T₁ , T₁ , T₂) = refl
distribˡ-γ (T₂ , T₀ , T₀) (T₁ , T₂ , T₀) = refl
distribˡ-γ (T₂ , T₀ , T₀) (T₁ , T₂ , T₁) = refl
distribˡ-γ (T₂ , T₀ , T₀) (T₁ , T₂ , T₂) = refl
distribˡ-γ (T₂ , T₀ , T₀) (T₂ , T₀ , T₀) = refl
distribˡ-γ (T₂ , T₀ , T₀) (T₂ , T₀ , T₁) = refl
distribˡ-γ (T₂ , T₀ , T₀) (T₂ , T₀ , T₂) = refl
distribˡ-γ (T₂ , T₀ , T₀) (T₂ , T₁ , T₀) = refl
distribˡ-γ (T₂ , T₀ , T₀) (T₂ , T₁ , T₁) = refl
distribˡ-γ (T₂ , T₀ , T₀) (T₂ , T₁ , T₂) = refl
distribˡ-γ (T₂ , T₀ , T₀) (T₂ , T₂ , T₀) = refl
distribˡ-γ (T₂ , T₀ , T₀) (T₂ , T₂ , T₁) = refl
distribˡ-γ (T₂ , T₀ , T₀) (T₂ , T₂ , T₂) = refl
distribˡ-γ (T₂ , T₀ , T₁) (T₀ , T₀ , T₀) = refl
distribˡ-γ (T₂ , T₀ , T₁) (T₀ , T₀ , T₁) = refl
distribˡ-γ (T₂ , T₀ , T₁) (T₀ , T₀ , T₂) = refl
distribˡ-γ (T₂ , T₀ , T₁) (T₀ , T₁ , T₀) = refl
distribˡ-γ (T₂ , T₀ , T₁) (T₀ , T₁ , T₁) = refl
distribˡ-γ (T₂ , T₀ , T₁) (T₀ , T₁ , T₂) = refl
distribˡ-γ (T₂ , T₀ , T₁) (T₀ , T₂ , T₀) = refl
distribˡ-γ (T₂ , T₀ , T₁) (T₀ , T₂ , T₁) = refl
distribˡ-γ (T₂ , T₀ , T₁) (T₀ , T₂ , T₂) = refl
distribˡ-γ (T₂ , T₀ , T₁) (T₁ , T₀ , T₀) = refl
distribˡ-γ (T₂ , T₀ , T₁) (T₁ , T₀ , T₁) = refl
distribˡ-γ (T₂ , T₀ , T₁) (T₁ , T₀ , T₂) = refl
distribˡ-γ (T₂ , T₀ , T₁) (T₁ , T₁ , T₀) = refl
distribˡ-γ (T₂ , T₀ , T₁) (T₁ , T₁ , T₁) = refl
distribˡ-γ (T₂ , T₀ , T₁) (T₁ , T₁ , T₂) = refl
distribˡ-γ (T₂ , T₀ , T₁) (T₁ , T₂ , T₀) = refl
distribˡ-γ (T₂ , T₀ , T₁) (T₁ , T₂ , T₁) = refl
distribˡ-γ (T₂ , T₀ , T₁) (T₁ , T₂ , T₂) = refl
distribˡ-γ (T₂ , T₀ , T₁) (T₂ , T₀ , T₀) = refl
distribˡ-γ (T₂ , T₀ , T₁) (T₂ , T₀ , T₁) = refl
distribˡ-γ (T₂ , T₀ , T₁) (T₂ , T₀ , T₂) = refl
distribˡ-γ (T₂ , T₀ , T₁) (T₂ , T₁ , T₀) = refl
distribˡ-γ (T₂ , T₀ , T₁) (T₂ , T₁ , T₁) = refl
distribˡ-γ (T₂ , T₀ , T₁) (T₂ , T₁ , T₂) = refl
distribˡ-γ (T₂ , T₀ , T₁) (T₂ , T₂ , T₀) = refl
distribˡ-γ (T₂ , T₀ , T₁) (T₂ , T₂ , T₁) = refl
distribˡ-γ (T₂ , T₀ , T₁) (T₂ , T₂ , T₂) = refl
distribˡ-γ (T₂ , T₀ , T₂) (T₀ , T₀ , T₀) = refl
distribˡ-γ (T₂ , T₀ , T₂) (T₀ , T₀ , T₁) = refl
distribˡ-γ (T₂ , T₀ , T₂) (T₀ , T₀ , T₂) = refl
distribˡ-γ (T₂ , T₀ , T₂) (T₀ , T₁ , T₀) = refl
distribˡ-γ (T₂ , T₀ , T₂) (T₀ , T₁ , T₁) = refl
distribˡ-γ (T₂ , T₀ , T₂) (T₀ , T₁ , T₂) = refl
distribˡ-γ (T₂ , T₀ , T₂) (T₀ , T₂ , T₀) = refl
distribˡ-γ (T₂ , T₀ , T₂) (T₀ , T₂ , T₁) = refl
distribˡ-γ (T₂ , T₀ , T₂) (T₀ , T₂ , T₂) = refl
distribˡ-γ (T₂ , T₀ , T₂) (T₁ , T₀ , T₀) = refl
distribˡ-γ (T₂ , T₀ , T₂) (T₁ , T₀ , T₁) = refl
distribˡ-γ (T₂ , T₀ , T₂) (T₁ , T₀ , T₂) = refl
distribˡ-γ (T₂ , T₀ , T₂) (T₁ , T₁ , T₀) = refl
distribˡ-γ (T₂ , T₀ , T₂) (T₁ , T₁ , T₁) = refl
distribˡ-γ (T₂ , T₀ , T₂) (T₁ , T₁ , T₂) = refl
distribˡ-γ (T₂ , T₀ , T₂) (T₁ , T₂ , T₀) = refl
distribˡ-γ (T₂ , T₀ , T₂) (T₁ , T₂ , T₁) = refl
distribˡ-γ (T₂ , T₀ , T₂) (T₁ , T₂ , T₂) = refl
distribˡ-γ (T₂ , T₀ , T₂) (T₂ , T₀ , T₀) = refl
distribˡ-γ (T₂ , T₀ , T₂) (T₂ , T₀ , T₁) = refl
distribˡ-γ (T₂ , T₀ , T₂) (T₂ , T₀ , T₂) = refl
distribˡ-γ (T₂ , T₀ , T₂) (T₂ , T₁ , T₀) = refl
distribˡ-γ (T₂ , T₀ , T₂) (T₂ , T₁ , T₁) = refl
distribˡ-γ (T₂ , T₀ , T₂) (T₂ , T₁ , T₂) = refl
distribˡ-γ (T₂ , T₀ , T₂) (T₂ , T₂ , T₀) = refl
distribˡ-γ (T₂ , T₀ , T₂) (T₂ , T₂ , T₁) = refl
distribˡ-γ (T₂ , T₀ , T₂) (T₂ , T₂ , T₂) = refl
distribˡ-γ (T₂ , T₁ , T₀) (T₀ , T₀ , T₀) = refl
distribˡ-γ (T₂ , T₁ , T₀) (T₀ , T₀ , T₁) = refl
distribˡ-γ (T₂ , T₁ , T₀) (T₀ , T₀ , T₂) = refl
distribˡ-γ (T₂ , T₁ , T₀) (T₀ , T₁ , T₀) = refl
distribˡ-γ (T₂ , T₁ , T₀) (T₀ , T₁ , T₁) = refl
distribˡ-γ (T₂ , T₁ , T₀) (T₀ , T₁ , T₂) = refl
distribˡ-γ (T₂ , T₁ , T₀) (T₀ , T₂ , T₀) = refl
distribˡ-γ (T₂ , T₁ , T₀) (T₀ , T₂ , T₁) = refl
distribˡ-γ (T₂ , T₁ , T₀) (T₀ , T₂ , T₂) = refl
distribˡ-γ (T₂ , T₁ , T₀) (T₁ , T₀ , T₀) = refl
distribˡ-γ (T₂ , T₁ , T₀) (T₁ , T₀ , T₁) = refl
distribˡ-γ (T₂ , T₁ , T₀) (T₁ , T₀ , T₂) = refl
distribˡ-γ (T₂ , T₁ , T₀) (T₁ , T₁ , T₀) = refl
distribˡ-γ (T₂ , T₁ , T₀) (T₁ , T₁ , T₁) = refl
distribˡ-γ (T₂ , T₁ , T₀) (T₁ , T₁ , T₂) = refl
distribˡ-γ (T₂ , T₁ , T₀) (T₁ , T₂ , T₀) = refl
distribˡ-γ (T₂ , T₁ , T₀) (T₁ , T₂ , T₁) = refl
distribˡ-γ (T₂ , T₁ , T₀) (T₁ , T₂ , T₂) = refl
distribˡ-γ (T₂ , T₁ , T₀) (T₂ , T₀ , T₀) = refl
distribˡ-γ (T₂ , T₁ , T₀) (T₂ , T₀ , T₁) = refl
distribˡ-γ (T₂ , T₁ , T₀) (T₂ , T₀ , T₂) = refl
distribˡ-γ (T₂ , T₁ , T₀) (T₂ , T₁ , T₀) = refl
distribˡ-γ (T₂ , T₁ , T₀) (T₂ , T₁ , T₁) = refl
distribˡ-γ (T₂ , T₁ , T₀) (T₂ , T₁ , T₂) = refl
distribˡ-γ (T₂ , T₁ , T₀) (T₂ , T₂ , T₀) = refl
distribˡ-γ (T₂ , T₁ , T₀) (T₂ , T₂ , T₁) = refl
distribˡ-γ (T₂ , T₁ , T₀) (T₂ , T₂ , T₂) = refl
distribˡ-γ (T₂ , T₁ , T₁) (T₀ , T₀ , T₀) = refl
distribˡ-γ (T₂ , T₁ , T₁) (T₀ , T₀ , T₁) = refl
distribˡ-γ (T₂ , T₁ , T₁) (T₀ , T₀ , T₂) = refl
distribˡ-γ (T₂ , T₁ , T₁) (T₀ , T₁ , T₀) = refl
distribˡ-γ (T₂ , T₁ , T₁) (T₀ , T₁ , T₁) = refl
distribˡ-γ (T₂ , T₁ , T₁) (T₀ , T₁ , T₂) = refl
distribˡ-γ (T₂ , T₁ , T₁) (T₀ , T₂ , T₀) = refl
distribˡ-γ (T₂ , T₁ , T₁) (T₀ , T₂ , T₁) = refl
distribˡ-γ (T₂ , T₁ , T₁) (T₀ , T₂ , T₂) = refl
distribˡ-γ (T₂ , T₁ , T₁) (T₁ , T₀ , T₀) = refl
distribˡ-γ (T₂ , T₁ , T₁) (T₁ , T₀ , T₁) = refl
distribˡ-γ (T₂ , T₁ , T₁) (T₁ , T₀ , T₂) = refl
distribˡ-γ (T₂ , T₁ , T₁) (T₁ , T₁ , T₀) = refl
distribˡ-γ (T₂ , T₁ , T₁) (T₁ , T₁ , T₁) = refl
distribˡ-γ (T₂ , T₁ , T₁) (T₁ , T₁ , T₂) = refl
distribˡ-γ (T₂ , T₁ , T₁) (T₁ , T₂ , T₀) = refl
distribˡ-γ (T₂ , T₁ , T₁) (T₁ , T₂ , T₁) = refl
distribˡ-γ (T₂ , T₁ , T₁) (T₁ , T₂ , T₂) = refl
distribˡ-γ (T₂ , T₁ , T₁) (T₂ , T₀ , T₀) = refl
distribˡ-γ (T₂ , T₁ , T₁) (T₂ , T₀ , T₁) = refl
distribˡ-γ (T₂ , T₁ , T₁) (T₂ , T₀ , T₂) = refl
distribˡ-γ (T₂ , T₁ , T₁) (T₂ , T₁ , T₀) = refl
distribˡ-γ (T₂ , T₁ , T₁) (T₂ , T₁ , T₁) = refl
distribˡ-γ (T₂ , T₁ , T₁) (T₂ , T₁ , T₂) = refl
distribˡ-γ (T₂ , T₁ , T₁) (T₂ , T₂ , T₀) = refl
distribˡ-γ (T₂ , T₁ , T₁) (T₂ , T₂ , T₁) = refl
distribˡ-γ (T₂ , T₁ , T₁) (T₂ , T₂ , T₂) = refl
distribˡ-γ (T₂ , T₁ , T₂) (T₀ , T₀ , T₀) = refl
distribˡ-γ (T₂ , T₁ , T₂) (T₀ , T₀ , T₁) = refl
distribˡ-γ (T₂ , T₁ , T₂) (T₀ , T₀ , T₂) = refl
distribˡ-γ (T₂ , T₁ , T₂) (T₀ , T₁ , T₀) = refl
distribˡ-γ (T₂ , T₁ , T₂) (T₀ , T₁ , T₁) = refl
distribˡ-γ (T₂ , T₁ , T₂) (T₀ , T₁ , T₂) = refl
distribˡ-γ (T₂ , T₁ , T₂) (T₀ , T₂ , T₀) = refl
distribˡ-γ (T₂ , T₁ , T₂) (T₀ , T₂ , T₁) = refl
distribˡ-γ (T₂ , T₁ , T₂) (T₀ , T₂ , T₂) = refl
distribˡ-γ (T₂ , T₁ , T₂) (T₁ , T₀ , T₀) = refl
distribˡ-γ (T₂ , T₁ , T₂) (T₁ , T₀ , T₁) = refl
distribˡ-γ (T₂ , T₁ , T₂) (T₁ , T₀ , T₂) = refl
distribˡ-γ (T₂ , T₁ , T₂) (T₁ , T₁ , T₀) = refl
distribˡ-γ (T₂ , T₁ , T₂) (T₁ , T₁ , T₁) = refl
distribˡ-γ (T₂ , T₁ , T₂) (T₁ , T₁ , T₂) = refl
distribˡ-γ (T₂ , T₁ , T₂) (T₁ , T₂ , T₀) = refl
distribˡ-γ (T₂ , T₁ , T₂) (T₁ , T₂ , T₁) = refl
distribˡ-γ (T₂ , T₁ , T₂) (T₁ , T₂ , T₂) = refl
distribˡ-γ (T₂ , T₁ , T₂) (T₂ , T₀ , T₀) = refl
distribˡ-γ (T₂ , T₁ , T₂) (T₂ , T₀ , T₁) = refl
distribˡ-γ (T₂ , T₁ , T₂) (T₂ , T₀ , T₂) = refl
distribˡ-γ (T₂ , T₁ , T₂) (T₂ , T₁ , T₀) = refl
distribˡ-γ (T₂ , T₁ , T₂) (T₂ , T₁ , T₁) = refl
distribˡ-γ (T₂ , T₁ , T₂) (T₂ , T₁ , T₂) = refl
distribˡ-γ (T₂ , T₁ , T₂) (T₂ , T₂ , T₀) = refl
distribˡ-γ (T₂ , T₁ , T₂) (T₂ , T₂ , T₁) = refl
distribˡ-γ (T₂ , T₁ , T₂) (T₂ , T₂ , T₂) = refl
distribˡ-γ (T₂ , T₂ , T₀) (T₀ , T₀ , T₀) = refl
distribˡ-γ (T₂ , T₂ , T₀) (T₀ , T₀ , T₁) = refl
distribˡ-γ (T₂ , T₂ , T₀) (T₀ , T₀ , T₂) = refl
distribˡ-γ (T₂ , T₂ , T₀) (T₀ , T₁ , T₀) = refl
distribˡ-γ (T₂ , T₂ , T₀) (T₀ , T₁ , T₁) = refl
distribˡ-γ (T₂ , T₂ , T₀) (T₀ , T₁ , T₂) = refl
distribˡ-γ (T₂ , T₂ , T₀) (T₀ , T₂ , T₀) = refl
distribˡ-γ (T₂ , T₂ , T₀) (T₀ , T₂ , T₁) = refl
distribˡ-γ (T₂ , T₂ , T₀) (T₀ , T₂ , T₂) = refl
distribˡ-γ (T₂ , T₂ , T₀) (T₁ , T₀ , T₀) = refl
distribˡ-γ (T₂ , T₂ , T₀) (T₁ , T₀ , T₁) = refl
distribˡ-γ (T₂ , T₂ , T₀) (T₁ , T₀ , T₂) = refl
distribˡ-γ (T₂ , T₂ , T₀) (T₁ , T₁ , T₀) = refl
distribˡ-γ (T₂ , T₂ , T₀) (T₁ , T₁ , T₁) = refl
distribˡ-γ (T₂ , T₂ , T₀) (T₁ , T₁ , T₂) = refl
distribˡ-γ (T₂ , T₂ , T₀) (T₁ , T₂ , T₀) = refl
distribˡ-γ (T₂ , T₂ , T₀) (T₁ , T₂ , T₁) = refl
distribˡ-γ (T₂ , T₂ , T₀) (T₁ , T₂ , T₂) = refl
distribˡ-γ (T₂ , T₂ , T₀) (T₂ , T₀ , T₀) = refl
distribˡ-γ (T₂ , T₂ , T₀) (T₂ , T₀ , T₁) = refl
distribˡ-γ (T₂ , T₂ , T₀) (T₂ , T₀ , T₂) = refl
distribˡ-γ (T₂ , T₂ , T₀) (T₂ , T₁ , T₀) = refl
distribˡ-γ (T₂ , T₂ , T₀) (T₂ , T₁ , T₁) = refl
distribˡ-γ (T₂ , T₂ , T₀) (T₂ , T₁ , T₂) = refl
distribˡ-γ (T₂ , T₂ , T₀) (T₂ , T₂ , T₀) = refl
distribˡ-γ (T₂ , T₂ , T₀) (T₂ , T₂ , T₁) = refl
distribˡ-γ (T₂ , T₂ , T₀) (T₂ , T₂ , T₂) = refl
distribˡ-γ (T₂ , T₂ , T₁) (T₀ , T₀ , T₀) = refl
distribˡ-γ (T₂ , T₂ , T₁) (T₀ , T₀ , T₁) = refl
distribˡ-γ (T₂ , T₂ , T₁) (T₀ , T₀ , T₂) = refl
distribˡ-γ (T₂ , T₂ , T₁) (T₀ , T₁ , T₀) = refl
distribˡ-γ (T₂ , T₂ , T₁) (T₀ , T₁ , T₁) = refl
distribˡ-γ (T₂ , T₂ , T₁) (T₀ , T₁ , T₂) = refl
distribˡ-γ (T₂ , T₂ , T₁) (T₀ , T₂ , T₀) = refl
distribˡ-γ (T₂ , T₂ , T₁) (T₀ , T₂ , T₁) = refl
distribˡ-γ (T₂ , T₂ , T₁) (T₀ , T₂ , T₂) = refl
distribˡ-γ (T₂ , T₂ , T₁) (T₁ , T₀ , T₀) = refl
distribˡ-γ (T₂ , T₂ , T₁) (T₁ , T₀ , T₁) = refl
distribˡ-γ (T₂ , T₂ , T₁) (T₁ , T₀ , T₂) = refl
distribˡ-γ (T₂ , T₂ , T₁) (T₁ , T₁ , T₀) = refl
distribˡ-γ (T₂ , T₂ , T₁) (T₁ , T₁ , T₁) = refl
distribˡ-γ (T₂ , T₂ , T₁) (T₁ , T₁ , T₂) = refl
distribˡ-γ (T₂ , T₂ , T₁) (T₁ , T₂ , T₀) = refl
distribˡ-γ (T₂ , T₂ , T₁) (T₁ , T₂ , T₁) = refl
distribˡ-γ (T₂ , T₂ , T₁) (T₁ , T₂ , T₂) = refl
distribˡ-γ (T₂ , T₂ , T₁) (T₂ , T₀ , T₀) = refl
distribˡ-γ (T₂ , T₂ , T₁) (T₂ , T₀ , T₁) = refl
distribˡ-γ (T₂ , T₂ , T₁) (T₂ , T₀ , T₂) = refl
distribˡ-γ (T₂ , T₂ , T₁) (T₂ , T₁ , T₀) = refl
distribˡ-γ (T₂ , T₂ , T₁) (T₂ , T₁ , T₁) = refl
distribˡ-γ (T₂ , T₂ , T₁) (T₂ , T₁ , T₂) = refl
distribˡ-γ (T₂ , T₂ , T₁) (T₂ , T₂ , T₀) = refl
distribˡ-γ (T₂ , T₂ , T₁) (T₂ , T₂ , T₁) = refl
distribˡ-γ (T₂ , T₂ , T₁) (T₂ , T₂ , T₂) = refl
distribˡ-γ (T₂ , T₂ , T₂) (T₀ , T₀ , T₀) = refl
distribˡ-γ (T₂ , T₂ , T₂) (T₀ , T₀ , T₁) = refl
distribˡ-γ (T₂ , T₂ , T₂) (T₀ , T₀ , T₂) = refl
distribˡ-γ (T₂ , T₂ , T₂) (T₀ , T₁ , T₀) = refl
distribˡ-γ (T₂ , T₂ , T₂) (T₀ , T₁ , T₁) = refl
distribˡ-γ (T₂ , T₂ , T₂) (T₀ , T₁ , T₂) = refl
distribˡ-γ (T₂ , T₂ , T₂) (T₀ , T₂ , T₀) = refl
distribˡ-γ (T₂ , T₂ , T₂) (T₀ , T₂ , T₁) = refl
distribˡ-γ (T₂ , T₂ , T₂) (T₀ , T₂ , T₂) = refl
distribˡ-γ (T₂ , T₂ , T₂) (T₁ , T₀ , T₀) = refl
distribˡ-γ (T₂ , T₂ , T₂) (T₁ , T₀ , T₁) = refl
distribˡ-γ (T₂ , T₂ , T₂) (T₁ , T₀ , T₂) = refl
distribˡ-γ (T₂ , T₂ , T₂) (T₁ , T₁ , T₀) = refl
distribˡ-γ (T₂ , T₂ , T₂) (T₁ , T₁ , T₁) = refl
distribˡ-γ (T₂ , T₂ , T₂) (T₁ , T₁ , T₂) = refl
distribˡ-γ (T₂ , T₂ , T₂) (T₁ , T₂ , T₀) = refl
distribˡ-γ (T₂ , T₂ , T₂) (T₁ , T₂ , T₁) = refl
distribˡ-γ (T₂ , T₂ , T₂) (T₁ , T₂ , T₂) = refl
distribˡ-γ (T₂ , T₂ , T₂) (T₂ , T₀ , T₀) = refl
distribˡ-γ (T₂ , T₂ , T₂) (T₂ , T₀ , T₁) = refl
distribˡ-γ (T₂ , T₂ , T₂) (T₂ , T₀ , T₂) = refl
distribˡ-γ (T₂ , T₂ , T₂) (T₂ , T₁ , T₀) = refl
distribˡ-γ (T₂ , T₂ , T₂) (T₂ , T₁ , T₁) = refl
distribˡ-γ (T₂ , T₂ , T₂) (T₂ , T₁ , T₂) = refl
distribˡ-γ (T₂ , T₂ , T₂) (T₂ , T₂ , T₀) = refl
distribˡ-γ (T₂ , T₂ , T₂) (T₂ , T₂ , T₁) = refl
distribˡ-γ (T₂ , T₂ , T₂) (T₂ , T₂ , T₂) = refl

-- γ 右分配: (x+y)·γ = x·γ + y·γ
distribʳ-γ : ∀ x y → (x +₉ y) *₉ γ ≡ (x *₉ γ) +₉ (y *₉ γ)
distribʳ-γ (T₀ , T₀ , T₀) (T₀ , T₀ , T₀) = refl
distribʳ-γ (T₀ , T₀ , T₀) (T₀ , T₀ , T₁) = refl
distribʳ-γ (T₀ , T₀ , T₀) (T₀ , T₀ , T₂) = refl
distribʳ-γ (T₀ , T₀ , T₀) (T₀ , T₁ , T₀) = refl
distribʳ-γ (T₀ , T₀ , T₀) (T₀ , T₁ , T₁) = refl
distribʳ-γ (T₀ , T₀ , T₀) (T₀ , T₁ , T₂) = refl
distribʳ-γ (T₀ , T₀ , T₀) (T₀ , T₂ , T₀) = refl
distribʳ-γ (T₀ , T₀ , T₀) (T₀ , T₂ , T₁) = refl
distribʳ-γ (T₀ , T₀ , T₀) (T₀ , T₂ , T₂) = refl
distribʳ-γ (T₀ , T₀ , T₀) (T₁ , T₀ , T₀) = refl
distribʳ-γ (T₀ , T₀ , T₀) (T₁ , T₀ , T₁) = refl
distribʳ-γ (T₀ , T₀ , T₀) (T₁ , T₀ , T₂) = refl
distribʳ-γ (T₀ , T₀ , T₀) (T₁ , T₁ , T₀) = refl
distribʳ-γ (T₀ , T₀ , T₀) (T₁ , T₁ , T₁) = refl
distribʳ-γ (T₀ , T₀ , T₀) (T₁ , T₁ , T₂) = refl
distribʳ-γ (T₀ , T₀ , T₀) (T₁ , T₂ , T₀) = refl
distribʳ-γ (T₀ , T₀ , T₀) (T₁ , T₂ , T₁) = refl
distribʳ-γ (T₀ , T₀ , T₀) (T₁ , T₂ , T₂) = refl
distribʳ-γ (T₀ , T₀ , T₀) (T₂ , T₀ , T₀) = refl
distribʳ-γ (T₀ , T₀ , T₀) (T₂ , T₀ , T₁) = refl
distribʳ-γ (T₀ , T₀ , T₀) (T₂ , T₀ , T₂) = refl
distribʳ-γ (T₀ , T₀ , T₀) (T₂ , T₁ , T₀) = refl
distribʳ-γ (T₀ , T₀ , T₀) (T₂ , T₁ , T₁) = refl
distribʳ-γ (T₀ , T₀ , T₀) (T₂ , T₁ , T₂) = refl
distribʳ-γ (T₀ , T₀ , T₀) (T₂ , T₂ , T₀) = refl
distribʳ-γ (T₀ , T₀ , T₀) (T₂ , T₂ , T₁) = refl
distribʳ-γ (T₀ , T₀ , T₀) (T₂ , T₂ , T₂) = refl
distribʳ-γ (T₀ , T₀ , T₁) (T₀ , T₀ , T₀) = refl
distribʳ-γ (T₀ , T₀ , T₁) (T₀ , T₀ , T₁) = refl
distribʳ-γ (T₀ , T₀ , T₁) (T₀ , T₀ , T₂) = refl
distribʳ-γ (T₀ , T₀ , T₁) (T₀ , T₁ , T₀) = refl
distribʳ-γ (T₀ , T₀ , T₁) (T₀ , T₁ , T₁) = refl
distribʳ-γ (T₀ , T₀ , T₁) (T₀ , T₁ , T₂) = refl
distribʳ-γ (T₀ , T₀ , T₁) (T₀ , T₂ , T₀) = refl
distribʳ-γ (T₀ , T₀ , T₁) (T₀ , T₂ , T₁) = refl
distribʳ-γ (T₀ , T₀ , T₁) (T₀ , T₂ , T₂) = refl
distribʳ-γ (T₀ , T₀ , T₁) (T₁ , T₀ , T₀) = refl
distribʳ-γ (T₀ , T₀ , T₁) (T₁ , T₀ , T₁) = refl
distribʳ-γ (T₀ , T₀ , T₁) (T₁ , T₀ , T₂) = refl
distribʳ-γ (T₀ , T₀ , T₁) (T₁ , T₁ , T₀) = refl
distribʳ-γ (T₀ , T₀ , T₁) (T₁ , T₁ , T₁) = refl
distribʳ-γ (T₀ , T₀ , T₁) (T₁ , T₁ , T₂) = refl
distribʳ-γ (T₀ , T₀ , T₁) (T₁ , T₂ , T₀) = refl
distribʳ-γ (T₀ , T₀ , T₁) (T₁ , T₂ , T₁) = refl
distribʳ-γ (T₀ , T₀ , T₁) (T₁ , T₂ , T₂) = refl
distribʳ-γ (T₀ , T₀ , T₁) (T₂ , T₀ , T₀) = refl
distribʳ-γ (T₀ , T₀ , T₁) (T₂ , T₀ , T₁) = refl
distribʳ-γ (T₀ , T₀ , T₁) (T₂ , T₀ , T₂) = refl
distribʳ-γ (T₀ , T₀ , T₁) (T₂ , T₁ , T₀) = refl
distribʳ-γ (T₀ , T₀ , T₁) (T₂ , T₁ , T₁) = refl
distribʳ-γ (T₀ , T₀ , T₁) (T₂ , T₁ , T₂) = refl
distribʳ-γ (T₀ , T₀ , T₁) (T₂ , T₂ , T₀) = refl
distribʳ-γ (T₀ , T₀ , T₁) (T₂ , T₂ , T₁) = refl
distribʳ-γ (T₀ , T₀ , T₁) (T₂ , T₂ , T₂) = refl
distribʳ-γ (T₀ , T₀ , T₂) (T₀ , T₀ , T₀) = refl
distribʳ-γ (T₀ , T₀ , T₂) (T₀ , T₀ , T₁) = refl
distribʳ-γ (T₀ , T₀ , T₂) (T₀ , T₀ , T₂) = refl
distribʳ-γ (T₀ , T₀ , T₂) (T₀ , T₁ , T₀) = refl
distribʳ-γ (T₀ , T₀ , T₂) (T₀ , T₁ , T₁) = refl
distribʳ-γ (T₀ , T₀ , T₂) (T₀ , T₁ , T₂) = refl
distribʳ-γ (T₀ , T₀ , T₂) (T₀ , T₂ , T₀) = refl
distribʳ-γ (T₀ , T₀ , T₂) (T₀ , T₂ , T₁) = refl
distribʳ-γ (T₀ , T₀ , T₂) (T₀ , T₂ , T₂) = refl
distribʳ-γ (T₀ , T₀ , T₂) (T₁ , T₀ , T₀) = refl
distribʳ-γ (T₀ , T₀ , T₂) (T₁ , T₀ , T₁) = refl
distribʳ-γ (T₀ , T₀ , T₂) (T₁ , T₀ , T₂) = refl
distribʳ-γ (T₀ , T₀ , T₂) (T₁ , T₁ , T₀) = refl
distribʳ-γ (T₀ , T₀ , T₂) (T₁ , T₁ , T₁) = refl
distribʳ-γ (T₀ , T₀ , T₂) (T₁ , T₁ , T₂) = refl
distribʳ-γ (T₀ , T₀ , T₂) (T₁ , T₂ , T₀) = refl
distribʳ-γ (T₀ , T₀ , T₂) (T₁ , T₂ , T₁) = refl
distribʳ-γ (T₀ , T₀ , T₂) (T₁ , T₂ , T₂) = refl
distribʳ-γ (T₀ , T₀ , T₂) (T₂ , T₀ , T₀) = refl
distribʳ-γ (T₀ , T₀ , T₂) (T₂ , T₀ , T₁) = refl
distribʳ-γ (T₀ , T₀ , T₂) (T₂ , T₀ , T₂) = refl
distribʳ-γ (T₀ , T₀ , T₂) (T₂ , T₁ , T₀) = refl
distribʳ-γ (T₀ , T₀ , T₂) (T₂ , T₁ , T₁) = refl
distribʳ-γ (T₀ , T₀ , T₂) (T₂ , T₁ , T₂) = refl
distribʳ-γ (T₀ , T₀ , T₂) (T₂ , T₂ , T₀) = refl
distribʳ-γ (T₀ , T₀ , T₂) (T₂ , T₂ , T₁) = refl
distribʳ-γ (T₀ , T₀ , T₂) (T₂ , T₂ , T₂) = refl
distribʳ-γ (T₀ , T₁ , T₀) (T₀ , T₀ , T₀) = refl
distribʳ-γ (T₀ , T₁ , T₀) (T₀ , T₀ , T₁) = refl
distribʳ-γ (T₀ , T₁ , T₀) (T₀ , T₀ , T₂) = refl
distribʳ-γ (T₀ , T₁ , T₀) (T₀ , T₁ , T₀) = refl
distribʳ-γ (T₀ , T₁ , T₀) (T₀ , T₁ , T₁) = refl
distribʳ-γ (T₀ , T₁ , T₀) (T₀ , T₁ , T₂) = refl
distribʳ-γ (T₀ , T₁ , T₀) (T₀ , T₂ , T₀) = refl
distribʳ-γ (T₀ , T₁ , T₀) (T₀ , T₂ , T₁) = refl
distribʳ-γ (T₀ , T₁ , T₀) (T₀ , T₂ , T₂) = refl
distribʳ-γ (T₀ , T₁ , T₀) (T₁ , T₀ , T₀) = refl
distribʳ-γ (T₀ , T₁ , T₀) (T₁ , T₀ , T₁) = refl
distribʳ-γ (T₀ , T₁ , T₀) (T₁ , T₀ , T₂) = refl
distribʳ-γ (T₀ , T₁ , T₀) (T₁ , T₁ , T₀) = refl
distribʳ-γ (T₀ , T₁ , T₀) (T₁ , T₁ , T₁) = refl
distribʳ-γ (T₀ , T₁ , T₀) (T₁ , T₁ , T₂) = refl
distribʳ-γ (T₀ , T₁ , T₀) (T₁ , T₂ , T₀) = refl
distribʳ-γ (T₀ , T₁ , T₀) (T₁ , T₂ , T₁) = refl
distribʳ-γ (T₀ , T₁ , T₀) (T₁ , T₂ , T₂) = refl
distribʳ-γ (T₀ , T₁ , T₀) (T₂ , T₀ , T₀) = refl
distribʳ-γ (T₀ , T₁ , T₀) (T₂ , T₀ , T₁) = refl
distribʳ-γ (T₀ , T₁ , T₀) (T₂ , T₀ , T₂) = refl
distribʳ-γ (T₀ , T₁ , T₀) (T₂ , T₁ , T₀) = refl
distribʳ-γ (T₀ , T₁ , T₀) (T₂ , T₁ , T₁) = refl
distribʳ-γ (T₀ , T₁ , T₀) (T₂ , T₁ , T₂) = refl
distribʳ-γ (T₀ , T₁ , T₀) (T₂ , T₂ , T₀) = refl
distribʳ-γ (T₀ , T₁ , T₀) (T₂ , T₂ , T₁) = refl
distribʳ-γ (T₀ , T₁ , T₀) (T₂ , T₂ , T₂) = refl
distribʳ-γ (T₀ , T₁ , T₁) (T₀ , T₀ , T₀) = refl
distribʳ-γ (T₀ , T₁ , T₁) (T₀ , T₀ , T₁) = refl
distribʳ-γ (T₀ , T₁ , T₁) (T₀ , T₀ , T₂) = refl
distribʳ-γ (T₀ , T₁ , T₁) (T₀ , T₁ , T₀) = refl
distribʳ-γ (T₀ , T₁ , T₁) (T₀ , T₁ , T₁) = refl
distribʳ-γ (T₀ , T₁ , T₁) (T₀ , T₁ , T₂) = refl
distribʳ-γ (T₀ , T₁ , T₁) (T₀ , T₂ , T₀) = refl
distribʳ-γ (T₀ , T₁ , T₁) (T₀ , T₂ , T₁) = refl
distribʳ-γ (T₀ , T₁ , T₁) (T₀ , T₂ , T₂) = refl
distribʳ-γ (T₀ , T₁ , T₁) (T₁ , T₀ , T₀) = refl
distribʳ-γ (T₀ , T₁ , T₁) (T₁ , T₀ , T₁) = refl
distribʳ-γ (T₀ , T₁ , T₁) (T₁ , T₀ , T₂) = refl
distribʳ-γ (T₀ , T₁ , T₁) (T₁ , T₁ , T₀) = refl
distribʳ-γ (T₀ , T₁ , T₁) (T₁ , T₁ , T₁) = refl
distribʳ-γ (T₀ , T₁ , T₁) (T₁ , T₁ , T₂) = refl
distribʳ-γ (T₀ , T₁ , T₁) (T₁ , T₂ , T₀) = refl
distribʳ-γ (T₀ , T₁ , T₁) (T₁ , T₂ , T₁) = refl
distribʳ-γ (T₀ , T₁ , T₁) (T₁ , T₂ , T₂) = refl
distribʳ-γ (T₀ , T₁ , T₁) (T₂ , T₀ , T₀) = refl
distribʳ-γ (T₀ , T₁ , T₁) (T₂ , T₀ , T₁) = refl
distribʳ-γ (T₀ , T₁ , T₁) (T₂ , T₀ , T₂) = refl
distribʳ-γ (T₀ , T₁ , T₁) (T₂ , T₁ , T₀) = refl
distribʳ-γ (T₀ , T₁ , T₁) (T₂ , T₁ , T₁) = refl
distribʳ-γ (T₀ , T₁ , T₁) (T₂ , T₁ , T₂) = refl
distribʳ-γ (T₀ , T₁ , T₁) (T₂ , T₂ , T₀) = refl
distribʳ-γ (T₀ , T₁ , T₁) (T₂ , T₂ , T₁) = refl
distribʳ-γ (T₀ , T₁ , T₁) (T₂ , T₂ , T₂) = refl
distribʳ-γ (T₀ , T₁ , T₂) (T₀ , T₀ , T₀) = refl
distribʳ-γ (T₀ , T₁ , T₂) (T₀ , T₀ , T₁) = refl
distribʳ-γ (T₀ , T₁ , T₂) (T₀ , T₀ , T₂) = refl
distribʳ-γ (T₀ , T₁ , T₂) (T₀ , T₁ , T₀) = refl
distribʳ-γ (T₀ , T₁ , T₂) (T₀ , T₁ , T₁) = refl
distribʳ-γ (T₀ , T₁ , T₂) (T₀ , T₁ , T₂) = refl
distribʳ-γ (T₀ , T₁ , T₂) (T₀ , T₂ , T₀) = refl
distribʳ-γ (T₀ , T₁ , T₂) (T₀ , T₂ , T₁) = refl
distribʳ-γ (T₀ , T₁ , T₂) (T₀ , T₂ , T₂) = refl
distribʳ-γ (T₀ , T₁ , T₂) (T₁ , T₀ , T₀) = refl
distribʳ-γ (T₀ , T₁ , T₂) (T₁ , T₀ , T₁) = refl
distribʳ-γ (T₀ , T₁ , T₂) (T₁ , T₀ , T₂) = refl
distribʳ-γ (T₀ , T₁ , T₂) (T₁ , T₁ , T₀) = refl
distribʳ-γ (T₀ , T₁ , T₂) (T₁ , T₁ , T₁) = refl
distribʳ-γ (T₀ , T₁ , T₂) (T₁ , T₁ , T₂) = refl
distribʳ-γ (T₀ , T₁ , T₂) (T₁ , T₂ , T₀) = refl
distribʳ-γ (T₀ , T₁ , T₂) (T₁ , T₂ , T₁) = refl
distribʳ-γ (T₀ , T₁ , T₂) (T₁ , T₂ , T₂) = refl
distribʳ-γ (T₀ , T₁ , T₂) (T₂ , T₀ , T₀) = refl
distribʳ-γ (T₀ , T₁ , T₂) (T₂ , T₀ , T₁) = refl
distribʳ-γ (T₀ , T₁ , T₂) (T₂ , T₀ , T₂) = refl
distribʳ-γ (T₀ , T₁ , T₂) (T₂ , T₁ , T₀) = refl
distribʳ-γ (T₀ , T₁ , T₂) (T₂ , T₁ , T₁) = refl
distribʳ-γ (T₀ , T₁ , T₂) (T₂ , T₁ , T₂) = refl
distribʳ-γ (T₀ , T₁ , T₂) (T₂ , T₂ , T₀) = refl
distribʳ-γ (T₀ , T₁ , T₂) (T₂ , T₂ , T₁) = refl
distribʳ-γ (T₀ , T₁ , T₂) (T₂ , T₂ , T₂) = refl
distribʳ-γ (T₀ , T₂ , T₀) (T₀ , T₀ , T₀) = refl
distribʳ-γ (T₀ , T₂ , T₀) (T₀ , T₀ , T₁) = refl
distribʳ-γ (T₀ , T₂ , T₀) (T₀ , T₀ , T₂) = refl
distribʳ-γ (T₀ , T₂ , T₀) (T₀ , T₁ , T₀) = refl
distribʳ-γ (T₀ , T₂ , T₀) (T₀ , T₁ , T₁) = refl
distribʳ-γ (T₀ , T₂ , T₀) (T₀ , T₁ , T₂) = refl
distribʳ-γ (T₀ , T₂ , T₀) (T₀ , T₂ , T₀) = refl
distribʳ-γ (T₀ , T₂ , T₀) (T₀ , T₂ , T₁) = refl
distribʳ-γ (T₀ , T₂ , T₀) (T₀ , T₂ , T₂) = refl
distribʳ-γ (T₀ , T₂ , T₀) (T₁ , T₀ , T₀) = refl
distribʳ-γ (T₀ , T₂ , T₀) (T₁ , T₀ , T₁) = refl
distribʳ-γ (T₀ , T₂ , T₀) (T₁ , T₀ , T₂) = refl
distribʳ-γ (T₀ , T₂ , T₀) (T₁ , T₁ , T₀) = refl
distribʳ-γ (T₀ , T₂ , T₀) (T₁ , T₁ , T₁) = refl
distribʳ-γ (T₀ , T₂ , T₀) (T₁ , T₁ , T₂) = refl
distribʳ-γ (T₀ , T₂ , T₀) (T₁ , T₂ , T₀) = refl
distribʳ-γ (T₀ , T₂ , T₀) (T₁ , T₂ , T₁) = refl
distribʳ-γ (T₀ , T₂ , T₀) (T₁ , T₂ , T₂) = refl
distribʳ-γ (T₀ , T₂ , T₀) (T₂ , T₀ , T₀) = refl
distribʳ-γ (T₀ , T₂ , T₀) (T₂ , T₀ , T₁) = refl
distribʳ-γ (T₀ , T₂ , T₀) (T₂ , T₀ , T₂) = refl
distribʳ-γ (T₀ , T₂ , T₀) (T₂ , T₁ , T₀) = refl
distribʳ-γ (T₀ , T₂ , T₀) (T₂ , T₁ , T₁) = refl
distribʳ-γ (T₀ , T₂ , T₀) (T₂ , T₁ , T₂) = refl
distribʳ-γ (T₀ , T₂ , T₀) (T₂ , T₂ , T₀) = refl
distribʳ-γ (T₀ , T₂ , T₀) (T₂ , T₂ , T₁) = refl
distribʳ-γ (T₀ , T₂ , T₀) (T₂ , T₂ , T₂) = refl
distribʳ-γ (T₀ , T₂ , T₁) (T₀ , T₀ , T₀) = refl
distribʳ-γ (T₀ , T₂ , T₁) (T₀ , T₀ , T₁) = refl
distribʳ-γ (T₀ , T₂ , T₁) (T₀ , T₀ , T₂) = refl
distribʳ-γ (T₀ , T₂ , T₁) (T₀ , T₁ , T₀) = refl
distribʳ-γ (T₀ , T₂ , T₁) (T₀ , T₁ , T₁) = refl
distribʳ-γ (T₀ , T₂ , T₁) (T₀ , T₁ , T₂) = refl
distribʳ-γ (T₀ , T₂ , T₁) (T₀ , T₂ , T₀) = refl
distribʳ-γ (T₀ , T₂ , T₁) (T₀ , T₂ , T₁) = refl
distribʳ-γ (T₀ , T₂ , T₁) (T₀ , T₂ , T₂) = refl
distribʳ-γ (T₀ , T₂ , T₁) (T₁ , T₀ , T₀) = refl
distribʳ-γ (T₀ , T₂ , T₁) (T₁ , T₀ , T₁) = refl
distribʳ-γ (T₀ , T₂ , T₁) (T₁ , T₀ , T₂) = refl
distribʳ-γ (T₀ , T₂ , T₁) (T₁ , T₁ , T₀) = refl
distribʳ-γ (T₀ , T₂ , T₁) (T₁ , T₁ , T₁) = refl
distribʳ-γ (T₀ , T₂ , T₁) (T₁ , T₁ , T₂) = refl
distribʳ-γ (T₀ , T₂ , T₁) (T₁ , T₂ , T₀) = refl
distribʳ-γ (T₀ , T₂ , T₁) (T₁ , T₂ , T₁) = refl
distribʳ-γ (T₀ , T₂ , T₁) (T₁ , T₂ , T₂) = refl
distribʳ-γ (T₀ , T₂ , T₁) (T₂ , T₀ , T₀) = refl
distribʳ-γ (T₀ , T₂ , T₁) (T₂ , T₀ , T₁) = refl
distribʳ-γ (T₀ , T₂ , T₁) (T₂ , T₀ , T₂) = refl
distribʳ-γ (T₀ , T₂ , T₁) (T₂ , T₁ , T₀) = refl
distribʳ-γ (T₀ , T₂ , T₁) (T₂ , T₁ , T₁) = refl
distribʳ-γ (T₀ , T₂ , T₁) (T₂ , T₁ , T₂) = refl
distribʳ-γ (T₀ , T₂ , T₁) (T₂ , T₂ , T₀) = refl
distribʳ-γ (T₀ , T₂ , T₁) (T₂ , T₂ , T₁) = refl
distribʳ-γ (T₀ , T₂ , T₁) (T₂ , T₂ , T₂) = refl
distribʳ-γ (T₀ , T₂ , T₂) (T₀ , T₀ , T₀) = refl
distribʳ-γ (T₀ , T₂ , T₂) (T₀ , T₀ , T₁) = refl
distribʳ-γ (T₀ , T₂ , T₂) (T₀ , T₀ , T₂) = refl
distribʳ-γ (T₀ , T₂ , T₂) (T₀ , T₁ , T₀) = refl
distribʳ-γ (T₀ , T₂ , T₂) (T₀ , T₁ , T₁) = refl
distribʳ-γ (T₀ , T₂ , T₂) (T₀ , T₁ , T₂) = refl
distribʳ-γ (T₀ , T₂ , T₂) (T₀ , T₂ , T₀) = refl
distribʳ-γ (T₀ , T₂ , T₂) (T₀ , T₂ , T₁) = refl
distribʳ-γ (T₀ , T₂ , T₂) (T₀ , T₂ , T₂) = refl
distribʳ-γ (T₀ , T₂ , T₂) (T₁ , T₀ , T₀) = refl
distribʳ-γ (T₀ , T₂ , T₂) (T₁ , T₀ , T₁) = refl
distribʳ-γ (T₀ , T₂ , T₂) (T₁ , T₀ , T₂) = refl
distribʳ-γ (T₀ , T₂ , T₂) (T₁ , T₁ , T₀) = refl
distribʳ-γ (T₀ , T₂ , T₂) (T₁ , T₁ , T₁) = refl
distribʳ-γ (T₀ , T₂ , T₂) (T₁ , T₁ , T₂) = refl
distribʳ-γ (T₀ , T₂ , T₂) (T₁ , T₂ , T₀) = refl
distribʳ-γ (T₀ , T₂ , T₂) (T₁ , T₂ , T₁) = refl
distribʳ-γ (T₀ , T₂ , T₂) (T₁ , T₂ , T₂) = refl
distribʳ-γ (T₀ , T₂ , T₂) (T₂ , T₀ , T₀) = refl
distribʳ-γ (T₀ , T₂ , T₂) (T₂ , T₀ , T₁) = refl
distribʳ-γ (T₀ , T₂ , T₂) (T₂ , T₀ , T₂) = refl
distribʳ-γ (T₀ , T₂ , T₂) (T₂ , T₁ , T₀) = refl
distribʳ-γ (T₀ , T₂ , T₂) (T₂ , T₁ , T₁) = refl
distribʳ-γ (T₀ , T₂ , T₂) (T₂ , T₁ , T₂) = refl
distribʳ-γ (T₀ , T₂ , T₂) (T₂ , T₂ , T₀) = refl
distribʳ-γ (T₀ , T₂ , T₂) (T₂ , T₂ , T₁) = refl
distribʳ-γ (T₀ , T₂ , T₂) (T₂ , T₂ , T₂) = refl
distribʳ-γ (T₁ , T₀ , T₀) (T₀ , T₀ , T₀) = refl
distribʳ-γ (T₁ , T₀ , T₀) (T₀ , T₀ , T₁) = refl
distribʳ-γ (T₁ , T₀ , T₀) (T₀ , T₀ , T₂) = refl
distribʳ-γ (T₁ , T₀ , T₀) (T₀ , T₁ , T₀) = refl
distribʳ-γ (T₁ , T₀ , T₀) (T₀ , T₁ , T₁) = refl
distribʳ-γ (T₁ , T₀ , T₀) (T₀ , T₁ , T₂) = refl
distribʳ-γ (T₁ , T₀ , T₀) (T₀ , T₂ , T₀) = refl
distribʳ-γ (T₁ , T₀ , T₀) (T₀ , T₂ , T₁) = refl
distribʳ-γ (T₁ , T₀ , T₀) (T₀ , T₂ , T₂) = refl
distribʳ-γ (T₁ , T₀ , T₀) (T₁ , T₀ , T₀) = refl
distribʳ-γ (T₁ , T₀ , T₀) (T₁ , T₀ , T₁) = refl
distribʳ-γ (T₁ , T₀ , T₀) (T₁ , T₀ , T₂) = refl
distribʳ-γ (T₁ , T₀ , T₀) (T₁ , T₁ , T₀) = refl
distribʳ-γ (T₁ , T₀ , T₀) (T₁ , T₁ , T₁) = refl
distribʳ-γ (T₁ , T₀ , T₀) (T₁ , T₁ , T₂) = refl
distribʳ-γ (T₁ , T₀ , T₀) (T₁ , T₂ , T₀) = refl
distribʳ-γ (T₁ , T₀ , T₀) (T₁ , T₂ , T₁) = refl
distribʳ-γ (T₁ , T₀ , T₀) (T₁ , T₂ , T₂) = refl
distribʳ-γ (T₁ , T₀ , T₀) (T₂ , T₀ , T₀) = refl
distribʳ-γ (T₁ , T₀ , T₀) (T₂ , T₀ , T₁) = refl
distribʳ-γ (T₁ , T₀ , T₀) (T₂ , T₀ , T₂) = refl
distribʳ-γ (T₁ , T₀ , T₀) (T₂ , T₁ , T₀) = refl
distribʳ-γ (T₁ , T₀ , T₀) (T₂ , T₁ , T₁) = refl
distribʳ-γ (T₁ , T₀ , T₀) (T₂ , T₁ , T₂) = refl
distribʳ-γ (T₁ , T₀ , T₀) (T₂ , T₂ , T₀) = refl
distribʳ-γ (T₁ , T₀ , T₀) (T₂ , T₂ , T₁) = refl
distribʳ-γ (T₁ , T₀ , T₀) (T₂ , T₂ , T₂) = refl
distribʳ-γ (T₁ , T₀ , T₁) (T₀ , T₀ , T₀) = refl
distribʳ-γ (T₁ , T₀ , T₁) (T₀ , T₀ , T₁) = refl
distribʳ-γ (T₁ , T₀ , T₁) (T₀ , T₀ , T₂) = refl
distribʳ-γ (T₁ , T₀ , T₁) (T₀ , T₁ , T₀) = refl
distribʳ-γ (T₁ , T₀ , T₁) (T₀ , T₁ , T₁) = refl
distribʳ-γ (T₁ , T₀ , T₁) (T₀ , T₁ , T₂) = refl
distribʳ-γ (T₁ , T₀ , T₁) (T₀ , T₂ , T₀) = refl
distribʳ-γ (T₁ , T₀ , T₁) (T₀ , T₂ , T₁) = refl
distribʳ-γ (T₁ , T₀ , T₁) (T₀ , T₂ , T₂) = refl
distribʳ-γ (T₁ , T₀ , T₁) (T₁ , T₀ , T₀) = refl
distribʳ-γ (T₁ , T₀ , T₁) (T₁ , T₀ , T₁) = refl
distribʳ-γ (T₁ , T₀ , T₁) (T₁ , T₀ , T₂) = refl
distribʳ-γ (T₁ , T₀ , T₁) (T₁ , T₁ , T₀) = refl
distribʳ-γ (T₁ , T₀ , T₁) (T₁ , T₁ , T₁) = refl
distribʳ-γ (T₁ , T₀ , T₁) (T₁ , T₁ , T₂) = refl
distribʳ-γ (T₁ , T₀ , T₁) (T₁ , T₂ , T₀) = refl
distribʳ-γ (T₁ , T₀ , T₁) (T₁ , T₂ , T₁) = refl
distribʳ-γ (T₁ , T₀ , T₁) (T₁ , T₂ , T₂) = refl
distribʳ-γ (T₁ , T₀ , T₁) (T₂ , T₀ , T₀) = refl
distribʳ-γ (T₁ , T₀ , T₁) (T₂ , T₀ , T₁) = refl
distribʳ-γ (T₁ , T₀ , T₁) (T₂ , T₀ , T₂) = refl
distribʳ-γ (T₁ , T₀ , T₁) (T₂ , T₁ , T₀) = refl
distribʳ-γ (T₁ , T₀ , T₁) (T₂ , T₁ , T₁) = refl
distribʳ-γ (T₁ , T₀ , T₁) (T₂ , T₁ , T₂) = refl
distribʳ-γ (T₁ , T₀ , T₁) (T₂ , T₂ , T₀) = refl
distribʳ-γ (T₁ , T₀ , T₁) (T₂ , T₂ , T₁) = refl
distribʳ-γ (T₁ , T₀ , T₁) (T₂ , T₂ , T₂) = refl
distribʳ-γ (T₁ , T₀ , T₂) (T₀ , T₀ , T₀) = refl
distribʳ-γ (T₁ , T₀ , T₂) (T₀ , T₀ , T₁) = refl
distribʳ-γ (T₁ , T₀ , T₂) (T₀ , T₀ , T₂) = refl
distribʳ-γ (T₁ , T₀ , T₂) (T₀ , T₁ , T₀) = refl
distribʳ-γ (T₁ , T₀ , T₂) (T₀ , T₁ , T₁) = refl
distribʳ-γ (T₁ , T₀ , T₂) (T₀ , T₁ , T₂) = refl
distribʳ-γ (T₁ , T₀ , T₂) (T₀ , T₂ , T₀) = refl
distribʳ-γ (T₁ , T₀ , T₂) (T₀ , T₂ , T₁) = refl
distribʳ-γ (T₁ , T₀ , T₂) (T₀ , T₂ , T₂) = refl
distribʳ-γ (T₁ , T₀ , T₂) (T₁ , T₀ , T₀) = refl
distribʳ-γ (T₁ , T₀ , T₂) (T₁ , T₀ , T₁) = refl
distribʳ-γ (T₁ , T₀ , T₂) (T₁ , T₀ , T₂) = refl
distribʳ-γ (T₁ , T₀ , T₂) (T₁ , T₁ , T₀) = refl
distribʳ-γ (T₁ , T₀ , T₂) (T₁ , T₁ , T₁) = refl
distribʳ-γ (T₁ , T₀ , T₂) (T₁ , T₁ , T₂) = refl
distribʳ-γ (T₁ , T₀ , T₂) (T₁ , T₂ , T₀) = refl
distribʳ-γ (T₁ , T₀ , T₂) (T₁ , T₂ , T₁) = refl
distribʳ-γ (T₁ , T₀ , T₂) (T₁ , T₂ , T₂) = refl
distribʳ-γ (T₁ , T₀ , T₂) (T₂ , T₀ , T₀) = refl
distribʳ-γ (T₁ , T₀ , T₂) (T₂ , T₀ , T₁) = refl
distribʳ-γ (T₁ , T₀ , T₂) (T₂ , T₀ , T₂) = refl
distribʳ-γ (T₁ , T₀ , T₂) (T₂ , T₁ , T₀) = refl
distribʳ-γ (T₁ , T₀ , T₂) (T₂ , T₁ , T₁) = refl
distribʳ-γ (T₁ , T₀ , T₂) (T₂ , T₁ , T₂) = refl
distribʳ-γ (T₁ , T₀ , T₂) (T₂ , T₂ , T₀) = refl
distribʳ-γ (T₁ , T₀ , T₂) (T₂ , T₂ , T₁) = refl
distribʳ-γ (T₁ , T₀ , T₂) (T₂ , T₂ , T₂) = refl
distribʳ-γ (T₁ , T₁ , T₀) (T₀ , T₀ , T₀) = refl
distribʳ-γ (T₁ , T₁ , T₀) (T₀ , T₀ , T₁) = refl
distribʳ-γ (T₁ , T₁ , T₀) (T₀ , T₀ , T₂) = refl
distribʳ-γ (T₁ , T₁ , T₀) (T₀ , T₁ , T₀) = refl
distribʳ-γ (T₁ , T₁ , T₀) (T₀ , T₁ , T₁) = refl
distribʳ-γ (T₁ , T₁ , T₀) (T₀ , T₁ , T₂) = refl
distribʳ-γ (T₁ , T₁ , T₀) (T₀ , T₂ , T₀) = refl
distribʳ-γ (T₁ , T₁ , T₀) (T₀ , T₂ , T₁) = refl
distribʳ-γ (T₁ , T₁ , T₀) (T₀ , T₂ , T₂) = refl
distribʳ-γ (T₁ , T₁ , T₀) (T₁ , T₀ , T₀) = refl
distribʳ-γ (T₁ , T₁ , T₀) (T₁ , T₀ , T₁) = refl
distribʳ-γ (T₁ , T₁ , T₀) (T₁ , T₀ , T₂) = refl
distribʳ-γ (T₁ , T₁ , T₀) (T₁ , T₁ , T₀) = refl
distribʳ-γ (T₁ , T₁ , T₀) (T₁ , T₁ , T₁) = refl
distribʳ-γ (T₁ , T₁ , T₀) (T₁ , T₁ , T₂) = refl
distribʳ-γ (T₁ , T₁ , T₀) (T₁ , T₂ , T₀) = refl
distribʳ-γ (T₁ , T₁ , T₀) (T₁ , T₂ , T₁) = refl
distribʳ-γ (T₁ , T₁ , T₀) (T₁ , T₂ , T₂) = refl
distribʳ-γ (T₁ , T₁ , T₀) (T₂ , T₀ , T₀) = refl
distribʳ-γ (T₁ , T₁ , T₀) (T₂ , T₀ , T₁) = refl
distribʳ-γ (T₁ , T₁ , T₀) (T₂ , T₀ , T₂) = refl
distribʳ-γ (T₁ , T₁ , T₀) (T₂ , T₁ , T₀) = refl
distribʳ-γ (T₁ , T₁ , T₀) (T₂ , T₁ , T₁) = refl
distribʳ-γ (T₁ , T₁ , T₀) (T₂ , T₁ , T₂) = refl
distribʳ-γ (T₁ , T₁ , T₀) (T₂ , T₂ , T₀) = refl
distribʳ-γ (T₁ , T₁ , T₀) (T₂ , T₂ , T₁) = refl
distribʳ-γ (T₁ , T₁ , T₀) (T₂ , T₂ , T₂) = refl
distribʳ-γ (T₁ , T₁ , T₁) (T₀ , T₀ , T₀) = refl
distribʳ-γ (T₁ , T₁ , T₁) (T₀ , T₀ , T₁) = refl
distribʳ-γ (T₁ , T₁ , T₁) (T₀ , T₀ , T₂) = refl
distribʳ-γ (T₁ , T₁ , T₁) (T₀ , T₁ , T₀) = refl
distribʳ-γ (T₁ , T₁ , T₁) (T₀ , T₁ , T₁) = refl
distribʳ-γ (T₁ , T₁ , T₁) (T₀ , T₁ , T₂) = refl
distribʳ-γ (T₁ , T₁ , T₁) (T₀ , T₂ , T₀) = refl
distribʳ-γ (T₁ , T₁ , T₁) (T₀ , T₂ , T₁) = refl
distribʳ-γ (T₁ , T₁ , T₁) (T₀ , T₂ , T₂) = refl
distribʳ-γ (T₁ , T₁ , T₁) (T₁ , T₀ , T₀) = refl
distribʳ-γ (T₁ , T₁ , T₁) (T₁ , T₀ , T₁) = refl
distribʳ-γ (T₁ , T₁ , T₁) (T₁ , T₀ , T₂) = refl
distribʳ-γ (T₁ , T₁ , T₁) (T₁ , T₁ , T₀) = refl
distribʳ-γ (T₁ , T₁ , T₁) (T₁ , T₁ , T₁) = refl
distribʳ-γ (T₁ , T₁ , T₁) (T₁ , T₁ , T₂) = refl
distribʳ-γ (T₁ , T₁ , T₁) (T₁ , T₂ , T₀) = refl
distribʳ-γ (T₁ , T₁ , T₁) (T₁ , T₂ , T₁) = refl
distribʳ-γ (T₁ , T₁ , T₁) (T₁ , T₂ , T₂) = refl
distribʳ-γ (T₁ , T₁ , T₁) (T₂ , T₀ , T₀) = refl
distribʳ-γ (T₁ , T₁ , T₁) (T₂ , T₀ , T₁) = refl
distribʳ-γ (T₁ , T₁ , T₁) (T₂ , T₀ , T₂) = refl
distribʳ-γ (T₁ , T₁ , T₁) (T₂ , T₁ , T₀) = refl
distribʳ-γ (T₁ , T₁ , T₁) (T₂ , T₁ , T₁) = refl
distribʳ-γ (T₁ , T₁ , T₁) (T₂ , T₁ , T₂) = refl
distribʳ-γ (T₁ , T₁ , T₁) (T₂ , T₂ , T₀) = refl
distribʳ-γ (T₁ , T₁ , T₁) (T₂ , T₂ , T₁) = refl
distribʳ-γ (T₁ , T₁ , T₁) (T₂ , T₂ , T₂) = refl
distribʳ-γ (T₁ , T₁ , T₂) (T₀ , T₀ , T₀) = refl
distribʳ-γ (T₁ , T₁ , T₂) (T₀ , T₀ , T₁) = refl
distribʳ-γ (T₁ , T₁ , T₂) (T₀ , T₀ , T₂) = refl
distribʳ-γ (T₁ , T₁ , T₂) (T₀ , T₁ , T₀) = refl
distribʳ-γ (T₁ , T₁ , T₂) (T₀ , T₁ , T₁) = refl
distribʳ-γ (T₁ , T₁ , T₂) (T₀ , T₁ , T₂) = refl
distribʳ-γ (T₁ , T₁ , T₂) (T₀ , T₂ , T₀) = refl
distribʳ-γ (T₁ , T₁ , T₂) (T₀ , T₂ , T₁) = refl
distribʳ-γ (T₁ , T₁ , T₂) (T₀ , T₂ , T₂) = refl
distribʳ-γ (T₁ , T₁ , T₂) (T₁ , T₀ , T₀) = refl
distribʳ-γ (T₁ , T₁ , T₂) (T₁ , T₀ , T₁) = refl
distribʳ-γ (T₁ , T₁ , T₂) (T₁ , T₀ , T₂) = refl
distribʳ-γ (T₁ , T₁ , T₂) (T₁ , T₁ , T₀) = refl
distribʳ-γ (T₁ , T₁ , T₂) (T₁ , T₁ , T₁) = refl
distribʳ-γ (T₁ , T₁ , T₂) (T₁ , T₁ , T₂) = refl
distribʳ-γ (T₁ , T₁ , T₂) (T₁ , T₂ , T₀) = refl
distribʳ-γ (T₁ , T₁ , T₂) (T₁ , T₂ , T₁) = refl
distribʳ-γ (T₁ , T₁ , T₂) (T₁ , T₂ , T₂) = refl
distribʳ-γ (T₁ , T₁ , T₂) (T₂ , T₀ , T₀) = refl
distribʳ-γ (T₁ , T₁ , T₂) (T₂ , T₀ , T₁) = refl
distribʳ-γ (T₁ , T₁ , T₂) (T₂ , T₀ , T₂) = refl
distribʳ-γ (T₁ , T₁ , T₂) (T₂ , T₁ , T₀) = refl
distribʳ-γ (T₁ , T₁ , T₂) (T₂ , T₁ , T₁) = refl
distribʳ-γ (T₁ , T₁ , T₂) (T₂ , T₁ , T₂) = refl
distribʳ-γ (T₁ , T₁ , T₂) (T₂ , T₂ , T₀) = refl
distribʳ-γ (T₁ , T₁ , T₂) (T₂ , T₂ , T₁) = refl
distribʳ-γ (T₁ , T₁ , T₂) (T₂ , T₂ , T₂) = refl
distribʳ-γ (T₁ , T₂ , T₀) (T₀ , T₀ , T₀) = refl
distribʳ-γ (T₁ , T₂ , T₀) (T₀ , T₀ , T₁) = refl
distribʳ-γ (T₁ , T₂ , T₀) (T₀ , T₀ , T₂) = refl
distribʳ-γ (T₁ , T₂ , T₀) (T₀ , T₁ , T₀) = refl
distribʳ-γ (T₁ , T₂ , T₀) (T₀ , T₁ , T₁) = refl
distribʳ-γ (T₁ , T₂ , T₀) (T₀ , T₁ , T₂) = refl
distribʳ-γ (T₁ , T₂ , T₀) (T₀ , T₂ , T₀) = refl
distribʳ-γ (T₁ , T₂ , T₀) (T₀ , T₂ , T₁) = refl
distribʳ-γ (T₁ , T₂ , T₀) (T₀ , T₂ , T₂) = refl
distribʳ-γ (T₁ , T₂ , T₀) (T₁ , T₀ , T₀) = refl
distribʳ-γ (T₁ , T₂ , T₀) (T₁ , T₀ , T₁) = refl
distribʳ-γ (T₁ , T₂ , T₀) (T₁ , T₀ , T₂) = refl
distribʳ-γ (T₁ , T₂ , T₀) (T₁ , T₁ , T₀) = refl
distribʳ-γ (T₁ , T₂ , T₀) (T₁ , T₁ , T₁) = refl
distribʳ-γ (T₁ , T₂ , T₀) (T₁ , T₁ , T₂) = refl
distribʳ-γ (T₁ , T₂ , T₀) (T₁ , T₂ , T₀) = refl
distribʳ-γ (T₁ , T₂ , T₀) (T₁ , T₂ , T₁) = refl
distribʳ-γ (T₁ , T₂ , T₀) (T₁ , T₂ , T₂) = refl
distribʳ-γ (T₁ , T₂ , T₀) (T₂ , T₀ , T₀) = refl
distribʳ-γ (T₁ , T₂ , T₀) (T₂ , T₀ , T₁) = refl
distribʳ-γ (T₁ , T₂ , T₀) (T₂ , T₀ , T₂) = refl
distribʳ-γ (T₁ , T₂ , T₀) (T₂ , T₁ , T₀) = refl
distribʳ-γ (T₁ , T₂ , T₀) (T₂ , T₁ , T₁) = refl
distribʳ-γ (T₁ , T₂ , T₀) (T₂ , T₁ , T₂) = refl
distribʳ-γ (T₁ , T₂ , T₀) (T₂ , T₂ , T₀) = refl
distribʳ-γ (T₁ , T₂ , T₀) (T₂ , T₂ , T₁) = refl
distribʳ-γ (T₁ , T₂ , T₀) (T₂ , T₂ , T₂) = refl
distribʳ-γ (T₁ , T₂ , T₁) (T₀ , T₀ , T₀) = refl
distribʳ-γ (T₁ , T₂ , T₁) (T₀ , T₀ , T₁) = refl
distribʳ-γ (T₁ , T₂ , T₁) (T₀ , T₀ , T₂) = refl
distribʳ-γ (T₁ , T₂ , T₁) (T₀ , T₁ , T₀) = refl
distribʳ-γ (T₁ , T₂ , T₁) (T₀ , T₁ , T₁) = refl
distribʳ-γ (T₁ , T₂ , T₁) (T₀ , T₁ , T₂) = refl
distribʳ-γ (T₁ , T₂ , T₁) (T₀ , T₂ , T₀) = refl
distribʳ-γ (T₁ , T₂ , T₁) (T₀ , T₂ , T₁) = refl
distribʳ-γ (T₁ , T₂ , T₁) (T₀ , T₂ , T₂) = refl
distribʳ-γ (T₁ , T₂ , T₁) (T₁ , T₀ , T₀) = refl
distribʳ-γ (T₁ , T₂ , T₁) (T₁ , T₀ , T₁) = refl
distribʳ-γ (T₁ , T₂ , T₁) (T₁ , T₀ , T₂) = refl
distribʳ-γ (T₁ , T₂ , T₁) (T₁ , T₁ , T₀) = refl
distribʳ-γ (T₁ , T₂ , T₁) (T₁ , T₁ , T₁) = refl
distribʳ-γ (T₁ , T₂ , T₁) (T₁ , T₁ , T₂) = refl
distribʳ-γ (T₁ , T₂ , T₁) (T₁ , T₂ , T₀) = refl
distribʳ-γ (T₁ , T₂ , T₁) (T₁ , T₂ , T₁) = refl
distribʳ-γ (T₁ , T₂ , T₁) (T₁ , T₂ , T₂) = refl
distribʳ-γ (T₁ , T₂ , T₁) (T₂ , T₀ , T₀) = refl
distribʳ-γ (T₁ , T₂ , T₁) (T₂ , T₀ , T₁) = refl
distribʳ-γ (T₁ , T₂ , T₁) (T₂ , T₀ , T₂) = refl
distribʳ-γ (T₁ , T₂ , T₁) (T₂ , T₁ , T₀) = refl
distribʳ-γ (T₁ , T₂ , T₁) (T₂ , T₁ , T₁) = refl
distribʳ-γ (T₁ , T₂ , T₁) (T₂ , T₁ , T₂) = refl
distribʳ-γ (T₁ , T₂ , T₁) (T₂ , T₂ , T₀) = refl
distribʳ-γ (T₁ , T₂ , T₁) (T₂ , T₂ , T₁) = refl
distribʳ-γ (T₁ , T₂ , T₁) (T₂ , T₂ , T₂) = refl
distribʳ-γ (T₁ , T₂ , T₂) (T₀ , T₀ , T₀) = refl
distribʳ-γ (T₁ , T₂ , T₂) (T₀ , T₀ , T₁) = refl
distribʳ-γ (T₁ , T₂ , T₂) (T₀ , T₀ , T₂) = refl
distribʳ-γ (T₁ , T₂ , T₂) (T₀ , T₁ , T₀) = refl
distribʳ-γ (T₁ , T₂ , T₂) (T₀ , T₁ , T₁) = refl
distribʳ-γ (T₁ , T₂ , T₂) (T₀ , T₁ , T₂) = refl
distribʳ-γ (T₁ , T₂ , T₂) (T₀ , T₂ , T₀) = refl
distribʳ-γ (T₁ , T₂ , T₂) (T₀ , T₂ , T₁) = refl
distribʳ-γ (T₁ , T₂ , T₂) (T₀ , T₂ , T₂) = refl
distribʳ-γ (T₁ , T₂ , T₂) (T₁ , T₀ , T₀) = refl
distribʳ-γ (T₁ , T₂ , T₂) (T₁ , T₀ , T₁) = refl
distribʳ-γ (T₁ , T₂ , T₂) (T₁ , T₀ , T₂) = refl
distribʳ-γ (T₁ , T₂ , T₂) (T₁ , T₁ , T₀) = refl
distribʳ-γ (T₁ , T₂ , T₂) (T₁ , T₁ , T₁) = refl
distribʳ-γ (T₁ , T₂ , T₂) (T₁ , T₁ , T₂) = refl
distribʳ-γ (T₁ , T₂ , T₂) (T₁ , T₂ , T₀) = refl
distribʳ-γ (T₁ , T₂ , T₂) (T₁ , T₂ , T₁) = refl
distribʳ-γ (T₁ , T₂ , T₂) (T₁ , T₂ , T₂) = refl
distribʳ-γ (T₁ , T₂ , T₂) (T₂ , T₀ , T₀) = refl
distribʳ-γ (T₁ , T₂ , T₂) (T₂ , T₀ , T₁) = refl
distribʳ-γ (T₁ , T₂ , T₂) (T₂ , T₀ , T₂) = refl
distribʳ-γ (T₁ , T₂ , T₂) (T₂ , T₁ , T₀) = refl
distribʳ-γ (T₁ , T₂ , T₂) (T₂ , T₁ , T₁) = refl
distribʳ-γ (T₁ , T₂ , T₂) (T₂ , T₁ , T₂) = refl
distribʳ-γ (T₁ , T₂ , T₂) (T₂ , T₂ , T₀) = refl
distribʳ-γ (T₁ , T₂ , T₂) (T₂ , T₂ , T₁) = refl
distribʳ-γ (T₁ , T₂ , T₂) (T₂ , T₂ , T₂) = refl
distribʳ-γ (T₂ , T₀ , T₀) (T₀ , T₀ , T₀) = refl
distribʳ-γ (T₂ , T₀ , T₀) (T₀ , T₀ , T₁) = refl
distribʳ-γ (T₂ , T₀ , T₀) (T₀ , T₀ , T₂) = refl
distribʳ-γ (T₂ , T₀ , T₀) (T₀ , T₁ , T₀) = refl
distribʳ-γ (T₂ , T₀ , T₀) (T₀ , T₁ , T₁) = refl
distribʳ-γ (T₂ , T₀ , T₀) (T₀ , T₁ , T₂) = refl
distribʳ-γ (T₂ , T₀ , T₀) (T₀ , T₂ , T₀) = refl
distribʳ-γ (T₂ , T₀ , T₀) (T₀ , T₂ , T₁) = refl
distribʳ-γ (T₂ , T₀ , T₀) (T₀ , T₂ , T₂) = refl
distribʳ-γ (T₂ , T₀ , T₀) (T₁ , T₀ , T₀) = refl
distribʳ-γ (T₂ , T₀ , T₀) (T₁ , T₀ , T₁) = refl
distribʳ-γ (T₂ , T₀ , T₀) (T₁ , T₀ , T₂) = refl
distribʳ-γ (T₂ , T₀ , T₀) (T₁ , T₁ , T₀) = refl
distribʳ-γ (T₂ , T₀ , T₀) (T₁ , T₁ , T₁) = refl
distribʳ-γ (T₂ , T₀ , T₀) (T₁ , T₁ , T₂) = refl
distribʳ-γ (T₂ , T₀ , T₀) (T₁ , T₂ , T₀) = refl
distribʳ-γ (T₂ , T₀ , T₀) (T₁ , T₂ , T₁) = refl
distribʳ-γ (T₂ , T₀ , T₀) (T₁ , T₂ , T₂) = refl
distribʳ-γ (T₂ , T₀ , T₀) (T₂ , T₀ , T₀) = refl
distribʳ-γ (T₂ , T₀ , T₀) (T₂ , T₀ , T₁) = refl
distribʳ-γ (T₂ , T₀ , T₀) (T₂ , T₀ , T₂) = refl
distribʳ-γ (T₂ , T₀ , T₀) (T₂ , T₁ , T₀) = refl
distribʳ-γ (T₂ , T₀ , T₀) (T₂ , T₁ , T₁) = refl
distribʳ-γ (T₂ , T₀ , T₀) (T₂ , T₁ , T₂) = refl
distribʳ-γ (T₂ , T₀ , T₀) (T₂ , T₂ , T₀) = refl
distribʳ-γ (T₂ , T₀ , T₀) (T₂ , T₂ , T₁) = refl
distribʳ-γ (T₂ , T₀ , T₀) (T₂ , T₂ , T₂) = refl
distribʳ-γ (T₂ , T₀ , T₁) (T₀ , T₀ , T₀) = refl
distribʳ-γ (T₂ , T₀ , T₁) (T₀ , T₀ , T₁) = refl
distribʳ-γ (T₂ , T₀ , T₁) (T₀ , T₀ , T₂) = refl
distribʳ-γ (T₂ , T₀ , T₁) (T₀ , T₁ , T₀) = refl
distribʳ-γ (T₂ , T₀ , T₁) (T₀ , T₁ , T₁) = refl
distribʳ-γ (T₂ , T₀ , T₁) (T₀ , T₁ , T₂) = refl
distribʳ-γ (T₂ , T₀ , T₁) (T₀ , T₂ , T₀) = refl
distribʳ-γ (T₂ , T₀ , T₁) (T₀ , T₂ , T₁) = refl
distribʳ-γ (T₂ , T₀ , T₁) (T₀ , T₂ , T₂) = refl
distribʳ-γ (T₂ , T₀ , T₁) (T₁ , T₀ , T₀) = refl
distribʳ-γ (T₂ , T₀ , T₁) (T₁ , T₀ , T₁) = refl
distribʳ-γ (T₂ , T₀ , T₁) (T₁ , T₀ , T₂) = refl
distribʳ-γ (T₂ , T₀ , T₁) (T₁ , T₁ , T₀) = refl
distribʳ-γ (T₂ , T₀ , T₁) (T₁ , T₁ , T₁) = refl
distribʳ-γ (T₂ , T₀ , T₁) (T₁ , T₁ , T₂) = refl
distribʳ-γ (T₂ , T₀ , T₁) (T₁ , T₂ , T₀) = refl
distribʳ-γ (T₂ , T₀ , T₁) (T₁ , T₂ , T₁) = refl
distribʳ-γ (T₂ , T₀ , T₁) (T₁ , T₂ , T₂) = refl
distribʳ-γ (T₂ , T₀ , T₁) (T₂ , T₀ , T₀) = refl
distribʳ-γ (T₂ , T₀ , T₁) (T₂ , T₀ , T₁) = refl
distribʳ-γ (T₂ , T₀ , T₁) (T₂ , T₀ , T₂) = refl
distribʳ-γ (T₂ , T₀ , T₁) (T₂ , T₁ , T₀) = refl
distribʳ-γ (T₂ , T₀ , T₁) (T₂ , T₁ , T₁) = refl
distribʳ-γ (T₂ , T₀ , T₁) (T₂ , T₁ , T₂) = refl
distribʳ-γ (T₂ , T₀ , T₁) (T₂ , T₂ , T₀) = refl
distribʳ-γ (T₂ , T₀ , T₁) (T₂ , T₂ , T₁) = refl
distribʳ-γ (T₂ , T₀ , T₁) (T₂ , T₂ , T₂) = refl
distribʳ-γ (T₂ , T₀ , T₂) (T₀ , T₀ , T₀) = refl
distribʳ-γ (T₂ , T₀ , T₂) (T₀ , T₀ , T₁) = refl
distribʳ-γ (T₂ , T₀ , T₂) (T₀ , T₀ , T₂) = refl
distribʳ-γ (T₂ , T₀ , T₂) (T₀ , T₁ , T₀) = refl
distribʳ-γ (T₂ , T₀ , T₂) (T₀ , T₁ , T₁) = refl
distribʳ-γ (T₂ , T₀ , T₂) (T₀ , T₁ , T₂) = refl
distribʳ-γ (T₂ , T₀ , T₂) (T₀ , T₂ , T₀) = refl
distribʳ-γ (T₂ , T₀ , T₂) (T₀ , T₂ , T₁) = refl
distribʳ-γ (T₂ , T₀ , T₂) (T₀ , T₂ , T₂) = refl
distribʳ-γ (T₂ , T₀ , T₂) (T₁ , T₀ , T₀) = refl
distribʳ-γ (T₂ , T₀ , T₂) (T₁ , T₀ , T₁) = refl
distribʳ-γ (T₂ , T₀ , T₂) (T₁ , T₀ , T₂) = refl
distribʳ-γ (T₂ , T₀ , T₂) (T₁ , T₁ , T₀) = refl
distribʳ-γ (T₂ , T₀ , T₂) (T₁ , T₁ , T₁) = refl
distribʳ-γ (T₂ , T₀ , T₂) (T₁ , T₁ , T₂) = refl
distribʳ-γ (T₂ , T₀ , T₂) (T₁ , T₂ , T₀) = refl
distribʳ-γ (T₂ , T₀ , T₂) (T₁ , T₂ , T₁) = refl
distribʳ-γ (T₂ , T₀ , T₂) (T₁ , T₂ , T₂) = refl
distribʳ-γ (T₂ , T₀ , T₂) (T₂ , T₀ , T₀) = refl
distribʳ-γ (T₂ , T₀ , T₂) (T₂ , T₀ , T₁) = refl
distribʳ-γ (T₂ , T₀ , T₂) (T₂ , T₀ , T₂) = refl
distribʳ-γ (T₂ , T₀ , T₂) (T₂ , T₁ , T₀) = refl
distribʳ-γ (T₂ , T₀ , T₂) (T₂ , T₁ , T₁) = refl
distribʳ-γ (T₂ , T₀ , T₂) (T₂ , T₁ , T₂) = refl
distribʳ-γ (T₂ , T₀ , T₂) (T₂ , T₂ , T₀) = refl
distribʳ-γ (T₂ , T₀ , T₂) (T₂ , T₂ , T₁) = refl
distribʳ-γ (T₂ , T₀ , T₂) (T₂ , T₂ , T₂) = refl
distribʳ-γ (T₂ , T₁ , T₀) (T₀ , T₀ , T₀) = refl
distribʳ-γ (T₂ , T₁ , T₀) (T₀ , T₀ , T₁) = refl
distribʳ-γ (T₂ , T₁ , T₀) (T₀ , T₀ , T₂) = refl
distribʳ-γ (T₂ , T₁ , T₀) (T₀ , T₁ , T₀) = refl
distribʳ-γ (T₂ , T₁ , T₀) (T₀ , T₁ , T₁) = refl
distribʳ-γ (T₂ , T₁ , T₀) (T₀ , T₁ , T₂) = refl
distribʳ-γ (T₂ , T₁ , T₀) (T₀ , T₂ , T₀) = refl
distribʳ-γ (T₂ , T₁ , T₀) (T₀ , T₂ , T₁) = refl
distribʳ-γ (T₂ , T₁ , T₀) (T₀ , T₂ , T₂) = refl
distribʳ-γ (T₂ , T₁ , T₀) (T₁ , T₀ , T₀) = refl
distribʳ-γ (T₂ , T₁ , T₀) (T₁ , T₀ , T₁) = refl
distribʳ-γ (T₂ , T₁ , T₀) (T₁ , T₀ , T₂) = refl
distribʳ-γ (T₂ , T₁ , T₀) (T₁ , T₁ , T₀) = refl
distribʳ-γ (T₂ , T₁ , T₀) (T₁ , T₁ , T₁) = refl
distribʳ-γ (T₂ , T₁ , T₀) (T₁ , T₁ , T₂) = refl
distribʳ-γ (T₂ , T₁ , T₀) (T₁ , T₂ , T₀) = refl
distribʳ-γ (T₂ , T₁ , T₀) (T₁ , T₂ , T₁) = refl
distribʳ-γ (T₂ , T₁ , T₀) (T₁ , T₂ , T₂) = refl
distribʳ-γ (T₂ , T₁ , T₀) (T₂ , T₀ , T₀) = refl
distribʳ-γ (T₂ , T₁ , T₀) (T₂ , T₀ , T₁) = refl
distribʳ-γ (T₂ , T₁ , T₀) (T₂ , T₀ , T₂) = refl
distribʳ-γ (T₂ , T₁ , T₀) (T₂ , T₁ , T₀) = refl
distribʳ-γ (T₂ , T₁ , T₀) (T₂ , T₁ , T₁) = refl
distribʳ-γ (T₂ , T₁ , T₀) (T₂ , T₁ , T₂) = refl
distribʳ-γ (T₂ , T₁ , T₀) (T₂ , T₂ , T₀) = refl
distribʳ-γ (T₂ , T₁ , T₀) (T₂ , T₂ , T₁) = refl
distribʳ-γ (T₂ , T₁ , T₀) (T₂ , T₂ , T₂) = refl
distribʳ-γ (T₂ , T₁ , T₁) (T₀ , T₀ , T₀) = refl
distribʳ-γ (T₂ , T₁ , T₁) (T₀ , T₀ , T₁) = refl
distribʳ-γ (T₂ , T₁ , T₁) (T₀ , T₀ , T₂) = refl
distribʳ-γ (T₂ , T₁ , T₁) (T₀ , T₁ , T₀) = refl
distribʳ-γ (T₂ , T₁ , T₁) (T₀ , T₁ , T₁) = refl
distribʳ-γ (T₂ , T₁ , T₁) (T₀ , T₁ , T₂) = refl
distribʳ-γ (T₂ , T₁ , T₁) (T₀ , T₂ , T₀) = refl
distribʳ-γ (T₂ , T₁ , T₁) (T₀ , T₂ , T₁) = refl
distribʳ-γ (T₂ , T₁ , T₁) (T₀ , T₂ , T₂) = refl
distribʳ-γ (T₂ , T₁ , T₁) (T₁ , T₀ , T₀) = refl
distribʳ-γ (T₂ , T₁ , T₁) (T₁ , T₀ , T₁) = refl
distribʳ-γ (T₂ , T₁ , T₁) (T₁ , T₀ , T₂) = refl
distribʳ-γ (T₂ , T₁ , T₁) (T₁ , T₁ , T₀) = refl
distribʳ-γ (T₂ , T₁ , T₁) (T₁ , T₁ , T₁) = refl
distribʳ-γ (T₂ , T₁ , T₁) (T₁ , T₁ , T₂) = refl
distribʳ-γ (T₂ , T₁ , T₁) (T₁ , T₂ , T₀) = refl
distribʳ-γ (T₂ , T₁ , T₁) (T₁ , T₂ , T₁) = refl
distribʳ-γ (T₂ , T₁ , T₁) (T₁ , T₂ , T₂) = refl
distribʳ-γ (T₂ , T₁ , T₁) (T₂ , T₀ , T₀) = refl
distribʳ-γ (T₂ , T₁ , T₁) (T₂ , T₀ , T₁) = refl
distribʳ-γ (T₂ , T₁ , T₁) (T₂ , T₀ , T₂) = refl
distribʳ-γ (T₂ , T₁ , T₁) (T₂ , T₁ , T₀) = refl
distribʳ-γ (T₂ , T₁ , T₁) (T₂ , T₁ , T₁) = refl
distribʳ-γ (T₂ , T₁ , T₁) (T₂ , T₁ , T₂) = refl
distribʳ-γ (T₂ , T₁ , T₁) (T₂ , T₂ , T₀) = refl
distribʳ-γ (T₂ , T₁ , T₁) (T₂ , T₂ , T₁) = refl
distribʳ-γ (T₂ , T₁ , T₁) (T₂ , T₂ , T₂) = refl
distribʳ-γ (T₂ , T₁ , T₂) (T₀ , T₀ , T₀) = refl
distribʳ-γ (T₂ , T₁ , T₂) (T₀ , T₀ , T₁) = refl
distribʳ-γ (T₂ , T₁ , T₂) (T₀ , T₀ , T₂) = refl
distribʳ-γ (T₂ , T₁ , T₂) (T₀ , T₁ , T₀) = refl
distribʳ-γ (T₂ , T₁ , T₂) (T₀ , T₁ , T₁) = refl
distribʳ-γ (T₂ , T₁ , T₂) (T₀ , T₁ , T₂) = refl
distribʳ-γ (T₂ , T₁ , T₂) (T₀ , T₂ , T₀) = refl
distribʳ-γ (T₂ , T₁ , T₂) (T₀ , T₂ , T₁) = refl
distribʳ-γ (T₂ , T₁ , T₂) (T₀ , T₂ , T₂) = refl
distribʳ-γ (T₂ , T₁ , T₂) (T₁ , T₀ , T₀) = refl
distribʳ-γ (T₂ , T₁ , T₂) (T₁ , T₀ , T₁) = refl
distribʳ-γ (T₂ , T₁ , T₂) (T₁ , T₀ , T₂) = refl
distribʳ-γ (T₂ , T₁ , T₂) (T₁ , T₁ , T₀) = refl
distribʳ-γ (T₂ , T₁ , T₂) (T₁ , T₁ , T₁) = refl
distribʳ-γ (T₂ , T₁ , T₂) (T₁ , T₁ , T₂) = refl
distribʳ-γ (T₂ , T₁ , T₂) (T₁ , T₂ , T₀) = refl
distribʳ-γ (T₂ , T₁ , T₂) (T₁ , T₂ , T₁) = refl
distribʳ-γ (T₂ , T₁ , T₂) (T₁ , T₂ , T₂) = refl
distribʳ-γ (T₂ , T₁ , T₂) (T₂ , T₀ , T₀) = refl
distribʳ-γ (T₂ , T₁ , T₂) (T₂ , T₀ , T₁) = refl
distribʳ-γ (T₂ , T₁ , T₂) (T₂ , T₀ , T₂) = refl
distribʳ-γ (T₂ , T₁ , T₂) (T₂ , T₁ , T₀) = refl
distribʳ-γ (T₂ , T₁ , T₂) (T₂ , T₁ , T₁) = refl
distribʳ-γ (T₂ , T₁ , T₂) (T₂ , T₁ , T₂) = refl
distribʳ-γ (T₂ , T₁ , T₂) (T₂ , T₂ , T₀) = refl
distribʳ-γ (T₂ , T₁ , T₂) (T₂ , T₂ , T₁) = refl
distribʳ-γ (T₂ , T₁ , T₂) (T₂ , T₂ , T₂) = refl
distribʳ-γ (T₂ , T₂ , T₀) (T₀ , T₀ , T₀) = refl
distribʳ-γ (T₂ , T₂ , T₀) (T₀ , T₀ , T₁) = refl
distribʳ-γ (T₂ , T₂ , T₀) (T₀ , T₀ , T₂) = refl
distribʳ-γ (T₂ , T₂ , T₀) (T₀ , T₁ , T₀) = refl
distribʳ-γ (T₂ , T₂ , T₀) (T₀ , T₁ , T₁) = refl
distribʳ-γ (T₂ , T₂ , T₀) (T₀ , T₁ , T₂) = refl
distribʳ-γ (T₂ , T₂ , T₀) (T₀ , T₂ , T₀) = refl
distribʳ-γ (T₂ , T₂ , T₀) (T₀ , T₂ , T₁) = refl
distribʳ-γ (T₂ , T₂ , T₀) (T₀ , T₂ , T₂) = refl
distribʳ-γ (T₂ , T₂ , T₀) (T₁ , T₀ , T₀) = refl
distribʳ-γ (T₂ , T₂ , T₀) (T₁ , T₀ , T₁) = refl
distribʳ-γ (T₂ , T₂ , T₀) (T₁ , T₀ , T₂) = refl
distribʳ-γ (T₂ , T₂ , T₀) (T₁ , T₁ , T₀) = refl
distribʳ-γ (T₂ , T₂ , T₀) (T₁ , T₁ , T₁) = refl
distribʳ-γ (T₂ , T₂ , T₀) (T₁ , T₁ , T₂) = refl
distribʳ-γ (T₂ , T₂ , T₀) (T₁ , T₂ , T₀) = refl
distribʳ-γ (T₂ , T₂ , T₀) (T₁ , T₂ , T₁) = refl
distribʳ-γ (T₂ , T₂ , T₀) (T₁ , T₂ , T₂) = refl
distribʳ-γ (T₂ , T₂ , T₀) (T₂ , T₀ , T₀) = refl
distribʳ-γ (T₂ , T₂ , T₀) (T₂ , T₀ , T₁) = refl
distribʳ-γ (T₂ , T₂ , T₀) (T₂ , T₀ , T₂) = refl
distribʳ-γ (T₂ , T₂ , T₀) (T₂ , T₁ , T₀) = refl
distribʳ-γ (T₂ , T₂ , T₀) (T₂ , T₁ , T₁) = refl
distribʳ-γ (T₂ , T₂ , T₀) (T₂ , T₁ , T₂) = refl
distribʳ-γ (T₂ , T₂ , T₀) (T₂ , T₂ , T₀) = refl
distribʳ-γ (T₂ , T₂ , T₀) (T₂ , T₂ , T₁) = refl
distribʳ-γ (T₂ , T₂ , T₀) (T₂ , T₂ , T₂) = refl
distribʳ-γ (T₂ , T₂ , T₁) (T₀ , T₀ , T₀) = refl
distribʳ-γ (T₂ , T₂ , T₁) (T₀ , T₀ , T₁) = refl
distribʳ-γ (T₂ , T₂ , T₁) (T₀ , T₀ , T₂) = refl
distribʳ-γ (T₂ , T₂ , T₁) (T₀ , T₁ , T₀) = refl
distribʳ-γ (T₂ , T₂ , T₁) (T₀ , T₁ , T₁) = refl
distribʳ-γ (T₂ , T₂ , T₁) (T₀ , T₁ , T₂) = refl
distribʳ-γ (T₂ , T₂ , T₁) (T₀ , T₂ , T₀) = refl
distribʳ-γ (T₂ , T₂ , T₁) (T₀ , T₂ , T₁) = refl
distribʳ-γ (T₂ , T₂ , T₁) (T₀ , T₂ , T₂) = refl
distribʳ-γ (T₂ , T₂ , T₁) (T₁ , T₀ , T₀) = refl
distribʳ-γ (T₂ , T₂ , T₁) (T₁ , T₀ , T₁) = refl
distribʳ-γ (T₂ , T₂ , T₁) (T₁ , T₀ , T₂) = refl
distribʳ-γ (T₂ , T₂ , T₁) (T₁ , T₁ , T₀) = refl
distribʳ-γ (T₂ , T₂ , T₁) (T₁ , T₁ , T₁) = refl
distribʳ-γ (T₂ , T₂ , T₁) (T₁ , T₁ , T₂) = refl
distribʳ-γ (T₂ , T₂ , T₁) (T₁ , T₂ , T₀) = refl
distribʳ-γ (T₂ , T₂ , T₁) (T₁ , T₂ , T₁) = refl
distribʳ-γ (T₂ , T₂ , T₁) (T₁ , T₂ , T₂) = refl
distribʳ-γ (T₂ , T₂ , T₁) (T₂ , T₀ , T₀) = refl
distribʳ-γ (T₂ , T₂ , T₁) (T₂ , T₀ , T₁) = refl
distribʳ-γ (T₂ , T₂ , T₁) (T₂ , T₀ , T₂) = refl
distribʳ-γ (T₂ , T₂ , T₁) (T₂ , T₁ , T₀) = refl
distribʳ-γ (T₂ , T₂ , T₁) (T₂ , T₁ , T₁) = refl
distribʳ-γ (T₂ , T₂ , T₁) (T₂ , T₁ , T₂) = refl
distribʳ-γ (T₂ , T₂ , T₁) (T₂ , T₂ , T₀) = refl
distribʳ-γ (T₂ , T₂ , T₁) (T₂ , T₂ , T₁) = refl
distribʳ-γ (T₂ , T₂ , T₁) (T₂ , T₂ , T₂) = refl
distribʳ-γ (T₂ , T₂ , T₂) (T₀ , T₀ , T₀) = refl
distribʳ-γ (T₂ , T₂ , T₂) (T₀ , T₀ , T₁) = refl
distribʳ-γ (T₂ , T₂ , T₂) (T₀ , T₀ , T₂) = refl
distribʳ-γ (T₂ , T₂ , T₂) (T₀ , T₁ , T₀) = refl
distribʳ-γ (T₂ , T₂ , T₂) (T₀ , T₁ , T₁) = refl
distribʳ-γ (T₂ , T₂ , T₂) (T₀ , T₁ , T₂) = refl
distribʳ-γ (T₂ , T₂ , T₂) (T₀ , T₂ , T₀) = refl
distribʳ-γ (T₂ , T₂ , T₂) (T₀ , T₂ , T₁) = refl
distribʳ-γ (T₂ , T₂ , T₂) (T₀ , T₂ , T₂) = refl
distribʳ-γ (T₂ , T₂ , T₂) (T₁ , T₀ , T₀) = refl
distribʳ-γ (T₂ , T₂ , T₂) (T₁ , T₀ , T₁) = refl
distribʳ-γ (T₂ , T₂ , T₂) (T₁ , T₀ , T₂) = refl
distribʳ-γ (T₂ , T₂ , T₂) (T₁ , T₁ , T₀) = refl
distribʳ-γ (T₂ , T₂ , T₂) (T₁ , T₁ , T₁) = refl
distribʳ-γ (T₂ , T₂ , T₂) (T₁ , T₁ , T₂) = refl
distribʳ-γ (T₂ , T₂ , T₂) (T₁ , T₂ , T₀) = refl
distribʳ-γ (T₂ , T₂ , T₂) (T₁ , T₂ , T₁) = refl
distribʳ-γ (T₂ , T₂ , T₂) (T₁ , T₂ , T₂) = refl
distribʳ-γ (T₂ , T₂ , T₂) (T₂ , T₀ , T₀) = refl
distribʳ-γ (T₂ , T₂ , T₂) (T₂ , T₀ , T₁) = refl
distribʳ-γ (T₂ , T₂ , T₂) (T₂ , T₀ , T₂) = refl
distribʳ-γ (T₂ , T₂ , T₂) (T₂ , T₁ , T₀) = refl
distribʳ-γ (T₂ , T₂ , T₂) (T₂ , T₁ , T₁) = refl
distribʳ-γ (T₂ , T₂ , T₂) (T₂ , T₁ , T₂) = refl
distribʳ-γ (T₂ , T₂ , T₂) (T₂ , T₂ , T₀) = refl
distribʳ-γ (T₂ , T₂ , T₂) (T₂ , T₂ , T₁) = refl
distribʳ-γ (T₂ , T₂ , T₂) (T₂ , T₂ , T₂) = refl

-- 立方零: 0³ = 0, 1³ = 1
cube-zero : cube27 zero27 ≡ zero27
cube-zero = refl

cube-one : cube27 one27 ≡ one27
cube-one = refl

-- t³ = t (GF(3) 中)
t³≡id : ∀ t → (t ⊗ t) ⊗ t ≡ t
t³≡id T₀ = refl
t³≡id T₁ = refl
t³≡id T₂ = refl

-- 立方自映射 (GF(3) 的 t³ = t 由 t³≡id 证明)
cubeTrit : Trit → Trit
cubeTrit t = (t ⊗ t) ⊗ t

-- 嵌入同态: emb(t⊗u) = emb t · emb u
emb-mul : ∀ t u → emb (t ⊗ u) ≡ emb t *₉ emb u
emb-mul t u = begin
  emb (t ⊗ u)
    ≡⟨⟩
  (t ⊗ u) , T₀ , T₀
    ≡⟨ cong₃ (λ p q r → p , q , r)
         (sym (trans (cong₂ _+₃_ refl (zeros4-e u t)) (⊕-identityʳ (t ⊗ u))))
         (sym (zeros2-e t u))
         (sym (zeros3-e t u)) ⟩
  emb t *₉ emb u
  ∎ where
    zeros4-e : ∀ u t → (T₀ ⊗ u) ⊕ ((T₀ ⊗ u) ⊕ ((T₀ ⊗ t) ⊕ (T₀ ⊗ t))) ≡ T₀
    zeros4-e u t = begin
      (T₀ ⊗ u) ⊕ ((T₀ ⊗ u) ⊕ ((T₀ ⊗ t) ⊕ (T₀ ⊗ t)))
        ≡⟨ cong₂ _+₃_ (⊗-zeroˡ u) (cong₂ _+₃_ (⊗-zeroˡ u) (cong₂ _+₃_ (⊗-zeroˡ t) (⊗-zeroˡ t))) ⟩
      T₀ ⊕ (T₀ ⊕ (T₀ ⊕ T₀))
        ≡⟨ ⊕-identityʳ (T₀ ⊕ (T₀ ⊕ T₀)) ⟩
      T₀ ⊕ (T₀ ⊕ T₀)
        ≡⟨ ⊕-identityʳ (T₀ ⊕ T₀) ⟩
      T₀ ⊕ T₀
        ≡⟨ ⊕-identityʳ T₀ ⟩
      T₀
      ∎
    zeros2-e : ∀ t u → (t ⊗ T₀) ⊕ ((T₀ ⊗ u) ⊕ ((T₀ ⊗ T₀) ⊕ ((T₀ ⊗ T₀) ⊕ ((T₀ ⊗ T₀) ⊕ (T₀ ⊗ T₀))))) ≡ T₀
    zeros2-e t u = begin
      (t ⊗ T₀) ⊕ ((T₀ ⊗ u) ⊕ ((T₀ ⊗ T₀) ⊕ ((T₀ ⊗ T₀) ⊕ ((T₀ ⊗ T₀) ⊕ (T₀ ⊗ T₀)))))
        ≡⟨ cong₂ _+₃_ (⊗-zeroʳ t) (cong₂ _+₃_ (⊗-zeroˡ u) (cong₂ _+₃_ (⊗-zeroˡ T₀) (cong₂ _+₃_ (⊗-zeroˡ T₀) (cong₂ _+₃_ (⊗-zeroˡ T₀) (⊗-zeroˡ T₀))))) ⟩
      T₀ ⊕ (T₀ ⊕ (T₀ ⊕ (T₀ ⊕ (T₀ ⊕ T₀))))
        ≡⟨ ⊕-identityʳ (T₀ ⊕ (T₀ ⊕ (T₀ ⊕ (T₀ ⊕ T₀)))) ⟩
      T₀ ⊕ (T₀ ⊕ (T₀ ⊕ (T₀ ⊕ T₀)))
        ≡⟨ ⊕-identityʳ (T₀ ⊕ (T₀ ⊕ (T₀ ⊕ T₀))) ⟩
      T₀ ⊕ (T₀ ⊕ (T₀ ⊕ T₀))
        ≡⟨ ⊕-identityʳ (T₀ ⊕ (T₀ ⊕ T₀)) ⟩
      T₀ ⊕ (T₀ ⊕ T₀)
        ≡⟨ ⊕-identityʳ (T₀ ⊕ T₀) ⟩
      T₀ ⊕ T₀
        ≡⟨ ⊕-identityʳ T₀ ⟩
      T₀
      ∎
    zeros3-e : ∀ t u → (t ⊗ T₀) ⊕ ((T₀ ⊗ T₀) ⊕ ((T₀ ⊗ u) ⊕ (T₀ ⊗ T₀))) ≡ T₀
    zeros3-e t u = begin
      (t ⊗ T₀) ⊕ ((T₀ ⊗ T₀) ⊕ ((T₀ ⊗ u) ⊕ (T₀ ⊗ T₀)))
        ≡⟨ cong₂ _+₃_ (⊗-zeroʳ t) (cong₂ _+₃_ (⊗-zeroˡ T₀) (cong₂ _+₃_ (⊗-zeroˡ u) (⊗-zeroˡ T₀))) ⟩
      T₀ ⊕ (T₀ ⊕ (T₀ ⊕ T₀))
        ≡⟨ ⊕-identityʳ (T₀ ⊕ (T₀ ⊕ T₀)) ⟩
      T₀ ⊕ (T₀ ⊕ T₀)
        ≡⟨ ⊕-identityʳ (T₀ ⊕ T₀) ⟩
      T₀ ⊕ T₀
        ≡⟨ ⊕-identityʳ T₀ ⟩
      T₀
      ∎

-- 嵌入立方: emb(t)³ = emb(t³)
embed-cube : ∀ t → cube27 (emb t) ≡ emb (cubeTrit t)
embed-cube t = begin
  cube27 (emb t)
    ≡⟨⟩
  (emb t *₉ emb t) *₉ emb t
    ≡⟨ cong (_*₉ emb t) (sym (emb-mul t t)) ⟩
  emb (t ⊗ t) *₉ emb t
    ≡⟨ sym (emb-mul (t ⊗ t) t) ⟩
  emb ((t ⊗ t) ⊗ t)
    ≡⟨⟩
  emb (cubeTrit t)
  ∎

--------------------------------------------------------------------------------
-- §3. 校验子机器
--------------------------------------------------------------------------------

-- γ 幂 (右乘递归)
γPow : ℕ → GF27
γPow zero = one27
γPow (suc n) = γPow n *₉ γ

-- γ³ 幂
γ3Pow : ℕ → GF27
γ3Pow zero = one27
γ3Pow (suc n) = γ3Pow n *₉ γ3

-- γ⁹ 幂
γ9Pow : ℕ → GF27
γ9Pow zero = one27
γ9Pow (suc n) = γ9Pow n *₉ γ9

-- 校验子: Σ_{k<n} emb(c k) · p k  (左结合显式和)
eval : (ℕ → Trit) → (ℕ → GF27) → ℕ → GF27
eval c p zero = zero27
eval c p (suc n) = eval c p n +₉ (emb (c n) *₉ p n)

-- 带偏移
evalFrom : (ℕ → Trit) → (ℕ → GF27) → ℕ → ℕ → GF27
evalFrom c p s zero = zero27
evalFrom c p s (suc n) = evalFrom c p s n +₉ (emb (c (s + n)) *₉ p (s + n))

-- 零消去
evalFrom-zero : ∀ c p s n → (∀ k → k < n → c (s + k) ≡ T₀) → evalFrom c p s n ≡ zero27
evalFrom-zero c p s zero    h = refl
evalFrom-zero c p s (suc n) h = begin
  evalFrom c p s n +₉ (emb (c (s + n)) *₉ p (s + n))
    ≡⟨ cong (_+₉ emb (c (s + n)) *₉ p (s + n)) (evalFrom-zero c p s n (λ k k<n → h k (m<n⇒m<1+n k<n))) ⟩
  zero27 +₉ (emb (c (s + n)) *₉ p (s + n))
    ≡⟨ cong (zero27 +₉_) (cong₂ _*₉_ (cong emb (h n (n<1+n n))) refl) ⟩
  zero27 +₉ (zero27 *₉ p (s + n))
    ≡⟨ cong (zero27 +₉_) (*27-zeroˡ (p (s + n))) ⟩
  zero27 +₉ zero27
    ≡⟨ +27-identityʳ zero27 ⟩
  zero27
  ∎

eval-zero : ∀ c p n → (∀ k → k < n → c k ≡ T₀) → eval c p n ≡ zero27
eval-zero c p zero    h = refl
eval-zero c p (suc n) h = begin
  eval c p n +₉ (emb (c n) *₉ p n)
    ≡⟨ cong (_+₉ emb (c n) *₉ p n) (eval-zero c p n (λ k k<n → h k (m<n⇒m<1+n k<n))) ⟩
  zero27 +₉ (emb (c n) *₉ p n)
    ≡⟨ cong (zero27 +₉_) (cong₂ _*₉_ (cong emb (h n (n<1+n n))) refl) ⟩
  zero27 +₉ (zero27 *₉ p n)
    ≡⟨ cong (zero27 +₉_) (*27-zeroˡ (p n)) ⟩
  zero27
  ∎

-- 拆分
eval-split : ∀ c p m n → eval c p (m + n) ≡ eval c p m +₉ evalFrom c p m n
eval-split c p m zero = begin
  eval c p (m + 0)
    ≡⟨ cong (λ n → eval c p n) (+-identityʳ m) ⟩
  eval c p m
    ≡⟨ sym (+27-identityʳ (eval c p m)) ⟩
  eval c p m +₉ zero27
  ∎
eval-split c p m (suc n) = begin
  eval c p (m + suc n)
    ≡⟨ cong (λ x → eval c p x) (+-suc m n) ⟩
  eval c p (m + n) +₉ (emb (c (m + n)) *₉ p (m + n))
    ≡⟨ cong (_+₉ emb (c (m + n)) *₉ p (m + n)) (eval-split c p m n) ⟩
  (eval c p m +₉ evalFrom c p m n) +₉ (emb (c (m + n)) *₉ p (m + n))
    ≡⟨ +27-assoc (eval c p m) (evalFrom c p m n) (emb (c (m + n)) *₉ p (m + n)) ⟩
  eval c p m +₉ (evalFrom c p m n +₉ (emb (c (m + n)) *₉ p (m + n)))
  ∎

-- 和立方: cube(eval c p n) ≡ eval (cube∘c) (cube∘p) n
sum-cube : ∀ c p n →
  cube27 (eval c p n) ≡ eval (λ k → cubeTrit (c k)) (λ k → cube27 (p k)) n
sum-cube c p zero = sym cube-zero
sum-cube c p (suc n) = begin
  cube27 (eval c p (suc n))
    ≡⟨⟩
  cube27 (eval c p n +₉ (emb (c n) *₉ p n))
    ≡⟨ cube-sum (eval c p n) (emb (c n) *₉ p n) ⟩
  cube27 (eval c p n) +₉ cube27 (emb (c n) *₉ p n)
    ≡⟨ cong (_+₉ cube27 (emb (c n) *₉ p n)) (sum-cube c p n) ⟩
  eval (λ k → cubeTrit (c k)) (λ k → cube27 (p k)) n +₉ cube27 (emb (c n) *₉ p n)
    ≡⟨ cong (eval (λ k → cubeTrit (c k)) (λ k → cube27 (p k)) n +₉_) (cube-mul (emb (c n)) (p n)) ⟩
  eval (λ k → cubeTrit (c k)) (λ k → cube27 (p k)) n +₉ (cube27 (emb (c n)) *₉ cube27 (p n))
    ≡⟨ cong (λ t → eval (λ k → cubeTrit (c k)) (λ k → cube27 (p k)) n +₉ (t *₉ cube27 (p n))) (embed-cube (c n)) ⟩
  eval (λ k → cubeTrit (c k)) (λ k → cube27 (p k)) n +₉ (emb (cubeTrit (c n)) *₉ cube27 (p n))
    ≡⟨⟩
  eval (λ k → cubeTrit (c k)) (λ k → cube27 (p k)) (suc n)
  ∎

-- γ 幂立方提升: (γᵏ)³ = (γ³)ᵏ
γ3Pow-cube : ∀ k → cube27 (γPow k) ≡ γ3Pow k
γ3Pow-cube zero = cube-one
γ3Pow-cube (suc n) = begin
  cube27 (γPow (suc n))
    ≡⟨⟩
  cube27 (γPow n *₉ γ)
    ≡⟨ cube-mul (γPow n) γ ⟩
  cube27 (γPow n) *₉ cube27 γ
    ≡⟨ cong (_*₉ cube27 γ) (γ3Pow-cube n) ⟩
  γ3Pow n *₉ cube27 γ
    ≡⟨ cong (γ3Pow n *₉_) gamma-cube ⟩
  γ3Pow n *₉ γ3
    ≡⟨⟩
  γ3Pow (suc n)
  ∎

-- (γ³ᵏ)³ = (γ⁹)ᵏ
γ9Pow-cube : ∀ k → cube27 (γ3Pow k) ≡ γ9Pow k
γ9Pow-cube zero = cube-one
γ9Pow-cube (suc n) = begin
  cube27 (γ3Pow (suc n))
    ≡⟨⟩
  cube27 (γ3Pow n *₉ γ3)
    ≡⟨ cube-mul (γ3Pow n) γ3 ⟩
  cube27 (γ3Pow n) *₉ cube27 γ3
    ≡⟨ cong (_*₉ cube27 γ3) (γ9Pow-cube n) ⟩
  γ9Pow n *₉ cube27 γ3
    ≡⟨ cong (γ9Pow n *₉_) (proj₁ (proj₂ frobenius-cycle)) ⟩
  γ9Pow n *₉ γ9
    ≡⟨⟩
  γ9Pow (suc n)
  ∎

-- γ 的阶: γ²⁶ = 1
γ-pow-26 : γPow 26 ≡ one27
γ-pow-26 = refl

--------------------------------------------------------------------------------
-- §4. 三根定理: c(γ)=0 ⟹ c(γ³)=c(γ⁹)=0
--------------------------------------------------------------------------------

-- 逐点相等 ⟹ 和相等 (双参数)
eval-cong2 : ∀ c c' p p' n →
  (∀ k → k < n → c k ≡ c' k) → (∀ k → k < n → p k ≡ p' k) → eval c p n ≡ eval c' p' n
eval-cong2 c c' p p' zero    hc hp = refl
eval-cong2 c c' p p' (suc n) hc hp = cong₂ _+₉_
  (eval-cong2 c c' p p' n (λ k k<n → hc k (m<n⇒m<1+n k<n)) (λ k k<n → hp k (m<n⇒m<1+n k<n)))
  (cong₂ _*₉_ (cong emb (hc n (s≤s ≤-refl))) (hp n (s≤s ≤-refl)))

-- c(γ³) = c(γ)³
eval-at-γ3 : ∀ c → eval c γ3Pow 26 ≡ cube27 (eval c γPow 26)
eval-at-γ3 c = begin
  eval c γ3Pow 26
    ≡⟨ eval-cong2 c (λ k → cubeTrit (c k)) γ3Pow (λ k → cube27 (γPow k)) 26
         (λ k _ → sym (t³≡id (c k)))
         (λ k _ → sym (γ3Pow-cube k)) ⟩
  eval (λ k → cubeTrit (c k)) (λ k → cube27 (γPow k)) 26
    ≡⟨ sym (sum-cube c γPow 26) ⟩
  cube27 (eval c γPow 26)
  ∎ where
    t³ : Trit → Trit
    t³ t = (t ⊗ t) ⊗ t

-- c(γ⁹) = c(γ³)³
eval-at-γ9 : ∀ c → eval c γ9Pow 26 ≡ cube27 (eval c γ3Pow 26)
eval-at-γ9 c = begin
  eval c γ9Pow 26
    ≡⟨ eval-cong2 c (λ k → cubeTrit (c k)) γ9Pow (λ k → cube27 (γ3Pow k)) 26
         (λ k _ → sym (t³≡id (c k)))
         (λ k _ → sym (γ9Pow-cube k)) ⟩
  eval (λ k → cubeTrit (c k)) (λ k → cube27 (γ3Pow k)) 26
    ≡⟨ sym (sum-cube c γ3Pow 26) ⟩
  cube27 (eval c γ3Pow 26)
  ∎ where
    t³ : Trit → Trit
    t³ t = (t ⊗ t) ⊗ t

--------------------------------------------------------------------------------
-- §5. 循环码
--------------------------------------------------------------------------------

-- 三元循环码 (长度 26): C = { c | c(γ) = 0 }
IsCodeword : (ℕ → Trit) → Set
IsCodeword c = eval c γPow 26 ≡ zero27

-- 循环移位
shift : (ℕ → Trit) → ℕ → Trit
shift c zero = c 25
shift c (suc k) = c k

-- shift(c)(γ) = γ · c(γ)
shift-eval : ∀ c → eval (shift c) γPow 26 ≡ γ *₉ eval c γPow 26
shift-eval c = begin
  eval (shift c) γPow 26
    ≡⟨ eval-split (shift c) γPow 1 25 ⟩
  eval (shift c) γPow 1 +₉ evalFrom (shift c) γPow 1 25
    ≡⟨⟩
  zero27 +₉ (emb (shift c 0) *₉ γPow 0) +₉ evalFrom (shift c) γPow 1 25
    ≡⟨⟩
  zero27 +₉ (emb (c 25) *₉ γPow 0) +₉ evalFrom (shift c) γPow 1 25
    ≡⟨ cong (λ t → zero27 +₉ t +₉ evalFrom (shift c) γPow 1 25) (*27-identityʳ (emb (c 25))) ⟩
  zero27 +₉ emb (c 25) +₉ evalFrom (shift c) γPow 1 25
    ≡⟨ +27-assoc zero27 (emb (c 25)) (evalFrom (shift c) γPow 1 25) ⟩
  (zero27 +₉ emb (c 25)) +₉ evalFrom (shift c) γPow 1 25
    ≡⟨ cong (_+₉ evalFrom (shift c) γPow 1 25) (head-zero (emb (c 25))) ⟩
  emb (c 25) +₉ evalFrom (shift c) γPow 1 25
    ≡⟨ cong (emb (c 25) +₉_) (evalFrom-shift c) ⟩
  emb (c 25) +₉ (eval c γPow 25 *₉ γ)
    ≡⟨ +27-comm (emb (c 25)) (eval c γPow 25 *₉ γ) ⟩
  (eval c γPow 25 *₉ γ) +₉ emb (c 25)
    ≡⟨ sym (γ-distrib c) ⟩
  γ *₉ eval c γPow 26
  ∎ where
    head-zero : ∀ A → zero27 +₉ A ≡ A
    head-zero A = begin
      zero27 +₉ A
        ≡⟨ +27-comm zero27 A ⟩
      A +₉ zero27
        ≡⟨ +27-identityʳ A ⟩
      A
      ∎
    sum-shift : ∀ c n → eval c γPow n *₉ γ ≡ evalFrom (shift c) γPow 1 n
    sum-shift c zero = begin
      eval c γPow 0 *₉ γ
        ≡⟨⟩
      zero27 *₉ γ
        ≡⟨ *27-zeroˡ γ ⟩
      zero27
      ∎
    sum-shift c (suc n) = begin
      eval c γPow (suc n) *₉ γ
        ≡⟨⟩
      (eval c γPow n +₉ (emb (c n) *₉ γPow n)) *₉ γ
        ≡⟨ distribʳ-γ (eval c γPow n) (emb (c n) *₉ γPow n) ⟩
      (eval c γPow n *₉ γ) +₉ ((emb (c n) *₉ γPow n) *₉ γ)
        ≡⟨ cong (_+₉ ((emb (c n) *₉ γPow n) *₉ γ)) (sum-shift c n) ⟩
      evalFrom (shift c) γPow 1 n +₉ ((emb (c n) *₉ γPow n) *₉ γ)
        ≡⟨ cong (evalFrom (shift c) γPow 1 n +₉_) (assoc-γ (emb (c n)) (γPow n)) ⟩
      evalFrom (shift c) γPow 1 n +₉ (emb (c n) *₉ (γPow n *₉ γ))
        ≡⟨⟩
      evalFrom (shift c) γPow 1 n +₉ (emb (shift c (suc n)) *₉ γPow (suc n))
        ≡⟨⟩
      evalFrom (shift c) γPow 1 (suc n)
      ∎
    evalFrom-shift : ∀ c → evalFrom (shift c) γPow 1 25 ≡ eval c γPow 25 *₉ γ
    evalFrom-shift c = begin
      evalFrom (shift c) γPow 1 25
        ≡⟨ sym (sum-shift c 25) ⟩
      (eval c γPow 25) *₉ γ
      ∎
    γ-distrib : ∀ c → γ *₉ eval c γPow 26 ≡ (eval c γPow 25 *₉ γ) +₉ emb (c 25)
    γ-distrib c = begin
      γ *₉ eval c γPow 26
        ≡⟨⟩
      γ *₉ (eval c γPow 25 +₉ (emb (c 25) *₉ γPow 25))
        ≡⟨ distribˡ-γ (eval c γPow 25) (emb (c 25) *₉ γPow 25) ⟩
      (γ *₉ eval c γPow 25) +₉ (γ *₉ (emb (c 25) *₉ γPow 25))
        ≡⟨ cong (_+₉ (γ *₉ (emb (c 25) *₉ γPow 25))) (*27-comm γ (eval c γPow 25)) ⟩
      (eval c γPow 25 *₉ γ) +₉ (γ *₉ (emb (c 25) *₉ γPow 25))
        ≡⟨ cong (λ t → (eval c γPow 25 *₉ γ) +₉ t) (*27-comm γ (emb (c 25) *₉ γPow 25)) ⟩
      (eval c γPow 25 *₉ γ) +₉ ((emb (c 25) *₉ γPow 25) *₉ γ)
        ≡⟨ cong (λ t → (eval c γPow 25 *₉ γ) +₉ t) (assoc-γ (emb (c 25)) (γPow 25)) ⟩
      (eval c γPow 25 *₉ γ) +₉ (emb (c 25) *₉ (γPow 25 *₉ γ))
        ≡⟨ cong (λ t → (eval c γPow 25 *₉ γ) +₉ (emb (c 25) *₉ t)) (γ-pow-25-γ) ⟩
      (eval c γPow 25 *₉ γ) +₉ (emb (c 25) *₉ one27)
        ≡⟨ cong (λ t → (eval c γPow 25 *₉ γ) +₉ t) (*27-identityʳ (emb (c 25))) ⟩
      (eval c γPow 25 *₉ γ) +₉ emb (c 25)
      ∎ where
        γ-pow-25-γ : γPow 25 *₉ γ ≡ one27
        γ-pow-25-γ = γ-pow-26

-- 循环码封闭性: C c ⟹ C (shift c)
cyclic-closed : ∀ c → IsCodeword c → IsCodeword (shift c)
cyclic-closed c cw = begin
  eval (shift c) γPow 26
    ≡⟨ shift-eval c ⟩
  γ *₉ eval c γPow 26
    ≡⟨ cong (γ *₉_) cw ⟩
  γ *₉ zero27
    ≡⟨ *27-zeroʳ γ ⟩
  zero27
  ∎

-- 三根: c(γ)=0 ⟹ c(γ³)=0
root-γ3 : ∀ c → IsCodeword c → eval c γ3Pow 26 ≡ zero27
root-γ3 c cw = begin
  eval c γ3Pow 26
    ≡⟨ eval-at-γ3 c ⟩
  cube27 (eval c γPow 26)
    ≡⟨ cong cube27 cw ⟩
  cube27 zero27
    ≡⟨ cube-zero ⟩
  zero27
  ∎

-- 三根: c(γ)=0 ⟹ c(γ⁹)=0
root-γ9 : ∀ c → IsCodeword c → eval c γ9Pow 26 ≡ zero27
root-γ9 c cw = begin
  eval c γ9Pow 26
    ≡⟨ eval-at-γ9 c ⟩
  cube27 (eval c γ3Pow 26)
    ≡⟨ cong cube27 (root-γ3 c cw) ⟩
  cube27 zero27
    ≡⟨ cube-zero ⟩
  zero27
  ∎

-- g 的三根见证 (引用 GF27Separation, g(γ)=g(γ³)=g(γ⁹)=0)
generator-root-gamma  = root-gamma
generator-root-gamma3 = root-gamma3
generator-root-gamma9 = root-gamma9

-- γ 的本原性 (阶 26): γ¹³ = −1 ⟹ 阶 = 26 = |GF(27)*|
generator-order-26 : (γ *₉ γ3) *₉ γ9 ≡ (T₂ , T₀ , T₀)
generator-order-26 = refl
