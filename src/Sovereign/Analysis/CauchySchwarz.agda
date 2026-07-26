{-# OPTIONS --rewriting #-}
module Sovereign.Analysis.CauchySchwarz where

--------------------------------------------------------------------------------
-- Cauchy-Schwarz 不等式与三角不等式 — GF(3) 内积空间的有限域版本
--
-- 核心定理:
--   1. Cauchy-Schwarz: N(⟨f,g⟩) ≤ N(⟨f,f⟩)·N(⟨g,g⟩)  (n=1, n=2)
--   2. 三角不等式:     ‖f+g‖ ≤ ‖f‖ + ‖g‖              (所有 n)
--
-- 证明策略: GF(3) 穷举法 (有限域仅 3 个元素)
--   n=1: 3×3 = 9 case, 等号成立
--   n=2: 结构化穷举 — 利用 GF(3)² 无各向同性向量
--
-- 关键限制:
--   GF(3) 内积是退化的 (存在各向同性向量), Cauchy-Schwarz 仅在
--   无各向同性向量的维度 (n≤2) 成立。n≥3 时 (1,1,1) 是各向同性向量,
--   CS 不等式失效 (见 §6 反例)。
--
-- 依赖:
--   Sovereign.Base.Trit — GF(3) 三进制本体
--   Sovereign.Algebra.FunctionalDiscrete — 内积空间结构
--
-- 0 postulate — 全部构造性证明
--------------------------------------------------------------------------------

open import Data.Nat using (ℕ; zero; suc)
open import Data.Vec using (Vec; []; _∷_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (¬_)
open import Function using (id; _∘_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; cong; cong₂; sym; trans; subst; subst₂)

open import Sovereign.Base.Trit using (
  Trit; T₀; T₁; T₂; _⊕_; _⊗_; negate;
  ⊕-identityˡ; ⊕-identityʳ; ⊕-comm; ⊕-assoc;
  ⊗-identityˡ; ⊗-identityʳ; ⊗-comm; ⊗-assoc;
  ⊗-distribˡ-⊕; ⊗-distribʳ-⊕;
  ⊗-zeroˡ; ⊗-zeroʳ)

open import Sovereign.Algebra.FunctionalDiscrete using (
  _+v_; _·v_; 0⃗;
  standard-inner-product; discrete-norm; quadratic-form;
  abs-gf3; norm-two-valued; norm-zero→vec-zero; norm-of-zero;
  vec-zero→norm-zero;
  +v-identityˡ; +v-identityʳ;
  isotropic-example; isotropic-nonzero)

--------------------------------------------------------------------------------
-- §1. Trit 全序 — T₀ < T₁ < T₂
--
-- GF(3) 上的自然序: 0 < 1 < 2
-- 用于表述 Cauchy-Schwarz 不等式中的 "≤"
--------------------------------------------------------------------------------

infix 4 _≤T_
data _≤T_ : Trit → Trit → Set where
  ≤T-00 : T₀ ≤T T₀
  ≤T-01 : T₀ ≤T T₁
  ≤T-02 : T₀ ≤T T₂
  ≤T-11 : T₁ ≤T T₁
  ≤T-12 : T₁ ≤T T₂
  ≤T-22 : T₂ ≤T T₂

-- ≤T 自反
≤T-refl : ∀ x → x ≤T x
≤T-refl T₀ = ≤T-00
≤T-refl T₁ = ≤T-11
≤T-refl T₂ = ≤T-22

-- 任何 Trit ≤T T₂ (T₂ 是最大值)
≤T-max : ∀ x → x ≤T T₂
≤T-max T₀ = ≤T-02
≤T-max T₁ = ≤T-12
≤T-max T₂ = ≤T-22

-- ≤T 传递
≤T-trans : ∀ {x y z} → x ≤T y → y ≤T z → x ≤T z
≤T-trans ≤T-00 ≤T-00 = ≤T-00
≤T-trans ≤T-00 ≤T-01 = ≤T-01
≤T-trans ≤T-00 ≤T-02 = ≤T-02
≤T-trans ≤T-01 ≤T-11 = ≤T-01
≤T-trans ≤T-01 ≤T-12 = ≤T-02
≤T-trans ≤T-02 ≤T-22 = ≤T-02
≤T-trans ≤T-11 ≤T-11 = ≤T-11
≤T-trans ≤T-11 ≤T-12 = ≤T-12
≤T-trans ≤T-12 ≤T-22 = ≤T-12
≤T-trans ≤T-22 ≤T-22 = ≤T-22

--------------------------------------------------------------------------------
-- §2. 范数平方 — N(a) = a·a (GF(3) 上的 "绝对值平方")
--
-- 在 GF(3) 中 (conj = id, 因为 GF(3) 是素域):
--   N(T₀) = T₀·T₀ = T₀  (零)
--   N(T₁) = T₁·T₁ = T₁  (单位)
--   N(T₂) = T₂·T₂ = T₁  (因为 2²=4≡1 mod 3)
--
-- N 的值域为 {T₀, T₁}: 零→T₀, 非零→T₁
-- 等价于 abs-gf3
--------------------------------------------------------------------------------

norm-sq : Trit → Trit
norm-sq x = x ⊗ x

-- N 的值计算
norm-sq-T₀ : norm-sq T₀ ≡ T₀
norm-sq-T₀ = refl

norm-sq-T₁ : norm-sq T₁ ≡ T₁
norm-sq-T₁ = refl

norm-sq-T₂ : norm-sq T₂ ≡ T₁
norm-sq-T₂ = refl

-- N(x) ≤T T₁ 对所有 x (值域 {T₀, T₁})
norm-sq-≤₁ : ∀ x → norm-sq x ≤T T₁
norm-sq-≤₁ T₀ = ≤T-01
norm-sq-≤₁ T₁ = ≤T-11
norm-sq-≤₁ T₂ = ≤T-11

-- N(x) = T₀ 当且仅当 x = T₀
norm-sq-eq-T₀ : ∀ x → norm-sq x ≡ T₀ → x ≡ T₀
norm-sq-eq-T₀ T₀ _ = refl
norm-sq-eq-T₀ T₁ ()
norm-sq-eq-T₀ T₂ ()

-- N 与 abs-gf3 一致
norm-sq-is-abs : ∀ x → norm-sq x ≡ abs-gf3 x
norm-sq-is-abs T₀ = refl
norm-sq-is-abs T₁ = refl
norm-sq-is-abs T₂ = refl

--------------------------------------------------------------------------------
-- §3. Cauchy-Schwarz 不等式 — n=1 (9 case 穷举)
--
-- 定理: N(⟨f,g⟩) ≤ N(⟨f,f⟩)·N(⟨g,g⟩)
-- 对 n=1: f=(a), g=(b), ⟨f,g⟩=a·b
--   N(a·b) = (a·b)² = a²·b² = N(a)·N(b) = N(⟨f,f⟩)·N(⟨g,g⟩)
--   等号成立!
--------------------------------------------------------------------------------

cauchy-schwarz-1 : ∀ (a b : Trit) →
  norm-sq (a ⊗ b)
  ≤T norm-sq (a ⊗ a) ⊗ norm-sq (b ⊗ b)
cauchy-schwarz-1 T₀ T₀ = ≤T-00
cauchy-schwarz-1 T₀ T₁ = ≤T-00
cauchy-schwarz-1 T₀ T₂ = ≤T-00
cauchy-schwarz-1 T₁ T₀ = ≤T-00
cauchy-schwarz-1 T₁ T₁ = ≤T-11
cauchy-schwarz-1 T₁ T₂ = ≤T-11
cauchy-schwarz-1 T₂ T₀ = ≤T-00
cauchy-schwarz-1 T₂ T₁ = ≤T-11
cauchy-schwarz-1 T₂ T₂ = ≤T-11

-- n=1 等号成立: N(a·b) ≡ N(a)·N(b)
-- 这是 GF(3) 上 Fermat 小定理的直接推论: a⁴ = a² (因为 a³ = a)
cauchy-schwarz-1-equality : ∀ (a b : Trit) →
  norm-sq (a ⊗ b) ≡ norm-sq (a ⊗ a) ⊗ norm-sq (b ⊗ b)
cauchy-schwarz-1-equality T₀ T₀ = refl
cauchy-schwarz-1-equality T₀ T₁ = refl
cauchy-schwarz-1-equality T₀ T₂ = refl
cauchy-schwarz-1-equality T₁ T₀ = refl
cauchy-schwarz-1-equality T₁ T₁ = refl
cauchy-schwarz-1-equality T₁ T₂ = refl
cauchy-schwarz-1-equality T₂ T₀ = refl
cauchy-schwarz-1-equality T₂ T₁ = refl
cauchy-schwarz-1-equality T₂ T₂ = refl

--------------------------------------------------------------------------------
-- §4. Cauchy-Schwarz 不等式 — n=2 (结构化穷举)
--
-- 关键引理: GF(3)² 中无各向同性向量
--   Q(a₁,a₂) = a₁²+a₂² = T₀ 当且仅当 a₁=a₂=T₀
--   (因为 a² ∈ {T₀,T₁}, 而 T₁⊕T₁=T₂≠T₀)
--
-- 证明策略:
--   Case 1: f=0 → ⟨f,g⟩=0, 两边均为 T₀
--   Case 2: g=0 → ⟨f,g⟩=0, 两边均为 T₀
--   Case 3: f≠0 且 g≠0 → N(Q(f))=T₁, N(Q(g))=T₁, RHS=T₁,
--           LHS=N(⟨f,g⟩)≤T₁ (因为 N 值域 {T₀,T₁})
--------------------------------------------------------------------------------

-- GF(3)² 无各向同性向量: Q(f)=T₀ → f=0
no-isotropic-2 : ∀ a₁ a₂ →
  (a₁ ⊗ a₁) ⊕ (a₂ ⊗ a₂) ≡ T₀ → a₁ ≡ T₀ × a₂ ≡ T₀
no-isotropic-2 T₀ T₀ _ = refl , refl
no-isotropic-2 T₀ T₁ ()
no-isotropic-2 T₀ T₂ ()
no-isotropic-2 T₁ T₀ ()
no-isotropic-2 T₁ T₁ ()
no-isotropic-2 T₁ T₂ ()
no-isotropic-2 T₂ T₀ ()
no-isotropic-2 T₂ T₁ ()
no-isotropic-2 T₂ T₂ ()

-- 内积与零向量为零 (左)
ip-zeroˡ : ∀ n (ys : Vec Trit n) →
  standard-inner-product n (0⃗ n) ys ≡ T₀
ip-zeroˡ zero [] = refl
ip-zeroˡ (suc n) (y ∷ ys) =
  cong₂ _⊕_ (⊗-zeroˡ y) (ip-zeroˡ n ys)

-- 内积与零向量为零 (右)
ip-zeroʳ : ∀ n (xs : Vec Trit n) →
  standard-inner-product n xs (0⃗ n) ≡ T₀
ip-zeroʳ zero [] = refl
ip-zeroʳ (suc n) (x ∷ xs) =
  cong₂ _⊕_ (⊗-zeroʳ x) (ip-zeroʳ n xs)

-- Cauchy-Schwarz 不等式 n=2
-- N(⟨f,g⟩) ≤ N(⟨f,f⟩)·N(⟨g,g⟩)
-- 66 clauses: 1 (f=0) + 1 (g=0) + 64 (f≠0, g≠0)
cauchy-schwarz-2 : ∀ (f g : Vec Trit 2) →
  norm-sq (standard-inner-product 2 f g)
  ≤T norm-sq (standard-inner-product 2 f f)
     ⊗ norm-sq (standard-inner-product 2 g g)
-- f = (T₀, T₀) = 0⃗: ⟨f,g⟩=T₀, LHS=T₀, RHS=T₀⊗...=T₀
cauchy-schwarz-2 (T₀ ∷ T₀ ∷ []) (b₁ ∷ b₂ ∷ []) = ≤T-00
-- g = (T₀, T₀) = 0⃗, f≠0: ⟨f,g⟩=T₀, LHS=T₀, RHS=...⊗T₀=T₀
cauchy-schwarz-2 (T₀ ∷ T₁ ∷ []) (T₀ ∷ T₀ ∷ []) = ≤T-00
cauchy-schwarz-2 (T₀ ∷ T₂ ∷ []) (T₀ ∷ T₀ ∷ []) = ≤T-00
cauchy-schwarz-2 (T₁ ∷ T₀ ∷ []) (T₀ ∷ T₀ ∷ []) = ≤T-00
cauchy-schwarz-2 (T₁ ∷ T₁ ∷ []) (T₀ ∷ T₀ ∷ []) = ≤T-00
cauchy-schwarz-2 (T₁ ∷ T₂ ∷ []) (T₀ ∷ T₀ ∷ []) = ≤T-00
cauchy-schwarz-2 (T₂ ∷ T₀ ∷ []) (T₀ ∷ T₀ ∷ []) = ≤T-00
cauchy-schwarz-2 (T₂ ∷ T₁ ∷ []) (T₀ ∷ T₀ ∷ []) = ≤T-00
cauchy-schwarz-2 (T₂ ∷ T₂ ∷ []) (T₀ ∷ T₀ ∷ []) = ≤T-00
-- f≠0, g≠0: RHS = T₁⊗T₁ = T₁, LHS = N(⟨f,g⟩) ≤T T₁
-- f = (T₀, T₁): ⟨f,g⟩ = b₂
cauchy-schwarz-2 (T₀ ∷ T₁ ∷ []) (T₀ ∷ T₁ ∷ []) = norm-sq-≤₁ T₁
cauchy-schwarz-2 (T₀ ∷ T₁ ∷ []) (T₀ ∷ T₂ ∷ []) = norm-sq-≤₁ T₂
cauchy-schwarz-2 (T₀ ∷ T₁ ∷ []) (T₁ ∷ T₀ ∷ []) = norm-sq-≤₁ T₀
cauchy-schwarz-2 (T₀ ∷ T₁ ∷ []) (T₁ ∷ T₁ ∷ []) = norm-sq-≤₁ T₁
cauchy-schwarz-2 (T₀ ∷ T₁ ∷ []) (T₁ ∷ T₂ ∷ []) = norm-sq-≤₁ T₂
cauchy-schwarz-2 (T₀ ∷ T₁ ∷ []) (T₂ ∷ T₀ ∷ []) = norm-sq-≤₁ T₀
cauchy-schwarz-2 (T₀ ∷ T₁ ∷ []) (T₂ ∷ T₁ ∷ []) = norm-sq-≤₁ T₁
cauchy-schwarz-2 (T₀ ∷ T₁ ∷ []) (T₂ ∷ T₂ ∷ []) = norm-sq-≤₁ T₂
-- f = (T₀, T₂): ⟨f,g⟩ = T₂⊗b₂
cauchy-schwarz-2 (T₀ ∷ T₂ ∷ []) (T₀ ∷ T₁ ∷ []) = norm-sq-≤₁ T₂
cauchy-schwarz-2 (T₀ ∷ T₂ ∷ []) (T₀ ∷ T₂ ∷ []) = norm-sq-≤₁ T₁
cauchy-schwarz-2 (T₀ ∷ T₂ ∷ []) (T₁ ∷ T₀ ∷ []) = norm-sq-≤₁ T₀
cauchy-schwarz-2 (T₀ ∷ T₂ ∷ []) (T₁ ∷ T₁ ∷ []) = norm-sq-≤₁ T₂
cauchy-schwarz-2 (T₀ ∷ T₂ ∷ []) (T₁ ∷ T₂ ∷ []) = norm-sq-≤₁ T₁
cauchy-schwarz-2 (T₀ ∷ T₂ ∷ []) (T₂ ∷ T₀ ∷ []) = norm-sq-≤₁ T₀
cauchy-schwarz-2 (T₀ ∷ T₂ ∷ []) (T₂ ∷ T₁ ∷ []) = norm-sq-≤₁ T₂
cauchy-schwarz-2 (T₀ ∷ T₂ ∷ []) (T₂ ∷ T₂ ∷ []) = norm-sq-≤₁ T₁
-- f = (T₁, T₀): ⟨f,g⟩ = b₁
cauchy-schwarz-2 (T₁ ∷ T₀ ∷ []) (T₀ ∷ T₁ ∷ []) = norm-sq-≤₁ T₀
cauchy-schwarz-2 (T₁ ∷ T₀ ∷ []) (T₀ ∷ T₂ ∷ []) = norm-sq-≤₁ T₀
cauchy-schwarz-2 (T₁ ∷ T₀ ∷ []) (T₁ ∷ T₀ ∷ []) = norm-sq-≤₁ T₁
cauchy-schwarz-2 (T₁ ∷ T₀ ∷ []) (T₁ ∷ T₁ ∷ []) = norm-sq-≤₁ T₁
cauchy-schwarz-2 (T₁ ∷ T₀ ∷ []) (T₁ ∷ T₂ ∷ []) = norm-sq-≤₁ T₁
cauchy-schwarz-2 (T₁ ∷ T₀ ∷ []) (T₂ ∷ T₀ ∷ []) = norm-sq-≤₁ T₂
cauchy-schwarz-2 (T₁ ∷ T₀ ∷ []) (T₂ ∷ T₁ ∷ []) = norm-sq-≤₁ T₂
cauchy-schwarz-2 (T₁ ∷ T₀ ∷ []) (T₂ ∷ T₂ ∷ []) = norm-sq-≤₁ T₂
-- f = (T₁, T₁): ⟨f,g⟩ = b₁⊕b₂
cauchy-schwarz-2 (T₁ ∷ T₁ ∷ []) (T₀ ∷ T₁ ∷ []) = norm-sq-≤₁ T₁
cauchy-schwarz-2 (T₁ ∷ T₁ ∷ []) (T₀ ∷ T₂ ∷ []) = norm-sq-≤₁ T₂
cauchy-schwarz-2 (T₁ ∷ T₁ ∷ []) (T₁ ∷ T₀ ∷ []) = norm-sq-≤₁ T₁
cauchy-schwarz-2 (T₁ ∷ T₁ ∷ []) (T₁ ∷ T₁ ∷ []) = norm-sq-≤₁ T₂
cauchy-schwarz-2 (T₁ ∷ T₁ ∷ []) (T₁ ∷ T₂ ∷ []) = norm-sq-≤₁ T₀
cauchy-schwarz-2 (T₁ ∷ T₁ ∷ []) (T₂ ∷ T₀ ∷ []) = norm-sq-≤₁ T₂
cauchy-schwarz-2 (T₁ ∷ T₁ ∷ []) (T₂ ∷ T₁ ∷ []) = norm-sq-≤₁ T₀
cauchy-schwarz-2 (T₁ ∷ T₁ ∷ []) (T₂ ∷ T₂ ∷ []) = norm-sq-≤₁ T₁
-- f = (T₁, T₂): ⟨f,g⟩ = b₁⊕(T₂⊗b₂)
cauchy-schwarz-2 (T₁ ∷ T₂ ∷ []) (T₀ ∷ T₁ ∷ []) = norm-sq-≤₁ T₂
cauchy-schwarz-2 (T₁ ∷ T₂ ∷ []) (T₀ ∷ T₂ ∷ []) = norm-sq-≤₁ T₁
cauchy-schwarz-2 (T₁ ∷ T₂ ∷ []) (T₁ ∷ T₀ ∷ []) = norm-sq-≤₁ T₁
cauchy-schwarz-2 (T₁ ∷ T₂ ∷ []) (T₁ ∷ T₁ ∷ []) = norm-sq-≤₁ T₀
cauchy-schwarz-2 (T₁ ∷ T₂ ∷ []) (T₁ ∷ T₂ ∷ []) = norm-sq-≤₁ T₂
cauchy-schwarz-2 (T₁ ∷ T₂ ∷ []) (T₂ ∷ T₀ ∷ []) = norm-sq-≤₁ T₂
cauchy-schwarz-2 (T₁ ∷ T₂ ∷ []) (T₂ ∷ T₁ ∷ []) = norm-sq-≤₁ T₁
cauchy-schwarz-2 (T₁ ∷ T₂ ∷ []) (T₂ ∷ T₂ ∷ []) = norm-sq-≤₁ T₀
-- f = (T₂, T₀): ⟨f,g⟩ = T₂⊗b₁
cauchy-schwarz-2 (T₂ ∷ T₀ ∷ []) (T₀ ∷ T₁ ∷ []) = norm-sq-≤₁ T₀
cauchy-schwarz-2 (T₂ ∷ T₀ ∷ []) (T₀ ∷ T₂ ∷ []) = norm-sq-≤₁ T₀
cauchy-schwarz-2 (T₂ ∷ T₀ ∷ []) (T₁ ∷ T₀ ∷ []) = norm-sq-≤₁ T₂
cauchy-schwarz-2 (T₂ ∷ T₀ ∷ []) (T₁ ∷ T₁ ∷ []) = norm-sq-≤₁ T₂
cauchy-schwarz-2 (T₂ ∷ T₀ ∷ []) (T₁ ∷ T₂ ∷ []) = norm-sq-≤₁ T₂
cauchy-schwarz-2 (T₂ ∷ T₀ ∷ []) (T₂ ∷ T₀ ∷ []) = norm-sq-≤₁ T₁
cauchy-schwarz-2 (T₂ ∷ T₀ ∷ []) (T₂ ∷ T₁ ∷ []) = norm-sq-≤₁ T₁
cauchy-schwarz-2 (T₂ ∷ T₀ ∷ []) (T₂ ∷ T₂ ∷ []) = norm-sq-≤₁ T₁
-- f = (T₂, T₁): ⟨f,g⟩ = (T₂⊗b₁)⊕b₂
cauchy-schwarz-2 (T₂ ∷ T₁ ∷ []) (T₀ ∷ T₁ ∷ []) = norm-sq-≤₁ T₁
cauchy-schwarz-2 (T₂ ∷ T₁ ∷ []) (T₀ ∷ T₂ ∷ []) = norm-sq-≤₁ T₂
cauchy-schwarz-2 (T₂ ∷ T₁ ∷ []) (T₁ ∷ T₀ ∷ []) = norm-sq-≤₁ T₂
cauchy-schwarz-2 (T₂ ∷ T₁ ∷ []) (T₁ ∷ T₁ ∷ []) = norm-sq-≤₁ T₀
cauchy-schwarz-2 (T₂ ∷ T₁ ∷ []) (T₁ ∷ T₂ ∷ []) = norm-sq-≤₁ T₁
cauchy-schwarz-2 (T₂ ∷ T₁ ∷ []) (T₂ ∷ T₀ ∷ []) = norm-sq-≤₁ T₁
cauchy-schwarz-2 (T₂ ∷ T₁ ∷ []) (T₂ ∷ T₁ ∷ []) = norm-sq-≤₁ T₂
cauchy-schwarz-2 (T₂ ∷ T₁ ∷ []) (T₂ ∷ T₂ ∷ []) = norm-sq-≤₁ T₀
-- f = (T₂, T₂): ⟨f,g⟩ = (T₂⊗b₁)⊕(T₂⊗b₂)
cauchy-schwarz-2 (T₂ ∷ T₂ ∷ []) (T₀ ∷ T₁ ∷ []) = norm-sq-≤₁ T₂
cauchy-schwarz-2 (T₂ ∷ T₂ ∷ []) (T₀ ∷ T₂ ∷ []) = norm-sq-≤₁ T₁
cauchy-schwarz-2 (T₂ ∷ T₂ ∷ []) (T₁ ∷ T₀ ∷ []) = norm-sq-≤₁ T₂
cauchy-schwarz-2 (T₂ ∷ T₂ ∷ []) (T₁ ∷ T₁ ∷ []) = norm-sq-≤₁ T₁
cauchy-schwarz-2 (T₂ ∷ T₂ ∷ []) (T₁ ∷ T₂ ∷ []) = norm-sq-≤₁ T₀
cauchy-schwarz-2 (T₂ ∷ T₂ ∷ []) (T₂ ∷ T₀ ∷ []) = norm-sq-≤₁ T₁
cauchy-schwarz-2 (T₂ ∷ T₂ ∷ []) (T₂ ∷ T₁ ∷ []) = norm-sq-≤₁ T₀
cauchy-schwarz-2 (T₂ ∷ T₂ ∷ []) (T₂ ∷ T₂ ∷ []) = norm-sq-≤₁ T₂

--------------------------------------------------------------------------------
-- §5. 三角不等式 — ‖f+g‖ ≤ ‖f‖ + ‖g‖ (所有 n)
--
-- 对离散 sup-范数 (discrete-norm), 值域仅 {T₀, T₁}:
--   Case 1: ‖f‖=T₀, ‖g‖=T₀ → f=0, g=0, ‖f+g‖=T₀ ≤ T₀⊕T₀=T₀
--   Case 2: ‖f‖=T₁, ‖g‖=T₀ → g=0, ‖f+g‖=‖f‖=T₁ ≤ T₁⊕T₀=T₁
--   Case 3: ‖f‖=T₀, ‖g‖=T₁ → f=0, ‖f+g‖=‖g‖=T₁ ≤ T₀⊕T₁=T₁
--   Case 4: ‖f‖=T₁, ‖g‖=T₁ → ‖f+g‖∈{T₀,T₁} ≤ T₁⊕T₁=T₂
--
-- 注: 连续泛函分析中三角不等式由 Cauchy-Schwarz 推出:
--   ‖f+g‖² = ‖f‖²+‖g‖²+2Re⟨f,g⟩ ≤ ‖f‖²+‖g‖²+2‖f‖‖g‖ = (‖f‖+‖g‖)²
-- 在 GF(3) 中, 内积范数退化 (各向同性向量), 上述推导不适用。
-- 但 sup-范数的三角不等式仍成立, 由二值性直接推出。
--------------------------------------------------------------------------------

-- 零向量加零向量仍为零向量
+v-zero-zero : ∀ n → 0⃗ n +v 0⃗ n ≡ 0⃗ n
+v-zero-zero zero = refl
+v-zero-zero (suc n) = cong (T₀ ∷_) (+v-zero-zero n)

-- 三角不等式
triangle-inequality : ∀ n (f g : Vec Trit n) →
  discrete-norm n (f +v g) ≤T discrete-norm n f ⊕ discrete-norm n g
triangle-inequality n f g with norm-two-valued n f | norm-two-valued n g
-- Case 1: ‖f‖=T₀, ‖g‖=T₀ → f=0, g=0
... | inj₁ pf | inj₁ pg =
  let f-zero = norm-zero→vec-zero n f pf
      g-zero = norm-zero→vec-zero n g pg
      f+v-g-zero : f +v g ≡ 0⃗ n
      f+v-g-zero = trans (cong₂ _+v_ f-zero g-zero) (+v-zero-zero n)
      norm-f+v-g : discrete-norm n (f +v g) ≡ T₀
      norm-f+v-g = vec-zero→norm-zero n (f +v g) f+v-g-zero
      rhs-eq : discrete-norm n f ⊕ discrete-norm n g ≡ T₀
      rhs-eq = cong₂ _⊕_ pf pg
  in subst₂ _≤T_ (sym norm-f+v-g) (sym rhs-eq) ≤T-00
-- Case 2: ‖f‖=T₁, ‖g‖=T₀ → g=0, f+g=f
... | inj₂ pf | inj₁ pg =
  let g-zero = norm-zero→vec-zero n g pg
      f+v-g-eq : f +v g ≡ f
      f+v-g-eq = trans (cong (f +v_) g-zero) (+v-identityʳ n f)
      norm-f+v-g : discrete-norm n (f +v g) ≡ T₁
      norm-f+v-g = trans (cong (discrete-norm n) f+v-g-eq) pf
      rhs-eq : discrete-norm n f ⊕ discrete-norm n g ≡ T₁
      rhs-eq = cong₂ _⊕_ pf pg
  in subst₂ _≤T_ (sym norm-f+v-g) (sym rhs-eq) ≤T-11
-- Case 3: ‖f‖=T₀, ‖g‖=T₁ → f=0, f+g=g
... | inj₁ pf | inj₂ pg =
  let f-zero = norm-zero→vec-zero n f pf
      f+v-g-eq : f +v g ≡ g
      f+v-g-eq = trans (cong (_+v g) f-zero) (+v-identityˡ n g)
      norm-f+v-g : discrete-norm n (f +v g) ≡ T₁
      norm-f+v-g = trans (cong (discrete-norm n) f+v-g-eq) pg
      rhs-eq : discrete-norm n f ⊕ discrete-norm n g ≡ T₁
      rhs-eq = cong₂ _⊕_ pf pg
  in subst₂ _≤T_ (sym norm-f+v-g) (sym rhs-eq) ≤T-11
-- Case 4: ‖f‖=T₁, ‖g‖=T₁ → ‖f+g‖∈{T₀,T₁} ≤ T₂
... | inj₂ pf | inj₂ pg =
  subst (discrete-norm n (f +v g) ≤T_)
    (sym (cong₂ _⊕_ pf pg))
    (≤T-max (discrete-norm n (f +v g)))

--------------------------------------------------------------------------------
-- §6. 各向同性反例 — Cauchy-Schwarz 在 n≥3 时失效
--
-- GF(3)³ 中 f=(1,1,1) 是各向同性向量:
--   Q(f) = 1+1+1 = 3 ≡ 0 (mod 3)
--   但 f ≠ 0
--
-- 取 g=(1,0,0):
--   ⟨f,g⟩ = 1, N(⟨f,g⟩) = 1
--   N(Q(f))·N(Q(g)) = N(0)·N(1) = 0·1 = 0
--   1 ≤ 0 为假 — Cauchy-Schwarz 失效!
--
-- 这是 GF(3) 内积空间与 ℝⁿ 内积空间的本质区别:
--   连续: 内积正定 → CS 恒成立
--   离散: 内积退化 → CS 仅在无各向同性向量的维度成立
--------------------------------------------------------------------------------

-- 反例验证: N(⟨f,g⟩) = T₁ 但 N(Q(f))·N(Q(g)) = T₀
cs-counterexample-lhs : norm-sq (standard-inner-product 3
  (T₁ ∷ T₁ ∷ T₁ ∷ []) (T₁ ∷ T₀ ∷ T₀ ∷ [])) ≡ T₁
cs-counterexample-lhs = refl

cs-counterexample-rhs : norm-sq (standard-inner-product 3
  (T₁ ∷ T₁ ∷ T₁ ∷ []) (T₁ ∷ T₁ ∷ T₁ ∷ []))
  ⊗ norm-sq (standard-inner-product 3
  (T₁ ∷ T₀ ∷ T₀ ∷ []) (T₁ ∷ T₀ ∷ T₀ ∷ [])) ≡ T₀
cs-counterexample-rhs = refl

-- 因此 CS 不等式 T₁ ≤T T₀ 不成立 (无构造子)
cs-fails-at-3 : ¬ (norm-sq (standard-inner-product 3
  (T₁ ∷ T₁ ∷ T₁ ∷ []) (T₁ ∷ T₀ ∷ T₀ ∷ []))
  ≤T norm-sq (standard-inner-product 3
  (T₁ ∷ T₁ ∷ T₁ ∷ []) (T₁ ∷ T₁ ∷ T₁ ∷ []))
  ⊗ norm-sq (standard-inner-product 3
  (T₁ ∷ T₀ ∷ T₀ ∷ []) (T₁ ∷ T₀ ∷ T₀ ∷ [])))
cs-fails-at-3 ()

--------------------------------------------------------------------------------
-- §7. 总结
--
-- 核心定理 (全部 0 postulate, 构造性证明):
--
-- 1. cauchy-schwarz-1: GF(3)¹ 上 CS 不等式 (9 case, 等号成立)
-- 2. cauchy-schwarz-2: GF(3)² 上 CS 不等式 (66 clause 结构化穷举)
-- 3. triangle-inequality: 所有 n 上 sup-范数三角不等式
-- 4. cs-fails-at-3: GF(3)³ 上 CS 不等式失效 (各向同性反例)
--
-- 数学本质:
--   GF(3) 内积空间的退化性 (各向同性向量) 是 CS 不等式的精确边界:
--   • n≤2: 无各向同性向量 → CS 成立
--   • n≥3: 有各向同性向量 → CS 失效
--   这是离散数学 (本体) 与连续数学 (投影) 的结构性差异:
--   连续 ℝⁿ 内积正定, CS 恒成立; 离散 GF(3)ⁿ 内积退化, CS 有维度限制
--------------------------------------------------------------------------------
