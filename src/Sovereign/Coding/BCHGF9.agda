{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Coding.BCHGF9
-- GF(9) 上的 [8,6,3] BCH 码: 最小距离界 + 系统编码 + 单错纠错 (P1-2, wiki 94B)
--
-- 数学背景:
--   β = 1+α ∈ GF(9)* 是 8 阶本原元 (GF9.gen-generates-all, α²=−1)。
--   取连续根 {β, β²} 的 BCH 码: C = { c ∈ GF(9)⁸ | S₁(c)=S₂(c)=0 },
--   其中 Sᵣ(c) = Σₖ cₖ·β^{r·k} (校验子)。设计距离 δ = 3。
--   生成多项式 g(x) = (x−β)(x−β²) = x² + 2x + (1+2α) 给出维数 8−2 = 6。
--
-- 宪法原则 (全离散, 无浮点, 无除法):
--   1. 校验子 = ℕ 递归显式和 (左结合), 零消去/拆分/稀疏引理均为 ℕ 归纳。
--   2. 最小距离 ≥ 3 的 BCH 界: 权 1 码字 ⟹ S₁ = vβⁱ ≠ 0 (非零积);
--      权 2 码字 ⟹ Vandermonde 恒等式 S₂−βⁱS₁ = wβʲ(βʲ−βⁱ) ≠ 0 (β 的 8 阶性)。
--   3. 编码 = 系统码 2×2 校验子解 (d = β²−β 的逆 = β, 无除法: d·dInv = 1 refl);
--      解码 = 校验子对 (S₁,S₂) → (位置, 值) 查表 (唯一性由 β 幂两两不同保证),
--      纠错 = 位调整, 正确性 = 编码正确性 + 校验子加性 + 查表反演。
--   4. GF(9) 域公理全部引用 GF9.agda (0 postulate)。
--
-- 包含:
--   §1 校验子机器: synd/syndFrom 递归和 + 零消去/拆分/稀疏引理
--   §2 β 幂次与 GF(9)* 非零引理 (星表示, toGF9-nonzero, nonzero-×, β-diff)
--   §3 [8,6,3] 码 + 系统编码 + encode-correct
--   §4 最小距离 ≥ 3 (BCH 界): 权 1 排除 + 权 2 Vandermonde + 权 3 见证码字
--   §5 单错纠错: 校验子加性 + findError 查表 + decode-correct
--
-- 0 postulate。

module Sovereign.Coding.BCHGF9 where

open import Data.Nat using (ℕ; zero; suc; _+_; _∸_; _%_; _<_; _≤_; _≟_; s≤s)
open import Data.Nat.Properties
  using (m∸n+n≡m; +-comm; +-assoc; +-suc; +-identityʳ; +-monoʳ-<; m≤m+n; <-≤-trans; ≟-diag; ≟-≡; <-irrefl; <-trans; <⇒≤; ≤-refl; m<n⇒m<1+n)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; _≢_; cong; cong₂; sym; trans; subst; module ≡-Reasoning)
open ≡-Reasoning
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Nullary.Decidable using (does)
open import Sovereign.Base.Trit using (Trit; T₀; T₁; T₂; _⊗_; _⊕_; negate; negate²; ⊗-zeroˡ; ⊗-zeroʳ; ⊕-identityˡ; ⊕-identityʳ; ⊕-inverse)
open import Sovereign.Algebra.GF9
  using (GF9; GF9Star; s1; s2; sα; s2α; s1α; s12α; s21α; s22α;
         toGF9; _+gf9_; _*gf9_; gf9-one;
         +gf9-comm; +gf9-assoc; +gf9-identityˡ; +gf9-identityʳ; +gf9-inverse;
         *gf9-comm; *gf9-assoc; *gf9-identityˡ; *gf9-identityʳ;
         *gf9-distribˡ-+gf9; *gf9-distribʳ-+gf9;
         _*s_; _^s_; gen; *s-toGF9;
         negate-⊕; negate-⊗; negate-⊗-negate; negate-⊗-comm)

zero9 : GF9
zero9 = T₀ , T₀

negate9 : GF9 → GF9
negate9 (a , b) = negate a , negate b

_-gf9_ : GF9 → GF9 → GF9
x -gf9 y = x +gf9 negate9 y

-- 本地别名 + 分层 fixity (GF9 原算子 +gf9/*gf9 同级 20, 混用解析歧义)
_+₉_ : GF9 → GF9 → GF9
x +₉ y = x +gf9 y

_*₉_ : GF9 → GF9 → GF9
x *₉ y = x *gf9 y

_-₉_ : GF9 → GF9 → GF9
x -₉ y = x +gf9 negate9 y

infixl 21 _+₉_
infixl 22 _*₉_
infixl 21 _-₉_


-- β = 1+α (8 阶本原元, 见 GF9.gen-generates-all)
beta : GF9
beta = T₁ , T₁

βPowT : ℕ → GF9
βPowT n = toGF9 (gen ^s (n % 8))

β2Pow : ℕ → GF9
β2Pow n = βPowT n *₉ βPowT n

--------------------------------------------------------------------------------
-- §0. GF9 层引理: 零律 / 负号律 / 消去律
--------------------------------------------------------------------------------

*gf9-zeroˡ : ∀ x → zero9 *₉ x ≡ zero9
*gf9-zeroˡ (c , d) = cong₂ _,_
  (trans (cong₂ _⊕_ (⊗-zeroˡ c) (cong negate (⊗-zeroˡ d))) (⊕-inverse T₀))
  (trans (cong₂ _⊕_ (⊗-zeroˡ d) (⊗-zeroˡ c)) (⊕-identityʳ T₀))

*gf9-zeroʳ : ∀ x → x *₉ zero9 ≡ zero9
*gf9-zeroʳ x = trans (*gf9-comm x zero9) (*gf9-zeroˡ x)

negate9-⊕ : ∀ x y → negate9 (x +₉ y) ≡ negate9 x +₉ negate9 y
negate9-⊕ (a , b) (c , d) = cong₂ _,_ (negate-⊕ a c) (negate-⊕ b d)

negate9² : ∀ x → negate9 (negate9 x) ≡ x
negate9² (a , b) = cong₂ _,_ (negate² a) (negate² b)

-- negate9(x·y) ≡ negate9 x · y
negate9-⊗ : ∀ x y → negate9 (x *₉ y) ≡ (negate9 x) *₉ y
negate9-⊗ (a , b) (c , d) = cong₂ _,_ real imag
  where
    real : negate ((a ⊗ c) ⊕ negate (b ⊗ d)) ≡ (negate a ⊗ c) ⊕ negate (negate b ⊗ d)
    real = trans (negate-⊕ (a ⊗ c) (negate (b ⊗ d)))
      (cong₂ _⊕_ (negate-⊗ a c)
        (trans (negate² (b ⊗ d))
          (sym (trans (negate-⊗ (negate b) d) (cong (_⊗ d) (negate² b))))))
    imag : negate ((a ⊗ d) ⊕ (b ⊗ c)) ≡ (negate a ⊗ d) ⊕ (negate b ⊗ c)
    imag = trans (negate-⊕ (a ⊗ d) (b ⊗ c)) (cong₂ _⊕_ (negate-⊗ a d) (negate-⊗ b c))

-- x·(−y) ≡ −(x·y)
*-negateʳ : ∀ x y → x *₉ negate9 y ≡ negate9 (x *₉ y)
*-negateʳ x y = begin
  x *₉ negate9 y
    ≡⟨ *gf9-comm x (negate9 y) ⟩
  negate9 y *₉ x
    ≡⟨ sym (negate9-⊗ y x) ⟩
  negate9 (y *₉ x)
    ≡⟨ cong negate9 (*gf9-comm y x) ⟩
  negate9 (x *₉ y)
  ∎

-- (x + y) + (−x + z) ≡ y + z
cancel-front : ∀ x y z → (x +₉ y) +₉ (negate9 x +₉ z) ≡ y +₉ z
cancel-front x y z = begin
  (x +₉ y) +₉ (negate9 x +₉ z)
    ≡⟨ +gf9-assoc x y (negate9 x +₉ z) ⟩
  x +₉ (y +₉ (negate9 x +₉ z))
    ≡⟨ cong (x +gf9_) (sym (+gf9-assoc y (negate9 x) z)) ⟩
  x +₉ ((y +₉ negate9 x) +₉ z)
    ≡⟨ cong (λ t → x +₉ (t +₉ z)) (+gf9-comm y (negate9 x)) ⟩
  x +₉ ((negate9 x +₉ y) +₉ z)
    ≡⟨ cong (x +gf9_) (+gf9-assoc (negate9 x) y z) ⟩
  x +₉ (negate9 x +₉ (y +₉ z))
    ≡⟨ sym (+gf9-assoc x (negate9 x) (y +₉ z)) ⟩
  (x +₉ negate9 x) +₉ (y +₉ z)
    ≡⟨ cong (_+gf9 (y +₉ z)) (+gf9-inverse x) ⟩
  zero9 +₉ (y +₉ z)
    ≡⟨ +gf9-identityˡ (y +₉ z) ⟩
  y +₉ z
  ∎

-- (x − y) + y ≡ x
cancel-left-neg : ∀ x y → (x +gf9 negate9 y) +gf9 y ≡ x
cancel-left-neg x y = begin
  (x +gf9 negate9 y) +gf9 y
    ≡⟨ +gf9-assoc x (negate9 y) y ⟩
  x +gf9 (negate9 y +gf9 y)
    ≡⟨ cong (x +gf9_) (+gf9-comm (negate9 y) y) ⟩
  x +gf9 (y +gf9 negate9 y)
    ≡⟨ cong (x +gf9_) (+gf9-inverse y) ⟩
  x +gf9 zero9
    ≡⟨ +gf9-identityʳ x ⟩
  x
  ∎

-- (x + y) + (−y) ≡ x
cancel-right : ∀ x y → (x +₉ y) +₉ negate9 y ≡ x
cancel-right x y = begin
  (x +₉ y) +₉ negate9 y
    ≡⟨ +gf9-assoc x y (negate9 y) ⟩
  x +₉ (y +₉ negate9 y)
    ≡⟨ cong (x +gf9_) (+gf9-inverse y) ⟩
  x +₉ zero9
    ≡⟨ +gf9-identityʳ x ⟩
  x
  ∎

-- x + (z + (−x)) ≡ z
cancel-mid : ∀ x z → x +₉ (z +₉ negate9 x) ≡ z
cancel-mid x z = begin
  x +₉ (z +₉ negate9 x)
    ≡⟨ sym (+gf9-assoc x z (negate9 x)) ⟩
  (x +₉ z) +₉ negate9 x
    ≡⟨ cong (_+gf9 negate9 x) (+gf9-comm x z) ⟩
  (z +₉ x) +₉ negate9 x
    ≡⟨ +gf9-assoc z x (negate9 x) ⟩
  z +₉ (x +₉ negate9 x)
    ≡⟨ cong (z +gf9_) (+gf9-inverse x) ⟩
  z +₉ zero9
    ≡⟨ +gf9-identityʳ z ⟩
  z
  ∎

-- x ≢ y ⟹ x − y ≢ 0
sub≢0 : ∀ x y → x ≢ y → x -gf9 y ≢ zero9
sub≢0 x y x≢y p = x≢y (begin
  x
    ≡⟨ sym (+gf9-identityʳ x) ⟩
  x +gf9 zero9
    ≡⟨ cong (x +gf9_) (sym (trans (+gf9-comm (negate9 y) y) (+gf9-inverse y))) ⟩
  x +gf9 (negate9 y +gf9 y)
    ≡⟨ sym (+gf9-assoc x (negate9 y) y) ⟩
  (x +gf9 negate9 y) +gf9 y
    ≡⟨ cong (_+gf9 y) p ⟩
  zero9 +gf9 y
    ≡⟨ +gf9-identityˡ y ⟩
  y
  ∎)

-- (x − y) + (y − x) ≡ 0
cancel-cross : ∀ x y → (x -₉ y) +₉ (y -₉ x) ≡ zero9
cancel-cross x y = begin
  (x +₉ negate9 y) +₉ (y +₉ negate9 x)
    ≡⟨ +gf9-assoc x (negate9 y) (y +₉ negate9 x) ⟩
  x +₉ (negate9 y +₉ (y +₉ negate9 x))
    ≡⟨ cong (x +gf9_) (sym (+gf9-assoc (negate9 y) y (negate9 x))) ⟩
  x +₉ ((negate9 y +₉ y) +₉ negate9 x)
    ≡⟨ cong (λ t → x +₉ (t +₉ negate9 x)) (+gf9-comm (negate9 y) y) ⟩
  x +₉ ((y +₉ negate9 y) +₉ negate9 x)
    ≡⟨ cong (λ t → x +₉ (t +₉ negate9 x)) (+gf9-inverse y) ⟩
  x +₉ (zero9 +₉ negate9 x)
    ≡⟨ cong (x +gf9_) (+gf9-identityˡ (negate9 x)) ⟩
  x +₉ negate9 x
    ≡⟨ +gf9-inverse x ⟩
  zero9
  ∎

-- (A + B) + (C + D) ≡ (A + C) + (B + D)
+-shuffle : ∀ A B C D → (A +₉ B) +₉ (C +₉ D) ≡ (A +₉ C) +₉ (B +₉ D)
+-shuffle A B C D = begin
  (A +₉ B) +₉ (C +₉ D)
    ≡⟨ +gf9-assoc A B (C +₉ D) ⟩
  A +₉ (B +₉ (C +₉ D))
    ≡⟨ cong (A +gf9_) (sym (+gf9-assoc B C D)) ⟩
  A +₉ ((B +₉ C) +₉ D)
    ≡⟨ cong (λ t → A +₉ (t +₉ D)) (+gf9-comm B C) ⟩
  A +₉ ((C +₉ B) +₉ D)
    ≡⟨ cong (A +gf9_) (+gf9-assoc C B D) ⟩
  A +₉ (C +₉ (B +₉ D))
    ≡⟨ sym (+gf9-assoc A C (B +₉ D)) ⟩
  (A +₉ C) +₉ (B +₉ D)
  ∎

-- βⁱ·(c·βⁱ) ≡ c·(βⁱ·βⁱ) (幂次吸收)
β-absorb : ∀ c i → βPowT i *₉ (c *₉ βPowT i) ≡ c *₉ (βPowT i *₉ βPowT i)
β-absorb c i = begin
  βPowT i *₉ (c *₉ βPowT i)
    ≡⟨ sym (*gf9-assoc (βPowT i) c (βPowT i)) ⟩
  (βPowT i *₉ c) *₉ βPowT i
    ≡⟨ cong (_*gf9 βPowT i) (*gf9-comm (βPowT i) c) ⟩
  (c *₉ βPowT i) *₉ βPowT i
    ≡⟨ *gf9-assoc c (βPowT i) (βPowT i) ⟩
  c *₉ (βPowT i *₉ βPowT i)
  ∎

-- βⁱ·(c·βʲ) ≡ c·(βⁱ·βʲ) (交错吸收)
β-absorb2 : ∀ c i z → βPowT i *₉ (c *₉ z) ≡ c *₉ (βPowT i *₉ z)
β-absorb2 c i z = begin
  βPowT i *₉ (c *₉ z)
    ≡⟨ sym (*gf9-assoc (βPowT i) c z) ⟩
  (βPowT i *₉ c) *₉ z
    ≡⟨ cong (_*gf9 z) (*gf9-comm (βPowT i) c) ⟩
  (c *₉ βPowT i) *₉ z
    ≡⟨ *gf9-assoc c (βPowT i) z ⟩
  c *₉ (βPowT i *₉ z)
  ∎

--------------------------------------------------------------------------------
-- §1. 校验子机器: synd / syndFrom + 零消去 / 拆分 / 稀疏
--------------------------------------------------------------------------------

-- Σ_{k<n} c k *₉ w k  (左结合显式和)
synd : (ℕ → GF9) → (ℕ → GF9) → ℕ → GF9
synd c w zero = zero9
synd c w (suc n) = synd c w n +₉ (c n *₉ w n)

-- Σ_{k<n} c (s+k) *₉ w (s+k)  (带起点偏移)
syndFrom : (ℕ → GF9) → (ℕ → GF9) → ℕ → ℕ → GF9
syndFrom c w s zero = zero9
syndFrom c w s (suc n) = syndFrom c w s n +₉ (c (s + n) *₉ w (s + n))

-- 零消去 (后缀版)
syndFrom-zero : ∀ c w s n → (∀ k → k < n → c (s + k) ≡ zero9) → syndFrom c w s n ≡ zero9
syndFrom-zero c w s zero    h = refl
syndFrom-zero c w s (suc n) h = begin
  syndFrom c w s n +₉ (c (s + n) *₉ w (s + n))
    ≡⟨ cong (_+gf9 (c (s + n) *₉ w (s + n)))
            (syndFrom-zero c w s n (λ k k<n → h k (m<n⇒m<1+n k<n))) ⟩
  zero9 +₉ (c (s + n) *₉ w (s + n))
    ≡⟨ cong (zero9 +gf9_) (cong (_*gf9 w (s + n)) (h n (s≤s ≤-refl))) ⟩
  zero9 +₉ (zero9 *₉ w (s + n))
    ≡⟨ cong (zero9 +gf9_) (*gf9-zeroˡ (w (s + n))) ⟩
  zero9 +₉ zero9
    ≡⟨ +gf9-identityˡ zero9 ⟩
  zero9
  ∎

-- 零消去 (前段版)
synd-zero : ∀ c w n → (∀ k → k < n → c k ≡ zero9) → synd c w n ≡ zero9
synd-zero c w zero    h = refl
synd-zero c w (suc n) h = begin
  synd c w n +₉ (c n *₉ w n)
    ≡⟨ cong (_+gf9 (c n *₉ w n)) (synd-zero c w n (λ k k<n → h k (m<n⇒m<1+n k<n))) ⟩
  zero9 +₉ (c n *₉ w n)
    ≡⟨ cong (zero9 +gf9_) (cong (_*gf9 w n) (h n (s≤s ≤-refl))) ⟩
  zero9 +₉ (zero9 *₉ w n)
    ≡⟨ cong (zero9 +gf9_) (*gf9-zeroˡ (w n)) ⟩
  zero9
  ∎

-- 拆分: synd c w (m+n) ≡ synd c w m + syndFrom c w m n
synd-split : ∀ c w m n → synd c w (m + n) ≡ synd c w m +₉ syndFrom c w m n
synd-split c w m zero = begin
  synd c w (m + 0)
    ≡⟨ cong (λ n → synd c w n) (+-identityʳ m) ⟩
  synd c w m
    ≡⟨ sym (+gf9-identityʳ (synd c w m)) ⟩
  synd c w m +₉ zero9
  ∎
synd-split c w m (suc n) = begin
  synd c w (m + suc n)
    ≡⟨ cong (λ x → synd c w x) (+-suc m n) ⟩
  synd c w (m + n) +₉ (c (m + n) *₉ w (m + n))
    ≡⟨ cong (_+gf9 (c (m + n) *₉ w (m + n))) (synd-split c w m n) ⟩
  (synd c w m +₉ syndFrom c w m n) +₉ (c (m + n) *₉ w (m + n))
    ≡⟨ +gf9-assoc (synd c w m) (syndFrom c w m n) (c (m + n) *₉ w (m + n)) ⟩
  synd c w m +₉ (syndFrom c w m n +₉ (c (m + n) *₉ w (m + n)))
    ≡⟨⟩
  synd c w m +₉ syndFrom c w m (suc n)
  ∎

-- 逐点相等 ⟹ 和相等
synd-cong : ∀ c c' w n → (∀ k → k < n → c k ≡ c' k) → synd c w n ≡ synd c' w n
synd-cong c c' w zero    h = refl
synd-cong c c' w (suc n) h = cong₂ _+gf9_
  (synd-cong c c' w n (λ k k<n → h k (m<n⇒m<1+n k<n)))
  (cong₂ _*gf9_ (h n (s≤s ≤-refl)) refl)

-- m<n ⟹ m ≢ n
m<n⇒m≢n : ∀ m n → m < n → m ≢ n
m<n⇒m≢n m n m<n refl = <-irrefl refl m<n

-- ≢ 的对称性
≢-sym : {A : Set} {a b : A} → a ≢ b → b ≢ a
≢-sym a≢b p = a≢b (sym p)

-- suc⁸ n < 8 ⟹ ⊥
suc⁸<n : ∀ n → suc (suc (suc (suc (suc (suc (suc (suc n))))))) < suc (suc (suc (suc (suc (suc (suc (suc zero))))))) → ⊥
suc⁸<n n (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s ()))))))))

-- 稀疏引理 (单非零位): synd c w 8 ≡ c i *₉ w i
synd-single : ∀ c w i → i < 8 →
  (∀ k → k < 8 → k ≢ i → c k ≡ zero9) → synd c w 8 ≡ c i *₉ w i
synd-single c w i i<8 vanish = begin
  synd c w 8
    ≡⟨ subst (λ n → synd c w n ≡ synd c w (suc i) +₉ syndFrom c w (suc i) (8 ∸ suc i))
             split-eq (synd-split c w (suc i) (8 ∸ suc i)) ⟩
  synd c w (suc i) +₉ syndFrom c w (suc i) (8 ∸ suc i)
    ≡⟨ cong (synd c w (suc i) +gf9_) (syndFrom-zero c w (suc i) (8 ∸ suc i) tail-zero) ⟩
  synd c w (suc i) +₉ zero9
    ≡⟨ +gf9-identityʳ (synd c w (suc i)) ⟩
  synd c w (suc i)
    ≡⟨⟩
  synd c w i +₉ (c i *₉ w i)
    ≡⟨ cong (_+gf9 (c i *₉ w i)) (synd-zero c w i front-zero) ⟩
  zero9 +₉ (c i *₉ w i)
    ≡⟨ +gf9-identityˡ (c i *₉ w i) ⟩
  c i *₉ w i
  ∎ where
    split-eq : suc i + (8 ∸ suc i) ≡ 8
    split-eq = trans (+-comm (suc i) (8 ∸ suc i)) (m∸n+n≡m i<8)
    tail-zero : ∀ k → k < 8 ∸ suc i → c (suc i + k) ≡ zero9
    tail-zero k k<rest = vanish (suc i + k) k<8 (≢-sym (m<n⇒m≢n i (suc i + k) i<pos))
      where
        i<pos : i < suc i + k
        i<pos = <-≤-trans (s≤s ≤-refl) (m≤m+n (suc i) k)
        k<8 : suc i + k < 8
        k<8 = subst (λ x → suc i + k < x) split-eq (+-monoʳ-< (suc i) k<rest)
    front-zero : ∀ k → k < i → c k ≡ zero9
    front-zero k k<i = vanish k (trans' k<i i<8) (m<n⇒m≢n k i k<i)
      where trans' : ∀ {a b c} → a < b → b < c → a < c
            trans' = <-trans

-- 稀疏引理 (双非零位, i < j): synd c w 8 ≡ (c i *₉ w i) + (c j *₉ w j)
synd-sparse2 : ∀ c w i j → i < j → j < 8 →
  (∀ k → k < 8 → k ≢ i → k ≢ j → c k ≡ zero9) →
  synd c w 8 ≡ (c i *₉ w i) +₉ (c j *₉ w j)
synd-sparse2 c w i j i<j j<8 vanish = begin
  synd c w 8
    ≡⟨ subst (λ n → synd c w n ≡ synd c w (suc j) +₉ syndFrom c w (suc j) (8 ∸ suc j))
             split-eq-j (synd-split c w (suc j) (8 ∸ suc j)) ⟩
  synd c w (suc j) +₉ syndFrom c w (suc j) (8 ∸ suc j)
    ≡⟨ cong (synd c w (suc j) +gf9_) (syndFrom-zero c w (suc j) (8 ∸ suc j) tail-zero) ⟩
  synd c w (suc j) +₉ zero9
    ≡⟨ +gf9-identityʳ (synd c w (suc j)) ⟩
  synd c w (suc j)
    ≡⟨⟩
  synd c w j +₉ (c j *₉ w j)
    ≡⟨ cong (_+gf9 c j *₉ w j) synd-mid ⟩
  (c i *₉ w i) +₉ c j *₉ w j
  ∎ where
    split-eq-j : suc j + (8 ∸ suc j) ≡ 8
    split-eq-j = trans (+-comm (suc j) (8 ∸ suc j)) (m∸n+n≡m j<8)
    tail-zero : ∀ k → k < 8 ∸ suc j → c (suc j + k) ≡ zero9
    tail-zero k k<rest = vanish (suc j + k) k<8
      (≢-sym (m<n⇒m≢n i (suc j + k) i<pos))
      (≢-sym (m<n⇒m≢n j (suc j + k) j<pos))
      where
        j<pos : j < suc j + k
        j<pos = <-≤-trans (s≤s ≤-refl) (m≤m+n (suc j) k)
        i<pos : i < suc j + k
        i<pos = <-trans i<j j<pos
        k<8 : suc j + k < 8
        k<8 = subst (λ x → suc j + k < x) split-eq-j (+-monoʳ-< (suc j) k<rest)
    split-eq-i : suc i + (j ∸ suc i) ≡ j
    split-eq-i = trans (+-comm (suc i) (j ∸ suc i)) (m∸n+n≡m i<j)
    mid-zero : ∀ k → k < j ∸ suc i → c (suc i + k) ≡ zero9
    mid-zero k k<mid = vanish (suc i + k) k<8
      (≢-sym (m<n⇒m≢n i (suc i + k) i<pos))
      (m<n⇒m≢n (suc i + k) j mid<8)
      where
        i<pos : i < suc i + k
        i<pos = <-≤-trans (s≤s ≤-refl) (m≤m+n (suc i) k)
        mid<8 : suc i + k < j
        mid<8 = subst (λ x → suc i + k < x) split-eq-i (+-monoʳ-< (suc i) k<mid)
        k<8 : suc i + k < 8
        k<8 = <-trans mid<8 j<8
    synd-mid : synd c w j ≡ c i *₉ w i
    synd-mid = begin
      synd c w j
        ≡⟨ subst (λ n → synd c w n ≡ synd c w (suc i) +₉ syndFrom c w (suc i) (j ∸ suc i))
                 split-eq-i (synd-split c w (suc i) (j ∸ suc i)) ⟩
      synd c w (suc i) +₉ syndFrom c w (suc i) (j ∸ suc i)
        ≡⟨ cong (synd c w (suc i) +gf9_) (syndFrom-zero c w (suc i) (j ∸ suc i) mid-zero) ⟩
      synd c w (suc i) +₉ zero9
        ≡⟨ +gf9-identityʳ (synd c w (suc i)) ⟩
      synd c w (suc i)
        ≡⟨⟩
      synd c w i +₉ (c i *₉ w i)
        ≡⟨ cong (_+gf9 (c i *₉ w i)) (synd-zero c w i (λ k k<i →
             vanish k (<-trans k<i (<-trans i<j j<8))
                      (m<n⇒m≢n k i k<i)
                      (m<n⇒m≢n k j (<-trans k<i i<j)))) ⟩
      zero9 +₉ (c i *₉ w i)
        ≡⟨ +gf9-identityˡ (c i *₉ w i) ⟩
      c i *₉ w i
      ∎

--------------------------------------------------------------------------------
-- §2. GF(9)* 非零引理 (星表示)
--------------------------------------------------------------------------------

-- toGF9 永不取零
toGF9-nonzero : ∀ x → toGF9 x ≢ zero9
toGF9-nonzero s1   = λ (); toGF9-nonzero s2   = λ ()
toGF9-nonzero sα   = λ (); toGF9-nonzero s2α  = λ ()
toGF9-nonzero s1α  = λ (); toGF9-nonzero s12α = λ ()
toGF9-nonzero s21α = λ (); toGF9-nonzero s22α = λ ()

βPowT-nonzero : ∀ n → βPowT n ≢ zero9
βPowT-nonzero n = toGF9-nonzero (gen ^s (n % 8))

-- 非零积 (81 case, 生成)
nonzero-× : ∀ v w → v ≢ zero9 → w ≢ zero9 → v *₉ w ≢ zero9
nonzero-× (T₀ , T₀) _ hv _ = ⊥-elim (hv refl)
nonzero-× (T₀ , T₁) (T₀ , T₀) _ hw = ⊥-elim (hw refl)
nonzero-× (T₀ , T₁) (T₀ , T₁) _ _ = λ ()
nonzero-× (T₀ , T₁) (T₀ , T₂) _ _ = λ ()
nonzero-× (T₀ , T₁) (T₁ , T₀) _ _ = λ ()
nonzero-× (T₀ , T₁) (T₁ , T₁) _ _ = λ ()
nonzero-× (T₀ , T₁) (T₁ , T₂) _ _ = λ ()
nonzero-× (T₀ , T₁) (T₂ , T₀) _ _ = λ ()
nonzero-× (T₀ , T₁) (T₂ , T₁) _ _ = λ ()
nonzero-× (T₀ , T₁) (T₂ , T₂) _ _ = λ ()
nonzero-× (T₀ , T₂) (T₀ , T₀) _ hw = ⊥-elim (hw refl)
nonzero-× (T₀ , T₂) (T₀ , T₁) _ _ = λ ()
nonzero-× (T₀ , T₂) (T₀ , T₂) _ _ = λ ()
nonzero-× (T₀ , T₂) (T₁ , T₀) _ _ = λ ()
nonzero-× (T₀ , T₂) (T₁ , T₁) _ _ = λ ()
nonzero-× (T₀ , T₂) (T₁ , T₂) _ _ = λ ()
nonzero-× (T₀ , T₂) (T₂ , T₀) _ _ = λ ()
nonzero-× (T₀ , T₂) (T₂ , T₁) _ _ = λ ()
nonzero-× (T₀ , T₂) (T₂ , T₂) _ _ = λ ()
nonzero-× (T₁ , T₀) (T₀ , T₀) _ hw = ⊥-elim (hw refl)
nonzero-× (T₁ , T₀) (T₀ , T₁) _ _ = λ ()
nonzero-× (T₁ , T₀) (T₀ , T₂) _ _ = λ ()
nonzero-× (T₁ , T₀) (T₁ , T₀) _ _ = λ ()
nonzero-× (T₁ , T₀) (T₁ , T₁) _ _ = λ ()
nonzero-× (T₁ , T₀) (T₁ , T₂) _ _ = λ ()
nonzero-× (T₁ , T₀) (T₂ , T₀) _ _ = λ ()
nonzero-× (T₁ , T₀) (T₂ , T₁) _ _ = λ ()
nonzero-× (T₁ , T₀) (T₂ , T₂) _ _ = λ ()
nonzero-× (T₁ , T₁) (T₀ , T₀) _ hw = ⊥-elim (hw refl)
nonzero-× (T₁ , T₁) (T₀ , T₁) _ _ = λ ()
nonzero-× (T₁ , T₁) (T₀ , T₂) _ _ = λ ()
nonzero-× (T₁ , T₁) (T₁ , T₀) _ _ = λ ()
nonzero-× (T₁ , T₁) (T₁ , T₁) _ _ = λ ()
nonzero-× (T₁ , T₁) (T₁ , T₂) _ _ = λ ()
nonzero-× (T₁ , T₁) (T₂ , T₀) _ _ = λ ()
nonzero-× (T₁ , T₁) (T₂ , T₁) _ _ = λ ()
nonzero-× (T₁ , T₁) (T₂ , T₂) _ _ = λ ()
nonzero-× (T₁ , T₂) (T₀ , T₀) _ hw = ⊥-elim (hw refl)
nonzero-× (T₁ , T₂) (T₀ , T₁) _ _ = λ ()
nonzero-× (T₁ , T₂) (T₀ , T₂) _ _ = λ ()
nonzero-× (T₁ , T₂) (T₁ , T₀) _ _ = λ ()
nonzero-× (T₁ , T₂) (T₁ , T₁) _ _ = λ ()
nonzero-× (T₁ , T₂) (T₁ , T₂) _ _ = λ ()
nonzero-× (T₁ , T₂) (T₂ , T₀) _ _ = λ ()
nonzero-× (T₁ , T₂) (T₂ , T₁) _ _ = λ ()
nonzero-× (T₁ , T₂) (T₂ , T₂) _ _ = λ ()
nonzero-× (T₂ , T₀) (T₀ , T₀) _ hw = ⊥-elim (hw refl)
nonzero-× (T₂ , T₀) (T₀ , T₁) _ _ = λ ()
nonzero-× (T₂ , T₀) (T₀ , T₂) _ _ = λ ()
nonzero-× (T₂ , T₀) (T₁ , T₀) _ _ = λ ()
nonzero-× (T₂ , T₀) (T₁ , T₁) _ _ = λ ()
nonzero-× (T₂ , T₀) (T₁ , T₂) _ _ = λ ()
nonzero-× (T₂ , T₀) (T₂ , T₀) _ _ = λ ()
nonzero-× (T₂ , T₀) (T₂ , T₁) _ _ = λ ()
nonzero-× (T₂ , T₀) (T₂ , T₂) _ _ = λ ()
nonzero-× (T₂ , T₁) (T₀ , T₀) _ hw = ⊥-elim (hw refl)
nonzero-× (T₂ , T₁) (T₀ , T₁) _ _ = λ ()
nonzero-× (T₂ , T₁) (T₀ , T₂) _ _ = λ ()
nonzero-× (T₂ , T₁) (T₁ , T₀) _ _ = λ ()
nonzero-× (T₂ , T₁) (T₁ , T₁) _ _ = λ ()
nonzero-× (T₂ , T₁) (T₁ , T₂) _ _ = λ ()
nonzero-× (T₂ , T₁) (T₂ , T₀) _ _ = λ ()
nonzero-× (T₂ , T₁) (T₂ , T₁) _ _ = λ ()
nonzero-× (T₂ , T₁) (T₂ , T₂) _ _ = λ ()
nonzero-× (T₂ , T₂) (T₀ , T₀) _ hw = ⊥-elim (hw refl)
nonzero-× (T₂ , T₂) (T₀ , T₁) _ _ = λ ()
nonzero-× (T₂ , T₂) (T₀ , T₂) _ _ = λ ()
nonzero-× (T₂ , T₂) (T₁ , T₀) _ _ = λ ()
nonzero-× (T₂ , T₂) (T₁ , T₁) _ _ = λ ()
nonzero-× (T₂ , T₂) (T₁ , T₂) _ _ = λ ()
nonzero-× (T₂ , T₂) (T₂ , T₀) _ _ = λ ()
nonzero-× (T₂ , T₂) (T₂ , T₁) _ _ = λ ()
nonzero-× (T₂ , T₂) (T₂ , T₂) _ _ = λ ()

-- β 幂次两两不同 (64 case, 生成)
β-diff : ∀ i j → i < 8 → j < 8 → i ≢ j → βPowT j ≢ βPowT i
β-diff (zero) (zero) _ _ i≢j = ⊥-elim (i≢j refl)
β-diff (zero) (suc zero) _ _ _ = λ ()
β-diff (zero) (suc (suc zero)) _ _ _ = λ ()
β-diff (zero) (suc (suc (suc zero))) _ _ _ = λ ()
β-diff (zero) (suc (suc (suc (suc zero)))) _ _ _ = λ ()
β-diff (zero) (suc (suc (suc (suc (suc zero))))) _ _ _ = λ ()
β-diff (zero) (suc (suc (suc (suc (suc (suc zero)))))) _ _ _ = λ ()
β-diff (zero) (suc (suc (suc (suc (suc (suc (suc zero))))))) _ _ _ = λ ()
β-diff (suc zero) (zero) _ _ _ = λ ()
β-diff (suc zero) (suc zero) _ _ i≢j = ⊥-elim (i≢j refl)
β-diff (suc zero) (suc (suc zero)) _ _ _ = λ ()
β-diff (suc zero) (suc (suc (suc zero))) _ _ _ = λ ()
β-diff (suc zero) (suc (suc (suc (suc zero)))) _ _ _ = λ ()
β-diff (suc zero) (suc (suc (suc (suc (suc zero))))) _ _ _ = λ ()
β-diff (suc zero) (suc (suc (suc (suc (suc (suc zero)))))) _ _ _ = λ ()
β-diff (suc zero) (suc (suc (suc (suc (suc (suc (suc zero))))))) _ _ _ = λ ()
β-diff (suc (suc zero)) (zero) _ _ _ = λ ()
β-diff (suc (suc zero)) (suc zero) _ _ _ = λ ()
β-diff (suc (suc zero)) (suc (suc zero)) _ _ i≢j = ⊥-elim (i≢j refl)
β-diff (suc (suc zero)) (suc (suc (suc zero))) _ _ _ = λ ()
β-diff (suc (suc zero)) (suc (suc (suc (suc zero)))) _ _ _ = λ ()
β-diff (suc (suc zero)) (suc (suc (suc (suc (suc zero))))) _ _ _ = λ ()
β-diff (suc (suc zero)) (suc (suc (suc (suc (suc (suc zero)))))) _ _ _ = λ ()
β-diff (suc (suc zero)) (suc (suc (suc (suc (suc (suc (suc zero))))))) _ _ _ = λ ()
β-diff (suc (suc (suc zero))) (zero) _ _ _ = λ ()
β-diff (suc (suc (suc zero))) (suc zero) _ _ _ = λ ()
β-diff (suc (suc (suc zero))) (suc (suc zero)) _ _ _ = λ ()
β-diff (suc (suc (suc zero))) (suc (suc (suc zero))) _ _ i≢j = ⊥-elim (i≢j refl)
β-diff (suc (suc (suc zero))) (suc (suc (suc (suc zero)))) _ _ _ = λ ()
β-diff (suc (suc (suc zero))) (suc (suc (suc (suc (suc zero))))) _ _ _ = λ ()
β-diff (suc (suc (suc zero))) (suc (suc (suc (suc (suc (suc zero)))))) _ _ _ = λ ()
β-diff (suc (suc (suc zero))) (suc (suc (suc (suc (suc (suc (suc zero))))))) _ _ _ = λ ()
β-diff (suc (suc (suc (suc zero)))) (zero) _ _ _ = λ ()
β-diff (suc (suc (suc (suc zero)))) (suc zero) _ _ _ = λ ()
β-diff (suc (suc (suc (suc zero)))) (suc (suc zero)) _ _ _ = λ ()
β-diff (suc (suc (suc (suc zero)))) (suc (suc (suc zero))) _ _ _ = λ ()
β-diff (suc (suc (suc (suc zero)))) (suc (suc (suc (suc zero)))) _ _ i≢j = ⊥-elim (i≢j refl)
β-diff (suc (suc (suc (suc zero)))) (suc (suc (suc (suc (suc zero))))) _ _ _ = λ ()
β-diff (suc (suc (suc (suc zero)))) (suc (suc (suc (suc (suc (suc zero)))))) _ _ _ = λ ()
β-diff (suc (suc (suc (suc zero)))) (suc (suc (suc (suc (suc (suc (suc zero))))))) _ _ _ = λ ()
β-diff (suc (suc (suc (suc (suc zero))))) (zero) _ _ _ = λ ()
β-diff (suc (suc (suc (suc (suc zero))))) (suc zero) _ _ _ = λ ()
β-diff (suc (suc (suc (suc (suc zero))))) (suc (suc zero)) _ _ _ = λ ()
β-diff (suc (suc (suc (suc (suc zero))))) (suc (suc (suc zero))) _ _ _ = λ ()
β-diff (suc (suc (suc (suc (suc zero))))) (suc (suc (suc (suc zero)))) _ _ _ = λ ()
β-diff (suc (suc (suc (suc (suc zero))))) (suc (suc (suc (suc (suc zero))))) _ _ i≢j = ⊥-elim (i≢j refl)
β-diff (suc (suc (suc (suc (suc zero))))) (suc (suc (suc (suc (suc (suc zero)))))) _ _ _ = λ ()
β-diff (suc (suc (suc (suc (suc zero))))) (suc (suc (suc (suc (suc (suc (suc zero))))))) _ _ _ = λ ()
β-diff (suc (suc (suc (suc (suc (suc zero)))))) (zero) _ _ _ = λ ()
β-diff (suc (suc (suc (suc (suc (suc zero)))))) (suc zero) _ _ _ = λ ()
β-diff (suc (suc (suc (suc (suc (suc zero)))))) (suc (suc zero)) _ _ _ = λ ()
β-diff (suc (suc (suc (suc (suc (suc zero)))))) (suc (suc (suc zero))) _ _ _ = λ ()
β-diff (suc (suc (suc (suc (suc (suc zero)))))) (suc (suc (suc (suc zero)))) _ _ _ = λ ()
β-diff (suc (suc (suc (suc (suc (suc zero)))))) (suc (suc (suc (suc (suc zero))))) _ _ _ = λ ()
β-diff (suc (suc (suc (suc (suc (suc zero)))))) (suc (suc (suc (suc (suc (suc zero)))))) _ _ i≢j = ⊥-elim (i≢j refl)
β-diff (suc (suc (suc (suc (suc (suc zero)))))) (suc (suc (suc (suc (suc (suc (suc zero))))))) _ _ _ = λ ()
β-diff (suc (suc (suc (suc (suc (suc (suc zero))))))) (zero) _ _ _ = λ ()
β-diff (suc (suc (suc (suc (suc (suc (suc zero))))))) (suc zero) _ _ _ = λ ()
β-diff (suc (suc (suc (suc (suc (suc (suc zero))))))) (suc (suc zero)) _ _ _ = λ ()
β-diff (suc (suc (suc (suc (suc (suc (suc zero))))))) (suc (suc (suc zero))) _ _ _ = λ ()
β-diff (suc (suc (suc (suc (suc (suc (suc zero))))))) (suc (suc (suc (suc zero)))) _ _ _ = λ ()
β-diff (suc (suc (suc (suc (suc (suc (suc zero))))))) (suc (suc (suc (suc (suc zero))))) _ _ _ = λ ()
β-diff (suc (suc (suc (suc (suc (suc (suc zero))))))) (suc (suc (suc (suc (suc (suc zero)))))) _ _ _ = λ ()
β-diff (suc (suc (suc (suc (suc (suc (suc zero))))))) (suc (suc (suc (suc (suc (suc (suc zero))))))) _ _ i≢j = ⊥-elim (i≢j refl)
β-diff (suc (suc (suc (suc (suc (suc (suc (suc m)))))))) _ i<8 _ _ = ⊥-elim (suc⁸<n _ i<8)
β-diff _ (suc (suc (suc (suc (suc (suc (suc (suc m)))))))) _ j<8 _ = ⊥-elim (suc⁸<n _ j<8)

--------------------------------------------------------------------------------
-- §3. [8,6,3] 码: 系统编码 + encode-correct
--------------------------------------------------------------------------------

-- 校验子 S₁, S₂ (根 β, β²)
S₁ : (ℕ → GF9) → GF9
S₁ c = synd c βPowT 8

S₂ : (ℕ → GF9) → GF9
S₂ c = synd c β2Pow 8

-- 信息位和 (位置 2..7)
M1 : (ℕ → GF9) → GF9
M1 m = syndFrom m βPowT 2 6

M2 : (ℕ → GF9) → GF9
M2 m = syndFrom m β2Pow 2 6

-- d = β² − β, 逆元 dInv = β (验证: d·dInv = 1)
d : GF9
d = β2Pow 1 -₉ βPowT 1

dInv : GF9
dInv = beta

dInv-correct : d *₉ dInv ≡ gf9-one
dInv-correct = refl

dInv-comm : dInv *₉ d ≡ gf9-one
dInv-comm = trans (*gf9-comm dInv d) dInv-correct

-- 校验位 (2×2 系统解): p₁ = (M₁−M₂)·(β²−β)⁻¹, p₀ = −M₁ − p₁β
p1 : (ℕ → GF9) → GF9
p1 m = (M1 m -₉ M2 m) *₉ dInv

p0 : (ℕ → GF9) → GF9
p0 m = negate9 (M1 m) -₉ (p1 m *₉ βPowT 1)

-- 系统编码: c = (p₀, p₁, m₂, ..., m₇)
encode : (ℕ → GF9) → ℕ → GF9
encode m zero = p0 m
encode m (suc zero) = p1 m
encode m (suc (suc k)) = m (suc (suc k))

-- synd c w 2 ≡ c 0 · w 0 + c 1 · w 1
peel2 : ∀ c w → synd c w 2 ≡ (c 0 *₉ w 0) +₉ (c 1 *₉ w 1)
peel2 c w = begin
  synd c w 2
    ≡⟨⟩
  (zero9 +₉ c 0 *₉ w 0) +₉ c 1 *₉ w 1
    ≡⟨ cong (_+gf9 c 1 *₉ w 1) (+gf9-identityˡ (c 0 *₉ w 0)) ⟩
  (c 0 *₉ w 0) +₉ c 1 *₉ w 1
  ∎

-- S₁(encode m) 展开
S1-eq : ∀ m → S₁ (encode m) ≡ (p0 m +₉ p1 m *₉ βPowT 1) +₉ M1 m
S1-eq m = begin
  S₁ (encode m)
    ≡⟨ synd-split (encode m) βPowT 2 6 ⟩
  synd (encode m) βPowT 2 +₉ syndFrom (encode m) βPowT 2 6
    ≡⟨ cong (_+gf9 syndFrom (encode m) βPowT 2 6) (peel2 (encode m) βPowT) ⟩
  ((encode m 0 *₉ βPowT 0) +₉ (encode m 1 *₉ βPowT 1)) +₉ syndFrom (encode m) βPowT 2 6
    ≡⟨⟩
  ((p0 m *₉ βPowT 0) +₉ (p1 m *₉ βPowT 1)) +₉ M1 m
    ≡⟨⟩
  ((p0 m *₉ gf9-one) +₉ (p1 m *₉ βPowT 1)) +₉ M1 m
    ≡⟨ cong (λ x → (x +₉ p1 m *₉ βPowT 1) +₉ M1 m) (*gf9-identityʳ (p0 m)) ⟩
  (p0 m +₉ p1 m *₉ βPowT 1) +₉ M1 m
  ∎

-- S₂(encode m) 展开
S2-eq : ∀ m → S₂ (encode m) ≡ (p0 m +₉ p1 m *₉ β2Pow 1) +₉ M2 m
S2-eq m = begin
  S₂ (encode m)
    ≡⟨ synd-split (encode m) β2Pow 2 6 ⟩
  synd (encode m) β2Pow 2 +₉ syndFrom (encode m) β2Pow 2 6
    ≡⟨ cong (_+gf9 syndFrom (encode m) β2Pow 2 6) (peel2 (encode m) β2Pow) ⟩
  ((encode m 0 *₉ β2Pow 0) +₉ (encode m 1 *₉ β2Pow 1)) +₉ syndFrom (encode m) β2Pow 2 6
    ≡⟨⟩
  ((p0 m *₉ β2Pow 0) +₉ (p1 m *₉ β2Pow 1)) +₉ M2 m
    ≡⟨⟩
  ((p0 m *₉ gf9-one) +₉ (p1 m *₉ β2Pow 1)) +₉ M2 m
    ≡⟨ cong (λ x → (x +₉ p1 m *₉ β2Pow 1) +₉ M2 m) (*gf9-identityʳ (p0 m)) ⟩
  (p0 m +₉ p1 m *₉ β2Pow 1) +₉ M2 m
  ∎

-- S₁ = 0
S1-zero : ∀ m → S₁ (encode m) ≡ zero9
S1-zero m = begin
  S₁ (encode m)
    ≡⟨ S1-eq m ⟩
  (p0 m +₉ p1 m *₉ βPowT 1) +₉ M1 m
    ≡⟨⟩
  ((negate9 (M1 m) -₉ (p1 m *₉ βPowT 1)) +₉ p1 m *₉ βPowT 1) +₉ M1 m
    ≡⟨ cong (_+gf9 M1 m) (cancel-left-neg (negate9 (M1 m)) (p1 m *₉ βPowT 1)) ⟩
  negate9 (M1 m) +₉ M1 m
    ≡⟨ +gf9-comm (negate9 (M1 m)) (M1 m) ⟩
  M1 m +₉ negate9 (M1 m)
    ≡⟨ +gf9-inverse (M1 m) ⟩
  zero9
  ∎

-- S₂ − S₁ = p₁·d + (M₂ − M₁)
S2minusS1 : ∀ m → S₂ (encode m) -₉ S₁ (encode m) ≡ (p1 m *₉ d) +₉ (M2 m -₉ M1 m)
S2minusS1 m = begin
  S₂ (encode m) -₉ S₁ (encode m)
    ≡⟨ cong₂ _-gf9_ (S2-eq m) (S1-eq m) ⟩
  ((p0 m +₉ p1 m *₉ β2Pow 1) +₉ M2 m) -₉ ((p0 m +₉ p1 m *₉ βPowT 1) +₉ M1 m)
    ≡⟨⟩
  ((p0 m +₉ p1 m *₉ β2Pow 1) +₉ M2 m) +₉ negate9 ((p0 m +₉ p1 m *₉ βPowT 1) +₉ M1 m)
    ≡⟨ cong (λ x → ((p0 m +₉ p1 m *₉ β2Pow 1) +₉ M2 m) +₉ x)
            (negate9-⊕ (p0 m +₉ p1 m *₉ βPowT 1) (M1 m)) ⟩
  ((p0 m +₉ p1 m *₉ β2Pow 1) +₉ M2 m) +₉ (negate9 (p0 m +₉ p1 m *₉ βPowT 1) +₉ negate9 (M1 m))
    ≡⟨ +-shuffle (p0 m +₉ p1 m *₉ β2Pow 1) (M2 m) (negate9 (p0 m +₉ p1 m *₉ βPowT 1)) (negate9 (M1 m)) ⟩
  ((p0 m +₉ p1 m *₉ β2Pow 1) +₉ negate9 (p0 m +₉ p1 m *₉ βPowT 1)) +₉ (M2 m +₉ negate9 (M1 m))
    ≡⟨ cong (_+gf9 (M2 m +₉ negate9 (M1 m))) (front-cancel m) ⟩
  (p1 m *₉ d) +₉ (M2 m +₉ negate9 (M1 m))
    ≡⟨⟩
  (p1 m *₉ d) +₉ (M2 m -₉ M1 m)
  ∎ where
    front-cancel : ∀ m →
      (p0 m +₉ p1 m *₉ β2Pow 1) +₉ negate9 (p0 m +₉ p1 m *₉ βPowT 1)
      ≡ p1 m *₉ d
    front-cancel m = begin
      (p0 m +₉ p1 m *₉ β2Pow 1) +₉ negate9 (p0 m +₉ p1 m *₉ βPowT 1)
        ≡⟨ cong (λ x → (p0 m +₉ p1 m *₉ β2Pow 1) +₉ x)
                (negate9-⊕ (p0 m) (p1 m *₉ βPowT 1)) ⟩
      (p0 m +₉ p1 m *₉ β2Pow 1) +₉ (negate9 (p0 m) +₉ negate9 (p1 m *₉ βPowT 1))
        ≡⟨ +gf9-assoc (p0 m) (p1 m *₉ β2Pow 1) (negate9 (p0 m) +₉ negate9 (p1 m *₉ βPowT 1)) ⟩
      p0 m +₉ ((p1 m *₉ β2Pow 1) +₉ (negate9 (p0 m) +₉ negate9 (p1 m *₉ βPowT 1)))
        ≡⟨ cong (p0 m +gf9_) (sym (+gf9-assoc (p1 m *₉ β2Pow 1) (negate9 (p0 m)) (negate9 (p1 m *₉ βPowT 1)))) ⟩
      p0 m +₉ (((p1 m *₉ β2Pow 1) +₉ negate9 (p0 m)) +₉ negate9 (p1 m *₉ βPowT 1))
        ≡⟨ cong (λ t → p0 m +₉ (t +₉ negate9 (p1 m *₉ βPowT 1)))
                (+gf9-comm (p1 m *₉ β2Pow 1) (negate9 (p0 m))) ⟩
      p0 m +₉ ((negate9 (p0 m) +₉ p1 m *₉ β2Pow 1) +₉ negate9 (p1 m *₉ βPowT 1))
        ≡⟨ cong (p0 m +gf9_) (+gf9-assoc (negate9 (p0 m)) (p1 m *₉ β2Pow 1) (negate9 (p1 m *₉ βPowT 1))) ⟩
      p0 m +₉ (negate9 (p0 m) +₉ ((p1 m *₉ β2Pow 1) +₉ negate9 (p1 m *₉ βPowT 1)))
        ≡⟨ cong (p0 m +gf9_) (+gf9-comm (negate9 (p0 m)) ((p1 m *₉ β2Pow 1) +₉ negate9 (p1 m *₉ βPowT 1))) ⟩
      p0 m +₉ (((p1 m *₉ β2Pow 1) +₉ negate9 (p1 m *₉ βPowT 1)) +₉ negate9 (p0 m))
        ≡⟨ cancel-mid (p0 m) ((p1 m *₉ β2Pow 1) +₉ negate9 (p1 m *₉ βPowT 1)) ⟩
      (p1 m *₉ β2Pow 1) +₉ negate9 (p1 m *₉ βPowT 1)
        ≡⟨⟩
      (p1 m *₉ β2Pow 1) +₉ negate9 (p1 m *₉ βPowT 1)
        ≡⟨ cong (λ x → p1 m *₉ β2Pow 1 +₉ x) (sym (*-negateʳ (p1 m) (βPowT 1))) ⟩
      (p1 m *₉ β2Pow 1) +₉ (p1 m *₉ negate9 (βPowT 1))
        ≡⟨ sym (*gf9-distribˡ-+gf9 (p1 m) (β2Pow 1) (negate9 (βPowT 1))) ⟩
      p1 m *₉ (β2Pow 1 +₉ negate9 (βPowT 1))
        ≡⟨⟩
      p1 m *₉ d
      ∎

-- S₂ − S₁ = 0
S2minusS1-zero : ∀ m → S₂ (encode m) -₉ S₁ (encode m) ≡ zero9
S2minusS1-zero m = begin
  S₂ (encode m) -₉ S₁ (encode m)
    ≡⟨ S2minusS1 m ⟩
  (p1 m *₉ d) +₉ (M2 m -₉ M1 m)
    ≡⟨ cong (_+gf9 (M2 m -₉ M1 m)) (p1d-eq m) ⟩
  (M1 m -₉ M2 m) +₉ (M2 m -₉ M1 m)
    ≡⟨ cancel-cross (M1 m) (M2 m) ⟩
  zero9
  ∎ where
    p1d-eq : ∀ m → p1 m *₉ d ≡ M1 m -₉ M2 m
    p1d-eq m = begin
      p1 m *₉ d
        ≡⟨⟩
      ((M1 m -₉ M2 m) *₉ dInv) *₉ d
        ≡⟨ *gf9-assoc (M1 m -₉ M2 m) dInv d ⟩
      (M1 m -₉ M2 m) *₉ (dInv *₉ d)
        ≡⟨ cong ((M1 m -₉ M2 m) *gf9_) dInv-comm ⟩
      (M1 m -₉ M2 m) *₉ gf9-one
        ≡⟨ *gf9-identityʳ (M1 m -₉ M2 m) ⟩
      M1 m -₉ M2 m
      ∎

-- S₂ = 0
S2-zero : ∀ m → S₂ (encode m) ≡ zero9
S2-zero m = begin
  S₂ (encode m)
    ≡⟨ sym (cancel-right (S₂ (encode m)) (negate9 (S₁ (encode m)))) ⟩
  (S₂ (encode m) +₉ negate9 (S₁ (encode m))) +₉ negate9 (negate9 (S₁ (encode m)))
    ≡⟨ cong (λ t → (S₂ (encode m) +₉ negate9 (S₁ (encode m))) +₉ t) (negate9² (S₁ (encode m))) ⟩
  (S₂ (encode m) +₉ negate9 (S₁ (encode m))) +₉ S₁ (encode m)
    ≡⟨ cong (_+gf9 S₁ (encode m)) (S2minusS1-zero m) ⟩
  zero9 +₉ S₁ (encode m)
    ≡⟨ cong (zero9 +gf9_) (S1-zero m) ⟩
  zero9 +₉ zero9
    ≡⟨ +gf9-identityˡ zero9 ⟩
  zero9
  ∎

-- 编码正确性: 每个 encode m 都是码字
encode-correct : ∀ m → (S₁ (encode m) ≡ zero9) × (S₂ (encode m) ≡ zero9)
encode-correct m = S1-zero m , S2-zero m

--------------------------------------------------------------------------------
-- §4. 最小距离 ≥ 3 (BCH 界)
--------------------------------------------------------------------------------

-- 权 1 排除: 单非零位 ⟹ S₁ ≠ 0 ⟹ 非码字
no-weight-1 : ∀ c i → i < 8 → c i ≢ zero9 →
  (∀ k → k < 8 → k ≢ i → c k ≡ zero9) → S₁ c ≢ zero9
no-weight-1 c i i<8 ci≢0 vanish s₁≡0 =
  nonzero-× (c i) (βPowT i) ci≢0 (βPowT-nonzero i)
    (trans (sym (synd-single c βPowT i i<8 vanish)) s₁≡0)

-- Vandermonde 恒等式: S₂ − βⁱ·S₁ = c j · βʲ · (βʲ − βⁱ)  (i < j, 双非零位)
vdm-identity : ∀ c i j → i < j → j < 8 →
  (∀ k → k < 8 → k ≢ i → k ≢ j → c k ≡ zero9) →
  S₂ c -₉ βPowT i *₉ S₁ c ≡ c j *₉ (βPowT j *₉ (βPowT j -₉ βPowT i))
vdm-identity c i j i<j j<8 vanish = begin
  S₂ c -₉ βPowT i *₉ S₁ c
    ≡⟨ cong₂ (λ x y → x -₉ βPowT i *₉ y)
             (synd-sparse2 c β2Pow i j i<j j<8 vanish)
             (synd-sparse2 c βPowT i j i<j j<8 vanish) ⟩
  ((c i *₉ β2Pow i) +₉ (c j *₉ β2Pow j)) -₉ βPowT i *₉ ((c i *₉ βPowT i) +₉ (c j *₉ βPowT j))
    ≡⟨⟩
  ((c i *₉ β2Pow i) +₉ (c j *₉ β2Pow j)) +₉ negate9 (βPowT i *₉ ((c i *₉ βPowT i) +₉ (c j *₉ βPowT j)))
    ≡⟨ cong (λ x → ((c i *₉ β2Pow i) +₉ (c j *₉ β2Pow j)) +₉ x)
            (negate9-⊗ (βPowT i) ((c i *₉ βPowT i) +₉ (c j *₉ βPowT j))) ⟩
  ((c i *₉ β2Pow i) +₉ (c j *₉ β2Pow j)) +₉ (negate9 (βPowT i) *₉ ((c i *₉ βPowT i) +₉ (c j *₉ βPowT j)))
    ≡⟨ cong (λ x → ((c i *₉ β2Pow i) +₉ (c j *₉ β2Pow j)) +₉ x)
            (*gf9-distribˡ-+gf9 (negate9 (βPowT i)) (c i *₉ βPowT i) (c j *₉ βPowT j)) ⟩
  ((c i *₉ β2Pow i) +₉ (c j *₉ β2Pow j)) +₉ ((negate9 (βPowT i) *₉ (c i *₉ βPowT i)) +₉ (negate9 (βPowT i) *₉ (c j *₉ βPowT j)))
    ≡⟨ cong₂ (λ x y → ((c i *₉ β2Pow i) +₉ (c j *₉ β2Pow j)) +₉ (x +₉ y))
             (negate-βi-ci) (negate-βi-cj) ⟩
  ((c i *₉ β2Pow i) +₉ (c j *₉ β2Pow j)) +₉ (negate9 (c i *₉ β2Pow i) +₉ negate9 (c j *₉ βPowT i *₉ βPowT j))
    ≡⟨ cong (λ x → ((c i *₉ β2Pow i) +₉ (c j *₉ β2Pow j)) +₉ (negate9 (c i *₉ β2Pow i) +₉ x))
            (cong negate9 (*gf9-assoc (c j) (βPowT i) (βPowT j))) ⟩
  ((c i *₉ β2Pow i) +₉ (c j *₉ β2Pow j)) +₉ (negate9 (c i *₉ β2Pow i) +₉ negate9 (c j *₉ (βPowT i *₉ βPowT j)))
    ≡⟨ cancel-front (c i *₉ β2Pow i) (c j *₉ β2Pow j) (negate9 (c j *₉ (βPowT i *₉ βPowT j))) ⟩
  (c j *₉ β2Pow j) +₉ negate9 (c j *₉ (βPowT i *₉ βPowT j))
    ≡⟨⟩
  (c j *₉ (βPowT j *₉ βPowT j)) +₉ negate9 (c j *₉ (βPowT i *₉ βPowT j))
    ≡⟨ cong (λ x → x +₉ negate9 (c j *₉ (βPowT i *₉ βPowT j)))
            (sym (β-absorb (c j) j)) ⟩
  (βPowT j *₉ (c j *₉ βPowT j)) +₉ negate9 (c j *₉ (βPowT i *₉ βPowT j))
    ≡⟨ cong (λ x → x +₉ negate9 (c j *₉ (βPowT i *₉ βPowT j)))
            (β-absorb2 (c j) j (βPowT j)) ⟩
  (c j *₉ (βPowT j *₉ βPowT j)) +₉ negate9 (c j *₉ (βPowT i *₉ βPowT j))
    ≡⟨ cong (λ x → c j *₉ (βPowT j *₉ βPowT j) +₉ x)
            (sym (*-negateʳ (c j) (βPowT i *₉ βPowT j))) ⟩
  (c j *₉ (βPowT j *₉ βPowT j)) +₉ (c j *₉ negate9 (βPowT i *₉ βPowT j))
    ≡⟨ sym (*gf9-distribˡ-+gf9 (c j) (βPowT j *₉ βPowT j) (negate9 (βPowT i *₉ βPowT j))) ⟩
  c j *₉ ((βPowT j *₉ βPowT j) +₉ negate9 (βPowT i *₉ βPowT j))
    ≡⟨ cong (c j *gf9_) (lemma-βj-βi j i) ⟩
  c j *₉ (βPowT j *₉ (βPowT j -₉ βPowT i))
    ≡⟨ cong (c j *gf9_) (*gf9-comm (βPowT j) (βPowT j -₉ βPowT i)) ⟩
  c j *₉ ((βPowT j -₉ βPowT i) *₉ βPowT j)
    ≡⟨ sym (*gf9-assoc (c j) (βPowT j -₉ βPowT i) (βPowT j)) ⟩
  (c j *₉ (βPowT j -₉ βPowT i)) *₉ βPowT j
    ≡⟨ *gf9-comm (c j *₉ (βPowT j -₉ βPowT i)) (βPowT j) ⟩
  βPowT j *₉ (c j *₉ (βPowT j -₉ βPowT i))
    ≡⟨ β-absorb2 (c j) j (βPowT j -₉ βPowT i) ⟩
  c j *₉ (βPowT j *₉ (βPowT j -₉ βPowT i))
  ∎ where
    negate-βi-ci : negate9 (βPowT i) *₉ (c i *₉ βPowT i) ≡ negate9 (c i *₉ β2Pow i)
    negate-βi-ci = begin
      negate9 (βPowT i) *₉ (c i *₉ βPowT i)
        ≡⟨ sym (negate9-⊗ (βPowT i) (c i *₉ βPowT i)) ⟩
      negate9 (βPowT i *₉ (c i *₉ βPowT i))
        ≡⟨ cong negate9 (β-absorb (c i) i) ⟩
      negate9 (c i *₉ (βPowT i *₉ βPowT i))
        ≡⟨⟩
      negate9 (c i *₉ β2Pow i)
      ∎
    negate-βi-cj : negate9 (βPowT i) *₉ (c j *₉ βPowT j) ≡ negate9 (c j *₉ βPowT i *₉ βPowT j)
    negate-βi-cj = begin
      negate9 (βPowT i) *₉ (c j *₉ βPowT j)
        ≡⟨ sym (negate9-⊗ (βPowT i) (c j *₉ βPowT j)) ⟩
      negate9 (βPowT i *₉ (c j *₉ βPowT j))
        ≡⟨ cong negate9 (β-absorb2 (c j) i (βPowT j)) ⟩
      negate9 (c j *₉ (βPowT i *₉ βPowT j))
        ≡⟨ cong negate9 (sym (*gf9-assoc (c j) (βPowT i) (βPowT j))) ⟩
      negate9 ((c j *₉ βPowT i) *₉ βPowT j)
        ≡⟨⟩
      negate9 (c j *₉ βPowT i *₉ βPowT j)
      ∎
    lemma-βj-βi : ∀ j i → (βPowT j *₉ βPowT j) +₉ negate9 (βPowT i *₉ βPowT j)
                    ≡ βPowT j *₉ (βPowT j -₉ βPowT i)
    lemma-βj-βi j i = begin
      (βPowT j *₉ βPowT j) +₉ negate9 (βPowT i *₉ βPowT j)
        ≡⟨ cong (λ x → βPowT j *₉ βPowT j +₉ negate9 x)
                (*gf9-comm (βPowT i) (βPowT j)) ⟩
      (βPowT j *₉ βPowT j) +₉ negate9 (βPowT j *₉ βPowT i)
        ≡⟨ cong (λ x → βPowT j *₉ βPowT j +₉ x)
                (sym (*-negateʳ (βPowT j) (βPowT i))) ⟩
      (βPowT j *₉ βPowT j) +₉ (βPowT j *₉ negate9 (βPowT i))
        ≡⟨ sym (*gf9-distribˡ-+gf9 (βPowT j) (βPowT j) (negate9 (βPowT i))) ⟩
      βPowT j *₉ (βPowT j +₉ negate9 (βPowT i))
        ≡⟨⟩
      βPowT j *₉ (βPowT j -₉ βPowT i)
      ∎

-- 权 2 排除: 双非零位 ⟹ 非码字
no-weight-2 : ∀ c i j → i < j → j < 8 → c i ≢ zero9 → c j ≢ zero9 →
  (∀ k → k < 8 → k ≢ i → k ≢ j → c k ≡ zero9) →
  ¬ (S₁ c ≡ zero9 × S₂ c ≡ zero9)
no-weight-2 c i j i<j j<8 ci≢0 cj≢0 vanish (s₁≡0 , s₂≡0) =
  nonzero-× (c j) (βPowT j *₉ (βPowT j -₉ βPowT i)) cj≢0
    (nonzero-× (βPowT j) (βPowT j -₉ βPowT i) (βPowT-nonzero j)
      (sub≢0 (βPowT j) (βPowT i)
        (β-diff i j (<-trans i<j j<8) j<8 (m<n⇒m≢n i j i<j))))
    (trans (sym (vdm-identity c i j i<j j<8 vanish)) lhs≡0)
  where
    lhs≡0 : S₂ c -₉ βPowT i *₉ S₁ c ≡ zero9
    lhs≡0 = begin
      S₂ c -₉ βPowT i *₉ S₁ c
        ≡⟨ cong₂ _-gf9_ s₂≡0 (cong (βPowT i *gf9_) s₁≡0) ⟩
      zero9 -₉ βPowT i *₉ zero9
        ≡⟨ cong (λ x → zero9 -₉ x) (*gf9-zeroʳ (βPowT i)) ⟩
      zero9 -₉ zero9
        ≡⟨⟩
      zero9 +₉ negate9 zero9
        ≡⟨ cong (zero9 +gf9_) (negate9-zero) ⟩
      zero9 +₉ zero9
        ≡⟨ +gf9-identityˡ zero9 ⟩
      zero9
      ∎ where
        negate9-zero : negate9 zero9 ≡ zero9
        negate9-zero = refl

-- 权 3 见证码字: g(x) = (x−β)(x−β²) = x² + 2x + (1+2α) (信息位 m₂=1)
m3 : ℕ → GF9
m3 k = if does (k ≟ 2) then gf9-one else zero9

wt : (ℕ → GF9) → ℕ → ℕ
wt c zero = 0
wt c (suc n) = wt c n + bool→ℕ (nonzero? (c n))
  where
    bool→ℕ : Bool → ℕ
    bool→ℕ true = 1
    bool→ℕ false = 0
    nonzero? : GF9 → Bool
    nonzero? (T₀ , T₀) = false
    nonzero? _ = true

-- 权 3 码字: encode m3 恰有 3 个非零位 (0, 1, 2)
weight-3-witness : wt (encode m3) 8 ≡ 3
weight-3-witness = refl

-- 综合: 最小距离 = 3 (下界: 无权 ≤2 码字; 上界: 权 3 码字存在)
min-distance : (∀ c i → i < 8 → c i ≢ zero9 → (∀ k → k < 8 → k ≢ i → c k ≡ zero9)
                 → S₁ c ≢ zero9)
             × (∀ c i j → i < j → j < 8 → c i ≢ zero9 → c j ≢ zero9 →
                  (∀ k → k < 8 → k ≢ i → k ≢ j → c k ≡ zero9)
                 → ¬ (S₁ c ≡ zero9 × S₂ c ≡ zero9))
             × (wt (encode m3) 8 ≡ 3)
min-distance = no-weight-1 , no-weight-2 , weight-3-witness

--------------------------------------------------------------------------------
-- §5. 单错纠错
--------------------------------------------------------------------------------

-- 单错: 位置 i 处值 v ≠ 0
err' : (k i : ℕ) → Dec (k ≡ i) → GF9 → GF9
err' k i (yes _) v = v
err' k i (no  _) v = zero9

err : GF9 → ℕ → ℕ → GF9
err v i k = err' k i (k ≟ i) v

err-at : ∀ v i → err v i i ≡ v
err-at v i with i ≟ i
... | yes _ = refl
... | no ¬p = ⊥-elim (¬p refl)

err-vanish : ∀ v i k → k ≢ i → err v i k ≡ zero9
err-vanish v i k k≢i with k ≟ i
... | yes p = ⊥-elim (k≢i p)
... | no  _ = refl

-- 校验子加性
synd-add : ∀ c e w n → synd (λ k → c k +₉ e k) w n ≡ synd c w n +₉ synd e w n
synd-add c e w zero = sym (+gf9-identityʳ zero9)
synd-add c e w (suc n) = begin
  synd (λ k → c k +₉ e k) w n +₉ ((c n +₉ e n) *₉ w n)
    ≡⟨ cong (_+gf9 (c n +₉ e n) *₉ w n) (synd-add c e w n) ⟩
  (synd c w n +₉ synd e w n) +₉ ((c n +₉ e n) *₉ w n)
    ≡⟨ cong (λ x → (synd c w n +₉ synd e w n) +₉ x)
            (*gf9-distribʳ-+gf9 (c n) (e n) (w n)) ⟩
  (synd c w n +₉ synd e w n) +₉ (c n *₉ w n +₉ e n *₉ w n)
    ≡⟨ +-shuffle (synd c w n) (synd e w n) (c n *₉ w n) (e n *₉ w n) ⟩
  (synd c w n +₉ c n *₉ w n) +₉ (synd e w n +₉ e n *₉ w n)
  ∎

-- 接收字 r = encode m + err v i 的校验子
S1-received : ∀ m i v → i < 8 → v ≢ zero9 →
  S₁ (λ k → encode m k +₉ err v i k) ≡ v *₉ βPowT i
S1-received m i v i<8 v≢0 = begin
  S₁ (λ k → encode m k +₉ err v i k)
    ≡⟨ synd-add (encode m) (err v i) βPowT 8 ⟩
  S₁ (encode m) +₉ synd (err v i) βPowT 8
    ≡⟨ cong (_+gf9 synd (err v i) βPowT 8) (S1-zero m) ⟩
  zero9 +₉ synd (err v i) βPowT 8
    ≡⟨ +gf9-identityˡ (synd (err v i) βPowT 8) ⟩
  synd (err v i) βPowT 8
    ≡⟨ synd-single (err v i) βPowT i i<8 (λ k k<8 k≢i → err-vanish v i k k≢i) ⟩
  err v i i *₉ βPowT i
    ≡⟨ cong (_*gf9 βPowT i) (err-at v i) ⟩
  v *₉ βPowT i
  ∎

S2-received : ∀ m i v → i < 8 → v ≢ zero9 →
  S₂ (λ k → encode m k +₉ err v i k) ≡ v *₉ β2Pow i
S2-received m i v i<8 v≢0 = begin
  S₂ (λ k → encode m k +₉ err v i k)
    ≡⟨ synd-add (encode m) (err v i) β2Pow 8 ⟩
  S₂ (encode m) +₉ synd (err v i) β2Pow 8
    ≡⟨ cong (_+gf9 synd (err v i) β2Pow 8) (S2-zero m) ⟩
  zero9 +₉ synd (err v i) β2Pow 8
    ≡⟨ +gf9-identityˡ (synd (err v i) β2Pow 8) ⟩
  synd (err v i) β2Pow 8
    ≡⟨ synd-single (err v i) β2Pow i i<8 (λ k k<8 k≢i → err-vanish v i k k≢i) ⟩
  err v i i *₉ β2Pow i
    ≡⟨ cong (_*gf9 β2Pow i) (err-at v i) ⟩
  v *₉ β2Pow i
  ∎

-- 错误定位表: (S₁, S₂) → (位置, 错误值)  (81 case, 生成)
findError : GF9 → GF9 → ℕ × GF9
findError (T₀ , T₀) (T₀ , T₀) = 0 , zero9
findError (T₀ , T₀) (T₀ , T₁) = 0 , zero9
findError (T₀ , T₀) (T₀ , T₂) = 0 , zero9
findError (T₀ , T₀) (T₁ , T₀) = 0 , zero9
findError (T₀ , T₀) (T₁ , T₁) = 0 , zero9
findError (T₀ , T₀) (T₁ , T₂) = 0 , zero9
findError (T₀ , T₀) (T₂ , T₀) = 0 , zero9
findError (T₀ , T₀) (T₂ , T₁) = 0 , zero9
findError (T₀ , T₀) (T₂ , T₂) = 0 , zero9
findError (T₀ , T₁) (T₀ , T₀) = 0 , zero9
findError (T₀ , T₁) (T₀ , T₁) = 0 , toGF9 sα
findError (T₀ , T₁) (T₀ , T₂) = 4 , toGF9 s2α
findError (T₀ , T₁) (T₁ , T₀) = 2 , toGF9 s2
findError (T₀ , T₁) (T₁ , T₁) = 3 , toGF9 s12α
findError (T₀ , T₁) (T₁ , T₂) = 5 , toGF9 s1α
findError (T₀ , T₁) (T₂ , T₀) = 6 , toGF9 s1
findError (T₀ , T₁) (T₂ , T₁) = 1 , toGF9 s22α
findError (T₀ , T₁) (T₂ , T₂) = 7 , toGF9 s21α
findError (T₀ , T₂) (T₀ , T₀) = 0 , zero9
findError (T₀ , T₂) (T₀ , T₁) = 4 , toGF9 sα
findError (T₀ , T₂) (T₀ , T₂) = 0 , toGF9 s2α
findError (T₀ , T₂) (T₁ , T₀) = 6 , toGF9 s2
findError (T₀ , T₂) (T₁ , T₁) = 7 , toGF9 s12α
findError (T₀ , T₂) (T₁ , T₂) = 1 , toGF9 s1α
findError (T₀ , T₂) (T₂ , T₀) = 2 , toGF9 s1
findError (T₀ , T₂) (T₂ , T₁) = 5 , toGF9 s22α
findError (T₀ , T₂) (T₂ , T₂) = 3 , toGF9 s21α
findError (T₁ , T₀) (T₀ , T₀) = 0 , zero9
findError (T₁ , T₀) (T₀ , T₁) = 6 , toGF9 s2α
findError (T₁ , T₀) (T₀ , T₂) = 2 , toGF9 sα
findError (T₁ , T₀) (T₁ , T₀) = 0 , toGF9 s1
findError (T₁ , T₀) (T₁ , T₁) = 1 , toGF9 s21α
findError (T₁ , T₀) (T₁ , T₂) = 3 , toGF9 s22α
findError (T₁ , T₀) (T₂ , T₀) = 4 , toGF9 s2
findError (T₁ , T₀) (T₂ , T₁) = 7 , toGF9 s1α
findError (T₁ , T₀) (T₂ , T₂) = 5 , toGF9 s12α
findError (T₁ , T₁) (T₀ , T₀) = 0 , zero9
findError (T₁ , T₁) (T₀ , T₁) = 5 , toGF9 s2
findError (T₁ , T₁) (T₀ , T₂) = 1 , toGF9 s1
findError (T₁ , T₁) (T₁ , T₀) = 7 , toGF9 s2α
findError (T₁ , T₁) (T₁ , T₁) = 0 , toGF9 s1α
findError (T₁ , T₁) (T₁ , T₂) = 2 , toGF9 s21α
findError (T₁ , T₁) (T₂ , T₀) = 3 , toGF9 sα
findError (T₁ , T₁) (T₂ , T₁) = 6 , toGF9 s12α
findError (T₁ , T₁) (T₂ , T₂) = 4 , toGF9 s22α
findError (T₁ , T₂) (T₀ , T₀) = 0 , zero9
findError (T₁ , T₂) (T₀ , T₁) = 3 , toGF9 s1
findError (T₁ , T₂) (T₀ , T₂) = 7 , toGF9 s2
findError (T₁ , T₂) (T₁ , T₀) = 5 , toGF9 sα
findError (T₁ , T₂) (T₁ , T₁) = 6 , toGF9 s22α
findError (T₁ , T₂) (T₁ , T₂) = 0 , toGF9 s12α
findError (T₁ , T₂) (T₂ , T₀) = 1 , toGF9 s2α
findError (T₁ , T₂) (T₂ , T₁) = 4 , toGF9 s21α
findError (T₁ , T₂) (T₂ , T₂) = 2 , toGF9 s1α
findError (T₂ , T₀) (T₀ , T₀) = 0 , zero9
findError (T₂ , T₀) (T₀ , T₁) = 2 , toGF9 s2α
findError (T₂ , T₀) (T₀ , T₂) = 6 , toGF9 sα
findError (T₂ , T₀) (T₁ , T₀) = 4 , toGF9 s1
findError (T₂ , T₀) (T₁ , T₁) = 5 , toGF9 s21α
findError (T₂ , T₀) (T₁ , T₂) = 7 , toGF9 s22α
findError (T₂ , T₀) (T₂ , T₀) = 0 , toGF9 s2
findError (T₂ , T₀) (T₂ , T₁) = 3 , toGF9 s1α
findError (T₂ , T₀) (T₂ , T₂) = 1 , toGF9 s12α
findError (T₂ , T₁) (T₀ , T₀) = 0 , zero9
findError (T₂ , T₁) (T₀ , T₁) = 7 , toGF9 s1
findError (T₂ , T₁) (T₀ , T₂) = 3 , toGF9 s2
findError (T₂ , T₁) (T₁ , T₀) = 1 , toGF9 sα
findError (T₂ , T₁) (T₁ , T₁) = 2 , toGF9 s22α
findError (T₂ , T₁) (T₁ , T₂) = 4 , toGF9 s12α
findError (T₂ , T₁) (T₂ , T₀) = 5 , toGF9 s2α
findError (T₂ , T₁) (T₂ , T₁) = 0 , toGF9 s21α
findError (T₂ , T₁) (T₂ , T₂) = 6 , toGF9 s1α
findError (T₂ , T₂) (T₀ , T₀) = 0 , zero9
findError (T₂ , T₂) (T₀ , T₁) = 1 , toGF9 s2
findError (T₂ , T₂) (T₀ , T₂) = 5 , toGF9 s1
findError (T₂ , T₂) (T₁ , T₀) = 3 , toGF9 s2α
findError (T₂ , T₂) (T₁ , T₁) = 4 , toGF9 s1α
findError (T₂ , T₂) (T₁ , T₂) = 6 , toGF9 s21α
findError (T₂ , T₂) (T₂ , T₀) = 7 , toGF9 sα
findError (T₂ , T₂) (T₂ , T₁) = 2 , toGF9 s12α
findError (T₂ , T₂) (T₂ , T₂) = 0 , toGF9 s22α

-- 定位表反演: 对任意合法 (i, v): findError (v·βⁱ, v·β²ⁱ) = (i, v)
findError-loc : ∀ i v → i < 8 → v ≢ zero9 →
  findError (v *₉ βPowT i) (v *₉ β2Pow i) ≡ (i , v)
findError-loc (zero) (T₀ , T₀) _ v≢0 = ⊥-elim (v≢0 refl)
findError-loc (zero) (T₀ , T₁) _ _ = refl
findError-loc (zero) (T₀ , T₂) _ _ = refl
findError-loc (zero) (T₁ , T₀) _ _ = refl
findError-loc (zero) (T₁ , T₁) _ _ = refl
findError-loc (zero) (T₁ , T₂) _ _ = refl
findError-loc (zero) (T₂ , T₀) _ _ = refl
findError-loc (zero) (T₂ , T₁) _ _ = refl
findError-loc (zero) (T₂ , T₂) _ _ = refl
findError-loc (suc zero) (T₀ , T₀) _ v≢0 = ⊥-elim (v≢0 refl)
findError-loc (suc zero) (T₀ , T₁) _ _ = refl
findError-loc (suc zero) (T₀ , T₂) _ _ = refl
findError-loc (suc zero) (T₁ , T₀) _ _ = refl
findError-loc (suc zero) (T₁ , T₁) _ _ = refl
findError-loc (suc zero) (T₁ , T₂) _ _ = refl
findError-loc (suc zero) (T₂ , T₀) _ _ = refl
findError-loc (suc zero) (T₂ , T₁) _ _ = refl
findError-loc (suc zero) (T₂ , T₂) _ _ = refl
findError-loc (suc (suc zero)) (T₀ , T₀) _ v≢0 = ⊥-elim (v≢0 refl)
findError-loc (suc (suc zero)) (T₀ , T₁) _ _ = refl
findError-loc (suc (suc zero)) (T₀ , T₂) _ _ = refl
findError-loc (suc (suc zero)) (T₁ , T₀) _ _ = refl
findError-loc (suc (suc zero)) (T₁ , T₁) _ _ = refl
findError-loc (suc (suc zero)) (T₁ , T₂) _ _ = refl
findError-loc (suc (suc zero)) (T₂ , T₀) _ _ = refl
findError-loc (suc (suc zero)) (T₂ , T₁) _ _ = refl
findError-loc (suc (suc zero)) (T₂ , T₂) _ _ = refl
findError-loc (suc (suc (suc zero))) (T₀ , T₀) _ v≢0 = ⊥-elim (v≢0 refl)
findError-loc (suc (suc (suc zero))) (T₀ , T₁) _ _ = refl
findError-loc (suc (suc (suc zero))) (T₀ , T₂) _ _ = refl
findError-loc (suc (suc (suc zero))) (T₁ , T₀) _ _ = refl
findError-loc (suc (suc (suc zero))) (T₁ , T₁) _ _ = refl
findError-loc (suc (suc (suc zero))) (T₁ , T₂) _ _ = refl
findError-loc (suc (suc (suc zero))) (T₂ , T₀) _ _ = refl
findError-loc (suc (suc (suc zero))) (T₂ , T₁) _ _ = refl
findError-loc (suc (suc (suc zero))) (T₂ , T₂) _ _ = refl
findError-loc (suc (suc (suc (suc zero)))) (T₀ , T₀) _ v≢0 = ⊥-elim (v≢0 refl)
findError-loc (suc (suc (suc (suc zero)))) (T₀ , T₁) _ _ = refl
findError-loc (suc (suc (suc (suc zero)))) (T₀ , T₂) _ _ = refl
findError-loc (suc (suc (suc (suc zero)))) (T₁ , T₀) _ _ = refl
findError-loc (suc (suc (suc (suc zero)))) (T₁ , T₁) _ _ = refl
findError-loc (suc (suc (suc (suc zero)))) (T₁ , T₂) _ _ = refl
findError-loc (suc (suc (suc (suc zero)))) (T₂ , T₀) _ _ = refl
findError-loc (suc (suc (suc (suc zero)))) (T₂ , T₁) _ _ = refl
findError-loc (suc (suc (suc (suc zero)))) (T₂ , T₂) _ _ = refl
findError-loc (suc (suc (suc (suc (suc zero))))) (T₀ , T₀) _ v≢0 = ⊥-elim (v≢0 refl)
findError-loc (suc (suc (suc (suc (suc zero))))) (T₀ , T₁) _ _ = refl
findError-loc (suc (suc (suc (suc (suc zero))))) (T₀ , T₂) _ _ = refl
findError-loc (suc (suc (suc (suc (suc zero))))) (T₁ , T₀) _ _ = refl
findError-loc (suc (suc (suc (suc (suc zero))))) (T₁ , T₁) _ _ = refl
findError-loc (suc (suc (suc (suc (suc zero))))) (T₁ , T₂) _ _ = refl
findError-loc (suc (suc (suc (suc (suc zero))))) (T₂ , T₀) _ _ = refl
findError-loc (suc (suc (suc (suc (suc zero))))) (T₂ , T₁) _ _ = refl
findError-loc (suc (suc (suc (suc (suc zero))))) (T₂ , T₂) _ _ = refl
findError-loc (suc (suc (suc (suc (suc (suc zero)))))) (T₀ , T₀) _ v≢0 = ⊥-elim (v≢0 refl)
findError-loc (suc (suc (suc (suc (suc (suc zero)))))) (T₀ , T₁) _ _ = refl
findError-loc (suc (suc (suc (suc (suc (suc zero)))))) (T₀ , T₂) _ _ = refl
findError-loc (suc (suc (suc (suc (suc (suc zero)))))) (T₁ , T₀) _ _ = refl
findError-loc (suc (suc (suc (suc (suc (suc zero)))))) (T₁ , T₁) _ _ = refl
findError-loc (suc (suc (suc (suc (suc (suc zero)))))) (T₁ , T₂) _ _ = refl
findError-loc (suc (suc (suc (suc (suc (suc zero)))))) (T₂ , T₀) _ _ = refl
findError-loc (suc (suc (suc (suc (suc (suc zero)))))) (T₂ , T₁) _ _ = refl
findError-loc (suc (suc (suc (suc (suc (suc zero)))))) (T₂ , T₂) _ _ = refl
findError-loc (suc (suc (suc (suc (suc (suc (suc zero))))))) (T₀ , T₀) _ v≢0 = ⊥-elim (v≢0 refl)
findError-loc (suc (suc (suc (suc (suc (suc (suc zero))))))) (T₀ , T₁) _ _ = refl
findError-loc (suc (suc (suc (suc (suc (suc (suc zero))))))) (T₀ , T₂) _ _ = refl
findError-loc (suc (suc (suc (suc (suc (suc (suc zero))))))) (T₁ , T₀) _ _ = refl
findError-loc (suc (suc (suc (suc (suc (suc (suc zero))))))) (T₁ , T₁) _ _ = refl
findError-loc (suc (suc (suc (suc (suc (suc (suc zero))))))) (T₁ , T₂) _ _ = refl
findError-loc (suc (suc (suc (suc (suc (suc (suc zero))))))) (T₂ , T₀) _ _ = refl
findError-loc (suc (suc (suc (suc (suc (suc (suc zero))))))) (T₂ , T₁) _ _ = refl
findError-loc (suc (suc (suc (suc (suc (suc (suc zero))))))) (T₂ , T₂) _ _ = refl
findError-loc (suc (suc (suc (suc (suc (suc (suc (suc m)))))))) (T₀ , T₀) i<8 _ = ⊥-elim (suc⁸<n _ i<8)
findError-loc (suc (suc (suc (suc (suc (suc (suc (suc m)))))))) (T₀ , T₁) i<8 _ = ⊥-elim (suc⁸<n _ i<8)
findError-loc (suc (suc (suc (suc (suc (suc (suc (suc m)))))))) (T₀ , T₂) i<8 _ = ⊥-elim (suc⁸<n _ i<8)
findError-loc (suc (suc (suc (suc (suc (suc (suc (suc m)))))))) (T₁ , T₀) i<8 _ = ⊥-elim (suc⁸<n _ i<8)
findError-loc (suc (suc (suc (suc (suc (suc (suc (suc m)))))))) (T₁ , T₁) i<8 _ = ⊥-elim (suc⁸<n _ i<8)
findError-loc (suc (suc (suc (suc (suc (suc (suc (suc m)))))))) (T₁ , T₂) i<8 _ = ⊥-elim (suc⁸<n _ i<8)
findError-loc (suc (suc (suc (suc (suc (suc (suc (suc m)))))))) (T₂ , T₀) i<8 _ = ⊥-elim (suc⁸<n _ i<8)
findError-loc (suc (suc (suc (suc (suc (suc (suc (suc m)))))))) (T₂ , T₁) i<8 _ = ⊥-elim (suc⁸<n _ i<8)
findError-loc (suc (suc (suc (suc (suc (suc (suc (suc m)))))))) (T₂ , T₂) i<8 _ = ⊥-elim (suc⁸<n _ i<8)

-- 位调整: 位置 i 加 v
adjust' : (k i : ℕ) → Dec (k ≡ i) → (ℕ → GF9) → GF9 → GF9
adjust' k i (yes _) r v = r k +₉ v
adjust' k i (no  _) r v = r k

adjust : (ℕ → GF9) → ℕ → GF9 → ℕ → GF9
adjust r i v k = adjust' k i (k ≟ i) r v

-- 调整还原: c + err v i 减去 v 回到 c
adjust-correct : ∀ c i v k → adjust (λ k → c k +₉ err v i k) i (negate9 v) k ≡ c k
adjust-correct c i v k = go (k ≟ i)
  where
    r = λ k → c k +₉ err v i k
    go : Dec (k ≡ i) → adjust r i (negate9 v) k ≡ c k
    go (yes p) = begin
      adjust r i (negate9 v) k
        ≡⟨⟩
      adjust' k i (k ≟ i) r (negate9 v)
        ≡⟨ cong (λ d → adjust' k i d r (negate9 v)) (≟-diag p) ⟩
      adjust' k i (yes p) r (negate9 v)
        ≡⟨⟩
      (c k +₉ err v i k) +₉ negate9 v
        ≡⟨ cong (λ x → (c x +₉ err v i x) +₉ negate9 v) p ⟩
      (c i +₉ err v i i) +₉ negate9 v
        ≡⟨ cong (λ x → (c i +₉ x) +₉ negate9 v) (err-at v i) ⟩
      (c i +₉ v) +₉ negate9 v
        ≡⟨ cancel-right (c i) v ⟩
      c i
        ≡⟨ sym (cong c p) ⟩
      c k
      ∎
    go (no ¬p) = begin
      adjust r i (negate9 v) k
        ≡⟨⟩
      adjust' k i (k ≟ i) r (negate9 v)
        ≡⟨ cong (λ d → adjust' k i d r (negate9 v)) (≟-≡ ¬p) ⟩
      adjust' k i (no ¬p) r (negate9 v)
        ≡⟨⟩
      c k +₉ err v i k
        ≡⟨ cong (c k +gf9_) (err-vanish v i k ¬p) ⟩
      c k +₉ zero9
        ≡⟨ +gf9-identityʳ (c k) ⟩
      c k
      ∎

-- 解码: 由校验子对定位并纠错
decode : (ℕ → GF9) → ℕ → GF9
decode r = adjust r (proj₁ (findError (S₁ r) (S₂ r))) (negate9 (proj₂ (findError (S₁ r) (S₂ r))))

-- 解码正确性: 码字 + 单错 ⟹ 解码还原码字
decode-correct : ∀ m i v → i < 8 → v ≢ zero9 →
  (k : ℕ) → decode (λ k → encode m k +₉ err v i k) k ≡ encode m k
decode-correct m i v i<8 v≢0 k = begin
  decode (λ k → encode m k +₉ err v i k) k
    ≡⟨ cong (λ p → adjust (λ k → encode m k +₉ err v i k) (proj₁ p) (negate9 (proj₂ p)) k)
            (find-located) ⟩
  adjust (λ k → encode m k +₉ err v i k) i (negate9 v) k
    ≡⟨ adjust-correct (encode m) i v k ⟩
  encode m k
  ∎ where
    r = λ k → encode m k +₉ err v i k
    find-located : findError (S₁ r) (S₂ r) ≡ (i , v)
    find-located = trans
      (cong₂ findError (S1-received m i v i<8 v≢0) (S2-received m i v i<8 v≢0))
      (findError-loc i v i<8 v≢0)
