{-# OPTIONS --rewriting #-}
module Sovereign.Algebra.GF9 where

-- GF(3²) = GF(3)[x]/(x²+1)
-- 9 个元素的有限域。α 是二次扩张 [GF(9):GF(3)]=2 的生成元，满足 α² = -1。
--   （在 GF(3) 中 -1 ≡ 2，但此处的 "2" 首先是扩张的拓扑序：
--     [GF(9):GF(3)]=2、|Gal|=2、σ²=id——结构序，不是域内元素值。
--     算术（x² 等于哪个元素）≠ 数论（什么元素生成了阶为 2 的共轭结构））
-- Galois 群 Gal(GF(9)/GF(3)) ≅ C₂, 生成元 σ(α) = -α。
--   σ(x) = x³ 是 Frobenius 自同构——多项式映射，char 3 代数原生涌现，
--   不是外挂结构（区别于复共轭 z↦z̄：char 0 无 Frobenius，必须额外引入）。
--
-- 使用 Sovereign.Base.Trit 作为 GF(3) 底层类型,
-- 与 Rust sov-math types.rs Trit 对齐。

open import Data.Product using (_×_; _,_; Σ; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; sym; trans; module ≡-Reasoning)
open ≡-Reasoning
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Sovereign.Base.Trit using (Trit; T₀; T₁; T₂; _⊕_; _⊗_;
  c3-ccw; c3-cw; negate; negate²; ⊕-inverse;
  ⊕-comm; ⊕-assoc; ⊕-identityˡ; ⊕-identityʳ;
  ⊗-comm; ⊗-identityˡ; ⊗-identityʳ;
  ⊗-distribˡ-⊕; ⊗-distribʳ-⊕; ⊗-zeroʳ; ⊗-zeroˡ)

-- GF(3) 类型别名 (与 Rust a≡ 对齐)
GF3 : Set
GF3 = Trit

-- C3 互逆性 (c3-cw/c3-ccw 定义在 Base/Trit)
c3-cw-ccw-inverse : ∀ x → c3-cw (c3-ccw x) ≡ x
c3-cw-ccw-inverse T₀ = refl; c3-cw-ccw-inverse T₁ = refl; c3-cw-ccw-inverse T₂ = refl

c3-ccw-cw-inverse : ∀ x → c3-ccw (c3-cw x) ≡ x
c3-ccw-cw-inverse T₀ = refl; c3-ccw-cw-inverse T₁ = refl; c3-ccw-cw-inverse T₂ = refl

-- negate 代数性质 (Trit 层, 各 9 case)
-- 这些引理驱动 GF9 层的域性质证明, 替代穷举

negate-⊕ : ∀ x y → negate (x ⊕ y) ≡ negate x ⊕ negate y
negate-⊕ T₀ y = refl
negate-⊕ T₁ T₀ = refl; negate-⊕ T₁ T₁ = refl; negate-⊕ T₁ T₂ = refl
negate-⊕ T₂ T₀ = refl; negate-⊕ T₂ T₁ = refl; negate-⊕ T₂ T₂ = refl

negate-⊗ : ∀ x y → negate (x ⊗ y) ≡ (negate x) ⊗ y
negate-⊗ T₀ y = refl
negate-⊗ T₁ T₀ = refl; negate-⊗ T₁ T₁ = refl; negate-⊗ T₁ T₂ = refl
negate-⊗ T₂ T₀ = refl; negate-⊗ T₂ T₁ = refl; negate-⊗ T₂ T₂ = refl

negate-⊗-negate : ∀ x y → (negate x) ⊗ (negate y) ≡ x ⊗ y
negate-⊗-negate T₀ y = refl
negate-⊗-negate T₁ T₀ = refl; negate-⊗-negate T₁ T₁ = refl; negate-⊗-negate T₁ T₂ = refl
negate-⊗-negate T₂ T₀ = refl; negate-⊗-negate T₂ T₁ = refl; negate-⊗-negate T₂ T₂ = refl

negate-⊗-comm : ∀ x y → (negate x) ⊗ y ≡ x ⊗ (negate y)
negate-⊗-comm T₀ y = refl
negate-⊗-comm T₁ T₀ = refl; negate-⊗-comm T₁ T₁ = refl; negate-⊗-comm T₁ T₂ = refl
negate-⊗-comm T₂ T₀ = refl; negate-⊗-comm T₂ T₁ = refl; negate-⊗-comm T₂ T₂ = refl

--------------------------------------------------------------------------------
-- 1. GF(3²) 域定义
--------------------------------------------------------------------------------

GF9 : Set
GF9 = GF3 × GF3   -- (a, b) = a + bα, α² = -1

embed-gf3 : GF3 → GF9
embed-gf3 a = a , T₀

alpha : GF9
alpha = T₀ , T₁   -- 0 + 1·α

--------------------------------------------------------------------------------
-- 2. Galois 共轭（Frobenius σ: a+bα ↦ a-bα）
--------------------------------------------------------------------------------

-- Galois 共轭: σ(a+bα) = a + (-b)·α = a + negate(b)·α
galoisConjugate : GF9 → GF9
galoisConjugate (a , b) = a , negate b

galoisConjugate² : ∀ x → galoisConjugate (galoisConjugate x) ≡ x
galoisConjugate² (a , b) = cong (a ,_) (negate² b)

--------------------------------------------------------------------------------
-- 3. 范数与迹
--------------------------------------------------------------------------------

-- N(a+bα) = a² + b²  (GF(3) 中)
galoisNorm : GF9 → GF3
galoisNorm (a , b) = (a ⊗ a) ⊕ (b ⊗ b)

galoisNorm-conjugate : ∀ x → galoisNorm (galoisConjugate x) ≡ galoisNorm x
galoisNorm-conjugate (a , b) = cong (λ x → (a ⊗ a) ⊕ x) (negate-⊗-negate b b)

-- Tr(a+bα) = 2a  (GF(3) 中 2a = -a)
galoisTrace : GF9 → GF3
galoisTrace (a , b) = a ⊕ a

--------------------------------------------------------------------------------
-- 4. GF(3²) 域运算
--------------------------------------------------------------------------------

_+gf9_ : GF9 → GF9 → GF9
(a , b) +gf9 (c , d) = (a ⊕ c) , (b ⊕ d)

-- (a+bα)(c+dα) = (ac - bd) + (ad+bc)α  with α² = -1
-- -bd = negate(b⊗d)
_*gf9_ : GF9 → GF9 → GF9
(a , b) *gf9 (c , d) = ((a ⊗ c) ⊕ (negate (b ⊗ d))) , ((a ⊗ d) ⊕ (b ⊗ c))

gf9-one : GF9
gf9-one = T₁ , T₀

--------------------------------------------------------------------------------
-- 4b. GF9 域公理 (成分 + GF3 环公理推导)
--------------------------------------------------------------------------------

-- 加法交换律 (成分: ⊕-comm)
+gf9-comm : ∀ x y → x +gf9 y ≡ y +gf9 x
+gf9-comm (a , b) (c , d) = cong₂ _,_ (⊕-comm a c) (⊕-comm b d)

-- 加法结合律 (成分: ⊕-assoc)
+gf9-assoc : ∀ x y z → (x +gf9 y) +gf9 z ≡ x +gf9 (y +gf9 z)
+gf9-assoc (a , b) (c , d) (e , f) = cong₂ _,_ (⊕-assoc a c e) (⊕-assoc b d f)

-- 加法单位元
+gf9-identityˡ : ∀ x → (T₀ , T₀) +gf9 x ≡ x
+gf9-identityˡ (a , b) = cong₂ _,_ (⊕-identityˡ a) (⊕-identityˡ b)

+gf9-identityʳ : ∀ x → x +gf9 (T₀ , T₀) ≡ x
+gf9-identityʳ (a , b) = cong₂ _,_ (⊕-identityʳ a) (⊕-identityʳ b)

-- 加法逆元
+gf9-inverse : ∀ x → x +gf9 (negate (proj₁ x) , negate (proj₂ x)) ≡ (T₀ , T₀)
+gf9-inverse (a , b) = cong₂ _,_ (⊕-inverse a) (⊕-inverse b)

-- 乘法单位元
*gf9-identityˡ : ∀ x → gf9-one *gf9 x ≡ x
*gf9-identityˡ (a , b) = cong₂ _,_
  (trans (cong (_⊕ T₀) (⊗-identityˡ a)) (⊕-identityʳ a))
  (trans (cong (_⊕ T₀) (⊗-identityˡ b)) (⊕-identityʳ b))

*gf9-identityʳ : ∀ x → x *gf9 gf9-one ≡ x
*gf9-identityʳ (a , b) = cong₂ _,_ real imag
  where
    -- 实部: a⊗T₁ ⊕ negate(b⊗T₀) = a ⊕ negate(T₀) = a ⊕ T₀ = a
    real : (a ⊗ T₁) ⊕ (negate (b ⊗ T₀)) ≡ a
    real = trans (cong (λ t → t ⊕ (negate (b ⊗ T₀))) (⊗-identityʳ a))
                 (trans (cong (a ⊕_) (cong negate (⊗-zeroʳ b)))
                        (⊕-identityʳ a))
    -- 虚部: a⊗T₀ ⊕ b⊗T₁ = T₀ ⊕ b = b
    imag : (a ⊗ T₀) ⊕ (b ⊗ T₁) ≡ b
    imag = trans (cong₂ _⊕_ (⊗-zeroʳ a) (⊗-identityʳ b)) (⊕-identityˡ b)

-- 乘法交换律 (代数证明: ⊗-comm + ⊕-comm)
*gf9-comm : ∀ x y → x *gf9 y ≡ y *gf9 x
*gf9-comm (a , b) (c , d) = cong₂ _,_
  (cong₂ (λ p q → p ⊕ (negate q)) (⊗-comm a c) (⊗-comm b d))
  (trans (cong₂ _⊕_ (⊗-comm a d) (⊗-comm b c)) (⊕-comm (d ⊗ a) (c ⊗ b)))

-- 四元和中交换中间两项: (w⊕x)⊕(y⊕z) ≡ (w⊕y)⊕(x⊕z)
-- 由 ⊕ 交换律和结合律推导
swap-middle : ∀ w x y z → (w ⊕ x) ⊕ (y ⊕ z) ≡ (w ⊕ y) ⊕ (x ⊕ z)
swap-middle w x y z =
  trans (sym (⊕-assoc (w ⊕ x) y z))
    (trans (cong (λ t → t ⊕ z) (⊕-assoc w x y))
      (trans (cong (λ t → (w ⊕ t) ⊕ z) (⊕-comm x y))
        (trans (cong (λ t → t ⊕ z) (sym (⊕-assoc w y x)))
          (⊕-assoc (w ⊕ y) x z))))

-- 左分配律: x * (y + z) ≡ x*y + x*z
-- 代数证明: 展开定义 → ⊗-distribˡ-⊕ + negate-⊕ + swap-middle
*gf9-distribˡ-+gf9 : ∀ x y z → x *gf9 (y +gf9 z) ≡ (x *gf9 y) +gf9 (x *gf9 z)
*gf9-distribˡ-+gf9 (a , b) (c , d) (e , f) = cong₂ _,_ real imag
  where
    real : (a ⊗ (c ⊕ e)) ⊕ (negate (b ⊗ (d ⊕ f)))
         ≡ ((a ⊗ c) ⊕ (negate (b ⊗ d))) ⊕ ((a ⊗ e) ⊕ (negate (b ⊗ f)))
    real = trans
      (cong₂ (λ u v → u ⊕ (negate v)) (⊗-distribˡ-⊕ a c e) (⊗-distribˡ-⊕ b d f))
      (trans (cong (((a ⊗ c) ⊕ (a ⊗ e)) ⊕_) (negate-⊕ (b ⊗ d) (b ⊗ f)))
             (swap-middle (a ⊗ c) (a ⊗ e) (negate (b ⊗ d)) (negate (b ⊗ f))))

    imag : (a ⊗ (d ⊕ f)) ⊕ (b ⊗ (c ⊕ e))
         ≡ ((a ⊗ d) ⊕ (b ⊗ c)) ⊕ ((a ⊗ f) ⊕ (b ⊗ e))
    imag = trans
      (cong₂ _⊕_ (⊗-distribˡ-⊕ a d f) (⊗-distribˡ-⊕ b c e))
      (swap-middle (a ⊗ d) (a ⊗ f) (b ⊗ c) (b ⊗ e))

-- 右分配律: (x + y) * z ≡ x*z + y*z
-- 代数证明: 展开定义 → ⊗-distribʳ-⊕ + negate-⊕ + swap-middle
*gf9-distribʳ-+gf9 : ∀ x y z → (x +gf9 y) *gf9 z ≡ (x *gf9 z) +gf9 (y *gf9 z)
*gf9-distribʳ-+gf9 (a , b) (c , d) (e , f) = cong₂ _,_ real imag
  where
    real : ((a ⊕ c) ⊗ e) ⊕ (negate ((b ⊕ d) ⊗ f))
         ≡ ((a ⊗ e) ⊕ (negate (b ⊗ f))) ⊕ ((c ⊗ e) ⊕ (negate (d ⊗ f)))
    real = trans
      (cong₂ (λ u v → u ⊕ (negate v)) (⊗-distribʳ-⊕ a c e) (⊗-distribʳ-⊕ b d f))
      (trans (cong (((a ⊗ e) ⊕ (c ⊗ e)) ⊕_) (negate-⊕ (b ⊗ f) (d ⊗ f)))
             (swap-middle (a ⊗ e) (c ⊗ e) (negate (b ⊗ f)) (negate (d ⊗ f))))

    imag : ((a ⊕ c) ⊗ f) ⊕ ((b ⊕ d) ⊗ e)
         ≡ ((a ⊗ f) ⊕ (b ⊗ e)) ⊕ ((c ⊗ f) ⊕ (d ⊗ e))
    imag = trans
      (cong₂ _⊕_ (⊗-distribʳ-⊕ a c f) (⊗-distribʳ-⊕ b d e))
      (swap-middle (a ⊗ f) (c ⊗ f) (b ⊗ e) (d ⊗ e))
--------------------------------------------------------------------------------

alpha-squared : alpha *gf9 alpha ≡ (T₂ , T₀)
alpha-squared = refl

alpha-powers-4 : (alpha *gf9 alpha) *gf9 (alpha *gf9 alpha) ≡ gf9-one
alpha-powers-4 = refl

galoisFixedPoint : ∀ x → galoisConjugate x ≡ x → Σ GF3 (λ a → x ≡ (a , T₀))
galoisFixedPoint (a , T₀) eq = a , refl
galoisFixedPoint (a , T₁) eq = ⊥-elim (T₂≢T₁ (cong proj₂ eq))
  where T₂≢T₁ : T₂ ≡ T₁ → ⊥
        T₂≢T₁ ()
galoisFixedPoint (a , T₂) eq = ⊥-elim (T₁≢T₂ (cong proj₂ eq))
  where T₁≢T₂ : T₁ ≡ T₂ → ⊥
        T₁≢T₂ ()

--------------------------------------------------------------------------------
-- 6. 共轭对——天然的 C₂ 商结构
--------------------------------------------------------------------------------

ConjugatePair : GF9 → Set
ConjugatePair x = Σ GF9 (λ y → (y ≡ x) ⊎ (y ≡ galoisConjugate x))

conjugatePair-size-1 : ∀ (a : GF3) → galoisConjugate (embed-gf3 a) ≡ embed-gf3 a
conjugatePair-size-1 a = refl

conjugatePair-size-2 : galoisConjugate alpha ≡ alpha → ⊥
conjugatePair-size-2 ()

--------------------------------------------------------------------------------
-- 7. Frobenius 乘法同态 + 共轭原生性
-- 代数证明: 利用 GF(3) 特征 3 的 Freshman's Dream
-- σ(x·y) = (x·y)³ = x³·y³ = σ(x)·σ(y)
-- 归约到 Trit 层 negate 的 3 个 9-case 引理, 替代 81 case 穷举
--------------------------------------------------------------------------------

-- σ(α) = -α = (T₀, T₂)
sigma-alpha : galoisConjugate alpha ≡ (T₀ , T₂)
sigma-alpha = refl

-- Frobenius 乘法同态: σ(x·y) ≡ σ(x)·σ(y)
-- 代数证明: 在特征 3 域中 (ab)³ = a³b³
-- 归约到 Trit 层 negate 的分配律 + 线性
lemma-frobenius-multiplicative : ∀ (x y : GF9) →
  galoisConjugate (x *gf9 y) ≡ (galoisConjugate x) *gf9 (galoisConjugate y)
lemma-frobenius-multiplicative (a , b) (c , d) =
  cong₂ _,_ eq-real eq-imag
  where
    -- 实部: a⊗c ⊕ negate(b⊗d) ≡ a⊗c ⊕ negate(negate(b)⊗negate(d))
    eq-real : (a ⊗ c) ⊕ negate (b ⊗ d) ≡ (a ⊗ c) ⊕ negate ((negate b) ⊗ (negate d))
    eq-real = cong (λ x → (a ⊗ c) ⊕ x) (sym (cong negate (negate-⊗-negate b d)))
    
    -- 虚部: negate(a⊗d ⊕ b⊗c) ≡ a⊗negate(d) ⊕ negate(b)⊗c
    eq-imag : negate ((a ⊗ d) ⊕ (b ⊗ c)) ≡ (a ⊗ (negate d)) ⊕ ((negate b) ⊗ c)
    eq-imag = trans
      (negate-⊕ (a ⊗ d) (b ⊗ c))
      (cong₂ _⊕_ (trans (negate-⊗ a d) (negate-⊗-comm a d)) (negate-⊗ b c))

-- 共轭原生性: σ(x·α) ≡ σ(x)·σ(α)
-- 直接由 Frobenius 乘法同态推导 (取 y = α)
lemma-eigen-conjugate : ∀ (x : GF9) →
  galoisConjugate (x *gf9 alpha) ≡ (galoisConjugate x) *gf9 galoisConjugate alpha
lemma-eigen-conjugate x = lemma-frobenius-multiplicative x alpha

--------------------------------------------------------------------------------
-- 8. GF(9)* 乘法群 — 8 个非零元素的有限循环群
--------------------------------------------------------------------------------

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)

-- GF(9)* 的 8 个非零元素 (与 GF9 = GF3 × GF3 的非零元素一一对应)
data GF9Star : Set where
  s1    : GF9Star  -- 1    = (T₁, T₀)
  s2    : GF9Star  -- 2    = (T₂, T₀)
  sα    : GF9Star  -- α    = (T₀, T₁)
  s2α   : GF9Star  -- 2α   = (T₀, T₂)
  s1α   : GF9Star  -- 1+α  = (T₁, T₁)
  s12α  : GF9Star  -- 1+2α = (T₁, T₂)
  s21α  : GF9Star  -- 2+α  = (T₂, T₁)
  s22α  : GF9Star  -- 2+2α = (T₂, T₂)

-- 嵌入 GF9Star → GF9
toGF9 : GF9Star → GF9
toGF9 s1   = T₁ , T₀
toGF9 s2   = T₂ , T₀
toGF9 sα   = T₀ , T₁
toGF9 s2α  = T₀ , T₂
toGF9 s1α  = T₁ , T₁
toGF9 s12α = T₁ , T₂
toGF9 s21α = T₂ , T₁
toGF9 s22α = T₂ , T₂

-- 从 GF9 解码 (非零元素 → GF9Star, 零元素 → s1 任意)
fromGF9 : GF9 → GF9Star
fromGF9 (T₀ , T₀) = s1
fromGF9 (T₁ , T₀) = s1
fromGF9 (T₂ , T₀) = s2
fromGF9 (T₀ , T₁) = sα
fromGF9 (T₀ , T₂) = s2α
fromGF9 (T₁ , T₁) = s1α
fromGF9 (T₁ , T₂) = s12α
fromGF9 (T₂ , T₁) = s21α
fromGF9 (T₂ , T₂) = s22α

-- fromGF9 ∘ toGF9 = id (8 case refl)
fromGF9-toGF9 : ∀ x → fromGF9 (toGF9 x) ≡ x
fromGF9-toGF9 s1 = refl
fromGF9-toGF9 s2 = refl
fromGF9-toGF9 sα = refl
fromGF9-toGF9 s2α = refl
fromGF9-toGF9 s1α = refl
fromGF9-toGF9 s12α = refl
fromGF9-toGF9 s21α = refl
fromGF9-toGF9 s22α = refl

-- toGF9 单射 (由 fromGF9-toGF9 推导)
toGF9-inj : ∀ {x y} → toGF9 x ≡ toGF9 y → x ≡ y
toGF9-inj {x} {y} eq = trans (sym (fromGF9-toGF9 x)) (trans (cong fromGF9 eq) (fromGF9-toGF9 y))

-- GF(9)* 乘法表 (8×8 = 64 case 穷举)
-- 由 (a+bα)(c+dα) = (ac-bd) + (ad+bc)α, α²=2=-1 推导
-- s1 行用 catch-all (单位元), 其余 7×8=56 case 显式穷举
_*s_ : GF9Star → GF9Star → GF9Star
s1 *s y = y    -- 单位元行
-- s2 行
s2 *s s1 = s2;    s2 *s s2 = s1;    s2 *s sα = s2α;   s2 *s s2α = sα
s2 *s s1α = s22α; s2 *s s12α = s21α; s2 *s s21α = s12α; s2 *s s22α = s1α
-- sα 行
sα *s s1 = sα;    sα *s s2 = s2α;   sα *s sα = s2;    sα *s s2α = s1
sα *s s1α = s21α; sα *s s12α = s1α;  sα *s s21α = s22α; sα *s s22α = s12α
-- s2α 行
s2α *s s1 = s2α;   s2α *s s2 = sα;    s2α *s sα = s1;    s2α *s s2α = s2
s2α *s s1α = s12α; s2α *s s12α = s22α; s2α *s s21α = s1α; s2α *s s22α = s21α
-- s1α 行
s1α *s s1 = s1α;   s1α *s s2 = s22α;  s1α *s sα = s21α;  s1α *s s2α = s12α
s1α *s s1α = s2α;  s1α *s s12α = s2;   s1α *s s21α = s1;   s1α *s s22α = sα
-- s12α 行
s12α *s s1 = s12α; s12α *s s2 = s21α; s12α *s sα = s1α;   s12α *s s2α = s22α
s12α *s s1α = s2;   s12α *s s12α = sα;   s12α *s s21α = s2α; s12α *s s22α = s1
-- s21α 行
s21α *s s1 = s21α; s21α *s s2 = s12α; s21α *s sα = s22α;  s21α *s s2α = s1α
s21α *s s1α = s1;   s21α *s s12α = s2α;  s21α *s s21α = sα;  s21α *s s22α = s2
-- s22α 行
s22α *s s1 = s22α; s22α *s s2 = s1α;   s22α *s sα = s12α;  s22α *s s2α = s21α
s22α *s s1α = sα;   s22α *s s12α = s1;   s22α *s s21α = s2;  s22α *s s22α = s2α

-- 乘法表与 GF9 域乘法的一致性 (64 case)
-- s1 行由 *gf9-identityˡ 推导, 其余 56 case 为 refl
*s-toGF9 : ∀ x y → toGF9 (x *s y) ≡ toGF9 x *gf9 toGF9 y
*s-toGF9 s1 y = sym (*gf9-identityˡ (toGF9 y))
*s-toGF9 s2 s1 = refl;    *s-toGF9 s2 s2 = refl;    *s-toGF9 s2 sα = refl;    *s-toGF9 s2 s2α = refl
*s-toGF9 s2 s1α = refl;   *s-toGF9 s2 s12α = refl;  *s-toGF9 s2 s21α = refl;  *s-toGF9 s2 s22α = refl
*s-toGF9 sα s1 = refl;    *s-toGF9 sα s2 = refl;    *s-toGF9 sα sα = refl;    *s-toGF9 sα s2α = refl
*s-toGF9 sα s1α = refl;   *s-toGF9 sα s12α = refl;  *s-toGF9 sα s21α = refl;  *s-toGF9 sα s22α = refl
*s-toGF9 s2α s1 = refl;   *s-toGF9 s2α s2 = refl;   *s-toGF9 s2α sα = refl;   *s-toGF9 s2α s2α = refl
*s-toGF9 s2α s1α = refl;  *s-toGF9 s2α s12α = refl; *s-toGF9 s2α s21α = refl; *s-toGF9 s2α s22α = refl
*s-toGF9 s1α s1 = refl;   *s-toGF9 s1α s2 = refl;   *s-toGF9 s1α sα = refl;   *s-toGF9 s1α s2α = refl
*s-toGF9 s1α s1α = refl;  *s-toGF9 s1α s12α = refl; *s-toGF9 s1α s21α = refl; *s-toGF9 s1α s22α = refl
*s-toGF9 s12α s1 = refl;  *s-toGF9 s12α s2 = refl;  *s-toGF9 s12α sα = refl;  *s-toGF9 s12α s2α = refl
*s-toGF9 s12α s1α = refl; *s-toGF9 s12α s12α = refl; *s-toGF9 s12α s21α = refl; *s-toGF9 s12α s22α = refl
*s-toGF9 s21α s1 = refl;  *s-toGF9 s21α s2 = refl;  *s-toGF9 s21α sα = refl;  *s-toGF9 s21α s2α = refl
*s-toGF9 s21α s1α = refl; *s-toGF9 s21α s12α = refl; *s-toGF9 s21α s21α = refl; *s-toGF9 s21α s22α = refl
*s-toGF9 s22α s1 = refl;  *s-toGF9 s22α s2 = refl;  *s-toGF9 s22α sα = refl;  *s-toGF9 s22α s2α = refl
*s-toGF9 s22α s1α = refl; *s-toGF9 s22α s12α = refl; *s-toGF9 s22α s21α = refl; *s-toGF9 s22α s22α = refl

-- 乘法单位元
*s-identityˡ : ∀ x → s1 *s x ≡ x
*s-identityˡ x = refl

*s-identityʳ : ∀ x → x *s s1 ≡ x
*s-identityʳ s1 = refl;   *s-identityʳ s2 = refl
*s-identityʳ sα = refl;   *s-identityʳ s2α = refl
*s-identityʳ s1α = refl;  *s-identityʳ s12α = refl
*s-identityʳ s21α = refl; *s-identityʳ s22α = refl

-- 乘法交换律 (64 case refl)
*s-comm : ∀ x y → x *s y ≡ y *s x
*s-comm s1 s1 = refl;   *s-comm s1 s2 = refl;   *s-comm s1 sα = refl;   *s-comm s1 s2α = refl
*s-comm s1 s1α = refl;  *s-comm s1 s12α = refl; *s-comm s1 s21α = refl; *s-comm s1 s22α = refl
*s-comm s2 s1 = refl;   *s-comm s2 s2 = refl;   *s-comm s2 sα = refl;   *s-comm s2 s2α = refl
*s-comm s2 s1α = refl;  *s-comm s2 s12α = refl; *s-comm s2 s21α = refl; *s-comm s2 s22α = refl
*s-comm sα s1 = refl;   *s-comm sα s2 = refl;   *s-comm sα sα = refl;   *s-comm sα s2α = refl
*s-comm sα s1α = refl;  *s-comm sα s12α = refl; *s-comm sα s21α = refl; *s-comm sα s22α = refl
*s-comm s2α s1 = refl;  *s-comm s2α s2 = refl;  *s-comm s2α sα = refl;  *s-comm s2α s2α = refl
*s-comm s2α s1α = refl; *s-comm s2α s12α = refl; *s-comm s2α s21α = refl; *s-comm s2α s22α = refl
*s-comm s1α s1 = refl;  *s-comm s1α s2 = refl;  *s-comm s1α sα = refl;  *s-comm s1α s2α = refl
*s-comm s1α s1α = refl; *s-comm s1α s12α = refl; *s-comm s1α s21α = refl; *s-comm s1α s22α = refl
*s-comm s12α s1 = refl; *s-comm s12α s2 = refl; *s-comm s12α sα = refl; *s-comm s12α s2α = refl
*s-comm s12α s1α = refl; *s-comm s12α s12α = refl; *s-comm s12α s21α = refl; *s-comm s12α s22α = refl
*s-comm s21α s1 = refl; *s-comm s21α s2 = refl; *s-comm s21α sα = refl; *s-comm s21α s2α = refl
*s-comm s21α s1α = refl; *s-comm s21α s12α = refl; *s-comm s21α s21α = refl; *s-comm s21α s22α = refl
*s-comm s22α s1 = refl; *s-comm s22α s2 = refl; *s-comm s22α sα = refl; *s-comm s22α s2α = refl
*s-comm s22α s1α = refl; *s-comm s22α s12α = refl; *s-comm s22α s21α = refl; *s-comm s22α s22α = refl

--------------------------------------------------------------------------------
-- 9. 循环群结构 — GF(9)* ≅ Z/8Z, 生成元 1+α
--------------------------------------------------------------------------------

-- 幂次函数
_^s_ : GF9Star → ℕ → GF9Star
x ^s zero = s1
x ^s (suc n) = x *s (x ^s n)

-- 生成元: 1+α (primitive element)
gen : GF9Star
gen = s1α

-- 幂次表 (全部 refl — Agda 计算归约)
-- (1+α)⁰ = 1
gen-pow-0 : gen ^s 0 ≡ s1
gen-pow-0 = refl

-- (1+α)¹ = 1+α
gen-pow-1 : gen ^s 1 ≡ s1α
gen-pow-1 = refl

-- (1+α)² = 2α
gen-pow-2 : gen ^s 2 ≡ s2α
gen-pow-2 = refl

-- (1+α)³ = 1+2α
gen-pow-3 : gen ^s 3 ≡ s12α
gen-pow-3 = refl

-- (1+α)⁴ = 2
gen-pow-4 : gen ^s 4 ≡ s2
gen-pow-4 = refl

-- (1+α)⁵ = 2+2α
gen-pow-5 : gen ^s 5 ≡ s22α
gen-pow-5 = refl

-- (1+α)⁶ = α
gen-pow-6 : gen ^s 6 ≡ sα
gen-pow-6 = refl

-- (1+α)⁷ = 2+α
gen-pow-7 : gen ^s 7 ≡ s21α
gen-pow-7 = refl

-- (1+α)⁸ = 1 (回到单位元 — 阶为 8)
gen-pow-8 : gen ^s 8 ≡ s1
gen-pow-8 = refl

-- 生成元遍历所有 8 个元素 (穷举验证)
gen-generates-all : ∀ x → Σ ℕ (λ n → gen ^s n ≡ x)
gen-generates-all s1   = 0 , refl
gen-generates-all s2   = 4 , refl
gen-generates-all sα   = 6 , refl
gen-generates-all s2α  = 2 , refl
gen-generates-all s1α  = 1 , refl
gen-generates-all s12α = 3 , refl
gen-generates-all s21α = 7 , refl
gen-generates-all s22α = 5 , refl

--------------------------------------------------------------------------------
-- 10. 乘法逆元
--------------------------------------------------------------------------------

inv : GF9Star → GF9Star
inv s1   = s1     -- 1⁻¹ = 1
inv s2   = s2     -- 2⁻¹ = 2 (2×2=4≡1)
inv sα   = s2α    -- α⁻¹ = 2α (α×2α=2α²=2×2=4≡1)
inv s2α  = sα     -- (2α)⁻¹ = α
inv s1α  = s21α   -- (1+α)⁻¹ = 2+α
inv s12α = s22α   -- (1+2α)⁻¹ = 2+2α
inv s21α = s1α    -- (2+α)⁻¹ = 1+α
inv s22α = s12α   -- (2+2α)⁻¹ = 1+2α

-- 逆元正确性 (8 case refl)
inv-correct : ∀ x → x *s inv x ≡ s1
inv-correct s1   = refl  -- s1 *s s1 = s1
inv-correct s2   = refl  -- s2 *s s2 = s1
inv-correct sα   = refl  -- sα *s s2α = s1
inv-correct s2α  = refl  -- s2α *s sα = s1
inv-correct s1α  = refl  -- s1α *s s21α = s1
inv-correct s12α = refl  -- s12α *s s22α = s1
inv-correct s21α = refl  -- s21α *s s1α = s1
inv-correct s22α = refl  -- s22α *s s12α = s1

-- 逆元对合: inv(inv(x)) = x
inv-involutive : ∀ x → inv (inv x) ≡ x
inv-involutive s1   = refl
inv-involutive s2   = refl
inv-involutive sα   = refl
inv-involutive s2α  = refl
inv-involutive s1α  = refl
inv-involutive s12α = refl
inv-involutive s21α = refl
inv-involutive s22α = refl

--------------------------------------------------------------------------------
-- 11. 子群结构
-- GF(9)* ≅ Z/8Z 的子群格:
--   {1} ⊂ {1,2} ⊂ {1,α,2,2α} ⊂ GF(9)*
--   阶:  1    2         4            8
--------------------------------------------------------------------------------

-- GF(3)* = {1, 2} — 2 阶子群 (≅ Z/2Z)
data GF3StarSub : Set where
  gf3s-1 : GF3StarSub
  gf3s-2 : GF3StarSub

gf3s-embed : GF3StarSub → GF9Star
gf3s-embed gf3s-1 = s1
gf3s-embed gf3s-2 = s2

gf3s-mul : GF3StarSub → GF3StarSub → GF3StarSub
gf3s-mul gf3s-1 gf3s-1 = gf3s-1  -- 1×1=1
gf3s-mul gf3s-1 gf3s-2 = gf3s-2  -- 1×2=2
gf3s-mul gf3s-2 gf3s-1 = gf3s-2  -- 2×1=2
gf3s-mul gf3s-2 gf3s-2 = gf3s-1  -- 2×2=1

gf3s-inv : GF3StarSub → GF3StarSub
gf3s-inv gf3s-1 = gf3s-1
gf3s-inv gf3s-2 = gf3s-2

gf3s-inv-correct : ∀ x → gf3s-mul x (gf3s-inv x) ≡ gf3s-1
gf3s-inv-correct gf3s-1 = refl
gf3s-inv-correct gf3s-2 = refl

gf3s-mul-compat : ∀ x y → gf3s-embed (gf3s-mul x y) ≡ gf3s-embed x *s gf3s-embed y
gf3s-mul-compat gf3s-1 gf3s-1 = refl
gf3s-mul-compat gf3s-1 gf3s-2 = refl
gf3s-mul-compat gf3s-2 gf3s-1 = refl
gf3s-mul-compat gf3s-2 gf3s-2 = refl

-- 4 阶子群 {1, α, 2, 2α} ≅ Z/4Z
-- 由 α 生成: α⁰=1, α¹=α, α²=2, α³=2α, α⁴=1
data Sub4 : Set where
  sub4-1  : Sub4
  sub4-α  : Sub4
  sub4-2  : Sub4
  sub4-2α : Sub4

sub4-embed : Sub4 → GF9Star
sub4-embed sub4-1  = s1
sub4-embed sub4-α  = sα
sub4-embed sub4-2  = s2
sub4-embed sub4-2α = s2α

sub4-mul : Sub4 → Sub4 → Sub4
sub4-mul sub4-1  sub4-1  = sub4-1;  sub4-mul sub4-1  sub4-α  = sub4-α
sub4-mul sub4-1  sub4-2  = sub4-2;  sub4-mul sub4-1  sub4-2α = sub4-2α
sub4-mul sub4-α  sub4-1  = sub4-α;  sub4-mul sub4-α  sub4-α  = sub4-2
sub4-mul sub4-α  sub4-2  = sub4-2α; sub4-mul sub4-α  sub4-2α = sub4-1
sub4-mul sub4-2  sub4-1  = sub4-2;  sub4-mul sub4-2  sub4-α  = sub4-2α
sub4-mul sub4-2  sub4-2  = sub4-1;  sub4-mul sub4-2  sub4-2α = sub4-α
sub4-mul sub4-2α sub4-1  = sub4-2α; sub4-mul sub4-2α sub4-α  = sub4-1
sub4-mul sub4-2α sub4-2  = sub4-α;  sub4-mul sub4-2α sub4-2α = sub4-2

sub4-inv : Sub4 → Sub4
sub4-inv sub4-1  = sub4-1
sub4-inv sub4-α  = sub4-2α  -- α×2α=1
sub4-inv sub4-2  = sub4-2   -- 2×2=1
sub4-inv sub4-2α = sub4-α   -- 2α×α=1

sub4-inv-correct : ∀ x → sub4-mul x (sub4-inv x) ≡ sub4-1
sub4-inv-correct sub4-1  = refl
sub4-inv-correct sub4-α  = refl
sub4-inv-correct sub4-2  = refl
sub4-inv-correct sub4-2α = refl

sub4-mul-compat : ∀ x y → sub4-embed (sub4-mul x y) ≡ sub4-embed x *s sub4-embed y
sub4-mul-compat sub4-1  sub4-1  = refl; sub4-mul-compat sub4-1  sub4-α  = refl
sub4-mul-compat sub4-1  sub4-2  = refl; sub4-mul-compat sub4-1  sub4-2α = refl
sub4-mul-compat sub4-α  sub4-1  = refl; sub4-mul-compat sub4-α  sub4-α  = refl
sub4-mul-compat sub4-α  sub4-2  = refl; sub4-mul-compat sub4-α  sub4-2α = refl
sub4-mul-compat sub4-2  sub4-1  = refl; sub4-mul-compat sub4-2  sub4-α  = refl
sub4-mul-compat sub4-2  sub4-2  = refl; sub4-mul-compat sub4-2  sub4-2α = refl
sub4-mul-compat sub4-2α sub4-1  = refl; sub4-mul-compat sub4-2α sub4-α  = refl
sub4-mul-compat sub4-2α sub4-2  = refl; sub4-mul-compat sub4-2α sub4-2α = refl

-- 子群嵌入保持单位元
gf3s-embed-unit : gf3s-embed gf3s-1 ≡ s1
gf3s-embed-unit = refl

sub4-embed-unit : sub4-embed sub4-1 ≡ s1
sub4-embed-unit = refl

--------------------------------------------------------------------------------
-- 12. GF(9) 乘法结合律 — 代数证明
-- (x*y)*z ≡ x*(y*z) 由 GF(3) 环公理推导
-- 策略: 展开为 GF(3) 的 ⊗/⊕, 使用 ⊗-assoc, ⊗-distrib, negate 分配律,
--       swap-middle 重排四项, 再收拢回 RHS
--------------------------------------------------------------------------------

open import Sovereign.Base.Trit using (⊗-assoc)

*gf9-assoc : ∀ x y z → (x *gf9 y) *gf9 z ≡ x *gf9 (y *gf9 z)
*gf9-assoc (a , b) (c , d) (e , f) = cong₂ _,_ real-eq imag-eq
  where
    -- 辅助: negate(x)⊗y ≡ negate(x⊗y)
    neg-mul-r : ∀ x y → (negate x) ⊗ y ≡ negate (x ⊗ y)
    neg-mul-r x y = sym (negate-⊗ x y)

    -- 辅助: x⊗negate(y) ≡ negate(x⊗y)
    mul-neg-r : ∀ x y → x ⊗ (negate y) ≡ negate (x ⊗ y)
    mul-neg-r x y = trans (sym (negate-⊗-comm x y)) (sym (negate-⊗ x y))

    -- 四项重排: (A⊕B)⊕(C⊕D) ≡ (A⊕C)⊕(D⊕B)
    rearrange4 : ∀ A B C D → (A ⊕ B) ⊕ (C ⊕ D) ≡ (A ⊕ C) ⊕ (D ⊕ B)
    rearrange4 A B C D =
      trans (swap-middle A B C D)
            (cong ((A ⊕ C) ⊕_) (⊕-comm B D))

    ------ 实部证明 ------
    -- LHS_real = ((a⊗c ⊕ neg(b⊗d))⊗e) ⊕ neg((a⊗d ⊕ b⊗c)⊗f)
    -- RHS_real = (a⊗(c⊗e ⊕ neg(d⊗f))) ⊕ neg(b⊗(c⊗f ⊕ d⊗e))
    -- 规范形  = (a⊗(c⊗e) ⊕ neg(a⊗(d⊗f))) ⊕ (neg(b⊗(c⊗f)) ⊕ neg(b⊗(d⊗e)))

    -- LHS → 展开分配
    r-step1 :
      (((a ⊗ c) ⊕ (negate (b ⊗ d))) ⊗ e) ⊕ (negate (((a ⊗ d) ⊕ (b ⊗ c)) ⊗ f))
      ≡
      (((a ⊗ c) ⊗ e) ⊕ ((negate (b ⊗ d)) ⊗ e))
      ⊕ (negate (((a ⊗ d) ⊗ f) ⊕ ((b ⊗ c) ⊗ f)))
    r-step1 = cong₂ _⊕_
      (⊗-distribʳ-⊕ (a ⊗ c) (negate (b ⊗ d)) e)
      (cong negate (⊗-distribʳ-⊕ (a ⊗ d) (b ⊗ c) f))

    -- 展开 → neg-mul-r + negate-⊕
    r-step2 :
      (((a ⊗ c) ⊗ e) ⊕ ((negate (b ⊗ d)) ⊗ e))
      ⊕ (negate (((a ⊗ d) ⊗ f) ⊕ ((b ⊗ c) ⊗ f)))
      ≡
      (((a ⊗ c) ⊗ e) ⊕ (negate ((b ⊗ d) ⊗ e)))
      ⊕ ((negate ((a ⊗ d) ⊗ f)) ⊕ (negate ((b ⊗ c) ⊗ f)))
    r-step2 = cong₂ _⊕_
      (cong₂ _⊕_ refl (neg-mul-r (b ⊗ d) e))
      (negate-⊕ ((a ⊗ d) ⊗ f) ((b ⊗ c) ⊗ f))

    -- ⊗-assoc 重结合
    r-step3 :
      (((a ⊗ c) ⊗ e) ⊕ (negate ((b ⊗ d) ⊗ e)))
      ⊕ ((negate ((a ⊗ d) ⊗ f)) ⊕ (negate ((b ⊗ c) ⊗ f)))
      ≡
      ((a ⊗ (c ⊗ e)) ⊕ (negate (b ⊗ (d ⊗ e))))
      ⊕ ((negate (a ⊗ (d ⊗ f))) ⊕ (negate (b ⊗ (c ⊗ f))))
    r-step3 = cong₂ _⊕_
      (cong₂ _⊕_ (⊗-assoc a c e) (cong negate (⊗-assoc b d e)))
      (cong₂ _⊕_ (cong negate (⊗-assoc a d f)) (cong negate (⊗-assoc b c f)))

    -- 四项重排
    r-step4 :
      ((a ⊗ (c ⊗ e)) ⊕ (negate (b ⊗ (d ⊗ e))))
      ⊕ ((negate (a ⊗ (d ⊗ f))) ⊕ (negate (b ⊗ (c ⊗ f))))
      ≡
      ((a ⊗ (c ⊗ e)) ⊕ (negate (a ⊗ (d ⊗ f))))
      ⊕ ((negate (b ⊗ (c ⊗ f))) ⊕ (negate (b ⊗ (d ⊗ e))))
    r-step4 = rearrange4
      (a ⊗ (c ⊗ e)) (negate (b ⊗ (d ⊗ e)))
      (negate (a ⊗ (d ⊗ f))) (negate (b ⊗ (c ⊗ f)))

    -- 收拢回 RHS
    r-step5 :
      ((a ⊗ (c ⊗ e)) ⊕ (negate (a ⊗ (d ⊗ f))))
      ⊕ ((negate (b ⊗ (c ⊗ f))) ⊕ (negate (b ⊗ (d ⊗ e))))
      ≡
      (a ⊗ ((c ⊗ e) ⊕ (negate (d ⊗ f))))
      ⊕ (negate (b ⊗ ((c ⊗ f) ⊕ (d ⊗ e))))
    r-step5 = cong₂ _⊕_
      (trans (cong₂ _⊕_ refl (sym (mul-neg-r a (d ⊗ f))))
             (sym (⊗-distribˡ-⊕ a (c ⊗ e) (negate (d ⊗ f)))))
      (trans (sym (negate-⊕ (b ⊗ (c ⊗ f)) (b ⊗ (d ⊗ e))))
             (cong negate (sym (⊗-distribˡ-⊕ b (c ⊗ f) (d ⊗ e)))))

    real-eq :
      (((a ⊗ c) ⊕ (negate (b ⊗ d))) ⊗ e) ⊕ (negate (((a ⊗ d) ⊕ (b ⊗ c)) ⊗ f))
      ≡
      (a ⊗ ((c ⊗ e) ⊕ (negate (d ⊗ f)))) ⊕ (negate (b ⊗ ((c ⊗ f) ⊕ (d ⊗ e))))
    real-eq = trans r-step1 (trans r-step2 (trans r-step3 (trans r-step4 r-step5)))

    ------ 虚部证明 ------
    -- LHS_imag = ((a⊗c ⊕ neg(b⊗d))⊗f) ⊕ ((a⊗d ⊕ b⊗c)⊗e)
    -- RHS_imag = (a⊗(c⊗f ⊕ d⊗e)) ⊕ (b⊗(c⊗e ⊕ neg(d⊗f)))

    -- LHS → 展开分配
    i-step1 :
      (((a ⊗ c) ⊕ (negate (b ⊗ d))) ⊗ f) ⊕ (((a ⊗ d) ⊕ (b ⊗ c)) ⊗ e)
      ≡
      (((a ⊗ c) ⊗ f) ⊕ ((negate (b ⊗ d)) ⊗ f))
      ⊕ (((a ⊗ d) ⊗ e) ⊕ ((b ⊗ c) ⊗ e))
    i-step1 = cong₂ _⊕_
      (⊗-distribʳ-⊕ (a ⊗ c) (negate (b ⊗ d)) f)
      (⊗-distribʳ-⊕ (a ⊗ d) (b ⊗ c) e)

    -- neg-mul-r + ⊗-assoc
    i-step2 :
      (((a ⊗ c) ⊗ f) ⊕ ((negate (b ⊗ d)) ⊗ f))
      ⊕ (((a ⊗ d) ⊗ e) ⊕ ((b ⊗ c) ⊗ e))
      ≡
      ((a ⊗ (c ⊗ f)) ⊕ (negate (b ⊗ (d ⊗ f))))
      ⊕ ((a ⊗ (d ⊗ e)) ⊕ (b ⊗ (c ⊗ e)))
    i-step2 = cong₂ _⊕_
      (cong₂ _⊕_ (⊗-assoc a c f)
                 (trans (neg-mul-r (b ⊗ d) f) (cong negate (⊗-assoc b d f))))
      (cong₂ _⊕_ (⊗-assoc a d e) (⊗-assoc b c e))

    -- 四项重排
    i-step3 :
      ((a ⊗ (c ⊗ f)) ⊕ (negate (b ⊗ (d ⊗ f))))
      ⊕ ((a ⊗ (d ⊗ e)) ⊕ (b ⊗ (c ⊗ e)))
      ≡
      ((a ⊗ (c ⊗ f)) ⊕ (a ⊗ (d ⊗ e)))
      ⊕ ((b ⊗ (c ⊗ e)) ⊕ (negate (b ⊗ (d ⊗ f))))
    i-step3 = rearrange4
      (a ⊗ (c ⊗ f)) (negate (b ⊗ (d ⊗ f)))
      (a ⊗ (d ⊗ e)) (b ⊗ (c ⊗ e))

    -- 收拢回 RHS
    i-step4 :
      ((a ⊗ (c ⊗ f)) ⊕ (a ⊗ (d ⊗ e)))
      ⊕ ((b ⊗ (c ⊗ e)) ⊕ (negate (b ⊗ (d ⊗ f))))
      ≡
      (a ⊗ ((c ⊗ f) ⊕ (d ⊗ e)))
      ⊕ (b ⊗ ((c ⊗ e) ⊕ (negate (d ⊗ f))))
    i-step4 = cong₂ _⊕_
      (sym (⊗-distribˡ-⊕ a (c ⊗ f) (d ⊗ e)))
      (trans (cong₂ _⊕_ refl (sym (mul-neg-r b (d ⊗ f))))
             (sym (⊗-distribˡ-⊕ b (c ⊗ e) (negate (d ⊗ f)))))

    imag-eq :
      (((a ⊗ c) ⊕ (negate (b ⊗ d))) ⊗ f) ⊕ (((a ⊗ d) ⊕ (b ⊗ c)) ⊗ e)
      ≡
      (a ⊗ ((c ⊗ f) ⊕ (d ⊗ e))) ⊕ (b ⊗ ((c ⊗ e) ⊕ (negate (d ⊗ f))))
    imag-eq = trans i-step1 (trans i-step2 (trans i-step3 i-step4))

--------------------------------------------------------------------------------
-- 13. GF9 本体乘法逆元 — 域结构的最后一环
-- 在 GF9 = GF3 × GF3 本体上构造逆元（第 10 节只在 GF9Star 上构造）
-- 零元素映射到自身（正确性定理限定 x ≢ 0，零 case 由假设矛盾排除）
--------------------------------------------------------------------------------

-- 非零判别: x ≢ y = x ≡ y → ⊥
_≢_ : GF9 → GF9 → Set
x ≢ y = x ≡ y → ⊥

gf9-zero : GF9
gf9-zero = T₀ , T₀

-- 逆元表 (与第 10 节 GF9Star 的 inv 一致: s1↔s1, s2↔s2, sα↔s2α, s1α↔s21α, s12α↔s22α)
gf9-inv : GF9 → GF9
gf9-inv (T₀ , T₀) = T₀ , T₀   -- 0 占位 (不被正确性定理覆盖)
gf9-inv (T₁ , T₀) = T₁ , T₀   -- 1⁻¹ = 1
gf9-inv (T₂ , T₀) = T₂ , T₀   -- 2⁻¹ = 2 (2×2=4≡1)
gf9-inv (T₀ , T₁) = T₀ , T₂   -- α⁻¹ = 2α (α×2α=2α²=2×2=4≡1)
gf9-inv (T₀ , T₂) = T₀ , T₁   -- (2α)⁻¹ = α
gf9-inv (T₁ , T₁) = T₂ , T₁   -- (1+α)⁻¹ = 2+α
gf9-inv (T₁ , T₂) = T₂ , T₂   -- (1+2α)⁻¹ = 2+2α
gf9-inv (T₂ , T₁) = T₁ , T₁   -- (2+α)⁻¹ = 1+α
gf9-inv (T₂ , T₂) = T₁ , T₂   -- (2+2α)⁻¹ = 1+2α

-- 逆元正确性: ∀ x → x ≢ 0 → x *gf9 gf9-inv x ≡ gf9-one (8 case refl)
gf9-inv-correct : ∀ x → x ≢ gf9-zero → x *gf9 gf9-inv x ≡ gf9-one
gf9-inv-correct (T₀ , T₀) neq = ⊥-elim (neq refl)
gf9-inv-correct (T₁ , T₀) neq = refl
gf9-inv-correct (T₂ , T₀) neq = refl
gf9-inv-correct (T₀ , T₁) neq = refl
gf9-inv-correct (T₀ , T₂) neq = refl
gf9-inv-correct (T₁ , T₁) neq = refl
gf9-inv-correct (T₁ , T₂) neq = refl
gf9-inv-correct (T₂ , T₁) neq = refl
gf9-inv-correct (T₂ , T₂) neq = refl

-- 右逆由交换律推出: ∀ x → x ≢ 0 → gf9-inv x *gf9 x ≡ gf9-one
gf9-inv-correctˡ : ∀ x → x ≢ gf9-zero → gf9-inv x *gf9 x ≡ gf9-one
gf9-inv-correctˡ x neq = trans (*gf9-comm (gf9-inv x) x) (gf9-inv-correct x neq)

-- 域公理形式 (存在性): ∀ x → x ≢ 0 → Σ y → x·y = 1
gf9-field-inverse : ∀ x → x ≢ gf9-zero → Σ GF9 (λ y → x *gf9 y ≡ gf9-one)
gf9-field-inverse x neq = gf9-inv x , gf9-inv-correct x neq

--------------------------------------------------------------------------------
-- 14. 不可否决核心: Frobenius 域同态 + x²+1 无根出生证明
--   σ(x)=x³ 在 char 3 上原生保持加法与乘法 — 不是外挂结构, 而是
--   有限域代数的刚性事实 (任何数学家/物理学家/大模型都无法否决的计算)。
--------------------------------------------------------------------------------

-- Frobenius 保持加法: σ(x+y) = σx + σy (符号证明)
galoisConjugate-add : ∀ x y →
  galoisConjugate (x +gf9 y) ≡ galoisConjugate x +gf9 galoisConjugate y
galoisConjugate-add (a , b) (c , d) = cong (λ t → (a ⊕ c) , t) (negate-⊕ b d)

-- Frobenius 保持乘法: σ(x·y) = σx · σy (符号证明, negate 引理驱动)
galoisConjugate-mul : ∀ x y →
  galoisConjugate (x *gf9 y) ≡ galoisConjugate x *gf9 galoisConjugate y
galoisConjugate-mul (a , b) (c , d) = cong₂ _,_
  (trans refl (cong (λ t → (a ⊗ c) ⊕ negate t) (sym (negate-⊗-negate b d))))
  (trans refl
    (trans (negate-⊕ (a ⊗ d) (b ⊗ c))
           (cong₂ _⊕_ (trans (negate-⊗ a d) (negate-⊗-comm a d)) (negate-⊗ b c))))

-- Frobenius 单射 (σ² = id 给出左逆)
galoisConjugate-injective : ∀ x y → galoisConjugate x ≡ galoisConjugate y → x ≡ y
galoisConjugate-injective x y e =
  trans (sym (galoisConjugate² x))
        (trans (cong galoisConjugate e) (galoisConjugate² y))

-- Frobenius 自同构 (三组件: 保加法 × 保乘法 × 单射 — |GF9|=9 有限, 单射即满射)
frobenius-automorphism :
  (∀ x y → galoisConjugate (x +gf9 y) ≡ galoisConjugate x +gf9 galoisConjugate y)
  × (∀ x y → galoisConjugate (x *gf9 y) ≡ galoisConjugate x *gf9 galoisConjugate y)
  × (∀ x y → galoisConjugate x ≡ galoisConjugate y → x ≡ y)
frobenius-automorphism = galoisConjugate-add , galoisConjugate-mul , galoisConjugate-injective

-- x²+1 在 GF(3) 上无根 (3 case): 0²+1=1, 1²+1=2, 2²+1=4≡2 皆非零
-- 二次多项式无根 ⟹ 不可约 ⟹ GF(3)[x]/(x²+1) 为域 — GF(9) 的出生证明
-- (域公理本身已在本体上构造性验证: ⊕/⊗ 律 + gf9-field-inverse)
x2p1-no-root : ∀ x → (x ⊗ x) ⊕ T₁ ≡ T₀ → ⊥
x2p1-no-root T₀ = λ ()
x2p1-no-root T₁ = λ ()
x2p1-no-root T₂ = λ ()

--------------------------------------------------------------------------------
-- 15. Frobenius 桥接恒等式 (四处叙事缺口的形式化闭合)
--   σ(x) ≡ x³;  N(x) ≡ x·σ(x);  Tr(x) ≡ x+σ(x);  N(x·y) ≡ N(x)·N(y)
--   全部 9-case 穷举 refl 或代数推导链, 0 postulate
--------------------------------------------------------------------------------

-- σ = 立方映射 (特征 3 Freshman's Dream: (a+bα)³ = a³+b³α³ = a-bα)
frobenius-cube : ∀ x → galoisConjugate x ≡ (x *gf9 x) *gf9 x
frobenius-cube (T₀ , T₀) = refl
frobenius-cube (T₀ , T₁) = refl
frobenius-cube (T₀ , T₂) = refl
frobenius-cube (T₁ , T₀) = refl
frobenius-cube (T₁ , T₁) = refl
frobenius-cube (T₁ , T₂) = refl
frobenius-cube (T₂ , T₀) = refl
frobenius-cube (T₂ , T₁) = refl
frobenius-cube (T₂ , T₂) = refl

-- 范数桥接: N(x) = x·σ(x) (共轭对坍缩为基座单值)
norm-conj-mul : ∀ x → embed-gf3 (galoisNorm x) ≡ x *gf9 galoisConjugate x
norm-conj-mul (T₀ , T₀) = refl
norm-conj-mul (T₀ , T₁) = refl
norm-conj-mul (T₀ , T₂) = refl
norm-conj-mul (T₁ , T₀) = refl
norm-conj-mul (T₁ , T₁) = refl
norm-conj-mul (T₁ , T₂) = refl
norm-conj-mul (T₂ , T₀) = refl
norm-conj-mul (T₂ , T₁) = refl
norm-conj-mul (T₂ , T₂) = refl

-- 迹桥接: Tr(x) = x+σ(x) (加性坍缩)
trace-conj-add : ∀ x → embed-gf3 (galoisTrace x) ≡ x +gf9 galoisConjugate x
trace-conj-add (T₀ , T₀) = refl
trace-conj-add (T₀ , T₁) = refl
trace-conj-add (T₀ , T₂) = refl
trace-conj-add (T₁ , T₀) = refl
trace-conj-add (T₁ , T₁) = refl
trace-conj-add (T₁ , T₂) = refl
trace-conj-add (T₂ , T₀) = refl
trace-conj-add (T₂ , T₁) = refl
trace-conj-add (T₂ , T₂) = refl

-- 嵌入保乘: embed(a⊗b) = embed(a)·embed(b)
embed-gf3-mul : ∀ a b → embed-gf3 (a ⊗ b) ≡ embed-gf3 a *gf9 embed-gf3 b
embed-gf3-mul T₀ T₀ = refl
embed-gf3-mul T₀ T₁ = refl
embed-gf3-mul T₀ T₂ = refl
embed-gf3-mul T₁ T₀ = refl
embed-gf3-mul T₁ T₁ = refl
embed-gf3-mul T₁ T₂ = refl
embed-gf3-mul T₂ T₀ = refl
embed-gf3-mul T₂ T₁ = refl
embed-gf3-mul T₂ T₂ = refl

-- 嵌入单射
embed-gf3-injective : ∀ {a b} → embed-gf3 a ≡ embed-gf3 b → a ≡ b
embed-gf3-injective e = cong proj₁ e

-- 中交换: (a·b)·(c·d) ≡ (a·c)·(b·d) (交换律重排)
mid-swap : ∀ a b c d → ((a *gf9 b) *gf9 (c *gf9 d)) ≡ ((a *gf9 c) *gf9 (b *gf9 d))
mid-swap a b c d = begin
  (a *gf9 b) *gf9 (c *gf9 d)
    ≡⟨ *gf9-assoc a b (c *gf9 d) ⟩
  a *gf9 (b *gf9 (c *gf9 d))
    ≡⟨ cong (λ t → a *gf9 t) (sym (*gf9-assoc b c d)) ⟩
  a *gf9 ((b *gf9 c) *gf9 d)
    ≡⟨ cong (λ t → a *gf9 (t *gf9 d)) (*gf9-comm b c) ⟩
  a *gf9 ((c *gf9 b) *gf9 d)
    ≡⟨ cong (λ t → a *gf9 t) (*gf9-assoc c b d) ⟩
  a *gf9 (c *gf9 (b *gf9 d))
    ≡⟨ sym (*gf9-assoc a c (b *gf9 d)) ⟩
  (a *gf9 c) *gf9 (b *gf9 d) ∎

-- 范数乘性: N(x·y) = N(x)·N(y)
-- 链: x·y·σ(x·y) = x·y·σx·σy = x·σx·y·σy = N(x)·N(y) (粘贴文本 #13 叙述闭合)
norm-mul : ∀ x y → galoisNorm (x *gf9 y) ≡ galoisNorm x ⊗ galoisNorm y
norm-mul x y = embed-gf3-injective (begin
  embed-gf3 (galoisNorm (x *gf9 y))
    ≡⟨ norm-conj-mul (x *gf9 y) ⟩
  (x *gf9 y) *gf9 galoisConjugate (x *gf9 y)
    ≡⟨ cong ((x *gf9 y) *gf9_) (lemma-frobenius-multiplicative x y) ⟩
  (x *gf9 y) *gf9 (galoisConjugate x *gf9 galoisConjugate y)
    ≡⟨ mid-swap x y (galoisConjugate x) (galoisConjugate y) ⟩
  (x *gf9 galoisConjugate x) *gf9 (y *gf9 galoisConjugate y)
    ≡⟨ cong₂ _*gf9_ (sym (norm-conj-mul x)) (sym (norm-conj-mul y)) ⟩
  embed-gf3 (galoisNorm x) *gf9 embed-gf3 (galoisNorm y)
    ≡⟨ sym (embed-gf3-mul (galoisNorm x) (galoisNorm y)) ⟩
  embed-gf3 (galoisNorm x ⊗ galoisNorm y) ∎)

-- 0 postulate.
