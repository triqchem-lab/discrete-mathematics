{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Foundation.QuotientBasic
-- 等价关系/等价类/良定义性——商结构的轻量基座
--
-- 数学背景：商集 A/R 的元素是 R-等价类；函数/运算下降到商上当且仅当它
-- **尊重等价关系**（Respects——代表元无关性）。本模块给出商结构的
-- Setoid 面：等价关系 record（关系入定义——三律为字段）+ 等价类判别
-- （cls-char：类相等 ⟺ 代表元相关）+ 良定义性组合律（resp-id/resp-∘）。
-- 与 Cubical.HITs.SetQuotients 的对应（桥注记）：本模块的 cls = [ x ] 的
-- 截面形、Respects = elimProp 的前提形——_PPI5c 商型先例的轻量前置。
--
-- 核心原则：
-- 1. IsEquivalence = 关系入定义（三律字段——B3/UniversalAlgebra 口径）
-- 2. 商良定义性主件 cls-char（类判别）——IsEquivalence 下可证
-- 3. 0 postulate / 0 hole；桥注记不 import（层内自含——Cubical 桥见注）
--
-- 包含：Rel/三性质 · IsEquivalence record · cls（等价类）· Respects/resp-∘ ·
--       cls-char（类判别）· QuotientSet record · 核对层

module Sovereign.Foundation.QuotientBasic where

open import Data.Product using (_×_; _,_)

--------------------------------------------------------------------------------
-- ③ 基础件层
--------------------------------------------------------------------------------

Rel : Set → Set₁
Rel A = A → A → Set

Reflexive : ∀ {A : Set} → Rel A → Set
Reflexive R = ∀ x → R x x

Symmetric : ∀ {A : Set} → Rel A → Set
Symmetric R = ∀ x y → R x y → R y x

Transitive : ∀ {A : Set} → Rel A → Set
Transitive R = ∀ x y z → R x y → R y z → R x z

-- 等价关系（关系入定义：三律 = record 字段——结构公理合法形）
record IsEquivalence {A : Set} (R : Rel A) : Set where
  field
    reflE  : Reflexive R
    symE   : Symmetric R
    transE : Transitive R

--------------------------------------------------------------------------------
-- ④ 主引理层：等价类与良定义性
--------------------------------------------------------------------------------

-- x 的等价类（截面形——类 = R x 的纤维）
cls : ∀ {A : Set} (R : Rel A) (x : A) → A → Set
cls R x y = R x y

-- 良定义性（代表元无关性）：f 把 R-相关送到 S-相关
Respects : ∀ {A B : Set} (f : A → B) → Rel A → Rel B → Set
Respects f R S = ∀ {x y} → R x y → S (f x) (f y)

-- 良定义组合律：恒等良定义 + 复合保良定义
resp-id : ∀ {A : Set} (R : Rel A) → Respects (λ x → x) R R
resp-id R r = r

resp-∘ : ∀ {A B C : Set} {R : Rel A} {S : Rel B} {T : Rel C}
         {g : B → C} {f : A → B}
       → Respects g S T → Respects f R S → Respects (λ x → g (f x)) R T
resp-∘ rg rf r = rg (rf r)

--------------------------------------------------------------------------------
-- ⑤ 组合层：类判别主件（商良定义性核心）
--------------------------------------------------------------------------------

-- 类判别（等价关系下）：R x x′ ⟺ 两截面逐点等价
-- （「同一点的两个代表元给出同一类」的严格形）
cls-char : ∀ {A : Set} {R : Rel A}
         → IsEquivalence R
         → ∀ {x x′} → R x x′
         → ∀ y → (cls R x y → cls R x′ y) × (cls R x′ y → cls R x y)
cls-char {R = R} eqv {x} {x′} r y = fwd , bwd
  where
  open IsEquivalence eqv
  fwd : cls R x y → cls R x′ y
  fwd h = transE x′ x y (symE x x′ r) h
  bwd : cls R x′ y → cls R x y
  bwd h = transE x x′ y r h

-- 商集载体（关系入定义：关系 + 等价性证据打包）
record QuotientSet (A : Set) : Set₁ where
  field
    R    : Rel A
    isEqv : IsEquivalence R

--------------------------------------------------------------------------------
-- ⑥ 核对层
--------------------------------------------------------------------------------

-- 试验载体：两点 + 全关系（恒等化商——类 = 全集）
data Two : Set where
  a₀ a₁ : Two

data ⊤ : Set where
  tt : ⊤

Total : Rel Two
Total _ _ = ⊤

-- 全关系的等价性（三律全 tt 形）
total-eqv : IsEquivalence Total
total-eqv = record
  { reflE  = λ _ → tt
  ; symE   = λ _ _ _ → tt
  ; transE = λ _ _ _ _ _ → tt
  }

check-cls-char : ∀ y → (cls Total a₀ y → cls Total a₁ y) × (cls Total a₁ y → cls Total a₀ y)
w₀₁ : Total a₀ a₁
w₀₁ = tt

w₁₀ : Total a₁ a₀
w₁₀ = tt

check-cls-char = cls-char {A = Two} {R = Total} total-eqv {x = a₀} {x′ = a₁} w₀₁

check-resp : Respects (λ (x : Two) → x) Total Total
check-resp = λ r → r

-- 桥注记（不在本文件 import——层内自含纪律）：
-- Cubical.HITs.SetQuotients 对应：cls R x ≡ 「[ x ] 的成员形」；
-- Respects f R S ≡ elimProp 下降前提；QuotientSet ≡ (A / R) 的数据面。
-- 实例先例：_PPI5c 的 BMapQ/bmQ（基点映射商）与 π₁ᵈ 商型族。
