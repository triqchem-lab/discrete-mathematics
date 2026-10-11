{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Foundation.RelationClosures
-- 二元关系的复合/逆/三闭包与闭包最小性定理
--
-- 数学背景：给定关系 R，其自反/对称/传递闭包是包含 R 的最小同类关系
-- （Coq Relations 族 / stdlib Relation.Binary.Construct.Closure 对应）。
-- 「最小性」是本模块的核心定理面：任何包含 R 的同类关系 S 都包含闭包——
-- 即闭包算子的**泛性质**（universal property）。本模块以自含归纳 data 形
-- 定义三闭包（与库内 AHomotopy 同族风格），最小性定理为可证主件。
--
-- 核心原则：
-- 1. 闭包 = 关系入定义（归纳 data 承载——关系是定义的组成非外来公理）
-- 2. 最小性三定理 = 泛性质主件（逐案归纳收口，零新公理）
-- 3. Rel/Reflexive/Symmetric/Transitive 采用本模块显式参数形（免 stdlib
--    Level 多态复杂度；数学内容同 stdlib Relation.Binary.Core）
--
-- 包含：Rel · 三性质谓词 · _∘ᵣ_（复合）· inv（逆）· RC/SC/TC 三闭包 ·
--       RC-min/SC-min/TC-min 最小性 · 核对层

module Sovereign.Foundation.RelationClosures where

open import Data.Product using (Σ; _×_; _,_)

--------------------------------------------------------------------------------
-- ③ 基础件层
--------------------------------------------------------------------------------

-- 二元关系（显式 Set 形——本模块口径）
Rel : Set → Set₁
Rel A = A → A → Set

Reflexive : ∀ {A : Set} → Rel A → Set
Reflexive R = ∀ x → R x x

Symmetric : ∀ {A : Set} → Rel A → Set
Symmetric R = ∀ x y → R x y → R y x

Transitive : ∀ {A : Set} → Rel A → Set
Transitive R = ∀ x y z → R x y → R y z → R x z

-- 关系复合：(R ∘ᵣ S) x z = 存在中间点 y（R 走到 y，S 从 y 起）
_∘ᵣ_ : ∀ {A : Set} → Rel A → Rel A → Rel A
(R ∘ᵣ S) x z = Σ _ (λ y → R x y × S y z)

-- 关系逆（反向边）
inv : ∀ {A : Set} → Rel A → Rel A
inv R x y = R y x

-- 逆是对合（定义相等直收口）
inv-inv : ∀ {A : Set} (R : Rel A) x y → inv (inv R) x y → R x y
inv-inv R x y r = r

--------------------------------------------------------------------------------
-- ④ 主引理层：三闭包（关系入定义——归纳 data 承载）
--------------------------------------------------------------------------------

-- 自反闭包：R ∪ 相等
data RC {A : Set} (R : Rel A) : Rel A where
  reflC : ∀ x → RC R x x
  embC  : ∀ {x y} → R x y → RC R x y

-- 对称闭包：R ∪ R⁻¹ 的对称化
data SC {A : Set} (R : Rel A) : Rel A where
  embS : ∀ {x y} → R x y → SC R x y
  symS : ∀ {x y} → SC R x y → SC R y x

-- 传递闭包：R 的有限正长度路径（右线性归纳形）
data TC {A : Set} (R : Rel A) : Rel A where
  embT  : ∀ {x y} → R x y → TC R x y
  stepT : ∀ {x y z} → R x z → TC R z y → TC R x y

--------------------------------------------------------------------------------
-- ⑤ 组合层：最小性定理（闭包泛性质——核心主件）
--------------------------------------------------------------------------------

-- 自反闭包最小性：任何包含 R 的自反关系包含 RC R
RC-min : ∀ {A : Set} (R S : Rel A)
       → Reflexive S
       → (∀ x y → R x y → S x y)
       → ∀ x y → RC R x y → S x y
RC-min R S reflS emb x .x (reflC .x) = reflS x
RC-min R S reflS emb x y  (embC r)   = emb x y r

-- 对称闭包最小性：任何包含 R 的对称关系包含 SC R
SC-min : ∀ {A : Set} (R S : Rel A)
       → Symmetric S
       → (∀ x y → R x y → S x y)
       → ∀ x y → SC R x y → S x y
SC-min R S S-sym emb x y (embS r)   = emb x y r
SC-min R S S-sym emb x y (symS s)   = S-sym y x (SC-min R S S-sym emb y x s)

-- 传递闭包最小性：任何包含 R 的传递关系包含 TC R（右线性归纳两案）
TC-min : ∀ {A : Set} (R S : Rel A)
       → Transitive S
       → (∀ x y → R x y → S x y)
       → ∀ x y → TC R x y → S x y
TC-min R S transS emb x y (embT r)             = emb x y r
TC-min R S transS emb x y (stepT {z = z} r s)  =
  transS x z y (emb x z r) (TC-min R S transS emb z y s)

--------------------------------------------------------------------------------
-- ⑥ 核对层：两元素试验关系上的构造形核对
--------------------------------------------------------------------------------

-- 试验载体（两元素）
data Two : Set where
  a₀ a₁ : Two

-- 试验关系：单边 a₀ → a₁
data Edge : Rel Two where
  e₀₁ : Edge a₀ a₁

-- 构造形核对
check-rc : RC Edge a₀ a₀
check-rc = reflC a₀

check-sc : SC Edge a₁ a₀
check-sc = symS (embS e₀₁)

check-tc : TC Edge a₀ a₁
check-tc = embT e₀₁

-- 复合×逆核对：(Edge ∘ᵣ inv Edge) 在 a₀ 处闭合成环见证
check-comp : (Edge ∘ᵣ inv Edge) a₀ a₀
check-comp = a₁ , e₀₁ , e₀₁

-- 逆对合核对（数据形直收口）
check-inv : inv (inv Edge) a₀ a₁ → Edge a₀ a₁
check-inv = inv-inv Edge a₀ a₁
