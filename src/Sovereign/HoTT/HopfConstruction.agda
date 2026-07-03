{-# OPTIONS --cubical --guardedness #-}

-- | Sovereign.HoTT.HopfConstruction
-- Hopf 纤维化的离散化版本
--
-- 参考 HoTT-Agda HopfConstruction.agda：
-- 给定群 G 作用于空间 X，构造 X/G 上的纤维化：
--   纤维 = X（每个轨道上的点）
--   全空间 = X × G（g-等变对）
--   底空间 = X/G（商空间）
--
-- 应用到 T⁶/A₄：A₄ 群作用 → T6╱A4 上的纤维化

module Sovereign.HoTT.HopfConstruction where

open import Data.Fin using (Fin; toℕ; fromℕ)
open import Data.Vec using (Vec; []; _∷_)
open import Data.Nat using (ℕ)
open import Cubical.Foundations.Prelude
  using (_≡_; refl)
open import Cubical.Data.Sigma using (_×_; _,_; fst; snd)

-- 归纳相等（用于与 T6.agda 的 A4OrbitEquiv 交互）
open import Relation.Binary.PropositionalEquality
  renaming (_≡_ to _≡i_; refl to refli)
open import Cubical.HITs.SetQuotients using (_/_; [_]; eq/; squash/)
open import Cubical.HITs.SetQuotients.Properties
  using (rec; elimProp; quotSurjectionEquiv)
open import Cubical.Foundations.Equiv using (_≃_)
open import Cubical.Foundations.Isomorphism using (iso; isoToEquiv)
open import Cubical.Functions.Surjection using (isSurjection)
open import Cubical.HITs.PropositionalTruncation
  using (∥_∥₁; ∣_∣₁; squash₁)

import Sovereign.Structology.T6 as T6
import Sovereign.Structology.A4Group as A4

--------------------------------------------------------------------------------
-- 1. A₄-等变全空间
--------------------------------------------------------------------------------

-- 全空间 = T6Lattice × A4Element，等价关系由 A₄ 轨道等价性决定
-- 这是构造纤维化 T6Lattice → T6╱A4 的标准方法

-- 等变对：一个 T⁶ 格点 + 一个 A₄ 群的标记元素
TotalPair : Set
TotalPair = T6.T6Lattice × T6.A4Element

-- 等变关系：(x, g) ~ (y, h) 当且仅当 x 与 y 在同一 A₄ 轨道
-- 这直接复用了 T6 中已定义的 A4OrbitEquiv 关系，
-- 使得投影 [(x,g)] ↦ [x] 在商类型上良定义
EquivRel : TotalPair → TotalPair → Set
EquivRel (x , _) (y , _) = T6.A4OrbitEquiv x y

-- 全空间（等变对的商）
TotalSpace : Set
TotalSpace = TotalPair / EquivRel

--------------------------------------------------------------------------------
-- 2. 纤维化投影
--------------------------------------------------------------------------------

-- 投影：TotalSpace → T6╱A4
-- 使用 SetQuotients.Properties.rec 从商类型 TotalSpace 映射到 T6╱A4
-- f : (x , g) ↦ [ x ]     — 从代表元对计算底空间点
-- feq : (x,g) ~ (y,h)  →  [x] ≡ [y]   — EquivRel 就是 A4OrbitEquiv，使用 eq/
projection : TotalSpace → T6.T6╱A4
projection = rec squash/
  (λ a → [ fst a ])
  (λ a b r → eq/ (fst a) (fst b) r)

--------------------------------------------------------------------------------
-- 3. 纤维
--------------------------------------------------------------------------------

-- 点 [x] 在底空间中的纤维 = { (x, g) | g ∈ A4Element } / ~
-- 当取代表元 x 时，纤维同构于 A4Element（V₄ 的 4 个元素）

-- 基点纤维：T6╱A4 中代表元 [x₀] 处的纤维
Fiber : T6.T6╱A4 → Set
Fiber _ = T6.A4Element

--------------------------------------------------------------------------------
-- 4. 全空间与底空间的等价性（使用 quotSurjectionEquiv）
--------------------------------------------------------------------------------

-- 投影在代表元上的底映射
projOnRep : TotalPair → T6.T6╱A4
projOnRep a = [ fst a ]

-- a4Action 单位元性质：T6.a4Action a4-id 直接返回原向量。
--   证明：对 T6Lattice (Vec GF3 6) 做模式匹配，
--   a4Action a4-id (v₀∷...∷v₅∷[]) 定义为 v₀∷...∷v₅∷[] = x.
a4Action-id : ∀ (x : T6.T6Lattice) → T6.a4Action T6.a4-id x ≡i x
a4Action-id (v₀ ∷ v₁ ∷ v₂ ∷ v₃ ∷ v₄ ∷ v₅ ∷ []) = refli

-- projOnRep 是满射：对任意 [x] ∈ T6╱A4，取 (x, a4-id) 为原像
projOnRepSurj : isSurjection projOnRep
projOnRepSurj = elimProp (λ _ → squash₁) λ x →
  ∣ (x , T6.a4-id) , eq/ (fst (x , T6.a4-id)) x (T6.a4-id , a4Action-id x) ∣₁

-- quotSurjectionEquiv 的应用：
-- 令 ker a b = projOnRep a ≡ projOnRep b（投影的核关系），则
--   quotSurjectionEquiv squash/ projOnRep projOnRepSurj
--     : (TotalPair / ker) ≃ T6╱A4
-- 即核商等价于底空间。
--
-- 但 TotalSpace = TotalPair / EquivRel，其中 EquivRel 是 A4OrbitEquiv。
-- 由于 EquivRel (x,_) (y,_) = A4OrbitEquiv x y，且 ker (x,_) (y,_) = ([x] ≡ [y])，
-- 由商的性质有 EquivRel a b → ker a b（通过 eq/），因此得到自然映射
--   toKer : TotalSpace → (TotalPair / ker)
--
-- 要建立 TotalSpace ≃ TotalPair/ker 的反向映射，需要 effective（有效商），
-- 即 [x] ≡ [y] → A4OrbitEquiv x y。effective 要求 R 是命题值的且为等价关系。
-- A4OrbitEquiv 作为 Σ A4Element (λ g → a4Action g x ≡ y) 在存在不动点
-- 的格点上不是命题值的（不同群元素可能产生相同作用），因此不能直接使用
-- effective。我们改为构造直接的 TotalSpace ≃ T6╱A4 同构。

-- 截面：T6╱A4 → TotalSpace，将 [x] 嵌入为 [ (x, a4-id) ]
section' : T6.T6╱A4 → TotalSpace
section' = rec squash/
  (λ x → [ (x , T6.a4-id) ])
  (λ x y r → eq/ (x , T6.a4-id) (y , T6.a4-id) r)

-- 全空间与底空间的等价性证明
-- projection ∘ section' ≡ id 且 section' ∘ projection ≡ id
totalSpaceEquiv : TotalSpace ≃ T6.T6╱A4
totalSpaceEquiv = isoToEquiv (iso projection section' sec-proj proj-sec)
  where
  -- 截面后投影回到自身
  sec-proj : ∀ b → projection (section' b) ≡ b
  sec-proj = elimProp (λ b →
      squash/ {A = T6.T6Lattice} {R = T6.A4OrbitEquiv}
        (projection (section' b)) b)
    λ x → refl

  -- 投影后截面回到自身（在商中等价）
  proj-sec : ∀ a → section' (projection a) ≡ a
  proj-sec = elimProp (λ a →
      squash/ {A = TotalPair} {R = EquivRel}
        (section' (projection a)) a)
    λ { (x , g) →
    eq/ (x , T6.a4-id) (x , g) (T6.a4-id , a4Action-id x) }

-- 推论：quotSurjectionEquiv 路径也可建立同样的等价性。
-- 通过 quotSurjectionEquiv 得到 ker/ ≃ T6╱A4，再结合 TotalSpace → ker/
-- 以及利用 section' ∘ equivFun 构造 ker/ → TotalSpace，可得到等价性。
-- 两种构造等价，此处采用直接同构更简洁。

--------------------------------------------------------------------------------
-- 5. 纤维丛结构（设计分析）
--------------------------------------------------------------------------------

-- T⁶/A₄ 上的纤维丛：
--   A₄Element（纤维）→ TotalSpace → T6╱A4（底空间）
--
-- 类比 Hopf 纤维化：
--   S¹（纤维）→ S³（全空间）→ S²（底空间）
--
-- 我们的是：
--   A₄Element（4点 V₄ 纤维）→ TotalSpace → T6╱A4（底空间）

-- 设计说明：当前 TotalSpace ≃ T6╱A4（由 totalSpaceEquiv 证明），
-- 这意味着每个纤维退化成了单点，而非预期的 |A4Element| = 4 个点。
-- 这是因为 EquivRel 将 (x, g) 和 (y, h) 等同当 x 和 y 在同一 A₄ 轨道，
-- 而不管第二分量 g 和 h，这使得全空间坍缩为底空间。
--
-- 要得到真正的 A₄-纤维丛（纤维 = A₄Element），需定义：
--   TotalSpace = T6Lattice                        （全空间 729 点）
--   Base      = T6╱A4                              （底空间 ≈ 61 等价类）
--   投影        TotalSpace → Base, x ↦ [x]
--   纤维        Fiber [x] = { y | [y] ≡ [x] }     （A₄ 轨道，大小 ≈ 12）
--
-- 或将 TotalPair 的等价关系修改为：
--   (x, g) ~ (y, h) iff x ≡ y   （仅当格点严格相同时才等同对）
-- 这样 TotalSpace ≃ T6Lattice × A₄Element，纤维自然为 A₄Element。

-- 局部平凡化：Fiber 定义为常数函数 Fiber _ = T6.A4Element，
--   因此 Fiber [ x ] 直接规约为 T6.A4Element，平凡成立。
--   TODO: 重构 TotalSpace 后再给出有意义的局部平凡化证明。
localTriviality : ∀ (x : T6.T6Lattice) →
  Fiber [ x ] ≡ T6.A4Element
localTriviality x = refl
