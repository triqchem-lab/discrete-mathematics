{-# OPTIONS --rewriting --guardedness #-}

-- | _PMc2（P2.2 McCord 弱等价本体——第 1-2 步：1-骨架桥 + K(X) 骨架层）
--
-- 数学背景：McCord 1966——有限 T₀ 空间 X 的序复形 K(X) 的几何实现 |K(X)| → X 是弱等价
--   （∀πₙ 同构 + π₀ 影）。本批交付前两步：① 1-骨架桥——K(X) 的 1-单形（有向 2-点链
--   IsChain2）与比较图 cmpGraph 的边（cmpEdge，无向含自环）的精确对应（x≢y 分离版）；
--   ② K(X) 骨架层组合数据（顶点/边/三角 + 面投影）+ 2 点链/反链两实例（与 McCordPi0
--   的 two-chain Connected / two-anti Disconnected 判定对账）。第 3 步精确立界见文末。
--
-- 核心原则：
--   1. 复用优先：Strict/IsChain2/IsChain3/IsChain/chain2-fn/桥件（OrderComplex）、
--      cmpEdge（McCordCore）、two-chain/two-anti/_⊑₂_（McCordPi0）零重证；
--   2. **两者不是同一谓词**：cmpEdge 含自环（⊑ 反身），IsChain2 不含（Strict 带 ≢）
--      ⇒ 桥必须带 x ≢ y 分离条件，等价只在相异点对上成立（自环处无对应单形）；
--   3. 骨架层只交组合数据（顶点/边/面谓词），不冒充几何实现（第 3 步立界）。
module Sovereign.Synthesis.Homotopy._PMc2 where

open import Data.Nat using (ℕ)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym)
open import Relation.Nullary using (¬_)
open import Sovereign.Synthesis.Topology.AlexandroffFinite using (FinitePoset)
open import Sovereign.Synthesis.Homotopy.McCordCore using (cmpEdge)
open import Sovereign.Synthesis.Topology.OrderComplex
  using (Strict; IsChain2; IsChain3; IsChain; chain2-fn; isChain2→general; general→chain2; strict→cmp)
open import Sovereign.Synthesis.Homotopy.McCordPi0 using (two-chain; two-anti; _⊑₂_; ⊑₂-01)

-- 双向蕴含 + 析取映射 + 等价复合（基础件层）
_↔_ : Set → Set → Set
A ↔ B = (A → B) × (B → A)

map⊎ : ∀ {A B C D : Set} → (A → C) → (B → D) → (A ⊎ B → C ⊎ D)
map⊎ f g (inj₁ a) = inj₁ (f a)
map⊎ f g (inj₂ b) = inj₂ (g b)

↔-trans : ∀ {A B C : Set} → A ↔ B → B ↔ C → A ↔ C
↔-trans (f , g) (h , k) = ((λ a → h (f a)) , (λ c → g (k c)))

--------------------------------------------------------------------------------
-- ① 1-骨架桥（cmpEdge ↔ IsChain2，x ≢ y 分离）
--------------------------------------------------------------------------------

-- 无向边对称（McCordCore flipcmp 的本地形）
cmp-sym : ∀ {n} (P : FinitePoset n) {x y : Fin n} → cmpEdge P x y → cmpEdge P y x
cmp-sym P (inj₁ h) = inj₂ h
cmp-sym P (inj₂ h) = inj₁ h

-- 反向桥：无向边 + 顶点相异 ⇒ 有向 2-点单形（两方向至少一成）
cmp→chain2 : ∀ {n} (P : FinitePoset n) {x y : Fin n} →
  cmpEdge P x y → ¬ (x ≡ y) → IsChain2 P x y ⊎ IsChain2 P y x
cmp→chain2 P (inj₁ h) x≢y = inj₁ (h , x≢y)
cmp→chain2 P (inj₂ h) x≢y = inj₂ (h , λ y≡x → x≢y (sym y≡x))

-- 1-骨架等价（相异点对上：比较图边 ⇔ 有序 2-点单形之析取）
skel-iff : ∀ {n} (P : FinitePoset n) {x y : Fin n} → ¬ (x ≡ y) →
  cmpEdge P x y ↔ (IsChain2 P x y ⊎ IsChain2 P y x)
skel-iff P x≢y =
  ( (λ e → cmp→chain2 P e x≢y)
  , λ { (inj₁ h) → strict→cmp P h
      ; (inj₂ h) → cmp-sym P (strict→cmp P h) } )

-- 一般 2-单形与 IsChain2 特例的等价（OrderComplex §9 两桥合体）
chain2-iff : ∀ {n} (P : FinitePoset n) (x y : Fin n) →
  IsChain P 2 (chain2-fn x y) ↔ IsChain2 P x y
chain2-iff P x y = ((λ h → general→chain2 P (chain2-fn x y) h) , (λ h → isChain2→general P h))

-- 1-骨架主定理（合成终形）：x≢y 处，K(X) 的一般 2-点链恰对应比较图的边
skel-main : ∀ {n} (P : FinitePoset n) {x y : Fin n} → ¬ (x ≡ y) →
  cmpEdge P x y ↔ (IsChain P 2 (chain2-fn x y) ⊎ IsChain P 2 (chain2-fn y x))
skel-main P {x} {y} x≢y = ↔-trans (skel-iff P x≢y)
  ( map⊎ (proj₂ (chain2-iff P x y)) (proj₂ (chain2-iff P y x))
  , map⊎ (proj₁ (chain2-iff P x y)) (proj₁ (chain2-iff P y x)) )

--------------------------------------------------------------------------------
-- ② K(X) 骨架层（组合数据——顶点/边/三角 + 面投影 + 两实例）
--------------------------------------------------------------------------------

KVert : ∀ {n} → Set
KVert {n} = Fin n

KEdge : ∀ {n} (P : FinitePoset n) → Fin n → Fin n → Set
KEdge P x y = IsChain2 P x y

KTri : ∀ {n} (P : FinitePoset n) → Fin n → Fin n → Fin n → Set
KTri P x y z = IsChain3 P x y z

-- 面单形性：三角的两条主面是边（subchain-closed 的 2 元投影特例）
tri-face-xy : ∀ {n} (P : FinitePoset n) {x y z : Fin n} → KTri P x y z → KEdge P x y
tri-face-xy P (hxy , _) = hxy
tri-face-yz : ∀ {n} (P : FinitePoset n) {x y z : Fin n} → KTri P x y z → KEdge P y z
tri-face-yz P (_ , hyz) = hyz

-- 2 点链（two-chain = McCordPi0 实例复用）：恰 1 条边（fzero ⊏ fsuc fzero）
chain2-KEdge : KEdge two-chain fzero (fsuc fzero)
chain2-KEdge = (⊑₂-01 , λ ())

-- 2 点反链（two-anti，⊑ = ≡）：零边——任何 Strict 直接矛盾（eq ∧ ≢）
an2-KEdge-absurd : ∀ (x y : Fin 2) → KEdge two-anti x y → ⊥
an2-KEdge-absurd x y (eq , neq) = neq eq

-- 对账（与 McCordPi0 判定一致——对抗配对）：
--   2 点链 1 边 ↔ Connected（two-chain proven）；2 点反链 0 边 ↔ Disconnected（two-anti proven）。

--------------------------------------------------------------------------------
-- ③ 第 3 步（几何实现 + πₙ 弱等价）精确立界
--
-- 剩余 = |K(X)| 的几何实现机件 + 弱等价（∀πₙ 同构）证明。精确分解：
--   (a) 几何实现骨架层：顶点/边/面的几何粘合（单纯复形实现：Δ² 嵌入等）
--       ——需拓扑空间机件（商拓扑/单纯形几何），本库 Topology 面仅有 Alexandroff 有限拓扑；
--   (b) πₙ 机件：同伦群定义 + π₀ 影（已由 P2.2a 交付）+ πₙ≥1 同构——需同伦群形式化
--       （本库现状：Homotopy 侧有 T6Homotopy/CRTFiberWinding 线，但 πₙ 定义层未建）；
--   (c) 弱等价组装：McCord 定理证明体——经典路线（形变收缩到骨架 + 单纯逼近），
--       每步都需 (a)+(b) 基建。估 (a)+(b) 各 1-2 批，(c) 另 1 批。
-- 现状判定：(a)(b) 均缺基建 ⇒ 本批止步于组合层（诚实分阶段）；组合层已与 π₀ 面
--   （P2.2a）与比较图语义完全对齐，无悬空。
--------------------------------------------------------------------------------
