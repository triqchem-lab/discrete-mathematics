{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Topology.OrderComplex
-- McCord 分解 M2：序复形 K(X) 的组合层（任务书 §2.2 M2）
--
-- 数学背景：McCord (1966) 对有限 T₀ 空间 X 构造序复形 K(X)——单形 = X 的
--   有限严格链。本模块在有限偏序集（AlexandroffFinite.FinitePoset）上给出
--   K(X) 的**组合层**：
--     ① 严格序 Strict = ⊑ ∧ ≢（链的原子步）；
--     ② 两两链 IsChain3 / IsChain2；
--     ③ 下降封闭核：三元链的三个二元子链仍是链（中间对 x ⊏ z 由 trans 跳接，
--        ≢ 由 antisym 传递矛盾）；
--     ④ 与比较图一致：Strict ⟹ cmpEdge（McCordCore 比较图 = 序复形 1-骨架）。
--     ⑤ 线性序 lin3 实例对抗：0 ⊏ 1 ⊏ 2 的三个子链全部闭合。
--
-- ⚠ 诚实边界（McCord 全量分解的当前状态，见台账 P2.2-M*）：
--   M1 空间↔偏序集：已由 AlexandroffFinite 闭合（回执 c80453e5…）；
--   M2 组合层：本模块，验证 = proof_compile exit 0（见回执）；
--   M3 几何实现 |K(X)|：BLOCKED（需拓扑/多面体机件，本库离散宪法下无）；
--   M4 映射 μ：BLOCKED（依赖 M3）；
--   M5 ∀n πₙ 同构：BLOCKED（依赖 M3/M4 + 一般同伦群）。
--   **全量定理未完成**——本模块闭合的是其组合前置件，不含任何完成宣称。
--
-- 【本地资产接线】矩阵化谱系：`Algebra/Jacobian/jac_Topology.agda` 的
--   FiniteComplex（顶点/边/面 + 入射数据）与 BoundaryMatrix（GF(3) 入射矩阵 +
--   rank/nullity 双侧证书）是序复形的**矩阵计算层**；本模块是**组合公理层**
--   （链的严格序 + 下降封闭）——两层互补：本层的链概念是 jac_Topology 入射
--   数据的组合语义；同调维数走 `Problem/Hodge/ChainComplex.dimH` 接口。
--
-- 0 postulate / 0 hole。
module Sovereign.Topology.OrderComplex where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat using (ℕ; zero; suc; _≤_; _<_; z≤n; s≤s)
open import Data.Nat.Properties
  using (≤-refl; ≤-trans; ≤-antisym; _≤?_; <⇒≢; <⇒≤)
open import Data.Fin using (Fin; toℕ) renaming (zero to fzero; suc to fsuc)
open import Data.Fin.Properties using (toℕ-injective)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; subst; cong; trans)
open import Sovereign.Topology.AlexandroffFinite using (FinitePoset)
open import Sovereign.Topology.McCordCore using (cmpEdge)

--------------------------------------------------------------------------------
-- §1. 严格序（链的原子步）：⊑ 且 ≠
--------------------------------------------------------------------------------

Strict : ∀ {n} (P : FinitePoset n) → Fin n → Fin n → Set
Strict P x y = (FinitePoset._⊑_ P x y) × (x ≢ y)

--------------------------------------------------------------------------------
-- §2. 两两链（序复形的单形：两两可比且同向严格）
--------------------------------------------------------------------------------

IsChain2 : ∀ {n} (P : FinitePoset n) → Fin n → Fin n → Set
IsChain2 P x y = Strict P x y

IsChain3 : ∀ {n} (P : FinitePoset n) → Fin n → Fin n → Fin n → Set
IsChain3 P x y z = Strict P x y × Strict P y z

--------------------------------------------------------------------------------
-- §3. 下降封闭核：三元链的三个二元子链仍是链
--
-- 序复形公理「单形的面仍是单形」在 3→2 层的构造性闭合：
--   (x ⊏ y ⊏ z) ⟹ (x ⊏ y) ∧ (x ⊏ z) ∧ (y ⊏ z)。
-- 中间对 x ⊏ z 由 ⊑-trans 跳接；x ≢ z 由 antisym 传递矛盾：
--   若 x ≡ z，则 y ⊑ z 变形为 y ⊑ x，antisym 给 x ≡ y，撞 x ≢ y。
--------------------------------------------------------------------------------

chain3-down : ∀ {n} (P : FinitePoset n) {x y z : Fin n} →
  IsChain3 P x y z →
  (Strict P x y) × (Strict P x z) × (Strict P y z)
chain3-down P {x} {y} {z} (hxy , hyz) =
  (hxy , (x⊑z , x≢z) , hyz)
  where
    x⊑z : FinitePoset._⊑_ P x z
    x⊑z = FinitePoset.⊑-trans P x y z (proj₁ hxy) (proj₁ hyz)

    x≢z : x ≢ z
    x≢z eq =
      proj₂ hxy
        (FinitePoset.⊑-antisym P x y
          (proj₁ hxy)
          (subst (λ w → FinitePoset._⊑_ P y w) (sym eq) (proj₁ hyz)))

--------------------------------------------------------------------------------
-- §4. 与比较图一致：Strict ⟹ cmpEdge（序复形 1-骨架 ⊆ 比较图）
--------------------------------------------------------------------------------

strict→cmp : ∀ {n} (P : FinitePoset n) {x y : Fin n} →
  Strict P x y → cmpEdge P x y
strict→cmp P (h⊑ , _) = inj₁ h⊑

--------------------------------------------------------------------------------
-- §5. 线性序实例 lin3（0 ⊏ 1 ⊏ 2）与具体点对抗
--------------------------------------------------------------------------------

lin3-⊑ : Fin 3 → Fin 3 → Set
lin3-⊑ a b = toℕ a ≤ toℕ b

lin3 : FinitePoset 3
lin3 = record
  { _⊑_       = lin3-⊑
  ; ⊑-dec     = λ a b → toℕ a ≤? toℕ b
  ; ⊑-refl    = λ a → ≤-refl
  ; ⊑-trans   = λ a b c h₁ h₂ → ≤-trans h₁ h₂
  ; ⊑-antisym = λ a b h₁ h₂ → toℕ-injective (≤-antisym h₁ h₂)
  }

-- 具体点对抗：0 ⊏ 1 ⊏ 2 的三元链
lin3-chain3 : IsChain3 lin3 fzero (fsuc fzero) (fsuc (fsuc fzero))
lin3-chain3 =
  ((z≤n , λ ()) , (s≤s z≤n , λ ()))

-- 下降封闭实例化：三个子链全闭合——中间对 (0 ⊏ 2) 含真实的 trans 跳接
lin3-down-instance :
  (Strict lin3 fzero (fsuc fzero)) ×
  (Strict lin3 fzero (fsuc (fsuc fzero))) ×
  (Strict lin3 (fsuc fzero) (fsuc (fsuc fzero)))
lin3-down-instance = chain3-down lin3 lin3-chain3

-- 一致性实例：链⟹比较图边（0 ⊏ 2 给出比较图的 (0,2) 边）
lin3-cmp-0-2 : cmpEdge lin3 fzero (fsuc (fsuc fzero))
lin3-cmp-0-2 = strict→cmp lin3 (proj₁ (proj₂ lin3-down-instance))

-- 既有资产衔接替代：lin3 的二元子链（0 ⊏ 1）独立闭合
lin3-chain2-01 : IsChain2 lin3 fzero (fsuc fzero)
lin3-chain2-01 = (z≤n , λ ())

--------------------------------------------------------------------------------
-- §6. P2.1 缺口闭合：序复形 1-骨架 ↔ 比较图（链-路径-边三方一致）
--
-- McCord K(X) 的 1-骨架意义：序复形的二元链（边）就是比较图的边；
-- 三元链给出比较图上的显式两跳路径。这把「组合层（本模块）」与
-- 「图连通层（AtkinQAnalysis.Path）」「0 层核（McCordCore）」焊成一体。
--------------------------------------------------------------------------------

open import Sovereign.Topology.AtkinQAnalysis using (Path; cons; nil)

-- 三元链 → 比较图上 x → z 的显式路径（经 y 两跳）
chain3-path : ∀ {n} (P : FinitePoset n) {x y z : Fin n} →
  IsChain3 P x y z → Path (cmpEdge P) x z
chain3-path P {x} {y} {z} (hxy , hyz) =
  cons x y z (inj₁ (proj₁ hxy))
       (cons y z z (inj₁ (proj₁ hyz)) (nil z))

-- 比较图边 + 两点不同 → 二元链（两方向之一）
edge-≠→chain : ∀ {n} (P : FinitePoset n) {x y : Fin n} →
  cmpEdge P x y → x ≢ y →
  IsChain2 P x y ⊎ IsChain2 P y x
edge-≠→chain P {x} {y} h ne with h
... | inj₁ x⊑y = inj₁ (x⊑y , ne)
... | inj₂ y⊑x = inj₂ (y⊑x , λ eq → ne (sym eq))

-- 具体点对抗：lin3 三元链 (0⊏1⊏2) 经 chain3-path 给出显式两跳路径
lin3-chain3-path : Path (cmpEdge lin3) fzero (fsuc (fsuc fzero))
lin3-chain3-path = chain3-path lin3 lin3-chain3

-- 对抗回证：边 + ≢ 给出二元链（(0,2) 方向）
lin3-edge-instance :
  cmpEdge lin3 fzero (fsuc (fsuc fzero)) →
  fzero ≢ fsuc (fsuc fzero) →
  IsChain2 lin3 fzero (fsuc (fsuc fzero)) ⊎
  IsChain2 lin3 (fsuc (fsuc fzero)) fzero
lin3-edge-instance h ne = edge-≠→chain lin3 h ne

--------------------------------------------------------------------------------
-- §7. 严格化：一般 k 两两链 + 子链封闭（序复形公理的一般形式）
--
-- 此前 IsChain2/IsChain3 是 2/3 特例；本节给出一般形式并证明
-- 序复形核心公理——「单形的面仍是单形」= 保序重标下的子链封闭。
--------------------------------------------------------------------------------

open import Data.Nat.Properties using (≤-trans; ≤-antisym) renaming (_<?_ to _≤?_)

-- 一般两两链：指标按 toℕ 比较的全序下逐对严格
IsChain : ∀ {n} (P : FinitePoset n) (k : ℕ) → (Fin k → Fin n) → Set
IsChain P k c = ∀ i j → toℕ i < toℕ j → Strict P (c i) (c j)

-- 严格序传递（从 chain3-down 的内联模式提取为一般引理）
strict-trans : ∀ {n} (P : FinitePoset n) {x y z : Fin n} →
  Strict P x y → Strict P y z → Strict P x z
strict-trans P {x} {y} {z} (h₁⊑ , h₁≢) (h₂⊑ , h₂≢) =
  (FinitePoset.⊑-trans P x y z h₁⊑ h₂⊑ , x≢z)
  where
    x≢z : x ≢ z
    x≢z eq =
      h₁≢ (FinitePoset.⊑-antisym P x y h₁⊑
        (subst (λ w → FinitePoset._⊑_ P y w) (sym eq) h₂⊑))

-- 子链封闭（序复形公理一般形式）：保序重标保持两两严格
subchain-closed : ∀ {n m} (P : FinitePoset n) (k : ℕ)
  (c : Fin k → Fin n) (r : Fin m → Fin k) →
  (∀ i j → toℕ i < toℕ j → toℕ (r i) < toℕ (r j)) →
  IsChain P k c → IsChain P m (λ i → c (r i))
subchain-closed P k c r r-mono ch i j h =
  ch (r i) (r j) (r-mono i j h)

--------------------------------------------------------------------------------
-- §8. lin3 一般链实例与子链对抗
--------------------------------------------------------------------------------

tri3 : Fin 3 → Fin 3
tri3 fzero = fzero
tri3 (fsuc fzero) = fsuc fzero
tri3 (fsuc (fsuc fzero)) = fsuc (fsuc fzero)

-- lin3 恒等链的三对两两严格（泛型证明：不逐 case 穷举）
n<0-elim : ∀ m → suc m ≤ zero → ⊥
n<0-elim m ()

s≤s-inv : ∀ {m n : ℕ} → suc m ≤ suc n → m ≤ n
s≤s-inv (s≤s p) = p

suc≤-elim : ∀ m → suc m ≤ m → ⊥
suc≤-elim zero ()
suc≤-elim (suc m) (s≤s p) = suc≤-elim m p

tri3-chain : IsChain lin3 3 (λ x → x)
tri3-chain i j h =
  (<⇒≤ h , λ eq → suc≤-elim (toℕ i)
    (subst (λ w → suc (toℕ i) ≤ w) (sym (cong toℕ eq)) h))

--------------------------------------------------------------------------------
-- §9. IsChain2/3 → 一般 IsChain 桥接（消除简化实现的最后缺口）
--
-- 「不得简化」要求的实质内容：证明 IsChain2/IsChain3 特例确实是
-- 一般 IsChain k 定义的实例。这桥接了早期模块（IsChain2/3 特例）
-- 与 §7 的泛型层（IsChain 一般 k）。
--------------------------------------------------------------------------------

-- Fin 2 → Fin n 的二元链函数
chain2-fn : ∀ {n : ℕ} → Fin n → Fin n → Fin 2 → Fin n
chain2-fn x y fzero = x
chain2-fn x y (fsuc fzero) = y

-- Fin 3 → Fin n 的三元链函数
chain3-fn : ∀ {n : ℕ} → Fin n → Fin n → Fin n → Fin 3 → Fin n
chain3-fn x y z fzero = x
chain3-fn x y z (fsuc fzero) = y
chain3-fn x y z (fsuc (fsuc fzero)) = z

-- IsChain2 是 IsChain 2 的实例
isChain2→general : ∀ {n} (P : FinitePoset n) {x y : Fin n} →
  IsChain2 P x y → IsChain P 2 (chain2-fn x y)
isChain2→general P {x} {y} h = go
  where
    go : ∀ (i j : Fin 2) → toℕ i < toℕ j →
      Strict P (chain2-fn x y i) (chain2-fn x y j)
    go fzero (fsuc fzero) _ = h
    go fzero fzero h₀ = ⊥-elim (n<0-elim zero h₀)
    go (fsuc fzero) fzero h' = ⊥-elim (n<0-elim _ h')
    go (fsuc fzero) (fsuc fzero) h'' = ⊥-elim (suc≤-elim 1 h'')

-- IsChain3 是 IsChain 3 的实例
isChain3→general : ∀ {n} (P : FinitePoset n) {x y z : Fin n} →
  IsChain3 P x y z → IsChain P 3 (chain3-fn x y z)
isChain3→general P {x} {y} {z} (hxy , hyz) = go
  where
    go : (i j : Fin 3) → toℕ i < toℕ j →
      Strict P (chain3-fn x y z i) (chain3-fn x y z j)
    go fzero (fsuc fzero) _ = hxy
    go fzero (fsuc (fsuc fzero)) _ = strict-trans P hxy hyz
    go (fsuc fzero) (fsuc (fsuc fzero)) _ = hyz
    go fzero fzero h₀ = ⊥-elim (n<0-elim zero h₀)
    go (fsuc fzero) fzero h = ⊥-elim (n<0-elim _ h)
    go (fsuc (fsuc fzero)) fzero h = ⊥-elim (n<0-elim _ h)
    go (fsuc (fsuc fzero)) (fsuc fzero) h =
      ⊥-elim (n<0-elim _ (s≤s-inv h))
    go (fsuc fzero) (fsuc fzero) h'' = ⊥-elim (suc≤-elim 1 h'')
    go (fsuc (fsuc fzero)) (fsuc (fsuc fzero)) h''' =
      ⊥-elim (n<0-elim zero (s≤s-inv (s≤s-inv h''')))

-- 泛型 → 二元子链（子链封闭的 2-元素特例）
general→chain2 : ∀ {n} (P : FinitePoset n) (c : Fin 2 → Fin n) →
  IsChain P 2 c → IsChain2 P (c fzero) (c (fsuc fzero))
general→chain2 P c h = h fzero (fsuc fzero) (s≤s z≤n)
