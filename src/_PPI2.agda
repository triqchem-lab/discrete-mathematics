{-# OPTIONS --cubical --rewriting --guardedness #-}

-- | _PPI2（P2.2c (b2) 商型实化：π₁ᵈ = Loop / AHomotopy）
--
-- 数学背景：π₁ 离散形的**商型实化**——Loop G x 模 AHomotopy 等价的集合商
--   （Cubical.HITs.SetQuotients；A4/Stab 先例同款 rec + eq/ 形）。(b1) 的 ⊞-resp
--   合同性（_PPI ④节）为群结构良定义输入件——群运算三律实化列剩余。
--
-- 核心原则：
--   1. 复用优先：Loop/π₁-Spec（_PPI）、AHomotopy 三律（BarceloAHomotopy）零重证；
--   2. 分件理由：Cubical Path 与 stdlib PropEq 两 _≡_ 分世界（_PPI = PropEq 世界，
--      本件 = Cubical 世界）——避免同名等式混淆（附录 8 分件纪律）；
--   3. 不冒充群结构：商型 + rec + 三律承载在案；群运算/结合律 modulo ∼ 依赖
--      ⊞-resp 的商面提升（剩余清单 b2-群）。
module _PPI2 where

open import Data.Fin using () renaming (zero to fzero; suc to fsuc)
open import Cubical.Foundations.Prelude using (_≡_; refl; sym; _∙_; isSet)
open import Cubical.HITs.SetQuotients using (_/_; [_]; eq/; squash/)
open import Cubical.HITs.SetQuotients.Properties using (rec)
open import Sovereign.Topology.BarceloAHomotopy
  using (DiGraph; Walk; nil; AHomotopy; AH-refl; AH-symm; AH-trans)
open import _PPI using (Loop; π₁-Spec; G2; ℓ0)

--------------------------------------------------------------------------------
-- ① 商型实化：π₁ᵈ = Loop / AHomotopy
--------------------------------------------------------------------------------

-- 离散基本群（商型承载）：以 x 为基点的闭 walk 模 A-homotopy 等价
π₁ᵈ : (G : DiGraph) (x : DiGraph.V G) → Set
π₁ᵈ G x = Loop G x / AHomotopy G

-- 等价关系在商上成为路径（eq/ 投影——三律承载的入口）
[]-resp : ∀ {G x} {ℓ m : Loop G x} → AHomotopy G ℓ m → _≡_ {A = π₁ᵈ G x} [ ℓ ] [ m ]
[]-resp {ℓ = ℓ} {m} h = eq/ ℓ m h

-- rec（良定义消去——商型映射由代表元 + 合同性决定；A4/Stab 先例同形）
π₁ᵈ-rec : ∀ {G x} {B : Set} (setB : isSet B)
        → (f : Loop G x → B)
        → (∀ ℓ m → AHomotopy G ℓ m → f ℓ ≡ f m)
        → π₁ᵈ G x → B
π₁ᵈ-rec setB f resp = rec {A = Loop _ _} {R = AHomotopy _} setB f resp

--------------------------------------------------------------------------------
-- ② 三律承载：AHomotopy 三律在商上成为路径三律
--------------------------------------------------------------------------------

π₁ᵈ-refl : ∀ {G x} (ℓ : Loop G x) → _≡_ {A = π₁ᵈ G x} [ ℓ ] [ ℓ ]
π₁ᵈ-refl ℓ = refl

π₁ᵈ-sym : ∀ {G x} {ℓ m : Loop G x} → _≡_ {A = π₁ᵈ G x} [ ℓ ] [ m ] → _≡_ {A = π₁ᵈ G x} [ m ] [ ℓ ]
π₁ᵈ-sym = sym

π₁ᵈ-trans : ∀ {G x} {ℓ m n : Loop G x} → _≡_ {A = π₁ᵈ G x} [ ℓ ] [ m ] → _≡_ {A = π₁ᵈ G x} [ m ] [ n ] → _≡_ {A = π₁ᵈ G x} [ ℓ ] [ n ]
π₁ᵈ-trans p q = p ∙ q

--------------------------------------------------------------------------------
-- ③ G2 最小实例核对（两件）
--------------------------------------------------------------------------------

-- 双通道：eq/-导出（AH-refl 合同）vs 纯 refl
check-quot-ℓ0 : _≡_ {A = π₁ᵈ G2 fzero} [ ℓ0 ] [ ℓ0 ]
check-quot-ℓ0 = []-resp (AH-refl ℓ0)

check-quot-ℓ0' : _≡_ {A = π₁ᵈ G2 fzero} [ ℓ0 ] [ ℓ0 ]
check-quot-ℓ0' = π₁ᵈ-refl ℓ0

-- 剩余（b2-群）：商面上的群运算（concat 诱导 + ⊞-resp 良定义提升）+
--   单位/逆/结合 modulo ∼ ——依赖 _PPI ④节 ⊞-resp 的商面 elimProp/ 提升（~30 行，下批）。
