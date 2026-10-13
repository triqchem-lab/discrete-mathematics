{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Synthesis.McCordPi0
-- _PMc（P2.2 最小可证核心：McCord π₀ 影——连通性对应）
--
-- 数学背景：McCord 1966 主命题：有限 T₀ 空间 X 存在单纯复形 K(X) 与弱同伦等价
--   |K(X)| → X。其 **0 阶面**（π₀ 影）：X 拓扑连通 ⇔ 比较图 cmpGraph(P) 连通。
--   弱等价本体（所有 πₙ 同构）需几何实现 + 同伦群机件——roadmap（P2.2 主节点）。
--   邻域前片：McCordCore（0 层核：底部锥/最小元）；本件是一般 π₀ 对应。
--
-- 核心原则：
--   1. 构造性双向：桥① 路网全连通 ⇒ 连通（逆变路径引理沿路逆推）；
--      桥② 无路对 ⇒ 不连通见证（U := 路径分量，双 upset 构造）
--   2. Alexandroff 语义：开集 = upset；不连通 = 非平凡双 upset 分割
--   3. 复用优先：Graph/Path（AtkinQAnalysis）、FinitePoset/IsUpset（AlexandroffFinite）、
--      cmpGraph/cmpEdge（McCordCore）——零重证
--
-- 包含：Disconnected / Connected / path-snoc / path-anti / π₀-bridge₁ / π₀-bridge₂ /
--       connected-no-unreachable / two-chain / two-anti / check-two-chain / check-two-anti
module Sovereign.Synthesis.McCordPi0 where

open import Data.Nat using (ℕ)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ-syntax; _×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Sovereign.Synthesis.AlexandroffFinite using (FinitePoset; IsUpset)
open import Sovereign.Synthesis.AtkinQAnalysis using (Path; nil; cons)
open import Sovereign.Synthesis.McCordCore using (cmpEdge)

--------------------------------------------------------------------------------
-- §1 连通性（Alexandroff 语义：开集 = upset；分割双侧皆开）
--------------------------------------------------------------------------------

Disconnected : ∀ {n : ℕ} (P : FinitePoset n) → Set₁
Disconnected {n} P = Σ[ U ∈ (Fin n → Set) ]
    (Σ[ x ∈ Fin n ] U x)
  × (Σ[ y ∈ Fin n ] (U y → ⊥))
  × IsUpset P U
  × IsUpset P (λ z → U z → ⊥)

Connected : ∀ {n : ℕ} (P : FinitePoset n) → Set₁
Connected P = Disconnected P → ⊥

--------------------------------------------------------------------------------
-- §2 逆变路径引理：双 upset 分割沿路径逆推（构造性核心）
--------------------------------------------------------------------------------

-- 路径尾接一步：x → a → b 拼成 x → b
path-snoc : ∀ {n : ℕ} {E : Fin n → Fin n → Set} {x a b} → Path E x a → E a b → Path E x b
path-snoc (nil x) e = cons x _ _ e (nil _)
path-snoc (cons x y z e p) e' = cons x y _ e (path-snoc p e')

-- 逆变：沿 x → y 路径，¬U y 逆推 ¬U x（每步用「U 正变」的逆否或「¬U 上闭」）
--   nil   ：¬U y 就是 ¬U x（同点）
--   cons  ：边 x~y 两种序向——x⊑y 用 U 的 upset 逆否；y⊑x 直接用 ¬U 的 upset
path-anti : ∀ {n : ℕ} (P : FinitePoset n) (U : Fin n → Set)
  → IsUpset P U → IsUpset P (λ z → U z → ⊥)
  → ∀ {x y} → Path (cmpEdge P) x y → (U y → ⊥) → (U x → ⊥)
path-anti P U uU vU (nil x) ny = ny
path-anti P U uU vU (cons x y z e p) nz ux with e
... | inj₁ xy = path-anti P U uU vU p nz (uU x y ux xy)   -- x⊑y：U x →[upset]→ U y →[IH]→ ⊥
... | inj₂ yx = vU y x (path-anti P U uU vU p nz) yx ux   -- y⊑x：¬U y →[¬U upset]→ ¬U x

--------------------------------------------------------------------------------
-- §3 π₀ 桥（构造性双向）
--------------------------------------------------------------------------------

-- 桥①：比较图路网全连通 ⇒ X 连通
π₀-bridge₁ : ∀ {n : ℕ} (P : FinitePoset n)
  → (∀ x y → Path (cmpEdge P) x y) → Connected P
π₀-bridge₁ P paths (U , (x , ux) , (y , ny) , uU , vU) =
  path-anti P U uU vU (paths x y) ny ux

-- 桥②：存在无路对 ⇒ 不连通（见证 U := x 的路径分量，双 upset）
comp-upset : ∀ {n : ℕ} (P : FinitePoset n) (x : Fin n)
  → IsUpset P (λ w → Path (cmpEdge P) x w)
comp-upset P x a b pa ab = path-snoc pa (inj₁ ab)          -- a⊑b 单步接入

comp-not-upset : ∀ {n : ℕ} (P : FinitePoset n) (x : Fin n)
  → IsUpset P (λ w → Path (cmpEdge P) x w → ⊥)
comp-not-upset P x a b na ab pb = na (path-snoc pb (inj₂ ab))  -- 反向边 b~a（a⊑b 注入右支）

π₀-bridge₂ : ∀ {n : ℕ} (P : FinitePoset n) (x y : Fin n)
  → (Path (cmpEdge P) x y → ⊥) → Disconnected P
π₀-bridge₂ P x y np =
  (λ w → Path (cmpEdge P) x w) , (x , nil x) , (y , np) , comp-upset P x , comp-not-upset P x

-- 推论（连通 ⇒ 无不可达对，构造性 ¬¬ 形）
connected-no-unreachable : ∀ {n : ℕ} (P : FinitePoset n)
  → Connected P → ∀ x y → (Path (cmpEdge P) x y → ⊥) → ⊥
connected-no-unreachable P conn x y np = conn (π₀-bridge₂ P x y np)

--------------------------------------------------------------------------------
-- §4 具体点交叉（2 点链连通 / 2 点反链不连通）
--------------------------------------------------------------------------------

-- 2 点链 fzero ⊑ fsuc fzero
data _⊑₂_ : Fin 2 → Fin 2 → Set where
  ⊑₂-00 : fzero ⊑₂ fzero
  ⊑₂-01 : fzero ⊑₂ fsuc fzero
  ⊑₂-11 : fsuc fzero ⊑₂ fsuc fzero

two-chain : FinitePoset 2
two-chain = record
  { _⊑_ = _⊑₂_
  ; ⊑-dec = dec2
  ; ⊑-refl = refl2
  ; ⊑-trans = trans2
  ; ⊑-antisym = anti2
  }
  where
    dec2 : ∀ a b → Dec (a ⊑₂ b)
    dec2 fzero fzero = yes ⊑₂-00
    dec2 fzero (fsuc fzero) = yes ⊑₂-01
    dec2 (fsuc fzero) fzero = no λ ()
    dec2 (fsuc fzero) (fsuc fzero) = yes ⊑₂-11
    refl2 : ∀ a → a ⊑₂ a
    refl2 fzero = ⊑₂-00
    refl2 (fsuc fzero) = ⊑₂-11
    trans2 : ∀ a b c → a ⊑₂ b → b ⊑₂ c → a ⊑₂ c
    trans2 fzero fzero c h k = lem0c c k
      where
        lem0c : ∀ c → fzero ⊑₂ c → fzero ⊑₂ c
        lem0c fzero hk = hk
        lem0c (fsuc fzero) hk = hk
    trans2 fzero (fsuc fzero) (fsuc fzero) h k = ⊑₂-01
    trans2 (fsuc fzero) (fsuc fzero) (fsuc fzero) h k = ⊑₂-11
    anti2 : ∀ a b → a ⊑₂ b → b ⊑₂ a → a ≡ b
    anti2 fzero fzero h k = refl
    anti2 fzero (fsuc fzero) h ()
    anti2 (fsuc fzero) fzero () k
    anti2 (fsuc fzero) (fsuc fzero) h k = refl

-- 2 点反链：序 = 相等
two-anti : FinitePoset 2
two-anti = record
  { _⊑_ = _≡_
  ; ⊑-dec = dec2
  ; ⊑-refl = λ a → refl
  ; ⊑-trans = λ a b c p q → trans p q
  ; ⊑-antisym = λ a b p q → p
  }
  where
    dec2 : ∀ a b → Dec (a ≡ b)
    dec2 fzero fzero = yes refl
    dec2 fzero (fsuc fzero) = no λ ()
    dec2 (fsuc fzero) fzero = no λ ()
    dec2 (fsuc fzero) (fsuc fzero) = yes refl

-- 交叉①：2 点链连通（路网四对全给）→ 桥①收口
check-two-chain : Connected two-chain
check-two-chain = π₀-bridge₁ two-chain paths2
  where
    paths2 : ∀ x y → Path (cmpEdge two-chain) x y
    paths2 fzero fzero = nil fzero
    paths2 fzero (fsuc fzero) = cons fzero (fsuc fzero) (fsuc fzero) (inj₁ ⊑₂-01) (nil (fsuc fzero))
    paths2 (fsuc fzero) fzero = cons (fsuc fzero) fzero fzero (inj₂ ⊑₂-01) (nil fzero)
    paths2 (fsuc fzero) (fsuc fzero) = nil (fsuc fzero)

-- 交叉②：2 点反链不连通（见证 U = {fzero}，双 upset 退化为等式搬运）→ 桥②可反向核
check-two-anti : Disconnected two-anti
check-two-anti = (λ w → w ≡ fzero) , (fzero , refl) , (fsuc fzero , λ ()) , u↑ , v↑
  where
    u↑ : IsUpset two-anti (λ w → w ≡ fzero)
    u↑ x y px xy = trans (sym xy) px
    v↑ : IsUpset two-anti (λ w → w ≡ fzero → ⊥)
    v↑ x y nx xy px = nx (trans xy px)
