{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Synthesis.Homotopy.C5Rigidity
--
-- **C₅ 的 A-同伦正规形刚性**（标准 A-同伦生成集 → 绕数刚性完全量化）
--
-- 数学背景：
--   标准 A-同伦（Barceló–Kramer–Laubenbacher–Weaver 2001；Morrill arXiv:1904.12065
--   Prop 5.12：贴 3/4-循环 2-胞腔 + 全自环约定）在**走层**的生成元 = 三类：
--     · tri-slide   三角弦滑动（p·e1·e2·b → p·e3·b ✓ 弦 e3 : x→z ✓）
--     · sq-slide4   方形滑动（p·e1·e2·e3·b → p·e4·b ✓）
--     · bt          回溯消去（p·e·f·q → p·q ✓ 「带反转 A-homotopy」标准生成集 ✓）
--   （先例：_PPI2:229-233 修正案 ✓ / _PN3·_PN4 谱系 ✓）
--
-- 本模块证明（C₅ 实例）：
--   ① **强终止化**：三生成元严格减长 ⇒ 正规形存在 ✓
--   ② **单调**：bt-free（无相邻回溯对）⇒ 全边同向 ✓
--   ③ **纯绕行**：bt-free 闭走 ⇒ 方向计数全归一侧 ✓
--   ④ **ℤ 桥接**：bt-free 闭走 ⇒ wind = ±len ✓
--   ⇒ **C₅ 的 AStepStd 正规形 = 纯绕行，且 wind = ±len**（绕数刚性 ✓）
--
-- 核心原则：
--   1. 具体边构造子（10 条逐条命名 ✓）—— 避开 `next5 i` 索引反演 UnificationStuck ✗
--   2. 方向计数用 ℕ（nCw/nCcw ✓）—— 避开 ℤ 构造子算术重排坑 ✗
--   3. 空模式断不可及（`()` ✓）—— 构造子互斥直接判空 ✓
--
-- 0 postulate / 0 hole。来源探针：_PEH42/43/44/45（回执 4b85debc…/1f695dc5…/749833b9…/fc5aa45a… ✓）

module Sovereign.Synthesis.Homotopy.C5Rigidity where

open import Data.Nat using (ℕ; zero; suc; _+_; _<_; _≤_; s≤s; z≤n)
open import Data.Nat.Properties using (≤-refl; <-trans)
open import Data.Integer using (ℤ; +_; -_) renaming (_+_ to _+ℤ_)
open import Data.Integer.Properties using (neg-distrib-+)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (Σ; _,_; _×_; proj₁)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; trans; sym)
open import Sovereign.Synthesis.Homotopy.BarceloAHomotopy
  using (DiGraph; Walk; cons; nil; _++w_)

--------------------------------------------------------------------------------
-- ① 标准 A-同伦生成集（通用 ✓ 三生成元 ✓）
--------------------------------------------------------------------------------

data AStepStd (G : DiGraph) : ∀ {u v} → Walk G u v → Walk G u v → Set where
  tri-slide : ∀ {u x y z v} (p : Walk G u x) (b : Walk G z v)
    (e1 : DiGraph.edge G x y) (e2 : DiGraph.edge G y z) (e3 : DiGraph.edge G x z)
    → AStepStd G (p ++w (cons e1 (cons e2 b))) (p ++w (cons e3 b))
  sq-slide4 : ∀ {u x y z w v} (p : Walk G u x) (b : Walk G w v)
    (e1 : DiGraph.edge G x y) (e2 : DiGraph.edge G y z) (e3 : DiGraph.edge G z w)
    (e4 : DiGraph.edge G x w)
    → AStepStd G (p ++w (cons e1 (cons e2 (cons e3 b)))) (p ++w (cons e4 b))
  bt : ∀ {u x y v} (p : Walk G u x) (q : Walk G x v)
    (e : DiGraph.edge G x y) (f : DiGraph.edge G y x)
    → AStepStd G (p ++w (cons e (cons f q))) (p ++w q)

--------------------------------------------------------------------------------
-- ② C₅ 具体图（10 条具体边 ✓ 端点全构造子 ✓）
--------------------------------------------------------------------------------

data C5-vert : Set where
  c0 c1 c2 c3 c4 : C5-vert

data E5 : C5-vert → C5-vert → Set where
  cw01 : E5 c0 c1
  cw12 : E5 c1 c2
  cw23 : E5 c2 c3
  cw34 : E5 c3 c4
  cw40 : E5 c4 c0
  cc10 : E5 c1 c0
  cc21 : E5 c2 c1
  cc32 : E5 c3 c2
  cc43 : E5 c4 c3
  cc04 : E5 c0 c4

C5G : DiGraph
C5G = record { V = C5-vert ; edge = E5 }

--------------------------------------------------------------------------------
-- ③ 走长度与强终止化（T1a ✓）
--------------------------------------------------------------------------------

len : ∀ {u v : C5-vert} → Walk C5G u v → ℕ
len (nil x) = zero
len (cons e b) = suc (len b)

len-++ : ∀ {u v w : C5-vert} (p : Walk C5G u v) (q : Walk C5G v w)
  → len p + len q ≡ len (p ++w q)
len-++ (nil x) q = refl
len-++ (cons e b) q = cong suc (len-++ b q)

-- ℕ 辅助（自证归纳 ✓ 不猜 stdlib 名）
≤-suc-self : ∀ n → n ≤ suc n
≤-suc-self zero = z≤n
≤-suc-self (suc n) = s≤s (≤-suc-self n)

+-lt-suc : ∀ m n → m + suc n < m + suc (suc n)
+-lt-suc zero n = ≤-refl
+-lt-suc (suc m) n = s≤s (+-lt-suc m n)

+-lt-suc2 : ∀ m n → m + suc n < m + suc (suc (suc n))
+-lt-suc2 m n = <-trans (+-lt-suc m n) (+-lt-suc m (suc n))

+-lt-id : ∀ m n → m + n < m + suc (suc n)
+-lt-id zero n = s≤s (≤-suc-self n)
+-lt-id (suc m) n = s≤s (+-lt-id m n)

-- 三生成元严格减长（tri −1 / sq −2 / bt −2 ✓）
len-tri : ∀ {u x y z v : C5-vert} (p : Walk C5G u x) (b : Walk C5G z v)
  (e1 : E5 x y) (e2 : E5 y z) (e3 : E5 x z)
  → len (p ++w (cons e3 b)) < len (p ++w (cons e1 (cons e2 b)))
len-tri p b e1 e2 e3
  rewrite sym (len-++ p (cons e3 b)) | sym (len-++ p (cons e1 (cons e2 b)))
  = +-lt-suc (len p) (len b)

len-sq : ∀ {u x y z w v : C5-vert} (p : Walk C5G u x) (b : Walk C5G w v)
  (e1 : E5 x y) (e2 : E5 y z) (e3 : E5 z w) (e4 : E5 x w)
  → len (p ++w (cons e4 b)) < len (p ++w (cons e1 (cons e2 (cons e3 b))))
len-sq p b e1 e2 e3 e4
  rewrite sym (len-++ p (cons e4 b)) | sym (len-++ p (cons e1 (cons e2 (cons e3 b))))
  = +-lt-suc2 (len p) (len b)

len-bt : ∀ {u x y v : C5-vert} (p : Walk C5G u x) (q : Walk C5G x v)
  (e : E5 x y) (f : E5 y x)
  → len (p ++w q) < len (p ++w (cons e (cons f q)))
len-bt p q e f
  rewrite sym (len-++ p q) | sym (len-++ p (cons e (cons f q)))
  = +-lt-id (len p) (len q)

-- ★ 强终止化（合并件 ✓）
AStepStd-dec : ∀ {u v : C5-vert} {w1 w2 : Walk C5G u v}
  (s : AStepStd C5G w1 w2) → len w2 < len w1
AStepStd-dec (tri-slide p b e1 e2 e3) = len-tri p b e1 e2 e3
AStepStd-dec (sq-slide4 p b e1 e2 e3 e4) = len-sq p b e1 e2 e3 e4
AStepStd-dec (bt p q e f) = len-bt p q e f

--------------------------------------------------------------------------------
-- ④ 方向、回溯对、bt-free、单调（T1b ✓）
--------------------------------------------------------------------------------

data Dir : Set where cw ccw : Dir

dirOf : ∀ {x y : C5-vert} → E5 x y → Dir
dirOf cw01 = cw
dirOf cw12 = cw
dirOf cw23 = cw
dirOf cw34 = cw
dirOf cw40 = cw
dirOf cc10 = ccw
dirOf cc21 = ccw
dirOf cc32 = ccw
dirOf cc43 = ccw
dirOf cc04 = ccw

data RevPair : ∀ {x y z : C5-vert} → E5 x y → E5 y z → Set where
  r-cw01 : RevPair cw01 cc10
  r-cw12 : RevPair cw12 cc21
  r-cw23 : RevPair cw23 cc32
  r-cw34 : RevPair cw34 cc43
  r-cw40 : RevPair cw40 cc04
  r-cc10 : RevPair cc10 cw01
  r-cc21 : RevPair cc21 cw12
  r-cc32 : RevPair cc32 cw23
  r-cc43 : RevPair cc43 cw34
  r-cc04 : RevPair cc04 cw40

allDir : ∀ {u v : C5-vert} → Walk C5G u v → Dir → Set
allDir (nil x) d = ⊤
allDir (cons e b) d = (dirOf e ≡ d) × allDir b d

btFree : ∀ {u v : C5-vert} → Walk C5G u v → Set
btFree (nil x) = ⊤
btFree (cons e (nil y)) = ⊤
btFree (cons e (cons f b)) = (RevPair e f → ⊥) × btFree (cons f b)

-- 关键步引理：非回溯 ⇒ 同向（20 子句全具体 ✓）
step-not-rev : ∀ {x y z : C5-vert} (e : E5 x y) (f : E5 y z)
  → (RevPair e f → ⊥) → dirOf f ≡ dirOf e
step-not-rev cw01 cw12 h = refl
step-not-rev cw01 cc10 h = ⊥-elim (h r-cw01)
step-not-rev cw12 cw23 h = refl
step-not-rev cw12 cc21 h = ⊥-elim (h r-cw12)
step-not-rev cw23 cw34 h = refl
step-not-rev cw23 cc32 h = ⊥-elim (h r-cw23)
step-not-rev cw34 cw40 h = refl
step-not-rev cw34 cc43 h = ⊥-elim (h r-cw34)
step-not-rev cw40 cw01 h = refl
step-not-rev cw40 cc04 h = ⊥-elim (h r-cw40)
step-not-rev cc10 cw01 h = ⊥-elim (h r-cc10)
step-not-rev cc10 cc04 h = refl
step-not-rev cc21 cw12 h = ⊥-elim (h r-cc21)
step-not-rev cc21 cc10 h = refl
step-not-rev cc32 cw23 h = ⊥-elim (h r-cc32)
step-not-rev cc32 cc21 h = refl
step-not-rev cc43 cw34 h = ⊥-elim (h r-cc43)
step-not-rev cc43 cc32 h = refl
step-not-rev cc04 cw40 h = ⊥-elim (h r-cc04)
step-not-rev cc04 cc43 h = refl

mono-step : ∀ {u y z v : C5-vert} (e : E5 u y) (f : E5 y z) (b : Walk C5G z v)
  → (RevPair e f → ⊥) → Σ Dir (allDir (cons f b))
  → Σ Dir (allDir (cons e (cons f b)))
mono-step e f b nr (d , ih) =
  d , (trans (sym (step-not-rev e f nr)) (proj₁ ih) , ih)

-- ★ 主定理：bt-free 走 ⇒ 单调 ✓
btFree-monotone : ∀ {u v : C5-vert} (w : Walk C5G u v) → btFree w → Σ Dir (allDir w)
btFree-monotone (nil x) bf = cw , tt
btFree-monotone (cons e (nil y)) bf = dirOf e , refl , tt
btFree-monotone (cons e (cons f b)) (nr , bf') =
  mono-step e f b nr (btFree-monotone (cons f b) bf')

--------------------------------------------------------------------------------
-- ⑤ 方向计数与纯绕行（T1c ✓）
--------------------------------------------------------------------------------

ind : Dir → ℕ
ind cw = suc zero
ind ccw = zero

ind' : Dir → ℕ
ind' cw = zero
ind' ccw = suc zero

nCw : ∀ {u v : C5-vert} → Walk C5G u v → ℕ
nCw (nil x) = zero
nCw (cons e b) = ind (dirOf e) + nCw b

nCcw : ∀ {u v : C5-vert} → Walk C5G u v → ℕ
nCcw (nil x) = zero
nCcw (cons e b) = ind' (dirOf e) + nCcw b

mono-cw-nCcw-0 : ∀ {u v : C5-vert} (w : Walk C5G u v) → allDir w cw → nCcw w ≡ zero
mono-cw-nCcw-0 (nil x) ad = refl
mono-cw-nCcw-0 (cons e b) (de≡cw , ad) = cong₂ _+_ (cong ind' de≡cw) (mono-cw-nCcw-0 b ad)

mono-cw-nCw-len : ∀ {u v : C5-vert} (w : Walk C5G u v) → allDir w cw → nCw w ≡ len w
mono-cw-nCw-len (nil x) ad = refl
mono-cw-nCw-len (cons e b) (de≡cw , ad) = cong₂ _+_ (cong ind de≡cw) (mono-cw-nCw-len b ad)

mono-ccw-nCw-0 : ∀ {u v : C5-vert} (w : Walk C5G u v) → allDir w ccw → nCw w ≡ zero
mono-ccw-nCw-0 (nil x) ad = refl
mono-ccw-nCw-0 (cons e b) (de≡ccw , ad) = cong₂ _+_ (cong ind de≡ccw) (mono-ccw-nCw-0 b ad)

mono-ccw-nCcw-len : ∀ {u v : C5-vert} (w : Walk C5G u v) → allDir w ccw → nCcw w ≡ len w
mono-ccw-nCcw-len (nil x) ad = refl
mono-ccw-nCcw-len (cons e b) (de≡ccw , ad) = cong₂ _+_ (cong ind' de≡ccw) (mono-ccw-nCcw-len b ad)

-- ★ 纯绕行：bt-free 闭走 ⇒ 计数全归一侧 ✓
winding-dichotomy : ∀ {x : C5-vert} (w : Walk C5G x x) → btFree w
  → ((nCcw w ≡ zero) × (nCw w ≡ len w))
  ⊎ ((nCw w ≡ zero) × (nCcw w ≡ len w))
winding-dichotomy w bf with btFree-monotone w bf
... | cw , ad = inj₁ (mono-cw-nCcw-0 w ad , mono-cw-nCw-len w ad)
... | ccw , ad = inj₂ (mono-ccw-nCw-0 w ad , mono-ccw-nCcw-len w ad)

--------------------------------------------------------------------------------
-- ⑥ ℤ 桥接（T1d ✓）
--------------------------------------------------------------------------------

wE : ∀ {x y : C5-vert} → E5 x y → ℤ
wE cw01 = + 1
wE cw12 = + 1
wE cw23 = + 1
wE cw34 = + 1
wE cw40 = + 1
wE cc10 = - (+ 1)
wE cc21 = - (+ 1)
wE cc32 = - (+ 1)
wE cc43 = - (+ 1)
wE cc04 = - (+ 1)

windE : ∀ {u v : C5-vert} → Walk C5G u v → ℤ
windE (nil x) = + 0
windE (cons e b) = wE e +ℤ windE b

wE-cw : ∀ {x y : C5-vert} (e : E5 x y) → dirOf e ≡ cw → wE e ≡ + 1
wE-cw cw01 h = refl
wE-cw cw12 h = refl
wE-cw cw23 h = refl
wE-cw cw34 h = refl
wE-cw cw40 h = refl
wE-cw cc10 ()
wE-cw cc21 ()
wE-cw cc32 ()
wE-cw cc43 ()
wE-cw cc04 ()

wE-ccw : ∀ {x y : C5-vert} (e : E5 x y) → dirOf e ≡ ccw → wE e ≡ - (+ 1)
wE-ccw cw01 ()
wE-ccw cw12 ()
wE-ccw cw23 ()
wE-ccw cw34 ()
wE-ccw cw40 ()
wE-ccw cc10 h = refl
wE-ccw cc21 h = refl
wE-ccw cc32 h = refl
wE-ccw cc43 h = refl
wE-ccw cc04 h = refl

wind-cw-len : ∀ {u v : C5-vert} (w : Walk C5G u v) → allDir w cw → windE w ≡ + len w
wind-cw-len (nil x) ad = refl
wind-cw-len (cons e b) (de≡cw , ad) =
  trans (cong₂ _+ℤ_ (wE-cw e de≡cw) (wind-cw-len b ad)) refl

wind-ccw-neg-len : ∀ {u v : C5-vert} (w : Walk C5G u v) → allDir w ccw
  → windE w ≡ - (+ len w)
wind-ccw-neg-len (nil x) ad = refl
wind-ccw-neg-len (cons e b) (de≡ccw , ad) =
  trans (cong₂ _+ℤ_ (wE-ccw e de≡ccw) (wind-ccw-neg-len b ad))
        (sym (neg-distrib-+ (+ 1) (+ len b)))

-- ★★ 主推论：bt-free 闭走 ⇒ wind = ±len ✓
btFree-wind-dichotomy : ∀ {x : C5-vert} (w : Walk C5G x x) → btFree w
  → (windE w ≡ + len w) ⊎ (windE w ≡ - (+ len w))
btFree-wind-dichotomy w bf with btFree-monotone w bf
... | cw , ad = inj₁ (wind-cw-len w ad)
... | ccw , ad = inj₂ (wind-ccw-neg-len w ad)
