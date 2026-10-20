{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Synthesis.Homotopy.C5FundamentalGroup
--
-- **π₁ᵈˢᵗᵈ(C₅) ≅ ℤ**（类判据形态 ✓ 与文献 π₁ᴬ(C_n) = ℤ (n≥5) 一致 ✓）
--
-- 数学背景（Kapulkin–Mavinkurve 2023 Ex 4.33 ✓ PDF 在库 ✓）：
--   AStepStd（标准 A-同伦生成集：tri-slide / sq-slide4 / bt ✓ C5Rigidity 已给）
--   的等价类由**绕数**完全分类：
--     ⟹ class-sound：同类 ⇒ 绕数相等（步级不变性归纳 ✓）
--     ⟸ class-complete：绕数相等 ⇒ 同类（正规形存在 ⇒ 单调 ⇒ 方向+长度由绕数定
--        ⇒ 正规形相等（双向单调唯一）✓）
--   ⇒ **类 ≅ 5ℤ ≅ ℤ** ✓
--
-- 核心原则：
--   1. C₅ 三角真空（无弦 ✓）／方形仅两种退化形（回溯对 + 同构造子 ✓）
--   2. 具体边构造子 + 顶点具体化（避 K 禁用对角索引墙 ✗ 先例 _PN4:310 ✓）
--   3. ℤ 算术自证（pos-inj/neg-inj/pos-neq-neg ✓ 不猜 stdlib 名 ✓）
--
-- 0 postulate / 0 hole。来源探针：_PEH46–_PEH52（回执 f699174d…/8b0c7541…/
-- 2af7cb21…/7c2f33cc…/2ac9c5ff…/7d5e537b…/0f3941b2… ✓）

module Sovereign.Synthesis.Homotopy.C5FundamentalGroup where

open import Data.Nat using (ℕ; zero; suc; _<_; _≤_; s≤s; z≤n)
open import Data.Nat.Induction using (<-wellFounded; Acc; acc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Data.Integer using (ℤ; +_; -_) renaming (_+_ to _+ℤ_)
open import Data.Integer.Properties using (+-assoc; +-identityˡ; +-identityʳ; +-inverseˡ; +-inverseʳ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans; sym)
open import Sovereign.Synthesis.Homotopy.BarceloAHomotopy using (Walk; cons; nil; _++w_)
open import Sovereign.Synthesis.Homotopy.C5Rigidity
  using (AStepStd; tri-slide; sq-slide4; bt; C5-vert; c0; c1; c2; c3; c4;
         E5; cw01; cw12; cw23; cw34; cw40; cc10; cc21; cc32; cc43; cc04; C5G;
         len; len-++; Dir; cw; ccw; dirOf; RevPair;
         r-cw01; r-cw12; r-cw23; r-cw34; r-cw40; r-cc10; r-cc21; r-cc32; r-cc43; r-cc04;
         allDir; btFree; step-not-rev; mono-step; btFree-monotone;
         wE; windE; wE-cw; wE-ccw; wind-cw-len; wind-ccw-neg-len)

--------------------------------------------------------------------------------
-- T4 系列（绕数不变性 → 正规形存在 → 双向唯一 → 类判据）✓
--------------------------------------------------------------------------------

--------------------------------------------------------------------------------
-- ① ★ T4a 三角真空：不存在弦（20 子句 ✓ 全空模式 ✓）
--------------------------------------------------------------------------------

no-tri : ∀ {x y z : C5-vert} (e1 : E5 x y) (e2 : E5 y z) (e3 : E5 x z) → ⊥
-- e1 = cw01 (c0→c1)：e2 只能 cw12 / cc10 ⇒ 弦 E5 c0 z 不存在 ✓
no-tri cw01 cw12 ()
no-tri cw01 cc10 ()
-- e1 = cw12 (c1→c2)
no-tri cw12 cw23 ()
no-tri cw12 cc21 ()
-- e1 = cw23 (c2→c3)
no-tri cw23 cw34 ()
no-tri cw23 cc32 ()
-- e1 = cw34 (c3→c4)
no-tri cw34 cw40 ()
no-tri cw34 cc43 ()
-- e1 = cw40 (c4→c0)
no-tri cw40 cw01 ()
no-tri cw40 cc04 ()
-- e1 = cc10 (c1→c0)
no-tri cc10 cw01 ()
no-tri cc10 cc04 ()
-- e1 = cc21 (c2→c1)
no-tri cc21 cw12 ()
no-tri cc21 cc10 ()
-- e1 = cc32 (c3→c2)
no-tri cc32 cw23 ()
no-tri cc32 cc21 ()
-- e1 = cc43 (c4→c3)
no-tri cc43 cw34 ()
no-tri cc43 cc32 ()
-- e1 = cc04 (c0→c4)
no-tri cc04 cw40 ()
no-tri cc04 cc43 ()

--------------------------------------------------------------------------------
-- ② ★ T4b bt 保持绕数：反向对绕数和 = 0 ✓（10 案 ✓）
--------------------------------------------------------------------------------

bt-wind-0 : ∀ {x y z : C5-vert} (e : E5 x y) (f : E5 y z)
  → RevPair e f → wE e +ℤ wE f ≡ + 0
bt-wind-0 cw01 cc10 r = +-inverseʳ (+ 1)
bt-wind-0 cw12 cc21 r = +-inverseʳ (+ 1)
bt-wind-0 cw23 cc32 r = +-inverseʳ (+ 1)
bt-wind-0 cw34 cc43 r = +-inverseʳ (+ 1)
bt-wind-0 cw40 cc04 r = +-inverseʳ (+ 1)
bt-wind-0 cc10 cw01 r = +-inverseʳ (- (+ 1))
bt-wind-0 cc21 cw12 r = +-inverseʳ (- (+ 1))
bt-wind-0 cc32 cw23 r = +-inverseʳ (- (+ 1))
bt-wind-0 cc43 cw34 r = +-inverseʳ (- (+ 1))
bt-wind-0 cc04 cw40 r = +-inverseʳ (- (+ 1))

--------------------------------------------------------------------------------
-- ★ 方形绕数不变性（30 子句 ✓ 形 A × 20 + 形 B × 10 ✓）
--------------------------------------------------------------------------------

sq-wind : ∀ {x y z w : C5-vert} (e1 : E5 x y) (e2 : E5 y z) (e3 : E5 z w)
          (e4 : E5 x w) → wE e1 +ℤ (wE e2 +ℤ wE e3) ≡ wE e4
sq-wind cw01 cc10 cw01 cw01 =
  trans (sym (+-assoc (wE cw01) (wE cc10) (wE cw01)))
    (trans (cong (_+ℤ wE cw01) (bt-wind-0 cw01 cc10 r-cw01))
           (+-identityˡ (wE cw01)))
sq-wind cw01 cc10 cc04 cc04 =
  trans (sym (+-assoc (wE cw01) (wE cc10) (wE cc04)))
    (trans (cong (_+ℤ wE cc04) (bt-wind-0 cw01 cc10 r-cw01))
           (+-identityˡ (wE cc04)))
sq-wind cw12 cc21 cw12 cw12 =
  trans (sym (+-assoc (wE cw12) (wE cc21) (wE cw12)))
    (trans (cong (_+ℤ wE cw12) (bt-wind-0 cw12 cc21 r-cw12))
           (+-identityˡ (wE cw12)))
sq-wind cw12 cc21 cc10 cc10 =
  trans (sym (+-assoc (wE cw12) (wE cc21) (wE cc10)))
    (trans (cong (_+ℤ wE cc10) (bt-wind-0 cw12 cc21 r-cw12))
           (+-identityˡ (wE cc10)))
sq-wind cw23 cc32 cw23 cw23 =
  trans (sym (+-assoc (wE cw23) (wE cc32) (wE cw23)))
    (trans (cong (_+ℤ wE cw23) (bt-wind-0 cw23 cc32 r-cw23))
           (+-identityˡ (wE cw23)))
sq-wind cw23 cc32 cc21 cc21 =
  trans (sym (+-assoc (wE cw23) (wE cc32) (wE cc21)))
    (trans (cong (_+ℤ wE cc21) (bt-wind-0 cw23 cc32 r-cw23))
           (+-identityˡ (wE cc21)))
sq-wind cw34 cc43 cw34 cw34 =
  trans (sym (+-assoc (wE cw34) (wE cc43) (wE cw34)))
    (trans (cong (_+ℤ wE cw34) (bt-wind-0 cw34 cc43 r-cw34))
           (+-identityˡ (wE cw34)))
sq-wind cw34 cc43 cc32 cc32 =
  trans (sym (+-assoc (wE cw34) (wE cc43) (wE cc32)))
    (trans (cong (_+ℤ wE cc32) (bt-wind-0 cw34 cc43 r-cw34))
           (+-identityˡ (wE cc32)))
sq-wind cw40 cc04 cw40 cw40 =
  trans (sym (+-assoc (wE cw40) (wE cc04) (wE cw40)))
    (trans (cong (_+ℤ wE cw40) (bt-wind-0 cw40 cc04 r-cw40))
           (+-identityˡ (wE cw40)))
sq-wind cw40 cc04 cc43 cc43 =
  trans (sym (+-assoc (wE cw40) (wE cc04) (wE cc43)))
    (trans (cong (_+ℤ wE cc43) (bt-wind-0 cw40 cc04 r-cw40))
           (+-identityˡ (wE cc43)))
sq-wind cc10 cw01 cw12 cw12 =
  trans (sym (+-assoc (wE cc10) (wE cw01) (wE cw12)))
    (trans (cong (_+ℤ wE cw12) (bt-wind-0 cc10 cw01 r-cc10))
           (+-identityˡ (wE cw12)))
sq-wind cc10 cw01 cc10 cc10 =
  trans (sym (+-assoc (wE cc10) (wE cw01) (wE cc10)))
    (trans (cong (_+ℤ wE cc10) (bt-wind-0 cc10 cw01 r-cc10))
           (+-identityˡ (wE cc10)))
sq-wind cc21 cw12 cw23 cw23 =
  trans (sym (+-assoc (wE cc21) (wE cw12) (wE cw23)))
    (trans (cong (_+ℤ wE cw23) (bt-wind-0 cc21 cw12 r-cc21))
           (+-identityˡ (wE cw23)))
sq-wind cc21 cw12 cc21 cc21 =
  trans (sym (+-assoc (wE cc21) (wE cw12) (wE cc21)))
    (trans (cong (_+ℤ wE cc21) (bt-wind-0 cc21 cw12 r-cc21))
           (+-identityˡ (wE cc21)))
sq-wind cc32 cw23 cw34 cw34 =
  trans (sym (+-assoc (wE cc32) (wE cw23) (wE cw34)))
    (trans (cong (_+ℤ wE cw34) (bt-wind-0 cc32 cw23 r-cc32))
           (+-identityˡ (wE cw34)))
sq-wind cc32 cw23 cc32 cc32 =
  trans (sym (+-assoc (wE cc32) (wE cw23) (wE cc32)))
    (trans (cong (_+ℤ wE cc32) (bt-wind-0 cc32 cw23 r-cc32))
           (+-identityˡ (wE cc32)))
sq-wind cc43 cw34 cw40 cw40 =
  trans (sym (+-assoc (wE cc43) (wE cw34) (wE cw40)))
    (trans (cong (_+ℤ wE cw40) (bt-wind-0 cc43 cw34 r-cc43))
           (+-identityˡ (wE cw40)))
sq-wind cc43 cw34 cc43 cc43 =
  trans (sym (+-assoc (wE cc43) (wE cw34) (wE cc43)))
    (trans (cong (_+ℤ wE cc43) (bt-wind-0 cc43 cw34 r-cc43))
           (+-identityˡ (wE cc43)))
sq-wind cc04 cw40 cw01 cw01 =
  trans (sym (+-assoc (wE cc04) (wE cw40) (wE cw01)))
    (trans (cong (_+ℤ wE cw01) (bt-wind-0 cc04 cw40 r-cc04))
           (+-identityˡ (wE cw01)))
sq-wind cc04 cw40 cc04 cc04 =
  trans (sym (+-assoc (wE cc04) (wE cw40) (wE cc04)))
    (trans (cong (_+ℤ wE cc04) (bt-wind-0 cc04 cw40 r-cc04))
           (+-identityˡ (wE cc04)))
sq-wind cw01 cw12 cc21 cw01 =
  trans (cong (wE cw01 +ℤ_) (bt-wind-0 cw12 cc21 r-cw12))
        (+-identityʳ (wE cw01))
sq-wind cw12 cw23 cc32 cw12 =
  trans (cong (wE cw12 +ℤ_) (bt-wind-0 cw23 cc32 r-cw23))
        (+-identityʳ (wE cw12))
sq-wind cw23 cw34 cc43 cw23 =
  trans (cong (wE cw23 +ℤ_) (bt-wind-0 cw34 cc43 r-cw34))
        (+-identityʳ (wE cw23))
sq-wind cw34 cw40 cc04 cw34 =
  trans (cong (wE cw34 +ℤ_) (bt-wind-0 cw40 cc04 r-cw40))
        (+-identityʳ (wE cw34))
sq-wind cw40 cw01 cc10 cw40 =
  trans (cong (wE cw40 +ℤ_) (bt-wind-0 cw01 cc10 r-cw01))
        (+-identityʳ (wE cw40))
sq-wind cc10 cc04 cw40 cc10 =
  trans (cong (wE cc10 +ℤ_) (bt-wind-0 cc04 cw40 r-cc04))
        (+-identityʳ (wE cc10))
sq-wind cc21 cc10 cw01 cc21 =
  trans (cong (wE cc21 +ℤ_) (bt-wind-0 cc10 cw01 r-cc10))
        (+-identityʳ (wE cc21))
sq-wind cc32 cc21 cw12 cc32 =
  trans (cong (wE cc32 +ℤ_) (bt-wind-0 cc21 cw12 r-cc21))
        (+-identityʳ (wE cc32))
sq-wind cc43 cc32 cw23 cc43 =
  trans (cong (wE cc43 +ℤ_) (bt-wind-0 cc32 cw23 r-cc32))
        (+-identityʳ (wE cc43))
sq-wind cc04 cc43 cw34 cc04 =
  trans (cong (wE cc04 +ℤ_) (bt-wind-0 cc43 cw34 r-cc43))
        (+-identityʳ (wE cc04))

--------------------------------------------------------------------------------
-- ① 拼接同态：windE (p ++w q) = windE p + windE q ✓（对 p 归纳 ✓）
--------------------------------------------------------------------------------

windE-++ : ∀ {u v w : C5-vert} (p : Walk C5G u v) (q : Walk C5G v w)
  → windE (p ++w q) ≡ windE p +ℤ windE q
windE-++ (nil x) q = sym (+-identityˡ (windE q))
windE-++ (cons e b) q =
  trans (cong (wE e +ℤ_) (windE-++ b q))
        (sym (+-assoc (wE e) (windE b) (windE q)))

--------------------------------------------------------------------------------
-- ② 反向边唯一：RevPair e f ✓（10 案 ✓ 每 e 恰一个反向 f ✓）
--------------------------------------------------------------------------------

rev-pair : ∀ {x y : C5-vert} (e : E5 x y) (f : E5 y x) → RevPair e f
rev-pair cw01 cc10 = r-cw01
rev-pair cw12 cc21 = r-cw12
rev-pair cw23 cc32 = r-cw23
rev-pair cw34 cc43 = r-cw34
rev-pair cw40 cc04 = r-cw40
rev-pair cc10 cw01 = r-cc10
rev-pair cc21 cw12 = r-cc21
rev-pair cc32 cw23 = r-cc32
rev-pair cc43 cw34 = r-cc43
rev-pair cc04 cw40 = r-cc04

--------------------------------------------------------------------------------
-- ③ 带尾巴 X 的局部方程（局部方程 + 结合律 ✓ 供步级用 ✓）
--------------------------------------------------------------------------------

sq-inner : ∀ {x y z w : C5-vert} (e1 : E5 x y) (e2 : E5 y z) (e3 : E5 z w)
  (e4 : E5 x w) (X : ℤ)
  → wE e1 +ℤ (wE e2 +ℤ (wE e3 +ℤ X)) ≡ wE e4 +ℤ X
sq-inner e1 e2 e3 e4 X =
  trans (cong (wE e1 +ℤ_) (sym (+-assoc (wE e2) (wE e3) X)))
        (trans (sym (+-assoc (wE e1) (wE e2 +ℤ wE e3) X))
               (cong (_+ℤ X) (sq-wind e1 e2 e3 e4)))

bt-inner : ∀ {x y z : C5-vert} (e : E5 x y) (f : E5 y z) (X : ℤ)
  → RevPair e f → wE e +ℤ (wE f +ℤ X) ≡ X
bt-inner e f X r =
  trans (sym (+-assoc (wE e) (wE f) X))
        (trans (cong (_+ℤ X) (bt-wind-0 e f r)) (+-identityˡ X))

--------------------------------------------------------------------------------
-- ④ ★ 步级绕数不变性：三生成元全覆盖 ✓
--------------------------------------------------------------------------------

AStepStd-wind : ∀ {u v : C5-vert} {w1 w2 : Walk C5G u v}
  (s : AStepStd C5G w1 w2) → windE w1 ≡ windE w2
-- tri：C₅ 无弦 ⇒ 真空 ✓
AStepStd-wind (tri-slide p b e1 e2 e3) = ⊥-elim (no-tri e1 e2 e3)
-- sq：局部方程 + 拼接同态 ✓
AStepStd-wind (sq-slide4 p b e1 e2 e3 e4) =
  trans (windE-++ p (cons e1 (cons e2 (cons e3 b))))
        (trans (cong (windE p +ℤ_) (sq-inner e1 e2 e3 e4 (windE b)))
               (sym (windE-++ p (cons e4 b))))
-- bt：反向对消 + 拼接同态 ✓
AStepStd-wind (bt p q e f) =
  trans (windE-++ p (cons e (cons f q)))
        (trans (cong (windE p +ℤ_) (bt-inner e f (windE q) (rev-pair e f)))
               (sym (windE-++ p q)))

--------------------------------------------------------------------------------
-- ⑤ 上下文引理：前缀 e 保持可施 ✓（3 案 ✓ 供 T4e 归纳用 ✓）
--------------------------------------------------------------------------------

step-cons : ∀ {u x v : C5-vert} (e : E5 u x) {w1 w2 : Walk C5G x v}
  → AStepStd C5G w1 w2 → AStepStd C5G (cons e w1) (cons e w2)
step-cons e (tri-slide p b e1 e2 e3) = tri-slide (cons e p) b e1 e2 e3
step-cons e (sq-slide4 p b e1 e2 e3 e4) = sq-slide4 (cons e p) b e1 e2 e3 e4
step-cons e (bt p q e' f) = bt (cons e p) q e' f

--------------------------------------------------------------------------------
-- ① 回溯对判定 ✓（20 子句 ✓）
--------------------------------------------------------------------------------

revPair? : ∀ {x y z : C5-vert} (e : E5 x y) (f : E5 y z) → Dec (RevPair e f)
revPair? cw01 cw12 = no (λ ())
revPair? cw01 cc10 = yes r-cw01
revPair? cw12 cw23 = no (λ ())
revPair? cw12 cc21 = yes r-cw12
revPair? cw23 cw34 = no (λ ())
revPair? cw23 cc32 = yes r-cw23
revPair? cw34 cw40 = no (λ ())
revPair? cw34 cc43 = yes r-cw34
revPair? cw40 cw01 = no (λ ())
revPair? cw40 cc04 = yes r-cw40
revPair? cc10 cw01 = yes r-cc10
revPair? cc10 cc04 = no (λ ())
revPair? cc21 cw12 = yes r-cc21
revPair? cc21 cc10 = no (λ ())
revPair? cc32 cw23 = yes r-cc32
revPair? cc32 cc21 = no (λ ())
revPair? cc43 cw34 = yes r-cc43
revPair? cc43 cc32 = no (λ ())
revPair? cc04 cw40 = yes r-cc04
revPair? cc04 cc43 = no (λ ())

--------------------------------------------------------------------------------
-- ② bt-free 判定 ✓（结构递归 ✓）
--------------------------------------------------------------------------------

dec-cons : ∀ {x y z v : C5-vert} (e : E5 x y) (f : E5 y z) (b : Walk C5G z v)
  → Dec (RevPair e f) → Dec (btFree (cons f b)) → Dec (btFree (cons e (cons f b)))
dec-cons e f b (yes r) _ = no (λ (nr , _) → nr r)
dec-cons e f b (no nr) (yes bf) = yes (nr , bf)
dec-cons e f b (no nr) (no nbf) = no (λ (_ , bf) → nbf bf)

btFree? : ∀ {u v : C5-vert} (w : Walk C5G u v) → Dec (btFree w)
btFree? (nil x) = yes tt
btFree? (cons e (nil y)) = yes tt
btFree? (cons e (cons f b)) = dec-cons e f b (revPair? e f) (btFree? (cons f b))

--------------------------------------------------------------------------------
-- ③ AStepStd 闭包 + 上下文保持 ✓
--------------------------------------------------------------------------------

data AH* : ∀ {u v : C5-vert} → Walk C5G u v → Walk C5G u v → Set where
  rfl* : ∀ {u v} (w : Walk C5G u v) → AH* w w
  step* : ∀ {u v} {w1 w2 w3 : Walk C5G u v}
    → AStepStd C5G w1 w2 → AH* w2 w3 → AH* w1 w3

AH*-cons : ∀ {u x v : C5-vert} (e : E5 u x) {w1 w2 : Walk C5G x v}
  → AH* w1 w2 → AH* (cons e w1) (cons e w2)
AH*-cons e (rfl* w) = rfl* (cons e w)
AH*-cons e (step* s h) = step* (step-cons e s) (AH*-cons e h)

--------------------------------------------------------------------------------
-- ④ ★ 步骤或 bt-free（结构递归 ✓ 递归在**直接位置** ✓ 避开 λ/with 陷阱 ✗）
--------------------------------------------------------------------------------

≤-suc-self : ∀ n → n ≤ suc n
≤-suc-self zero = z≤n
≤-suc-self (suc n) = s≤s (≤-suc-self n)

step-or : ∀ {u v : C5-vert} (w : Walk C5G u v)
  → (Σ (Walk C5G u v) (λ w1 → AStepStd C5G w w1 × len w1 < len w))
  ⊎ btFree w
step-or (nil x) = inj₂ tt
step-or (cons e (nil y)) = inj₂ tt
-- 先处理尾部（直接递归 ✓ 结构更小 ✓）
step-or (cons e (cons f b)) with step-or (cons f b)
... | inj₁ (w1 , s , lt) = inj₁ (cons e w1 , step-cons e s , s≤s lt)
... | inj₂ bf with revPair? e f
-- 头部即回溯对 ⇒ bt 步骤 ✓（10 子句细化索引 ✓）
...   | yes r-cw01 = inj₁ (b , bt (nil c0) b cw01 cc10 , s≤s (≤-suc-self (len b)))
...   | yes r-cw12 = inj₁ (b , bt (nil c1) b cw12 cc21 , s≤s (≤-suc-self (len b)))
...   | yes r-cw23 = inj₁ (b , bt (nil c2) b cw23 cc32 , s≤s (≤-suc-self (len b)))
...   | yes r-cw34 = inj₁ (b , bt (nil c3) b cw34 cc43 , s≤s (≤-suc-self (len b)))
...   | yes r-cw40 = inj₁ (b , bt (nil c4) b cw40 cc04 , s≤s (≤-suc-self (len b)))
...   | yes r-cc10 = inj₁ (b , bt (nil c1) b cc10 cw01 , s≤s (≤-suc-self (len b)))
...   | yes r-cc21 = inj₁ (b , bt (nil c2) b cc21 cw12 , s≤s (≤-suc-self (len b)))
...   | yes r-cc32 = inj₁ (b , bt (nil c3) b cc32 cw23 , s≤s (≤-suc-self (len b)))
...   | yes r-cc43 = inj₁ (b , bt (nil c4) b cc43 cw34 , s≤s (≤-suc-self (len b)))
...   | yes r-cc04 = inj₁ (b , bt (nil c0) b cc04 cw40 , s≤s (≤-suc-self (len b)))
-- 头部非回溯 ⇒ bt-free ✓
...   | no nr = inj₂ (nr , bf)

-- 推论：¬bt-free ⇒ 存在减长步骤 ✓（无递归 ✓）
step-exists-dec : ∀ {u v : C5-vert} (w : Walk C5G u v) → ¬ (btFree w)
  → Σ (Walk C5G u v) (λ w1 → AStepStd C5G w w1 × len w1 < len w)
step-exists-dec w nb with step-or w
... | inj₁ sw = sw
... | inj₂ bf = ⊥-elim (nb bf)

--------------------------------------------------------------------------------
-- ⑤ ★★ 正规形存在：每条走归约到 bt-free 走 ✓（len 良基归纳 ✓）
--     范式：`go w (acc rec)` ✓（先例 Decimal/Proofs.agda:91 ✓）
--     解构 Σ 用 **helper（模式在参数位 ✓）** 避开 with 抽象 ✗（_PEH43 先例 ✓）
--------------------------------------------------------------------------------

mutual
  nf-go : ∀ {u v : C5-vert} (w : Walk C5G u v) → Acc _<_ (len w)
    → Σ (Walk C5G u v) (λ w' → btFree w' × AH* w w')
  nf-go w (acc rec) with btFree? w
  ... | yes bf = w , bf , rfl* w
  ... | no nbf = nf-step w (step-exists-dec w nbf) (acc rec)

  nf-step : ∀ {u v : C5-vert} (w : Walk C5G u v)
    → Σ (Walk C5G u v) (λ w1 → AStepStd C5G w w1 × len w1 < len w)
    → Acc _<_ (len w)
    → Σ (Walk C5G u v) (λ w' → btFree w' × AH* w w')
  nf-step w (w1 , s , lt) (acc rec) with nf-go w1 (rec lt)
  ... | w2 , bf2 , h = w2 , bf2 , step* s h

nf-exists : ∀ {u v : C5-vert} (w : Walk C5G u v)
  → Σ (Walk C5G u v) (λ w' → btFree w' × AH* w w')
nf-exists w = nf-go w (<-wellFounded (len w))

--------------------------------------------------------------------------------
-- ① suc 单射（自证 ✓ 不猜 stdlib 名）
--------------------------------------------------------------------------------

suc-inj : ∀ {m n : ℕ} → suc m ≡ suc n → m ≡ n
suc-inj refl = refl

--------------------------------------------------------------------------------
-- ③ ★ 每顶点 cw 出边唯一 ✓（10 案 ✓）
--------------------------------------------------------------------------------

cw-edge-unique : ∀ {u v : C5-vert} (e e' : E5 u v)
  → dirOf e ≡ cw → dirOf e' ≡ cw → e ≡ e'
cw-edge-unique cw01 cw01 d d' = refl
cw-edge-unique cw12 cw12 d d' = refl
cw-edge-unique cw23 cw23 d d' = refl
cw-edge-unique cw34 cw34 d d' = refl
cw-edge-unique cw40 cw40 d d' = refl

--------------------------------------------------------------------------------
-- ③b cons 同余（自证 ✓ 避开 cong₂ 隐式顶点不对齐 ✗）
--------------------------------------------------------------------------------

cons-eq : ∀ {u v w : C5-vert} {e e' : E5 u v} {b b' : Walk C5G v w}
  → e ≡ e' → b ≡ b' → cons e b ≡ cons e' b'
cons-eq refl refl = refl

--------------------------------------------------------------------------------
-- ④ ★★ 单调走唯一：全 cw 走由 (起点, 长度) 确定 ✓
--     ⚠ 顶点具体化（K 禁用下对角索引 nil 模式卡死 ✗ 先例 _PN4:310 ✓）
--     每顶点 helper：具体边模式（2 案 ✓）＋ 非 cw 边空模式 ✓
--     mutual 跨顶点（沿 cw 后继 ✓）——走参数结构更小 ⇒ 终止性 ✓
--------------------------------------------------------------------------------

mutual
  cw-unique-c0 : ∀ {y : C5-vert} (w1 w2 : Walk C5G c0 y)
    → allDir w1 cw → allDir w2 cw → len w1 ≡ len w2 → w1 ≡ w2
  cw-unique-c0 (nil x) (nil y) ad1 ad2 eq = refl
  cw-unique-c0 (nil x) (cons e b) ad1 ad2 eq with len (cons e b) | eq
  ... | suc n | ()
  cw-unique-c0 (cons e b) (nil y) ad1 ad2 eq with len (cons e b) | eq
  ... | suc n | ()
  cw-unique-c0 (cons cw01 b) (cons cw01 b') (d1 , ad1) (d2 , ad2) eq =
    cons-eq refl (cw-unique-c1 b b' ad1 ad2 (suc-inj eq))
  cw-unique-c0 (cons cw01 b) (cons cc04 b') (d1 , ad1) (() , ad2) eq
  cw-unique-c0 (cons cc04 b) (cons e' b') (() , ad1) (d2 , ad2) eq
  cw-unique-c1 : ∀ {y : C5-vert} (w1 w2 : Walk C5G c1 y)
    → allDir w1 cw → allDir w2 cw → len w1 ≡ len w2 → w1 ≡ w2
  cw-unique-c1 (nil x) (nil y) ad1 ad2 eq = refl
  cw-unique-c1 (nil x) (cons e b) ad1 ad2 eq with len (cons e b) | eq
  ... | suc n | ()
  cw-unique-c1 (cons e b) (nil y) ad1 ad2 eq with len (cons e b) | eq
  ... | suc n | ()
  cw-unique-c1 (cons cw12 b) (cons cw12 b') (d1 , ad1) (d2 , ad2) eq =
    cons-eq refl (cw-unique-c2 b b' ad1 ad2 (suc-inj eq))
  cw-unique-c1 (cons cw12 b) (cons cc10 b') (d1 , ad1) (() , ad2) eq
  cw-unique-c1 (cons cc10 b) (cons e' b') (() , ad1) (d2 , ad2) eq
  cw-unique-c2 : ∀ {y : C5-vert} (w1 w2 : Walk C5G c2 y)
    → allDir w1 cw → allDir w2 cw → len w1 ≡ len w2 → w1 ≡ w2
  cw-unique-c2 (nil x) (nil y) ad1 ad2 eq = refl
  cw-unique-c2 (nil x) (cons e b) ad1 ad2 eq with len (cons e b) | eq
  ... | suc n | ()
  cw-unique-c2 (cons e b) (nil y) ad1 ad2 eq with len (cons e b) | eq
  ... | suc n | ()
  cw-unique-c2 (cons cw23 b) (cons cw23 b') (d1 , ad1) (d2 , ad2) eq =
    cons-eq refl (cw-unique-c3 b b' ad1 ad2 (suc-inj eq))
  cw-unique-c2 (cons cw23 b) (cons cc21 b') (d1 , ad1) (() , ad2) eq
  cw-unique-c2 (cons cc21 b) (cons e' b') (() , ad1) (d2 , ad2) eq
  cw-unique-c3 : ∀ {y : C5-vert} (w1 w2 : Walk C5G c3 y)
    → allDir w1 cw → allDir w2 cw → len w1 ≡ len w2 → w1 ≡ w2
  cw-unique-c3 (nil x) (nil y) ad1 ad2 eq = refl
  cw-unique-c3 (nil x) (cons e b) ad1 ad2 eq with len (cons e b) | eq
  ... | suc n | ()
  cw-unique-c3 (cons e b) (nil y) ad1 ad2 eq with len (cons e b) | eq
  ... | suc n | ()
  cw-unique-c3 (cons cw34 b) (cons cw34 b') (d1 , ad1) (d2 , ad2) eq =
    cons-eq refl (cw-unique-c4 b b' ad1 ad2 (suc-inj eq))
  cw-unique-c3 (cons cw34 b) (cons cc32 b') (d1 , ad1) (() , ad2) eq
  cw-unique-c3 (cons cc32 b) (cons e' b') (() , ad1) (d2 , ad2) eq
  cw-unique-c4 : ∀ {y : C5-vert} (w1 w2 : Walk C5G c4 y)
    → allDir w1 cw → allDir w2 cw → len w1 ≡ len w2 → w1 ≡ w2
  cw-unique-c4 (nil x) (nil y) ad1 ad2 eq = refl
  cw-unique-c4 (nil x) (cons e b) ad1 ad2 eq with len (cons e b) | eq
  ... | suc n | ()
  cw-unique-c4 (cons e b) (nil y) ad1 ad2 eq with len (cons e b) | eq
  ... | suc n | ()
  cw-unique-c4 (cons cw40 b) (cons cw40 b') (d1 , ad1) (d2 , ad2) eq =
    cons-eq refl (cw-unique-c0 b b' ad1 ad2 (suc-inj eq))
  cw-unique-c4 (cons cw40 b) (cons cc43 b') (d1 , ad1) (() , ad2) eq
  cw-unique-c4 (cons cc43 b) (cons e' b') (() , ad1) (d2 , ad2) eq

-- 一般化：任意起点分派 ✓
cw-unique : ∀ {x y : C5-vert} (w1 w2 : Walk C5G x y)
  → allDir w1 cw → allDir w2 cw → len w1 ≡ len w2 → w1 ≡ w2
cw-unique {x = c0} = cw-unique-c0
cw-unique {x = c1} = cw-unique-c1
cw-unique {x = c2} = cw-unique-c2
cw-unique {x = c3} = cw-unique-c3
cw-unique {x = c4} = cw-unique-c4

--------------------------------------------------------------------------------
-- 双向单调唯一（5 顶点 helper × 9 子句 = 45 ✓ mutual 沿 cw/ccw 后继 ✓）
--------------------------------------------------------------------------------

mutual
  mono-unique-c0 : ∀ {y : C5-vert} (w1 w2 : Walk C5G c0 y) (d : Dir)
    → allDir w1 d → allDir w2 d → len w1 ≡ len w2 → w1 ≡ w2
  mono-unique-c0 (nil x) (nil y) d ad1 ad2 eq = refl
  mono-unique-c0 (nil x) (cons e b) d ad1 ad2 eq with len (cons e b) | eq
  ... | suc n | ()
  mono-unique-c0 (cons e b) (nil y) d ad1 ad2 eq with len (cons e b) | eq
  ... | suc n | ()
  -- cw 方向（头边必 cw01 ✓ 否则 dirOf = ccw ≢ cw ⇒ 空模式 ✓）
  mono-unique-c0 (cons cw01 b) (cons cw01 b') cw (d1 , ad1) (d2 , ad2) eq =
    cons-eq refl (mono-unique-c1 b b' cw ad1 ad2 (suc-inj eq))
  mono-unique-c0 (cons cw01 b) (cons cc04 b') cw (d1 , ad1) (() , ad2) eq
  mono-unique-c0 (cons cc04 b) (cons e' b') cw (() , ad1) (d2 , ad2) eq
  -- ccw 方向（头边必 cc04 ✓）
  mono-unique-c0 (cons cc04 b) (cons cc04 b') ccw (d1 , ad1) (d2 , ad2) eq =
    cons-eq refl (mono-unique-c4 b b' ccw ad1 ad2 (suc-inj eq))
  mono-unique-c0 (cons cc04 b) (cons cw01 b') ccw (d1 , ad1) (() , ad2) eq
  mono-unique-c0 (cons cw01 b) (cons e' b') ccw (() , ad1) (d2 , ad2) eq
  mono-unique-c1 : ∀ {y : C5-vert} (w1 w2 : Walk C5G c1 y) (d : Dir)
    → allDir w1 d → allDir w2 d → len w1 ≡ len w2 → w1 ≡ w2
  mono-unique-c1 (nil x) (nil y) d ad1 ad2 eq = refl
  mono-unique-c1 (nil x) (cons e b) d ad1 ad2 eq with len (cons e b) | eq
  ... | suc n | ()
  mono-unique-c1 (cons e b) (nil y) d ad1 ad2 eq with len (cons e b) | eq
  ... | suc n | ()
  -- cw 方向（头边必 cw12 ✓ 否则 dirOf = ccw ≢ cw ⇒ 空模式 ✓）
  mono-unique-c1 (cons cw12 b) (cons cw12 b') cw (d1 , ad1) (d2 , ad2) eq =
    cons-eq refl (mono-unique-c2 b b' cw ad1 ad2 (suc-inj eq))
  mono-unique-c1 (cons cw12 b) (cons cc10 b') cw (d1 , ad1) (() , ad2) eq
  mono-unique-c1 (cons cc10 b) (cons e' b') cw (() , ad1) (d2 , ad2) eq
  -- ccw 方向（头边必 cc10 ✓）
  mono-unique-c1 (cons cc10 b) (cons cc10 b') ccw (d1 , ad1) (d2 , ad2) eq =
    cons-eq refl (mono-unique-c0 b b' ccw ad1 ad2 (suc-inj eq))
  mono-unique-c1 (cons cc10 b) (cons cw12 b') ccw (d1 , ad1) (() , ad2) eq
  mono-unique-c1 (cons cw12 b) (cons e' b') ccw (() , ad1) (d2 , ad2) eq
  mono-unique-c2 : ∀ {y : C5-vert} (w1 w2 : Walk C5G c2 y) (d : Dir)
    → allDir w1 d → allDir w2 d → len w1 ≡ len w2 → w1 ≡ w2
  mono-unique-c2 (nil x) (nil y) d ad1 ad2 eq = refl
  mono-unique-c2 (nil x) (cons e b) d ad1 ad2 eq with len (cons e b) | eq
  ... | suc n | ()
  mono-unique-c2 (cons e b) (nil y) d ad1 ad2 eq with len (cons e b) | eq
  ... | suc n | ()
  -- cw 方向（头边必 cw23 ✓ 否则 dirOf = ccw ≢ cw ⇒ 空模式 ✓）
  mono-unique-c2 (cons cw23 b) (cons cw23 b') cw (d1 , ad1) (d2 , ad2) eq =
    cons-eq refl (mono-unique-c3 b b' cw ad1 ad2 (suc-inj eq))
  mono-unique-c2 (cons cw23 b) (cons cc21 b') cw (d1 , ad1) (() , ad2) eq
  mono-unique-c2 (cons cc21 b) (cons e' b') cw (() , ad1) (d2 , ad2) eq
  -- ccw 方向（头边必 cc21 ✓）
  mono-unique-c2 (cons cc21 b) (cons cc21 b') ccw (d1 , ad1) (d2 , ad2) eq =
    cons-eq refl (mono-unique-c1 b b' ccw ad1 ad2 (suc-inj eq))
  mono-unique-c2 (cons cc21 b) (cons cw23 b') ccw (d1 , ad1) (() , ad2) eq
  mono-unique-c2 (cons cw23 b) (cons e' b') ccw (() , ad1) (d2 , ad2) eq
  mono-unique-c3 : ∀ {y : C5-vert} (w1 w2 : Walk C5G c3 y) (d : Dir)
    → allDir w1 d → allDir w2 d → len w1 ≡ len w2 → w1 ≡ w2
  mono-unique-c3 (nil x) (nil y) d ad1 ad2 eq = refl
  mono-unique-c3 (nil x) (cons e b) d ad1 ad2 eq with len (cons e b) | eq
  ... | suc n | ()
  mono-unique-c3 (cons e b) (nil y) d ad1 ad2 eq with len (cons e b) | eq
  ... | suc n | ()
  -- cw 方向（头边必 cw34 ✓ 否则 dirOf = ccw ≢ cw ⇒ 空模式 ✓）
  mono-unique-c3 (cons cw34 b) (cons cw34 b') cw (d1 , ad1) (d2 , ad2) eq =
    cons-eq refl (mono-unique-c4 b b' cw ad1 ad2 (suc-inj eq))
  mono-unique-c3 (cons cw34 b) (cons cc32 b') cw (d1 , ad1) (() , ad2) eq
  mono-unique-c3 (cons cc32 b) (cons e' b') cw (() , ad1) (d2 , ad2) eq
  -- ccw 方向（头边必 cc32 ✓）
  mono-unique-c3 (cons cc32 b) (cons cc32 b') ccw (d1 , ad1) (d2 , ad2) eq =
    cons-eq refl (mono-unique-c2 b b' ccw ad1 ad2 (suc-inj eq))
  mono-unique-c3 (cons cc32 b) (cons cw34 b') ccw (d1 , ad1) (() , ad2) eq
  mono-unique-c3 (cons cw34 b) (cons e' b') ccw (() , ad1) (d2 , ad2) eq
  mono-unique-c4 : ∀ {y : C5-vert} (w1 w2 : Walk C5G c4 y) (d : Dir)
    → allDir w1 d → allDir w2 d → len w1 ≡ len w2 → w1 ≡ w2
  mono-unique-c4 (nil x) (nil y) d ad1 ad2 eq = refl
  mono-unique-c4 (nil x) (cons e b) d ad1 ad2 eq with len (cons e b) | eq
  ... | suc n | ()
  mono-unique-c4 (cons e b) (nil y) d ad1 ad2 eq with len (cons e b) | eq
  ... | suc n | ()
  -- cw 方向（头边必 cw40 ✓ 否则 dirOf = ccw ≢ cw ⇒ 空模式 ✓）
  mono-unique-c4 (cons cw40 b) (cons cw40 b') cw (d1 , ad1) (d2 , ad2) eq =
    cons-eq refl (mono-unique-c0 b b' cw ad1 ad2 (suc-inj eq))
  mono-unique-c4 (cons cw40 b) (cons cc43 b') cw (d1 , ad1) (() , ad2) eq
  mono-unique-c4 (cons cc43 b) (cons e' b') cw (() , ad1) (d2 , ad2) eq
  -- ccw 方向（头边必 cc43 ✓）
  mono-unique-c4 (cons cc43 b) (cons cc43 b') ccw (d1 , ad1) (d2 , ad2) eq =
    cons-eq refl (mono-unique-c3 b b' ccw ad1 ad2 (suc-inj eq))
  mono-unique-c4 (cons cc43 b) (cons cw40 b') ccw (d1 , ad1) (() , ad2) eq
  mono-unique-c4 (cons cw40 b) (cons e' b') ccw (() , ad1) (d2 , ad2) eq

mono-unique : ∀ {x y : C5-vert} (w1 w2 : Walk C5G x y) (d : Dir)
  → allDir w1 d → allDir w2 d → len w1 ≡ len w2 → w1 ≡ w2
mono-unique {x = c0} = mono-unique-c0
mono-unique {x = c1} = mono-unique-c1
mono-unique {x = c2} = mono-unique-c2
mono-unique {x = c3} = mono-unique-c3
mono-unique {x = c4} = mono-unique-c4

--------------------------------------------------------------------------------
-- ① ℤ 单射/相斥（自证 ✓ 不猜 stdlib 名）
--------------------------------------------------------------------------------

pos-inj : ∀ {m n : ℕ} → + m ≡ + n → m ≡ n
pos-inj {zero} {zero} p = refl
pos-inj {zero} {suc n} ()
pos-inj {suc m} {zero} ()
pos-inj {suc m} {suc n} refl = refl

neg-inj : ∀ {m n : ℕ} → - (+ m) ≡ - (+ n) → m ≡ n
neg-inj {zero} {zero} p = refl
neg-inj {zero} {suc n} ()
neg-inj {suc m} {zero} ()
neg-inj {suc m} {suc n} refl = refl

swap× : ∀ {a b : ℕ} → (a ≡ zero) × (b ≡ zero) → (b ≡ zero) × (a ≡ zero)
swap× (p , q) = q , p

pos-neq-neg : ∀ {m n : ℕ} → + m ≡ - (+ n) → (m ≡ zero) × (n ≡ zero)
pos-neq-neg {zero} {zero} p = refl , refl
pos-neq-neg {zero} {suc n} ()
pos-neq-neg {suc m} {zero} ()
pos-neq-neg {suc m} {suc n} ()

--------------------------------------------------------------------------------
-- ② 零长相等（逐顶点具体化 ✓ 避 K 禁用对角墙 ✗ 先例 _PN4:310 ✓）
--------------------------------------------------------------------------------

len-zero-eq-c0 : (w1 w2 : Walk C5G c0 c0)
  → len w1 ≡ zero → len w2 ≡ zero → w1 ≡ w2
len-zero-eq-c0 (nil x) (nil y) p q = refl
len-zero-eq-c0 (nil x) (cons e b) p ()
len-zero-eq-c0 (cons e b) w2 () q
len-zero-eq-c1 : (w1 w2 : Walk C5G c1 c1)
  → len w1 ≡ zero → len w2 ≡ zero → w1 ≡ w2
len-zero-eq-c1 (nil x) (nil y) p q = refl
len-zero-eq-c1 (nil x) (cons e b) p ()
len-zero-eq-c1 (cons e b) w2 () q
len-zero-eq-c2 : (w1 w2 : Walk C5G c2 c2)
  → len w1 ≡ zero → len w2 ≡ zero → w1 ≡ w2
len-zero-eq-c2 (nil x) (nil y) p q = refl
len-zero-eq-c2 (nil x) (cons e b) p ()
len-zero-eq-c2 (cons e b) w2 () q
len-zero-eq-c3 : (w1 w2 : Walk C5G c3 c3)
  → len w1 ≡ zero → len w2 ≡ zero → w1 ≡ w2
len-zero-eq-c3 (nil x) (nil y) p q = refl
len-zero-eq-c3 (nil x) (cons e b) p ()
len-zero-eq-c3 (cons e b) w2 () q
len-zero-eq-c4 : (w1 w2 : Walk C5G c4 c4)
  → len w1 ≡ zero → len w2 ≡ zero → w1 ≡ w2
len-zero-eq-c4 (nil x) (nil y) p q = refl
len-zero-eq-c4 (nil x) (cons e b) p ()
len-zero-eq-c4 (cons e b) w2 () q

len-zero-eq : (x : C5-vert) (w1 w2 : Walk C5G x x)
  → len w1 ≡ zero → len w2 ≡ zero → w1 ≡ w2
len-zero-eq c0 = len-zero-eq-c0
len-zero-eq c1 = len-zero-eq-c1
len-zero-eq c2 = len-zero-eq-c2
len-zero-eq c3 = len-zero-eq-c3
len-zero-eq c4 = len-zero-eq-c4

--------------------------------------------------------------------------------
-- ③ 对称传递闭包 AHs + 音性 ⟹
--------------------------------------------------------------------------------

data AHs : ∀ {u v : C5-vert} → Walk C5G u v → Walk C5G u v → Set where
  rfls : ∀ {u v} (w : Walk C5G u v) → AHs w w
  steps : ∀ {u v} {w1 w2 : Walk C5G u v} → AStepStd C5G w1 w2 → AHs w1 w2
  syms : ∀ {u v} {w1 w2 : Walk C5G u v} → AHs w1 w2 → AHs w2 w1
  transs : ∀ {u v} {w1 w2 w3 : Walk C5G u v} → AHs w1 w2 → AHs w2 w3 → AHs w1 w3

eqs→AHs : ∀ {u v : C5-vert} {w1 w2 : Walk C5G u v} → w1 ≡ w2 → AHs w1 w2
eqs→AHs refl = rfls _

AH*-to-AHs : ∀ {u v : C5-vert} {w1 w2 : Walk C5G u v} → AH* w1 w2 → AHs w1 w2
AH*-to-AHs (rfl* w) = rfls w
AH*-to-AHs (step* s h) = transs (steps s) (AH*-to-AHs h)

class-sound : ∀ {u v : C5-vert} {w1 w2 : Walk C5G u v}
  → AHs w1 w2 → windE w1 ≡ windE w2
class-sound (rfls w) = refl
class-sound (steps s) = AStepStd-wind s
class-sound (syms h) = sym (class-sound h)
class-sound (transs h1 h2) = trans (class-sound h1) (class-sound h2)

--------------------------------------------------------------------------------
-- ④ ★★ 类判据 ⟸：绕数相等 ⇒ 同类 ✓（方向分派 helper ✓ 参数位模式避 with ✗）
--------------------------------------------------------------------------------

class-dir : (x : C5-vert) (nf1 nf2 : Walk C5G x x) (d1 d2 : Dir)
  → allDir nf1 d1 → allDir nf2 d2 → windE nf1 ≡ windE nf2 → AHs nf1 nf2
-- 双 cw：ℤ 正部单射 ⇒ 长度相等 ⇒ 双向唯一 ✓
class-dir x nf1 nf2 cw cw ad1 ad2 eq =
  eqs→AHs (mono-unique nf1 nf2 cw ad1 ad2 (pos-inj w-eq))
  where
    w-eq : + len nf1 ≡ + len nf2
    w-eq = trans (sym (wind-cw-len nf1 ad1)) (trans eq (wind-cw-len nf2 ad2))
-- 双 ccw：ℤ 负部单射 ✓
class-dir x nf1 nf2 ccw ccw ad1 ad2 eq =
  eqs→AHs (mono-unique nf1 nf2 ccw ad1 ad2 (neg-inj w-eq))
  where
    w-eq : - (+ len nf1) ≡ - (+ len nf2)
    w-eq = trans (sym (wind-ccw-neg-len nf1 ad1)) (trans eq (wind-ccw-neg-len nf2 ad2))
-- 混合：绕数相斥 ⇒ 双方长度 0 ⇒ 零长相等 ✓
class-dir x nf1 nf2 cw ccw ad1 ad2 eq =
  eqs→AHs (len-zero-eq x nf1 nf2 (proj₁ p) (proj₂ p))
  where
    w-eq : + len nf1 ≡ - (+ len nf2)
    w-eq = trans (sym (wind-cw-len nf1 ad1)) (trans eq (wind-ccw-neg-len nf2 ad2))
    p : (len nf1 ≡ zero) × (len nf2 ≡ zero)
    p = pos-neq-neg w-eq
class-dir x nf1 nf2 ccw cw ad1 ad2 eq =
  eqs→AHs (len-zero-eq x nf1 nf2 (proj₁ p) (proj₂ p))
  where
    w-eq : - (+ len nf1) ≡ + len nf2
    w-eq = trans (sym (wind-ccw-neg-len nf1 ad1)) (trans eq (wind-cw-len nf2 ad2))
    p : (len nf1 ≡ zero) × (len nf2 ≡ zero)
    p = swap× (pos-neq-neg (sym w-eq))

-- 组合：正规形 + 方向 + 拼接 ✓
class-aux : (x : C5-vert) (w1 w2 : Walk C5G x x)
  → Σ (Walk C5G x x) (λ nf1 → btFree nf1 × AH* w1 nf1)
  → Σ (Walk C5G x x) (λ nf2 → btFree nf2 × AH* w2 nf2)
  → windE w1 ≡ windE w2 → AHs w1 w2
class-aux x w1 w2 (nf1 , bf1 , h1) (nf2 , bf2 , h2) eq =
  transs (AH*-to-AHs h1)
    (transs (class-dir x nf1 nf2 d1 d2 ad1 ad2 nf-eq)
            (syms (AH*-to-AHs h2)))
  where
    d1 = proj₁ (btFree-monotone nf1 bf1)
    ad1 = proj₂ (btFree-monotone nf1 bf1)
    d2 = proj₁ (btFree-monotone nf2 bf2)
    ad2 = proj₂ (btFree-monotone nf2 bf2)
    nf-eq : windE nf1 ≡ windE nf2
    nf-eq = trans (sym (class-sound (AH*-to-AHs h1)))
                  (trans eq (class-sound (AH*-to-AHs h2)))

class-complete : (x : C5-vert) (w1 w2 : Walk C5G x x)
  → windE w1 ≡ windE w2 → AHs w1 w2
class-complete x w1 w2 eq = class-aux x w1 w2 (nf-exists w1) (nf-exists w2) eq
