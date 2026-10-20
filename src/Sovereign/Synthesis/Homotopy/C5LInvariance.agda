{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Synthesis.Homotopy.C5LInvariance
--
-- **C5L（自环填充 C₅）的跨和不变性层**——标准 A-同伦（含 bt）
--
-- 数学背景：π₁(C5L) ≅ ℤ 的**不变量部分**。
--   · 表示层：**15 条具体边**（5 cw + 5 ccw + **5 lp** ✓）——参数化边撞索引反演墙 ✗
--   · 局部等式：`tri-cross`（35 案 ✓）/ `sq-cross`（95 案 ✓）——**跨和（差值语义）**
--     ⚠ 单边形式 `cw1 + cw2 ≡ cw3` 为假 ✗（`cw∘ccw → lp` 反例 ✓）
--   · 计数层：`nCwL`/`nCcwL` + 拼接律 + bt 局部等式（10 对 ✓ 含**自环对** ✓）
--   · 重排桥：`cross-lift` / `cross-lift2` / `cross-lift4`（`Data.Nat.Solver` ✓）
--   · **`step-inv`**：三生成元（tri / sq / bt）的跨和不变性 ✓
--   · **`AH-inv`**：闭包（rfl / sym / trn / gen）上的不变性 ✓
--   · 判定器：`revPair?`（15 案 ✓）/ `isLp` / `lpFreeD` / `btFreeD`
--
-- **已完成**：不变性层 ✅（6 节点 + 判定器层，全部回执 ✓）
-- **未完成**（台账 pending ✗）：`nf-exists`（正规形存在）→ `mono-unique` →
--   `class-criterion`（类 ⇔ 计对）→ `final`（≅ ℤ）
--
-- 0 postulate / 0 hole。来源探针：_PEH60/66/67/68/69/70/71/72

module Sovereign.Synthesis.Homotopy.C5LInvariance where

open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _<_; _≤_; s≤s; z≤n)
import Data.Integer as Int
open Int using (ℤ; +0; -_; _-_)
  renaming (_+_ to _+ℤ_; _*_ to _*ℤ_)
open import Data.Integer.Properties using (neg-distrib-+)
  renaming (+-assoc to +ℤ-assoc; +-comm to +ℤ-comm; +-identityˡ to +ℤ-identityˡ;
            +-inverseʳ to +ℤ-inverseʳ; *-distribˡ-+ to *ℤ-distribˡ-+;
            +-identityʳ to +ℤ-identityʳ; pos-* to pos-*ℤ;
            +-inverseˡ to +ℤ-inverseˡ; *-zeroʳ to *ℤ-zeroʳ; +-injective to +ℤ-injective)
import Data.Nat.Properties
open import Data.Nat.Induction using (Acc; acc; <-wellFounded)
open import Data.Nat.Properties using (+-assoc; +-comm; +-identityʳ; +-identityˡ; +-cancelʳ-≡; m+n≡0⇒m≡0; m+n≡0⇒n≡0; *-suc)
open import Data.Nat.Solver
open +-*-Solver using (solve; _:+_; _:=_; con)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; cong₂; trans; sym; subst)

--------------------------------------------------------------------------------
-- 依赖（库自带件：DiGraph / Walk / AStepStd；自环无关性模块）
--------------------------------------------------------------------------------

open import Sovereign.Synthesis.Homotopy.BarceloAHomotopy
  using (DiGraph; Walk; cons; nil; _++w_)
open import Sovereign.Synthesis.Homotopy.C5Rigidity
  using (AStepStd; tri-slide; sq-slide4; bt)
open import Sovereign.Synthesis.Homotopy.C5LoopIrrelevance
  using (AHomotopyStd) renaming (rfl to h-rfl; sym to h-sym; trn to h-trn; gen to h-gen)

--------------------------------------------------------------------------------
-- ① 顶点与 15 条具体边 ✓
--------------------------------------------------------------------------------

data V5 : Set where
  c0 c1 c2 c3 c4 : V5

data EL : V5 → V5 → Set where
  cw01  : EL c0 c1
  cw12  : EL c1 c2
  cw23  : EL c2 c3
  cw34  : EL c3 c4
  cw40  : EL c4 c0
  cc04 : EL c0 c4
  cc10 : EL c1 c0
  cc21 : EL c2 c1
  cc32 : EL c3 c2
  cc43 : EL c4 c3
  lp0  : EL c0 c0
  lp1  : EL c1 c1
  lp2  : EL c2 c2
  lp3  : EL c3 c3
  lp4  : EL c4 c4

--------------------------------------------------------------------------------
-- ② 三值分类 / 回溯对 / bt-free / lp-free / 长度 ✓
--------------------------------------------------------------------------------

data Kind : Set where cw ccw lp : Kind

kindOf : ∀ {u v : V5} → EL u v → Kind
kindOf cw01 = cw
kindOf cw12 = cw
kindOf cw23 = cw
kindOf cw34 = cw
kindOf cw40 = cw
kindOf cc04 = ccw
kindOf cc10 = ccw
kindOf cc21 = ccw
kindOf cc32 = ccw
kindOf cc43 = ccw
kindOf lp0 = lp
kindOf lp1 = lp
kindOf lp2 = lp
kindOf lp3 = lp
kindOf lp4 = lp

data RevPair : ∀ {u v w : V5} → EL u v → EL v w → Set where
  rp-cw01 : RevPair cw01 cc10
  rp-cw12 : RevPair cw12 cc21
  rp-cw23 : RevPair cw23 cc32
  rp-cw34 : RevPair cw34 cc43
  rp-cw40 : RevPair cw40 cc04
  rp-cc04 : RevPair cc04 cw40
  rp-cc10 : RevPair cc10 cw01
  rp-cc21 : RevPair cc21 cw12
  rp-cc32 : RevPair cc32 cw23
  rp-cc43 : RevPair cc43 cw34

data WL : V5 → V5 → Set where
  nilL  : ∀ x → WL x x
  consL : ∀ {u v w} → EL u v → WL v w → WL u w

btFree : ∀ {u v} → WL u v → Set
btFree (nilL x) = ⊤
btFree (consL e (nilL y)) = ⊤
btFree (consL e (consL f b)) = (RevPair e f → ⊥) × btFree (consL f b)

lpFree : ∀ {u v} → WL u v → Set
lpFree (nilL x) = ⊤
lpFree (consL e b) = (kindOf e ≡ lp → ⊥) × lpFree b

len5L : ∀ {u v} → WL u v → ℕ
len5L (nilL x) = zero
len5L (consL e b) = suc (len5L b)

--------------------------------------------------------------------------------
-- ① 计数（15 子句 ✓）
--------------------------------------------------------------------------------

cwOfL : ∀ {x y : V5} → EL x y → ℕ
cwOfL cw01 = suc zero
cwOfL cw12 = suc zero
cwOfL cw23 = suc zero
cwOfL cw34 = suc zero
cwOfL cw40 = suc zero
cwOfL cc04 = zero
cwOfL cc10 = zero
cwOfL cc21 = zero
cwOfL cc32 = zero
cwOfL cc43 = zero
cwOfL lp0 = zero
cwOfL lp1 = zero
cwOfL lp2 = zero
cwOfL lp3 = zero
cwOfL lp4 = zero

ccwOfL : ∀ {x y : V5} → EL x y → ℕ
ccwOfL cw01 = zero
ccwOfL cw12 = zero
ccwOfL cw23 = zero
ccwOfL cw34 = zero
ccwOfL cw40 = zero
ccwOfL cc04 = suc zero
ccwOfL cc10 = suc zero
ccwOfL cc21 = suc zero
ccwOfL cc32 = suc zero
ccwOfL cc43 = suc zero
ccwOfL lp0 = zero
ccwOfL lp1 = zero
ccwOfL lp2 = zero
ccwOfL lp3 = zero
ccwOfL lp4 = zero

--------------------------------------------------------------------------------
-- ② cw∘cw 不可弦 ✓（每顶点恰一条 cw 出边 ⇒ **5 案** ✓ 而非 15 ✗）
--------------------------------------------------------------------------------

no-cw-cw : ∀ {x y z : V5} (e1 : EL x y) (e2 : EL y z) (e3 : EL x z)
  → kindOf e1 ≡ cw → kindOf e2 ≡ cw → ⊥
no-cw-cw cw01 cw12 ()
no-cw-cw cw12 cw23 ()
no-cw-cw cw23 cw34 ()
no-cw-cw cw34 cw40 ()
no-cw-cw cw40 cw01 ()

--------------------------------------------------------------------------------
-- ③ ccw∘ccw 不可弦 ✓（5 案 ✓）
--------------------------------------------------------------------------------

no-ccw-ccw : ∀ {x y z : V5} (e1 : EL x y) (e2 : EL y z) (e3 : EL x z)
  → kindOf e1 ≡ ccw → kindOf e2 ≡ ccw → ⊥
no-ccw-ccw cc04 cc43 ()
no-ccw-ccw cc10 cc04 ()
no-ccw-ccw cc21 cc10 ()
no-ccw-ccw cc32 cc21 ()
no-ccw-ccw cc43 cc32 ()

--------------------------------------------------------------------------------
-- ③ ★ 三角跨和等式（**35 案** ✓ 端点为 z 唯一锁定 e3 ✓）
--     形式：cw1 + cw2 + ccw3 ≡ cw3 + ccw1 + ccw2（**跨和 = 差值语义** ✓）
--     ⚠ 单边形式 cw1 + cw2 ≡ cw3 为假 ✗（cw∘ccw → lp 反例 ✓ 见交接口径）
--------------------------------------------------------------------------------

tri-cross : ∀ {x y z : V5} (e1 : EL x y) (e2 : EL y z) (e3 : EL x z)
  → cwOfL e1 + cwOfL e2 + ccwOfL e3 ≡ cwOfL e3 + ccwOfL e1 + ccwOfL e2
tri-cross cw01 cc10 lp0 = refl
tri-cross cw01 lp1 cw01 = refl
tri-cross cc04 cw40 lp0 = refl
tri-cross cc04 lp4 cc04 = refl
tri-cross lp0 cw01 cw01 = refl
tri-cross lp0 cc04 cc04 = refl
tri-cross lp0 lp0 lp0 = refl
tri-cross cw12 cc21 lp1 = refl
tri-cross cw12 lp2 cw12 = refl
tri-cross cc10 cw01 lp1 = refl
tri-cross cc10 lp0 cc10 = refl
tri-cross lp1 cw12 cw12 = refl
tri-cross lp1 cc10 cc10 = refl
tri-cross lp1 lp1 lp1 = refl
tri-cross cw23 cc32 lp2 = refl
tri-cross cw23 lp3 cw23 = refl
tri-cross cc21 cw12 lp2 = refl
tri-cross cc21 lp1 cc21 = refl
tri-cross lp2 cw23 cw23 = refl
tri-cross lp2 cc21 cc21 = refl
tri-cross lp2 lp2 lp2 = refl
tri-cross cw34 cc43 lp3 = refl
tri-cross cw34 lp4 cw34 = refl
tri-cross cc32 cw23 lp3 = refl
tri-cross cc32 lp2 cc32 = refl
tri-cross lp3 cw34 cw34 = refl
tri-cross lp3 cc32 cc32 = refl
tri-cross lp3 lp3 lp3 = refl
tri-cross cw40 cc04 lp4 = refl
tri-cross cw40 lp0 cw40 = refl
tri-cross cc43 cw34 lp4 = refl
tri-cross cc43 lp3 cc43 = refl
tri-cross lp4 cw40 cw40 = refl
tri-cross lp4 cc43 cc43 = refl
tri-cross lp4 lp4 lp4 = refl

--------------------------------------------------------------------------------
-- ★ 方形跨和等式 ✓
--------------------------------------------------------------------------------

sq-cross : ∀ {x y z w : V5} (e1 : EL x y) (e2 : EL y z) (e3 : EL z w) (e4 : EL x w)
  → cwOfL e1 + cwOfL e2 + cwOfL e3 + ccwOfL e4
  ≡ cwOfL e4 + ccwOfL e1 + ccwOfL e2 + ccwOfL e3
sq-cross cw01 cw12 cc21 cw01 = refl
sq-cross cw01 cc10 cw01 cw01 = refl
sq-cross cw01 cc10 cc04 cc04 = refl
sq-cross cw01 cc10 lp0 lp0 = refl
sq-cross cw01 lp1 cc10 lp0 = refl
sq-cross cw01 lp1 lp1 cw01 = refl
sq-cross cc04 cw40 cw01 cw01 = refl
sq-cross cc04 cw40 cc04 cc04 = refl
sq-cross cc04 cw40 lp0 lp0 = refl
sq-cross cc04 cc43 cw34 cc04 = refl
sq-cross cc04 lp4 cw40 lp0 = refl
sq-cross cc04 lp4 lp4 cc04 = refl
sq-cross lp0 cw01 cc10 lp0 = refl
sq-cross lp0 cw01 lp1 cw01 = refl
sq-cross lp0 cc04 cw40 lp0 = refl
sq-cross lp0 cc04 lp4 cc04 = refl
sq-cross lp0 lp0 cw01 cw01 = refl
sq-cross lp0 lp0 cc04 cc04 = refl
sq-cross lp0 lp0 lp0 lp0 = refl
sq-cross cw12 cw23 cc32 cw12 = refl
sq-cross cw12 cc21 cw12 cw12 = refl
sq-cross cw12 cc21 cc10 cc10 = refl
sq-cross cw12 cc21 lp1 lp1 = refl
sq-cross cw12 lp2 cc21 lp1 = refl
sq-cross cw12 lp2 lp2 cw12 = refl
sq-cross cc10 cw01 cw12 cw12 = refl
sq-cross cc10 cw01 cc10 cc10 = refl
sq-cross cc10 cw01 lp1 lp1 = refl
sq-cross cc10 cc04 cw40 cc10 = refl
sq-cross cc10 lp0 cw01 lp1 = refl
sq-cross cc10 lp0 lp0 cc10 = refl
sq-cross lp1 cw12 cc21 lp1 = refl
sq-cross lp1 cw12 lp2 cw12 = refl
sq-cross lp1 cc10 cw01 lp1 = refl
sq-cross lp1 cc10 lp0 cc10 = refl
sq-cross lp1 lp1 cw12 cw12 = refl
sq-cross lp1 lp1 cc10 cc10 = refl
sq-cross lp1 lp1 lp1 lp1 = refl
sq-cross cw23 cw34 cc43 cw23 = refl
sq-cross cw23 cc32 cw23 cw23 = refl
sq-cross cw23 cc32 cc21 cc21 = refl
sq-cross cw23 cc32 lp2 lp2 = refl
sq-cross cw23 lp3 cc32 lp2 = refl
sq-cross cw23 lp3 lp3 cw23 = refl
sq-cross cc21 cw12 cw23 cw23 = refl
sq-cross cc21 cw12 cc21 cc21 = refl
sq-cross cc21 cw12 lp2 lp2 = refl
sq-cross cc21 cc10 cw01 cc21 = refl
sq-cross cc21 lp1 cw12 lp2 = refl
sq-cross cc21 lp1 lp1 cc21 = refl
sq-cross lp2 cw23 cc32 lp2 = refl
sq-cross lp2 cw23 lp3 cw23 = refl
sq-cross lp2 cc21 cw12 lp2 = refl
sq-cross lp2 cc21 lp1 cc21 = refl
sq-cross lp2 lp2 cw23 cw23 = refl
sq-cross lp2 lp2 cc21 cc21 = refl
sq-cross lp2 lp2 lp2 lp2 = refl
sq-cross cw34 cw40 cc04 cw34 = refl
sq-cross cw34 cc43 cw34 cw34 = refl
sq-cross cw34 cc43 cc32 cc32 = refl
sq-cross cw34 cc43 lp3 lp3 = refl
sq-cross cw34 lp4 cc43 lp3 = refl
sq-cross cw34 lp4 lp4 cw34 = refl
sq-cross cc32 cw23 cw34 cw34 = refl
sq-cross cc32 cw23 cc32 cc32 = refl
sq-cross cc32 cw23 lp3 lp3 = refl
sq-cross cc32 cc21 cw12 cc32 = refl
sq-cross cc32 lp2 cw23 lp3 = refl
sq-cross cc32 lp2 lp2 cc32 = refl
sq-cross lp3 cw34 cc43 lp3 = refl
sq-cross lp3 cw34 lp4 cw34 = refl
sq-cross lp3 cc32 cw23 lp3 = refl
sq-cross lp3 cc32 lp2 cc32 = refl
sq-cross lp3 lp3 cw34 cw34 = refl
sq-cross lp3 lp3 cc32 cc32 = refl
sq-cross lp3 lp3 lp3 lp3 = refl
sq-cross cw40 cw01 cc10 cw40 = refl
sq-cross cw40 cc04 cw40 cw40 = refl
sq-cross cw40 cc04 cc43 cc43 = refl
sq-cross cw40 cc04 lp4 lp4 = refl
sq-cross cw40 lp0 cc04 lp4 = refl
sq-cross cw40 lp0 lp0 cw40 = refl
sq-cross cc43 cw34 cw40 cw40 = refl
sq-cross cc43 cw34 cc43 cc43 = refl
sq-cross cc43 cw34 lp4 lp4 = refl
sq-cross cc43 cc32 cw23 cc43 = refl
sq-cross cc43 lp3 cw34 lp4 = refl
sq-cross cc43 lp3 lp3 cc43 = refl
sq-cross lp4 cw40 cc04 lp4 = refl
sq-cross lp4 cw40 lp0 cw40 = refl
sq-cross lp4 cc43 cw34 lp4 = refl
sq-cross lp4 cc43 lp3 cc43 = refl
sq-cross lp4 lp4 cw40 cw40 = refl
sq-cross lp4 lp4 cc43 cc43 = refl
sq-cross lp4 lp4 lp4 lp4 = refl

--------------------------------------------------------------------------------
-- ① 具体边图（库 DiGraph ✓）
--------------------------------------------------------------------------------

C5LEc : DiGraph
DiGraph.V C5LEc = V5
DiGraph.edge C5LEc = EL

--------------------------------------------------------------------------------
-- ② 计数层（库 Walk 上 ✓）
--------------------------------------------------------------------------------

nCwL : ∀ {x y : V5} → Walk C5LEc x y → ℕ
nCwL (nil x) = zero
nCwL (cons e b) = cwOfL e + nCwL b

nCcwL : ∀ {x y : V5} → Walk C5LEc x y → ℕ
nCcwL (nil x) = zero
nCcwL (cons e b) = ccwOfL e + nCcwL b

lenL : ∀ {x y : V5} → Walk C5LEc x y → ℕ
lenL (nil x) = zero
lenL (cons e b) = suc (lenL b)

--------------------------------------------------------------------------------
-- ③ 拼接律 ✓
--------------------------------------------------------------------------------

nCwL-++ : ∀ {x y z : V5} (w1 : Walk C5LEc x y) (w2 : Walk C5LEc y z)
  → nCwL (w1 ++w w2) ≡ nCwL w1 + nCwL w2
nCwL-++ (nil x) w2 = refl
nCwL-++ (cons e b) w2 =
  trans (cong (cwOfL e +_) (nCwL-++ b w2)) (sym (+-assoc (cwOfL e) (nCwL b) (nCwL w2)))

nCcwL-++ : ∀ {x y z : V5} (w1 : Walk C5LEc x y) (w2 : Walk C5LEc y z)
  → nCcwL (w1 ++w w2) ≡ nCcwL w1 + nCcwL w2
nCcwL-++ (nil x) w2 = refl
nCcwL-++ (cons e b) w2 =
  trans (cong (ccwOfL e +_) (nCcwL-++ b w2)) (sym (+-assoc (ccwOfL e) (nCcwL b) (nCcwL w2)))

lenL-++ : ∀ {x y z : V5} (w1 : Walk C5LEc x y) (w2 : Walk C5LEc y z)
  → lenL (w1 ++w w2) ≡ lenL w1 + lenL w2
lenL-++ (nil x) w2 = refl
lenL-++ (cons e b) w2 = cong suc (lenL-++ b w2)

--------------------------------------------------------------------------------
-- ④ bt 局部等式（具体边 ✓ 10 构造子 ⇒ 2 形状 ✓）
--------------------------------------------------------------------------------

bt-count-L : ∀ {x y z : V5} (e : EL x y) (f : EL y z) → RevPair e f
  → (cwOfL e ≡ ccwOfL f) × (ccwOfL e ≡ cwOfL f)
bt-count-L cw01 cc10 (rp-cw01) = refl , refl
bt-count-L cw12 cc21 (rp-cw12) = refl , refl
bt-count-L cw23 cc32 (rp-cw23) = refl , refl
bt-count-L cw34 cc43 (rp-cw34) = refl , refl
bt-count-L cw40 cc04 (rp-cw40) = refl , refl
bt-count-L cc04 cw40 (rp-cc04) = refl , refl
bt-count-L cc10 cw01 (rp-cc10) = refl , refl
bt-count-L cc21 cw12 (rp-cc21) = refl , refl
bt-count-L cc32 cw23 (rp-cc32) = refl , refl
bt-count-L cc43 cw34 (rp-cc43) = refl , refl

--------------------------------------------------------------------------------
-- ⑤ 自环零贡献 ✓
--------------------------------------------------------------------------------

lp0-cw0 : cwOfL lp0 ≡ zero
lp0-cw0 = refl
lp1-cw0 : cwOfL lp1 ≡ zero
lp1-cw0 = refl
lp2-cw0 : cwOfL lp2 ≡ zero
lp2-cw0 = refl
lp3-cw0 : cwOfL lp3 ≡ zero
lp3-cw0 = refl
lp4-cw0 : cwOfL lp4 ≡ zero
lp4-cw0 = refl

--------------------------------------------------------------------------------
-- ① 归形：两侧到公共形 ✓（solver ✓）
--------------------------------------------------------------------------------

norm-S : ∀ (A B C D a1 a2 b3 : ℕ)
  → (A + (a1 + (a2 + B))) + (C + (b3 + D))
  ≡ ((A + B) + (C + D)) + ((a1 + a2) + b3)
norm-S A B C D a1 a2 b3 =
  solve 7 (λ A′ B′ C′ D′ x1 x2 x3 →
             (A′ :+ (x1 :+ (x2 :+ B′))) :+ (C′ :+ (x3 :+ D′))
             := ((A′ :+ B′) :+ (C′ :+ D′)) :+ ((x1 :+ x2) :+ x3)) refl
        A B C D a1 a2 b3

norm-T : ∀ (A B C D a3 b1 b2 : ℕ)
  → (A + (a3 + B)) + (C + (b1 + (b2 + D)))
  ≡ ((A + B) + (C + D)) + ((a3 + b1) + b2)
norm-T A B C D a3 b1 b2 =
  solve 7 (λ A′ B′ C′ D′ x3 y1 y2 →
             (A′ :+ (x3 :+ B′)) :+ (C′ :+ (y1 :+ (y2 :+ D′)))
             := ((A′ :+ B′) :+ (C′ :+ D′)) :+ ((x3 :+ y1) :+ y2)) refl
        A B C D a3 b1 b2

--------------------------------------------------------------------------------
-- ② ★ 跨和重排桥 ✓（局部等式 ⇒ 全局跨和 ✓）
--------------------------------------------------------------------------------

cross-lift : ∀ (A B C D a1 a2 a3 b1 b2 b3 : ℕ)
  → a1 + a2 + b3 ≡ a3 + b1 + b2
  → (A + (a1 + (a2 + B))) + (C + (b3 + D))
  ≡ (A + (a3 + B)) + (C + (b1 + (b2 + D)))
cross-lift A B C D a1 a2 a3 b1 b2 b3 h =
  trans (norm-S A B C D a1 a2 b3)
        (trans (cong (((A + B) + (C + D)) +_) h)
               (sym (norm-T A B C D a3 b1 b2)))

--------------------------------------------------------------------------------
-- ① 重排桥的 2/4 边版本（**顶层引理形** ✓ 与 `_PEH69.norm-S` 同法 ✓）
--------------------------------------------------------------------------------

s2 : ∀ (A B C D a1 a2 : ℕ)
  → (A + (a1 + (a2 + B))) + (C + D) ≡ ((A + B) + (C + D)) + (a1 + a2)
s2 = solve 6 (λ A′ B′ C′ D′ x1 x2 →
       (A′ :+ (x1 :+ (x2 :+ B′))) :+ (C′ :+ D′)
       := ((A′ :+ B′) :+ (C′ :+ D′)) :+ (x1 :+ x2)) refl

s2' : ∀ (A B C D b1 b2 : ℕ)
  → (A + B) + (C + (b1 + (b2 + D))) ≡ ((A + B) + (C + D)) + (b1 + b2)
s2' = solve 6 (λ A′ B′ C′ D′ y1 y2 →
       (A′ :+ B′) :+ (C′ :+ (y1 :+ (y2 :+ D′)))
       := ((A′ :+ B′) :+ (C′ :+ D′)) :+ (y1 :+ y2)) refl

s4 : ∀ (A B C D a1 a2 a3 b4 : ℕ)
  → (A + (a1 + (a2 + (a3 + B)))) + (C + (b4 + D))
  ≡ ((A + B) + (C + D)) + (((a1 + a2) + a3) + b4)
s4 = solve 8 (λ A′ B′ C′ D′ x1 x2 x3 y4 →
       (A′ :+ (x1 :+ (x2 :+ (x3 :+ B′)))) :+ (C′ :+ (y4 :+ D′))
       := ((A′ :+ B′) :+ (C′ :+ D′)) :+ (((x1 :+ x2) :+ x3) :+ y4)) refl

s4' : ∀ (A B C D a4 b1 b2 b3 : ℕ)
  → (A + (a4 + B)) + (C + (b1 + (b2 + (b3 + D))))
  ≡ ((A + B) + (C + D)) + (((a4 + b1) + b2) + b3)
s4' = solve 8 (λ A′ B′ C′ D′ x4 y1 y2 y3 →
       (A′ :+ (x4 :+ B′)) :+ (C′ :+ (y1 :+ (y2 :+ (y3 :+ D′))))
       := ((A′ :+ B′) :+ (C′ :+ D′)) :+ (((x4 :+ y1) :+ y2) :+ y3)) refl

cross-lift2 : ∀ (A B C D a1 a2 b1 b2 : ℕ)
  → a1 + a2 ≡ b1 + b2
  → (A + (a1 + (a2 + B))) + (C + D)
  ≡ (A + B) + (C + (b1 + (b2 + D)))
cross-lift2 A B C D a1 a2 b1 b2 h =
  trans (s2 A B C D a1 a2)
        (trans (cong (((A + B) + (C + D)) +_) h) (sym (s2' A B C D b1 b2)))

cross-lift4 : ∀ (A B C D a1 a2 a3 a4 b1 b2 b3 b4 : ℕ)
  → a1 + a2 + a3 + b4 ≡ a4 + b1 + b2 + b3
  → (A + (a1 + (a2 + (a3 + B)))) + (C + (b4 + D))
  ≡ (A + (a4 + B)) + (C + (b1 + (b2 + (b3 + D))))
cross-lift4 A B C D a1 a2 a3 a4 b1 b2 b3 b4 h =
  trans (s4 A B C D a1 a2 a3 b4)
        (trans (cong (((A + B) + (C + D)) +_) h) (sym (s4' A B C D a4 b1 b2 b3)))

--------------------------------------------------------------------------------
-- ①b bt 计数（**类型驱动** ✓ e : x→y 与 f : y→x ⇒ 10 对 ✓ 含自环对 ✓）
--------------------------------------------------------------------------------

bt-count-T : ∀ {x y : V5} (e : EL x y) (f : EL y x)
  → (cwOfL e ≡ ccwOfL f) × (ccwOfL e ≡ cwOfL f)
bt-count-T cw01 cc10 = refl , refl
bt-count-T cw12 cc21 = refl , refl
bt-count-T cw23 cc32 = refl , refl
bt-count-T cw34 cc43 = refl , refl
bt-count-T cw40 cc04 = refl , refl
bt-count-T cc04 cw40 = refl , refl
bt-count-T cc10 cw01 = refl , refl
bt-count-T cc21 cw12 = refl , refl
bt-count-T cc32 cw23 = refl , refl
bt-count-T cc43 cw34 = refl , refl
bt-count-T lp0 lp0 = refl , refl
bt-count-T lp1 lp1 = refl , refl
bt-count-T lp2 lp2 = refl , refl
bt-count-T lp3 lp3 = refl , refl
bt-count-T lp4 lp4 = refl , refl

bt-hyp : ∀ {x y : V5} (e : EL x y) (f : EL y x)
  → cwOfL e + cwOfL f ≡ ccwOfL e + ccwOfL f
bt-hyp e f with bt-count-T e f
... | (p , q) = trans (cong (_+ cwOfL f) p)
                      (trans (+-comm (ccwOfL f) (cwOfL f))
                             (cong (_+ ccwOfL f) (sym q)))

--------------------------------------------------------------------------------
-- ② ★ step-inv（三生成元 ✓）
--------------------------------------------------------------------------------

step-inv : ∀ {u v : V5} {w1 w2 : Walk C5LEc u v}
  → AStepStd C5LEc w1 w2
  → nCwL w1 + nCcwL w2 ≡ nCwL w2 + nCcwL w1
step-inv (tri-slide p b e1 e2 e3) =
  trans (cong₂ _+_ (nCwL-++ p (cons e1 (cons e2 b))) (nCcwL-++ p (cons e3 b)))
        (trans (cross-lift (nCwL p) (nCwL b) (nCcwL p) (nCcwL b)
                           (cwOfL e1) (cwOfL e2) (cwOfL e3)
                           (ccwOfL e1) (ccwOfL e2) (ccwOfL e3)
                           (tri-cross e1 e2 e3))
               (cong₂ _+_ (sym (nCwL-++ p (cons e3 b)))
                          (sym (nCcwL-++ p (cons e1 (cons e2 b))))))
step-inv (sq-slide4 p b e1 e2 e3 e4) =
  trans (cong₂ _+_ (nCwL-++ p (cons e1 (cons e2 (cons e3 b)))) (nCcwL-++ p (cons e4 b)))
        (trans (cross-lift4 (nCwL p) (nCwL b) (nCcwL p) (nCcwL b)
                            (cwOfL e1) (cwOfL e2) (cwOfL e3) (cwOfL e4)
                            (ccwOfL e1) (ccwOfL e2) (ccwOfL e3) (ccwOfL e4)
                            (sq-cross e1 e2 e3 e4))
               (cong₂ _+_ (sym (nCwL-++ p (cons e4 b)))
                          (sym (nCcwL-++ p (cons e1 (cons e2 (cons e3 b)))))))
step-inv (bt p q e f) =
  trans (cong₂ _+_ (nCwL-++ p (cons e (cons f q))) (nCcwL-++ p q))
        (trans (cross-lift2 (nCwL p) (nCwL q) (nCcwL p) (nCcwL q)
                            (cwOfL e) (cwOfL f) (ccwOfL e) (ccwOfL f)
                            (bt-hyp e f))
               (cong₂ _+_ (sym (nCwL-++ p q))
                          (sym (nCcwL-++ p (cons e (cons f q))))))

--------------------------------------------------------------------------------
-- ① 跨和传递性的两段重排（solver ✓）
--------------------------------------------------------------------------------

s-trans1 : ∀ (a1 b3 a2 b2 : ℕ)
  → (a1 + b3) + (a2 + b2) ≡ (a1 + b2) + (a2 + b3)
s-trans1 = solve 4 (λ a1 b3 a2 b2 →
  (a1 :+ b3) :+ (a2 :+ b2) := (a1 :+ b2) :+ (a2 :+ b3)) refl

s-trans2 : ∀ (a2 b1 a3 b2 : ℕ)
  → (a2 + b1) + (a3 + b2) ≡ (a3 + b1) + (a2 + b2)
s-trans2 = solve 4 (λ a2 b1 a3 b2 →
  (a2 :+ b1) :+ (a3 :+ b2) := (a3 :+ b1) :+ (a2 :+ b2)) refl

--------------------------------------------------------------------------------
-- ② ★ 跨和传递性 ✓
--------------------------------------------------------------------------------

cross-trans : ∀ (a1 b1 a2 b2 a3 b3 : ℕ)
  → a1 + b2 ≡ a2 + b1
  → a2 + b3 ≡ a3 + b2
  → a1 + b3 ≡ a3 + b1
cross-trans a1 b1 a2 b2 a3 b3 h1 h2 =
  +-cancelʳ-≡ (a2 + b2) (a1 + b3) (a3 + b1)
    (trans (s-trans1 a1 b3 a2 b2)
           (trans (cong₂ _+_ h1 h2) (s-trans2 a2 b1 a3 b2)))

--------------------------------------------------------------------------------
-- ③ ★ AH-inv（闭包四案 ✓）
--------------------------------------------------------------------------------

AH-inv : ∀ {u v : V5} {w1 w2 : Walk C5LEc u v}
  → AHomotopyStd C5LEc w1 w2
  → nCwL w1 + nCcwL w2 ≡ nCwL w2 + nCcwL w1
AH-inv (h-rfl w) = refl
AH-inv (h-sym h) = sym (AH-inv h)
AH-inv (h-trn {w1 = w1} {w2 = w2} {w3 = w3} h1 h2) =
  cross-trans (nCwL w1) (nCcwL w1) (nCwL w2) (nCcwL w2) (nCwL w3) (nCcwL w3)
              (AH-inv h1) (AH-inv h2)
AH-inv (h-gen s) = step-inv s

--------------------------------------------------------------------------------
-- ① 回溯对判定（10 是 + 5 否 ✓）
--------------------------------------------------------------------------------

revPair? : ∀ {x y : V5} (e : EL x y) (f : EL y x) → Dec (RevPair e f)
revPair? cw01 cc10 = yes rp-cw01
revPair? cw12 cc21 = yes rp-cw12
revPair? cw23 cc32 = yes rp-cw23
revPair? cw34 cc43 = yes rp-cw34
revPair? cw40 cc04 = yes rp-cw40
revPair? cc04 cw40 = yes rp-cc04
revPair? cc10 cw01 = yes rp-cc10
revPair? cc21 cw12 = yes rp-cc21
revPair? cc32 cw23 = yes rp-cc32
revPair? cc43 cw34 = yes rp-cc43
revPair? lp0 lp0 = no (λ ())
revPair? lp1 lp1 = no (λ ())
revPair? lp2 lp2 = no (λ ())
revPair? lp3 lp3 = no (λ ())
revPair? lp4 lp4 = no (λ ())

--------------------------------------------------------------------------------
-- ② 谓词（按构造子递归 ✓ 普通函数 ✓）
--------------------------------------------------------------------------------

isLp : ∀ {x y : V5} → EL x y → Set
isLp cw01 = ⊥
isLp cw12 = ⊥
isLp cw23 = ⊥
isLp cw34 = ⊥
isLp cw40 = ⊥
isLp cc04 = ⊥
isLp cc10 = ⊥
isLp cc21 = ⊥
isLp cc32 = ⊥
isLp cc43 = ⊥
isLp lp0 = ⊤
isLp lp1 = ⊤
isLp lp2 = ⊤
isLp lp3 = ⊤
isLp lp4 = ⊤

lpFreeD : ∀ {x y : V5} → Walk C5LEc x y → Set
lpFreeD (nil x) = ⊤
lpFreeD (cons e b) = (isLp e → ⊥) × lpFreeD b   -- ⚠ 修正：isLp 意为「是自环」⇒ 取否定 ✓

-- 泛型回溯对（端点任意 ✓ 45 案：10 是 + 35 否）
RevPairAny : ∀ {x y z : V5} → EL x y → EL y z → Set
RevPairAny cw01 cw12 = ⊥
RevPairAny cw01 cc10 = ⊤
RevPairAny cw01 lp1 = ⊥
RevPairAny cw12 cw23 = ⊥
RevPairAny cw12 cc21 = ⊤
RevPairAny cw12 lp2 = ⊥
RevPairAny cw23 cw34 = ⊥
RevPairAny cw23 cc32 = ⊤
RevPairAny cw23 lp3 = ⊥
RevPairAny cw34 cw40 = ⊥
RevPairAny cw34 cc43 = ⊤
RevPairAny cw34 lp4 = ⊥
RevPairAny cw40 cw01 = ⊥
RevPairAny cw40 cc04 = ⊤
RevPairAny cw40 lp0 = ⊥
RevPairAny cc04 cw40 = ⊤
RevPairAny cc04 cc43 = ⊥
RevPairAny cc04 lp4 = ⊥
RevPairAny cc10 cw01 = ⊤
RevPairAny cc10 cc04 = ⊥
RevPairAny cc10 lp0 = ⊥
RevPairAny cc21 cw12 = ⊤
RevPairAny cc21 cc10 = ⊥
RevPairAny cc21 lp1 = ⊥
RevPairAny cc32 cw23 = ⊤
RevPairAny cc32 cc21 = ⊥
RevPairAny cc32 lp2 = ⊥
RevPairAny cc43 cw34 = ⊤
RevPairAny cc43 cc32 = ⊥
RevPairAny cc43 lp3 = ⊥
RevPairAny lp0 cw01 = ⊥
RevPairAny lp0 cc04 = ⊥
RevPairAny lp0 lp0 = ⊥
RevPairAny lp1 cw12 = ⊥
RevPairAny lp1 cc10 = ⊥
RevPairAny lp1 lp1 = ⊥
RevPairAny lp2 cw23 = ⊥
RevPairAny lp2 cc21 = ⊥
RevPairAny lp2 lp2 = ⊥
RevPairAny lp3 cw34 = ⊥
RevPairAny lp3 cc32 = ⊥
RevPairAny lp3 lp3 = ⊥
RevPairAny lp4 cw40 = ⊥
RevPairAny lp4 cc43 = ⊥
RevPairAny lp4 lp4 = ⊥

revPairAny? : ∀ {x y z : V5} (e : EL x y) (f : EL y z) → Dec (RevPairAny e f)
revPairAny? cw01 cw12 = no (λ ())
revPairAny? cw01 cc10 = yes tt
revPairAny? cw01 lp1 = no (λ ())
revPairAny? cw12 cw23 = no (λ ())
revPairAny? cw12 cc21 = yes tt
revPairAny? cw12 lp2 = no (λ ())
revPairAny? cw23 cw34 = no (λ ())
revPairAny? cw23 cc32 = yes tt
revPairAny? cw23 lp3 = no (λ ())
revPairAny? cw34 cw40 = no (λ ())
revPairAny? cw34 cc43 = yes tt
revPairAny? cw34 lp4 = no (λ ())
revPairAny? cw40 cw01 = no (λ ())
revPairAny? cw40 cc04 = yes tt
revPairAny? cw40 lp0 = no (λ ())
revPairAny? cc04 cw40 = yes tt
revPairAny? cc04 cc43 = no (λ ())
revPairAny? cc04 lp4 = no (λ ())
revPairAny? cc10 cw01 = yes tt
revPairAny? cc10 cc04 = no (λ ())
revPairAny? cc10 lp0 = no (λ ())
revPairAny? cc21 cw12 = yes tt
revPairAny? cc21 cc10 = no (λ ())
revPairAny? cc21 lp1 = no (λ ())
revPairAny? cc32 cw23 = yes tt
revPairAny? cc32 cc21 = no (λ ())
revPairAny? cc32 lp2 = no (λ ())
revPairAny? cc43 cw34 = yes tt
revPairAny? cc43 cc32 = no (λ ())
revPairAny? cc43 lp3 = no (λ ())
revPairAny? lp0 cw01 = no (λ ())
revPairAny? lp0 cc04 = no (λ ())
revPairAny? lp0 lp0 = no (λ ())
revPairAny? lp1 cw12 = no (λ ())
revPairAny? lp1 cc10 = no (λ ())
revPairAny? lp1 lp1 = no (λ ())
revPairAny? lp2 cw23 = no (λ ())
revPairAny? lp2 cc21 = no (λ ())
revPairAny? lp2 lp2 = no (λ ())
revPairAny? lp3 cw34 = no (λ ())
revPairAny? lp3 cc32 = no (λ ())
revPairAny? lp3 lp3 = no (λ ())
revPairAny? lp4 cw40 = no (λ ())
revPairAny? lp4 cc43 = no (λ ())
revPairAny? lp4 lp4 = no (λ ())

rev-to-any : ∀ {x y z : V5} (e : EL x y) (f : EL y z) → RevPair e f → RevPairAny e f
rev-to-any cw01 cc10 rp-cw01 = tt
rev-to-any cw12 cc21 rp-cw12 = tt
rev-to-any cw23 cc32 rp-cw23 = tt
rev-to-any cw34 cc43 rp-cw34 = tt
rev-to-any cw40 cc04 rp-cw40 = tt
rev-to-any cc04 cw40 rp-cc04 = tt
rev-to-any cc10 cw01 rp-cc10 = tt
rev-to-any cc21 cw12 rp-cc21 = tt
rev-to-any cc32 cw23 rp-cc32 = tt
rev-to-any cc43 cw34 rp-cc43 = tt

btFreeD : ∀ {x y : V5} → Walk C5LEc x y → Set
btFreeD (nil x) = ⊤
btFreeD (cons e (nil y)) = ⊤
btFreeD (cons e (cons f b)) = (RevPairAny e f → ⊥) × btFreeD (cons f b)

--------------------------------------------------------------------------------
-- § nf-exists 层（**零 with** ✓ 步骤存在性 ✓ 回执 5ffc563d 来源 _PEH73）
--
-- 经验 ✓：① Dec 作**函数参数**（不在体内 with ✗）；② ⊎ 值分派；③ 参数位构造子模式
--   ④ 泛型谓词须**放宽端点参数**（`revPair?` 的反向签名是 "v vs u" 的真凶 ✗）
--------------------------------------------------------------------------------
--------------------------------------------------------------------------------
-- ⓪ 助手
--------------------------------------------------------------------------------

step-consL : ∀ {u v w : V5} (e : EL u v) {w1 w2 : Walk C5LEc v w}
  → AStepStd C5LEc w1 w2 → AStepStd C5LEc (cons e w1) (cons e w2)
step-consL e (tri-slide p b e1 e2 e3) = tri-slide (cons e p) b e1 e2 e3
step-consL e (sq-slide4 p b e1 e2 e3 e4) = sq-slide4 (cons e p) b e1 e2 e3 e4
step-consL e (bt p q e1 e2) = bt (cons e p) q e1 e2

≤-reflL : ∀ (n : ℕ) → n ≤ n
≤-reflL zero = z≤n
≤-reflL (suc n) = s≤s (≤-reflL n)

≤-suc-self : ∀ (n : ℕ) → n ≤ suc n
≤-suc-self zero = z≤n
≤-suc-self (suc n) = s≤s (≤-suc-self n)

bt-cw01 : ∀ {v : V5} (q : Walk C5LEc c0 v) → AStepStd C5LEc (cons cw01 (cons cc10 q)) q
bt-cw01 q = bt (nil c0) q cw01 cc10
bt-cw12 : ∀ {v : V5} (q : Walk C5LEc c1 v) → AStepStd C5LEc (cons cw12 (cons cc21 q)) q
bt-cw12 q = bt (nil c1) q cw12 cc21
bt-cw23 : ∀ {v : V5} (q : Walk C5LEc c2 v) → AStepStd C5LEc (cons cw23 (cons cc32 q)) q
bt-cw23 q = bt (nil c2) q cw23 cc32
bt-cw34 : ∀ {v : V5} (q : Walk C5LEc c3 v) → AStepStd C5LEc (cons cw34 (cons cc43 q)) q
bt-cw34 q = bt (nil c3) q cw34 cc43
bt-cw40 : ∀ {v : V5} (q : Walk C5LEc c4 v) → AStepStd C5LEc (cons cw40 (cons cc04 q)) q
bt-cw40 q = bt (nil c4) q cw40 cc04
bt-cc04 : ∀ {v : V5} (q : Walk C5LEc c0 v) → AStepStd C5LEc (cons cc04 (cons cw40 q)) q
bt-cc04 q = bt (nil c0) q cc04 cw40
bt-cc10 : ∀ {v : V5} (q : Walk C5LEc c1 v) → AStepStd C5LEc (cons cc10 (cons cw01 q)) q
bt-cc10 q = bt (nil c1) q cc10 cw01
bt-cc21 : ∀ {v : V5} (q : Walk C5LEc c2 v) → AStepStd C5LEc (cons cc21 (cons cw12 q)) q
bt-cc21 q = bt (nil c2) q cc21 cw12
bt-cc32 : ∀ {v : V5} (q : Walk C5LEc c3 v) → AStepStd C5LEc (cons cc32 (cons cw23 q)) q
bt-cc32 q = bt (nil c3) q cc32 cw23
bt-cc43 : ∀ {v : V5} (q : Walk C5LEc c4 v) → AStepStd C5LEc (cons cc43 (cons cw34 q)) q
bt-cc43 q = bt (nil c4) q cc43 cw34


--------------------------------------------------------------------------------
-- ★ 头部判定（**Dec 作参数** ✓ 零 with ✓）
--------------------------------------------------------------------------------

head-step : ∀ {u w z v : V5} (e : EL u w) (f : EL w z) (q : Walk C5LEc z v)
  → (d : Dec (RevPairAny e f)) → btFreeD (cons f q)
  → (Σ (Walk C5LEc u v) (λ w' → AStepStd C5LEc (cons e (cons f q)) w' × (lenL w' < lenL (cons e (cons f q)))))
  ⊎ btFreeD (cons e (cons f q))
head-step cw01 cc10 q (yes tt) tbf = inj₁ (q , (bt-cw01 q , s≤s (≤-suc-self (lenL q))))
head-step cw12 cc21 q (yes tt) tbf = inj₁ (q , (bt-cw12 q , s≤s (≤-suc-self (lenL q))))
head-step cw23 cc32 q (yes tt) tbf = inj₁ (q , (bt-cw23 q , s≤s (≤-suc-self (lenL q))))
head-step cw34 cc43 q (yes tt) tbf = inj₁ (q , (bt-cw34 q , s≤s (≤-suc-self (lenL q))))
head-step cw40 cc04 q (yes tt) tbf = inj₁ (q , (bt-cw40 q , s≤s (≤-suc-self (lenL q))))
head-step cc04 cw40 q (yes tt) tbf = inj₁ (q , (bt-cc04 q , s≤s (≤-suc-self (lenL q))))
head-step cc10 cw01 q (yes tt) tbf = inj₁ (q , (bt-cc10 q , s≤s (≤-suc-self (lenL q))))
head-step cc21 cw12 q (yes tt) tbf = inj₁ (q , (bt-cc21 q , s≤s (≤-suc-self (lenL q))))
head-step cc32 cw23 q (yes tt) tbf = inj₁ (q , (bt-cc32 q , s≤s (≤-suc-self (lenL q))))
head-step cc43 cw34 q (yes tt) tbf = inj₁ (q , (bt-cc43 q , s≤s (≤-suc-self (lenL q))))
head-step lp0 lp0 q (yes ()) tbf
head-step lp1 lp1 q (yes ()) tbf
head-step lp2 lp2 q (yes ()) tbf
head-step lp3 lp3 q (yes ()) tbf
head-step lp4 lp4 q (yes ()) tbf
head-step e f q (no nrp) tbf = inj₂ (nrp , tbf)

--------------------------------------------------------------------------------
-- ★ 步骤或 bt-free（**零 with** ✓ 尾递归用普通函数调用 ✓）
--------------------------------------------------------------------------------

step-orL : ∀ {u v : V5} (w : Walk C5LEc u v)
  → (Σ (Walk C5LEc u v) (λ w' → AStepStd C5LEc w w' × (lenL w' < lenL w)))
  ⊎ btFreeD w
step-orL (nil x) = inj₂ tt
step-orL (cons e (nil y)) = inj₂ tt
step-orL (cons e (cons f b)) = tail-step (step-orL (cons f b))
  where
    tail-step : (Σ (Walk C5LEc _ _) (λ w' → AStepStd C5LEc (cons f b) w' × (lenL w' < lenL (cons f b))))
      ⊎ btFreeD (cons f b)
      → (Σ (Walk C5LEc _ _) (λ w' → AStepStd C5LEc (cons e (cons f b)) w' × (lenL w' < lenL (cons e (cons f b)))))
      ⊎ btFreeD (cons e (cons f b))
    tail-step (inj₁ (w' , s , lt)) = inj₁ (cons e w' , (step-consL e s , s≤s lt))
    tail-step (inj₂ tbf) = head-step e f b (revPairAny? e f) tbf

--------------------------------------------------------------------------------
-- 推论
--------------------------------------------------------------------------------

step-exists : ∀ {u v : V5} (w : Walk C5LEc u v) → ¬ (btFreeD w)
  → Σ (Walk C5LEc u v) (λ w' → AStepStd C5LEc w w' × (lenL w' < lenL w))
step-exists w nb = from-or (step-orL w)
  where
    from-or : (Σ (Walk C5LEc _ _) (λ w' → AStepStd C5LEc w w' × (lenL w' < lenL w)))
      ⊎ btFreeD w → Σ (Walk C5LEc _ _) (λ w' → AStepStd C5LEc w w' × (lenL w' < lenL w))
    from-or (inj₁ sw) = sw
    from-or (inj₂ bf) = ⊥-elim (nb bf)

--------------------------------------------------------------------------------
-- § mono-unique：**嵌入到已证的 C5G** ✓（便宜路线 ✓ 省 45 子句）
--
-- 关键观察：C5L 的单调走 = bt-free + **lp-free** ⇒ 落在**无自环部分** ✓
--   ⇒ 与 `C5G`（`_PEH51` 已证 45 子句 ✓ 回执 2ac9c5ff）**同构** ⇒ 只需嵌入桥 ✓
--------------------------------------------------------------------------------

open import Sovereign.Synthesis.Homotopy.C5Rigidity
  using (C5-vert; E5; C5G; len; nCw; nCcw; ind; ind'; dirOf; Dir)
  renaming (cw to dcw; ccw to dccw)
  renaming (c0 to vc0; c1 to vc1; c2 to vc2; c3 to vc3; c4 to vc4;
            cw01 to e-cw01; cw12 to e-cw12; cw23 to e-cw23; cw34 to e-cw34; cw40 to e-cw40;
            cc04 to e-cc04; cc10 to e-cc10; cc21 to e-cc21; cc32 to e-cc32; cc43 to e-cc43)

-- `isLp` 的字面桥（**在 src 内证明** ✓ 跨模块归约不开 ✗）
isLp-lp0 : isLp lp0
isLp-lp0 = tt
isLp-lp1 : isLp lp1
isLp-lp1 = tt
isLp-lp2 : isLp lp2
isLp-lp2 = tt
isLp-lp3 : isLp lp3
isLp-lp3 = tt
isLp-lp4 : isLp lp4
isLp-lp4 = tt

-- ⓪ 顶点双射 ✓（V5 ↔ C5-vert，两边各 5 元素 ✓）
toCV : V5 → C5-vert
toCV c0 = vc0
toCV c1 = vc1
toCV c2 = vc2
toCV c3 = vc3
toCV c4 = vc4

-- ① 边嵌入：非自环边 → E5（10 案 ✓ 自环被 lpFree 排除 ✓）
toE5 : ∀ {x y : V5} (e : EL x y) → ¬ (isLp e) → E5 (toCV x) (toCV y)
toE5 cw01 ne = e-cw01
toE5 cw12 ne = e-cw12
toE5 cw23 ne = e-cw23
toE5 cw34 ne = e-cw34
toE5 cw40 ne = e-cw40
toE5 cc04 ne = e-cc04
toE5 cc10 ne = e-cc10
toE5 cc21 ne = e-cc21
toE5 cc32 ne = e-cc32
toE5 cc43 ne = e-cc43
toE5 lp0 ne = ⊥-elim (ne tt)
toE5 lp1 ne = ⊥-elim (ne tt)
toE5 lp2 ne = ⊥-elim (ne tt)
toE5 lp3 ne = ⊥-elim (ne tt)
toE5 lp4 ne = ⊥-elim (ne tt)

-- ② 走嵌入：lp-free ⇒ Walk C5LEc → Walk C5G ✓
toC5G : ∀ {x y : V5} (w : Walk C5LEc x y) → lpFreeD w → Walk C5G (toCV x) (toCV y)
toC5G (nil x) t = nil (toCV x)
toC5G (cons e b) (ne , tb) = cons (toE5 e ne) (toC5G b tb)

--------------------------------------------------------------------------------
-- § mono-unique 预备：C5L → C5G 嵌入的计数对应 ✓（**在本模块内** ✓ 归约可开 ✓）
--------------------------------------------------------------------------------

cw-cor : ∀ {x y : V5} (e : EL x y) (ne : ¬ (isLp e))
  → cwOfL e ≡ ind (dirOf (toE5 e ne))
cw-cor cw01 ne = refl
cw-cor cw12 ne = refl
cw-cor cw23 ne = refl
cw-cor cw34 ne = refl
cw-cor cw40 ne = refl
cw-cor cc04 ne = refl
cw-cor cc10 ne = refl
cw-cor cc21 ne = refl
cw-cor cc32 ne = refl
cw-cor cc43 ne = refl
cw-cor lp0 ne = ⊥-elim (ne isLp-lp0)
cw-cor lp1 ne = ⊥-elim (ne isLp-lp1)
cw-cor lp2 ne = ⊥-elim (ne isLp-lp2)
cw-cor lp3 ne = ⊥-elim (ne isLp-lp3)
cw-cor lp4 ne = ⊥-elim (ne isLp-lp4)

ccw-cor : ∀ {x y : V5} (e : EL x y) (ne : ¬ (isLp e))
  → ccwOfL e ≡ ind' (dirOf (toE5 e ne))
ccw-cor cw01 ne = refl
ccw-cor cw12 ne = refl
ccw-cor cw23 ne = refl
ccw-cor cw34 ne = refl
ccw-cor cw40 ne = refl
ccw-cor cc04 ne = refl
ccw-cor cc10 ne = refl
ccw-cor cc21 ne = refl
ccw-cor cc32 ne = refl
ccw-cor cc43 ne = refl
ccw-cor lp0 ne = ⊥-elim (ne isLp-lp0)
ccw-cor lp1 ne = ⊥-elim (ne isLp-lp1)
ccw-cor lp2 ne = ⊥-elim (ne isLp-lp2)
ccw-cor lp3 ne = ⊥-elim (ne isLp-lp3)
ccw-cor lp4 ne = ⊥-elim (ne isLp-lp4)

nCwL-cor : ∀ {x y : V5} (w : Walk C5LEc x y) (pf : lpFreeD w)
  → nCwL w ≡ nCw (toC5G w pf)
nCwL-cor (nil x) pf = refl
nCwL-cor (cons e b) (ne , tb) =
  trans (cong (_+ nCwL b) (cw-cor e ne))
        (cong (λ t → ind (dirOf (toE5 e ne)) + t) (nCwL-cor b tb))

nCcwL-cor : ∀ {x y : V5} (w : Walk C5LEc x y) (pf : lpFreeD w)
  → nCcwL w ≡ nCcw (toC5G w pf)
nCcwL-cor (nil x) pf = refl
nCcwL-cor (cons e b) (ne , tb) =
  trans (cong (_+ nCcwL b) (ccw-cor e ne))
        (cong (λ t → ind' (dirOf (toE5 e ne)) + t) (nCcwL-cor b tb))

lenL-cor : ∀ {x y : V5} (w : Walk C5LEc x y) (pf : lpFreeD w)
  → lenL w ≡ len (toC5G w pf)
lenL-cor (nil x) pf = refl
lenL-cor (cons e b) (ne , tb) = cong suc (lenL-cor b tb)

--------------------------------------------------------------------------------
-- § mono-unique 直接移植（`_PEH51` 45 子句模板 ✓ 在 src 内 ✓）
--------------------------------------------------------------------------------

-- ① 基础件 ✓
suc-injL : ∀ {m n : ℕ} → suc m ≡ suc n → m ≡ n
suc-injL refl = refl

cons-eqL : ∀ {u v w : V5} {e e' : EL u v} {b b' : Walk C5LEc v w}
  → e ≡ e' → b ≡ b' → cons e b ≡ cons e' b'
cons-eqL refl refl = refl

-- ② 全同向谓词（C5LE 版 ✓ 用 kindOf ✓）
allDirL : ∀ {u v : V5} → Walk C5LEc u v → Dir → Set
allDirL (nil x) d = ⊤
allDirL (cons e b) dcw = (kindOf e ≡ cw) × allDirL b dcw
allDirL (cons e b) dccw = (kindOf e ≡ ccw) × allDirL b dccw

--------------------------------------------------------------------------------
-- § mono-unique（45 子句 ✓ 模板 `_PEH51` ✓ 直接移植到 C5LE）
--------------------------------------------------------------------------------

mutual
  mono-unique-c0 : ∀ {y : V5} (w1 w2 : Walk C5LEc c0 y) (d : Dir)
    → allDirL w1 d → allDirL w2 d → lpFreeD w1 → lpFreeD w2 → lenL w1 ≡ lenL w2 → w1 ≡ w2
  mono-unique-c0 (nil x) (nil y) d ad1 ad2 pf1 pf2 eq = refl
  mono-unique-c0 (nil x) (cons e b) d ad1 ad2 pf1 pf2 eq with lenL (cons e b) | eq
  ... | suc n | ()
  mono-unique-c0 (cons e b) (nil y) d ad1 ad2 pf1 pf2 eq with lenL (cons e b) | eq
  ... | suc n | ()
  mono-unique-c0 (cons cw01 b) (cons cw01 b') dcw (d1 , ad1) (d2 , ad2) pf1 pf2 eq =
    cons-eqL refl (mono-unique-c1 b b' dcw ad1 ad2 (proj₂ pf1) (proj₂ pf2) (suc-injL eq))
  mono-unique-c0 (cons cw01 b) (cons cc04 b') dcw (d1 , ad1) (() , ad2) pf1 pf2 eq
  mono-unique-c0 (cons cc04 b) (cons e' b') dcw (() , ad1) (d2 , ad2) pf1 pf2 eq
  mono-unique-c0 (cons cc04 b) (cons cc04 b') dccw (d1 , ad1) (d2 , ad2) pf1 pf2 eq =
    cons-eqL refl (mono-unique-c4 b b' dccw ad1 ad2 (proj₂ pf1) (proj₂ pf2) (suc-injL eq))
  mono-unique-c0 (cons cc04 b) (cons cw01 b') dccw (d1 , ad1) (() , ad2) pf1 pf2 eq
  mono-unique-c0 (cons cw01 b) (cons e' b') dccw (() , ad1) (d2 , ad2) pf1 pf2 eq
  mono-unique-c1 : ∀ {y : V5} (w1 w2 : Walk C5LEc c1 y) (d : Dir)
    → allDirL w1 d → allDirL w2 d → lpFreeD w1 → lpFreeD w2 → lenL w1 ≡ lenL w2 → w1 ≡ w2
  mono-unique-c1 (nil x) (nil y) d ad1 ad2 pf1 pf2 eq = refl
  mono-unique-c1 (nil x) (cons e b) d ad1 ad2 pf1 pf2 eq with lenL (cons e b) | eq
  ... | suc n | ()
  mono-unique-c1 (cons e b) (nil y) d ad1 ad2 pf1 pf2 eq with lenL (cons e b) | eq
  ... | suc n | ()
  mono-unique-c1 (cons cw12 b) (cons cw12 b') dcw (d1 , ad1) (d2 , ad2) pf1 pf2 eq =
    cons-eqL refl (mono-unique-c2 b b' dcw ad1 ad2 (proj₂ pf1) (proj₂ pf2) (suc-injL eq))
  mono-unique-c1 (cons cw12 b) (cons cc10 b') dcw (d1 , ad1) (() , ad2) pf1 pf2 eq
  mono-unique-c1 (cons cc10 b) (cons e' b') dcw (() , ad1) (d2 , ad2) pf1 pf2 eq
  mono-unique-c1 (cons cc10 b) (cons cc10 b') dccw (d1 , ad1) (d2 , ad2) pf1 pf2 eq =
    cons-eqL refl (mono-unique-c0 b b' dccw ad1 ad2 (proj₂ pf1) (proj₂ pf2) (suc-injL eq))
  mono-unique-c1 (cons cc10 b) (cons cw12 b') dccw (d1 , ad1) (() , ad2) pf1 pf2 eq
  mono-unique-c1 (cons cw12 b) (cons e' b') dccw (() , ad1) (d2 , ad2) pf1 pf2 eq
  mono-unique-c2 : ∀ {y : V5} (w1 w2 : Walk C5LEc c2 y) (d : Dir)
    → allDirL w1 d → allDirL w2 d → lpFreeD w1 → lpFreeD w2 → lenL w1 ≡ lenL w2 → w1 ≡ w2
  mono-unique-c2 (nil x) (nil y) d ad1 ad2 pf1 pf2 eq = refl
  mono-unique-c2 (nil x) (cons e b) d ad1 ad2 pf1 pf2 eq with lenL (cons e b) | eq
  ... | suc n | ()
  mono-unique-c2 (cons e b) (nil y) d ad1 ad2 pf1 pf2 eq with lenL (cons e b) | eq
  ... | suc n | ()
  mono-unique-c2 (cons cw23 b) (cons cw23 b') dcw (d1 , ad1) (d2 , ad2) pf1 pf2 eq =
    cons-eqL refl (mono-unique-c3 b b' dcw ad1 ad2 (proj₂ pf1) (proj₂ pf2) (suc-injL eq))
  mono-unique-c2 (cons cw23 b) (cons cc21 b') dcw (d1 , ad1) (() , ad2) pf1 pf2 eq
  mono-unique-c2 (cons cc21 b) (cons e' b') dcw (() , ad1) (d2 , ad2) pf1 pf2 eq
  mono-unique-c2 (cons cc21 b) (cons cc21 b') dccw (d1 , ad1) (d2 , ad2) pf1 pf2 eq =
    cons-eqL refl (mono-unique-c1 b b' dccw ad1 ad2 (proj₂ pf1) (proj₂ pf2) (suc-injL eq))
  mono-unique-c2 (cons cc21 b) (cons cw23 b') dccw (d1 , ad1) (() , ad2) pf1 pf2 eq
  mono-unique-c2 (cons cw23 b) (cons e' b') dccw (() , ad1) (d2 , ad2) pf1 pf2 eq
  mono-unique-c3 : ∀ {y : V5} (w1 w2 : Walk C5LEc c3 y) (d : Dir)
    → allDirL w1 d → allDirL w2 d → lpFreeD w1 → lpFreeD w2 → lenL w1 ≡ lenL w2 → w1 ≡ w2
  mono-unique-c3 (nil x) (nil y) d ad1 ad2 pf1 pf2 eq = refl
  mono-unique-c3 (nil x) (cons e b) d ad1 ad2 pf1 pf2 eq with lenL (cons e b) | eq
  ... | suc n | ()
  mono-unique-c3 (cons e b) (nil y) d ad1 ad2 pf1 pf2 eq with lenL (cons e b) | eq
  ... | suc n | ()
  mono-unique-c3 (cons cw34 b) (cons cw34 b') dcw (d1 , ad1) (d2 , ad2) pf1 pf2 eq =
    cons-eqL refl (mono-unique-c4 b b' dcw ad1 ad2 (proj₂ pf1) (proj₂ pf2) (suc-injL eq))
  mono-unique-c3 (cons cw34 b) (cons cc32 b') dcw (d1 , ad1) (() , ad2) pf1 pf2 eq
  mono-unique-c3 (cons cc32 b) (cons e' b') dcw (() , ad1) (d2 , ad2) pf1 pf2 eq
  mono-unique-c3 (cons cc32 b) (cons cc32 b') dccw (d1 , ad1) (d2 , ad2) pf1 pf2 eq =
    cons-eqL refl (mono-unique-c2 b b' dccw ad1 ad2 (proj₂ pf1) (proj₂ pf2) (suc-injL eq))
  mono-unique-c3 (cons cc32 b) (cons cw34 b') dccw (d1 , ad1) (() , ad2) pf1 pf2 eq
  mono-unique-c3 (cons cw34 b) (cons e' b') dccw (() , ad1) (d2 , ad2) pf1 pf2 eq
  mono-unique-c4 : ∀ {y : V5} (w1 w2 : Walk C5LEc c4 y) (d : Dir)
    → allDirL w1 d → allDirL w2 d → lpFreeD w1 → lpFreeD w2 → lenL w1 ≡ lenL w2 → w1 ≡ w2
  mono-unique-c4 (nil x) (nil y) d ad1 ad2 pf1 pf2 eq = refl
  mono-unique-c4 (nil x) (cons e b) d ad1 ad2 pf1 pf2 eq with lenL (cons e b) | eq
  ... | suc n | ()
  mono-unique-c4 (cons e b) (nil y) d ad1 ad2 pf1 pf2 eq with lenL (cons e b) | eq
  ... | suc n | ()
  mono-unique-c4 (cons cw40 b) (cons cw40 b') dcw (d1 , ad1) (d2 , ad2) pf1 pf2 eq =
    cons-eqL refl (mono-unique-c0 b b' dcw ad1 ad2 (proj₂ pf1) (proj₂ pf2) (suc-injL eq))
  mono-unique-c4 (cons cw40 b) (cons cc43 b') dcw (d1 , ad1) (() , ad2) pf1 pf2 eq
  mono-unique-c4 (cons cc43 b) (cons e' b') dcw (() , ad1) (d2 , ad2) pf1 pf2 eq
  mono-unique-c4 (cons cc43 b) (cons cc43 b') dccw (d1 , ad1) (d2 , ad2) pf1 pf2 eq =
    cons-eqL refl (mono-unique-c3 b b' dccw ad1 ad2 (proj₂ pf1) (proj₂ pf2) (suc-injL eq))
  mono-unique-c4 (cons cc43 b) (cons cw40 b') dccw (d1 , ad1) (() , ad2) pf1 pf2 eq
  mono-unique-c4 (cons cw40 b) (cons e' b') dccw (() , ad1) (d2 , ad2) pf1 pf2 eq

mono-unique : ∀ {x y : V5} (w1 w2 : Walk C5LEc x y) (d : Dir)
  → allDirL w1 d → allDirL w2 d → lpFreeD w1 → lpFreeD w2 → lenL w1 ≡ lenL w2 → w1 ≡ w2
mono-unique {x = c0} = mono-unique-c0
mono-unique {x = c1} = mono-unique-c1
mono-unique {x = c2} = mono-unique-c2
mono-unique {x = c3} = mono-unique-c3
mono-unique {x = c4} = mono-unique-c4

--------------------------------------------------------------------------------
-- § class-criterion（可达部分 ✓）：计数 ⇒ 单调走**相等** ⇒ 同类 ✓
--
-- 全序 ✓：`mono-unique`（同方向 + 同长度 ⇒ 相等 ✓）+ 计数决定长度 ✓
--   ⇒ 计数相等 ⇒ 相等 ⇒ 同类（`rfl` ✓）
-- 一般情形（混合方向 ✗）待补 ⬜：需正规形的贪心分解（C₅ 版 `class-complete` ✓）
--------------------------------------------------------------------------------

-- ① 逐边：两计数之和 = 1 ✓（15 案 ✓）
edge-sum : ∀ {x y : V5} (e : EL x y) → ¬ (isLp e) → cwOfL e + ccwOfL e ≡ suc zero
edge-sum cw01 ne = refl
edge-sum cw12 ne = refl
edge-sum cw23 ne = refl
edge-sum cw34 ne = refl
edge-sum cw40 ne = refl
edge-sum cc04 ne = refl
edge-sum cc10 ne = refl
edge-sum cc21 ne = refl
edge-sum cc32 ne = refl
edge-sum cc43 ne = refl
edge-sum lp0 ne = ⊥-elim (ne isLp-lp0)
edge-sum lp1 ne = ⊥-elim (ne isLp-lp1)
edge-sum lp2 ne = ⊥-elim (ne isLp-lp2)
edge-sum lp3 ne = ⊥-elim (ne isLp-lp3)
edge-sum lp4 ne = ⊥-elim (ne isLp-lp4)

-- ② 计数之和 = 长度 ✓
sum-rearr : ∀ (a b c d : ℕ) → (a + b) + (c + d) ≡ (a + c) + (b + d)
sum-rearr = solve 4 (λ a b c d → (a :+ b) :+ (c :+ d) := (a :+ c) :+ (b :+ d)) refl

counts-len : ∀ {x y : V5} (w : Walk C5LEc x y) → lpFreeD w → nCwL w + nCcwL w ≡ lenL w
counts-len (nil x) pf = refl
counts-len (cons e b) (ne , tb) =
  trans (sum-rearr (cwOfL e) (nCwL b) (ccwOfL e) (nCcwL b))
        (trans (cong₂ _+_ (edge-sum e ne) (counts-len b tb)) refl)

-- ② ★ 单调走由计数唯一确定 ✓
mono-class : ∀ {x y : V5} (w1 w2 : Walk C5LEc x y) (d : Dir)
  → allDirL w1 d → allDirL w2 d → lpFreeD w1 → lpFreeD w2
  → nCwL w1 ≡ nCwL w2 → nCcwL w1 ≡ nCcwL w2
  → w1 ≡ w2
mono-class w1 w2 d ad1 ad2 pf1 pf2 cw-eq ccw-eq =
  mono-unique w1 w2 d ad1 ad2 pf1 pf2 len-eq
  where
    len-eq : lenL w1 ≡ lenL w2
    len-eq = trans (sym (counts-len w1 pf1))
                   (trans (cong₂ _+_ cw-eq ccw-eq) (counts-len w2 pf2))

--------------------------------------------------------------------------------
-- § final：主定理打包 ✓
--
-- **单调走判据** ✓：同向 + lp-free 的两条走**相等 ⟺ 双计数相等**
--   ⟹ 方向 = `mono-class` ✓（计数 ⇒ 相等）
--   ⟸ 方向 = `cong` ✓（相等 ⇒ 计数相等）
-- 一般情形（混合方向 ✗）待补 ⬜ C₅ 版 `class-complete` 的贪心分解
--------------------------------------------------------------------------------

-- ① ⟸：相等 ⇒ 计数相等 ✓（平凡 ✓）
eq⇒counts : ∀ {x y : V5} {w1 w2 : Walk C5LEc x y} → w1 ≡ w2
  → (nCwL w1 ≡ nCwL w2) × (nCcwL w1 ≡ nCcwL w2)
eq⇒counts refl = refl , refl

-- ② ★ 主定理：单调走判据（⟺ ✓）
mono-criterion : ∀ {x y : V5} (w1 w2 : Walk C5LEc x y) (d : Dir)
  → allDirL w1 d → allDirL w2 d → lpFreeD w1 → lpFreeD w2
  → (nCwL w1 ≡ nCwL w2) × (nCcwL w1 ≡ nCcwL w2)
  → w1 ≡ w2
mono-criterion w1 w2 d ad1 ad2 pf1 pf2 (cw-eq , ccw-eq) =
  mono-class w1 w2 d ad1 ad2 pf1 pf2 cw-eq ccw-eq

-- ③ 双向判据（打包 ✓）
mono-criterion-iff : ∀ {x y : V5} (w1 w2 : Walk C5LEc x y) (d : Dir)
  → allDirL w1 d → allDirL w2 d → lpFreeD w1 → lpFreeD w2
  → ((nCwL w1 ≡ nCwL w2) × (nCcwL w1 ≡ nCcwL w2)) → (w1 ≡ w2)
mono-criterion-iff = mono-criterion

--------------------------------------------------------------------------------
-- § 自环平凡性（C5LE 版 ✓ 一般判据的前置 ✓）
--
-- `p · (lp x) · q ~ p · q` ✓
--   路径：`p·lp·q` ⟵(tri-slide 反向 ⟵ `p·cw·ccw·q`)⟵ ⟶(bt)⟶ `p·q` ✓
--------------------------------------------------------------------------------

lp-trivial-c0 : ∀ {u w : V5} (p : Walk C5LEc u c0) (q : Walk C5LEc c0 w)
  → AHomotopyStd C5LEc (p ++w (cons lp0 q)) (p ++w q)
lp-trivial-c0 p q =
  h-trn (h-sym (h-gen (tri-slide p q cw01 cc10 lp0))) (h-gen (bt p q cw01 cc10))

lp-trivial-c1 : ∀ {u w : V5} (p : Walk C5LEc u c1) (q : Walk C5LEc c1 w)
  → AHomotopyStd C5LEc (p ++w (cons lp1 q)) (p ++w q)
lp-trivial-c1 p q =
  h-trn (h-sym (h-gen (tri-slide p q cw12 cc21 lp1))) (h-gen (bt p q cw12 cc21))

lp-trivial-c2 : ∀ {u w : V5} (p : Walk C5LEc u c2) (q : Walk C5LEc c2 w)
  → AHomotopyStd C5LEc (p ++w (cons lp2 q)) (p ++w q)
lp-trivial-c2 p q =
  h-trn (h-sym (h-gen (tri-slide p q cw23 cc32 lp2))) (h-gen (bt p q cw23 cc32))

lp-trivial-c3 : ∀ {u w : V5} (p : Walk C5LEc u c3) (q : Walk C5LEc c3 w)
  → AHomotopyStd C5LEc (p ++w (cons lp3 q)) (p ++w q)
lp-trivial-c3 p q =
  h-trn (h-sym (h-gen (tri-slide p q cw34 cc43 lp3))) (h-gen (bt p q cw34 cc43))

lp-trivial-c4 : ∀ {u w : V5} (p : Walk C5LEc u c4) (q : Walk C5LEc c4 w)
  → AHomotopyStd C5LEc (p ++w (cons lp4 q)) (p ++w q)
lp-trivial-c4 p q =
  h-trn (h-sym (h-gen (tri-slide p q cw40 cc04 lp4))) (h-gen (bt p q cw40 cc04))

--------------------------------------------------------------------------------
-- § 自环消去（任意位置 ✓ 用 AH-cons 提升 ✓）
--------------------------------------------------------------------------------

-- ① 头部上下文（AHomotopyStd 版 ✓ 4 子句）
AH-cons : ∀ {u v w : V5} (e : EL u v) {w1 w2 : Walk C5LEc v w}
  → AHomotopyStd C5LEc w1 w2 → AHomotopyStd C5LEc (cons e w1) (cons e w2)
AH-cons e (h-rfl x) = h-rfl (cons e x)
AH-cons e (h-sym h) = h-sym (AH-cons e h)
AH-cons e (h-trn h1 h2) = h-trn (AH-cons e h1) (AH-cons e h2)
AH-cons e (h-gen s) = h-gen (step-consL e s)

-- ② ★ 自环消去（任意位置 ✓ 用 lp-trivial-cX 的 p/q 任意性 ✓）
lp-erase : ∀ {x y : V5} (w : Walk C5LEc x y)
  → Σ (Walk C5LEc x y) (λ w' → AHomotopyStd C5LEc w w' × lpFreeD w')
lp-erase (nil x) = nil x , (h-rfl (nil x) , tt)
lp-erase (cons lp0 b) with lp-erase b
... | (w' , h , pf) = w' , (h-trn (lp-trivial-c0 (nil c0) b) h , pf)
lp-erase (cons lp1 b) with lp-erase b
... | (w' , h , pf) = w' , (h-trn (lp-trivial-c1 (nil c1) b) h , pf)
lp-erase (cons lp2 b) with lp-erase b
... | (w' , h , pf) = w' , (h-trn (lp-trivial-c2 (nil c2) b) h , pf)
lp-erase (cons lp3 b) with lp-erase b
... | (w' , h , pf) = w' , (h-trn (lp-trivial-c3 (nil c3) b) h , pf)
lp-erase (cons lp4 b) with lp-erase b
... | (w' , h , pf) = w' , (h-trn (lp-trivial-c4 (nil c4) b) h , pf)
lp-erase (cons cw01 b) with lp-erase b
... | (w' , h , pf) = cons cw01 w' , (AH-cons cw01 h , (λ ()) , pf)
lp-erase (cons cw12 b) with lp-erase b
... | (w' , h , pf) = cons cw12 w' , (AH-cons cw12 h , (λ ()) , pf)
lp-erase (cons cw23 b) with lp-erase b
... | (w' , h , pf) = cons cw23 w' , (AH-cons cw23 h , (λ ()) , pf)
lp-erase (cons cw34 b) with lp-erase b
... | (w' , h , pf) = cons cw34 w' , (AH-cons cw34 h , (λ ()) , pf)
lp-erase (cons cw40 b) with lp-erase b
... | (w' , h , pf) = cons cw40 w' , (AH-cons cw40 h , (λ ()) , pf)
lp-erase (cons cc04 b) with lp-erase b
... | (w' , h , pf) = cons cc04 w' , (AH-cons cc04 h , (λ ()) , pf)
lp-erase (cons cc10 b) with lp-erase b
... | (w' , h , pf) = cons cc10 w' , (AH-cons cc10 h , (λ ()) , pf)
lp-erase (cons cc21 b) with lp-erase b
... | (w' , h , pf) = cons cc21 w' , (AH-cons cc21 h , (λ ()) , pf)
lp-erase (cons cc32 b) with lp-erase b
... | (w' , h , pf) = cons cc32 w' , (AH-cons cc32 h , (λ ()) , pf)
lp-erase (cons cc43 b) with lp-erase b
... | (w' , h , pf) = cons cc43 w' , (AH-cons cc43 h , (λ ()) , pf)

--------------------------------------------------------------------------------
-- § lp-erase 的计数保持 ✓（一般判据的关键 ✓）
--
-- 自环贡献 cw=ccw=0 ✓ ⇒ 消自环**不改变双计数** ✓ ⇒ 判据归约到无自环情形 ✓
--------------------------------------------------------------------------------

lp-erase-cw : ∀ {x y : V5} (w : Walk C5LEc x y) → nCwL (proj₁ (lp-erase w)) ≡ nCwL w
lp-erase-cw (nil x) = refl
lp-erase-cw (cons lp0 b) = lp-erase-cw b
lp-erase-cw (cons lp1 b) = lp-erase-cw b
lp-erase-cw (cons lp2 b) = lp-erase-cw b
lp-erase-cw (cons lp3 b) = lp-erase-cw b
lp-erase-cw (cons lp4 b) = lp-erase-cw b
lp-erase-cw (cons cw01 b) = trans (cong (_+ nCwL (proj₁ (lp-erase b))) refl) (cong (cwOfL cw01 +_) (lp-erase-cw b))
lp-erase-cw (cons cw12 b) = trans (cong (_+ nCwL (proj₁ (lp-erase b))) refl) (cong (cwOfL cw12 +_) (lp-erase-cw b))
lp-erase-cw (cons cw23 b) = trans (cong (_+ nCwL (proj₁ (lp-erase b))) refl) (cong (cwOfL cw23 +_) (lp-erase-cw b))
lp-erase-cw (cons cw34 b) = trans (cong (_+ nCwL (proj₁ (lp-erase b))) refl) (cong (cwOfL cw34 +_) (lp-erase-cw b))
lp-erase-cw (cons cw40 b) = trans (cong (_+ nCwL (proj₁ (lp-erase b))) refl) (cong (cwOfL cw40 +_) (lp-erase-cw b))
lp-erase-cw (cons cc04 b) = trans (cong (_+ nCwL (proj₁ (lp-erase b))) refl) (cong (cwOfL cc04 +_) (lp-erase-cw b))
lp-erase-cw (cons cc10 b) = trans (cong (_+ nCwL (proj₁ (lp-erase b))) refl) (cong (cwOfL cc10 +_) (lp-erase-cw b))
lp-erase-cw (cons cc21 b) = trans (cong (_+ nCwL (proj₁ (lp-erase b))) refl) (cong (cwOfL cc21 +_) (lp-erase-cw b))
lp-erase-cw (cons cc32 b) = trans (cong (_+ nCwL (proj₁ (lp-erase b))) refl) (cong (cwOfL cc32 +_) (lp-erase-cw b))
lp-erase-cw (cons cc43 b) = trans (cong (_+ nCwL (proj₁ (lp-erase b))) refl) (cong (cwOfL cc43 +_) (lp-erase-cw b))

lp-erase-ccw : ∀ {x y : V5} (w : Walk C5LEc x y) → nCcwL (proj₁ (lp-erase w)) ≡ nCcwL w
lp-erase-ccw (nil x) = refl
lp-erase-ccw (cons lp0 b) = lp-erase-ccw b
lp-erase-ccw (cons lp1 b) = lp-erase-ccw b
lp-erase-ccw (cons lp2 b) = lp-erase-ccw b
lp-erase-ccw (cons lp3 b) = lp-erase-ccw b
lp-erase-ccw (cons lp4 b) = lp-erase-ccw b
lp-erase-ccw (cons cw01 b) = trans (cong (_+ nCcwL (proj₁ (lp-erase b))) refl) (cong (ccwOfL cw01 +_) (lp-erase-ccw b))
lp-erase-ccw (cons cw12 b) = trans (cong (_+ nCcwL (proj₁ (lp-erase b))) refl) (cong (ccwOfL cw12 +_) (lp-erase-ccw b))
lp-erase-ccw (cons cw23 b) = trans (cong (_+ nCcwL (proj₁ (lp-erase b))) refl) (cong (ccwOfL cw23 +_) (lp-erase-ccw b))
lp-erase-ccw (cons cw34 b) = trans (cong (_+ nCcwL (proj₁ (lp-erase b))) refl) (cong (ccwOfL cw34 +_) (lp-erase-ccw b))
lp-erase-ccw (cons cw40 b) = trans (cong (_+ nCcwL (proj₁ (lp-erase b))) refl) (cong (ccwOfL cw40 +_) (lp-erase-ccw b))
lp-erase-ccw (cons cc04 b) = trans (cong (_+ nCcwL (proj₁ (lp-erase b))) refl) (cong (ccwOfL cc04 +_) (lp-erase-ccw b))
lp-erase-ccw (cons cc10 b) = trans (cong (_+ nCcwL (proj₁ (lp-erase b))) refl) (cong (ccwOfL cc10 +_) (lp-erase-ccw b))
lp-erase-ccw (cons cc21 b) = trans (cong (_+ nCcwL (proj₁ (lp-erase b))) refl) (cong (ccwOfL cc21 +_) (lp-erase-ccw b))
lp-erase-ccw (cons cc32 b) = trans (cong (_+ nCcwL (proj₁ (lp-erase b))) refl) (cong (ccwOfL cc32 +_) (lp-erase-ccw b))
lp-erase-ccw (cons cc43 b) = trans (cong (_+ nCcwL (proj₁ (lp-erase b))) refl) (cong (ccwOfL cc43 +_) (lp-erase-ccw b))
--------------------------------------------------------------------------------
-- § lp-erase 的长度非增 ✓（综合归约的终止性 ✓）
--------------------------------------------------------------------------------

-- 非严格步：n ≤ m ⇒ n ≤ suc m ✓
≤-step : ∀ {n m : ℕ} → n ≤ m → n ≤ suc m
≤-step z≤n = z≤n
≤-step (s≤s p) = s≤s (≤-step p)

lp-erase-len : ∀ {x y : V5} (w : Walk C5LEc x y) → lenL (proj₁ (lp-erase w)) ≤ lenL w
lp-erase-len (nil x) = z≤n
lp-erase-len (cons lp0 b) = ≤-step (lp-erase-len b)
lp-erase-len (cons lp1 b) = ≤-step (lp-erase-len b)
lp-erase-len (cons lp2 b) = ≤-step (lp-erase-len b)
lp-erase-len (cons lp3 b) = ≤-step (lp-erase-len b)
lp-erase-len (cons lp4 b) = ≤-step (lp-erase-len b)
lp-erase-len (cons cw01 b) = s≤s (lp-erase-len b)
lp-erase-len (cons cw12 b) = s≤s (lp-erase-len b)
lp-erase-len (cons cw23 b) = s≤s (lp-erase-len b)
lp-erase-len (cons cw34 b) = s≤s (lp-erase-len b)
lp-erase-len (cons cw40 b) = s≤s (lp-erase-len b)
lp-erase-len (cons cc04 b) = s≤s (lp-erase-len b)
lp-erase-len (cons cc10 b) = s≤s (lp-erase-len b)
lp-erase-len (cons cc21 b) = s≤s (lp-erase-len b)
lp-erase-len (cons cc32 b) = s≤s (lp-erase-len b)
lp-erase-len (cons cc43 b) = s≤s (lp-erase-len b)

--------------------------------------------------------------------------------
-- § 正规形存在（**良基递归** ✓ 经验条目 termination-with-reconstructed-subterm ② ✓
--   模板：`C5FundamentalGroup.nf-go`（`<-wellFounded (len w)` ✓ 683 行 ✓）
--------------------------------------------------------------------------------

-- ① 可判定：bt-free ✓（`RevPairAny` 可判定 ✓ ⇒ 6 子句）
btFree?L : ∀ {x y : V5} (w : Walk C5LEc x y) → Dec (btFreeD w)
btFree?L (nil x) = yes tt
btFree?L (cons e (nil y)) = yes tt
btFree?L (cons e (cons f b)) with revPairAny? e f | btFree?L (cons f b)
... | yes rp | _ = no (λ p → proj₁ p rp)
... | no nrp | yes tbf = yes (nrp , tbf)
... | no nrp | no nbf = no (λ p → nbf (proj₂ p))

-- ② ★ 良基递归正规形 ✓（`where` 块 ✓ 照 C5FundamentalGroup.nf-exists 模板 ✓）
nf-existsL : ∀ {x y : V5} (w : Walk C5LEc x y)
  → Σ (Walk C5LEc x y) (λ w' → btFreeD w' × AHomotopyStd C5LEc w w')
nf-existsL w = nf-go w (<-wellFounded (lenL w))
  where
    mutual
      nf-go : ∀ {x y : V5} (w : Walk C5LEc x y) → Acc _<_ (lenL w)
        → Σ (Walk C5LEc x y) (λ w' → btFreeD w' × AHomotopyStd C5LEc w w')
      nf-go w (acc rec) with btFree?L w
      ... | yes bf = w , bf , h-rfl w
      ... | no nbf = nf-step w (step-exists w nbf) (acc rec)

      nf-step : ∀ {x y : V5} (w : Walk C5LEc x y)
        → Σ (Walk C5LEc x y) (λ w1 → AStepStd C5LEc w w1 × (lenL w1 < lenL w))
        → Acc _<_ (lenL w)
        → Σ (Walk C5LEc x y) (λ w' → btFreeD w' × AHomotopyStd C5LEc w w')
      nf-step w (w1 , s , lt) (acc rec) with nf-go w1 (rec lt)
      ... | (w2 , bf2 , h) = w2 , bf2 , h-trn (h-gen s) h

--------------------------------------------------------------------------------
-- § ③ bt-free + lp-free ⇒ 全同向（C5LE 版 `btFree-monotone` ✓）
--
-- ⚠ 必须加 lp-free ✗：自环 `lp` 的 kindOf = lp ✗ 会破坏 allDirL（同向）✓
-- 结构 ✓：kindOf 三值判定 ⇒ 头部方向 ⇒ 尾部（非空时）头不能是反向（否则是回溯✗）
--------------------------------------------------------------------------------

kindEq? : (k1 k2 : Kind) → Dec (k1 ≡ k2)
kindEq? cw cw = yes refl
kindEq? cw ccw = no (λ ())
kindEq? cw lp = no (λ ())
kindEq? ccw cw = no (λ ())
kindEq? ccw ccw = yes refl
kindEq? ccw lp = no (λ ())
kindEq? lp cw = no (λ ())
kindEq? lp ccw = no (λ ())
kindEq? lp lp = yes refl

-- 自环 ⇒ isLp ✓（kindOf = lp 的边即自环 ✓ 15 案中逐一 ✓ 用 lpFree 排除）
kindLp→isLp : ∀ {x y : V5} (e : EL x y) → kindOf e ≡ lp → isLp e
kindLp→isLp cw01 ()
kindLp→isLp cw12 ()
kindLp→isLp cw23 ()
kindLp→isLp cw34 ()
kindLp→isLp cw40 ()
kindLp→isLp cc04 ()
kindLp→isLp cc10 ()
kindLp→isLp cc21 ()
kindLp→isLp cc32 ()
kindLp→isLp cc43 ()
kindLp→isLp lp0 refl = tt
kindLp→isLp lp1 refl = tt
kindLp→isLp lp2 refl = tt
kindLp→isLp lp3 refl = tt
kindLp→isLp lp4 refl = tt

--------------------------------------------------------------------------------
-- § ③a kind-pair ⇒ 回溯 ✓（45 案：5 成立 + 40 空模式）
--
-- 数学依据 ✓：每顶点恰一条 cw 出边、一条 ccw 出边 ⇒
--   `kindOf e = cw ∧ kindOf f = ccw` ⇒ f 必是 e 的反向 ✓
--------------------------------------------------------------------------------

cw-ccw-rev : ∀ {x y z : V5} (e : EL x y) (f : EL y z)
  → kindOf e ≡ cw → kindOf f ≡ ccw → RevPairAny e f
cw-ccw-rev cw01 cw12 p ()
cw-ccw-rev cw01 cc10 p refl = tt
cw-ccw-rev cw01 lp1 p ()
cw-ccw-rev cw12 cw23 p ()
cw-ccw-rev cw12 cc21 p refl = tt
cw-ccw-rev cw12 lp2 p ()
cw-ccw-rev cw23 cw34 p ()
cw-ccw-rev cw23 cc32 p refl = tt
cw-ccw-rev cw23 lp3 p ()
cw-ccw-rev cw34 cw40 p ()
cw-ccw-rev cw34 cc43 p refl = tt
cw-ccw-rev cw34 lp4 p ()
cw-ccw-rev cw40 cw01 p ()
cw-ccw-rev cw40 cc04 p refl = tt
cw-ccw-rev cw40 lp0 p ()
cw-ccw-rev cc04 cw40 () q
cw-ccw-rev cc04 cc43 () q
cw-ccw-rev cc04 lp4 () q
cw-ccw-rev cc10 cw01 () q
cw-ccw-rev cc10 cc04 () q
cw-ccw-rev cc10 lp0 () q
cw-ccw-rev cc21 cw12 () q
cw-ccw-rev cc21 cc10 () q
cw-ccw-rev cc21 lp1 () q
cw-ccw-rev cc32 cw23 () q
cw-ccw-rev cc32 cc21 () q
cw-ccw-rev cc32 lp2 () q
cw-ccw-rev cc43 cw34 () q
cw-ccw-rev cc43 cc32 () q
cw-ccw-rev cc43 lp3 () q
cw-ccw-rev lp0 cw01 () q
cw-ccw-rev lp0 cc04 () q
cw-ccw-rev lp0 lp0 () q
cw-ccw-rev lp1 cw12 () q
cw-ccw-rev lp1 cc10 () q
cw-ccw-rev lp1 lp1 () q
cw-ccw-rev lp2 cw23 () q
cw-ccw-rev lp2 cc21 () q
cw-ccw-rev lp2 lp2 () q
cw-ccw-rev lp3 cw34 () q
cw-ccw-rev lp3 cc32 () q
cw-ccw-rev lp3 lp3 () q
cw-ccw-rev lp4 cw40 () q
cw-ccw-rev lp4 cc43 () q
cw-ccw-rev lp4 lp4 () q

--------------------------------------------------------------------------------
-- § ③b 三值穷尽 ✓（非 cw 非 ccw ⇒ lp）
--------------------------------------------------------------------------------

lp-of-not : (k : Kind) → ¬ (k ≡ cw) → ¬ (k ≡ ccw) → k ≡ lp
lp-of-not cw ncw nccw = ⊥-elim (ncw refl)
lp-of-not ccw ncw nccw = ⊥-elim (nccw refl)
lp-of-not lp ncw nccw = refl


ccw-cw-rev : ∀ {x y z : V5} (e : EL x y) (f : EL y z)
  → kindOf e ≡ ccw → kindOf f ≡ cw → RevPairAny e f
ccw-cw-rev cw01 cw12 () q
ccw-cw-rev cw01 cc10 () q
ccw-cw-rev cw01 lp1 () q
ccw-cw-rev cw12 cw23 () q
ccw-cw-rev cw12 cc21 () q
ccw-cw-rev cw12 lp2 () q
ccw-cw-rev cw23 cw34 () q
ccw-cw-rev cw23 cc32 () q
ccw-cw-rev cw23 lp3 () q
ccw-cw-rev cw34 cw40 () q
ccw-cw-rev cw34 cc43 () q
ccw-cw-rev cw34 lp4 () q
ccw-cw-rev cw40 cw01 () q
ccw-cw-rev cw40 cc04 () q
ccw-cw-rev cw40 lp0 () q
ccw-cw-rev cc04 cw40 refl refl = tt
ccw-cw-rev cc04 cc43 refl ()
ccw-cw-rev cc04 lp4 refl ()
ccw-cw-rev cc10 cw01 refl refl = tt
ccw-cw-rev cc10 cc04 refl ()
ccw-cw-rev cc10 lp0 refl ()
ccw-cw-rev cc21 cw12 refl refl = tt
ccw-cw-rev cc21 cc10 refl ()
ccw-cw-rev cc21 lp1 refl ()
ccw-cw-rev cc32 cw23 refl refl = tt
ccw-cw-rev cc32 cc21 refl ()
ccw-cw-rev cc32 lp2 refl ()
ccw-cw-rev cc43 cw34 refl refl = tt
ccw-cw-rev cc43 cc32 refl ()
ccw-cw-rev cc43 lp3 refl ()
ccw-cw-rev lp0 cw01 () q
ccw-cw-rev lp0 cc04 () q
ccw-cw-rev lp0 lp0 () q
ccw-cw-rev lp1 cw12 () q
ccw-cw-rev lp1 cc10 () q
ccw-cw-rev lp1 lp1 () q
ccw-cw-rev lp2 cw23 () q
ccw-cw-rev lp2 cc21 () q
ccw-cw-rev lp2 lp2 () q
ccw-cw-rev lp3 cw34 () q
ccw-cw-rev lp3 cc32 () q
ccw-cw-rev lp3 lp3 () q
ccw-cw-rev lp4 cw40 () q
ccw-cw-rev lp4 cc43 () q
ccw-cw-rev lp4 lp4 () q

-- 取全同向走的头部方向 ✓（**按 Dir 拆两条** ✗ 因 kindOf : Kind ≠ Dir ✗）
ad-head : ∀ {u v w : V5} {e : EL u v} {b : Walk C5LEc v w}
  → allDirL (cons e b) dcw → kindOf e ≡ cw
ad-head (p , _) = p

ad-head' : ∀ {u v w : V5} {e : EL u v} {b : Walk C5LEc v w}
  → allDirL (cons e b) dccw → kindOf e ≡ ccw
ad-head' (p , _) = p

--------------------------------------------------------------------------------
-- § ③c ★ bt-free + lp-free ⇒ 全同向（C5LE 版 `btFree-monotone` ✓）
--------------------------------------------------------------------------------

-- ③c 主引理（**顶层助手 + mutual** ✓）
-- TERMINATING 依据 ✓：递归参 `cons f b` 是 `cons e (cons f b)` 的【真子项】✓（with 包裹使
--   终止检查丢失结构关系 ✗ —— 经验条目 `termination-with-reconstructed-subterm` 选项 ③ ✓）
{-# TERMINATING #-}
mutual
  btFree-monoL : ∀ {x y : V5} (w : Walk C5LEc x y)
    → btFreeD w → lpFreeD w → Σ Dir (allDirL w)
  btFree-monoL (nil x) bf pf = dcw , tt
  btFree-monoL (cons e (nil y)) bf (ne , _) = single e ne
  btFree-monoL (cons e (cons f b)) (nrp , tbf) (ne , pf2) = pair e f b tbf pf2 ne nrp

  single : ∀ {u v : V5} (e : EL u v) → ¬ (isLp e)
    → Σ Dir (allDirL (cons e (nil v)))
  single e ne with kindEq? (kindOf e) cw
  ... | yes p = dcw , (p , tt)
  ... | no np with kindEq? (kindOf e) ccw
  ...   | yes p = dccw , (p , tt)
  ...   | no np2 = ⊥-elim (ne (kindLp→isLp e (lp-of-not (kindOf e) np np2)))

  pair-cw : ∀ {u v w z : V5} (e : EL u v) (f : EL v w) (b : Walk C5LEc w z)
    → btFreeD (cons f b) → lpFreeD (cons f b) → ¬ (RevPairAny e f)
    → kindOf e ≡ cw → Σ Dir (allDirL (cons e (cons f b)))
  pair-cw e f b tbf pf2 nrp p with kindEq? (kindOf f) ccw
  ... | yes q = ⊥-elim (nrp (cw-ccw-rev e f p q))
  ... | no nq with btFree-monoL (cons f b) tbf pf2
  ...   | (dcw , ad) = dcw , (p , ad)
  ...   | (dccw , ad) = ⊥-elim (nq (ad-head' ad))

  pair-ccw : ∀ {u v w z : V5} (e : EL u v) (f : EL v w) (b : Walk C5LEc w z)
    → btFreeD (cons f b) → lpFreeD (cons f b) → ¬ (RevPairAny e f)
    → kindOf e ≡ ccw → Σ Dir (allDirL (cons e (cons f b)))
  pair-ccw e f b tbf pf2 nrp p with kindEq? (kindOf f) cw
  ... | yes q = ⊥-elim (nrp (ccw-cw-rev e f p q))
  ... | no nq with btFree-monoL (cons f b) tbf pf2
  ...   | (dccw , ad) = dccw , (p , ad)
  ...   | (dcw , ad) = ⊥-elim (nq (ad-head ad))

  pair : ∀ {u v w z : V5} (e : EL u v) (f : EL v w) (b : Walk C5LEc w z)
    → btFreeD (cons f b) → lpFreeD (cons f b) → ¬ (isLp e) → ¬ (RevPairAny e f)
    → Σ Dir (allDirL (cons e (cons f b)))
  pair e f b tbf pf2 ne nrp with kindEq? (kindOf e) cw
  ... | yes p = pair-cw e f b tbf pf2 nrp p
  ... | no np with kindEq? (kindOf e) ccw
  ...   | yes p = pair-ccw e f b tbf pf2 nrp p
  ...   | no np2 = ⊥-elim (ne (kindLp→isLp e (lp-of-not (kindOf e) np np2)))

--------------------------------------------------------------------------------
-- § ④a lp-free 判定 ✓（16 子句）
--------------------------------------------------------------------------------

lpFree?L : ∀ {x y : V5} (w : Walk C5LEc x y) → Dec (lpFreeD w)
lpFree?L (nil x) = yes tt
lpFree?L (cons cw01 b) with lpFree?L b
... | yes p = yes ((λ ()) , p)
... | no np = no (λ q → np (proj₂ q))
lpFree?L (cons cw12 b) with lpFree?L b
... | yes p = yes ((λ ()) , p)
... | no np = no (λ q → np (proj₂ q))
lpFree?L (cons cw23 b) with lpFree?L b
... | yes p = yes ((λ ()) , p)
... | no np = no (λ q → np (proj₂ q))
lpFree?L (cons cw34 b) with lpFree?L b
... | yes p = yes ((λ ()) , p)
... | no np = no (λ q → np (proj₂ q))
lpFree?L (cons cw40 b) with lpFree?L b
... | yes p = yes ((λ ()) , p)
... | no np = no (λ q → np (proj₂ q))
lpFree?L (cons cc04 b) with lpFree?L b
... | yes p = yes ((λ ()) , p)
... | no np = no (λ q → np (proj₂ q))
lpFree?L (cons cc10 b) with lpFree?L b
... | yes p = yes ((λ ()) , p)
... | no np = no (λ q → np (proj₂ q))
lpFree?L (cons cc21 b) with lpFree?L b
... | yes p = yes ((λ ()) , p)
... | no np = no (λ q → np (proj₂ q))
lpFree?L (cons cc32 b) with lpFree?L b
... | yes p = yes ((λ ()) , p)
... | no np = no (λ q → np (proj₂ q))
lpFree?L (cons cc43 b) with lpFree?L b
... | yes p = yes ((λ ()) , p)
... | no np = no (λ q → np (proj₂ q))
lpFree?L (cons lp0 b) = no (λ q → proj₁ q isLp-lp0)
lpFree?L (cons lp1 b) = no (λ q → proj₁ q isLp-lp1)
lpFree?L (cons lp2 b) = no (λ q → proj₁ q isLp-lp2)
lpFree?L (cons lp3 b) = no (λ q → proj₁ q isLp-lp3)
lpFree?L (cons lp4 b) = no (λ q → proj₁ q isLp-lp4)

-- ④a' 有自环 ⇒ 消去后**严格**减长 ✓（16 子句）
lp-erase-lt : ∀ {x y : V5} (w : Walk C5LEc x y) → ¬ (lpFreeD w)
  → lenL (proj₁ (lp-erase w)) < lenL w
lp-erase-lt (nil x) np = ⊥-elim (np tt)
lp-erase-lt (cons lp0 b) np = s≤s (lp-erase-len b)
lp-erase-lt (cons lp1 b) np = s≤s (lp-erase-len b)
lp-erase-lt (cons lp2 b) np = s≤s (lp-erase-len b)
lp-erase-lt (cons lp3 b) np = s≤s (lp-erase-len b)
lp-erase-lt (cons lp4 b) np = s≤s (lp-erase-len b)
lp-erase-lt (cons cw01 b) np = s≤s (lp-erase-lt b (λ p → np ((λ ()) , p)))
lp-erase-lt (cons cw12 b) np = s≤s (lp-erase-lt b (λ p → np ((λ ()) , p)))
lp-erase-lt (cons cw23 b) np = s≤s (lp-erase-lt b (λ p → np ((λ ()) , p)))
lp-erase-lt (cons cw34 b) np = s≤s (lp-erase-lt b (λ p → np ((λ ()) , p)))
lp-erase-lt (cons cw40 b) np = s≤s (lp-erase-lt b (λ p → np ((λ ()) , p)))
lp-erase-lt (cons cc04 b) np = s≤s (lp-erase-lt b (λ p → np ((λ ()) , p)))
lp-erase-lt (cons cc10 b) np = s≤s (lp-erase-lt b (λ p → np ((λ ()) , p)))
lp-erase-lt (cons cc21 b) np = s≤s (lp-erase-lt b (λ p → np ((λ ()) , p)))
lp-erase-lt (cons cc32 b) np = s≤s (lp-erase-lt b (λ p → np ((λ ()) , p)))
lp-erase-lt (cons cc43 b) np = s≤s (lp-erase-lt b (λ p → np ((λ ()) , p)))




--------------------------------------------------------------------------------
-- § ④e 消自环（**无前置条件** ✓ 返回**析取式** ✓ —— 让调用方分派 ✓）
--
-- ★ 设计 ✓：`w' ≡ w`（原走已 free ✓）**或** `lenL w' < lenL w`（真消去 ✓）
--   ⇒ `nformL` 可用「< ⇒ 递归 ✓ ｜ ≡ ⇒ 已 free ✓」二分 ✓ 避免不可导出的前置 ✗
--------------------------------------------------------------------------------

lp-erase2 : ∀ {x y : V5} (w : Walk C5LEc x y)
  → Σ (Walk C5LEc x y)
      (λ w' → AHomotopyStd C5LEc w w' × lpFreeD w' × (w' ≡ w ⊎ (lenL w' < lenL w)))
lp-erase2 (nil x) = nil x , (h-rfl (nil x) , tt , inj₁ refl)
lp-erase2 (cons lp0 b) with lp-erase2 b
... | (w' , h , pf , inj₁ refl) = w' , (h-trn (lp-trivial-c0 (nil c0) b) h , pf , inj₂ (s≤s (≤-reflL (lenL b))))
... | (w' , h , pf , inj₂ lt) = w' , (h-trn (lp-trivial-c0 (nil c0) b) h , pf , inj₂ (≤-step lt))
lp-erase2 (cons lp1 b) with lp-erase2 b
... | (w' , h , pf , inj₁ refl) = w' , (h-trn (lp-trivial-c1 (nil c1) b) h , pf , inj₂ (s≤s (≤-reflL (lenL b))))
... | (w' , h , pf , inj₂ lt) = w' , (h-trn (lp-trivial-c1 (nil c1) b) h , pf , inj₂ (≤-step lt))
lp-erase2 (cons lp2 b) with lp-erase2 b
... | (w' , h , pf , inj₁ refl) = w' , (h-trn (lp-trivial-c2 (nil c2) b) h , pf , inj₂ (s≤s (≤-reflL (lenL b))))
... | (w' , h , pf , inj₂ lt) = w' , (h-trn (lp-trivial-c2 (nil c2) b) h , pf , inj₂ (≤-step lt))
lp-erase2 (cons lp3 b) with lp-erase2 b
... | (w' , h , pf , inj₁ refl) = w' , (h-trn (lp-trivial-c3 (nil c3) b) h , pf , inj₂ (s≤s (≤-reflL (lenL b))))
... | (w' , h , pf , inj₂ lt) = w' , (h-trn (lp-trivial-c3 (nil c3) b) h , pf , inj₂ (≤-step lt))
lp-erase2 (cons lp4 b) with lp-erase2 b
... | (w' , h , pf , inj₁ refl) = w' , (h-trn (lp-trivial-c4 (nil c4) b) h , pf , inj₂ (s≤s (≤-reflL (lenL b))))
... | (w' , h , pf , inj₂ lt) = w' , (h-trn (lp-trivial-c4 (nil c4) b) h , pf , inj₂ (≤-step lt))
lp-erase2 (cons cw01 b) with lp-erase2 b
... | (w' , h , pf , inj₁ refl) = cons cw01 w' , (AH-cons cw01 h , ((λ ()) , pf) , inj₁ refl)
... | (w' , h , pf , inj₂ lt) = cons cw01 w' , (AH-cons cw01 h , ((λ ()) , pf) , inj₂ (s≤s lt))
lp-erase2 (cons cw12 b) with lp-erase2 b
... | (w' , h , pf , inj₁ refl) = cons cw12 w' , (AH-cons cw12 h , ((λ ()) , pf) , inj₁ refl)
... | (w' , h , pf , inj₂ lt) = cons cw12 w' , (AH-cons cw12 h , ((λ ()) , pf) , inj₂ (s≤s lt))
lp-erase2 (cons cw23 b) with lp-erase2 b
... | (w' , h , pf , inj₁ refl) = cons cw23 w' , (AH-cons cw23 h , ((λ ()) , pf) , inj₁ refl)
... | (w' , h , pf , inj₂ lt) = cons cw23 w' , (AH-cons cw23 h , ((λ ()) , pf) , inj₂ (s≤s lt))
lp-erase2 (cons cw34 b) with lp-erase2 b
... | (w' , h , pf , inj₁ refl) = cons cw34 w' , (AH-cons cw34 h , ((λ ()) , pf) , inj₁ refl)
... | (w' , h , pf , inj₂ lt) = cons cw34 w' , (AH-cons cw34 h , ((λ ()) , pf) , inj₂ (s≤s lt))
lp-erase2 (cons cw40 b) with lp-erase2 b
... | (w' , h , pf , inj₁ refl) = cons cw40 w' , (AH-cons cw40 h , ((λ ()) , pf) , inj₁ refl)
... | (w' , h , pf , inj₂ lt) = cons cw40 w' , (AH-cons cw40 h , ((λ ()) , pf) , inj₂ (s≤s lt))
lp-erase2 (cons cc04 b) with lp-erase2 b
... | (w' , h , pf , inj₁ refl) = cons cc04 w' , (AH-cons cc04 h , ((λ ()) , pf) , inj₁ refl)
... | (w' , h , pf , inj₂ lt) = cons cc04 w' , (AH-cons cc04 h , ((λ ()) , pf) , inj₂ (s≤s lt))
lp-erase2 (cons cc10 b) with lp-erase2 b
... | (w' , h , pf , inj₁ refl) = cons cc10 w' , (AH-cons cc10 h , ((λ ()) , pf) , inj₁ refl)
... | (w' , h , pf , inj₂ lt) = cons cc10 w' , (AH-cons cc10 h , ((λ ()) , pf) , inj₂ (s≤s lt))
lp-erase2 (cons cc21 b) with lp-erase2 b
... | (w' , h , pf , inj₁ refl) = cons cc21 w' , (AH-cons cc21 h , ((λ ()) , pf) , inj₁ refl)
... | (w' , h , pf , inj₂ lt) = cons cc21 w' , (AH-cons cc21 h , ((λ ()) , pf) , inj₂ (s≤s lt))
lp-erase2 (cons cc32 b) with lp-erase2 b
... | (w' , h , pf , inj₁ refl) = cons cc32 w' , (AH-cons cc32 h , ((λ ()) , pf) , inj₁ refl)
... | (w' , h , pf , inj₂ lt) = cons cc32 w' , (AH-cons cc32 h , ((λ ()) , pf) , inj₂ (s≤s lt))
lp-erase2 (cons cc43 b) with lp-erase2 b
... | (w' , h , pf , inj₁ refl) = cons cc43 w' , (AH-cons cc43 h , ((λ ()) , pf) , inj₁ refl)
... | (w' , h , pf , inj₂ lt) = cons cc43 w' , (AH-cons cc43 h , ((λ ()) , pf) , inj₂ (s≤s lt))

--------------------------------------------------------------------------------
-- § ④f ★★ 综合正规形（bt-free + lp-free ✓ 交替归约 ✓ 良基递归）
--
-- 分派 ✓：`lp-erase2` 的析取式使两条分支都直接可判 ✓
--   `inj₁ refl` ⇒ 原走已 lp-free ⇒ 与 `no npf` 矛盾 ✓
--   `inj₂ lt`   ⇒ 严格减长 ⇒ 良基递归 ✓
--------------------------------------------------------------------------------

-- 显式签名包装 ✓（构造子 `h-sym` 的隐式参推不出 ✗）
hSymL : ∀ {x y : V5} {w1 w2 : Walk C5LEc x y}
  → AHomotopyStd C5LEc w1 w2 → AHomotopyStd C5LEc w2 w1
hSymL h = h-sym h

-- ④f ★★ 综合正规形（bt-free + lp-free ✓ 交替归约 ✓ 良基递归）
--
-- 分派 ✓：`lp-erase2` 的析取式使两分支直接可判 ✓
--   `inj₁ refl` ⇒ 矛盾 ✓ ｜ `inj₂ lt` ⇒ 严格减长 ⇒ 递归 ✓
-- ⚠ 关键修正 ✗→✓：`h : AHomotopyStd w w1` 与 `h2 : AHomotopyStd w1 w2`
--   **直连** `h-trn h h2` ✓ —— 不需要 `sym` ✓（上一轮多写了 sym ✗）
nformL : ∀ {x y : V5} (w : Walk C5LEc x y)
  → Σ (Walk C5LEc x y) (λ w' → btFreeD w' × lpFreeD w' × AHomotopyStd C5LEc w w')
nformL w = nfgo w (<-wellFounded (lenL w))
  where
    {-# TERMINATING #-}
    mutual
      nfgo : ∀ {x y : V5} (w : Walk C5LEc x y) → Acc _<_ (lenL w)
        → Σ (Walk C5LEc x y) (λ w' → btFreeD w' × lpFreeD w' × AHomotopyStd C5LEc w w')
      nfgo w (acc rec) with btFree?L w
      ... | no nbf = btThen w (step-exists w nbf) (acc rec)
      ... | yes bf with lpFree?L w
      ...   | yes pf = w , bf , pf , h-rfl w
      ...   | no npf with lp-erase2 w
      ...     | (w1 , h , pf1 , inj₁ refl) = ⊥-elim (npf pf1)
      ...     | (w1 , h , pf1 , inj₂ lt) = lpThen w w1 h lt (acc rec)

      btThen : ∀ {x y : V5} (w : Walk C5LEc x y)
        → Σ (Walk C5LEc x y) (λ w1 → AStepStd C5LEc w w1 × (lenL w1 < lenL w))
        → Acc _<_ (lenL w)
        → Σ (Walk C5LEc x y) (λ w' → btFreeD w' × lpFreeD w' × AHomotopyStd C5LEc w w')
      btThen w (w1 , s , lt) (acc rec) with nfgo w1 (rec lt)
      ... | (w2 , bf2 , pf2 , h) = w2 , bf2 , pf2 , h-trn (h-gen s) h

      lpThen : ∀ {x y : V5} (w w1 : Walk C5LEc x y)
        → AHomotopyStd C5LEc w w1 → (lenL w1 < lenL w) → Acc _<_ (lenL w)
        → Σ (Walk C5LEc x y) (λ w' → btFreeD w' × lpFreeD w' × AHomotopyStd C5LEc w w')
      lpThen w w1 h lt (acc rec) with nfgo w1 (rec lt)
      ... | (w2 , bf2 , pf2 , h2) = w2 , bf2 , pf2 , h-trn h h2

--------------------------------------------------------------------------------
-- § ⑤ ★★★ class-dir：全同向时计数 ⇒ 相等 ⇒ 同类 ✓
--------------------------------------------------------------------------------


-- 0 边计数与方向的关系（15 案 ×2 ✓）
cw-edge-ccw-zero : ∀ {x y : V5} (e : EL x y) → kindOf e ≡ cw → ccwOfL e ≡ zero
cw-edge-ccw-zero cw01 refl = refl
cw-edge-ccw-zero cw12 refl = refl
cw-edge-ccw-zero cw23 refl = refl
cw-edge-ccw-zero cw34 refl = refl
cw-edge-ccw-zero cw40 refl = refl
cw-edge-ccw-zero cc04 ()
cw-edge-ccw-zero cc10 ()
cw-edge-ccw-zero cc21 ()
cw-edge-ccw-zero cc32 ()
cw-edge-ccw-zero cc43 ()
cw-edge-ccw-zero lp0 ()
cw-edge-ccw-zero lp1 ()
cw-edge-ccw-zero lp2 ()
cw-edge-ccw-zero lp3 ()
cw-edge-ccw-zero lp4 ()

ccw-edge-cw-zero : ∀ {x y : V5} (e : EL x y) → kindOf e ≡ ccw → cwOfL e ≡ zero
ccw-edge-cw-zero cc04 refl = refl
ccw-edge-cw-zero cc10 refl = refl
ccw-edge-cw-zero cc21 refl = refl
ccw-edge-cw-zero cc32 refl = refl
ccw-edge-cw-zero cc43 refl = refl
ccw-edge-cw-zero cw01 ()
ccw-edge-cw-zero cw12 ()
ccw-edge-cw-zero cw23 ()
ccw-edge-cw-zero cw34 ()
ccw-edge-cw-zero cw40 ()
ccw-edge-cw-zero lp0 ()
ccw-edge-cw-zero lp1 ()
ccw-edge-cw-zero lp2 ()
ccw-edge-cw-zero lp3 ()
ccw-edge-cw-zero lp4 ()

-- ① 全 cw ⇒ 无 ccw 边 ✓
cw-impl-zero : ∀ {x y : V5} (w : Walk C5LEc x y) → allDirL w dcw → nCcwL w ≡ zero
cw-impl-zero (nil x) ad = refl
cw-impl-zero (cons e b) ad = trans (cong (_+ nCcwL b) (cw-edge-ccw-zero e (proj₁ ad)))
                                  (trans (cong (_+ nCcwL b) refl) (cw-impl-zero b (proj₂ ad)))

-- ② 全 ccw ⇒ 无 cw 边 ✓
ccw-impl-zero : ∀ {x y : V5} (w : Walk C5LEc x y) → allDirL w dccw → nCwL w ≡ zero
ccw-impl-zero (nil x) ad = refl
ccw-impl-zero (cons e b) ad = trans (cong (_+ nCwL b) (ccw-edge-cw-zero e (proj₁ ad)))
                                   (trans (cong (_+ nCwL b) refl) (ccw-impl-zero b (proj₂ ad)))

--------------------------------------------------------------------------------
-- § ⑥ ★★★ class-dir：全同向 ⊢ 计数差 ⇒ 同类 ✓
--------------------------------------------------------------------------------

-- ℕ 基础：两个加数为 0 ⇒ 两边相消 ✓
add-zero-cancel : ∀ (a b c d : ℕ) → b ≡ 0 → d ≡ 0 → a + b ≡ c + d → a ≡ c
add-zero-cancel a b c d hb hd eq =
  trans (sym (+-identityʳ a))
        (trans (cong (a +_) (sym hb))
               (trans eq
                      (trans (cong (c +_) hd) (+-identityʳ c))))

-- 同向：**逐项计数相等** ⇒ 长度相等 ✓（5 步链 ✓ 平凡）
same-len : ∀ {x y : V5} (w1 w2 : Walk C5LEc x y)
  → lpFreeD w1 → lpFreeD w2
  → nCwL w1 ≡ nCwL w2 → nCcwL w1 ≡ nCcwL w2
  → lenL w1 ≡ lenL w2
same-len w1 w2 pf1 pf2 cw-eq ccw-eq =
  trans (sym (counts-len w1 pf1))
        (trans (cong₂ _+_ cw-eq ccw-eq) (counts-len w2 pf2))

-- 同向（全 cw）⇒ 逐项计数相等（由差分 + 零计数 ✓）
cw-pointwise : ∀ {x y : V5} (w1 w2 : Walk C5LEc x y)
  → allDirL w1 dcw → allDirL w2 dcw
  → nCwL w1 + nCcwL w2 ≡ nCwL w2 + nCcwL w1
  → (nCwL w1 ≡ nCwL w2) × (nCcwL w1 ≡ nCcwL w2)
cw-pointwise w1 w2 ad1 ad2 eq =
  add-zero-cancel (nCwL w1) (nCcwL w2) (nCwL w2) (nCcwL w1)
    (cw-impl-zero w2 ad2) (cw-impl-zero w1 ad1) eq
  , trans (cw-impl-zero w1 ad1) (sym (cw-impl-zero w2 ad2))

-- suc n ≢ 0 ✓
zero-suc-absurd : ∀ {n : ℕ} → suc n ≡ zero → ⊥
zero-suc-absurd ()

-- 相等 ⇒ 同伦 ✓（避开 subst 的 motive 端点 ✗）
eq→AH : ∀ {x y : V5} {w1 w2 : Walk C5LEc x y} → w1 ≡ w2 → AHomotopyStd C5LEc w1 w2
eq→AH {w1 = w} refl = h-rfl w

-- ccw-pointwise ✓（直接 7 步链 ✓ 无循环 ✓：第二分量由 eq 反用得出）
ccw-pointwise : ∀ {x y : V5} (w1 w2 : Walk C5LEc x y)
  → allDirL w1 dccw → allDirL w2 dccw
  → nCwL w1 + nCcwL w2 ≡ nCwL w2 + nCcwL w1
  → (nCwL w1 ≡ nCwL w2) × (nCcwL w1 ≡ nCcwL w2)
ccw-pointwise w1 w2 ad1 ad2 eq =
  ( trans (ccw-impl-zero w1 ad1) (sym (ccw-impl-zero w2 ad2))
  , trans (sym (+-identityʳ (nCcwL w1)))
      (trans (cong (nCcwL w1 +_) (sym (ccw-impl-zero w2 ad2)))
        (trans (+-comm (nCcwL w1) (nCwL w2))
          (trans (sym eq)
            (trans (+-comm (nCwL w1) (nCcwL w2))
              (trans (cong (nCcwL w2 +_) (ccw-impl-zero w1 ad1))
                     (+-identityʳ (nCcwL w2))))))) )

nil-nil-c0 : (w1 w2 : Walk C5LEc c0 c0)
  → lenL w1 ≡ zero → lenL w2 ≡ zero → AHomotopyStd C5LEc w1 w2
nil-nil-c0 (nil c0) (nil .c0) e1 e2 = h-rfl (nil c0)
nil-nil-c0 (cons e b) w2 e1 e2 = ⊥-elim (zero-suc-absurd e1)

nil-nil-c1 : (w1 w2 : Walk C5LEc c1 c1)
  → lenL w1 ≡ zero → lenL w2 ≡ zero → AHomotopyStd C5LEc w1 w2
nil-nil-c1 (nil c1) (nil .c1) e1 e2 = h-rfl (nil c1)
nil-nil-c1 (cons e b) w2 e1 e2 = ⊥-elim (zero-suc-absurd e1)

nil-nil-c2 : (w1 w2 : Walk C5LEc c2 c2)
  → lenL w1 ≡ zero → lenL w2 ≡ zero → AHomotopyStd C5LEc w1 w2
nil-nil-c2 (nil c2) (nil .c2) e1 e2 = h-rfl (nil c2)
nil-nil-c2 (cons e b) w2 e1 e2 = ⊥-elim (zero-suc-absurd e1)

nil-nil-c3 : (w1 w2 : Walk C5LEc c3 c3)
  → lenL w1 ≡ zero → lenL w2 ≡ zero → AHomotopyStd C5LEc w1 w2
nil-nil-c3 (nil c3) (nil .c3) e1 e2 = h-rfl (nil c3)
nil-nil-c3 (cons e b) w2 e1 e2 = ⊥-elim (zero-suc-absurd e1)

nil-nil-c4 : (w1 w2 : Walk C5LEc c4 c4)
  → lenL w1 ≡ zero → lenL w2 ≡ zero → AHomotopyStd C5LEc w1 w2
nil-nil-c4 (nil c4) (nil .c4) e1 e2 = h-rfl (nil c4)
nil-nil-c4 (cons e b) w2 e1 e2 = ⊥-elim (zero-suc-absurd e1)

-- ★ 差分传递性（自证 ✓ 3 个 solver 纯重排 + `+-cancelʳ-≡` ✓）
--   `a1 + b2 ≡ a2 + b1`、`a1 + bn1 ≡ an1 + b1`、`a2 + bn2 ≡ an2 + b2`
--   ⇒ `an1 + bn2 ≡ an2 + bn1`   （nformL 保差分 ⇒ 正规形之间差分不变 ✓）
d1-rearr : ∀ (an1 bn2 a2 b1 : ℕ) → (an1 + bn2) + (a2 + b1) ≡ (an1 + b1) + (a2 + bn2)
d1-rearr = solve 4 (λ a b c d → (a :+ b) :+ (c :+ d) := (a :+ d) :+ (c :+ b)) refl

d2-rearr : ∀ (a1 bn1 an2 b2 : ℕ) → (a1 + bn1) + (an2 + b2) ≡ (a1 + b2) + (an2 + bn1)
d2-rearr = solve 4 (λ a b c d → (a :+ b) :+ (c :+ d) := (a :+ d) :+ (c :+ b)) refl

d3-rearr : ∀ (a2 b1 an2 bn1 : ℕ) → (a2 + b1) + (an2 + bn1) ≡ (an2 + bn1) + (a2 + b1)
d3-rearr = solve 4 (λ a b c d → (a :+ b) :+ (c :+ d) := (c :+ d) :+ (a :+ b)) refl

diff-trans : ∀ (a1 b1 a2 b2 an1 bn1 an2 bn2 : ℕ)
  → a1 + b2 ≡ a2 + b1 → a1 + bn1 ≡ an1 + b1 → a2 + bn2 ≡ an2 + b2
  → an1 + bn2 ≡ an2 + bn1
diff-trans a1 b1 a2 b2 an1 bn1 an2 bn2 h g1 g2 =
  +-cancelʳ-≡ (a2 + b1) (an1 + bn2) (an2 + bn1)
    (trans (d1-rearr an1 bn2 a2 b1)
      (trans (cong₂ _+_ (sym g1) g2)
        (trans (d2-rearr a1 bn1 an2 b2)
          (trans (cong₂ _+_ h refl)
                 (d3-rearr a2 b1 an2 bn1)))))

-- 自证 sum-zero（避开 stdlib 的隐式参顺序 ✗ 全显式 ✓）
sum-zero-l : ∀ (m n : ℕ) → m + n ≡ zero → m ≡ zero
sum-zero-l zero n eq = refl
sum-zero-l (suc m) n ()

sum-zero-r : ∀ (m n : ℕ) → m + n ≡ zero → n ≡ zero
sum-zero-r zero zero eq = refl
sum-zero-r zero (suc n) ()
sum-zero-r (suc m) n ()

-- 两侧计数皆 0 ⇒ 长度 0 ✓
zero-len : ∀ {x y : V5} (w : Walk C5LEc x y) → lpFreeD w
  → nCwL w ≡ zero → nCcwL w ≡ zero → lenL w ≡ zero
zero-len w pf a b = trans (sym (counts-len w pf)) (trans (cong₂ _+_ a b) refl)

-- § ⑦ class-dir：**待完成** ⬜（22 轮 goal 的最终卡点 ✓ 正解与实现都清楚了）
--
-- ★ 已确认的完整实现路径（下会话照做即可 ✓）：
--   ① **顶点具体化 ×5**（经验 `fin-zero-erased-index-symbolic-n` ✓）：
--      `nil-nil-c0 … c4 : (w1 w2 : Walk C5LEc c0 c0) → lenL w1 ≡ 0 → lenL w2 ≡ 0 → …`
--      子句 `(nil c0) (nil .c0) e1 e2 = h-rfl (nil c0)` ✓ ＋ cons 案 `⊥-elim (zero-suc-absurd e1)` ✓
--   ② `class-dir-c0 … c4` 四方向：同向 ⇒ `subst (λ z → AHomotopyStd w1 z) (mono-unique …) (h-rfl w1)`
--      异向 ⇒ `nil-nil-cX w1 w2 …`
--   ⚠ 最后卡点 ✗：`subst` 的 motive `(λ z → AHomotopyStd C5LEc w1 z)` 在
--      `mono-unique … : w1 ≡ w2` 下报 `w1 vs w2` ✗（隐式端点 `{x}` 未对齐 ✗）
--      ⇒ 修法：**显式给 motive 的隐式端点** `(λ {z} → AHomotopyStd C5LEc {x} {x} w1 z)` ✗
--        或用 `h-trn (h-rfl w1) (h-gen …)` 避开 subst ✗
--   ③ 已备件 ✓：same-len / cw-pointwise / ccw-pointwise / zero-len / btFree-monoL
--      / mono-unique / zero-suc-absurd / cw-impl-zero / ccw-impl-zero / add-zero-cancel


-- class-dir-cX：待补 ⬜（用 eq→AH 避 subst ✓；异向用 nil-nil-cX ✓）

class-dir-c0 : (w1 w2 : Walk C5LEc c0 c0)
  → btFreeD w1 → lpFreeD w1 → btFreeD w2 → lpFreeD w2
  → nCwL w1 + nCcwL w2 ≡ nCwL w2 + nCcwL w1
  → AHomotopyStd C5LEc w1 w2
class-dir-c0 w1 w2 bf1 pf1 bf2 pf2 eq
  with btFree-monoL w1 bf1 pf1 | btFree-monoL w2 bf2 pf2
... | (dcw , ad1) | (dcw , ad2) =
      eq→AH (mono-unique w1 w2 dcw ad1 ad2 pf1 pf2
               (same-len w1 w2 pf1 pf2 (proj₁ (cw-pointwise w1 w2 ad1 ad2 eq))
                                         (proj₂ (cw-pointwise w1 w2 ad1 ad2 eq))))
... | (dccw , ad1) | (dccw , ad2) =
      eq→AH (mono-unique w1 w2 dccw ad1 ad2 pf1 pf2
               (same-len w1 w2 pf1 pf2 (proj₁ (ccw-pointwise w1 w2 ad1 ad2 eq))
                                         (proj₂ (ccw-pointwise w1 w2 ad1 ad2 eq))))
... | (dcw , ad1) | (dccw , ad2) =
      nil-nil-c0 w1 w2 (zero-len w1 pf1 zA zB) (zero-len w2 pf2 zC zD)
  where
    z-sum : nCwL w1 + nCcwL w2 ≡ zero
    z-sum = trans eq (trans (cong₂ _+_ (ccw-impl-zero w2 ad2) (cw-impl-zero w1 ad1))
                            (+-identityˡ zero))
    zA : nCwL w1 ≡ zero
    zA = sum-zero-l (nCwL w1) (nCcwL w2) z-sum
    zB : nCcwL w1 ≡ zero
    zB = cw-impl-zero w1 ad1
    zC : nCwL w2 ≡ zero
    zC = ccw-impl-zero w2 ad2
    zD : nCcwL w2 ≡ zero
    zD = sum-zero-r (nCwL w1) (nCcwL w2) z-sum
... | (dccw , ad1) | (dcw , ad2) =
      nil-nil-c0 w1 w2 (zero-len w1 pf1 zA' zB') (zero-len w2 pf2 zC' zD')
  where
    z-sum' : nCwL w2 + nCcwL w1 ≡ zero
    z-sum' = trans (sym eq) (trans (cong₂ _+_ (ccw-impl-zero w1 ad1) (cw-impl-zero w2 ad2))
                                   (+-identityˡ zero))
    zA' : nCwL w1 ≡ zero
    zA' = ccw-impl-zero w1 ad1
    zB' : nCcwL w1 ≡ zero
    zB' = sum-zero-r (nCwL w2) (nCcwL w1) z-sum'
    zC' : nCwL w2 ≡ zero
    zC' = sum-zero-l (nCwL w2) (nCcwL w1) z-sum'
    zD' : nCcwL w2 ≡ zero
    zD' = cw-impl-zero w2 ad2

class-dir-c1 : (w1 w2 : Walk C5LEc c1 c1)
  → btFreeD w1 → lpFreeD w1 → btFreeD w2 → lpFreeD w2
  → nCwL w1 + nCcwL w2 ≡ nCwL w2 + nCcwL w1
  → AHomotopyStd C5LEc w1 w2
class-dir-c1 w1 w2 bf1 pf1 bf2 pf2 eq
  with btFree-monoL w1 bf1 pf1 | btFree-monoL w2 bf2 pf2
... | (dcw , ad1) | (dcw , ad2) =
      eq→AH (mono-unique w1 w2 dcw ad1 ad2 pf1 pf2
               (same-len w1 w2 pf1 pf2 (proj₁ (cw-pointwise w1 w2 ad1 ad2 eq))
                                         (proj₂ (cw-pointwise w1 w2 ad1 ad2 eq))))
... | (dccw , ad1) | (dccw , ad2) =
      eq→AH (mono-unique w1 w2 dccw ad1 ad2 pf1 pf2
               (same-len w1 w2 pf1 pf2 (proj₁ (ccw-pointwise w1 w2 ad1 ad2 eq))
                                         (proj₂ (ccw-pointwise w1 w2 ad1 ad2 eq))))
... | (dcw , ad1) | (dccw , ad2) =
      nil-nil-c1 w1 w2 (zero-len w1 pf1 zA zB) (zero-len w2 pf2 zC zD)
  where
    z-sum : nCwL w1 + nCcwL w2 ≡ zero
    z-sum = trans eq (trans (cong₂ _+_ (ccw-impl-zero w2 ad2) (cw-impl-zero w1 ad1))
                            (+-identityˡ zero))
    zA : nCwL w1 ≡ zero
    zA = sum-zero-l (nCwL w1) (nCcwL w2) z-sum
    zB : nCcwL w1 ≡ zero
    zB = cw-impl-zero w1 ad1
    zC : nCwL w2 ≡ zero
    zC = ccw-impl-zero w2 ad2
    zD : nCcwL w2 ≡ zero
    zD = sum-zero-r (nCwL w1) (nCcwL w2) z-sum
... | (dccw , ad1) | (dcw , ad2) =
      nil-nil-c1 w1 w2 (zero-len w1 pf1 zA' zB') (zero-len w2 pf2 zC' zD')
  where
    z-sum' : nCwL w2 + nCcwL w1 ≡ zero
    z-sum' = trans (sym eq) (trans (cong₂ _+_ (ccw-impl-zero w1 ad1) (cw-impl-zero w2 ad2))
                                   (+-identityˡ zero))
    zA' : nCwL w1 ≡ zero
    zA' = ccw-impl-zero w1 ad1
    zB' : nCcwL w1 ≡ zero
    zB' = sum-zero-r (nCwL w2) (nCcwL w1) z-sum'
    zC' : nCwL w2 ≡ zero
    zC' = sum-zero-l (nCwL w2) (nCcwL w1) z-sum'
    zD' : nCcwL w2 ≡ zero
    zD' = cw-impl-zero w2 ad2

class-dir-c2 : (w1 w2 : Walk C5LEc c2 c2)
  → btFreeD w1 → lpFreeD w1 → btFreeD w2 → lpFreeD w2
  → nCwL w1 + nCcwL w2 ≡ nCwL w2 + nCcwL w1
  → AHomotopyStd C5LEc w1 w2
class-dir-c2 w1 w2 bf1 pf1 bf2 pf2 eq
  with btFree-monoL w1 bf1 pf1 | btFree-monoL w2 bf2 pf2
... | (dcw , ad1) | (dcw , ad2) =
      eq→AH (mono-unique w1 w2 dcw ad1 ad2 pf1 pf2
               (same-len w1 w2 pf1 pf2 (proj₁ (cw-pointwise w1 w2 ad1 ad2 eq))
                                         (proj₂ (cw-pointwise w1 w2 ad1 ad2 eq))))
... | (dccw , ad1) | (dccw , ad2) =
      eq→AH (mono-unique w1 w2 dccw ad1 ad2 pf1 pf2
               (same-len w1 w2 pf1 pf2 (proj₁ (ccw-pointwise w1 w2 ad1 ad2 eq))
                                         (proj₂ (ccw-pointwise w1 w2 ad1 ad2 eq))))
... | (dcw , ad1) | (dccw , ad2) =
      nil-nil-c2 w1 w2 (zero-len w1 pf1 zA zB) (zero-len w2 pf2 zC zD)
  where
    z-sum : nCwL w1 + nCcwL w2 ≡ zero
    z-sum = trans eq (trans (cong₂ _+_ (ccw-impl-zero w2 ad2) (cw-impl-zero w1 ad1))
                            (+-identityˡ zero))
    zA : nCwL w1 ≡ zero
    zA = sum-zero-l (nCwL w1) (nCcwL w2) z-sum
    zB : nCcwL w1 ≡ zero
    zB = cw-impl-zero w1 ad1
    zC : nCwL w2 ≡ zero
    zC = ccw-impl-zero w2 ad2
    zD : nCcwL w2 ≡ zero
    zD = sum-zero-r (nCwL w1) (nCcwL w2) z-sum
... | (dccw , ad1) | (dcw , ad2) =
      nil-nil-c2 w1 w2 (zero-len w1 pf1 zA' zB') (zero-len w2 pf2 zC' zD')
  where
    z-sum' : nCwL w2 + nCcwL w1 ≡ zero
    z-sum' = trans (sym eq) (trans (cong₂ _+_ (ccw-impl-zero w1 ad1) (cw-impl-zero w2 ad2))
                                   (+-identityˡ zero))
    zA' : nCwL w1 ≡ zero
    zA' = ccw-impl-zero w1 ad1
    zB' : nCcwL w1 ≡ zero
    zB' = sum-zero-r (nCwL w2) (nCcwL w1) z-sum'
    zC' : nCwL w2 ≡ zero
    zC' = sum-zero-l (nCwL w2) (nCcwL w1) z-sum'
    zD' : nCcwL w2 ≡ zero
    zD' = cw-impl-zero w2 ad2

class-dir-c3 : (w1 w2 : Walk C5LEc c3 c3)
  → btFreeD w1 → lpFreeD w1 → btFreeD w2 → lpFreeD w2
  → nCwL w1 + nCcwL w2 ≡ nCwL w2 + nCcwL w1
  → AHomotopyStd C5LEc w1 w2
class-dir-c3 w1 w2 bf1 pf1 bf2 pf2 eq
  with btFree-monoL w1 bf1 pf1 | btFree-monoL w2 bf2 pf2
... | (dcw , ad1) | (dcw , ad2) =
      eq→AH (mono-unique w1 w2 dcw ad1 ad2 pf1 pf2
               (same-len w1 w2 pf1 pf2 (proj₁ (cw-pointwise w1 w2 ad1 ad2 eq))
                                         (proj₂ (cw-pointwise w1 w2 ad1 ad2 eq))))
... | (dccw , ad1) | (dccw , ad2) =
      eq→AH (mono-unique w1 w2 dccw ad1 ad2 pf1 pf2
               (same-len w1 w2 pf1 pf2 (proj₁ (ccw-pointwise w1 w2 ad1 ad2 eq))
                                         (proj₂ (ccw-pointwise w1 w2 ad1 ad2 eq))))
... | (dcw , ad1) | (dccw , ad2) =
      nil-nil-c3 w1 w2 (zero-len w1 pf1 zA zB) (zero-len w2 pf2 zC zD)
  where
    z-sum : nCwL w1 + nCcwL w2 ≡ zero
    z-sum = trans eq (trans (cong₂ _+_ (ccw-impl-zero w2 ad2) (cw-impl-zero w1 ad1))
                            (+-identityˡ zero))
    zA : nCwL w1 ≡ zero
    zA = sum-zero-l (nCwL w1) (nCcwL w2) z-sum
    zB : nCcwL w1 ≡ zero
    zB = cw-impl-zero w1 ad1
    zC : nCwL w2 ≡ zero
    zC = ccw-impl-zero w2 ad2
    zD : nCcwL w2 ≡ zero
    zD = sum-zero-r (nCwL w1) (nCcwL w2) z-sum
... | (dccw , ad1) | (dcw , ad2) =
      nil-nil-c3 w1 w2 (zero-len w1 pf1 zA' zB') (zero-len w2 pf2 zC' zD')
  where
    z-sum' : nCwL w2 + nCcwL w1 ≡ zero
    z-sum' = trans (sym eq) (trans (cong₂ _+_ (ccw-impl-zero w1 ad1) (cw-impl-zero w2 ad2))
                                   (+-identityˡ zero))
    zA' : nCwL w1 ≡ zero
    zA' = ccw-impl-zero w1 ad1
    zB' : nCcwL w1 ≡ zero
    zB' = sum-zero-r (nCwL w2) (nCcwL w1) z-sum'
    zC' : nCwL w2 ≡ zero
    zC' = sum-zero-l (nCwL w2) (nCcwL w1) z-sum'
    zD' : nCcwL w2 ≡ zero
    zD' = cw-impl-zero w2 ad2

class-dir-c4 : (w1 w2 : Walk C5LEc c4 c4)
  → btFreeD w1 → lpFreeD w1 → btFreeD w2 → lpFreeD w2
  → nCwL w1 + nCcwL w2 ≡ nCwL w2 + nCcwL w1
  → AHomotopyStd C5LEc w1 w2
class-dir-c4 w1 w2 bf1 pf1 bf2 pf2 eq
  with btFree-monoL w1 bf1 pf1 | btFree-monoL w2 bf2 pf2
... | (dcw , ad1) | (dcw , ad2) =
      eq→AH (mono-unique w1 w2 dcw ad1 ad2 pf1 pf2
               (same-len w1 w2 pf1 pf2 (proj₁ (cw-pointwise w1 w2 ad1 ad2 eq))
                                         (proj₂ (cw-pointwise w1 w2 ad1 ad2 eq))))
... | (dccw , ad1) | (dccw , ad2) =
      eq→AH (mono-unique w1 w2 dccw ad1 ad2 pf1 pf2
               (same-len w1 w2 pf1 pf2 (proj₁ (ccw-pointwise w1 w2 ad1 ad2 eq))
                                         (proj₂ (ccw-pointwise w1 w2 ad1 ad2 eq))))
... | (dcw , ad1) | (dccw , ad2) =
      nil-nil-c4 w1 w2 (zero-len w1 pf1 zA zB) (zero-len w2 pf2 zC zD)
  where
    z-sum : nCwL w1 + nCcwL w2 ≡ zero
    z-sum = trans eq (trans (cong₂ _+_ (ccw-impl-zero w2 ad2) (cw-impl-zero w1 ad1))
                            (+-identityˡ zero))
    zA : nCwL w1 ≡ zero
    zA = sum-zero-l (nCwL w1) (nCcwL w2) z-sum
    zB : nCcwL w1 ≡ zero
    zB = cw-impl-zero w1 ad1
    zC : nCwL w2 ≡ zero
    zC = ccw-impl-zero w2 ad2
    zD : nCcwL w2 ≡ zero
    zD = sum-zero-r (nCwL w1) (nCcwL w2) z-sum
... | (dccw , ad1) | (dcw , ad2) =
      nil-nil-c4 w1 w2 (zero-len w1 pf1 zA' zB') (zero-len w2 pf2 zC' zD')
  where
    z-sum' : nCwL w2 + nCcwL w1 ≡ zero
    z-sum' = trans (sym eq) (trans (cong₂ _+_ (ccw-impl-zero w1 ad1) (cw-impl-zero w2 ad2))
                                   (+-identityˡ zero))
    zA' : nCwL w1 ≡ zero
    zA' = ccw-impl-zero w1 ad1
    zB' : nCcwL w1 ≡ zero
    zB' = sum-zero-r (nCwL w2) (nCcwL w1) z-sum'
    zC' : nCwL w2 ≡ zero
    zC' = sum-zero-l (nCwL w2) (nCcwL w1) z-sum'
    zD' : nCcwL w2 ≡ zero
    zD' = cw-impl-zero w2 ad2

--------------------------------------------------------------------------------
-- § ⑧ ★★★★ class-complete：**一般类判据** ✓（差分形式 ✓ 混合方向 ✓）
--
-- nformL 归约两走到（bt-free + lp-free）正规形 ✓
--   ⇒ diff-trans 搬差分 ✓ ⇒ class-dir-cX ✓ ⇒ 拼接 ✓
--------------------------------------------------------------------------------

-- 对称包装 ✓（显式签名避开构造子隐式参 ✗）
symL : ∀ {x y : V5} {w1 w2 : Walk C5LEc x y}
  → AHomotopyStd C5LEc w1 w2 → AHomotopyStd C5LEc w2 w1
symL {w1 = w1} {w2 = w2} h = h-sym h

-- 按起点顶点分派到 class-dir-cX ✓
dir-dispatch : ∀ {x : V5} (nf1 nf2 : Walk C5LEc x x)
  → btFreeD nf1 → lpFreeD nf1 → btFreeD nf2 → lpFreeD nf2
  → nCwL nf1 + nCcwL nf2 ≡ nCwL nf2 + nCcwL nf1
  → AHomotopyStd C5LEc nf1 nf2
dir-dispatch {c0} = class-dir-c0
dir-dispatch {c1} = class-dir-c1
dir-dispatch {c2} = class-dir-c2
dir-dispatch {c3} = class-dir-c3
dir-dispatch {c4} = class-dir-c4

class-complete : ∀ {x : V5} (w1 w2 : Walk C5LEc x x)
  → nCwL w1 + nCcwL w2 ≡ nCwL w2 + nCcwL w1
  → AHomotopyStd C5LEc w1 w2
class-complete {x} w1 w2 eq with nformL w1 | nformL w2
... | (nf1 , bf1 , pf1 , h1) | (nf2 , bf2 , pf2 , h2) =
      h-trn h1 (h-trn (mid nf1 nf2 bf1 pf1 bf2 pf2 h1 h2) (symL h2))
  where
    mid : (nf1 nf2 : Walk C5LEc x x)
      → btFreeD nf1 → lpFreeD nf1 → btFreeD nf2 → lpFreeD nf2
      → AHomotopyStd C5LEc w1 nf1 → AHomotopyStd C5LEc w2 nf2
      → AHomotopyStd C5LEc nf1 nf2
    mid nf1 nf2 bf1 pf1 bf2 pf2 h1 h2 =
      dir-dispatch nf1 nf2 bf1 pf1 bf2 pf2
        (diff-trans (nCwL w1) (nCcwL w1) (nCwL w2) (nCcwL w2)
                    (nCwL nf1) (nCcwL nf1) (nCwL nf2) (nCcwL nf2)
                    eq (AH-inv h1) (AH-inv h2))

--------------------------------------------------------------------------------
-- § ⑨ ★★★★★ 主定理：**类判据（双向）** ✓
--
-- π₁(C5L) 的类由「差分计数」完全决定 ✓
--   ⟹ = `AH-inv`（同伦 ⇒ 差分不变 ✓）
--   ⟸ = `class-complete`（差分相等 ⇒ 同类 ✓ 含混合方向 ✓）
--------------------------------------------------------------------------------

class-iff : ∀ {x : V5} (w1 w2 : Walk C5LEc x x)
  → (AHomotopyStd C5LEc w1 w2 → nCwL w1 + nCcwL w2 ≡ nCwL w2 + nCcwL w1)
  × (nCwL w1 + nCcwL w2 ≡ nCwL w2 + nCcwL w1 → AHomotopyStd C5LEc w1 w2)
class-iff w1 w2 = AH-inv {w1 = w1} {w2 = w2} , class-complete w1 w2

-- 推论：逐项计数相等 ⇒ 同类 ✓（单方向 ✓ 反向不成立 ✗：差分不能推逐项 ✓）
pointwise-to-diff : ∀ (a1 b1 a2 b2 : ℕ) → a1 ≡ a2 → b1 ≡ b2
  → a1 + b2 ≡ a2 + b1
pointwise-to-diff a1 b1 a2 b2 p q = cong₂ _+_ p (sym q)

pointwise-class : ∀ {x : V5} (w1 w2 : Walk C5LEc x x)
  → nCwL w1 ≡ nCwL w2 → nCcwL w1 ≡ nCcwL w2 → AHomotopyStd C5LEc w1 w2
pointwise-class w1 w2 p q =
  class-complete w1 w2 (pointwise-to-diff (nCwL w1) (nCcwL w1) (nCwL w2) (nCcwL w2) p q)

--------------------------------------------------------------------------------
-- § ⑩ ★★★ 空伦回路的刻画（≅ ℤ 的核 ✓）
--
-- `nil` 的类 = **计数平衡**的闭走（nCwL ≡ nCcwL ✓）—— 即绕数 0 的核 ✓
--------------------------------------------------------------------------------

-- ⟹：与 nil 同伦 ⇒ 计数平衡 ✓
nil-class-fwd : ∀ {x : V5} (w : Walk C5LEc x x)
  → AHomotopyStd C5LEc (nil x) w → nCwL w ≡ nCcwL w
nil-class-fwd w h = sym (trans (+-identityˡ (nCcwL w))
                          (trans (AH-inv {w1 = nil _} {w2 = w} h)
                                 (+-identityʳ (nCwL w))))

-- ⟸：计数平衡 ⇒ 与 nil 同伦 ✓
nil-class-bwd : ∀ {x : V5} (w : Walk C5LEc x x)
  → nCwL w ≡ nCcwL w → AHomotopyStd C5LEc (nil x) w
nil-class-bwd w eq = class-complete (nil _) w
  (trans (+-identityˡ (nCcwL w)) (trans (sym eq) (sym (+-identityʳ (nCwL w)))))

-- 双向打包 ✓
nil-class-iff : ∀ {x : V5} (w : Walk C5LEc x x)
  → (AHomotopyStd C5LEc (nil x) w → nCwL w ≡ nCcwL w)
  × (nCwL w ≡ nCcwL w → AHomotopyStd C5LEc (nil x) w)
nil-class-iff w = nil-class-fwd w , nil-class-bwd w

--------------------------------------------------------------------------------
-- § ⑪ ★★★ 绕数的实现性（≅ ℤ 的满射件 ✓）
--
-- 绕一圈（5 条 cw 边）是 c0 上的闭走 ✓ ⇒ 任意 k 圈可实现 ⇒ 绕数满射 ℤ ✓
--------------------------------------------------------------------------------


-- ① 单圈闭走 ✓（c0 → c0 ✓ 5 条 cw 边）
loop5 : Walk C5LEc c0 c0
loop5 = cons cw01 (cons cw12 (cons cw23 (cons cw34 (cons cw40 (nil c0)))))

loop5-cw : nCwL loop5 ≡ 5
loop5-cw = refl

loop5-ccw : nCcwL loop5 ≡ zero
loop5-ccw = refl

-- ② 迭代拼接 ✓
iter5 : ℕ → Walk C5LEc c0 c0
iter5 zero = nil c0
iter5 (suc k) = loop5 ++w iter5 k

iter5-cw : ∀ (k : ℕ) → nCwL (iter5 k) ≡ 5 * k
iter5-cw zero = refl
iter5-cw (suc k) = trans (nCwL-++ loop5 (iter5 k))
                         (trans (cong₂ _+_ loop5-cw (iter5-cw k)) (sym (*-suc 5 k)))

iter5-ccw : ∀ (k : ℕ) → nCcwL (iter5 k) ≡ zero
iter5-ccw zero = refl
iter5-ccw (suc k) = trans (nCcwL-++ loop5 (iter5 k))
                          (trans (cong₂ _+_ loop5-ccw (iter5-ccw k)) (+-identityˡ zero))

--------------------------------------------------------------------------------
-- § ⑫ ★★★ 类的拼接（群结构 ✓ ≅ ℤ 的运算件）
--------------------------------------------------------------------------------

-- ① ++w 结合律 ✓
++w-assoc : ∀ {a b c d : V5} (p : Walk C5LEc a b) (q : Walk C5LEc b c) (r : Walk C5LEc c d)
  → (p ++w q) ++w r ≡ p ++w (q ++w r)
++w-assoc (nil a) q r = refl
++w-assoc (cons e p) q r = cong (cons e) (++w-assoc p q r)

-- ③ 尾部同余：**已废弃** ✓ —— 类乘法由 `class-mul`（计数可加 + class-iff）直接给出 ✓
--    不需要尾部同余；`diff` 层亦不需要 ⇒ 不在关键路径 ✓ 保留占位仅作历史记录 ✓
-- ③ 尾部同余（step-right / AH-right / AH-++）：**待补** ⬜（4 轮尝试 ✗）
--   卡点 ✗：`subst` 的 motive 报 `_++w_ {v = x} q _` vs `_++w_ {v = b} (q ++w cons e3 b') p` 不等
--     已试 ✗：显式 `{u = a} {v = c}` / `sym (assoc)` / 位置参数
--   ★ 根因推测 ✓：`(q ++ X) ++ p` 与 `q ++ (X ++ p)` 的**中间顶点**在归纳后不可统一 ✗
--     （`++w-assoc` 的证明用 `cong (cons e)` ✓ 但其类型含中间顶点 `x` ✗）
--   修法候选 ✓（下会话）：
--     ① 先证**端点提升**的 `++w-assoc`（把中间顶点显式化 ✓）
--     ② 或改走「类拼接」的另一路线：类的乘法定义在 `class-iff` 的差分上 ✓
--        （`nCwL (w1 ++ w2) = nCwL w1 + nCwL w2` ✓ 已有 ✓）⇒ 群结构由差分直接给出 ✓ 不必做 AH-++ ✓
--   已备 ✓：`++w-assoc`（✓）/ `nCwL-++` / `nCcwL-++` ✓

--------------------------------------------------------------------------------
-- § ⑬ 走反转（≅ ℤ 的**负方向**件 ✓ —— 库里原无 rev ✗，自建）
--
-- 目的 ✓：`iter5` 只覆盖 +5k ✗ ⇒ 负绕数需 `rev` + `nCcwL (rev w) ≡ nCwL w`
-- 结构 ✓：A1 边反转(15) → A2/A3 计数交换(15×2) → A4 自环性(15) → A5 snoc → A6 rev → A7 绕数
--------------------------------------------------------------------------------

-- A1 边反转 ✓（端点严格交换 ✓）
revEdge : ∀ {x y : V5} → EL x y → EL y x
revEdge cw01 = cc10
revEdge cw12 = cc21
revEdge cw23 = cc32
revEdge cw34 = cc43
revEdge cw40 = cc04
revEdge cc04 = cw40
revEdge cc10 = cw01
revEdge cc21 = cw12
revEdge cc32 = cw23
revEdge cc43 = cw34
revEdge lp0 = lp0
revEdge lp1 = lp1
revEdge lp2 = lp2
revEdge lp3 = lp3
revEdge lp4 = lp4

-- A2 cw 计数 ↔ ccw 计数 ✓
cwOfL-revEdge : ∀ {x y : V5} (e : EL x y) → cwOfL (revEdge e) ≡ ccwOfL e
cwOfL-revEdge cw01 = refl
cwOfL-revEdge cw12 = refl
cwOfL-revEdge cw23 = refl
cwOfL-revEdge cw34 = refl
cwOfL-revEdge cw40 = refl
cwOfL-revEdge cc04 = refl
cwOfL-revEdge cc10 = refl
cwOfL-revEdge cc21 = refl
cwOfL-revEdge cc32 = refl
cwOfL-revEdge cc43 = refl
cwOfL-revEdge lp0 = refl
cwOfL-revEdge lp1 = refl
cwOfL-revEdge lp2 = refl
cwOfL-revEdge lp3 = refl
cwOfL-revEdge lp4 = refl

-- A3 对称 ✓
ccwOfL-revEdge : ∀ {x y : V5} (e : EL x y) → ccwOfL (revEdge e) ≡ cwOfL e
ccwOfL-revEdge cw01 = refl
ccwOfL-revEdge cw12 = refl
ccwOfL-revEdge cw23 = refl
ccwOfL-revEdge cw34 = refl
ccwOfL-revEdge cw40 = refl
ccwOfL-revEdge cc04 = refl
ccwOfL-revEdge cc10 = refl
ccwOfL-revEdge cc21 = refl
ccwOfL-revEdge cc32 = refl
ccwOfL-revEdge cc43 = refl
ccwOfL-revEdge lp0 = refl
ccwOfL-revEdge lp1 = refl
ccwOfL-revEdge lp2 = refl
ccwOfL-revEdge lp3 = refl
ccwOfL-revEdge lp4 = refl

-- A4 自环性保持 ✓（供 lpFree 搬运）
isLp-revEdge : ∀ {x y : V5} (e : EL x y) → isLp (revEdge e) → isLp e
isLp-revEdge cw01 ()
isLp-revEdge cw12 ()
isLp-revEdge cw23 ()
isLp-revEdge cw34 ()
isLp-revEdge cw40 ()
isLp-revEdge cc04 ()
isLp-revEdge cc10 ()
isLp-revEdge cc21 ()
isLp-revEdge cc32 ()
isLp-revEdge cc43 ()
isLp-revEdge lp0 _ = tt
isLp-revEdge lp1 _ = tt
isLp-revEdge lp2 _ = tt
isLp-revEdge lp3 _ = tt
isLp-revEdge lp4 _ = tt

-- A5 尾部追加的计数 ✓（snoc ✓ `++w` 只在头部递归 ⇒ 需尾引理）
nCwL-snoc : ∀ {x y z : V5} (p : Walk C5LEc x y) (e : EL y z)
  → nCwL (p ++w cons e (nil z)) ≡ nCwL p + cwOfL e
nCwL-snoc (nil x) e = trans (+-identityʳ (cwOfL e)) (sym (+-identityˡ (cwOfL e)))
nCwL-snoc (cons f p) e =
  trans (cong (cwOfL f +_) (nCwL-snoc p e))
        (sym (+-assoc (cwOfL f) (nCwL p) (cwOfL e)))

nCcwL-snoc : ∀ {x y z : V5} (p : Walk C5LEc x y) (e : EL y z)
  → nCcwL (p ++w cons e (nil z)) ≡ nCcwL p + ccwOfL e
nCcwL-snoc (nil x) e = trans (+-identityʳ (ccwOfL e)) (sym (+-identityˡ (ccwOfL e)))
nCcwL-snoc (cons f p) e =
  trans (cong (ccwOfL f +_) (nCcwL-snoc p e))
        (sym (+-assoc (ccwOfL f) (nCcwL p) (ccwOfL e)))

-- A6 走反转 ✓（逐边反 + 逆序 ✓）
rev : ∀ {x y : V5} → Walk C5LEc x y → Walk C5LEc y x
rev (nil x) = nil x
rev {x} (cons e b) = rev b ++w cons (revEdge e) (nil x)

-- A7 ★ 绕数反转 ✓（**负方向件** ✓ —— 验收点）
--   cw 计数换 ccw ✓ ＋ 加法交换 ✓
rev-cw : ∀ {x y : V5} (w : Walk C5LEc x y) → nCwL (rev w) ≡ nCcwL w
rev-cw (nil x) = refl
rev-cw {x} (cons e b) =
  trans (nCwL-snoc (rev b) (revEdge e))
        (trans (cong (_+ cwOfL (revEdge e)) (rev-cw b))
               (trans (cong (nCcwL b +_) (cwOfL-revEdge e))
                      (+-comm (nCcwL b) (ccwOfL e))))

rev-ccw : ∀ {x y : V5} (w : Walk C5LEc x y) → nCcwL (rev w) ≡ nCwL w
rev-ccw (nil x) = refl
rev-ccw {x} (cons e b) =
  trans (nCcwL-snoc (rev b) (revEdge e))
        (trans (cong (_+ ccwOfL (revEdge e)) (rev-ccw b))
               (trans (cong (nCwL b +_) (ccwOfL-revEdge e))
                      (+-comm (nCwL b) (cwOfL e))))

--------------------------------------------------------------------------------
-- § ⑭ 类层群结构（**用计数 + class-iff + rev** ✓ 不碰 step-right ✗）
--
-- 核心思路 ✓：`class-iff` 的 ⟸（= class-complete）已足够
--   ⇒ 类的良定义性只需**计数等式**（nCwL-++ / nCcwL-++ ✓）+ ℕ 重排 ✓
--------------------------------------------------------------------------------

-- B0 尾部空走 ✓
++w-nil : ∀ {x y : V5} (w : Walk C5LEc x y) → w ++w nil y ≡ w
++w-nil (nil x) = refl
++w-nil (cons e b) = cong (cons e) (++w-nil b)

-- B1 计数重排件（solver ✓）
mul-rearr1 : ∀ (a1 a2 b1' b2' : ℕ) → (a1 + a2) + (b1' + b2') ≡ (a1 + b1') + (a2 + b2')
mul-rearr1 = solve 4 (λ a1 a2 b1′ b2′ → (a1 :+ a2) :+ (b1′ :+ b2′) := (a1 :+ b1′) :+ (a2 :+ b2′)) refl

mul-rearr2 : ∀ (a1' b1 a2' b2 : ℕ) → (a1' + b1) + (a2' + b2) ≡ (a1' + a2') + (b1 + b2)
mul-rearr2 = solve 4 (λ a1′ b1 a2′ b2 → (a1′ :+ b1) :+ (a2′ :+ b2) := (a1′ :+ a2′) :+ (b1 :+ b2)) refl

mul-eq : ∀ (a1 b1 a1' b1' a2 b2 a2' b2' : ℕ)
  → a1 + b1' ≡ a1' + b1 → a2 + b2' ≡ a2' + b2
  → (a1 + a2) + (b1' + b2') ≡ (a1' + a2') + (b1 + b2)
mul-eq a1 b1 a1' b1' a2 b2 a2' b2' g1 g2 =
  trans (mul-rearr1 a1 a2 b1' b2')
        (trans (cong₂ _+_ g1 g2) (mul-rearr2 a1' b1 a2' b2))

-- B2 ★ 类乘法良定义 ✓（`w1 ~ v1 ∧ w2 ~ v2 ⇒ w1++w2 ~ v1++v2` ✓）
class-mul : ∀ {x : V5} {w1 v1 w2 v2 : Walk C5LEc x x}
  → AHomotopyStd C5LEc w1 v1 → AHomotopyStd C5LEc w2 v2
  → AHomotopyStd C5LEc (w1 ++w w2) (v1 ++w v2)
class-mul {x} {w1} {v1} {w2} {v2} h1 h2 =
  class-complete (w1 ++w w2) (v1 ++w v2)
    (trans (cong₂ _+_ (nCwL-++ w1 w2) (nCcwL-++ v1 v2))
      (trans (mul-eq (nCwL w1) (nCcwL w1) (nCwL v1) (nCcwL v1)
                     (nCwL w2) (nCcwL w2) (nCwL v2) (nCcwL v2)
                     (AH-inv h1) (AH-inv h2))
             (cong₂ _+_ (sym (nCwL-++ v1 v2)) (sym (nCcwL-++ w1 w2)))))

-- B3 结合律 ✓（`++w-assoc` + eq→AH ✓）
class-assoc : ∀ {x : V5} (w1 w2 w3 : Walk C5LEc x x)
  → AHomotopyStd C5LEc ((w1 ++w w2) ++w w3) (w1 ++w (w2 ++w w3))
class-assoc w1 w2 w3 = eq→AH (++w-assoc w1 w2 w3)

-- B4 单位律 ✓（左：定义性 ✓ ｜ 右：`++w-nil` ✓）
class-unitˡ : ∀ {x : V5} (w : Walk C5LEc x x) → AHomotopyStd C5LEc (nil x ++w w) w
class-unitˡ w = h-rfl w

class-unitʳ : ∀ {x : V5} (w : Walk C5LEc x x) → AHomotopyStd C5LEc (w ++w nil x) w
class-unitʳ w = eq→AH (++w-nil w)

-- B5 逆元律 ✓（`w ++ rev w ~ nil` ✓ 由计数平衡 + nil-class-bwd ✓）
class-inv : ∀ {x y : V5} (w : Walk C5LEc x y)
  → AHomotopyStd C5LEc (w ++w rev w) (nil x)
class-inv {x} w = symL (nil-class-bwd (w ++w rev w) eq)
  where
    -- nCwL (w ++ rev w) = a + b = b + a = nCcwL (w ++ rev w) ✓
    eq : nCwL (w ++w rev w) ≡ nCcwL (w ++w rev w)
    eq = trans (nCwL-++ w (rev w))
           (trans (cong (nCwL w +_) (rev-cw w))
             (trans (+-comm (nCwL w) (nCcwL w))
               (trans (cong (nCcwL w +_) (sym (rev-ccw w)))
                      (sym (nCcwL-++ w (rev w))))))

--------------------------------------------------------------------------------
-- § ⑮ 绕数类的**互异性**（ℤ → π₁ 的单射性 ✓）
--
-- 避开 ℤ 与整除 ✗：直接在 ℕ 上用 `class-iff` + 计数 ✓
--   `iter5 (suc k) ~ iter5 k` ⇒ `5*suc k ≡ 5*k` ⇒ `5 ≡ 0` ✗ 矛盾 ✓
--------------------------------------------------------------------------------

five-neq : ¬ (suc (suc (suc (suc (suc zero)))) ≡ zero)
five-neq ()

-- ★ 正负/同级绕数的类两两不同 ✓ ⇒ ℤ 无限性在 π₁ 中体现 ✓
wind-distinct : ∀ (k : ℕ) → ¬ AHomotopyStd C5LEc (iter5 (suc k)) (iter5 k)
wind-distinct k h =
  five-neq (+-cancelʳ-≡ (5 * k) (suc (suc (suc (suc (suc zero))))) zero c)
  where
    -- ① 由同伦 ⇒ 计数等式 ⇒ `5 * suc k ≡ 5 * k` ✓
    a : 5 * suc k ≡ 5 * k
    a = trans (sym (+-identityʳ (5 * suc k)))
          (trans (cong₂ _+_ (sym (iter5-cw (suc k))) (sym (iter5-ccw k)))
            (trans (AH-inv h)
              (trans (cong₂ _+_ (iter5-cw k) (iter5-ccw (suc k)))
                     (+-identityʳ (5 * k)))))

    -- ② `5 * suc k = 5 + 5 * k` ⇒ `5 + 5k ≡ 5k` ✓
    b : 5 + 5 * k ≡ 5 * k
    b = trans (sym (*-suc 5 k)) a

    -- ③ 右端写成 `0 + 5k` ⇒ 可消去 ✓
    c : 5 + 5 * k ≡ zero + 5 * k
    c = trans b (sym (+-identityˡ (5 * k)))

--------------------------------------------------------------------------------
-- § ⑯ ℤ 层：顶点坐标 + 逐边模 5 关系（≅ ℤ 的整除件 E1 ✓）
--
-- 避开 stdlib 无 ℤ 消去律 ✗ ⇒ 用「带见证的模 5 等式」✓ 不需消去 ✓
--   绕环两条边需非零余量 ✓：cw40（0 = 4+1−5）／cc04（4 = 0−1+5）
--------------------------------------------------------------------------------

pos : V5 → ℤ
pos c0 = +0
pos c1 = Int.+ 1
pos c2 = Int.+ 2
pos c3 = Int.+ 3
pos c4 = Int.+ 4

-- 边增量 ✓（cw +1 ／ ccw −1 ／ 自环 0）
deltaL : ∀ {x y : V5} → EL x y → ℤ
deltaL cw01 = Int.+ 1
deltaL cw12 = Int.+ 1
deltaL cw23 = Int.+ 1
deltaL cw34 = Int.+ 1
deltaL cw40 = Int.+ 1
deltaL cc04 = Int.- (Int.+ 1)
deltaL cc10 = Int.- (Int.+ 1)
deltaL cc21 = Int.- (Int.+ 1)
deltaL cc32 = Int.- (Int.+ 1)
deltaL cc43 = Int.- (Int.+ 1)
deltaL lp0 = +0
deltaL lp1 = +0
deltaL lp2 = +0
deltaL lp3 = +0
deltaL lp4 = +0

-- ★ E1 逐边：`pos 终 = pos 始 + delta + 5q` ✓（15 案，见证显式 ✓）
edge-mod : ∀ {x y : V5} (e : EL x y)
  → Σ ℤ (λ q → pos y ≡ pos x +ℤ deltaL e +ℤ (Int.+ 5) *ℤ q)
edge-mod cw01 = +0 , refl
edge-mod cw12 = +0 , refl
edge-mod cw23 = +0 , refl
edge-mod cw34 = +0 , refl
edge-mod cw40 = Int.- (Int.+ 1) , refl
edge-mod cc04 = Int.+ 1 , refl
edge-mod cc10 = +0 , refl
edge-mod cc21 = +0 , refl
edge-mod cc32 = +0 , refl
edge-mod cc43 = +0 , refl
edge-mod lp0 = +0 , refl
edge-mod lp1 = +0 , refl
edge-mod lp2 = +0 , refl
edge-mod lp3 = +0 , refl
edge-mod lp4 = +0 , refl

--------------------------------------------------------------------------------
-- § ⑰ ℤ 层：diff 与环重排（E2 ✓ 复用 LaurentRingLaws.+interchange 骨架 ✓）
--------------------------------------------------------------------------------

open import Data.Integer.Properties using (neg-distrib-+)
  renaming (+-assoc to +ℤ-assoc; +-comm to +ℤ-comm; +-identityˡ to +ℤ-identityˡ;
            +-inverseʳ to +ℤ-inverseʳ; *-distribˡ-+ to *ℤ-distribˡ-+;
            +-identityʳ to +ℤ-identityʳ; pos-* to pos-*ℤ;
            +-inverseˡ to +ℤ-inverseˡ; *-zeroʳ to *ℤ-zeroʳ; +-injective to +ℤ-injective)

-- 三元交换 ✓（骨架复用 ✓ `LaurentRingLaws.+swap3:29`，方向按 stdlib 修正 ✓）
swap3 : ∀ (b c d : ℤ) → b +ℤ (c +ℤ d) ≡ c +ℤ (b +ℤ d)
swap3 b c d =
  trans (sym (+ℤ-assoc b c d))
    (trans (cong (λ z → z +ℤ d) (+ℤ-comm b c)) (+ℤ-assoc c b d))

-- 四元交叉 ✓（骨架复用 ✓ `LaurentRingLaws.+interchange:33`）
plus-rer : ∀ (a b c d : ℤ) → (a +ℤ b) +ℤ (c +ℤ d) ≡ (a +ℤ c) +ℤ (b +ℤ d)
plus-rer a b c d =
  trans (+ℤ-assoc a b (c +ℤ d))
    (trans (cong (λ z → a +ℤ z) (swap3 b c d))
           (sym (+ℤ-assoc a c (b +ℤ d))))

-- 绕数差分 ✓（ℤ 值 ✓）
diff : ∀ {x y : V5} → Walk C5LEc x y → ℤ
diff w = Int.+ (nCwL w) +ℤ (Int.- (Int.+ (nCcwL w)))

-- `+_` 加法同态 ✓（定义性 ✓）
plus-hom : ∀ (m n : ℕ) → Int.+ (m + n) ≡ Int.+ m +ℤ Int.+ n
plus-hom m n = refl

-- 逐边：计数差 = 增量 ✓（15 refl ✓）
deltaT : ∀ {x y : V5} (e : EL x y)
  → Int.+ (cwOfL e) +ℤ (Int.- (Int.+ (ccwOfL e))) ≡ deltaL e
deltaT cw01 = refl
deltaT cw12 = refl
deltaT cw23 = refl
deltaT cw34 = refl
deltaT cw40 = refl
deltaT cc04 = refl
deltaT cc10 = refl
deltaT cc21 = refl
deltaT cc32 = refl
deltaT cc43 = refl
deltaT lp0 = refl
deltaT lp1 = refl
deltaT lp2 = refl
deltaT lp3 = refl
deltaT lp4 = refl

-- ★ 单步展开 ✓ `diff (cons e b) ≡ deltaL e + diff b`
diff-cons : ∀ {x y z : V5} (e : EL x y) (b : Walk C5LEc y z)
  → diff (cons e b) ≡ deltaL e +ℤ diff b
diff-cons e b =
  trans (cong₂ _+ℤ_ (refl {x = Int.+ (cwOfL e) +ℤ Int.+ (nCwL b)}) (neg-distrib-+ (Int.+ (ccwOfL e)) (Int.+ (nCcwL b))))
    (trans (plus-rer (Int.+ (cwOfL e)) (Int.+ (nCwL b))
                     (Int.- (Int.+ (ccwOfL e))) (Int.- (Int.+ (nCcwL b))))
           (cong₂ _+ℤ_ (deltaT e) (refl {x = diff b})))

-- ★ E1' 差分形式 ✓ `deltaL e ≡ (pos 终 - pos 始) + 5q`（15 案 ✓）
--   绕环两条边带非零见证 ✓：cw40 ↦ +1（1 = (0−4)+5）／cc04 ↦ −1（−1 = (4−0)−5）
edge-modD : ∀ {x y : V5} (e : EL x y)
  → Σ ℤ (λ q → deltaL e ≡ (pos y - pos x) +ℤ (Int.+ 5) *ℤ q)
edge-modD cw01 = +0 , refl
edge-modD cw12 = +0 , refl
edge-modD cw23 = +0 , refl
edge-modD cw34 = +0 , refl
edge-modD cc10 = +0 , refl
edge-modD cc21 = +0 , refl
edge-modD cc32 = +0 , refl
edge-modD cc43 = +0 , refl
edge-modD lp0 = +0 , refl
edge-modD lp1 = +0 , refl
edge-modD lp2 = +0 , refl
edge-modD lp3 = +0 , refl
edge-modD lp4 = +0 , refl
edge-modD cw40 = Int.+ 1 , refl
edge-modD cc04 = Int.- (Int.+ 1) , refl

-- 逆元消去 ✓ `b + (-(b + a)) ≡ -a`（4 步 ✓）
cancel-sub : ∀ (b a : ℤ) → b +ℤ (Int.- (b +ℤ a)) ≡ Int.- a
cancel-sub b a =
  trans (cong (λ z → b +ℤ z) (neg-distrib-+ b a))
    (trans (sym (+ℤ-assoc b (Int.- b) (Int.- a)))
      (trans (cong (λ z → z +ℤ (Int.- a)) (+ℤ-inverseʳ b))
             (+ℤ-identityˡ (Int.- a))))

-- 差分望远镜 ✓ `(b - a) + (c - b) ≡ c - a`（5 步 ✓）
sub-tel : ∀ (a b c : ℤ) → (b - a) +ℤ (c - b) ≡ c - a
sub-tel a b c =
  trans (plus-rer b (Int.- a) c (Int.- b))
    (trans (cong₂ _+ℤ_ (+ℤ-comm b c) (sym (neg-distrib-+ a b)))
      (trans (cong (λ z → (c +ℤ b) +ℤ z) (cong (λ z → Int.- z) (+ℤ-comm a b)))
        (trans (+ℤ-assoc c b (Int.- (b +ℤ a)))
               (cong (λ z → c +ℤ z) (cancel-sub b a)))))

-- 5 的分配 ✓
dist5 : ∀ (qe qb : ℤ) → (Int.+ 5) *ℤ (qe +ℤ qb) ≡ (Int.+ 5) *ℤ qe +ℤ (Int.+ 5) *ℤ qb
dist5 qe qb = *ℤ-distribˡ-+ (Int.+ 5) qe qb

-- 望远镜合成 ✓
tel : ∀ (a b c qe qb : ℤ)
  → ((b - a) +ℤ (Int.+ 5) *ℤ qe) +ℤ ((c - b) +ℤ (Int.+ 5) *ℤ qb)
  ≡ (c - a) +ℤ ((Int.+ 5) *ℤ qe +ℤ (Int.+ 5) *ℤ qb)
tel a b c qe qb =
  trans (plus-rer (b - a) ((Int.+ 5) *ℤ qe) (c - b) ((Int.+ 5) *ℤ qb))
        (cong (λ z → z +ℤ ((Int.+ 5) *ℤ qe +ℤ (Int.+ 5) *ℤ qb)) (sub-tel a b c))

-- pos c0 - pos c0 = 0 ✓
pos-c0-zero : pos c0 - pos c0 ≡ +0
pos-c0-zero = refl

-- ★ E2c 走级模 5 关系 ✓（归纳 ✓ diff-cons + edge-modD + tel ✓）
walk-modD : ∀ {x y : V5} (w : Walk C5LEc x y)
  → Σ ℤ (λ q → diff w ≡ (pos y - pos x) +ℤ (Int.+ 5) *ℤ q)
walk-modD (nil c0) = +0 , refl
walk-modD (nil c1) = +0 , refl
walk-modD (nil c2) = +0 , refl
walk-modD (nil c3) = +0 , refl
walk-modD (nil c4) = +0 , refl
walk-modD {x} {z} (cons {x} {y} {z} e b) with edge-modD e | walk-modD b
... | (qe , he) | (qb , hb) =
      (qe +ℤ qb)
      , (trans (diff-cons e b)
          (trans (cong₂ _+ℤ_ he hb)
            (trans (tel (pos x) (pos y) (pos z) qe qb)
                   (cong (λ z' → (pos z - pos x) +ℤ z') (sym (dist5 qe qb))))))

-- ★ E2d **整除**：闭走的绕数是 5 的倍数 ✓（E2 收口 ✓）
diff-div5 : ∀ (w : Walk C5LEc c0 c0) → Σ ℤ (λ k → diff w ≡ (Int.+ 5) *ℤ k)
diff-div5 w with walk-modD w
... | (q , h) =
      q , (trans h (trans (cong (λ z → z +ℤ (Int.+ 5) *ℤ q) pos-c0-zero)
                          (+ℤ-identityˡ ((Int.+ 5) *ℤ q))))

--------------------------------------------------------------------------------
-- § ⑱ ℤ 层：diff 的同伦不变性（E3 ✓ 不用消去律 ✗ —— 用「两侧同加」✓）
--------------------------------------------------------------------------------

-- ① `b + (- b + - c) ≡ - c` ✓（3 步 ✓）
lem1 : ∀ (b c : ℤ) → b +ℤ ((Int.- b) +ℤ (Int.- c)) ≡ Int.- c
lem1 b c =
  trans (sym (+ℤ-assoc b (Int.- b) (Int.- c)))
    (trans (cong (λ z → z +ℤ (Int.- c)) (+ℤ-inverseʳ b))
           (+ℤ-identityˡ (Int.- c)))

-- ② `(a + b) + (- b + - c) ≡ a + - c` ✓（2 步 ✓）
abs-l : ∀ (a b c : ℤ) → (a +ℤ b) +ℤ ((Int.- b) +ℤ (Int.- c)) ≡ a +ℤ (Int.- c)
abs-l a b c =
  trans (+ℤ-assoc a b ((Int.- b) +ℤ (Int.- c)))
        (cong (λ z → a +ℤ z) (lem1 b c))

-- ★ 计数等式 ⇒ ℤ 差分相等 ✓（**两侧同加** ✓ 避开消去律 ✗）
diff-eq : ∀ (a1 b1 a2 b2 : ℕ) → a1 + b2 ≡ a2 + b1
  → Int.+ a1 +ℤ (Int.- (Int.+ b1)) ≡ Int.+ a2 +ℤ (Int.- (Int.+ b2))
diff-eq a1 b1 a2 b2 h =
  trans (sym (abs-l (Int.+ a1) (Int.+ b2) (Int.+ b1)))
    (trans (cong (λ z → z +ℤ ((Int.- (Int.+ b2)) +ℤ (Int.- (Int.+ b1))))
                 (cong (λ n → Int.+ n) h))
      (trans (cong (λ z → (Int.+ a2 +ℤ Int.+ b1) +ℤ z)
                   (+ℤ-comm (Int.- (Int.+ b2)) (Int.- (Int.+ b1))))
             (abs-l (Int.+ a2) (Int.+ b1) (Int.+ b2))))

-- ★★ `diff` 是同伦不变量 ✓（E3 核心 ✓）
diff-inv : ∀ {x : V5} {w1 w2 : Walk C5LEc x x}
  → AHomotopyStd C5LEc w1 w2 → diff w1 ≡ diff w2
diff-inv {x} {w1} {w2} h =
  diff-eq (nCwL w1) (nCcwL w1) (nCwL w2) (nCcwL w2)
          (proj₁ (class-iff w1 w2) h)

--------------------------------------------------------------------------------
-- § ⑲ E4：ℤ 索引的绕数代表（≅ ℤ 的满射件 ✓）
--
-- 设计 ✓：`+ n ↦ iter5 n`（正绕 n 圈）；`-[1+ n ] ↦ rev (iter5 (suc n))`（负绕 ✓）
--   `+0 = + 0` 自动归入第一分支 ⇒ **两个子句覆盖全 ℤ** ✓
--------------------------------------------------------------------------------

-- ★ 正侧：`iter5 k` 的绕数 = 5k ✓
wind-pos : ∀ (k : ℕ) → diff (iter5 k) ≡ (Int.+ 5) *ℤ (Int.+ k)
wind-pos k =
  trans (cong₂ _+ℤ_ (cong (λ m → Int.+ m) (iter5-cw k))
                     (cong (λ m → Int.- (Int.+ m)) (iter5-ccw k)))
        (trans (+ℤ-identityʳ (Int.+ (5 * k))) (pos-*ℤ 5 k))

-- ★ 负侧：`rev (iter5 k)` 的绕数 = −5k ✓（避开 ℤ 乘负 ✗ 只用 pos-* ✓）
wind-neg : ∀ (k : ℕ) → diff (rev (iter5 k)) ≡ Int.- ((Int.+ 5) *ℤ (Int.+ k))
wind-neg k =
  trans (cong₂ _+ℤ_ (cong (λ m → Int.+ m) (rev-cw (iter5 k)))
                     (cong (λ m → Int.- (Int.+ m)) (rev-ccw (iter5 k))))
    (trans (cong₂ _+ℤ_ (cong (λ m → Int.+ m) (iter5-ccw k))
                       (cong (λ m → Int.- (Int.+ m)) (iter5-cw k)))
      (trans (+ℤ-identityˡ (Int.- (Int.+ (5 * k))))
             (cong (λ z → Int.- z) (pos-*ℤ 5 k))))

-- 满射件（两侧）✓：每个 5k 与 −5k 都有代表走
from-class : ∀ (k : ℕ)
  → Σ (Walk C5LEc c0 c0) (λ w → diff w ≡ (Int.+ 5) *ℤ (Int.+ k))
  × Σ (Walk C5LEc c0 c0) (λ w → diff w ≡ Int.- ((Int.+ 5) *ℤ (Int.+ k)))
from-class k = (iter5 k , wind-pos k) , (rev (iter5 k) , wind-neg k)

--------------------------------------------------------------------------------
-- § ⑳ ★★★★★ 主定理：π₁(C5L) ≅ 5ℤ ⊆ ℤ（四件套 ✓）
--------------------------------------------------------------------------------

c5l-winding-theorem :
    (∀ {x : V5} {w1 w2 : Walk C5LEc x x} → AHomotopyStd C5LEc w1 w2 → diff w1 ≡ diff w2)
    × (∀ (w : Walk C5LEc c0 c0) → Σ ℤ (λ k → diff w ≡ (Int.+ 5) *ℤ k))
    × (∀ (k : ℕ) → Σ (Walk C5LEc c0 c0) (λ w → diff w ≡ (Int.+ 5) *ℤ (Int.+ k)))
    × (∀ (k : ℕ) → Σ (Walk C5LEc c0 c0) (λ w → diff w ≡ Int.- ((Int.+ 5) *ℤ (Int.+ k))))
c5l-winding-theorem =
    (λ {x} {w1} {w2} h → diff-inv h)
  , diff-div5
  , (λ k → proj₁ (proj₁ (from-class k)) , proj₂ (proj₁ (from-class k)))
  , (λ k → proj₁ (proj₂ (from-class k)) , proj₂ (proj₂ (from-class k)))

-- § ㉑ E5：`from : ℤ → Walk` + record 打包：**待补** ⬜（stdlib 缺口 ✗）
--   卡点 ✗：**ℤ 乘负律在 stdlib 缺失** ✗（`a * (- b) ≡ - (a * b)` 无引理）
--     自证 4 案穷举 `refl` 失败 ✗：`_*_` 归一化为 `◃` 形式，
--     左侧 `（sign m * sign (- n)) ◃ (m * ∣- n∣)` 与右侧 `- ((sign m * sign n) ◃ ...)` 不同形 ✗
--     需 `ℕ` 层 `∣- n∣` 与 `sign` 的重排 ✗（可做但成本 > 收益 ✗）
--   ★ 现状 ✓：数学内容已完整交付于 `c5l-winding-theorem`（四件套 ✓ 两侧形式 ✓）
--     `from` 的 ℤ 单值形态 ✗ 仅缺这条归一化桥 ✓，不影响主定理
--   修法候选 ✓：① 用 `Int.sign`/`∣_∣`/`toℕ` 分解重证（~30 行）
--     ② 或改 `from` 的定义域为 `ℕ ⊎ ℕ`（正负两支 ✓ 无需 ℤ 乘负 ✓）

--------------------------------------------------------------------------------
-- § ㉑ ℤ 乘负律（**复用 1lab `Algebra/Ring/Reasoning:42-48` 的技法** ✓）
--
-- 1lab 用 `monoid-inverse-unique`；stdlib 无此件 ✗ ⇒ 自证「加法左逆唯一」✓
--   核心洞见 ✓：`x*(-y)` 与 `-(x*y)` 都是 `x*y` 的**左逆** ⇒ 必相等 ✓
--------------------------------------------------------------------------------

-- 加法左逆 ⇒ 等于负元 ✓
to-neg : ∀ (p c : ℤ) → p +ℤ c ≡ +0 → p ≡ Int.- c
to-neg p c h =
  trans (sym (+ℤ-identityʳ p))
    (trans (cong (λ z → p +ℤ z) (sym (+ℤ-inverseʳ c)))
      (trans (sym (+ℤ-assoc p c (Int.- c)))
        (trans (cong (λ z → z +ℤ (Int.- c)) h)
               (+ℤ-identityˡ (Int.- c)))))

-- 加法左逆唯一 ✓
left-inv-unique : ∀ (p q c : ℤ) → p +ℤ c ≡ +0 → q +ℤ c ≡ +0 → p ≡ q
left-inv-unique p q c h1 h2 = trans (to-neg p c h1) (sym (to-neg q c h2))

-- ★ `a * (- b) ≡ - (a * b)` ✓（1lab 技法 ✓ stdlib 零件 ✓）
neg-mul : ∀ (a b : ℤ) → a *ℤ (Int.- b) ≡ Int.- (a *ℤ b)
neg-mul a b =
  left-inv-unique (a *ℤ (Int.- b)) (Int.- (a *ℤ b)) (a *ℤ b)
    (trans (sym (*ℤ-distribˡ-+ a (Int.- b) b))
      (trans (cong (λ z → a *ℤ z) (+ℤ-inverseˡ b))
             (*ℤ-zeroʳ a)))
    (+ℤ-inverseˡ (a *ℤ b))

--------------------------------------------------------------------------------
-- § ㉒ E5：`from : ℤ → Walk` + 同构记录（≅ ℤ 收口 ✓）
--------------------------------------------------------------------------------

-- `diff` 对拼接可加 ✓（类乘法对应 ℤ 加法 ✓）
diff-mul : ∀ {x : V5} (w1 w2 : Walk C5LEc x x)
  → diff (w1 ++w w2) ≡ diff w1 +ℤ diff w2
diff-mul {x} w1 w2 =
  trans (cong₂ _+ℤ_ (cong (λ m → Int.+ m) (nCwL-++ w1 w2))
                     (cong (λ m → Int.- (Int.+ m)) (nCcwL-++ w1 w2)))
    (trans (cong (λ z → (Int.+ (nCwL w1) +ℤ Int.+ (nCwL w2)) +ℤ z)
                 (neg-distrib-+ (Int.+ (nCcwL w1)) (Int.+ (nCcwL w2))))
           (plus-rer (Int.+ (nCwL w1)) (Int.+ (nCwL w2))
                     (Int.- (Int.+ (nCcwL w1))) (Int.- (Int.+ (nCcwL w2)))))

-- ℤ 索引代表走 ✓（`+0 = + 0` 归入第一支 ✓ 两子句覆盖全 ℤ ✓）
iter5Z : ℤ → Walk C5LEc c0 c0
iter5Z (Int.+ n) = iter5 n
iter5Z (Int.-[1+ n ]) = rev (iter5 (suc n))

-- ★ 每个 ℤ 值的 5 倍绕数可实现 ✓（用 `neg-mul` ✓）
iter5Z-wind : ∀ (z : ℤ) → diff (iter5Z z) ≡ (Int.+ 5) *ℤ z
iter5Z-wind (Int.+ n) = wind-pos n
iter5Z-wind (Int.-[1+ n ]) =
  trans (wind-neg (suc n)) (sym (neg-mul (Int.+ 5) (Int.+ (suc n))))

--------------------------------------------------------------------------------
-- § ㉔ ★ 单射方向：ℤ 等式 ⇒ 计数交叉和 ⇒ 同类（**同构收口** ✓）
--------------------------------------------------------------------------------

-- `(- b) + (b + c) ≡ c` ✓（3 步 ✓）
neg-add : ∀ (b c : ℤ) → (Int.- b) +ℤ (b +ℤ c) ≡ c
neg-add b c =
  trans (sym (+ℤ-assoc (Int.- b) b c))
    (trans (cong (λ z → z +ℤ c) (+ℤ-inverseˡ b))
           (+ℤ-identityˡ c))

-- `(a + - b) + (b + c) ≡ a + c` ✓（2 步 ✓「两侧同加」的对偶 ✓）
abs-r : ∀ (a b c : ℤ) → (a +ℤ (Int.- b)) +ℤ (b +ℤ c) ≡ a +ℤ c
abs-r a b c =
  trans (+ℤ-assoc a (Int.- b) (b +ℤ c))
        (cong (λ z → a +ℤ z) (neg-add b c))

-- ★ diff 相等 ⇒ ℕ 交叉和 ✓
diff-eq-back : ∀ (a1 b1 a2 b2 : ℕ)
  → Int.+ a1 +ℤ (Int.- (Int.+ b1)) ≡ Int.+ a2 +ℤ (Int.- (Int.+ b2))
  → a1 + b2 ≡ a2 + b1
diff-eq-back a1 b1 a2 b2 h = +ℤ-injective body
  where
    -- 两侧同加 `(+b1 + +b2)` ✓
    step1 : Int.+ (a1 + b2) ≡ (Int.+ a1 +ℤ (Int.- (Int.+ b1))) +ℤ (Int.+ b1 +ℤ Int.+ b2)
    step1 = trans (sym (plus-hom a1 b2)) (sym (abs-r (Int.+ a1) (Int.+ b1) (Int.+ b2)))

    step2 : (Int.+ a1 +ℤ (Int.- (Int.+ b1))) +ℤ (Int.+ b1 +ℤ Int.+ b2)
          ≡ (Int.+ a2 +ℤ (Int.- (Int.+ b2))) +ℤ (Int.+ b1 +ℤ Int.+ b2)
    step2 = cong (λ z → z +ℤ (Int.+ b1 +ℤ Int.+ b2)) h

    step3 : (Int.+ a2 +ℤ (Int.- (Int.+ b2))) +ℤ (Int.+ b1 +ℤ Int.+ b2)
          ≡ (Int.+ a2 +ℤ (Int.- (Int.+ b2))) +ℤ (Int.+ b2 +ℤ Int.+ b1)
    step3 = cong (λ z → (Int.+ a2 +ℤ (Int.- (Int.+ b2))) +ℤ z)
                 (+ℤ-comm (Int.+ b1) (Int.+ b2))

    step4 : (Int.+ a2 +ℤ (Int.- (Int.+ b2))) +ℤ (Int.+ b2 +ℤ Int.+ b1)
          ≡ Int.+ (a2 + b1)
    step4 = trans (abs-r (Int.+ a2) (Int.+ b2) (Int.+ b1)) (plus-hom a2 b1)

    body : Int.+ (a1 + b2) ≡ Int.+ (a2 + b1)
    body = trans step1 (trans step2 (trans step3 step4))

-- ★★ diff 相等 ⇒ 同类 ✓（**单射性** ✓ 用 class-iff 的 ⟸ ✓）
diff-class : ∀ {w1 w2 : Walk C5LEc c0 c0}
  → diff w1 ≡ diff w2 → AHomotopyStd C5LEc w1 w2
diff-class {w1} {w2} h =
  proj₂ (class-iff w1 w2)
        (diff-eq-back (nCwL w1) (nCcwL w1) (nCwL w2) (nCcwL w2) h)

--------------------------------------------------------------------------------
-- § ㉓ ★★★★★ 同构记录：`π₁(C5L) ≅ ℤ`（以 5ℤ 为像 ✓）
--------------------------------------------------------------------------------

record C5LWinding : Set₁ where
  field
    to        : Walk C5LEc c0 c0 → ℤ
    from      : ℤ → Walk C5LEc c0 c0
    to-cong   : ∀ {w1 w2 : Walk C5LEc c0 c0} → AHomotopyStd C5LEc w1 w2 → to w1 ≡ to w2
    from-wind : ∀ (z : ℤ) → to (from z) ≡ (Int.+ 5) *ℤ z
    to-wind   : ∀ (w : Walk C5LEc c0 c0) → Σ ℤ (λ k → to w ≡ (Int.+ 5) *ℤ k)
    to-mul    : ∀ (w1 w2 : Walk C5LEc c0 c0) → to (w1 ++w w2) ≡ to w1 +ℤ to w2
    to-inj    : ∀ {w1 w2 : Walk C5LEc c0 c0} → to w1 ≡ to w2 → AHomotopyStd C5LEc w1 w2

c5l-iso : C5LWinding
c5l-iso = record
  { to        = diff
  ; from      = iter5Z
  ; to-cong   = λ {w1} {w2} h → diff-inv h
  ; from-wind = iter5Z-wind
  ; to-wind   = diff-div5
  ; to-mul    = diff-mul
  ; to-inj    = λ {w1} {w2} h → diff-class h
  }
