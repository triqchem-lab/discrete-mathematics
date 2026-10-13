{-# OPTIONS --rewriting --guardedness #-}

-- | _PPI5b —— πₙ-B2：C→A 桥（可判定排程）+ DHomotopy 柱体细化（Iᵈ 单步生成元形）
--
-- 数学背景：
--   按 docs/plan/pi-n-design.md 路线行 πₙ-B2（B1 成果在 _PPI5）：
--   ① C→A 桥 = 「子集排序成链」的可判定排程——C 呈现层（sub-face 包含）
--     ↔ A 计算层（Snd-face 有序链）互译：有序链之间的包含关系给出
--     **唯一单调索引映射**（排程），排程由可判定查表 find-vert 构造；
--     二元枚举排序成链 sort2 是其最小通用形。
--   ② DHomotopy 柱体细化 = Iᵈ 单步生成元形：单步 = 2 点组合区间 Id 上的
--     柱体映射（端点取值 + 步相等——gen 案的柱体形，与 DStep 等价）；
--     n 步柱体 = 单步生成元序列（Chain），DHomotopy 四案各有柱体解释：
--     refl'→cnil / gen→单步 / symm'→逆序 / trans'→拼接。
--   不动 B1 件（Snd-face/sub-face/DHomotopy/dh-pw/pw-dh 全引不改）。
--
-- 核心原则：
--   1. 复用优先：<ᵢ/Simplex（_PPI3）、linPoset/Snd-face/sub-face/vert-distinct/
--      DStep/DHomotopy/dh-pw/pw-dh/vchain-2case（_PPI5）零重证；
--   2. 免匹配纪律（#51/#52）：Fin 构造子走 {zero}/{suc _} 形；suc _ ≤ 0 头级
--      可 refute（a3 备忘）；辅助件顶层命名（免匹配范式）；
--   3. 查表/排程带 Dec 实参（aux 判定参数范式）——不嵌 with 沼泽；
--   4. 零洞零 postulate；核对件 refl 级。
--
-- 包含：≟Fin · tail-spx · find-vert（可判定查表）
--       · sched/sched-pw/sched-mono/sched-uniq/mono→sub（C↔A 互译）
--       · vchain-2gen · sort2（二元排序成链）
--       · Id · CylObj · CylStep · dstep↔cs（单步生成元形）
--       · Chain/capp/crev/chain-pw/chain-len/dh↔chain（柱体四案解释）
--       · S¹ᵈ 核对层（桥往返 + 排序 + 柱体实例）
module _PPI5b where

-- ────────────────────────────────────────────────────────────────────
-- ② 导入区
-- ────────────────────────────────────────────────────────────────────
open import Data.Nat using (ℕ; zero; suc; _≤_; _<_; z≤n; s≤s)
open import Data.Nat.Properties using (_≟_; _≤?_; ≤-trans; ≤-total; ≤∧≢⇒<; ≰⇒>; n≤1+n)
open import Data.Fin using (Fin; toℕ) renaming (zero to fzero; suc to fsuc)
open import Data.Fin.Properties using (toℕ-injective; ¬Fin0)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (_×_; Σ; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; cong; trans; subst)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Sovereign.Synthesis.OrderComplex using (Strict)
open import _PPI3 using (_<ᵢ_; Simplex) renaming (≤-irrefl-1 to ≤irr1)
open import _PPI5 using
  ( linPoset; Snd-face; sub-face; vert-distinct; DStep; DHomotopy; refl'; symm'; trans'; gen
  ; dh-pw; pw-dh; S1d-face; vv0; vv2; v01; v02; vchain-2case; check-sub-v0; g2fold )

-- ────────────────────────────────────────────────────────────────────
-- ③ 基础件层：可判定序件 + 查表机件
-- ────────────────────────────────────────────────────────────────────

-- Fin 异名判定（toℕ 单射反演）
_≟Fin_ : ∀ {m} (a b : Fin m) → Dec (a ≡ b)
a ≟Fin b with toℕ a ≟ toℕ b
... | yes p = yes (toℕ-injective p)
... | no  q = no (λ eq → q (cong toℕ eq))

-- 尾单形（查表递归机件——顶点表取 fsuc 后缀）
tail-spx : ∀ {m k} → Simplex (linPoset m) (suc k) → Simplex (linPoset m) k
tail-spx s = record
  { vert   = λ j → Simplex.vert s (fsuc j)
  ; vchain = λ i j p → Simplex.vchain s (fsuc i) (fsuc j) (s≤s p) }

-- 查表否定汇聚（顶层命名——免匹配范式）
find-no : ∀ {m k} (t : Simplex (linPoset m) (suc k)) (v : Fin m) →
          ¬ (Simplex.vert t fzero ≡ v) →
          ¬ (Σ (Fin k) (λ j → Simplex.vert (tail-spx t) j ≡ v)) →
          ¬ (Σ (Fin (suc k)) (λ j → Simplex.vert t j ≡ v))
find-no t v nq1 nq2 (fzero , q) = nq1 q
find-no t v nq1 nq2 (fsuc j , q) = nq2 (j , q)

-- 顶层辅助件（免匹配范式——三件均无 with 嵌套）
toℕ-≢ : ∀ {m} {a b : Fin m} → a ≢ b → toℕ a ≢ toℕ b
toℕ-≢ nq e = nq (toℕ-injective e)

<-≡-irr : ∀ {u v : ℕ} → u < v → u ≡ v → ⊥
<-≡-irr {u} lt eq = ≤irr1 (subst (λ y → suc u ≤ y) (sym eq) lt)

<-asym : ∀ {u v : ℕ} → u < v → v < u → ⊥
<-asym {u} {v} p q = ≤irr1 (≤-trans p (≤-trans (n≤1+n v) q))

-- 可判定查表：v 在顶点表 t 中的位置（Dec——排程的判定机件）
find-vert : ∀ {m k} (t : Simplex (linPoset m) k) (v : Fin m) →
            Dec (Σ (Fin k) (λ j → Simplex.vert t j ≡ v))
find-vert {k = zero}   t v = no (λ w → ¬Fin0 (proj₁ w))
find-vert {k = suc k} t v with Simplex.vert t fzero ≟Fin v
... | yes p = yes (fzero , p)
... | no nq1 with find-vert (tail-spx t) v
...   | yes (j , q) = yes (fsuc j , q)
...   | no  nq2     = no (find-no t v nq1 nq2)

-- Strict 反演：顶点表严格递增（toℕ 层）
vert-strict : ∀ {m k} (t : Simplex (linPoset m) k) (a b : Fin k) → a <ᵢ b →
              toℕ (Simplex.vert t a) < toℕ (Simplex.vert t b)
vert-strict t a b p with Simplex.vchain t a b p
... | le , ne = ≤∧≢⇒< le (λ eq → ne (toℕ-injective eq))

-- 顶点表单射（排程唯一性的机件）
vert-inj : ∀ {m k} (t : Simplex (linPoset m) k) (a b : Fin k) →
           Simplex.vert t a ≡ Simplex.vert t b → a ≡ b
vert-inj t a b eq with a ≟Fin b
... | yes q = q
... | no  nq with ≤-total (toℕ a) (toℕ b)
...   | inj₁ le = ⊥-elim (<-≡-irr (vert-strict t a b (≤∧≢⇒< le (toℕ-≢ nq))) (cong toℕ eq))
...   | inj₂ le = ⊥-elim (<-≡-irr (vert-strict t b a (≤∧≢⇒< le (toℕ-≢ (λ e → nq (sym e)))))
                                   (sym (cong toℕ eq)))

-- ────────────────────────────────────────────────────────────────────
-- ④ C→A 桥：包含 → 可判定排程（互译三件 + 唯一性）
-- ────────────────────────────────────────────────────────────────────

-- 排程见证（可判定查表构造——「可判定排程」本体）
sched-w : ∀ {n k l} (s : Snd-face n k) (t : Snd-face n l) (sub : sub-face s t) (i : Fin k) →
          Σ (Fin l) (λ j → Simplex.vert s i ≡ Simplex.vert t j)
sched-w s t sub i with find-vert t (Simplex.vert s i)
... | yes (j , q) = j , sym q
... | no  nq      = ⊥-elim (nq (proj₁ (sub i) , sym (proj₂ (sub i))))

-- 排程（索引映射）+ 点态相等
sched : ∀ {n k l} (s : Snd-face n k) (t : Snd-face n l) (sub : sub-face s t) → Fin k → Fin l
sched s t sub i = proj₁ (sched-w s t sub i)

sched-pw : ∀ {n k l} (s : Snd-face n k) (t : Snd-face n l) (sub : sub-face s t) →
           ∀ i → Simplex.vert s i ≡ Simplex.vert t (sched s t sub i)
sched-pw s t sub i = proj₂ (sched-w s t sub i)

-- 排程单调（有序链的排程保序——「排序成链」的序内容）
sched-mono : ∀ {n k l} (s : Snd-face n k) (t : Snd-face n l) (sub : sub-face s t) →
             ∀ i j → i <ᵢ j → sched s t sub i <ᵢ sched s t sub j
sched-mono s t sub i j p = mono-go
  where
    g : _ → _
    g = sched s t sub
    lt-s : toℕ (Simplex.vert s i) < toℕ (Simplex.vert s j)
    lt-s = vert-strict s i j p
    pw-i : toℕ (Simplex.vert s i) ≡ toℕ (Simplex.vert t (g i))
    pw-i = cong toℕ (sched-pw s t sub i)
    pw-j : toℕ (Simplex.vert s j) ≡ toℕ (Simplex.vert t (g j))
    pw-j = cong toℕ (sched-pw s t sub j)
    lt-t : toℕ (Simplex.vert t (g i)) < toℕ (Simplex.vert t (g j))
    lt-t = subst (λ x → suc x ≤ toℕ (Simplex.vert t (g j))) pw-i
             (subst (λ y → suc (toℕ (Simplex.vert s i)) ≤ y) pw-j lt-s)
    mono-go : g i <ᵢ g j
    mono-go with toℕ (g i) ≟ toℕ (g j)
    ... | yes e = ⊥-elim (<-≡-irr lt-t (cong toℕ (cong (Simplex.vert t) (toℕ-injective e))))
    ... | no  ne with ≤-total (toℕ (g i)) (toℕ (g j))
    ...   | inj₁ le = ≤∧≢⇒< le ne
    ...   | inj₂ le = ⊥-elim (<-asym lt-t
                          (vert-strict t (g j) (g i) (≤∧≢⇒< le (λ e → ne (sym e)))))

-- 排程唯一（mono→sub 的逆向配套——互译闭合）
sched-uniq : ∀ {n k l} (s : Snd-face n k) (t : Snd-face n l) (sub : sub-face s t) →
             (g₂ : Fin k → Fin l) → (∀ i → Simplex.vert s i ≡ Simplex.vert t (g₂ i)) →
             ∀ i → sched s t sub i ≡ g₂ i
sched-uniq s t sub g₂ pw2 i =
  vert-inj t (sched s t sub i) (g₂ i)
    (trans (sym (sched-pw s t sub i)) (pw2 i))

-- A→C（互译另一半）：单调点态映射 → 包含
mono→sub : ∀ {n k l} (s : Snd-face n k) (t : Snd-face n l) →
           (g : Fin k → Fin l) → (∀ i → Simplex.vert s i ≡ Simplex.vert t (g i)) →
           sub-face s t
mono→sub s t g pw i = g i , pw i

-- ────────────────────────────────────────────────────────────────────
-- ⑤ 排序成链：二元枚举的最小通用形（C 无序枚举 → A 有序链）
-- ────────────────────────────────────────────────────────────────────

-- 二元链性分派器（vchain-2case 的泛形——m 任意）
vchain-2gen : ∀ {m} (f : Fin 2 → Fin m) →
              toℕ (f fzero) ≤ toℕ (f (fsuc fzero)) →
              f fzero ≢ f (fsuc fzero) →
              (i j : Fin 2) → i <ᵢ j → Strict (linPoset m) (f i) (f j)
vchain-2gen f le ne fzero      (fsuc fzero) _ = le , ne
vchain-2gen f le ne fzero      fzero        ()
vchain-2gen f le ne (fsuc fzero) fzero      ()
vchain-2gen f le ne (fsuc fzero) (fsuc fzero) (s≤s ())

-- 二元枚举排序成链（升序链 + 像集保序/交换二择一——排序往返内容）
sort2 : ∀ {m} (f : Fin 2 → Fin m) → f fzero ≢ f (fsuc fzero) →
        Σ (Simplex (linPoset m) 2) (λ s →
          (Simplex.vert s fzero ≡ f fzero × Simplex.vert s (fsuc fzero) ≡ f (fsuc fzero)) ⊎
          (Simplex.vert s fzero ≡ f (fsuc fzero) × Simplex.vert s (fsuc fzero) ≡ f fzero))
sort2 {m} f ne with toℕ (f fzero) ≤? toℕ (f (fsuc fzero))
... | yes le = record { vert = f ; vchain = vchain-2gen f le ne } , inj₁ (refl , refl)
... | no  nle = record { vert = swp ; vchain = vchain-2gen swp le₂ ne₂ } , inj₂ (refl , refl)
  where
    swp : Fin 2 → Fin m
    swp fzero      = f (fsuc fzero)
    swp (fsuc fzero) = f fzero
    le₂ : toℕ (swp fzero) ≤ toℕ (swp (fsuc fzero))
    le₂ = ≤-trans (n≤1+n (toℕ (f (fsuc fzero)))) (≰⇒> nle)
    ne₂ : swp fzero ≢ swp (fsuc fzero)
    ne₂ e = ne (sym e)

-- ────────────────────────────────────────────────────────────────────
-- ⑥ 柱体机件：Iᵈ 单步生成元形（DHomotopy 四案的柱体解释）
-- ────────────────────────────────────────────────────────────────────

-- Iᵈ = 2 点组合区间（单步承载）
data Id : Set where
  i0 i1 : Id

-- S × Iᵈⁿ（n 步柱体对象——纯组合数据）
CylObj : Set → ℕ → Set
CylObj S n = S × Fin (suc n)

-- 单步生成元：Iᵈ 单步柱体映射（端点取值 + 步相等）——gen 案的柱体形
CylStep : {S X : Set} (f g : S → X) → Set
CylStep {S} {X} f g = Σ (S → Id → X) (λ H →
  (∀ s → H s i0 ≡ f s) × (∀ s → H s i1 ≡ g s) × (∀ s → H s i1 ≡ H s i0))

-- 单步生成元形 ↔ DStep（柱体单步 = 逐点步）
dstep→cs : {S X : Set} {f g : S → X} → DStep f g → CylStep f g
dstep→cs {S} {X} {f} {g} d = H , (λ s → refl) , (λ s → refl) , (λ s → sym (d s))
  where
    H : S → Id → X
    H s i0 = f s
    H s i1 = g s

cs→dstep : {S X : Set} {f g : S → X} → CylStep f g → DStep f g
cs→dstep (H , at0 , at1 , st) s = trans (sym (at0 s)) (trans (sym (st s)) (at1 s))

-- n 步柱体 = 单步生成元序列（柱体展开形）
data Chain {S X : Set} : (S → X) → (S → X) → Set where
  cnil  : ∀ {f : S → X} → Chain f f
  ccons : ∀ {f g h : S → X} → DStep f g → Chain g h → Chain f h

-- 拼接（trans' 案的柱体解释）
capp : {S X : Set} {f g h : S → X} → Chain f g → Chain g h → Chain f h
capp cnil        c2 = c2
capp (ccons d c1) c2 = ccons d (capp c1 c2)

-- 逆序（symm' 案的柱体解释）
crev : {S X : Set} {f g : S → X} → Chain f g → Chain g f
crev cnil         = cnil
crev (ccons d c)  = capp (crev c) (ccons (λ s → sym (d s)) cnil)

-- 逐点解释 + 步数
chain-pw : {S X : Set} {f g : S → X} → Chain f g → ∀ s → f s ≡ g s
chain-pw cnil        s = refl
chain-pw (ccons d c) s = trans (d s) (chain-pw c s)

chain-len : {S X : Set} {f g : S → X} → Chain f g → ℕ
chain-len cnil        = zero
chain-len (ccons d c) = suc (chain-len c)

-- DHomotopy ↔ Chain（四案柱体解释——本件核心）
dh→chain : {S X : Set} {f g : S → X} → DHomotopy f g → Chain f g
dh→chain refl'        = cnil
dh→chain (gen d)       = ccons d cnil
dh→chain (symm' q)     = crev (dh→chain q)
dh→chain (trans' q1 q2) = capp (dh→chain q1) (dh→chain q2)

chain→dh : {S X : Set} {f g : S → X} → Chain f g → DHomotopy f g
chain→dh c = pw-dh (chain-pw c)

-- ────────────────────────────────────────────────────────────────────
-- ⑦ S¹ᵈ 核对层：桥往返 + 排序 + 柱体实例（refl 级）
-- ────────────────────────────────────────────────────────────────────

-- vv2 ⊆ v02 的包含见证（C 视图原子）
sub-vv2-v02 : sub-face vv2 v02
sub-vv2-v02 fzero = fsuc fzero , refl

-- 桥实例①：vv0 ⊆ v01 的排程 = 首位（查表找 0）
check-sched-0 : sched vv0 v01 check-sub-v0 fzero ≡ fzero
check-sched-0 = refl

-- 桥实例②：vv2 ⊆ v02 的排程 = 次位（查表跳过 0 找 2）
check-sched-2 : sched vv2 v02 sub-vv2-v02 fzero ≡ fsuc fzero
check-sched-2 = refl

-- 桥往返：mono→sub ∘ (sched,sched-pw) 回到包含（互译闭合）
check-round-sub : sub-face vv0 v01
check-round-sub = mono→sub vv0 v01 (sched vv0 v01 check-sub-v0) (sched-pw vv0 v01 check-sub-v0)

-- 排程唯一性实例（手写排程 = 构造排程）
g-hand : Fin 1 → Fin 2
g-hand fzero = fzero

pw-hand : ∀ i → Simplex.vert vv0 i ≡ Simplex.vert v01 (g-hand i)
pw-hand fzero = refl

check-uniq : ∀ i → sched vv0 v01 check-sub-v0 i ≡ g-hand i
check-uniq = sched-uniq vv0 v01 check-sub-v0 g-hand pw-hand

-- 排序成链实例（升序枚举 → 原序链；降序枚举 → 交换链）
enum-01 : Fin 2 → Fin 3
enum-01 fzero      = fzero
enum-01 (fsuc fzero) = fsuc fzero

enum-10 : Fin 2 → Fin 3
enum-10 fzero      = fsuc fzero
enum-10 (fsuc fzero) = fzero

ne-01 : enum-01 fzero ≢ enum-01 (fsuc fzero)
ne-01 ()

ne-10 : enum-10 fzero ≢ enum-10 (fsuc fzero)
ne-10 ()

check-sort-01 : toℕ (Simplex.vert (proj₁ (sort2 enum-01 ne-01)) fzero) ≡ 0
check-sort-01 = refl

check-sort-10 : toℕ (Simplex.vert (proj₁ (sort2 enum-10 ne-10)) fzero) ≡ 0
check-sort-10 = refl

check-sort-10-b : toℕ (Simplex.vert (proj₁ (sort2 enum-10 ne-10)) (fsuc fzero)) ≡ 1
check-sort-10-b = refl

-- 柱体实例（S¹ᵈ × Iᵈ）：0/1/2 步 + 单步生成元往返
d0 : DStep g2fold g2fold
d0 = λ s → refl

check-cyl-obj : CylObj (Fin 3) 1
check-cyl-obj = fzero , fzero

check-chain-0 : Chain g2fold g2fold
check-chain-0 = cnil

check-chain-1 : Chain g2fold g2fold
check-chain-1 = ccons d0 cnil

check-chain-len : chain-len (capp check-chain-1 check-chain-1) ≡ 2
check-chain-len = refl

check-crev-len : chain-len (crev (capp check-chain-1 check-chain-1)) ≡ 2
check-crev-len = refl

check-cs-round : CylStep g2fold g2fold
check-cs-round = dstep→cs d0

check-cs-back : DStep g2fold g2fold
check-cs-back = cs→dstep (dstep→cs d0)

-- 柱体四案往返（dh→chain→dh 于 gen/复合案）
check-dhchain : DHomotopy g2fold g2fold
check-dhchain = chain→dh (dh→chain (trans' (gen d0) (gen d0)))

-- ────────────────────────────────────────────────────────────────────
-- ⑧ 精确剩余（立界——B3 前置）
--   (i) 一般 k 元枚举排序成链（insertion 形）——sort2 为其 k=2 形；
--   (ii) Chain ↔ ℕ 阶梯柱体（CylObj 展开）互译——本件 Chain 即柱体展开形；
--   (iii) [Sⁿᵈ,X]_* 商型 + n=1 一般桥——B3（B1 的 S1-bridge-stmt 立界处）；
--   (iv) 未决点照立档：Sⁿᵈ 圈长参数化；C₄ 相位不打通。
-- ────────────────────────────────────────────────────────────────────
