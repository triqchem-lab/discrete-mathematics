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
open import Sovereign.Synthesis.BarceloAHomotopy
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

--------------------------------------------------------------------------------
-- ⑤ 商面群运算（P2.2c (b2-群)）：⊞ᵈ 乘法 + 单位 + 结合 modulo ∼；逆 = 对称图条件件
--------------------------------------------------------------------------------
--
-- 数学背景：π₁ᵈ 上的群结构三件——乘法由 concat 诱导（⊞-resp 保证良定义），
--   单位 = [ nil ]，结合 modulo ∼ 由 walk 连接结合律提升。
--   ⚠ 逆元的本体论边界：walk 反向落在 **反向图 Gᵒᵖ**（有向图边不可自动翻回）——
--   逆运算需要对称结构（flip : edge G a b → edge G b a）；一般有向图立界。
-- 策略：双 rec（外层函数空间 isSetΠ）+ elimProp/（商上等式是命题）+ 复用 ⊞-resp 零重证。

open import Cubical.Foundations.Prelude using (funExt; cong) renaming (subst2 to subst₂)
open import Cubical.Foundations.HLevels using (isSetΠ)
open import Cubical.HITs.SetQuotients.Properties using (elimProp3) renaming (elimProp to elimProp/q)
open import Sovereign.Synthesis.BarceloAHomotopy
  using (cons; _++w_; AStep; slide; expand; refl'; symm; trans'; gen)
open import _PPI using (⊞-resp; ++w-resp-l)
open import Data.Fin using (Fin)
open import Data.Unit using (⊤; tt)

-- ── 5.1 乘法良定义（双 rec：内层固定 ℓ 消 m，外层消 ℓ——函数空间 isSet）──

private
  ⊞ᵈ-inner : ∀ (G : DiGraph) (x : DiGraph.V G) (ℓ : Loop G x) → π₁ᵈ G x → π₁ᵈ G x
  ⊞ᵈ-inner G x ℓ = π₁ᵈ-rec squash/ (λ m → [ ℓ ++w m ])
                     (λ m m' h → eq/ (ℓ ++w m) (ℓ ++w m') (++w-resp-l G ℓ h))
  -- 合同性输入：++w-resp-l（_PPI ④节）零重证

  ⊞ᵈ-outer : ∀ (G : DiGraph) (x : DiGraph.V G) (ℓ ℓ' : Loop G x)
           → AHomotopy G ℓ ℓ'
           → _≡_ {A = π₁ᵈ G x → π₁ᵈ G x} (⊞ᵈ-inner G x ℓ) (⊞ᵈ-inner G x ℓ')
  ⊞ᵈ-outer G x ℓ ℓ' h =
    funExt (elimProp/q (λ q → squash/ _ _)
      λ m → eq/ (ℓ ++w m) (ℓ' ++w m) (⊞-resp G h (AH-refl m)))
  -- 商上等式是命题（squash/）⇒ elimProp/ 合法；代表元步 = ⊞-resp（hℓ = h，hm = refl）

_⊞ᵈ_ : ∀ {G x} → π₁ᵈ G x → π₁ᵈ G x → π₁ᵈ G x
_⊞ᵈ_ {G} {x} = π₁ᵈ-rec (isSetΠ (λ _ → squash/)) (⊞ᵈ-inner G x) (⊞ᵈ-outer G x)

-- ── 5.2 walk 连接单位元（Cubical 世界重证——两 _≡_ 分世界纪律）──

++w-idʳ : ∀ (G : DiGraph) {a b} (p : Walk G a b)
       → _≡_ {A = Walk G a b} (p ++w nil b) p
++w-idʳ G (nil v) = refl
++w-idʳ G (cons e p) = cong (cons e) (++w-idʳ G p)

-- 商面单位元双侧
⊞ᵈ-unitʳ : ∀ {G x} (q : π₁ᵈ G x) → _≡_ {A = π₁ᵈ G x} (q ⊞ᵈ [ nil x ]) q
⊞ᵈ-unitʳ {G} {x} = elimProp/q (λ q → squash/ _ _) λ ℓ → cong [_] (++w-idʳ G ℓ)

⊞ᵈ-unitˡ : ∀ {G x} (q : π₁ᵈ G x) → _≡_ {A = π₁ᵈ G x} ([ nil x ] ⊞ᵈ q) q
⊞ᵈ-unitˡ {G} {x} = elimProp/q (λ q → squash/ _ _) λ ℓ → refl
--   [ nil ++ ℓ ] = [ ℓ ] [defeq：nil ++w q = q]

-- ── 5.3 结合 modulo ∼（walk 连接结合律提升）──

++w-assoc : ∀ (G : DiGraph) {a b c d} (p : Walk G a b) (m : Walk G b c) (n : Walk G c d)
          → _≡_ {A = Walk G a d} ((p ++w m) ++w n) (p ++w (m ++w n))
++w-assoc G (nil v) m n = refl
++w-assoc G (cons e p) m n = cong (cons e) (++w-assoc G p m n)

⊞ᵈ-assoc : ∀ {G x} (a b c : π₁ᵈ G x)
         → _≡_ {A = π₁ᵈ G x} ((a ⊞ᵈ b) ⊞ᵈ c) (a ⊞ᵈ (b ⊞ᵈ c))
⊞ᵈ-assoc {G} {x} =
  elimProp3 (λ a b c → squash/ _ _)
    (λ ℓ m n → cong [_] (++w-assoc G ℓ m n))

-- ── 5.4 逆元（对称图条件件）：rev + 合同性 ──
--
-- 本体论边界：rev : Walk G a b → Walk G b a 需要边翻转 flip（反向边在 Gᵒᵖ）。
--   对称图（带 flip 数据）下 rev 回落 G；一般有向图**立界**（见节尾）。

rev : ∀ (G : DiGraph) {a b} (flip : ∀ {u v} → DiGraph.edge G u v → DiGraph.edge G v u)
    → Walk G a b → Walk G b a
rev G flip (nil v) = nil v
rev G flip (cons {u = u} e p) = rev G flip p ++w cons (flip e) (nil u)

-- rev 形状桥（slide/expand 反演的对齐件——免匹配优先 + 泛化索引防塌陷）
rev-nested : ∀ (G : DiGraph) {x y z v} (flip : ∀ {u w} → DiGraph.edge G u w → DiGraph.edge G w u)
           → (b : Walk G z v) (e1 : DiGraph.edge G x y) (e2 : DiGraph.edge G y z)
           → _≡_ {A = Walk G v x} (rev G flip (cons e1 (cons e2 b)))
                                  (rev G flip b ++w cons (flip e2) (cons (flip e1) (nil x)))
rev-nested G flip b e1 e2 = ++w-assoc G (rev G flip b) (cons (flip e2) (nil _)) (cons (flip e1) (nil _))
--   rev 对 cons 头 definitional 归约 ⇒ 无须匹配 b；一步 assoc 归位（C₂++C₁ 形 defeq）

rev-form3 : ∀ (G : DiGraph) {a x z v} (flip : ∀ {u w} → DiGraph.edge G u w → DiGraph.edge G w u)
          → (p : Walk G a x) (b : Walk G z v) (e3 : DiGraph.edge G x z)
          → _≡_ {A = Walk G v a} (rev G flip (p ++w cons e3 b))
                                 (rev G flip b ++w cons (flip e3) (rev G flip p))
rev-form3 G flip (nil _) b e3 = refl
rev-form3 G flip (cons e p) b e3 =
  cong (_++w cons (flip e) (nil _)) (rev-form3 G flip p b e3)
    ∙ ++w-assoc G (rev G flip b) (cons (flip e3) (rev G flip p)) (cons (flip e) (nil _))
--   nil 案 defeq（rev (cons e3 b) 归约）；cons 案 = IH 搬运 + assoc 归位 [2 链]

rev-form2 : ∀ (G : DiGraph) {a x y z v} (flip : ∀ {u w} → DiGraph.edge G u w → DiGraph.edge G w u)
          → (p : Walk G a x) (b : Walk G z v) (e1 : DiGraph.edge G x y) (e2 : DiGraph.edge G y z)
          → _≡_ {A = Walk G v a} (rev G flip (p ++w cons e1 (cons e2 b)))
                                 (rev G flip b ++w cons (flip e2) (cons (flip e1) (rev G flip p)))
rev-form2 G flip (nil _) b e1 e2 = rev-nested G flip b e1 e2
rev-form2 G flip (cons e p) b e1 e2 =
  cong (_++w cons (flip e) (nil _)) (rev-form2 G flip p b e1 e2)
    ∙ ++w-assoc G (rev G flip b) (cons (flip e2) (cons (flip e1) (rev G flip p))) (cons (flip e) (nil _))

-- rev 对 A-homotopy 合同（四案——gen 案 = slide↔expand 反演 + subst₂ 对齐）
rev-resp : ∀ (G : DiGraph) {a b} (flip : ∀ {u v} → DiGraph.edge G u v → DiGraph.edge G v u)
         → {w1 w2 : Walk G a b} → AHomotopy G w1 w2
         → AHomotopy G (rev G flip w1) (rev G flip w2)
rev-resp G flip (refl' w) = refl' (rev G flip w)
rev-resp G flip (symm h) = symm (rev-resp G flip h)
rev-resp G flip (trans' h1 h2) = trans' (rev-resp G flip h1) (rev-resp G flip h2)
rev-resp G flip (gen (slide p b e1 e2 e3)) =
  subst₂ (λ u w → AHomotopy G u w)
    (sym (rev-form2 G flip p b e1 e2)) (sym (rev-form3 G flip p b e3))
    (symm (gen (expand (rev G flip b) (rev G flip p) (flip e2) (flip e1) (flip e3))))
rev-resp G flip (gen (expand p b e1 e2 e3)) =
  subst₂ (λ u w → AHomotopy G u w)
    (sym (rev-form3 G flip p b e3)) (sym (rev-form2 G flip p b e1 e2))
    (symm (gen (slide (rev G flip b) (rev G flip p) (flip e2) (flip e1) (flip e3))))
--   反演要点：slide 反向 = expand（e1↔e2 位对换、e3 单支）——附录 14 对齐范式

-- 逆运算（商面良定义——rev-resp 合同性输入）
invᵈ : ∀ {G x} (flip : ∀ {u v} → DiGraph.edge G u v → DiGraph.edge G v u) → π₁ᵈ G x → π₁ᵈ G x
invᵈ {G} {x} flip = π₁ᵈ-rec squash/ (λ ℓ → [ rev G flip ℓ ])
                      (λ ℓ ℓ' h → eq/ _ _ (rev-resp G flip h))

-- ── 5.5 G2s 对称双点图核对（三件）──

G2s : DiGraph
G2s = record { V = Fin 2 ; edge = λ a b → ⊤ }

flip2s : ∀ {u v} → DiGraph.edge G2s u v → DiGraph.edge G2s v u
flip2s {u} {v} _ = tt

check-⊞ᵈ-assoc : _≡_ {A = π₁ᵈ G2s fzero} (([ nil fzero ] ⊞ᵈ [ nil fzero ]) ⊞ᵈ [ nil fzero ])
                                     ([ nil fzero ] ⊞ᵈ ([ nil fzero ] ⊞ᵈ [ nil fzero ]))
check-⊞ᵈ-assoc = ⊞ᵈ-assoc [ nil fzero ] [ nil fzero ] [ nil fzero ]

check-⊞ᵈ-unit : _≡_ {A = π₁ᵈ G2s fzero} ([ nil fzero ] ⊞ᵈ [ nil fzero ]) [ nil fzero ]
check-⊞ᵈ-unit = ⊞ᵈ-unitʳ [ nil fzero ]

check-invᵈ-ℓ0 : _≡_ {A = π₁ᵈ G2s fzero} (invᵈ (λ {u} {v} → flip2s {u} {v}) [ nil fzero ]) [ nil fzero ]
check-invᵈ-ℓ0 = refl

-- ── 5.6 立界（精确剩余）──
-- (i) 一般逆律 q ⊞ᵈ invᵈ q ≡ [ nil ]：需 w ++w rev w ∼ nil 的 A-homotopy 收缩
--   （逐边 expand 对消——归纳 ~20-40 行）；G2s 平凡例已核（check-invᵈ-ℓ0）。
-- (ii) 一般有向图的逆：无 flip 则 rev 落 Gᵒᵖ，π₁ᵈ 仅成幺半群——逆元存在性
--   恰是「对称图 vs 有向图」的分水岭（Barcelo 理论的群/幺半群分界）。

-- ────────────────────────────────────────────────────────────────────
-- ⑥ 一般逆律：**反证件**（statement_wrong 定谳）+ 修正案立界
--
-- 数学背景：⑤节立界件「一般逆律 w ++w rev w ∼ nil」经本节定谳为**普遍假命题**——
--   AStep 生成元只有三角替换（slide/expand），两沿皆 ≥1 边 ⇒ 空 walk `nil`
--   是 AHomotopy **孤立点**。非空 w 时 w ++w rev w（非空）永远 ∼ 不上 nil。
--   Q 不变量 = 「同零长 ⊕ 同正长」（len 测度法——免匹配纪律：无 absurd 模式、
--   无索引统一，K 禁用下全程安全）。
-- 修正案（立界，与 ⑤节 flip 分水岭并列）：
--   (1) 逆律需 AStep 增**回溯消去生成元** backtrack：
--       AStep'(p ++ cons e (cons (flip e) b)) (p ++ b)——生成元入定义
--       （豁免精化判据正解②；本体论：「带反转 A-homotopy」的标准生成集）；
--   (2) 涟漪清单：AHomotopy 合同族（disp2-respects 等）补 backtrack 案；
--       disp2 对该案需新前提「flip 权重互逆」wt x y *A wt (flip e) ≡ oneA；
--   (3) 修补后逆律骨架（~20-40 行）：cons e p 归纳 + rev-resp 搬运 +
--       backtrack 收口；⊞ᵈ-inv = elimProp/q + cong [_] 一步。
-- ────────────────────────────────────────────────────────────────────

open import Data.Empty using (⊥; ⊥-elim)

-- flip2s 具名化（消 λ 实参 meta）
fl2s : ∀ {u v : DiGraph.V G2s} → DiGraph.edge G2s u v → DiGraph.edge G2s v u
fl2s {u} {v} e = flip2s {u} {v} e
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Cubical.Data.Bool using (Bool; true; false; isSetBool)
open import Cubical.Foundations.Prelude using (subst)

-- len：walk 边数（nil/cons 纯计算两案——免匹配纪律：无 absurd、无索引统一）
len : ∀ {G : DiGraph} {u v} → Walk G u v → ℕ
len (nil _) = zero
len (cons e p) = suc (len p)

Pos : ℕ → Set
Pos zero = ⊥
Pos (suc n) = ⊤

isZeroB : ℕ → Bool
isZeroB zero = true
isZeroB (suc n) = false

-- Q：同零长 ⊕ 同正长（AHomotopy 不变量）
Q : ∀ {G : DiGraph} {u v} → Walk G u v → Walk G u v → Set
Q a b = ((len a ≡ zero) × (len b ≡ zero)) ⊎ (Pos (len a) × Pos (len b))

Q-self : ∀ {G : DiGraph} {u v} (a : Walk G u v) → Q a a
Q-self (nil _) = inj₁ (refl , refl)
Q-self (cons e p) = inj₂ (tt , tt)

-- p ++ cons e b 恒正长（两案纯计算）
++w-cons-Pos : ∀ {G : DiGraph} {u x z v} (p : Walk G u x) (e : DiGraph.edge G x z) (b : Walk G z v)
             → Pos (len (p ++w cons e b))
++w-cons-Pos (nil _) e b = tt
++w-cons-Pos (cons e p) e' b = tt

-- AStep 两沿恒同正长（slide/expand 皆 p ++ cons …形）
Q-AStep : ∀ {G : DiGraph} {u v} {a b : Walk G u v} → AStep G a b → Q a b
Q-AStep (slide p q e1 e2 e3) = inj₂ (++w-cons-Pos p e1 (cons e2 q) , ++w-cons-Pos p e3 q)
Q-AStep (expand p q e1 e2 e3) = inj₂ (++w-cons-Pos p e3 q , ++w-cons-Pos p e1 (cons e2 q))

Q-swap : ∀ {G : DiGraph} {u v} {a b : Walk G u v} → Q a b → Q b a
Q-swap (inj₁ (x , y)) = inj₁ (y , x)
Q-swap (inj₂ (x , y)) = inj₂ (y , x)

Q-trans : ∀ {G : DiGraph} {u v} {a b c : Walk G u v} → Q a b → Q b c → Q a c
Q-trans (inj₁ (x , _)) (inj₁ (_ , z)) = inj₁ (x , z)
Q-trans (inj₁ (_ , eb)) (inj₂ (nb , _)) = ⊥-elim (subst Pos eb nb)
Q-trans (inj₂ (_ , nb)) (inj₁ (eb , _)) = ⊥-elim (subst Pos eb nb)
Q-trans (inj₂ (x , _)) (inj₂ (_ , z)) = inj₂ (x , z)

-- Q 是 AHomotopy 不变量（四案归纳）
Q-hom : ∀ {G : DiGraph} {u v} {a b : Walk G u v} → AHomotopy G a b → Q a b
Q-hom (refl' w) = Q-self w
Q-hom (symm h) = Q-swap (Q-hom h)
Q-hom (trans' h1 h2) = Q-trans (Q-hom h1) (Q-hom h2)
Q-hom (gen s) = Q-AStep s

-- 主反证件：非空 w ⇒ w ++w rev w 永不 ∼ nil（通用图——**含环亦假**）
inv-law-false : ∀ {G : DiGraph} (fl : ∀ {u v} → DiGraph.edge G u v → DiGraph.edge G v u)
                {x y} (w : Walk G x y) (ne : Pos (len w))
              → AHomotopy G (w ++w rev G fl w) (nil x) → ⊥
inv-law-false {G} fl {x} {y} (cons e p) tt h = go (Q-hom h)
  where
  go : Q (cons e (p ++w rev G fl (cons e p))) (nil x) → ⊥
  go (inj₁ (ez , _)) = ⊥-elim (subst Pos ez tt)
  go (inj₂ (_ , pn)) = ⊥-elim pn

-- S 分离器两桥（isZeroB ∘ len——ℕ 上归纳，K 安全）
isZero-false : (n : ℕ) → Pos n → _≡_ {A = Bool} (isZeroB n) false
isZero-false zero p = ⊥-elim p
isZero-false (suc n) tt = refl

S-resp : ∀ {G : DiGraph} {u v} (a b : Walk G u v) → AHomotopy G a b
       → _≡_ {A = Bool} (isZeroB (len a)) (isZeroB (len b))
S-resp a b h = go (Q-hom h)
  where
  go : Q a b → _≡_ {A = Bool} (isZeroB (len a)) (isZeroB (len b))
  go (inj₁ (ez , ez')) = cong isZeroB ez ∙ cong isZeroB (sym ez')
  go (inj₂ (pa , pb)) = isZero-false (len a) pa ∙ sym (isZero-false (len b) pb)

S̄ : ∀ {G : DiGraph} {x : DiGraph.V G} → π₁ᵈ G x → Bool
S̄ {G} {x} = π₁ᵈ-rec isSetBool (λ ℓ → isZeroB (len ℓ)) (λ ℓ m h → S-resp ℓ m h)

T : Bool → Set
T true = ⊤
T false = ⊥

true≢false : _≡_ {A = Bool} true false → ⊥
true≢false p = subst T p tt

-- 平凡例核对（ℓ0 路径：nil ++ rev nil = nil ∼ nil ✓）
check-inv-law-ℓ0 : AHomotopy G2s (nil fzero ++w rev G2s (λ {u} {v} → flip2s {u} {v}) (nil fzero)) (nil fzero)
check-inv-law-ℓ0 = AH-refl (nil fzero)

-- 商面通用反证件（变量 walk 形——具体例因常值边族（edge G2s _ _ ≡ ⊤）的
--   顶点隐式 meta 怪癖改走通用形；inv-law-false 已覆盖全部非空 walk）
no-quot-nil-gen : ∀ {x : DiGraph.V G2s} (ℓ : Loop G2s x) → Pos (len ℓ)
                → _≡_ {A = π₁ᵈ G2s x} [ ℓ ] [ nil x ] → ⊥
no-quot-nil-gen ℓ p q = true≢false (sym (sym (isZero-false (len ℓ) p) ∙ cong S̄ q))

-- 一般例（手工核对清单——编译外证据）：G2s 上 w = e00∷e00∷nil（2 边 loop），
--   w ++w rev w = 4 边 walk，Q-hom 任意 ∼ 触不到 nil（inv-law-false 实例）。

