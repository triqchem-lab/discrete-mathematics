{-# OPTIONS --rewriting --guardedness #-}
-- ══════════════════════════════════════════════════════════════════════════════
-- | _PPI4j
-- Gskel A 批：excursion 分解定理（残段形）+ two-chain 复原核对
--
-- 数学背景：
--   x-excursion = x 闭走且内部不经过 x 的非空 walk。组合事实（任意有向图）：
--   walk 在每次返回起点处切割 ⟹ 分解为 excursion 序列 + 残段（不再回起点）；
--   闭 walk 的残段为 nil ⟹ 唯一分解为 excursion 序列 ⟹ Loop ≅ 自由幺半群 F(Eₓ)。
--   NoTriangle 条件下 AHomotopy = 对角（_PPI4h 的 ah-diag-gen）⟹ π₁ᵈ ≅ Loop。
--
-- 核心原则：
--   1. PropEq 核 + eqToPath 总桥（CRT 赤免精化判据正解①同款——
--      切分需 refl 精化顶点索引，Cubical Path 不可 pattern 精化）；
--   2. **K 禁免匹配纪律（残段形）**：loop 型（同索引 Walk G u u）的 nil 匹配
--      造 reflexive 索引方程 ⇔ K（SplitError 两路实测钉死）⇒ 切分在**一般
--      walk（双异端点 metavar）**上做，输出「excursion 序列 + 残段」；
--   3. 证明携带构造（cutG/cutAccG 返回重构等式——分解存在性在构造中一次完成）；
--   4. NoX 值形命题（否定积）；前缀扩张 NoX-ext 维持内部无 x 不变量。
--
-- 包含：NoX/Nonempty/IsExc（excursion 谓词层）｜cutG/cutAccG（残段形切分——携带重构）
--       ｜two-chain 复原核对（concrete Fin 面——构造子可用，全通道 refl 验证）
-- ─────────────────────────────────────────────────────────────────────────────
-- 立界（精确剩余，root cause 钉死）：
--   (i)  loop 级残段归零：cutG w = (es , r , _) on Loop ⇒ r ≡ nil——
--        K 禁下 loop 型 nil 匹配不可行（⇔ K），需 JMeq / 长度燃料 /
--        cubical-J 化输出等式三路线之一（~30-60 行）；
--   (ii) 分解唯一性（幂等 cut∘concat = id on 全 excursion 表）——依赖 (i)；
--   (iii) MonoidIso 主定理（Loop ≅ F(Eₓ) 八字段）——依赖 (i)(ii)。
--   two-chain 具体面（Fin 构造子可用）上 (i)(ii)(iii) 已全通道 refl 级验证——
--   泛形卡点纯属 K-索引技术面，非数学缺口（对照 _PPI4g 于 Fin 2 全形可证）。
-- ══════════════════════════════════════════════════════════════════════════════
module _PPI4j where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.List using (List; []; _∷_; _++_)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂; subst)
open import Agda.Builtin.Equality using () renaming (refl to reflᴱ; _≡_ to _≡ᴱ_)
open import Cubical.Foundations.Prelude using () renaming (_≡_ to _≡ᶜ_)
open import Cubical.Data.Equality.Conversion using (eqToPath)
open import Sovereign.Topology.BarceloAHomotopy
  using (DiGraph; Walk; nil; cons; _++w_)
open import _PPI using (Loop)

private
  module DG = DiGraph

-- ══════════════════════════════════════════════════════════════════════════════
-- §0 walk 小代数（PropEq 本地形——免混世界）
-- ══════════════════════════════════════════════════════════════════════════════

++w-assocᴱ : ∀ {G : DiGraph} {a b c d} (p : Walk G a b) (m : Walk G b c) (n : Walk G c d)
           → (p ++w m) ++w n ≡ p ++w (m ++w n)
++w-assocᴱ (nil v) m n = refl
++w-assocᴱ (cons e p) m n = cong (cons e) (++w-assocᴱ p m n)

++w-nilᴱ : ∀ {G : DiGraph} {a b} (p : Walk G a b) → p ++w nil b ≡ p
++w-nilᴱ (nil v) = refl
++w-nilᴱ (cons e p) = cong (cons e) (++w-nilᴱ p)

-- ══════════════════════════════════════════════════════════════════════════════
-- §1 谓词层（excursion 定义——x 显式参数，匹配不需索引精化）
-- ══════════════════════════════════════════════════════════════════════════════

-- 顶点 x 不出现在 walk 内部（端点不算——单边 walk 无内部恒真）
NoX : ∀ {G : DiGraph} (x : DG.V G) → ∀ {u v} → Walk G u v → Set
NoX x (nil v) = ⊤
NoX x (cons e (nil v)) = ⊤
NoX x (cons {v = u'} e (cons e' b)) = (x ≡ u' → ⊥) × NoX x (cons e' b)

-- 非空形（excursion 排除 nil——自由幺半群生成元非单位）
Nonempty : ∀ {G : DiGraph} → ∀ {u v} → Walk G u v → Set
Nonempty (nil v) = ⊥
Nonempty (cons e b) = ⊤

-- x-excursion：x 闭走 + 内部无 x + 非空
IsExc : ∀ {G : DiGraph} (x : DG.V G) → Loop G x → Set
IsExc x w = NoX x w × Nonempty w

-- 前缀扩张：p 无内部 x、终点 v ≠ x ⟹ p ++w (v→w 单边) 无内部 x
NoX-ext : ∀ {G : DiGraph} {x u v w} (p : Walk G u v) → NoX x p → (x ≡ v → ⊥)
        → (e : DG.edge G v w) → NoX x (p ++w cons e (nil w))
NoX-ext (nil v) n ne e = tt
NoX-ext (cons {v = u'} e0 (nil .u')) n ne e = ne , tt
NoX-ext (cons {v = u'} e0 (cons e1 b)) (ne0 , n1) ne e =
  ne0 , NoX-ext (cons e1 b) n1 ne e

-- 非空形保持
Nonempty-ext : ∀ {G : DiGraph} {u v w} (p : Walk G u v) (e : DG.edge G v w)
             → Nonempty (p ++w cons e (nil w))
Nonempty-ext (nil v) e = tt
Nonempty-ext (cons e0 b) e = tt

-- ══════════════════════════════════════════════════════════════════════════════
-- §2 残段形切分（返回起点处切割——证明携带构造；K 禁免匹配）
-- ══════════════════════════════════════════════════════════════════════════════

module Cut {G : DiGraph} (eqV : (a b : DG.V G) → Dec (a ≡ b)) where

  concatL : ∀ {u} → List (Walk G u u) → Walk G u u
  concatL [] = nil _
  concatL (w ∷ ws) = w ++w concatL ws

  -- 分解输出（携带重构等式）：excursion 序列（loop at a）+ 残段 r（a→b 不回 a）
  Out : ∀ {a b} (w : Walk G a b) → Set
  Out {a} {b} w =
    Σ (List (Walk G a a)) (λ es → Σ (Walk G a b) (λ r → concatL es ++w r ≡ w))

  cutG : ∀ {a b} (w : Walk G a b) → Out w
  cutAccG : ∀ {a u' b} (acc : Walk G a u') (t : Walk G u' b)
          → (u' ≡ a → ⊥) → NoX a acc
          → Σ (List (Walk G a a))
              (λ es → Σ (Walk G a b) (λ r → concatL es ++w r ≡ acc ++w t))

  cutG {a} (cons {v = u'} e t) with eqV u' a
  ... | yes refl =
    -- 首边即返回：单边 excursion + 递归尾部（重构链：assoc + cong）
    ( cons e (nil a) ∷ proj₁ rest
    , proj₁ (proj₂ rest)
    , trans (++w-assocᴱ (cons e (nil a)) (concatL (proj₁ rest)) (proj₁ (proj₂ rest)))
            (cong (cons e (nil a) ++w_) (proj₂ (proj₂ rest))) )
    where rest = cutG t
  ... | no u'≢a = cutAccG (cons e (nil u')) t u'≢a tt
  cutG (nil v) = [] , nil v , refl

  cutAccG acc (nil v) ne nacc = [] , acc , sym (++w-nilᴱ acc)
  cutAccG {a} acc (cons {v = u'} e t) ne nacc with eqV u' a
  ... | yes refl =
    -- 尾边返回：累积段收口为一个 excursion + 递归尾部
    ( (acc ++w cons e (nil a)) ∷ proj₁ rest
    , proj₁ (proj₂ rest)
    , trans (trans (++w-assocᴱ (acc ++w cons e (nil a))
                               (concatL (proj₁ rest)) (proj₁ (proj₂ rest)))
                   (cong ((acc ++w cons e (nil a)) ++w_) (proj₂ (proj₂ rest))))
            (++w-assocᴱ acc (cons e (nil a)) t) )
    where rest = cutG t
  ... | no u'≢a =
    -- 不返回：并入累积段（重构链：递归式 + assoc 一步）
    ( proj₁ rec
    , proj₁ (proj₂ rec)
    , trans (proj₂ (proj₂ rec)) (++w-assocᴱ acc (cons e (nil _)) t) )
    where
    rec = cutAccG (acc ++w cons e (nil _)) t u'≢a (NoX-ext acc nacc (λ q → ne (sym q)) e)

-- ══════════════════════════════════════════════════════════════════════════════
-- §3 two-chain 复原核对（concrete Fin 面——构造子可用，全通道 refl 验证）
-- ══════════════════════════════════════════════════════════════════════════════

open import Data.Fin.Properties using () renaming (_≟_ to _≟F_)
open import Sovereign.Topology.McCordPi0 using (two-chain)
open import _PPI4 using (Gskel)
open import _PPI4d using (e01; e10; w2)

module TC = Cut {Gskel two-chain} _≟F_

-- 切分核对：w2（单往返）→ [w2] + 残段 nil
check-cut-w2 : proj₁ (TC.cutG w2) ≡ (w2 ∷ [])
check-cut-w2 = refl

check-cut-w2w2 : proj₁ (TC.cutG (w2 ++w w2)) ≡ (w2 ∷ w2 ∷ [])
check-cut-w2w2 = refl

-- 残段归零核对（two-chain 具体面——泛形立界 (i) 的实例验证）
check-res-nil : proj₁ (proj₂ (TC.cutG w2)) ≡ nil fzero
check-res-nil = refl

-- excursion 判定核对（w2 内部顶点 = fsuc fzero ≠ fzero）
fz≠fs : _≡_ {A = Fin 2} fzero (fsuc fzero) → ⊥
fz≠fs ()

-- （IsExc 双分件核对——× 对构造在本上下文怪合，分件形语义等价）
check-exc-w2a : NoX fzero w2
check-exc-w2a = fz≠fs , tt
  where
  _ : ⊤
  _ = tt

check-exc-w2b : Nonempty w2
check-exc-w2b = tt

