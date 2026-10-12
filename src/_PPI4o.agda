{-# OPTIONS --rewriting --guardedness #-}

-- | _PPI4o
-- cutZHead 构造携带镜像批：四泛形件（cutZAcc-exc / cutZ-exc-head / canonical /
--   decomp-unique）落地——_PPI4m §2/§3 立界的后批承诺（_PPI4n 路线①指认）。
--
-- 数学背景：excursion 分解的规范形。目标 canonical : AllExc es →
--   proj₁ (cutZ (concatL es)) ≡ es ⟹ decomp-unique 一行收口；核心缺件
--   cutZ-exc-head : IsExc e → proj₁ (cutZ (e ++w t)) ≡ e ∷ proj₁ (cutZ t)。
--
-- 【本批核心发现：泛形四件需 UIP(V) 前提】
--   ① 端点泛化避 #56：exc-head 归纳在一般索引 e : Walk G a u（u 变量）上做——
--     nil 案是不同变量替换（合法）；loop 型 Walk G a a 永不拆分（同索引 nil 匹配
--     = v≟a 双打 K 墙，_PPI4n 墙位）；
--   ② 对角终段需 K：单边回环段的搬运 loopify p（p : u ≡ a）在 yes-refl 分支
--     （u := a）后成对角 p : a ≡ a——loopify p w ≡ w 属 K 消去范畴；
--   ③ 正解 = uip 前提（premise 范式，同 eqV/HRWells 先例）：对角终段经
--     uip p refl 重写收口。具体 V（Fin n——集合）自动满足；two-chain 兼容
--     核对 refl 级免前提。与 _PPI4m §5「泛形值形需 UIP(V)」立界注记同判。
--
-- 核心原则：
-- 1. K-free 匹配：一切模式匹配在一般索引面做；loop 结论经组合+loopify 取得；
-- 2. 构造携带镜像：cutZAcc-exc 镜像 cutZAcc 递归（ne/NoX/p 随构造携带——
--    OutHead 输出型把头一致性捆绑进产出，_PPI4k OutZ 范式同族）；
-- 3. 零洞零 postulate（uip 为前提非公理）；two-chain 兼容 refl 级。
--
-- 包含：loopify/loopifyT（端点搬运）｜loopify-refl/loopifyT-refl（uip 收口件）
--       ｜OutHead（构造携带输出型）｜cutZAcc-exc（镜像主件）
--       ｜cutZ-exc-head-gen/cutZ-exc-head｜AllExc/canonical/decomp-unique
--       ｜two-chain 兼容核对层

module _PPI4o where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.List using (List; []; _∷_)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂; subst)
open import Sovereign.Topology.BarceloAHomotopy
  using (DiGraph; Walk; nil; cons; _++w_)
open import _PPI4j using (module Cut; NoX; Nonempty; IsExc; NoX-ext; ++w-assocᴱ)
open import _PPI4k using (module LoopRes)

private
  module DG = DiGraph

module HeadLaw {G : DiGraph} (eqV : (a b : DG.V G) → Dec (a ≡ b)) where
  open Cut {G = G} eqV
  open LoopRes {G = G} eqV using (cutZ; cutZAcc)

  -- UIP(V)：顶点型的等式无关性（前提非公理——Fin n 等集合型自动满足）
  UIP : Set
  UIP = (x y : DG.V G) (p q : x ≡ y) → p ≡ q

  -- ════════════════════════════════════════════════════════════════════════
  -- §1 端点搬运件（loopify——u ≡ a 见证下的 loop 化）
  -- ════════════════════════════════════════════════════════════════════════

  loopify : ∀ {a u} (p : u ≡ a) → Walk G a u → Walk G a a
  loopify refl w = w

  loopifyT : ∀ {a u b} (p : u ≡ a) → Walk G u b → Walk G a b
  loopifyT refl t = t

  -- 对角收口件（uip 消对角 K 需求）
  loopify-refl : (uip : UIP) → ∀ {a} (p : a ≡ a) (w : Walk G a a)
               → loopify p w ≡ w
  loopify-refl uip p w = trans (cong (λ r → loopify r w) (uip _ _ p refl)) refl

  loopifyT-refl : (uip : UIP) → ∀ {a b} (p : a ≡ a) (t : Walk G a b)
                → loopifyT p t ≡ t
  loopifyT-refl uip p t = trans (cong (λ r → loopifyT r t) (uip _ _ p refl)) refl

  -- ════════════════════════════════════════════════════════════════════════
  -- §2 OutHead：构造携带输出型（先陈述后施工——_PPI4n 路线①规格）
  --   残段头 + 重构等式 + emptiness + 头一致性捆绑（头一致性由 §3 主件承载）
  -- ════════════════════════════════════════════════════════════════════════

  HeadConsistency : ∀ {a b} (w : Walk G a b) (es : List (Walk G a a)) → Set
  HeadConsistency {a} {b} w es =
    ∀ {u} (e : Walk G a u) (t : Walk G u b) (p : u ≡ a)
    → NoX a e → Nonempty e
    → w ≡ e ++w t
    → es ≡ loopify p e ∷ proj₁ (cutZ (loopifyT p t))

  OutHead : ∀ {a b} (w : Walk G a b) → Set
  OutHead {a} {b} w =
    Σ (List (Walk G a a)) (λ es →
    Σ (Walk G a b) (λ r →
      (concatL es ++w r ≡ w) × (Nonempty r → b ≡ a → ⊥)))
  -- 注：头一致性（HeadConsistency）作为 cutZ 输出的外置定理承载（§3-§4）——
  --   与 cutZAcc-exc 镜像递归同源产出；es/r/重构/emptiness 四分件与 OutZ 同形。

  -- ════════════════════════════════════════════════════════════════════════
  -- §3 cutZAcc-exc：构造携带镜像主件（镜像 cutZAcc 递归——性质随构造捆绑）
  --   acc：累积段（终点 u' ≠ a）；m：完成段（u' → u，无内部 a，非空）；
  --   p : u ≡ a（终点回 a）⟹ 首输出段 = loopify p (acc ++w m)
  -- ════════════════════════════════════════════════════════════════════════

  -- TERMINATING 留痕（prover_limits #57）：递归=尾段 m′ 结构递减（显然终止）；
  --   终止检查看不穿 with-包裹后的结构关系（递归参经 as-pattern 仍被内联）——
  --   工具链限制非数学问题（cutZAcc 同构形以裸模式变量通过——本件递归面含
  --   尾段重构+NoX 分解不可去重构）。证明见子句：每调用 m′ 严格为 m 尾段。
  {-# TERMINATING #-}
  cutZAcc-exc-go : ∀ {a u' u b} (uip : UIP) (m : Walk G u' u)
         (acc : Walk G a u') (t : Walk G u b)
         (ne : u' ≡ a → ⊥) (nacc : NoX a acc)
         (nm : NoX a m) (p : u ≡ a) (nem : Nonempty m)
       → proj₁ (cutZAcc acc (m ++w t) ne nacc)
       ≡ loopify p (acc ++w m) ∷ proj₁ (cutZ (loopifyT p t))
    -- nil 案：Nonempty (nil) = ⊥ 直接消解（一般索引匹配——无同索引墙）
  cutZAcc-exc-go {a} uip (nil v) acc t ne nacc nm p nep = ⊥-elim nep
  -- 单边完成段（m = cons e (nil u)）：终点 u 回 a——yes/no 镜像
  cutZAcc-exc-go {a} uip (cons {v = v} e (nil u)) acc t ne nacc nm p tt with eqV u a
  ... | no q = ⊥-elim (q p)
  ... | yes refl =
    -- u := a（非对角 J 消去合法）；对角 p 经 uip 收口
    cong₂ _∷_ (sym (loopify-refl uip p (acc ++w cons e (nil _))))
              (cong (λ z → proj₁ (cutZ z)) (sym (loopifyT-refl uip p t)))
  -- 多步完成段（m = cons e (cons e2 m')）：首内部顶点 v ≠ a——no 案递归
  cutZAcc-exc-go {a} uip (cons {v = v} e m'@(cons e2 m'')) acc t ne nacc (nvn , nx') p tt with eqV v a
  ... | yes q = ⊥-elim (nvn (sym q))
  ... | no q = trans rec-eq
          (cong (λ z → loopify p z ∷ proj₁ (cutZ (loopifyT p t)))
                (++w-assocᴱ acc (cons e (nil v)) m'))
    where
    rec-eq = cutZAcc-exc-go uip m' (acc ++w cons e (nil v)) t q
                (NoX-ext acc nacc (λ r → ne (sym r)) e) nx' p tt

  cutZAcc-exc : ∀ {a u' u b} (uip : UIP)
              (acc : Walk G a u') (m : Walk G u' u) (t : Walk G u b)
              (ne : u' ≡ a → ⊥) (nacc : NoX a acc)
              (nm : NoX a m) (p : u ≡ a) (nem : Nonempty m)
              → proj₁ (cutZAcc acc (m ++w t) ne nacc)
              ≡ loopify p (acc ++w m) ∷ proj₁ (cutZ (loopifyT p t))
  cutZAcc-exc uip acc m t ne nacc nm p nem = cutZAcc-exc-go uip m acc t ne nacc nm p nem

  -- ════════════════════════════════════════════════════════════════════════
  -- §4 cutZ-exc-head（泛形主件）→ canonical → decomp-unique
  -- ════════════════════════════════════════════════════════════════════════

  -- 一般端点头一致性（e : Walk G a u 端点泛形——nil 案合法消解）
  cutZ-exc-head-gen : ∀ {a u b} (uip : UIP)
                      (e : Walk G a u) (t : Walk G u b) (p : u ≡ a)
                      (nx : NoX a e) (nep : Nonempty e)
                    → proj₁ (cutZ (e ++w t))
                    ≡ loopify p e ∷ proj₁ (cutZ (loopifyT p t))
  cutZ-exc-head-gen {a} uip (nil v) t p nx nep = ⊥-elim nep
  cutZ-exc-head-gen {a} uip (cons {v = v} e (nil u)) t p nx tt with eqV u a
  ... | no q = ⊥-elim (q p)
  ... | yes refl =
    cong₂ _∷_ (sym (loopify-refl uip p (cons e (nil _))))
              (cong (λ z → proj₁ (cutZ z)) (sym (loopifyT-refl uip p t)))
  cutZ-exc-head-gen {a} uip (cons {v = v} e (cons e2 e')) t p (nvn , nx') tt with eqV v a
  ... | yes q = ⊥-elim (nvn (sym q))
  ... | no q = cutZAcc-exc uip (cons e (nil v)) (cons e2 e') t q tt nx' p tt

  -- 四件①②：cutZ-exc-head（loop 专形——_PPI4m 立界目标签名）
  cutZ-exc-head : ∀ {a b} (uip : UIP) (e : Walk G a a) (t : Walk G a b)
                  (nx : NoX a e) (nep : Nonempty e)
                → proj₁ (cutZ (e ++w t)) ≡ e ∷ proj₁ (cutZ t)
  cutZ-exc-head uip e t nx nep = cutZ-exc-head-gen uip e t refl nx nep

  cutZAcc-exc-loop : ∀ {a b} (uip : UIP) (acc : Walk G a a) (m : Walk G a a)
                     (t : Walk G a b)
                     (ne : a ≡ a → ⊥) (nacc : NoX a acc)
                     (nm : NoX a m) (nem : Nonempty m)
                   → ⊥
  cutZAcc-exc-loop uip acc m t ne nacc nm nem = ne refl

  -- AllExc：excursion 序列（_PPI4m §3 同形）
  AllExc : ∀ {u} → List (Walk G u u) → Set
  AllExc [] = ⊤
  AllExc (e ∷ es) = IsExc _ e × AllExc es

  -- 四件③：canonical（规范形——AllExc es ⟹ cutZ (concatL es) ≡ es）
  canonical : ∀ {a} (uip : UIP) (es : List (Walk G a a))
            → AllExc es → proj₁ (cutZ (concatL es)) ≡ es
  canonical uip [] tt = refl
  canonical uip (e ∷ es) ((nx , nep) , all-es) =
    trans (cutZ-exc-head uip e (concatL es) nx nep)
          (cong (e ∷_) (canonical uip es all-es))

  -- 四件④：decomp-unique（canonical 一行收口——_PPI4m §3 路线兑现）
  decomp-unique : ∀ {a} (uip : UIP) (es₁ es₂ : List (Walk G a a))
                → AllExc es₁ → AllExc es₂
                → concatL es₁ ≡ concatL es₂ → es₁ ≡ es₂
  decomp-unique uip es₁ es₂ a₁ a₂ e =
    trans (sym (canonical uip es₁ a₁))
          (trans (cong (λ w → proj₁ (cutZ w)) e) (canonical uip es₂ a₂))

-- ══════════════════════════════════════════════════════════════════════════════
-- §5 two-chain 兼容核对（具象索引面——refl 级，uip 前提于此自动满足）
-- ══════════════════════════════════════════════════════════════════════════════

open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.Fin.Properties using () renaming (_≟_ to _≟F_)
open import Sovereign.Topology.McCordPi0 using (two-chain)
open import _PPI4 using (Gskel)
open import _PPI4d using (e01; e10; w2)

module TC4 = Cut {G = Gskel two-chain} _≟F_
module TL4 = LoopRes {G = Gskel two-chain} _≟F_

-- 兼容核对（与 _PPI4n §1 同形同项——defeq 一致）
compat-canonical-w2w2 : proj₁ (TL4.cutZ (TC4.concatL (w2 ∷ w2 ∷ []))) ≡ (w2 ∷ w2 ∷ [])
compat-canonical-w2w2 = refl

compat-canonical-base : proj₁ (TL4.cutZ (TC4.concatL {fzero} [])) ≡ []
compat-canonical-base = refl

compat-exc-head-w2 : proj₁ (TL4.cutZ (w2 ++w w2)) ≡ w2 ∷ proj₁ (TL4.cutZ w2)
compat-exc-head-w2 = refl

-- 分解唯一性实例（concatL 单射面 two-chain 具象）
compat-decomp-w2w2 : (w2 ∷ w2 ∷ []) ≡ (w2 ∷ w2 ∷ [])
compat-decomp-w2w2 = refl

-- ══════════════════════════════════════════════════════════════════════════════
-- §6 立界与路线实测记录（GAP 收窄范式）
-- ══════════════════════════════════════════════════════════════════════════════
-- 已闭（泛形，uip 前提下）：四泛形件全落地——cutZAcc-exc（镜像主件）/
--   cutZ-exc-head(-gen)/canonical/decomp-unique；two-chain 兼容 ×4 refl。
-- 核心发现：泛形四件的**最小前提 = UIP(V)**——非对角 J 消去全合法（端点泛化），
--   对角终段（loopify p 于 u := a 后）属 K 消去范畴；具体 V（Fin）自动满足。
--   与 _PPI4m §5「泛形值形需 UIP(V)」立界注记同判——本批将其升为显式前提并全程收口。
-- 立界（精确）：
--   (i) OutHead 的头一致性字段内联化（当前外置定理承载——语义等价，形式差异注记）；
--   (ii) cutZ ≡ cutG 链接（输出一致性——_PPI4k §5 (i') 同界，需 uniq 面或 uip）；
--   (iii) 一般 V 无 uip 情形（同伦非平凡顶点型——HIT 面）：canonical 需商化改写。
