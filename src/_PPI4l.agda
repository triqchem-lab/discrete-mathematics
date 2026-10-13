{-# OPTIONS --rewriting --guardedness #-}

-- | _PPI4l
-- Gskel (ii)：分解唯一性——excursion 泵引理 + 链接件 (i') + two-chain 唯一性主件 + MonoidIso 骨架
--
-- 数学背景：excursion 分解（_PPI4j cutG / _PPI4k cutZ）把 loop 切成「无内部回返」的
--   非空段序列 + 残段。分解唯一性 = 这些段是拼接不可约的原子（泵引理），故任何两个
--   全 excursion 分解必同。本件三段：
--   ① 泵引理（拼接不可约形）：excursion 不能写成两个非空 loop 的拼接——连接点 a
--      成为内部顶点，与 NoX 冲突（noX-junction）；
--   ② 链接件 (i')：cutZ 与 cutG 的分量级一致性（互递镜像——签名先行形，_PPI4j 先例）；
--   ③ 唯一性主件：two-chain 上 w2·w2 双分解唯一性全证（exc-shape 分类 + 头消去
--      cons-inj₂ 取证钉边 + concat-nil 收尾）；一般形骨架 + MonoidIso 八字段展开。
--
-- 核心原则：
-- 1. K-free：同索引 loop 型匹配只在**具象 Fin 索引**（fzero : Fin 2）面做（#56 ③）；
--    泛形段零匹配（noX-junction 全组合）；
-- 2. 边消解走 edgeGskel-neq（调用而非匹配——无边构造子依赖）；
-- 3. 零洞零 postulate；two-chain 核对层 refl 级。
--
-- 包含：noX-junction（连接点引理）｜exc-irreducible（泵引理）
--       ｜cutZAcc-fst/cutZ-fst/cutZAcc-snd/cutZ-snd（(i') 链接件）
--       ｜cons-inj₂（头消去）｜exc-shape（excursion 形状分类）
--       ｜concat-nil ｜uniq-w2 ｜uniq-w2w2（唯一性主件）｜w2w2-not-exc
--       ｜decomp-unique（一般形骨架）｜MonoidIso 八字段展开注记

module _PPI4l where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.List using (List; []; _∷_)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.Fin.Properties using () renaming (_≟_ to _≟F_)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂; subst)
open import Sovereign.Synthesis.BarceloAHomotopy
  using (DiGraph; Walk; nil; cons; _++w_)
open import Sovereign.Synthesis.McCordPi0 using (two-chain)
open import _PPI4 using (Gskel)
open import _PPI4c using (edgeGskel-neq)
open import _PPI4d using (e01; e10; w2)
open import _PPI4j using (module Cut; NoX; Nonempty; IsExc; NoX-ext; ++w-nilᴱ)
open import _PPI4k using (module LoopRes)

private
  module DG = DiGraph

-- ══════════════════════════════════════════════════════════════════════════════
-- §1 泵引理（excursion 拼接不可约形——泛形零匹配）
-- ══════════════════════════════════════════════════════════════════════════════

-- 连接点引理：非空 p（u → a）拼接非空 q（a → a）⟹
--   连接点 a 是 p ++w q 的内部顶点 ⟹ NoX a (p ++w q) 破。
-- 证明纯组合（匹配在一般双索引面做——无同索引反射等式）。
noX-junction : ∀ {G : DiGraph} {u a b} (p : Walk G u a) (np : Nonempty p)
             → (q : Walk G a b) (nq : Nonempty q)
             → NoX a (p ++w q) → ⊥
noX-junction (nil v) () _ _ _
noX-junction (cons e (nil v)) _ (nil _) () _
noX-junction (cons e (nil v)) _ (cons e' q') _ n = proj₁ n refl
noX-junction (cons e (cons e' b)) _ q nq n =
  noX-junction (cons e' b) tt q nq (proj₂ n)

-- 泵引理（不可约形）：excursion 不可写成两个非空 loop 的拼接。
exc-irreducible : ∀ {G : DiGraph} {a} (w : Walk G a a) (nx : NoX a w)
               → (p q : Walk G a a) (np : Nonempty p) (nq : Nonempty q)
               → p ++w q ≡ w → ⊥
exc-irreducible {a = a} w nx p q np nq eq =
  noX-junction p np q nq (subst (NoX a) (sym eq) nx)

-- ══════════════════════════════════════════════════════════════════════════════
-- §2 链接件 (i')：cutZ ≡ cutG（分量级——互递镜像，签名先行形）
--   cutZ = cutG + 残段 emptiness 证据（构造携带形）；两递归同形 ⟹ 分量一致。
-- ══════════════════════════════════════════════════════════════════════════════

module Link {G : DiGraph} (eqV : (a b : DG.V G) → Dec (a ≡ b)) where
  open Cut {G = G} eqV
  open LoopRes {G = G} eqV

  cutZAcc-fst : ∀ {a u' b} (acc : Walk G a u') (t : Walk G u' b)
              → (ne : u' ≡ a → ⊥) (nacc : NoX a acc)
              → proj₁ (cutZAcc acc t ne nacc) ≡ proj₁ (cutAccG acc t ne nacc)

  cutZ-fst : ∀ {a b} (w : Walk G a b)
           → proj₁ (cutZ w) ≡ proj₁ (cutG w)

  cutZAcc-snd : ∀ {a u' b} (acc : Walk G a u') (t : Walk G u' b)
              → (ne : u' ≡ a → ⊥) (nacc : NoX a acc)
              → proj₁ (proj₂ (cutZAcc acc t ne nacc))
              ≡ proj₁ (proj₂ (cutAccG acc t ne nacc))

  cutZ-snd : ∀ {a b} (w : Walk G a b)
           → proj₁ (proj₂ (cutZ w)) ≡ proj₁ (proj₂ (cutG w))

  cutZ-fst (nil v) = refl
  cutZ-fst {a} (cons {v = u'} e t) with eqV u' a
  ... | yes refl = cong (λ k → cons e (nil a) ∷ k) (cutZ-fst t)
  ... | no p = cutZAcc-fst (cons e (nil u')) t p tt

  cutZAcc-fst acc (nil v) ne nacc = refl
  cutZAcc-fst {a} acc (cons {v = u'} e t) ne nacc with eqV u' a
  ... | yes refl = cong (λ k → (acc ++w cons e (nil a)) ∷ k) (cutZ-fst t)
  ... | no p =
    cutZAcc-fst (acc ++w cons e (nil _)) t p
      (NoX-ext acc nacc (λ q → ne (sym q)) e)

  cutZ-snd (nil v) = refl
  cutZ-snd {a} (cons {v = u'} e t) with eqV u' a
  ... | yes refl = cutZ-snd t
  ... | no p = cutZAcc-snd (cons e (nil u')) t p tt

  cutZAcc-snd acc (nil v) ne nacc = refl
  cutZAcc-snd {a} acc (cons {v = u'} e t) ne nacc with eqV u' a
  ... | yes refl = cutZ-snd t
  ... | no p =
    cutZAcc-snd (acc ++w cons e (nil _)) t p
      (NoX-ext acc nacc (λ q → ne (sym q)) e)

-- ══════════════════════════════════════════════════════════════════════════════
-- §3 头消去 + two-chain 唯一性主件（具象 Fin 面——构造子可用）
-- ══════════════════════════════════════════════════════════════════════════════

-- 头消去：泛形 cons-inj₂ 撞 K 墙（refl 匹配产 v = v 反射等式——#56）——
-- 正解 = 具象索引形（中点为字面 Fin 2 构造子时零元参，普通构造子合一）。
module U2 where
  open Cut {G = Gskel two-chain} _≟F_ using (concatL)

  W : Set
  W = Walk (Gskel two-chain) fzero fzero

  -- 全 excursion 列表
  AllExc : List W → Set
  AllExc [] = ⊤
  AllExc (e ∷ es) = IsExc fzero e × AllExc es

  -- 头消去具象件（中点 = fsuc fzero 字面——零元参合一）
  uncons : {x y : DG.edge (Gskel two-chain) fzero (fsuc fzero)}
           {p q : Walk (Gskel two-chain) (fsuc fzero) fzero}
         → cons x p ≡ cons y q → (x ≡ y) × (p ≡ q)
  uncons refl = refl , refl

  -- 尾消去具象件（中点 = fzero 字面）
  uncons₀ : {x y : DG.edge (Gskel two-chain) (fsuc fzero) fzero}
            {p q : Walk (Gskel two-chain) fzero fzero}
          → cons x p ≡ cons y q → (x ≡ y) × (p ≡ q)
  uncons₀ refl = refl , refl

  -- w2 消去：w2 ++w X ≡ w2 ++w w2 ⟹ X ≡ w2（两步头消去）
  cancel-w2 : {X Y : W} → w2 ++w X ≡ w2 ++w Y → X ≡ Y
  cancel-w2 {X} {Y} eq = proj₂ (uncons₀ (proj₂ (uncons eq)))

  -- excursion 形状分类（具象 Fin 消解：nil/单边/三段全 ⊥，唯两段形）
  exc-shape : (e : W) → IsExc fzero e
            → Σ (DG.edge (Gskel two-chain) fzero (fsuc fzero)) (λ x →
              Σ (DG.edge (Gskel two-chain) (fsuc fzero) fzero) (λ y →
                e ≡ cons x (cons y (nil fzero))))
  exc-shape (nil .fzero) (_ , ne) = ⊥-elim ne
  exc-shape (cons {v = fzero} x (nil .fzero)) (_ , _) =
    ⊥-elim (edgeGskel-neq fzero fzero x refl)
  exc-shape (cons {v = v₁} x (cons {v = fzero} y (nil .fzero))) (nx , _) with v₁
  ... | fzero = ⊥-elim (edgeGskel-neq fzero fzero x refl)
  ... | fsuc fzero = x , y , refl
  exc-shape (cons {v = v₁} x (cons {v = v₂} y (cons z b))) (nx , _) with v₁ | v₂
  ... | fzero | _ = ⊥-elim (proj₁ nx refl)
  ... | fsuc fzero | fzero = ⊥-elim (proj₁ (proj₂ nx) refl)
  ... | fsuc fzero | fsuc fzero =
    ⊥-elim (edgeGskel-neq (fsuc fzero) (fsuc fzero) y refl)

  -- concat-nil：全 excursion 列表拼接为 nil ⟹ 列表为空
  concat-nil : (es : List W) → AllExc es → concatL es ≡ nil fzero → es ≡ []
  concat-nil [] _ _ = refl
  concat-nil (e ∷ es) (exc-e , _) eq with exc-shape e exc-e
  ... | x , y , refl = ⊥-elim (no-cons≡nil eq)
    where
    no-cons≡nil : {v : Fin 2} {x : DG.edge (Gskel two-chain) fzero v}
                  {p : Walk (Gskel two-chain) v fzero}
                → cons x p ≡ nil fzero → ⊥
    no-cons≡nil ()

  -- 唯一性主件 A：concatL es ≡ w2 ⟹ es ≡ [w2]
  uniq-w2 : (es : List W) → AllExc es → concatL es ≡ w2 → es ≡ (w2 ∷ [])
  uniq-w2 [] _ ()
  uniq-w2 (e ∷ es) (exc-e , all-es) eq with exc-shape e exc-e
  ... | x , y , refl =
    cong₂ _∷_ eq-e (concat-nil es all-es (proj₂ (uncons₀ (proj₂ (uncons eq)))))
    where
    -- eq : cons x (cons y (concatL es)) ≡ cons e01 (cons e10 (nil fzero))
    eq-x : x ≡ e01
    eq-x = proj₁ (uncons eq)
    eq-y : y ≡ e10
    eq-y = proj₁ (uncons₀ (proj₂ (uncons eq)))
    eq-e : cons x (cons y (nil fzero)) ≡ w2
    eq-e = trans (cong (λ k → cons k (cons y (nil fzero))) eq-x)
                 (cong (λ k → cons e01 (cons k (nil fzero))) eq-y)

  -- 唯一性主件 B：concatL es ≡ w2 ++w w2 ⟹ es ≡ [w2 , w2]（双分解唯一性）
  uniq-w2w2 : (es : List W) → AllExc es → concatL es ≡ w2 ++w w2
            → es ≡ (w2 ∷ w2 ∷ [])
  uniq-w2w2 [] _ ()
  uniq-w2w2 (e ∷ es) (exc-e , all-es) eq with exc-shape e exc-e
  ... | x , y , refl =
    cong₂ _∷_ eq-e (uniq-w2 es all-es rest2)
    where
    -- eq : cons x (cons y (concatL es)) ≡ cons e01 (cons e10 w2)
    eq-x : x ≡ e01
    eq-x = proj₁ (uncons eq)
    eq-y : y ≡ e10
    eq-y = proj₁ (uncons₀ (proj₂ (uncons eq)))
    rest2 : concatL es ≡ w2
    rest2 = proj₂ (uncons₀ (proj₂ (uncons eq)))
    eq-e : cons x (cons y (nil fzero)) ≡ w2
    eq-e = trans (cong (λ k → cons k (cons y (nil fzero))) eq-x)
                 (cong (λ k → cons e01 (cons k (nil fzero))) eq-y)

  -- 反向事实：w2w2 本身不是 excursion（内部回返 fzero）——唯一性的另一半语境
  w2w2-not-exc : IsExc fzero (w2 ++w w2) → ⊥
  w2w2-not-exc (nx , _) = proj₁ (proj₂ nx) refl

-- ══════════════════════════════════════════════════════════════════════════════
-- §4 一般形唯一性骨架 + MonoidIso 八字段展开（立界注记）
-- ══════════════════════════════════════════════════════════════════════════════
--
-- decomp-unique（一般 G，骨架陈述——立界）：
--   ∀ (es es' : List (Loop G a)) → AllExc es → AllExc es'
--   → concatL es ≡ concatL es' → es ≡ es'
-- 步骤分解（two-chain 实例已按此走通——一般形卡点在头消去后的「首回返位」引理）：
--   (1) 泵引理（§1）⟹ 每个 excursion 是原子；
--   (2) 首回返唯一 ⟹ 首项一致（two-chain 上由 uncons 钉边直接取得——
--       一般形需「首回返位由 walk 本身决定」引理，估 30-50 行；卡 K-索引面
--       时走 _PPI4k 的残段化三路线）；
--   (3) 归纳收尾（concat-nil 同款）。
--
-- MonoidIso 八字段展开（目标：π₁ᵈ(Gskel G) ≅ F(E_x)——excursion 自由幺半群）：
--   ① to       : loop ↦ cutZ 的 excursion 序列（List E_x）——(i') 链接后语义确定；
--   ② from     : 序列 ↦ concatL——_PPI4j concatL；
--   ③ to-·     : to (p ⊞ q) ≡ to p ++ to q——分解对拼接的可加性（泵引理+唯一性 ⟹）；
--   ④ from-·   : concatL (es ++ es') ≡ concatL es ++w concatL es'——_PPI4k concatL-++ ✓ 已证；
--   ⑤ to∘from  : concatL es ↦ es——唯一性主件（本件 §3 two-chain 形已证）；
--   ⑥ from∘to  : w ↦ concatL (cutZ w) ≡ w——重构等式（cutZ 携带件 ✓）；
--   ⑦ 保单位   : to [nil] ≡ [] ｜from [] ≡ [nil]——defeq 级；
--   ⑧ 保逆（无）: F(E_x) 自由幺半群无逆——与分水岭一致（Gskel 侧 (ℕ,+) 无挠面）。
--   状态：②④⑥⑦ 已在库（既有件）；①⑤ 一般形待 (2) 首回返引理；③ 待 ⑤。
--
-- 诚实边界：
--   · two-chain 面唯一性 = 本件已证（uniq-w2w2 全形）；
--   · 一般形 = 骨架 + 泵引理已证 + 首回返引理立界（~30-50 行）；
--   · MonoidIso 八字段中 ④⑥⑦ 为既有件引用，①③⑤⑧ 依赖一般形唯一性。

-- ══════════════════════════════════════════════════════════════════════════════
-- §5 核对层（two-chain 具象面——refl 级）
-- ══════════════════════════════════════════════════════════════════════════════

open import _PPI4j using (check-exc-w2a; check-exc-w2b)

open Cut {G = Gskel two-chain} _≟F_ using (concatL)

module TCZ = LoopRes {Gskel two-chain} _≟F_

-- 链接件核对：cutZ/cutG 在 w2·w2 上同输出
check-link-w2w2 : proj₁ (TCZ.cutZ (w2 ++w w2)) ≡ (w2 ∷ w2 ∷ [])
check-link-w2w2 = refl

-- 唯一性主件实例调用核对（类型级对账——真证明在 §3）
check-uniq-w2w2-type : (es : List U2.W) → U2.AllExc es
                     → concatL es ≡ w2 ++w w2
                     → es ≡ (w2 ∷ w2 ∷ [])
check-uniq-w2w2-type = U2.uniq-w2w2

-- 泵引理实例：w2 不可拆（无非空 loop 对拼接成 w2）
check-pump-w2 : (p q : U2.W) → Nonempty p → Nonempty q
              → p ++w q ≡ w2 → ⊥
check-pump-w2 = exc-irreducible w2 check-exc-w2a

-- w2w2 非 excursion 核对
check-w2w2-not-exc : IsExc fzero (w2 ++w w2) → ⊥
check-w2w2-not-exc = U2.w2w2-not-exc
