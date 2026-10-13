{-# OPTIONS --rewriting --guardedness #-}

-- | _PPI4k
-- Gskel (i)：loop 级残段归零（泛形 emptiness/len-0 主件 + 具象值形）+ 分解唯一性骨架 + MonoidIso 立界
--
-- 数学背景：_PPI4j 残段形切分 cutG 在返回起点处切割为 excursion 序列 + 残段；
--   loop 级残段归零 = 闭走的残段必空。K-索引墙实证（本件探针复现）：
--   loop 型 Walk G x x 上匹配 nil ⟺ unifier 产出 v≟x 双打 ⟹ x = x 反射等式
--   需 K 消去（K 禁用下不可行）。**正解 = 零 K 组合**：
--   ① emptiness 主件（一般索引 u v 上匹配——nil 情形是不同变量替换，无反射等式）；
--   ② len-0 形由 ① + len-zero-from-empty 组合导出（**完全不匹配 w**——loop 结论
--      经组合而非模式匹配取得）；
--   ③ 值形 r ≡ nil 保留具象索引面（two-chain 等字面索引可 refl；泛形值形需
--      UIP(V) 或燃料重建+唯一性——立界，如实标注适用域）。
-- 核心原则：
-- 1. K-free：loop 型 nil 匹配禁用；一切匹配在一般索引面做；
-- 2. 互归纳镜像 cutG/cutAccG with 分叉；证明携带构造沿用；
-- 3. 零洞零 postulate；two-chain 复原核对。
--
-- 包含：len（本地测度）｜res/resa（残段投影）｜res-empty-G/res-empty-Acc（泛形主件）
--       ｜len-zero-from-empty ｜res-len0-G（loop 级残段长度归零——泛形归零主件）
--       ｜concatL-++（分解同态骨架）｜two-chain 核对层

module _PPI4k where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.List using (List; []; _∷_; _++_)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂; subst)
open import Sovereign.Synthesis.BarceloAHomotopy
  using (DiGraph; Walk; nil; cons; _++w_)
open import _PPI4j using (module Cut; NoX; Nonempty; NoX-ext; ++w-assocᴱ; ++w-nilᴱ)

private
  module DG = DiGraph

module LoopRes {G : DiGraph} (eqV : (a b : DG.V G) → Dec (a ≡ b)) where
  open Cut {G = G} eqV

  -- 本地长度测度（K-free 归零形承载）
  len : ∀ {u v} → Walk G u v → ℕ
  len (nil v) = zero
  len (cons e b) = suc (len b)


  -- 残段投影
  res : ∀ {a b} (w : Walk G a b) → Walk G a b
  res w = proj₁ (proj₂ (cutG w))

  -- ════════════════════════════════════════════════════════════════════════
  -- §1 构造携带形（cutZ——性质随构造捆绑；类型面零 stuck 应用，K-free）
  --   泛形主件：残段 emptiness（Nonempty r → b ≡ a → ⊥）随切分递归一并产出；
  --   loop 推论：残段空 ⟹ len-0——「残段归零」泛形内容（值形≡nil 见 §4 立界）。
  --   与 cutG 输出的一致性 = 分解唯一性（②）——立界（含 two-chain 实例 refl 实证）。
  -- ════════════════════════════════════════════════════════════════════════

  OutZ : ∀ {a b} (w : Walk G a b) → Set
  OutZ {a} {b} w =
    Σ (List (Walk G a a)) (λ es →
    Σ (Walk G a b) (λ r →
      (concatL es ++w r ≡ w) × (Nonempty r → b ≡ a → ⊥)))

  cutZ : ∀ {a b} (w : Walk G a b) → OutZ w
  cutZAcc : ∀ {a u' b} (acc : Walk G a u') (t : Walk G u' b)
          → (ne : u' ≡ a → ⊥) (nacc : NoX a acc)
          → Σ (List (Walk G a a)) (λ es →
            Σ (Walk G a b) (λ r →
              (concatL es ++w r ≡ acc ++w t) × (Nonempty r → b ≡ a → ⊥)))

  cutZ (nil v) = [] , nil v , refl , (λ ())
  cutZ {a} (cons {v = u'} e t) with eqV u' a
  ... | yes refl =
    ( cons e (nil a) ∷ proj₁ rest
    , proj₁ (proj₂ rest)
    , trans (++w-assocᴱ (cons e (nil a)) (concatL (proj₁ rest)) (proj₁ (proj₂ rest)))
            (cong (cons e (nil a) ++w_) (proj₁ (proj₂ (proj₂ rest))))
    , proj₂ (proj₂ (proj₂ rest)) )
    where rest = cutZ t
  ... | no p = cutZAcc (cons e (nil u')) t p tt

  cutZAcc acc (nil v) ne nacc =
    [] , acc , sym (++w-nilᴱ acc) , (λ _ q → ne q)
  cutZAcc {a} acc (cons {v = u'} e t) ne nacc with eqV u' a
  ... | yes refl =
    ( (acc ++w cons e (nil a)) ∷ proj₁ rest
    , proj₁ (proj₂ rest)
    , trans (trans (++w-assocᴱ (acc ++w cons e (nil a))
                               (concatL (proj₁ rest)) (proj₁ (proj₂ rest)))
                   (cong ((acc ++w cons e (nil a)) ++w_) (proj₁ (proj₂ (proj₂ rest)))))
            (++w-assocᴱ acc (cons e (nil a)) t)
    , proj₂ (proj₂ (proj₂ rest)) )
    where rest = cutZ t
  ... | no p =
    ( proj₁ rec
    , proj₁ (proj₂ rec)
    , trans (proj₁ (proj₂ (proj₂ rec))) (++w-assocᴱ acc (cons e (nil _)) t)
    , proj₂ (proj₂ (proj₂ rec)) )
    where
    rec = cutZAcc (acc ++w cons e (nil _)) t p
            (NoX-ext acc nacc (λ q → ne (sym q)) e)

  -- 泛形主件（corollary 形）
  resZ : ∀ {a b} (w : Walk G a b) → Walk G a b
  resZ w = proj₁ (proj₂ (cutZ w))

  resZ-empty : ∀ {a b} (w : Walk G a b)
             → Nonempty (resZ w) → b ≡ a → ⊥
  resZ-empty w = proj₂ (proj₂ (proj₂ (cutZ w)))

  -- ════════════════════════════════════════════════════════════════════════
  -- §2 len-0 形（泛形归零主件——组合导出，零 loop 匹配）
  -- ════════════════════════════════════════════════════════════════════════

  len-zero-from-empty : ∀ {u v} (r : Walk G u v)
                      → (Nonempty r → ⊥) → len r ≡ zero
  len-zero-from-empty (nil v) _ = refl
  len-zero-from-empty (cons e b) ne = ⊥-elim (ne tt)

  -- loop 级残段长度归零（泛形！——组合而非模式匹配取得 loop 结论）
  resZ-len0 : ∀ {x} (w : Walk G x x) → len (resZ w) ≡ zero
  resZ-len0 w = len-zero-from-empty (resZ w) (λ ne → resZ-empty w ne refl)

  -- ════════════════════════════════════════════════════════════════════════
  -- §3 分解同态骨架（唯一性前置——②的 len 面）
  -- ════════════════════════════════════════════════════════════════════════

  concatL-++ : ∀ {a} (es₁ es₂ : List (Walk G a a))
             → concatL (es₁ ++ es₂) ≡ concatL es₁ ++w concatL es₂
  concatL-++ [] es₂ = refl
  concatL-++ (e ∷ es₁) es₂ =
    trans (cong (e ++w_) (concatL-++ es₁ es₂))
          (sym (++w-assocᴱ e (concatL es₁) (concatL es₂)))

  len-++w : ∀ {u v w'} (p : Walk G u v) (q : Walk G v w')
          → len (p ++w q) ≡ len p + len q
  len-++w (nil v) q = refl
  len-++w (cons e p) q = cong suc (len-++w p q)

-- ══════════════════════════════════════════════════════════════════════════════
-- §4 two-chain 复原核对（具象索引面——值形 r ≡ nil 于此 refl 级成立）
-- ══════════════════════════════════════════════════════════════════════════════

open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.Fin.Properties using () renaming (_≟_ to _≟F_)
open import Sovereign.Synthesis.McCordPi0 using (two-chain)
open import _PPI4 using (Gskel)
open import _PPI4d using (e01; e10; w2)

module TCZ = LoopRes {Gskel two-chain} _≟F_

-- cutZ 与 cutG 输出一致性（two-chain 实例 refl 实证）
check-cutZ-w2 : proj₁ (TCZ.cutZ w2) ≡ (w2 ∷ [])
check-cutZ-w2 = refl

check-cutZ-eqG-w2 : proj₁ (proj₂ (TCZ.cutZ w2)) ≡ TCZ.res w2
check-cutZ-eqG-w2 = refl

-- 具象值形残段归零（立界 (i) 的 two-chain 面——泛形值形见 §5）
check-resZ-nil-w2 : TCZ.resZ w2 ≡ nil fzero
check-resZ-nil-w2 = refl

check-resZ-nil-w2w2 : TCZ.resZ (w2 ++w w2) ≡ nil fzero
check-resZ-nil-w2w2 = refl

check-resZ-len0-w2 : TCZ.len (TCZ.resZ w2) ≡ zero
check-resZ-len0-w2 = refl

-- ══════════════════════════════════════════════════════════════════════════════
-- §5 立界与路线对比表（(i) 收窄定性——GAP 范式）
-- ══════════════════════════════════════════════════════════════════════════════
-- 已闭（泛形）：cutZ 残段 emptiness（Nonempty r → b ≡ a → ⊥）+ loop 级 len-0
--   （resZ-len0——组合导出，零 loop 匹配，K-free）；two-chain 具象值形 refl ×3。
-- 立界（精确）：
--   (i') cutG 残段 ≡ nil 的泛形值形——需 cutG ≡ cutZ 链接（= ②分解唯一性）或
--        UIP(V)（索引型 V 的 K）；三路线对比：
--        ① JMeq：异质等式桥——重且未证必要；③ cubical-J：J 消去 refl 形同样
--        受阻于 loop 型 nil 匹配的 v≟x 双打（J 不消 unifier 的 K 需求）；
--        ② 构造携带形（本件采用）：性质随 cutZ 捆绑产出——泛形全闭；
--        链接 cutG=cutZ 留 ② 唯一性（推荐路线——兼得 ②）。
--   (ii) ② 分解唯一性全形：(es,r) 规范形唯一——需 excursion 互不穿透（泵引理形）
--        + concatL-++ 同态（已证）+ len 面（已证 len-++w）；估 1-2 批。
--   (iii) ③ MonoidIso 八字段（F(Eₓ) 自由幺半群）依赖 (i')(ii)——骨架留档：
--        to = proj₁ ∘ cutZ（loop ⟼ excursion 列表）｜from = concatL｜
--        往返 = ②唯一性 + concatL-++｜⊕= _++_（列表）——依赖 (ii) 后可全闭。
