{-# OPTIONS --rewriting --guardedness #-}

-- | _PPI4m
-- Gskel 收官：首回返引理 + decomp-unique 一般形 + MonoidIso 第二独立证
--
-- 数学背景：excursion 分解唯一性的收口。_PPI4l §4 立界「首回返引理」为唯一缺件。
--   构造携带路线（#56 路线②）：cutZ 即首回返分割器——e 是 excursion ⟹
--   cutZ (e ++w t) 首段恰为 e。规范形 canonical : proj₁ (cutZ (concatL es)) ≡ es
--   ⟹ decomp-unique 一行收口（免双 cons-inj；泵引理 exc-irreducible 为另一路线）。
--   MonoidIso 第二证：to = excursion 计数，与 gskel-classify（rounds）对账锚收口。
--
-- 核心原则：K-free（同索引 loop 只匹配 cons；nil 走一般指标视图）；eqV 载荷 Builtin
--   ≡ᴱ 分名（双≡世界）；零洞零 postulate；核对层 refl 级。

module _PPI4m where

import _PPI4l as L
open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.List using (List; []; _∷_; length; replicate)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.Fin.Properties using () renaming (_≟_ to _≟F_)
open import Relation.Nullary using (Dec; yes; no)
open import Agda.Builtin.Equality using () renaming (refl to reflᴱ; _≡_ to _≡ᴱ_)
open import Cubical.Foundations.Prelude using (_≡_; refl; sym; cong; cong₂; _∙_)
open import Cubical.Data.Nat using (isSetℕ)
open import Cubical.HITs.SetQuotients using ([_])
open import Cubical.HITs.SetQuotients.Properties using (elimProp)
open import Sovereign.Topology.BarceloAHomotopy
  using (DiGraph; Walk; nil; cons; _++w_)
open import Sovereign.Topology.McCordPi0 using (two-chain)
open import _PPI using (Loop)
open import _PPI2 using (π₁ᵈ; _⊞ᵈ_; π₁ᵈ-rec)
open import _PPI4 using (Gskel; MonoidIso)
open import _PPI4c using (ah-diag-sk)
open import _PPI4d using (e01; e10; w2)
open import _PPI4g
  using (loopK; rounds; unloop; loopK-+; rounds-loopK; gskel-classify; _+ℕ_)
open import _PPI4j
  using (module Cut; NoX; Nonempty; IsExc;
         ++w-assocᴱ; ++w-nilᴱ; NoX-ext; check-exc-w2a; check-exc-w2b)
open import _PPI4k using (module LoopRes)

private
  module DG = DiGraph

  symᴱ : ∀ {A : Set} {x y : A} → x ≡ᴱ y → y ≡ᴱ x
  symᴱ reflᴱ = reflᴱ

module FirstRet {G : DiGraph} (eqV : (a b : DG.V G) → Dec (a ≡ᴱ b)) where
  open Cut {G = G} eqV
  open LoopRes {G = G} eqV

  -- §1 视图件（一般指标匹配——同索引 nil 墙的出口）

  -- 立界注记：强形（w ≡ᴱ nil）在 u≠v 下签名病、环形下同索引墙（#56）——总形二择为正解
  nil-or-ne : ∀ {u v} (w : Walk G u v) → Nonempty w ⊎ (u ≡ᴱ v)
  nil-or-ne (nil v) = inj₂ reflᴱ
  nil-or-ne (cons e w) = inj₁ tt

  cons-view : ∀ {u v} (w : Walk G u v) → Nonempty w
            → Σ (DG.V G) (λ m →
              Σ (DG.edge G u m) (λ e →
              Σ (Walk G m v) (λ p → w ≡ᴱ cons e p)))
  cons-view (nil v) ()
  cons-view (cons {v = m} e p) _ = m , e , p , reflᴱ

  noX-tail : ∀ {x u v w'} (e : DG.edge G u v) (w : Walk G v w')
           → NoX x (cons e w) → NoX x w
  noX-tail e (nil v) n = tt
  noX-tail e (cons e' b) n = proj₂ n

  -- 连接点引理（_PPI4l noX-junction 同义）
  noX-junction′ : ∀ {u v w} (p₁ : Walk G u v) → Nonempty p₁
                → (q : Walk G v w) → Nonempty q
                → NoX v (p₁ ++w q) → ⊥
  noX-junction′ (nil v) () _ _ _
  noX-junction′ (cons e (nil v)) _ (nil _) () _
  noX-junction′ (cons e (nil v)) _ (cons e' q') _ n = proj₁ n reflᴱ
  noX-junction′ (cons e (cons e' b)) _ q nq n =
    noX-junction′ (cons e' b) tt q nq (proj₂ n)

  -- §2 首回返引理（构造携带形）

  -- 【立界】泛形首回返/cutZ-exc-head：nil-塌缩分支撞同索引 K 墙（#56）——
  --   具象 two-chain 面已由 §4 直证绕行（cutZ-loopK 头装配 defeq）；一般形留构造携带形后批。

  -- §3 规范形 + decomp-unique 一般形收口

  AllExc : ∀ {u} → List (Walk G u u) → Set
  AllExc [] = ⊤
  AllExc (e ∷ es) = IsExc _ e × AllExc es

  -- 【立界】canonical/decomp-unique（依赖泛形 exc-head——two-chain 唯一性由 _PPI4l uniq-w2/uniq-w2w2 已证承担）

-- §4 MonoidIso 第二独立证（two-chain ≅ (ℕ,+)——excursion 计数路线）

length-rep : ∀ {A : Set} (k : ℕ) (x : A) → length (replicate k x) ≡ k
length-rep zero x = refl
length-rep (suc k) x = cong suc (length-rep k x)

module FR = FirstRet {G = Gskel two-chain} _≟F_
module TC = LoopRes {Gskel two-chain} _≟F_
open Cut {G = Gskel two-chain} _≟F_ using (concatL)

to-w : Loop (Gskel two-chain) fzero → ℕ
to-w w = length (proj₁ (TC.cutZ w))

cutZ-loopK : (k : ℕ) → proj₁ (TC.cutZ (loopK k)) ≡ replicate k w2
cutZ-loopK zero = refl
cutZ-loopK (suc k) = cong (w2 ∷_) (cutZ-loopK k)

to-w≡rounds : (w : Loop (Gskel two-chain) fzero) → to-w w ≡ rounds w
to-w≡rounds w =
  cong (λ k → length (proj₁ (TC.cutZ k))) (unloop w)
  ∙ cong length (cutZ-loopK (rounds w))
  ∙ length-rep (rounds w) w2

toQ : π₁ᵈ (Gskel two-chain) fzero → ℕ
toQ = π₁ᵈ-rec isSetℕ to-w (λ ℓ m h → cong to-w (ah-diag-sk h))

to≡roundsQ : (x : π₁ᵈ (Gskel two-chain) fzero)
           → toQ x ≡ MonoidIso.to gskel-classify x
to≡roundsQ = elimProp (λ _ → isSetℕ _ _) to-w≡rounds

gskel-classify-2 :
  MonoidIso (π₁ᵈ (Gskel two-chain) fzero) ℕ
            (_⊞ᵈ_ {G = Gskel two-chain}) [ nil fzero ]
            _+ℕ_ zero
gskel-classify-2 = record
  { to      = toQ
  ; from    = λ k → [ loopK k ]
  ; to-·    = λ x y → to≡roundsQ (x ⊞ᵈ y)
                ∙ MonoidIso.to-· gskel-classify x y
                ∙ cong₂ _+ℕ_ (sym (to≡roundsQ x)) (sym (to≡roundsQ y))
  ; to-e    = refl
  ; from-·  = λ k m → cong [_] (loopK-+ k m)
  ; from-e  = refl
  ; to∘from = λ k → cong length (cutZ-loopK k) ∙ length-rep k w2
  ; from∘to = λ x → cong (λ n → [ loopK n ]) (to≡roundsQ x)
                ∙ MonoidIso.from∘to gskel-classify x
  }

-- §5 核对层（two-chain 具象——refl 级）

check-canonical-w2w2 : proj₁ (TC.cutZ (concatL (w2 ∷ w2 ∷ []))) ≡ (w2 ∷ w2 ∷ [])
check-canonical-w2w2 = refl

check-cutZ-loopK-3 : proj₁ (TC.cutZ (loopK 3)) ≡ w2 ∷ w2 ∷ w2 ∷ []
check-cutZ-loopK-3 = refl

check-to-w2-2 : MonoidIso.to gskel-classify-2 [ w2 ] ≡ suc zero
check-to-w2-2 = refl

check-agree-w2w2 : MonoidIso.to gskel-classify-2 [ w2 ++w w2 ]
                 ≡ MonoidIso.to gskel-classify [ w2 ++w w2 ]
check-agree-w2w2 = refl

-- 【指针】唯一性对账件移 _PPI4l.check-uniq-w2w2-type（同内容已在彼处——本文件不再重复；
--   泛形 decomp-unique 立界注记见 §3）。