{-# OPTIONS --cubical --rewriting --guardedness #-}

-- | _PPI4g
-- π₁ᵈ(Gskel two-chain) 完全分类（v2 立界件「自由幺半群 iso」转工时）：
--   主定理 gskel-classify：π₁ᵈ(Gskel two-chain) fzero ≅ (ℕ,+)（MonoidIso 八字段全闭）。
--
-- 数学背景：
--   Gskel two-chain = 2 顶点 + 2 有向边（e01 = 0→1，e10 = 1→0，无自环——v2-1 已证）。
--   闭 walk 必交替 (e01∷e10)^k ⇒ 由往返计数 k = n₊ = n₋ 完全决定（「两顶点往返计数对」
--   在闭 walk 处退化为对角 (k,k)）。AHomotopy = 对角（ah-diag-sk）⇒ 商类即 walk 本身。
--
-- 核心原则：
--   ① 免匹配纪律：{v =} 索引细化 + ⊥-elim 自环消解（even2-len 分派器形复用）；
--   ② 边规范化：⊑₂ 三构造子穷尽 + ≢ 分量 isPropΠ（证明无关）；
--   ③ 商面零重证：π₁ᵈ-rec/⊞ᵈ β/ah-diag-sk 全复用（_PPI2/_PPI4 机件）。
--
-- 包含：§1 loopK/rounds 走向计数｜§2 边规范化 + 重构 unloop｜§3 可加性 + MonoidIso 主定理
--       ｜§4 计数对分型（npos/nneg）+ 核对层

module _PPI4g where

open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_×_; _,_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat using (ℕ; zero; suc)
open import Agda.Builtin.Equality using () renaming (refl to reflᴱ; _≡_ to _≡ᴱ_)
open import Cubical.Foundations.Prelude using (_≡_; refl; sym; cong; _∙_)
open import Cubical.Foundations.HLevels using (isPropΠ)
open import Cubical.Data.Nat using (isSetℕ)
open import Cubical.HITs.SetQuotients using ([_]; squash/)
open import Cubical.HITs.SetQuotients.Properties using (rec; elimProp; elimProp2)
open import Sovereign.Topology.BarceloAHomotopy
  using (DiGraph; Walk; nil; cons; AHomotopy; _++w_)
open import Sovereign.Synthesis.McCordPi0 using (two-chain; ⊑₂-01; _⊑₂_)
open import _PPI using (Loop)
open import _PPI4 using (Gskel; MonoidIso)
open import _PPI2 using (π₁ᵈ; _⊞ᵈ_; π₁ᵈ-rec)
open import _PPI4c using (edgeGskel-neq; ah-diag-sk)
open import Sovereign.Topology._PMc2 using (KEdge)
open import _PPI4d using (e01; e10; w0; w2; w4)

private
  module DG = DiGraph

infixl 6 _+ℕ_
_+ℕ_ : ℕ → ℕ → ℕ
zero  +ℕ n = n
suc m +ℕ n = suc (m +ℕ n)

---------------------------------------------------------------------------------
-- §1 loopK（k 次往返）+ rounds（往返计数——分派器形 mutual）
---------------------------------------------------------------------------------

loopK : ℕ → Loop (Gskel two-chain) fzero
loopK zero    = nil fzero
loopK (suc k) = cons e01 (cons e10 (loopK k))

mutual
  rounds : (w : Loop (Gskel two-chain) fzero) → ℕ
  rounds (nil fzero) = zero
  rounds (cons {v = fzero} e _) = ⊥-elim (edgeGskel-neq fzero fzero e reflᴱ)
  rounds (cons {v = fsuc fzero} e t) = suc (rounds₁ t)

  rounds₁ : (t : Walk (Gskel two-chain) (fsuc fzero) fzero) → ℕ
  rounds₁ (cons {v = fzero} e b) = rounds b
  rounds₁ (cons {v = fsuc fzero} e _) = ⊥-elim (edgeGskel-neq (fsuc fzero) (fsuc fzero) e reflᴱ)

rounds-loopK : ∀ k → rounds (loopK k) ≡ k
rounds-loopK zero = refl
rounds-loopK (suc k) = cong suc (rounds-loopK k)

---------------------------------------------------------------------------------
-- §2 边规范化（⊑₂ 三构造子穷尽）+ 重构主件 unloop

isProp⊥L : (x y : ⊥) → x ≡ y
isProp⊥L x _ = ⊥-elim x
---------------------------------------------------------------------------------

no1⊑0 : fsuc fzero ⊑₂ fzero → ⊥
no1⊑0 ()

-- 隐式钉参（πₙ-B1 教训④：fzero : Fin (suc ?n) 独立签名不钉 ⇒ {A = Fin 2} 显式）
E01 : Set
E01 = _≡ᴱ_ {A = Fin 2} fzero (fsuc fzero)

0≢1 : E01 → ⊥
0≢1 ()

-- 同向 KEdge 的证明无关（⊑ 头唯一构造子 + ≢ 分量 isPropΠ）
-- 命名件钉返回型（配对 λ 免 meta 塌陷——πₙ-B1 教训同款）
k01-fill : (E01 → ⊥) → KEdge two-chain fzero (fsuc fzero)
k01-fill r = (⊑₂-01 , r)

canon-01 : (p q : KEdge two-chain fzero (fsuc fzero)) → p ≡ q
canon-01 (⊑₂-01 , r) (⊑₂-01 , r') =
  cong k01-fill (isPropΠ (λ _ → isProp⊥L) r r')

-- e : edge 0 1 = KEdge 0 1 ⊎ KEdge 1 0；反向分量的 ⊑ 头无构造子 ⇒ 归 inj₁ 正范
edge01-canon : (e : DG.edge (Gskel two-chain) fzero (fsuc fzero)) → e ≡ e01
edge01-canon (inj₁ p) = cong inj₁ (canon-01 p (⊑₂-01 , 0≢1))
edge01-canon (inj₂ (q , _)) = ⊥-elim (no1⊑0 q)

edge10-canon : (e : DG.edge (Gskel two-chain) (fsuc fzero) fzero) → e ≡ e10
edge10-canon (inj₁ (q , _)) = ⊥-elim (no1⊑0 q)
edge10-canon (inj₂ p) = cong inj₂ (canon-01 p (⊑₂-01 , 0≢1))

-- 重构主件：任何闭 walk = loopK（往返计数）——分类的「构造性」半边
mutual
  unloop : (w : Loop (Gskel two-chain) fzero) → w ≡ loopK (rounds w)
  unloop (nil fzero) = refl
  unloop (cons {v = fzero} e _) = ⊥-elim (edgeGskel-neq fzero fzero e reflᴱ)
  unloop (cons {v = fsuc fzero} e t) = unloop₁ e t

  unloop₁ : (e : DG.edge (Gskel two-chain) fzero (fsuc fzero))
            (t : Walk (Gskel two-chain) (fsuc fzero) fzero)
          → cons e t ≡ loopK (suc (rounds₁ t))
  unloop₁ e (cons {v = fzero} e' b) =
    cong (λ x → cons x (cons e' b)) (edge01-canon e)
    ∙ cong (λ x → cons e01 (cons x b)) (edge10-canon e')
    ∙ cong (λ x → cons e01 (cons e10 x)) (unloop b)
  unloop₁ e (cons {v = fsuc fzero} e' _) =
    ⊥-elim (edgeGskel-neq (fsuc fzero) (fsuc fzero) e' reflᴱ)

---------------------------------------------------------------------------------
-- §3 可加性 + MonoidIso 主定理
---------------------------------------------------------------------------------

-- 往返计数对连接可加（mutual 走向分配）
mutual
  rounds-++ : (w w' : Loop (Gskel two-chain) fzero)
            → rounds (w ++w w') ≡ rounds w +ℕ rounds w'
  rounds-++ (nil fzero) w' = refl
  rounds-++ (cons {v = fzero} e _) w' = ⊥-elim (edgeGskel-neq fzero fzero e reflᴱ)
  rounds-++ (cons {v = fsuc fzero} e t) w' = cong suc (rounds₁-++ t w')

  rounds₁-++ : (t : Walk (Gskel two-chain) (fsuc fzero) fzero)
               (w' : Loop (Gskel two-chain) fzero)
             → rounds₁ (t ++w w') ≡ rounds₁ t +ℕ rounds w'
  rounds₁-++ (cons {v = fzero} e b) w' = rounds-++ b w'
  rounds₁-++ (cons {v = fsuc fzero} e _) w' =
    ⊥-elim (edgeGskel-neq (fsuc fzero) (fsuc fzero) e reflᴱ)

loopK-+ : ∀ k m → loopK (k +ℕ m) ≡ loopK k ++w loopK m
loopK-+ zero m = refl
loopK-+ (suc k) m = cong (λ x → cons e01 (cons e10 x)) (loopK-+ k m)

-- 主定理：π₁ᵈ(Gskel two-chain) ≅ (ℕ,+)（MonoidIso 八字段全闭）
gskel-classify :
  MonoidIso (π₁ᵈ (Gskel two-chain) fzero) ℕ
            (_⊞ᵈ_ {G = Gskel two-chain}) [ nil fzero ]
            _+ℕ_ zero
gskel-classify = record
  { to      = π₁ᵈ-rec isSetℕ rounds (λ ℓ m h → cong rounds (ah-diag-sk h))
  ; from    = λ k → [ loopK k ]
  ; to-·    = elimProp2 (λ _ _ → isSetℕ _ _) rounds-++
  ; to-e    = refl
  ; from-·  = λ k m → cong [_] (loopK-+ k m)
  ; from-e  = refl
  ; to∘from = rounds-loopK
  ; from∘to = elimProp (λ _ → squash/ _ _) λ ℓ → sym (cong [_] (unloop ℓ))
  }

---------------------------------------------------------------------------------
-- §4 计数对分型（npos/nneg——「两顶点往返计数对」）+ 核对层
---------------------------------------------------------------------------------

npos : ∀ {u v} → Walk (Gskel two-chain) u v → ℕ
npos (nil _) = zero
npos (cons (inj₁ _) p) = suc (npos p)
npos (cons (inj₂ _) p) = npos p

nneg : ∀ {u v} → Walk (Gskel two-chain) u v → ℕ
nneg (nil _) = zero
nneg (cons (inj₁ _) p) = nneg p
nneg (cons (inj₂ _) p) = suc (nneg p)

-- 计数对 = AHomotopy 不变量（对角化后 cong 直得）
pair-inv : ∀ {w w' : Loop (Gskel two-chain) fzero}
         → AHomotopy (Gskel two-chain) w w'
         → (npos w ≡ npos w') × (nneg w ≡ nneg w')
pair-inv h = cong npos (ah-diag-sk h) , cong nneg (ah-diag-sk h)

npos-loopK : ∀ k → npos (loopK k) ≡ k
npos-loopK zero = refl
npos-loopK (suc k) = cong suc (npos-loopK k)

nneg-loopK : ∀ k → nneg (loopK k) ≡ k
nneg-loopK zero = refl
nneg-loopK (suc k) = cong suc (nneg-loopK k)

-- 计数对与往返计数的对齐（命名件——≤3 链纪律拆分）
npos-≡-rounds : (w : Loop (Gskel two-chain) fzero) → npos w ≡ rounds w
npos-≡-rounds w = cong npos (unloop w) ∙ npos-loopK (rounds w)

nneg-≡-rounds : (w : Loop (Gskel two-chain) fzero) → nneg w ≡ rounds w
nneg-≡-rounds w = cong nneg (unloop w) ∙ nneg-loopK (rounds w)

-- 闭 walk 对角定理：n₊ = n₋（计数对退化为对角 (k,k)）
loop-diagonal : (w : Loop (Gskel two-chain) fzero) → npos w ≡ nneg w
loop-diagonal w = npos-≡-rounds w ∙ sym (nneg-≡-rounds w)

-- 计数对完全分类：同计数 ⟹ 同 walk（「同 pair ⟹ ∼」的构造性形）
loop-classify : (w w' : Loop (Gskel two-chain) fzero)
              → npos w ≡ npos w' → w ≡ w'
loop-classify w w' p =
  unloop w ∙ cong loopK k-eq ∙ sym (unloop w')
  where
  k-eq : rounds w ≡ rounds w'
  k-eq = sym (npos-≡-rounds w) ∙ p ∙ npos-≡-rounds w'

-- 核对层（w0/w2/w4 分类 + 计数对）
chk-rounds-w0 : rounds w0 ≡ zero
chk-rounds-w0 = refl

chk-rounds-w2 : rounds w2 ≡ suc zero
chk-rounds-w2 = refl

chk-rounds-w4 : rounds w4 ≡ suc (suc zero)
chk-rounds-w4 = refl

chk-loopK-2 : loopK (suc (suc zero)) ≡ w4
chk-loopK-2 = refl

chk-pair-w2 : (npos w2 ≡ suc zero) × (nneg w2 ≡ suc zero)
chk-pair-w2 = refl , refl

chk-pair-w4 : (npos w4 ≡ suc (suc zero)) × (nneg w4 ≡ suc (suc zero))
chk-pair-w4 = refl , refl

chk-to-w2 : MonoidIso.to gskel-classify [ w2 ] ≡ suc zero
chk-to-w2 = refl

chk-from-2 : MonoidIso.from gskel-classify (suc (suc zero)) ≡ [ w4 ]
chk-from-2 = refl
