{-# OPTIONS --rewriting --guardedness #-}

-- | _PM2r — GAP-M2-routeEnum 探针：泛型路由枚举（存在性 + 恰一次数据层）
--
-- 数学背景：Morse 路由枚举问题。MorseRouteListG 已立泛型接口 RouteListG
--   （routeList + route-complete + route-sound），实现层留实例（缺口①）；
--   CoefRoute（系数路由，MorseCoeffRoute）数据层枚举为缺口②。
--   本件交付：①泛型 direct 路由实现（DecMorph + FiniteK = RouteListG 实例）
--   ② CoefRoute 候选表完备性 + K₃ 具体核对（字面成员链）
--   ③ filterF NoDup 保持（恰一次的过滤面）
--   ⚠ 数学边界（侦察实证）：Morse 系数 ≠ 原始边界系数（routing-k3 总系数 T₁
--   而 coeffᵏ v1 e20 = T₀）——候选表 = 全 (τ,μ) 对才正确；「μ ≡ coeff τ σ」
--   一致性仅 cr-direct 真；cr-via 系数传播律立界。
--
-- 核心原则：
--   1. 零 with（aux 显式判定参数范式——filterF/consD 互递归 + 判定值模式匹配）
--   2. 完备性无前提（候选表法）；恰一次过滤面（NoDup 保持）+ 全表传递立界
--   3. 复用优先：FiniteK/allCells/EnumComplete/_∈List_/upTo 零重证
module _PM2r where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat using (ℕ; zero; suc; _<_; _≤_; z≤n; s≤s)
open import Data.List using (List; []; _∷_; _++_; map; concatMap)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _×_; _,_) renaming (proj₁ to p₁; proj₂ to p₂)
open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Binary.PropositionalEquality
open import Sovereign.Base.Trit using (Trit; T₀; T₁; T₂)
open import Sovereign.Application.MorseRouteListG
  using (FiniteK; EnumComplete; allCells; upTo; _∈List_; here; there; RouteListG)
import Sovereign.Topology.MorseCoeffRoute as MCR
open import Sovereign.Topology.FormanMinimal
  using (Sx; v0; v1; v2; e01; e12; e20; t)

--------------------------------------------------------------------------------
-- §1 工具层
--------------------------------------------------------------------------------

lt-or-eq : (i m : ℕ) → i ≤ m → (i < m) ⊎ (i ≡ m)
lt-or-eq zero zero z≤n = inj₂ refl
lt-or-eq zero (suc m) z≤n = inj₁ (s≤s z≤n)
lt-or-eq (suc i) zero ()
lt-or-eq (suc i) (suc m) (s≤s p) with lt-or-eq i m p
... | inj₁ l = inj₁ (s≤s l)
... | inj₂ e = inj₂ (cong suc e)

map-mem : {A B : Set} (f : A → B) (x : A) (xs : List A) → x ∈List xs → f x ∈List map f xs
map-mem f x .(x ∷ _) (here _) = here _
map-mem f x .(_ ∷ _) (there y ys m) = there (f y) (map f ys) (map-mem f x ys m)

++-mem-l : {A : Set} {x : A} (xs ys : List A) → x ∈List xs → x ∈List (xs ++ ys)
++-mem-l (x ∷ xs) ys (here .xs) = here (xs ++ ys)
++-mem-l (y ∷ xs) ys (there .y .xs m) = there y (xs ++ ys) (++-mem-l xs ys m)

++-mem-r : {A : Set} {x : A} (xs ys : List A) → x ∈List ys → x ∈List (xs ++ ys)
++-mem-r [] ys m = m
++-mem-r (y ∷ xs) ys m = there y (xs ++ ys) (++-mem-r xs ys m)

∈List-++-inv : {A : Set} {x : A} (xs ys : List A) → x ∈List (xs ++ ys) → (x ∈List xs) ⊎ (x ∈List ys)
∈List-++-inv [] ys m = inj₂ m
∈List-++-inv (x ∷ xs) ys (here .(xs ++ ys)) = inj₁ (here xs)
∈List-++-inv (y ∷ xs) ys (there .y .(xs ++ ys) m) with ∈List-++-inv xs ys m
... | inj₁ l = inj₁ (there y xs l)
... | inj₂ r = inj₂ r

upTo-mem : (i n : ℕ) → i < n → i ∈List upTo n
upTo-mem i (suc m) (s≤s p) with lt-or-eq i m p
... | inj₁ l = ++-mem-l (upTo m) (m ∷ []) (upTo-mem i m l)
... | inj₂ e = subst (λ z → z ∈List upTo (suc m)) (sym e) (++-mem-r (upTo m) (m ∷ []) (here []))

allCells-mem : {K : Set} (ec : EnumComplete K) → (k : K) → k ∈List allCells (EnumComplete.fk ec)
allCells-mem ec k with EnumComplete.enum-surj ec k
... | (i , i<n , eq) =
  subst (λ z → z ∈List allCells (EnumComplete.fk ec)) eq
    (map-mem (FiniteK.enumK (EnumComplete.fk ec)) i
      (upTo (FiniteK.nK (EnumComplete.fk ec)))
      (upTo-mem i (FiniteK.nK (EnumComplete.fk ec)) i<n))

concatMap-mem : {A B : Set} (g : A → List B) (y : A) (ys : List A) (b : B) →
  b ∈List g y → y ∈List ys → b ∈List concatMap g ys
concatMap-mem g y .(y ∷ zs) b gb (here zs) = ++-mem-l (g y) (concatMap g zs) gb
concatMap-mem g y (z ∷ zs) b gb (there .z .zs ym) =
  ++-mem-r (g z) (concatMap g zs) (concatMap-mem g y zs b gb ym)

data NoDup {K : Set} : List K → Set where
  nd-[] : NoDup []
  nd-∷ : ∀ {x xs} → ¬ (x ∈List xs) → NoDup xs → NoDup (x ∷ xs)

--------------------------------------------------------------------------------
-- §2 可判定形态 + Dec 过滤（零 with：consD 显式判定参数）
--------------------------------------------------------------------------------

record DecMorph (K : Set) (Face : K → K → Set) (V : K → Maybe K) : Set where
  field
    face-dec : (τ σ : K) → Dec (Face τ σ)
    v-noth-dec : (w : K) → Dec (V w ≡ nothing)

×-dec : {A B : Set} → Dec A → Dec B → Dec (A × B)
×-dec (yes a) (yes b) = yes (a , b)
×-dec (yes a) (no ¬b) = no (λ ab → ¬b (p₂ ab))
×-dec (no ¬a) _ = no (λ ab → ¬a (p₁ ab))

mutual
  filterF : {A : Set} {P : A → Set} (dP : (a : A) → Dec (P a)) → List A → List A
  filterF dP [] = []
  filterF dP (x ∷ xs) = consD dP x xs (dP x)

  consD : {A : Set} {P : A → Set} (dP : (a : A) → Dec (P a)) (y : A) (ys : List A) →
    Dec (P y) → List A
  consD dP y ys (yes _) = y ∷ filterF dP ys
  consD dP y ys (no _) = filterF dP ys

-- §2.1 成员正向（aux：判定值模式匹配，零 with）
memHere : {A : Set} {P : A → Set} (dP : (a : A) → Dec (P a)) (x : A) (xs : List A) →
  P x → (d : Dec (P x)) → x ∈List consD dP x xs d
memHere dP x xs px (yes _) = here (filterF dP xs)
memHere dP x xs px (no ¬p) = ⊥-elim (¬p px)

memThere : {A : Set} {P : A → Set} (dP : (a : A) → Dec (P a)) (y : A) (ys : List A) →
  (d : Dec (P y)) (x : A) → x ∈List filterF dP ys → x ∈List consD dP y ys d
memThere dP y ys (yes _) x m = there y (filterF dP ys) m
memThere dP y ys (no _) x m = m

filterF-mem : {A : Set} {P : A → Set} (dP : (a : A) → Dec (P a)) (x : A) (xs : List A) →
  P x → x ∈List xs → x ∈List filterF dP xs
filterF-mem dP x .(x ∷ _) px (here _) = memHere dP x _ px (dP x)
filterF-mem dP x (y ∷ ys) px (there .y .ys m) =
  memThere dP y ys (dP y) x (filterF-mem dP x ys px m)

-- §2.2 成员逆向（out）
filterF-out : {A : Set} {P : A → Set} (dP : (a : A) → Dec (P a)) (x : A) (xs : List A) →
  x ∈List filterF dP xs → Σ (P x) (λ _ → x ∈List xs)
filterF-out dP x [] ()
filterF-out dP x (y ∷ xs) m = outG dP y xs (dP y) x m
  where
    outG : {A : Set} {P : A → Set} (dP : (a : A) → Dec (P a)) (y : A) (ys : List A) →
      (d : Dec (P y)) (x : A) → x ∈List consD dP y ys d → Σ (P x) (λ _ → x ∈List (y ∷ ys))
    outG dP y ys (yes py) .y (here .(filterF dP ys)) = py , here ys
    outG dP y ys (yes py) x (there .y .(filterF dP ys) mm) with filterF-out dP x ys mm
    ... | (px , l) = px , there y ys l
    outG dP y ys (no _) x mm with filterF-out dP x ys mm
    ... | (px , l) = px , there y ys l

-- §2.3 NoDup 保持（恰一次的过滤面）
filterF-nodup : {A : Set} {P : A → Set} (dP : (a : A) → Dec (P a)) (xs : List A) →
  NoDup xs → NoDup (filterF dP xs)
filterF-nodup dP [] nd-[] = nd-[]
filterF-nodup dP (y ∷ xs) (nd-∷ ¬in nd) = nodupG dP y xs (dP y) ¬in (filterF-nodup dP xs nd)
  where
    nodupG : {A : Set} {P : A → Set} (dP : (a : A) → Dec (P a)) (y : A) (ys : List A) →
      (d : Dec (P y)) → ¬ (y ∈List ys) → NoDup (filterF dP ys) → NoDup (consD dP y ys d)
    nodupG dP y ys (yes _) ¬in nd = nd-∷ (λ m → ¬in (p₂ (filterF-out dP y ys m))) nd
    nodupG dP y ys (no _) ¬in nd = nd

--------------------------------------------------------------------------------
-- §3 泛型 direct 路由实现（RouteListG 实例——缺口①）
--------------------------------------------------------------------------------

directCond : {K : Set} (Face : K → K → Set) (V : K → Maybe K) (τ σ : K) → Set
directCond Face V τ σ = Face τ σ × (V τ ≡ nothing)

directCells : {K : Set} {Face : K → K → Set} {V : K → Maybe K}
  (dm : DecMorph K Face V) (fk : FiniteK K) (σ : K) → List K
directCells dm fk σ = filterF (λ τ → ×-dec (DecMorph.face-dec dm τ σ) (DecMorph.v-noth-dec dm τ))
  (allCells fk)

routeListG-direct : {K : Set} {Face : K → K → Set} {V : K → Maybe K}
  (ec : EnumComplete K) (dm : DecMorph K Face V) → RouteListG K Face V
routeListG-direct {K} {Face} {V} ec dm = record
  { routeList = directCells dm (EnumComplete.fk ec)
  ; route-complete = λ σ τ cond →
      filterF-mem (λ τ → ×-dec (DecMorph.face-dec dm τ σ) (DecMorph.v-noth-dec dm τ))
        τ (allCells (EnumComplete.fk ec)) cond (allCells-mem ec τ)
  ; route-sound = λ σ τ m →
      p₁ (filterF-out (λ τ → ×-dec (DecMorph.face-dec dm τ σ) (DecMorph.v-noth-dec dm τ))
        τ (allCells (EnumComplete.fk ec)) m)
  }

--------------------------------------------------------------------------------
-- §4 CoefRoute 候选表（数据层枚举——缺口②）
--------------------------------------------------------------------------------

tritList : List Trit
tritList = T₀ ∷ T₁ ∷ T₂ ∷ []

trit-mem : (μ : Trit) → μ ∈List tritList
trit-mem T₀ = here (T₁ ∷ T₂ ∷ [])
trit-mem T₁ = there T₀ (T₁ ∷ T₂ ∷ []) (here (T₂ ∷ []))
trit-mem T₂ = there T₀ (T₁ ∷ T₂ ∷ []) (there T₁ (T₂ ∷ []) (here []))

grp : {K : Set} → K → List (K × Trit)
grp τ = map (λ μ → (τ , μ)) tritList

coefCand : {K : Set} (fk : FiniteK K) (σ : K) → List (K × Trit)
coefCand fk _ = concatMap grp (allCells fk)

-- 候选表完备性（无前提）：任意路由的 (τ,μ) 必在全候选表。
-- 数学注：候选面 = K × Trit 全积——「哪些是真路由」是 cr-via 系数传播律问题（立界）。
module _ {K : Set} {V : K → Maybe K} {Face : K → K → Set} {coeff : K → K → Trit} where
  open MCR.CoeffRouteDef K V Face coeff using (CoefRoute)

  coef-route-complete : (ec : EnumComplete K) (σ τ : K) (μ : Trit) →
    CoefRoute σ τ μ → (τ , μ) ∈List coefCand (EnumComplete.fk ec) σ
  coef-route-complete ec σ τ μ _ =
    concatMap-mem (grp {K}) τ (allCells (EnumComplete.fk ec)) (τ , μ)
      (map-mem (λ ν → (τ , ν)) μ tritList (trit-mem μ))
      (allCells-mem ec τ)

--------------------------------------------------------------------------------
-- §5 K₃ 具体核对（字面成员链——全积 21 对）
--------------------------------------------------------------------------------

sxAt : ℕ → Sx
sxAt zero = v0
sxAt (suc zero) = v1
sxAt (suc (suc zero)) = v2
sxAt (suc (suc (suc zero))) = e01
sxAt (suc (suc (suc (suc zero)))) = e12
sxAt (suc (suc (suc (suc (suc zero))))) = e20
sxAt (suc (suc (suc (suc (suc (suc _)))))) = t

fkS : FiniteK Sx
fkS = record { nK = 7 ; enumK = sxAt }

-- routing-k3 终点数据 (v1 , T₁) 在候选表（grp v1 段第 2 位）
check-v1T1 : (v1 , T₁) ∈List coefCand fkS e20
check-v1T1 = there (v0 , T₀) _ (there (v0 , T₁) _ (there (v0 , T₂) _ (there (v1 , T₀) _ (here _))))

-- direct-route 数据 (v2 , T₂) 在候选表（grp v2 段第 3 位）
check-v2T2 : (v2 , T₂) ∈List coefCand fkS e20
check-v2T2 =
  there (v0 , T₀) _ (there (v0 , T₁) _ (there (v0 , T₂) _
  (there (v1 , T₀) _ (there (v1 , T₁) _ (there (v1 , T₂) _
  (there (v2 , T₀) _ (there (v2 , T₁) _ (here _))))))))

-- 两条路由数据互异（恰一次的具体面：不同 τ 决然不同）
v1≢v2 : ¬ (v1 ≡ v2)
v1≢v2 ()

fst : Sx × Trit → Sx
fst z = p₁ z

check-distinct : ¬ ((v1 , T₁) ≡ (v2 , T₂))
check-distinct e = v1≢v2 (cong fst e)

--------------------------------------------------------------------------------
-- §6 立界（精确剩余）
--------------------------------------------------------------------------------
-- (i) cr-via 系数传播律（Morse 系数 = 路由总系数的计算律）——真路由面刻画；
-- (ii) 全表恰一次传递（map/concatMap NoDup 需单射前提 + ∈List 引理精化，~30-60 行）；
-- (iii) 推导层 multiplicity（同一 (τ,μ) 多推导）与数据层恰一次的对账定理；
-- (iv) RouteListG 的 via 面（递归枚举 cr-via 路由——dim 下降保证终止）。
