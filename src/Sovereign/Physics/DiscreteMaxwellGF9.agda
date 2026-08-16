{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Physics.DiscreteMaxwellGF9
-- 78 电磁学 — GF(9) 共轭电磁学时间演化层 (0 postulate, 无洞)
--
-- 电场 E 与磁场 B 是一个 GF(9) 场 F = E + Bα 的实部与虚部。
-- GF(9) = GF(3)[x]/(x²+1), α² = -1。Frobenius 共轭 σ(a+bα) = a-bα
-- 在代数上实现「90° 相位差」——垂直性是 σ 的结构产物, 非外加几何条件。
--
-- 复用资产: Sovereign.Base.Trit (Trit/⊕/negate/c3-ccw),
--           Sovereign.Algebra.GF9 (GF9=Trit×Trit/_+gf9_/galoisConjugate)。
--
-- 核心 (0-postulate, 全部 refl/符号):
--   σ-time-comm      σ 与时间差分交换 (90° 相位差演化不变)
--   curl9 (共轭旋度)  实部=∇×B, 虚部=-∇×E
--   reVec-curl9 / imVec-curl9  投影定理 (定义直接给出 refl)
--   ampere-from-unified   实部投影 ⇒ 安培定律
--   faraday-from-unified  虚部投影 ⇒ 法拉第定律
--
-- 诚实边界: 与 DiscreteEMField3D 的 Fin 3 静态内核是两套格点表示
-- (Trit vs Fin 3), 本模块独立基于 Trit, 是离散第一性本体的相位升维层。

module Sovereign.Physics.DiscreteMaxwellGF9 where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂; module ≡-Reasoning)
open ≡-Reasoning

open import Sovereign.Base.Trit using (Trit; T₀; T₁; T₂; _⊕_; negate; negate²; c3-ccw;
  ⊕-assoc; ⊕-comm; ⊕-identityˡ; ⊕-inverse)
open import Sovereign.Algebra.GF9
  using (GF9; _+gf9_)
  renaming (galoisConjugate to σ; galoisConjugate-add to σ-add)

--------------------------------------------------------------------------------
-- §1. GF9 投影与负元; σ 保负元
--------------------------------------------------------------------------------

re : GF9 → Trit
re = proj₁

im : GF9 → Trit
im = proj₂

neg9 : GF9 → GF9
neg9 (a , b) = (negate a , negate b)

σ-neg : ∀ x → σ (neg9 x) ≡ neg9 (σ x)
σ-neg (a , b) = refl

--------------------------------------------------------------------------------
-- §2. 时间层
--------------------------------------------------------------------------------

Time : Set
Time = ℕ

Point : Set
Point = Trit × Trit × Trit

nextT : Trit → Trit
nextT = c3-ccw

GF9Scal : Set
GF9Scal = Point → GF9

GF9Vec : Set
GF9Vec = Point → GF9 × GF9 × GF9

GF9ScalTime : Set
GF9ScalTime = Time → Point → GF9

GF9VecTime : Set
GF9VecTime = Time → Point → GF9 × GF9 × GF9

addVec9 : GF9 × GF9 × GF9 → GF9 × GF9 × GF9 → GF9 × GF9 × GF9
addVec9 (x1 , y1 , z1) (x2 , y2 , z2) = (x1 +gf9 x2 , y1 +gf9 y2 , z1 +gf9 z2)

negVec9 : GF9 × GF9 × GF9 → GF9 × GF9 × GF9
negVec9 (x , y , z) = (neg9 x , neg9 y , neg9 z)

Δt9 : GF9ScalTime → Time → Point → GF9
Δt9 F t p = (F (suc t) p) +gf9 (neg9 (F t p))

ΔtV9 : GF9VecTime → Time → Point → GF9 × GF9 × GF9
ΔtV9 F t p = addVec9 (F (suc t) p) (negVec9 (F t p))

--------------------------------------------------------------------------------
-- §3. σ 与时间差分交换 (共轭守恒核心)
--------------------------------------------------------------------------------

σ-time-comm : ∀ (F : GF9ScalTime) (t : Time) (p : Point) →
  σ (Δt9 F t p) ≡ Δt9 (λ s q → σ (F s q)) t p
σ-time-comm F t p = begin
  σ ((F (suc t) p) +gf9 (neg9 (F t p)))
    ≡⟨ σ-add (F (suc t) p) (neg9 (F t p)) ⟩
  (σ (F (suc t) p)) +gf9 (σ (neg9 (F t p)))
    ≡⟨ cong ((σ (F (suc t) p)) +gf9_) (σ-neg (F t p)) ⟩
  (σ (F (suc t) p)) +gf9 (neg9 (σ (F t p)))
    ≡⟨ refl ⟩
  Δt9 (λ s q → σ (F s q)) t p ∎

--------------------------------------------------------------------------------
-- §4. Trit 差分与旋度 (共轭旋度的 GF(3) 内核)
--------------------------------------------------------------------------------

TritScal : Set
TritScal = Point → Trit

TritVec : Set
TritVec = Point → Trit × Trit × Trit

dxT : TritScal → TritScal
dxT φ (i , j , k) = (φ (nextT i , j , k)) ⊕ (negate (φ (i , j , k)))

dyT : TritScal → TritScal
dyT φ (i , j , k) = (φ (i , nextT j , k)) ⊕ (negate (φ (i , j , k)))

dzT : TritScal → TritScal
dzT φ (i , j , k) = (φ (i , j , nextT k)) ⊕ (negate (φ (i , j , k)))

vxT : TritVec → TritScal
vxT A p = proj₁ (A p)

vyT : TritVec → TritScal
vyT A p = proj₁ (proj₂ (A p))

vzT : TritVec → TritScal
vzT A p = proj₂ (proj₂ (A p))

addVecT : Trit × Trit × Trit → Trit × Trit × Trit → Trit × Trit × Trit
addVecT (x1 , y1 , z1) (x2 , y2 , z2) = (x1 ⊕ x2 , y1 ⊕ y2 , z1 ⊕ z2)

negVecT : Trit × Trit × Trit → Trit × Trit × Trit
negVecT (x , y , z) = (negate x , negate y , negate z)

curlT : TritVec → TritVec
curlT A (i , j , k) =
  ( (dyT (vzT A) (i , j , k)) ⊕ (negate (dzT (vyT A) (i , j , k))) ,
    (dzT (vxT A) (i , j , k)) ⊕ (negate (dxT (vzT A) (i , j , k))) ,
    (dxT (vyT A) (i , j , k)) ⊕ (negate (dyT (vxT A) (i , j , k))) )

--------------------------------------------------------------------------------
-- §5. 三元组级实/虚投影 与 共轭旋度 curl9
--------------------------------------------------------------------------------

-- 三元组级投影: GF9×GF9×GF9 → Trit×Trit×Trit
reVec : GF9 × GF9 × GF9 → Trit × Trit × Trit
reVec (x , y , z) = (re x , re y , re z)

imVec : GF9 × GF9 × GF9 → Trit × Trit × Trit
imVec (x , y , z) = (im x , im y , im z)

-- 场级投影 (逐点三元组投影)
realVec : GF9Vec → TritVec
realVec A p = reVec (A p)

imagVec : GF9Vec → TritVec
imagVec A p = imVec (A p)

-- 共轭旋度: 实部 = ∇×B, 虚部 = -∇×E  (B=虚部场, E=实部场)
curl9 : GF9Vec → GF9Vec
curl9 A p =
  let cB = curlT (imagVec A) p   -- ∇×B
      cE = curlT (realVec A) p   -- ∇×E
  in ( (proj₁ cB , negate (proj₁ cE)) ,
       (proj₁ (proj₂ cB) , negate (proj₁ (proj₂ cE))) ,
       (proj₂ (proj₂ cB) , negate (proj₂ (proj₂ cE))) )

-- 投影定理 1: 实部投影 = ∇×B  (定义直接给出)
reVec-curl9 : ∀ (A : GF9Vec) (p : Point) →
  reVec (curl9 A p) ≡ curlT (imagVec A) p
reVec-curl9 A p = refl

-- 投影定理 2: 虚部投影 = -∇×E  (定义直接给出)
imVec-curl9 : ∀ (A : GF9Vec) (p : Point) →
  imVec (curl9 A p) ≡ negVecT (curlT (realVec A) p)
imVec-curl9 A p = refl

--------------------------------------------------------------------------------
-- §6. 统一 Maxwell 方程与实/虚投影定理
--------------------------------------------------------------------------------

TritVecTime : Set
TritVecTime = Time → Point → Trit × Trit × Trit

ΔtVT : TritVecTime → Time → Point → Trit × Trit × Trit
ΔtVT F t p = addVecT (F (suc t) p) (negVecT (F t p))

-- 实/虚投影与向量代数、时间差分的交换 (分量定义, 均 refl)
reVec-addVec9 : ∀ x y → reVec (addVec9 x y) ≡ addVecT (reVec x) (reVec y)
reVec-addVec9 _ _ = refl

reVec-negVec9 : ∀ x → reVec (negVec9 x) ≡ negVecT (reVec x)
reVec-negVec9 _ = refl

imVec-addVec9 : ∀ x y → imVec (addVec9 x y) ≡ addVecT (imVec x) (imVec y)
imVec-addVec9 _ _ = refl

imVec-negVec9 : ∀ x → imVec (negVec9 x) ≡ negVecT (imVec x)
imVec-negVec9 _ = refl

reVec-ΔtV9 : ∀ (F : GF9VecTime) (t : Time) (p : Point) →
  reVec (ΔtV9 F t p) ≡ ΔtVT (λ s q → realVec (F s) q) t p
reVec-ΔtV9 F t p = refl

imVec-ΔtV9 : ∀ (F : GF9VecTime) (t : Time) (p : Point) →
  imVec (ΔtV9 F t p) ≡ ΔtVT (λ s q → imagVec (F s) q) t p
imVec-ΔtV9 F t p = refl

-- 统一 Maxwell 方程: Δ_t F = ∇×F - J  (单一 GF9 旋量方程)
UnifiedMaxwellHolds : GF9VecTime → GF9VecTime → Set
UnifiedMaxwellHolds F J = ∀ t p →
  ΔtV9 F t p ≡ addVec9 (curl9 (F t) p) (negVec9 (J t p))

-- 安培定律 (实部投影): Δ_t E = ∇×B - J_real
ampere-from-unified : ∀ (F J : GF9VecTime) → UnifiedMaxwellHolds F J →
  ∀ t p → ΔtVT (λ s q → realVec (F s) q) t p
        ≡ addVecT (curlT (imagVec (F t)) p) (negVecT (reVec (J t p)))
ampere-from-unified F J unif t p = begin
  ΔtVT (λ s q → realVec (F s) q) t p
    ≡⟨ sym (reVec-ΔtV9 F t p) ⟩
  reVec (ΔtV9 F t p)
    ≡⟨ cong reVec (unif t p) ⟩
  reVec (addVec9 (curl9 (F t) p) (negVec9 (J t p)))
    ≡⟨ reVec-addVec9 (curl9 (F t) p) (negVec9 (J t p)) ⟩
  addVecT (reVec (curl9 (F t) p)) (reVec (negVec9 (J t p)))
    ≡⟨ cong₂ addVecT (reVec-curl9 (F t) p) (reVec-negVec9 (J t p)) ⟩
  addVecT (curlT (imagVec (F t)) p) (negVecT (reVec (J t p)))
    ≡⟨ refl ⟩
  addVecT (curlT (imagVec (F t)) p) (negVecT (reVec (J t p))) ∎

-- 法拉第定律 (虚部投影): Δ_t B = -∇×E - J_imag
faraday-from-unified : ∀ (F J : GF9VecTime) → UnifiedMaxwellHolds F J →
  ∀ t p → ΔtVT (λ s q → imagVec (F s) q) t p
        ≡ addVecT (negVecT (curlT (realVec (F t)) p)) (negVecT (imVec (J t p)))
faraday-from-unified F J unif t p = begin
  ΔtVT (λ s q → imagVec (F s) q) t p
    ≡⟨ sym (imVec-ΔtV9 F t p) ⟩
  imVec (ΔtV9 F t p)
    ≡⟨ cong imVec (unif t p) ⟩
  imVec (addVec9 (curl9 (F t) p) (negVec9 (J t p)))
    ≡⟨ imVec-addVec9 (curl9 (F t) p) (negVec9 (J t p)) ⟩
  addVecT (imVec (curl9 (F t) p)) (imVec (negVec9 (J t p)))
    ≡⟨ cong₂ addVecT (imVec-curl9 (F t) p) (imVec-negVec9 (J t p)) ⟩
  addVecT (negVecT (curlT (realVec (F t)) p)) (negVecT (imVec (J t p))) ∎

--------------------------------------------------------------------------------
-- §7. σ 与空间差分/标准旋度交换 (补齐 curl-sigma-comm 锚点)
--   注: 此处的 curl9std 是「标准 GF9 旋度」(分量式), 与 §5 的「共轭旋度
--   curl9」不同。σ 是代数同态, 与标准旋度交换 (curl-sigma-comm);
--   而在共轭旋度下 σ 不交换 — 共轭旋度的实/虚分离已由 §5 的投影定理
--   (reVec-curl9 / imVec-curl9) 直接给出。两者并存, 各有用途:
--     curl9std 承载「σ 与空间运算交换」的代数对称;
--     curl9    承载「统一方程实/虚投影」的物理对应。
--------------------------------------------------------------------------------

-- GF9 标量场差分 (dx9/dy9/dz9)
dx9 : GF9Scal → GF9Scal
dx9 φ (i , j , k) = (φ (nextT i , j , k)) +gf9 (neg9 (φ (i , j , k)))

dy9 : GF9Scal → GF9Scal
dy9 φ (i , j , k) = (φ (i , nextT j , k)) +gf9 (neg9 (φ (i , j , k)))

dz9 : GF9Scal → GF9Scal
dz9 φ (i , j , k) = (φ (i , j , nextT k)) +gf9 (neg9 (φ (i , j , k)))

-- σ 与差分交换 (代数同态 + σ-neg)
σ-dx-comm : ∀ (φ : GF9Scal) (p : Point) → σ (dx9 φ p) ≡ dx9 (λ q → σ (φ q)) p
σ-dx-comm φ (i , j , k) = begin
  σ ((φ (nextT i , j , k)) +gf9 (neg9 (φ (i , j , k))))
    ≡⟨ σ-add (φ (nextT i , j , k)) (neg9 (φ (i , j , k))) ⟩
  (σ (φ (nextT i , j , k))) +gf9 (σ (neg9 (φ (i , j , k))))
    ≡⟨ cong ((σ (φ (nextT i , j , k))) +gf9_) (σ-neg (φ (i , j , k))) ⟩
  (σ (φ (nextT i , j , k))) +gf9 (neg9 (σ (φ (i , j , k))))
    ≡⟨ refl ⟩
  dx9 (λ q → σ (φ q)) (i , j , k) ∎

σ-dy-comm : ∀ (φ : GF9Scal) (p : Point) → σ (dy9 φ p) ≡ dy9 (λ q → σ (φ q)) p
σ-dy-comm φ (i , j , k) = begin
  σ ((φ (i , nextT j , k)) +gf9 (neg9 (φ (i , j , k))))
    ≡⟨ σ-add (φ (i , nextT j , k)) (neg9 (φ (i , j , k))) ⟩
  (σ (φ (i , nextT j , k))) +gf9 (σ (neg9 (φ (i , j , k))))
    ≡⟨ cong ((σ (φ (i , nextT j , k))) +gf9_) (σ-neg (φ (i , j , k))) ⟩
  (σ (φ (i , nextT j , k))) +gf9 (neg9 (σ (φ (i , j , k))))
    ≡⟨ refl ⟩
  dy9 (λ q → σ (φ q)) (i , j , k) ∎

σ-dz-comm : ∀ (φ : GF9Scal) (p : Point) → σ (dz9 φ p) ≡ dz9 (λ q → σ (φ q)) p
σ-dz-comm φ (i , j , k) = begin
  σ ((φ (i , j , nextT k)) +gf9 (neg9 (φ (i , j , k))))
    ≡⟨ σ-add (φ (i , j , nextT k)) (neg9 (φ (i , j , k))) ⟩
  (σ (φ (i , j , nextT k))) +gf9 (σ (neg9 (φ (i , j , k))))
    ≡⟨ cong ((σ (φ (i , j , nextT k))) +gf9_) (σ-neg (φ (i , j , k))) ⟩
  (σ (φ (i , j , nextT k))) +gf9 (neg9 (σ (φ (i , j , k))))
    ≡⟨ refl ⟩
  dz9 (λ q → σ (φ q)) (i , j , k) ∎

-- GF9 向量场分量投影
vx9 : GF9Vec → GF9Scal
vx9 A p = proj₁ (A p)

vy9 : GF9Vec → GF9Scal
vy9 A p = proj₁ (proj₂ (A p))

vz9 : GF9Vec → GF9Scal
vz9 A p = proj₂ (proj₂ (A p))

-- σ 逐分量作用于向量场
σVec : GF9 × GF9 × GF9 → GF9 × GF9 × GF9
σVec (x , y , z) = (σ x , σ y , σ z)

σVecField : GF9Vec → GF9Vec
σVecField A p = σVec (A p)

-- 标准 GF9 旋度 (分量式, 非共轭)
curl9std : GF9Vec → GF9Vec
curl9std A (i , j , k) =
  ( (dy9 (vz9 A) (i , j , k)) +gf9 (neg9 (dz9 (vy9 A) (i , j , k))) ,
    (dz9 (vx9 A) (i , j , k)) +gf9 (neg9 (dx9 (vz9 A) (i , j , k))) ,
    (dx9 (vy9 A) (i , j , k)) +gf9 (neg9 (dy9 (vx9 A) (i , j , k))) )

-- σ 与标准旋度交换: σ(∇×A) = ∇×(σA)  (相位差在空间旋度下守恒)
curl-sigma-comm : ∀ (A : GF9Vec) (p : Point) →
  σVec (curl9std A p) ≡ curl9std (σVecField A) p
curl-sigma-comm A (i , j , k) = cong₂ _,_
  -- x 分量: σ(dy vz - dz vy) = dy(σvz) - dz(σvy)
  (begin
    σ ((dy9 (vz9 A) (i , j , k)) +gf9 (neg9 (dz9 (vy9 A) (i , j , k))))
      ≡⟨ σ-add (dy9 (vz9 A) (i , j , k)) (neg9 (dz9 (vy9 A) (i , j , k))) ⟩
    (σ (dy9 (vz9 A) (i , j , k))) +gf9 (σ (neg9 (dz9 (vy9 A) (i , j , k))))
      ≡⟨ cong₂ _+gf9_
           (σ-dy-comm (vz9 A) (i , j , k))
           (trans (σ-neg (dz9 (vy9 A) (i , j , k)))
                  (cong neg9 (σ-dz-comm (vy9 A) (i , j , k)))) ⟩
    (dy9 (λ q → σ (vz9 A q)) (i , j , k)) +gf9 (neg9 (dz9 (λ q → σ (vy9 A q)) (i , j , k)))
      ≡⟨ refl ⟩
    (dy9 (vz9 (σVecField A)) (i , j , k)) +gf9 (neg9 (dz9 (vy9 (σVecField A)) (i , j , k))) ∎)
  (cong₂ _,_
    -- y 分量
    (begin
      σ ((dz9 (vx9 A) (i , j , k)) +gf9 (neg9 (dx9 (vz9 A) (i , j , k))))
        ≡⟨ σ-add (dz9 (vx9 A) (i , j , k)) (neg9 (dx9 (vz9 A) (i , j , k))) ⟩
      (σ (dz9 (vx9 A) (i , j , k))) +gf9 (σ (neg9 (dx9 (vz9 A) (i , j , k))))
        ≡⟨ cong₂ _+gf9_
             (σ-dz-comm (vx9 A) (i , j , k))
             (trans (σ-neg (dx9 (vz9 A) (i , j , k)))
                    (cong neg9 (σ-dx-comm (vz9 A) (i , j , k)))) ⟩
      (dz9 (λ q → σ (vx9 A q)) (i , j , k)) +gf9 (neg9 (dx9 (λ q → σ (vz9 A q)) (i , j , k)))
        ≡⟨ refl ⟩
      (dz9 (vx9 (σVecField A)) (i , j , k)) +gf9 (neg9 (dx9 (vz9 (σVecField A)) (i , j , k))) ∎)
    -- z 分量
    (begin
      σ ((dx9 (vy9 A) (i , j , k)) +gf9 (neg9 (dy9 (vx9 A) (i , j , k))))
        ≡⟨ σ-add (dx9 (vy9 A) (i , j , k)) (neg9 (dy9 (vx9 A) (i , j , k))) ⟩
      (σ (dx9 (vy9 A) (i , j , k))) +gf9 (σ (neg9 (dy9 (vx9 A) (i , j , k))))
        ≡⟨ cong₂ _+gf9_
             (σ-dx-comm (vy9 A) (i , j , k))
             (trans (σ-neg (dy9 (vx9 A) (i , j , k)))
                    (cong neg9 (σ-dy-comm (vx9 A) (i , j , k)))) ⟩
      (dx9 (λ q → σ (vy9 A q)) (i , j , k)) +gf9 (neg9 (dy9 (λ q → σ (vx9 A q)) (i , j , k)))
        ≡⟨ refl ⟩
      (dx9 (vy9 (σVecField A)) (i , j , k)) +gf9 (neg9 (dy9 (vx9 (σVecField A)) (i , j , k))) ∎))

--------------------------------------------------------------------------------
-- §8. GF9 散度 与 σ-散度交换 (补全 σ 与空间运算交换)
--------------------------------------------------------------------------------

-- GF9 散度: div A = dx(vx) + (dy(vy) + dz(vz))  (右结合, 与 divT 一致)
div9 : GF9Vec → GF9Scal
div9 A p = (dx9 (vx9 A) p) +gf9 ((dy9 (vy9 A) p) +gf9 (dz9 (vz9 A) p))

-- σ 与散度交换: σ(div A) = div(σA)  (σ 是代数同态 + 与差分交换)
σ-div-comm : ∀ (A : GF9Vec) (p : Point) → σ (div9 A p) ≡ div9 (σVecField A) p
σ-div-comm A p = begin
  σ ((dx9 (vx9 A) p) +gf9 ((dy9 (vy9 A) p) +gf9 (dz9 (vz9 A) p)))
    ≡⟨ σ-add (dx9 (vx9 A) p) ((dy9 (vy9 A) p) +gf9 (dz9 (vz9 A) p)) ⟩
  (σ (dx9 (vx9 A) p)) +gf9 (σ ((dy9 (vy9 A) p) +gf9 (dz9 (vz9 A) p)))
    ≡⟨ cong ((σ (dx9 (vx9 A) p)) +gf9_) (σ-add (dy9 (vy9 A) p) (dz9 (vz9 A) p)) ⟩
  (σ (dx9 (vx9 A) p)) +gf9 ((σ (dy9 (vy9 A) p)) +gf9 (σ (dz9 (vz9 A) p)))
    ≡⟨ cong₂ _+gf9_
         (σ-dx-comm (vx9 A) p)
         (cong₂ _+gf9_ (σ-dy-comm (vy9 A) p) (σ-dz-comm (vz9 A) p)) ⟩
  (dx9 (λ q → σ (vx9 A q)) p) +gf9 ((dy9 (λ q → σ (vy9 A q)) p) +gf9 (dz9 (λ q → σ (vz9 A q)) p))
    ≡⟨ refl ⟩
  div9 (σVecField A) p ∎

--------------------------------------------------------------------------------
-- §9. 任务1 地基: Trit 负号对加法分配 (negate-⊕) + 差分交换律
--   div∘curl=0 的 GF(9) 版需要: negate-⊕ (负号分配) + 差分交换律
--   + 六项重排对消。本 § 先落第一块 negate-⊕ (全 case refl)。
--------------------------------------------------------------------------------

-- negate(x ⊕ y) ≡ negate x ⊕ negate y  (加法群同态, GF(3) 穷举 refl)
negate-⊕ : ∀ x y → negate (x ⊕ y) ≡ (negate x) ⊕ (negate y)
negate-⊕ T₀ y = refl
negate-⊕ T₁ T₀ = refl
negate-⊕ T₁ T₁ = refl
negate-⊕ T₁ T₂ = refl
negate-⊕ T₂ T₀ = refl
negate-⊕ T₂ T₁ = refl
negate-⊕ T₂ T₂ = refl

-- 内层引理: (negate a) ⊕ b ≡ negate (a ⊕ (negate b))  (差分方程求解内核)
innerT : ∀ a b → (negate a) ⊕ b ≡ negate (a ⊕ (negate b))
innerT a b = begin
  (negate a) ⊕ b
    ≡⟨ cong ((negate a) ⊕_) (sym (negate² b)) ⟩
  (negate a) ⊕ (negate (negate b))
    ≡⟨ sym (negate-⊕ a (negate b)) ⟩
  negate (a ⊕ (negate b)) ∎

-- 差分交换律: dyT ∘ dxT ≡ dxT ∘ dyT (类比 DiscreteEMField3D.dy-dx-comm)
dyT-dxT-comm : ∀ (φ : TritScal) (p : Point) → dyT (dxT φ) p ≡ dxT (dyT φ) p
dyT-dxT-comm φ (i , j , k) = begin
  dyT (dxT φ) (i , j , k)
    ≡⟨ refl ⟩
  (φ (nextT i , nextT j , k) ⊕ negate (φ (i , nextT j , k))) ⊕ negate (φ (nextT i , j , k) ⊕ negate (φ (i , j , k)))
    ≡⟨ cong ((φ (nextT i , nextT j , k) ⊕ negate (φ (i , nextT j , k))) ⊕_)
            (negate-⊕ (φ (nextT i , j , k)) (negate (φ (i , j , k)))) ⟩
  (φ (nextT i , nextT j , k) ⊕ negate (φ (i , nextT j , k))) ⊕ (negate (φ (nextT i , j , k)) ⊕ negate (negate (φ (i , j , k))))
    ≡⟨ cong (λ t → (φ (nextT i , nextT j , k) ⊕ negate (φ (i , nextT j , k))) ⊕ (negate (φ (nextT i , j , k)) ⊕ t))
            (negate² (φ (i , j , k))) ⟩
  (φ (nextT i , nextT j , k) ⊕ negate (φ (i , nextT j , k))) ⊕ (negate (φ (nextT i , j , k)) ⊕ φ (i , j , k))
    ≡⟨ sym (⊕-assoc (φ (nextT i , nextT j , k) ⊕ negate (φ (i , nextT j , k))) (negate (φ (nextT i , j , k))) (φ (i , j , k))) ⟩
  ((φ (nextT i , nextT j , k) ⊕ negate (φ (i , nextT j , k))) ⊕ negate (φ (nextT i , j , k))) ⊕ φ (i , j , k)
    ≡⟨ cong (λ t → t ⊕ φ (i , j , k))
            (trans (⊕-assoc (φ (nextT i , nextT j , k)) (negate (φ (i , nextT j , k))) (negate (φ (nextT i , j , k))))
                   (cong (φ (nextT i , nextT j , k) ⊕_) (⊕-comm (negate (φ (i , nextT j , k))) (negate (φ (nextT i , j , k)))))) ⟩
  (φ (nextT i , nextT j , k) ⊕ (negate (φ (nextT i , j , k)) ⊕ negate (φ (i , nextT j , k)))) ⊕ φ (i , j , k)
    ≡⟨ cong (λ t → t ⊕ φ (i , j , k))
            (sym (⊕-assoc (φ (nextT i , nextT j , k)) (negate (φ (nextT i , j , k))) (negate (φ (i , nextT j , k))))) ⟩
  ((φ (nextT i , nextT j , k) ⊕ negate (φ (nextT i , j , k))) ⊕ negate (φ (i , nextT j , k))) ⊕ φ (i , j , k)
    ≡⟨ ⊕-assoc (φ (nextT i , nextT j , k) ⊕ negate (φ (nextT i , j , k))) (negate (φ (i , nextT j , k))) (φ (i , j , k)) ⟩
  (φ (nextT i , nextT j , k) ⊕ negate (φ (nextT i , j , k))) ⊕ (negate (φ (i , nextT j , k)) ⊕ φ (i , j , k))
    ≡⟨ cong ((φ (nextT i , nextT j , k) ⊕ negate (φ (nextT i , j , k))) ⊕_)
            (innerT (φ (i , nextT j , k)) (φ (i , j , k))) ⟩
  (φ (nextT i , nextT j , k) ⊕ negate (φ (nextT i , j , k))) ⊕ negate (φ (i , nextT j , k) ⊕ negate (φ (i , j , k)))
    ≡⟨ refl ⟩
  dxT (dyT φ) (i , j , k) ∎

-- 差分交换律: dzT ∘ dyT ≡ dyT ∘ dzT (坐标轮换 j↔k)
dzT-dyT-comm : ∀ (φ : TritScal) (p : Point) → dzT (dyT φ) p ≡ dyT (dzT φ) p
dzT-dyT-comm φ (i , j , k) = begin
  dzT (dyT φ) (i , j , k)
    ≡⟨ refl ⟩
  (φ (i , nextT j , nextT k) ⊕ negate (φ (i , j , nextT k))) ⊕ negate (φ (i , nextT j , k) ⊕ negate (φ (i , j , k)))
    ≡⟨ cong ((φ (i , nextT j , nextT k) ⊕ negate (φ (i , j , nextT k))) ⊕_)
            (negate-⊕ (φ (i , nextT j , k)) (negate (φ (i , j , k)))) ⟩
  (φ (i , nextT j , nextT k) ⊕ negate (φ (i , j , nextT k))) ⊕ (negate (φ (i , nextT j , k)) ⊕ negate (negate (φ (i , j , k))))
    ≡⟨ cong (λ t → (φ (i , nextT j , nextT k) ⊕ negate (φ (i , j , nextT k))) ⊕ (negate (φ (i , nextT j , k)) ⊕ t))
            (negate² (φ (i , j , k))) ⟩
  (φ (i , nextT j , nextT k) ⊕ negate (φ (i , j , nextT k))) ⊕ (negate (φ (i , nextT j , k)) ⊕ φ (i , j , k))
    ≡⟨ sym (⊕-assoc (φ (i , nextT j , nextT k) ⊕ negate (φ (i , j , nextT k))) (negate (φ (i , nextT j , k))) (φ (i , j , k))) ⟩
  ((φ (i , nextT j , nextT k) ⊕ negate (φ (i , j , nextT k))) ⊕ negate (φ (i , nextT j , k))) ⊕ φ (i , j , k)
    ≡⟨ cong (λ t → t ⊕ φ (i , j , k))
            (trans (⊕-assoc (φ (i , nextT j , nextT k)) (negate (φ (i , j , nextT k))) (negate (φ (i , nextT j , k))))
                   (cong (φ (i , nextT j , nextT k) ⊕_) (⊕-comm (negate (φ (i , j , nextT k))) (negate (φ (i , nextT j , k)))))) ⟩
  (φ (i , nextT j , nextT k) ⊕ (negate (φ (i , nextT j , k)) ⊕ negate (φ (i , j , nextT k)))) ⊕ φ (i , j , k)
    ≡⟨ cong (λ t → t ⊕ φ (i , j , k))
            (sym (⊕-assoc (φ (i , nextT j , nextT k)) (negate (φ (i , nextT j , k))) (negate (φ (i , j , nextT k))))) ⟩
  ((φ (i , nextT j , nextT k) ⊕ negate (φ (i , nextT j , k))) ⊕ negate (φ (i , j , nextT k))) ⊕ φ (i , j , k)
    ≡⟨ ⊕-assoc (φ (i , nextT j , nextT k) ⊕ negate (φ (i , nextT j , k))) (negate (φ (i , j , nextT k))) (φ (i , j , k)) ⟩
  (φ (i , nextT j , nextT k) ⊕ negate (φ (i , nextT j , k))) ⊕ (negate (φ (i , j , nextT k)) ⊕ φ (i , j , k))
    ≡⟨ cong ((φ (i , nextT j , nextT k) ⊕ negate (φ (i , nextT j , k))) ⊕_)
            (innerT (φ (i , j , nextT k)) (φ (i , j , k))) ⟩
  (φ (i , nextT j , nextT k) ⊕ negate (φ (i , nextT j , k))) ⊕ negate (φ (i , j , nextT k) ⊕ negate (φ (i , j , k)))
    ≡⟨ refl ⟩
  dyT (dzT φ) (i , j , k) ∎

-- 差分交换律: dzT ∘ dxT ≡ dxT ∘ dzT (坐标轮换 i↔k)
dzT-dxT-comm : ∀ (φ : TritScal) (p : Point) → dzT (dxT φ) p ≡ dxT (dzT φ) p
dzT-dxT-comm φ (i , j , k) = begin
  dzT (dxT φ) (i , j , k)
    ≡⟨ refl ⟩
  (φ (nextT i , j , nextT k) ⊕ negate (φ (i , j , nextT k))) ⊕ negate (φ (nextT i , j , k) ⊕ negate (φ (i , j , k)))
    ≡⟨ cong ((φ (nextT i , j , nextT k) ⊕ negate (φ (i , j , nextT k))) ⊕_)
            (negate-⊕ (φ (nextT i , j , k)) (negate (φ (i , j , k)))) ⟩
  (φ (nextT i , j , nextT k) ⊕ negate (φ (i , j , nextT k))) ⊕ (negate (φ (nextT i , j , k)) ⊕ negate (negate (φ (i , j , k))))
    ≡⟨ cong (λ t → (φ (nextT i , j , nextT k) ⊕ negate (φ (i , j , nextT k))) ⊕ (negate (φ (nextT i , j , k)) ⊕ t))
            (negate² (φ (i , j , k))) ⟩
  (φ (nextT i , j , nextT k) ⊕ negate (φ (i , j , nextT k))) ⊕ (negate (φ (nextT i , j , k)) ⊕ φ (i , j , k))
    ≡⟨ sym (⊕-assoc (φ (nextT i , j , nextT k) ⊕ negate (φ (i , j , nextT k))) (negate (φ (nextT i , j , k))) (φ (i , j , k))) ⟩
  ((φ (nextT i , j , nextT k) ⊕ negate (φ (i , j , nextT k))) ⊕ negate (φ (nextT i , j , k))) ⊕ φ (i , j , k)
    ≡⟨ cong (λ t → t ⊕ φ (i , j , k))
            (trans (⊕-assoc (φ (nextT i , j , nextT k)) (negate (φ (i , j , nextT k))) (negate (φ (nextT i , j , k))))
                   (cong (φ (nextT i , j , nextT k) ⊕_) (⊕-comm (negate (φ (i , j , nextT k))) (negate (φ (nextT i , j , k)))))) ⟩
  (φ (nextT i , j , nextT k) ⊕ (negate (φ (nextT i , j , k)) ⊕ negate (φ (i , j , nextT k)))) ⊕ φ (i , j , k)
    ≡⟨ cong (λ t → t ⊕ φ (i , j , k))
            (sym (⊕-assoc (φ (nextT i , j , nextT k)) (negate (φ (nextT i , j , k))) (negate (φ (i , j , nextT k))))) ⟩
  ((φ (nextT i , j , nextT k) ⊕ negate (φ (nextT i , j , k))) ⊕ negate (φ (i , j , nextT k))) ⊕ φ (i , j , k)
    ≡⟨ ⊕-assoc (φ (nextT i , j , nextT k) ⊕ negate (φ (nextT i , j , k))) (negate (φ (i , j , nextT k))) (φ (i , j , k)) ⟩
  (φ (nextT i , j , nextT k) ⊕ negate (φ (nextT i , j , k))) ⊕ (negate (φ (i , j , nextT k)) ⊕ φ (i , j , k))
    ≡⟨ cong ((φ (nextT i , j , nextT k) ⊕ negate (φ (nextT i , j , k))) ⊕_)
            (innerT (φ (i , j , nextT k)) (φ (i , j , k))) ⟩
  (φ (nextT i , j , nextT k) ⊕ negate (φ (nextT i , j , k))) ⊕ negate (φ (i , j , nextT k) ⊕ negate (φ (i , j , k)))
    ≡⟨ refl ⟩
  dxT (dzT φ) (i , j , k) ∎

-- 差分可加性: dxT(φ⊕ψ) = dxT φ ⊕ dxT ψ (类比 DiscreteEMField3D.dx-add)
dxT-add : ∀ (φ ψ : TritScal) (p : Point) → dxT (λ q → (φ q) ⊕ (ψ q)) p ≡ (dxT φ p) ⊕ (dxT ψ p)
dxT-add φ ψ (i , j , k) = begin
  dxT (λ q → (φ q) ⊕ (ψ q)) (i , j , k)
    ≡⟨ refl ⟩
  ((φ (nextT i , j , k)) ⊕ (ψ (nextT i , j , k))) ⊕ negate ((φ (i , j , k)) ⊕ (ψ (i , j , k)))
    ≡⟨ cong (((φ (nextT i , j , k)) ⊕ (ψ (nextT i , j , k))) ⊕_)
            (negate-⊕ (φ (i , j , k)) (ψ (i , j , k))) ⟩
  ((φ (nextT i , j , k)) ⊕ (ψ (nextT i , j , k))) ⊕ ((negate (φ (i , j , k))) ⊕ (negate (ψ (i , j , k))))
    ≡⟨ ⊕-assoc (φ (nextT i , j , k)) (ψ (nextT i , j , k))
               ((negate (φ (i , j , k))) ⊕ (negate (ψ (i , j , k)))) ⟩
  (φ (nextT i , j , k)) ⊕ ((ψ (nextT i , j , k)) ⊕ ((negate (φ (i , j , k))) ⊕ (negate (ψ (i , j , k)))))
    ≡⟨ cong ((φ (nextT i , j , k)) ⊕_)
            (sym (⊕-assoc (ψ (nextT i , j , k)) (negate (φ (i , j , k))) (negate (ψ (i , j , k))))) ⟩
  (φ (nextT i , j , k)) ⊕ (((ψ (nextT i , j , k)) ⊕ (negate (φ (i , j , k)))) ⊕ (negate (ψ (i , j , k))))
    ≡⟨ cong ((φ (nextT i , j , k)) ⊕_)
            (cong (λ t → t ⊕ (negate (ψ (i , j , k))))
                  (⊕-comm (ψ (nextT i , j , k)) (negate (φ (i , j , k))))) ⟩
  (φ (nextT i , j , k)) ⊕ (((negate (φ (i , j , k))) ⊕ (ψ (nextT i , j , k))) ⊕ (negate (ψ (i , j , k))))
    ≡⟨ cong ((φ (nextT i , j , k)) ⊕_)
            (⊕-assoc (negate (φ (i , j , k))) (ψ (nextT i , j , k)) (negate (ψ (i , j , k)))) ⟩
  (φ (nextT i , j , k)) ⊕ ((negate (φ (i , j , k))) ⊕ ((ψ (nextT i , j , k)) ⊕ (negate (ψ (i , j , k)))))
    ≡⟨ sym (⊕-assoc (φ (nextT i , j , k)) (negate (φ (i , j , k)))
                    ((ψ (nextT i , j , k)) ⊕ (negate (ψ (i , j , k))))) ⟩
  ((φ (nextT i , j , k)) ⊕ (negate (φ (i , j , k)))) ⊕ ((ψ (nextT i , j , k)) ⊕ (negate (ψ (i , j , k))))
    ≡⟨ refl ⟩
  (dxT φ (i , j , k)) ⊕ (dxT ψ (i , j , k)) ∎

-- 差分负号: dxT(negate∘φ) = negate(dxT φ)  (negate-⊕ 直接落链)
dxT-neg : ∀ (φ : TritScal) (p : Point) → dxT (λ q → negate (φ q)) p ≡ negate (dxT φ p)
dxT-neg φ (i , j , k) = begin
  dxT (λ q → negate (φ q)) (i , j , k)
    ≡⟨ refl ⟩
  (negate (φ (nextT i , j , k))) ⊕ (negate (negate (φ (i , j , k))))
    ≡⟨ sym (negate-⊕ (φ (nextT i , j , k)) (negate (φ (i , j , k)))) ⟩
  negate ((φ (nextT i , j , k)) ⊕ (negate (φ (i , j , k))))
    ≡⟨ refl ⟩
  negate (dxT φ (i , j , k)) ∎

-- 成对对消: dxT(dyT f) - dyT(dxT f) = 0 (差分交换 + ⊕-inverse)
pair-cancel-1T : ∀ (f : TritScal) (p : Point) → (dxT (dyT f) p) ⊕ (negate (dyT (dxT f) p)) ≡ T₀
pair-cancel-1T f p = begin
  (dxT (dyT f) p) ⊕ (negate (dyT (dxT f) p))
    ≡⟨ cong (λ t → (dxT (dyT f) p) ⊕ (negate t)) (dyT-dxT-comm f p) ⟩
  (dxT (dyT f) p) ⊕ (negate (dxT (dyT f) p))
    ≡⟨ ⊕-inverse (dxT (dyT f) p) ⟩
  T₀ ∎

pair-cancel-2T : ∀ (f : TritScal) (p : Point) → (dyT (dzT f) p) ⊕ (negate (dzT (dyT f) p)) ≡ T₀
pair-cancel-2T f p = begin
  (dyT (dzT f) p) ⊕ (negate (dzT (dyT f) p))
    ≡⟨ cong (λ t → (dyT (dzT f) p) ⊕ (negate t)) (dzT-dyT-comm f p) ⟩
  (dyT (dzT f) p) ⊕ (negate (dyT (dzT f) p))
    ≡⟨ ⊕-inverse (dyT (dzT f) p) ⟩
  T₀ ∎

pair-cancel-3T : ∀ (f : TritScal) (p : Point) → (dzT (dxT f) p) ⊕ (negate (dxT (dzT f) p)) ≡ T₀
pair-cancel-3T f p = begin
  (dzT (dxT f) p) ⊕ (negate (dxT (dzT f) p))
    ≡⟨ cong (λ t → (dzT (dxT f) p) ⊕ (negate t)) (sym (dzT-dxT-comm f p)) ⟩
  (dzT (dxT f) p) ⊕ (negate (dzT (dxT f) p))
    ≡⟨ ⊕-inverse (dzT (dxT f) p) ⟩
  T₀ ∎

-- 成对换位: (x⊕y)⊕(z⊕w) ≡ (x⊕w)⊕(z⊕y) (类比 DiscreteEMCore.pair-swap)
pair-swapT : ∀ x y z w → (x ⊕ y) ⊕ (z ⊕ w) ≡ (x ⊕ w) ⊕ (z ⊕ y)
pair-swapT x y z w = begin
  (x ⊕ y) ⊕ (z ⊕ w)
    ≡⟨ sym (⊕-assoc (x ⊕ y) z w) ⟩
  ((x ⊕ y) ⊕ z) ⊕ w
    ≡⟨ cong (λ t → t ⊕ w) (⊕-assoc x y z) ⟩
  (x ⊕ (y ⊕ z)) ⊕ w
    ≡⟨ cong (λ t → t ⊕ w) (cong (x ⊕_) (⊕-comm y z)) ⟩
  (x ⊕ (z ⊕ y)) ⊕ w
    ≡⟨ cong (λ t → t ⊕ w) (sym (⊕-assoc x z y)) ⟩
  ((x ⊕ z) ⊕ y) ⊕ w
    ≡⟨ ⊕-assoc (x ⊕ z) y w ⟩
  (x ⊕ z) ⊕ (y ⊕ w)
    ≡⟨ cong ((x ⊕ z) ⊕_) (⊕-comm y w) ⟩
  (x ⊕ z) ⊕ (w ⊕ y)
    ≡⟨ sym (⊕-assoc (x ⊕ z) w y) ⟩
  ((x ⊕ z) ⊕ w) ⊕ y
    ≡⟨ cong (λ t → t ⊕ y) (⊕-assoc x z w) ⟩
  (x ⊕ (z ⊕ w)) ⊕ y
    ≡⟨ cong (λ t → t ⊕ y) (cong (x ⊕_) (⊕-comm z w)) ⟩
  (x ⊕ (w ⊕ z)) ⊕ y
    ≡⟨ cong (λ t → t ⊕ y) (sym (⊕-assoc x w z)) ⟩
  ((x ⊕ w) ⊕ z) ⊕ y
    ≡⟨ ⊕-assoc (x ⊕ w) z y ⟩
  (x ⊕ w) ⊕ (z ⊕ y) ∎

-- 六元素换位: (a⊕b)⊕((c⊕d)⊕(e⊕f)) ≡ (a⊕d)⊕((c⊕f)⊕(e⊕b)) (类比 DiscreteEMCore.six-rotate)
six-rotateT : ∀ a b c d e f →
  (a ⊕ b) ⊕ ((c ⊕ d) ⊕ (e ⊕ f)) ≡ (a ⊕ d) ⊕ ((c ⊕ f) ⊕ (e ⊕ b))
six-rotateT a b c d e f = begin
  (a ⊕ b) ⊕ ((c ⊕ d) ⊕ (e ⊕ f))
    ≡⟨ cong ((a ⊕ b) ⊕_) (pair-swapT c d e f) ⟩
  (a ⊕ b) ⊕ ((c ⊕ f) ⊕ (e ⊕ d))
    ≡⟨ sym (⊕-assoc (a ⊕ b) (c ⊕ f) (e ⊕ d)) ⟩
  ((a ⊕ b) ⊕ (c ⊕ f)) ⊕ (e ⊕ d)
    ≡⟨ pair-swapT (a ⊕ b) (c ⊕ f) e d ⟩
  ((a ⊕ b) ⊕ d) ⊕ (e ⊕ (c ⊕ f))
    ≡⟨ cong (λ t → t ⊕ (e ⊕ (c ⊕ f))) (⊕-assoc a b d) ⟩
  (a ⊕ (b ⊕ d)) ⊕ (e ⊕ (c ⊕ f))
    ≡⟨ cong (λ t → t ⊕ (e ⊕ (c ⊕ f))) (cong (a ⊕_) (⊕-comm b d)) ⟩
  (a ⊕ (d ⊕ b)) ⊕ (e ⊕ (c ⊕ f))
    ≡⟨ cong (λ t → t ⊕ (e ⊕ (c ⊕ f))) (sym (⊕-assoc a d b)) ⟩
  ((a ⊕ d) ⊕ b) ⊕ (e ⊕ (c ⊕ f))
    ≡⟨ ⊕-assoc (a ⊕ d) b (e ⊕ (c ⊕ f)) ⟩
  (a ⊕ d) ⊕ (b ⊕ (e ⊕ (c ⊕ f)))
    ≡⟨ cong ((a ⊕ d) ⊕_) (sym (⊕-assoc b e (c ⊕ f))) ⟩
  (a ⊕ d) ⊕ ((b ⊕ e) ⊕ (c ⊕ f))
    ≡⟨ cong ((a ⊕ d) ⊕_) (cong (λ t → t ⊕ (c ⊕ f)) (⊕-comm b e)) ⟩
  (a ⊕ d) ⊕ ((e ⊕ b) ⊕ (c ⊕ f))
    ≡⟨ cong ((a ⊕ d) ⊕_) (⊕-comm (e ⊕ b) (c ⊕ f)) ⟩
  (a ⊕ d) ⊕ ((c ⊕ f) ⊕ (e ⊕ b)) ∎

-- dyT/dzT 可加性 (坐标轮换 dxT-add)
dyT-add : ∀ (φ ψ : TritScal) (p : Point) → dyT (λ q → (φ q) ⊕ (ψ q)) p ≡ (dyT φ p) ⊕ (dyT ψ p)
dyT-add φ ψ (i , j , k) = begin
  dyT (λ q → (φ q) ⊕ (ψ q)) (i , j , k)
    ≡⟨ refl ⟩
  ((φ (i , nextT j , k)) ⊕ (ψ (i , nextT j , k))) ⊕ negate ((φ (i , j , k)) ⊕ (ψ (i , j , k)))
    ≡⟨ cong (((φ (i , nextT j , k)) ⊕ (ψ (i , nextT j , k))) ⊕_)
            (negate-⊕ (φ (i , j , k)) (ψ (i , j , k))) ⟩
  ((φ (i , nextT j , k)) ⊕ (ψ (i , nextT j , k))) ⊕ ((negate (φ (i , j , k))) ⊕ (negate (ψ (i , j , k))))
    ≡⟨ ⊕-assoc (φ (i , nextT j , k)) (ψ (i , nextT j , k))
               ((negate (φ (i , j , k))) ⊕ (negate (ψ (i , j , k)))) ⟩
  (φ (i , nextT j , k)) ⊕ ((ψ (i , nextT j , k)) ⊕ ((negate (φ (i , j , k))) ⊕ (negate (ψ (i , j , k)))))
    ≡⟨ cong ((φ (i , nextT j , k)) ⊕_)
            (sym (⊕-assoc (ψ (i , nextT j , k)) (negate (φ (i , j , k))) (negate (ψ (i , j , k))))) ⟩
  (φ (i , nextT j , k)) ⊕ (((ψ (i , nextT j , k)) ⊕ (negate (φ (i , j , k)))) ⊕ (negate (ψ (i , j , k))))
    ≡⟨ cong ((φ (i , nextT j , k)) ⊕_)
            (cong (λ t → t ⊕ (negate (ψ (i , j , k))))
                  (⊕-comm (ψ (i , nextT j , k)) (negate (φ (i , j , k))))) ⟩
  (φ (i , nextT j , k)) ⊕ (((negate (φ (i , j , k))) ⊕ (ψ (i , nextT j , k))) ⊕ (negate (ψ (i , j , k))))
    ≡⟨ cong ((φ (i , nextT j , k)) ⊕_)
            (⊕-assoc (negate (φ (i , j , k))) (ψ (i , nextT j , k)) (negate (ψ (i , j , k)))) ⟩
  (φ (i , nextT j , k)) ⊕ ((negate (φ (i , j , k))) ⊕ ((ψ (i , nextT j , k)) ⊕ (negate (ψ (i , j , k)))))
    ≡⟨ sym (⊕-assoc (φ (i , nextT j , k)) (negate (φ (i , j , k)))
                    ((ψ (i , nextT j , k)) ⊕ (negate (ψ (i , j , k))))) ⟩
  ((φ (i , nextT j , k)) ⊕ (negate (φ (i , j , k)))) ⊕ ((ψ (i , nextT j , k)) ⊕ (negate (ψ (i , j , k))))
    ≡⟨ refl ⟩
  (dyT φ (i , j , k)) ⊕ (dyT ψ (i , j , k)) ∎

dzT-add : ∀ (φ ψ : TritScal) (p : Point) → dzT (λ q → (φ q) ⊕ (ψ q)) p ≡ (dzT φ p) ⊕ (dzT ψ p)
dzT-add φ ψ (i , j , k) = begin
  dzT (λ q → (φ q) ⊕ (ψ q)) (i , j , k)
    ≡⟨ refl ⟩
  ((φ (i , j , nextT k)) ⊕ (ψ (i , j , nextT k))) ⊕ negate ((φ (i , j , k)) ⊕ (ψ (i , j , k)))
    ≡⟨ cong (((φ (i , j , nextT k)) ⊕ (ψ (i , j , nextT k))) ⊕_)
            (negate-⊕ (φ (i , j , k)) (ψ (i , j , k))) ⟩
  ((φ (i , j , nextT k)) ⊕ (ψ (i , j , nextT k))) ⊕ ((negate (φ (i , j , k))) ⊕ (negate (ψ (i , j , k))))
    ≡⟨ ⊕-assoc (φ (i , j , nextT k)) (ψ (i , j , nextT k))
               ((negate (φ (i , j , k))) ⊕ (negate (ψ (i , j , k)))) ⟩
  (φ (i , j , nextT k)) ⊕ ((ψ (i , j , nextT k)) ⊕ ((negate (φ (i , j , k))) ⊕ (negate (ψ (i , j , k)))))
    ≡⟨ cong ((φ (i , j , nextT k)) ⊕_)
            (sym (⊕-assoc (ψ (i , j , nextT k)) (negate (φ (i , j , k))) (negate (ψ (i , j , k))))) ⟩
  (φ (i , j , nextT k)) ⊕ (((ψ (i , j , nextT k)) ⊕ (negate (φ (i , j , k)))) ⊕ (negate (ψ (i , j , k))))
    ≡⟨ cong ((φ (i , j , nextT k)) ⊕_)
            (cong (λ t → t ⊕ (negate (ψ (i , j , k))))
                  (⊕-comm (ψ (i , j , nextT k)) (negate (φ (i , j , k))))) ⟩
  (φ (i , j , nextT k)) ⊕ (((negate (φ (i , j , k))) ⊕ (ψ (i , j , nextT k))) ⊕ (negate (ψ (i , j , k))))
    ≡⟨ cong ((φ (i , j , nextT k)) ⊕_)
            (⊕-assoc (negate (φ (i , j , k))) (ψ (i , j , nextT k)) (negate (ψ (i , j , k)))) ⟩
  (φ (i , j , nextT k)) ⊕ ((negate (φ (i , j , k))) ⊕ ((ψ (i , j , nextT k)) ⊕ (negate (ψ (i , j , k)))))
    ≡⟨ sym (⊕-assoc (φ (i , j , nextT k)) (negate (φ (i , j , k)))
                    ((ψ (i , j , nextT k)) ⊕ (negate (ψ (i , j , k))))) ⟩
  ((φ (i , j , nextT k)) ⊕ (negate (φ (i , j , k)))) ⊕ ((ψ (i , j , nextT k)) ⊕ (negate (ψ (i , j , k))))
    ≡⟨ refl ⟩
  (dzT φ (i , j , k)) ⊕ (dzT ψ (i , j , k)) ∎

-- dyT/dzT 负号 (坐标轮换 dxT-neg)
dyT-neg : ∀ (φ : TritScal) (p : Point) → dyT (λ q → negate (φ q)) p ≡ negate (dyT φ p)
dyT-neg φ (i , j , k) = begin
  dyT (λ q → negate (φ q)) (i , j , k)
    ≡⟨ refl ⟩
  (negate (φ (i , nextT j , k))) ⊕ (negate (negate (φ (i , j , k))))
    ≡⟨ sym (negate-⊕ (φ (i , nextT j , k)) (negate (φ (i , j , k)))) ⟩
  negate ((φ (i , nextT j , k)) ⊕ (negate (φ (i , j , k))))
    ≡⟨ refl ⟩
  negate (dyT φ (i , j , k)) ∎

dzT-neg : ∀ (φ : TritScal) (p : Point) → dzT (λ q → negate (φ q)) p ≡ negate (dzT φ p)
dzT-neg φ (i , j , k) = begin
  dzT (λ q → negate (φ q)) (i , j , k)
    ≡⟨ refl ⟩
  (negate (φ (i , j , nextT k))) ⊕ (negate (negate (φ (i , j , k))))
    ≡⟨ sym (negate-⊕ (φ (i , j , nextT k)) (negate (φ (i , j , k)))) ⟩
  negate ((φ (i , j , nextT k)) ⊕ (negate (φ (i , j , k))))
    ≡⟨ refl ⟩
  negate (dzT φ (i , j , k)) ∎

-- Trit 散度: div A = dx(vx) + (dy(vy) + dz(vz))
divT : TritVec → TritScal
divT A p = (dxT (vxT A) p) ⊕ ((dyT (vyT A) p) ⊕ (dzT (vzT A) p))

-- 核心: div∘curl = 0 (Trit 版, 类比 DiscreteEMCore.div-curl-zero)
div-curl-zero-Trit : ∀ (A : TritVec) (p : Point) → divT (curlT A) p ≡ T₀
div-curl-zero-Trit A (i , j , k) = begin
  divT (curlT A) (i , j , k)
    ≡⟨ refl ⟩
  (dxT (λ q → (dyT (vzT A) q) ⊕ (negate (dzT (vyT A) q))) (i , j , k)) ⊕
    ((dyT (λ q → (dzT (vxT A) q) ⊕ (negate (dxT (vzT A) q))) (i , j , k)) ⊕
     (dzT (λ q → (dxT (vyT A) q) ⊕ (negate (dyT (vxT A) q))) (i , j , k)))
    ≡⟨ cong₂ _⊕_
         (dxT-add (dyT (vzT A)) (λ q → negate (dzT (vyT A) q)) (i , j , k))
         (cong₂ _⊕_
           (dyT-add (dzT (vxT A)) (λ q → negate (dxT (vzT A) q)) (i , j , k))
           (dzT-add (dxT (vyT A)) (λ q → negate (dyT (vxT A) q)) (i , j , k))) ⟩
  ((dxT (dyT (vzT A)) (i , j , k)) ⊕ (dxT (λ q → negate (dzT (vyT A) q)) (i , j , k))) ⊕
    (((dyT (dzT (vxT A)) (i , j , k)) ⊕ (dyT (λ q → negate (dxT (vzT A) q)) (i , j , k))) ⊕
     ((dzT (dxT (vyT A)) (i , j , k)) ⊕ (dzT (λ q → negate (dyT (vxT A) q)) (i , j , k))))
    ≡⟨ cong₂ _⊕_
         (cong ((dxT (dyT (vzT A)) (i , j , k)) ⊕_) (dxT-neg (dzT (vyT A)) (i , j , k)))
         (cong₂ _⊕_
           (cong ((dyT (dzT (vxT A)) (i , j , k)) ⊕_) (dyT-neg (dxT (vzT A)) (i , j , k)))
           (cong ((dzT (dxT (vyT A)) (i , j , k)) ⊕_) (dzT-neg (dyT (vxT A)) (i , j , k)))) ⟩
  ((dxT (dyT (vzT A)) (i , j , k)) ⊕ (negate (dxT (dzT (vyT A)) (i , j , k)))) ⊕
    (((dyT (dzT (vxT A)) (i , j , k)) ⊕ (negate (dyT (dxT (vzT A)) (i , j , k)))) ⊕
     ((dzT (dxT (vyT A)) (i , j , k)) ⊕ (negate (dzT (dyT (vxT A)) (i , j , k)))))
    ≡⟨ six-rotateT (dxT (dyT (vzT A)) (i , j , k)) (negate (dxT (dzT (vyT A)) (i , j , k)))
                   (dyT (dzT (vxT A)) (i , j , k)) (negate (dyT (dxT (vzT A)) (i , j , k)))
                   (dzT (dxT (vyT A)) (i , j , k)) (negate (dzT (dyT (vxT A)) (i , j , k))) ⟩
  ((dxT (dyT (vzT A)) (i , j , k)) ⊕ (negate (dyT (dxT (vzT A)) (i , j , k)))) ⊕
    (((dyT (dzT (vxT A)) (i , j , k)) ⊕ (negate (dzT (dyT (vxT A)) (i , j , k)))) ⊕
     ((dzT (dxT (vyT A)) (i , j , k)) ⊕ (negate (dxT (dzT (vyT A)) (i , j , k)))))
    ≡⟨ cong₂ _⊕_
         (pair-cancel-1T (vzT A) (i , j , k))
         (cong₂ _⊕_ (pair-cancel-2T (vxT A) (i , j , k)) (pair-cancel-3T (vyT A) (i , j , k))) ⟩
  T₀ ⊕ (T₀ ⊕ T₀)
    ≡⟨ refl ⟩
  T₀ ∎

--------------------------------------------------------------------------------
-- §10. div∘curl = 0 的 GF(9) 版本 (分量降维到 Trit 版)
--------------------------------------------------------------------------------

-- GF9 零元
zero9 : GF9
zero9 = (T₀ , T₀)

-- re/im 与 div9 交换 (div9 分量式, definitional refl)
re-div9 : ∀ (A : GF9Vec) (p : Point) → re (div9 A p) ≡ divT (realVec A) p
re-div9 A p = refl

im-div9 : ∀ (A : GF9Vec) (p : Point) → im (div9 A p) ≡ divT (imagVec A) p
im-div9 A p = refl

-- div∘curl = 0: div9(curl9std A) = zero9 (实部/虚部各自降维到 div-curl-zero-Trit)
div-curl-zero-GF9 : ∀ (A : GF9Vec) (p : Point) → div9 (curl9std A) p ≡ zero9
div-curl-zero-GF9 A p = begin
  div9 (curl9std A) p
    ≡⟨ cong₂ _,_ (re-div9 (curl9std A) p) (im-div9 (curl9std A) p) ⟩
  (divT (realVec (curl9std A)) p , divT (imagVec (curl9std A)) p)
    ≡⟨ refl ⟩
  (divT (curlT (realVec A)) p , divT (curlT (imagVec A)) p)
    ≡⟨ cong₂ _,_ (div-curl-zero-Trit (realVec A) p) (div-curl-zero-Trit (imagVec A) p) ⟩
  (T₀ , T₀) ∎

--------------------------------------------------------------------------------
-- §11. GF9 代数 + 差分线性 (电荷守恒的前置)
--------------------------------------------------------------------------------

+gf9-assoc : ∀ x y z → (x +gf9 y) +gf9 z ≡ x +gf9 (y +gf9 z)
+gf9-assoc (a , b) (c , d) (e , f) = cong₂ _,_ (⊕-assoc a c e) (⊕-assoc b d f)

+gf9-comm : ∀ x y → x +gf9 y ≡ y +gf9 x
+gf9-comm (a , b) (c , d) = cong₂ _,_ (⊕-comm a c) (⊕-comm b d)

+gf9-identityˡ : ∀ x → zero9 +gf9 x ≡ x
+gf9-identityˡ (a , b) = cong₂ _,_ (⊕-identityˡ a) (⊕-identityˡ b)

neg9-add9 : ∀ x y → neg9 (x +gf9 y) ≡ (neg9 x) +gf9 (neg9 y)
neg9-add9 (a , b) (c , d) = cong₂ _,_ (negate-⊕ a c) (negate-⊕ b d)

-- GF9 差分可加性 dx9(φ+ψ) = dx9 φ + dx9 ψ (类比 dxT-add)
dx9-add : ∀ (φ ψ : GF9Scal) (p : Point) → dx9 (λ q → (φ q) +gf9 (ψ q)) p ≡ (dx9 φ p) +gf9 (dx9 ψ p)
dx9-add φ ψ (i , j , k) = begin
  dx9 (λ q → (φ q) +gf9 (ψ q)) (i , j , k)
    ≡⟨ refl ⟩
  ((φ (nextT i , j , k)) +gf9 (ψ (nextT i , j , k))) +gf9 neg9 ((φ (i , j , k)) +gf9 (ψ (i , j , k)))
    ≡⟨ cong (((φ (nextT i , j , k)) +gf9 (ψ (nextT i , j , k))) +gf9_)
            (neg9-add9 (φ (i , j , k)) (ψ (i , j , k))) ⟩
  ((φ (nextT i , j , k)) +gf9 (ψ (nextT i , j , k))) +gf9 ((neg9 (φ (i , j , k))) +gf9 (neg9 (ψ (i , j , k))))
    ≡⟨ +gf9-assoc (φ (nextT i , j , k)) (ψ (nextT i , j , k)) ((neg9 (φ (i , j , k))) +gf9 (neg9 (ψ (i , j , k)))) ⟩
  (φ (nextT i , j , k)) +gf9 ((ψ (nextT i , j , k)) +gf9 ((neg9 (φ (i , j , k))) +gf9 (neg9 (ψ (i , j , k)))))
    ≡⟨ cong ((φ (nextT i , j , k)) +gf9_)
            (sym (+gf9-assoc (ψ (nextT i , j , k)) (neg9 (φ (i , j , k))) (neg9 (ψ (i , j , k))))) ⟩
  (φ (nextT i , j , k)) +gf9 (((ψ (nextT i , j , k)) +gf9 (neg9 (φ (i , j , k)))) +gf9 (neg9 (ψ (i , j , k))))
    ≡⟨ cong ((φ (nextT i , j , k)) +gf9_)
            (cong (λ t → t +gf9 (neg9 (ψ (i , j , k))))
                  (+gf9-comm (ψ (nextT i , j , k)) (neg9 (φ (i , j , k))))) ⟩
  (φ (nextT i , j , k)) +gf9 (((neg9 (φ (i , j , k))) +gf9 (ψ (nextT i , j , k))) +gf9 (neg9 (ψ (i , j , k))))
    ≡⟨ cong ((φ (nextT i , j , k)) +gf9_)
            (+gf9-assoc (neg9 (φ (i , j , k))) (ψ (nextT i , j , k)) (neg9 (ψ (i , j , k)))) ⟩
  (φ (nextT i , j , k)) +gf9 ((neg9 (φ (i , j , k))) +gf9 ((ψ (nextT i , j , k)) +gf9 (neg9 (ψ (i , j , k)))))
    ≡⟨ sym (+gf9-assoc (φ (nextT i , j , k)) (neg9 (φ (i , j , k))) ((ψ (nextT i , j , k)) +gf9 (neg9 (ψ (i , j , k))))) ⟩
  ((φ (nextT i , j , k)) +gf9 (neg9 (φ (i , j , k)))) +gf9 ((ψ (nextT i , j , k)) +gf9 (neg9 (ψ (i , j , k))))
    ≡⟨ refl ⟩
  (dx9 φ (i , j , k)) +gf9 (dx9 ψ (i , j , k)) ∎

dy9-add : ∀ (φ ψ : GF9Scal) (p : Point) → dy9 (λ q → (φ q) +gf9 (ψ q)) p ≡ (dy9 φ p) +gf9 (dy9 ψ p)
dy9-add φ ψ (i , j , k) = begin
  dy9 (λ q → (φ q) +gf9 (ψ q)) (i , j , k)
    ≡⟨ refl ⟩
  ((φ (i , nextT j , k)) +gf9 (ψ (i , nextT j , k))) +gf9 neg9 ((φ (i , j , k)) +gf9 (ψ (i , j , k)))
    ≡⟨ cong (((φ (i , nextT j , k)) +gf9 (ψ (i , nextT j , k))) +gf9_)
            (neg9-add9 (φ (i , j , k)) (ψ (i , j , k))) ⟩
  ((φ (i , nextT j , k)) +gf9 (ψ (i , nextT j , k))) +gf9 ((neg9 (φ (i , j , k))) +gf9 (neg9 (ψ (i , j , k))))
    ≡⟨ +gf9-assoc (φ (i , nextT j , k)) (ψ (i , nextT j , k)) ((neg9 (φ (i , j , k))) +gf9 (neg9 (ψ (i , j , k)))) ⟩
  (φ (i , nextT j , k)) +gf9 ((ψ (i , nextT j , k)) +gf9 ((neg9 (φ (i , j , k))) +gf9 (neg9 (ψ (i , j , k)))))
    ≡⟨ cong ((φ (i , nextT j , k)) +gf9_)
            (sym (+gf9-assoc (ψ (i , nextT j , k)) (neg9 (φ (i , j , k))) (neg9 (ψ (i , j , k))))) ⟩
  (φ (i , nextT j , k)) +gf9 (((ψ (i , nextT j , k)) +gf9 (neg9 (φ (i , j , k)))) +gf9 (neg9 (ψ (i , j , k))))
    ≡⟨ cong ((φ (i , nextT j , k)) +gf9_)
            (cong (λ t → t +gf9 (neg9 (ψ (i , j , k))))
                  (+gf9-comm (ψ (i , nextT j , k)) (neg9 (φ (i , j , k))))) ⟩
  (φ (i , nextT j , k)) +gf9 (((neg9 (φ (i , j , k))) +gf9 (ψ (i , nextT j , k))) +gf9 (neg9 (ψ (i , j , k))))
    ≡⟨ cong ((φ (i , nextT j , k)) +gf9_)
            (+gf9-assoc (neg9 (φ (i , j , k))) (ψ (i , nextT j , k)) (neg9 (ψ (i , j , k)))) ⟩
  (φ (i , nextT j , k)) +gf9 ((neg9 (φ (i , j , k))) +gf9 ((ψ (i , nextT j , k)) +gf9 (neg9 (ψ (i , j , k)))))
    ≡⟨ sym (+gf9-assoc (φ (i , nextT j , k)) (neg9 (φ (i , j , k))) ((ψ (i , nextT j , k)) +gf9 (neg9 (ψ (i , j , k))))) ⟩
  ((φ (i , nextT j , k)) +gf9 (neg9 (φ (i , j , k)))) +gf9 ((ψ (i , nextT j , k)) +gf9 (neg9 (ψ (i , j , k))))
    ≡⟨ refl ⟩
  (dy9 φ (i , j , k)) +gf9 (dy9 ψ (i , j , k)) ∎

dz9-add : ∀ (φ ψ : GF9Scal) (p : Point) → dz9 (λ q → (φ q) +gf9 (ψ q)) p ≡ (dz9 φ p) +gf9 (dz9 ψ p)
dz9-add φ ψ (i , j , k) = begin
  dz9 (λ q → (φ q) +gf9 (ψ q)) (i , j , k)
    ≡⟨ refl ⟩
  ((φ (i , j , nextT k)) +gf9 (ψ (i , j , nextT k))) +gf9 neg9 ((φ (i , j , k)) +gf9 (ψ (i , j , k)))
    ≡⟨ cong (((φ (i , j , nextT k)) +gf9 (ψ (i , j , nextT k))) +gf9_)
            (neg9-add9 (φ (i , j , k)) (ψ (i , j , k))) ⟩
  ((φ (i , j , nextT k)) +gf9 (ψ (i , j , nextT k))) +gf9 ((neg9 (φ (i , j , k))) +gf9 (neg9 (ψ (i , j , k))))
    ≡⟨ +gf9-assoc (φ (i , j , nextT k)) (ψ (i , j , nextT k)) ((neg9 (φ (i , j , k))) +gf9 (neg9 (ψ (i , j , k)))) ⟩
  (φ (i , j , nextT k)) +gf9 ((ψ (i , j , nextT k)) +gf9 ((neg9 (φ (i , j , k))) +gf9 (neg9 (ψ (i , j , k)))))
    ≡⟨ cong ((φ (i , j , nextT k)) +gf9_)
            (sym (+gf9-assoc (ψ (i , j , nextT k)) (neg9 (φ (i , j , k))) (neg9 (ψ (i , j , k))))) ⟩
  (φ (i , j , nextT k)) +gf9 (((ψ (i , j , nextT k)) +gf9 (neg9 (φ (i , j , k)))) +gf9 (neg9 (ψ (i , j , k))))
    ≡⟨ cong ((φ (i , j , nextT k)) +gf9_)
            (cong (λ t → t +gf9 (neg9 (ψ (i , j , k))))
                  (+gf9-comm (ψ (i , j , nextT k)) (neg9 (φ (i , j , k))))) ⟩
  (φ (i , j , nextT k)) +gf9 (((neg9 (φ (i , j , k))) +gf9 (ψ (i , j , nextT k))) +gf9 (neg9 (ψ (i , j , k))))
    ≡⟨ cong ((φ (i , j , nextT k)) +gf9_)
            (+gf9-assoc (neg9 (φ (i , j , k))) (ψ (i , j , nextT k)) (neg9 (ψ (i , j , k)))) ⟩
  (φ (i , j , nextT k)) +gf9 ((neg9 (φ (i , j , k))) +gf9 ((ψ (i , j , nextT k)) +gf9 (neg9 (ψ (i , j , k)))))
    ≡⟨ sym (+gf9-assoc (φ (i , j , nextT k)) (neg9 (φ (i , j , k))) ((ψ (i , j , nextT k)) +gf9 (neg9 (ψ (i , j , k))))) ⟩
  ((φ (i , j , nextT k)) +gf9 (neg9 (φ (i , j , k)))) +gf9 ((ψ (i , j , nextT k)) +gf9 (neg9 (ψ (i , j , k))))
    ≡⟨ refl ⟩
  (dz9 φ (i , j , k)) +gf9 (dz9 ψ (i , j , k)) ∎

-- GF9 差分负号 dx9(neg9∘φ) = neg9(dx9 φ)
dx9-neg : ∀ (φ : GF9Scal) (p : Point) → dx9 (λ q → neg9 (φ q)) p ≡ neg9 (dx9 φ p)
dx9-neg φ (i , j , k) = begin
  dx9 (λ q → neg9 (φ q)) (i , j , k)
    ≡⟨ refl ⟩
  (neg9 (φ (nextT i , j , k))) +gf9 (neg9 (neg9 (φ (i , j , k))))
    ≡⟨ sym (neg9-add9 (φ (nextT i , j , k)) (neg9 (φ (i , j , k)))) ⟩
  neg9 ((φ (nextT i , j , k)) +gf9 (neg9 (φ (i , j , k))))
    ≡⟨ refl ⟩
  neg9 (dx9 φ (i , j , k)) ∎

dy9-neg : ∀ (φ : GF9Scal) (p : Point) → dy9 (λ q → neg9 (φ q)) p ≡ neg9 (dy9 φ p)
dy9-neg φ (i , j , k) = begin
  dy9 (λ q → neg9 (φ q)) (i , j , k)
    ≡⟨ refl ⟩
  (neg9 (φ (i , nextT j , k))) +gf9 (neg9 (neg9 (φ (i , j , k))))
    ≡⟨ sym (neg9-add9 (φ (i , nextT j , k)) (neg9 (φ (i , j , k)))) ⟩
  neg9 ((φ (i , nextT j , k)) +gf9 (neg9 (φ (i , j , k))))
    ≡⟨ refl ⟩
  neg9 (dy9 φ (i , j , k)) ∎

dz9-neg : ∀ (φ : GF9Scal) (p : Point) → dz9 (λ q → neg9 (φ q)) p ≡ neg9 (dz9 φ p)
dz9-neg φ (i , j , k) = begin
  dz9 (λ q → neg9 (φ q)) (i , j , k)
    ≡⟨ refl ⟩
  (neg9 (φ (i , j , nextT k))) +gf9 (neg9 (neg9 (φ (i , j , k))))
    ≡⟨ sym (neg9-add9 (φ (i , j , nextT k)) (neg9 (φ (i , j , k)))) ⟩
  neg9 ((φ (i , j , nextT k)) +gf9 (neg9 (φ (i , j , k))))
    ≡⟨ refl ⟩
  neg9 (dz9 φ (i , j , k)) ∎

--------------------------------------------------------------------------------
-- §12. 散度线性 + 电荷守恒 (方案2)
--------------------------------------------------------------------------------

-- 四元素换位: (x+y)+(z+w) ≡ (x+z)+(y+w) (类比 DiscreteEMCore.shuffle22)
shuffle22-9 : ∀ x y z w → (x +gf9 y) +gf9 (z +gf9 w) ≡ (x +gf9 z) +gf9 (y +gf9 w)
shuffle22-9 x y z w = begin
  (x +gf9 y) +gf9 (z +gf9 w)
    ≡⟨ sym (+gf9-assoc (x +gf9 y) z w) ⟩
  ((x +gf9 y) +gf9 z) +gf9 w
    ≡⟨ cong (λ t → t +gf9 w) (+gf9-assoc x y z) ⟩
  (x +gf9 (y +gf9 z)) +gf9 w
    ≡⟨ cong (λ t → t +gf9 w) (cong (x +gf9_) (+gf9-comm y z)) ⟩
  (x +gf9 (z +gf9 y)) +gf9 w
    ≡⟨ cong (λ t → t +gf9 w) (sym (+gf9-assoc x z y)) ⟩
  ((x +gf9 z) +gf9 y) +gf9 w
    ≡⟨ +gf9-assoc (x +gf9 z) y w ⟩
  (x +gf9 z) +gf9 (y +gf9 w) ∎

-- 六项 33 归并: (a+b)+((c+d)+(e+f)) ≡ (a+(c+e))+(b+(d+f)) (类比 div-rearrange)
div9-rearrange9 : ∀ a b c d e f →
  (a +gf9 b) +gf9 ((c +gf9 d) +gf9 (e +gf9 f))
    ≡ (a +gf9 (c +gf9 e)) +gf9 (b +gf9 (d +gf9 f))
div9-rearrange9 a b c d e f = begin
  (a +gf9 b) +gf9 ((c +gf9 d) +gf9 (e +gf9 f))
    ≡⟨ sym (+gf9-assoc (a +gf9 b) (c +gf9 d) (e +gf9 f)) ⟩
  ((a +gf9 b) +gf9 (c +gf9 d)) +gf9 (e +gf9 f)
    ≡⟨ shuffle22-9 (a +gf9 b) (c +gf9 d) e f ⟩
  ((a +gf9 b) +gf9 e) +gf9 ((c +gf9 d) +gf9 f)
    ≡⟨ cong (λ t → t +gf9 ((c +gf9 d) +gf9 f)) (+gf9-assoc a b e) ⟩
  (a +gf9 (b +gf9 e)) +gf9 ((c +gf9 d) +gf9 f)
    ≡⟨ cong (λ t → t +gf9 ((c +gf9 d) +gf9 f)) (cong (a +gf9_) (+gf9-comm b e)) ⟩
  (a +gf9 (e +gf9 b)) +gf9 ((c +gf9 d) +gf9 f)
    ≡⟨ cong (λ t → t +gf9 ((c +gf9 d) +gf9 f)) (sym (+gf9-assoc a e b)) ⟩
  ((a +gf9 e) +gf9 b) +gf9 ((c +gf9 d) +gf9 f)
    ≡⟨ +gf9-assoc (a +gf9 e) b ((c +gf9 d) +gf9 f) ⟩
  (a +gf9 e) +gf9 (b +gf9 ((c +gf9 d) +gf9 f))
    ≡⟨ cong ((a +gf9 e) +gf9_) (sym (+gf9-assoc b (c +gf9 d) f)) ⟩
  (a +gf9 e) +gf9 ((b +gf9 (c +gf9 d)) +gf9 f)
    ≡⟨ cong ((a +gf9 e) +gf9_) (cong (λ t → t +gf9 f) (sym (+gf9-assoc b c d))) ⟩
  (a +gf9 e) +gf9 (((b +gf9 c) +gf9 d) +gf9 f)
    ≡⟨ cong ((a +gf9 e) +gf9_) (cong (λ t → t +gf9 f) (cong (λ u → u +gf9 d) (+gf9-comm b c))) ⟩
  (a +gf9 e) +gf9 (((c +gf9 b) +gf9 d) +gf9 f)
    ≡⟨ cong ((a +gf9 e) +gf9_) (cong (λ t → t +gf9 f) (+gf9-assoc c b d)) ⟩
  (a +gf9 e) +gf9 ((c +gf9 (b +gf9 d)) +gf9 f)
    ≡⟨ cong ((a +gf9 e) +gf9_) (+gf9-assoc c (b +gf9 d) f) ⟩
  (a +gf9 e) +gf9 (c +gf9 ((b +gf9 d) +gf9 f))
    ≡⟨ cong ((a +gf9 e) +gf9_) (cong (c +gf9_) (+gf9-assoc b d f)) ⟩
  (a +gf9 e) +gf9 (c +gf9 (b +gf9 (d +gf9 f)))
    ≡⟨ sym (+gf9-assoc (a +gf9 e) c (b +gf9 (d +gf9 f))) ⟩
  ((a +gf9 e) +gf9 c) +gf9 (b +gf9 (d +gf9 f))
    ≡⟨ cong (λ t → t +gf9 (b +gf9 (d +gf9 f))) (+gf9-assoc a e c) ⟩
  (a +gf9 (e +gf9 c)) +gf9 (b +gf9 (d +gf9 f))
    ≡⟨ cong (λ t → t +gf9 (b +gf9 (d +gf9 f))) (cong (a +gf9_) (+gf9-comm e c)) ⟩
  (a +gf9 (c +gf9 e)) +gf9 (b +gf9 (d +gf9 f)) ∎

-- 散度线性: div9(A+B) = div9 A + div9 B
div9-add : ∀ (A B : GF9Vec) (p : Point) →
  div9 (λ q → addVec9 (A q) (B q)) p ≡ (div9 A p) +gf9 (div9 B p)
div9-add A B p = begin
  div9 (λ q → addVec9 (A q) (B q)) p
    ≡⟨ refl ⟩
  (dx9 (λ q → (vx9 A q) +gf9 (vx9 B q)) p) +gf9
    ((dy9 (λ q → (vy9 A q) +gf9 (vy9 B q)) p) +gf9
     (dz9 (λ q → (vz9 A q) +gf9 (vz9 B q)) p))
    ≡⟨ cong₂ _+gf9_
         (dx9-add (vx9 A) (vx9 B) p)
         (cong₂ _+gf9_ (dy9-add (vy9 A) (vy9 B) p) (dz9-add (vz9 A) (vz9 B) p)) ⟩
  ((dx9 (vx9 A) p) +gf9 (dx9 (vx9 B) p)) +gf9
    (((dy9 (vy9 A) p) +gf9 (dy9 (vy9 B) p)) +gf9
     ((dz9 (vz9 A) p) +gf9 (dz9 (vz9 B) p)))
    ≡⟨ div9-rearrange9 (dx9 (vx9 A) p) (dx9 (vx9 B) p)
                       (dy9 (vy9 A) p) (dy9 (vy9 B) p)
                       (dz9 (vz9 A) p) (dz9 (vz9 B) p) ⟩
  ((dx9 (vx9 A) p) +gf9 ((dy9 (vy9 A) p) +gf9 (dz9 (vz9 A) p))) +gf9
    ((dx9 (vx9 B) p) +gf9 ((dy9 (vy9 B) p) +gf9 (dz9 (vz9 B) p)))
    ≡⟨ refl ⟩
  (div9 A p) +gf9 (div9 B p) ∎

-- 散度负号: div9(-A) = -div9 A
div9-neg : ∀ (A : GF9Vec) (p : Point) →
  div9 (λ q → negVec9 (A q)) p ≡ neg9 (div9 A p)
div9-neg A p = begin
  div9 (λ q → negVec9 (A q)) p
    ≡⟨ refl ⟩
  (dx9 (λ q → neg9 (vx9 A q)) p) +gf9
    ((dy9 (λ q → neg9 (vy9 A q)) p) +gf9
     (dz9 (λ q → neg9 (vz9 A q)) p))
    ≡⟨ cong₂ _+gf9_
         (dx9-neg (vx9 A) p)
         (cong₂ _+gf9_ (dy9-neg (vy9 A) p) (dz9-neg (vz9 A) p)) ⟩
  (neg9 (dx9 (vx9 A) p)) +gf9
    ((neg9 (dy9 (vy9 A) p)) +gf9 (neg9 (dz9 (vz9 A) p)))
    ≡⟨ sym (cong ((neg9 (dx9 (vx9 A) p)) +gf9_)
            (neg9-add9 (dy9 (vy9 A) p) (dz9 (vz9 A) p))) ⟩
  (neg9 (dx9 (vx9 A) p)) +gf9 (neg9 ((dy9 (vy9 A) p) +gf9 (dz9 (vz9 A) p)))
    ≡⟨ sym (neg9-add9 (dx9 (vx9 A) p) ((dy9 (vy9 A) p) +gf9 (dz9 (vz9 A) p))) ⟩
  neg9 ((dx9 (vx9 A) p) +gf9 ((dy9 (vy9 A) p) +gf9 (dz9 (vz9 A) p)))
    ≡⟨ refl ⟩
  neg9 (div9 A p) ∎

--------------------------------------------------------------------------------
-- §13. 电荷守恒 (统一 Maxwell 取散度, 方案2)
--------------------------------------------------------------------------------

-- neg9 三项分配: (neg9 x) + ((neg9 y) + (neg9 z)) ≡ neg9 (x + (y + z))
neg9-add9-3 : ∀ x y z → (neg9 x) +gf9 ((neg9 y) +gf9 (neg9 z)) ≡ neg9 (x +gf9 (y +gf9 z))
neg9-add9-3 x y z = begin
  (neg9 x) +gf9 ((neg9 y) +gf9 (neg9 z))
    ≡⟨ sym (cong ((neg9 x) +gf9_) (neg9-add9 y z)) ⟩
  (neg9 x) +gf9 (neg9 (y +gf9 z))
    ≡⟨ sym (neg9-add9 x (y +gf9 z)) ⟩
  neg9 (x +gf9 (y +gf9 z)) ∎

-- Trit 散度负号: divT(negVecT∘A) = negate(divT A)
divT-neg : ∀ (A : TritVec) (p : Point) → divT (λ q → negVecT (A q)) p ≡ negate (divT A p)
divT-neg A p = begin
  divT (λ q → negVecT (A q)) p
    ≡⟨ refl ⟩
  (dxT (λ q → negate (vxT A q)) p) ⊕ ((dyT (λ q → negate (vyT A q)) p) ⊕ (dzT (λ q → negate (vzT A q)) p))
    ≡⟨ cong₂ _⊕_
         (dxT-neg (vxT A) p)
         (cong₂ _⊕_ (dyT-neg (vyT A) p) (dzT-neg (vzT A) p)) ⟩
  (negate (dxT (vxT A) p)) ⊕ ((negate (dyT (vyT A) p)) ⊕ (negate (dzT (vzT A) p)))
    ≡⟨ sym (cong ((negate (dxT (vxT A) p)) ⊕_) (negate-⊕ (dyT (vyT A) p) (dzT (vzT A) p))) ⟩
  (negate (dxT (vxT A) p)) ⊕ (negate ((dyT (vyT A) p) ⊕ (dzT (vzT A) p)))
    ≡⟨ sym (negate-⊕ (dxT (vxT A) p) ((dyT (vyT A) p) ⊕ (dzT (vzT A) p))) ⟩
  negate ((dxT (vxT A) p) ⊕ ((dyT (vyT A) p) ⊕ (dzT (vzT A) p)))
    ≡⟨ refl ⟩
  negate (divT A p) ∎

-- 散度与时间差分交换: div9(Δ_t F) = Δ_t(div9 F)
div9-time-comm : ∀ (F : GF9VecTime) (t : Time) (p : Point) →
  div9 (λ q → ΔtV9 F t q) p ≡ Δt9 (λ s q → div9 (F s) q) t p
div9-time-comm F t p = begin
  div9 (λ q → ΔtV9 F t q) p
    ≡⟨ refl ⟩
  (dx9 (λ q → (vx9 (F (suc t)) q) +gf9 neg9 (vx9 (F t) q)) p) +gf9
    ((dy9 (λ q → (vy9 (F (suc t)) q) +gf9 neg9 (vy9 (F t) q)) p) +gf9
     (dz9 (λ q → (vz9 (F (suc t)) q) +gf9 neg9 (vz9 (F t) q)) p))
    ≡⟨ cong₂ _+gf9_
         (dx9-add (vx9 (F (suc t))) (λ q → neg9 (vx9 (F t) q)) p)
         (cong₂ _+gf9_
           (dy9-add (vy9 (F (suc t))) (λ q → neg9 (vy9 (F t) q)) p)
           (dz9-add (vz9 (F (suc t))) (λ q → neg9 (vz9 (F t) q)) p)) ⟩
  ((dx9 (vx9 (F (suc t))) p) +gf9 (dx9 (λ q → neg9 (vx9 (F t) q)) p)) +gf9
    (((dy9 (vy9 (F (suc t))) p) +gf9 (dy9 (λ q → neg9 (vy9 (F t) q)) p)) +gf9
     ((dz9 (vz9 (F (suc t))) p) +gf9 (dz9 (λ q → neg9 (vz9 (F t) q)) p)))
    ≡⟨ cong₂ _+gf9_
         (cong ((dx9 (vx9 (F (suc t))) p) +gf9_) (dx9-neg (vx9 (F t)) p))
         (cong₂ _+gf9_
           (cong ((dy9 (vy9 (F (suc t))) p) +gf9_) (dy9-neg (vy9 (F t)) p))
           (cong ((dz9 (vz9 (F (suc t))) p) +gf9_) (dz9-neg (vz9 (F t)) p))) ⟩
  ((dx9 (vx9 (F (suc t))) p) +gf9 neg9 (dx9 (vx9 (F t)) p)) +gf9
    (((dy9 (vy9 (F (suc t))) p) +gf9 neg9 (dy9 (vy9 (F t)) p)) +gf9
     ((dz9 (vz9 (F (suc t))) p) +gf9 neg9 (dz9 (vz9 (F t)) p)))
    ≡⟨ div9-rearrange9 (dx9 (vx9 (F (suc t))) p) (neg9 (dx9 (vx9 (F t)) p))
                       (dy9 (vy9 (F (suc t))) p) (neg9 (dy9 (vy9 (F t)) p))
                       (dz9 (vz9 (F (suc t))) p) (neg9 (dz9 (vz9 (F t)) p)) ⟩
  ((dx9 (vx9 (F (suc t))) p) +gf9 ((dy9 (vy9 (F (suc t))) p) +gf9 (dz9 (vz9 (F (suc t))) p))) +gf9
    ((neg9 (dx9 (vx9 (F t)) p)) +gf9 ((neg9 (dy9 (vy9 (F t)) p)) +gf9 (neg9 (dz9 (vz9 (F t)) p))))
    ≡⟨ cong (((dx9 (vx9 (F (suc t))) p) +gf9 ((dy9 (vy9 (F (suc t))) p) +gf9 (dz9 (vz9 (F (suc t))) p))) +gf9_)
            (neg9-add9-3 (dx9 (vx9 (F t)) p) (dy9 (vy9 (F t)) p) (dz9 (vz9 (F t)) p)) ⟩
  ((dx9 (vx9 (F (suc t))) p) +gf9 ((dy9 (vy9 (F (suc t))) p) +gf9 (dz9 (vz9 (F (suc t))) p))) +gf9
    (neg9 ((dx9 (vx9 (F t)) p) +gf9 ((dy9 (vy9 (F t)) p) +gf9 (dz9 (vz9 (F t)) p))))
    ≡⟨ refl ⟩
  Δt9 (λ s q → div9 (F s) q) t p ∎

-- 共轭旋度散度为零: div9(curl9 F) = zero9 (实部/虚部降维到 div-curl-zero-Trit)
div9-curl9-zero : ∀ (F : GF9Vec) (p : Point) → div9 (curl9 F) p ≡ zero9
div9-curl9-zero F p = begin
  div9 (curl9 F) p
    ≡⟨ cong₂ _,_ (re-div9 (curl9 F) p) (im-div9 (curl9 F) p) ⟩
  (divT (realVec (curl9 F)) p , divT (imagVec (curl9 F)) p)
    ≡⟨ refl ⟩
  (divT (curlT (imagVec F)) p , divT (λ q → negVecT (curlT (realVec F) q)) p)
    ≡⟨ cong₂ _,_
         (div-curl-zero-Trit (imagVec F) p)
         (trans (divT-neg (curlT (realVec F)) p)
                (cong negate (div-curl-zero-Trit (realVec F) p))) ⟩
  (T₀ , negate T₀)
    ≡⟨ refl ⟩
  zero9 ∎

-- neg9 对合 / +gf9 逆元 (GF9 代数, 电荷守恒对消所需)
neg9-involutive : ∀ x → neg9 (neg9 x) ≡ x
neg9-involutive (a , b) = cong₂ _,_ (negate² a) (negate² b)

+gf9-inverse : ∀ x → x +gf9 neg9 x ≡ zero9
+gf9-inverse (a , b) = cong₂ _,_ (⊕-inverse a) (⊕-inverse b)

-- 消去引理: (u + x) + (-u) ≡ x (GF9 版 cancel-right)
cancel-right9 : ∀ u x → (u +gf9 x) +gf9 neg9 u ≡ x
cancel-right9 u x = begin
  (u +gf9 x) +gf9 neg9 u
    ≡⟨ +gf9-assoc u x (neg9 u) ⟩
  u +gf9 (x +gf9 neg9 u)
    ≡⟨ cong (u +gf9_) (+gf9-comm x (neg9 u)) ⟩
  u +gf9 (neg9 u +gf9 x)
    ≡⟨ sym (+gf9-assoc u (neg9 u) x) ⟩
  (u +gf9 neg9 u) +gf9 x
    ≡⟨ cong (λ v → v +gf9 x) (+gf9-inverse u) ⟩
  zero9 +gf9 x
    ≡⟨ +gf9-identityˡ x ⟩
  x ∎

-- 场级统一 Maxwell 步进 (构造性动力学, 避免 funext)
UnifiedMaxwellStep : GF9VecTime → GF9VecTime → Set
UnifiedMaxwellStep F J = ∀ t → F (suc t) ≡
  λ q → addVec9 (F t q) (addVec9 (curl9 (F t) q) (negVec9 (J t q)))

-- div9-step: 步进 ⇒ div F(t+1) = div F(t) - div J(t)
div9-step : ∀ (F J : GF9VecTime) → UnifiedMaxwellStep F J →
  ∀ t p → div9 (F (suc t)) p ≡ (div9 (F t) p) +gf9 (neg9 (div9 (J t) p))
div9-step F J Fstep t p = begin
  div9 (F (suc t)) p
    ≡⟨ cong (λ G → div9 G p) (Fstep t) ⟩
  div9 (λ q → addVec9 (F t q) (addVec9 (curl9 (F t) q) (negVec9 (J t q)))) p
    ≡⟨ div9-add (F t) (λ q → addVec9 (curl9 (F t) q) (negVec9 (J t q))) p ⟩
  (div9 (F t) p) +gf9 (div9 (λ q → addVec9 (curl9 (F t) q) (negVec9 (J t q))) p)
    ≡⟨ cong ((div9 (F t) p) +gf9_) (div9-add (curl9 (F t)) (λ q → negVec9 (J t q)) p) ⟩
  (div9 (F t) p) +gf9 ((div9 (curl9 (F t)) p) +gf9 (div9 (λ q → negVec9 (J t q)) p))
    ≡⟨ cong ((div9 (F t) p) +gf9_)
            (cong₂ _+gf9_ (div9-curl9-zero (F t) p) (div9-neg (J t) p)) ⟩
  (div9 (F t) p) +gf9 (zero9 +gf9 (neg9 (div9 (J t) p)))
    ≡⟨ cong ((div9 (F t) p) +gf9_) (+gf9-identityˡ (neg9 (div9 (J t) p))) ⟩
  (div9 (F t) p) +gf9 (neg9 (div9 (J t) p)) ∎

-- 电荷守恒 (连续性方程): 步进 + 高斯(ρ=div F) ⇒ Δ_t ρ = -div J
charge-conservation-GF9 : ∀ (F J : GF9VecTime) (ρ : GF9ScalTime) →
  UnifiedMaxwellStep F J → (∀ t p → div9 (F t) p ≡ ρ t p) →
  ∀ t p → Δt9 ρ t p ≡ neg9 (div9 (J t) p)
charge-conservation-GF9 F J ρ Fstep gauss t p = begin
  Δt9 ρ t p
    ≡⟨ refl ⟩
  (ρ (suc t) p) +gf9 neg9 (ρ t p)
    ≡⟨ cong₂ _+gf9_ (sym (gauss (suc t) p)) (cong neg9 (sym (gauss t p))) ⟩
  (div9 (F (suc t)) p) +gf9 neg9 (div9 (F t) p)
    ≡⟨ cong (λ x → x +gf9 neg9 (div9 (F t) p)) (div9-step F J Fstep t p) ⟩
  ((div9 (F t) p) +gf9 (neg9 (div9 (J t) p))) +gf9 neg9 (div9 (F t) p)
    ≡⟨ cancel-right9 (div9 (F t) p) (neg9 (div9 (J t) p)) ⟩
  neg9 (div9 (J t) p) ∎

-- 0 postulate.
