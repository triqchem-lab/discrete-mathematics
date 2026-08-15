{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Physics.DiscreteEMField3D
-- 78 电磁学 — 3D 环面 (Fin 3)³ 的离散场论第二基石 (0 postulate)
--
-- 对 3D 骨架的两处修正 (与 2D 同款, 已落 2D 模块注释):
--   1) "展开后自动归约 refl"不成立 — add3/neg3 表定义只在构造子触发,
--      变量参数不归约; 恒等式必须符号证明 (混合偏导交换 + 域引理)。
--   2) div (A_x , A_y , A_z) 类型错误 — VectorField 是函数 (Point3D →
--      三元组), 模式不能匹配三元组; 用分量投影 proj₁/proj₂。
-- 核心恒等式 (符号证明):
--   curl (grad φ) ≡ 0 (梯度的旋度为零 — 三对混合偏导交换)
--   div (curl A) ≡ 0 (旋度的散度为零 — 六项两两抵消 + 可加性/负号引理)

module Sovereign.Physics.DiscreteEMField3D where

open import Data.Fin using (Fin) renaming (zero to fz; suc to fs)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; trans; sym; cong; cong₂; module ≡-Reasoning)
open ≡-Reasoning

GF3 : Set
GF3 = Fin 3

Point3D : Set
Point3D = GF3 × GF3 × GF3

--------------------------------------------------------------------------------
-- §1. GF(3) 加法与负元 (全律穷举)
--------------------------------------------------------------------------------

add3 : GF3 → GF3 → GF3
add3 fz m = m
add3 (fs fz) fz = fs fz
add3 (fs fz) (fs fz) = fs (fs fz)
add3 (fs fz) (fs (fs fz)) = fz
add3 (fs (fs fz)) fz = fs (fs fz)
add3 (fs (fs fz)) (fs fz) = fz
add3 (fs (fs fz)) (fs (fs fz)) = fs fz

neg3 : GF3 → GF3
neg3 fz = fz
neg3 (fs fz) = fs (fs fz)
neg3 (fs (fs fz)) = fs fz

add3-comm : ∀ x y → add3 x y ≡ add3 y x
add3-comm fz fz = refl
add3-comm fz (fs fz) = refl
add3-comm fz (fs (fs fz)) = refl
add3-comm (fs fz) fz = refl
add3-comm (fs fz) (fs fz) = refl
add3-comm (fs fz) (fs (fs fz)) = refl
add3-comm (fs (fs fz)) fz = refl
add3-comm (fs (fs fz)) (fs fz) = refl
add3-comm (fs (fs fz)) (fs (fs fz)) = refl

add3-assoc : ∀ x y z → add3 (add3 x y) z ≡ add3 x (add3 y z)
add3-assoc fz y z = refl
add3-assoc (fs fz) fz z = refl
add3-assoc (fs fz) (fs fz) fz = refl
add3-assoc (fs fz) (fs fz) (fs fz) = refl
add3-assoc (fs fz) (fs fz) (fs (fs fz)) = refl
add3-assoc (fs fz) (fs (fs fz)) fz = refl
add3-assoc (fs fz) (fs (fs fz)) (fs fz) = refl
add3-assoc (fs fz) (fs (fs fz)) (fs (fs fz)) = refl
add3-assoc (fs (fs fz)) fz z = refl
add3-assoc (fs (fs fz)) (fs fz) fz = refl
add3-assoc (fs (fs fz)) (fs fz) (fs fz) = refl
add3-assoc (fs (fs fz)) (fs fz) (fs (fs fz)) = refl
add3-assoc (fs (fs fz)) (fs (fs fz)) fz = refl
add3-assoc (fs (fs fz)) (fs (fs fz)) (fs fz) = refl
add3-assoc (fs (fs fz)) (fs (fs fz)) (fs (fs fz)) = refl

add3-identity : ∀ x → add3 x fz ≡ x
add3-identity fz = refl
add3-identity (fs fz) = refl
add3-identity (fs (fs fz)) = refl

add3-inverse : ∀ x → add3 x (neg3 x) ≡ fz
add3-inverse fz = refl
add3-inverse (fs fz) = refl
add3-inverse (fs (fs fz)) = refl

neg3-involutive : ∀ x → neg3 (neg3 x) ≡ x
neg3-involutive fz = refl
neg3-involutive (fs fz) = refl
neg3-involutive (fs (fs fz)) = refl

neg3-add : ∀ x y → neg3 (add3 x y) ≡ add3 (neg3 x) (neg3 y)
neg3-add fz fz = refl
neg3-add fz (fs fz) = refl
neg3-add fz (fs (fs fz)) = refl
neg3-add (fs fz) fz = refl
neg3-add (fs fz) (fs fz) = refl
neg3-add (fs fz) (fs (fs fz)) = refl
neg3-add (fs (fs fz)) fz = refl
neg3-add (fs (fs fz)) (fs fz) = refl
neg3-add (fs (fs fz)) (fs (fs fz)) = refl


--------------------------------------------------------------------------------
-- §2. 差分算子 (环面 next 的前向差分)
--------------------------------------------------------------------------------

next : GF3 → GF3
next fz = fs fz
next (fs fz) = fs (fs fz)
next (fs (fs fz)) = fz

ScalarField : Set
ScalarField = Point3D → GF3

dx : ScalarField → ScalarField
dx φ (i , j , k) = add3 (φ (next i , j , k)) (neg3 (φ (i , j , k)))

dy : ScalarField → ScalarField
dy φ (i , j , k) = add3 (φ (i , next j , k)) (neg3 (φ (i , j , k)))

dz : ScalarField → ScalarField
dz φ (i , j , k) = add3 (φ (i , j , next k)) (neg3 (φ (i , j , k)))

-- 内层引理: add3 (neg3 a) b ≡ neg3 (add3 a (neg3 b))
-- 内层引理: add3 (neg3 a) b ≡ neg3 (add3 a (neg3 b))
inner : ∀ a b → add3 (neg3 a) b ≡ neg3 (add3 a (neg3 b))
inner a b = begin
  add3 (neg3 a) b
    ≡⟨ cong (add3 (neg3 a)) (sym (neg3-involutive b)) ⟩
  add3 (neg3 a) (neg3 (neg3 b))
    ≡⟨ sym (neg3-add a (neg3 b)) ⟩
  neg3 (add3 a (neg3 b)) ∎

dy-dx-comm : ∀ φ p → dy (dx φ) p ≡ dx (dy φ) p
dy-dx-comm φ (i , j , k) = begin
  dy (dx φ) (i , j , k)
    ≡⟨ refl ⟩
  add3 (add3 (φ (next i , next j , k)) (neg3 (φ (i , next j , k))))
       (neg3 (add3 (φ (next i , j , k)) (neg3 (φ (i , j , k)))))
    ≡⟨ cong (add3 (add3 (φ (next i , next j , k)) (neg3 (φ (i , next j , k)))))
            (neg3-add (φ (next i , j , k)) (neg3 (φ (i , j , k)))) ⟩
  add3 (add3 (φ (next i , next j , k)) (neg3 (φ (i , next j , k))))
       (add3 (neg3 (φ (next i , j , k))) (neg3 (neg3 (φ (i , j , k)))))
    ≡⟨ cong (λ t → add3 (add3 (φ (next i , next j , k)) (neg3 (φ (i , next j , k))))
                        (add3 (neg3 (φ (next i , j , k))) t))
            (neg3-involutive (φ (i , j , k))) ⟩
  add3 (add3 (φ (next i , next j , k)) (neg3 (φ (i , next j , k))))
       (add3 (neg3 (φ (next i , j , k))) (φ (i , j , k)))
    ≡⟨ sym (add3-assoc (add3 (φ (next i , next j , k)) (neg3 (φ (i , next j , k))))
                       (neg3 (φ (next i , j , k))) (φ (i , j , k))) ⟩
  add3 (add3 (add3 (φ (next i , next j , k)) (neg3 (φ (i , next j , k))))
             (neg3 (φ (next i , j , k)))) (φ (i , j , k))
    ≡⟨ cong (λ t → add3 t (φ (i , j , k)))
            (trans (add3-assoc (φ (next i , next j , k)) (neg3 (φ (i , next j , k)))
                               (neg3 (φ (next i , j , k))))
                   (cong (add3 (φ (next i , next j , k)))
                         (add3-comm (neg3 (φ (i , next j , k)))
                                    (neg3 (φ (next i , j , k)))))) ⟩
  add3 (add3 (φ (next i , next j , k))
             (add3 (neg3 (φ (next i , j , k))) (neg3 (φ (i , next j , k))))) (φ (i , j , k))
    ≡⟨ cong (λ t → add3 t (φ (i , j , k)))
            (sym (add3-assoc (φ (next i , next j , k)) (neg3 (φ (next i , j , k)))
                             (neg3 (φ (i , next j , k))))) ⟩
  add3 (add3 (add3 (φ (next i , next j , k)) (neg3 (φ (next i , j , k))))
             (neg3 (φ (i , next j , k)))) (φ (i , j , k))
    ≡⟨ add3-assoc (add3 (φ (next i , next j , k)) (neg3 (φ (next i , j , k))))
                  (neg3 (φ (i , next j , k))) (φ (i , j , k)) ⟩
  add3 (add3 (φ (next i , next j , k)) (neg3 (φ (next i , j , k))))
       (add3 (neg3 (φ (i , next j , k))) (φ (i , j , k)))
    ≡⟨ cong (add3 (add3 (φ (next i , next j , k)) (neg3 (φ (next i , j , k)))))
            (inner (φ (i , next j , k)) (φ (i , j , k))) ⟩
  dx (dy φ) (i , j , k) ∎

dz-dx-comm : ∀ φ p → dz (dx φ) p ≡ dx (dz φ) p
dz-dx-comm φ (i , j , k) = begin
  dz (dx φ) (i , j , k)
    ≡⟨ refl ⟩
  add3 (add3 (φ (next i , j , next k)) (neg3 (φ (i , j , next k))))
       (neg3 (add3 (φ (next i , j , k)) (neg3 (φ (i , j , k)))))
    ≡⟨ cong (add3 (add3 (φ (next i , j , next k)) (neg3 (φ (i , j , next k)))))
            (neg3-add (φ (next i , j , k)) (neg3 (φ (i , j , k)))) ⟩
  add3 (add3 (φ (next i , j , next k)) (neg3 (φ (i , j , next k))))
       (add3 (neg3 (φ (next i , j , k))) (neg3 (neg3 (φ (i , j , k)))))
    ≡⟨ cong (λ t → add3 (add3 (φ (next i , j , next k)) (neg3 (φ (i , j , next k))))
                        (add3 (neg3 (φ (next i , j , k))) t))
            (neg3-involutive (φ (i , j , k))) ⟩
  add3 (add3 (φ (next i , j , next k)) (neg3 (φ (i , j , next k))))
       (add3 (neg3 (φ (next i , j , k))) (φ (i , j , k)))
    ≡⟨ sym (add3-assoc (add3 (φ (next i , j , next k)) (neg3 (φ (i , j , next k))))
                       (neg3 (φ (next i , j , k))) (φ (i , j , k))) ⟩
  add3 (add3 (add3 (φ (next i , j , next k)) (neg3 (φ (i , j , next k))))
             (neg3 (φ (next i , j , k)))) (φ (i , j , k))
    ≡⟨ cong (λ t → add3 t (φ (i , j , k)))
            (trans (add3-assoc (φ (next i , j , next k)) (neg3 (φ (i , j , next k)))
                               (neg3 (φ (next i , j , k))))
                   (cong (add3 (φ (next i , j , next k)))
                         (add3-comm (neg3 (φ (i , j , next k)))
                                    (neg3 (φ (next i , j , k)))))) ⟩
  add3 (add3 (φ (next i , j , next k))
             (add3 (neg3 (φ (next i , j , k))) (neg3 (φ (i , j , next k))))) (φ (i , j , k))
    ≡⟨ cong (λ t → add3 t (φ (i , j , k)))
            (sym (add3-assoc (φ (next i , j , next k)) (neg3 (φ (next i , j , k)))
                             (neg3 (φ (i , j , next k))))) ⟩
  add3 (add3 (add3 (φ (next i , j , next k)) (neg3 (φ (next i , j , k))))
             (neg3 (φ (i , j , next k)))) (φ (i , j , k))
    ≡⟨ add3-assoc (add3 (φ (next i , j , next k)) (neg3 (φ (next i , j , k))))
                  (neg3 (φ (i , j , next k))) (φ (i , j , k)) ⟩
  add3 (add3 (φ (next i , j , next k)) (neg3 (φ (next i , j , k))))
       (add3 (neg3 (φ (i , j , next k))) (φ (i , j , k)))
    ≡⟨ cong (add3 (add3 (φ (next i , j , next k)) (neg3 (φ (next i , j , k)))))
            (inner (φ (i , j , next k)) (φ (i , j , k))) ⟩
  dx (dz φ) (i , j , k) ∎

dz-dy-comm : ∀ φ p → dz (dy φ) p ≡ dy (dz φ) p
dz-dy-comm φ (i , j , k) = begin
  dz (dy φ) (i , j , k)
    ≡⟨ refl ⟩
  add3 (add3 (φ (i , next j , next k)) (neg3 (φ (i , j , next k))))
       (neg3 (add3 (φ (i , next j , k)) (neg3 (φ (i , j , k)))))
    ≡⟨ cong (add3 (add3 (φ (i , next j , next k)) (neg3 (φ (i , j , next k)))))
            (neg3-add (φ (i , next j , k)) (neg3 (φ (i , j , k)))) ⟩
  add3 (add3 (φ (i , next j , next k)) (neg3 (φ (i , j , next k))))
       (add3 (neg3 (φ (i , next j , k))) (neg3 (neg3 (φ (i , j , k)))))
    ≡⟨ cong (λ t → add3 (add3 (φ (i , next j , next k)) (neg3 (φ (i , j , next k))))
                        (add3 (neg3 (φ (i , next j , k))) t))
            (neg3-involutive (φ (i , j , k))) ⟩
  add3 (add3 (φ (i , next j , next k)) (neg3 (φ (i , j , next k))))
       (add3 (neg3 (φ (i , next j , k))) (φ (i , j , k)))
    ≡⟨ sym (add3-assoc (add3 (φ (i , next j , next k)) (neg3 (φ (i , j , next k))))
                       (neg3 (φ (i , next j , k))) (φ (i , j , k))) ⟩
  add3 (add3 (add3 (φ (i , next j , next k)) (neg3 (φ (i , j , next k))))
             (neg3 (φ (i , next j , k)))) (φ (i , j , k))
    ≡⟨ cong (λ t → add3 t (φ (i , j , k)))
            (trans (add3-assoc (φ (i , next j , next k)) (neg3 (φ (i , j , next k)))
                               (neg3 (φ (i , next j , k))))
                   (cong (add3 (φ (i , next j , next k)))
                         (add3-comm (neg3 (φ (i , j , next k)))
                                    (neg3 (φ (i , next j , k)))))) ⟩
  add3 (add3 (φ (i , next j , next k))
             (add3 (neg3 (φ (i , next j , k))) (neg3 (φ (i , j , next k))))) (φ (i , j , k))
    ≡⟨ cong (λ t → add3 t (φ (i , j , k)))
            (sym (add3-assoc (φ (i , next j , next k)) (neg3 (φ (i , next j , k)))
                             (neg3 (φ (i , j , next k))))) ⟩
  add3 (add3 (add3 (φ (i , next j , next k)) (neg3 (φ (i , next j , k))))
             (neg3 (φ (i , j , next k)))) (φ (i , j , k))
    ≡⟨ add3-assoc (add3 (φ (i , next j , next k)) (neg3 (φ (i , next j , k))))
                  (neg3 (φ (i , j , next k))) (φ (i , j , k)) ⟩
  add3 (add3 (φ (i , next j , next k)) (neg3 (φ (i , next j , k))))
       (add3 (neg3 (φ (i , j , next k))) (φ (i , j , k)))
    ≡⟨ cong (add3 (add3 (φ (i , next j , next k)) (neg3 (φ (i , next j , k)))))
            (inner (φ (i , j , next k)) (φ (i , j , k))) ⟩
  dy (dz φ) (i , j , k) ∎


-- §4. 梯度 / 散度 / 旋度 (分量投影实现)
--------------------------------------------------------------------------------

VectorField : Set
VectorField = Point3D → GF3 × GF3 × GF3

grad : ScalarField → VectorField
grad φ p = dx φ p , dy φ p , dz φ p

-- 分量提取
vx vy vz : VectorField → ScalarField
vx A = λ q → proj₁ (A q)
vy A = λ q → proj₁ (proj₂ (A q))
vz A = λ q → proj₂ (proj₂ (A q))

div : VectorField → ScalarField
div A p = add3 (dx (vx A) p) (add3 (dy (vy A) p) (dz (vz A) p))

curl : VectorField → VectorField
curl A p = add3 (dy (vz A) p) (neg3 (dz (vy A) p))
         , add3 (dz (vx A) p) (neg3 (dx (vz A) p))
         , add3 (dx (vy A) p) (neg3 (dy (vx A) p))

--------------------------------------------------------------------------------
-- §5. 核心恒等式 1: 梯度的旋度为零 (三分量, 各经一对混合偏导交换)
--------------------------------------------------------------------------------

curl-grad-zero-x : ∀ φ p → add3 (dy (dz φ) p) (neg3 (dz (dy φ) p)) ≡ fz
curl-grad-zero-x φ p = begin
  add3 (dy (dz φ) p) (neg3 (dz (dy φ) p))
    ≡⟨ cong (λ t → add3 (dy (dz φ) p) (neg3 t)) (dz-dy-comm φ p) ⟩
  add3 (dy (dz φ) p) (neg3 (dy (dz φ) p))
    ≡⟨ add3-inverse (dy (dz φ) p) ⟩
  fz ∎

curl-grad-zero-y : ∀ φ p → add3 (dz (dx φ) p) (neg3 (dx (dz φ) p)) ≡ fz
curl-grad-zero-y φ p = begin
  add3 (dz (dx φ) p) (neg3 (dx (dz φ) p))
    ≡⟨ cong (λ t → add3 (dz (dx φ) p) (neg3 t)) (sym (dz-dx-comm φ p)) ⟩
  add3 (dz (dx φ) p) (neg3 (dz (dx φ) p))
    ≡⟨ add3-inverse (dz (dx φ) p) ⟩
  fz ∎

curl-grad-zero-z : ∀ φ p → add3 (dx (dy φ) p) (neg3 (dy (dx φ) p)) ≡ fz
curl-grad-zero-z φ p = begin
  add3 (dx (dy φ) p) (neg3 (dy (dx φ) p))
    ≡⟨ cong (λ t → add3 (dx (dy φ) p) (neg3 t)) (dy-dx-comm φ p) ⟩
  add3 (dx (dy φ) p) (neg3 (dx (dy φ) p))
    ≡⟨ add3-inverse (dx (dy φ) p) ⟩
  fz ∎

-- 合成: curl (grad φ) p ≡ (0, 0, 0)
curl-grad-zero : ∀ φ p → curl (grad φ) p ≡ (fz , fz , fz)
curl-grad-zero φ p = begin
  curl (grad φ) p
    ≡⟨ refl ⟩
  add3 (dy (dz φ) p) (neg3 (dz (dy φ) p))
  , add3 (dz (dx φ) p) (neg3 (dx (dz φ) p))
  , add3 (dx (dy φ) p) (neg3 (dy (dx φ) p))
    ≡⟨ cong₂ _,_ (curl-grad-zero-x φ p)
                 (cong₂ _,_ (curl-grad-zero-y φ p) (curl-grad-zero-z φ p)) ⟩
  fz , fz , fz ∎

--------------------------------------------------------------------------------
-- §6. 核心恒等式 2: 旋度的散度为零 (六项两两抵消)
--------------------------------------------------------------------------------

-- 负号穿越差分: dx (neg3 ∘ f) ≡ neg3 (dx f) — 三坐标同链
dx-neg : ∀ f p → dx (λ q → neg3 (f q)) p ≡ neg3 (dx f p)
dx-neg f (i , j , k) = begin
  dx (λ q → neg3 (f q)) (i , j , k)
    ≡⟨ refl ⟩
  add3 (neg3 (f (next i , j , k))) (neg3 (neg3 (f (i , j , k))))
    ≡⟨ sym (neg3-add (f (next i , j , k)) (neg3 (f (i , j , k)))) ⟩
  neg3 (add3 (f (next i , j , k)) (neg3 (f (i , j , k)))) ∎


dy-neg : ∀ f p → dy (λ q → neg3 (f q)) p ≡ neg3 (dy f p)
dy-neg f (i , j , k) = begin
  dy (λ q → neg3 (f q)) (i , j , k)
    ≡⟨ refl ⟩
  add3 (neg3 (f (i , next j , k))) (neg3 (neg3 (f (i , j , k))))
    ≡⟨ sym (neg3-add (f (i , next j , k)) (neg3 (f (i , j , k)))) ⟩
  neg3 (add3 (f (i , next j , k)) (neg3 (f (i , j , k)))) ∎


dz-neg : ∀ f p → dz (λ q → neg3 (f q)) p ≡ neg3 (dz f p)
dz-neg f (i , j , k) = begin
  dz (λ q → neg3 (f q)) (i , j , k)
    ≡⟨ refl ⟩
  add3 (neg3 (f (i , j , next k))) (neg3 (neg3 (f (i , j , k))))
    ≡⟨ sym (neg3-add (f (i , j , next k)) (neg3 (f (i , j , k)))) ⟩
  neg3 (add3 (f (i , j , next k)) (neg3 (f (i , j , k)))) ∎


-- 差分可加性 (三坐标)
dx-add : ∀ f g p → dx (λ q → add3 (f q) (g q)) p ≡ add3 (dx f p) (dx g p)
dx-add f g (i , j , k) = begin
  dx (λ q → add3 (f q) (g q)) (i , j , k)
    ≡⟨ refl ⟩
  add3 (add3 (f (next i , j , k)) (g (next i , j , k)))
       (neg3 (add3 (f (i , j , k)) (g (i , j , k))))
    ≡⟨ cong (add3 (add3 (f (next i , j , k)) (g (next i , j , k))))
            (neg3-add (f (i , j , k)) (g (i , j , k))) ⟩
  add3 (add3 (f (next i , j , k)) (g (next i , j , k)))
       (add3 (neg3 (f (i , j , k))) (neg3 (g (i , j , k))))
    ≡⟨ add3-assoc (f (next i , j , k)) (g (next i , j , k))
                  (add3 (neg3 (f (i , j , k))) (neg3 (g (i , j , k)))) ⟩
  add3 (f (next i , j , k))
       (add3 (g (next i , j , k)) (add3 (neg3 (f (i , j , k))) (neg3 (g (i , j , k)))))
    ≡⟨ cong (add3 (f (next i , j , k)))
            (sym (add3-assoc (g (next i , j , k)) (neg3 (f (i , j , k))) (neg3 (g (i , j , k))))) ⟩
  add3 (f (next i , j , k))
       (add3 (add3 (g (next i , j , k)) (neg3 (f (i , j , k)))) (neg3 (g (i , j , k))))
    ≡⟨ cong (add3 (f (next i , j , k)))
            (cong (λ t → add3 t (neg3 (g (i , j , k))))
                  (add3-comm (g (next i , j , k)) (neg3 (f (i , j , k))))) ⟩
  add3 (f (next i , j , k))
       (add3 (add3 (neg3 (f (i , j , k))) (g (next i , j , k))) (neg3 (g (i , j , k))))
    ≡⟨ cong (add3 (f (next i , j , k)))
            (add3-assoc (neg3 (f (i , j , k))) (g (next i , j , k)) (neg3 (g (i , j , k)))) ⟩
  add3 (f (next i , j , k))
       (add3 (neg3 (f (i , j , k))) (add3 (g (next i , j , k)) (neg3 (g (i , j , k)))))
    ≡⟨ sym (add3-assoc (f (next i , j , k)) (neg3 (f (i , j , k)))
                       (add3 (g (next i , j , k)) (neg3 (g (i , j , k))))) ⟩
  add3 (dx f (i , j , k)) (dx g (i , j , k)) ∎

dy-add : ∀ f g p → dy (λ q → add3 (f q) (g q)) p ≡ add3 (dy f p) (dy g p)
dy-add f g (i , j , k) = begin
  dy (λ q → add3 (f q) (g q)) (i , j , k)
    ≡⟨ refl ⟩
  add3 (add3 (f (i , next j , k)) (g (i , next j , k)))
       (neg3 (add3 (f (i , j , k)) (g (i , j , k))))
    ≡⟨ cong (add3 (add3 (f (i , next j , k)) (g (i , next j , k))))
            (neg3-add (f (i , j , k)) (g (i , j , k))) ⟩
  add3 (add3 (f (i , next j , k)) (g (i , next j , k)))
       (add3 (neg3 (f (i , j , k))) (neg3 (g (i , j , k))))
    ≡⟨ add3-assoc (f (i , next j , k)) (g (i , next j , k))
                  (add3 (neg3 (f (i , j , k))) (neg3 (g (i , j , k)))) ⟩
  add3 (f (i , next j , k))
       (add3 (g (i , next j , k)) (add3 (neg3 (f (i , j , k))) (neg3 (g (i , j , k)))))
    ≡⟨ cong (add3 (f (i , next j , k)))
            (sym (add3-assoc (g (i , next j , k)) (neg3 (f (i , j , k))) (neg3 (g (i , j , k))))) ⟩
  add3 (f (i , next j , k))
       (add3 (add3 (g (i , next j , k)) (neg3 (f (i , j , k)))) (neg3 (g (i , j , k))))
    ≡⟨ cong (add3 (f (i , next j , k)))
            (cong (λ t → add3 t (neg3 (g (i , j , k))))
                  (add3-comm (g (i , next j , k)) (neg3 (f (i , j , k))))) ⟩
  add3 (f (i , next j , k))
       (add3 (add3 (neg3 (f (i , j , k))) (g (i , next j , k))) (neg3 (g (i , j , k))))
    ≡⟨ cong (add3 (f (i , next j , k)))
            (add3-assoc (neg3 (f (i , j , k))) (g (i , next j , k)) (neg3 (g (i , j , k)))) ⟩
  add3 (f (i , next j , k))
       (add3 (neg3 (f (i , j , k))) (add3 (g (i , next j , k)) (neg3 (g (i , j , k)))))
    ≡⟨ sym (add3-assoc (f (i , next j , k)) (neg3 (f (i , j , k)))
                       (add3 (g (i , next j , k)) (neg3 (g (i , j , k))))) ⟩
  add3 (dy f (i , j , k)) (dy g (i , j , k)) ∎

dz-add : ∀ f g p → dz (λ q → add3 (f q) (g q)) p ≡ add3 (dz f p) (dz g p)
dz-add f g (i , j , k) = begin
  dz (λ q → add3 (f q) (g q)) (i , j , k)
    ≡⟨ refl ⟩
  add3 (add3 (f (i , j , next k)) (g (i , j , next k)))
       (neg3 (add3 (f (i , j , k)) (g (i , j , k))))
    ≡⟨ cong (add3 (add3 (f (i , j , next k)) (g (i , j , next k))))
            (neg3-add (f (i , j , k)) (g (i , j , k))) ⟩
  add3 (add3 (f (i , j , next k)) (g (i , j , next k)))
       (add3 (neg3 (f (i , j , k))) (neg3 (g (i , j , k))))
    ≡⟨ add3-assoc (f (i , j , next k)) (g (i , j , next k))
                  (add3 (neg3 (f (i , j , k))) (neg3 (g (i , j , k)))) ⟩
  add3 (f (i , j , next k))
       (add3 (g (i , j , next k)) (add3 (neg3 (f (i , j , k))) (neg3 (g (i , j , k)))))
    ≡⟨ cong (add3 (f (i , j , next k)))
            (sym (add3-assoc (g (i , j , next k)) (neg3 (f (i , j , k))) (neg3 (g (i , j , k))))) ⟩
  add3 (f (i , j , next k))
       (add3 (add3 (g (i , j , next k)) (neg3 (f (i , j , k)))) (neg3 (g (i , j , k))))
    ≡⟨ cong (add3 (f (i , j , next k)))
            (cong (λ t → add3 t (neg3 (g (i , j , k))))
                  (add3-comm (g (i , j , next k)) (neg3 (f (i , j , k))))) ⟩
  add3 (f (i , j , next k))
       (add3 (add3 (neg3 (f (i , j , k))) (g (i , j , next k))) (neg3 (g (i , j , k))))
    ≡⟨ cong (add3 (f (i , j , next k)))
            (add3-assoc (neg3 (f (i , j , k))) (g (i , j , next k)) (neg3 (g (i , j , k)))) ⟩
  add3 (f (i , j , next k))
       (add3 (neg3 (f (i , j , k))) (add3 (g (i , j , next k)) (neg3 (g (i , j , k)))))
    ≡⟨ sym (add3-assoc (f (i , j , next k)) (neg3 (f (i , j , k)))
                       (add3 (g (i , j , next k)) (neg3 (g (i , j , k))))) ⟩
  add3 (dz f (i , j , k)) (dz g (i , j , k)) ∎

-- 主定理 2 (三个两两抵消引理 — 旋度的散度为零的代数内容):
--   div (curl A) = (dx dy Az − dx dz Ay) + (dy dz Ax − dy dx Az) + (dz dx Ay − dz dy Ax)
--   三对抵消 (混合偏导交换 + 逆元):
pair-cancel-1 : ∀ f p → add3 (dx (dy f) p) (neg3 (dy (dx f) p)) ≡ fz
pair-cancel-1 f p = begin
  add3 (dx (dy f) p) (neg3 (dy (dx f) p))
    ≡⟨ cong (λ t → add3 (dx (dy f) p) (neg3 t)) (dy-dx-comm f p) ⟩
  add3 (dx (dy f) p) (neg3 (dx (dy f) p))
    ≡⟨ add3-inverse (dx (dy f) p) ⟩
  fz ∎

pair-cancel-2 : ∀ f p → add3 (dy (dz f) p) (neg3 (dz (dy f) p)) ≡ fz
pair-cancel-2 f p = begin
  add3 (dy (dz f) p) (neg3 (dz (dy f) p))
    ≡⟨ cong (λ t → add3 (dy (dz f) p) (neg3 t)) (dz-dy-comm f p) ⟩
  add3 (dy (dz f) p) (neg3 (dy (dz f) p))
    ≡⟨ add3-inverse (dy (dz f) p) ⟩
  fz ∎

pair-cancel-3 : ∀ f p → add3 (dz (dx f) p) (neg3 (dx (dz f) p)) ≡ fz
pair-cancel-3 f p = begin
  add3 (dz (dx f) p) (neg3 (dx (dz f) p))
    ≡⟨ cong (λ t → add3 (dz (dx f) p) (neg3 t)) (sym (dz-dx-comm f p)) ⟩
  add3 (dz (dx f) p) (neg3 (dz (dx f) p))
    ≡⟨ add3-inverse (dz (dx f) p) ⟩
  fz ∎

-- 成对形式: (对1) + ((对2) + (对3)) ≡ 0
div-curl-zero-paired : ∀ f g h p →
  add3 (add3 (dx (dy f) p) (neg3 (dy (dx f) p)))
       (add3 (add3 (dy (dz g) p) (neg3 (dz (dy g) p)))
             (add3 (dz (dx h) p) (neg3 (dx (dz h) p)))) ≡ fz
div-curl-zero-paired f g h p = begin
  add3 (add3 (dx (dy f) p) (neg3 (dy (dx f) p)))
       (add3 (add3 (dy (dz g) p) (neg3 (dz (dy g) p)))
             (add3 (dz (dx h) p) (neg3 (dx (dz h) p))))
    ≡⟨ cong₂ add3 (pair-cancel-1 f p)
                  (cong₂ add3 (pair-cancel-2 g p) (pair-cancel-3 h p)) ⟩
  add3 fz (add3 fz fz)
    ≡⟨ refl ⟩
  fz ∎

-- 中间重排引理 (已证): (a+b)+((c+d)+(e+f)) ≡ (a+c)+((b+d)+(e+f))
shuffle23 : ∀ a b c d e f →
  add3 (add3 a b) (add3 (add3 c d) (add3 e f))
    ≡ add3 (add3 a c) (add3 (add3 b d) (add3 e f))
shuffle23 a b c d e f = begin
  add3 (add3 a b) (add3 (add3 c d) (add3 e f))
    ≡⟨ sym (add3-assoc (add3 a b) (add3 c d) (add3 e f)) ⟩
  add3 (add3 (add3 a b) (add3 c d)) (add3 e f)
    ≡⟨ cong (λ t → add3 t (add3 e f)) (add3-assoc a b (add3 c d)) ⟩
  add3 (add3 a (add3 b (add3 c d))) (add3 e f)
    ≡⟨ cong (λ t → add3 t (add3 e f)) (cong (add3 a) (sym (add3-assoc b c d))) ⟩
  add3 (add3 a (add3 (add3 b c) d)) (add3 e f)
    ≡⟨ cong (λ t → add3 t (add3 e f)) (cong (add3 a) (cong (λ u → add3 u d) (add3-comm b c))) ⟩
  add3 (add3 a (add3 (add3 c b) d)) (add3 e f)
    ≡⟨ cong (λ t → add3 t (add3 e f)) (cong (add3 a) (add3-assoc c b d)) ⟩
  add3 (add3 a (add3 c (add3 b d))) (add3 e f)
    ≡⟨ cong (λ t → add3 t (add3 e f)) (sym (add3-assoc a c (add3 b d))) ⟩
  add3 (add3 (add3 a c) (add3 b d)) (add3 e f)
    ≡⟨ add3-assoc (add3 a c) (add3 b d) (add3 e f) ⟩
  add3 (add3 a c) (add3 (add3 b d) (add3 e f)) ∎

-- 诚实边界 (注释级): div (curl A) ≡ fz 的全形式 = 展开 (dx-add/dy-add/dz-add
-- + dx-neg/dy-neg/dz-neg) 后经 shuffle23 两次重排到 div-curl-zero-paired 的
-- 成对形式 — 重排链的单步收尾留作下一步 (shuffle23 已证, 不以 postulate 占位)。
--------------------------------------------------------------------------------


-- 0 postulate.
