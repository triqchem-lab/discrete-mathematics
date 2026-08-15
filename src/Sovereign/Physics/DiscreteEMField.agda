{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Physics.DiscreteEMField
-- 78 电磁学 — 3×3 周期环面上的离散场论第一基石 (0 postulate)
--
-- 对骨架的核心修正: "curl(grad φ) 对任意 φ 自动归约"不成立 —
-- add3/neg3 的表定义只在构造子上触发, 变量参数不归约; 9 格点模式
-- 只固定 p, φ 仍自由。正确路线 = 符号证明:
--   §1 GF(3) 域引理 (add3/neg3 全律穷举)
--   §2 差分算子 dx/dy (前向差分, 环面 next)
--   §3 混合偏导交换 dy∘dx ≡ dx∘dy (符号 ≡-链)
--   §4 grad/curl 与主定理 grad-curl-zero (梯度的旋度恒零)
--   §5 规范不变性: curl(A + grad φ) ≡ curl A (curl 线性 + 主定理)

module Sovereign.Physics.DiscreteEMField where

open import Data.Fin using (Fin) renaming (zero to fz; suc to fs)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; trans; sym; cong; cong₂; module ≡-Reasoning)
open ≡-Reasoning

GF3 : Set
GF3 = Fin 3

Point2D : Set
Point2D = GF3 × GF3

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
ScalarField = Point2D → GF3

dx : ScalarField → ScalarField
dx φ (i , j) = add3 (φ (next i , j)) (neg3 (φ (i , j)))

dy : ScalarField → ScalarField
dy φ (i , j) = add3 (φ (i , next j)) (neg3 (φ (i , j)))

--------------------------------------------------------------------------------
-- §3. 混合偏导交换: dy∘dx ≡ dx∘dy (符号证明)
--------------------------------------------------------------------------------

-- dy (dx φ) (i,j)
--   = [φ(next i, next j) − φ(i, next j)] − [φ(next i, j) − φ(i, j)]
--   = φ(next i, next j) − φ(i, next j) − φ(next i, j) + φ(i, j)
-- dx (dy φ) (i,j)
--   = [φ(next i, next j) − φ(next i, j)] − [φ(i, next j) − φ(i, j)]
--   = 同四元组 (重排) — 由 add3 交换/结合 + neg3-add + neg3 对合证明
-- 内层引理: add3 (neg3 a) b ≡ neg3 (add3 a (neg3 b))
inner : ∀ a b → add3 (neg3 a) b ≡ neg3 (add3 a (neg3 b))
inner a b = begin
  add3 (neg3 a) b
    ≡⟨ cong (add3 (neg3 a)) (sym (neg3-involutive b)) ⟩
  add3 (neg3 a) (neg3 (neg3 b))
    ≡⟨ sym (neg3-add a (neg3 b)) ⟩
  neg3 (add3 a (neg3 b)) ∎

dy-dx-comm : ∀ φ p → dy (dx φ) p ≡ dx (dy φ) p
dy-dx-comm φ (i , j) = begin
  dy (dx φ) (i , j)
    ≡⟨ refl ⟩
  add3 (add3 (φ (next i , next j)) (neg3 (φ (i , next j))))
       (neg3 (add3 (φ (next i , j)) (neg3 (φ (i , j)))))
    ≡⟨ cong (add3 (add3 (φ (next i , next j)) (neg3 (φ (i , next j)))))
            (neg3-add (φ (next i , j)) (neg3 (φ (i , j)))) ⟩
  add3 (add3 (φ (next i , next j)) (neg3 (φ (i , next j))))
       (add3 (neg3 (φ (next i , j))) (neg3 (neg3 (φ (i , j)))))
    ≡⟨ cong (λ t → add3 (add3 (φ (next i , next j)) (neg3 (φ (i , next j))))
                        (add3 (neg3 (φ (next i , j))) t))
            (neg3-involutive (φ (i , j))) ⟩
  add3 (add3 (φ (next i , next j)) (neg3 (φ (i , next j))))
       (add3 (neg3 (φ (next i , j))) (φ (i , j)))
    ≡⟨ sym (add3-assoc (add3 (φ (next i , next j)) (neg3 (φ (i , next j))))
                       (neg3 (φ (next i , j))) (φ (i , j))) ⟩
  add3 (add3 (add3 (φ (next i , next j)) (neg3 (φ (i , next j))))
             (neg3 (φ (next i , j)))) (φ (i , j))
    ≡⟨ cong (λ t → add3 t (φ (i , j)))
            (trans (add3-assoc (φ (next i , next j)) (neg3 (φ (i , next j)))
                               (neg3 (φ (next i , j))))
                   (cong (add3 (φ (next i , next j)))
                         (add3-comm (neg3 (φ (i , next j)))
                                    (neg3 (φ (next i , j)))))) ⟩
  add3 (add3 (φ (next i , next j))
             (add3 (neg3 (φ (next i , j))) (neg3 (φ (i , next j))))) (φ (i , j))
    ≡⟨ cong (λ t → add3 t (φ (i , j)))
            (sym (add3-assoc (φ (next i , next j)) (neg3 (φ (next i , j)))
                             (neg3 (φ (i , next j))))) ⟩
  add3 (add3 (add3 (φ (next i , next j)) (neg3 (φ (next i , j))))
             (neg3 (φ (i , next j)))) (φ (i , j))
    ≡⟨ add3-assoc (add3 (φ (next i , next j)) (neg3 (φ (next i , j))))
                  (neg3 (φ (i , next j))) (φ (i , j)) ⟩
  add3 (add3 (φ (next i , next j)) (neg3 (φ (next i , j))))
       (add3 (neg3 (φ (i , next j))) (φ (i , j)))
    ≡⟨ cong (add3 (add3 (φ (next i , next j)) (neg3 (φ (next i , j)))))
            (inner (φ (i , next j)) (φ (i , j))) ⟩
  dx (dy φ) (i , j) ∎

-- §4. 梯度与旋度 — 主定理: 梯度的旋度恒零
--------------------------------------------------------------------------------

VectorField : Set
VectorField = Point2D → GF3 × GF3

grad : ScalarField → VectorField
grad φ p = dx φ p , dy φ p

-- 2D 标量旋度: curl A = dy A_x − dx A_y
curl : VectorField → ScalarField
curl A p = add3 (dy (λ q → proj₁ (A q)) p)
                (neg3 (dx (λ q → proj₂ (A q)) p))

-- 主定理: curl (grad φ) p ≡ 0 — 由 dy-dx-comm + add3-inverse
grad-curl-zero : ∀ φ p → curl (grad φ) p ≡ fz
grad-curl-zero φ p = begin
  curl (grad φ) p
    ≡⟨ refl ⟩
  add3 (dy (dx φ) p) (neg3 (dx (dy φ) p))
    ≡⟨ cong (λ t → add3 t (neg3 (dx (dy φ) p))) (dy-dx-comm φ p) ⟩
  add3 (dx (dy φ) p) (neg3 (dx (dy φ) p))
    ≡⟨ add3-inverse (dx (dy φ) p) ⟩
  fz ∎

--------------------------------------------------------------------------------
-- §5. 规范不变性: curl(A ⊕a grad φ) ≡ curl A
--------------------------------------------------------------------------------

-- 向量场加法 (点态)
_⊕a_ : VectorField → VectorField → VectorField
(A ⊕a B) p = add3 (proj₁ (A p)) (proj₁ (B p)) , add3 (proj₂ (A p)) (proj₂ (B p))

-- dx 的可加性: dx (φ + ψ) ≡ dx φ + dx ψ (符号链)
dx-add : ∀ φ ψ p → dx (λ q → add3 (φ q) (ψ q)) p ≡ add3 (dx φ p) (dx ψ p)
dx-add φ ψ (i , j) = begin
  dx (λ q → add3 (φ q) (ψ q)) (i , j)
    ≡⟨ refl ⟩
  add3 (add3 (φ (next i , j)) (ψ (next i , j)))
       (neg3 (add3 (φ (i , j)) (ψ (i , j))))
    ≡⟨ cong (add3 (add3 (φ (next i , j)) (ψ (next i , j))))
            (neg3-add (φ (i , j)) (ψ (i , j))) ⟩
  add3 (add3 (φ (next i , j)) (ψ (next i , j)))
       (add3 (neg3 (φ (i , j))) (neg3 (ψ (i , j))))
    ≡⟨ add3-assoc (φ (next i , j)) (ψ (next i , j))
                  (add3 (neg3 (φ (i , j))) (neg3 (ψ (i , j)))) ⟩
  add3 (φ (next i , j))
       (add3 (ψ (next i , j)) (add3 (neg3 (φ (i , j))) (neg3 (ψ (i , j)))))
    ≡⟨ cong (add3 (φ (next i , j)))
            (sym (add3-assoc (ψ (next i , j)) (neg3 (φ (i , j))) (neg3 (ψ (i , j))))) ⟩
  add3 (φ (next i , j))
       (add3 (add3 (ψ (next i , j)) (neg3 (φ (i , j)))) (neg3 (ψ (i , j))))
    ≡⟨ cong (add3 (φ (next i , j)))
            (cong (λ t → add3 t (neg3 (ψ (i , j))))
                  (add3-comm (ψ (next i , j)) (neg3 (φ (i , j))))) ⟩
  add3 (φ (next i , j))
       (add3 (add3 (neg3 (φ (i , j))) (ψ (next i , j))) (neg3 (ψ (i , j))))
    ≡⟨ cong (add3 (φ (next i , j)))
            (add3-assoc (neg3 (φ (i , j))) (ψ (next i , j)) (neg3 (ψ (i , j)))) ⟩
  add3 (φ (next i , j))
       (add3 (neg3 (φ (i , j))) (add3 (ψ (next i , j)) (neg3 (ψ (i , j)))))
    ≡⟨ sym (add3-assoc (φ (next i , j)) (neg3 (φ (i , j)))
                       (add3 (ψ (next i , j)) (neg3 (ψ (i , j))))) ⟩
  add3 (dx φ (i , j)) (dx ψ (i , j)) ∎

dy-add : ∀ φ ψ p → dy (λ q → add3 (φ q) (ψ q)) p ≡ add3 (dy φ p) (dy ψ p)
dy-add φ ψ (i , j) = begin
  dy (λ q → add3 (φ q) (ψ q)) (i , j)
    ≡⟨ refl ⟩
  add3 (add3 (φ (i , next j)) (ψ (i , next j)))
       (neg3 (add3 (φ (i , j)) (ψ (i , j))))
    ≡⟨ cong (add3 (add3 (φ (i , next j)) (ψ (i , next j))))
            (neg3-add (φ (i , j)) (ψ (i , j))) ⟩
  add3 (add3 (φ (i , next j)) (ψ (i , next j)))
       (add3 (neg3 (φ (i , j))) (neg3 (ψ (i , j))))
    ≡⟨ add3-assoc (φ (i , next j)) (ψ (i , next j))
                  (add3 (neg3 (φ (i , j))) (neg3 (ψ (i , j)))) ⟩
  add3 (φ (i , next j))
       (add3 (ψ (i , next j)) (add3 (neg3 (φ (i , j))) (neg3 (ψ (i , j)))))
    ≡⟨ cong (add3 (φ (i , next j)))
            (sym (add3-assoc (ψ (i , next j)) (neg3 (φ (i , j))) (neg3 (ψ (i , j))))) ⟩
  add3 (φ (i , next j))
       (add3 (add3 (ψ (i , next j)) (neg3 (φ (i , j)))) (neg3 (ψ (i , j))))
    ≡⟨ cong (add3 (φ (i , next j)))
            (cong (λ t → add3 t (neg3 (ψ (i , j))))
                  (add3-comm (ψ (i , next j)) (neg3 (φ (i , j))))) ⟩
  add3 (φ (i , next j))
       (add3 (add3 (neg3 (φ (i , j))) (ψ (i , next j))) (neg3 (ψ (i , j))))
    ≡⟨ cong (add3 (φ (i , next j)))
            (add3-assoc (neg3 (φ (i , j))) (ψ (i , next j)) (neg3 (ψ (i , j)))) ⟩
  add3 (φ (i , next j))
       (add3 (neg3 (φ (i , j))) (add3 (ψ (i , next j)) (neg3 (ψ (i , j)))))
    ≡⟨ sym (add3-assoc (φ (i , next j)) (neg3 (φ (i , j)))
                       (add3 (ψ (i , next j)) (neg3 (ψ (i , j))))) ⟩
  add3 (dy φ (i , j)) (dy ψ (i , j)) ∎

-- curl 线性 (点态): curl (A ⊕a B) ≡ curl A + curl B
curl-linear : ∀ A B p → curl (A ⊕a B) p ≡ add3 (curl A p) (curl B p)
curl-linear A B (i , j) = begin
  curl (A ⊕a B) (i , j)
    ≡⟨ refl ⟩
  add3 (dy (λ q → add3 (proj₁ (A q)) (proj₁ (B q))) (i , j))
       (neg3 (dx (λ q → add3 (proj₂ (A q)) (proj₂ (B q))) (i , j)))
    ≡⟨ cong₂ add3
         (dy-add (λ q → proj₁ (A q)) (λ q → proj₁ (B q)) (i , j))
         (cong neg3 (dx-add (λ q → proj₂ (A q)) (λ q → proj₂ (B q)) (i , j))) ⟩
  add3 (add3 (dy (λ q → proj₁ (A q)) (i , j)) (dy (λ q → proj₁ (B q)) (i , j)))
       (neg3 (add3 (dx (λ q → proj₂ (A q)) (i , j)) (dx (λ q → proj₂ (B q)) (i , j))))
    ≡⟨ cong (add3 (add3 (dy (λ q → proj₁ (A q)) (i , j)) (dy (λ q → proj₁ (B q)) (i , j))))
            (neg3-add (dx (λ q → proj₂ (A q)) (i , j)) (dx (λ q → proj₂ (B q)) (i , j))) ⟩
  add3 (add3 (dy (λ q → proj₁ (A q)) (i , j)) (dy (λ q → proj₁ (B q)) (i , j)))
       (add3 (neg3 (dx (λ q → proj₂ (A q)) (i , j))) (neg3 (dx (λ q → proj₂ (B q)) (i , j))))
    ≡⟨ add3-assoc (dy (λ q → proj₁ (A q)) (i , j)) (dy (λ q → proj₁ (B q)) (i , j))
                  (add3 (neg3 (dx (λ q → proj₂ (A q)) (i , j)))
                        (neg3 (dx (λ q → proj₂ (B q)) (i , j)))) ⟩
  add3 (dy (λ q → proj₁ (A q)) (i , j))
       (add3 (dy (λ q → proj₁ (B q)) (i , j))
             (add3 (neg3 (dx (λ q → proj₂ (A q)) (i , j)))
                   (neg3 (dx (λ q → proj₂ (B q)) (i , j)))))
    ≡⟨ cong (add3 (dy (λ q → proj₁ (A q)) (i , j)))
            (sym (add3-assoc (dy (λ q → proj₁ (B q)) (i , j))
                             (neg3 (dx (λ q → proj₂ (A q)) (i , j)))
                             (neg3 (dx (λ q → proj₂ (B q)) (i , j))))) ⟩
  add3 (dy (λ q → proj₁ (A q)) (i , j))
       (add3 (add3 (dy (λ q → proj₁ (B q)) (i , j))
                   (neg3 (dx (λ q → proj₂ (A q)) (i , j))))
             (neg3 (dx (λ q → proj₂ (B q)) (i , j))))
    ≡⟨ cong (add3 (dy (λ q → proj₁ (A q)) (i , j)))
            (cong (λ t → add3 t (neg3 (dx (λ q → proj₂ (B q)) (i , j))))
                  (add3-comm (dy (λ q → proj₁ (B q)) (i , j))
                             (neg3 (dx (λ q → proj₂ (A q)) (i , j))))) ⟩
  add3 (dy (λ q → proj₁ (A q)) (i , j))
       (add3 (add3 (neg3 (dx (λ q → proj₂ (A q)) (i , j)))
                   (dy (λ q → proj₁ (B q)) (i , j)))
             (neg3 (dx (λ q → proj₂ (B q)) (i , j))))
    ≡⟨ cong (add3 (dy (λ q → proj₁ (A q)) (i , j)))
            (add3-assoc (neg3 (dx (λ q → proj₂ (A q)) (i , j)))
                        (dy (λ q → proj₁ (B q)) (i , j))
                        (neg3 (dx (λ q → proj₂ (B q)) (i , j)))) ⟩
  add3 (dy (λ q → proj₁ (A q)) (i , j))
       (add3 (neg3 (dx (λ q → proj₂ (A q)) (i , j)))
             (add3 (dy (λ q → proj₁ (B q)) (i , j))
                   (neg3 (dx (λ q → proj₂ (B q)) (i , j)))))
    ≡⟨ sym (add3-assoc (dy (λ q → proj₁ (A q)) (i , j))
                       (neg3 (dx (λ q → proj₂ (A q)) (i , j)))
                       (add3 (dy (λ q → proj₁ (B q)) (i , j))
                             (neg3 (dx (λ q → proj₂ (B q)) (i , j))))) ⟩
  add3 (curl A (i , j)) (curl B (i , j)) ∎

-- 规范不变性: 加规范梯度不改变旋度 (A' = A ⊕a grad φ)
gauge-invariance : ∀ A φ p → curl (A ⊕a grad φ) p ≡ curl A p
gauge-invariance A φ p = begin
  curl (A ⊕a grad φ) p
    ≡⟨ curl-linear A (grad φ) p ⟩
  add3 (curl A p) (curl (grad φ) p)
    ≡⟨ cong (add3 (curl A p)) (grad-curl-zero φ p) ⟩
  add3 (curl A p) fz
    ≡⟨ add3-identity (curl A p) ⟩
  curl A p ∎

-- 0 postulate.
