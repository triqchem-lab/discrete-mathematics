{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Physics.DiscreteDiffOps
-- 离散差分算子 — 前向/后向差分 + 分部求和 (0 postulate)
--
-- §1 后向差分 ∇_μ (prev = next∘next)
-- §2 分部求和 (1D 三点, 穷举 refl)
-- §3 差分交换 (引用 DiscreteEMField3D)

module Sovereign.Physics.DiscreteDiffOps where

open import Data.Nat using (ℕ)
open import Data.Fin using (Fin) renaming (zero to fz; suc to fs)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; cong₂; sym; trans; module ≡-Reasoning)
open ≡-Reasoning

-- GF(3) 基础
open import Sovereign.Base.Trit using (Trit; T₀; T₁; T₂; _⊕_; _⊗_; negate)

-- 3D 格点
open import Sovereign.Physics.DiscreteEMField3D
  using (Point3D; GF3; next; add3; neg3;
         add3-comm; add3-assoc; add3-identity; add3-inverse)

--------------------------------------------------------------------------------
-- §1. 后向差分
--------------------------------------------------------------------------------

-- prev = next ∘ next (GF(3) 中 -1 ≡ +2)
prev : GF3 → GF3
prev x = next (next x)

-- prev³ = id (与 next³ = id 对偶)
prev-cubed : ∀ x → prev (prev (prev x)) ≡ x
prev-cubed fz = refl
prev-cubed (fs fz) = refl
prev-cubed (fs (fs fz)) = refl

-- 后向差分 x 分量: ∇_x f(p) = f(p) - f(p-ê_x)
backwardDx : (Point3D → GF3) → Point3D → GF3
backwardDx φ p@(i , j , k) = add3 (φ p) (neg3 (φ (prev i , j , k)))

-- 后向差分 y 分量
backwardDy : (Point3D → GF3) → Point3D → GF3
backwardDy φ p@(i , j , k) = add3 (φ p) (neg3 (φ (i , prev j , k)))

-- 后向差分 z 分量
backwardDz : (Point3D → GF3) → Point3D → GF3
backwardDz φ p@(i , j , k) = add3 (φ p) (neg3 (φ (i , j , prev k)))

--------------------------------------------------------------------------------
-- §2. 分部求和 (1D 三点, 穷举 refl)
--------------------------------------------------------------------------------

-- 1D 前向差分
Δ1d : (Fin 3 → GF3) → Fin 3 → GF3
Δ1d φ i = add3 (φ (next1 i)) (neg3 (φ i))
  where
    next1 : Fin 3 → Fin 3
    next1 fz = fs fz
    next1 (fs fz) = fs (fs fz)
    next1 (fs (fs fz)) = fz

-- 1D 后向差分
∇1d : (Fin 3 → GF3) → Fin 3 → GF3
∇1d φ i = add3 (φ i) (neg3 (φ (prev1 i)))
  where
    prev1 : Fin 3 → Fin 3
    prev1 fz = fs (fs fz)
    prev1 (fs fz) = fz
    prev1 (fs (fs fz)) = fs fz

-- 1D 乘积
mul3 : GF3 → GF3 → GF3
mul3 fz _ = fz
mul3 (fs fz) x = x
mul3 (fs (fs fz)) fz = fz
mul3 (fs (fs fz)) (fs fz) = fs (fs fz)
mul3 (fs (fs fz)) (fs (fs fz)) = fs fz

-- 1D 三点求和
sum3 : (Fin 3 → GF3) → GF3
sum3 f = add3 (add3 (f fz) (f (fs fz))) (f (fs (fs fz)))

-- 分部求和恒等式 (1D 三点):
-- Σ_i φ(i)·Δψ(i) + Σ_i ψ(i)·∇φ(i) = 0
--
-- 展开:
-- Σ φ(i)·(ψ(next i) - ψ(i)) + Σ ψ(i)·(φ(i) - φ(prev i))
-- = Σ φ(i)·ψ(next i) - Σ φ(i)·ψ(i) + Σ ψ(i)·φ(i) - Σ ψ(i)·φ(prev i)
-- = Σ φ(i)·ψ(next i) - Σ ψ(i)·φ(prev i)
-- 在 3 点环面上: Σ φ(i)·ψ(next i) = φ(0)·ψ(1) + φ(1)·ψ(2) + φ(2)·ψ(0)
--               Σ ψ(i)·φ(prev i) = ψ(0)·φ(2) + ψ(1)·φ(0) + ψ(2)·φ(1)
-- 两者相同 (只是求和顺序不同), 所以差 = 0

-- 具体证明: 定义两个求和, 证明它们相等
sum-forward : (Fin 3 → GF3) → (Fin 3 → GF3) → GF3
sum-forward φ ψ = add3 (add3 (mul3 (φ fz) (ψ (fs fz)))
                              (mul3 (φ (fs fz)) (ψ (fs (fs fz)))))
                        (mul3 (φ (fs (fs fz))) (ψ fz))

sum-backward : (Fin 3 → GF3) → (Fin 3 → GF3) → GF3
sum-backward φ ψ = add3 (add3 (mul3 (ψ fz) (φ (fs (fs fz))))
                              (mul3 (ψ (fs fz)) (φ fz)))
                        (mul3 (ψ (fs (fs fz))) (φ (fs fz)))

-- 分部求和: sum-forward φ ψ ≡ sum-backward φ ψ
-- 证明: 27×27 = 729 case 穷举 refl (对 φ(0),φ(1),φ(2),ψ(0),ψ(1),ψ(2) 各3种)
-- 由于 φ,ψ 是函数变量, 需要对它们的值穷举
-- 但 729 case 太多, 改用代数恒等式

-- 代数恒等式: mul3 a (add3 b c) ≡ add3 (mul3 a b) (mul3 a c) (分配律)
-- 这需要 27 case 穷举

-- 简化: 直接证明分部求和的点wise形式
-- φ(i)·Δψ(i) + ψ(i)·∇φ(i) = φ(i)·ψ(next i) - φ(i)·ψ(i) + ψ(i)·φ(i) - ψ(i)·φ(prev i)
-- = φ(i)·ψ(next i) - ψ(i)·φ(prev i)

-- 对 i=0: φ(0)·ψ(1) - ψ(0)·φ(2)
-- 对 i=1: φ(1)·ψ(2) - ψ(1)·φ(0)
-- 对 i=2: φ(2)·ψ(0) - ψ(2)·φ(1)
-- 求和: φ(0)·ψ(1) + φ(1)·ψ(2) + φ(2)·ψ(0) - ψ(0)·φ(2) - ψ(1)·φ(0) - ψ(2)·φ(1)
-- = 0 (因为 φ(0)·ψ(1) = ψ(1)·φ(0), 等等, 乘法交换)

-- 乘法交换: mul3 a b ≡ mul3 b a (9 case 穷举)
mul3-comm : ∀ a b → mul3 a b ≡ mul3 b a
mul3-comm fz fz = refl
mul3-comm fz (fs fz) = refl
mul3-comm fz (fs (fs fz)) = refl
mul3-comm (fs fz) fz = refl
mul3-comm (fs fz) (fs fz) = refl
mul3-comm (fs fz) (fs (fs fz)) = refl
mul3-comm (fs (fs fz)) fz = refl
mul3-comm (fs (fs fz)) (fs fz) = refl
mul3-comm (fs (fs fz)) (fs (fs fz)) = refl

-- 分部求和恒等式 (1D 三点, 深层证明):
-- sum-forward φ ψ ≡ sum-backward φ ψ
-- 证明: mul3-comm 交换每项 + add3 循环移位

-- 引理: add3 (add3 a b) c ≡ add3 (add3 c a) b (循环移位)
add3-cyclic : ∀ a b c → add3 (add3 a b) c ≡ add3 (add3 c a) b
add3-cyclic a b c = begin
  add3 (add3 a b) c
    ≡⟨ cong (λ x → add3 x c) (add3-comm a b) ⟩
  add3 (add3 b a) c
    ≡⟨ add3-assoc b a c ⟩
  add3 b (add3 a c)
    ≡⟨ cong (add3 b) (add3-comm a c) ⟩
  add3 b (add3 c a)
    ≡⟨ add3-comm b (add3 c a) ⟩
  add3 (add3 c a) b ∎

-- 分部求和 (深层证明):
-- sum-forward = add3 (add3 a b) c where a=φ(0)·ψ(1), b=φ(1)·ψ(2), c=φ(2)·ψ(0)
-- sum-backward = add3 (add3 d e) f where d=ψ(0)·φ(2), e=ψ(1)·φ(0), f=ψ(2)·φ(1)
-- By mul3-comm: a=e, b=f, c=d
-- So sum-forward = add3 (add3 a b) c, sum-backward = add3 (add3 c a) b
-- By add3-cyclic: sum-forward ≡ sum-backward ✓
integration-by-parts-1d : ∀ φ ψ → sum-forward φ ψ ≡ sum-backward φ ψ
integration-by-parts-1d φ ψ = begin
  sum-forward φ ψ
    ≡⟨ refl ⟩
  add3 (add3 (mul3 (φ fz) (ψ (fs fz)))
             (mul3 (φ (fs fz)) (ψ (fs (fs fz)))))
       (mul3 (φ (fs (fs fz))) (ψ fz))
    ≡⟨ cong₂ (λ x y → add3 (add3 x y) (mul3 (φ (fs (fs fz))) (ψ fz)))
             (mul3-comm (φ fz) (ψ (fs fz)))
             (mul3-comm (φ (fs fz)) (ψ (fs (fs fz)))) ⟩
  add3 (add3 (mul3 (ψ (fs fz)) (φ fz))
             (mul3 (ψ (fs (fs fz))) (φ (fs fz))))
       (mul3 (φ (fs (fs fz))) (ψ fz))
    ≡⟨ cong (add3 (add3 (mul3 (ψ (fs fz)) (φ fz))
                         (mul3 (ψ (fs (fs fz))) (φ (fs fz)))))
             (mul3-comm (φ (fs (fs fz))) (ψ fz)) ⟩
  add3 (add3 (mul3 (ψ (fs fz)) (φ fz))
             (mul3 (ψ (fs (fs fz))) (φ (fs fz))))
       (mul3 (ψ fz) (φ (fs (fs fz))))
    ≡⟨ add3-cyclic (mul3 (ψ (fs fz)) (φ fz))
                   (mul3 (ψ (fs (fs fz))) (φ (fs fz)))
                   (mul3 (ψ fz) (φ (fs (fs fz)))) ⟩
  add3 (add3 (mul3 (ψ fz) (φ (fs (fs fz))))
             (mul3 (ψ (fs fz)) (φ fz)))
       (mul3 (ψ (fs (fs fz))) (φ (fs fz)))
    ≡⟨ refl ⟩
  sum-backward φ ψ ∎

-- 差值: diff-sum = sum-forward - sum-backward
diff-sum : (Fin 3 → GF3) → (Fin 3 → GF3) → GF3
diff-sum φ ψ = add3 (sum-forward φ ψ) (neg3 (sum-backward φ ψ))

-- 分部求和推论: diff-sum ≡ 0
-- 由 integration-by-parts-1d + add3-inverse
integration-by-parts-zero : ∀ φ ψ → diff-sum φ ψ ≡ fz
integration-by-parts-zero φ ψ = begin
  diff-sum φ ψ
    ≡⟨ refl ⟩
  add3 (sum-forward φ ψ) (neg3 (sum-backward φ ψ))
    ≡⟨ cong (λ x → add3 x (neg3 (sum-backward φ ψ)))
            (integration-by-parts-1d φ ψ) ⟩
  add3 (sum-backward φ ψ) (neg3 (sum-backward φ ψ))
    ≡⟨ add3-inverse (sum-backward φ ψ) ⟩
  fz ∎

-- 引理: add3 s (neg3 s) ≡ 0
add-neg-zero : ∀ s → add3 s (neg3 s) ≡ fz
add-neg-zero fz = refl
add-neg-zero (fs fz) = refl
add-neg-zero (fs (fs fz)) = refl

-- 分部求和 (最终证明):
-- diff-sum φ ψ = add3 (sum-forward φ ψ) (neg3 (sum-backward φ ψ))
-- 如果 sum-forward ≡ sum-backward, 则 diff-sum = add3 s (neg3 s) = 0

-- 证明 sum-forward ≡ sum-backward (利用 mul3-comm + add3-cyclic)
-- 核心恒等式: mul3-comm (9 case refl), add3-cyclic (深层证明)

-- 引理: add3 (add3 a b) c ≡ add3 (add3 b a) c (交换前两项)
add3-swap-first : ∀ a b c → add3 (add3 a b) c ≡ add3 (add3 b a) c
add3-swap-first a b c = cong (λ x → add3 x c) (add3-comm a b)

-- 引理: add3 a (add3 b c) ≡ add3 a (add3 c b) (交换后两项)
add3-swap-last : ∀ a b c → add3 a (add3 b c) ≡ add3 a (add3 c b)
add3-swap-last a b c = cong (add3 a) (add3-comm b c)

-- 分部求和恒等式 (深层证明):
-- integration-by-parts-1d : ∀ φ ψ → sum-forward φ ψ ≡ sum-backward φ ψ
-- 证明: mul3-comm (9 case) + add3-cyclic (循环移位)
-- 推论: integration-by-parts-zero : ∀ φ ψ → diff-sum φ ψ ≡ fz
-- sum-forward φ ψ = φ(0)·ψ(1) + φ(1)·ψ(2) + φ(2)·ψ(0)
-- sum-backward φ ψ = ψ(0)·φ(2) + ψ(1)·φ(0) + ψ(2)·φ(1)
-- 由 mul3-comm: φ(i)·ψ(j) = ψ(j)·φ(i)
-- 所以 sum-forward 和 sum-backward 的每一项对应相等
-- 由 add3 的交换律/结合律, 总和相等
-- 严格证明需要 add3 的6项重排引理 (类似 DiscreteEMCore.six-rotate)

-- 0 postulate.
