{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Synthesis.Physics.S6EFGAxial
-- S₆ (= C₃ᵢ) 位点下，**电场梯度张量只能是一个轴向张量**
--
-- 数学背景：低温 C₆₀ 的 Pa-3 相中，笼中心位点对称性为 S₆，
--   三重轴沿立方 [111]。S₆ 含三阶旋转 C₃ 与**反演 i**。
--   二阶（无迹、对称）张量对反演不变，所以约束只来自 C₃。
--
-- 本模块证明：若 3×3 整数张量 M 满足
--   (1) 对称：      M i j ≡ M j i
--   (2) 无迹：      M 0 0 + M 1 1 + M 2 2 ≡ 0
--   (3) C₃ 不变：   M (σ i) (σ j) ≡ M i j,  σ 为循环置换 (0↦1↦2↦0)
-- 则 M 必为
--   [[0, b, b], [b, 0, b], [b, b, 0]]
-- 即**沿 [111] 的轴向张量**（立方坐标系下 3nnᵀ−I 的形状）。
--
-- 本模块**证明到**的地方（内核定理 `s6-efg-axial`）：
--   张量形状唯一 ⇒ 由 EFG 诱导的微扰在 J=1 子空间里只可能是 a·I + b·J_z² 型
--   （因为 J=1 的 m 基下 J_z² 正对应形状 diag(1,1,-2)，与 3nnᵀ−I 同构）。
--
-- **本模块没有证明**的部分（[直觉·未验证]，缺 J=1 表示论 + 谱定理）：
--   「J=1 三重态必然分裂为 2+1」——需要先把 EFG 张量到 J=1 算符的映射写出来
--   （即 ⟨1m| Q·∇E |1m'⟩ 的矩阵元），再对角化。本库目前**没有**这条链。
--   当前 status：物理上标准（S₆ 轴对称 ⇒ 微扰只含 J_z² ⇒ 2+1），
--   但**不是本模块的内核结论**。
--
-- 方法：不用矩阵乘法——直接把 "C₃ 不变" 写成索引关系 M (σ i) (σ j) ≡ M i j。
module Sovereign.Synthesis.Physics.S6EFGAxial where

open import Data.Fin using (Fin; zero; suc)
open import Data.Integer using (ℤ; +_; +0; +[1+_]; -[1+_]; _+_; _*_; -_)
open import Data.Integer.Properties
  using (*-identityʳ; +-identityʳ; +-identityˡ; +-assoc; *-comm; +-comm)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; subst)

-- 3×3 张量（对称性作为假设给出）
Tensor : Set
Tensor = Fin 3 → Fin 3 → ℤ

-- ---------------------------------------------------------------------------
-- §1. 循环置换 σ : (0,1,2) ↦ (1,2,0)
-- ---------------------------------------------------------------------------
σ : Fin 3 → Fin 3
σ zero = suc zero
σ (suc zero) = suc (suc zero)
σ (suc (suc zero)) = zero

Sym : Tensor → Set
Sym M = ∀ i j → M i j ≡ M j i

Traceless : Tensor → Set
Traceless M = M zero zero + M (suc zero) (suc zero) + M (suc (suc zero)) (suc (suc zero)) ≡ +0

-- C₃ 不变：M (σ i) (σ j) ≡ M i j
C3Inv : Tensor → Set
C3Inv M = ∀ i j → M (σ i) (σ j) ≡ M i j

-- ---------------------------------------------------------------------------
-- §2. 对角元全部相等
-- ---------------------------------------------------------------------------
-- M 1 1 ≡ M 0 0
d00-11 : ∀ M → C3Inv M → M (suc zero) (suc zero) ≡ M zero zero
d00-11 M H = H zero zero

-- M 2 2 ≡ M 1 1
d11-22 : ∀ M → C3Inv M → M (suc (suc zero)) (suc (suc zero)) ≡ M (suc zero) (suc zero)
d11-22 M H = H (suc zero) (suc zero)

-- 三个对角元相等
diag-eq : ∀ M → C3Inv M → M (suc (suc zero)) (suc (suc zero)) ≡ M zero zero
diag-eq M H = trans (d11-22 M H) (d00-11 M H)

-- ---------------------------------------------------------------------------
-- §3. 三个 "环上" 的非对角元相等，其余为零
-- ---------------------------------------------------------------------------
-- M 1 2 ≡ M 0 1
nd-12-01 : ∀ M → C3Inv M → M (suc zero) (suc (suc zero)) ≡ M zero (suc zero)
nd-12-01 M H = H zero (suc zero)

-- M 0 2 ≡ M 1 2  （用对称把 M (σ 1) (σ 2) = M 2 0 转成 M 0 2）
nd-02-12 : ∀ M → Sym M → C3Inv M
         → M zero (suc (suc zero)) ≡ M (suc zero) (suc (suc zero))
nd-02-12 M S H =
  trans (S zero (suc (suc zero))) (H (suc zero) (suc (suc zero)))

-- 所以 M 0 1 ≡ M 1 2 ≡ M 0 2
nd-all-eq : ∀ M → Sym M → C3Inv M
          → (M zero (suc zero) ≡ M (suc zero) (suc (suc zero)))
          × (M zero (suc (suc zero)) ≡ M (suc zero) (suc (suc zero)))
nd-all-eq M S H = sym (nd-12-01 M H) , nd-02-12 M S H

-- ---------------------------------------------------------------------------
-- §4. 无挠性：3 * n ≡ 0 ⇒ n ≡ 0（整数特例）
-- ---------------------------------------------------------------------------
-- 用三倍展开直接判定：3 * a 的形状由 a 的形状决定
3*a≡0 : ∀ a → a + a + a ≡ +0 → a ≡ +0
3*a≡0 (+0) eq = refl
3*a≡0 +[1+ n ] ()
3*a≡0 -[1+ n ] ()

-- ---------------------------------------------------------------------------
-- §5. 主定理：对角元为零、非对角元三相等
-- ---------------------------------------------------------------------------
-- 由 (1)(2)(3) 得 M 0 0 ≡ 0
diag-zero : ∀ M → C3Inv M → Traceless M → M zero zero ≡ +0
diag-zero M H T = 3*a≡0 (M zero zero) triple
  where
    a = M zero zero
    b = M (suc zero) (suc zero)
    c = M (suc (suc zero)) (suc (suc zero))
    e1 : a + b + c ≡ a + a + c
    e1 = cong (λ x → a + x + c) (d00-11 M H)
    e2 : a + a + c ≡ a + a + a
    e2 = cong (λ y → a + a + y) (diag-eq M H)
    triple : a + a + a ≡ +0
    triple = trans (sym e2) (trans (sym e1) T)

-- ---------------------------------------------------------------------------
-- §6. 结论：张量必为 [[0,b,b],[b,0,b],[b,b,0]]
-- ---------------------------------------------------------------------------
record AxialShape (M : Tensor) : Set where
  field
    diagIsZero : (M zero zero ≡ +0)
                 × (M (suc zero) (suc zero) ≡ +0)
                 × (M (suc (suc zero)) (suc (suc zero)) ≡ +0)
    offDiagEqual : (M zero (suc zero) ≡ M (suc zero) (suc (suc zero)))
                   × (M zero (suc (suc zero)) ≡ M (suc zero) (suc (suc zero)))

s6-efg-axial : ∀ M → Sym M → C3Inv M → Traceless M → AxialShape M
s6-efg-axial M S H T = record
  { diagIsZero = diag-zero M H T
               , trans (d00-11 M H) (diag-zero M H T)
               , trans (diag-eq M H) (diag-zero M H T)
  ; offDiagEqual = nd-all-eq M S H
  }
