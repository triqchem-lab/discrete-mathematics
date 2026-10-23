{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Synthesis.Physics.NoSplitJ1Full
-- 「与 A₄ 交换的 3×3 整矩阵必为标量」——一般（含非对角）情形
--
-- 与 NoSplitJ1 的关系：NoSplitJ1 只证**对角**情形；本模块补上非对角。
--
-- 方法：不引入一般矩阵乘法，直接按「在基向量上的作用」展开。
--   NSFapply A v i = A i 0 * v 0 + A i 1 * v 1 + A i 2 * v 2
--   在 e₀/e₁/e₂ 上取值时，乘 0/1 的项由 stdlib 引理消去。
-- 无挠性（-x ≡ x ⇒ x ≡ 0）由**构造子互异**直接给出（+[1+n] 与 -[1+n] 是不同构造子）。
--
-- 主定理（已证）：`no-split-full` —— 若整矩阵 A 与 NSFshift（3-循环）和 NSFflip（反演型 180° 旋转）
--   都交换，则 6 个非对角元全为 0，且三个对角元相等 ⇒ A 是标量矩阵。
--   **生成元就是 A₄**（数值核验，2026-10-22）：{NSFshift, NSFflip} 在复合下的闭包 = **12 阶**，
--   全部是 det = +1 的有符号置换矩阵 ⇒ 正是 A₄ ⊂ SO(3) 的 3 维表示；且
--   ord(NSFshift)=3、ord(NSFflip)=2、ord(NSFflip∘NSFshift)=3 ⇒ 展示关系 ⟨s,f | s³=f²=(fs)³=1⟩ 与 A₄ 一致。
--   Agda 侧已证 s³ = id（shift³）、f² = id（flip²）、(fs)³ = id（g³，NSFg = NSFflip ∘ NSFshift）
--   ⇒ A₄ 的展示关系全部落在内核里；只剩「12 个矩阵的枚举」是 oracle 数值核验。
--   故 A₄ 的交换子代数 ⊆ 这两个元素的交换子代数 = 标量 ⇒
--   **A₄ 不变微扰不能劈裂 J=1 三重态**（一般情形，含非对角）。
--
-- 0 postulate / 0 hole。
module Sovereign.Synthesis.Physics.NoSplitJ1Full where

open import Data.Fin using (Fin; zero; suc)
open import Data.Integer using (ℤ; +_; +0; +[1+_]; -[1+_]; _+_; _*_; -_)
open import Data.Integer.Properties using (+-identityʳ; +-identityˡ; *-identityʳ; *-zeroʳ; *-comm; -1*i≡-i; neg-involutive)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)

--------------------------------------------------------------------------------
-- §1. 载体与基向量
--------------------------------------------------------------------------------
NSFV : Set
NSFV = Fin 3 → ℤ

NSFe0 : NSFV
NSFe0 zero = + 1
NSFe0 (suc zero) = +0
NSFe0 (suc (suc zero)) = +0

NSFe1 : NSFV
NSFe1 zero = +0
NSFe1 (suc zero) = + 1
NSFe1 (suc (suc zero)) = +0

NSFe2 : NSFV
NSFe2 zero = +0
NSFe2 (suc zero) = +0
NSFe2 (suc (suc zero)) = + 1

--------------------------------------------------------------------------------
-- §2. 逐分量算术
--------------------------------------------------------------------------------
+0ʳ : ∀ x → x + +0 ≡ x
+0ʳ = +-identityʳ

*1ʳ : ∀ x → x * (+ 1) ≡ x
*1ʳ = *-identityʳ

*0ʳ : ∀ x → x * +0 ≡ +0
*0ʳ = *-zeroʳ

*-1ʳ : ∀ x → x * (- (+ 1)) ≡ - x
*-1ʳ x = trans (*-comm x (- (+ 1))) (-1*i≡-i x)

-- 无挠性：- x ≡ x ⇒ x ≡ +0（非零情形由构造子互异排除）
neg-eq-self : ∀ x → - x ≡ x → x ≡ +0
neg-eq-self +0 eq = refl
neg-eq-self +[1+ n ] ()
neg-eq-self -[1+ n ] ()

--------------------------------------------------------------------------------
-- §3. 矩阵在向量上的作用、两个生成元
--------------------------------------------------------------------------------
NSFapply : (Fin 3 → Fin 3 → ℤ) → NSFV → NSFV
NSFapply A v zero = A zero zero * v zero + A zero (suc zero) * v (suc zero)
                 + A zero (suc (suc zero)) * v (suc (suc zero))
NSFapply A v (suc zero) = A (suc zero) zero * v zero + A (suc zero) (suc zero) * v (suc zero)
                       + A (suc zero) (suc (suc zero)) * v (suc (suc zero))
NSFapply A v (suc (suc zero)) = A (suc (suc zero)) zero * v zero
                             + A (suc (suc zero)) (suc zero) * v (suc zero)
                             + A (suc (suc zero)) (suc (suc zero)) * v (suc (suc zero))

NSFshift : NSFV → NSFV                       -- 3-循环 (v₀,v₁,v₂) ↦ (v₂,v₀,v₁)
NSFshift v zero = v (suc (suc zero))
NSFshift v (suc zero) = v zero
NSFshift v (suc (suc zero)) = v (suc zero)

NSFflip : NSFV → NSFV                        -- (v₀,v₁,v₂) ↦ (−v₀,−v₁,v₂)
NSFflip v zero = - v zero
NSFflip v (suc zero) = - v (suc zero)
NSFflip v (suc (suc zero)) = v (suc (suc zero))

--------------------------------------------------------------------------------
-- §4. 基向量上取值 = 取列
--------------------------------------------------------------------------------
apply-e0 : ∀ A i → NSFapply A NSFe0 i ≡ A i zero
apply-e0 A zero rewrite *1ʳ (A zero zero) | *0ʳ (A zero (suc zero)) | *0ʳ (A zero (suc (suc zero))) | +0ʳ (A zero zero) | +0ʳ (A zero zero) = refl
apply-e0 A (suc zero) rewrite *1ʳ (A (suc zero) zero) | *0ʳ (A (suc zero) (suc zero)) | *0ʳ (A (suc zero) (suc (suc zero))) | +0ʳ (A (suc zero) zero) | +0ʳ (A (suc zero) zero) = refl
apply-e0 A (suc (suc zero)) rewrite *1ʳ (A (suc (suc zero)) zero) | *0ʳ (A (suc (suc zero)) (suc zero)) | *0ʳ (A (suc (suc zero)) (suc (suc zero))) | +0ʳ (A (suc (suc zero)) zero) | +0ʳ (A (suc (suc zero)) zero) = refl

apply-e1 : ∀ A i → NSFapply A NSFe1 i ≡ A i (suc zero)
apply-e1 A zero rewrite *1ʳ (A zero (suc zero)) | *0ʳ (A zero zero) | *0ʳ (A zero (suc (suc zero))) | +-identityˡ (A zero (suc zero)) | +0ʳ (A zero (suc zero)) = refl
apply-e1 A (suc zero) rewrite *1ʳ (A (suc zero) (suc zero)) | *0ʳ (A (suc zero) zero) | *0ʳ (A (suc zero) (suc (suc zero))) | +-identityˡ (A (suc zero) (suc zero)) | +0ʳ (A (suc zero) (suc zero)) = refl
apply-e1 A (suc (suc zero)) rewrite *1ʳ (A (suc (suc zero)) (suc zero)) | *0ʳ (A (suc (suc zero)) zero) | *0ʳ (A (suc (suc zero)) (suc (suc zero))) | +-identityˡ (A (suc (suc zero)) (suc zero)) | +0ʳ (A (suc (suc zero)) (suc zero)) = refl

apply-e2 : ∀ A i → NSFapply A NSFe2 i ≡ A i (suc (suc zero))
apply-e2 A zero rewrite *1ʳ (A zero (suc (suc zero))) | *0ʳ (A zero zero) | *0ʳ (A zero (suc zero)) | +-identityˡ (+0) | +-identityˡ (A zero (suc (suc zero))) = refl
apply-e2 A (suc zero) rewrite *1ʳ (A (suc zero) (suc (suc zero))) | *0ʳ (A (suc zero) zero) | *0ʳ (A (suc zero) (suc zero)) | +-identityˡ (+0) | +-identityˡ (A (suc zero) (suc (suc zero))) = refl
apply-e2 A (suc (suc zero)) rewrite *1ʳ (A (suc (suc zero)) (suc (suc zero))) | *0ʳ (A (suc (suc zero)) zero) | *0ʳ (A (suc (suc zero)) (suc zero)) | +-identityˡ (+0) | +-identityˡ (A (suc (suc zero)) (suc (suc zero))) = refl

apply-flip-e0 : ∀ A i → NSFapply A (NSFflip NSFe0) i ≡ - (A i zero)
apply-flip-e0 A zero rewrite *-1ʳ (A zero zero) | *0ʳ (A zero (suc zero))
                            | *0ʳ (A zero (suc (suc zero)))
                            | +0ʳ (- (A zero zero)) | +0ʳ (- (A zero zero)) = refl
apply-flip-e0 A (suc zero) rewrite *-1ʳ (A (suc zero) zero)
                                  | *0ʳ (A (suc zero) (suc zero))
                                  | *0ʳ (A (suc zero) (suc (suc zero)))
                                  | +0ʳ (- (A (suc zero) zero))
                                  | +0ʳ (- (A (suc zero) zero)) = refl
apply-flip-e0 A (suc (suc zero)) rewrite *-1ʳ (A (suc (suc zero)) zero)
                                        | *0ʳ (A (suc (suc zero)) (suc zero))
                                        | *0ʳ (A (suc (suc zero)) (suc (suc zero)))
                                        | +0ʳ (- (A (suc (suc zero)) zero))
                                        | +0ʳ (- (A (suc (suc zero)) zero)) = refl
apply-flip-e1 : ∀ A i → NSFapply A (NSFflip NSFe1) i ≡ - (A i (suc zero))
apply-flip-e1 A zero rewrite *0ʳ (A zero zero) | *-1ʳ (A zero (suc zero)) | *0ʳ (A zero (suc (suc zero))) | +-identityˡ (- (A zero (suc zero))) | +0ʳ (- (A zero (suc zero))) = refl
apply-flip-e1 A (suc zero) rewrite *0ʳ (A (suc zero) zero) | *-1ʳ (A (suc zero) (suc zero)) | *0ʳ (A (suc zero) (suc (suc zero))) | +-identityˡ (- (A (suc zero) (suc zero))) | +0ʳ (- (A (suc zero) (suc zero))) = refl
apply-flip-e1 A (suc (suc zero)) rewrite *0ʳ (A (suc (suc zero)) zero) | *-1ʳ (A (suc (suc zero)) (suc zero)) | *0ʳ (A (suc (suc zero)) (suc (suc zero))) | +-identityˡ (- (A (suc (suc zero)) (suc zero))) | +0ʳ (- (A (suc (suc zero)) (suc zero))) = refl

--------------------------------------------------------------------------------
-- §5. 两条交换性假设与由此导出的分量关系
--------------------------------------------------------------------------------
Commutes-shift : (Fin 3 → Fin 3 → ℤ) → Set
Commutes-shift A = ∀ v i → NSFapply A (NSFshift v) i ≡ NSFshift (NSFapply A v) i

Commutes-flip : (Fin 3 → Fin 3 → ℤ) → Set
Commutes-flip A = ∀ v i → NSFapply A (NSFflip v) i ≡ NSFflip (NSFapply A v) i

-- 3-循环给出的循环关系（9 条，取需要的 6 条）
c01-20 : ∀ A → Commutes-shift A → A zero (suc zero) ≡ A (suc (suc zero)) zero
c01-20 A H = trans (sym (apply-e1 A zero)) (trans (H NSFe0 zero) (apply-e0 A (suc (suc zero))))

c11-00 : ∀ A → Commutes-shift A → A (suc zero) (suc zero) ≡ A zero zero
c11-00 A H = trans (sym (apply-e1 A (suc zero))) (trans (H NSFe0 (suc zero)) (apply-e0 A zero))

c21-10 : ∀ A → Commutes-shift A → A (suc (suc zero)) (suc zero) ≡ A (suc zero) zero
c21-10 A H = trans (sym (apply-e1 A (suc (suc zero))))
                   (trans (H NSFe0 (suc (suc zero))) (apply-e0 A (suc zero)))

c02-21 : ∀ A → Commutes-shift A → A zero (suc (suc zero)) ≡ A (suc (suc zero)) (suc zero)
c02-21 A H = trans (sym (apply-e2 A zero)) (trans (H NSFe1 zero) (apply-e1 A (suc (suc zero))))

c12-01 : ∀ A → Commutes-shift A → A (suc zero) (suc (suc zero)) ≡ A zero (suc zero)
c12-01 A H = trans (sym (apply-e2 A (suc zero))) (trans (H NSFe1 (suc zero)) (apply-e1 A zero))

c22-11 : ∀ A → Commutes-shift A → A (suc (suc zero)) (suc (suc zero)) ≡ A (suc zero) (suc zero)
c22-11 A H = trans (sym (apply-e2 A (suc (suc zero))))
                   (trans (H NSFe1 (suc (suc zero))) (apply-e1 A (suc zero)))

c10-02 : ∀ A → Commutes-shift A → A (suc zero) zero ≡ A zero (suc (suc zero))
c10-02 A H = trans (sym (apply-e0 A (suc zero))) (trans (H NSFe2 (suc zero)) (apply-e2 A zero))

c20-12 : ∀ A → Commutes-shift A → A (suc (suc zero)) zero ≡ A (suc zero) (suc (suc zero))
c20-12 A H = trans (sym (apply-e0 A (suc (suc zero))))
                   (trans (H NSFe2 (suc (suc zero))) (apply-e2 A (suc zero)))

-- 反演型元素给出的两条「自反 ⇒ 零」
n20 : ∀ A → Commutes-flip A → - (A (suc (suc zero)) zero) ≡ A (suc (suc zero)) zero
n20 A H = trans (sym (apply-flip-e0 A (suc (suc zero))))
                (trans (H NSFe0 (suc (suc zero))) (apply-e0 A (suc (suc zero))))

n21 : ∀ A → Commutes-flip A → - (A (suc (suc zero)) (suc zero)) ≡ A (suc (suc zero)) (suc zero)
n21 A H = trans (sym (apply-flip-e1 A (suc (suc zero))))
                (trans (H NSFe1 (suc (suc zero))) (apply-e1 A (suc (suc zero))))

--------------------------------------------------------------------------------
-- §6. 主定理：与两个生成元都交换的整矩阵必为标量
--------------------------------------------------------------------------------
no-split-full :
  ∀ A → Commutes-shift A → Commutes-flip A →
  (A zero (suc zero) ≡ +0) × (A zero (suc (suc zero)) ≡ +0)
  × (A (suc zero) zero ≡ +0) × (A (suc zero) (suc (suc zero)) ≡ +0)
  × (A (suc (suc zero)) zero ≡ +0) × (A (suc (suc zero)) (suc zero) ≡ +0)
  × (A zero zero ≡ A (suc zero) (suc zero))
  × (A (suc zero) (suc zero) ≡ A (suc (suc zero)) (suc (suc zero)))
no-split-full A Hs Hf = z01 , z02 , z10 , z12 , z20 , z21 , d01 , d12
  where
    z20 : A (suc (suc zero)) zero ≡ +0
    z20 = neg-eq-self (A (suc (suc zero)) zero) (n20 A Hf)

    z21 : A (suc (suc zero)) (suc zero) ≡ +0
    z21 = neg-eq-self (A (suc (suc zero)) (suc zero)) (n21 A Hf)

    z01 : A zero (suc zero) ≡ +0
    z01 = trans (c01-20 A Hs) z20

    z02 : A zero (suc (suc zero)) ≡ +0
    z02 = trans (c02-21 A Hs) z21

    z10 : A (suc zero) zero ≡ +0
    z10 = trans (c10-02 A Hs) z02

    z12 : A (suc zero) (suc (suc zero)) ≡ +0
    z12 = trans (c12-01 A Hs) z01

    d01 : A zero zero ≡ A (suc zero) (suc zero)
    d01 = sym (c11-00 A Hs)

    d12 : A (suc zero) (suc zero) ≡ A (suc (suc zero)) (suc (suc zero))
    d12 = sym (c22-11 A Hs)

--------------------------------------------------------------------------------
-- §7. 两个生成元的阶（展示关系 s³ = 1、f² = 1）
--------------------------------------------------------------------------------
-- 3-循环：shift³ = id（逐点定义性成立）
shift³ : ∀ v i → NSFshift (NSFshift (NSFshift v)) i ≡ v i
shift³ v zero = refl
shift³ v (suc zero) = refl
shift³ v (suc (suc zero)) = refl

-- 反演型：flip² = id（需 neg-involutive：- - x ≡ x）
flip² : ∀ v i → NSFflip (NSFflip v) i ≡ v i
flip² v zero = neg-involutive (v zero)
flip² v (suc zero) = neg-involutive (v (suc zero))
flip² v (suc (suc zero)) = refl

-- 复合 NSFg = NSFflip ∘ NSFshift 的阶为 3（展示关系 (fs)³ = 1）
NSFg : NSFV → NSFV
NSFg v = NSFflip (NSFshift v)

g³ : ∀ v i → NSFg (NSFg (NSFg v)) i ≡ v i
g³ v zero = neg-involutive (v zero)
g³ v (suc zero) = neg-involutive (v (suc zero))
g³ v (suc (suc zero)) = neg-involutive (v (suc (suc zero)))
