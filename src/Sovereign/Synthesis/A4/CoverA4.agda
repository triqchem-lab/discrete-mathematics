{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Synthesis.A4.CoverA4 —— **第 1 块（地基）**
--
-- 目标（T1 的 Agda 版）：把 "2A₄ = SL(2,F₃)" 从命名变成定理，路径是
--   SL(2,F₃) 在 P¹(F₃)（GF(3)² 的 4 条 1 维子空间）上的诱导置换。
--
-- 本文件落地**地基**（0 postulate / 0 hole）：
--   ① V2 = GF(3)² 的向量；negV 取负，negV-invol
--   ② 4 条线的规范代表 rep : Line → V2
--   ③ canon : V2 → V2（非零向量规范到线代表；零向量为占位）
--   ④ 矩阵作用 act : Mat2 → V2 → V2
--   ⑤ 关键引理：act-neg（作用线性）、canon-idem（规范化幂等）
--
-- 下一块（已规划）：lineOf / permOf、同态（用 act-neg + canon-idem + 矩阵结合律，
--   **不靠 24×24 枚举**）、像 = A₄、核 = {I,−I}。
--
-- 口径：所有 case 都是**有限构造子穷举**（Fin 3 / Line），非数值字面量暴力求值。
module Sovereign.Synthesis.A4.CoverA4 where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin using (Fin; zero; suc)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong; cong₂; module ≡-Reasoning)

open import Sovereign.Synthesis.Representation.Fin3Semiring
  using (neg3; mul3-distribˡ; neg3-zero; neg3-add; neg3-invol; neg3-mulʳ)

open import Sovereign.Algebra.LinearAlgebra.Matrix2
  using (m00; m01; m10; m11)

open import Sovereign.Synthesis.Representation.SL23Cayley
  using (Mat2; add3; mul3; toMat)
open import Sovereign.Synthesis.A4.BinaryTetrahedralDefiningRep
  using (SL23; g0; g1; g2; g3; g4; g5; g6; g7; g8; g9; g10; g11
        ; g12; g13; g14; g15; g16; g17; g18; g19; g20; g21; g22; g23)

open ≡-Reasoning

--------------------------------------------------------------------------------
-- ① GF(3)² 的向量
--------------------------------------------------------------------------------

record V2 : Set where
  constructor v2
  field
    vx vy : Fin 3

vzero : V2
vzero = v2 zero zero

negV : V2 → V2
negV (v2 x y) = v2 (neg3 x) (neg3 y)

negV-invol : ∀ v → negV (negV v) ≡ v
negV-invol (v2 x y) = cong₂ v2 (neg3-invol x) (neg3-invol y)

--------------------------------------------------------------------------------
-- ② 4 条线的规范代表（首非零坐标归一为 1）
--------------------------------------------------------------------------------

data Line : Set where
  L0 L1 L2 L3 : Line

rep : Line → V2
rep L0 = v2 (suc zero) zero                    -- {(1,0),(2,0)}
rep L1 = v2 zero (suc zero)                    -- {(0,1),(0,2)}
rep L2 = v2 (suc zero) (suc zero)              -- {(1,1),(2,2)}
rep L3 = v2 (suc zero) (suc (suc zero))        -- {(1,2),(2,1)}

--------------------------------------------------------------------------------
-- ③ canon：非零向量 → 所在线的代表
--
--   首坐标 = 1 ⇒ 原样；首坐标 = 2 ⇒ 取负（(2,y) ↦ (1,−y)）；
--   首坐标 = 0 ⇒ (0,1) 或 (0,2) 都是 L1。
--   零向量无定义，用 vzero 占位（下游只用非零向量）。
--------------------------------------------------------------------------------

canon : V2 → V2
canon (v2 zero zero)                       = vzero
canon (v2 zero (suc zero))                 = v2 zero (suc zero)
canon (v2 zero (suc (suc zero)))           = v2 zero (suc zero)
canon (v2 (suc zero) y)                    = v2 (suc zero) y
canon (v2 (suc (suc zero)) y)              = negV (v2 (suc (suc zero)) y)

canon-idem : ∀ v → canon (canon v) ≡ canon v
canon-idem (v2 zero zero)                  = refl
canon-idem (v2 zero (suc zero))            = refl
canon-idem (v2 zero (suc (suc zero)))      = refl
canon-idem (v2 (suc zero) zero)            = refl
canon-idem (v2 (suc zero) (suc zero))      = refl
canon-idem (v2 (suc zero) (suc (suc zero))) = refl
canon-idem (v2 (suc (suc zero)) zero)      = refl
canon-idem (v2 (suc (suc zero)) (suc zero)) = refl
canon-idem (v2 (suc (suc zero)) (suc (suc zero))) = refl

--------------------------------------------------------------------------------
-- ④ 矩阵作用
--------------------------------------------------------------------------------

act : Mat2 → V2 → V2
act m (v2 x y) =
  v2 (add3 (mul3 (m00 m) x) (mul3 (m01 m) y))
     (add3 (mul3 (m10 m) x) (mul3 (m11 m) y))

--------------------------------------------------------------------------------
-- ⑤ act-neg：作用与取负可交换（线性）
--
--   (a·(−x)) ⊕ (b·(−y)) = −(a·x) ⊕ −(b·y) = −((a·x) ⊕ (b·y))
--   第一、二步用 neg3-mulʳ，第三步用 neg3-add 的对称。
--------------------------------------------------------------------------------

act-neg : ∀ (m : Mat2) (v : V2) → act m (negV v) ≡ negV (act m v)
act-neg m (v2 x y) = cong₂ v2 row1 row2
  where
    row1 : add3 (mul3 (m00 m) (neg3 x)) (mul3 (m01 m) (neg3 y))
         ≡ neg3 (add3 (mul3 (m00 m) x) (mul3 (m01 m) y))
    row1 = begin
        add3 (mul3 (m00 m) (neg3 x)) (mul3 (m01 m) (neg3 y))
      ≡⟨ cong₂ add3 (neg3-mulʳ (m00 m) x) (neg3-mulʳ (m01 m) y) ⟩
        add3 (neg3 (mul3 (m00 m) x)) (neg3 (mul3 (m01 m) y))
      ≡⟨ sym (neg3-add (mul3 (m00 m) x) (mul3 (m01 m) y)) ⟩
        neg3 (add3 (mul3 (m00 m) x) (mul3 (m01 m) y))
      ∎
    row2 : add3 (mul3 (m10 m) (neg3 x)) (mul3 (m11 m) (neg3 y))
         ≡ neg3 (add3 (mul3 (m10 m) x) (mul3 (m11 m) y))
    row2 = begin
        add3 (mul3 (m10 m) (neg3 x)) (mul3 (m11 m) (neg3 y))
      ≡⟨ cong₂ add3 (neg3-mulʳ (m10 m) x) (neg3-mulʳ (m11 m) y) ⟩
        add3 (neg3 (mul3 (m10 m) x)) (neg3 (mul3 (m11 m) y))
      ≡⟨ sym (neg3-add (mul3 (m10 m) x) (mul3 (m11 m) y)) ⟩
        neg3 (add3 (mul3 (m10 m) x) (mul3 (m11 m) y))
      ∎

--------------------------------------------------------------------------------
-- ⑥ 线索引与诱导置换
--------------------------------------------------------------------------------

lineIdx : Line → Fin 4
lineIdx L0 = zero
lineIdx L1 = suc zero
lineIdx L2 = suc (suc zero)
lineIdx L3 = suc (suc (suc zero))

-- | 向量所在线（(0,0) 为占位，下游只用非零向量）
lineOf : V2 → Line
lineOf (v2 zero zero)                        = L0
lineOf (v2 zero (suc zero))                  = L1
lineOf (v2 zero (suc (suc zero)))            = L1
lineOf (v2 (suc zero) zero)                  = L0
lineOf (v2 (suc zero) (suc zero))            = L2
lineOf (v2 (suc zero) (suc (suc zero)))      = L3
lineOf (v2 (suc (suc zero)) zero)            = L0
lineOf (v2 (suc (suc zero)) (suc zero))      = L3
lineOf (v2 (suc (suc zero)) (suc (suc zero))) = L2

-- | 矩阵在 P¹(F₃) 上的诱导置换
permAt : Mat2 → Fin 4 → Fin 4
permAt m i = lineIdx (lineOf (act m (rep' i)))
  where
    rep' : Fin 4 → V2
    rep' zero                    = rep L0
    rep' (suc zero)              = rep L1
    rep' (suc (suc zero))        = rep L2
    rep' (suc (suc (suc zero)))  = rep L3

-- I（g6）与 −I（g15）都作用为恒等
perm-id : ∀ i → permAt (toMat g6) i ≡ i
perm-id zero                   = refl
perm-id (suc zero)             = refl
perm-id (suc (suc zero))       = refl
perm-id (suc (suc (suc zero))) = refl

perm-negI : ∀ i → permAt (toMat g15) i ≡ i
perm-negI zero                   = refl
perm-negI (suc zero)             = refl
perm-negI (suc (suc zero))       = refl
perm-negI (suc (suc (suc zero))) = refl

--------------------------------------------------------------------------------
-- ⑦ 核 = {I, −I}
--
-- 正向（⊆）：`perm-id` / `perm-negI`。
-- 反向（⊇）：24 个构造子上逐一给见证——除 g6（I）与 g15（−I）外，
--   都存在一个 i 使 permAt 把它送到别的线；于是"作用为恒等"的假设被 `λ ()` 反驳。
--   这是**构造子穷举**（SL23 的 24 个构造子），不是数值字面量暴力求值。
--------------------------------------------------------------------------------

-- Fin 4 的字面量（类型写死；裸 `zero`/`suc zero` 在 Fin 上是多态的，会留 meta）
f0 : Fin 4
f0 = zero
f1 : Fin 4
f1 = suc zero
f2 : Fin 4
f2 = suc (suc zero)
f3 : Fin 4
f3 = suc (suc (suc zero))

1≢0 : f1 ≢ f0
1≢0 = λ ()
2≢0 : f2 ≢ f0
2≢0 = λ ()
3≢0 : f3 ≢ f0
3≢0 = λ ()
2≢1 : f2 ≢ f1
2≢1 = λ ()
3≢1 : f3 ≢ f1
3≢1 = λ ()

-- | 核 = {I, −I}：24 个构造子逐一判定（构造子穷举，非数值暴力）
kernel-spec : ∀ (x : SL23) → (∀ i → permAt (toMat x) i ≡ i) → (x ≡ g6) ⊎ (x ≡ g15)
kernel-spec g0  hyp = ⊥-elim (1≢0 (hyp f0))
kernel-spec g1  hyp = ⊥-elim (1≢0 (hyp f0))
kernel-spec g2  hyp = ⊥-elim (1≢0 (hyp f0))
kernel-spec g3  hyp = ⊥-elim (1≢0 (hyp f0))
kernel-spec g4  hyp = ⊥-elim (1≢0 (hyp f0))
kernel-spec g5  hyp = ⊥-elim (1≢0 (hyp f0))
kernel-spec g6  hyp = inj₁ refl
kernel-spec g7  hyp = ⊥-elim (2≢0 (hyp f0))
kernel-spec g8  hyp = ⊥-elim (3≢0 (hyp f0))
kernel-spec g9  hyp = ⊥-elim (2≢1 (hyp f1))
kernel-spec g10 hyp = ⊥-elim (2≢0 (hyp f0))
kernel-spec g11 hyp = ⊥-elim (3≢0 (hyp f0))
kernel-spec g12 hyp = ⊥-elim (3≢1 (hyp f1))
kernel-spec g13 hyp = ⊥-elim (2≢0 (hyp f0))
kernel-spec g14 hyp = ⊥-elim (3≢0 (hyp f0))
kernel-spec g15 hyp = inj₂ refl
kernel-spec g16 hyp = ⊥-elim (3≢0 (hyp f0))
kernel-spec g17 hyp = ⊥-elim (2≢0 (hyp f0))
kernel-spec g18 hyp = ⊥-elim (3≢1 (hyp f1))
kernel-spec g19 hyp = ⊥-elim (3≢0 (hyp f0))
kernel-spec g20 hyp = ⊥-elim (2≢0 (hyp f0))
kernel-spec g21 hyp = ⊥-elim (2≢1 (hyp f1))
kernel-spec g22 hyp = ⊥-elim (3≢0 (hyp f0))
kernel-spec g23 hyp = ⊥-elim (2≢0 (hyp f0))
