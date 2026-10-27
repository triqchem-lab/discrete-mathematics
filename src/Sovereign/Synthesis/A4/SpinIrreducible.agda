{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Synthesis.A4.SpinIrreducible
--
-- **2 维旋量表示没有不变直线**（内部判据第一块：线性性 + 「公共特征向量 ⇒ 可交换」）
--
-- 背景：`CharTable2A4` 里的"2 维不可约"靠特征标判据（⟨χ,χ⟩ = |G|）+ 已证表示来源。
-- 要给出**表示内部**的理由，先要能谈"不变线"：
--
--     不变线 = Σ[ v ∈ Z[ω]² ] (v ≠ 0) × (∀ g, ∃ c, ρ(g)·v = c·v)
--
-- 不变线等价于公共特征向量：每个 ρ(g) 在 v 上都只作用为标量。本文件证：
--
--   ① 线性性基础：`interchange`（a·(c·x) ≡ c·(a·x)）、`scaleV-assoc`、
--      `mulV-scale`（标量可提出矩阵：ρ(A)·(c·v) ≡ c·(ρ(A)·v)）；
--   ② **关键引理** `commute-on-eigenvector`：
--        A v ≡ c·v  →  B v ≡ d·v  →  A(Bv) ≡ B(Av)
--      代数为：A(Bv) = A(d·v) = d·(Av) = d·(c·v) = (dc)·v；
--              B(Av) = (cd)·v；而 Z[ω] 交换 ⇒ 相等。
--
-- 这条引理是不变线障碍的核心：它把"存在公共特征向量"转成"ρ(g0) 与 ρ(g9) 在 v 上
-- 交换"，而两者的交换子矩阵没有非零公共零点方向（下一步：由交换子 = [[1,−2−ω],
-- [1−ω,−1]]、det = 2，消元得 2·x ≡ 0 ∧ 2·y ≡ 0，再由 Z[ω] 无挠得 x = y = 0，
-- 与 v ≠ 0 矛盾）。本文件只证到 ②，不含该消元。
--
-- 0 postulate / 0 hole。
module Sovereign.Synthesis.A4.SpinIrreducible where

open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂)

open import Sovereign.Synthesis.A4.A4Representation
  using (Zω; zeroZω; addZω; mulZω)
open import Sovereign.Algebra.FieldTower.Zomega
  using (mulZω-assoc; mulZω-comm; mulZω-distribˡ)
open import Sovereign.Synthesis.A4.BilinearSchur2A4 using (M2E; m2e)

--------------------------------------------------------------------------------
-- ① 向量、矩阵-向量作用、标量乘
--------------------------------------------------------------------------------

Pair : Set
Pair = Zω × Zω

zeroV : Pair
zeroV = zeroZω , zeroZω

-- | 矩阵作用：ρ(A)·v
mulMV : M2E → Pair → Pair
mulMV (m2e a b c d) (x , y) =
  addZω (mulZω a x) (mulZω b y) , addZω (mulZω c x) (mulZω d y)

-- | 标量乘：c·v
scaleV : Zω → Pair → Pair
scaleV c (x , y) = mulZω c x , mulZω c y

-- | 标量乘结合：c·(d·v) ≡ (c·d)·v
scaleV-assoc : ∀ (c d : Zω) (v : Pair) → scaleV c (scaleV d v) ≡ scaleV (mulZω c d) v
scaleV-assoc c d (x , y) =
  cong₂ _,_ (sym (mulZω-assoc c d x)) (sym (mulZω-assoc c d y))

-- | 系数交换：a·(c·x) ≡ c·(a·x)
interchange : ∀ (a c x : Zω) → mulZω a (mulZω c x) ≡ mulZω c (mulZω a x)
interchange a c x =
  trans (sym (mulZω-assoc a c x))
    (trans (cong (λ t → mulZω t x) (mulZω-comm a c))
           (mulZω-assoc c a x))

-- | **标量可提出矩阵**：ρ(A)·(c·v) ≡ c·(ρ(A)·v)
mulV-scale : ∀ (A : M2E) (c : Zω) (v : Pair)
           → mulMV A (scaleV c v) ≡ scaleV c (mulMV A v)
mulV-scale (m2e a b d e) c (x , y) = cong₂ _,_
  (trans (cong₂ addZω (interchange a c x) (interchange b c y))
         (sym (mulZω-distribˡ c (mulZω a x) (mulZω b y))))
  (trans (cong₂ addZω (interchange d c x) (interchange e c y))
         (sym (mulZω-distribˡ c (mulZω d x) (mulZω e y))))

--------------------------------------------------------------------------------
-- ② 关键引理：公共特征向量 ⇒ 两算子交换
--------------------------------------------------------------------------------

-- | A(Bv) = (d·c)·v
AB-form : ∀ (A B : M2E) (v : Pair) (c d : Zω)
        → mulMV A v ≡ scaleV c v
        → mulMV B v ≡ scaleV d v
        → mulMV A (mulMV B v) ≡ scaleV (mulZω d c) v
AB-form A B v c d Av Bv =
  trans (cong (mulMV A) Bv)
    (trans (mulV-scale A d v)
      (trans (cong (scaleV d) Av) (scaleV-assoc d c v)))

-- | B(Av) = (c·d)·v
BA-form : ∀ (A B : M2E) (v : Pair) (c d : Zω)
        → mulMV A v ≡ scaleV c v
        → mulMV B v ≡ scaleV d v
        → mulMV B (mulMV A v) ≡ scaleV (mulZω c d) v
BA-form A B v c d Av Bv =
  trans (cong (mulMV B) Av)
    (trans (mulV-scale B c v)
      (trans (cong (scaleV c) Bv) (scaleV-assoc c d v)))

commute-on-eigenvector :
    ∀ (A B : M2E) (v : Pair) (c d : Zω)
    → mulMV A v ≡ scaleV c v
    → mulMV B v ≡ scaleV d v
    → mulMV A (mulMV B v) ≡ mulMV B (mulMV A v)
commute-on-eigenvector A B v c d Av Bv =
  trans (AB-form A B v c d Av Bv)
    (trans (cong (λ t → scaleV t v) (mulZω-comm d c))
           (sym (BA-form A B v c d Av Bv)))
