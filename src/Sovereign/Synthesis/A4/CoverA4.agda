{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Synthesis.A4.CoverA4 —— **第 1 块（地基）**
--
-- 目标（T1 的 Agda 版）：把 "2A₄ = SL(2,F₃)" 从命名变成定理，路径是
--   SL(2,F₃) 在 P¹(F₃)（GF(3)² 的 4 条 1 维子空间）上的诱导置换。
--
-- 本文件落地（0 postulate / 0 hole）：
--   ① V2 = GF(3)² 的向量；negV 取负，negV-invol
--   ② 4 条线的规范代表 rep : Line → V2
--   ③ canon : V2 → V2（非零向量规范到线代表；零向量为占位）
--   ④ 矩阵作用 act : Mat2 → V2 → V2
--   ⑤ 关键引理：act-neg（作用线性）、canon-idem（规范化幂等）
--   ⑥ lineOf / permAt（P¹(F₃) 上的诱导置换）与核 = {I,−I}（构造子穷举）
--   ⑦ 线层面的替换（canon / crank）与 act 的**代数**同态 act-mul
--   ⑧ 同态 permAt-hom：**不靠 24×24 枚举**（act-mul + 行列式 ⇒ 非零保持 + 线替换）
--   ⑨ 像 = A₄：SL23 → A₄ 的显式投影像表（24 构造子）＋ 满射（12 构造子）
--
-- 口径：所有 case 都是**有限构造子穷举**（Fin 3 / Fin 4 / SL23 的 24 构造子 / A₄ 的
--   12 构造子），非数值字面量暴力求值。permAt 的同态性走代数链（act-mul），
--   唯一用到 SL23 构造子穷举的是 `det-toMat`（det = 1 是定义表示的入场券）
--   与像表（像的**取值**只能逐项算出，这是有限数据不是猜想）。
module Sovereign.Synthesis.A4.CoverA4 where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin using (Fin; zero; suc)
open import Data.Product using (Σ; _×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong; cong₂; module ≡-Reasoning)

open import Sovereign.Synthesis.Representation.Fin3Semiring
  using ( neg3; I2
        ; add3-assoc; add3-comm; add3-idˡ; add3-idʳ
        ; mul3-assoc; mul3-comm; mul3-idˡ
        ; mul3-zeroˡ; mul3-zeroʳ; mul3-distribˡ; mul3-distribʳ
        ; neg3-zero; neg3-add; neg3-invol; neg3-mulʳ )

open import Sovereign.Algebra.LinearAlgebra.Matrix2
  using (m00; m01; m10; m11; mkMat2)

open import Sovereign.Synthesis.Representation.Matrix2Inverse
  using (det3; adj; det-one-adj)

open import Sovereign.Synthesis.Representation.SL23Cayley
  using (Mat2; add3; mul3; toMat; mulMat2; _⊗_; toMat-hom)
open import Sovereign.Synthesis.A4.BinaryTetrahedralDefiningRep
  using (SL23; g0; g1; g2; g3; g4; g5; g6; g7; g8; g9; g10; g11
        ; g12; g13; g14; g15; g16; g17; g18; g19; g20; g21; g22; g23)
open import Sovereign.Synthesis.A4.A4Group
  using (A4; Id; Rot; Flip; perm)

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

-- | 线代表的索引版（`rep ∘ lineIdx` 的逆方向；下游 crank / 像表都要用）
repIdx : Fin 4 → V2
repIdx zero                   = rep L0
repIdx (suc zero)             = rep L1
repIdx (suc (suc zero))       = rep L2
repIdx (suc (suc (suc zero))) = rep L3

-- | 矩阵在 P¹(F₃) 上的诱导置换
permAt : Mat2 → Fin 4 → Fin 4
permAt m i = lineIdx (lineOf (act m (repIdx i)))

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

--------------------------------------------------------------------------------
-- ⑧ 线层面的替换：canon / crank
--
--   P¹ 上的作用要良定义：同一根线的两个非零代表必须落到同一根线。两步——
--     ① 规范代表 canon v 与 v 本身只差一个符号（canon-cases）；
--     ② act 与取负可交换（act-neg）、取负不改线（lineOf-neg）⇒ 线不变。
--
--   `crank v = repIdx (lineIdx (lineOf v))` 是**按线标签**取的代表：它与 canon v
--   一致（v ≠ 0 时），零向量是唯一例外（crank 给 L0 的代表，canon 给零向量本身）。
--------------------------------------------------------------------------------

canon-cases : ∀ (v : V2) → (canon v ≡ v) ⊎ (canon v ≡ negV v)
canon-cases (v2 zero zero)                        = inj₁ refl
canon-cases (v2 zero (suc zero))                  = inj₁ refl
canon-cases (v2 zero (suc (suc zero)))            = inj₂ refl
canon-cases (v2 (suc zero) y)                     = inj₁ refl
canon-cases (v2 (suc (suc zero)) y)               = inj₂ refl

-- 取负不改线：v 与 −v 张成同一条 1 维子空间（9 构造子穷举）
lineOf-neg : ∀ (v : V2) → lineOf (negV v) ≡ lineOf v
lineOf-neg (v2 zero zero)                         = refl
lineOf-neg (v2 zero (suc zero))                   = refl
lineOf-neg (v2 zero (suc (suc zero)))             = refl
lineOf-neg (v2 (suc zero) zero)                   = refl
lineOf-neg (v2 (suc zero) (suc zero))             = refl
lineOf-neg (v2 (suc zero) (suc (suc zero)))       = refl
lineOf-neg (v2 (suc (suc zero)) zero)             = refl
lineOf-neg (v2 (suc (suc zero)) (suc zero))       = refl
lineOf-neg (v2 (suc (suc zero)) (suc (suc zero))) = refl

-- 线上的替换不影响像所在线
line-act-canon : ∀ (m : Mat2) (v : V2) → lineOf (act m (canon v)) ≡ lineOf (act m v)
line-act-canon m v with canon-cases v
... | inj₁ e = cong (λ w → lineOf (act m w)) e
... | inj₂ e = trans (cong (λ w → lineOf (act m w)) e)
                     (trans (cong lineOf (act-neg m v)) (lineOf-neg (act m v)))

crank : V2 → V2
crank v = repIdx (lineIdx (lineOf v))

crank-cases : ∀ (v : V2) → (crank v ≡ canon v) ⊎ (v ≡ vzero)
crank-cases (v2 zero zero)                        = inj₂ refl
crank-cases (v2 zero (suc zero))                  = inj₁ refl
crank-cases (v2 zero (suc (suc zero)))            = inj₁ refl
crank-cases (v2 (suc zero) zero)                  = inj₁ refl
crank-cases (v2 (suc zero) (suc zero))            = inj₁ refl
crank-cases (v2 (suc zero) (suc (suc zero)))      = inj₁ refl
crank-cases (v2 (suc (suc zero)) zero)            = inj₁ refl
crank-cases (v2 (suc (suc zero)) (suc zero))      = inj₁ refl
crank-cases (v2 (suc (suc zero)) (suc (suc zero))) = inj₁ refl

line-act-crank : ∀ (m : Mat2) (v : V2) → v ≢ vzero
               → lineOf (act m (crank v)) ≡ lineOf (act m v)
line-act-crank m v nz with crank-cases v
... | inj₁ e = trans (cong (λ w → lineOf (act m w)) e) (line-act-canon m v)
... | inj₂ e = ⊥-elim (nz e)

--------------------------------------------------------------------------------
-- ⑨ act 与矩阵乘法相容（同态的**代数**核心）
--
--   这一节是 permAt 同态性的全部代数内容，与 P¹ / 线无关：
--     act (M·N) v ≡ act M (act N v)
--   逐分量证明：分配律把括号拆开，结合律把系数并起来，再用四项换位
--   （add3-mid-swap）把 (a·p)x + (a·q)y + (b·r)x + (b·s)y 排成
--   ((a·p)x + (b·r)x) + ((a·q)y + (b·s)y)，最后合回 (a·p + b·r)x。
--------------------------------------------------------------------------------

act-id : ∀ (v : V2) → act I2 v ≡ v
act-id (v2 x y) = cong₂ v2 row1 row2
  where
    row1 : add3 (mul3 (suc zero) x) (mul3 zero y) ≡ x
    row1 = trans (cong₂ add3 (mul3-idˡ x) (mul3-zeroˡ y)) (add3-idʳ x)
    row2 : add3 (mul3 zero x) (mul3 (suc zero) y) ≡ y
    row2 = trans (cong₂ add3 (mul3-zeroˡ x) (mul3-idˡ y)) (add3-idˡ y)

act-vzero : ∀ (m : Mat2) → act m vzero ≡ vzero
act-vzero (mkMat2 a b c d) = cong₂ v2 row1 row2
  where
    row1 : add3 (mul3 a zero) (mul3 b zero) ≡ zero
    row1 = trans (cong₂ add3 (mul3-zeroʳ a) (mul3-zeroʳ b)) (add3-idʳ zero)
    row2 : add3 (mul3 c zero) (mul3 d zero) ≡ zero
    row2 = trans (cong₂ add3 (mul3-zeroʳ c) (mul3-zeroʳ d)) (add3-idʳ zero)

-- 四项换位：(A+B)+(C+D) ≡ (A+C)+(B+D)
--
-- ⚠ 与 `Application/Physics/DiscreteNoether.add3-swap` 命题相同但**不 import**：
--   Synthesis/A4 在依赖方向上是低层，import Application/* 会造成层次倒置。
--   该引理本属 Fin3Semiring 层级，等库里做搬迁时两处一并收编。
add3-mid-swap : ∀ A B C D → add3 (add3 A B) (add3 C D) ≡ add3 (add3 A C) (add3 B D)
add3-mid-swap A B C D = begin
    add3 (add3 A B) (add3 C D)
  ≡⟨ add3-assoc A B (add3 C D) ⟩
    add3 A (add3 B (add3 C D))
  ≡⟨ cong (add3 A) (sym (add3-assoc B C D)) ⟩
    add3 A (add3 (add3 B C) D)
  ≡⟨ cong (λ t → add3 A (add3 t D)) (add3-comm B C) ⟩
    add3 A (add3 (add3 C B) D)
  ≡⟨ cong (add3 A) (add3-assoc C B D) ⟩
    add3 A (add3 C (add3 B D))
  ≡⟨ sym (add3-assoc A C (add3 B D)) ⟩
    add3 (add3 A C) (add3 B D)
  ∎

-- 一个分量式：(a·(px+qy)) + (b·(rx+sy)) ≡ (ap+br)·x + (aq+bs)·y
row-mul : ∀ (a b p q r s x y : Fin 3)
        → add3 (mul3 a (add3 (mul3 p x) (mul3 q y)))
               (mul3 b (add3 (mul3 r x) (mul3 s y)))
        ≡ add3 (mul3 (add3 (mul3 a p) (mul3 b r)) x)
               (mul3 (add3 (mul3 a q) (mul3 b s)) y)
row-mul a b p q r s x y = begin
    add3 (mul3 a (add3 (mul3 p x) (mul3 q y)))
         (mul3 b (add3 (mul3 r x) (mul3 s y)))
  ≡⟨ cong₂ add3 (mul3-distribˡ a (mul3 p x) (mul3 q y))
                (mul3-distribˡ b (mul3 r x) (mul3 s y)) ⟩
    add3 (add3 (mul3 a (mul3 p x)) (mul3 a (mul3 q y)))
         (add3 (mul3 b (mul3 r x)) (mul3 b (mul3 s y)))
  ≡⟨ cong₂ add3
       (cong₂ add3 (sym (mul3-assoc a p x)) (sym (mul3-assoc a q y)))
       (cong₂ add3 (sym (mul3-assoc b r x)) (sym (mul3-assoc b s y))) ⟩
    add3 (add3 (mul3 (mul3 a p) x) (mul3 (mul3 a q) y))
         (add3 (mul3 (mul3 b r) x) (mul3 (mul3 b s) y))
  ≡⟨ add3-mid-swap (mul3 (mul3 a p) x) (mul3 (mul3 a q) y)
                   (mul3 (mul3 b r) x) (mul3 (mul3 b s) y) ⟩
    add3 (add3 (mul3 (mul3 a p) x) (mul3 (mul3 b r) x))
         (add3 (mul3 (mul3 a q) y) (mul3 (mul3 b s) y))
  ≡⟨ cong₂ add3 (sym (mul3-distribʳ x (mul3 a p) (mul3 b r)))
                (sym (mul3-distribʳ y (mul3 a q) (mul3 b s))) ⟩
    add3 (mul3 (add3 (mul3 a p) (mul3 b r)) x)
         (mul3 (add3 (mul3 a q) (mul3 b s)) y)
  ∎

act-mul : ∀ (m n : Mat2) (v : V2) → act (mulMat2 m n) v ≡ act m (act n v)
act-mul (mkMat2 a b c d) (mkMat2 p q r s) (v2 x y) = cong₂ v2
  (sym (row-mul a b p q r s x y))
  (sym (row-mul c d p q r s x y))

--------------------------------------------------------------------------------
-- ⑩ 非零保持：det = 1 ⇒ act 单射（用伴随矩阵作逆，不做除法）
--
--   `Matrix2Inverse` 已证 det M = 1 ⇒ M·adj M = adj M·M = I。于是
--       v ≡ act I v ≡ act (adj M · M) v ≡ act (adj M) (act M v)，
--   若 act M v ≡ 0 则 v ≡ 0。
--------------------------------------------------------------------------------

act-inj : ∀ (m : Mat2) → det3 m ≡ suc zero
        → ∀ (v : V2) → act m v ≡ vzero → v ≡ vzero
act-inj m det1 v e = begin
    v                         ≡⟨ sym (act-id v) ⟩
    act I2 v                  ≡⟨ cong (λ w → act w v) (sym (det-one-adj m det1)) ⟩
    act (mulMat2 (adj m) m) v ≡⟨ act-mul (adj m) m v ⟩
    act (adj m) (act m v)     ≡⟨ cong (act (adj m)) e ⟩
    act (adj m) vzero         ≡⟨ act-vzero (adj m) ⟩
    vzero                     ∎

act-nz : ∀ (m : Mat2) → det3 m ≡ suc zero
       → ∀ (v : V2) → v ≢ vzero → act m v ≢ vzero
act-nz m det1 v nz e = nz (act-inj m det1 v e)

repIdx-nz : ∀ (i : Fin 4) → repIdx i ≢ vzero
repIdx-nz zero                   = λ ()
repIdx-nz (suc zero)             = λ ()
repIdx-nz (suc (suc zero))       = λ ()
repIdx-nz (suc (suc (suc zero))) = λ ()

-- SL(2,F₃) 的 24 个矩阵行列式都是 1（定义表示的入场券，24 构造子穷举）
det-toMat : ∀ (x : SL23) → det3 (toMat x) ≡ suc zero
det-toMat g0  = refl
det-toMat g1  = refl
det-toMat g2  = refl
det-toMat g3  = refl
det-toMat g4  = refl
det-toMat g5  = refl
det-toMat g6  = refl
det-toMat g7  = refl
det-toMat g8  = refl
det-toMat g9  = refl
det-toMat g10 = refl
det-toMat g11 = refl
det-toMat g12 = refl
det-toMat g13 = refl
det-toMat g14 = refl
det-toMat g15 = refl
det-toMat g16 = refl
det-toMat g17 = refl
det-toMat g18 = refl
det-toMat g19 = refl
det-toMat g20 = refl
det-toMat g21 = refl
det-toMat g22 = refl
det-toMat g23 = refl

--------------------------------------------------------------------------------
-- ⑪ 同态：permAt (M·N) ≡ permAt M ∘ permAt N
--
--   与 24×24 枚举无关：act-mul 给出“先作用再作用”，act-nz 保证中间向量非零，
--   line-act-crank 把“按线标签取代表”换回真实向量。三者复合即得。
--------------------------------------------------------------------------------

permAt-mul : ∀ (a b : Mat2) (i : Fin 4) → act b (repIdx i) ≢ vzero
           → permAt (mulMat2 a b) i ≡ permAt a (permAt b i)
permAt-mul a b i nz = begin
    permAt (mulMat2 a b) i
  ≡⟨ cong (λ w → lineIdx (lineOf w)) (act-mul a b (repIdx i)) ⟩
    lineIdx (lineOf (act a (act b (repIdx i))))
  ≡⟨ sym (cong lineIdx (line-act-crank a (act b (repIdx i)) nz)) ⟩
    lineIdx (lineOf (act a (crank (act b (repIdx i)))))
  ≡⟨⟩
    permAt a (permAt b i)
  ∎

-- | **SL(2,F₃) 的乘法 → P¹(F₃) 置换的复合**
permAt-hom : ∀ (x y : SL23) (i : Fin 4)
           → permAt (toMat (x ⊗ y)) i ≡ permAt (toMat x) (permAt (toMat y) i)
permAt-hom x y i = begin
    permAt (toMat (x ⊗ y)) i
  ≡⟨ cong (λ m → permAt m i) (toMat-hom x y) ⟩
    permAt (mulMat2 (toMat x) (toMat y)) i
  ≡⟨ permAt-mul (toMat x) (toMat y) i
       (act-nz (toMat y) (det-toMat y) (repIdx i) (repIdx-nz i)) ⟩
    permAt (toMat x) (permAt (toMat y) i)
  ∎

--------------------------------------------------------------------------------
-- ⑫ 像 = A₄
--
--   两个方向：
--     像 ⊆ A₄ —— 显式投影 `toA4 : SL23 → A₄`，24 构造子逐一核对
--                 permAt (toMat x) 与 perm (toA4 x) 在 4 个线代表上一致；
--     A₄ ⊆ 像 —— `toA4` 满射（12 构造子各给一个原像），于是每个 perm a
--                 都是某个 permAt (toMat x)。
--   注意 `toA4` 恰好把 x 与 −x（g6/g15、g0/g3、g1/g5、… ）映到同一个 A₄ 元素：
--   这与核 = {I,−I} 是同一件事，不是额外假设。
--------------------------------------------------------------------------------

-- 24 个构造子的 A₄ 像（12 个值，每个值出现两次：x 与 −x）
toA4 : SL23 → A4
toA4 g0 = Flip zero
toA4 g1 = Rot (suc (suc (suc zero))) zero
toA4 g2 = Rot (suc (suc zero)) zero
toA4 g3 = Flip zero
toA4 g4 = Rot (suc (suc zero)) zero
toA4 g5 = Rot (suc (suc (suc zero))) zero
toA4 g6 = Id
toA4 g7 = Rot (suc zero) zero
toA4 g8 = Rot (suc zero) (suc zero)
toA4 g9 = Rot zero zero
toA4 g10 = Flip (suc zero)
toA4 g11 = Rot (suc (suc zero)) (suc zero)
toA4 g12 = Rot zero (suc zero)
toA4 g13 = Rot (suc (suc (suc zero))) (suc zero)
toA4 g14 = Flip (suc (suc zero))
toA4 g15 = Id
toA4 g16 = Rot (suc zero) (suc zero)
toA4 g17 = Rot (suc zero) zero
toA4 g18 = Rot zero (suc zero)
toA4 g19 = Flip (suc (suc zero))
toA4 g20 = Rot (suc (suc (suc zero))) (suc zero)
toA4 g21 = Rot zero zero
toA4 g22 = Rot (suc (suc zero)) (suc zero)
toA4 g23 = Flip (suc zero)

-- 第 0 个线代表上的取值：24 个构造子逐一归约
img-at0 : ∀ (x : SL23) → permAt (toMat x) f0 ≡ perm (toA4 x) f0
img-at0 g0  = refl
img-at0 g1  = refl
img-at0 g2  = refl
img-at0 g3  = refl
img-at0 g4  = refl
img-at0 g5  = refl
img-at0 g6  = refl
img-at0 g7  = refl
img-at0 g8  = refl
img-at0 g9  = refl
img-at0 g10 = refl
img-at0 g11 = refl
img-at0 g12 = refl
img-at0 g13 = refl
img-at0 g14 = refl
img-at0 g15 = refl
img-at0 g16 = refl
img-at0 g17 = refl
img-at0 g18 = refl
img-at0 g19 = refl
img-at0 g20 = refl
img-at0 g21 = refl
img-at0 g22 = refl
img-at0 g23 = refl

-- 第 1 个线代表上的取值
img-at1 : ∀ (x : SL23) → permAt (toMat x) f1 ≡ perm (toA4 x) f1
img-at1 g0  = refl
img-at1 g1  = refl
img-at1 g2  = refl
img-at1 g3  = refl
img-at1 g4  = refl
img-at1 g5  = refl
img-at1 g6  = refl
img-at1 g7  = refl
img-at1 g8  = refl
img-at1 g9  = refl
img-at1 g10 = refl
img-at1 g11 = refl
img-at1 g12 = refl
img-at1 g13 = refl
img-at1 g14 = refl
img-at1 g15 = refl
img-at1 g16 = refl
img-at1 g17 = refl
img-at1 g18 = refl
img-at1 g19 = refl
img-at1 g20 = refl
img-at1 g21 = refl
img-at1 g22 = refl
img-at1 g23 = refl

-- 第 2 个线代表上的取值
img-at2 : ∀ (x : SL23) → permAt (toMat x) f2 ≡ perm (toA4 x) f2
img-at2 g0  = refl
img-at2 g1  = refl
img-at2 g2  = refl
img-at2 g3  = refl
img-at2 g4  = refl
img-at2 g5  = refl
img-at2 g6  = refl
img-at2 g7  = refl
img-at2 g8  = refl
img-at2 g9  = refl
img-at2 g10 = refl
img-at2 g11 = refl
img-at2 g12 = refl
img-at2 g13 = refl
img-at2 g14 = refl
img-at2 g15 = refl
img-at2 g16 = refl
img-at2 g17 = refl
img-at2 g18 = refl
img-at2 g19 = refl
img-at2 g20 = refl
img-at2 g21 = refl
img-at2 g22 = refl
img-at2 g23 = refl

-- 第 3 个线代表上的取值
img-at3 : ∀ (x : SL23) → permAt (toMat x) f3 ≡ perm (toA4 x) f3
img-at3 g0  = refl
img-at3 g1  = refl
img-at3 g2  = refl
img-at3 g3  = refl
img-at3 g4  = refl
img-at3 g5  = refl
img-at3 g6  = refl
img-at3 g7  = refl
img-at3 g8  = refl
img-at3 g9  = refl
img-at3 g10 = refl
img-at3 g11 = refl
img-at3 g12 = refl
img-at3 g13 = refl
img-at3 g14 = refl
img-at3 g15 = refl
img-at3 g16 = refl
img-at3 g17 = refl
img-at3 g18 = refl
img-at3 g19 = refl
img-at3 g20 = refl
img-at3 g21 = refl
img-at3 g22 = refl
img-at3 g23 = refl

-- 逐点组装（避免 funext：像的相等按 Fin 4 的四个点陈述）
image-in-A4 : ∀ (x : SL23) (i : Fin 4) → permAt (toMat x) i ≡ perm (toA4 x) i
image-in-A4 x zero                   = img-at0 x
image-in-A4 x (suc zero)             = img-at1 x
image-in-A4 x (suc (suc zero))       = img-at2 x
image-in-A4 x (suc (suc (suc zero))) = img-at3 x

-- 满射：每个 A₄ 元素都有 SL(2,F₃) 里的原像
toA4-surj : ∀ (a : A4) → Σ SL23 (λ x → toA4 x ≡ a)
toA4-surj Id                                      = g6 , refl
toA4-surj (Rot zero zero)                         = g9 , refl
toA4-surj (Rot zero (suc zero))                   = g12 , refl
toA4-surj (Rot (suc zero) zero)                   = g7 , refl
toA4-surj (Rot (suc zero) (suc zero))             = g8 , refl
toA4-surj (Rot (suc (suc zero)) zero)             = g2 , refl
toA4-surj (Rot (suc (suc zero)) (suc zero))       = g11 , refl
toA4-surj (Rot (suc (suc (suc zero))) zero)       = g1 , refl
toA4-surj (Rot (suc (suc (suc zero))) (suc zero)) = g13 , refl
toA4-surj (Flip zero)                             = g0 , refl
toA4-surj (Flip (suc zero))                       = g10 , refl
toA4-surj (Flip (suc (suc zero)))                 = g14 , refl

-- 像 ⊆ A₄
image-subset-A4 : ∀ (x : SL23) → Σ A4 (λ a → ∀ i → permAt (toMat x) i ≡ perm a i)
image-subset-A4 x = toA4 x , image-in-A4 x

-- A₄ ⊆ 像
image-covers-A4 : ∀ (a : A4) → Σ SL23 (λ x → ∀ i → permAt (toMat x) i ≡ perm a i)
image-covers-A4 a with toA4-surj a
... | x , refl = x , image-in-A4 x

--------------------------------------------------------------------------------
-- ⑬ 结论：覆盖数据（"SL(2,F₃)/{±I} ≅ A₄" 的四件套）
--
--   同态 + 核 = {I,−I} + 像 = A₄ 三条合起来才是「商群同构」的完整内容：
--     · hom          乘法 → 复合（不靠枚举）
--     · kernel-exact 纤维大小 = 2（核恰为 {±I}）
--     · image-subset 像落在 A₄ 里
--     · image-cover  A₄ 每个元素都被打到（满）
--   商群本身（`SL23/{±I}` 的 setoid 商 + 泛性质）仍不在本库，因此这里陈述的是
--   覆盖数据，而不是一个 `GroupIsomorphism` 项。
--------------------------------------------------------------------------------

record CoverA4 : Set where
  field
    hom            : ∀ (x y : SL23) (i : Fin 4)
                   → permAt (toMat (x ⊗ y)) i ≡ permAt (toMat x) (permAt (toMat y) i)
    kernel-exact   : ∀ (x : SL23) → (∀ i → permAt (toMat x) i ≡ i)
                   → (x ≡ g6) ⊎ (x ≡ g15)
    kernel-realised : (∀ i → permAt (toMat g6) i ≡ i) × (∀ i → permAt (toMat g15) i ≡ i)
    image-subset   : ∀ (x : SL23) → Σ A4 (λ a → ∀ i → permAt (toMat x) i ≡ perm a i)
    image-cover    : ∀ (a : A4) → Σ SL23 (λ x → ∀ i → permAt (toMat x) i ≡ perm a i)

coverA4 : CoverA4
coverA4 = record
  { hom             = permAt-hom
  ; kernel-exact    = kernel-spec
  ; kernel-realised = perm-id , perm-negI
  ; image-subset    = image-subset-A4
  ; image-cover     = image-covers-A4
  }
