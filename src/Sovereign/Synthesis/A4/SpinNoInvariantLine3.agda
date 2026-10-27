{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Synthesis.A4.SpinNoInvariantLine3
--
-- **3 维 ρ₃ 的不变线障碍**（完整链条：闭乘积 → 交换子 → 三条线性方程 → 消元）
--
-- 3 维不能照搬 2 维的「两条方程直接消元」：实测提升后的 ρ₃ = rho3 ∘ toA4 的
-- 384 个非零交换子**全部** det = 0、秩 = 2，没有单位行列式，也没有 ±1 的 3 行子式。
-- 最小非零子式是 det = 4（交换子 C 的 0、2 行与 E 的 2 行），故走「核的交 + det = 4 子式」
-- 而不是行列式判据。
--
-- 内容：
--   ① 三个表示矩阵 A = ρ(g0)、B = ρ(g1)、D = ρ(g2)（gₖ 是 SL(2,3) 的生成元）
--   ② 四个闭乘积矩阵 A·B、B·A、A·D、D·A（由 `mulMM3` 归约，Agda 自算，非外部脚本）
--   ③ 交换子矩阵的行
--        C = A·B − B·A = [[1,0,1],[2,−2,2],[1,−2,1]]
--        E = A·D − D·A = [[1,1,−1],[2,0,−2],[1,1,−1]]
--      取 C₀、C₂、E₂（即下方 E1/E3/F3 三条方程），行列式 = 4 ≠ 0。
--   ④ 由 `commute3`（公共特征向量 ⇒ 交换）得到闭矩阵方程
--        ρ(A·B)·v ≡ ρ(B·A)·v      ρ(A·D)·v ≡ ρ(D·A)·v
--   ⑤ 逐行化简（1/0/−1 系数在变量处不归约，须显式引理）
--   ⑥ 三条分量化线性方程 E1、E3、F3
--   ⑦ 消元：x = −z；(E3) ⇒ −y = y ⇒ y = 0；(F3) ⇒ z = x = −z ⇒ z = 0
--      —— 全程只用 2-无挠（`two-zero`），无需 four-zero
--   ⑧ `no-invariant-line3`：不存在非零的公共特征向量（对全部 24 个 SL(2,3) 元素）
--
-- 作用相容（`mulMV3 (mulMM3 A B) v ≡ mulMV3 A (mulMV3 B v)`）在 `SpinIrreducible3`。
--
-- 0 postulate / 0 hole。
module Sovereign.Synthesis.A4.SpinNoInvariantLine3 where

open import Data.Vec using (Vec; []; _∷_)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong; cong₂; module ≡-Reasoning)

open ≡-Reasoning

open import Sovereign.Synthesis.A4.A4Representation
  using (Zω; zeroZω; oneZω; negZω; addZω; mulZω)
open import Sovereign.Algebra.FieldTower.Zomega
  using ( mulZω-identityˡ; mulZω-zeroˡ; negZω-mulˡ; negZω-involutive
        ; addZω-comm; addZω-identityˡ; addZω-identityʳ; addZω-inverseʳ )
open import Sovereign.Synthesis.FieldTower.MatrixZω using (Mat; dot; mulMat)
open import Sovereign.Synthesis.A4.A4ThreeDimRep using (rho3)
open import Sovereign.Synthesis.A4.CoverA4 using (toA4)
open import Sovereign.Synthesis.A4.BinaryTetrahedralDefiningRep using (SL23; g0; g1; g2)
open import Sovereign.Synthesis.A4.SpinIrreducible3
  using (Vec3; zeroV3; vec3-cong; mulMV3; scaleV3; mulMM3; mulMV3-mulMM3; commute3)
open import Sovereign.Synthesis.A4.SpinNoInvariantLine
  using (twoZ; twoZ-mul; two-zero; add-cancelʳ)

--------------------------------------------------------------------------------
-- ① 三个群元素对应的 3 维表示矩阵
--
--   toA4 g0 = Flip zero        toA4 g1 = Rot 3 zero        toA4 g2 = Rot 2 zero
--------------------------------------------------------------------------------

A3 B3 D3 : Mat 3 3
A3 = rho3 (toA4 g0)
B3 = rho3 (toA4 g1)
D3 = rho3 (toA4 g2)

--------------------------------------------------------------------------------
-- ② 四个闭乘积矩阵（由 `mulMM3` 归约得出）
--
--   条目 0/±1 全用 `zeroZω`/`oneZω`/`negZω oneZω`（ℤ 的 `_*_` 由 `sign ◃ (|_|*|_|)`
--   定义，含负数的乘积不按字面归约，故 `refl` 能过正是「这是 Agda 算出来的」的证据）。
--------------------------------------------------------------------------------

ABm BAm ADm DAm : Mat 3 3
ABm = (oneZω ∷ zeroZω ∷ zeroZω ∷ []) ∷
      (oneZω ∷ negZω oneZω ∷ oneZω ∷ []) ∷
      (oneZω ∷ negZω oneZω ∷ zeroZω ∷ []) ∷ []
BAm = (zeroZω ∷ zeroZω ∷ negZω oneZω ∷ []) ∷
      (negZω oneZω ∷ oneZω ∷ negZω oneZω ∷ []) ∷
      (zeroZω ∷ oneZω ∷ negZω oneZω ∷ []) ∷ []
ADm = (oneZω ∷ zeroZω ∷ zeroZω ∷ []) ∷
      (oneZω ∷ zeroZω ∷ negZω oneZω ∷ []) ∷
      (zeroZω ∷ oneZω ∷ negZω oneZω ∷ []) ∷ []
DAm = (zeroZω ∷ negZω oneZω ∷ oneZω ∷ []) ∷
      (negZω oneZω ∷ zeroZω ∷ oneZω ∷ []) ∷
      (negZω oneZω ∷ zeroZω ∷ zeroZω ∷ []) ∷ []

-- | ρ(g0)·ρ(g1)
AB3-mat : mulMM3 A3 B3 ≡ ABm
AB3-mat = refl

-- | ρ(g1)·ρ(g0)
BA3-mat : mulMM3 B3 A3 ≡ BAm
BA3-mat = refl

-- | ρ(g0)·ρ(g2)
AD3-mat : mulMM3 A3 D3 ≡ ADm
AD3-mat = refl

-- | ρ(g2)·ρ(g0)
DA3-mat : mulMM3 D3 A3 ≡ DAm
DA3-mat = refl

-- | 交叉核对：行组合定义与库内「行·列」定义 `mulMat` 在这一对上逐条一致
--   （同时说明 `mulMM3` 不是 `mulMat` 的转置）。
AB-cross : mulMM3 A3 B3 ≡ mulMat A3 B3
AB-cross = refl

--------------------------------------------------------------------------------
-- ④ 由 commute3 得到闭矩阵方程
--
--   公共特征向量 v（A·v = c·v、B·v = d·v）⇒ A(B v) ≡ B(A v)（`commute3`）
--   ⇒ ρ(A·B)·v ≡ ρ(B·A)·v（作用相容 + 上面四个闭乘积）。
--------------------------------------------------------------------------------

AB-act : ∀ (v : Vec3) → mulMV3 A3 (mulMV3 B3 v) ≡ mulMV3 ABm v
AB-act v =
  trans (sym (mulMV3-mulMM3 A3 B3 v)) (cong (λ M → mulMV3 M v) AB3-mat)

BA-act : ∀ (v : Vec3) → mulMV3 B3 (mulMV3 A3 v) ≡ mulMV3 BAm v
BA-act v =
  trans (sym (mulMV3-mulMM3 B3 A3 v)) (cong (λ M → mulMV3 M v) BA3-mat)

AD-act : ∀ (v : Vec3) → mulMV3 A3 (mulMV3 D3 v) ≡ mulMV3 ADm v
AD-act v =
  trans (sym (mulMV3-mulMM3 A3 D3 v)) (cong (λ M → mulMV3 M v) AD3-mat)

DA-act : ∀ (v : Vec3) → mulMV3 D3 (mulMV3 A3 v) ≡ mulMV3 DAm v
DA-act v =
  trans (sym (mulMV3-mulMM3 D3 A3 v)) (cong (λ M → mulMV3 M v) DA3-mat)

-- | 交换子行方程（A、B）：ρ(A·B)·v ≡ ρ(B·A)·v
AB-comm-act : ∀ (v : Vec3) (c d : Zω)
            → mulMV3 A3 v ≡ scaleV3 c v
            → mulMV3 B3 v ≡ scaleV3 d v
            → mulMV3 ABm v ≡ mulMV3 BAm v
AB-comm-act v c d Av Bv =
  trans (sym (AB-act v))
    (trans (commute3 A3 B3 v c d Av Bv) (BA-act v))

-- | 交换子行方程（A、D）：ρ(A·D)·v ≡ ρ(D·A)·v
AD-comm-act : ∀ (v : Vec3) (c e : Zω)
            → mulMV3 A3 v ≡ scaleV3 c v
            → mulMV3 D3 v ≡ scaleV3 e v
            → mulMV3 ADm v ≡ mulMV3 DAm v
AD-comm-act v c e Av Dv =
  trans (sym (AD-act v))
    (trans (commute3 A3 D3 v c e Av Dv) (DA-act v))

--------------------------------------------------------------------------------
-- ⑤ 逐行化简
--
--   ⚠ `mulZω oneZω x` 在**变量**处不归约（ℤ 的 `_*_` 是 `sign ◃ (|_|*|_|)`，
--   `sign (+1) ◃ (1 * |a|)` 只到 `|a|`），故 1/0/−1 系数必须逐条显式化简。
--------------------------------------------------------------------------------

-- | (−1)·x ≡ −x
neg-one-mul : ∀ (x : Zω) → mulZω (negZω oneZω) x ≡ negZω x
neg-one-mul x = trans (negZω-mulˡ oneZω x) (cong negZω (mulZω-identityˡ x))

-- | dot (1,0,0) v ≡ x
row-100 : ∀ (x y z : Zω)
        → dot (oneZω ∷ zeroZω ∷ zeroZω ∷ []) (x ∷ y ∷ z ∷ []) ≡ x
row-100 x y z = begin
    addZω (mulZω oneZω x) (addZω (mulZω zeroZω y) (addZω (mulZω zeroZω z) zeroZω))
  ≡⟨ cong₂ addZω (mulZω-identityˡ x)
        (cong₂ addZω (mulZω-zeroˡ y)
          (cong (λ t → addZω t zeroZω) (mulZω-zeroˡ z))) ⟩
    addZω x (addZω zeroZω (addZω zeroZω zeroZω))
  ≡⟨ cong (addZω x) (addZω-identityˡ (addZω zeroZω zeroZω)) ⟩
    addZω x (addZω zeroZω zeroZω)
  ≡⟨ cong (addZω x) (addZω-identityˡ zeroZω) ⟩
    addZω x zeroZω
  ≡⟨ addZω-identityʳ x ⟩
    x ∎

-- | dot (0,0,−1) v ≡ −z
row-001m : ∀ (x y z : Zω)
         → dot (zeroZω ∷ zeroZω ∷ negZω oneZω ∷ []) (x ∷ y ∷ z ∷ []) ≡ negZω z
row-001m x y z = begin
    addZω (mulZω zeroZω x) (addZω (mulZω zeroZω y)
                                    (addZω (mulZω (negZω oneZω) z) zeroZω))
  ≡⟨ cong₂ addZω (mulZω-zeroˡ x)
        (cong₂ addZω (mulZω-zeroˡ y)
          (cong (λ t → addZω t zeroZω) (neg-one-mul z))) ⟩
    addZω zeroZω (addZω zeroZω (addZω (negZω z) zeroZω))
  ≡⟨ cong (addZω zeroZω) (cong (addZω zeroZω) (addZω-identityʳ (negZω z))) ⟩
    addZω zeroZω (addZω zeroZω (negZω z))
  ≡⟨ cong (addZω zeroZω) (addZω-identityˡ (negZω z)) ⟩
    addZω zeroZω (negZω z)
  ≡⟨ addZω-identityˡ (negZω z) ⟩
    negZω z ∎

-- | dot (1,−1,0) v ≡ x ⊕ (−y)
row-1m10 : ∀ (x y z : Zω)
         → dot (oneZω ∷ negZω oneZω ∷ zeroZω ∷ []) (x ∷ y ∷ z ∷ [])
         ≡ addZω x (negZω y)
row-1m10 x y z = begin
    addZω (mulZω oneZω x) (addZω (mulZω (negZω oneZω) y)
                                    (addZω (mulZω zeroZω z) zeroZω))
  ≡⟨ cong₂ addZω (mulZω-identityˡ x)
        (cong₂ addZω (neg-one-mul y)
          (cong (λ t → addZω t zeroZω) (mulZω-zeroˡ z))) ⟩
    addZω x (addZω (negZω y) (addZω zeroZω zeroZω))
  ≡⟨ cong (addZω x) (cong (addZω (negZω y)) (addZω-identityˡ zeroZω)) ⟩
    addZω x (addZω (negZω y) zeroZω)
  ≡⟨ cong (addZω x) (addZω-identityʳ (negZω y)) ⟩
    addZω x (negZω y) ∎

-- | dot (0,1,−1) v ≡ y ⊕ (−z)
row-01m1 : ∀ (x y z : Zω)
         → dot (zeroZω ∷ oneZω ∷ negZω oneZω ∷ []) (x ∷ y ∷ z ∷ [])
         ≡ addZω y (negZω z)
row-01m1 x y z = begin
    addZω (mulZω zeroZω x) (addZω (mulZω oneZω y)
                                    (addZω (mulZω (negZω oneZω) z) zeroZω))
  ≡⟨ cong₂ addZω (mulZω-zeroˡ x)
        (cong₂ addZω (mulZω-identityˡ y)
          (cong (λ t → addZω t zeroZω) (neg-one-mul z))) ⟩
    addZω zeroZω (addZω y (addZω (negZω z) zeroZω))
  ≡⟨ cong (addZω zeroZω) (cong (addZω y) (addZω-identityʳ (negZω z))) ⟩
    addZω zeroZω (addZω y (negZω z))
  ≡⟨ addZω-identityˡ (addZω y (negZω z)) ⟩
    addZω y (negZω z) ∎

-- | dot (−1,0,0) v ≡ −x
row-m100 : ∀ (x y z : Zω)
         → dot (negZω oneZω ∷ zeroZω ∷ zeroZω ∷ []) (x ∷ y ∷ z ∷ []) ≡ negZω x
row-m100 x y z = begin
    addZω (mulZω (negZω oneZω) x) (addZω (mulZω zeroZω y)
                                        (addZω (mulZω zeroZω z) zeroZω))
  ≡⟨ cong₂ addZω (neg-one-mul x)
        (cong₂ addZω (mulZω-zeroˡ y)
          (cong (λ t → addZω t zeroZω) (mulZω-zeroˡ z))) ⟩
    addZω (negZω x) (addZω zeroZω (addZω zeroZω zeroZω))
  ≡⟨ cong (addZω (negZω x)) (addZω-identityˡ (addZω zeroZω zeroZω)) ⟩
    addZω (negZω x) (addZω zeroZω zeroZω)
  ≡⟨ cong (addZω (negZω x)) (addZω-identityˡ zeroZω) ⟩
    addZω (negZω x) zeroZω
  ≡⟨ addZω-identityʳ (negZω x) ⟩
    negZω x ∎

--------------------------------------------------------------------------------
-- ⑥ 三条分量化线性方程（公共特征向量 v = (x,y,z) 必须满足）
--
--   (E1)  x          ≡ −z             （AB 交换子 第 0 行）
--   (E3)  x ⊕ (−y)   ≡ y ⊕ (−z)       （AB 交换子 第 2 行）
--   (F3)  y ⊕ (−z)   ≡ −x             （AD 交换子 第 2 行）
--------------------------------------------------------------------------------

proj0 : Vec3 → Zω
proj0 (a ∷ _ ∷ _ ∷ []) = a

proj2 : Vec3 → Zω
proj2 (_ ∷ _ ∷ c ∷ []) = c

-- | (E1) x ≡ −z
eq-E1 : ∀ (x y z c d : Zω)
   → mulMV3 A3 (x ∷ y ∷ z ∷ []) ≡ scaleV3 c (x ∷ y ∷ z ∷ [])
   → mulMV3 B3 (x ∷ y ∷ z ∷ []) ≡ scaleV3 d (x ∷ y ∷ z ∷ [])
   → x ≡ negZω z
eq-E1 x y z c d Av Bv =
  trans (sym (row-100 x y z))
    (trans (cong proj0 (AB-comm-act (x ∷ y ∷ z ∷ []) c d Av Bv))
           (row-001m x y z))

-- | (E3) x ⊕ (−y) ≡ y ⊕ (−z)
eq-E3 : ∀ (x y z c d : Zω)
   → mulMV3 A3 (x ∷ y ∷ z ∷ []) ≡ scaleV3 c (x ∷ y ∷ z ∷ [])
   → mulMV3 B3 (x ∷ y ∷ z ∷ []) ≡ scaleV3 d (x ∷ y ∷ z ∷ [])
   → addZω x (negZω y) ≡ addZω y (negZω z)
eq-E3 x y z c d Av Bv =
  trans (sym (row-1m10 x y z))
    (trans (cong proj2 (AB-comm-act (x ∷ y ∷ z ∷ []) c d Av Bv))
           (row-01m1 x y z))

-- | (F3) y ⊕ (−z) ≡ −x
eq-F3 : ∀ (x y z c e : Zω)
   → mulMV3 A3 (x ∷ y ∷ z ∷ []) ≡ scaleV3 c (x ∷ y ∷ z ∷ [])
   → mulMV3 D3 (x ∷ y ∷ z ∷ []) ≡ scaleV3 e (x ∷ y ∷ z ∷ [])
   → addZω y (negZω z) ≡ negZω x
eq-F3 x y z c e Av Dv =
  trans (sym (row-01m1 x y z))
    (trans (cong proj2 (AD-comm-act (x ∷ y ∷ z ∷ []) c e Av Dv))
           (row-m100 x y z))

--------------------------------------------------------------------------------
-- ⑦ 消元
--
--   (E1) ⇒ x = −z；(E3) ⇒ −y = y ⇒ 2y = 0 ⇒ y = 0；(F3) ⇒ −z = −x ⇒ z = x = −z
--   ⇒ 2z = 0 ⇒ z = 0 ⇒ x = 0。全程只用 2-无挠（`two-zero`），不需要 four-zero。
--------------------------------------------------------------------------------

-- | w 与自己相反 ⇒ w ≡ 0
self-neg-zero : ∀ (w : Zω) → negZω w ≡ w → w ≡ zeroZω
self-neg-zero w h =
  two-zero w
    (trans (twoZ-mul w)
      (trans (cong (λ t → addZω w t) (sym h)) (addZω-inverseʳ w)))

-- | (E1) + (E3) ⇒ −y ≡ y
neg-y : ∀ (x y z : Zω)
      → x ≡ negZω z
      → addZω x (negZω y) ≡ addZω y (negZω z)
      → negZω y ≡ y
neg-y x y z h1 h3 =
  add-cancelʳ (negZω y) y (negZω z)
    (trans (sym (addZω-comm (negZω z) (negZω y)))
      (trans (cong (λ t → addZω t (negZω y)) (sym h1)) h3))

-- | (E1) + y ≡ 0 + (F3) ⇒ z ≡ −z
neg-z : ∀ (x y z : Zω)
      → x ≡ negZω z
      → y ≡ zeroZω
      → addZω y (negZω z) ≡ negZω x
      → z ≡ negZω z
neg-z x y z h1 hy h4 =
  trans x≡z (trans h1 refl)
  where
    -- −z ≡ −x  （用 y ≡ 0 去掉 F3 左端首项）
    step1 : negZω z ≡ negZω x
    step1 = trans (sym (addZω-identityˡ (negZω z)))
              (trans (cong (λ t → addZω t (negZω z)) (sym hy)) h4)

    -- z ≡ x
    x≡z : z ≡ x
    x≡z = trans (sym (negZω-involutive z))
            (trans (cong negZω step1) (negZω-involutive x))

--------------------------------------------------------------------------------
-- ⑧ 主结论：3 维 ρ₃ 没有不变线
--------------------------------------------------------------------------------

no-invariant-line3
  : ¬ (Σ Vec3 (λ v → (v ≢ zeroV3)
              × (∀ (g : SL23) → Σ Zω (λ c →
                    mulMV3 (rho3 (toA4 g)) v ≡ scaleV3 c v))))
no-invariant-line3 ((x ∷ y ∷ z ∷ []) , vnz , evec) =
  vnz (vec3-cong x0 y0 z0)
  where
    h1 : x ≡ negZω z
    h1 = eq-E1 x y z (proj₁ (evec g0)) (proj₁ (evec g1))
                  (proj₂ (evec g0)) (proj₂ (evec g1))

    h3 : addZω x (negZω y) ≡ addZω y (negZω z)
    h3 = eq-E3 x y z (proj₁ (evec g0)) (proj₁ (evec g1))
                  (proj₂ (evec g0)) (proj₂ (evec g1))

    h4 : addZω y (negZω z) ≡ negZω x
    h4 = eq-F3 x y z (proj₁ (evec g0)) (proj₁ (evec g2))
                  (proj₂ (evec g0)) (proj₂ (evec g2))

    y0 : y ≡ zeroZω
    y0 = self-neg-zero y (neg-y x y z h1 h3)

    z0 : z ≡ zeroZω
    z0 = self-neg-zero z (sym (neg-z x y z h1 y0 h4))

    x0 : x ≡ zeroZω
    x0 = trans h1 (cong negZω z0)


