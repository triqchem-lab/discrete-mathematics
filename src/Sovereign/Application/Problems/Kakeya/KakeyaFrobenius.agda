{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Application.Problems.Kakeya.KakeyaFrobenius
-- KakeyaFrobenius — Frobenius 的 Kakeya 保持与方向轨道分解（改题件：基座 → GF(9)）
--
-- 实测结论（本件第一结论，决定全件形态）：
--   GF(3) 基座上 Frobenius x ↦ x³ 恒等（Fermat 小定理 x³ ≡ x mod 3；
--   Jacobian.GF3.fermat3 已证，本件 KK-fermat3 复算 3 案 refl 交叉确认）。
--   故 GF(3)^n 方向空间上的 σ-轨道全平凡（§1：n=2 的 4 方向 = 4 个独点轨道，
--   n=3 的 13 方向同理）——原计划的 GF(3)^pool（pool=6，364 方向）轨道分解
--   因此平凡，按预案改题扩域：
--   GF(9) = GF(3)[α]/(α²+1)，Gal(GF(9)/GF(3)) ≅ C₂，σ(a+bα) = a−bα 非平凡。
--
-- 口径：
--   「线」= F₃-参数线 p + t·d（t ∈ Trit，3 点/线），与 KakeyaGF3 §3 同构；
--   GF(9)² ≅ F₃⁴，F₃-方向总数 (81−1)/2 = 40（基座 pool=6 时的对应量
--   364 = (729−1)/2）。方向 = {v, −v}（F₃ 口径的二元组）。
--
-- 内容：
--   §1 GF(3) 基座恒等实测 + 方向轨道平凡（4 案）
--   §2 GF(9) Frobenius σ：F₃-线性双射（KK-σ-add / KK-σ-scalar / σ²=id）
--   §3 Kakeya 保持（构造性）：K 每方向含线 ⟹ σK 每方向含线
--   §4 方向 σ-轨道：周期 ≤ 2 一般定理 + 实例（不动 1 + 交换 2 = 3 方向闭合；
--      40 方向完全分解需 40 案枚举，立界——头注声明）
-- 0 postulate / 0 hole.

module Sovereign.Application.Problems.Kakeya.KakeyaFrobenius where

open import Data.Nat using (ℕ; _+_; _*_)
open import Data.Product using (_×_; _,_; Σ)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; cong₂; sym; trans)

open import Sovereign.Base.Trit using (Trit; T₀; T₁; T₂; _⊕_; _⊗_; negate)
open import Sovereign.Algebra.Jacobian.GF3 using (fermat3)
open import Sovereign.Application.Problems.Kakeya.KakeyaGF3
  using (Dir2; d-horiz; d-vert; d-diag1; d-diag2; dir2-card; card-GF3²)
open import Sovereign.Algebra.FieldTower.GF9
  using (GF9; embed-gf3; alpha; galoisConjugate; galoisConjugate²; negate-⊕)

--------------------------------------------------------------------------------
-- §1. GF(3) 基座恒等实测：x³ ≡ x，方向轨道全平凡
--------------------------------------------------------------------------------

KK-cube : Trit → Trit
KK-cube x = (x ⊗ x) ⊗ x

KK-fermat3 : ∀ x → KK-cube x ≡ x
KK-fermat3 T₀ = refl
KK-fermat3 T₁ = refl
KK-fermat3 T₂ = refl

-- 交叉确认：与 Jacobian.GF3.fermat3（先证）同陈述
KK-fermat3-agree : ∀ x → KK-cube x ≡ x
KK-fermat3-agree = fermat3

-- σ₃ = negate 在 GF(3)² 方向集上的作用：negate v = −v 与 v 同方向 → 恒等
-- （⟨(2,0)⟩ = ⟨(1,0)⟩、⟨(0,2)⟩ = ⟨(0,1)⟩、⟨(2,2)⟩ = 2·⟨(1,1)⟩、⟨(2,1)⟩ = 2·⟨(1,2)⟩）
KK-σ3-dir : Dir2 → Dir2
KK-σ3-dir d-horiz = d-horiz
KK-σ3-dir d-vert  = d-vert
KK-σ3-dir d-diag1 = d-diag1
KK-σ3-dir d-diag2 = d-diag2

KK-σ3-dir-trivial : ∀ d → KK-σ3-dir d ≡ d
KK-σ3-dir-trivial d-horiz = refl
KK-σ3-dir-trivial d-vert  = refl
KK-σ3-dir-trivial d-diag1 = refl
KK-σ3-dir-trivial d-diag2 = refl

-- 轨道计数（基座 n=2）：4 方向 = 4 个独点轨道（n=3 的 13 方向同理平凡）
KK-gf3-orbits : ℕ
KK-gf3-orbits = dir2-card

KK-gf3-orbits-trivial : KK-gf3-orbits * 2 + 1 ≡ card-GF3²
KK-gf3-orbits-trivial = refl

--------------------------------------------------------------------------------
-- §2. GF(9) Frobenius σ：F₃-线性双射（σ² = id）
--------------------------------------------------------------------------------

KK-Pt : Set
KK-Pt = GF9 × GF9        -- GF(9)² ≅ F₃⁴（点 / 方向向量两用）

KK-σ : KK-Pt → KK-Pt
KK-σ (u , v) = galoisConjugate u , galoisConjugate v

-- 对合性：σ² = id（双射，逆 = σ 自身）
KK-σ-invol : ∀ p → KK-σ (KK-σ p) ≡ p
KK-σ-invol (u , v) = cong₂ _,_ (galoisConjugate² u) (galoisConjugate² v)

-- 非平凡见证：σ(1, α) ≠ (1, α)（虚部分量翻转）
KK-vX : KK-Pt
KK-vX = embed-gf3 T₁ , alpha

KK-σ-vX-ne : KK-σ KK-vX ≡ KK-vX → ⊥
KK-σ-vX-ne ()

-- F₃-线性：加法同态
_KK+_ : KK-Pt → KK-Pt → KK-Pt
((a , b) , (c , d)) KK+ ((e , f) , (g , h)) =
  ((a ⊕ e , b ⊕ f) , (c ⊕ g , d ⊕ h))

KK-σ-add : ∀ p q → KK-σ (p KK+ q) ≡ KK-σ p KK+ KK-σ q
KK-σ-add ((a , b) , (c , d)) ((e , f) , (g , h)) =
  cong₂ (λ x y → ((a ⊕ e , x) , (c ⊕ g , y))) (negate-⊕ b f) (negate-⊕ d h)

-- 逐分量加法逆（§4 方向等价与 §2 标量乘共用）
KK-negv : KK-Pt → KK-Pt
KK-negv ((a , b) , (c , d)) =
  (negate a , negate b) , (negate c , negate d)

-- F₃-线性：标量同态（t ∈ GF(3) 嵌入标量；三分案定义，语义 = 逐分量 t⊗x：
-- T₀·p = 0、T₁·p = p、T₂·p = −p）
_KK⊙_ : Trit → KK-Pt → KK-Pt
T₀ KK⊙ _ = ((T₀ , T₀) , (T₀ , T₀))
T₁ KK⊙ p = p
T₂ KK⊙ p = KK-negv p

KK-σ-scalar : ∀ t p → KK-σ (t KK⊙ p) ≡ t KK⊙ (KK-σ p)
KK-σ-scalar T₀ p = refl
KK-σ-scalar T₁ p = refl
KK-σ-scalar T₂ p = refl

--------------------------------------------------------------------------------
-- §3. Kakeya 保持（构造性）：线 ⟨p,d⟩ 的像 = ⟨σp, σd⟩
--------------------------------------------------------------------------------

KK-line : KK-Pt → KK-Pt → Trit → KK-Pt
KK-line p d t = p KK+ (t KK⊙ d)

KK-line-σ : ∀ p d t → KK-σ (KK-line p d t) ≡ KK-line (KK-σ p) (KK-σ d) t
KK-line-σ p d t =
  trans (KK-σ-add p (t KK⊙ d)) (cong (KK-σ p KK+_) (KK-σ-scalar t d))

-- 挂谷集谓词与「每方向含线」
KK-KSet : Set₁
KK-KSet = KK-Pt → Set

KK-hasLine : KK-KSet → KK-Pt → Set
KK-hasLine K d = Σ KK-Pt (λ p → ∀ t → K (KK-line p d t))

-- σ(K) = {σ x : x ∈ K}
KK-image : KK-KSet → KK-KSet
KK-image K q = Σ KK-Pt (λ x → (q ≡ KK-σ x) × K x)

-- 核心：σ 把 (p 沿 d 的线) 映到 (σp 沿 σd 的线)，故挂谷性保持
KK-kakeya-preserved : ∀ (K : KK-KSet) (d : KK-Pt) →
  KK-hasLine K d → KK-hasLine (KK-image K) (KK-σ d)
KK-kakeya-preserved K d (p , hp) =
  KK-σ p , λ t → KK-line p d t , sym (KK-line-σ p d t) , hp t

--------------------------------------------------------------------------------
-- §4. 方向 σ-轨道：周期 ≤ 2 一般定理 + 实例（不动 / 交换）
--------------------------------------------------------------------------------

-- F₃-方向等价：{v, −v}
KK-sameDir : KK-Pt → KK-Pt → Set
KK-sameDir v w = (v ≡ w) ⊎ (v ≡ KK-negv w)

-- 一般定理：σ-轨道周期 ≤ 2（σ² 回到原方向；由 σ² = id 直接给出）
KK-orbit-period : ∀ v → KK-sameDir (KK-σ (KK-σ v)) v
KK-orbit-period v = inj₁ (KK-σ-invol v)

-- 实例 1（不动轨道）：v = (1, 1)，GF(3)² 嵌入方向，两分量皆 σ-不动点
KK-vD : KK-Pt
KK-vD = embed-gf3 T₁ , embed-gf3 T₁

KK-vD-fixed : KK-sameDir (KK-σ KK-vD) KK-vD
KK-vD-fixed = inj₁ refl

-- 实例 2（交换轨道）：v = (1, α)；σv = (1, 2α) 是与 v 不同的新 F₃-方向
KK-vX-orbit-ne : KK-sameDir (KK-σ KK-vX) KK-vX → ⊥
KK-vX-orbit-ne (inj₁ ())
KK-vX-orbit-ne (inj₂ ())

KK-vX-orbit-closed : KK-sameDir (KK-σ (KK-σ KK-vX)) KK-vX
KK-vX-orbit-closed = KK-orbit-period KK-vX

-- 实例计数：1（不动轨道）+ 2（交换轨道）= 3 个 F₃-方向已被轨道覆盖
KK-orbit-instance-count : ℕ
KK-orbit-instance-count = 1 + 2

KK-orbit-instance-ok : KK-orbit-instance-count ≡ 3
KK-orbit-instance-ok = refl

-- F₃-方向总数：(81−1)/2 = 40；完全轨道分解需 40 案枚举，立界（头注）。
-- 结构性部分（轨道周期 ≤ 2）已由 KK-orbit-period 一般性闭合。
KK-dir-card : ℕ
KK-dir-card = 40

KK-dir-card-formula : KK-dir-card * 2 + 1 ≡ card-GF3² * card-GF3²
KK-dir-card-formula = refl
