{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Constitution.DecisionSoundness
--
-- 宪法：离散判定层的**可靠性边界** —— dype 判定引擎修复的 Agda 依据。
--
-- 第一原理：结构 = 生成方式。判定「两个对象相等」只能沿**生成方式**做
-- （构造子 / 分量 / 精确编码），不得用「某个投影的像相同」冒充相等。
-- 传统数学的三处缺陷在此被显式挡住：
--
--   ① 缺**代数刚性**：连续统上 Aut(ℂ) 有 2^beth 个野自同构（无原生共轭）；
--      GF(9)/GF(3) 的 Frobenius σ(x)=x³ 是算术强制的原生共轭，Gal ≅ C₂。
--      本模块把它落成定理：**σ 的不动域恰为 GF(3)**。
--   ② **存在逃逸**：连续统里 ε→0 逃逸 / 测度泄漏为零；在判定层它的同构像是
--      「把投影相同当相等」—— dype 的 `gf9CrtProject`（只取实部）与
--      `convTopological`（只比 6624 对齐奇偶）正是这种逃逸。
--      本模块把「投影有损」形式化为 LossyProjection：**存在同像异点**。
--   ③ **相位不可约**：C₄→C₂ 的非忠实商不构成合法同余。此处给出
--      σ 在相位层非平凡的见证（共轭对必须判为相异）。
--
-- 对齐：Algebra/GF9.agda（galoisConjugate:95、σ²=id、Gal(GF(9)/GF(3))≅C₂）；
--   docs/duodecimal/11-type-theory-presentation.md（展示群八要素）；
--   docs/cross-level/frobenius-vs-conjugation-erratum.md（σ 由算术强制）。
--
-- 0 postulate / 0 hole。本文件只做**判定层**的宪法性陈述，不重复域公理。

module Sovereign.Constitution.DecisionSoundness where

open import Data.Bool using (Bool; true; false)
open import Data.Empty using (⊥)
open import Data.Product using (_×_; _,_; ∃; ∃-syntax; proj₁; proj₂)
open import Data.Vec using (Vec; []; _∷_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; cong; cong₂; sym; trans)

open import Sovereign.Base.Trit using (Trit; T₀; T₁; T₂; negate)
open import Sovereign.Algebra.GF9 using (GF9; galoisConjugate)

--------------------------------------------------------------------------------
-- §0 逻辑小件（自足，不依赖 stdlib 的 Bool 库）
--------------------------------------------------------------------------------

_⇔_ : Set → Set → Set
P ⇔ Q = (P → Q) × (Q → P)

andBool : Bool → Bool → Bool
andBool true true = true
andBool _    _    = false

andBool-trueˡ : ∀ {p q : Bool} → andBool p q ≡ true → p ≡ true
andBool-trueˡ {true}  {true}  _ = refl
andBool-trueˡ {true}  {false} ()
andBool-trueˡ {false} {_}     ()

andBool-trueʳ : ∀ {p q : Bool} → andBool p q ≡ true → q ≡ true
andBool-trueʳ {true}  {true}  _ = refl
andBool-trueʳ {true}  {false} ()
andBool-trueʳ {false} {_}     ()

--------------------------------------------------------------------------------
-- §1 Trit 级基础：构造子相异 ⇒ 空模式；negate 的不动点只有 T₀
--------------------------------------------------------------------------------

T₁≢T₀ : T₁ ≢ T₀
T₁≢T₀ ()

T₀≢T₁ : T₀ ≢ T₁
T₀≢T₁ ()

T₂≢T₁ : T₂ ≢ T₁
T₂≢T₁ ()

-- | negate 的不动点只有 T₀ —— 「代数刚性」在本层的种子：
--   σ(a,b)=(a,⊖b) 若要固定 b，只能是 b = 0。
neg-fix⇒zero : ∀ (b : Trit) → negate b ≡ b → b ≡ T₀
neg-fix⇒zero T₀ _ = refl
neg-fix⇒zero T₁ ()
neg-fix⇒zero T₂ ()

zero-fix : negate T₀ ≡ T₀
zero-fix = refl

--------------------------------------------------------------------------------
-- §2 可判定相等必须是**分量式**的，且带可靠性证明
--
-- 宪法要求：判定过程本身是**带证明字段的结构**（结构即签名），
--   而不是一个裸 Bool —— 否则「相等」只是实现细节，不是命题。
--------------------------------------------------------------------------------

record SoundDecision (A : Set) : Set where
  field
    decide    : A → A → Bool
    refl-true : ∀ (x : A) → decide x x ≡ true
    sound     : ∀ (x y : A) → decide x y ≡ true → x ≡ y

tritEq : Trit → Trit → Bool
tritEq T₀ T₀ = true
tritEq T₀ T₁ = false
tritEq T₀ T₂ = false
tritEq T₁ T₀ = false
tritEq T₁ T₁ = true
tritEq T₁ T₂ = false
tritEq T₂ T₀ = false
tritEq T₂ T₁ = false
tritEq T₂ T₂ = true

tritEq-refl : ∀ (a : Trit) → tritEq a a ≡ true
tritEq-refl T₀ = refl
tritEq-refl T₁ = refl
tritEq-refl T₂ = refl

tritEq-true : ∀ (a b : Trit) → tritEq a b ≡ true → a ≡ b
tritEq-true T₀ T₀ _ = refl
tritEq-true T₀ T₁ ()
tritEq-true T₀ T₂ ()
tritEq-true T₁ T₀ ()
tritEq-true T₁ T₁ _ = refl
tritEq-true T₁ T₂ ()
tritEq-true T₂ T₀ ()
tritEq-true T₂ T₁ ()
tritEq-true T₂ T₂ _ = refl

-- | GF(9) 的**正确**判定：实部 ∧ 虚部都相等。
--   对比 dype 的 `gf9CrtProject`（只取实部 ⇒ 9 元素只映到 3 个坐标）——
--   那是投影，不是判定。两部分都进判定，于是可靠性可证。
decEqGf9 : GF9 → GF9 → Bool
decEqGf9 (a , b) (c , d) = andBool (tritEq a c) (tritEq b d)

decEqGf9-refl : ∀ (x : GF9) → decEqGf9 x x ≡ true
decEqGf9-refl (a , b) = cong₂ andBool (tritEq-refl a) (tritEq-refl b)

decEqGf9-sound : ∀ (x y : GF9) → decEqGf9 x y ≡ true → x ≡ y
decEqGf9-sound (a , b) (c , d) p =
  cong₂ _,_ (tritEq-true a c (andBool-trueˡ p))
            (tritEq-true b d (andBool-trueʳ p))

gf9SoundDecision : SoundDecision GF9
gf9SoundDecision = record
  { decide    = decEqGf9
  ; refl-true = decEqGf9-refl
  ; sound     = decEqGf9-sound
  }

--------------------------------------------------------------------------------
-- §3 代数刚性：Frobenius 的不动域恰为 GF(3)
--------------------------------------------------------------------------------

-- | σ(a + bα) = a − bα（= x³，幂映射本身即同态）
sigma : GF9 → GF9
sigma = galoisConjugate

-- | σ 固定 x ⇒ 虚部为 0（不动域 ⊆ GF(3)）
sigma-fix⇒real : ∀ (x : GF9) → sigma x ≡ x → proj₂ x ≡ T₀
sigma-fix⇒real (a , b) p = neg-fix⇒zero b (cong proj₂ p)

-- | 虚部为 0 ⇒ σ 固定 x（GF(3) ⊆ 不动域）
real⇒sigma-fix : ∀ (x : GF9) → proj₂ x ≡ T₀ → sigma x ≡ x
real⇒sigma-fix (a , b) p = cong (a ,_) (trans (cong negate p) (sym p))

-- | 合起来：**不动域 = 纯实部**（GF(3) 的嵌入像）—— 代数刚性
fix-iff-real : ∀ (x : GF9) → (sigma x ≡ x) ⇔ (proj₂ x ≡ T₀)
fix-iff-real x = sigma-fix⇒real x , real⇒sigma-fix x

-- | σ 在相位层**非平凡**（相位不可约：不能把 C₄ 商成 C₂）
sigma-nontrivial : sigma (T₀ , T₁) ≢ (T₀ , T₁)
sigma-nontrivial p = T₂≢T₁ (cong proj₂ p)

--------------------------------------------------------------------------------
-- §4 存在逃逸的形式化：投影有损（同像异点）
--------------------------------------------------------------------------------

-- | 「有损投影」= 存在两个**相异**对象映到同一像。
--   判定层若用它冒充相等，就等于在离散基座上重演连续统的存在逃逸。
record LossyProjection (A B : Set) : Set where
  field
    project      : A → B
    nonInjective : ∃[ x ] ∃[ y ] ((project x ≡ project y) × (x ≢ y))

-- | 实部投影（= dype `gf9CrtProject` 的全部信息量）有损：
--   (T₁,T₀) (T₁,T₁) (T₁,T₂) 实部都是 T₁，但三者互不相等。
realPart : GF9 → Trit
realPart = proj₁

realPart-lossy : LossyProjection GF9 Trit
realPart-lossy = record
  { project      = realPart
  ; nonInjective = (T₁ , T₀) , (T₁ , T₁) , refl , (λ p → T₀≢T₁ (cong proj₂ p))
  }

-- | 群**轨道**等价同样不是相等：4-trit 截面上的置换把互异两点放进同一轨道。
--   对照 dype `convGeometric`（A4 轨道等价冒充格点相等）
--   与 `convTopological`（只比 6624 对齐奇偶）。
hd : Vec Trit 4 → Trit
hd (x ∷ _) = x

swap01 : Vec Trit 4 → Vec Trit 4
swap01 (x ∷ y ∷ z ∷ w ∷ []) = y ∷ x ∷ z ∷ w ∷ []

orbit-has-distinct-points : ∃[ x ] ∃[ y ] ((swap01 x ≡ y) × (x ≢ y))
orbit-has-distinct-points =
  (T₁ ∷ T₀ ∷ T₀ ∷ T₀ ∷ []) , (T₀ ∷ T₁ ∷ T₀ ∷ T₀ ∷ []) , refl
    , (λ p → T₁≢T₀ (cong hd p))

--------------------------------------------------------------------------------
-- §5 判定层宪法条目（可引用给 dype 的 Haskell 侧）
--------------------------------------------------------------------------------

-- C1 判定相等只能沿生成方式：Trit 逐构造子、GF(9) 逐分量（§2）
-- C2 投影（CRT 余数 / 实部 / 轨道 / 对齐奇偶）**有损**，只能作不变量，不得作相等（§4）
-- C3 相位不可约：共轭对必须判为**相异**（§3 sigma-nontrivial）
-- C4 刚性：原生共轭 σ 恰固定基域（§3 fix-iff-real）—— 离散基座相对连续统的结构性优势
-- C5 不可判不得冒充相等：判定结果必须允许 Unknown，而不是 Equal/NotEqual 二选一

-- 0 postulate.
