{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Algebra.FieldTower.Zomega
-- Z[ω] 环律提升层: 把 RootMath.Eisenstein 已证环律迁移到 A4Representation 的 Zω 载体
--
-- 数学背景:
--   Z[ω] = Eisenstein 整数环 ℤ[ω], ω² + ω + 1 = 0 (即 ω² = -1-ω, ω³ = 1)。
--   元素 a + bω (a,b ∈ ℤ), 乘法 (a+bω)(c+dω) = (ac-bd) + (ad+bc-bd)ω
--   — ω² = -1-ω 是化简关键 (bd·ω² = -bd - bd·ω, 并入常数项与 ω 项)。
--
-- 载体勘定 (勿重定义):
--   Zω / mkZω / addZω / mulZω / negZω / zeroZω / oneZω 已在
--   Sovereign.Synthesis.A4.A4Representation 定义 (记录对 (a,b) ∈ ℤ²)。
--   本模块 import 复用, 只补环律, 不新增载体。
--
-- 路径选型 (A: 逐分量代数链 —— 已在库内完成, 本模块做迁移而不重证):
--   Sovereign.Foundation.Eisenstein 的 Eisenstein 载体与 Zω 的运算公式逐字同形
--   (同一 ℤ 运算、同一 ω²=-1-ω 化简形), 且已证全套环律:
--     +ᵉ-comm / +ᵉ-assoc / +ᵉ-identityˡʳ / +ᵉ-inverseˡʳ
--     *ᵉ-comm / *ᵉ-assoc / *ᵉ-identityˡʳ / *ᵉ-distribˡʳ
--   本模块经「记录分量投影桥」liftEis (§0) 把定理迁到 Zω —— 不重复 ≈250 行
--   分量代数链 (重新证明已有引理 = 浪费)。零元律 Eisenstein 未收, 由 §3 直接补。
--   对抗验证 §4 给出具体点 refl 交叉比对 (直接计算 vs 定理实例)。
--
-- 用途: A4ThreeDimRep 的 rho3-hom 生成元路线 —— mulMat 结合/分配律展开的
--   Zω 分量证明消耗 mulZω-assoc / mulZω-distribˡʳ / mulZω-comm (dot 重排)。
--
-- 0 postulate / 0 hole / 0 sorry。

module Sovereign.Algebra.FieldTower.Zomega where

open import Data.Integer.Base using (ℤ; +_; -[1+_]; _+_; _-_; _*_; -_; ∣_∣)
open import Data.Integer.Properties
  using (*-zeroˡ; *-zeroʳ; neg-involutive; neg-distribˡ-*; neg-distrib-+;
         +-comm; +-assoc; +-identityˡ; +-identityʳ; +-inverseˡ;
         *-comm; *-distribˡ-+)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; cong; cong₂; sym; trans; module ≡-Reasoning)
open import Data.Empty using (⊥)

open ≡-Reasoning

open import Sovereign.Synthesis.A4.A4Representation
  using (Zω; mkZω; addZω; negZω; subZω; mulZω; conjZω; zeroZω; oneZω; ω; ω²)
open import Sovereign.Foundation.Eisenstein
  using (Eisenstein; eis; _+ᵉ_; _*ᵉ_;
         +ᵉ-comm; +ᵉ-assoc; +ᵉ-identityˡ; +ᵉ-identityʳ; +ᵉ-inverseˡ; +ᵉ-inverseʳ;
         *ᵉ-comm; *ᵉ-assoc; *ᵉ-identityˡ; *ᵉ-identityʳ; *ᵉ-distribˡ; *ᵉ-distribʳ;
         conjᵉ-mul; norm-mul; neg-*-r; neg-*-l)

--------------------------------------------------------------------------------
-- §0. 记录分量投影桥: Eisenstein 等式 → Zω 等式
--   两载体是同一乘法公式的两次定义 (mkZω (a*c-b*d) (a*d+b*c-b*d) ↔ eis 同形),
--   故 Eisenstein 定理的两个分量投影就是 Zω 目标的两个分量。
--------------------------------------------------------------------------------

eisA : Eisenstein → ℤ
eisA (eis x _) = x

eisB : Eisenstein → ℤ
eisB (eis _ y) = y

-- 桥: Eisenstein 上的等式 ⇒ Zω 上的等式 (两侧分量定义同形, 直接对齐)
liftEis : ∀ {x y : Eisenstein} → x ≡ y → mkZω (eisA x) (eisB x) ≡ mkZω (eisA y) (eisB y)
liftEis p = cong₂ mkZω (cong eisA p) (cong eisB p)

--------------------------------------------------------------------------------
-- §1. 加法: 交换幺半群 + 逆 (addZω / negZω / zeroZω)
--------------------------------------------------------------------------------

addZω-comm : ∀ x y → addZω x y ≡ addZω y x
addZω-comm (mkZω a b) (mkZω c d) = liftEis (+ᵉ-comm (eis a b) (eis c d))

addZω-assoc : ∀ x y z → addZω (addZω x y) z ≡ addZω x (addZω y z)
addZω-assoc (mkZω a b) (mkZω c d) (mkZω e f) = liftEis (+ᵉ-assoc (eis a b) (eis c d) (eis e f))

addZω-identityˡ : ∀ x → addZω zeroZω x ≡ x
addZω-identityˡ (mkZω a b) = liftEis (+ᵉ-identityˡ (eis a b))

addZω-identityʳ : ∀ x → addZω x zeroZω ≡ x
addZω-identityʳ (mkZω a b) = liftEis (+ᵉ-identityʳ (eis a b))

addZω-inverseˡ : ∀ x → addZω (negZω x) x ≡ zeroZω
addZω-inverseˡ (mkZω a b) = liftEis (+ᵉ-inverseˡ (eis a b))

addZω-inverseʳ : ∀ x → addZω x (negZω x) ≡ zeroZω
addZω-inverseʳ (mkZω a b) = liftEis (+ᵉ-inverseʳ (eis a b))

negZω-involutive : ∀ x → negZω (negZω x) ≡ x
negZω-involutive (mkZω a b) = cong₂ mkZω (neg-involutive a) (neg-involutive b)

--------------------------------------------------------------------------------
-- §1.5 加法重排: 与乘法无关的纯交换群事实
--   矩阵乘法相容性（`mulMV·mulM`）要把「按列分组」的加法树改写成「按行分组」，
--   即对加法做转置。这里只放与 Zω 具体系数无关的通用换位，供 2/3 维两条路共用。
--------------------------------------------------------------------------------

-- | 三项换位：(a ⊕ b) ⊕ c ≡ (a ⊕ c) ⊕ b
add-swap : ∀ a b c → addZω (addZω a b) c ≡ addZω (addZω a c) b
add-swap a b c = begin
    addZω (addZω a b) c
  ≡⟨ addZω-assoc a b c ⟩
    addZω a (addZω b c)
  ≡⟨ cong (addZω a) (addZω-comm b c) ⟩
    addZω a (addZω c b)
  ≡⟨ sym (addZω-assoc a c b) ⟩
    addZω (addZω a c) b ∎

-- | 四项换位（2×2 加法转置）：(a ⊕ b) ⊕ (c ⊕ d) ≡ (a ⊕ c) ⊕ (b ⊕ d)
add-swap4 : ∀ a b c d
          → addZω (addZω a b) (addZω c d) ≡ addZω (addZω a c) (addZω b d)
add-swap4 a b c d = begin
    addZω (addZω a b) (addZω c d)
  ≡⟨ addZω-assoc a b (addZω c d) ⟩
    addZω a (addZω b (addZω c d))
  ≡⟨ cong (addZω a) (sym (addZω-assoc b c d)) ⟩
    addZω a (addZω (addZω b c) d)
  ≡⟨ cong (λ t → addZω a (addZω t d)) (addZω-comm b c) ⟩
    addZω a (addZω (addZω c b) d)
  ≡⟨ cong (addZω a) (addZω-assoc c b d) ⟩
    addZω a (addZω c (addZω b d))
  ≡⟨ sym (addZω-assoc a c (addZω b d)) ⟩
    addZω (addZω a c) (addZω b d) ∎

-- | 2×3 加法转置：
--   (a₀⊕b₀) ⊕ ((a₁⊕b₁) ⊕ (a₂⊕b₂)) ≡ (a₀⊕(a₁⊕a₂)) ⊕ (b₀⊕(b₁⊕b₂))
add-transpose-23 : ∀ a₀ a₁ a₂ b₀ b₁ b₂
                 → addZω (addZω a₀ b₀) (addZω (addZω a₁ b₁) (addZω a₂ b₂))
                 ≡ addZω (addZω a₀ (addZω a₁ a₂)) (addZω b₀ (addZω b₁ b₂))
add-transpose-23 a₀ a₁ a₂ b₀ b₁ b₂ = begin
    addZω (addZω a₀ b₀) (addZω (addZω a₁ b₁) (addZω a₂ b₂))
  ≡⟨ cong (addZω (addZω a₀ b₀)) (add-swap4 a₁ b₁ a₂ b₂) ⟩
    addZω (addZω a₀ b₀) (addZω (addZω a₁ a₂) (addZω b₁ b₂))
  ≡⟨ sym (addZω-assoc (addZω a₀ b₀) (addZω a₁ a₂) (addZω b₁ b₂)) ⟩
    addZω (addZω (addZω a₀ b₀) (addZω a₁ a₂)) (addZω b₁ b₂)
  ≡⟨ cong (λ t → addZω t (addZω b₁ b₂)) (add-swap a₀ b₀ (addZω a₁ a₂)) ⟩
    addZω (addZω (addZω a₀ (addZω a₁ a₂)) b₀) (addZω b₁ b₂)
  ≡⟨ addZω-assoc (addZω a₀ (addZω a₁ a₂)) b₀ (addZω b₁ b₂) ⟩
    addZω (addZω a₀ (addZω a₁ a₂)) (addZω b₀ (addZω b₁ b₂)) ∎

--------------------------------------------------------------------------------
-- §2. 乘法: 交换幺半群 (mulZω / oneZω) —— 核心: 结合律
--------------------------------------------------------------------------------

mulZω-assoc : ∀ x y z → mulZω (mulZω x y) z ≡ mulZω x (mulZω y z)
mulZω-assoc (mkZω a b) (mkZω c d) (mkZω e f) = liftEis (*ᵉ-assoc (eis a b) (eis c d) (eis e f))

mulZω-comm : ∀ x y → mulZω x y ≡ mulZω y x
mulZω-comm (mkZω a b) (mkZω c d) = liftEis (*ᵉ-comm (eis a b) (eis c d))

mulZω-identityˡ : ∀ x → mulZω oneZω x ≡ x
mulZω-identityˡ (mkZω a b) = liftEis (*ᵉ-identityˡ (eis a b))

mulZω-identityʳ : ∀ x → mulZω x oneZω ≡ x
mulZω-identityʳ (mkZω a b) = liftEis (*ᵉ-identityʳ (eis a b))

--------------------------------------------------------------------------------
-- §3. 分配律与零元 (mulZω / addZω 交互)
--------------------------------------------------------------------------------

mulZω-distribˡ : ∀ x y z → mulZω x (addZω y z) ≡ addZω (mulZω x y) (mulZω x z)
mulZω-distribˡ (mkZω a b) (mkZω c d) (mkZω e f) =
  liftEis (*ᵉ-distribˡ (eis a b) (eis c d) (eis e f))

mulZω-distribʳ : ∀ x y z → mulZω (addZω x y) z ≡ addZω (mulZω x z) (mulZω y z)
mulZω-distribʳ (mkZω a b) (mkZω c d) (mkZω e f) =
  liftEis (*ᵉ-distribʳ (eis a b) (eis c d) (eis e f))

-- 零元律 (Eisenstein 未收, 由 ℤ 的 *-zeroˡ/ʳ 直接补)
mulZω-zeroˡ : ∀ x → mulZω zeroZω x ≡ zeroZω
mulZω-zeroˡ (mkZω a b) = cong₂ mkZω comp1 comp2
  where
  comp1 : + 0 * a - + 0 * b ≡ + 0
  comp1 = trans (cong₂ _-_ (*-zeroˡ a) (*-zeroˡ b)) refl

  comp2 : + 0 * b + + 0 * a - + 0 * b ≡ + 0
  comp2 = trans (cong₂ (λ u v → u + v - u) (*-zeroˡ b) (*-zeroˡ a)) refl

mulZω-zeroʳ : ∀ x → mulZω x zeroZω ≡ zeroZω
mulZω-zeroʳ (mkZω a b) = cong₂ mkZω comp1 comp2
  where
  comp1 : a * + 0 - b * + 0 ≡ + 0
  comp1 = trans (cong₂ _-_ (*-zeroʳ a) (*-zeroʳ b)) refl

  comp2 : a * + 0 + b * + 0 - b * + 0 ≡ + 0
  comp2 = trans (cong₂ (λ u v → u + v - v) (*-zeroʳ a) (*-zeroʳ b)) refl

--------------------------------------------------------------------------------
-- §4. 对抗验证: 具体点上「直接计算」与「定理实例」交叉比对
--   全部具体 ℤ 常数: refl 闭合 = 定义归约到同一闭项;
--   同一等式再由 §1–§3 定理实例给出第二路径, 两路一致才闭合。
--------------------------------------------------------------------------------

private
  x₁ y₁ z₁ : Zω
  x₁ = mkZω (+ 2) -[1+ 0 ]      -- 2 - ω
  y₁ = mkZω -[1+ 1 ] (+ 3)      -- -2 + 3ω
  z₁ = ω                        -- ω

-- 结合律: 路径 1 = 直接计算
assoc-check-calc : mulZω (mulZω x₁ y₁) z₁ ≡ mulZω x₁ (mulZω y₁ z₁)
assoc-check-calc = refl

-- 结合律: 路径 2 = 定理实例
assoc-check-thm : mulZω (mulZω x₁ y₁) z₁ ≡ mulZω x₁ (mulZω y₁ z₁)
assoc-check-thm = mulZω-assoc x₁ y₁ z₁

-- 分配律: 路径 1 = 直接计算
distrib-check-calc : mulZω x₁ (addZω y₁ z₁) ≡ addZω (mulZω x₁ y₁) (mulZω x₁ z₁)
distrib-check-calc = refl

-- 分配律: 路径 2 = 定理实例
distrib-check-thm : mulZω x₁ (addZω y₁ z₁) ≡ addZω (mulZω x₁ y₁) (mulZω x₁ z₁)
distrib-check-thm = mulZω-distribˡ x₁ y₁ z₁

-- 交换律: 直接计算
comm-check-calc : mulZω x₁ y₁ ≡ mulZω y₁ x₁
comm-check-calc = refl

-- ω 关系式 sanity: ω³ = 1 在 mulZω 下闭合 (与 A4Representation.omega-cubed 同源)
omega-cubed-check : mulZω (mulZω ω ω) ω ≡ oneZω
omega-cubed-check = refl

-- ω² = -1 - ω 在 mulZω 下闭合 (与 A4Representation.omega-squared-form 同源)
omega-squared-check : mulZω ω ω ≡ addZω (negZω oneZω) (negZω ω)
omega-squared-check = refl

--------------------------------------------------------------------------------
-- §5. 负元与乘法、加法（补 ℤ 在负数处不 refl 归约的那两条）
--
--   背景：ℤ 的 `_*_` 是 `sign ◃ (|_| * |_|)`，`_+_` 在混合符号处也不按字面归约。
--   于是 (−a)·(−b) ≡ a·b、a(c − d) 这类式子虽然是"显然"的，Agda 却要显式引理。
--   这两条（ˡ 与 ʳ）正是下游（A₄ 表示的交换子、消元里的负数乘积）唯一需要的形态。
--------------------------------------------------------------------------------

-- | 负元是加法的同态：−(x + y) ≡ (−x) + (−y)
negZω-add : ∀ x y → negZω (addZω x y) ≡ addZω (negZω x) (negZω y)
negZω-add (mkZω a b) (mkZω c d) =
  cong₂ mkZω (neg-distrib-+ a c) (neg-distrib-+ b d)

-- | (−x)·y ≡ −(x·y)
negZω-mulˡ : ∀ x y → mulZω (negZω x) y ≡ negZω (mulZω x y)
negZω-mulˡ (mkZω a b) (mkZω c d) = cong₂ mkZω c1 c2
  where
    -- 坐标 1：(−a)c − (−b)d ≡ −(ac − bd)
    c1 : (- a) * c - (- b) * d ≡ - (a * c - b * d)
    c1 = trans (cong₂ _-_ (sym (neg-distribˡ-* a c)) (sym (neg-distribˡ-* b d)))
               (sym (neg-distrib-+ (a * c) (- (b * d))))

    -- 坐标 2：(−a)d + (−b)c − (−b)d ≡ −(ad + bc − bd)
    c2 : (- a) * d + (- b) * c - (- b) * d ≡ - (a * d + b * c - b * d)
    c2 = trans
           (cong₂ _-_
             (cong₂ _+_ (sym (neg-distribˡ-* a d)) (sym (neg-distribˡ-* b c)))
             (sym (neg-distribˡ-* b d)))
           (trans (cong (λ t → t + (- (- (b * d))))
                        (sym (neg-distrib-+ (a * d) (b * c))))
                  (sym (neg-distrib-+ (a * d + b * c) (- (b * d)))))

-- | x·(−y) ≡ −(x·y)（由 ˡ + 交换律导出，不再重证分量）
negZω-mulʳ : ∀ x y → mulZω x (negZω y) ≡ negZω (mulZω x y)
negZω-mulʳ x y =
  trans (mulZω-comm x (negZω y))
    (trans (negZω-mulˡ y x) (cong negZω (mulZω-comm y x)))

--------------------------------------------------------------------------------
-- §6. ω 的阶锚（三个阶的区分: 加法无限阶 / 乘法 3 阶 / 单位群 C₆）
--   加法群: Z[ω] ≅ ℤ² 自由模（秩 2），ω 加法无限阶——任何 n·ω ≠ 0 (n≠0)；
--   乘法幺半群: ω³ = 1，ω 是 3 次单位根（乘法阶恰 3）；
--   单位群: Z[ω]^× = {±1, ±ω, ±ω²} ≅ C₆（§9）。
--   特征 0 是关键: GF(3) 中 ω ≡ 1（x³−1=(x−1)³ 单根塌缩），此处 ω ≢ 1 严格成立。
--------------------------------------------------------------------------------

private
  b-one-vs-zero : Zω.b ω ≡ Zω.b zeroZω → ⊥
  b-one-vs-zero = λ ()

-- | ω ≢ 0: ω-系数 1 ≠ 0（加法无限阶的最小锚）
omega-nonzero : ω ≢ zeroZω
omega-nonzero eq = b-one-vs-zero (cong Zω.b eq)

-- | ω ≢ 1: ω-系数 1 ≠ 0（乘法 3 阶非平凡的锚; 特征 3 下此式失效）
omega-not-one : ω ≢ oneZω
omega-not-one eq = b-one-vs-zero (cong Zω.b eq)

--------------------------------------------------------------------------------
-- §7. 共轭 conjZω（ω ↦ ω²）: Gal(Z[ω]/ℤ) ≅ ℤ/2 的对合环自同构
--   注意: 这是 Galois 共轭（复共轭），不是 GF(9) 的 Frobenius x↦x³
--   （char 0 下 x↦x³ 不保持加法，不是环同态——见 ZomegaMod3 头注）。
--------------------------------------------------------------------------------

-- | 对合性: conj² = id —— Gal ≅ ℤ/2 的「阶 2」锚
conjZω-involutive : ∀ x → conjZω (conjZω x) ≡ x
conjZω-involutive (mkZω a b) = cong₂ mkZω comp1 comp2
  where
  comp1 : (a - b) - (- b) ≡ a
  comp1 = trans (+-assoc a (- b) (- (- b)))
           (trans (cong (λ t → a + t)
                    (trans (cong (λ s → (- b) + s) (neg-involutive b)) (+-inverseˡ b)))
                  (+-identityʳ a))

  comp2 : - (- b) ≡ b
  comp2 = neg-involutive b

-- | 加法同态: conj(x+y) = conj(x)+conj(y)
conjZω-add : ∀ x y → conjZω (addZω x y) ≡ addZω (conjZω x) (conjZω y)
conjZω-add (mkZω a b) (mkZω c d) = cong₂ mkZω comp1 comp2
  where
  comp1 : (a + c) - (b + d) ≡ (a - b) + (c - d)
  comp1 = begin
      (a + c) + (- (b + d))
    ≡⟨ cong (λ s → (a + c) + s) (neg-distrib-+ b d) ⟩
      (a + c) + ((- b) + (- d))
    ≡⟨ +-assoc a c ((- b) + (- d)) ⟩
      a + (c + ((- b) + (- d)))
    ≡⟨ cong (λ s → a + s) (sym (+-assoc c (- b) (- d))) ⟩
      a + ((c + (- b)) + (- d))
    ≡⟨ cong (λ t → a + (t + (- d))) (+-comm c (- b)) ⟩
      a + (((- b) + c) + (- d))
    ≡⟨ cong (λ s → a + s) (+-assoc (- b) c (- d)) ⟩
      a + ((- b) + (c + (- d)))
    ≡⟨ sym (+-assoc a (- b) (c + (- d))) ⟩
      (a + (- b)) + (c + (- d))
    ∎

  comp2 : - (b + d) ≡ (- b) + (- d)
  comp2 = neg-distrib-+ b d

-- | 乘法同态: conj(xy) = conj(x)·conj(y)
--   注意: Eisenstein.conjᵉ 用 (+ 0) − v 形、A4.conjZω 用 − v 形——分量级迁移时
--   以 +-identityˡ (−v) : (+ 0) + (−v) ≡ −v 归一两形，再经 §0 投影取得分量等式。
conjZω-mul : ∀ x y → conjZω (mulZω x y) ≡ mulZω (conjZω x) (conjZω y)
conjZω-mul (mkZω a b) (mkZω c d) = cong₂ mkZω comp1 comp2
  where
  comp1 : (a * c - b * d) - (a * d + b * c - b * d)
          ≡ (a - b) * (c - d) - (- b) * (- d)
  comp1 = trans (cong eisA (conjᵉ-mul (eis a b) (eis c d)))
           (cong₂ (λ s t → (a - b) * (c - d) - s * t)
                  (+-identityˡ (- b)) (+-identityˡ (- d)))

  comp2 : - (a * d + b * c - b * d)
          ≡ (a - b) * (- d) + (- b) * (c - d) - (- b) * (- d)
  comp2 = trans (sym (+-identityˡ (- (a * d + b * c - b * d))))
           (trans (cong eisB (conjᵉ-mul (eis a b) (eis c d)))
             (cong₂ (λ s t → (a - b) * s + t * (c - d) - t * s)
                    (+-identityˡ (- d)) (+-identityˡ (- b))))

-- | 与负元交换: conj(−x) = −conj(x)
conjZω-neg : ∀ x → conjZω (negZω x) ≡ negZω (conjZω x)
conjZω-neg (mkZω a b) = cong₂ mkZω comp1 refl
  where
  comp1 : (- a) - (- b) ≡ - (a - b)
  comp1 = trans (cong (λ s → (- a) + s) (neg-involutive b))
           (sym (trans (neg-distrib-+ a (- b)) (cong (λ s → (- a) + s) (neg-involutive b))))

--------------------------------------------------------------------------------
-- §8. 范数 N(a+bω) = a² − ab + b²（正定二次型; 判别式 −3）
--   载体为 A4Representation.Zω。乘性 N(xy)=N(x)N(y) 经 §0 桥迁移
--   Eisenstein.norm-mul（两载体范数公式逐字同形，定义层即可互换）。
--   整环性: xy=0 ⟹ N(x)N(y)=N(0)=0 ⟹ ℤ 中 N(x)=0 或 N(y)=0
--   ⟹ x=0 或 y=0（正定性用 ℕ 序，本模块立界，见 ZomegaMod3 头注）。
--------------------------------------------------------------------------------

normZω : Zω → ℤ
normZω (mkZω a b) = a * a - a * b + b * b

-- | x·conj(x) = (N(x), 0)——范数与共轭的连接
normZω-form : ∀ x → mulZω x (conjZω x) ≡ mkZω (normZω x) (+ 0)
normZω-form (mkZω a b) = cong₂ mkZω comp1 comp2
  where
  comp1 : a * (a - b) - b * (- b) ≡ a * a - a * b + b * b
  comp1 = begin
      a * (a - b) - b * (- b)
    ≡⟨ cong₂ _-_ (*-distribˡ-+ a a (- b)) (neg-*-r b b) ⟩
      (a * a + a * (- b)) - (- (b * b))
    ≡⟨ cong (λ t → (a * a + t) - (- (b * b))) (neg-*-r a b) ⟩
      (a * a + (- (a * b))) - (- (b * b))
    ≡⟨ cong (λ t → (a * a + (- (a * b))) + t) (neg-involutive (b * b)) ⟩
      (a * a + (- (a * b))) + b * b
    ∎

  comp2 : a * (- b) + b * (a - b) - b * (- b) ≡ + 0
  comp2 = begin
      a * (- b) + b * (a - b) - b * (- b)
    ≡⟨ cong (λ t → t + b * (a - b) - b * (- b)) (neg-*-r a b) ⟩
      (- (a * b)) + b * (a - b) - b * (- b)
    ≡⟨ cong (λ t → (- (a * b)) + t - b * (- b)) (*-distribˡ-+ b a (- b)) ⟩
      (- (a * b)) + (b * a + b * (- b)) - b * (- b)
    ≡⟨ cong (λ t → (- (a * b)) + (b * a + t) - t) (neg-*-r b b) ⟩
      (- (a * b)) + (b * a + (- (b * b))) - (- (b * b))
    ≡⟨ cong (λ t → (- (a * b)) + (b * a + (- (b * b))) + t) (neg-involutive (b * b)) ⟩
      (- (a * b)) + (b * a + (- (b * b))) + b * b
    ≡⟨ cong (λ t → t + b * b) (sym (+-assoc (- (a * b)) (b * a) (- (b * b)))) ⟩
      (((- (a * b)) + b * a) + (- (b * b))) + b * b
    ≡⟨ cong (λ t → (((- (a * b)) + t) + (- (b * b))) + b * b) (*-comm b a) ⟩
      (((- (a * b)) + a * b) + (- (b * b))) + b * b
    ≡⟨ cong (λ t → (t + (- (b * b))) + b * b) (+-inverseˡ (a * b)) ⟩
      (+ 0 + (- (b * b))) + b * b
    ≡⟨ cong (λ t → t + b * b) (+-identityˡ (- (b * b))) ⟩
      (- (b * b)) + b * b
    ≡⟨ +-inverseˡ (b * b) ⟩
      + 0
    ∎

-- | 范数乘性: N(xy) = N(x)·N(y)（迁移自 Eisenstein.norm-mul; 两式归约同形）
normZω-mul : ∀ x y → normZω (mulZω x y) ≡ normZω x * normZω y
normZω-mul (mkZω a b) (mkZω c d) = norm-mul (eis a b) (eis c d)

-- | 共轭保范数: N(conj x) = N(x)——Gal 共轭保持二次型 Q（判别式 −3 的不变性）。
--   路线: N(conj x) 是 conj²x·conj x 的 a-分量（normZω-form @ conj x），
--   conj² ≡ id 后即 x·conj x 的 a-分量 = N(x)。
normZω-conj : ∀ x → normZω (conjZω x) ≡ normZω x
normZω-conj x =
  trans (sym (cong Zω.a (normZω-form (conjZω x))))
    (trans (cong (λ t → Zω.a (mulZω (conjZω x) t)) (conjZω-involutive x))
      (trans (cong Zω.a (mulZω-comm (conjZω x) x))
             (cong Zω.a (normZω-form x))))

--------------------------------------------------------------------------------
-- §9. 单位群 Z[ω]^× = {±1, ±ω, ±ω²} ≅ C₆
--   ±ω 是 6 次单位根: ω³=1, (−ω)³=−1, (±ω)⁶=1——三个阶的第三层。
--   生成元 g = 1+ω = −ω²，g⁰..g⁶ 遍历全群（与 Eisenstein.unitGen 同源迁移）。
--   命名带 uZω 前缀: 与 Eisenstein 的 unit1/unitω 等全局不撞名（重名门禁）。
--------------------------------------------------------------------------------

uZω-one    : Zω;  uZω-one    = oneZω
uZω-mone   : Zω;  uZω-mone   = negZω oneZω
uZω-omega  : Zω;  uZω-omega  = ω
uZω-omega2 : Zω;  uZω-omega2 = ω²
uZω-momega : Zω;  uZω-momega = negZω ω
uZω-momega2 : Zω;  uZω-momega2 = negZω ω²

-- 逆元配对（6 对 12 元全枚举, 全 refl）
uZω-inv-one    : mulZω uZω-one     uZω-one      ≡ uZω-one;    uZω-inv-one    = refl
uZω-inv-mone   : mulZω uZω-mone    uZω-mone     ≡ uZω-one;    uZω-inv-mone   = refl
uZω-inv-omega  : mulZω uZω-omega   uZω-omega2   ≡ uZω-one;    uZω-inv-omega  = refl
uZω-inv-omega2 : mulZω uZω-omega2  uZω-omega    ≡ uZω-one;    uZω-inv-omega2 = refl
uZω-inv-momega : mulZω uZω-momega  uZω-momega2  ≡ uZω-one;    uZω-inv-momega = refl
uZω-inv-momega2 : mulZω uZω-momega2 uZω-momega   ≡ uZω-one;    uZω-inv-momega2 = refl

-- 单位范数均为 1（N(u)=1 ⟺ u ∈ Z[ω]^× 的「⟸」侧）
uZω-norm-one    : normZω uZω-one     ≡ + 1;  uZω-norm-one    = refl
uZω-norm-mone   : normZω uZω-mone    ≡ + 1;  uZω-norm-mone   = refl
uZω-norm-omega  : normZω uZω-omega   ≡ + 1;  uZω-norm-omega  = refl
uZω-norm-omega2 : normZω uZω-omega2  ≡ + 1;  uZω-norm-omega2 = refl
uZω-norm-momega : normZω uZω-momega  ≡ + 1;  uZω-norm-momega = refl
uZω-norm-momega2 : normZω uZω-momega2 ≡ + 1;  uZω-norm-momega2 = refl

-- 生成元 g = 1+ω = −ω² 的 C₆ 循环: 1 → 1+ω → ω → −1 → ω² → −ω → 1
uZωGen : Zω
uZωGen = addZω oneZω ω

uZωGen-pow-0 : oneZω ≡ uZω-one;                                        uZωGen-pow-0 = refl
uZωGen-pow-1 : uZωGen ≡ uZω-momega2;                                   uZωGen-pow-1 = refl
uZωGen-pow-2 : mulZω uZωGen uZωGen ≡ uZω-omega;                        uZωGen-pow-2 = refl
uZωGen-pow-3 : mulZω (mulZω uZωGen uZωGen) uZωGen ≡ uZω-mone;          uZωGen-pow-3 = refl
uZωGen-pow-4 : mulZω (mulZω (mulZω uZωGen uZωGen) uZωGen) uZωGen ≡ uZω-omega2;  uZωGen-pow-4 = refl
uZωGen-pow-5 : mulZω (mulZω (mulZω (mulZω uZωGen uZωGen) uZωGen) uZωGen) uZωGen ≡ uZω-momega;  uZωGen-pow-5 = refl
uZωGen-pow-6 : mulZω (mulZω (mulZω (mulZω (mulZω uZωGen uZωGen) uZωGen) uZωGen) uZωGen) uZωGen ≡ uZω-one;  uZωGen-pow-6 = refl

-- 0 postulate.
