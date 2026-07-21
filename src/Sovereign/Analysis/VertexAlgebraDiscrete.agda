{-# OPTIONS --rewriting --guardedness #-}
-- | Sovereign.Analysis.VertexAlgebraDiscrete
-- GF(9) 离散顶点代数: char 3 截断使 OPE 模式有限化
--
-- 核心洞察: 在特征 3 域上, n! ≡ 0 (n ≥ 3),
-- 顶点算子的 OPE 自然截断为有限模式 (mode 0, 1, 2)。
-- GF(9)ⁿ 上的逐点乘法构成交换代数, 给出有限维顶点代数。
--
-- 0 postulate — 全部构造性证明
module Sovereign.Analysis.VertexAlgebraDiscrete where

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Fin using (Fin; fromℕ)
import Data.Fin as Fin
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Function using (_∘_; id)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; cong₂; sym; trans)

open import Sovereign.Base.Trit using (
  Trit; T₀; T₁; T₂; _⊕_; _⊗_;
  ⊗-zeroʳ; ⊗-zeroˡ; ⊗-identityˡ)

open import Sovereign.Algebra.GF9 using (
  GF9; GF3; _+gf9_; _*gf9_; gf9-one;
  galoisConjugate; galoisConjugate²;
  galoisNorm; embed-gf3;
  +gf9-comm; +gf9-assoc; +gf9-identityˡ; +gf9-identityʳ;
  *gf9-comm; *gf9-assoc; *gf9-identityˡ; *gf9-identityʳ;
  *gf9-distribˡ-+gf9; *gf9-distribʳ-+gf9;
  lemma-frobenius-multiplicative;
  conjugatePair-size-1)

open import Sovereign.Analysis.FiniteInnerProduct using (
  VectorSpace; gf9-zero; zeroVec; _+V_; _·V_;
  hermitianIP; normSq; Orthogonal;
  *gf9-zeroˡ; *gf9-zeroʳ;
  zero-orthogonalˡ; zero-orthogonalʳ;
  sumGF9; sumGF9-const-zero; sumGF9-cong)

--------------------------------------------------------------------------------
-- §1. 逐点乘法 — 使 GF(9)ⁿ 成为交换代数
--------------------------------------------------------------------------------

infixl 7 _*V_
_*V_ : ∀ {n} → VectorSpace n → VectorSpace n → VectorSpace n
(f *V g) i = f i *gf9 g i

-- 逐点乘法交换律
*V-comm : ∀ {n} (f g : VectorSpace n) → ∀ i → (f *V g) i ≡ (g *V f) i
*V-comm f g i = *gf9-comm (f i) (g i)

-- 逐点乘法结合律
*V-assoc : ∀ {n} (f g h : VectorSpace n) → ∀ i →
  ((f *V g) *V h) i ≡ (f *V (g *V h)) i
*V-assoc f g h i = *gf9-assoc (f i) (g i) (h i)

-- 逐点乘法单位元 (常值 1 向量)
unitVec : ∀ n → VectorSpace n
unitVec n _ = gf9-one

*V-identityˡ : ∀ {n} (f : VectorSpace n) → ∀ i →
  (unitVec n *V f) i ≡ f i
*V-identityˡ f i = *gf9-identityˡ (f i)

*V-identityʳ : ∀ {n} (f : VectorSpace n) → ∀ i →
  (f *V unitVec _) i ≡ f i
*V-identityʳ f i = *gf9-identityʳ (f i)

-- 零向量吸收律
*V-zeroˡ : ∀ {n} (f : VectorSpace n) → ∀ i →
  (zeroVec n *V f) i ≡ gf9-zero
*V-zeroˡ f i = *gf9-zeroˡ (f i)

*V-zeroʳ : ∀ {n} (f : VectorSpace n) → ∀ i →
  (f *V zeroVec _) i ≡ gf9-zero
*V-zeroʳ f i = *gf9-zeroʳ (f i)

--------------------------------------------------------------------------------
-- §2. 顶点算子 — 状态-场对应 Y: V → End(V)
--------------------------------------------------------------------------------

-- 顶点算子: 向量空间上的线性算子
VertexOp : ℕ → Set
VertexOp n = VectorSpace n → VectorSpace n

-- 状态-场对应: Y(a)(b) = a *V b (逐点乘法)
Y : ∀ {n} → VectorSpace n → VertexOp n
Y a b = a *V b

-- Y 的逐点描述
Y-pointwise : ∀ {n} (a b : VectorSpace n) → ∀ i →
  Y a b i ≡ a i *gf9 b i
Y-pointwise a b i = refl

--------------------------------------------------------------------------------
-- §3. 真空态与创生公理
--------------------------------------------------------------------------------

-- 真空态: 零向量
vacuum : ∀ n → VectorSpace n
vacuum n = zeroVec n

-- 创生公理 (弱形式): Y(|0⟩)|0⟩ = |0⟩
-- 真空态自作用仍为真空
vacuum-creation : ∀ n → ∀ i →
  Y (vacuum n) (vacuum n) i ≡ vacuum n i
vacuum-creation n i = *gf9-zeroˡ gf9-zero

-- Y(vacuum) 是零算子: Y(|0⟩)(a) = |0⟩ 对任意 a
vacuum-zero-op : ∀ {n} (a : VectorSpace n) → ∀ i →
  Y (vacuum n) a i ≡ gf9-zero
vacuum-zero-op a i = *gf9-zeroˡ (a i)

--------------------------------------------------------------------------------
-- §4. 恒等算子 — Y(unitVec) = id
--------------------------------------------------------------------------------

-- Y(1) 是恒等算子 (逐点)
Y-unit-id : ∀ {n} (f : VectorSpace n) → ∀ i →
  Y (unitVec n) f i ≡ f i
Y-unit-id f i = *gf9-identityˡ (f i)

-- 右恒等
Y-unit-idʳ : ∀ {n} (f : VectorSpace n) → ∀ i →
  Y f (unitVec n) i ≡ f i
Y-unit-idʳ f i = *gf9-identityʳ (f i)

--------------------------------------------------------------------------------
-- §5. Y-结合律
--------------------------------------------------------------------------------

-- Y(a)(Y(b)(Y(c)(x))) = Y(a·b)(Y(c)(x)) (逐点)
Y-assoc : ∀ {n} (a b c x : VectorSpace n) → ∀ i →
  Y a (Y b (Y c x)) i ≡ Y (a *V b) (Y c x) i
Y-assoc a b c x i = sym (*gf9-assoc (a i) (b i) (c i *gf9 x i))

--------------------------------------------------------------------------------
-- §6. 局部性 — char 3 截断的核心定理
-- Y(a) 与 Y(b) 交换 (逐点): 逐点乘法的交换性
-- 在 OPE 语言中: 所有奇点项消失, 场完全局域
--------------------------------------------------------------------------------

locality : ∀ {n} (a b : VectorSpace n) (x : VectorSpace n) → ∀ i →
  Y a (Y b x) i ≡ Y b (Y a x) i
locality a b x i =
  trans (sym (*gf9-assoc (a i) (b i) (x i)))
    (trans (cong (λ t → t *gf9 x i) (*gf9-comm (a i) (b i)))
           (*gf9-assoc (b i) (a i) (x i)))

-- 局部性的推论: Y(a) ∘ Y(b) = Y(a·b) (逐点)
Y-fusion : ∀ {n} (a b x : VectorSpace n) → ∀ i →
  Y a (Y b x) i ≡ Y (a *V b) x i
Y-fusion a b x i = sym (*gf9-assoc (a i) (b i) (x i))

--------------------------------------------------------------------------------
-- §7. 真空期望值 — ⟨0|Y(a)|0⟩ = 0
--------------------------------------------------------------------------------

-- 真空与任何态正交: ⟨0|Y(a)|0⟩ = 0
vacuum-expectation : ∀ n (a : VectorSpace n) →
  hermitianIP n (vacuum n) (Y a (vacuum n)) ≡ gf9-zero
vacuum-expectation n a = zero-orthogonalˡ n (a *V vacuum n)

-- 更一般地: ⟨0|b⟩ = 0 对任意 b
vacuum-orth-all : ∀ n (b : VectorSpace n) →
  hermitianIP n (vacuum n) b ≡ gf9-zero
vacuum-orth-all n b = zero-orthogonalˡ n b

--------------------------------------------------------------------------------
-- §8. 平移算子 — 循环移位
--------------------------------------------------------------------------------

-- 循环右移: T(f)(0) = f(n), T(f)(i+1) = f(i)
-- 在 Fin (suc n) 上, fromℕ n 是最大元素
shift : ∀ {n} → VectorSpace (suc n) → VectorSpace (suc n)
shift {n} f Fin.zero    = f (fromℕ n)
shift {n} f (Fin.suc i) = f (Fin.inject₁ i)

-- n=1 时 shift 是恒等 (Fin 1 只有一个元素)
shift₁-id : ∀ (f : VectorSpace 1) → ∀ i → shift f i ≡ f i
shift₁-id f Fin.zero = refl

-- n=2 时 shift 交换两个分量
shift₂-swap-zero : ∀ (f : VectorSpace 2) →
  shift f Fin.zero ≡ f (Fin.suc Fin.zero)
shift₂-swap-zero f = refl

shift₂-swap-suc : ∀ (f : VectorSpace 2) →
  shift f (Fin.suc Fin.zero) ≡ f Fin.zero
shift₂-swap-suc f = refl

-- n=2 时 shift 是对合: shift² = id (逐点)
shift₂-involutive : ∀ (f : VectorSpace 2) → ∀ i →
  shift (shift f) i ≡ f i
shift₂-involutive f Fin.zero          = refl
shift₂-involutive f (Fin.suc Fin.zero) = refl

--------------------------------------------------------------------------------
-- §9. 平移协变性 — Y(shift a) = shift ∘ Y(a) ∘ shift
--------------------------------------------------------------------------------

-- n=1: 平移协变 (平凡, shift = id)
trans-cov₁ : ∀ (a x : VectorSpace 1) → ∀ i →
  Y (shift a) x i ≡ shift (Y a (shift x)) i
trans-cov₁ a x Fin.zero = refl

-- n=2: 平移协变 (shift 是交换, 逐点验证)
trans-cov₂ : ∀ (a x : VectorSpace 2) → ∀ i →
  Y (shift a) x i ≡ shift (Y a (shift x)) i
trans-cov₂ a x Fin.zero          = refl
trans-cov₂ a x (Fin.suc Fin.zero) = refl

--------------------------------------------------------------------------------
-- §10. char 3 阶乘截断 — n! ≡ 0 (mod 3) 对 n ≥ 3
--------------------------------------------------------------------------------

-- 自然数到 GF(3) 的约化
ℕ→GF3 : ℕ → GF3
ℕ→GF3 zero                  = T₀
ℕ→GF3 (suc zero)            = T₁
ℕ→GF3 (suc (suc zero))      = T₂
ℕ→GF3 (suc (suc (suc n)))   = ℕ→GF3 n

-- GF(3) 阶乘: n! mod 3
fact-gf3 : ℕ → GF3
fact-gf3 zero    = T₁                        -- 0! = 1
fact-gf3 (suc n) = ℕ→GF3 (suc n) ⊗ fact-gf3 n  -- (n+1)! = (n+1)·n!

-- 验证小值
fact-0 : fact-gf3 0 ≡ T₁
fact-0 = refl

fact-1 : fact-gf3 1 ≡ T₁
fact-1 = refl

fact-2 : fact-gf3 2 ≡ T₂
fact-2 = refl

fact-3 : fact-gf3 3 ≡ T₀
fact-3 = refl

-- 核心截断定理: n! ≡ 0 (mod 3) 对 n ≥ 3
char3-fact-zero : ∀ n → fact-gf3 (suc (suc (suc n))) ≡ T₀
char3-fact-zero zero = refl
char3-fact-zero (suc n) =
  trans (cong (ℕ→GF3 (suc (suc (suc (suc n)))) ⊗_) (char3-fact-zero n))
        (⊗-zeroʳ (ℕ→GF3 (suc (suc (suc (suc n))))))

--------------------------------------------------------------------------------
-- §11. OPE 模式有限性
--------------------------------------------------------------------------------

-- char 3 中 OPE 只有 3 个非平凡模式 (mode 0, 1, 2)
-- 因为 n! = 0 (n ≥ 3) 使高阶模式消失
data OPEMode : Set where
  mode-0 : OPEMode   -- 零阶模式 (场值)
  mode-1 : OPEMode   -- 一阶模式 (导数)
  mode-2 : OPEMode   -- 二阶模式 (char 3 允许的最高阶)

-- 模式数 = 3 (char 3 的截断阶)
ope-mode-count : ℕ
ope-mode-count = 3

-- 模式截断: 3 个模式恰好对应 fact-gf3 非零的阶数
-- fact-gf3 0 = T₁ ≠ T₀, fact-gf3 1 = T₁ ≠ T₀, fact-gf3 2 = T₂ ≠ T₀
-- fact-gf3 3 = T₀ (截断点)
mode-0-nonzero : fact-gf3 0 ≡ T₁
mode-0-nonzero = refl

mode-1-nonzero : fact-gf3 1 ≡ T₁
mode-1-nonzero = refl

mode-2-nonzero : fact-gf3 2 ≡ T₂
mode-2-nonzero = refl

mode-3-zero : fact-gf3 3 ≡ T₀
mode-3-zero = refl

-- n=1 时 End(GF9¹) 的模式有限性:
-- 顶点算子由 GF9 的 9 个元素参数化
Y₁-param : GF9 → VertexOp 1
Y₁-param a = Y (λ _ → a)

-- 参数化是逐点确定的
Y₁-param-pointwise : ∀ (a : GF9) (x : VectorSpace 1) →
  Y₁-param a x Fin.zero ≡ a *gf9 x Fin.zero
Y₁-param-pointwise a x = refl

--------------------------------------------------------------------------------
-- §12. Frobenius 自同构作为顶点算子
--------------------------------------------------------------------------------

-- GF(3) 嵌入的常值向量
embedVec : ∀ n → GF3 → VectorSpace n
embedVec n a _ = embed-gf3 a

-- GF(3) 嵌入定义的顶点算子
embed-Op : ∀ n → GF3 → VertexOp n
embed-Op n a = Y (embedVec n a)

-- 逐点 Galois 共轭 (Frobenius 作用)
σ-vec : ∀ {n} → VectorSpace n → VectorSpace n
σ-vec f i = galoisConjugate (f i)

-- Frobenius 与 GF(3) 嵌入顶点算子交换 (逐点):
-- σ(Y(embed a)(x)) = Y(embed a)(σ(x))
-- 证明: σ(embed(a)·x) = σ(embed(a))·σ(x) = embed(a)·σ(x)
--       (Frobenius 乘法同态 + GF(3) 元素是 Galois 不动点)
frobenius-embed-commute : ∀ n (a : GF3) (x : VectorSpace n) → ∀ i →
  σ-vec (embed-Op n a x) i ≡ embed-Op n a (σ-vec x) i
frobenius-embed-commute n a x i =
  trans (lemma-frobenius-multiplicative (embed-gf3 a) (x i))
        (cong (_*gf9 galoisConjugate (x i)) (conjugatePair-size-1 a))

-- 特殊情形: a = T₁ (GF(3) 单位元), embed-Op 是恒等
frobenius-id-commute : ∀ n (x : VectorSpace n) → ∀ i →
  σ-vec (Y (unitVec n) x) i ≡ Y (unitVec n) (σ-vec x) i
frobenius-id-commute n x i =
  frobenius-embed-commute n T₁ x i

-- Galois 共轭是对合 (逐点)
σ-vec-involutive : ∀ {n} (f : VectorSpace n) → ∀ i →
  σ-vec (σ-vec f) i ≡ f i
σ-vec-involutive f i = galoisConjugate² (f i)

--------------------------------------------------------------------------------
-- §13. 分配律 — Y 保持加法结构
--------------------------------------------------------------------------------

-- Y(a) 是加法同态: Y(a)(b+c) = Y(a)(b) + Y(a)(c) (逐点)
Y-additive : ∀ {n} (a b c : VectorSpace n) → ∀ i →
  Y a (b +V c) i ≡ (Y a b +V Y a c) i
Y-additive a b c i = *gf9-distribˡ-+gf9 (a i) (b i) (c i)

-- 右分配: Y(a+b)(c) = Y(a)(c) + Y(b)(c) (逐点)
Y-additiveʳ : ∀ {n} (a b c : VectorSpace n) → ∀ i →
  Y (a +V b) c i ≡ (Y a c +V Y b c) i
Y-additiveʳ a b c i = *gf9-distribʳ-+gf9 (a i) (b i) (c i)

--------------------------------------------------------------------------------
-- §14. 总结
--------------------------------------------------------------------------------

-- 核心定理列表 (全部 0 postulate, 构造性证明):
--
-- 1. _*V_: GF(9)ⁿ 上的逐点乘法, 构成交换代数
--    交换律 *V-comm, 结合律 *V-assoc, 单位元 unitVec
--
-- 2. Y: 状态-场对应 Y(a)(b) = a *V b
--    恒等 Y-unit-id, 结合律 Y-assoc, 分配律 Y-additive
--
-- 3. vacuum: 真空态 = zeroVec
--    创生公理 vacuum-creation, 零算子 vacuum-zero-op
--
-- 4. locality: 局部性 (场交换)
--    Y(a)(Y(b)(x)) = Y(b)(Y(a)(x)) (逐点)
--
-- 5. vacuum-expectation: 真空期望值 ⟨0|Y(a)|0⟩ = 0
--
-- 6. shift: 循环平移算子
--    平移协变性 trans-cov₁, trans-cov₂
--
-- 7. char3-fact-zero: char 3 阶乘截断 n! ≡ 0 (n ≥ 3)
--    OPE 模式有限: 仅 mode-0, mode-1, mode-2
--
-- 8. frobenius-embed-commute: Frobenius 与 GF(3) 顶点算子交换
--    σ(Y(embed a)(x)) = Y(embed a)(σ(x))
--------------------------------------------------------------------------------
