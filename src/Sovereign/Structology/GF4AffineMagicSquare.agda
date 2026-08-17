{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Structology.GF4AffineMagicSquare
-- 完全幻方五定理: GF(4) 仿射正交拉丁方对 (0 postulate)
--
-- 【幻方三层定义】(会话裁定 #10)
--   第1层 传统数字幻方: 行/列/对角和相等 (静态验算) — MagicSquareM4.agda 实例
--   第2层 卢先生幻方: 矢量方向动态系统 — 命名层, 不进入证明链
--   第3层 框架可证幻方: 正交拉丁方对叠加 + 系数不对称 a≠b (构造推导) — 本模块
--
-- 【定理序列】(会话裁定 #9, 证明层/命名层严格分离)
--   T1    正交性: 16 对互异 (承 OrthogonalLatinSquare.orthogonal)
--   T2′   转置恒等式: L2 ≡ L1ᵀ (主对角反射 — 命名层挂 Slot 4↔5 手征交换)
--   T2″   系数 σ-像 (实例级): σ4(α)=α+1, σ4(α+1)=α — 命名层挂 Slot 6 内部规范相位
--         诚实边界: 常数项 c=2 未共轭 (σ4(2)=3≠2), 不可声称 L2 = σ(L1)
--   T-sym 统一判据: det[[a,b],[b,a]] = a²⊕b² = (a⊕b)² (特征2), 非零 ⟺ a≠b
--         正交性条件与对角 transversal 条件统一为同一判据
--   T3    完全幻方: M0 = 4·L1+L2 十线全 ≡ 30
--
-- 【命名层锚点】(保留, 不进证明链): 顺/逆手征共轭 ↔ 转置 L1↔L2;
--   σ 系数作用与转置在 GF(4) {2,3} 轨道数值重合, 但分属不同槽位, 不可合并声明。
--
-- 【负结果】经典 Dürer M₄ 不是正交拉丁方叠加 (自然基4编码高位 [3,0,0,3] 非拉丁),
--   且库 M4 ∉ Dürer 的 D4 轨道 — 数值验证:
--   docs/cross-level/gf4-affine-magic-square-verification.md
--   Rust: sov-math/sov-validation/src/gf4_magic.rs

module Sovereign.Structology.GF4AffineMagicSquare where

open import Data.Nat using (ℕ; _+_; _*_)
open import Data.Fin using (Fin; zero; suc)
open import Data.Vec using (Vec; []; _∷_; zipWith)
open import Data.Bool using (Bool; true)
open import Data.Product using (_×_; _,_)
open import Data.Empty using (⊥-elim)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)

open import Sovereign.Structology.GF4
  using (GF4; g0; g1; ga; gb; add4; mul4)
open import Sovereign.Structology.OrthogonalLatinSquare
  using (L1; L2; super0; allDistinct; orthogonal; sum4; rowSum; column;
         diagSum; antidiagSum)

--------------------------------------------------------------------------------
-- §1. T1 正交性: 16 对互异
--------------------------------------------------------------------------------

T1 : allDistinct super0 ≡ true
T1 = orthogonal

--------------------------------------------------------------------------------
-- §2. T2′ 转置恒等式: L2 ≡ L1ᵀ (主对角反射)
--------------------------------------------------------------------------------

transpose4 : Vec (Vec ℕ 4) 4 → Vec (Vec ℕ 4) 4
transpose4 ((a ∷ b ∷ c ∷ d ∷ []) ∷ (e ∷ f ∷ g ∷ h ∷ []) ∷
            (i ∷ j ∷ k ∷ l ∷ []) ∷ (m ∷ n ∷ o ∷ p ∷ []) ∷ []) =
  (a ∷ e ∷ i ∷ m ∷ []) ∷ (b ∷ f ∷ j ∷ n ∷ []) ∷
  (c ∷ g ∷ k ∷ o ∷ []) ∷ (d ∷ h ∷ l ∷ p ∷ []) ∷ []

T2′ : transpose4 L1 ≡ L2
T2′ = refl

--------------------------------------------------------------------------------
-- §3. T2″ 系数 σ-像 (实例级) + 诚实边界
--------------------------------------------------------------------------------

-- GF(4) Frobenius σ: x ↦ x² (0↦0, 1↦1, α↦α+1, α+1↦α)
σ4 : GF4 → GF4
σ4 g0 = g0
σ4 g1 = g1
σ4 ga = gb
σ4 gb = ga

-- 线性系数 (2,3)=(ga,gb) 的 σ-像 = (3,2)=(gb,ga) = L2 的线性系数
T2″ : σ4 ga ≡ gb × σ4 gb ≡ ga
T2″ = refl , refl

-- 诚实边界: 常数项 c = 2 = ga 不被共轭 (σ4(ga)=gb≠ga)
-- ⟹ 只能证「线性部分 σ-像」, 不可声称 L2 = σ(L1) 整体
constant-not-conjugated : σ4 ga ≢ ga
constant-not-conjugated ()

--------------------------------------------------------------------------------
-- §4. T-sym 统一判据: 正交性 ⟺ 系数不对称 a≠b
--------------------------------------------------------------------------------

-- 特征 2 Freshman's Dream: (a⊕b)² = a²⊕b² (16 穷举 refl)
T-sym-square : ∀ a b → mul4 (add4 a b) (add4 a b) ≡ add4 (mul4 a a) (mul4 b b)
T-sym-square g0 g0 = refl
T-sym-square g0 g1 = refl
T-sym-square g0 ga = refl
T-sym-square g0 gb = refl
T-sym-square g1 g0 = refl
T-sym-square g1 g1 = refl
T-sym-square g1 ga = refl
T-sym-square g1 gb = refl
T-sym-square ga g0 = refl
T-sym-square ga g1 = refl
T-sym-square ga ga = refl
T-sym-square ga gb = refl
T-sym-square gb g0 = refl
T-sym-square gb g1 = refl
T-sym-square gb ga = refl
T-sym-square gb gb = refl

-- 特征 2: a⊕a = 0
add4-self : ∀ a → add4 a a ≡ g0
add4-self g0 = refl
add4-self g1 = refl
add4-self ga = refl
add4-self gb = refl

-- a = b ⟹ det[[a,b],[b,a]] = a²⊕b² = 0 (对角退化)
det-zero-eq : ∀ a → mul4 (add4 a a) (add4 a a) ≡ g0
det-zero-eq a rewrite add4-self a = refl

-- a ≠ b ⟹ det = (a⊕b)² ≠ 0 (对角 transversal + 正交)
det-neq-zero : ∀ a b → a ≢ b → mul4 (add4 a b) (add4 a b) ≢ g0
det-neq-zero g0 g0 ne = ⊥-elim (ne refl)
det-neq-zero g0 g1 _ = λ()
det-neq-zero g0 ga _ = λ()
det-neq-zero g0 gb _ = λ()
det-neq-zero g1 g0 _ = λ()
det-neq-zero g1 g1 ne = ⊥-elim (ne refl)
det-neq-zero g1 ga _ = λ()
det-neq-zero g1 gb _ = λ()
det-neq-zero ga g0 _ = λ()
det-neq-zero ga g1 _ = λ()
det-neq-zero ga ga ne = ⊥-elim (ne refl)
det-neq-zero ga gb _ = λ()
det-neq-zero gb g0 _ = λ()
det-neq-zero gb g1 _ = λ()
det-neq-zero gb ga _ = λ()
det-neq-zero gb gb ne = ⊥-elim (ne refl)

-- T-sym 统一定理: 行列式判据 = 平方判据, 非零 ⟺ a≠b
T-sym : (∀ a b → mul4 (add4 a b) (add4 a b) ≡ add4 (mul4 a a) (mul4 b b))
      × (∀ a b → a ≢ b → mul4 (add4 a b) (add4 a b) ≢ g0)
      × (∀ a → mul4 (add4 a a) (add4 a a) ≡ g0)
T-sym = T-sym-square , det-neq-zero , det-zero-eq

-- 本实例: det[[2,3],[3,2]] = (ga⊕gb)² = g1² = g1 ≠ 0
det-instance-nonzero : mul4 (add4 ga gb) (add4 ga gb) ≢ g0
det-instance-nonzero = λ()

--------------------------------------------------------------------------------
-- §5. T3 完全幻方: M0 = 4·L1 + L2 十线全 ≡ 30
--------------------------------------------------------------------------------

M0 : Vec (Vec ℕ 4) 4
M0 = zipWith (zipWith (λ a b → 4 * a + b)) L1 L2

T3 : (rowSum M0 zero ≡ 30 × rowSum M0 (suc zero) ≡ 30 ×
      rowSum M0 (suc (suc zero)) ≡ 30 × rowSum M0 (suc (suc (suc zero))) ≡ 30)
   × (sum4 (column M0 zero) ≡ 30 × sum4 (column M0 (suc zero)) ≡ 30 ×
      sum4 (column M0 (suc (suc zero))) ≡ 30 × sum4 (column M0 (suc (suc (suc zero)))) ≡ 30)
   × (diagSum M0 ≡ 30 × antidiagSum M0 ≡ 30)
T3 = (refl , refl , refl , refl) , (refl , refl , refl , refl) , (refl , refl)

-- 0 postulate.
