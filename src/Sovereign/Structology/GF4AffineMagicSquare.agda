{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Structology.GF4AffineMagicSquare
-- 完全幻方五定理: GF(4) 仿射正交拉丁方对 (0 postulate)
--
-- 【幻方定义: 一本体 + 两投影】(会话裁定 #11, 修正此前「三层并列」表述)
--   本体: 幻方 = 矢量方向动态系统 (卢先生定义) — 环上 n 个矢量方向同时变化,
--     套环同步演化, 解 = 闭合约束下的全部轨线。没有静态几何。
--   投影 1 (本模块): 框架可证定义 = 本体在 GF(4) 基座上的显式实现, 仍是动态的:
--     L1 = 2i+3j+2, L2 = 3i+2j+2 是两个环的动态法则;
--     正交性 = 两环同时转, 16 组合各出现一次; 完全闭合 = 十线等和不变量。
--   投影 2: 传统数字幻方 = 动态过程的静态投影切片 (电影的一帧),
--     只保留「十线和相等」不变量 — MagicSquareM4.agda 实例, 非并列层。
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
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; cong; cong₂; module ≡-Reasoning)
open ≡-Reasoning

open import Sovereign.Structology.GF4
  using (GF4; g0; g1; ga; gb; add4; mul4;
         add4-comm; add4-assoc; distrib-left; distrib-right)
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

--------------------------------------------------------------------------------
-- §6. 动态矢量轨线生成法则 (观测层, 会话裁定 #14)
--   环同步转动 (i,j) ↦ (i⊕t, j⊕t) 经仿射映射投影为值环上步长 (a⊕b) 的平移:
--   L(i⊕t, j⊕t) ≡ L(i,j) ⊕ (a⊕b)·t, 其中 L(i,j) = a·i ⊕ b·j ⊕ c
--   闭合判据: a⊕b ≠ 0 ⟹ 轨线覆盖全部值 (对角 transversal, 完全幻方)
--   基座层对应: SP2Ternary.agda (+1 归零周期 3 / ×2 乌比斯环周期 2)
--------------------------------------------------------------------------------

-- 重组引理: ((a⊕b) ⊕ (c⊕d)) ⊕ e ≡ ((a⊕c) ⊕ e) ⊕ (b⊕d)
add4-regroup : ∀ a b c d e →
  add4 (add4 (add4 a b) (add4 c d)) e
  ≡ add4 (add4 (add4 a c) e) (add4 b d)
add4-regroup a b c d e = begin
  add4 (add4 (add4 a b) (add4 c d)) e
    ≡⟨ add4-assoc (add4 a b) (add4 c d) e ⟩
  add4 (add4 a b) (add4 (add4 c d) e)
    ≡⟨ cong (add4 (add4 a b)) (add4-assoc c d e) ⟩
  add4 (add4 a b) (add4 c (add4 d e))
    ≡⟨ add4-assoc a b (add4 c (add4 d e)) ⟩
  add4 a (add4 b (add4 c (add4 d e)))
    ≡⟨ cong (add4 a) (sym (add4-assoc b c (add4 d e))) ⟩
  add4 a (add4 (add4 b c) (add4 d e))
    ≡⟨ cong (λ u → add4 a (add4 u (add4 d e))) (add4-comm b c) ⟩
  add4 a (add4 (add4 c b) (add4 d e))
    ≡⟨ cong (add4 a) (add4-assoc c b (add4 d e)) ⟩
  add4 a (add4 c (add4 b (add4 d e)))
    ≡⟨ cong (λ u → add4 a (add4 c u)) (sym (add4-assoc b d e)) ⟩
  add4 a (add4 c (add4 (add4 b d) e))
    ≡⟨ sym (add4-assoc a c (add4 (add4 b d) e)) ⟩
  add4 (add4 a c) (add4 (add4 b d) e)
    ≡⟨ cong (add4 (add4 a c)) (add4-comm (add4 b d) e) ⟩
  add4 (add4 a c) (add4 e (add4 b d))
    ≡⟨ sym (add4-assoc (add4 a c) e (add4 b d)) ⟩
  add4 (add4 (add4 a c) e) (add4 b d) ∎

-- 仿射轨线一般法则: L(i⊕t,j⊕t) ≡ L(i,j) ⊕ (a⊕b)·t
affine-trajectory : ∀ a b c i j t →
  add4 (add4 (mul4 a (add4 i t)) (mul4 b (add4 j t))) c
  ≡ add4 (add4 (add4 (mul4 a i) (mul4 b j)) c) (mul4 (add4 a b) t)
affine-trajectory a b c i j t = begin
  add4 (add4 (mul4 a (add4 i t)) (mul4 b (add4 j t))) c
    ≡⟨ cong (λ u → add4 u c)
            (cong₂ add4 (distrib-left a i t) (distrib-left b j t)) ⟩
  add4 (add4 (add4 (mul4 a i) (mul4 a t)) (add4 (mul4 b j) (mul4 b t))) c
    ≡⟨ add4-regroup (mul4 a i) (mul4 a t) (mul4 b j) (mul4 b t) c ⟩
  add4 (add4 (add4 (mul4 a i) (mul4 b j)) c) (add4 (mul4 a t) (mul4 b t))
    ≡⟨ cong (add4 (add4 (add4 (mul4 a i) (mul4 b j)) c))
            (sym (distrib-right a b t)) ⟩
  add4 (add4 (add4 (mul4 a i) (mul4 b j)) c) (mul4 (add4 a b) t) ∎

-- L1 = 2i⊕3j⊕2 的轨线: 步长 ga⊕gb = g1
trajectory-L1 : ∀ i j t →
  add4 (add4 (mul4 ga (add4 i t)) (mul4 gb (add4 j t))) ga
  ≡ add4 (add4 (add4 (mul4 ga i) (mul4 gb j)) ga) (mul4 (add4 ga gb) t)
trajectory-L1 = affine-trajectory ga gb ga

-- L2 = 3i⊕2j⊕2 的轨线: 步长 gb⊕ga = g1
trajectory-L2 : ∀ i j t →
  add4 (add4 (mul4 gb (add4 i t)) (mul4 ga (add4 j t))) ga
  ≡ add4 (add4 (add4 (mul4 gb i) (mul4 ga j)) ga) (mul4 (add4 gb ga) t)
trajectory-L2 = affine-trajectory gb ga ga

-- 步长值: ga⊕gb = g1 ≠ g0 ⟹ 4-循环覆盖全部值 (闭合判据 a⊕b≠0 的实例)
trajectory-step : add4 ga gb ≡ g1
trajectory-step = refl

trajectory-step-nonzero : add4 ga gb ≢ g0
trajectory-step-nonzero ()

-- 0 postulate.
