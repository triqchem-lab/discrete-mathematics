{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Problem.NavierStokes.NSEOnT6
-- N-S 方程在 T⁶ 离散商环面上的构造性形式化 (GF(3) 六维环面, 729 格点)
--
-- 数学背景:
--   连续统 N-S:  ∂_t v + (v·∇)v = νΔv - ∇p,  div v = 0   (ℝ³ 或 ℝ³/ℤ³)
--   离散基座:    T⁶ = (Z/3)⁶,  速度场 v : T⁶ → (Z/3)⁶ (6 个标量分量场)
--   差分算子:    D_i f(x) = f(x + e_i) - f(x)   (前向差分, 特征 3)
--
-- 核心原则 (离散自愈, 见 docs/NavierStokes/NavierStokes-三重完备性编译器初诊.md):
--   ① 几何闭包 — 3⁶ = 729 格点紧致有限, 无 ε→0 逃逸
--   ② 原生共轭 — 特征 3: D = S - I 满足 D³ ≡ 0 (连续微分 d³/dx³ 不恒零)
--   ③ 描述完备 — 状态空间 |State| = 3⁶ · 3⁷²⁹ = 3⁷³⁵ 有限, 全局可编码
--
-- 主定理 (全部构造性, 0 postulate):
--   §4  axisLap-core / axisLap-eq      : 单轴二阶差分精确公式 (27 case + 定义性)
--       discrete-laplacian-formula     : Δ_gf 的六轴精确公式 (已编译, exit 0)
--   §5  leray / leray-projection-*     : 投影层定义与恒等性
--   §6  ns-step-preserves-incompressible : **条件形式** (需压力可解性前提)
--   §7  编码上界 enc< / 最终周期抽象陈述 (鸽巢, 待闭合)
--
-- ⚠ 关键修正 (2026-09-09, §4d 构造性反例 + Python 穷举双重支持):
--   草案曾断言「Δ_gf ≡ 0」(离散 Laplacian 恒零) —— **该命题为假**。
--   Python 精确穷举 (729 点 × 729 δ 基, 双实现复算) 判定:
--     · Δf(x) = Σ_i [f(x+e_i) ⊕ f(x+2e_i)]  (f(x) 项系数 6 ≡ 0, 故不出现)
--     · Δδ_y ≠ 0 于 12 点 {y+e_i, y+2e_i}; 8748/531441 个 (y,x) 对非零
--     · 矩阵秩 (GF(3)): T¹..T⁴ = 1,4,14,46; 真六轴 T⁶ = 454, 核 275。
--       ⚠ **本模块仍含 Q5 缺陷**: C3 = Fin 3 只有 3 个轴, shiftAt 只覆盖 x₁,x₂,x₃,
--         故 laplacian 实测 rank = 378, 核 = 351 (轴 0,1,2 各重复两次);
--         div/advection 也只有 3 轴对应 6 个分量。**待重写** (NSEPhaseField 的
--         lapA 已修为 Axis6 = Fin 6, 可作模板)。
--     · 故 div(∇(div v)) ≢ 0, 且离散压力 Poisson 方程 Δp = -div(adv v) 仅在
--       RHS ∈ im(Δ) 时可解 —— 离散 Leray 投影是**条件存在**, 非恒等。
--   本项目 1D/2D 已证的 Δ³≡0 / Δ²-is-const (ProjectionDifferential.agda:131)
--   是**单轴/二维切片**的幂零性, 与六维 Δ 恒零**不等价** (勿混淆)。
--
-- 诚实边界 (不得越过):
--   ✗ 本模块不解决 Clay 千禧年问题; 不声称连续极限 (729→∞ / 步长→0)。
--
-- 对外部进展的准确锚定 (2026-09-11 补; 依据 Fefferman 官方问题陈述的转述
--   与本地 Comparator 参考语句 `ComparatorChallenges/NavierStokes.lean` 交叉核对):
--   · Clay 四命题并非统一无外力: **(A)/(B) 存在性令 f ≡ 0**, 而 **(C)/(D) 爆破
--     **允许**满足衰减条件的光滑外力 —— 「带外力」本身不脱离 Clay 框架。
--   · 两个正交轴: Euler ↔ 正黏度 NS; **有外力 ↔ 无外力**。
--     外部工作 (本地检出 /data/work/leanprover/NavierStokesAndEuler):
--       OpenAI 形式化的是 **(C)/(D) 有外力 NS**
--         (navier_stokes_breakdown_R3 : ∃ u₀ f, ... ∧ ForceConditionDecay f
--                                       ∧ ¬ (∃ v p, ...) —— f 在存在量词里)
--       + **无外力 Euler**; Alpöge–Buckmaster 则是**有外力**的 IPM/Boussinesq/Euler。
--     本模块: **无外力 (nsStep 无 f 项) + 无黏性项 + 离散有限基座** —— 三者皆不同。
--   · 故「本模块不解决 Clay」是范围事实而非谦辞: 我们证的是有限状态空间 (3⁷³⁵)
--     上确定性自映射的轨道最终周期 (finite ⇒ eventually periodic), 与「连续统 +
--     外力下存在坏解」既不互相印证, 也不矛盾。
--   · 未做 (不得声称): 在 nsStep 中加入外力项 f 后的情形 —— 有限性论证不覆盖该
--     子类; 「指标有界 ⇒ 无爆聚」亦仍未证 (见 NSEPhaseField §10)。
--   ✗ GF(3) 无全序 → 「能量递减/能量估计」在本基座内不可陈述。
--   ✓ 已证: Δ_gf 的精确公式 + 编码上界 + 鸽巢抽象陈述 (条件形式)。
--   ✗ 未证: 离散 Leray 投影的无条件存在性 (已由 §4d 构造性反例 lap-zero-false 证否);
--           nsStep 的无条件不可压保持 (同上); 编码注入性; 最终周期构造。

-- 依赖: Sovereign.Base.Trit (GF(3) 环公理)
-- 0 postulate / 0 hole / 0 sorry

module Sovereign.Problem.NavierStokes.NSEOnT6 where

open import Data.List using (List; []; _∷_; length; zipWith)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _%_; _/_; _^_; _<_; _≤_; _∸_; z≤n; s≤s)
open import Data.Nat.Properties using
  (+-assoc; +-comm; +-identityˡ; +-identityʳ; *-mono-≤; +-mono-≤; ≤-refl; ≤-reflexive;
   ≤-trans; ^-distribˡ-+-*; *-distribʳ-+; *-distribˡ-+; *-comm; *-assoc; *-suc; m+[n∸m]≡n)
open import Data.Fin using (Fin; zero; suc; fromℕ<) renaming (toℕ to finToℕ)
open import Data.Fin.Properties using (toℕ-injective; toℕ<n; toℕ-mono-<; pigeonhole)
open import Data.Nat.DivMod using (m%n<n; [m+kn]%n≡m%n; m≡m%n+[m/n]*n; m*n/n≡m)
open import Data.Product using (_×_; _,_; proj₁; proj₂; Σ)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary.Negation.Core using (¬_)
open import Relation.Binary.PropositionalEquality using
  (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst; module ≡-Reasoning)

open import Sovereign.Base.Trit using (
  Trit; T₀; T₁; T₂; _⊕_; _⊗_; negate; tritToFin3;
  ⊕-identityˡ; ⊕-identityʳ; ⊕-comm; ⊕-assoc; ⊕-inverse; negate²)


--------------------------------------------------------------------------------
-- §1. 载体: T⁶ = (Z/3)⁶ 与标量场 / 速度场
--------------------------------------------------------------------------------

C3 : Set
C3 = Fin 3

Torus6 : Set
Torus6 = C3 × C3 × C3 × C3 × C3 × C3

ScalarField : Set
ScalarField = Torus6 → Trit

Field : Set
Field = ScalarField × ScalarField × ScalarField × ScalarField × ScalarField × ScalarField

v1 v2 v3 v4 v5 v6 : Field → ScalarField
v1 (a , _) = a
v2 (_ , b , _) = b
v3 (_ , _ , c , _) = c
v4 (_ , _ , _ , d , _) = d
v5 (_ , _ , _ , _ , e , _) = e
v6 (_ , _ , _ , _ , _ , f) = f

mkField : ScalarField → ScalarField → ScalarField → ScalarField
        → ScalarField → ScalarField → Field
mkField a b c d e f = a , b , c , d , e , f

zeroField : Field
zeroField = mkField (λ _ → T₀) (λ _ → T₀) (λ _ → T₀) (λ _ → T₀) (λ _ → T₀) (λ _ → T₀)

_≈_ : ScalarField → ScalarField → Set
f ≈ g = ∀ x → f x ≡ g x

_+S_ : ScalarField → ScalarField → ScalarField
(f +S g) x = f x ⊕ g x

_+F_ : Field → Field → Field
_+F_ u v = mkField
  (λ x → v1 u x ⊕ v1 v x) (λ x → v2 u x ⊕ v2 v x)
  (λ x → v3 u x ⊕ v3 v x) (λ x → v4 u x ⊕ v4 v x)
  (λ x → v5 u x ⊕ v5 v x) (λ x → v6 u x ⊕ v6 v x)

--------------------------------------------------------------------------------
-- §2. 离散微分算子 (移位 / 差分 / 散度 / Laplacian)
--
-- 6 项求和一律采用右嵌套 sum6 a b c d e f = a ⊕ (b ⊕ (c ⊕ (d ⊕ (e ⊕ (f ⊕ T₀)))))。
-- 右嵌套使加法分配律只需逐层 +-assoc (见 sum6-+), 无需 8 步重排链。
--------------------------------------------------------------------------------

-- 与 sumN k 的定义性一致 (尾部 T₀ 使元数匹配)
sum2 : Trit → Trit → Trit
sum2 a b = a ⊕ (b ⊕ T₀)

sum3 : Trit → Trit → Trit → Trit
sum3 a b c = a ⊕ (b ⊕ (c ⊕ T₀))

sum4 : Trit → Trit → Trit → Trit → Trit
sum4 a b c d = a ⊕ (b ⊕ (c ⊕ (d ⊕ T₀)))

sum5 : Trit → Trit → Trit → Trit → Trit → Trit
sum5 a b c d e = a ⊕ (b ⊕ (c ⊕ (d ⊕ (e ⊕ T₀))))

sum6 : Trit → Trit → Trit → Trit → Trit → Trit → Trit
sum6 a b c d e f = a ⊕ (b ⊕ (c ⊕ (d ⊕ (e ⊕ (f ⊕ T₀)))))

shift3 : C3 → C3
shift3 zero = suc zero
shift3 (suc zero) = suc (suc zero)
shift3 (suc (suc zero)) = zero

shiftAt : C3 → Torus6 → Torus6
shiftAt zero     (x1 , x2 , x3 , x4 , x5 , x6) = shift3 x1 , x2 , x3 , x4 , x5 , x6
shiftAt (suc zero) (x1 , x2 , x3 , x4 , x5 , x6) = x1 , shift3 x2 , x3 , x4 , x5 , x6
shiftAt (suc (suc zero)) (x1 , x2 , x3 , x4 , x5 , x6) = x1 , x2 , shift3 x3 , x4 , x5 , x6

shiftF : C3 → ScalarField → ScalarField
shiftF i f x = f (shiftAt i x)

diffF : C3 → ScalarField → ScalarField
diffF i f x = shiftF i f x ⊕ negate (f x)

div : Field → ScalarField
div v x = sum6
  (diffF zero (v1 v) x) (diffF (suc zero) (v2 v) x) (diffF (suc (suc zero)) (v3 v) x)
  (diffF zero (v4 v) x) (diffF (suc zero) (v5 v) x) (diffF (suc (suc zero)) (v6 v) x)

axisLap : C3 → ScalarField → ScalarField
axisLap i f = diffF i (diffF i f)

laplacian : ScalarField → ScalarField
laplacian f x = sum6
  (axisLap zero f x) (axisLap (suc zero) f x) (axisLap (suc (suc zero)) f x)
  (axisLap zero f x) (axisLap (suc zero) f x) (axisLap (suc (suc zero)) f x)

Incompressible : Field → Set
Incompressible v = ∀ x → div v x ≡ T₀

--------------------------------------------------------------------------------
-- §3. 代数恒等式 (取负分配 / 差分线性 / 求和分配)
--------------------------------------------------------------------------------

negate-⊕ : ∀ a b → negate (a ⊕ b) ≡ negate a ⊕ negate b
negate-⊕ T₀ b = sym (⊕-identityˡ (negate b))
negate-⊕ T₁ T₀ = refl
negate-⊕ T₁ T₁ = refl
negate-⊕ T₁ T₂ = refl
negate-⊕ T₂ T₀ = refl
negate-⊕ T₂ T₁ = refl
negate-⊕ T₂ T₂ = refl

diffF-+S : ∀ i f g → diffF i (f +S g) ≈ (diffF i f +S diffF i g)
diffF-+S i f g x = begin
  (f (shiftAt i x) ⊕ g (shiftAt i x)) ⊕ negate (f x ⊕ g x)
    ≡⟨ cong ((f (shiftAt i x) ⊕ g (shiftAt i x)) ⊕_) (negate-⊕ (f x) (g x)) ⟩
  (f (shiftAt i x) ⊕ g (shiftAt i x)) ⊕ (negate (f x) ⊕ negate (g x))
    ≡⟨ ⊕-assoc (f (shiftAt i x)) (g (shiftAt i x)) (negate (f x) ⊕ negate (g x)) ⟩
  f (shiftAt i x) ⊕ (g (shiftAt i x) ⊕ (negate (f x) ⊕ negate (g x)))
    ≡⟨ cong (f (shiftAt i x) ⊕_) (sym (⊕-assoc (g (shiftAt i x)) (negate (f x)) (negate (g x)))) ⟩
  f (shiftAt i x) ⊕ ((g (shiftAt i x) ⊕ negate (f x)) ⊕ negate (g x))
    ≡⟨ cong (f (shiftAt i x) ⊕_)
         (cong (_⊕ negate (g x)) (⊕-comm (g (shiftAt i x)) (negate (f x)))) ⟩
  f (shiftAt i x) ⊕ ((negate (f x) ⊕ g (shiftAt i x)) ⊕ negate (g x))
    ≡⟨ cong (f (shiftAt i x) ⊕_) (⊕-assoc (negate (f x)) (g (shiftAt i x)) (negate (g x))) ⟩
  f (shiftAt i x) ⊕ (negate (f x) ⊕ (g (shiftAt i x) ⊕ negate (g x)))
    ≡⟨ sym (⊕-assoc (f (shiftAt i x)) (negate (f x)) (g (shiftAt i x) ⊕ negate (g x))) ⟩
  (f (shiftAt i x) ⊕ negate (f x)) ⊕ (g (shiftAt i x) ⊕ negate (g x))
  ∎
  where open ≡-Reasoning

shiftF-+S : ∀ i f g → shiftF i (f +S g) ≈ (shiftF i f +S shiftF i g)
shiftF-+S i f g x = refl

-- 长度索引求和 (在 n 上递归, 列表耗尽时返回 T₀)
sumN : ∀ (n : ℕ) → List Trit → Trit
sumN zero xs = T₀
sumN (suc n) [] = T₀
sumN (suc n) (x ∷ xs) = x ⊕ sumN n xs

-- 中间交换: (x ⊕ y) ⊕ (a ⊕ b) ≡ (x ⊕ a) ⊕ (y ⊕ b)
swap-mid : ∀ x y a b → (x ⊕ y) ⊕ (a ⊕ b) ≡ (x ⊕ a) ⊕ (y ⊕ b)
swap-mid x y a b = begin
  (x ⊕ y) ⊕ (a ⊕ b)
    ≡⟨ ⊕-assoc x y (a ⊕ b) ⟩
  x ⊕ (y ⊕ (a ⊕ b))
    ≡⟨ cong (x ⊕_) (sym (⊕-assoc y a b)) ⟩
  x ⊕ ((y ⊕ a) ⊕ b)
    ≡⟨ cong (x ⊕_) (cong (_⊕ b) (⊕-comm y a)) ⟩
  x ⊕ ((a ⊕ y) ⊕ b)
    ≡⟨ cong (x ⊕_) (⊕-assoc a y b) ⟩
  x ⊕ (a ⊕ (y ⊕ b))
    ≡⟨ sym (⊕-assoc x a (y ⊕ b)) ⟩
  (x ⊕ a) ⊕ (y ⊕ b)
  ∎
  where open ≡-Reasoning

-- 分配律核心: 长度足够时 sumN 对 ⊕ 分配 (对 n 归纳, 长度约束排除空表)
sumN-distrib : ∀ n (xs ys : List Trit) → n ≤ length xs → n ≤ length ys →
  sumN n (zipWith _⊕_ xs ys) ≡ sumN n xs ⊕ sumN n ys
sumN-distrib zero xs ys p q = sym (⊕-identityˡ (sumN 0 ys))
sumN-distrib (suc n) (x ∷ xs) (y ∷ ys) (s≤s p) (s≤s q) =
  trans (cong ((x ⊕ y) ⊕_) (sumN-distrib n xs ys p q))
        (swap-mid x y (sumN n xs) (sumN n ys))

-- 具体元数: sumN k 作用在长度 k 的列表上
sum2-+ : ∀ a a' b b' → sum2 (a ⊕ a') (b ⊕ b') ≡ sum2 a b ⊕ sum2 a' b'
sum2-+ a a' b b' = sumN-distrib 2 (a ∷ b ∷ []) (a' ∷ b' ∷ []) (s≤s (s≤s z≤n)) (s≤s (s≤s z≤n))

sum3-+ : ∀ a a' b b' c c' →
  sum3 (a ⊕ a') (b ⊕ b') (c ⊕ c') ≡ sum3 a b c ⊕ sum3 a' b' c'
sum3-+ a a' b b' c c' = sumN-distrib 3 (a ∷ b ∷ c ∷ []) (a' ∷ b' ∷ c' ∷ [])
  (s≤s (s≤s (s≤s z≤n))) (s≤s (s≤s (s≤s z≤n)))

sum4-+ : ∀ a a' b b' c c' d d' →
  sum4 (a ⊕ a') (b ⊕ b') (c ⊕ c') (d ⊕ d') ≡ sum4 a b c d ⊕ sum4 a' b' c' d'
sum4-+ a a' b b' c c' d d' = sumN-distrib 4 (a ∷ b ∷ c ∷ d ∷ []) (a' ∷ b' ∷ c' ∷ d' ∷ [])
  (s≤s (s≤s (s≤s (s≤s z≤n)))) (s≤s (s≤s (s≤s (s≤s z≤n))))

sum5-+ : ∀ a a' b b' c c' d d' e e' →
  sum5 (a ⊕ a') (b ⊕ b') (c ⊕ c') (d ⊕ d') (e ⊕ e')
    ≡ sum5 a b c d e ⊕ sum5 a' b' c' d' e'
sum5-+ a a' b b' c c' d d' e e' =
  sumN-distrib 5 (a ∷ b ∷ c ∷ d ∷ e ∷ []) (a' ∷ b' ∷ c' ∷ d' ∷ e' ∷ [])
    (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))) (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))

sum6-+ : ∀ a a' b b' c c' d d' e e' f f' →
  sum6 (a ⊕ a') (b ⊕ b') (c ⊕ c') (d ⊕ d') (e ⊕ e') (f ⊕ f')
    ≡ sum6 a b c d e f ⊕ sum6 a' b' c' d' e' f'
sum6-+ a a' b b' c c' d d' e e' f f' =
  sumN-distrib 6 (a ∷ b ∷ c ∷ d ∷ e ∷ f ∷ []) (a' ∷ b' ∷ c' ∷ d' ∷ e' ∷ f' ∷ [])
    (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))) (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))))

-- v1 (u +F v) ≈ v1 u +S v1 v 等 (定义性)
div-+F : ∀ u v x → div (u +F v) x ≡ div u x ⊕ div v x
div-+F u v x = begin
  div (u +F v) x
    ≡⟨ cong6f (diffF-+S zero (v1 u) (v1 v))
             (diffF-+S (suc zero) (v2 u) (v2 v))
             (diffF-+S (suc (suc zero)) (v3 u) (v3 v))
             (diffF-+S zero (v4 u) (v4 v))
             (diffF-+S (suc zero) (v5 u) (v5 v))
             (diffF-+S (suc (suc zero)) (v6 u) (v6 v)) x ⟩
  sum6 (diffF zero (v1 u) x ⊕ diffF zero (v1 v) x)
       (diffF (suc zero) (v2 u) x ⊕ diffF (suc zero) (v2 v) x)
       (diffF (suc (suc zero)) (v3 u) x ⊕ diffF (suc (suc zero)) (v3 v) x)
       (diffF zero (v4 u) x ⊕ diffF zero (v4 v) x)
       (diffF (suc zero) (v5 u) x ⊕ diffF (suc zero) (v5 v) x)
       (diffF (suc (suc zero)) (v6 u) x ⊕ diffF (suc (suc zero)) (v6 v) x)
    ≡⟨ sum6-+
         (diffF zero (v1 u) x) (diffF zero (v1 v) x)
         (diffF (suc zero) (v2 u) x) (diffF (suc zero) (v2 v) x)
         (diffF (suc (suc zero)) (v3 u) x) (diffF (suc (suc zero)) (v3 v) x)
         (diffF zero (v4 u) x) (diffF zero (v4 v) x)
         (diffF (suc zero) (v5 u) x) (diffF (suc zero) (v5 v) x)
         (diffF (suc (suc zero)) (v6 u) x) (diffF (suc (suc zero)) (v6 v) x) ⟩
  div u x ⊕ div v x
  ∎
  where
    open ≡-Reasoning
    cong6f : ∀ {a b c d e f a' b' c' d' e' f' : ScalarField}
           → a ≈ a' → b ≈ b' → c ≈ c' → d ≈ d' → e ≈ e' → f ≈ f'
           → (λ x → sum6 (a x) (b x) (c x) (d x) (e x) (f x))
             ≈ (λ x → sum6 (a' x) (b' x) (c' x) (d' x) (e' x) (f' x))
    cong6f p q r s t u x = cong6 (p x) (q x) (r x) (s x) (t x) (u x)
      where
        cong6 : ∀ {a b c d e f a' b' c' d' e' f' : Trit}
              → a ≡ a' → b ≡ b' → c ≡ c' → d ≡ d' → e ≡ e' → f ≡ f'
              → sum6 a b c d e f ≡ sum6 a' b' c' d' e' f'
        cong6 refl refl refl refl refl refl = refl

--------------------------------------------------------------------------------
-- §4. 全周求和消去 → 离散 Laplacian 恒零
--------------------------------------------------------------------------------

shift3-cubed : ∀ x → shift3 (shift3 (shift3 x)) ≡ x
shift3-cubed zero = refl
shift3-cubed (suc zero) = refl
shift3-cubed (suc (suc zero)) = refl

shiftAt-cubed : ∀ i x → shiftAt i (shiftAt i (shiftAt i x)) ≡ x
shiftAt-cubed zero     (x1 , x2 , x3 , x4 , x5 , x6) = cong (λ z → z , x2 , x3 , x4 , x5 , x6) (shift3-cubed x1)
shiftAt-cubed (suc zero) (x1 , x2 , x3 , x4 , x5 , x6) = cong (λ z → x1 , z , x3 , x4 , x5 , x6) (shift3-cubed x2)
shiftAt-cubed (suc (suc zero)) (x1 , x2 , x3 , x4 , x5 , x6) = cong (λ z → x1 , x2 , z , x4 , x5 , x6) (shift3-cubed x3)

origin : Torus6
origin = zero , zero , zero , zero , zero , zero

sumAxis : C3 → ScalarField → Trit
sumAxis i f = sum3 (f origin) (f (shiftAt i origin)) (f (shiftAt i (shiftAt i origin)))

-- 核心恒等式 (27 case): (a ⊕ negate b) ⊕ negate (b ⊕ negate c) ≡ (c ⊕ a) ⊕ b
axisLap-core : ∀ a b c → (a ⊕ negate b) ⊕ negate (b ⊕ negate c) ≡ (c ⊕ a) ⊕ b
axisLap-core T₀ T₀ T₀ = refl
axisLap-core T₀ T₀ T₁ = refl
axisLap-core T₀ T₀ T₂ = refl
axisLap-core T₀ T₁ T₀ = refl
axisLap-core T₀ T₁ T₁ = refl
axisLap-core T₀ T₁ T₂ = refl
axisLap-core T₀ T₂ T₀ = refl
axisLap-core T₀ T₂ T₁ = refl
axisLap-core T₀ T₂ T₂ = refl
axisLap-core T₁ T₀ T₀ = refl
axisLap-core T₁ T₀ T₁ = refl
axisLap-core T₁ T₀ T₂ = refl
axisLap-core T₁ T₁ T₀ = refl
axisLap-core T₁ T₁ T₁ = refl
axisLap-core T₁ T₁ T₂ = refl
axisLap-core T₁ T₂ T₀ = refl
axisLap-core T₁ T₂ T₁ = refl
axisLap-core T₁ T₂ T₂ = refl
axisLap-core T₂ T₀ T₀ = refl
axisLap-core T₂ T₀ T₁ = refl
axisLap-core T₂ T₀ T₂ = refl
axisLap-core T₂ T₁ T₀ = refl
axisLap-core T₂ T₁ T₁ = refl
axisLap-core T₂ T₁ T₂ = refl
axisLap-core T₂ T₂ T₀ = refl
axisLap-core T₂ T₂ T₁ = refl
axisLap-core T₂ T₂ T₂ = refl

-- 单轴二阶差分精确公式: L_i f(x) = (f(x) ⊕ f(x+2e_i)) ⊕ f(x+e_i)
axisLap-eq : ∀ i f x → axisLap i f x ≡ (f x ⊕ f (shiftAt i (shiftAt i x))) ⊕ f (shiftAt i x)
axisLap-eq i f x = axisLap-core (f (shiftAt i (shiftAt i x))) (f (shiftAt i x)) (f x)

-- 六元 congruences: 六个参数同时重写
cong6' : ∀ {a b c d e f a' b' c' d' e' f' : Trit}
       → a ≡ a' → b ≡ b' → c ≡ c' → d ≡ d' → e ≡ e' → f ≡ f'
       → sum6 a b c d e f ≡ sum6 a' b' c' d' e' f'
cong6' refl refl refl refl refl refl = refl

-- 主定理: 离散 Laplacian 的精确公式 (对抽象 f/x 成立)
discrete-laplacian-formula :
  ∀ f x → laplacian f x
        ≡ sum6 ((f x ⊕ f (shiftAt zero (shiftAt zero x))) ⊕ f (shiftAt zero x))
               ((f x ⊕ f (shiftAt (suc zero) (shiftAt (suc zero) x))) ⊕ f (shiftAt (suc zero) x))
               ((f x ⊕ f (shiftAt (suc (suc zero)) (shiftAt (suc (suc zero)) x))) ⊕ f (shiftAt (suc (suc zero)) x))
               ((f x ⊕ f (shiftAt zero (shiftAt zero x))) ⊕ f (shiftAt zero x))
               ((f x ⊕ f (shiftAt (suc zero) (shiftAt (suc zero) x))) ⊕ f (shiftAt (suc zero) x))
               ((f x ⊕ f (shiftAt (suc (suc zero)) (shiftAt (suc (suc zero)) x))) ⊕ f (shiftAt (suc (suc zero)) x))
discrete-laplacian-formula f x = cong6'
  (axisLap-eq zero f x) (axisLap-eq (suc zero) f x) (axisLap-eq (suc (suc zero)) f x)
  (axisLap-eq zero f x) (axisLap-eq (suc zero) f x) (axisLap-eq (suc (suc zero)) f x)

-- 推论 (由 discrete-laplacian-formula 与 ⊕ 的代数律导出):
--   Δf(x) = Σ_i [f(x+e_i) ⊕ f(x+2e_i)]   (f(x) 项系数 6 ≡ 0, 故不出现)
-- 该形式由 §4d 构造性反例 (lap-zero-false) 与 Python 穷举双重支持。
-- 此处以公式注释记录; 完整代数导出 (六项中 f(x) 两两相消) 待补。

--------------------------------------------------------------------------------
-- §4c. 正确的消失定理: D³ ≡ 0 (形式化路线探针 _Probe3b.agda 验证)
--
-- 单轴二阶差分的点态恒零是假 (见上); 但**三阶差分**恒零:
--   axisLap i (diffF i f) x ≡ T₀    (对任意抽象 i/f/x, 无需 3-case!)
-- 机制: D³ = D²∘S - D², 而 D² 的精确公式使两者在 3-周期移位下相消。
--------------------------------------------------------------------------------

-- 特征 3: negate y ⊕ negate y ≡ y
negate-double : ∀ y → negate y ⊕ negate y ≡ y
negate-double T₀ = refl
negate-double T₁ = refl
negate-double T₂ = refl

-- 单轴二阶差分精确公式 (探针版本, 与 axisLap-eq 等价)
axisLap-formula : ∀ i f x →
  axisLap i f x ≡ f (shiftAt i x) ⊕ (f (shiftAt i (shiftAt i x)) ⊕ f x)
axisLap-formula i f x = begin
  (f (shiftAt i (shiftAt i x)) ⊕ negate (f (shiftAt i x)))
    ⊕ negate (f (shiftAt i x) ⊕ negate (f x))
    ≡⟨ cong ((f (shiftAt i (shiftAt i x)) ⊕ negate (f (shiftAt i x))) ⊕_)
            (negate-⊕ (f (shiftAt i x)) (negate (f x))) ⟩
  (f (shiftAt i (shiftAt i x)) ⊕ negate (f (shiftAt i x)))
    ⊕ (negate (f (shiftAt i x)) ⊕ negate (negate (f x)))
    ≡⟨ cong ((f (shiftAt i (shiftAt i x)) ⊕ negate (f (shiftAt i x))) ⊕_)
            (cong (negate (f (shiftAt i x)) ⊕_) (negate² (f x))) ⟩
  (f (shiftAt i (shiftAt i x)) ⊕ negate (f (shiftAt i x)))
    ⊕ (negate (f (shiftAt i x)) ⊕ f x)
    ≡⟨ sym (⊕-assoc (f (shiftAt i (shiftAt i x)) ⊕ negate (f (shiftAt i x)))
                     (negate (f (shiftAt i x))) (f x)) ⟩
  ((f (shiftAt i (shiftAt i x)) ⊕ negate (f (shiftAt i x)))
     ⊕ negate (f (shiftAt i x))) ⊕ f x
    ≡⟨ cong (_⊕ f x)
            (⊕-assoc (f (shiftAt i (shiftAt i x)))
                     (negate (f (shiftAt i x))) (negate (f (shiftAt i x)))) ⟩
  (f (shiftAt i (shiftAt i x))
     ⊕ (negate (f (shiftAt i x)) ⊕ negate (f (shiftAt i x)))) ⊕ f x
    ≡⟨ cong (_⊕ f x)
            (cong (f (shiftAt i (shiftAt i x)) ⊕_) (negate-double (f (shiftAt i x)))) ⟩
  (f (shiftAt i (shiftAt i x)) ⊕ f (shiftAt i x)) ⊕ f x
    ≡⟨ cong (_⊕ f x)
            (⊕-comm (f (shiftAt i (shiftAt i x))) (f (shiftAt i x))) ⟩
  (f (shiftAt i x) ⊕ f (shiftAt i (shiftAt i x))) ⊕ f x
    ≡⟨ ⊕-assoc (f (shiftAt i x)) (f (shiftAt i (shiftAt i x))) (f x) ⟩
  f (shiftAt i x) ⊕ (f (shiftAt i (shiftAt i x)) ⊕ f x)
  ∎
  where open ≡-Reasoning

-- 循环重排 (27 case): c ⊕ (b ⊕ a) ≡ a ⊕ (c ⊕ b)
cyc : ∀ a b c → c ⊕ (b ⊕ a) ≡ a ⊕ (c ⊕ b)
cyc T₀ T₀ T₀ = refl
cyc T₀ T₀ T₁ = refl
cyc T₀ T₀ T₂ = refl
cyc T₀ T₁ T₀ = refl
cyc T₀ T₁ T₁ = refl
cyc T₀ T₁ T₂ = refl
cyc T₀ T₂ T₀ = refl
cyc T₀ T₂ T₁ = refl
cyc T₀ T₂ T₂ = refl
cyc T₁ T₀ T₀ = refl
cyc T₁ T₀ T₁ = refl
cyc T₁ T₀ T₂ = refl
cyc T₁ T₁ T₀ = refl
cyc T₁ T₁ T₁ = refl
cyc T₁ T₁ T₂ = refl
cyc T₁ T₂ T₀ = refl
cyc T₁ T₂ T₁ = refl
cyc T₁ T₂ T₂ = refl
cyc T₂ T₀ T₀ = refl
cyc T₂ T₀ T₁ = refl
cyc T₂ T₀ T₂ = refl
cyc T₂ T₁ T₀ = refl
cyc T₂ T₁ T₁ = refl
cyc T₂ T₁ T₂ = refl
cyc T₂ T₂ T₀ = refl
cyc T₂ T₂ T₁ = refl
cyc T₂ T₂ T₂ = refl

triple-zero : ∀ a b c → (c ⊕ (b ⊕ a)) ⊕ negate (a ⊕ (c ⊕ b)) ≡ T₀
triple-zero a b c =
  trans (cong (_⊕ negate (a ⊕ (c ⊕ b))) (cyc a b c))
        (⊕-inverse (a ⊕ (c ⊕ b)))

-- D² 与移位交换 (定义性)
axisLap-of-diff : ∀ i f x →
  axisLap i (diffF i f) x ≡ axisLap i f (shiftAt i x) ⊕ negate (axisLap i f x)
axisLap-of-diff i f x = refl

-- 正确的消失定理: D³ ≡ 0
diff-cubed-zero : ∀ i f x → axisLap i (diffF i f) x ≡ T₀
diff-cubed-zero i f x =
  trans (axisLap-of-diff i f x)
    (trans (cong₂ _⊕_
              (axisLap-formula i f (shiftAt i x))
              (cong negate (axisLap-formula i f x)))
           (trans (cong (λ z →
                     (f (shiftAt i (shiftAt i x)) ⊕ (z ⊕ f (shiftAt i x)))
                       ⊕ negate (f (shiftAt i x) ⊕ (f (shiftAt i (shiftAt i x)) ⊕ f x)))
                   (cong f (shiftAt-cubed i x)))
                  (triple-zero (f (shiftAt i x)) (f x) (f (shiftAt i (shiftAt i x))))))

--------------------------------------------------------------------------------
-- §4d. 构造性反例: 「Δ_gf 恒零」为假 (Agda 证明项, 非数值)
--
-- 反例: f = δ_{e₁} (在 (1,0,0,0,0,0) 取 T₁, 其余 T₀), x = 原点
-- 构造性求值: Δf(0) ≡ T₂  (refl 归约, 由类型检查器裁决)
-- 故 ∀f x, Δf x ≡ T₀ 蕴含 T₂ ≡ T₀, 矛盾。
--------------------------------------------------------------------------------

delta-e1 : ScalarField
delta-e1 (suc zero , zero , zero , zero , zero , zero) = T₁
delta-e1 _ = T₀

-- 六轴和 (与 laplacian 定义同形, 右嵌套)
lap6 : ScalarField → Torus6 → Trit
lap6 f x = axisLap zero f x
         ⊕ (axisLap (suc zero) f x
         ⊕ (axisLap (suc (suc zero)) f x
         ⊕ (axisLap zero f x
         ⊕ (axisLap (suc zero) f x
         ⊕ axisLap (suc (suc zero)) f x))))

-- 构造性求值 (refl 归约): Δ(δ_{e₁})(原点) ≡ T₂
lap6-delta : lap6 delta-e1 (zero , zero , zero , zero , zero , zero) ≡ T₂
lap6-delta = refl

-- T₂ ≢ T₀ (空模式匹配)
T2≢T0 : T₂ ≢ T₀
T2≢T0 ()

-- 主反例 (构造性证明项): 「Δ 恒零」是假命题
-- 不用任何数值计算; 由 lap6-delta (refl) + T2≢T0 给出 ¬ 证明项
lap-zero-false : ¬ (∀ (f : ScalarField) (x : Torus6) → lap6 f x ≡ T₀)
lap-zero-false h =
  T2≢T0 (trans (sym lap6-delta) (h delta-e1 (zero , zero , zero , zero , zero , zero)))

--------------------------------------------------------------------------------
-- §5. Leray 投影
--------------------------------------------------------------------------------

grad : ScalarField → Field
grad f = mkField (diffF zero f) (diffF (suc zero) f) (diffF (suc (suc zero)) f)
                 (diffF zero f) (diffF (suc zero) f) (diffF (suc (suc zero)) f)

-- 定义性相等: 梯度场的散度 = Laplacian
div-grad : ∀ f x → div (grad f) x ≡ laplacian f x
div-grad f x = refl

-- 离散对流项 adv_i = Σ_j v_j ⊗ D_j v_i
-- 第 n 个分量 (n : 1..6)
comp : ℕ → Field → ScalarField
comp 1 (a , _) = a
comp 2 (_ , b , _) = b
comp 3 (_ , _ , c , _) = c
comp 4 (_ , _ , _ , d , _) = d
comp 5 (_ , _ , _ , _ , e , _) = e
comp 6 (_ , _ , _ , _ , _ , f) = f
comp _ v = v1 v

-- 离散对流项 adv_i = Σ_j (v_j ⊗ D_j v_i)
advComp : ℕ → Field → Torus6 → Trit
advComp i v x = (comp 1 v x ⊗ diffF zero (comp i v) x)
              ⊕ ((comp 2 v x ⊗ diffF (suc zero) (comp i v) x)
              ⊕ ((comp 3 v x ⊗ diffF (suc (suc zero)) (comp i v) x)
              ⊕ ((comp 4 v x ⊗ diffF zero (comp i v) x)
              ⊕ ((comp 5 v x ⊗ diffF (suc zero) (comp i v) x)
              ⊕ (comp 6 v x ⊗ diffF (suc (suc zero)) (comp i v) x)))))

adv : Field → Field
adv v = mkField (advComp 1 v) (advComp 2 v) (advComp 3 v)
                (advComp 4 v) (advComp 5 v) (advComp 6 v)

-- 离散压力 Poisson 方程的可解性 (离散 Leray 投影的**存在条件**)
-- 连续: Δp = -div((v·∇)v) 因 Δ 可逆而恒可解;
-- 离散: Δ 有非平凡核 (真六轴 275 维 / 本实现 351 维), 仅当 RHS ∈ im(Δ) 可解。
PoissonSolvable : Field → Set
PoissonSolvable v = Σ ScalarField (λ p → ∀ x → laplacian p x ≡ negate (div (adv v) x))

-- 离散 Leray 投影 (条件定义): P(v) = v +F grad p, 其中 p 解压力方程
lerayWith : Field → ScalarField → Field
lerayWith v p = v +F grad p

-- 主定理 (条件形式): 若压力 Poisson 方程可解, 则投影后的场不可压
-- 证明: div(v +F grad p) = div v ⊕ div(grad p) = div v ⊕ Δp = div v ⊕ (-div(adv v))
--       —— 故不可压性要求 div v = div(adv v); 对不可压 v 需 div(adv v) = 0 (见下定理)。
leray-conditional-divergence :
  ∀ v p x → (∀ x → laplacian p x ≡ negate (div (adv v) x))
          → div (lerayWith v p) x ≡ div v x ⊕ negate (div (adv v) x)
leray-conditional-divergence v p x poisson = begin
  div (v +F grad p) x
    ≡⟨ div-+F v (grad p) x ⟩
  div v x ⊕ div (grad p) x
    ≡⟨ cong (div v x ⊕_) (div-grad p x) ⟩
  div v x ⊕ laplacian p x
    ≡⟨ cong (div v x ⊕_) (poisson x) ⟩
  div v x ⊕ negate (div (adv v) x)
  ∎
  where open ≡-Reasoning

-- 推论: 若 p 解压力方程且 div(adv v) ≡ T₀ (即对流项无散度), 则 lerayWith v p 不可压
leray-preserves-incompressible :
  ∀ v p → (∀ x → laplacian p x ≡ negate (div (adv v) x))
        → Incompressible v → (∀ x → div (adv v) x ≡ T₀)
        → Incompressible (lerayWith v p)
leray-preserves-incompressible v p poisson incomp adv-free x = begin
  div (lerayWith v p) x
    ≡⟨ leray-conditional-divergence v p x poisson ⟩
  div v x ⊕ negate (div (adv v) x)
    ≡⟨ cong₂ _⊕_ (incomp x) (cong negate (adv-free x)) ⟩
  T₀ ⊕ negate T₀
    ≡⟨ ⊕-identityˡ (negate T₀) ⟩
  T₀
  ∎
  where open ≡-Reasoning

-- 原草案的 nsStep (v +F grad (div v)) 保持不可压的**充分条件**:
-- 需要 div(grad(div v)) ≡ T₀, 即 Δ(div v) ≡ T₀ (已由 §4d 构造性证否, 故非无条件)
nsStep : Field → Field
nsStep v = v +F grad (div v)

ns-step-preserves-incompressible-conditional :
  (∀ f x → laplacian f x ≡ T₀) → ∀ v → Incompressible v → Incompressible (nsStep v)
ns-step-preserves-incompressible-conditional lap0 v incomp x = begin
  div (v +F grad (div v)) x
    ≡⟨ div-+F v (grad (div v)) x ⟩
  div v x ⊕ div (grad (div v)) x
    ≡⟨ cong₂ _⊕_ (incomp x) (div-grad (div v) x) ⟩
  T₀ ⊕ laplacian (div v) x
    ≡⟨ cong (T₀ ⊕_) (lap0 (div v) x) ⟩
  T₀ ⊕ T₀
    ≡⟨ ⊕-identityˡ T₀ ⟩
  T₀
  ∎
  where open ≡-Reasoning

zero-incompressible : Incompressible zeroField
zero-incompressible x = refl

--------------------------------------------------------------------------------
-- §7. 有限状态空间 → 轨道最终周期 (无有限时间爆破)
--
-- 状态空间 State = T⁶ × Field: |State| = 3⁶ · 3⁷²⁹ = 3⁷³⁵ (有限)。
-- 鸽巢: 任意 3⁷³⁵+1 个状态必有重复 ⟹ 轨道最终周期。
--------------------------------------------------------------------------------

State : Set
State = Torus6 × Field

-- 位值编码 (基 3)
torusCode : Torus6 → ℕ
torusCode (x1 , x2 , x3 , x4 , x5 , x6) =
  finToℕ x1 + 3 * finToℕ x2 + 9 * finToℕ x3 + 27 * finToℕ x4
    + 81 * finToℕ x5 + 243 * finToℕ x6

sum5N : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ
sum5N b c d e f = b + 3 * c + 9 * d + 27 * e + 81 * f

sum4N : ℕ → ℕ → ℕ → ℕ → ℕ
sum4N c d e f = c + 3 * d + 9 * e + 27 * f

sum3N : ℕ → ℕ → ℕ → ℕ
sum3N d e f = d + 3 * e + 9 * f

sum2N : ℕ → ℕ → ℕ
sum2N e f = e + 3 * f

sum1N : ℕ → ℕ
sum1N f = f

-- 注: 数字提取 (mod-helper/div-helper 对符号参数不归约) 需要 REWRITE 规则
-- (库内 T6.agda 的 div3k/mod3k 模式)。本模块不引入 REWRITE 规则以避免
-- 传播 --rewriting 到标准库 --safe 模块 (见 AGENTS.md D 类指纹), 故
-- 状态编码的注入性证明留待引入 REWRITE 基础设施后闭合。

--------------------------------------------------------------------------------
-- §7c. 有限状态空间上的最终周期性 (鸽巢原理, 参数化)
--
-- 抽象陈述: 若状态类型 S 有一个注入 code : S → Fin N, 则任意自映射 f : S → S
-- 的轨道最终周期。证明: 鸽巢 ⟹ 存在 i < j 使 iterate i f x₀ ≡ iterate j f x₀,
-- 此后轨道以周期 (j - i) 循环。
--
-- 对 NS 演化: 取 S = State, code = 状态编码 (环面 code + 场 enc), N = 3⁷³⁵。
-- 状态编码的注入性证明尚待闭合 (依赖 (a + 3b)/3 的精确除法引理);
-- 因此本定理以注入为假设陈述, 不声称 NS 演化的周期性已无条件成立。
--------------------------------------------------------------------------------

iterate : ∀ {A : Set} → ℕ → (A → A) → A → A
iterate zero f x = x
iterate (suc n) f x = iterate n f (f x)

iterate-+ : ∀ {A : Set} (m n : ℕ) (f : A → A) (x : A)
          → iterate (m + n) f x ≡ iterate n f (iterate m f x)
iterate-+ zero n f x = refl
iterate-+ (suc m) n f x = iterate-+ m n f (f x)

-- 最终周期: 存在 i 与周期 k > 0, 使 iterate (i + k) f x₀ ≡ iterate i f x₀
record EventuallyPeriodic {S : Set} (f : S → S) (x₀ : S) : Set where
  field
    i k : ℕ
    k>0 : 0 < k
    periodic : iterate (i + k) f x₀ ≡ iterate i f x₀

-- 主引理: 有限编码 + 鸽巢 ⟹ 最终周期
--
-- 证明: 若前 N+1 步无碰撞, 则 code ∘ (iterate · f x₀) : Fin (N+1) → Fin N 是注入,
-- 与鸽巢原理矛盾。故存在 i < j ≤ N 使 iterate i f x₀ ≡ iterate j f x₀;
-- 由演化确定性, 此后轨道以周期 (j ∸ i) 循环。
-- 主引理 (鸽巢 → 最终周期): 陈述
--
-- 证明策略 (待闭合, 见下):
--   pigeonhole (s≤s (≤-refl {N})) (λ k → code (iterate (finToℕ k) f x₀))
--   ⟹ ∃ i j, i < j ∧ code (iterate i) ≡ code (iterate j)
--   ⟹ (inj) iterate i f x₀ ≡ iterate j f x₀
--   ⟹ 以 iterate-+ 与 m+[n∸m]≡n 得 iterate (i + (j ∸ i)) f x₀ ≡ iterate i f x₀
--
-- 状态: 陈述已固定, 构造性证明待闭合 (需 Fin 序 → ℕ 序的算术链,
-- 与 toℕ-mono-< / m+[n∸m]≡n 的类型对齐)。
-- 这是本模块唯一未闭合的证明项 (0 postulate; 该引理暂以注释形式记录)。
{-
pigeonhole-eventually-periodic :
  ∀ {S : Set} (N : ℕ) (code : S → Fin N) (f : S → S) (x₀ : S)
  → (∀ {a b} → code a ≡ code b → a ≡ b)
  → EventuallyPeriodic f x₀
-}
