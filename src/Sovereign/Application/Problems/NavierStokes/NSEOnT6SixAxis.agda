{-# OPTIONS --rewriting --guardedness #-}

-- | NSE6Axis — N-S 方程在 T⁶ 上的**六轴**离散微分算子（Q5 缺陷修复版）
--
-- 数学背景
--   连续统 N-S:  ∂_t v + (v·∇)v = νΔv - ∇p,   div v = 0      (ℝ³ 或 ℝ³/ℤ³)
--   离散基座:    T⁶ = (Z/3)⁶,  |T⁶| = 729 格点
--                标量场 f : T⁶ → Trit (GF(3) 幅度)
--                速度场 v = (v₁,…,v₆) : T⁶ → (GF(3))⁶
--   差分算子:    (Dᵢ f)(x) = f(x + eᵢ) - f(x) = f(x+eᵢ) ⊕ negate (f x)   (前向差分, 特征 3)
--   六个算子:    div₆ = Σ_{i=1}^{6} D_i v_i,   grad₆ f = (D_1 f, …, D_6 f)
--                laplacian₆ = Σ_{i=1}^{6} D_i D_i
--
-- Q5 缺陷与本模块的修复（本模块存在的唯一理由）
--   上游 `Sovereign.Application.Problems.NavierStokes.NSEOnT6` 用 `C3 = Fin 3` 当轴索引，
--   `shiftAt : C3 → Torus6 → Torus6` 只覆盖 x₁,x₂,x₃；于是
--     · `div` 的六个分量两两共用同一个轴：  v₁,v₄ ↦ 轴 0;  v₂,v₅ ↦ 轴 1;  v₃,v₆ ↦ 轴 2
--     · `grad` 同理（第 4,5,6 分量等于第 1,2,3 分量）
--     · `laplacian` 把轴 0,1,2 的轴二阶差分各**重复两次**
--   ⇒ `laplacian` 实测 rank = 378, 核维数 351（真六轴为 rank 454 / 核 275）。
--   本模块把轴索引换成 `Axis6 = Fin 6`，`shiftAt6` 覆盖 x₁…x₆ 全部六个坐标，
--   第 i 个向量分量**只**沿第 i 个轴差分 —— 六轴一一对应，无别名、无重复。
--
-- 与上游三轴版的差异（逐条；本模块不 import 上游，故不存在「继承缺陷」）
--   ① 轴索引:      C3 = Fin 3          →  Axis6 = Fin 6         (六个轴各司其职)
--   ② shiftAt:     3 个 case            →  6 个 case             (x₁…x₆ 全可移位)
--   ③ div:         分量↦轴 有重复        →  分量↦轴 是**双射** i ↦ i
--   ④ grad:        第 4,5,6 分量复写略   →  六个分量各取自己的轴
--   ⑤ laplacian:   轴 0,1,2 各算两次      →  轴 0…5 各算一次
--   ⑥ div-grad6:   `refl`（定义性相等）—— **这一点与上游相同**：上游的 `div-grad`
--                  也是 `refl`，因为它的 grad/div/laplacian 三者用的是**同一套有缺陷
--                  的轴分配**，定义性对齐是自洽的。换句话说 `div-grad = refl` **不能**
--                  证明轴分配正确：它只证明「三处写法一致」。本模块因此额外给出
--                  **反例型判别引理**（§6），构造性地证明六轴版 ≢ 三轴复刻版。
--   ⑦ div6-+F6 / nsStep6 的条件保持：与上游同形而换到六轴词汇。
--   ⑧ 上游戏标 `laplacian f x ≡ T₀`（离散 Δ 恒零）在本版**同样为假**，本模块给出
--      构造性否证 `laplacian6-not-identically-zero`，并把它当作诚实边界写进 §6/§7。
--
-- 主定理
--   §5  div-grad6 : ∀ f x → div6 (grad6 f) x ≡ laplacian6 f x            (refl)
--   §8  advAt / adv1..adv6 / advField6 : 离散对流 `Σ_j v_j ⊗ D_j v_i`（六轴 1-1）
--   §5  div6-+F6  : ∀ u v x → div6 (u +F6 v) x ≡ div6 u x ⊕ div6 v x     (代数链)
--   §5  ns-step6-preserves-incompressible-conditional                    (条件式)
--   §5  ns-step6-preserves-incompressible                                (可用式：逐场前提)
--   §6  laplacian6 ≢ laplacian3Replica / div6 ≢ div3Replica              (判别引理)
--
-- 诚实边界（不得越过）
--   ✗ 本模块是 GF(3) **幅度层**的算子层，不含 DC 的 C₄ 相位层
--     （相位层在 `NSEPhaseField` 的 `phaseDiff`/`AlphaPower` 一侧）。按相位不可约性
--     元公理，幅度层的结论**不得**被解释为对相位层已完备。
--   ✗ 不解决 Clay 千禧年问题；不声称连续极限（729 → ∞ / 步长 → 0）。
--   ✗ 六个轴的定义性修复**不**蕴含「离散 Δ 可逆」：Δ₆ 的核维数 275（真六轴）而非 0，
--     故离散 Leray 投影仍是条件存在（`PoissonSolvable` 那类前提不可省）。
--   ✓ 已证: 六轴 div∘grad = laplacian（定义性）、div 线性、nsStep6 的条件不可压保持、
--           六轴 ≢ 三轴复刻（构造性反例）、**对流项 adv1..adv6 / advField6**（§8，2026-10-20）。
--   ✗ 未证: 无条件不可压保持（前提 `laplacian6 f x ≡ T₀` 全局成立**是假的**，见 §7）。
--
-- 依赖: Sovereign.Base.Trit （GF(3) 环公理）。为使「六轴 vs 三轴」的判别引理
--   不受上游缺陷定义影响，本模块**不 import** 上游 NSEOnT6 —— 其中的通用 GF(3)
--   求和引理（sumN-distrib / sum6-+）在 §3 本地重导一遍（与轴分配无关）。
-- 0 postulate / 0 hole / 0 sorry

module Sovereign.Application.Problems.NavierStokes.NSEOnT6SixAxis where

open import Data.List using (List; []; _∷_; length; zipWith)
open import Data.Nat using (ℕ; zero; suc; _≤_; z≤n; s≤s)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.Product using (_×_; _,_; proj₁; proj₂; Σ; ∃)
open import Relation.Nullary.Negation.Core using (¬_)
open import Relation.Binary.PropositionalEquality using
  (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst; module ≡-Reasoning)

open import Sovereign.Base.Trit using (
  Trit; T₀; T₁; T₂; _⊕_; _⊗_; negate;
  ⊕-identityˡ; ⊕-identityʳ; ⊕-comm; ⊕-assoc; ⊕-inverse; negate²)

--------------------------------------------------------------------------------
-- §1. 载体: T⁶ = (Z/3)⁶, 标量场与六分量速度场
--
-- 注: Fin 的 zero/suc 在此重命名为 fzero/fsuc, 与 ℕ 的 zero/suc 并存不产生歧义
--     (C 类指纹预防)。
--------------------------------------------------------------------------------

C3 : Set
C3 = Fin 3

-- 轴索引: **六个**轴（Q5 修复的核心 —— 上游用 Fin 3 只覆盖三个轴）
Axis6 : Set
Axis6 = Fin 6

-- 六个具名轴
a0 a1 a2 a3 a4 a5 : Axis6
a0 = fzero
a1 = fsuc fzero
a2 = fsuc (fsuc fzero)
a3 = fsuc (fsuc (fsuc fzero))
a4 = fsuc (fsuc (fsuc (fsuc fzero)))
a5 = fsuc (fsuc (fsuc (fsuc (fsuc fzero))))

Torus6 : Set
Torus6 = C3 × C3 × C3 × C3 × C3 × C3

ScalarField : Set
ScalarField = Torus6 → Trit

Field : Set
Field = ScalarField × ScalarField × ScalarField
      × ScalarField × ScalarField × ScalarField

-- 六分量投影（右嵌套元组）
v1 v2 v3 v4 v5 v6 : Field → ScalarField
v1 (a , _) = a
v2 (_ , b , _) = b
v3 (_ , _ , c , _) = c
v4 (_ , _ , _ , d , _) = d
v5 (_ , _ , _ , _ , e , _) = e
v6 (_ , _ , _ , _ , _ , f) = f

mkField6 : ScalarField → ScalarField → ScalarField
         → ScalarField → ScalarField → ScalarField → Field
mkField6 a b c d e f = a , b , c , d , e , f

zeroS : ScalarField
zeroS = λ _ → T₀

zeroField6 : Field
zeroField6 = mkField6 zeroS zeroS zeroS zeroS zeroS zeroS

-- 点态相等（避免 funext）
_≈_ : ScalarField → ScalarField → Set
f ≈ g = ∀ x → f x ≡ g x

_+S_ : ScalarField → ScalarField → ScalarField
(f +S g) x = f x ⊕ g x

_+F6_ : Field → Field → Field
_+F6_ u v = mkField6
  (λ x → v1 u x ⊕ v1 v x) (λ x → v2 u x ⊕ v2 v x)
  (λ x → v3 u x ⊕ v3 v x) (λ x → v4 u x ⊕ v4 v x)
  (λ x → v5 u x ⊕ v5 v x) (λ x → v6 u x ⊕ v6 v x)

--------------------------------------------------------------------------------
-- §2. 六轴离散微分算子
--
-- 六项求和一律右嵌套:  sum6 a b c d e f = a ⊕ (b ⊕ (c ⊕ (d ⊕ (e ⊕ (f ⊕ T₀)))))
-- 尾部 T₀ 使分配律只需逐层 ⊕-assoc（见 §3 sum6-+），无需 8 步重排链。
--------------------------------------------------------------------------------

sum6 : Trit → Trit → Trit → Trit → Trit → Trit → Trit
sum6 a b c d e f = a ⊕ (b ⊕ (c ⊕ (d ⊕ (e ⊕ (f ⊕ T₀)))))

-- 坐标级循环移位 0 → 1 → 2 → 0
shift3 : C3 → C3
shift3 fzero = fsuc fzero
shift3 (fsuc fzero) = fsuc (fsuc fzero)
shift3 (fsuc (fsuc fzero)) = fzero

-- **六轴**移位: 第 i 轴只动第 i 个坐标 (Q5 修复点)
shiftAt6 : Axis6 → Torus6 → Torus6
shiftAt6 fzero (x1 , x2 , x3 , x4 , x5 , x6) =
  shift3 x1 , x2 , x3 , x4 , x5 , x6
shiftAt6 (fsuc fzero) (x1 , x2 , x3 , x4 , x5 , x6) =
  x1 , shift3 x2 , x3 , x4 , x5 , x6
shiftAt6 (fsuc (fsuc fzero)) (x1 , x2 , x3 , x4 , x5 , x6) =
  x1 , x2 , shift3 x3 , x4 , x5 , x6
shiftAt6 (fsuc (fsuc (fsuc fzero))) (x1 , x2 , x3 , x4 , x5 , x6) =
  x1 , x2 , x3 , shift3 x4 , x5 , x6
shiftAt6 (fsuc (fsuc (fsuc (fsuc fzero)))) (x1 , x2 , x3 , x4 , x5 , x6) =
  x1 , x2 , x3 , x4 , shift3 x5 , x6
shiftAt6 (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))) (x1 , x2 , x3 , x4 , x5 , x6) =
  x1 , x2 , x3 , x4 , x5 , shift3 x6

shiftF6 : Axis6 → ScalarField → ScalarField
shiftF6 i f x = f (shiftAt6 i x)

diffF6 : Axis6 → ScalarField → ScalarField
diffF6 i f x = shiftF6 i f x ⊕ negate (f x)

-- 单轴二阶差分
axisLap6 : Axis6 → ScalarField → ScalarField
axisLap6 i f = diffF6 i (diffF6 i f)

-- 散度: 第 i 个分量沿**第 i 个轴**差分（i ↦ i 是双射 —— 修复的核心）
div6 : Field → ScalarField
div6 v x = sum6
  (diffF6 a0 (v1 v) x) (diffF6 a1 (v2 v) x) (diffF6 a2 (v3 v) x)
  (diffF6 a3 (v4 v) x) (diffF6 a4 (v5 v) x) (diffF6 a5 (v6 v) x)

-- 梯度: 六个分量各取自己的轴
grad6 : ScalarField → Field
grad6 f = mkField6
  (diffF6 a0 f) (diffF6 a1 f) (diffF6 a2 f)
  (diffF6 a3 f) (diffF6 a4 f) (diffF6 a5 f)

-- 六轴 Laplacian: 轴 0…5 各算**一次**
laplacian6 : ScalarField → ScalarField
laplacian6 f x = sum6
  (axisLap6 a0 f x) (axisLap6 a1 f x) (axisLap6 a2 f x)
  (axisLap6 a3 f x) (axisLap6 a4 f x) (axisLap6 a5 f x)

-- 不可压性: 散度点态为零
Incompressible6 : Field → Set
Incompressible6 v = ∀ x → div6 v x ≡ T₀

--------------------------------------------------------------------------------
-- §3. 代数恒等式（GF(3): 取负分配 / 差分线性 / 六项求和分配）
--------------------------------------------------------------------------------

negate-⊕ : ∀ a b → negate (a ⊕ b) ≡ negate a ⊕ negate b
negate-⊕ T₀ b = sym (⊕-identityˡ (negate b))
negate-⊕ T₁ T₀ = refl
negate-⊕ T₁ T₁ = refl
negate-⊕ T₁ T₂ = refl
negate-⊕ T₂ T₀ = refl
negate-⊕ T₂ T₁ = refl
negate-⊕ T₂ T₂ = refl

-- 差分的加法线性
diffF6-+S : ∀ i f g → diffF6 i (f +S g) ≈ (diffF6 i f +S diffF6 i g)
diffF6-+S i f g x = begin
  (f (shiftAt6 i x) ⊕ g (shiftAt6 i x)) ⊕ negate (f x ⊕ g x)
    ≡⟨ cong ((f (shiftAt6 i x) ⊕ g (shiftAt6 i x)) ⊕_) (negate-⊕ (f x) (g x)) ⟩
  (f (shiftAt6 i x) ⊕ g (shiftAt6 i x)) ⊕ (negate (f x) ⊕ negate (g x))
    ≡⟨ ⊕-assoc (f (shiftAt6 i x)) (g (shiftAt6 i x)) (negate (f x) ⊕ negate (g x)) ⟩
  f (shiftAt6 i x) ⊕ (g (shiftAt6 i x) ⊕ (negate (f x) ⊕ negate (g x)))
    ≡⟨ cong (f (shiftAt6 i x) ⊕_)
         (sym (⊕-assoc (g (shiftAt6 i x)) (negate (f x)) (negate (g x)))) ⟩
  f (shiftAt6 i x) ⊕ ((g (shiftAt6 i x) ⊕ negate (f x)) ⊕ negate (g x))
    ≡⟨ cong (f (shiftAt6 i x) ⊕_)
         (cong (_⊕ negate (g x)) (⊕-comm (g (shiftAt6 i x)) (negate (f x)))) ⟩
  f (shiftAt6 i x) ⊕ ((negate (f x) ⊕ g (shiftAt6 i x)) ⊕ negate (g x))
    ≡⟨ cong (f (shiftAt6 i x) ⊕_)
         (⊕-assoc (negate (f x)) (g (shiftAt6 i x)) (negate (g x))) ⟩
  f (shiftAt6 i x) ⊕ (negate (f x) ⊕ (g (shiftAt6 i x) ⊕ negate (g x)))
    ≡⟨ sym (⊕-assoc (f (shiftAt6 i x)) (negate (f x))
                    (g (shiftAt6 i x) ⊕ negate (g x))) ⟩
  (f (shiftAt6 i x) ⊕ negate (f x)) ⊕ (g (shiftAt6 i x) ⊕ negate (g x))
  ∎
  where open ≡-Reasoning

-- 长度索引求和（n 上递归；列表耗尽返回 T₀）
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

-- 分配律核心: 长度足够时 sumN 对 ⊕ 分配
sumN-distrib : ∀ n (xs ys : List Trit) → n ≤ length xs → n ≤ length ys →
  sumN n (zipWith _⊕_ xs ys) ≡ sumN n xs ⊕ sumN n ys
sumN-distrib zero xs ys p q = sym (⊕-identityˡ (sumN 0 ys))
sumN-distrib (suc n) (x ∷ xs) (y ∷ ys) (s≤s p) (s≤s q) =
  trans (cong ((x ⊕ y) ⊕_) (sumN-distrib n xs ys p q))
        (swap-mid x y (sumN n xs) (sumN n ys))

six-le : 6 ≤ 6
six-le = s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))

sum6-+ : ∀ a a' b b' c c' d d' e e' f f' →
  sum6 (a ⊕ a') (b ⊕ b') (c ⊕ c') (d ⊕ d') (e ⊕ e') (f ⊕ f')
    ≡ sum6 a b c d e f ⊕ sum6 a' b' c' d' e' f'
sum6-+ a a' b b' c c' d d' e e' f f' =
  sumN-distrib 6
    (a ∷ b ∷ c ∷ d ∷ e ∷ f ∷ []) (a' ∷ b' ∷ c' ∷ d' ∷ e' ∷ f' ∷ [])
    six-le six-le

--------------------------------------------------------------------------------
-- §4. 散度的加法线性（nsStep6 的不可压保持需要它）
--------------------------------------------------------------------------------

div6-+F6 : ∀ u v x → div6 (u +F6 v) x ≡ div6 u x ⊕ div6 v x
div6-+F6 u v x = begin
  div6 (u +F6 v) x
    ≡⟨ cong6f (diffF6-+S a0 (v1 u) (v1 v))
              (diffF6-+S a1 (v2 u) (v2 v))
              (diffF6-+S a2 (v3 u) (v3 v))
              (diffF6-+S a3 (v4 u) (v4 v))
              (diffF6-+S a4 (v5 u) (v5 v))
              (diffF6-+S a5 (v6 u) (v6 v)) x ⟩
  sum6 (diffF6 a0 (v1 u) x ⊕ diffF6 a0 (v1 v) x)
       (diffF6 a1 (v2 u) x ⊕ diffF6 a1 (v2 v) x)
       (diffF6 a2 (v3 u) x ⊕ diffF6 a2 (v3 v) x)
       (diffF6 a3 (v4 u) x ⊕ diffF6 a3 (v4 v) x)
       (diffF6 a4 (v5 u) x ⊕ diffF6 a4 (v5 v) x)
       (diffF6 a5 (v6 u) x ⊕ diffF6 a5 (v6 v) x)
    ≡⟨ sum6-+
         (diffF6 a0 (v1 u) x) (diffF6 a0 (v1 v) x)
         (diffF6 a1 (v2 u) x) (diffF6 a1 (v2 v) x)
         (diffF6 a2 (v3 u) x) (diffF6 a2 (v3 v) x)
         (diffF6 a3 (v4 u) x) (diffF6 a3 (v4 v) x)
         (diffF6 a4 (v5 u) x) (diffF6 a4 (v5 v) x)
         (diffF6 a5 (v6 u) x) (diffF6 a5 (v6 v) x) ⟩
  div6 u x ⊕ div6 v x
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
-- §5. 主定理: div₆ ∘ grad₆ = laplacian₆，及 nsStep6 的不可压保持
--------------------------------------------------------------------------------

-- 定义性相等: 梯度场的散度 = 六轴 Laplacian
--
-- 为什么是 refl: div6 的第 i 项是 diffF6 aᵢ (vᵢ (grad6 f))，
-- vᵢ (grad6 f) ≡ diffF6 aᵢ f（mkField6 的第 i 投影），故第 i 项 ≡ axisLap6 aᵢ f，
-- 与 laplacian6 的第 i 项**同一项**（同一个 aᵢ，不是别名）。
div-grad6 : ∀ f x → div6 (grad6 f) x ≡ laplacian6 f x
div-grad6 f x = refl

-- N-S 的离散「压力修正步」（与上游 nsStep 同形，但六个轴各自对应）
nsStep6 : Field → Field
nsStep6 v = v +F6 grad6 (div6 v)

-- 条件形式（与上游 ns-step-preserves-incompressible-conditional 同形）
--
-- 前提 `∀ f x → laplacian6 f x ≡ T₀` 是**全局**假设；它在 GF(3) 上为假
-- （见 §6 laplacian6-not-identically-zero），故此定理本身正确但前提不可满足。
-- 之所以两个版本都保留：与上游口径可比 + 给出真正可用的逐场版本（见下）。
ns-step6-preserves-incompressible-conditional :
  (∀ f x → laplacian6 f x ≡ T₀) → ∀ v → Incompressible6 v → Incompressible6 (nsStep6 v)
ns-step6-preserves-incompressible-conditional lap0 v incomp x = begin
  div6 (v +F6 grad6 (div6 v)) x
    ≡⟨ div6-+F6 v (grad6 (div6 v)) x ⟩
  div6 v x ⊕ div6 (grad6 (div6 v)) x
    ≡⟨ cong₂ _⊕_ (incomp x) (div-grad6 (div6 v) x) ⟩
  T₀ ⊕ laplacian6 (div6 v) x
    ≡⟨ cong (T₀ ⊕_) (lap0 (div6 v) x) ⟩
  T₀ ⊕ T₀
    ≡⟨ ⊕-identityˡ T₀ ⟩
  T₀
  ∎
  where open ≡-Reasoning

-- 可用形式: 前提收窄到**这一条轨道的这一项**（不是全局恒零）
--
-- 前提 `∀ x → laplacian6 (div6 v) x ≡ T₀` 即 div₆(grad₆(div₆ v)) = 0；
-- 它等价于「v 的散度是 Δ₆ 的核元素」。Δ₆ 核维数 275 ≠ 0，故该前提
-- **可满足**（例如 div6 v ≡ zeroS 时平凡成立），不像全局版那样被 §6 否证。
ns-step6-preserves-incompressible :
  ∀ v → Incompressible6 v
      → (∀ x → laplacian6 (div6 v) x ≡ T₀)
      → Incompressible6 (nsStep6 v)
ns-step6-preserves-incompressible v incomp lapv x = begin
  div6 (v +F6 grad6 (div6 v)) x
    ≡⟨ div6-+F6 v (grad6 (div6 v)) x ⟩
  div6 v x ⊕ div6 (grad6 (div6 v)) x
    ≡⟨ cong₂ _⊕_ (incomp x) (div-grad6 (div6 v) x) ⟩
  T₀ ⊕ laplacian6 (div6 v) x
    ≡⟨ cong (T₀ ⊕_) (lapv x) ⟩
  T₀ ⊕ T₀
    ≡⟨ ⊕-identityˡ T₀ ⟩
  T₀
  ∎
  where open ≡-Reasoning

-- 零场不可压（定义性）
zero-incompressible6 : Incompressible6 zeroField6
zero-incompressible6 x = refl

--------------------------------------------------------------------------------
-- §6. 判别引理: 六轴版 ≢ 三轴复刻版（构造性反例，非数值计算）
--
-- `div-grad6 = refl` 只说明三处写法自洽；它**不能**说明轴分配正确
-- （上游的 `div-grad = refl` 在缺陷下同样成立）。这里给出真正有判别力的证据：
-- 三轴复刻版（把上游 C3 = Fin 3 的轴分配在六轴词汇下重写一遍）在某个具体场上
-- 给出不同的值，差值由 T₁ ≢ T₀ 判定。
--
-- 复刻版的定义（**仅用于比较，不参与主定理**）:
--   · laplacian3Replica: 轴 a0,a1,a2 各算**两次**（上游 laplacian 的原样）
--   · div3Replica     : 分量 4,5,6 复用轴 a0,a1,a2（上游 div 的原样）
--------------------------------------------------------------------------------

-- 三轴复刻版 Laplacian（上游 laplacian 的轴分配）
laplacian3Replica : ScalarField → ScalarField
laplacian3Replica f x = sum6
  (axisLap6 a0 f x) (axisLap6 a1 f x) (axisLap6 a2 f x)
  (axisLap6 a0 f x) (axisLap6 a1 f x) (axisLap6 a2 f x)

-- 三轴复刻版散度（上游 div 的轴分配）
div3Replica : Field → ScalarField
div3Replica v x = sum6
  (diffF6 a0 (v1 v) x) (diffF6 a1 (v2 v) x) (diffF6 a2 (v3 v) x)
  (diffF6 a0 (v4 v) x) (diffF6 a1 (v5 v) x) (diffF6 a2 (v6 v) x)

origin6 : Torus6
origin6 = fzero , fzero , fzero , fzero , fzero , fzero

-- 第 4 坐标上的单点源 δ_{e₄}: 在 (0,0,0,1,0,0) 取 T₁, 其余 T₀
delta-e4 : ScalarField
delta-e4 (fzero , fzero , fzero , fsuc fzero , fzero , fzero) = T₁
delta-e4 _ = T₀

-- δ_{e₄} 只非零于 x₄ 方向 —— 只有**第 4 个轴（a3）**能看到它
laplacian6-delta-e4 : laplacian6 delta-e4 origin6 ≡ T₁
laplacian6-delta-e4 = refl

-- 三轴复刻版看不到 x₄ 方向（它只摸 a0,a1,a2）
laplacian3Replica-delta-e4 : laplacian3Replica delta-e4 origin6 ≡ T₀
laplacian3Replica-delta-e4 = refl

T1≢T0 : T₁ ≢ T₀
T1≢T0 ()

-- 判别定理 ①: 六轴 laplacian ≢ 三轴复刻（存在见证）
laplacian6≢laplacian3Replica : ¬ (∀ f x → laplacian6 f x ≡ laplacian3Replica f x)
laplacian6≢laplacian3Replica h = T1≢T0
  (trans (sym laplacian6-delta-e4)
    (trans (h delta-e4 origin6) laplacian3Replica-delta-e4))

-- 只非零于 v₄ 分量的场（用于判别 div6）
field4 : Field
field4 = mkField6 zeroS zeroS zeroS delta-e4 zeroS zeroS

div6-field4 : div6 field4 origin6 ≡ T₁
div6-field4 = refl

div3Replica-field4 : div3Replica field4 origin6 ≡ T₀
div3Replica-field4 = refl

-- 判别定理 ②: 六轴 div ≢ 三轴复刻（存在见证）
div6≢div3Replica : ¬ (∀ v x → div6 v x ≡ div3Replica v x)
div6≢div3Replica h = T1≢T0
  (trans (sym div6-field4) (trans (h field4 origin6) div3Replica-field4))

--------------------------------------------------------------------------------
-- §7. 六个轴确实互不相同 + 离散 Δ 恒零为假（诚实边界的形式化）
--------------------------------------------------------------------------------

-- 第 i 轴移位有周期 3（C₃ 作用，逐轴成立）
shift3-cubed : ∀ x → shift3 (shift3 (shift3 x)) ≡ x
shift3-cubed fzero = refl
shift3-cubed (fsuc fzero) = refl
shift3-cubed (fsuc (fsuc fzero)) = refl

shiftAt6-cubed : ∀ i x → shiftAt6 i (shiftAt6 i (shiftAt6 i x)) ≡ x
shiftAt6-cubed fzero (x1 , x2 , x3 , x4 , x5 , x6) =
  cong (λ z → z , x2 , x3 , x4 , x5 , x6) (shift3-cubed x1)
shiftAt6-cubed (fsuc fzero) (x1 , x2 , x3 , x4 , x5 , x6) =
  cong (λ z → x1 , z , x3 , x4 , x5 , x6) (shift3-cubed x2)
shiftAt6-cubed (fsuc (fsuc fzero)) (x1 , x2 , x3 , x4 , x5 , x6) =
  cong (λ z → x1 , x2 , z , x4 , x5 , x6) (shift3-cubed x3)
shiftAt6-cubed (fsuc (fsuc (fsuc fzero))) (x1 , x2 , x3 , x4 , x5 , x6) =
  cong (λ z → x1 , x2 , x3 , z , x5 , x6) (shift3-cubed x4)
shiftAt6-cubed (fsuc (fsuc (fsuc (fsuc fzero)))) (x1 , x2 , x3 , x4 , x5 , x6) =
  cong (λ z → x1 , x2 , x3 , x4 , z , x6) (shift3-cubed x5)
shiftAt6-cubed (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))) (x1 , x2 , x3 , x4 , x5 , x6) =
  cong (λ z → x1 , x2 , x3 , x4 , x5 , z) (shift3-cubed x6)

-- 第 4 坐标投影
x4Of : Torus6 → C3
x4Of (_ , _ , _ , d , _ , _) = d

-- 轴 a3 与轴 a0 是**不同的**变换：在原点处，a3 动 x₄，a0 动 x₁
-- （上游三轴版里 a3 根本不存在；若强行写成 a3 ↦ a0，此引理即为假 —— 即 Q5 的实质）
axis3≠axis0 : shiftAt6 a3 origin6 ≢ shiftAt6 a0 origin6
axis3≠axis0 h =
  fsuc≢fzero (trans (sym a3-x4) (trans (cong x4Of h) a0-x4))
  where
    fsuc≢fzero : fsuc fzero ≢ fzero
    fsuc≢fzero ()

    a3-x4 : x4Of (shiftAt6 a3 origin6) ≡ fsuc fzero
    a3-x4 = refl

    a0-x4 : x4Of (shiftAt6 a0 origin6) ≡ fzero
    a0-x4 = refl

-- 离散 Laplacian **不**恒零（与上游 §4d 的 lap-zero-false 同一结论，六轴词汇重述）
laplacian6-not-identically-zero : ¬ (∀ f x → laplacian6 f x ≡ T₀)
laplacian6-not-identically-zero h =
  T1≢T0 (trans (sym laplacian6-delta-e4) (h delta-e4 origin6))

--------------------------------------------------------------------------------
-- §8. 对流项（T2 移植，2026-10-20）
--
-- 数学内容：离散对流 `adv_i = Σ_j v_j ⊗ D_j v_i`
--   （`NSEOnT6.agda:542` 的原始定义；本模块按六轴 1-1 对应重写）
-- 与上游 Q5 缺陷版的差别：第 j 个求和项用**第 j 个轴**的差分，六轴互不相同；
--   上游 `C3 = Fin 3` 版会让第 4,5,6 项复用轴 0,1,2。
--
-- 说明（与 `NSEPresentation.agda:367` 的关系）：那边的 `adv6` 定义在
-- `PresField`（幅度×相位）载体上；本模块载体是纯幅度 `Trit`，
-- 故这里是**同一定义在幅度层的重写**，不是逐字复制。
--
-- 含：advAt / adv1..adv6 / advField6 + 分量投影 + 零场判定
--------------------------------------------------------------------------------

-- 一般式：`advAt v w = Σ_j v_j ⊗ D_j w`，取 `w = v_i` 即得 `adv_i`
advAt : Field → ScalarField → ScalarField
advAt v w x = sum6
  (v1 v x ⊗ diffF6 a0 w x)
  (v2 v x ⊗ diffF6 a1 w x)
  (v3 v x ⊗ diffF6 a2 w x)
  (v4 v x ⊗ diffF6 a3 w x)
  (v5 v x ⊗ diffF6 a4 w x)
  (v6 v x ⊗ diffF6 a5 w x)

adv1 adv2 adv3 adv4 adv5 adv6 : Field → ScalarField
adv1 v = advAt v (v1 v)
adv2 v = advAt v (v2 v)
adv3 v = advAt v (v3 v)
adv4 v = advAt v (v4 v)
adv5 v = advAt v (v5 v)
adv6 v = advAt v (v6 v)

-- 对流速度场
advField6 : Field → Field
advField6 v = mkField6 (adv1 v) (adv2 v) (adv3 v) (adv4 v) (adv5 v) (adv6 v)

-- 分量投影（逐点 `refl`）
v1-advField6 : ∀ v → v1 (advField6 v) ≈ adv1 v
v1-advField6 v x = refl

v6-advField6 : ∀ v → v6 (advField6 v) ≈ adv6 v
v6-advField6 v x = refl

-- 零场的对流为零（`T₀ ⊗ _ ≡ T₀` 逐点成立）
adv6-zero : ∀ x → adv6 zeroField6 x ≡ T₀
adv6-zero x = refl

--------------------------------------------------------------------------------
-- §9. 非零调和场（T3 第一步，2026-10-20）
--
-- 见证：`f(x) = x₁`（只取第一个坐标的值，作为 Trit）。
-- 为什么调和：`laplacian6 = Σ_j P_j`，其中 `P_j f = f + S_j f + S_j² f`（沿第 j 轴取轨道和）。
--   · j ≥ 2：`f` 不含 `x_j` ⇒ `P_j f = 3f ≡ T₀`（特征 3）
--   · j = 1：`P_1 f = x₁ ⊕ (x₁⊕1) ⊕ (x₁⊕2) = 3x₁ ⊕ 3 ≡ T₀`
-- ⇒ `Δ f = Σ_j T₀ ≡ T₀`，但 `f ≠ 0`（在 x₁ = 1 处取 T₁）。
--
-- 关键：`proj1f` 忽略 x₂…x₆ ⇒ 只需对 **x₁** 分 3 个情形，无需 729 穷举。
--------------------------------------------------------------------------------

-- 坐标值：C3 → Trit
coord : C3 → Trit
coord fzero               = T₀
coord (fsuc fzero)        = T₁
coord (fsuc (fsuc fzero)) = T₂

-- 只取第一个坐标的标量场
proj1f : ScalarField
proj1f (x1 , x2 , x3 , x4 , x5 , x6) = coord x1

-- 主引理：`laplacian6 proj1f ≡ T₀` 逐点成立（对 x₁ 三分，其余保持变量）
lap-proj1f-zero :
  ∀ (x1 x2 x3 x4 x5 x6 : C3) →
    laplacian6 proj1f (x1 , x2 , x3 , x4 , x5 , x6) ≡ T₀
lap-proj1f-zero fzero                x2 x3 x4 x5 x6 = refl
lap-proj1f-zero (fsuc fzero)         x2 x3 x4 x5 x6 = refl
lap-proj1f-zero (fsuc (fsuc fzero))  x2 x3 x4 x5 x6 = refl

-- 非零性见证点
nonzero-point : Torus6
nonzero-point = fsuc fzero , fzero , fzero , fzero , fzero , fzero

proj1f-nonzero : proj1f nonzero-point ≢ T₀
proj1f-nonzero ()

-- ★ 非零调和场存在
harmonic-nonzero :
  Σ ScalarField (λ f → (∀ x → laplacian6 f x ≡ T₀) × (∃ λ x → f x ≢ T₀))
harmonic-nonzero = proj1f
  , (λ { (x1 , x2 , x3 , x4 , x5 , x6) → lap-proj1f-zero x1 x2 x3 x4 x5 x6 })
  , (nonzero-point , proj1f-nonzero)

--------------------------------------------------------------------------------
-- §10. 核非平凡 ⇒ Poisson 解不唯一（T3 第二步，2026-10-20）
--
-- §9 给了 `ker Δ₆ ≠ {0}`。由**线性性**即得：`p` 解 `Δ p ≡ g`、`h` 调和
-- ⇒ `p +S h` 也是解 ⇒ 压力解**不唯一**。
--
-- 关键前置：`⊕-assoc x y z : (x ⊕ y) ⊕ z ≡ x ⊕ (y ⊕ z)`（**左嵌套在左**，别记反 ✗）。
--------------------------------------------------------------------------------

-- `(a ⊕ b) ⊕ (c ⊕ d) ≡ (a ⊕ c) ⊕ (b ⊕ d)`（五步，方向按 `⊕-assoc` 真签名）
sum4-shuffle : ∀ a b c d → (a ⊕ b) ⊕ (c ⊕ d) ≡ (a ⊕ c) ⊕ (b ⊕ d)
sum4-shuffle a b c d = begin
    (a ⊕ b) ⊕ (c ⊕ d)
  ≡⟨ ⊕-assoc a b (c ⊕ d) ⟩
    a ⊕ (b ⊕ (c ⊕ d))
  ≡⟨ cong (a ⊕_) (sym (⊕-assoc b c d)) ⟩
    a ⊕ ((b ⊕ c) ⊕ d)
  ≡⟨ cong (λ z → a ⊕ (z ⊕ d)) (⊕-comm b c) ⟩
    a ⊕ ((c ⊕ b) ⊕ d)
  ≡⟨ cong (a ⊕_) (⊕-assoc c b d) ⟩
    a ⊕ (c ⊕ (b ⊕ d))
  ≡⟨ sym (⊕-assoc a c (b ⊕ d)) ⟩
    (a ⊕ c) ⊕ (b ⊕ d)
  ∎
  where
    open ≡-Reasoning

-- 单轴二阶差分的线性性
axisLap6-+S : ∀ i f g → axisLap6 i (f +S g) ≈ (axisLap6 i f +S axisLap6 i g)
axisLap6-+S i f g x = begin
    axisLap6 i (f +S g) x
  ≡⟨ cong₂ (λ p q → p ⊕ negate q)
           (diffF6-+S i f g (shiftAt6 i x)) (diffF6-+S i f g x) ⟩
    (diffF6 i f (shiftAt6 i x) ⊕ diffF6 i g (shiftAt6 i x))
      ⊕ negate (diffF6 i f x ⊕ diffF6 i g x)
  ≡⟨ cong (λ z → (diffF6 i f (shiftAt6 i x) ⊕ diffF6 i g (shiftAt6 i x)) ⊕ z)
          (negate-⊕ (diffF6 i f x) (diffF6 i g x)) ⟩
    (diffF6 i f (shiftAt6 i x) ⊕ diffF6 i g (shiftAt6 i x))
      ⊕ (negate (diffF6 i f x) ⊕ negate (diffF6 i g x))
  ≡⟨ sum4-shuffle (diffF6 i f (shiftAt6 i x)) (diffF6 i g (shiftAt6 i x))
                  (negate (diffF6 i f x)) (negate (diffF6 i g x)) ⟩
    (diffF6 i f (shiftAt6 i x) ⊕ negate (diffF6 i f x))
      ⊕ (diffF6 i g (shiftAt6 i x) ⊕ negate (diffF6 i g x))
  ∎
  where
    open ≡-Reasoning

--------------------------------------------------------------------------------
-- §11. `laplacian6` 线性性 + Poisson 解不唯一（T3 收口，2026-10-20）
--------------------------------------------------------------------------------

-- 六元同余（Trit 层；`div6-+F6` 里的同名 helper 是局部 where 绑定，未导出）
cong6-Trit : ∀ {a b c d e f a' b' c' d' e' f' : Trit}
  → a ≡ a' → b ≡ b' → c ≡ c' → d ≡ d' → e ≡ e' → f ≡ f'
  → sum6 a b c d e f ≡ sum6 a' b' c' d' e' f'
cong6-Trit refl refl refl refl refl refl = refl

-- 六轴 Laplacian 线性性
laplacian6-+S : ∀ f g → laplacian6 (f +S g) ≈ (laplacian6 f +S laplacian6 g)
laplacian6-+S f g x =
  trans (cong6-Trit (axisLap6-+S a0 f g x) (axisLap6-+S a1 f g x)
                    (axisLap6-+S a2 f g x) (axisLap6-+S a3 f g x)
                    (axisLap6-+S a4 f g x) (axisLap6-+S a5 f g x))
        (sum6-+ (axisLap6 a0 f x) (axisLap6 a0 g x)
                (axisLap6 a1 f x) (axisLap6 a1 g x)
                (axisLap6 a2 f x) (axisLap6 a2 g x)
                (axisLap6 a3 f x) (axisLap6 a3 g x)
                (axisLap6 a4 f x) (axisLap6 a4 g x)
                (axisLap6 a5 f x) (axisLap6 a5 g x))

-- 调和场对加法封闭（核是子空间）
harmonic-closed :
  ∀ f g → (∀ x → laplacian6 f x ≡ T₀) → (∀ x → laplacian6 g x ≡ T₀) →
    ∀ x → laplacian6 (f +S g) x ≡ T₀
harmonic-closed f g hf hg x =
  trans (laplacian6-+S f g x) (trans (cong₂ _⊕_ (hf x) (hg x)) refl)

-- ★ 解不唯一：Poisson 解 ⊕ 调和场仍是解
poisson-solution-add-harmonic :
  ∀ (g p h : ScalarField) →
    (∀ x → laplacian6 p x ≡ g x) → (∀ x → laplacian6 h x ≡ T₀) →
    ∀ x → laplacian6 (p +S h) x ≡ g x
poisson-solution-add-harmonic g p h hp hh x =
  trans (laplacian6-+S p h x)
        (trans (cong₂ _⊕_ (hp x) (hh x)) (⊕-identityʳ (g x)))

-- `a ⊕ b ≡ a ⇒ b ≡ T₀`（GF(3) 加法消去，三分）
⊕-cancel-zero : ∀ a b → a ⊕ b ≡ a → b ≡ T₀
⊕-cancel-zero T₀ T₀ refl = refl
⊕-cancel-zero T₁ T₀ refl = refl
⊕-cancel-zero T₂ T₀ refl = refl

-- `proj1f` 逐点调和（把 §9 的六坐标版本转成元组形式）
proj1f-harmonic : ∀ x → laplacian6 proj1f x ≡ T₀
proj1f-harmonic (x1 , x2 , x3 , x4 , x5 , x6) = lap-proj1f-zero x1 x2 x3 x4 x5 x6

-- ★★ T3 主定理：Poisson 解**不唯一**——任何解都能加非零调和场扰动
poisson-nonunique :
  ∀ (g p : ScalarField) → (∀ x → laplacian6 p x ≡ g x) →
    ∃ (λ p' → (∀ x → laplacian6 p' x ≡ g x) × (∃ λ x → p' x ≢ p x))
poisson-nonunique g p hp =
    (p +S proj1f)
  , (poisson-solution-add-harmonic g p proj1f hp proj1f-harmonic)
  , (nonzero-point , λ eq → proj1f-nonzero (⊕-cancel-zero (p nonzero-point) (proj1f nonzero-point) eq))

--------------------------------------------------------------------------------
-- §12. 秩核的结构框架（T4 第一步，2026-10-20）
--
-- 为什么秩是可算的：`laplacian6 = Σ_j (沿第 j 轴逐线求和)`。
--   `lineSum j f x = f x ⊕ f(x+e_j) ⊕ f(x+2e_j)`   （整条线求和）
-- 这是 `Δ` 的**张量/线分解**：`M_j` 把每条方向-j 的线（3 点）压成一个和。
--
-- 由此立即可得的关键结构：`M_j ∘ M_j = 3·M_j ≡ 0`（特征 3）
--   —— 这是「6 个互相垂直的幂零块」，也是 rank 454 的来源。
--
-- ⚠ 精确 rank = 454 / ker = 275 的形式化需要 GF(3) 上的秩-零化度定理 +
--   线/面计数（729 点、243×6 条线）—— 见 `RESEARCH.nse-rank-kernel` 的诚实边界。
--   当前 oracle 回执 `dae6f7dc` 已用**精确整数行化简**证实该数字 ✓。
--------------------------------------------------------------------------------

-- `a ⊕ a ⊕ a ≡ T₀`（特征 3 的三倍零）
⊕-triple-zero : ∀ a → a ⊕ (a ⊕ (a ⊕ T₀)) ≡ T₀
⊕-triple-zero T₀ = refl
⊕-triple-zero T₁ = refl
⊕-triple-zero T₂ = refl

-- 坐标级三次移位回到原点
shift3-3 : ∀ a → shift3 (shift3 (shift3 a)) ≡ a
shift3-3 fzero               = refl
shift3-3 (fsuc fzero)        = refl
shift3-3 (fsuc (fsuc fzero)) = refl

-- 六轴通用：三次 shift 回到原点
shiftAt6-3 : ∀ i x → shiftAt6 i (shiftAt6 i (shiftAt6 i x)) ≡ x
shiftAt6-3 fzero (x1 , x2 , x3 , x4 , x5 , x6) =
  cong (λ z → z , x2 , x3 , x4 , x5 , x6) (shift3-3 x1)
shiftAt6-3 (fsuc fzero) (x1 , x2 , x3 , x4 , x5 , x6) =
  cong (λ z → x1 , z , x3 , x4 , x5 , x6) (shift3-3 x2)
shiftAt6-3 (fsuc (fsuc fzero)) (x1 , x2 , x3 , x4 , x5 , x6) =
  cong (λ z → x1 , x2 , z , x4 , x5 , x6) (shift3-3 x3)
shiftAt6-3 (fsuc (fsuc (fsuc fzero))) (x1 , x2 , x3 , x4 , x5 , x6) =
  cong (λ z → x1 , x2 , x3 , z , x5 , x6) (shift3-3 x4)
shiftAt6-3 (fsuc (fsuc (fsuc (fsuc fzero)))) (x1 , x2 , x3 , x4 , x5 , x6) =
  cong (λ z → x1 , x2 , x3 , x4 , z , x6) (shift3-3 x5)
shiftAt6-3 (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))) (x1 , x2 , x3 , x4 , x5 , x6) =
  cong (λ z → x1 , x2 , x3 , x4 , x5 , z) (shift3-3 x6)

-- 沿第 i 轴**整条线**求和：M_j f (x) = f x ⊕ f(x+e_j) ⊕ f(x+2e_j)
lineSum : Axis6 → ScalarField → ScalarField
lineSum i f x = f x ⊕ (shiftF6 i f x ⊕ shiftF6 i (shiftF6 i f) x)

-- 三循环坍缩：`(a⊕b⊕c) ⊕ (b⊕c⊕a) ⊕ (c⊕a⊕b) ≡ T₀`（27 个构造子情形，≤27 可穷举）
-- 这是 `M_j² = 3·M_j ≡ 0` 的算术核心。
cycle3 : ∀ a b c → (a ⊕ (b ⊕ c)) ⊕ ((b ⊕ (c ⊕ a)) ⊕ (c ⊕ (a ⊕ b))) ≡ T₀
cycle3 T₀ T₀ T₀ = refl
cycle3 T₀ T₀ T₁ = refl
cycle3 T₀ T₀ T₂ = refl
cycle3 T₀ T₁ T₀ = refl
cycle3 T₀ T₁ T₁ = refl
cycle3 T₀ T₁ T₂ = refl
cycle3 T₀ T₂ T₀ = refl
cycle3 T₀ T₂ T₁ = refl
cycle3 T₀ T₂ T₂ = refl
cycle3 T₁ T₀ T₀ = refl
cycle3 T₁ T₀ T₁ = refl
cycle3 T₁ T₀ T₂ = refl
cycle3 T₁ T₁ T₀ = refl
cycle3 T₁ T₁ T₁ = refl
cycle3 T₁ T₁ T₂ = refl
cycle3 T₁ T₂ T₀ = refl
cycle3 T₁ T₂ T₁ = refl
cycle3 T₁ T₂ T₂ = refl
cycle3 T₂ T₀ T₀ = refl
cycle3 T₂ T₀ T₁ = refl
cycle3 T₂ T₀ T₂ = refl
cycle3 T₂ T₁ T₀ = refl
cycle3 T₂ T₁ T₁ = refl
cycle3 T₂ T₁ T₂ = refl
cycle3 T₂ T₂ T₀ = refl
cycle3 T₂ T₂ T₁ = refl
cycle3 T₂ T₂ T₂ = refl

-- 三次 shift 在函数层的点态形式
shiftF6-3 : ∀ i f → shiftF6 i (shiftF6 i (shiftF6 i f)) ≈ f
shiftF6-3 i f x = cong f (shiftAt6-3 i x)

-- ★ `M_j ∘ M_j = 3·M_j ≡ 0`（特征 3）：线算子的幂零性
lineSum-sq : ∀ i f x → lineSum i (lineSum i f) x ≡ T₀
lineSum-sq i f x
  rewrite shiftAt6-3 i x
  = cycle3 (f x) (f (shiftAt6 i x)) (f (shiftAt6 i (shiftAt6 i x)))

-- 三值算术核（27 情形）：`D(Df)` 与「整条线求和」在 `a=f x, b=f sx, c=f ssx` 下相等
--   LHS = (c ⊕ negate b) ⊕ negate (b ⊕ negate a)   （二阶前向差分的展开）
--   RHS = a ⊕ (b ⊕ c)                             （整条线求和）
lap3-eq : ∀ (a b c : Trit) → (c ⊕ negate b) ⊕ negate (b ⊕ negate a) ≡ (a ⊕ (b ⊕ c))
lap3-eq T₀ T₀ T₀ = refl
lap3-eq T₀ T₀ T₁ = refl
lap3-eq T₀ T₀ T₂ = refl
lap3-eq T₀ T₁ T₀ = refl
lap3-eq T₀ T₁ T₁ = refl
lap3-eq T₀ T₁ T₂ = refl
lap3-eq T₀ T₂ T₀ = refl
lap3-eq T₀ T₂ T₁ = refl
lap3-eq T₀ T₂ T₂ = refl
lap3-eq T₁ T₀ T₀ = refl
lap3-eq T₁ T₀ T₁ = refl
lap3-eq T₁ T₀ T₂ = refl
lap3-eq T₁ T₁ T₀ = refl
lap3-eq T₁ T₁ T₁ = refl
lap3-eq T₁ T₁ T₂ = refl
lap3-eq T₁ T₂ T₀ = refl
lap3-eq T₁ T₂ T₁ = refl
lap3-eq T₁ T₂ T₂ = refl
lap3-eq T₂ T₀ T₀ = refl
lap3-eq T₂ T₀ T₁ = refl
lap3-eq T₂ T₀ T₂ = refl
lap3-eq T₂ T₁ T₀ = refl
lap3-eq T₂ T₁ T₁ = refl
lap3-eq T₂ T₁ T₂ = refl
lap3-eq T₂ T₂ T₀ = refl
lap3-eq T₂ T₂ T₁ = refl
lap3-eq T₂ T₂ T₂ = refl

-- ★ 单轴二阶差分 = 整条线求和（框架的最后一环）
axisLap6-eq-lineSum : ∀ i f x → axisLap6 i f x ≡ lineSum i f x
axisLap6-eq-lineSum i f x =
  lap3-eq (f x) (f (shiftAt6 i x)) (f (shiftAt6 i (shiftAt6 i x)))

-- ★★ 框架完成：`laplacian6` 就是 6 个线算子之和
lineForm6 : ∀ f x → laplacian6 f x ≡
  sum6 (lineSum a0 f x) (lineSum a1 f x) (lineSum a2 f x)
       (lineSum a3 f x) (lineSum a4 f x) (lineSum a5 f x)
lineForm6 f x =
  cong6-Trit (axisLap6-eq-lineSum a0 f x) (axisLap6-eq-lineSum a1 f x)
             (axisLap6-eq-lineSum a2 f x) (axisLap6-eq-lineSum a3 f x)
             (axisLap6-eq-lineSum a4 f x) (axisLap6-eq-lineSum a5 f x)
