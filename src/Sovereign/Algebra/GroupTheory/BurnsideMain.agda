{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Algebra.GroupTheory.BurnsideMain
--
-- **Burnside（Cauchy–Frobenius）引理**的收口：把块 1（双重计数）、块 2（共轭不变）
-- 与块 3（轨道划分 + 通用纤维分解）组装成乘法形式的定理。
--
--        n · #orbits  ≡  Σ_x |Stab x|        （块 3 主定理）
--   Σ_g |Fix g|  ≡  Σ_x |Stab x|             （块 1，Burnside.agda）
--   ⟹  Σ_g |Fix g|  ≡  n · #orbits          （经典形式）
--
-- 数学背景与**为什么用乘法形式**：
--   等式两边都是 ℕ 计数。写成 #orbits = Σ_x |Stab x| / n 会要求先交出整除见证，
--   而「n ∣ Σ_x |Stab x|」正是 Burnside 要证的结论本身 —— 循环依赖；
--   且 ℕ 的 _/_ 是截断除法，没有见证就无法把除法形式回推成乘法形式。
--   乘法形式与已有接口天然对齐：
--     · 块 2 给的是 |Stab (g·x)| ≡ |Stab x|（等式）
--     · orbit-stabilizer-auto 给的是 |Orbit a| · |Stab a| ≡ |G|（乘式）
--     · 通用纤维分解给的是 Σ_x f (L x) ≡ Σ_y |fiber_y| · f y（乘式）
--   三条都是乘法/等式形状，整除性作为**推论**自动落地。所以「绕开除法」不是技巧，
--   是唯一不需要循环依赖的陈述形状。
--
-- 证明架构（四步，全部复用已有件）：
--   ① Σ_x |Stab x| ≡ Σ_x |Stab (orbRep x)|        块 2 拉平（stabSize-conj）
--   ②        ≡ Σ_x |Stab (toFin RepEnum (orbLabel x))|   orbLabel-ok
--   ③        ≡ Σ_y |fiber_y| · |Stab (toFin RepEnum y)|  通用纤维分解 sumFin-fiber
--   ④        ≡ Σ_y n ≡ #orbits · n                fiberSizeEqOrbit + orbit-stabilizer-auto
--
-- 核心原则：
--   1. **不重造**：群代数（assoc / inverseˡ / identityˡ / inv-inv）取 FinGroup 字段；
--      双射 ⇒ 基数相等用 stdlib cantor-schröder-bernstein；子类型枚举用 CosetAuto.SubEnum；
--      本节真正新写的只有「共轭把 |Stab| 沿轨道拉平」与「纤维 = 轨道」两处
--   2. **自动构造**：orbit-stabilizer 用自动版（只喂 G、A、a），不手工传 8 个假设
--   3. 0 postulate / 0 hole；无 funExt；trans 嵌套浅，每步一个具名引理
--   4. **对抗验证**（§4）：定理在具体作用上的数字与独立 refl 计算逐位比对 ——
--      含一个**非传递**实例（平凡作用，Fin 3，#orbits = 3），这是唯一能测出
--      numOrbits ≠ 1 的情形，防止「传递作用碰巧对上」
--
-- 诚实边界：
--   作用是有限集 Fin p 上的（#orbits 才有限）；不声称无限作用或拓扑群的 Burnside。
--   #orbits 的定义取「轨道内 toℕ 最小元」作判据 —— 换判据结论不变，本模块不证这一点。
--
-- 包含：stabSize-orbRep / orbStab / fiber-stab-eq / chain / burnside-main /
--       burnside-classical / numOrbitsOf / burnside-lemma / §4 对抗验证

module Sovereign.Algebra.GroupTheory.BurnsideMain where

open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; module ≡-Reasoning)

open import Sovereign.Algebra.GroupTheory.Lagrange using (FinGroup; C4)
open import Sovereign.Algebra.GroupTheory.OrbitStabilizer
  using (Action; C4-regular; C4-parity)
open import Sovereign.Algebra.GroupTheory.CosetAuto using (SubEnum)
open import Sovereign.Algebra.GroupTheory.OrbitStabilizerAuto
  using (orb-enum; stab-enum; orbit-stabilizer-auto)
open import Sovereign.Algebra.GroupTheory.Burnside
  using (sumFin; sumFin-cong; stabSize; stabCount; fixCount; stabSize-conj;
         burnside-double-count)
open import Sovereign.Algebra.GroupTheory.BurnsideFiber
  using (sumFin-const; sumFin-fiber; fiberSize)
open import Sovereign.Algebra.GroupTheory.OrbitPartition
  using (module OrbitPart)

open import Data.Nat.Properties using (*-comm)

--------------------------------------------------------------------------------
-- 组装
--------------------------------------------------------------------------------

module Assembly {n p : ℕ} (G : FinGroup n) (A : Action G (Fin p)) where
  open OrbitPart G A
  open FinGroup G
  open Action A
  open ≡-Reasoning

  -- 块 2（stabSize-conj）把同一轨道内各点的 |Stab| 拉平：
  -- x 与 orbRep x 同轨道，故 x 可由某个 g 把 orbRep x 送过去
  stabSize-orbRep : ∀ x → stabSize G A x ≡ stabSize G A (orbRep x)
  stabSize-orbRep x =
    trans (cong (stabSize G A) (sym (proj₂ (orbRep-eq x))))
          (stabSize-conj G A (proj₁ (orbRep-eq x)) (orbRep x))

  -- orbit-stabilizer-auto 的乘法形式（自动版只喂 G、A、a 三个参数）
  orbStab : ∀ (a : Fin p) → SubEnum.size (orbEnum a) * stabSize G A a ≡ n
  orbStab a = proj₂ (proj₂ (orbit-stabilizer-auto G A a))

  -- 每个轨道标签 y 的贡献恰为 n（第 4 步）
  fiber-stab-eq : ∀ (y : Fin numOrbits)
                → fiberSize orbLabel y * stabSize G A (SubEnum.toFin RepEnum y) ≡ n
  fiber-stab-eq y = begin
    fiberSize orbLabel y * stabSize G A (SubEnum.toFin RepEnum y)
      ≡⟨ cong (_* stabSize G A (SubEnum.toFin RepEnum y)) (fiberSizeEqOrbit y) ⟩
    SubEnum.size (orbEnum (SubEnum.toFin RepEnum y))
      * stabSize G A (SubEnum.toFin RepEnum y)
      ≡⟨ orbStab (SubEnum.toFin RepEnum y) ⟩
    n ∎

  chain : stabCount G A ≡ numOrbits * n
  chain = begin
    stabCount G A
      ≡⟨ sumFin-cong (λ x → stabSize-orbRep x) ⟩
    sumFin (λ x → stabSize G A (orbRep x))
      ≡⟨ sumFin-cong (λ x → cong (stabSize G A) (sym (orbLabel-ok x))) ⟩
    sumFin (λ x → stabSize G A (SubEnum.toFin RepEnum (orbLabel x)))
      ≡⟨ sumFin-fiber orbLabel (λ y → stabSize G A (SubEnum.toFin RepEnum y)) ⟩
    sumFin (λ y → fiberSize orbLabel y * stabSize G A (SubEnum.toFin RepEnum y))
      ≡⟨ sumFin-cong (λ y → fiber-stab-eq y) ⟩
    sumFin (λ (_ : Fin numOrbits) → n)
      ≡⟨ sumFin-const {numOrbits} n ⟩
    numOrbits * n ∎

  -- 块 3 主定理：乘法形式（不用除法，无循环依赖）
  burnside-main : n * numOrbits ≡ stabCount G A
  burnside-main = trans (*-comm n numOrbits) (sym chain)

  -- 经典 Burnside：Σ_g |Fix g| ≡ n · #orbits（块 1 收口）
  burnside-classical : fixCount G A ≡ n * numOrbits
  burnside-classical = trans (burnside-double-count G A) (sym burnside-main)

--------------------------------------------------------------------------------
-- 顶层入口
--------------------------------------------------------------------------------

numOrbitsOf : ∀ {n p} (G : FinGroup n) (A : Action G (Fin p)) → ℕ
numOrbitsOf G A = OrbitPart.numOrbits G A

burnside-lemma : ∀ {n p} (G : FinGroup n) (A : Action G (Fin p))
               → n * numOrbitsOf G A ≡ stabCount G A
burnside-lemma G A = Assembly.burnside-main G A

burnside-classical : ∀ {n p} (G : FinGroup n) (A : Action G (Fin p))
                   → fixCount G A ≡ n * numOrbitsOf G A
burnside-classical G A = Assembly.burnside-classical G A

--------------------------------------------------------------------------------
-- §4. 对抗验证：具体点 refl 交叉比对
--
-- 定理在具体作用上算出的数字，必须与**独立** refl 计算逐位一致 —— 这是发现论证
-- 空洞的唯一可靠手段（块 1 / 块 2 沿用的协议）。三个实例覆盖两种 #orbits：
--   ① 正则作用（传递，#orbits = 1）
--   ② 奇偶作用（传递，#orbits = 1）
--   ③ 平凡作用（**非传递**，#orbits = 3）—— 唯一能测出 numOrbits ≠ 1 的情形
--------------------------------------------------------------------------------

-- C₄ 在 Fin 3 上的平凡作用（既非传递也非自由：每条轨道是单点）
C4-trivial : Action C4 (Fin 3)
C4-trivial = record
  { _·_ = λ _ x → x
  ; ·-ε = λ x → refl
  ; ·-⊙ = λ g h x → refl
  }

-- ① 正则作用
reg-numOrbits : numOrbitsOf C4 C4-regular ≡ 1
reg-numOrbits = refl

reg-stabCount : stabCount C4 C4-regular ≡ 4
reg-stabCount = refl

reg-agree : 4 * 1 ≡ 4
reg-agree = burnside-lemma C4 C4-regular

-- ② 奇偶作用（稳定子 {0,2} 阶 2，两个点共 2 + 2 = 4）
par-numOrbits : numOrbitsOf C4 C4-parity ≡ 1
par-numOrbits = refl

par-stabCount : stabCount C4 C4-parity ≡ 4
par-stabCount = refl

par-agree : 4 * 1 ≡ 4
par-agree = burnside-lemma C4 C4-parity

-- ③ 非传递实例：三条单点轨道，每点稳定子 = 全群（阶 4），总计 3 × 4 = 12
triv-numOrbits : numOrbitsOf C4 C4-trivial ≡ 3
triv-numOrbits = refl

triv-stabCount : stabCount C4 C4-trivial ≡ 12
triv-stabCount = refl

triv-agree : 4 * 3 ≡ 12
triv-agree = burnside-lemma C4 C4-trivial

-- ④ 经典形式与块 1 的交叉一致（Σ_g |Fix g| 独立算出也是 12）
triv-fixCount : fixCount C4 C4-trivial ≡ 12
triv-fixCount = refl

triv-classical : fixCount C4 C4-trivial ≡ 4 * 3
triv-classical = burnside-classical C4 C4-trivial
