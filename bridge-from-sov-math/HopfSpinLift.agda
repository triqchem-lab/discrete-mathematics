{-# OPTIONS --cubical --rewriting --guardedness #-}

-- | HopfSpinLift — 把 HopfConstruction 的 A₄ 作用提升到 2A₄（相位与 Hopf 投影等变对齐）
--
-- 问题：A₄（12 胞腔球面的对称群）没有 4 阶元，而相位 C₄ 需要 4 阶。
--   4 阶元只存在于双重覆盖 2A₄ = SL(2,3)（库内 BinaryTetrahedral: `q8-i⁴`）。
-- 构造：把全空间升为 **自旋全空间** SpinTotal = TotalSpace × GF(3)²，
--   2A₄ 按 2 维定义表示 ρ 作用在 GF(3)² 上，按 π 作用在底上：
--     phaseAct (x , v) = (a4Action g x , ρ(R) · v)
--   其中 R = [[0,2],[1,0]] 是 2A₄ 的 4 阶元（RotBridge），g = π(R) 是 A₄ 的 2 阶元。
--
-- 证明（4 条）：
--   ① phaseAct⁴ ≡ id        （ρ(R)⁴ = I，且 g² = Id）
--   ② phaseAct² ≢ id        （ρ(R)² = 2I ≠ I —— 自旋部分翻转，正是双重覆盖的非平凡性）
--   ③ 等变对齐: totalProj ∘ fst ∘ phaseAct ≡ totalProj ∘ fst
--      （相位作用保持 A₄ 轨道 ⇒ 投影到底空间不变；相位是纤维/自旋自由度，不是轨道置换）
--   ④ det ρ(R) = 1           （ρ(R) ∈ SL(2,3) = 2A₄，见 RotBridge.R-det-is-1）
--
-- 诚实边界：本模块以「g 是 A₄ 的 2 阶元」为**参数假设**（存在性显然：A₄ 的 3 个双对换，
--   见 A4Group）；未在本模块内构造具体 g 并证其阶为 2 —— 这属于 A4Group 侧的实例化。
module HopfSpinLift where

open import Data.Fin using (Fin; zero; suc; toℕ)
open import Data.Vec using (Vec; _∷_; [])
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Empty using (⊥)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality
  renaming (_≡_ to _≡i_; refl to refli; cong to congi; sym to symi; trans to transi; cong₂ to congi₂)
open import Cubical.Foundations.Prelude using (_≡_; refl)

open import Sovereign.Base.Trit using (Trit; T₀; T₁; T₂; _⊕_; _⊗_; negate)
import Sovereign.Synthesis.Homotopy.HopfConstruction as H
import Sovereign.Synthesis.Combinatorics.T6 as T6
import Sovereign.Synthesis.A4.A4Group as A4
import RotBridge as RB

--------------------------------------------------------------------------------
-- §1. 自旋坐标：GF(3)² 与 2A₄ 的 2 维表示
--------------------------------------------------------------------------------

Spin : Set
Spin = Trit × Trit

-- 2×2 GF(3) 矩阵作用（复用 RotBridge 的 Mat2/mulM；此处直接给 apply）
applyM : RB.Mat2 → Spin → Spin
applyM A (x , y) = ( (RB.m00 A ⊗ x) ⊕ (RB.m01 A ⊗ y)
                   , (RB.m10 A ⊗ x) ⊕ (RB.m11 A ⊗ y) )

-- ρ(R) 的 4 阶性（RotBridge §5）
R²≡2I : RB.mulM RB.R RB.R ≡i RB.negIM
R²≡2I = RB.R²≡2I

R⁴≡I : RB.mulM (RB.mulM RB.R RB.R) (RB.mulM RB.R RB.R) ≡i RB.idM
R⁴≡I = RB.R⁴≡I

--------------------------------------------------------------------------------
-- §2. 自旋全空间与相位作用
--------------------------------------------------------------------------------

SpinTotal : Set
SpinTotal = H.TotalSpace × Spin

-- | 相位作用: 底上按 A₄ 的 g 作用，自旋上按 ρ(R) 作用
phaseAct : (g : A4.A4) → SpinTotal → SpinTotal
phaseAct g (x , v) = (T6.a4Action g x , applyM RB.R v)

-- 底投影: 取 A₄ 轨道
spinProj : SpinTotal → H.Base
spinProj s = H.totalProj (proj₁ s)

--------------------------------------------------------------------------------
-- §3. ① 四次回位（需要 g 的平方 = A₄ 单位）
--------------------------------------------------------------------------------

-- 以参数形式给出「g 是 2 阶元」：A₄ 中双对换满足 g² = Id（实例化见 A4Group）
phaseAct⁴≡id : (g : A4.A4)
             → (g² : ∀ x → T6.a4Action g (T6.a4Action g x) ≡i x)
             → ∀ s → (let s1 = phaseAct g s in
                      let s2 = phaseAct g s1 in
                      let s3 = phaseAct g s2 in
                      phaseAct g s3) ≡i s
phaseAct⁴≡id g g² (x , v) = path
  where
    -- 四次旋转的矩阵作用 = I（GF(3) 上逐分量 refl）
    v4 : ∀ (w : Spin) → applyM RB.R (applyM RB.R (applyM RB.R (applyM RB.R w))) ≡i w
    v4 (T₀ , T₀) = refli
    v4 (T₀ , T₁) = refli
    v4 (T₀ , T₂) = refli
    v4 (T₁ , T₀) = refli
    v4 (T₁ , T₁) = refli
    v4 (T₁ , T₂) = refli
    v4 (T₂ , T₀) = refli
    v4 (T₂ , T₁) = refli
    v4 (T₂ , T₂) = refli
    -- 四次作用后底上回位 (g² 用两次)，自旋上回位 (v4)
    y : H.TotalSpace
    y = T6.a4Action g (T6.a4Action g x)

    p-base : T6.a4Action g (T6.a4Action g (T6.a4Action g (T6.a4Action g x))) ≡i x
    p-base = transi (g² y) (g² x)

    path : ( T6.a4Action g (T6.a4Action g (T6.a4Action g (T6.a4Action g x)))
           , applyM RB.R (applyM RB.R (applyM RB.R (applyM RB.R v))) ) ≡i (x , v)
    path = congi₂ _,_ p-base (v4 v)

--------------------------------------------------------------------------------
-- §3.5 实例化：g = A4.Flip zero（双对换 (0 1)(2 3)，2 阶元）—— 不再作为假设
--------------------------------------------------------------------------------

g0 : A4.A4
g0 = A4.Flip zero

-- 二次作用 = 恒等（置换的平方；控制流在类型检查器里归约，refl）
a4Action-twice : ∀ (x : H.TotalSpace) → T6.a4Action g0 (T6.a4Action g0 x) ≡i x
a4Action-twice (v₀ ∷ v₁ ∷ v₂ ∷ v₃ ∷ v₄ ∷ v₅ ∷ []) = refli

-- | 相位作用四次回位（**无参数假设**，g₀ 的具体阶已由 a4Action-twice 给出）
phaseAct⁴≡id-inst : ∀ s → (let s1 = phaseAct g0 s in
                           let s2 = phaseAct g0 s1 in
                           let s3 = phaseAct g0 s2 in
                           phaseAct g0 s3) ≡i s
phaseAct⁴≡id-inst = phaseAct⁴≡id g0 a4Action-twice

--------------------------------------------------------------------------------
-- §4. ② 平方非恒等（立即可见：自旋部分被翻转）
--------------------------------------------------------------------------------

-- R² = 2I ⇒ 对 v = (T₁, T₀) 作用得 (T₂, T₀) ≠ (T₁, T₀)
phaseAct²-nontrivial : ¬ (applyM RB.R (applyM RB.R (T₁ , T₀)) ≡i (T₁ , T₀))
phaseAct²-nontrivial ()
  where
    -- 2I 作用: (x,y) ↦ (2x, 2y)，在 (T₁,T₀) 上得 (T₂,T₀)
    unfold : applyM RB.R (applyM RB.R (T₁ , T₀)) ≡i (T₂ , T₀)
    unfold = refli

--------------------------------------------------------------------------------
-- §5. ③ 等变对齐：相位作用不改变 A₄ 轨道 ⇒ 投影到底空间不变
--------------------------------------------------------------------------------

phase-equivariant : (g : A4.A4) (s : SpinTotal)
                  → spinProj (phaseAct g s) ≡ spinProj s
phase-equivariant g (x , v) = H.action-in-orbit g x

--------------------------------------------------------------------------------
-- §6. ④ det ρ(R) = 1（R ∈ SL(2,3) = 2A₄）
--------------------------------------------------------------------------------

detR≡1 : RB.detM RB.R ≡i T₁
detR≡1 = RB.R-det-is-1
