{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Synthesis.Representation.SL2Bridge
-- **桥的最后一段**：把 `BraidToSL23` 的词层求值接到 setoid 泛性质上。
--
-- 四步（与计划 1→4 对应）：
--   ① det-eval       : eval 的每个词像行列式都是 1（否则落不进 SL2）
--   ② toWalk         : Word（5 构造子）→ Walk B(Bool)（语法翻译）
--   ③ 实例化         : SetoidUniversal 于 SL2-setoid-group，生成元 true↦σ₁, false↦σ₂
--   ④ SL2-uniqueness : 任何在生成元上一致的标架 φ 与 eval 逐点 ≈（商关系由 eval-braid 落实）
--
-- ⚠ 边界（必读，别过度声称）：
--   ④ 证明的是「**在走层**（`Walk B(Bool)`）上，任何满足生成元/同态约束的 φ 都与 eval 一致」。
--   它**不等于**「存在从 B₃ 商群到 SL2 的群同态」——后者需要**商群的泛性质**
--   （把关系 `aba ≈ bab` 生成的同余取商），库里尚无该件（`_PN15` 只有自由群）。
--   已证到的是：给定「φ 在生成元上与 eval 相同」，则 φ 与 eval 处处相同——
--   这正是把 B₃ 的表示「识别为」eval 所需的那一步，扣掉商的那一半。
--
-- 策略：结构递归 + setoid 替换（每项 ≤3 步）+ 复用（det-mul3 / det-one-* / uniqueness）
-- 0 postulate / 0 hole。

module Sovereign.Synthesis.Representation.SL2Bridge where

open import Data.Bool using (Bool; true; false)
open import Data.Fin using (Fin; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂)

-- 语法层：走与 B(Bool) 的边
open import Sovereign.Synthesis.Homotopy.BarceloAHomotopy using (Walk; nil; cons; _++w_)
open import _PN15 using (BEdge; fwd; bwd; BA; SetoidGroupData)

-- setoid 泛性质 + SL2 的 setoid 群
open import Sovereign.Synthesis.Representation.SetoidFreeGroupUniversal using ()
open import Sovereign.Synthesis.Representation.SL2SetoidGroup using
  ( SL2; _≈s_; sl2-mul; sl2-e; sl2-inv; SL2-setoid-group )

-- 矩阵侧：det 的乘法性、adj、det
open import Sovereign.Synthesis.Representation.Matrix2DetMul using (det-mul3)
open import Sovereign.Synthesis.Representation.Matrix2Inverse using (det3; adj)
open import Sovereign.Synthesis.Representation.SL23Cayley using (Mat2; mulMat2; mul3)

-- 词与词层求值
-- 词来自零依赖的 Word 模块；求值来自桥模块
open import Sovereign.Algebra.GroupTheory.Word using
  ( Word; ε; _·a; _·b; _·ai; _·bi )
open import Sovereign.Algebra.GroupTheory.BraidToSL23 using
  ( σ₁M; σ₂M; σ₁Minv; σ₂Minv; det-σ₁; det-σ₂ )
  renaming (eval to evalW)
-- 词层求值改名 evalW，把 `eval` 让给 setoid 泛性质
open SetoidGroupData SL2-setoid-group

--------------------------------------------------------------------------------
-- ① 逆元的行列式（两个具体逆，各一例 refl）
--------------------------------------------------------------------------------

det-σ₁Minv : det3 σ₁Minv ≡ suc zero
det-σ₁Minv = refl

det-σ₂Minv : det3 σ₂Minv ≡ suc zero
det-σ₂Minv = refl

-- eval 的像恒在 SL(2,F₃)：每一步都用 det-mul3 + 生成元 det = 1
det-eval : ∀ w → det3 (evalW w) ≡ suc zero
det-eval ε       = refl
det-eval (w ·a)  = trans (det-mul3 (evalW w) σ₁M)
                         (trans (cong₂ mul3 (det-eval w) det-σ₁) refl)
det-eval (w ·b)  = trans (det-mul3 (evalW w) σ₂M)
                         (trans (cong₂ mul3 (det-eval w) det-σ₂) refl)
det-eval (w ·ai) = trans (det-mul3 (evalW w) σ₁Minv)
                         (trans (cong₂ mul3 (det-eval w) det-σ₁Minv) refl)
det-eval (w ·bi) = trans (det-mul3 (evalW w) σ₂Minv)
                         (trans (cong₂ mul3 (det-eval w) det-σ₂Minv) refl)

--------------------------------------------------------------------------------
-- ② 语法翻译：Word → Walk B(Bool)
--------------------------------------------------------------------------------

toWalk : Word → Walk (BA Bool) tt tt
toWalk ε        = nil tt
toWalk (w ·a)   = toWalk w ++w cons (fwd true)  (nil tt)
toWalk (w ·b)   = toWalk w ++w cons (fwd false) (nil tt)
toWalk (w ·ai)  = toWalk w ++w cons (bwd true)  (nil tt)
toWalk (w ·bi)  = toWalk w ++w cons (bwd false) (nil tt)

--------------------------------------------------------------------------------
-- ③ 生成元：true ↦ σ₁，false ↦ σ₂（含 det = 1 证明，故落在 SL2）
--------------------------------------------------------------------------------

σ₁S : SL2
σ₁S = σ₁M , det-σ₁

σ₂S : SL2
σ₂S = σ₂M , det-σ₂

gen : Bool → SL2
gen true  = σ₁S
gen false = σ₂S

-- ⚠ 必须写在 gen 之后：Agda 顺序作用域，参数化模块的 open 不能前向引用
open Sovereign.Synthesis.Representation.SetoidFreeGroupUniversal.SetoidUniversal
     SL2-setoid-group gen

-- adj 与显式逆元逐字相等（两例 refl）
adj-σ₁ : adj σ₁M ≡ σ₁Minv
adj-σ₁ = refl

adj-σ₂ : adj σ₂M ≡ σ₂Minv
adj-σ₂ = refl

--------------------------------------------------------------------------------
-- ④ 一致性：词层 eval 与 setoid 泛性质的 eval 逐点相同
--------------------------------------------------------------------------------

-- ⚠ 证明用 `_≡_` 层的 `trans`/`cong₂`：`_≈_` 定义上就是 `proj₁ _ ≡ proj₁ _`，
--   直接展开可绕过 setoid 组合子的隐式参数（`trans≈` 的 `{y}` 在中性项上无法确定）。
eval-coherence : ∀ w → eval (toWalk w) ≈ (evalW w , det-eval w)
eval-coherence ε = refl
eval-coherence (w ·a) =
  trans (eval-++w (toWalk w) (cons (fwd true) (nil tt)))
    (trans (cong₂ mulMat2 (eval-coherence w) refl) refl)
eval-coherence (w ·b) =
  trans (eval-++w (toWalk w) (cons (fwd false) (nil tt)))
    (trans (cong₂ mulMat2 (eval-coherence w) refl) refl)
eval-coherence (w ·ai) =
  trans (eval-++w (toWalk w) (cons (bwd true) (nil tt)))
    (trans (cong₂ mulMat2 (eval-coherence w) adj-σ₁) refl)
eval-coherence (w ·bi) =
  trans (eval-++w (toWalk w) (cons (bwd false) (nil tt)))
    (trans (cong₂ mulMat2 (eval-coherence w) adj-σ₂) refl)

-- 唯一性（直接引用 setoid 泛性质）
SL2-uniqueness : (φ : Walk (BA Bool) tt tt → SL2)
               → φ (nil tt) ≈ sl2-e
               → (∀ b → φ (cons (fwd b) (nil tt)) ≈ gen b)
               → (∀ b → φ (cons (bwd b) (nil tt)) ≈ sl2-inv (gen b))
               → (∀ p q → φ (p ++w q) ≈ sl2-mul (φ p) (φ q))
               → (p : Walk (BA Bool) tt tt)
               → φ p ≈ eval p
SL2-uniqueness = uniqueness
