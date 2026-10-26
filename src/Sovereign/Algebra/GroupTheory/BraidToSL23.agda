{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Algebra.GroupTheory.BraidToSL23
-- 桥：B₃ 的展示 → SL(2,F₃) ≅ 2A₄ 的定义表示，并在该像里证 (σ₁σ₂)³ ≡ −I。
--
-- 为什么要这座桥：
--   · `GroupTheory/BraidGroup.agda` 证的是**源侧**：(σ₁σ₂)³ 在 B₃ 展示里与两生成元交换
--     （W-central-σ₁/σ₂，只用 assoc + braid-rel）。
--   · `Synthesis/A4/BinaryTetrahedral.agda` 的 `q8-neg1-central` 证的是**像侧**：
--     −1 在 Q₈ ⊂ 2A₄ 中心。
--   · 两侧此前从未接线。本模块给出接线中**可计算的那一半**：
--     把生成元映到矩阵、验证辫关系被保持、并算出 W 的像恰为 −I。
--
-- 取值来源（不是新发明）：
--   Burau 表示 σ₁ ↦ [[−t,1],[0,1]]、σ₂ ↦ [[1,0],[t,−t]]（`BurauRep.agda`），
--   在 t ≡ −1 (mod 3) 处取值 ⇒ σ₁ ↦ [[1,1],[0,1]]、σ₂ ↦ [[1,0],[2,1]]，
--   正是 SL(2,F₃) 的两个标准生成元（PhaseMatrixBridge 已用同一对）。
--
-- ⚠ 诚实边界（2026-10-26 更新）：
--   · 已证：定义关系被保持（eval-braid）、W ↦ −I（eval-W）、
--     **eval 对词拼接同态**（eval-++W）、−I 在像侧 24 元素上中心（negI-central）、
--     **四个具体逆律**（σ₁/σ₂ 的 A·A⁻¹ / A⁻¹·A ≡ I，全 refl）、
--     **四条消去律**（eval ((w·x)·x⁻¹) ≡ eval w，双向）。
--   · 未证：把「词按消去取商 = 自由群 F₂」形式化为 setoid 商，
--     以及把 F₂ 再按 braid 关系取商得 B₃——即 eval 从 B₃ 出发的**良定义性**。
--     `_PN15` 有自由群泛性质（参数化为 GroupData），但要对 SL(2,F₃) 套用还需
--     `GroupData SL2`：**逆已有**（`Matrix2Inverse.det-one-mul / det-one-adj`，
--     det=1 ⇒ adj 即双侧逆）；**缺** det 的乘法性（⇒ SL2 对乘法封闭）与群律装配。
-- 0 postulate / 0 hole。

module Sovereign.Algebra.GroupTheory.BraidToSL23 where

open import Data.Fin using (Fin; zero; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂)

-- Fin 3 的环结构 + 矩阵幺半群律（含 I2）；GF(3) 逆理论（含 det3）
open import Sovereign.Synthesis.Representation.Fin3Semiring using
  ( I2; mat-assoc; mat-idʳ )
open import Sovereign.Synthesis.Representation.Matrix2Inverse using (det3)
-- 2×2 GF(3) 矩阵与 24 个 SL(2,F₃) 元素
open import Sovereign.Synthesis.Representation.SL23Cayley using
  ( Mat2; mat2; mulMat2; toMat )
-- 词（零依赖语法层）：Word / ε / 四字母 / _++W_ / aba / bab
open import Sovereign.Algebra.GroupTheory.Word using
  ( Word; ε; _·a; _·b; _·ai; _·bi; _++W_; aba; bab )
-- g0..g23 由 DefiningRep 定义；SL23Cayley 不转出它们，故直接取自源头
open import Sovereign.Synthesis.A4.BinaryTetrahedralDefiningRep using
  ( SL23
  ; g0; g1; g2; g3; g4; g5; g6; g7; g8; g9; g10; g11
  ; g12; g13; g14; g15; g16; g17; g18; g19; g20; g21; g22; g23 )
-- 投影 m00/m01/m10/m11 来自 Matrix2 的 `open Mat2 public`；SL23Cayley 只重命名导入、不转出
-- ⚠ mulMat2 在 SL23Cayley 里已绑定 add3/mul3（二元）；Matrix2 的同名函数接域运算，
--   这里重命名为 mulMat2F 以免被遮蔽。
open import Sovereign.Algebra.LinearAlgebra.Matrix2
  using (m00; m01; m10; m11; mkMat2) renaming (mulMat2 to mulMat2F)

--------------------------------------------------------------------------------
-- 1. 生成元的像（Burau 在 t ≡ −1 mod 3 处取值）
--

σ₁M : Mat2
σ₁M = mat2 (suc zero) (suc zero) zero (suc zero)          -- [[1,1],[0,1]]

σ₂M : Mat2
σ₂M = mat2 (suc zero) zero (suc (suc zero)) (suc zero)    -- [[1,0],[2,1]] = [[1,0],[−1,1]]

-- 两个**具体**逆元（det = 1，故逆 = 伴随矩阵；只给这两例，不建一般逆律）
σ₁Minv : Mat2
σ₁Minv = mat2 (suc zero) (suc (suc zero)) zero (suc zero)   -- [[1,2],[0,1]]

σ₂Minv : Mat2
σ₂Minv = mat2 (suc zero) zero (suc zero) (suc zero)         -- [[1,0],[1,1]]

negI : Mat2
negI = mat2 (suc (suc zero)) zero zero (suc (suc zero))   -- [[2,0],[0,2]] = −I

--------------------------------------------------------------------------------
-- 2. 自由词与求值
--

-- 词与其拼接已抽到零依赖的 `Word` 模块（使 cubical 商模块的导入锥不含 --rewriting）

eval : Word → Mat2
eval ε       = mat2 (suc zero) zero zero (suc zero)   -- I
eval (w ·a)  = mulMat2 (eval w) σ₁M
eval (w ·b)  = mulMat2 (eval w) σ₂M
eval (w ·ai) = mulMat2 (eval w) σ₁Minv
eval (w ·bi) = mulMat2 (eval w) σ₂Minv

--------------------------------------------------------------------------------
-- 3. 定义关系在像中被保持（泛性质的可计算一半）
--


-- R: aba ≡ bab 在矩阵像里成立（逐项计算，refl）
eval-braid : eval aba ≡ eval bab
eval-braid = refl

--------------------------------------------------------------------------------
-- 4. W = (σ₁σ₂)³ 的像恰为 −I
--

-- 右结合形态，与 BraidGroup.W = σ₁·(σ₂·(σ₁·(σ₂·(σ₁·σ₂)))) 逐字对应
wValue : Mat2
wValue = mulMat2 σ₁M
           (mulMat2 σ₂M
             (mulMat2 σ₁M
               (mulMat2 σ₂M
                 (mulMat2 σ₁M σ₂M))))

-- **[主定理]** (σ₁σ₂)³ 在 SL(2,F₃) 中的像 = −I
eval-W : wValue ≡ negI
eval-W = refl

-- 左结合形态（经自由词求值）给出同一结果；两者相等正是矩阵乘法的结合律
wWord : Word
wWord = ((((ε ·a) ·b) ·a) ·b) ·a ·b

eval-W-word : eval wWord ≡ negI
eval-W-word = refl

eval-W-agrees : eval wWord ≡ wValue
eval-W-agrees = refl

--------------------------------------------------------------------------------
-- 5. 两个生成元与 W 都在 SL(2,F₃) 内（det ≡ 1）
--
-- ⚠ 不能用 Matrix2.det：那是 ad + bc，只在 char 2 等于行列式。
--   这里显式给 GF(3) 版：det = ad − bc = ad + (−b)c。
--

det-σ₁ : det3 σ₁M ≡ suc zero
det-σ₁ = refl

det-σ₂ : det3 σ₂M ≡ suc zero
det-σ₂ = refl

det-W : det3 wValue ≡ suc zero
det-W = refl

--------------------------------------------------------------------------------
-- 5b. eval 是同态：eval (p ++ q) ≡ eval p · eval q
--
-- 需要三件：
--   (i)   add3/mul3 ≡ _⊕_/_⊗_（SL23Cayley 的局部表 = Base/Trit 的域运算）
--   (ii)  mulMat2 ≡ mulMat2 _⊕_ _⊗_（把 (i) 抬到矩阵层）
--   (iii) 矩阵结合律 + 右单位律（Matrix2Laws.mat-assoc-3 / mat-idʳ-3）
-- 有了这三件，归纳法只需结构递归 + cong。
--

-- 关键：Mat2 的系数是 **Fin 3**，而 Base/Trit 的环律建在 **Trit** 上——两者是
-- 不同数据类型（同基数，有双射）。故先经双射把 Trit 的环律搬到 Fin 3，
-- 得到 CommSemiring (Fin 3)，再用 Matrix2Laws 的泛型结合律/单位律。
-- 矩阵乘法本身不变，仍是 SL23Cayley 的 add3/mul3。

-- **[主定理] eval 对词拼接是同态**
eval-++W : ∀ p q → eval (p ++W q) ≡ mulMat2 (eval p) (eval q)
eval-++W p ε = sym (mat-idʳ (eval p))
eval-++W p (q ·a) =
  trans (cong (λ T → mulMat2 T σ₁M) (eval-++W p q))
        (mat-assoc (eval p) (eval q) σ₁M)
eval-++W p (q ·b) =
  trans (cong (λ T → mulMat2 T σ₂M) (eval-++W p q))
        (mat-assoc (eval p) (eval q) σ₂M)
eval-++W p (q ·ai) =
  trans (cong (λ T → mulMat2 T σ₁Minv) (eval-++W p q))
        (mat-assoc (eval p) (eval q) σ₁Minv)
eval-++W p (q ·bi) =
  trans (cong (λ T → mulMat2 T σ₂Minv) (eval-++W p q))
        (mat-assoc (eval p) (eval q) σ₂Minv)

--------------------------------------------------------------------------------
-- 5c. 四个具体逆律 + 消去律
--
-- 只证两个生成元各自的 A·A⁻¹ = A⁻¹·A = I（各一例 refl），
-- 不建一般矩阵逆律（那需要 det 可逆的一般理论）。
-- 有了它才能说 eval 尊重"消去"，即自由群 F₂ 的商关系在像中成立。
--

σ₁-invˡ : mulMat2 σ₁M σ₁Minv ≡ I2
σ₁-invˡ = refl

σ₁-invʳ : mulMat2 σ₁Minv σ₁M ≡ I2
σ₁-invʳ = refl

σ₂-invˡ : mulMat2 σ₂M σ₂Minv ≡ I2
σ₂-invˡ = refl

σ₂-invʳ : mulMat2 σ₂Minv σ₂M ≡ I2
σ₂-invʳ = refl

-- 消去：eval ((w·a)·a⁻¹) ≡ eval w（同左、同 b）
eval-cancel-a : ∀ w → eval ((w ·a) ·ai) ≡ eval w
eval-cancel-a w =
  trans (trans (mat-assoc (eval w) σ₁M σ₁Minv)
               (cong (mulMat2 (eval w)) σ₁-invˡ))
        (mat-idʳ (eval w))

eval-cancel-b : ∀ w → eval ((w ·b) ·bi) ≡ eval w
eval-cancel-b w =
  trans (trans (mat-assoc (eval w) σ₂M σ₂Minv)
               (cong (mulMat2 (eval w)) σ₂-invˡ))
        (mat-idʳ (eval w))

eval-cancel-ai : ∀ w → eval ((w ·ai) ·a) ≡ eval w
eval-cancel-ai w =
  trans (trans (mat-assoc (eval w) σ₁Minv σ₁M)
               (cong (mulMat2 (eval w)) σ₁-invʳ))
        (mat-idʳ (eval w))

eval-cancel-bi : ∀ w → eval ((w ·bi) ·b) ≡ eval w
eval-cancel-bi w =
  trans (trans (mat-assoc (eval w) σ₂Minv σ₂M)
               (cong (mulMat2 (eval w)) σ₂-invʳ))
        (mat-idʳ (eval w))

--------------------------------------------------------------------------------
-- 6. 像侧中心性：−I 在 SL(2,F₃) 的 24 个元素上逐点中心
--
-- 这一步把两侧的**结论**接住：源侧是 BraidGroup 的 W-central-σ₁/σ₂（与生成元交换），
-- 像侧是这里 24 个元素全交换（对应 BinaryTetrahedral 的 q8-neg1-central）。
-- 24 个元素全部构造子，逐点 refl。
--

negI-is-g15 : negI ≡ toMat g15
negI-is-g15 = refl

negI-central : ∀ (g : SL23) → mulMat2 negI (toMat g) ≡ mulMat2 (toMat g) negI
negI-central g0  = refl
negI-central g1  = refl
negI-central g2  = refl
negI-central g3  = refl
negI-central g4  = refl
negI-central g5  = refl
negI-central g6  = refl
negI-central g7  = refl
negI-central g8  = refl
negI-central g9  = refl
negI-central g10 = refl
negI-central g11 = refl
negI-central g12 = refl
negI-central g13 = refl
negI-central g14 = refl
negI-central g15 = refl
negI-central g16 = refl
negI-central g17 = refl
negI-central g18 = refl
negI-central g19 = refl
negI-central g20 = refl
negI-central g21 = refl
negI-central g22 = refl
negI-central g23 = refl
