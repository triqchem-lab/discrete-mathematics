{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Algebra.LinearAlgebra.TensorRankRestrictGF3
-- M20: 限制界词汇——rows/cols/inner 完成集计数与零秩抽取
-- （镜像 Lean `Rectangle/Sparse/Model.lean:15-21`; 2609.06725 的下界证明对象,
--   立项 B-T2, 2026-11-26）
--
-- 数学背景
--   下界机制的词汇: 对加权张量 w（三元组上取值, 非零处称支撑）, 三个方向的
--   「完成集」计数——rows(t) = 与 t 同 (b,c) 的支撑格数, cols(t) = 同 (a,c),
--   inner(t) = 同 (a,b)。2609.06725（F₂ 上 3×3 ≥ 21）的证明对象正是
--   「限制界约束每个子空间里第一因子的个数」+ 陪集分析 + 穷举;
--   Lean 的 DegreeBound（Sparse/Law.lean）用的也是这三把尺子。
--
-- 内容
--   §1 完成集计数 suppRows / suppCols / suppInner（嵌套 ℕ 和, 镜像 Finset.filter .card）
--   §2 和的基本引理: sumℕ-const / sumℕ-one; 推论: 全 T₁ 加权的支撑数 = n³
--   §3 ★ 零秩抽取 weighted-zero: WeightedRankLE₃ n 0 w ⟹ w ≡ T₀（处处）
--      ——下界游戏的第一个约束: 0 项分解只剩零张量
--
-- 诚实边界
--   · Lean 的 conditional/premium（条件熵, Model.lean:29-37）要 ℝ 对数, 本库不做
--     （宪法排除）; 有限口径属立项 B-T3/B-T4。
--   · 陪集/子空间分析未镜像（2609.06725 的第二半）。
--
-- 复用(先查后写): suppInd/supportSize₃/wmm/WeightedRankLE₃（M19）、sumℕ（M18）、
--   oneIf-refl（M16-B）、oneIf（TensorRankGF3）。
--
-- 0 postulate / 0 REWRITE 规则 / 0 洞
module Sovereign.Algebra.LinearAlgebra.TensorRankRestrictGF3 where

open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
open import Data.Nat.Properties using (*-identityʳ; *-assoc)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; sym; cong; cong₂)

open import Sovereign.Base.Trit using (Trit; T₀; T₁; _⊗_; ⊗-identityˡ; ⊗-identityʳ)
open import Sovereign.Algebra.LinearAlgebra.TensorRankGF3
  using (RankLE₃; mm; Pos; Out; oneIf)
open import Sovereign.Algebra.LinearAlgebra.TensorRankFlattenGF3 using (oneIf-refl)
open import Sovereign.Algebra.LinearAlgebra.TensorRankSparseGF3
  using (WeightedRankLE₃; wmm; suppInd; supportSize₃)
open import Sovereign.Algebra.LinearAlgebra.TensorRankCircuitGF3 using (sumℕ)

--------------------------------------------------------------------------------
-- §1. 完成集计数（镜像 Lean Sparse/Model.lean 的 rows/cols/inner）
--------------------------------------------------------------------------------

-- 与 t = (a,b,c) 同 (b,c) 的支撑格数（变首指标）
suppRows : ∀ n → (Fin n → Fin n → Fin n → Trit) → Fin n → Fin n → Fin n → ℕ
suppRows n w a b c = sumℕ {n} (λ x → suppInd (w x b c))

-- 同 (a,c): 变第二指标
suppCols : ∀ n → (Fin n → Fin n → Fin n → Trit) → Fin n → Fin n → Fin n → ℕ
suppCols n w a b c = sumℕ {n} (λ y → suppInd (w a y c))

-- 同 (a,b): 变第三指标
suppInner : ∀ n → (Fin n → Fin n → Fin n → Trit) → Fin n → Fin n → Fin n → ℕ
suppInner n w a b c = sumℕ {n} (λ z → suppInd (w a b z))

--------------------------------------------------------------------------------
-- §2. 和的基本引理
--------------------------------------------------------------------------------

-- 常值和: Σ_{i<n} c = n * c（suc 情形: c + n*c 就是 suc n * c 的定义展开）
sumℕ-const : ∀ (n : ℕ) (c : ℕ) → sumℕ {n} (λ _ → c) ≡ n * c
sumℕ-const zero c = refl
sumℕ-const (suc n) c = cong (c +_) (sumℕ-const n c)

-- 单位和: Σ_{i<n} 1 = n
sumℕ-one : ∀ (n : ℕ) → sumℕ {n} (λ _ → suc zero) ≡ n
sumℕ-one n = trans (sumℕ-const n (suc zero)) (*-identityʳ n)

-- 全 T₁ 加权的支撑数 = n * n * n（对 n 归纳; 每层一次 sumℕ-const + 收尾单位律/结合律）
supportSize-allT₁ : ∀ n → supportSize₃ n (λ _ _ _ → T₁) ≡ n * n * n
supportSize-allT₁ zero = refl
supportSize-allT₁ (suc n) =
  trans (sumℕ-const (suc n) MID)
  (trans (cong (λ t → suc n * t) L2)
  (trans (cong (λ t → suc n * (suc n * t)) (*-identityʳ (suc n)))
         (sym (*-assoc (suc n) (suc n) (suc n)))))
  where
  INNER : ℕ
  INNER = sumℕ {suc n} (λ k → suppInd T₁)
  MID : ℕ
  MID = sumℕ {suc n} (λ j → INNER)
  L3 : INNER ≡ suc n * 1
  L3 = sumℕ-const (suc n) (suc zero)
  L2 : MID ≡ suc n * (suc n * 1)
  L2 = trans (sumℕ-const (suc n) INNER) (cong (λ t → suc n * t) L3)

--------------------------------------------------------------------------------
-- §3. ★ 零秩抽取: 0 项分解只剩零张量
--------------------------------------------------------------------------------

-- mm 在循环位 (a,c),(c,b),(a,b) 处的值是 T₁（三重 oneIf-refl + 双重左单位）
mm-cyclic : ∀ n (a b c : Fin n) → mm n (a , c) (c , b) (a , b) ≡ T₁
mm-cyclic n a b c =
  trans (cong (λ t → t ⊗ ((oneIf c c) ⊗ (oneIf b b))) (oneIf-refl a))
  (trans (cong (λ t → T₁ ⊗ t) (cong₂ _⊗_ (oneIf-refl c) (oneIf-refl b)))
         (trans (⊗-identityˡ (T₁ ⊗ T₁)) (⊗-identityˡ T₁)))

-- ★ WeightedRankLE₃ n 0 w ⟹ w ≡ T₀（处处）
--   取 x = (a,c), y = (c,b), z = (a,b): sumFin {0} = T₀ 落在 wmm 上,
--   而 wmm = w a b c ⊗ (mm 循环位) = w a b c ⊗ T₁ = w a b c
weighted-zero : ∀ n w → WeightedRankLE₃ n 0 w → ∀ a b c → w a b c ≡ T₀
weighted-zero n w hw a b c =
  trans (sym W-wmm) (sym H)
  where
  H : T₀ ≡ wmm n w (a , c) (c , b) (a , b)
  H = WeightedRankLE₃.wrank-eq hw (a , c) (c , b) (a , b)
  W-wmm : (w a b c) ⊗ (mm n (a , c) (c , b) (a , b)) ≡ w a b c
  W-wmm = trans (cong (λ t → (w a b c) ⊗ t) (mm-cyclic n a b c))
                (⊗-identityʳ (w a b c))
