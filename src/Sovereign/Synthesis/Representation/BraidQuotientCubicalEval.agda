{-# OPTIONS --cubical --rewriting --guardedness #-}

-- | Sovereign.Synthesis.Representation.BraidQuotientCubicalEval
-- **把 eval 下降到商 `B3 = Word / ≈b`**：`eval-B3 : B3 → Mat2`，
-- 并验证它在代表词上与 `eval` 一致（rec 的 β）。
--
-- 与 `BraidQuotientRec.resp` 的区别（本件的价值所在）：
--   · `resp` 是「φ 逐点尊重 ≈b」——点式命题；商只是"等价类"的说法；
--   · 本件给的是 `B3 → Mat2` 这个**函数**，商是**类型**，
--     且 `eval-B3 [ w ] ≡ eval w` 是 refl。泛性质因此可以陈述在类型层。
--
-- ⚠ 本模块同时开 `--cubical` 与 `--rewriting`，理由：
--   它导入 `BraidQuotient`（→ BraidToSL23 → SL23Cayley → Trit），而 `Trit` 声明了
--   `--rewriting`（**纯标志**：其注释写明自身不用规则，是为 T6/Xuanwu/JacobianIS 继承）。
--   探针实测：`--cubical` 下**真正声明的** REWRITE 规则会被静默忽略。
--   本导入锥经逐模块点数**无任何 `{-# REWRITE #-}`** ⇒ 无规则可丢，安全性成立。
--
-- E1 桥（本模块的技术核心）：
--   `Mat2` 的字段是 **stdlib** `Data.Fin.Fin 3`，而 cubical 只给
--   `Cubical.Data.FinData` 的 `isSetFin`。两者构型不同（一个 Σ、一个归纳类型），
--   故先造 `Data.Fin ↔ FinData` 的 retract，再用 `isSetRetract` 把 h-level 搬过来。
--
-- 包含：toPath / toFD / fromFD / retract / isSetStdFin / mat→4 / mat←4 /
--       isSetMat2 / eval-B3 / eval-B3-β / eval-B3-W
-- 0 postulate / 0 hole。

module Sovereign.Synthesis.Representation.BraidQuotientCubicalEval where

open import Cubical.Foundations.Prelude
  using (Type; isSet; _≡_; refl; cong; _∙_)

open import Cubical.Foundations.HLevels using (isSetRetract; isSet×)
open import Cubical.Data.Sigma using (_×_; _,_)
open import Cubical.Data.FinData.Base as FD using ()
open import Cubical.Data.FinData.Properties as FDP using (isSetFin)
open import Cubical.HITs.SetQuotients using ([_])

open import Data.Fin.Base as StdFin using ()
open import Relation.Binary.PropositionalEquality as PE using ()

open import Sovereign.Synthesis.Representation.SL23Cayley using (Mat2)
open import Sovereign.Algebra.LinearAlgebra.Matrix2 using (mkMat2)
open import Sovereign.Algebra.GroupTheory.Word using (Word)
open import Sovereign.Algebra.GroupTheory.BraidQuotient using (eval-resp)
open import Sovereign.Algebra.GroupTheory.BraidToSL23 using (eval; wWord; eval-W-word; negI)
open import Sovereign.Synthesis.Representation.BraidQuotientCubical using (B3; B3-rec)

--------------------------------------------------------------------------------
-- ① 命题相等 → Path（本 cubical 版本无现成 toPath）
--------------------------------------------------------------------------------

toPath : ∀ {A : Type} {x y : A} → PE._≡_ x y → _≡_ x y
toPath {x = x} p = PE.subst (λ y → _≡_ x y) p refl

--------------------------------------------------------------------------------
-- ② Data.Fin ↔ FinData 的 retract（E1 桥）
--
-- 两者都是「长度 n 的有限类型」的归纳表示，但构造子属于不同数据类型
-- （stdlib 的 `Fin` 是索引族，cubical 的 `FinData` 是另一份同构副本）。
--------------------------------------------------------------------------------

toFD : ∀ {n} → StdFin.Fin n → FD.Fin n
toFD StdFin.zero    = FD.zero
toFD (StdFin.suc i) = FD.suc (toFD i)

fromFD : ∀ {n} → FD.Fin n → StdFin.Fin n
fromFD FD.zero    = StdFin.zero
fromFD (FD.suc i) = StdFin.suc (fromFD i)

retract : ∀ {n} (x : StdFin.Fin n) → fromFD (toFD x) ≡ x
retract StdFin.zero    = refl
retract (StdFin.suc i) = cong StdFin.suc (retract i)

-- stdlib Fin 是集合（把 FinData 的 h-level 沿 retract 搬过来）
isSetStdFin : ∀ {n} → isSet (StdFin.Fin n)
isSetStdFin = isSetRetract toFD fromFD retract FDP.isSetFin

--------------------------------------------------------------------------------
-- ③ Mat2 是集合（4 个 Fin 3 字段）
--------------------------------------------------------------------------------

mat→4 : Mat2 → StdFin.Fin 3 × StdFin.Fin 3 × StdFin.Fin 3 × StdFin.Fin 3
mat→4 (mkMat2 a b c d) = a , b , c , d

mat←4 : StdFin.Fin 3 × StdFin.Fin 3 × StdFin.Fin 3 × StdFin.Fin 3 → Mat2
mat←4 (a , b , c , d) = mkMat2 a b c d

isSetMat2 : isSet Mat2
isSetMat2 = isSetRetract mat→4 mat←4 (λ _ → refl)
              (isSet× isSetStdFin
                (isSet× isSetStdFin (isSet× isSetStdFin isSetStdFin)))

--------------------------------------------------------------------------------
-- ④ 下降：eval 成为商上的函数
--------------------------------------------------------------------------------

eval-B3 : B3 → Mat2
eval-B3 = B3-rec isSetMat2 eval (λ a b r → toPath (eval-resp r))

-- 计算规则：在代表词上就是 eval（rec 的 β）
eval-B3-β : ∀ (w : Word) → eval-B3 [ w ] ≡ eval w
eval-B3-β w = refl

-- W 的整个类映到 −I（把「代表词」的结论提升到「类」）
-- ⚠ 注意 toPath：`eval-W-word` 陈述在 PropositionalEquality 的 `_≡_` 上，
--   而这里是 cubical 的 Path（`B3-rec` 的 β 给的是 Path），不能直接用 `∙` 粘。
eval-B3-W : eval-B3 [ wWord ] ≡ negI
eval-B3-W = eval-B3-β wWord ∙ toPath eval-W-word
