{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Algebra.Complexity.Tableau-Pool
-- tableau 的**线性化池**：把 `(时刻, 偏移, 符号)` 压成一个 CNF 变量号 —— 里程碑 M3c 闸门 G2
--
-- 【本件在 Cook–Levin 里的位置】M3a 已证 `AtoCNF-sat` 对**任意** `e : A → Fin (suc m)`
-- 成立（不要求单射，也不要求满射）。G3 的子句族却必须真的交出一个 `e`。池就是那个
-- `e` 的具体值：三段 `Fin` 乘积用 stdlib 的 `combine` 压平，逆方向用 `remQuot`。
--
-- 【为什么不手搓乘除】`_*_` 递归在**首参**上，手写 `toℕ` 编号就得自己证 `n * k` 的
-- 除法往返（`%`/`/` 的边界全落在 stuck 项上），那是本项目吃过多次亏的算术沼泽。
-- stdlib 直接给了 `remQuot-combine`（`Data/Fin/Properties.agda:694`）与
-- `combine-remQuot`（:699），本件只做**一层套一层**的搬运，不产生新的算术义务。
--
-- 【尺寸口径】`poolSize len T V = suc T * ((3 * off-L len T) * V)`：
--   · `suc T`  —— 时刻 `0..T`（与 `InNP-TM` 的 `tm-p` 上界口径一致）；
--   · `3 * L`  —— 偏移码 `Fin 3 × Fin L`（`offTag` 恰好 3 支，`off-L` 是帧宽）；
--   · `V`      —— 字母表（`Fin V`）。
--   读法：`T+1` 个时刻 × 每时刻 `3L` 个格位 × `V` 个符号。
--   ⚠ `CNF.Lit m = Sign × Fin (suc m)` 是 **m+1 个槽**；本件取 `m = poolSize`，
--   即最高槽 `poolSize` **空置不用**（无碰撞，也不需要额外前提）。这是 M1 的既定
--   约定，不是笔误。
--
-- 【为什么 `poolDec` 要拆成四个投影步】`poolDec` 是三层嵌套 `remQuot` 的投影项；
-- 若写成单个 `let`/`with` 定义，`remQuot-combine` 的改写要在一整个嵌套项上做
-- `cong` 链（每层都得手工指出改写点）。拆成 `poolTime`/`poolCell`/`poolCode`/`poolSym`
-- 之后，每条 `*-enc` 是「一次 `remQuot-combine` + 一次 `cong proj`」，往返用
-- `cong₂ _,_` 组装 —— 分解是为了**让证明可读**，不是为了绕障碍。
--
-- 分级约定：〔结构定义〕/〔结构证明〕/〔refl 枚举〕/〔立界注记〕（同 TimeBound）。
-- 0 postulate / 0 hole。

module Sovereign.Algebra.Complexity.Tableau-Pool where

open import Data.Nat using (ℕ; suc; _≤_; _*_; s≤s⁻¹)
open import Data.Nat.Properties using (m<n⇒m<1+n)
open import Data.Fin using (Fin; toℕ; fromℕ<; combine; remQuot)
  renaming (zero to fzero; suc to fsuc)
open import Data.Fin.Properties using (remQuot-combine; toℕ<n)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; trans; cong; cong₂)

open import Sovereign.Algebra.Complexity.SATMember using (Sign; Lit)
open import Sovereign.Algebra.Complexity.CNF using (Clause'; Formula')
open import Sovereign.Algebra.Complexity.Tableau-Tape
  using (TOff; tH; tL; tR; InOff; offTag; offEnc; offDec; offDec-enc; off-L)

-- ────────────────────────────────────────────────────────────────────
-- §1 尺寸（B1 / B1b）〔结构定义〕
-- ────────────────────────────────────────────────────────────────────

poolSize : (len T V : ℕ) → ℕ
poolSize len T V = suc T * ((3 * off-L len T) * V)

-- 时刻上界：`toℕ t < suc T ⟹ toℕ t ≤ T`（给 `offEnc` 的 `hT` 用）
pool-fin-le : ∀ {T : ℕ} (t : Fin (suc T)) → toℕ t ≤ T
pool-fin-le t = s≤s⁻¹ (toℕ<n t)

-- ────────────────────────────────────────────────────────────────────
-- §2 编码（B2）〔结构定义〕
-- ────────────────────────────────────────────────────────────────────
-- 偏移先压成 `Fin (3 * L)`：tag 在外层（`combine` 的首参是高位），索引在内层。
-- 取 `proj₂ (offEnc …)` 而非 `offIdx o`：`offEnc` 的索引位已经带好 `Fin L` 的界内证明，
-- `offIdx` 只是裸 ℕ。

poolOffFin : ∀ (len T t : ℕ) (o : TOff) (h : InOff len t o) (hT : t ≤ T)
           → Fin (3 * off-L len T)
poolOffFin len T t o h hT = combine (offTag o) (proj₂ (offEnc len T t o h hT))

-- 三层压平：时刻 ⊗ (格位码 ⊗ 符号)
poolEnc : ∀ (len T V : ℕ) (t : Fin (suc T)) (o : TOff)
            (h : InOff len (toℕ t) o) (a : Fin V)
        → Fin (poolSize len T V)
poolEnc len T V t o h a =
  combine t (combine (poolOffFin len T (toℕ t) o h (pool-fin-le t)) a)

-- ────────────────────────────────────────────────────────────────────
-- §3 解码（B3）〔结构定义〕
-- ────────────────────────────────────────────────────────────────────
-- 投影步的次序：先解时刻 → 再解「格位码 / 符号」→ 最后把格位码解回 `TOff`。
-- `poolCode` 只是 `Fin (3 * L)`；`offDec` 要的是 `Fin 3 × Fin L`，故再由一次
-- `remQuot (off-L len T)` 取回那对（`offDec-enc` 说「解回再合成 = 原码」）。

poolTime : ∀ (len T V : ℕ) → Fin (poolSize len T V) → Fin (suc T)
poolTime len T V i = proj₁ (remQuot {m = suc T} ((3 * off-L len T) * V) i)

poolCell : ∀ (len T V : ℕ) → Fin (poolSize len T V) → Fin ((3 * off-L len T) * V)
poolCell len T V i = proj₂ (remQuot {m = suc T} ((3 * off-L len T) * V) i)

poolCode : ∀ (len T V : ℕ) → Fin (poolSize len T V) → Fin (3 * off-L len T)
poolCode len T V i = proj₁ (remQuot {m = 3 * off-L len T} V (poolCell len T V i))

poolSym : ∀ (len T V : ℕ) → Fin (poolSize len T V) → Fin V
poolSym len T V i = proj₂ (remQuot {m = 3 * off-L len T} V (poolCell len T V i))

poolDec : ∀ (len T V : ℕ) → Fin (poolSize len T V) → Fin (suc T) × (TOff × Fin V)
poolDec len T V i =
  poolTime len T V i
  , (offDec len T (remQuot {m = 3} (off-L len T) (poolCode len T V i)) , poolSym len T V i)

-- ────────────────────────────────────────────────────────────────────
-- §4 往返（B4a + B4b）〔结构证明〕
-- ────────────────────────────────────────────────────────────────────
-- B4a：格位码解回 `offEnc`。三支各一条 `remQuot-combine`，右手边直接当目标 ——
-- 因为 `offEnc` 在每支上**定义性地**就是 `(offTag o , 索引)`（`offTag` 的 3 支与
-- `offEnc` 的 3 支逐一对应），连 `cong` 都不需要。
poolOffFin-spec : ∀ (len T t : ℕ) (o : TOff) (h : InOff len t o) (hT : t ≤ T)
                → remQuot {m = 3} (off-L len T) (poolOffFin len T t o h hT)
                  ≡ offEnc len T t o h hT
poolOffFin-spec len T t tH h hT =
  remQuot-combine {n = 3} {k = off-L len T} (offTag tH) (proj₂ (offEnc len T t tH h hT))
poolOffFin-spec len T t (tL k) h hT =
  remQuot-combine {n = 3} {k = off-L len T} (offTag (tL k))
                  (proj₂ (offEnc len T t (tL k) h hT))
poolOffFin-spec len T t (tR k) h hT =
  remQuot-combine {n = 3} {k = off-L len T} (offTag (tR k))
                  (proj₂ (offEnc len T t (tR k) h hT))

-- B4b-1：时间位（外层 `combine`）
poolTime-enc : ∀ (len T V : ℕ) (t : Fin (suc T)) (o : TOff)
                 (h : InOff len (toℕ t) o) (a : Fin V)
             → poolTime len T V (poolEnc len T V t o h a) ≡ t
poolTime-enc len T V t o h a =
  cong proj₁ (remQuot-combine {n = suc T} {k = (3 * off-L len T) * V} t
                              (combine (poolOffFin len T (toℕ t) o h (pool-fin-le t)) a))

-- B4b-2：格位码 + 符号那一层（中层 `combine` 的右分量）
poolCell-enc : ∀ (len T V : ℕ) (t : Fin (suc T)) (o : TOff)
                 (h : InOff len (toℕ t) o) (a : Fin V)
             → poolCell len T V (poolEnc len T V t o h a)
               ≡ combine (poolOffFin len T (toℕ t) o h (pool-fin-le t)) a
poolCell-enc len T V t o h a =
  cong proj₂ (remQuot-combine {n = suc T} {k = (3 * off-L len T) * V} t
                              (combine (poolOffFin len T (toℕ t) o h (pool-fin-le t)) a))

-- B4b-3：格位码（中层的左分量；先过 `poolCell-enc`，再过内层 `remQuot-combine`）
poolCode-enc : ∀ (len T V : ℕ) (t : Fin (suc T)) (o : TOff)
                 (h : InOff len (toℕ t) o) (a : Fin V)
             → poolCode len T V (poolEnc len T V t o h a)
               ≡ poolOffFin len T (toℕ t) o h (pool-fin-le t)
poolCode-enc len T V t o h a =
  trans (cong (λ c → proj₁ (remQuot {m = 3 * off-L len T} V c))
              (poolCell-enc len T V t o h a))
        (cong proj₁ (remQuot-combine {n = 3 * off-L len T} {k = V}
                                     (poolOffFin len T (toℕ t) o h (pool-fin-le t)) a))

-- B4b-4：符号位（中层的右分量）
poolSym-enc : ∀ (len T V : ℕ) (t : Fin (suc T)) (o : TOff)
                (h : InOff len (toℕ t) o) (a : Fin V)
            → poolSym len T V (poolEnc len T V t o h a) ≡ a
poolSym-enc len T V t o h a =
  trans (cong (λ c → proj₂ (remQuot {m = 3 * off-L len T} V c))
              (poolCell-enc len T V t o h a))
        (cong proj₂ (remQuot-combine {n = 3 * off-L len T} {k = V}
                                     (poolOffFin len T (toℕ t) o h (pool-fin-le t)) a))

-- B4b-5：格位码 → `TOff`（`poolCode-enc` 一次 `cong`，B4a 一次，A6 的 `offDec-enc` 收尾）
poolOffDec-enc : ∀ (len T V : ℕ) (t : Fin (suc T)) (o : TOff)
                   (h : InOff len (toℕ t) o) (a : Fin V)
               → offDec len T
                   (remQuot {m = 3} (off-L len T)
                     (poolCode len T V (poolEnc len T V t o h a)))
                 ≡ o
poolOffDec-enc len T V t o h a =
  trans (cong (λ c → offDec len T (remQuot {m = 3} (off-L len T) c))
              (poolCode-enc len T V t o h a))
        (trans (cong (offDec len T)
                     (poolOffFin-spec len T (toℕ t) o h (pool-fin-le t)))
               (offDec-enc len T (toℕ t) o h (pool-fin-le t)))

-- B4b-6：主引理 —— 解码-编码在界内互逆（`cong₂ _,_` 把三段装回三元组）
poolDec-enc : ∀ (len T V : ℕ) (t : Fin (suc T)) (o : TOff)
                (h : InOff len (toℕ t) o) (a : Fin V)
            → poolDec len T V (poolEnc len T V t o h a) ≡ (t , (o , a))
poolDec-enc len T V t o h a =
  cong₂ _,_ (poolTime-enc len T V t o h a)
        (cong₂ _,_ (poolOffDec-enc len T V t o h a) (poolSym-enc len T V t o h a))

-- ────────────────────────────────────────────────────────────────────
-- §5 接线到 M1 的变量层（B5）〔结构定义〕
-- ────────────────────────────────────────────────────────────────────
-- `Lit m = Sign × Fin (suc m)`：池号 `i : Fin poolSize` 抬进 `Fin (suc poolSize)`。
-- 这格抬升是「`Lit` 的 m+1 槽约定」的直接后果，用 `fromℕ<` + `m<n⇒m<1+n` 完成。
poolLit : ∀ (len T V : ℕ) → Sign → Fin (poolSize len T V) → Lit (poolSize len T V)
poolLit len T V s i = s , fromℕ< (m<n⇒m<1+n (toℕ<n i))

-- 子句 / 公式的类型别名：G3 的子句族直接用这两个，不必反复写 `poolSize len T V`
PoolClause : ∀ (len T V : ℕ) → Set
PoolClause len T V = Clause' (poolSize len T V)

PoolFormula : ∀ (len T V : ℕ) → Set
PoolFormula len T V = Formula' (poolSize len T V)

-- ────────────────────────────────────────────────────────────────────
-- §6 核对层（B6）〔refl 枚举〕
-- ────────────────────────────────────────────────────────────────────

-- `off-L 2 3 = suc (suc (2 + 3 + 3)) = 10` ⟹ `4 * (30 * 2) = 240`
Tp-check-poolSize : poolSize 2 3 2 ≡ 240
Tp-check-poolSize = refl

-- 具体点：len = 1、T = 1、V = 2、t = 1、o = tH、a = 0
Tp-check-poolDec-enc : poolDec 1 1 2 (poolEnc 1 1 2 (fsuc fzero) tH tt fzero)
                     ≡ (fsuc fzero , (tH , fzero))
Tp-check-poolDec-enc = poolDec-enc 1 1 2 (fsuc fzero) tH tt fzero
