{-# OPTIONS --rewriting --guardedness #-}

-- ⚠️ [HISTORICAL 2026-10-10 人类裁决] List 表示路线已冻结：唯一主路线 = 函数表示 LaurentCubical（funExt 直接得函数相等）。本模块不再投入新工作；下游请迁移到 LaurentCubical。
-- | Sovereign.Algebra.LaurentRing
-- P3.4 T1a：Z[t,t⁻¹] 环——定义层 + 规范化 + t·t⁻¹≡1 实例。
--
-- 数学背景：Laurent 多项式环 Z[t,t⁻¹]，项表示 List (ℤ × ℤ)（系数, 指数），
-- 基础运算复用 LaurentDistrib（*-assoc 逐点已证、distrib-perm 模置换已证）。
--
-- 规范化 norm（路线 B：foldr insertCᵌ）：
--   insertCᵌ —— 插入式规范化（LaurentNorm），直接产出 Canon（严格降序+指数互异）
-- 环公理的「逐点相等」陈述依赖排序唯一性 sort-unique（台账 pending，
-- Laurent.sort-unique）；本模块先交付定义层 + t·t⁻¹≡1 单项式实例。
--
-- 诚实边界（完成度）：
--   ✅ T1a-1/2 类型与运算（复用，回执 0966426a / 85deea2f）
--   ✅ T1a-4 t 与 t⁻¹
--   ✅ T1a-5 t·t⁻¹ ≡ 1（单项式实例：t、t⁻¹ 各一项，乘积恰为 [(+1,+0)]，
--      无排序歧义，refl 可证——有界实例，不证一般单位律）
--   ✅ norm 规范化函数
--   ⏳ T1a-3 一般环公理（逐点）——pending on Laurent.sort-unique
--   ⏳ 规范化正确性（merge 保有序、norm 幂等）——pending
--
-- 0 postulate / 0 hole。
module Sovereign.Algebra.LaurentRing where

open import Data.Integer using (ℤ; +_; -[1+_]; +0; +[1+_]; _+_; _*_)
open import Data.Integer.Properties using (_≟_)
open import Data.List using (List; []; _∷_)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; _≢_)
open import Relation.Nullary using (yes; no)
open import Relation.Nullary.Decidable using (¬?)
open import Sovereign.Algebra.LaurentDistrib
  using (LaurentTerm; Laurent; mulTerm; mapL; _++L_; _*L_;
         mapL-++L; ++L-assoc; distrib-perm)
open import Sovereign.Algebra.LaurentSums using (norm; normC)

-- ────────────────────────────────────────────────────────────────────
-- 常数：0、1、t、t⁻¹
-- 约定：项 = (系数, 指数)；t 的指数为 +1，t⁻¹ 的指数为 -1
-- ────────────────────────────────────────────────────────────────────

R0 : Laurent
R0 = []

R1 : Laurent
R1 = (+ 1 , + 0) ∷ []

tvar : Laurent
tvar = (+ 1 , + 1) ∷ []

tinv : Laurent
tinv = (+ 1 , -[1+ 0 ]) ∷ []

-- t × t⁻¹ ≡ 1（单项式实例）：mulTerm (+1,+1) (+1,-1) = (+1, +0)，
-- 乘积 = [(+1,+0)] = R1，封闭项归约，refl 可证。
tmul-tinv : tvar *L tinv ≡ R1
tmul-tinv = refl

-- ────────────────────────────────────────────────────────────────────
-- 规范化：merge（合并相邻同指数项）→ dropZ（去零系数）→ norm
-- 前置条件：输入已按指数降序排序（norm 先过 sort 保证）
-- ────────────────────────────────────────────────────────────────────

-- 规范化：路线 B（insertCᵌ），从 LaurentSums 导入
-- norm = proj₁ ∘ normC，其中 normC 递归 fold insertCᵌ 产出 Canon
-- （旧路线 A 的 dropZ ∘ merge ∘ sort 已废弃——Sorted 中间态不兼容 Canon）

-- 规范化实例：norm (t·t⁻¹) = norm [(+1,+0)] = [(+1,+0)] = R1
norm-tmul-tinv : norm (tvar *L tinv) ≡ R1
norm-tmul-tinv = refl

-- ────────────────────────────────────────────────────────────────────
-- 诚实边界：以下为 pending（不在本模块声称已证）
--   1. merge-preserves-sorted : Sorted ts → Sorted (merge ts)
--   2. norm-idem : norm (norm p) ≡ norm p
--   3. sort-unique（Laurent.sort-unique 台账节点）→ 一般环公理
--   4. norm-+comm : norm (a ++L b) ≡ norm (b ++L a)
-- ────────────────────────────────────────────────────────────────────

-- ────────────────────────────────────────────────────────────────────
-- ── 2026-10-11 补件（T1a-3 一般环公理，norm 等价下；sort-unique 前置已解）──
--   每律一顶一签名。易律从 List 层同余直接提升（cong norm）；
--   难律（+-comm / distrib / *-assoc）走「sums 逐点相等 → 唯一性提升」，
--   唯一性件在 LaurentSums 补件段（canon-sums-unique 系）。
--   ⚠ 零系边界（2026-10-11 发现）：insertCᵌ 保留孤零项（insert (0,n) [] = [(0,n)]），
--   sums-唯一性对含零系数项的输入不成立——难律若需 NoZero 前提将另行注明。
-- ────────────────────────────────────────────────────────────────────

open import Data.List.Properties using (++-identityʳ)
open import Relation.Binary.PropositionalEquality using (cong)

-- 加法结合（norm 等价下）：List 层即结合，norm 同余直接得
+-assoc-norm : ∀ a b c → norm ((a ++L b) ++L c) ≡ norm (a ++L (b ++L c))
+-assoc-norm a b c = cong norm (++L-assoc a b c)

-- 加法单位（norm 等价下）：R0 = []，List 层右单位即得
+-identity-norm : ∀ a → norm (a ++L R0) ≡ norm a
+-identity-norm a = cong norm (++-identityʳ a)

-- ────────────────────────────────────────────────────────────────────
-- ── 2026-10-11 Stage3 ── 四难律收口（NoZero 前提版）
--   路线：sums 逐点相等 → canon-sums-unique-nz 提升。
--   原签名 norm (a ++L b) ≡ norm a ++L norm b **为假**（同指数反例
--   a=[(1,0)] b=[(2,0)：LHS [(3,0)]、RHS [(1,0),(2,0)]）——正解为
--   norm-复合形（右端再 norm）；+-comm-norm 形本就成立。
-- ────────────────────────────────────────────────────────────────────

open import Data.Integer.Properties using (+-comm)
open import Data.Unit using (tt)
open import Sovereign.Algebra.LaurentMulAssoc using (*-assoc; *-++-distribˡ)
open import Relation.Binary.PropositionalEquality using (trans; cong; sym)
open import Relation.Nullary using (¬_)
open import Sovereign.Algebra.LaurentSums
  using (NoZero; norm-nozero; ++L-nozero; sums; sums-++L; norm-sums;
         canon-sums-unique-nz; sums-resp-↭)

-- ℤ 无零因子：非零积非零
*-nz : ∀ (c d : ℤ) → c ≢ + 0 → d ≢ + 0 → (c * d) ≢ + 0
*-nz +0 d hc _ = λ _ → hc refl
*-nz c +0 _ hd = λ _ → hd refl
*-nz +[1+ m ] +[1+ n ] _ _ = λ ()
*-nz +[1+ m ] (-[1+ n ]) _ _ = λ ()
*-nz (-[1+ m ]) +[1+ n ] _ _ = λ ()
*-nz (-[1+ m ]) (-[1+ n ]) _ _ = λ ()

-- mapL/mulTerm 保 NoZero（逐项非零积）
mapL-noz : ∀ (x : LaurentTerm) ys → proj₁ x ≢ + 0 → NoZero ys →
           NoZero (mapL (mulTerm x) ys)
mapL-noz x [] _ _ = tt
mapL-noz x ((c , n) ∷ ys) hx (hc , nys) = *-nz (proj₁ x) c hx hc , mapL-noz x ys hx nys

-- *L 保 NoZero（foldr 拼接逐段保持）
*L-nozero : ∀ xs ys → NoZero xs → NoZero ys → NoZero (xs *L ys)
*L-nozero [] ys _ _ = tt
*L-nozero ((c , n) ∷ xs) ys (hc , nxs) nys =
  ++L-nozero (mapL (mulTerm (c , n)) ys) (xs *L ys)
    (mapL-noz (c , n) ys hc nys) (*L-nozero xs ys nxs nys)

-- 提升件（sums 逐点链 → canon-sums-unique-nz；两端 norm 输出自动 Canon）
lift-norm : ∀ (xs ys : Laurent) (nx : NoZero xs) (ny : NoZero ys) →
            (∀ u → sums u xs ≡ sums u ys) → norm xs ≡ norm ys
lift-norm xs ys nx ny eqs =
  canon-sums-unique-nz (norm xs) (norm ys)
    (proj₂ (normC xs)) (proj₂ (normC ys))
    (norm-nozero xs nx) (norm-nozero ys ny)
    (λ u → trans (norm-sums u xs) (trans (eqs u) (sym (norm-sums u ys))))

-- 律 1：+-comm-norm（norm 交换）
+-comm-norm : ∀ a b → NoZero a → NoZero b → norm (a ++L b) ≡ norm (b ++L a)
+-comm-norm a b na nb =
  lift-norm (a ++L b) (b ++L a) (++L-nozero a b na nb) (++L-nozero b a nb na)
    (λ u → trans (sums-++L u a b) (trans (+-comm (sums u a) (sums u b)) (sym (sums-++L u b a))))

-- 律 2：norm-+（正解 = norm 复合形；原「≡ norm a ++L norm b」形为假见段注）
--   逐点中段具名拆分 norm-+-pw（外链 3 + 内链 2，各 ≤3）
norm-+-pw : ∀ u xs ys → NoZero xs → NoZero ys →
            sums u xs + sums u ys ≡ sums u (norm xs) + sums u (norm ys)
norm-+-pw u xs ys nx ny =
  trans (cong (λ z → z + sums u ys) (sym (norm-sums u xs)))
    (cong (λ z → sums u (norm xs) + z) (sym (norm-sums u ys)))

norm-+ : ∀ xs ys → NoZero xs → NoZero ys →
         norm (xs ++L ys) ≡ norm (norm xs ++L norm ys)
norm-+ xs ys nx ny =
  lift-norm (xs ++L ys) (norm xs ++L norm ys)
    (++L-nozero xs ys nx ny)
    (++L-nozero (norm xs) (norm ys) (norm-nozero xs nx) (norm-nozero ys ny))
    (λ u → trans (sums-++L u xs ys)
            (trans (norm-+-pw u xs ys nx ny)
                   (sym (sums-++L u (norm xs) (norm ys)))))

-- 律 3：distrib-norm（分配律——distrib-perm 置换捷径）
distrib-norm : ∀ a b c → NoZero a → NoZero b → NoZero c →
               norm (a *L (b ++L c)) ≡ norm ((a *L b) ++L (a *L c))
distrib-norm a b c na nb nc =
  lift-norm (a *L (b ++L c)) ((a *L b) ++L (a *L c))
    (*L-nozero a (b ++L c) na (++L-nozero b c nb nc))
    (++L-nozero (a *L b) (a *L c) (*L-nozero a b na nb) (*L-nozero a c na nc))
    (λ u → sums-resp-↭ u (distrib-perm a b c))

-- 律 4：*-assoc-norm（乘法结合 norm 等价）——LaurentMulAssoc.*-assoc 为全列表相等
--   ⇒ cong norm 直得，**免 NoZero 前提**（比四难律原计划更强）
*-assoc-norm : ∀ a b c → norm ((a *L b) *L c) ≡ norm (a *L (b *L c))
*-assoc-norm a b c = cong norm (*-assoc a b c)

-- 右分配（bonus）：*-++-distribˡ 为全列表相等 ⇒ 同样免前提
distrib-norm-r : ∀ a b c → norm ((a ++L b) *L c) ≡ norm ((a *L c) ++L (b *L c))
distrib-norm-r a b c = cong norm (*-++-distribˡ a b c)
