{-# OPTIONS --rewriting --guardedness #-}

-- ⚠️ [HISTORICAL 2026-10-10 人类裁决] List 表示路线已冻结：唯一主路线 = 函数表示 LaurentCubical（funExt 直接得函数相等）。本模块不再投入新工作；下游请迁移到 LaurentCubical。
-- | Sovereign.Algebra.LaurentDistrib
-- Laurent 多项式分配律：先证伪、再证真。
--
-- 数学背景：Z[t,t⁻¹] 的项用裸 List (ℤ × ℤ) 表示（未排序、不去重）。
-- 「项列表逐点相等」意义下的分配律
--     a *L (b ++L c) ≡ (a *L b) ++L (a *L c)
-- 是【假命题】：两个相等的「和式」在裸列表上顺序不同
-- （(A++B)++(C++D) 与 (A++C)++(B++D) 中项不交换）。
-- 下面给出具体反例 not-distrib-pointwise 证伪它（statement_wrong 诊断）。
--
-- 多项式的项列表本质是【有序化前的多重集表示】，分配律的真命题是：
--     a *L (b ++L c) ↭ (a *L b) ++L (a *L c)   （模置换相等 ↭）
-- 由 distrib-perm 证明（0 postulate / 0 hole）。
-- 逐点相等版本的完整环公理需要排序规范化（见 LaurentSort 路线），
-- 置换不变量正是排序规范化的合法性依据。
module Sovereign.Algebra.LaurentDistrib where

open import Data.Integer using (ℤ; +_; _+_; _*_)
open import Data.List using (List; []; _∷_; foldr; _++_)
import Data.List.Properties

open import Data.Product using (Σ; _×_; _,_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; sym; trans)
open import Relation.Nullary using (¬_)
open import Data.List.Relation.Binary.Permutation.Propositional
  using (_↭_; refl; prep; ↭-trans; ↭-sym)
open import Data.List.Relation.Binary.Permutation.Propositional.Properties
  using (++⁺ˡ; ++⁺ʳ; ++-assoc; ++-comm)

open import Sovereign.Algebra.LaurentBase using (LaurentTerm; Laurent) public

mulTerm : LaurentTerm → LaurentTerm → LaurentTerm
mulTerm (c₁ , n₁) (c₂ , n₂) = (c₁ * c₂ , n₁ + n₂)

mapL : (LaurentTerm → LaurentTerm) → Laurent → Laurent
mapL f [] = []
mapL f (x ∷ xs) = f x ∷ mapL f xs

infixl 6 _++L_
-- _++L_ 是 Data.List._++_ 的定义别名（同一函数，两个名字）。
-- 为什么必须别名：stdlib 置换引理 ++⁺ˡ/++⁺ʳ 的类型携带 Data.List._++_，
-- 若 *L 用另一个自定义 append，单射分解失败（两个不同定义符号不可分解）。
_++L_ : Laurent → Laurent → Laurent
xs ++L ys = xs ++ ys

++L-assoc : ∀ xs ys zs → (xs ++L ys) ++L zs ≡ xs ++L (ys ++L zs)
++L-assoc xs ys zs = Data.List.Properties.++-assoc xs ys zs

infixl 7 _*L_
_*L_ : Laurent → Laurent → Laurent
xs *L ys = foldr (λ x acc → mapL (mulTerm x) ys ++L acc) [] xs

mapL-++L : (f : LaurentTerm → LaurentTerm) (xs ys : Laurent) →
           mapL f (xs ++L ys) ≡ mapL f xs ++L mapL f ys
mapL-++L f [] ys = refl
mapL-++L f (x ∷ xs) ys = cong (f x ∷_) (mapL-++L f xs ys)

-- ────────────────────────────────────────────────────────────────────
-- 第一步：证伪逐点陈述（statement_wrong 诊断，具体反例）
-- 取 a = x + 1, b = c = 1：
--   a *L (b ++ c)   = [(+1,+1), (+1,+1), (+1,+0), (+1,+0)] = l₁
--   (a*L b) ++ a*L c = [(+1,+1), (+1,+0), (+1,+1), (+1,+0)] = l₂
-- 两个封闭项按定义归约（refl），再证 l₁ ≢ l₂。
-- ────────────────────────────────────────────────────────────────────

-- 命名常量（避免裸对子在推断模式下与 ≡ 的 fixity 冲突）
a-ex : Laurent
a-ex = (+ 1 , + 1) ∷ ((+ 1 , + 0) ∷ [])

b-ex : Laurent
b-ex = (+ 1 , + 0) ∷ []

l₁ : Laurent
l₁ = (+ 1 , + 1) ∷ ((+ 1 , + 1) ∷ ((+ 1 , + 0) ∷ ((+ 1 , + 0) ∷ [])))

l₂ : Laurent
l₂ = (+ 1 , + 1) ∷ ((+ 1 , + 0) ∷ ((+ 1 , + 1) ∷ ((+ 1 , + 0) ∷ [])))

pa : a-ex *L (b-ex ++L b-ex) ≡ l₁
pa = refl

pc : (a-ex *L b-ex) ++L (a-ex *L b-ex) ≡ l₂
pc = refl

-- 反例的两列表在第 2 个位置不同：(+1,+1) vs (+1,+0)
l₁≢l₂ : ¬ (l₁ ≡ l₂)
l₁≢l₂ ()

-- 逐点分配律为假：若对一切 a b c 成立，反例给出 l₁ ≡ l₂，矛盾
not-distrib-pointwise :
  ¬ (∀ a b c → a *L (b ++L c) ≡ (a *L b) ++L (a *L c))
not-distrib-pointwise d = l₁≢l₂ (trans (d a-ex b-ex b-ex) (sym pc))

-- ────────────────────────────────────────────────────────────────────
-- 第二步：真命题——模置换相等意义下的分配律
-- ────────────────────────────────────────────────────────────────────

-- mapL 对 ++ 分配（模置换）：mapL f (xs ++ ys) ↭ mapL f xs ++ mapL f ys
mapL-++-↭ : ∀ (f : LaurentTerm → LaurentTerm) (xs ys : Laurent) →
            mapL f (xs ++ ys) ↭ mapL f xs ++ mapL f ys
mapL-++-↭ f [] ys = refl
mapL-++-↭ f (x ∷ xs) ys = prep (f x) (mapL-++-↭ f xs ys)

-- 交换中项（模置换）：(A ++ B) ++ (C ++ D) ↭ (A ++ C) ++ (B ++ D)
-- 这正是逐点相等做不到的那一步；置换意义下合法。
--   (A++B)++(C++D) ↭ A++(B++(C++D)) ↭ A++(C++(B++D)) ↭ (A++C)++(B++D)
-- 中间一步由 (B++C++D) ↭ (C++B++D) 经 assoc/comm 组装。
++-interchange : ∀ (A B C D : Laurent) →
                 (A ++ B) ++ (C ++ D) ↭ (A ++ C) ++ (B ++ D)
++-interchange A B C D =
  ↭-trans (++-assoc A B (C ++ D))
    (↭-trans (++⁺ˡ A middle)
      (↭-sym (++-assoc A C (B ++ D))))
  where
  -- B ++ (C ++ D) ↭ C ++ (B ++ D)
  middle : B ++ (C ++ D) ↭ C ++ (B ++ D)
  middle =
    ↭-trans (↭-sym (++-assoc B C D))
      (↭-trans (++⁺ʳ D (++-comm B C))
        (++-assoc C B D))

-- 分配律（模置换）：a *L (b ++L c) ↭ (a *L b) ++L (a *L c)
-- 证明：对 a 归纳。
--   归纳步骤：LHS = mapL (mulTerm x) (b ++ c) ++ xs *L (b ++ c)
--     ↭ (mapL x b ++ mapL x c) ++ (xs *L b ++ xs *L c)
--         [mapL-++-↭ 与归纳假设经 ++⁺ 双侧]
--     ↭ (mapL x b ++ xs *L b) ++ (mapL x c ++ xs *L c) = RHS   [++-interchange]
distrib-perm : ∀ a b c → a *L (b ++L c) ↭ (a *L b) ++L (a *L c)
distrib-perm [] b c = refl
distrib-perm (x ∷ xs) b c =
  ↭-trans step1 (++-interchange (mapL (mulTerm x) b) (mapL (mulTerm x) c)
                                (xs *L b) (xs *L c))
  where
  -- 第一步：mapL-++-↭（左侧）+ 归纳假设（右侧）经 ++⁺
  step1 : (x ∷ xs) *L (b ++L c)
         ↭ ((mapL (mulTerm x) b) ++L (mapL (mulTerm x) c))
           ++L ((xs *L b) ++L (xs *L c))
  step1 = ↭-trans (++⁺ʳ (xs *L (b ++L c)) (mapL-++-↭ (mulTerm x) b c))
                  (++⁺ˡ ((mapL (mulTerm x) b) ++L (mapL (mulTerm x) c))
                        (distrib-perm xs b c))
