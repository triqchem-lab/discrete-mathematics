{-# OPTIONS --rewriting --guardedness #-}
-- | _PS3chk —— Stage3 四难律小例探针（独立验证件，用完可删）
module _PS3chk where

open import Data.Integer using (ℤ; +_; -[1+_]; _+_)
open import Data.List using (List; []; _∷_)
open import Data.Product using (_,_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (¬_)
open import Sovereign.Algebra.LaurentDistrib using (LaurentTerm; Laurent; _++L_; _*L_)
open import Sovereign.Algebra.LaurentSums using (norm; NoZero)
open import Sovereign.Algebra.LaurentRing
  using (+-assoc-norm; +-identity-norm; +-comm-norm; norm-+; distrib-norm;
         *-assoc-norm; distrib-norm-r; R0)

a b c : Laurent
a = ((+ 1) , + 0) ∷ []
b = ((+ 2) , + 1) ∷ []
c = ((+ 3) , -[1+ 0 ]) ∷ []

nza : NoZero a
nza = (λ ()) , tt
nzb : NoZero b
nzb = (λ ()) , tt
nzc : NoZero c
nzc = (λ ()) , tt

-- 六律经定理调用（构造性）
chk-comm : norm (a ++L b) ≡ norm (b ++L a)
chk-comm = +-comm-norm a b nza nzb
chk-plus : norm (a ++L b) ≡ norm (norm a ++L norm b)
chk-plus = norm-+ a b nza nzb
chk-distl : norm (a *L (b ++L c)) ≡ norm ((a *L b) ++L (a *L c))
chk-distl = distrib-norm a b c nza nzb nzc
chk-assoc : norm ((a *L b) *L c) ≡ norm (a *L (b *L c))
chk-assoc = *-assoc-norm a b c
chk-assoc+ : norm ((a ++L b) ++L c) ≡ norm (a ++L (b ++L c))
chk-assoc+ = +-assoc-norm a b c
chk-id : norm (a ++L R0) ≡ norm a
chk-id = +-identity-norm a
chk-distr : norm ((a ++L b) *L c) ≡ norm ((a *L c) ++L (b *L c))
chk-distr = distrib-norm-r a b c

-- 独立 refl 交叉（不经定理直接算）：交换律双通道 + tie 合并消解
chk-refl-comm : norm (a ++L b) ≡ norm (b ++L a)
chk-refl-comm = refl
chk-refl-merge : norm (((+ 1) , + 0) ∷ ((+ 2) , + 0) ∷ []) ≡ (((+ 3) , + 0) ∷ [])
chk-refl-merge = refl
