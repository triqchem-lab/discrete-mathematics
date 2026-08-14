{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Constitution.WindingAsymmetry
-- 宪法：宇宙非对称性——源于缠绕数与泛音列公理
-- 
-- 核心论断：
-- - 极向缠绕 144：不可拆分
-- - 环向缠绕 46：不可约化
-- - 泛音列公理：损益操作方向性不可逆
-- - 对称性讨论脱离缠绕数与泛音列均属违宪

module Sovereign.Constitution.WindingAsymmetry where

open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _^_; _%_; _/_; _≤_; _≥_; _∸_; NonZero; ≢-nonZero; nonZero; s≤s; z≤n)
open import Data.Nat.DivMod using (m%n<n; [m+kn]%n≡m%n)
open import Data.Nat.Properties using (m^n≡0⇒m≡0; 1+n≢0; m≤m+n)
open import Data.Integer using (ℤ; +_; -_; -[1+_]; ∣_∣; +≤+; -≤+; -≤-) renaming (_+_ to _+ℤ_; _-_ to _-ℤ_; _*_ to _*ℤ_; _/_ to _/ℤ_; _≥_ to _≥ℤ_; _≤_ to _≤ℤ_)
open import Data.Integer.Properties using (_≤?_)
open import Relation.Nullary using (Dec; yes; no)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.String using (String)
open import Data.Fin using (Fin; toℕ; fromℕ<; _<_) renaming (zero to fzero; suc to fsuc)
open import Data.Fin.Properties using (fromℕ<-cong; toℕ-fromℕ<)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; cong₂)
open import Relation.Nullary using (¬_)
open import Data.Vec using (Vec; []; _∷_; lookup)
open import Relation.Binary.PropositionalEquality using ()
open import Data.Product using (_×_; _,_; ∃; ∃-syntax; Σ)
open import Data.Sum using (_⊎_)

-- 导入核心模块
open import Sovereign.Structology.Winding using (PolarWinding; ToroidalWinding; 
                                                  polarWindingValue; toroidalWindingValue)
open import Sovereign.Base.Lü using (LüName;
                                      HuangZhong; LinZhong; TaiCu; NanLu;
                                      GuXian; YingZhong; RuiBin; DaLu;
                                      YiZe; JiaZhong; WuShe; ZhongLu)
open import Sovereign.RootMath.LengthLattice using (lüToLength)
open import Sovereign.Coupling.LossGain using (LossGain; Sun; Yi; applyLossGain)

--------------------------------------------------------------------------------
-- 1. 泛音列公理：L = L₀ · 2^a · 3^b
--------------------------------------------------------------------------------

-- 泛音列指数对
record HarmonicExponents : Set where
  constructor mkExp
  field
    a : ℤ  -- 因子 2 的幂次
    b : ℤ  -- 因子 3 的幂次

-- 泛音列公理：长度格点由指数对决定
powNZ : (b : ℤ) → NonZero (3 ^ ∣ b ∣)
powNZ b = ≢-nonZero (λ eq → 1+n≢0 (m^n≡0⇒m≡0 3 ∣ b ∣ eq))

harmonicLaw : HarmonicExponents → ℕ
harmonicLaw (mkExp a b) with + 0 ≤? a | + 0 ≤? b
-- 2026-08 P0 修复: 原 if a ≥ 0 then ... 的 ≥ 返回 Set 而非 Bool; 改为
--   ≤? 判定逐分支 + 显式 NonZero 实例 (3^∣b∣ ≢ 0 由 m^n≡0⇒m≡0)。
... | yes _ | yes _ = _/_ (81 * (2 ^ ∣ a ∣)) (3 ^ ∣ b ∣) {{powNZ b}}
... | yes _ | no  _ = _/_ (81 * (2 ^ ∣ a ∣)) 1 {{nonZero}}
... | no  _ | yes _ = _/_ (81 * 1) (3 ^ ∣ b ∣) {{powNZ b}}
... | no  _ | no  _ = _/_ (81 * 1) 1 {{nonZero}}

-- 损益操作对指数的影响
applySun : HarmonicExponents → HarmonicExponents
applySun (mkExp a b) = mkExp (a +ℤ + 1) (b -ℤ + 1)  -- 损：a+1, b-1

applyYi : HarmonicExponents → HarmonicExponents
applyYi (mkExp a b) = mkExp (a +ℤ + 2) (b -ℤ + 1)  -- 益：a+2, b-1

-- 十二律指数序列
twelveLüExponents : Vec HarmonicExponents 12
twelveLüExponents = 
  mkExp (+ 0) (+ 0) ∷   -- 黄钟 (0,0)
  mkExp (+ 1) (-[1+ 0 ]) ∷   -- 林钟 (1,-1)
  mkExp (+ 3) (-[1+ 1 ]) ∷   -- 太簇 (3,-2)
  mkExp (+ 4) (-[1+ 2 ]) ∷   -- 南吕 (4,-3)
  mkExp (+ 6) (-[1+ 3 ]) ∷   -- 姑洗 (6,-4)
  mkExp (+ 7) (-[1+ 4 ]) ∷   -- 应钟 (7,-5)
  mkExp (+ 9) (-[1+ 5 ]) ∷   -- 蕤宾 (9,-6)
  mkExp (+ 10) (-[1+ 6 ]) ∷  -- 大吕 (10,-7)
  mkExp (+ 12) (-[1+ 7 ]) ∷  -- 夷则 (12,-8)
  mkExp (+ 13) (-[1+ 8 ]) ∷  -- 夹钟 (13,-9)
  mkExp (+ 15) (-[1+ 9 ]) ∷  -- 无射 (15,-10)
  mkExp (+ 16) (-[1+ 10 ]) ∷ -- 仲吕 (16,-11)
  []

--------------------------------------------------------------------------------
-- 2. 损益方向性的不可逆性
--------------------------------------------------------------------------------

-- 定理：损益操作在 ℤ 指数上可逆 (2026-08 P0 轨道 A 处置)
-- 原 sunNotInvertible/yiNotInvertible (¬ 不可逆) 为假命题 —
--   见证: applySun (mkExp -1 +1) ≡ (0,0), applyYi (mkExp -2 +1) ≡ (0,0)。
--   "损益不可逆"教义仅对 ℕ 约束指数成立 (ℕ 版重述留待; 本模块指数为 ℤ)。
sunInvertible : Σ HarmonicExponents (λ inv → applySun inv ≡ mkExp (+ 0) (+ 0))
sunInvertible = mkExp (- (+ 1)) (+ 1) , refl

yiInvertible : Σ HarmonicExponents (λ inv → applyYi inv ≡ mkExp (+ 0) (+ 0))
yiInvertible = mkExp (- (+ 2)) (+ 1) , refl

-- 定理：指数 a 单调递增 / b 单调递减（损益链中）
-- 2026-08 P0 轨道 C: 原 2 条 postulate → 66+66 case 逐对证明 (0 postulate):
--   a 序列 0,1,3,4,6,7,9,10,12,13,15,16 递增; b 序列 0,-1,...,-11 递减,
--   每对 (i,j) 的 ≤ℤ 由 +≤+/m≤m+n 或 -≤-/-≤+ 直接给出。
aMonotonicallyIncreasing : ∀ (i j : Fin 12) → i < j →
  HarmonicExponents.a (lookup twelveLüExponents i) ≤ℤ
  HarmonicExponents.a (lookup twelveLüExponents j)
aMonotonicallyIncreasing (fzero) (fsuc (fzero)) (s≤s (z≤n)) = +≤+ (m≤m+n 0 1)
aMonotonicallyIncreasing (fzero) (fsuc (fsuc (fzero))) (s≤s (z≤n)) = +≤+ (m≤m+n 0 3)
aMonotonicallyIncreasing (fzero) (fsuc (fsuc (fsuc (fzero)))) (s≤s (z≤n)) = +≤+ (m≤m+n 0 4)
aMonotonicallyIncreasing (fzero) (fsuc (fsuc (fsuc (fsuc (fzero))))) (s≤s (z≤n)) = +≤+ (m≤m+n 0 6)
aMonotonicallyIncreasing (fzero) (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))) (s≤s (z≤n)) = +≤+ (m≤m+n 0 7)
aMonotonicallyIncreasing (fzero) (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))) (s≤s (z≤n)) = +≤+ (m≤m+n 0 9)
aMonotonicallyIncreasing (fzero) (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))))) (s≤s (z≤n)) = +≤+ (m≤m+n 0 10)
aMonotonicallyIncreasing (fzero) (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))))) (s≤s (z≤n)) = +≤+ (m≤m+n 0 12)
aMonotonicallyIncreasing (fzero) (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))))))) (s≤s (z≤n)) = +≤+ (m≤m+n 0 13)
aMonotonicallyIncreasing (fzero) (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))))))) (s≤s (z≤n)) = +≤+ (m≤m+n 0 15)
aMonotonicallyIncreasing (fzero) (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))))))))) (s≤s (z≤n)) = +≤+ (m≤m+n 0 16)
aMonotonicallyIncreasing (fsuc (fzero)) (fsuc (fsuc (fzero))) (s≤s (s≤s (z≤n))) = +≤+ (m≤m+n 1 2)
aMonotonicallyIncreasing (fsuc (fzero)) (fsuc (fsuc (fsuc (fzero)))) (s≤s (s≤s (z≤n))) = +≤+ (m≤m+n 1 3)
aMonotonicallyIncreasing (fsuc (fzero)) (fsuc (fsuc (fsuc (fsuc (fzero))))) (s≤s (s≤s (z≤n))) = +≤+ (m≤m+n 1 5)
aMonotonicallyIncreasing (fsuc (fzero)) (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))) (s≤s (s≤s (z≤n))) = +≤+ (m≤m+n 1 6)
aMonotonicallyIncreasing (fsuc (fzero)) (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))) (s≤s (s≤s (z≤n))) = +≤+ (m≤m+n 1 8)
aMonotonicallyIncreasing (fsuc (fzero)) (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))))) (s≤s (s≤s (z≤n))) = +≤+ (m≤m+n 1 9)
aMonotonicallyIncreasing (fsuc (fzero)) (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))))) (s≤s (s≤s (z≤n))) = +≤+ (m≤m+n 1 11)
aMonotonicallyIncreasing (fsuc (fzero)) (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))))))) (s≤s (s≤s (z≤n))) = +≤+ (m≤m+n 1 12)
aMonotonicallyIncreasing (fsuc (fzero)) (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))))))) (s≤s (s≤s (z≤n))) = +≤+ (m≤m+n 1 14)
aMonotonicallyIncreasing (fsuc (fzero)) (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))))))))) (s≤s (s≤s (z≤n))) = +≤+ (m≤m+n 1 15)
aMonotonicallyIncreasing (fsuc (fsuc (fzero))) (fsuc (fsuc (fsuc (fzero)))) (s≤s (s≤s (s≤s (z≤n)))) = +≤+ (m≤m+n 3 1)
aMonotonicallyIncreasing (fsuc (fsuc (fzero))) (fsuc (fsuc (fsuc (fsuc (fzero))))) (s≤s (s≤s (s≤s (z≤n)))) = +≤+ (m≤m+n 3 3)
aMonotonicallyIncreasing (fsuc (fsuc (fzero))) (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))) (s≤s (s≤s (s≤s (z≤n)))) = +≤+ (m≤m+n 3 4)
aMonotonicallyIncreasing (fsuc (fsuc (fzero))) (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))) (s≤s (s≤s (s≤s (z≤n)))) = +≤+ (m≤m+n 3 6)
aMonotonicallyIncreasing (fsuc (fsuc (fzero))) (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))))) (s≤s (s≤s (s≤s (z≤n)))) = +≤+ (m≤m+n 3 7)
aMonotonicallyIncreasing (fsuc (fsuc (fzero))) (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))))) (s≤s (s≤s (s≤s (z≤n)))) = +≤+ (m≤m+n 3 9)
aMonotonicallyIncreasing (fsuc (fsuc (fzero))) (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))))))) (s≤s (s≤s (s≤s (z≤n)))) = +≤+ (m≤m+n 3 10)
aMonotonicallyIncreasing (fsuc (fsuc (fzero))) (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))))))) (s≤s (s≤s (s≤s (z≤n)))) = +≤+ (m≤m+n 3 12)
aMonotonicallyIncreasing (fsuc (fsuc (fzero))) (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))))))))) (s≤s (s≤s (s≤s (z≤n)))) = +≤+ (m≤m+n 3 13)
aMonotonicallyIncreasing (fsuc (fsuc (fsuc (fzero)))) (fsuc (fsuc (fsuc (fsuc (fzero))))) (s≤s (s≤s (s≤s (s≤s (z≤n))))) = +≤+ (m≤m+n 4 2)
aMonotonicallyIncreasing (fsuc (fsuc (fsuc (fzero)))) (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))) (s≤s (s≤s (s≤s (s≤s (z≤n))))) = +≤+ (m≤m+n 4 3)
aMonotonicallyIncreasing (fsuc (fsuc (fsuc (fzero)))) (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))) (s≤s (s≤s (s≤s (s≤s (z≤n))))) = +≤+ (m≤m+n 4 5)
aMonotonicallyIncreasing (fsuc (fsuc (fsuc (fzero)))) (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))))) (s≤s (s≤s (s≤s (s≤s (z≤n))))) = +≤+ (m≤m+n 4 6)
aMonotonicallyIncreasing (fsuc (fsuc (fsuc (fzero)))) (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))))) (s≤s (s≤s (s≤s (s≤s (z≤n))))) = +≤+ (m≤m+n 4 8)
aMonotonicallyIncreasing (fsuc (fsuc (fsuc (fzero)))) (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))))))) (s≤s (s≤s (s≤s (s≤s (z≤n))))) = +≤+ (m≤m+n 4 9)
aMonotonicallyIncreasing (fsuc (fsuc (fsuc (fzero)))) (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))))))) (s≤s (s≤s (s≤s (s≤s (z≤n))))) = +≤+ (m≤m+n 4 11)
aMonotonicallyIncreasing (fsuc (fsuc (fsuc (fzero)))) (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))))))))) (s≤s (s≤s (s≤s (s≤s (z≤n))))) = +≤+ (m≤m+n 4 12)
aMonotonicallyIncreasing (fsuc (fsuc (fsuc (fsuc (fzero))))) (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))) (s≤s (s≤s (s≤s (s≤s (s≤s (z≤n)))))) = +≤+ (m≤m+n 6 1)
aMonotonicallyIncreasing (fsuc (fsuc (fsuc (fsuc (fzero))))) (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))) (s≤s (s≤s (s≤s (s≤s (s≤s (z≤n)))))) = +≤+ (m≤m+n 6 3)
aMonotonicallyIncreasing (fsuc (fsuc (fsuc (fsuc (fzero))))) (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))))) (s≤s (s≤s (s≤s (s≤s (s≤s (z≤n)))))) = +≤+ (m≤m+n 6 4)
aMonotonicallyIncreasing (fsuc (fsuc (fsuc (fsuc (fzero))))) (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))))) (s≤s (s≤s (s≤s (s≤s (s≤s (z≤n)))))) = +≤+ (m≤m+n 6 6)
aMonotonicallyIncreasing (fsuc (fsuc (fsuc (fsuc (fzero))))) (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))))))) (s≤s (s≤s (s≤s (s≤s (s≤s (z≤n)))))) = +≤+ (m≤m+n 6 7)
aMonotonicallyIncreasing (fsuc (fsuc (fsuc (fsuc (fzero))))) (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))))))) (s≤s (s≤s (s≤s (s≤s (s≤s (z≤n)))))) = +≤+ (m≤m+n 6 9)
aMonotonicallyIncreasing (fsuc (fsuc (fsuc (fsuc (fzero))))) (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))))))))) (s≤s (s≤s (s≤s (s≤s (s≤s (z≤n)))))) = +≤+ (m≤m+n 6 10)
aMonotonicallyIncreasing (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))) (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))) (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (z≤n))))))) = +≤+ (m≤m+n 7 2)
aMonotonicallyIncreasing (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))) (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))))) (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (z≤n))))))) = +≤+ (m≤m+n 7 3)
aMonotonicallyIncreasing (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))) (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))))) (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (z≤n))))))) = +≤+ (m≤m+n 7 5)
aMonotonicallyIncreasing (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))) (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))))))) (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (z≤n))))))) = +≤+ (m≤m+n 7 6)
aMonotonicallyIncreasing (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))) (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))))))) (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (z≤n))))))) = +≤+ (m≤m+n 7 8)
aMonotonicallyIncreasing (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))) (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))))))))) (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (z≤n))))))) = +≤+ (m≤m+n 7 9)
aMonotonicallyIncreasing (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))) (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))))) (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (z≤n)))))))) = +≤+ (m≤m+n 9 1)
aMonotonicallyIncreasing (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))) (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))))) (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (z≤n)))))))) = +≤+ (m≤m+n 9 3)
aMonotonicallyIncreasing (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))) (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))))))) (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (z≤n)))))))) = +≤+ (m≤m+n 9 4)
aMonotonicallyIncreasing (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))) (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))))))) (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (z≤n)))))))) = +≤+ (m≤m+n 9 6)
aMonotonicallyIncreasing (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))) (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))))))))) (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (z≤n)))))))) = +≤+ (m≤m+n 9 7)
aMonotonicallyIncreasing (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))))) (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))))) (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (z≤n))))))))) = +≤+ (m≤m+n 10 2)
aMonotonicallyIncreasing (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))))) (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))))))) (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (z≤n))))))))) = +≤+ (m≤m+n 10 3)
aMonotonicallyIncreasing (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))))) (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))))))) (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (z≤n))))))))) = +≤+ (m≤m+n 10 5)
aMonotonicallyIncreasing (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))))) (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))))))))) (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (z≤n))))))))) = +≤+ (m≤m+n 10 6)
aMonotonicallyIncreasing (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))))) (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))))))) (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (z≤n)))))))))) = +≤+ (m≤m+n 12 1)
aMonotonicallyIncreasing (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))))) (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))))))) (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (z≤n)))))))))) = +≤+ (m≤m+n 12 3)
aMonotonicallyIncreasing (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))))) (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))))))))) (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (z≤n)))))))))) = +≤+ (m≤m+n 12 4)
aMonotonicallyIncreasing (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))))))) (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))))))) (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (z≤n))))))))))) = +≤+ (m≤m+n 13 2)
aMonotonicallyIncreasing (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))))))) (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))))))))) (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (z≤n))))))))))) = +≤+ (m≤m+n 13 3)
aMonotonicallyIncreasing (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))))))) (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))))))))) (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (z≤n)))))))))))) = +≤+ (m≤m+n 15 1)

bMonotonicallyDecreasing : ∀ (i j : Fin 12) → i < j →
  HarmonicExponents.b (lookup twelveLüExponents j) ≤ℤ
  HarmonicExponents.b (lookup twelveLüExponents i)
bMonotonicallyDecreasing (fzero) (fsuc (fzero)) (s≤s (z≤n)) = -≤+
bMonotonicallyDecreasing (fzero) (fsuc (fsuc (fzero))) (s≤s (z≤n)) = -≤+
bMonotonicallyDecreasing (fzero) (fsuc (fsuc (fsuc (fzero)))) (s≤s (z≤n)) = -≤+
bMonotonicallyDecreasing (fzero) (fsuc (fsuc (fsuc (fsuc (fzero))))) (s≤s (z≤n)) = -≤+
bMonotonicallyDecreasing (fzero) (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))) (s≤s (z≤n)) = -≤+
bMonotonicallyDecreasing (fzero) (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))) (s≤s (z≤n)) = -≤+
bMonotonicallyDecreasing (fzero) (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))))) (s≤s (z≤n)) = -≤+
bMonotonicallyDecreasing (fzero) (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))))) (s≤s (z≤n)) = -≤+
bMonotonicallyDecreasing (fzero) (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))))))) (s≤s (z≤n)) = -≤+
bMonotonicallyDecreasing (fzero) (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))))))) (s≤s (z≤n)) = -≤+
bMonotonicallyDecreasing (fzero) (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))))))))) (s≤s (z≤n)) = -≤+
bMonotonicallyDecreasing (fsuc (fzero)) (fsuc (fsuc (fzero))) (s≤s (s≤s (z≤n))) = -≤- (m≤m+n 0 1)
bMonotonicallyDecreasing (fsuc (fzero)) (fsuc (fsuc (fsuc (fzero)))) (s≤s (s≤s (z≤n))) = -≤- (m≤m+n 0 2)
bMonotonicallyDecreasing (fsuc (fzero)) (fsuc (fsuc (fsuc (fsuc (fzero))))) (s≤s (s≤s (z≤n))) = -≤- (m≤m+n 0 3)
bMonotonicallyDecreasing (fsuc (fzero)) (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))) (s≤s (s≤s (z≤n))) = -≤- (m≤m+n 0 4)
bMonotonicallyDecreasing (fsuc (fzero)) (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))) (s≤s (s≤s (z≤n))) = -≤- (m≤m+n 0 5)
bMonotonicallyDecreasing (fsuc (fzero)) (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))))) (s≤s (s≤s (z≤n))) = -≤- (m≤m+n 0 6)
bMonotonicallyDecreasing (fsuc (fzero)) (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))))) (s≤s (s≤s (z≤n))) = -≤- (m≤m+n 0 7)
bMonotonicallyDecreasing (fsuc (fzero)) (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))))))) (s≤s (s≤s (z≤n))) = -≤- (m≤m+n 0 8)
bMonotonicallyDecreasing (fsuc (fzero)) (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))))))) (s≤s (s≤s (z≤n))) = -≤- (m≤m+n 0 9)
bMonotonicallyDecreasing (fsuc (fzero)) (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))))))))) (s≤s (s≤s (z≤n))) = -≤- (m≤m+n 0 10)
bMonotonicallyDecreasing (fsuc (fsuc (fzero))) (fsuc (fsuc (fsuc (fzero)))) (s≤s (s≤s (s≤s (z≤n)))) = -≤- (m≤m+n 1 1)
bMonotonicallyDecreasing (fsuc (fsuc (fzero))) (fsuc (fsuc (fsuc (fsuc (fzero))))) (s≤s (s≤s (s≤s (z≤n)))) = -≤- (m≤m+n 1 2)
bMonotonicallyDecreasing (fsuc (fsuc (fzero))) (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))) (s≤s (s≤s (s≤s (z≤n)))) = -≤- (m≤m+n 1 3)
bMonotonicallyDecreasing (fsuc (fsuc (fzero))) (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))) (s≤s (s≤s (s≤s (z≤n)))) = -≤- (m≤m+n 1 4)
bMonotonicallyDecreasing (fsuc (fsuc (fzero))) (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))))) (s≤s (s≤s (s≤s (z≤n)))) = -≤- (m≤m+n 1 5)
bMonotonicallyDecreasing (fsuc (fsuc (fzero))) (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))))) (s≤s (s≤s (s≤s (z≤n)))) = -≤- (m≤m+n 1 6)
bMonotonicallyDecreasing (fsuc (fsuc (fzero))) (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))))))) (s≤s (s≤s (s≤s (z≤n)))) = -≤- (m≤m+n 1 7)
bMonotonicallyDecreasing (fsuc (fsuc (fzero))) (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))))))) (s≤s (s≤s (s≤s (z≤n)))) = -≤- (m≤m+n 1 8)
bMonotonicallyDecreasing (fsuc (fsuc (fzero))) (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))))))))) (s≤s (s≤s (s≤s (z≤n)))) = -≤- (m≤m+n 1 9)
bMonotonicallyDecreasing (fsuc (fsuc (fsuc (fzero)))) (fsuc (fsuc (fsuc (fsuc (fzero))))) (s≤s (s≤s (s≤s (s≤s (z≤n))))) = -≤- (m≤m+n 2 1)
bMonotonicallyDecreasing (fsuc (fsuc (fsuc (fzero)))) (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))) (s≤s (s≤s (s≤s (s≤s (z≤n))))) = -≤- (m≤m+n 2 2)
bMonotonicallyDecreasing (fsuc (fsuc (fsuc (fzero)))) (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))) (s≤s (s≤s (s≤s (s≤s (z≤n))))) = -≤- (m≤m+n 2 3)
bMonotonicallyDecreasing (fsuc (fsuc (fsuc (fzero)))) (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))))) (s≤s (s≤s (s≤s (s≤s (z≤n))))) = -≤- (m≤m+n 2 4)
bMonotonicallyDecreasing (fsuc (fsuc (fsuc (fzero)))) (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))))) (s≤s (s≤s (s≤s (s≤s (z≤n))))) = -≤- (m≤m+n 2 5)
bMonotonicallyDecreasing (fsuc (fsuc (fsuc (fzero)))) (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))))))) (s≤s (s≤s (s≤s (s≤s (z≤n))))) = -≤- (m≤m+n 2 6)
bMonotonicallyDecreasing (fsuc (fsuc (fsuc (fzero)))) (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))))))) (s≤s (s≤s (s≤s (s≤s (z≤n))))) = -≤- (m≤m+n 2 7)
bMonotonicallyDecreasing (fsuc (fsuc (fsuc (fzero)))) (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))))))))) (s≤s (s≤s (s≤s (s≤s (z≤n))))) = -≤- (m≤m+n 2 8)
bMonotonicallyDecreasing (fsuc (fsuc (fsuc (fsuc (fzero))))) (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))) (s≤s (s≤s (s≤s (s≤s (s≤s (z≤n)))))) = -≤- (m≤m+n 3 1)
bMonotonicallyDecreasing (fsuc (fsuc (fsuc (fsuc (fzero))))) (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))) (s≤s (s≤s (s≤s (s≤s (s≤s (z≤n)))))) = -≤- (m≤m+n 3 2)
bMonotonicallyDecreasing (fsuc (fsuc (fsuc (fsuc (fzero))))) (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))))) (s≤s (s≤s (s≤s (s≤s (s≤s (z≤n)))))) = -≤- (m≤m+n 3 3)
bMonotonicallyDecreasing (fsuc (fsuc (fsuc (fsuc (fzero))))) (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))))) (s≤s (s≤s (s≤s (s≤s (s≤s (z≤n)))))) = -≤- (m≤m+n 3 4)
bMonotonicallyDecreasing (fsuc (fsuc (fsuc (fsuc (fzero))))) (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))))))) (s≤s (s≤s (s≤s (s≤s (s≤s (z≤n)))))) = -≤- (m≤m+n 3 5)
bMonotonicallyDecreasing (fsuc (fsuc (fsuc (fsuc (fzero))))) (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))))))) (s≤s (s≤s (s≤s (s≤s (s≤s (z≤n)))))) = -≤- (m≤m+n 3 6)
bMonotonicallyDecreasing (fsuc (fsuc (fsuc (fsuc (fzero))))) (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))))))))) (s≤s (s≤s (s≤s (s≤s (s≤s (z≤n)))))) = -≤- (m≤m+n 3 7)
bMonotonicallyDecreasing (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))) (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))) (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (z≤n))))))) = -≤- (m≤m+n 4 1)
bMonotonicallyDecreasing (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))) (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))))) (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (z≤n))))))) = -≤- (m≤m+n 4 2)
bMonotonicallyDecreasing (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))) (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))))) (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (z≤n))))))) = -≤- (m≤m+n 4 3)
bMonotonicallyDecreasing (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))) (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))))))) (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (z≤n))))))) = -≤- (m≤m+n 4 4)
bMonotonicallyDecreasing (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))) (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))))))) (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (z≤n))))))) = -≤- (m≤m+n 4 5)
bMonotonicallyDecreasing (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))) (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))))))))) (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (z≤n))))))) = -≤- (m≤m+n 4 6)
bMonotonicallyDecreasing (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))) (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))))) (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (z≤n)))))))) = -≤- (m≤m+n 5 1)
bMonotonicallyDecreasing (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))) (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))))) (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (z≤n)))))))) = -≤- (m≤m+n 5 2)
bMonotonicallyDecreasing (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))) (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))))))) (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (z≤n)))))))) = -≤- (m≤m+n 5 3)
bMonotonicallyDecreasing (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))) (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))))))) (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (z≤n)))))))) = -≤- (m≤m+n 5 4)
bMonotonicallyDecreasing (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))) (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))))))))) (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (z≤n)))))))) = -≤- (m≤m+n 5 5)
bMonotonicallyDecreasing (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))))) (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))))) (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (z≤n))))))))) = -≤- (m≤m+n 6 1)
bMonotonicallyDecreasing (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))))) (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))))))) (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (z≤n))))))))) = -≤- (m≤m+n 6 2)
bMonotonicallyDecreasing (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))))) (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))))))) (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (z≤n))))))))) = -≤- (m≤m+n 6 3)
bMonotonicallyDecreasing (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))))) (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))))))))) (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (z≤n))))))))) = -≤- (m≤m+n 6 4)
bMonotonicallyDecreasing (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))))) (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))))))) (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (z≤n)))))))))) = -≤- (m≤m+n 7 1)
bMonotonicallyDecreasing (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))))) (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))))))) (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (z≤n)))))))))) = -≤- (m≤m+n 7 2)
bMonotonicallyDecreasing (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))))) (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))))))))) (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (z≤n)))))))))) = -≤- (m≤m+n 7 3)
bMonotonicallyDecreasing (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))))))) (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))))))) (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (z≤n))))))))))) = -≤- (m≤m+n 8 1)
bMonotonicallyDecreasing (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))))))) (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))))))))) (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (z≤n))))))))))) = -≤- (m≤m+n 8 2)
bMonotonicallyDecreasing (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero))))))))))) (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fzero)))))))))))) (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (z≤n)))))))))))) = -≤- (m≤m+n 9 1)


--------------------------------------------------------------------------------
-- 3. 极向 144 与环向 46 的相位差
--------------------------------------------------------------------------------

-- 极向缠绕相位（模 144）
polarPhase : ℕ → Fin 144
polarPhase n = fromℕ< (m%n<n n 144)

-- 环向缠绕相位（模 46）
toroidalPhase : ℕ → Fin 46
toroidalPhase n = fromℕ< (m%n<n n 46)

-- 相位差 (2026-08 P0 修复: 原 if p ≥ t 的 ≥ 返回 Set 非 Bool —
--   改为对称差 (p ∸ t) + (t ∸ p) = |p − t|, 语义等价且免 if)
phaseDifference : ℕ → ℕ
phaseDifference n = 
  let p = toℕ (polarPhase n)
      t = toℕ (toroidalPhase n)
  in (p ∸ t) + (t ∸ p)

-- 定理：极向与环向周期不同
polarNotEqualToroidal : 144 ≢ 46
polarNotEqualToroidal = λ ()

-- 定理：相位差永不恒定（除非达到 LCM）
-- 2026-08 P0 证明 (原 hole): 见证 n=0 与 n=144 —
--   phaseDifference 0 = 0, phaseDifference 144 = 6, 故不存在常值 c。
phaseDiffNotConstant : ¬ (∃ λ c → (∀ n → phaseDifference n ≡ c))
phaseDiffNotConstant (c , h) =
  let h0 : phaseDifference 0 ≡ c ; h0 = h 0
      h144 : phaseDifference 144 ≡ c ; h144 = h 144
      six≠zero : 6 ≢ 0 ; six≠zero = λ ()
  in six≠zero (trans h144 (sym h0))

-- 完整环面巡游: 144 × 46 = 6624 (含相位/方向/角速度差)
-- 注: LCM(144,46)=3312 是代数简化, 丢失了几何信息, 已移除
FULL_TOUR_VALUE : ℕ
FULL_TOUR_VALUE = 6624

-- 定理：每 6624 步极向与环向完成一次完整巡游
-- 2026-08 P0 证明 (原 hole): 6624 = 46·144, [m+kn]%n≡m%n 给出
--   (n+6624)%144 ≡ n%144 与 (n+6624)%46 ≡ n%46, fromℕ<-cong 合成 Fin 相等,
--   相位差随之不变 (CanonicityAlignment 同款)。
phaseAlignment : ∀ (n : ℕ) →
  phaseDifference (n + FULL_TOUR_VALUE) ≡ phaseDifference n
phaseAlignment n =
  cong₂ (λ p t → (p ∸ t) + (t ∸ p)) (polarShift n) (toroidalShift n)
  where
    polarShift : ∀ n → toℕ (polarPhase (n + FULL_TOUR_VALUE)) ≡ toℕ (polarPhase n)
    polarShift n =
      trans (toℕ-fromℕ< (m%n<n (n + FULL_TOUR_VALUE) 144))
        (trans ([m+kn]%n≡m%n n 46 144) (sym (toℕ-fromℕ< (m%n<n n 144))))
    toroidalShift : ∀ n → toℕ (toroidalPhase (n + FULL_TOUR_VALUE)) ≡ toℕ (toroidalPhase n)
    toroidalShift n =
      trans (toℕ-fromℕ< (m%n<n (n + FULL_TOUR_VALUE) 46))
        (trans ([m+kn]%n≡m%n n 144 46) (sym (toℕ-fromℕ< (m%n<n n 46))))

--------------------------------------------------------------------------------
-- 4. 仲吕闭合：唯一非损益复位操作
--------------------------------------------------------------------------------

-- 仲吕闭合模运算
zhonglvModReset : ℤ → ℤ
zhonglvModReset acc = (acc *ℤ + 177147) /ℤ + 65536

-- 定理：仲吕闭合不是损益操作
-- 2026-08 P0 轨道 A 处置: 原 zhonglvNotSunYi (¬∃lg 全称) 为假命题 —
--   见证 acc=0, lg=Sun: zhonglvModReset 0 = 0 = applyLossGain 0 Sun
--   (0 ≡ + 0, refl 直证) — 公理使 ⊥ 可导出, 已删除。
--   事实: 仲吕闭合在 acc=0 处与损操作重合; "非损益复位"是相位语义
--   (模数缩放 177147/65536 vs 2/3), 非 ℤ 层逐点 ≠, 教义保留为注释。

-- 定理：仲吕闭合是唯一的非损益复位方式
-- 2026-08 P0 轨道 A 处置: 原 onlyResetMechanism 为假命题 —
--   见证 reset = λ acc → + applyLossGain (∣ acc ∣) Sun:
--   第一支在 acc=65536 失败 (43690 ≠ 177147), 第二支在任意 acc 失败
--   (lg=Sun 给出 ≡) — 两支皆伪, 公理使 ⊥ 可导出, 已删除。
--   "唯一复位方式"的宪法语义由 LossGain 表 + 仲吕相位锚定承载,
--   不以 ∀-覆盖任意函数的 ℤ 层命题驻留。

--------------------------------------------------------------------------------
-- 5. 非对称性的宪法定义
--------------------------------------------------------------------------------

-- 非对称性 = 极向 144 ≠ 环向 46
-- 2026-08 P0 修正: 原 proof 字段为 ¬∃inv (applySun inv ≡ (0,0)) — 假命题
--   (ℤ 指数上损益平移可逆, sunInvertible/yiInvertible 给出见证);
--   真实非对称性 = 缠绕周期不同 (polarNotEqualToroidal, λ() 已证)。
record Asymmetry : Set where
  field
    source : String  -- 非对称性来源
    proof : 144 ≢ 46

asymmetryEvidence : Asymmetry
asymmetryEvidence = record
  { source = "极向 144 ≠ 环向 46"
  ; proof = polarNotEqualToroidal
  }

-- 宪法定理：宇宙非对称性是缠绕数与泛音列公理的必然
universeAsymmetric : Asymmetry
universeAsymmetric = record
  { source = "极向144 ≠ 环向46，周期不同"
  ; proof = polarNotEqualToroidal
  }

-- 仲吕相位同步触发谓词
record ZhonglvPhaseSyncTriggered (n : ℕ) : Set where
  constructor syncAt
  field
    stepCount : ℕ
    stepIs : stepCount ≡ n

-- 定理：若损益可逆，则宇宙无呼吸（热寂）
-- 2026-08 P0 轨道 A 处置: 原 reversibleImpliesHeatDeath 若保留为公理将导出 ⊥ —
--   前提已在 ℤ 上可证 (sunInvertible), 而结论 ¬∃breath 被
--   syncAt 0 refl : ZhonglvPhaseSyncTriggered 0 直接反驳。已删除。
--   该"热寂反事实论证"的原意是: 在 ℕ 约束指数上损益才不可逆 —
--   教义保留为本注释, 不在 ℤ 指数模块驻留假命题。

--------------------------------------------------------------------------------
-- 6. 合法表述 vs 非法表述
--------------------------------------------------------------------------------

-- 合法表述
data LegalStatement : Set where
  WindingAsymmetry : LegalStatement  -- "极向144≠环向46"
  SunYiDirection : LegalStatement    -- "损益方向性不可逆"
  PhaseDiff : LegalStatement         -- "极向/环向相位差"
  ZhonglvReset : LegalStatement      -- "仲吕相位同步是唯一复位方式"

-- 非法表述（脱离缠绕数与泛音列的对称性讨论）
data IllegalStatement : Set where
  EuclideanSymmetry : IllegalStatement  -- "欧氏几何对称性"
  GroupSymmetry : IllegalStatement      -- "A₄/I_h/T_d 群对称"
  ReflectionSymmetry : IllegalStatement -- "反射对称"
  SymmetryBreaking : IllegalStatement   -- "对称性破缺"

-- 合法谓词：一个 Set 在律算宪法下是否合法
record IsLegal (A : Set) : Set where
  constructor mkLegal
  field
    legalStatement : LegalStatement

-- 宪法条款：禁止非法表述
-- 2026-08 P0 轨道 A 处置: 原 noIllegalSymmetry : ∀ s → ⊥ 为假命题 —
--   IllegalStatement 是含 4 个构造子的归纳类型 (EuclideanSymmetry 等),
--   noIllegalSymmetry EuclideanSymmetry : ⊥ 直证其反 (⊥ 可导出), 已删除。
--   "禁止非法表述"是书写/风格教义, 不以 ⊥ 公理驻留; 非法表述类型本身保留
--   (用于命名禁域, 不用于导出矛盾)。
postulate
  onlyLegalLanguage : ∀ (statement : Set) →
    IsLegal statement → LegalStatement
