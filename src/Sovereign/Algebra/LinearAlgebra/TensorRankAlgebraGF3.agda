{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Algebra.LinearAlgebra.TensorRankAlgebraGF3
-- M23: 秩分解上的四条通用操作 —— 为 Hopcroft–Kerr 的 2×2 排除论证（立项 C 的 C-T2）而建。
-- 指标集泛型: X Y Z 是任意集合, 只用到 Trit 上的求和。
--
-- 数学背景
--   设 T : X → Y → Z → Trit 有 r 项分解 T(x,y,z) = Σ_i a i x ⊗ (b i y ⊗ c i z)（M22 的 RankLE）。
--   下界论证反复用到四种「保持分解存在, 只改项数或张量」的操作:
--   ① rank-drop: 去掉一项恒零的项, 项数减一。
--   ② ★ slice-normalize —— Hopcroft–Kerr 的代换: 若 T 在 z = c 处的切片
--        T(x,y,c) ≡ f x ⊗ g y 是一个非零的秩一张量, 则分解可改写成
--        T = (f ⊗ g ⊗ w) ⊕ 余项, 其中 w : Z → Trit 满足 w c ≡ T₁, 余项只有 r − 1 项。
--        证明就是 Gauss 消元: 切片是各项的线性组合 Σ_i (c i c) ⊗ (a i ⊗ b i), 取系数非零的一项
--        把 f ⊗ g 解出来, 其余各项减去适当的倍数。Wang 框架 §5.3（引理 2, forced product）
--        与 §5.4（substitution）用的是同一条。
--   ③ ★ 切片张成的计数下界: 第一因子的系数 {a i} 张成所有「其余两个因子的切片的线性组合」
--        W λ x = Σ_j Σ_k λ j k ⊗ T x (eY j) (eZ k); 若这样的组合有 3^d 个两两不同, 则 d ≤ r。
--        这是 M16-B 展平下界的推广（那里只取 λ 为标准基, 得 n² ≤ r）;
--        forced product 里「残差展平 ≥ 4」说的是同一件事。
--   ④ ★ rank-linvar: 第一因子沿一对互逆的线性映射 (A, cA) 换元后, 分解搬回原张量。
--        M22 的 rank-invar 是它沿坐标点的版本; 这里是线性限制 rank-restrict 的逆向一半。
--
-- 为什么单独一件
--   · 这四条都与「2×2」无关, Bläser 的 19（C-T3）等后续路线同样要用; 放在一件里只证一次。
--   · 库内此前没有: M22 只有沿映射的拉回 / 搬回与线性限制的一半, M16-B 的张成引理只对
--     「标准基落在张成里」这一个 λ 证过。
--
-- 诚实边界
--   · 本件不改进任何下界数字; 结论在 TensorRankHK2GF3。
--   · 求和写在 Fin 上（sumFin）, 所以 ③ 的两个枚举 eY / eZ 与 ④ 的指标集都是 Fin。
--
-- 复用（先查后写）: sumFin / sumFin-cong / sumFin-zero(GF3LaplacianN) /
--   sumFin-add(GF3RankNullity) / sumFin-δ·δc(GF3Dim) / fromFun·toFun·toFun-fromFun(GF3Count) /
--   fromFun-cong(GF3BasisCount) / 3^-mono-<(GF3RankNullity) / sumFin-distrʳ·sumFin-swap₃·⊗-rot·δc-sym
--   (TensorRankFlattenGF3) / RankLE·⊗-swap₁₂·rank-swap·rank-rot(TensorRankIndexGF3)。
--   2×2 矩阵逆在 Synthesis/Representation/Matrix2Inverse —— 层序禁反向依赖, 本件不用。
--
-- 0 postulate / 0 REWRITE 规则 / 0 洞
module Sovereign.Algebra.LinearAlgebra.TensorRankAlgebraGF3 where

open import Data.Nat using (ℕ; zero; suc; pred; _^_; _≤_; _<_)
open import Data.Nat.Properties using (<⇒≱; ≮⇒≥)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.Fin.Properties using (injective⇒≤)
open import Data.Product using (_×_; _,_; proj₁; proj₂; Σ)
open import Data.Empty using (⊥; ⊥-elim)
open import Function.Definitions using (Injective)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; cong₂)
open import Relation.Nullary using (yes; no; Dec)

open import Sovereign.Base.Trit using
  (Trit; T₀; T₁; T₂; _⊕_; _⊗_; negate
  ; ⊕-identityˡ; ⊕-identityʳ; ⊕-comm; ⊕-assoc; ⊕-inverse
  ; ⊗-identityˡ; ⊗-identityʳ; ⊗-comm; ⊗-assoc; ⊗-zeroˡ; ⊗-zeroʳ
  ; ⊗-distribˡ-⊕; ⊗-distribʳ-⊕)
open import Sovereign.Algebra.LinearAlgebra.GF3LaplacianN using (sumFin; sumFin-cong; sumFin-zero)
open import Sovereign.Algebra.LinearAlgebra.GF3Dim using (δc; sumFin-δ)
open import Sovereign.Algebra.LinearAlgebra.GF3Count using (fromFun; toFun; fromFun-toFun; toFun-fromFun)
open import Sovereign.Algebra.LinearAlgebra.GF3BasisCount using (fromFun-cong)
open import Sovereign.Algebra.LinearAlgebra.GF3RankNullity using (sumFin-add; 3^-mono-<)
open import Sovereign.Algebra.LinearAlgebra.TensorRankFlattenGF3
  using (sumFin-distrʳ; sumFin-swap₃; ⊗-rot; δc-sym)
open import Sovereign.Algebra.LinearAlgebra.TensorRankIndexGF3 using (RankLE; ⊗-swap₁₂; rank-swap; rank-rot)

-- record 字段不随模块按名字导出, 本地打开泛型 record
open RankLE using (ra; rb; rc; rank-eq)

--------------------------------------------------------------------------------
-- §0 Trit 与 sumFin 的小引理
--------------------------------------------------------------------------------

-- 取反就是乘 T₂
negate-T₂ : ∀ x → negate x ≡ T₂ ⊗ x
negate-T₂ T₀ = refl
negate-T₂ T₁ = refl
negate-T₂ T₂ = refl

-- 取反对加法分配
neg-⊕ : ∀ a b → negate (a ⊕ b) ≡ (negate a) ⊕ (negate b)
neg-⊕ T₀ T₀ = refl
neg-⊕ T₀ T₁ = refl
neg-⊕ T₀ T₂ = refl
neg-⊕ T₁ T₀ = refl
neg-⊕ T₁ T₁ = refl
neg-⊕ T₁ T₂ = refl
neg-⊕ T₂ T₀ = refl
neg-⊕ T₂ T₁ = refl
neg-⊕ T₂ T₂ = refl

-- 取反对乘法: 左因子可以提出来
neg-⊗ˡ : ∀ k x → negate (k ⊗ x) ≡ k ⊗ (negate x)
neg-⊗ˡ k x =
  trans (negate-T₂ (k ⊗ x))
        (trans (sym (⊗-assoc T₂ k x))
               (trans (cong (λ v → v ⊗ x) (⊗-comm T₂ k))
                      (trans (⊗-assoc k T₂ x) (cong (λ v → k ⊗ v) (sym (negate-T₂ x))))))

-- 三因子轮换: a ⊗ (b ⊗ c) ≡ b ⊗ (c ⊗ a)
⊗-cycle : ∀ a b c → (a ⊗ (b ⊗ c)) ≡ (b ⊗ (c ⊗ a))
⊗-cycle a b c = trans (⊗-rot a b c) (⊗-rot c a b)

-- 后两个因子换位
⊗-swap₂₃ : ∀ a b c d → a ⊗ (b ⊗ (c ⊗ d)) ≡ a ⊗ (c ⊗ (b ⊗ d))
⊗-swap₂₃ a b c d = cong (λ v → a ⊗ v) (⊗-swap₁₂ c b d)

-- 四因子的换位: p ⊗ (q ⊗ (c ⊗ w)) ≡ w ⊗ (c ⊗ (p ⊗ q))
⊗-prod4 : ∀ p q c w → p ⊗ (q ⊗ (c ⊗ w)) ≡ w ⊗ (c ⊗ (p ⊗ q))
⊗-prod4 p q c w =
  trans (⊗-swap₂₃ p q c w)
        (trans (sym (⊗-swap₁₂ p c (q ⊗ w)))
               (trans (cong (λ v → c ⊗ v) (⊗-rot p q w)) (sym (⊗-swap₁₂ c w (p ⊗ q)))))

-- T₂ 从最里层挪到最外层
⊗-T₂-out : ∀ p q x → p ⊗ (q ⊗ (T₂ ⊗ x)) ≡ T₂ ⊗ (p ⊗ (q ⊗ x))
⊗-T₂-out p q x =
  trans (cong (λ v → p ⊗ v) (sym (⊗-swap₁₂ q T₂ x))) (sym (⊗-swap₁₂ p T₂ (q ⊗ x)))

-- 左因子提出求和: Σ (k ⊗ u i) ≡ k ⊗ Σ u i
sumFin-scale : ∀ {r} (k : Trit) (u : Fin r → Trit) →
  sumFin (λ i → (k ⊗ (u i))) ≡ k ⊗ sumFin u
sumFin-scale {zero} k u = sym (⊗-zeroʳ k)
sumFin-scale {suc r} k u =
  trans (cong (λ v → (k ⊗ (u fzero)) ⊕ v) (sumFin-scale k (λ i → u (fsuc i))))
        (sym (⊗-distribˡ-⊕ k (u fzero) (sumFin (λ i → u (fsuc i)))))

-- 取反提出求和: Σ negate (u i) ≡ negate (Σ u i)
sumFin-neg : ∀ {r} (u : Fin r → Trit) → sumFin (λ i → negate (u i)) ≡ negate (sumFin u)
sumFin-neg {zero} u = refl
sumFin-neg {suc r} u =
  trans (cong (λ v → (negate (u fzero)) ⊕ v) (sumFin-neg (λ i → u (fsuc i))))
        (sym (neg-⊕ (u fzero) (sumFin (λ i → u (fsuc i)))))

-- Σ negate (k ⊗ h i) ≡ negate (k ⊗ Σ h i)
sumFin-neg-scale : ∀ {r} (k : Trit) (h : Fin r → Trit) →
  sumFin (λ i → negate (k ⊗ (h i))) ≡ negate (k ⊗ sumFin h)
sumFin-neg-scale k h =
  trans (sumFin-cong (λ i → neg-⊗ˡ k (h i)))
        (trans (sumFin-scale k (λ i → negate (h i)))
               (trans (cong (λ v → k ⊗ v) (sumFin-neg h)) (sym (neg-⊗ˡ k (sumFin h)))))

-- 三因子的和交换: Σ_i u i ⊗ Σ_q (v q i ⊗ w q) ≡ Σ_q (Σ_i (u i ⊗ v q i)) ⊗ w q
--   内和提出左因子 u i → 结合 → sumFin-swap₃
sumFin-swap-lin : ∀ p q (u : Fin p → Trit) (v : Fin q → Fin p → Trit) (w : Fin q → Trit) →
  sumFin (λ i → (u i) ⊗ sumFin (λ j → ((v j i) ⊗ (w j)))) ≡
  sumFin (λ j → (sumFin (λ i → ((u i) ⊗ (v j i)))) ⊗ (w j))
sumFin-swap-lin p q u v w = trans s1 (trans s2 s3)
  where
  -- 内和提出左因子
  s1 : sumFin (λ i → (u i) ⊗ sumFin (λ j → ((v j i) ⊗ (w j)))) ≡
       sumFin (λ i → sumFin (λ j → ((u i) ⊗ ((v j i) ⊗ (w j)))))
  s1 = sumFin-cong (λ i → sym (sumFin-scale (u i) (λ j → (v j i) ⊗ (w j))))

  -- 结合
  s2 : sumFin (λ i → sumFin (λ j → ((u i) ⊗ ((v j i) ⊗ (w j))))) ≡
       sumFin (λ i → sumFin (λ j → (((u i) ⊗ (v j i)) ⊗ (w j))))
  s2 = sumFin-cong (λ i → sumFin-cong (λ j → sym (⊗-assoc (u i) (v j i) (w j))))

  -- 和交换
  s3 : sumFin (λ i → sumFin (λ j → (((u i) ⊗ (v j i)) ⊗ (w j)))) ≡
       sumFin (λ j → (sumFin (λ i → ((u i) ⊗ (v j i)))) ⊗ (w j))
  s3 = sym (sumFin-swap₃ p q (λ i j → (u i) ⊗ (v j i)) w)

-- Trit 上的可判定相等
infix 4 _≡ₜ?_
_≡ₜ?_ : (a b : Trit) → Dec (a ≡ b)
T₀ ≡ₜ? T₀ = yes refl
T₀ ≡ₜ? T₁ = no (λ ())
T₀ ≡ₜ? T₂ = no (λ ())
T₁ ≡ₜ? T₀ = no (λ ())
T₁ ≡ₜ? T₁ = yes refl
T₁ ≡ₜ? T₂ = no (λ ())
T₂ ≡ₜ? T₀ = no (λ ())
T₂ ≡ₜ? T₁ = no (λ ())
T₂ ≡ₜ? T₂ = yes refl

-- 和不为零 ⟹ 某一项不为零
sumFin-nonzero : ∀ {r} (g : Fin r → Trit) → sumFin g ≢ T₀ → Σ (Fin r) (λ i → g i ≢ T₀)
sumFin-nonzero {zero} g h = ⊥-elim (h refl)
sumFin-nonzero {suc r} g h with g fzero ≡ₜ? T₀
... | no neq = fzero , neq
... | yes eq =
  let ih = sumFin-nonzero (λ k → g (fsuc k))
                  (λ s → h (trans (cong (λ v → v ⊕ sumFin (λ k → g (fsuc k))) eq) s))
  in fsuc (proj₁ ih) , proj₂ ih

-- 非零元的逆（T₀ 上无定义, 取 T₀）
TritInv : Trit → Trit
TritInv T₀ = T₀
TritInv T₁ = T₁
TritInv T₂ = T₂

TritInv-nonzero : ∀ c → c ≢ T₀ → (TritInv c) ⊗ c ≡ T₁
TritInv-nonzero T₀ h = ⊥-elim (h refl)
TritInv-nonzero T₁ h = refl
TritInv-nonzero T₂ h = refl

--------------------------------------------------------------------------------
-- §1 去掉一项恒零的项
--------------------------------------------------------------------------------

-- Fin (suc r) 挖掉 i 之后的指标
skip : ∀ {r} → Fin (suc r) → Fin r → Fin (suc r)
skip fzero j = fsuc j
skip (fsuc i) fzero = fzero
skip (fsuc i) (fsuc j) = fsuc (skip i j)

-- 和在第 i 项处拆开
skip-sum : ∀ r (i : Fin (suc r)) (g : Fin (suc r) → Trit) →
  sumFin g ≡ (g i) ⊕ sumFin (λ j → g (skip i j))
skip-sum zero fzero g = refl
skip-sum (suc r) fzero g = refl
skip-sum (suc r) (fsuc i) g =
  trans (cong (λ v → (g fzero) ⊕ v) (skip-sum r i (λ k → g (fsuc k))))
        (trans (sym (⊕-assoc (g fzero) (g (fsuc i)) (sumFin (λ j → g (fsuc (skip i j))))))
               (trans (cong (λ v → v ⊕ (sumFin (λ j → g (fsuc (skip i j)))))
                              (⊕-comm (g fzero) (g (fsuc i))))
                      (⊕-assoc (g (fsuc i)) (g fzero) (sumFin (λ j → g (fsuc (skip i j)))))))

-- ★ 第 i 项的第一因子恒零 ⟹ 它对和张无贡献, 去掉后仍是 r 项分解
rank-drop : ∀ {X Y Z r} (T : X → Y → Z → Trit) (ρ : RankLE X Y Z T (suc r)) (i : Fin (suc r)) →
  (∀ x → ra ρ i x ≡ T₀) → RankLE X Y Z T r
rank-drop {X} {Y} {Z} {r} T ρ i h = record
  { ra = λ j x → ra ρ (skip i j) x
  ; rb = λ j y → rb ρ (skip i j) y
  ; rc = λ j z → rc ρ (skip i j) z
  ; rank-eq = prf }
  where
  -- 每一项
  g : ∀ x y z → Fin (suc r) → Trit
  g x y z k = (ra ρ k x) ⊗ ((rb ρ k y) ⊗ (rc ρ k z))

  -- 挖掉第 i 项之后的和
  rest-sum : ∀ x y z → Trit
  rest-sum x y z = sumFin (λ j → g x y z (skip i j))

  -- 第 i 项恒零
  gi-zero : ∀ x y z → g x y z i ≡ T₀
  gi-zero x y z =
    trans (cong (λ v → v ⊗ ((rb ρ i y) ⊗ (rc ρ i z))) (h x))
          (⊗-zeroˡ ((rb ρ i y) ⊗ (rc ρ i z)))

  prf : ∀ x y z → rest-sum x y z ≡ T x y z
  prf x y z = sym big
    where
    -- 最后一步: T₀ ⊕ 余和 ≡ 余和（按定义成立）
    last : (g x y z i) ⊕ rest-sum x y z ≡ rest-sum x y z
    last = trans (cong (λ v → v ⊕ rest-sum x y z) (gi-zero x y z)) refl

    big : T x y z ≡ rest-sum x y z
    big = trans (sym (rank-eq ρ x y z)) (trans (skip-sum r i (g x y z)) last)

-- 两个张量置换（给 rank-drop₃ 用; 显式写出, 免得内核去反演 sumFin 的模式匹配）
perm₁ : ∀ {X Y Z : Set} → (X → Y → Z → Trit) → Y → Z → X → Trit
perm₁ T y z x = T x y z

perm₂ : ∀ {X Y Z : Set} → (X → Y → Z → Trit) → Z → X → Y → Trit
perm₂ T z x y = T x y z

-- ★ 第 i 项的第三因子恒零 ⟹ 去掉后仍是 r 项分解
--   轮回两次把第三因子转到首位, 用 rank-drop, 再轮回回来
rank-drop₃ : ∀ {X Y Z r} (T : X → Y → Z → Trit) (ρ : RankLE X Y Z T (suc r)) (i : Fin (suc r)) →
  (∀ z → rc ρ i z ≡ T₀) → RankLE X Y Z T r
rank-drop₃ T ρ i h =
  rank-rot (perm₂ T) (rank-drop (perm₂ T) (rank-rot (perm₁ T) (rank-rot T ρ)) i h)

--------------------------------------------------------------------------------
-- §2 ★ 切片规范化（Hopcroft–Kerr 的代换）
--------------------------------------------------------------------------------

-- a ⊗ (b ⊗ (u ⊕ v)) ≡ (a ⊗ (b ⊗ u)) ⊕ (a ⊗ (b ⊗ v))
expand : ∀ (p q u v : Trit) → (p ⊗ (q ⊗ (u ⊕ v))) ≡ ((p ⊗ (q ⊗ u)) ⊕ (p ⊗ (q ⊗ v)))
expand p q u v =
  trans (cong (λ t → p ⊗ t) (⊗-distribˡ-⊕ q u v)) (⊗-distribˡ-⊕ p (q ⊗ u) (q ⊗ v))

-- 被减掉的那一半: p ⊗ (q ⊗ −(c₀ ⊗ w₀)) ≡ −(w₀ ⊗ (c₀ ⊗ (p ⊗ q)))
sub-term : ∀ (p q c₀ w₀ : Trit) → (p ⊗ (q ⊗ negate (c₀ ⊗ w₀))) ≡ negate (w₀ ⊗ (c₀ ⊗ (p ⊗ q)))
sub-term p q c₀ w₀ =
  trans (cong (λ v → p ⊗ (q ⊗ v)) (negate-T₂ (c₀ ⊗ w₀)))
        (trans (⊗-T₂-out p q (c₀ ⊗ w₀))
               (trans (cong (λ v → T₂ ⊗ v) (⊗-prod4 p q c₀ w₀))
                      (sym (negate-T₂ (w₀ ⊗ (c₀ ⊗ (p ⊗ q)))))))

-- ★★ 切片规范化: T 在 z = c 处的切片是非零的秩一张量 f ⊗ g ⟹
--   T = (f ⊗ g ⊗ w) ⊕ 余项, w c ≡ T₁, 余项只有 pred r 项。
--   读法: 分解里有一项被换成 f ⊗ g ⊗ w（把切片「照字面算出来」）, 代价是项数减一。
slice-normalize :
  ∀ {X Y Z r} (T : X → Y → Z → Trit) (c : Z) (f : X → Trit) (g : Y → Trit) →
  (∀ x y → T x y c ≡ (f x) ⊗ (g y)) →
  ∀ (x₀ : X) (y₀ : Y) → ((f x₀) ⊗ (g y₀)) ≢ T₀ →
  (ρ : RankLE X Y Z T r) →
  Σ (Z → Trit) (λ w → ((w c ≡ T₁) ×
    RankLE X Y Z (λ x y z → (T x y z) ⊕ negate ((f x) ⊗ ((g y) ⊗ (w z)))) (pred r)))
slice-normalize {r = zero} T c f g se x₀ y₀ nz ρ =
  ⊥-elim (nz (trans (sym (se x₀ y₀)) (sym (rank-eq ρ x₀ y₀ c))))
slice-normalize {X} {Y} {Z} {suc s} T c f g se x₀ y₀ nz ρ = w , w-at , rest
  where
  -- 项的第一、二因子的积
  M : Fin (suc s) → X → Y → Trit
  M i x y = (ra ρ i x) ⊗ (rb ρ i y)

  -- 切片的系数向量: Σ_i (rc i c) ⊗ (a i ⊗ b i) ≡ f ⊗ g
  slice-coef : ∀ x y → sumFin (λ i → (rc ρ i c) ⊗ (M i x y)) ≡ (f x) ⊗ (g y)
  slice-coef x y =
    trans (sumFin-cong (λ i → ⊗-cycle (rc ρ i c) (ra ρ i x) (rb ρ i y)))
          (trans (rank-eq ρ x y c) (se x y))

  -- 切片非零 ⟹ 系数向量非零
  nz' : sumFin (λ i → (rc ρ i c) ⊗ (M i x₀ y₀)) ≢ T₀
  nz' h = nz (trans (sym (slice-coef x₀ y₀)) h)

  -- 系数非零的一项
  step : Σ (Fin (suc s)) (λ i → (rc ρ i c) ≢ T₀)
  step = helper (sumFin-nonzero (λ i → (rc ρ i c) ⊗ (M i x₀ y₀)) nz')
    where
    helper : Σ (Fin (suc s)) (λ i → ((rc ρ i c) ⊗ (M i x₀ y₀)) ≢ T₀) →
             Σ (Fin (suc s)) (λ i → (rc ρ i c) ≢ T₀)
    helper (i , hi) =
      i , (λ eq → hi (trans (cong (λ v → v ⊗ (M i x₀ y₀)) eq) (⊗-zeroˡ (M i x₀ y₀))))

  i₀ : Fin (suc s)
  i₀ = proj₁ step

  k : Trit
  k = rc ρ i₀ c

  ki : Trit
  ki = TritInv k

  k-inv : (ki ⊗ k) ≡ T₁
  k-inv = TritInv-nonzero k (proj₂ step)

  -- 新项的第三因子: w z = k⁻¹ ⊗ rc i₀ z
  w : Z → Trit
  w z = ki ⊗ (rc ρ i₀ z)

  w-at : w c ≡ T₁
  w-at = k-inv

  -- 其余各项的第三因子: 减去 (rc i c ⊗ k⁻¹) 倍的 rc i₀
  rc' : Fin (suc s) → Z → Trit
  rc' i z = (rc ρ i z) ⊕ negate ((rc ρ i c) ⊗ (w z))

  -- 被解出来的那一项恢复成原来的第三因子
  restore : ∀ z → (k ⊗ (w z)) ≡ rc ρ i₀ z
  restore z =
    trans (sym (⊗-assoc k ki (rc ρ i₀ z)))
          (trans (cong (λ v → v ⊗ (rc ρ i₀ z)) (trans (⊗-comm k ki) k-inv)) (⊗-identityˡ (rc ρ i₀ z)))

  -- 第 i₀ 项被整个减掉
  zero-at : ∀ z → rc' i₀ z ≡ T₀
  zero-at z =
    trans (cong (λ v → (rc ρ i₀ z) ⊕ negate v) (restore z)) (⊕-inverse (rc ρ i₀ z))

  -- 改写后的恒等式（项数仍是 suc s, 第 i₀ 项恒零）
  eq : ∀ x y z → sumFin (λ i → (ra ρ i x) ⊗ ((rb ρ i y) ⊗ (rc' i z))) ≡
        (T x y z) ⊕ negate ((f x) ⊗ ((g y) ⊗ (w z)))
  eq x y z = proof
    where
    -- 每项里被减掉的那一半
    B : Fin (suc s) → Trit
    B i = (ra ρ i x) ⊗ ((rb ρ i y) ⊗ negate ((rc ρ i c) ⊗ (w z)))

    -- 原来的和
    S : Trit
    S = sumFin (λ i → (ra ρ i x) ⊗ ((rb ρ i y) ⊗ (rc ρ i z)))

    -- 分配 + 求和的加性
    step1 : sumFin (λ i → (ra ρ i x) ⊗ ((rb ρ i y) ⊗ (rc' i z))) ≡ S ⊕ sumFin B
    step1 =
      trans (sumFin-cong (λ i → expand (ra ρ i x) (rb ρ i y) (rc ρ i z)
                                              (negate ((rc ρ i c) ⊗ (w z)))))
            (sumFin-add (λ i → (ra ρ i x) ⊗ ((rb ρ i y) ⊗ (rc ρ i z))) B)

    -- 原分解
    step2 : S ⊕ sumFin B ≡ (T x y z) ⊕ sumFin B
    step2 = cong (λ v → v ⊕ sumFin B) (rank-eq ρ x y z)

    -- 被减掉的一半合起来是 w ⊗ 切片
    step3 : sumFin B ≡ negate ((w z) ⊗ ((f x) ⊗ (g y)))
    step3 =
      trans (sumFin-cong (λ i → sub-term (ra ρ i x) (rb ρ i y) (rc ρ i c) (w z)))
            (trans (sumFin-neg-scale (w z) (λ i → (rc ρ i c) ⊗ (M i x y)))
                   (cong (λ v → negate ((w z) ⊗ v)) (slice-coef x y)))

    -- 三因子轮换到目标形状
    step4 : (T x y z) ⊕ negate ((w z) ⊗ ((f x) ⊗ (g y))) ≡
            (T x y z) ⊕ negate ((f x) ⊗ ((g y) ⊗ (w z)))
    step4 = cong (λ v → (T x y z) ⊕ negate v) (⊗-cycle (w z) (f x) (g y))

    proof : sumFin (λ i → (ra ρ i x) ⊗ ((rb ρ i y) ⊗ (rc' i z))) ≡
            (T x y z) ⊕ negate ((f x) ⊗ ((g y) ⊗ (w z)))
    proof = trans step1 (trans step2 (trans (cong (λ v → (T x y z) ⊕ v) step3) step4))

  rest : RankLE X Y Z (λ x y z → (T x y z) ⊕ negate ((f x) ⊗ ((g y) ⊗ (w z)))) (pred (suc s))
  -- 余项（张量显式写出: 内核不会去反演 sumFin 的模式匹配来猜它）
  R : X → Y → Z → Trit
  R x y z = (T x y z) ⊕ negate ((f x) ⊗ ((g y) ⊗ (w z)))

  rest = rank-drop₃ R record { ra = ra ρ ; rb = rb ρ ; rc = rc' ; rank-eq = eq } i₀ zero-at

--------------------------------------------------------------------------------
-- §3 ★ 切片张成的计数下界
--------------------------------------------------------------------------------

-- 给定分解 ρ 与第二、三因子的枚举 eY / eZ:
--   第一因子的系数 {ra i} 张成所有切片的线性组合 W λ。
module SpanGen (X Y Z : Set) (T : X → Y → Z → Trit) (r : ℕ) (ρ : RankLE X Y Z T r)
                (m n : ℕ) (eY : Fin m → Y) (eZ : Fin n → Z) where

  -- 切片的线性组合: W q x = Σ_j Σ_k λ j k ⊗ T x (eY j) (eZ k)
  W : (Fin m → Fin n → Trit) → X → Trit
  W q x = sumFin (λ j → sumFin (λ k → (q j k) ⊗ (T x (eY j) (eZ k))))

  -- 坐标: coord q i = Σ_j Σ_k λ j k ⊗ (b i (eY j) ⊗ c i (eZ k))
  coord : (Fin m → Fin n → Trit) → Fin r → Trit
  coord q i = sumFin (λ j → sumFin (λ k → (q j k) ⊗ ((rb ρ i (eY j)) ⊗ (rc ρ i (eZ k)))))

  -- 每项: (λ ⊗ (b ⊗ c)) ⊗ a ≡ λ ⊗ (a ⊗ (b ⊗ c))
  rot-term : ∀ (q : Fin m → Fin n → Trit) (j : Fin m) (k : Fin n) (i : Fin r) (x : X) →
    ((q j k) ⊗ ((rb ρ i (eY j)) ⊗ (rc ρ i (eZ k)))) ⊗ (ra ρ i x) ≡
    (q j k) ⊗ ((ra ρ i x) ⊗ ((rb ρ i (eY j)) ⊗ (rc ρ i (eZ k))))
  rot-term q j k i x =
    trans (⊗-assoc (q j k) ((rb ρ i (eY j)) ⊗ (rc ρ i (eZ k))) (ra ρ i x))
          (cong (λ v → (q j k) ⊗ v)
                (⊗-comm ((rb ρ i (eY j)) ⊗ (rc ρ i (eZ k))) (ra ρ i x)))

  -- 对 i 求和后提公因子, 再用原分解
  inner-sum : ∀ (q : Fin m → Fin n → Trit) (j : Fin m) (k : Fin n) (x : X) →
    sumFin (λ i → ((q j k) ⊗ ((rb ρ i (eY j)) ⊗ (rc ρ i (eZ k)))) ⊗ (ra ρ i x)) ≡
    (q j k) ⊗ (T x (eY j) (eZ k))
  inner-sum q j k x =
    trans (sumFin-cong (λ i → rot-term q j k i x))
          (trans (sumFin-scale (q j k) (λ i → (ra ρ i x) ⊗ ((rb ρ i (eY j)) ⊗ (rc ρ i (eZ k)))))
                (cong (λ v → (q j k) ⊗ v) (rank-eq ρ x (eY j) (eZ k))))

  -- 固定 j: 先对 k 求和再对 i 求和 ⟹ 先对 i 求和再对 k 求和, 并算出内层
  per-j : ∀ (q : Fin m → Fin n → Trit) (j : Fin m) (x : X) →
    sumFin (λ i → (sumFin (λ k → (q j k) ⊗ ((rb ρ i (eY j)) ⊗ (rc ρ i (eZ k))))) ⊗ (ra ρ i x)) ≡
    sumFin (λ k → (q j k) ⊗ (T x (eY j) (eZ k)))
  per-j q j x =
    trans (sumFin-swap₃ n r (λ k i → (q j k) ⊗ ((rb ρ i (eY j)) ⊗ (rc ρ i (eZ k))))
                        (λ i → ra ρ i x))
          (sumFin-cong (λ k → inner-sum q j k x))

  -- ★★ 一切切片组合都在张成里: Σ_i (coord q i) ⊗ (a i x) ≡ W q x
  span-full : ∀ (q : Fin m → Fin n → Trit) (x : X) → sumFin (λ i → (coord q i) ⊗ (ra ρ i x)) ≡ W q x
  span-full q x =
    trans (sumFin-swap₃ m r (λ j i → sumFin (λ k → (q j k) ⊗ ((rb ρ i (eY j)) ⊗ (rc ρ i (eZ k)))))
                           (λ i → ra ρ i x))
          (sumFin-cong (λ j → per-j q j x))

  -- W 对权重的加性
  W-add : ∀ (q μ : Fin m → Fin n → Trit) (x : X) → W (λ j k → (q j k) ⊕ (μ j k)) x ≡ (W q x) ⊕ (W μ x)
  W-add q μ x = trans s1 s2
    where
    -- 内层分配
    inner : ∀ j → sumFin (λ k → ((q j k) ⊕ (μ j k)) ⊗ (T x (eY j) (eZ k))) ≡
                   (sumFin (λ k → (q j k) ⊗ (T x (eY j) (eZ k)))) ⊕
                   (sumFin (λ k → (μ j k) ⊗ (T x (eY j) (eZ k))))
    inner j = sumFin-distrʳ (λ k → (q j k)) (λ k → (μ j k)) (λ k → (T x (eY j) (eZ k)))

    s1 : W (λ j k → (q j k) ⊕ (μ j k)) x ≡
         sumFin (λ j → (sumFin (λ k → (q j k) ⊗ (T x (eY j) (eZ k)))) ⊕
                       (sumFin (λ k → (μ j k) ⊗ (T x (eY j) (eZ k)))))
    s1 = sumFin-cong inner

    -- 外层求和的加性
    s2 : sumFin (λ j → (sumFin (λ k → (q j k) ⊗ (T x (eY j) (eZ k)))) ⊕
                      (sumFin (λ k → (μ j k) ⊗ (T x (eY j) (eZ k))))) ≡
         (W q x) ⊕ (W μ x)
    s2 = sumFin-add (λ j → sumFin (λ k → (q j k) ⊗ (T x (eY j) (eZ k))))
                    (λ j → sumFin (λ k → (μ j k) ⊗ (T x (eY j) (eZ k))))

  -- W 对权重的齐性
  W-scale : ∀ (c : Trit) (q : Fin m → Fin n → Trit) (x : X) → W (λ j k → c ⊗ (q j k)) x ≡ c ⊗ (W q x)
  W-scale c q x = trans s1 s2
    where
    -- 内层: 结合后提出左因子
    inner : ∀ j → sumFin (λ k → (c ⊗ (q j k)) ⊗ (T x (eY j) (eZ k))) ≡
                   c ⊗ sumFin (λ k → (q j k) ⊗ (T x (eY j) (eZ k)))
    inner j =
      trans (sumFin-cong (λ k → ⊗-assoc c (q j k) (T x (eY j) (eZ k))))
            (sumFin-scale c (λ k → (q j k) ⊗ (T x (eY j) (eZ k))))

    s1 : W (λ j k → c ⊗ (q j k)) x ≡
         sumFin (λ j → c ⊗ sumFin (λ k → (q j k) ⊗ (T x (eY j) (eZ k))))
    s1 = sumFin-cong inner

    -- 外层提出左因子
    s2 : sumFin (λ j → c ⊗ sumFin (λ k → (q j k) ⊗ (T x (eY j) (eZ k)))) ≡ c ⊗ (W q x)
    s2 = sumFin-scale c (λ j → sumFin (λ k → (q j k) ⊗ (T x (eY j) (eZ k))))

  -- ★ 计数下界: 若 emb 把 Fin (3^d) 嵌入切片组合（处处取值相同则编号相同）, 则 d ≤ r。
  bound : ∀ d (emb : Fin (3 ^ d) → (Fin m → Fin n → Trit)) →
    (∀ κ κ' → (∀ x → W (emb κ) x ≡ W (emb κ') x) → κ ≡ κ') → d ≤ r
  bound d emb inj = ≮⇒≥ contra
    where
    φ : Fin (3 ^ d) → Fin (3 ^ r)
    φ κ = fromFun r (coord (emb κ))

    φ-injective : Injective _≡_ _≡_ φ
    φ-injective {κ} {κ'} h = inj κ κ' w-eq
      where
      -- (1) 坐标逐项相同
      t-eq : ∀ i → (coord (emb κ)) i ≡ (coord (emb κ')) i
      t-eq i = trans (sym (toFun-fromFun r (coord (emb κ)) i))
                     (trans (cong (λ z → toFun r z i) h) (toFun-fromFun r (coord (emb κ')) i))
      -- (2) 处处取值相同
      w-eq : ∀ x → W (emb κ) x ≡ W (emb κ') x
      w-eq x = trans (sym (span-full (emb κ) x))
                     (trans (sumFin-cong (λ i → cong (λ z → z ⊗ (ra ρ i x)) (t-eq i)))
                            (span-full (emb κ') x))

    contra : r < d → ⊥
    contra hlt = <⇒≱ (3^-mono-< hlt) (injective⇒≤ φ-injective)

--------------------------------------------------------------------------------
-- §4 ★ 线性换元
--------------------------------------------------------------------------------

-- ★ 线性不变性: TW w = Σ_k (A k w) ⊗ TK k 是 TK 沿 A 的线性限制;
--   若 cA 是它的左逆（Σ_w cA w k₀ ⊗ A k w ≡ δ k k₀）, 则 TW 的分解搬回 TK。
--   构造: a 复合 cA。与 M22 rank-restrict 合起来: 沿「有左逆的线性映射」限制不改变可分解性。
rank-linvar : ∀ {k m r} {Y Z : Set} (TK : Fin m → Y → Z → Trit) (A : Fin m → Fin k → Trit)
              (cA : Fin k → Fin m → Trit) →
  (∀ k' k₀ → sumFin (λ w → (cA w k₀) ⊗ (A k' w)) ≡ δc k' k₀) →
  ∀ (TW : Fin k → Y → Z → Trit) →
  (∀ w y z → TW w y z ≡ sumFin (λ k → (A k w) ⊗ (TK k y z))) →
  RankLE (Fin k) Y Z TW r → RankLE (Fin m) Y Z TK r
rank-linvar {k} {m} {r} {Y} {Z} TK A cA inv TW rel ρ = record
  { ra = λ i k₀ → sumFin (λ w → (cA w k₀) ⊗ (ra ρ i w))
  ; rb = rb ρ
  ; rc = rc ρ
  ; rank-eq = prf }
  where
  prf : ∀ k₀ y z →
    sumFin (λ i → (sumFin (λ w → (cA w k₀) ⊗ (ra ρ i w))) ⊗ ((rb ρ i y) ⊗ (rc ρ i z))) ≡ TK k₀ y z
  prf k₀ y z = sym chain
    where
    -- (1) δ 挑出第 k₀ 个切片
    s1 : TK k₀ y z ≡ sumFin (λ k' → (δc k' k₀) ⊗ (TK k' y z))
    s1 = sym (trans (sumFin-cong (λ k' → cong (λ v → v ⊗ (TK k' y z)) (δc-sym k' k₀)))
                    (sumFin-δ (λ k' → TK k' y z) k₀))
    -- (2) δ 换成 cA 与 A 的乘积
    s2 : sumFin (λ k' → (δc k' k₀) ⊗ (TK k' y z)) ≡
         sumFin (λ k' → (sumFin (λ w → (cA w k₀) ⊗ (A k' w))) ⊗ (TK k' y z))
    s2 = sumFin-cong (λ k' → cong (λ v → v ⊗ (TK k' y z)) (sym (inv k' k₀)))
    -- (3) 和交换: 先对外面的 k' 求和
    s3 : sumFin (λ k' → (sumFin (λ w → (cA w k₀) ⊗ (A k' w))) ⊗ (TK k' y z)) ≡
         sumFin (λ w → (cA w k₀) ⊗ sumFin (λ k' → (A k' w) ⊗ (TK k' y z)))
    s3 = sym (sumFin-swap-lin k m (λ w → cA w k₀) (λ k' w → A k' w) (λ k' → TK k' y z))
    -- (4) 认出限制张量, 用它的分解
    s4 : sumFin (λ w → (cA w k₀) ⊗ sumFin (λ k' → (A k' w) ⊗ (TK k' y z))) ≡
         sumFin (λ w → (cA w k₀) ⊗ sumFin (λ i → (ra ρ i w) ⊗ ((rb ρ i y) ⊗ (rc ρ i z))))
    s4 = sumFin-cong (λ w → trans (cong (λ v → (cA w k₀) ⊗ v) (sym (rel w y z))) (cong (λ v → (cA w k₀) ⊗ v) (sym (rank-eq ρ w y z))))
    -- (5) 和交换: 先对 w 求和
    s5 : sumFin (λ w → (cA w k₀) ⊗ sumFin (λ i → (ra ρ i w) ⊗ ((rb ρ i y) ⊗ (rc ρ i z)))) ≡
         sumFin (λ i → (sumFin (λ w → (cA w k₀) ⊗ (ra ρ i w))) ⊗ ((rb ρ i y) ⊗ (rc ρ i z)))
    s5 = sumFin-swap-lin k r (λ w → cA w k₀) (λ i w → ra ρ i w) (λ i → (rb ρ i y) ⊗ (rc ρ i z))

    chain : TK k₀ y z ≡ sumFin (λ i → (sumFin (λ w → (cA w k₀) ⊗ (ra ρ i w))) ⊗ ((rb ρ i y) ⊗ (rc ρ i z)))
    chain = trans s1 (trans s2 (trans s3 (trans s4 s5)))

-- ★ 第二因子的线性换元
rank-change₂ : ∀ {X Z k m r} (TK : X → Fin m → Z → Trit) (A : Fin m → Fin k → Trit)
               (cA : Fin k → Fin m → Trit) →
  (∀ k' k₀ → sumFin (λ w → (cA w k₀) ⊗ (A k' w)) ≡ δc k' k₀) →
  ∀ (TW : X → Fin k → Z → Trit) →
  (∀ x w z → TW x w z ≡ sumFin (λ k → (A k w) ⊗ (TK x k z))) →
  RankLE X (Fin k) Z TW r → RankLE X (Fin m) Z TK r
rank-change₂ TK A cA inv TW rel ρ =
  rank-swap (λ k x z → TK x k z)
    (rank-linvar (λ k x z → TK x k z) A cA inv (λ w x z → TW x w z) (λ w x z → rel x w z)
                            (rank-swap TW ρ))

-- ★ 第三因子的线性换元
rank-change₃ : ∀ {X Y k m r} (TK : X → Y → Fin m → Trit) (B : Fin m → Fin k → Trit)
               (cB : Fin k → Fin m → Trit) →
  (∀ k' k₀ → sumFin (λ w → (cB w k₀) ⊗ (B k' w)) ≡ δc k' k₀) →
  ∀ (TW : X → Y → Fin k → Trit) →
  (∀ x y w → TW x y w ≡ sumFin (λ k → (B k w) ⊗ (TK x y k))) →
  RankLE X Y (Fin k) TW r → RankLE X Y (Fin m) TK r
--   (w, x, y) ↦ 先轮回成 (y, w, x), 再对换成 (w, y, x); 换元后 (k, y, x) ↦ 轮回成 (y, x, k), 对换成 (x, y, k)
rank-change₃ TK B cB inv TW rel ρ =
  rank-swap (λ y x k → TK x y k)
    (rank-rot (λ k y x → TK x y k)
      (rank-linvar (λ k y x → TK x y k) B cB inv (λ w y x → TW x y w) (λ w y x → rel x y w)
        (rank-swap (λ y w x → TW x y w) (rank-rot TW ρ))))

-- ★ 张量逐点相等到处可搬
rank-cong : ∀ {X Y Z r} {T T' : X → Y → Z → Trit} →
  (∀ x y z → T x y z ≡ T' x y z) → RankLE X Y Z T r → RankLE X Y Z T' r
rank-cong h ρ = record
  { ra = ra ρ
  ; rb = rb ρ
  ; rc = rc ρ
  ; rank-eq = λ x y z → trans (rank-eq ρ x y z) (h x y z) }
