{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Algebra.LinearAlgebra.TensorRankGF3
-- M16-A: GF(3) 上矩阵乘法张量的**秩分解**——陈述层与 M13 接桥
-- （M16-B 展平下界 n² ≤ r 在 TensorRankFlattenGF3）
--
-- 数学背景
--   n×n 矩阵乘法张量 ⟨n,n,n⟩ 的结构常数是
--     T(x,y,z) = [x.1 = z.1 ∧ x.2 = y.1 ∧ y.2 = z.2],
--   其中 x = (i,j) 是左输入位置, y = (j,k) 是右输入位置, z = (i,k) 是输出位置。
--   「r 项秩分解」是三组系数 a, b, c : Fin r → … → Trit, 使
--     Σ_k a k x ⊗ b k y ⊗ c k z ≡ T(x,y,z)    对一切指标三元组成立。
--   最小的 r 就是张量秩; 每个秩分解就是一个双线性算法。
--
-- 为什么有这一件
--   OpenAI 的 ω = 9/4（每域）在 GF(3) 上的全部内容, 是一族关于这个谓词的有限命题:
--     ∀ n ≥ 2, r:  RankLE₃ n r → n^9 ≤ r^4
--   （Lean `key/MatrixExponent.lean:45 square_iff_prime_ranks` 在 p = 3 的实例;
--     头注原话: The obstruction can be checked entirely on finite rank decompositions）。
--   在本件之前这个谓词在本库不存在——那句话在我们这边连陈述都写不出。
--   本件镜像 Lean 的谓词定义（`RationalCircuits.lean:48 RankLE`）,
--   并把 M13（Strassen 的七乘方案）接上去: M13 说的正是「T₂ 有一个 7 项秩分解」。
--
-- 内容
--   §1 谓词 RankLE₃（结构常数形式）
--   §2 M13 接桥: 七门拆成 α_k ⊗ β_k 与输出系数 c_k
--      ★ strassen-is-rank-form : 对任意矩阵, 秩分解的和就是 Strassen 的输出
--      ★ rank-strassen       : RankLE₃ 2 7
--   §3 外部边界（无居民）: ω₃-boundary（下半; 上半的陈述与两半的关系在 TensorRankUpperGF3）
--
-- 诚实边界
--   · 本件**不证** n^9 ≤ r^4。那是外部定理（Lean 里有证明; 本库未导入、未复现）。
--   · rank-strassen 只是上界见证（秩 ≤ 7）, 不是「秩恰为 7」。
--     下界有两个: 展平下界 n² ≤ r（`TensorRankFlattenGF3.rank-lower`, n = 2 时即 r ≥ 4）;
--     n = 2 的精确下界 r ≥ 7 由 Hopcroft–Kerr 的排除论证给出
--     （`TensorRankHK2GF3.rank-2x2-lower`, 2026-11-28; 见 `TensorRankHK2GF3.rank₂₂₂-is-7`:
--     下半 rank-2x2-lower, 上半本件的 rank-strassen）。
--   · 先算后验: engineering/oracle_tensor_rank_gf3.py 的三条判据（64 个结构常数 /
--     6561 组输入走普通矩阵乘法 / 基矩阵两路会合）。
--     oracle 另能按指标三元组发射 64 条 refl 子句; 本件 §2 **没有**贴用它们,
--     实际组织是「任意矩阵的接桥（strassen-is-rank-form）+ 16 对基矩阵 × 4 个输出位置的 refl
--     （mm-basis）」, 两者的数值对应就是判据三。
--
-- 0 postulate / 0 hole

module Sovereign.Algebra.LinearAlgebra.TensorRankGF3 where

open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _^_; _≤_)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.Fin.Properties using (_≟_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂)
open import Relation.Nullary using (yes; no)

open import Sovereign.Base.Trit using
  (Trit; T₀; T₁; T₂; _⊕_; _⊗_; negate
  ; ⊕-identityˡ; ⊕-identityʳ; ⊕-assoc; ⊗-assoc; ⊗-identityʳ; ⊗-zeroʳ)
open import Sovereign.Algebra.LinearAlgebra.GF3LaplacianN using (sumFin; sumFin-cong)
open import Sovereign.Algebra.LinearAlgebra.Matrix2
  using (Mat2; mkMat2; m00; m01; m10; m11)
open import Sovereign.Algebra.LinearAlgebra.StrassenGF3
  using (m1; m2; m3; m4; m5; m6; m7; strassen; mul₃; strassen-correct)

--------------------------------------------------------------------------------
-- §1. 谓词: 矩阵乘法张量的结构常数与秩分解
--------------------------------------------------------------------------------

-- 左 / 右输入位置 (行, 列)
Pos : ℕ → Set
Pos n = Fin n × Fin n

-- 输出位置 (行, 列)
Out : ℕ → Set
Out n = Fin n × Fin n

-- 指示: 相等取 T₁, 否则 T₀
oneIf : ∀ {n} → Fin n → Fin n → Trit
oneIf i j with i ≟ j
... | yes _ = T₁
... | no  _ = T₀

-- ★ 矩阵乘法张量 ⟨n,n,n⟩ 的结构常数
--   三个条件的合取写成指示函数之积（0/1 值的乘积就是合取）
mm : (n : ℕ) → Pos n → Pos n → Out n → Trit
mm n x y z =
  (oneIf (proj₁ x) (proj₁ z)) ⊗ ((oneIf (proj₂ x) (proj₁ y)) ⊗ (oneIf (proj₂ y) (proj₂ z)))

-- ★ r 项秩分解（镜像 Lean `RationalCircuits.lean:48 RankLE`）
record RankLE₃ (n r : ℕ) : Set where
  field
    ra : Fin r → Pos n → Trit
    rb : Fin r → Pos n → Trit
    rc : Fin r → Out n → Trit
    rank-eq : ∀ x y z → sumFin (λ i → (ra i x) ⊗ ((rb i y) ⊗ (rc i z))) ≡ mm n x y z

--------------------------------------------------------------------------------
-- §2. M13 接桥
--------------------------------------------------------------------------------

-- 位置 → 矩阵元 / 矩阵元 → 位置 的两个读法
at : Mat2 Trit → Pos 2 → Trit
at A (fzero , fzero) = m00 A
at A (fzero , fsuc fzero) = m01 A
at A (fsuc fzero , fzero) = m10 A
at A (fsuc fzero , fsuc fzero) = m11 A

-- 基矩阵: 只在位置 x 处取 T₁
E : Pos 2 → Mat2 Trit
E (fzero , fzero) = mkMat2 T₁ T₀ T₀ T₀
E (fzero , fsuc fzero) = mkMat2 T₀ T₁ T₀ T₀
E (fsuc fzero , fzero) = mkMat2 T₀ T₀ T₁ T₀
E (fsuc fzero , fsuc fzero) = mkMat2 T₀ T₀ T₀ T₁

-- A 的七个线性型 α_k（与 M13 的 m1 … m7 逐门对应）
L : Fin 7 → Mat2 Trit → Trit
L fzero A = m00 A ⊕ m11 A
L (fsuc fzero) A = m10 A ⊕ m11 A
L (fsuc (fsuc fzero)) A = m00 A
L (fsuc (fsuc (fsuc fzero))) A = m11 A
L (fsuc (fsuc (fsuc (fsuc fzero)))) A = m00 A ⊕ m01 A
L (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))) A = m10 A ⊕ negate (m00 A)
L (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))) A = m01 A ⊕ negate (m11 A)

-- B 的七个线性型 β_k
R : Fin 7 → Mat2 Trit → Trit
R fzero B = m00 B ⊕ m11 B
R (fsuc fzero) B = m00 B
R (fsuc (fsuc fzero)) B = m01 B ⊕ negate (m11 B)
R (fsuc (fsuc (fsuc fzero))) B = m10 B ⊕ negate (m00 B)
R (fsuc (fsuc (fsuc (fsuc fzero)))) B = m11 B
R (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))) B = m00 B ⊕ m01 B
R (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))) B = m10 B ⊕ m11 B

-- M13 的七门排成一张表
mTab : Fin 7 → Mat2 Trit → Mat2 Trit → Trit
mTab fzero = m1
mTab (fsuc fzero) = m2
mTab (fsuc (fsuc fzero)) = m3
mTab (fsuc (fsuc (fsuc fzero))) = m4
mTab (fsuc (fsuc (fsuc (fsuc fzero)))) = m5
mTab (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))) = m6
mTab (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))) = m7

-- 每一门恰是 α_k ⊗ β_k
LR : ∀ i A B → (L i A) ⊗ (R i B) ≡ mTab i A B
LR fzero (mkMat2 a _ _ d) (mkMat2 e _ _ h) = refl
LR (fsuc fzero) (mkMat2 _ _ c d) (mkMat2 e _ _ _) = refl
LR (fsuc (fsuc fzero)) (mkMat2 a _ _ _) (mkMat2 _ f _ h) = refl
LR (fsuc (fsuc (fsuc fzero))) (mkMat2 _ _ _ d) (mkMat2 e _ g _) = refl
LR (fsuc (fsuc (fsuc (fsuc fzero)))) (mkMat2 a b _ _) (mkMat2 _ _ _ h) = refl
LR (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))) (mkMat2 a _ c _) (mkMat2 e f _ _) = refl
LR (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))) (mkMat2 _ b _ d) (mkMat2 _ _ g h) = refl

-- 输出系数 c_k(z): M13 的输出组合里第 k 门的系数
--   out00 = m1 ⊕ m4 ⊖ m5 ⊕ m7;  out01 = m3 ⊕ m5;
--   out10 = m2 ⊕ m4;            out11 = m1 ⊖ m2 ⊕ m3 ⊕ m6
C : Fin 7 → Out 2 → Trit
C fzero (fzero , fzero) = T₁
C fzero (fsuc fzero , fsuc fzero) = T₁
C (fsuc fzero) (fsuc fzero , fzero) = T₁
C (fsuc fzero) (fsuc fzero , fsuc fzero) = T₂
C (fsuc (fsuc fzero)) (fzero , fsuc fzero) = T₁
C (fsuc (fsuc fzero)) (fsuc fzero , fsuc fzero) = T₁
C (fsuc (fsuc (fsuc fzero))) (fzero , fzero) = T₁
C (fsuc (fsuc (fsuc fzero))) (fsuc fzero , fzero) = T₁
C (fsuc (fsuc (fsuc (fsuc fzero)))) (fzero , fzero) = T₂
C (fsuc (fsuc (fsuc (fsuc fzero)))) (fzero , fsuc fzero) = T₁
C (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))) (fsuc fzero , fsuc fzero) = T₁
C (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))) (fzero , fzero) = T₁
C _ _ = T₀

-- 乘以 T₀ / T₁ / T₂ 分别是: 归零 / 不变 / 取负
sc : Trit → Trit → Trit
sc T₀ _ = T₀
sc T₁ x = x
sc T₂ x = negate x

⊗-sc : ∀ k x → x ⊗ k ≡ sc k x
⊗-sc T₀ T₀ = refl
⊗-sc T₀ T₁ = refl
⊗-sc T₀ T₂ = refl
⊗-sc T₁ T₀ = refl
⊗-sc T₁ T₁ = refl
⊗-sc T₁ T₂ = refl
⊗-sc T₂ T₀ = refl
⊗-sc T₂ T₁ = refl
⊗-sc T₂ T₂ = refl

-- M13 的输出组合, 写成门的函数（下标用完整的构造子数字: C 的子句按构造子匹配,
-- 定义名缩写不会被统一器展开）
combo : Out 2 → (Fin 7 → Trit) → Trit
combo (fzero , fzero) m = (((m fzero) ⊕ (m (fsuc (fsuc (fsuc fzero))))) ⊕ (negate (m (fsuc (fsuc (fsuc (fsuc fzero))))))) ⊕ (m (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))))
combo (fzero , fsuc fzero) m = (m (fsuc (fsuc fzero))) ⊕ (m (fsuc (fsuc (fsuc (fsuc fzero)))))
combo (fsuc fzero , fzero) m = (m (fsuc fzero)) ⊕ (m (fsuc (fsuc (fsuc fzero))))
combo (fsuc fzero , fsuc fzero) m = (((m fzero) ⊕ (negate (m (fsuc fzero)))) ⊕ (m (fsuc (fsuc fzero)))) ⊕ (m (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))

-- Strassen 的输出就是 combo 作用在七门上
at-strassen : ∀ A B z → at (strassen A B) z ≡ combo z (λ i → mTab i A B)
at-strassen A B (fzero , fzero) = refl
at-strassen A B (fzero , fsuc fzero) = refl
at-strassen A B (fsuc fzero , fzero) = refl
at-strassen A B (fsuc fzero , fsuc fzero) = refl

-- Fin 7 上和的完全展开式（右嵌套）
nest7 : (Fin 7 → Trit) → Trit
nest7 g =   (g fzero) ⊕ ((g (fsuc fzero)) ⊕ ((g (fsuc (fsuc fzero))) ⊕ ((g (fsuc (fsuc (fsuc fzero)))) ⊕ ((g (fsuc (fsuc (fsuc (fsuc fzero))))) ⊕ ((g (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))) ⊕ ((g (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))) ⊕ T₀))))))

-- 按定义成立
sumFin7 : ∀ (g : Fin 7 → Trit) → sumFin g ≡ nest7 g
sumFin7 g = refl

-- 归一化后的被加项: 第 i 项是 m i 乘以系数 C i z
g7 : Out 2 → (Fin 7 → Trit) → Fin 7 → Trit
g7 z m i = sc (C i z) (m i)

-- 两把改写工具: 在「a ⊕ ·」与「a ⊕ (b ⊕ (c ⊕ ·))」的位置改写（显式 λ, 不产生元变量）
cong₁ : ∀ a y z → y ≡ z → (a ⊕ y) ≡ (a ⊕ z)
cong₁ a y z e = cong (λ t → a ⊕ t) e

cong₃ : ∀ a b c y z → y ≡ z → (a ⊕ (b ⊕ (c ⊕ y))) ≡ (a ⊕ (b ⊕ (c ⊕ z)))
cong₃ a b c y z e = cong (λ t → a ⊕ (b ⊕ (c ⊕ t))) e

-- 展开后的嵌套式整理成 combo: 零项按定义消去（第一段 refl）, 再用 ⊕ 的单位律与结合律
norm : ∀ z m → nest7 (g7 z m) ≡ combo z m
norm (fzero , fzero) m =
  trans refl
    (trans (cong₃ (m fzero) (m (fsuc (fsuc (fsuc fzero)))) (negate (m (fsuc (fsuc (fsuc (fsuc fzero)))))) (((m (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))) ⊕ T₀)) (m (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))) (⊕-identityʳ (m (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))))))
      (trans (sym (⊕-assoc (m fzero) (m (fsuc (fsuc (fsuc fzero)))) ((negate (m (fsuc (fsuc (fsuc (fsuc fzero)))))) ⊕ (m (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))))))
        (sym (⊕-assoc ((m fzero) ⊕ (m (fsuc (fsuc (fsuc fzero))))) (negate (m (fsuc (fsuc (fsuc (fsuc fzero)))))) (m (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))))))))
norm (fzero , fsuc fzero) m =
  trans refl (cong₁ (m (fsuc (fsuc fzero))) (((m (fsuc (fsuc (fsuc (fsuc fzero))))) ⊕ T₀)) (m (fsuc (fsuc (fsuc (fsuc fzero))))) (⊕-identityʳ (m (fsuc (fsuc (fsuc (fsuc fzero)))))))
norm (fsuc fzero , fzero) m =
  trans refl (cong₁ (m (fsuc fzero)) (((m (fsuc (fsuc (fsuc fzero)))) ⊕ T₀)) (m (fsuc (fsuc (fsuc fzero)))) (⊕-identityʳ (m (fsuc (fsuc (fsuc fzero))))))
norm (fsuc fzero , fsuc fzero) m =
  trans refl
    (trans (cong₃ (m fzero) (negate (m (fsuc fzero))) (m (fsuc (fsuc fzero))) (((m (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))) ⊕ T₀)) (m (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))) (⊕-identityʳ (m (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))))
      (trans (sym (⊕-assoc (m fzero) (negate (m (fsuc fzero))) ((m (fsuc (fsuc fzero))) ⊕ (m (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))))))
        (sym (⊕-assoc ((m fzero) ⊕ (negate (m (fsuc fzero)))) (m (fsuc (fsuc fzero))) (m (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))))))

-- ★ 稀疏系数求和: Σ_k (m k) ⊗ (c k z) 就是 combo
--   每项归一化（⊗-sc）→ 完全展开（sumFin7）→ 整理（norm）
sum-combo : ∀ z m → sumFin (λ i → (m i) ⊗ (C i z)) ≡ combo z m
sum-combo z m =
  trans (sumFin-cong {g = λ i → (m i) ⊗ (C i z)} {h = g7 z m} (λ i → ⊗-sc (C i z) (m i)))
    (trans (sumFin7 (g7 z m)) (norm z m))

-- ★★ 接桥: 对任意矩阵, 秩分解的和就是 Strassen 的输出（由 M13 的 strassen-correct 承证）
strassen-is-rank-form :
  ∀ A B z → sumFin (λ i → (L i A) ⊗ ((R i B) ⊗ (C i z))) ≡ at (mul₃ A B) z
strassen-is-rank-form A B z =
  trans (sumFin-cong (λ i → sym (⊗-assoc (L i A) (R i B) (C i z))))
    (trans (sumFin-cong (λ i → cong (λ v → (v ⊗ (C i z))) (LR i A B)))
      (trans (sum-combo z (λ i → mTab i A B))
        (trans (sym (at-strassen A B z))
          (cong (λ M → at M z)
            (strassen-correct (m00 A) (m01 A) (m10 A) (m11 A)
              (m00 B) (m01 B) (m10 B) (m11 B))))))

-- 基矩阵的乘积就是张量的结构常数（16 条闭值子句, 每条对 4 个输出位置各一个 refl）
--   数值对应: oracle 的判据三「两路会合」（16 对基矩阵 × 4 输出 = 64 次比对）
mm-basis : ∀ x y z → at (mul₃ (E x) (E y)) z ≡ mm 2 x y z
mm-basis (fzero , fzero) (fzero , fzero) = λ { (fzero , fzero) → refl ; (fzero , fsuc fzero) → refl ; (fsuc fzero , fzero) → refl ; (fsuc fzero , fsuc fzero) → refl }
mm-basis (fzero , fzero) (fzero , fsuc fzero) = λ { (fzero , fzero) → refl ; (fzero , fsuc fzero) → refl ; (fsuc fzero , fzero) → refl ; (fsuc fzero , fsuc fzero) → refl }
mm-basis (fzero , fzero) (fsuc fzero , fzero) = λ { (fzero , fzero) → refl ; (fzero , fsuc fzero) → refl ; (fsuc fzero , fzero) → refl ; (fsuc fzero , fsuc fzero) → refl }
mm-basis (fzero , fzero) (fsuc fzero , fsuc fzero) = λ { (fzero , fzero) → refl ; (fzero , fsuc fzero) → refl ; (fsuc fzero , fzero) → refl ; (fsuc fzero , fsuc fzero) → refl }
mm-basis (fzero , fsuc fzero) (fzero , fzero) = λ { (fzero , fzero) → refl ; (fzero , fsuc fzero) → refl ; (fsuc fzero , fzero) → refl ; (fsuc fzero , fsuc fzero) → refl }
mm-basis (fzero , fsuc fzero) (fzero , fsuc fzero) = λ { (fzero , fzero) → refl ; (fzero , fsuc fzero) → refl ; (fsuc fzero , fzero) → refl ; (fsuc fzero , fsuc fzero) → refl }
mm-basis (fzero , fsuc fzero) (fsuc fzero , fzero) = λ { (fzero , fzero) → refl ; (fzero , fsuc fzero) → refl ; (fsuc fzero , fzero) → refl ; (fsuc fzero , fsuc fzero) → refl }
mm-basis (fzero , fsuc fzero) (fsuc fzero , fsuc fzero) = λ { (fzero , fzero) → refl ; (fzero , fsuc fzero) → refl ; (fsuc fzero , fzero) → refl ; (fsuc fzero , fsuc fzero) → refl }
mm-basis (fsuc fzero , fzero) (fzero , fzero) = λ { (fzero , fzero) → refl ; (fzero , fsuc fzero) → refl ; (fsuc fzero , fzero) → refl ; (fsuc fzero , fsuc fzero) → refl }
mm-basis (fsuc fzero , fzero) (fzero , fsuc fzero) = λ { (fzero , fzero) → refl ; (fzero , fsuc fzero) → refl ; (fsuc fzero , fzero) → refl ; (fsuc fzero , fsuc fzero) → refl }
mm-basis (fsuc fzero , fzero) (fsuc fzero , fzero) = λ { (fzero , fzero) → refl ; (fzero , fsuc fzero) → refl ; (fsuc fzero , fzero) → refl ; (fsuc fzero , fsuc fzero) → refl }
mm-basis (fsuc fzero , fzero) (fsuc fzero , fsuc fzero) = λ { (fzero , fzero) → refl ; (fzero , fsuc fzero) → refl ; (fsuc fzero , fzero) → refl ; (fsuc fzero , fsuc fzero) → refl }
mm-basis (fsuc fzero , fsuc fzero) (fzero , fzero) = λ { (fzero , fzero) → refl ; (fzero , fsuc fzero) → refl ; (fsuc fzero , fzero) → refl ; (fsuc fzero , fsuc fzero) → refl }
mm-basis (fsuc fzero , fsuc fzero) (fzero , fsuc fzero) = λ { (fzero , fzero) → refl ; (fzero , fsuc fzero) → refl ; (fsuc fzero , fzero) → refl ; (fsuc fzero , fsuc fzero) → refl }
mm-basis (fsuc fzero , fsuc fzero) (fsuc fzero , fzero) = λ { (fzero , fzero) → refl ; (fzero , fsuc fzero) → refl ; (fsuc fzero , fzero) → refl ; (fsuc fzero , fsuc fzero) → refl }
mm-basis (fsuc fzero , fsuc fzero) (fsuc fzero , fsuc fzero) = λ { (fzero , fzero) → refl ; (fzero , fsuc fzero) → refl ; (fsuc fzero , fzero) → refl ; (fsuc fzero , fsuc fzero) → refl }

-- ★ 2×2 矩阵乘法张量在 GF(3) 上有一个 7 项秩分解
rank-strassen : RankLE₃ 2 7
rank-strassen = record
  { ra = λ i x → L i (E x)
  ; rb = λ i y → R i (E y)
  ; rc = C
  ; rank-eq = λ x y z → trans (strassen-is-rank-form (E x) (E y) z) (mm-basis x y z)
  }

--------------------------------------------------------------------------------
-- §3. 外部边界（无居民）
--------------------------------------------------------------------------------

-- OpenAI 的下界在 GF(3) 上的实例: 每个秩分解都满足 n^9 ≤ r^4, 即秩 ≥ n^(9/4)。
--   来源: Lean `key/MatrixExponent.lean:45 square_iff_prime_ranks` 取 p = 3。
--   状态: 外部定理。本库**没有**它的证明, 也没有把它当公理导入——这里只是一个类型,
--         用来把「我们这边还欠什么」写成一句可核对的话。
--   n = 2 时它说的是 r ≥ 5（4^4 = 256 < 512 ≤ 5^4）, 比库内已证的 r ≥ 7 弱
--   （TensorRankHK2GF3.rank-2x2-lower）; 展平下界 r ≥ 4（TensorRankFlattenGF3.rank-lower）
--   更弱; §2 的见证给 r ≤ 7。n = 2 处精确值是 7（TensorRankHK2GF3.rank₂₂₂-is-7）。
--   这是「每域 ω = 9/4」的下半; 上半（每个比值 > 9/4 都有一个严格节省）的陈述是
--   TensorRankUpperGF3.ω₃-upper, 库内能证的部分是 ★ strassen-saving（比值 ≥ 17/6）。
ω₃-boundary : Set
ω₃-boundary = ∀ n r → 2 ≤ n → RankLE₃ n r → n ^ 9 ≤ r ^ 4
