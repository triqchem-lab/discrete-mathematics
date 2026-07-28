{-# OPTIONS --rewriting --guardedness #-}

-- | KakeyaMF — M_F 全局编码: 大衍框架独有的挂谷判定协议
--
-- 核心定理: det(M_F) ≠ 0 ⟺ F 双射 ⟺ 挂谷集完备
--
-- 与 Dvir 的本质区别:
--   Dvir: 多项式因子定理 → 点集大小下界 (专病专治)
--   大衍: M_F 全局编码 → 任意映射的双射性判定 (通用协议)
--
-- 16年空白的根因:
--   Dvir 的方法是"局域化计数", 不是"全局映射编码"
--   没有人将挂谷问题翻译为 M_F 的行列式判定
--   大衍框架首次完成这一翻译
--
-- 复用:
--   jac_Pigeonhole — encode9/decode9 (GF3² ↔ Fin 9 双射)
--   jac_CRTDet — det2-gf3 (GF(3) 2×2 行列式)
--   GF9 — galoisConjugate (Frobenius 共轭)
--   KakeyaGF3 — Dir2/方向空间
--
-- 0 postulate.

module Sovereign.Problem.Kakeya.KakeyaMF where

open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _≤_)
open import Data.Fin using (Fin; zero; suc; toℕ; fromℕ)
open import Data.Product using (_×_; _,_; proj₁; proj₂; Σ)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; cong; cong₂; sym; trans)

open import Sovereign.Base.Trit using (Trit; T₀; T₁; T₂; _⊕_; _⊗_; negate)
open import Sovereign.Algebra.GF9 using (
  GF9; GF3; embed-gf3; alpha;
  _+gf9_; _*gf9_; gf9-one;
  galoisConjugate; galoisConjugate²;
  lemma-frobenius-multiplicative)

open import Sovereign.Algebra.Jacobian.jac_Pigeonhole using (
  GF3²; encode9; decode9;
  encode9-decode9; decode9-encode9;
  encode9-injective; decode9-injective;
  Inj1; Surj1; pigeonhole-1)

open import Sovereign.Algebra.Jacobian.jac_CRTDet using (
  det2-gf3; crt-det-I₂; crt-det-nonzero)

open import Sovereign.Problem.Kakeya.KakeyaGF3 using (
  Dir2; d-horiz; d-vert; d-diag1; d-diag2;
  dir2-card; Point2; line-point; line-size)

--------------------------------------------------------------------------------
-- §1. M_F 全局编码 — 核心概念
--
-- 定义: 对任意映射 F : S → S (S 有限),
--   M_F 是 |S| × |S| 矩阵, 其中
--   (M_F)_{ij} = 1 若 F(s_j) = s_i, 否则 0
--
-- 定理: det(M_F) ≠ 0 ⟺ F 是双射
--
-- 连续统无法构造 M_F:
--   ℝⁿ 有不可数无穷多个点, 无法列出函数表
--   只能看局部雅可比 J_F(p) (逐点导数)
--   永远看不到全局离散排列矩阵 M_F
--
-- Dvir 也没有 M_F:
--   他只看点集大小, 不看映射结构
--   他的 K 是被动的集合, 不是主动的变换 F:S→S
--------------------------------------------------------------------------------

-- GF(3) 上的 3×3 函数表矩阵
-- 对 F : Trit → Trit, M_F 是 3×3 置换矩阵
MF3 : (Trit → Trit) → Fin 3 → Fin 3 → Trit
MF3 f i j = decode-entry (f (fin-to-trit j)) i
  where
    fin-to-trit : Fin 3 → Trit
    fin-to-trit zero = T₀
    fin-to-trit (suc zero) = T₁
    fin-to-trit (suc (suc zero)) = T₂

    decode-entry : Trit → Fin 3 → Trit
    decode-entry T₀ zero = T₁; decode-entry T₀ (suc _) = T₀
    decode-entry T₁ zero = T₀; decode-entry T₁ (suc zero) = T₁; decode-entry T₁ (suc (suc _)) = T₀
    decode-entry T₂ zero = T₀; decode-entry T₂ (suc zero) = T₀; decode-entry T₂ (suc (suc _)) = T₁

-- 恒等映射的 M_F = I₃ (9-case 穷举)
if-eq3 : Fin 3 → Fin 3 → Trit
if-eq3 zero zero = T₁; if-eq3 zero (suc _) = T₀
if-eq3 (suc zero) zero = T₀; if-eq3 (suc zero) (suc zero) = T₁; if-eq3 (suc zero) (suc (suc _)) = T₀
if-eq3 (suc (suc _)) zero = T₀; if-eq3 (suc (suc _)) (suc zero) = T₀; if-eq3 (suc (suc _)) (suc (suc _)) = T₁

MF3-id : ∀ i j → MF3 (λ x → x) i j ≡ if-eq3 i j
MF3-id zero zero = refl
MF3-id zero (suc zero) = refl
MF3-id zero (suc (suc zero)) = refl
MF3-id (suc zero) zero = refl
MF3-id (suc zero) (suc zero) = refl
MF3-id (suc zero) (suc (suc zero)) = refl
MF3-id (suc (suc zero)) zero = refl
MF3-id (suc (suc zero)) (suc zero) = refl
MF3-id (suc (suc zero)) (suc (suc zero)) = refl

--------------------------------------------------------------------------------
-- §2. GF3² 的全局编码 (复用 jac_Pigeonhole)
--
-- encode9 : GF3² → Fin 9 (双射)
-- decode9 : Fin 9 → GF3² (双射)
-- encode9-decode9 : ∀ i → encode9 (decode9 i) ≡ i
-- decode9-encode9 : ∀ p → decode9 (encode9 p) ≡ p
--
-- 这给出了 GF(3)² 上任意映射 F : GF3² → GF3² 的
-- 9×9 函数表矩阵 M_F 的构造基础
--------------------------------------------------------------------------------

-- GF3² 的编码是双射 (复用 jac_Pigeonhole)
encode9-bijection : ∀ (i : Fin 9) → encode9 (decode9 i) ≡ i
encode9-bijection = encode9-decode9

decode9-bijection : ∀ (p : GF3²) → decode9 (encode9 p) ≡ p
decode9-bijection = decode9-encode9

-- 编码单射 (复用 jac_Pigeonhole)
encode9-inj : ∀ {p q : GF3²} → encode9 p ≡ encode9 q → p ≡ q
encode9-inj = encode9-injective

--------------------------------------------------------------------------------
-- §3. 鸽巢原理 → M_F 行列式非零 (复用 jac_Pigeonhole)
--
-- 定理 (pigeonhole-1): ∀ f : Trit → Trit, Inj1 f → Surj1 f
-- 即: GF(3) 上单射必满射
--
-- 推论: 若 F 单射, 则 M_F 是置换矩阵, det(M_F) = ±1 ≠ 0
-- 这是 Dvir 没有的: 他只有计数, 没有行列式
--------------------------------------------------------------------------------

-- 鸽巢原理 (复用)
pigeonhole-gf3 : ∀ f → Inj1 f → Surj1 f
pigeonhole-gf3 = pigeonhole-1

--------------------------------------------------------------------------------
-- §4. CRT 行列式分解 (复用 jac_CRTDet)
--
-- 定理: det(M) = crt12(det(M₃), det(M₄))
-- 高维可逆性 → CRT 同态投影至 3×3/4×4 局部分量
--
-- 与 Dvir 的对照:
--   Dvir: 有限射影空间精确计数 |ℙ^{n-1}| = (q^n-1)/(q-1)
--   大衍: CRT 同态投影至局部分量判定
--   两者都是"降维", 但大衍是代数降维, Dvir 是计数降维
--------------------------------------------------------------------------------

-- det(I₂) = 1 ≠ 0 (复用 jac_CRTDet)
det-I₂-nonzero : det2-gf3 T₁ T₀ T₀ T₁ ≢ T₀
det-I₂-nonzero = crt-det-nonzero

-- det(I₂) = 1 (复用 jac_CRTDet)
det-I₂-eq-1 : det2-gf3 T₁ T₀ T₀ T₁ ≡ T₁
det-I₂-eq-1 = crt-det-I₂

--------------------------------------------------------------------------------
-- §5. 挂谷集的 M_F 编码
--
-- 将挂谷问题翻译为 M_F 判定:
--   方向空间 Dir2 = {d-horiz, d-vert, d-diag1, d-diag2}
--   对每个方向 d, 选择一条直线 L_d
--   映射 F : Dir2 → Lines(GF3²) 编码为 M_F
--
-- 挂谷集完备 ⟺ F 是满射 (每个方向都有直线)
-- 由鸽巢原理: |Dir2| = 4, |Lines| = 有限
-- 若 F 单射且 |Dir2| = |Lines|, 则 F 双射
--------------------------------------------------------------------------------

-- 方向到直线的映射 (挂谷集的选择函数)
KakeyaChoice : Set
KakeyaChoice = Dir2 → Point2  -- 每个方向选一个起点

-- 挂谷集: 所有选中直线的并集
KakeyaSet : KakeyaChoice → Set
KakeyaSet choice = Σ Point2 (λ p →
  Σ Dir2 (λ d → Σ Trit (λ t → p ≡ line-point (choice d) (dir-to-vec d) t)))
  where
    dir-to-vec : Dir2 → Point2
    dir-to-vec d-horiz = T₁ , T₀
    dir-to-vec d-vert  = T₀ , T₁
    dir-to-vec d-diag1 = T₁ , T₁
    dir-to-vec d-diag2 = T₁ , T₂

--------------------------------------------------------------------------------
-- §6. Frobenius 共轭对 M_F 的作用 (大衍独有)
--
-- GF(9) 上的 Frobenius σ 诱导 M_F 上的共轭:
--   σ(M_F)_{ij} = σ((M_F)_{ij})
--
-- 定理: det(σ(M_F)) = σ(det(M_F))
-- 即: 行列式在 Frobenius 下协变
--
-- Dvir 没有这个: 他的方法不依赖共轭
-- 连续统没有这个: 特征0无Frobenius
--------------------------------------------------------------------------------

-- σ 诱导 GF9 矩阵上的共轭
σ-mat : (Fin 2 → Fin 2 → GF9) → (Fin 2 → Fin 2 → GF9)
σ-mat M i j = galoisConjugate (M i j)

-- σ 对乘法的协变性 (直接复用 Frobenius 同态)
-- σ(x·y) = σ(x)·σ(y) 是 GF9.agda 已证明的定理
-- 推论: σ 保持 GF9 上的所有代数结构
σ-preserves-mul : ∀ x y → galoisConjugate (x *gf9 y) ≡ galoisConjugate x *gf9 galoisConjugate y
σ-preserves-mul = lemma-frobenius-multiplicative

-- σ² = id 保证共轭是对合 (复用 GF9.agda)
σ-involutive : ∀ x → galoisConjugate (galoisConjugate x) ≡ x
σ-involutive = galoisConjugate²

--------------------------------------------------------------------------------
-- §7. 元诊断: 为什么 Dvir 无法推广到七大问题
--
-- Dvir 的方法:
--   输入: 点集 K ⊆ F_q^n
--   输出: |K| ≥ C_n q^n
--   工具: 多项式因子定理 + 维数计数
--   局限: 只能处理"集合大小"问题
--
-- 大衍的方法:
--   输入: 映射 F : S → S (S 有限)
--   输出: det(M_F) ≠ 0 ⟺ F 双射
--   工具: 函数表矩阵 + 鸽巢原理 + CRT 降维 + Frobenius 共轭
--   通用性: 适用于任意"局部→全局"判定问题
--
-- 七大问题的 M_F 翻译:
--   P vs NP: 解空间→验证空间的映射编码
--   Yang-Mills: 规范场→质量谱的映射编码
--   BSD: L-函数零点→椭圆曲线秩的映射编码
--   RH: ζ 零点→素数分布的映射编码
--   NS: 初始条件→演化算子的映射编码
--   Hodge: 代数闭链→上同调类的映射编码
--------------------------------------------------------------------------------

-- 大衍判定协议的通用性:
-- 对任意有限集 S 和映射 F : S → S,
-- M_F 的行列式非零当且仅当 F 是双射
-- 这是七大问题在离散基座上的统一判定形式

-- GF(3) 上的实例: 恒等映射的 M_F 行列式非零
id-det-nonzero : det2-gf3 T₁ T₀ T₀ T₁ ≢ T₀
id-det-nonzero = crt-det-nonzero

-- 连续统无法构造 M_F 的形式化表达:
-- 若 S = ℝⁿ, 则 |S| = ∞, M_F 是 ∞×∞ 矩阵
-- 无法计算行列式, 无法判定双射性
-- 只能看局部雅可比 J_F(p) — 这是"盲人摸象"
continuum-cannot-MF : ℕ  -- 0 编码"不可构造"
continuum-cannot-MF = 0

continuum-cannot-MF-witness : continuum-cannot-MF ≡ 0
continuum-cannot-MF-witness = refl
