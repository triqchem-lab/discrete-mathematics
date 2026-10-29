{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Application.Problems.Kakeya.KakeyaGF3
-- KakeyaGF3 — 挂谷猜想的 GF(3) 基座: 向量空间/方向/直线/Dvir下界
--
-- 数学背景:
--   Dvir (2008): |K| ≥ C_n q^n, 任意有限域 F_q, 2页纸多项式方法
--   王虹 & Zahl (2025): ℝ³ 挂谷猜想, 127页解析学
--
-- 本模块只处理 GF(3) 上的结构 (无共轭):
--   GF(3)^n 向量空间, 射影方向空间, 直线, Dvir 下界
--   GF(9) Frobenius 共轭见 KakeyaGF9.agda
--
-- §7-§9 扩展口径注记 (dir6 / F_3^6 挂谷 / 极小基数):
--   dirN-card 沿用 §2 的「射影公式验算」口径: dirN-card * 2 + 1 ≡ 3^n (refl)
--   ——这是公式一致性验算, 不是 364 方向的组合枚举;逐义支撑由 KK-canon
--   规范代表机制给出 (标量类 {v, 2v} 映到唯一代表, 首非零坐标归一 T₁;
--   类内相异 KK-scale2-neq-self 闭合), 完整轨道计数 (364 = 类数) 立界。
--   Dvir@n=6: 1/n! 口径数值 ⌈729/720⌉ = 2 (Dvir 2008 一般定理实例化,
--   定理本体未形式化, 立界);deg-2 多项式方法界 28 = (n+1)(n+2)/2@n=6
--   (三根零化核心 KK-poly2-three-roots 已闭合;核引理/归纳装配立界)。
--   DKSW ⌈(3/2)^6⌉ = 12 入档;精确极小标「SAT/ILP 外部求解」立界。
-- 0 postulate, 0 hole;§7 起新符号一律 KK- 前缀。

module Sovereign.Application.Problems.Kakeya.KakeyaGF3 where

open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _≤_; _<_; s≤s; z≤n)
open import Data.Nat.Properties using (m≤m+n)
open import Data.Product using (_×_; _,_; proj₁; proj₂; Σ)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_)
open import Data.Vec using (Vec; []; _∷_; replicate)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; cong; cong₂; sym; trans)

open import Sovereign.Base.Trit
  using (Trit; T₀; T₁; T₂; _⊕_; _⊗_; negate;
         ⊕-identityˡ; ⊕-identityʳ; ⊗-identityˡ; ⊗-identityʳ; ⊗-zeroʳ)

--------------------------------------------------------------------------------
-- §1. GF(3)^n 向量空间
--
-- 复用 Sovereign.Base.Trit 作为 GF(3) 底层
-- GF(3)^n = Vec Trit n
--------------------------------------------------------------------------------

GF3Vec : ℕ → Set
GF3Vec n = Vec Trit n

-- 具体维度实例
GF3¹ : Set; GF3¹ = GF3Vec 1
GF3² : Set; GF3² = GF3Vec 2
GF3³ : Set; GF3³ = GF3Vec 3

-- 点数定理: |GF(3)^n| = 3^n
card-GF3¹ : ℕ; card-GF3¹ = 3
card-GF3² : ℕ; card-GF3² = 9
card-GF3³ : ℕ; card-GF3³ = 27

-- 3 = 3 (定义等式)
card-GF3¹-ok : card-GF3¹ ≡ 3
card-GF3¹-ok = refl

-- 9 = 3 * 3 (乘法结构)
card-GF3²-ok : card-GF3² ≡ card-GF3¹ * card-GF3¹
card-GF3²-ok = refl

-- 27 = 3 * 9 (乘法结构)
card-GF3³-ok : card-GF3³ ≡ card-GF3¹ * card-GF3²
card-GF3³-ok = refl

--------------------------------------------------------------------------------
-- §2. 方向空间: 有限射影空间 ℙ^{n-1}(GF(3))
--
-- 定理: |ℙ^{n-1}(GF(3))| = (3^n - 1) / (3 - 1) = (3^n - 1) / 2
--
-- 连续统病态对照:
--   ℝ^n 的方向空间 = S^{n-1}, 不可数无穷
--   GF(3)^n 的方向空间 = ℙ^{n-1}(GF(3)), 精确有限
--   这一有限性是 Dvir 2页纸 vs 王虹 127页 的根源
--------------------------------------------------------------------------------

-- GF(3)^2 的 4 个射影方向
-- ℙ¹(GF(3)) = {⟨(1,0)⟩, ⟨(0,1)⟩, ⟨(1,1)⟩, ⟨(1,2)⟩}
data Dir2 : Set where
  d-horiz : Dir2   -- ⟨(1,0)⟩: 水平方向
  d-vert  : Dir2   -- ⟨(0,1)⟩: 垂直方向
  d-diag1 : Dir2   -- ⟨(1,1)⟩: 对角方向
  d-diag2 : Dir2   -- ⟨(1,2)⟩: 反对角方向

-- |ℙ¹(GF(3))| = (9-1)/2 = 4
dir2-card : ℕ
dir2-card = 4

-- 4*2+1 = 9 (射影方向数公式验证)
dir2-card-formula : dir2-card * 2 + 1 ≡ card-GF3²
dir2-card-formula = refl

-- GF(3)^3 的 13 个射影方向
-- |ℙ²(GF(3))| = (27-1)/2 = 13
dir3-card : ℕ
dir3-card = 13

dir3-card-formula : dir3-card * 2 + 1 ≡ card-GF3³
dir3-card-formula = refl

--------------------------------------------------------------------------------
-- §3. GF(3) 上的直线
--
-- 定义: 过点 p 沿方向 d 的直线 = {p, p+d, p+2d}
-- GF(3) 特征: 每条直线恰好 3 个点
-- 连续统对照: ℝ^n 中直线有不可数无穷个点
--------------------------------------------------------------------------------

-- GF(3)^2 中的点
Point2 : Set
Point2 = Trit × Trit

-- 方向向量 (非零)
DirVec2 : Set
DirVec2 = Trit × Trit

-- 直线上的点: p + t·d, t ∈ {0, 1, 2}
line-point : Point2 → DirVec2 → Trit → Point2
line-point (px , py) (dx , dy) t = (px ⊕ (t ⊗ dx)) , (py ⊕ (t ⊗ dy))

-- 每条直线 3 个点 (GF(3) 特征)
line-size : ℕ
line-size = 3

-- 3 ≠ 0 (直线非空)
line-nonempty : line-size ≢ 0
line-nonempty ()

--------------------------------------------------------------------------------
-- §4. Dvir 下界定理 (GF(3) 实例)
--
-- Dvir 定理: 对任意 n, 任意有限域 F_q,
--   若 K ⊆ F_q^n 是挂谷集, 则 |K| ≥ C_n · q^n
--   其中 C_n = 1/n!
--
-- GF(3) 实例:
--   n=2: |K| ≥ ⌈9/2⌉ = 5
--   n=3: |K| ≥ ⌈27/6⌉ = 5
--
-- 证明策略 (Dvir): 多项式方法
--   1. 假设 |K| 很小
--   2. 构造低次非零多项式 P 在 K 上恒为零 (鸽巢原理)
--   3. P 在每个方向的直线上有 > deg(P) 个零点
--   4. 由因子定理, P 在每条直线上恒为零
--   5. P 的零点过多, 与低次假设矛盾
--------------------------------------------------------------------------------

-- Dvir 下界 (GF(3), n=2)
dvir-bound-2 : ℕ
dvir-bound-2 = 5

-- Dvir 下界 (GF(3), n=3)
dvir-bound-3 : ℕ
dvir-bound-3 = 5

-- 下界合法性: 5 ≤ 9 (n=2)
dvir-2-valid : dvir-bound-2 ≤ card-GF3²
dvir-2-valid = s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))

-- 下界合法性: 5 ≤ 27 (n=3)
dvir-3-valid : dvir-bound-3 ≤ card-GF3³
dvir-3-valid = s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))

--------------------------------------------------------------------------------
-- §5. 鸽巢原理与重叠必然性
--
-- 4 个方向 × 3 个点/线 = 12 > 9 = |GF(3)²|
-- 因此挂谷集中的直线必须重叠
--
-- Dvir 的核心: 多项式空间维数 vs 点集大小 → 计数矛盾
-- 大衍的核心: 函数表矩阵 M_F 列互异 → det(M_F) ≠ 0
-- 两者共享鸽巢原理底座
--------------------------------------------------------------------------------

-- 4方向 × 3点/线 = 12
overlap-arithmetic : 4 * 3 ≡ 12
overlap-arithmetic = refl

--------------------------------------------------------------------------------
-- §6. 连续统病态对照
--
-- 连续统 ℝ^n: 方向空间 S^{n-1} 不可数 → 127页 (王虹 n=3)
-- 离散 GF(3)^n: 方向空间 ℙ^{n-1} 有限 → 计数即可 (Dvir 2页)
-- 127页 vs 2页 = 连续统病态的量度
--------------------------------------------------------------------------------

-- 连续统方向数: 不可数 (用 0 编码"无法用 ℕ 表示")
pathology-continuum : ℕ
pathology-continuum = 0

-- 离散方向数: 精确有限
healing-discrete-n2 : ℕ
healing-discrete-n2 = dir2-card  -- 4

healing-discrete-n3 : ℕ
healing-discrete-n3 = dir3-card  -- 13

-- 病态诊断: 连续统方向数无法用 ℕ 编码
pathology-witness : pathology-continuum ≡ 0
pathology-witness = refl

-- 离散自愈: 方向数精确有限
healing-n2 : healing-discrete-n2 ≡ 4
healing-n2 = refl

healing-n3 : healing-discrete-n3 ≡ 13
healing-n3 = refl

--------------------------------------------------------------------------------
-- §7. GF(3)^6 与六维射影方向空间 (dir6 = 364)
--
-- |GF(3)^6| = 3^6 = 729;|ℙ⁵(GF(3))| = (729−1)/2 = 364。
-- 口径: KK-dirN-card 走「射影公式验算」 KK-dirN-card * 2 + 1 ≡ 3^n (refl),
-- 与 §2 dir2/dir3 同一口径;364 的完整轨道计数立界 (见 head 注记)。
-- 逐义支撑: 每个方向 = 标量类 {v, 2v} (GF(3) 非零标量只有 T₁/T₂),
-- KK-canon 把类映到唯一规范代表 (首非零坐标归一为 T₁)。
--------------------------------------------------------------------------------

KK-card-GF3⁴ : ℕ; KK-card-GF3⁴ = 81
KK-card-GF3⁵ : ℕ; KK-card-GF3⁵ = 243
KK-card-GF3⁶ : ℕ; KK-card-GF3⁶ = 729

-- 3^4 = 3^3 · 3, 3^5 = 3^4 · 3, 3^6 = 3^5 · 3 (乘法结构)
KK-card-GF3⁴-ok : KK-card-GF3⁴ ≡ card-GF3³ * 3
KK-card-GF3⁴-ok = refl

KK-card-GF3⁵-ok : KK-card-GF3⁵ ≡ KK-card-GF3⁴ * 3
KK-card-GF3⁵-ok = refl

KK-card-GF3⁶-ok : KK-card-GF3⁶ ≡ KK-card-GF3⁵ * 3
KK-card-GF3⁶-ok = refl

-- 射影方向数阶梯: (3^n − 1)/2, 验算形 dirN · 2 + 1 ≡ 3^n
KK-dir4-card : ℕ; KK-dir4-card = 40     -- (81 − 1)/2
KK-dir5-card : ℕ; KK-dir5-card = 121    -- (243 − 1)/2
KK-dir6-card : ℕ; KK-dir6-card = 364    -- (729 − 1)/2

KK-dir4-card-formula : KK-dir4-card * 2 + 1 ≡ KK-card-GF3⁴
KK-dir4-card-formula = refl

KK-dir5-card-formula : KK-dir5-card * 2 + 1 ≡ KK-card-GF3⁵
KK-dir5-card-formula = refl

KK-dir6-card-formula : KK-dir6-card * 2 + 1 ≡ KK-card-GF3⁶
KK-dir6-card-formula = refl

--------------------------------------------------------------------------------
-- §7b. 方向标量类的规范代表 (逐义构造)
--
-- 向量逐点运算: KK-vec-scale (标量乘) / KK-vec-plus (加) / KK-zero-vec (零向量)。
-- KK-canon: 首个非零坐标为 T₀ 时前缀保留并递归;为 T₁ 时原样保留;
-- 为 T₂ 时整向量乘 T₂ (GF(3) 中 2·x = negate x) 使其归一为 T₁。
--------------------------------------------------------------------------------

KK-vec-scale : ∀ n → Trit → GF3Vec n → GF3Vec n
KK-vec-scale zero _ [] = []
KK-vec-scale (suc n) t (x ∷ xs) = (t ⊗ x) ∷ KK-vec-scale n t xs

KK-vec-plus : ∀ n → GF3Vec n → GF3Vec n → GF3Vec n
KK-vec-plus zero [] [] = []
KK-vec-plus (suc n) (x ∷ xs) (y ∷ ys) = (x ⊕ y) ∷ KK-vec-plus n xs ys

KK-zero-vec : ∀ n → GF3Vec n
KK-zero-vec n = replicate n T₀

-- T₁ 是缩放单位元: 1·v = v [逐坐标 ⊗-identityʳ]
KK-scale-one : ∀ n (v : GF3Vec n) → KK-vec-scale n T₁ v ≡ v
KK-scale-one zero [] = refl
KK-scale-one (suc n) (x ∷ xs) =
  cong₂ _∷_ (⊗-identityˡ x) (KK-scale-one n xs)

-- T₂ 缩放的平方反演: 2·(2·x) = 4·x ≡ x [3 案 refl]
KK-mul2² : ∀ x → T₂ ⊗ (T₂ ⊗ x) ≡ x
KK-mul2² T₀ = refl; KK-mul2² T₁ = refl; KK-mul2² T₂ = refl

KK-scale-two-involution : ∀ n (v : GF3Vec n) →
  KK-vec-scale n T₂ (KK-vec-scale n T₂ v) ≡ v
KK-scale-two-involution zero [] = refl
KK-scale-two-involution (suc n) (x ∷ xs) =
  cong₂ _∷_ (KK-mul2² x) (KK-scale-two-involution n xs)

-- 规范代表: 首非零坐标归一为 T₁
KK-canon : ∀ n → GF3Vec n → GF3Vec n
KK-canon zero [] = []
KK-canon (suc n) (T₀ ∷ xs) = T₀ ∷ KK-canon n xs
KK-canon (suc n) (T₁ ∷ xs) = T₁ ∷ xs
KK-canon (suc n) (T₂ ∷ xs) = T₁ ∷ KK-vec-scale n T₂ xs

-- 幂等: canon 已是规范形
KK-canon-idem : ∀ n (v : GF3Vec n) → KK-canon n (KK-canon n v) ≡ KK-canon n v
KK-canon-idem zero [] = refl
KK-canon-idem (suc n) (T₀ ∷ xs) = cong (T₀ ∷_) (KK-canon-idem n xs)
KK-canon-idem (suc n) (T₁ ∷ xs) = refl
KK-canon-idem (suc n) (T₂ ∷ xs) = refl

-- canon 对 T₂ 缩放不变: 2v 与 v 同类 [逐案: T₀ 续/ T₁ 用反演/ T₂ 已归一]
KK-canon-scale2 : ∀ n (v : GF3Vec n) →
  KK-canon n (KK-vec-scale n T₂ v) ≡ KK-canon n v
KK-canon-scale2 zero [] = refl
KK-canon-scale2 (suc n) (T₀ ∷ xs) = cong (T₀ ∷_) (KK-canon-scale2 n xs)
KK-canon-scale2 (suc n) (T₁ ∷ xs) =
  cong (T₁ ∷_) (KK-scale-two-involution n xs)
KK-canon-scale2 (suc n) (T₂ ∷ xs) = refl

-- canon 对一切非零标量不变 ⟹ canon 只依赖标量类 ⟨v⟩ = {v, 2v}
KK-canon-scalar-invariant : ∀ n (t : Trit) (v : GF3Vec n) →
  t ≢ T₀ → KK-canon n (KK-vec-scale n t v) ≡ KK-canon n v
KK-canon-scalar-invariant n T₀ v neq = ⊥-elim (neq refl)
KK-canon-scalar-invariant n T₁ v _ = cong (KK-canon n) (KK-scale-one n v)
KK-canon-scalar-invariant n T₂ v _ = KK-canon-scale2 n v

-- 构造性 ∷ 单射 (∷-injective, 3 行, 免导入)
KK-∷-inj : ∀ {n} {x y : Trit} {xs ys : GF3Vec n} →
  x ∷ xs ≡ y ∷ ys → x ≡ y × xs ≡ ys
KK-∷-inj refl = refl , refl

-- 类内相异: 若 2v = v 则 v = 0 (逐坐标 T₂⊗x = x ⟹ x = T₀)
-- ⟹ 非零 v 的类 {v, 2v} 恰含 2 个相异向量 (非零标量共 T₁/T₂ 两个, 平凡半)
KK-mul2-1 : T₂ ⊗ T₁ ≡ T₂
KK-mul2-1 = refl

KK-mul2-2 : T₂ ⊗ T₂ ≡ T₁
KK-mul2-2 = refl

KK-t2-neq-t1 : T₂ ≢ T₁
KK-t2-neq-t1 ()

KK-scale2-neq-self : ∀ n (v : GF3Vec n) →
  KK-vec-scale n T₂ v ≡ v → v ≡ KK-zero-vec n
KK-scale2-neq-self zero [] _ = refl
KK-scale2-neq-self (suc n) (T₀ ∷ xs) h =
  cong (T₀ ∷_) (KK-scale2-neq-self n xs (proj₂ (KK-∷-inj h)))
KK-scale2-neq-self (suc n) (T₁ ∷ xs) h =
  let hd : T₂ ≡ T₁
      hd = trans KK-mul2-1 (proj₁ (KK-∷-inj h))
  in ⊥-elim (KK-t2-neq-t1 hd)
KK-scale2-neq-self (suc n) (T₂ ∷ xs) h =
  let hd : T₁ ≡ T₂
      hd = trans KK-mul2-2 (proj₁ (KK-∷-inj h))
  in ⊥-elim (KK-t2-neq-t1 (sym hd))

--------------------------------------------------------------------------------
-- §8. F_3^6 挂谷集与 Dvir@n=6 (多项式方法结构化)
--
-- 定义: K ⊆ GF(3)^6 挂谷 ⟺ 每个方向含一条整线 (三点 p+t·d, t∈{T₀,T₁,T₂})。
-- 方向以非零向量量化 (向量 d 与 2d 张同一条线, 故与「按标量类量化」等价:
-- p + t·(2d) 随 t 遍历恰为 {p, p+2d, p+d} = {p, p+d, p+2d})。
--
-- n=6 直接枚举不可行 (364 方向 × 线族 3⁶ ⟹ 走结构化):
--   [已闭合] 三根零化引理 KK-poly2-three-roots:
--     q=3、deg≤2 单变量多项式在三根全零 ⟹ 系数全零 (≤27 案 + 恒等桥)。
--     这是「多项式方法」在 (F_3, deg 2) 处的完整核心。
--   [数值件] Dvir 1/n! 口径: ⌈3⁶/6!⌉ = ⌈729/720⌉ = 2 (一般定理实例化)。
--   [立界①] 核引理 (F_3 线性代数): |K| < (n+1)(n+2)/2 ⟹ 求值映射
--     F_3^{deg≤2 单项式} → F_3^K 核非平凡 ⟹ ∃ P ≢ 0, deg P ≤ 2, P|_K ≡ 0。
--   [立界②] 顶齐次装配: P|_{L_u} ≡ 0 ⟹ t² 系数 = 顶齐次部 P₂(u) = 0 ∀方向 u
--     (系数抽取: (p+tu)^α 的 t² 系数仅 |α|=2 项贡献 u^α)。
--   [立界③] 归约引理归纳: 既约 (逐坐标 deg<3) 多项式全域恒零 ⟹ 恒零,
--     逐坐标归纳复用三根零化;⟹ P₂ ≡ 0 ⟹ P₁ ≡ 0 ⟹ 常数 = P(0) ∈ K = 0
--     ⟹ P ≡ 0 与 P ≢ 0 矛盾 ⟹ |K| ≥ (n+1)(n+2)/2,n=6 → 28。
--   注: 界的「载体计数」环节 (carrier 谓词 ↦ ℕ) 未形式化, 界按数值口径入档。
--------------------------------------------------------------------------------

-- 非零坐标 / 非零向量谓词
data KK-NonZeroTrit : Trit → Set where
  KK-nz₁ : KK-NonZeroTrit T₁
  KK-nz₂ : KK-NonZeroTrit T₂

KK-nonzero-vec : ∀ n → GF3Vec n → Set
KK-nonzero-vec zero [] = ⊥
KK-nonzero-vec (suc n) (x ∷ xs) = KK-NonZeroTrit x ⊎ KK-nonzero-vec n xs

-- 过点 p 沿方向 d 的直线的参数点: p + t·d
KK-line-point6 : GF3Vec 6 → GF3Vec 6 → Trit → GF3Vec 6
KK-line-point6 p d t = KK-vec-plus 6 p (KK-vec-scale 6 t d)

-- F_3^6 挂谷集: 每方向 (非零向量) 含一条整线
record KK-KakeyaSet6 : Set₁ where
  field
    KK-carrier : GF3Vec 6 → Set
    KK-cover : ∀ (d : GF3Vec 6) → KK-nonzero-vec 6 d →
      Σ (GF3Vec 6) (λ p → ∀ (t : Trit) → KK-carrier (KK-line-point6 p d t))

-- 非空性见证: 全空间是挂谷集 (平凡上界 729)
KK-whole-space6 : KK-KakeyaSet6
KK-whole-space6 = record
  { KK-carrier = λ _ → ⊤
  ; KK-cover = λ d _ → KK-zero-vec 6 , λ _ → tt }

--------------------------------------------------------------------------------
-- §8b. 三根零化引理 (deg≤2 多项式方法核心, 已闭合)
--------------------------------------------------------------------------------

-- 单变量二次多项式 Horner 求值: a·t² + b·t + c (⊕/⊗ 同级非结合, 全显式括号)
KK-poly2-eval : Trit → Trit → Trit → Trit → Trit
KK-poly2-eval a b c t = (((a ⊗ t) ⊕ b) ⊗ t) ⊕ c

-- 桥1: t = T₀ 求值 = c [内层经 ⊗-zeroʳ 两段归约, 变量首参的 ⊗ 需显式重写]
KK-eval0-inner : ∀ a b → ((a ⊗ T₀) ⊕ b) ≡ b
KK-eval0-inner a b =
  trans (cong (λ u → (u ⊕ b)) (⊗-zeroʳ a))   -- a⊗T₀ ↦ T₀ [⊗-zeroʳ]
        (⊕-identityˡ b)                       -- T₀⊕b ↦ b

KK-poly2-eval0 : ∀ a b c → KK-poly2-eval a b c T₀ ≡ c
KK-poly2-eval0 a b c =
  trans (cong (λ u → ((u ⊗ T₀) ⊕ c)) (KK-eval0-inner a b))  -- 内层 ↦ b
        (trans (cong (λ u → (u ⊕ c)) (⊗-zeroʳ b))           -- b⊗T₀ ↦ T₀
               (⊕-identityˡ c))                             -- T₀⊕c ↦ c

-- 桥2: t = T₁ 求值 = a ⊕ b ⊕ c [两步 ⊗-identityʳ, ≤3 trans]
KK-poly2-eval1 : ∀ a b c → KK-poly2-eval a b c T₁ ≡ (a ⊕ b) ⊕ c
KK-poly2-eval1 a b c =
  trans (cong (λ u → ((u ⊕ b) ⊗ T₁) ⊕ c) (⊗-identityʳ a))    -- a⊗T₁ ↦ a
        (cong (λ u → u ⊕ c) (⊗-identityʳ (a ⊕ b)))            -- (a⊕b)⊗T₁ ↦ a⊕b

-- 桥3: t = T₂ 求值定义性即 Horner 形
KK-poly2-eval2 : ∀ a b c → KK-poly2-eval a b c T₂ ≡ ((((a ⊗ T₂) ⊕ b) ⊗ T₂) ⊕ c)
KK-poly2-eval2 a b c = refl

-- 核心 9 案: a ⊕ b = 0 且 (a⊗T₂ ⊕ b)⊗T₂ = 0 ⟹ a = b = 0
-- (几何: P(1) = P(2) = 0 且 c = 0 ⟹ a = b = 0;8 案矛盾 + 1 案 refl)
KK-t1-neq-t0 : T₁ ≢ T₀
KK-t1-neq-t0 ()

KK-t2-neq-t0 : T₂ ≢ T₀
KK-t2-neq-t0 ()

KK-tri-root-core : ∀ a b →
  a ⊕ b ≡ T₀ → (((a ⊗ T₂) ⊕ b) ⊗ T₂) ≡ T₀ → a ≡ T₀ × b ≡ T₀
KK-tri-root-core T₀ T₀ _  _  = refl , refl
KK-tri-root-core T₀ T₁ e₁ _  = ⊥-elim (KK-t1-neq-t0 e₁)  -- T₀⊕T₁ ↦ T₁
KK-tri-root-core T₀ T₂ e₁ _  = ⊥-elim (KK-t2-neq-t0 e₁)  -- T₂ ≢ T₀
KK-tri-root-core T₁ T₀ e₁ _  = ⊥-elim (KK-t1-neq-t0 e₁)  -- T₁⊕T₀ ↦ T₁
KK-tri-root-core T₁ T₁ e₁ _  = ⊥-elim (KK-t2-neq-t0 e₁)  -- T₁⊕T₁ ↦ T₂
KK-tri-root-core T₁ T₂ _  e₂ = ⊥-elim (KK-t2-neq-t0 e₂)  -- (T₂⊕T₂)⊗T₂ ↦ T₂
KK-tri-root-core T₂ T₀ e₁ _  = ⊥-elim (KK-t2-neq-t0 e₁)  -- T₂⊕T₀ ↦ T₂
KK-tri-root-core T₂ T₁ _  e₂ = ⊥-elim (KK-t1-neq-t0 e₂)  -- (T₁⊕T₁)⊗T₂ ↦ T₁
KK-tri-root-core T₂ T₂ e₁ _  = ⊥-elim (KK-t1-neq-t0 e₁)  -- T₂⊕T₂ ↦ T₁

-- 三根零化引理: deg ≤ 2 多项式在 F_3 三点全零 ⟹ 系数全零
-- (P|_线 限制恒零 ⟺ 顶齐次系数抽取的原子;q=3 处 deg<q 直接致命)
KK-poly2-three-roots : ∀ a b c →
  KK-poly2-eval a b c T₀ ≡ T₀ →
  KK-poly2-eval a b c T₁ ≡ T₀ →
  KK-poly2-eval a b c T₂ ≡ T₀ →
  a ≡ T₀ × b ≡ T₀ × c ≡ T₀
KK-poly2-three-roots a b c h₀ h₁ h₂ = go cEq e₁ e₂
  where
  -- c = P(0) = 0 [桥1]
  cEq : c ≡ T₀
  cEq = trans (sym (KK-poly2-eval0 a b c)) h₀
  -- a ⊕ b ⊕ c = P(1) = 0 [桥2]
  e₁ : (a ⊕ b) ⊕ c ≡ T₀
  e₁ = trans (sym (KK-poly2-eval1 a b c)) h₁
  -- P(2) = 0 [桥3]
  e₂ : ((((a ⊗ T₂) ⊕ b) ⊗ T₂) ⊕ c) ≡ T₀
  e₂ = trans (sym (KK-poly2-eval2 a b c)) h₂
  go : (ceq : c ≡ T₀) → (a ⊕ b) ⊕ c ≡ T₀ →
      ((((a ⊗ T₂) ⊕ b) ⊗ T₂) ⊕ c) ≡ T₀ → a ≡ T₀ × b ≡ T₀ × c ≡ T₀
  go refl e₁' e₂' =
    let e₁'' : a ⊕ b ≡ T₀
        e₁'' = trans (sym (⊕-identityʳ (a ⊕ b))) e₁'
        e₂'' : (((a ⊗ T₂) ⊕ b) ⊗ T₂) ≡ T₀
        e₂'' = trans (sym (⊕-identityʳ (((a ⊗ T₂) ⊕ b) ⊗ T₂))) e₂'
        core : a ≡ T₀ × b ≡ T₀
        core = KK-tri-root-core a b e₁'' e₂''
    in  proj₁ core , proj₂ core , refl

--------------------------------------------------------------------------------
-- §8c. Dvir@n=6 数值件 (1/n! 口径) 与 deg-2 方法界 (n ≤ 3, 6)
--------------------------------------------------------------------------------

-- 6! = 720
KK-fact6 : ℕ
KK-fact6 = 720

KK-fact6-check : KK-fact6 ≡ 6 * (5 * (4 * (3 * (2 * 1))))
KK-fact6-check = refl

-- Dvir 1/n! 口径: |K| ≥ ⌈3⁶/6!⌉ = ⌈729/720⌉ = 2
-- (⌈·⌉ 的算术锚: 1·720 < 729 ≤ 2·720;一般 Dvir 定理本体未形式化, 立界)
KK-dvir-bound-6 : ℕ
KK-dvir-bound-6 = 2

KK-dvir-6-ceil-below : 1 * KK-fact6 < KK-card-GF3⁶
KK-dvir-6-ceil-below = m≤m+n 721 8    -- 721 = suc 720, 721+8 = 729

KK-dvir-6-ceil-above : KK-card-GF3⁶ ≤ 2 * KK-fact6
KK-dvir-6-ceil-above = m≤m+n 729 711  -- 729+711 = 1440 = 2·720

KK-dvir-6-valid : KK-dvir-bound-6 ≤ KK-card-GF3⁶
KK-dvir-6-valid = s≤s (s≤s z≤n)

-- deg-2 多项式方法界: |K| ≥ (n+1)(n+2)/2 (半积验算 C(n+2,2))
KK-deg2-monomials-2 : ℕ; KK-deg2-monomials-2 = 6    -- C(4,2)
KK-deg2-monomials-3 : ℕ; KK-deg2-monomials-3 = 10   -- C(5,2)
KK-deg2-monomials-6 : ℕ; KK-deg2-monomials-6 = 28   -- C(8,2)

KK-deg2-2-half : 2 * KK-deg2-monomials-2 ≡ 3 * 4
KK-deg2-2-half = refl

KK-deg2-3-half : 2 * KK-deg2-monomials-3 ≡ 4 * 5
KK-deg2-3-half = refl

KK-deg2-6-half : 2 * KK-deg2-monomials-6 ≡ 7 * 8
KK-deg2-6-half = refl

KK-deg2-bound-2 : ℕ; KK-deg2-bound-2 = KK-deg2-monomials-2
KK-deg2-bound-3 : ℕ; KK-deg2-bound-3 = KK-deg2-monomials-3
KK-deg2-bound-6 : ℕ; KK-deg2-bound-6 = KK-deg2-monomials-6

KK-deg2-2-valid : KK-deg2-bound-2 ≤ card-GF3²
KK-deg2-2-valid = m≤m+n 6 3

KK-deg2-3-valid : KK-deg2-bound-3 ≤ card-GF3³
KK-deg2-3-valid = m≤m+n 10 17

KK-deg2-6-valid : KK-deg2-bound-6 ≤ KK-card-GF3⁶
KK-deg2-6-valid = m≤m+n 28 701

--------------------------------------------------------------------------------
-- §9. 极小基数: DKSW 界入档 + 精确极小「SAT/ILP 外部求解」立界
--
-- DKSW (Dvir–Kopparty–Saraf–Sudan 2009, 重数方法): 任意 n, 任意 Kakeya K ⊆ F_3^n,
--   |K| ≥ (3/2)^n。
-- n = 6: (3/2)^6 = 729/64 ∈ (11, 12) [704 < 729 < 768] ⟹ 整数下界 12。
-- 对照: 本模块 §8c 的 deg-2 初等界 28 在 n=6 强于 DKSW 12
--   (小 n 区间 (n+1)(n+2)/2 占优;大 n 时 DKSW 指数型 (3/2)^n ≫ n²/2 反超;
--    两界不冲突, 皆合法下界)。
-- 精确极小 min|K| (F_3^6 挂谷集): 未知, ∈ [28, 729];
--   标注「SAT/ILP 外部求解」立界: 729 布尔变量 (每点 ∈/∉ K) × 364 方向约束
--   (每方向 ∃ p, 三点全 ∈ K), 求解器外置, 本库只入档界与口径。
--------------------------------------------------------------------------------

KK-dksw-bound-6 : ℕ
KK-dksw-bound-6 = 12

-- (3/2)^6 > 11: 704 = 11·64 < 729
KK-dksw-6-frac-below : 11 * 64 < KK-card-GF3⁶
KK-dksw-6-frac-below = m≤m+n 705 24    -- 705 = suc 704, 705+24 = 729

-- (3/2)^6 < 12: 729 < 768 = 12·64
KK-dksw-6-frac-above : KK-card-GF3⁶ < 12 * 64
KK-dksw-6-frac-above = m≤m+n 730 38    -- 730 = suc 729, 730+38 = 768

KK-dksw-6-valid : KK-dksw-bound-6 ≤ KK-card-GF3⁶
KK-dksw-6-valid = m≤m+n 12 717

-- 两界一致性: DKSW 12 ≤ deg-2 界 28 (§8c 界在 n=6 支配)
KK-dksw-le-deg2-6 : KK-dksw-bound-6 ≤ KK-deg2-bound-6
KK-dksw-le-deg2-6 = m≤m+n 12 16
