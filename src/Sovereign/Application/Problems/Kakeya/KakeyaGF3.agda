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
--
-- §10-§13 扩展口径注记 (F1 修正边界: 极小基数 = 验证解 only):
--   §10-§11: F_3^6 全点枚举 (KK-vecsN, 729 点) + dir6 轨道计数闭合——
--   KK-dir6-list = 规范代表 ∩ 非零 的构造列表, 计数引理
--   KK-dir6-list-count : length ≡ 364 由封闭计算给出 (§7 的「轨道计数
--   立界」转闭合);与 KK-canon 的一致性 (isCanon ↔ canon-id) 逐义闭合。
--   §12: 指示函数形挂谷集 K : (Fin 6 → Trit) → Bool + IsKakeya6
--   (方向量化 = 364 规范代表列表成员;§8 record 的非零向量量化与此等价,
--   由 KK-canon-scalar-cover 支撑) + KK-check 可判定验证器
--   Dec (IsKakeya6 K × lenK6 K ≡ k)。
--   ★ 两分声明: 本模块提供的是「验证解」——给定 K, 判定挂谷性 + 基数;
--   「最优性」(极小基数的证明, min|K| = m 的下界证书) 需 SAT/ILP UNSAT
--   证书验证器, 另任务, 本模块不含 (§9 的求解器外置口径同此)。
--   §13: n=1 实例闭合 (唯一方向 ⟨T₁⟩, 挂谷 ⟺ |K| = 3, 精确) + n=6
--   线三点相异 (|线| = 3, 逐坐标构造) + 闭合下界 3 ≤ |K| (强于 §8c 的
--   Dvir 1/n! 口径数值 2);Dvir/deg-2/DKSW 的 n=6 全称下界仍按 §8c/§9
--   口径立界 (多项式方法/重数方法的归纳装配未形式化)。
-- 0 postulate, 0 hole;§7 起新符号一律 KK- 前缀。

module Sovereign.Application.Problems.Kakeya.KakeyaGF3 where

open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _≤_; _<_; s≤s; z≤n)
open import Data.Nat.Properties using (m≤m+n; _≟_; ≤-trans)
open import Data.Product using (_×_; _,_; proj₁; proj₂; Σ)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Bool using (Bool; true; false)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.Vec using (Vec; []; _∷_; replicate; lookup)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; cong; cong₂; sym; trans; subst)

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

--------------------------------------------------------------------------------
-- §10. F_3^6 全点枚举基座 (验证器的有限论域)
--
-- 自带 KK-List (免 stdlib List 与 Vec 的 _∷_/[] 二义), 3^n 点按字典序枚举:
--   KK-vecsN (suc n) = concat (map (λ w → map (λ b → b ∷ w) [T₀,T₁,T₂]) (KK-vecsN n))
-- 完备性 KK-vecsN-complete: 每个 v : GF3Vec n 都在枚举中 (结构归纳)。
-- 计数: length (KK-vecsN 6) ≡ 729 由封闭计算给出。
--------------------------------------------------------------------------------

data KK-List (A : Set) : Set where
  KK-nil  : KK-List A
  KK-cons : A → KK-List A → KK-List A

KK-map : ∀ {A B : Set} → (A → B) → KK-List A → KK-List B
KK-map f KK-nil = KK-nil
KK-map f (KK-cons x xs) = KK-cons (f x) (KK-map f xs)

_KK++_ : ∀ {A : Set} → KK-List A → KK-List A → KK-List A
KK-nil KK++ ys = ys
KK-cons x xs KK++ ys = KK-cons x (xs KK++ ys)

KK-concat : ∀ {A : Set} → KK-List (KK-List A) → KK-List A
KK-concat KK-nil = KK-nil
KK-concat (KK-cons xs xss) = xs KK++ KK-concat xss

KK-length : ∀ {A : Set} → KK-List A → ℕ
KK-length KK-nil = zero
KK-length (KK-cons x xs) = suc (KK-length xs)

KK-filterB : ∀ {A : Set} → (A → Bool) → KK-List A → KK-List A
KK-filterB f KK-nil = KK-nil
KK-filterB f (KK-cons x xs) with f x
... | true  = KK-cons x (KK-filterB f xs)
... | false = KK-filterB f xs

KK-cnt : ∀ {A : Set} → (A → Bool) → KK-List A → ℕ
KK-cnt f KK-nil = zero
KK-cnt f (KK-cons x xs) with f x
... | true  = suc (KK-cnt f xs)
... | false = KK-cnt f xs

-- Bool 辅助件
KK-andB : Bool → Bool → Bool
KK-andB true  b = b
KK-andB false b = false

KK-orB : Bool → Bool → Bool
KK-orB true  b = true
KK-orB false b = b

KK-nzb : Trit → Bool
KK-nzb T₀ = false
KK-nzb T₁ = true
KK-nzb T₂ = true

KK-false≢true : false ≢ true
KK-false≢true ()

KK-andB-in : ∀ (a b : Bool) → KK-andB a b ≡ true → a ≡ true × b ≡ true
KK-andB-in true  true  _ = refl , refl
KK-andB-in true  false ()
KK-andB-in false _     ()

KK-andB-cong : ∀ (a b : Bool) → a ≡ true → b ≡ true → KK-andB a b ≡ true
KK-andB-cong true  true  _ _ = refl
KK-andB-cong true  false _ h₂ = ⊥-elim (KK-false≢true h₂)
KK-andB-cong false _     h₁ _ = ⊥-elim (KK-false≢true h₁)

KK-Bool≟ : ∀ (a b : Bool) → Dec (a ≡ b)
KK-Bool≟ true  true  = yes refl
KK-Bool≟ true  false = no (λ ())
KK-Bool≟ false true  = no (λ ())
KK-Bool≟ false false = yes refl

KK-×-dec : ∀ {A B : Set} → Dec A → Dec B → Dec (A × B)
KK-×-dec (yes a) (yes b) = yes (a , b)
KK-×-dec (yes a) (no ¬b) = no λ h → ¬b (proj₂ h)
KK-×-dec (no ¬a) (yes b) = no λ h → ¬a (proj₁ h)
KK-×-dec (no ¬a) (no ¬b) = no λ h → ¬a (proj₁ h)

-- 成员谓词 (自带, 无方程负载: KK-here 靠索引统一元素与表头)
data KK-∈L {A : Set} (x : A) : KK-List A → Set where
  KK-here  : ∀ {xs} → KK-∈L x (KK-cons x xs)
  KK-there : ∀ {y xs} → KK-∈L x xs → KK-∈L x (KK-cons y xs)

data KK-Any {A : Set} (P : A → Set) : KK-List A → Set where
  KK-any-here  : ∀ {x xs} → P x → KK-Any P (KK-cons x xs)
  KK-any-there : ∀ {x xs} → KK-Any P xs → KK-Any P (KK-cons x xs)

data KK-All {A : Set} (P : A → Set) : KK-List A → Set where
  KK-all-nil : KK-All P KK-nil
  KK-all-cons : ∀ {x xs} → P x → KK-All P xs → KK-All P (KK-cons x xs)

-- 有限 ∀/∃ 的可判定性 (短路段: any 首真即停, all 首假即停)
KK-anyDec : ∀ {A : Set} (P : A → Set) → (∀ x → Dec (P x)) → (xs : KK-List A) → Dec (KK-Any P xs)
KK-anyDec P P? KK-nil = no (λ ())
KK-anyDec P P? (KK-cons x xs) with P? x
... | yes px = yes (KK-any-here px)
... | no ¬px with KK-anyDec P P? xs
...   | yes pxs = yes (KK-any-there pxs)
...   | no ¬pxs = no λ { (KK-any-here px) → ¬px px ; (KK-any-there pxs) → ¬pxs pxs }

KK-allDec : ∀ {A : Set} (P : A → Set) → (∀ x → Dec (P x)) → (xs : KK-List A) → Dec (KK-All P xs)
KK-allDec P P? KK-nil = yes KK-all-nil
KK-allDec P P? (KK-cons x xs) with P? x
... | no ¬px = no λ { (KK-all-cons px pxs) → ¬px px }
... | yes px with KK-allDec P P? xs
...   | yes pxs = yes (KK-all-cons px pxs)
...   | no ¬pxs = no λ { (KK-all-cons px pxs) → ¬pxs pxs }

-- All ↔ 有界 ∀ 转换
KK-All→∀∈ : ∀ {A : Set} (P : A → Set) (xs : KK-List A) →
  KK-All P xs → ∀ x → KK-∈L x xs → P x
KK-All→∀∈ P KK-nil KK-all-nil x ()
KK-All→∀∈ P (KK-cons y ys) (KK-all-cons py pys) x KK-here = py
KK-All→∀∈ P (KK-cons y ys) (KK-all-cons py pys) x (KK-there x∈) = KK-All→∀∈ P ys pys x x∈

KK-∀∈→All : ∀ {A : Set} (P : A → Set) (xs : KK-List A) →
  (∀ x → KK-∈L x xs → P x) → KK-All P xs
KK-∀∈→All P KK-nil h = KK-all-nil
KK-∀∈→All P (KK-cons y ys) h = KK-all-cons (h y KK-here) (KK-∀∈→All P ys (λ x x∈ → h x (KK-there x∈)))

-- Any ↔ Σ 转换
KK-Any→Σ : ∀ {A : Set} (P : A → Set) (xs : KK-List A) → KK-Any P xs → Σ A (λ x → P x)
KK-Any→Σ P (KK-cons x xs) (KK-any-here px) = x , px
KK-Any→Σ P (KK-cons x xs) (KK-any-there pxs) = KK-Any→Σ P xs pxs

KK-Σ→Any : ∀ {A : Set} (P : A → Set) {x xs} → KK-∈L x xs → P x → KK-Any P xs
KK-Σ→Any P KK-here px = KK-any-here px
KK-Σ→Any P (KK-there x∈) px = KK-any-there (KK-Σ→Any P x∈ px)

-- 成员追索件
KK-∈-map : ∀ {A B : Set} (f : A → B) {x xs} → KK-∈L x xs → KK-∈L (f x) (KK-map f xs)
KK-∈-map f KK-here = KK-here
KK-∈-map f (KK-there x∈) = KK-there (KK-∈-map f x∈)

KK-∈-++ˡ : ∀ {A : Set} {x : A} (xs ys : KK-List A) → KK-∈L x xs → KK-∈L x (xs KK++ ys)
KK-∈-++ˡ (KK-cons a as) ys KK-here = KK-here
KK-∈-++ˡ (KK-cons a as) ys (KK-there x∈) = KK-there (KK-∈-++ˡ as ys x∈)

KK-∈-++ʳ : ∀ {A : Set} {x : A} (xs ys : KK-List A) → KK-∈L x ys → KK-∈L x (xs KK++ ys)
KK-∈-++ʳ KK-nil ys x∈ = x∈
KK-∈-++ʳ (KK-cons a as) ys x∈ = KK-there (KK-∈-++ʳ as ys x∈)

KK-concat-∈ : ∀ {A B : Set} (F : A → KK-List B) {x : A} {y : B} (xs : KK-List A) →
  KK-∈L x xs → KK-∈L y (F x) → KK-∈L y (KK-concat (KK-map F xs))
KK-concat-∈ F (KK-cons a as) KK-here y∈Fx = KK-∈-++ˡ (F a) (KK-concat (KK-map F as)) y∈Fx
KK-concat-∈ F (KK-cons a as) (KK-there x∈) y∈Fx =
  KK-∈-++ʳ (F a) (KK-concat (KK-map F as)) (KK-concat-∈ F as x∈ y∈Fx)

-- GF(3) 全值表
KK-allTrits : KK-List Trit
KK-allTrits = KK-cons T₀ (KK-cons T₁ (KK-cons T₂ KK-nil))

KK-allTrits-complete : ∀ (a : Trit) → KK-∈L a KK-allTrits
KK-allTrits-complete T₀ = KK-here
KK-allTrits-complete T₁ = KK-there KK-here
KK-allTrits-complete T₂ = KK-there (KK-there KK-here)

-- 3^n 点枚举: KK-vecsN n 恰含全部 GF3Vec n
KK-vecsN : ∀ n → KK-List (GF3Vec n)
KK-vecsN zero = KK-cons [] KK-nil
KK-vecsN (suc n) =
  KK-concat (KK-map (λ w → KK-map (λ b → b ∷ w) KK-allTrits) (KK-vecsN n))

KK-vecs6 : KK-List (GF3Vec 6)
KK-vecs6 = KK-vecsN 6

KK-vecsN-complete : ∀ n (v : GF3Vec n) → KK-∈L v (KK-vecsN n)
KK-vecsN-complete zero [] = KK-here
KK-vecsN-complete (suc n) (a ∷ v) =
  KK-concat-∈ (λ w → KK-map (λ b → b ∷ w) KK-allTrits) (KK-vecsN n)
    (KK-vecsN-complete n v)
    (KK-∈-map (λ b → b ∷ v) (KK-allTrits-complete a))

KK-vecs6-count : KK-length KK-vecs6 ≡ 729
KK-vecs6-count = refl

KK-vecs6-complete : ∀ (v : GF3Vec 6) → KK-∈L v KK-vecs6
KK-vecs6-complete = KK-vecsN-complete 6

--------------------------------------------------------------------------------
-- §11. dir6 轨道计数闭合 (§7 的「364 立界」→ 构造列表 + 计数引理)
--
-- 口径: 方向 = 非零向量的标量类 {v, 2v};规范代表 = 首非零坐标为 T₁ 的向量。
-- KK-dir6-list = 枚举 729 点中「规范 ∧ 非零」的过滤表;
--   计数引理 length ≡ 364 = (3⁶−1)/2 由封闭计算给出。
-- 与 §7b KK-canon 的一致性: isCanon ↔ canon-id (互推), 保证「过滤出的表」
-- 与「规范代表机制」逐义同一, 不是两套口径。
--------------------------------------------------------------------------------

KK-isCanonB : ∀ n → GF3Vec n → Bool
KK-isCanonB zero [] = true
KK-isCanonB (suc n) (T₀ ∷ xs) = KK-isCanonB n xs
KK-isCanonB (suc n) (T₁ ∷ xs) = true
KK-isCanonB (suc n) (T₂ ∷ xs) = false

KK-anyNZB : ∀ n → GF3Vec n → Bool
KK-anyNZB zero [] = false
KK-anyNZB (suc n) (x ∷ xs) = KK-orB (KK-nzb x) (KK-anyNZB n xs)

-- 一致性: isCanonB true ⟹ KK-canon 幂等于 v
KK-isCanon→canon : ∀ n (v : GF3Vec n) → KK-isCanonB n v ≡ true → KK-canon n v ≡ v
KK-isCanon→canon zero [] _ = refl
KK-isCanon→canon (suc n) (T₀ ∷ xs) h = cong (T₀ ∷_) (KK-isCanon→canon n xs h)
KK-isCanon→canon (suc n) (T₁ ∷ xs) _ = refl
KK-isCanon→canon (suc n) (T₂ ∷ xs) ()

-- 一致性 (反方向): KK-canon 幂等于 v ⟹ isCanonB true
KK-t1-neq-t2 : T₁ ≢ T₂
KK-t1-neq-t2 ()

KK-canon→isCanon : ∀ n (v : GF3Vec n) → KK-canon n v ≡ v → KK-isCanonB n v ≡ true
KK-canon→isCanon zero [] _ = refl
KK-canon→isCanon (suc n) (T₀ ∷ xs) h = KK-canon→isCanon n xs (proj₂ (KK-∷-inj h))
KK-canon→isCanon (suc n) (T₁ ∷ xs) _ = refl
KK-canon→isCanon (suc n) (T₂ ∷ xs) h = ⊥-elim (KK-t1-neq-t2 (proj₁ (KK-∷-inj h)))

-- dir6 构造列表: 729 点过滤「规范 ∧ 非零」
KK-dir6-list : KK-List (GF3Vec 6)
KK-dir6-list =
  KK-filterB (λ v → KK-andB (KK-isCanonB 6 v) (KK-anyNZB 6 v)) KK-vecs6

-- 计数引理 (轨道计数闭合): |dir6-list| = 364 = (3⁶−1)/2
KK-dir6-list-count : KK-length KK-dir6-list ≡ 364
KK-dir6-list-count = refl

-- 与 §7 公式口径接轨: 364 字面 = 构造表长
KK-dir6-count-closed : KK-dir6-card ≡ KK-length KK-dir6-list
KK-dir6-count-closed = refl

-- 过滤进入: 谓词为真且在原表 ⟹ 在过滤表 (KK-check 下界装配用)
KK-filterB-∈ : ∀ {A : Set} (f : A → Bool) {x : A} (xs : KK-List A) →
  KK-∈L x xs → f x ≡ true → KK-∈L x (KK-filterB f xs)
KK-filterB-∈ f KK-nil () _
KK-filterB-∈ f (KK-cons a as) KK-here fx with f a | fx
... | true  | _   = KK-here
... | false | () 
KK-filterB-∈ f (KK-cons a as) (KK-there x∈) fx with f a | fx
... | true  | _ = KK-there (KK-filterB-∈ f as x∈ fx)
... | false | _ = KK-filterB-∈ f as x∈ fx

-- 首方向见证: ⟨T₁,0,…,0⟩ 是 dir6-list 的表头 (KK-check 语义抽检用)
KK-d0 : GF3Vec 6
KK-d0 = T₁ ∷ KK-zero-vec 5

KK-d0-∈ : KK-∈L KK-d0 KK-dir6-list
KK-d0-∈ = KK-here

-- 覆盖引理: 每个非零向量与其规范代表同标量类 (dir6-list 覆盖全部方向)
KK-canon-scalar-cover : ∀ n (v : GF3Vec n) → KK-anyNZB n v ≡ true →
  Σ Trit (λ c → c ≢ T₀ × v ≡ KK-vec-scale n c (KK-canon n v))
KK-canon-scalar-cover zero [] ()
KK-canon-scalar-cover (suc n) (T₀ ∷ xs) h =
  let ih = KK-canon-scalar-cover n xs h in
  proj₁ ih , proj₁ (proj₂ ih) ,
  cong₂ _∷_ (sym (⊗-zeroʳ (proj₁ ih))) (proj₂ (proj₂ ih))
KK-canon-scalar-cover (suc n) (T₁ ∷ xs) _ =
  T₁ , (λ ()) , sym (KK-scale-one (suc n) (T₁ ∷ xs))
KK-canon-scalar-cover (suc n) (T₂ ∷ xs) _ =
  T₂ , (λ ()) , sym (cong (T₂ ∷_) (KK-scale-two-involution n xs))

-- ± 类恰一规范代表: 规范非零向量的 2 倍不再是规范形
KK-isCanon-scale2-false : ∀ n (v : GF3Vec n) →
  KK-isCanonB n v ≡ true → KK-anyNZB n v ≡ true →
  KK-isCanonB n (KK-vec-scale n T₂ v) ≡ false
KK-isCanon-scale2-false (suc n) (T₀ ∷ xs) h nz =
  KK-isCanon-scale2-false n xs h nz
KK-isCanon-scale2-false (suc n) (T₁ ∷ xs) _ _ = refl
KK-isCanon-scale2-false (suc n) (T₂ ∷ xs) () _

--------------------------------------------------------------------------------
-- §12. 指示函数形挂谷集与 KK-check 可判定验证器 (任务④: 验证解 only)
--
-- K : (Fin 6 → Trit) → Bool (指示函数形;点以函数形给出, 枚举点经 KK-tab6
--   送入 K)。IsKakeya6: 方向量化 = 364 规范代表列表 KK-dir6-list 的成员——
--   与 §8 record 的「非零向量量化」等价 (KK-canon-scalar-cover: 每个非零
--   向量与其规范代表同标量类, 张同一条线)。
-- 线上点: p + t·d 的 Vec 层构造 KK-line-point6 (§8) 经 KK-tab6 送入 K——
--   「逐点函数形」λ i → p i ⊕ (t ⊗ d i) 与 tab6 ∘ line-point6 逐点一致
--   (funext 下重合;本库以 Vec 层构造为准, 规避 funext 依赖)。
-- KK-check: Dec (IsKakeya6 K × lenK6 K ≡ k)——有限论域 (364×729) 暴力
--   可判定;执行抽检: 空集判 no、全空间判 yes。
-- ★ 两分声明: 本节是「验证解」;最优性 (极小基数下界证书, SAT/ILP UNSAT)
--   另任务, 见 §9/头注。
--------------------------------------------------------------------------------

-- 指示函数形: 点 = Fin 6 → Trit
KK-K6Ind : Set
KK-K6Ind = (Fin 6 → Trit) → Bool

-- 枚举点的函数形 (任务②的 (Fin 6 → Trit) 口径入口)
KK-tab6 : GF3Vec 6 → Fin 6 → Trit
KK-tab6 v i = lookup v i

-- 线上点检查: 三点 p + T₀·d, p + T₁·d, p + T₂·d 全在 K
KK-lineOK6 : KK-K6Ind → GF3Vec 6 → GF3Vec 6 → Bool
KK-lineOK6 K p dv =
  KK-andB (K (KK-tab6 (KK-line-point6 p dv T₀)))
          (KK-andB (K (KK-tab6 (KK-line-point6 p dv T₁)))
                   (K (KK-tab6 (KK-line-point6 p dv T₂))))

-- 单方向含线 (有界 ∃): ∃ p, 三点全在 K
KK-hasLine6 : KK-K6Ind → GF3Vec 6 → Set
KK-hasLine6 K dv =
  Σ (GF3Vec 6) (λ p → KK-lineOK6 K p dv ≡ true)

-- 挂谷性: 每 364 方向各含一条整线 (有界 ∀, ∀ 方向 d ∈ dir6-list → ∃ p)
KK-IsKakeya6 : KK-K6Ind → Set
KK-IsKakeya6 K =
  ∀ (dv : GF3Vec 6) → KK-∈L dv KK-dir6-list → KK-hasLine6 K dv

-- 指示基数: K 为真的点数 (729 点全查)
KK-lenK6 : KK-K6Ind → ℕ
KK-lenK6 K = KK-cnt (λ v → K (KK-tab6 v)) KK-vecs6

-- 基数上界: lenK6 ≤ 全点数
KK-m≤suc : ∀ m → m ≤ suc m
KK-m≤suc zero = z≤n
KK-m≤suc (suc m) = s≤s (KK-m≤suc m)

KK-cnt≤KK-length : ∀ {A : Set} (f : A → Bool) (xs : KK-List A) →
  KK-cnt f xs ≤ KK-length xs
KK-cnt≤KK-length f KK-nil = z≤n
KK-cnt≤KK-length f (KK-cons a as) with f a
... | true  = s≤s (KK-cnt≤KK-length f as)
... | false = ≤-trans (KK-cnt≤KK-length f as) (KK-m≤suc (KK-length as))

KK-lenK6-le : ∀ K → KK-lenK6 K ≤ KK-length KK-vecs6
KK-lenK6-le K = KK-cnt≤KK-length (λ v → K (KK-tab6 v)) KK-vecs6

-- 单方向判定 (anyDec: 首个满足的 p 即停)
KK-hasLine? : ∀ (K : KK-K6Ind) (dv : GF3Vec 6) → Dec (KK-hasLine6 K dv)
KK-hasLine? K dv with
  KK-anyDec (λ p → KK-lineOK6 K p dv ≡ true)
            (λ p → KK-Bool≟ (KK-lineOK6 K p dv) true)
            KK-vecs6
... | yes anyP = yes (KK-Any→Σ _ _ anyP)
... | no ¬anyP =
  no λ { (q , hq) →
    ¬anyP (KK-Σ→Any (λ p → KK-lineOK6 K p dv ≡ true)
                    (KK-vecsN-complete 6 q) hq) }

-- 挂谷性判定 (allDec: 首个失败的方向即停)
KK-kakeya? : ∀ (K : KK-K6Ind) → Dec (KK-IsKakeya6 K)
KK-kakeya? K with
  KK-allDec (λ dv → KK-hasLine6 K dv) (λ dv → KK-hasLine? K dv) KK-dir6-list
... | yes allP = yes (KK-All→∀∈ _ KK-dir6-list allP)
... | no ¬allP = no λ h → ¬allP (KK-∀∈→All _ KK-dir6-list h)

-- ★ KK-check: 可判定验证器 (任务④形态)
KK-check : (K : KK-K6Ind) (k : ℕ) → Dec (KK-IsKakeya6 K × KK-lenK6 K ≡ k)
KK-check K k = KK-×-dec (KK-kakeya? K) (KK-lenK6 K ≟ k)

-- 执行抽检 (空集): 判 no (语义)
KK-empty6 : KK-K6Ind
KK-empty6 = λ _ → false

-- 空集的线检查恒为 false (K 恒假 ⟹ andB 链归约 false), 三点式为空等式
KK-empty6-line-absurd : ∀ (p dv : GF3Vec 6) → KK-lineOK6 KK-empty6 p dv ≡ true → ⊥
KK-empty6-line-absurd p dv ()

KK-empty6-not : ¬ KK-IsKakeya6 KK-empty6
KK-empty6-not h =
  let (p , hline) = h KK-d0 KK-d0-∈ in
  KK-empty6-line-absurd p KK-d0 hline

KK-empty6-len : KK-lenK6 KK-empty6 ≡ 0
KK-empty6-len = refl

-- 执行抽检 (全空间): 判 yes (语义)
KK-full6 : KK-K6Ind
KK-full6 = λ _ → true

KK-full6-kakeya : KK-IsKakeya6 KK-full6
KK-full6-kakeya dv _ = KK-zero-vec 6 , refl

KK-full6-len : KK-lenK6 KK-full6 ≡ 729
KK-full6-len = refl

-- 执行抽检 (判定管线本身, 强制求值): 空集 → no, 全空间 → yes
KK-DecYes : ∀ {A : Set} → Dec A → Set
KK-DecYes (yes _) = ⊤
KK-DecYes (no _)  = ⊥

KK-DecNo : ∀ {A : Set} → Dec A → Set
KK-DecNo (yes _) = ⊥
KK-DecNo (no _)  = ⊤

KK-check-empty6-no : KK-DecNo (KK-check KK-empty6 0)
KK-check-empty6-no = tt

KK-check-full6-yes : KK-DecYes (KK-check KK-full6 729)
KK-check-full6-yes = tt

--------------------------------------------------------------------------------
-- §13. 实例闭合与闭合下界 (任务③的修正边界交付)
--
-- [n=1 精确闭合] 唯一方向 ⟨T₁⟩ 的直线 = 全空间 {p, p⊕1, p⊕2}, 故
--   挂谷 ⟺ 三点全真 ⟺ |K| = 3: KK-dvir-instance-1 (闭合) +
--   KK-len3→kakeya1 (反方向), 合成 KK-IsKakeya1 K ↔ KK-lenK1 K ≡ 3。
--   判定管线 KK-check1 在全空间/空集上强制求值 (yes/no 双侧)。
-- [n=6 几何] 线上三点两两相异 (KK-line3-distinct, 逐坐标构造):
--   非零方向在某坐标非零, GF(3) 特征 3 ⟹ t ↦ p + t·d 在该坐标单射。
-- [n=6 闭合下界] KK-kakeya6-ge3: 任何 KK-IsKakeya6 挂谷集满足
--   3 ≤ |K| (三个相异点全真 + 枚举计数), 强于 §8c 的 Dvir 1/n! 数值 2;
--   Dvir/deg-2/DKSW 的全称下界仍按 §8c/§9 口径立界。
--------------------------------------------------------------------------------

-- ── n=1: 唯一方向 ⟨T₁⟩ ──────────────────────────────────────────────

KK-lineOK1 : (Trit → Bool) → Trit → Bool
KK-lineOK1 K p =
  KK-andB (K (p ⊕ T₀))
          (KK-andB (K (p ⊕ T₁)) (K (p ⊕ (T₁ ⊕ T₁))))

KK-IsKakeya1 : (Trit → Bool) → Set
KK-IsKakeya1 K = Σ Trit (λ p → KK-lineOK1 K p ≡ true)

KK-lenK1 : (Trit → Bool) → ℕ
KK-lenK1 K = KK-cnt K KK-allTrits

-- 三点全真 ⟹ 计数 = 3 [逐点重写]
KK-cnt-true3 : ∀ (K : Trit → Bool) →
  K T₀ ≡ true → K T₁ ≡ true → K T₂ ≡ true → KK-lenK1 K ≡ 3
KK-cnt-true3 K h₀ h₁ h₂ rewrite h₀ | h₁ | h₂ = refl

-- 三点式反演 (显式 Bool 参数, 免元变量卡解)
KK-andB3-in : ∀ (a b c : Bool) → KK-andB a (KK-andB b c) ≡ true →
  a ≡ true × b ≡ true × c ≡ true
KK-andB3-in a b c h =
  proj₁ (KK-andB-in a (KK-andB b c) h) ,
  KK-andB-in b c (proj₂ (KK-andB-in a (KK-andB b c) h))

-- [闭合] 挂谷₁ ⟹ |K| = 3 (三案 p, 逐案线点归约 + andB 反演)
KK-dvir-instance-1 : ∀ (K : Trit → Bool) → KK-IsKakeya1 K → KK-lenK1 K ≡ 3
KK-dvir-instance-1 K (T₀ , h) =
  let q = KK-andB3-in (K (T₀ ⊕ T₀)) (K (T₀ ⊕ T₁)) (K (T₀ ⊕ (T₁ ⊕ T₁))) h in
  KK-cnt-true3 K (proj₁ q) (proj₁ (proj₂ q)) (proj₂ (proj₂ q))
KK-dvir-instance-1 K (T₁ , h) =
  let q = KK-andB3-in (K (T₁ ⊕ T₀)) (K (T₁ ⊕ T₁)) (K (T₁ ⊕ (T₁ ⊕ T₁))) h in
  KK-cnt-true3 K (proj₂ (proj₂ q)) (proj₁ q) (proj₁ (proj₂ q))
KK-dvir-instance-1 K (T₂ , h) =
  let q = KK-andB3-in (K (T₂ ⊕ T₀)) (K (T₂ ⊕ T₁)) (K (T₂ ⊕ (T₁ ⊕ T₁))) h in
  KK-cnt-true3 K (proj₁ (proj₂ q)) (proj₂ (proj₂ q)) (proj₁ q)

-- [闭合] 反方向: 三点全真 ⟹ 挂谷₁ (取 p = T₀ 见证)
KK-len3→kakeya1 : ∀ (K : Trit → Bool) →
  K T₀ ≡ true → K T₁ ≡ true → K T₂ ≡ true → KK-IsKakeya1 K
KK-len3→kakeya1 K h₀ h₁ h₂ =
  T₀ , KK-andB-cong (K (T₀ ⊕ T₀))
                    (KK-andB (K (T₀ ⊕ T₁)) (K (T₀ ⊕ (T₁ ⊕ T₁))))
                    h₀
                    (KK-andB-cong (K (T₀ ⊕ T₁)) (K (T₀ ⊕ (T₁ ⊕ T₁))) h₁ h₂)

-- n=1 判定管线 (三候选首中即停)
KK-kakeya1? : ∀ (K : Trit → Bool) → Dec (KK-IsKakeya1 K)
KK-kakeya1? K with
  KK-Bool≟ (KK-lineOK1 K T₀) true
    | KK-Bool≟ (KK-lineOK1 K T₁) true
    | KK-Bool≟ (KK-lineOK1 K T₂) true
... | yes h₀ | _     | _     = yes (T₀ , h₀)
... | no _   | yes h₁ | _     = yes (T₁ , h₁)
... | no _   | no _   | yes h₂ = yes (T₂ , h₂)
... | no ¬₀  | no ¬₁  | no ¬₂ =
  no (λ { (T₀ , h) → ¬₀ h ; (T₁ , h) → ¬₁ h ; (T₂ , h) → ¬₂ h })

KK-check1 : (K : Trit → Bool) (k : ℕ) →
  Dec (KK-IsKakeya1 K × KK-lenK1 K ≡ k)
KK-check1 K k = KK-×-dec (KK-kakeya1? K) (KK-lenK1 K ≟ k)

-- 执行抽检 (强制求值, 全管线 yes 分支逐字闭合)
KK-check1-full : KK-check1 (λ _ → true) 3 ≡ yes ((T₀ , refl) , refl)
KK-check1-full = refl

-- 执行抽检 (no 分支)
KK-empty1 : Trit → Bool
KK-empty1 = λ _ → false

KK-check1-empty-no : KK-DecNo (KK-check1 KK-empty1 0)
KK-check1-empty-no = tt

-- ── n=6 几何: 线上三点两两相异 ───────────────────────────────────────

KK-nzb→NZ : ∀ (x : Trit) → KK-nzb x ≡ true → KK-NonZeroTrit x
KK-nzb→NZ T₀ ()
KK-nzb→NZ T₁ _ = KK-nz₁
KK-nzb→NZ T₂ _ = KK-nz₂

KK-orB-true-inv : ∀ (a b : Bool) → KK-orB a b ≡ true → (a ≡ true) ⊎ (b ≡ true)
KK-orB-true-inv true b _ = inj₁ refl
KK-orB-true-inv false b h = inj₂ h

KK-anyNZB→nonzero : ∀ n (v : GF3Vec n) → KK-anyNZB n v ≡ true → KK-nonzero-vec n v
KK-anyNZB→nonzero zero [] ()
KK-anyNZB→nonzero (suc n) (x ∷ xs) h with KK-orB-true-inv (KK-nzb x) (KK-anyNZB n xs) h
... | inj₁ nzbT = inj₁ (KK-nzb→NZ x nzbT)
... | inj₂ restT = inj₂ (KK-anyNZB→nonzero n xs restT)

-- 非零向量 ⟹ 某坐标非零
KK-nonzero→coord : ∀ n (v : GF3Vec n) → KK-nonzero-vec n v →
  Σ (Fin n) (λ i → lookup v i ≢ T₀)
KK-nonzero→coord zero [] ()
KK-nonzero→coord (suc n) (x ∷ xs) (inj₁ KK-nz₁) = fzero , (λ ())
KK-nonzero→coord (suc n) (x ∷ xs) (inj₁ KK-nz₂) = fzero , (λ ())
KK-nonzero→coord (suc n) (x ∷ xs) (inj₂ rest) =
  let (i , neq) = KK-nonzero→coord n xs rest in
  fsuc i , neq

-- 逐坐标 lookup 桥
KK-lookup-scale : ∀ n (t : Trit) (v : GF3Vec n) (i : Fin n) →
  lookup (KK-vec-scale n t v) i ≡ t ⊗ lookup v i
KK-lookup-scale zero t [] ()
KK-lookup-scale (suc n) t (x ∷ xs) fzero = refl
KK-lookup-scale (suc n) t (x ∷ xs) (fsuc i) = KK-lookup-scale n t xs i

KK-lookup-plus : ∀ n (u v : GF3Vec n) (i : Fin n) →
  lookup (KK-vec-plus n u v) i ≡ lookup u i ⊕ lookup v i
KK-lookup-plus zero [] [] ()
KK-lookup-plus (suc n) (x ∷ xs) (y ∷ ys) fzero = refl
KK-lookup-plus (suc n) (x ∷ xs) (y ∷ ys) (fsuc i) = KK-lookup-plus n xs ys i

KK-lookup-line6 : ∀ (p dv : GF3Vec 6) (t : Trit) (i : Fin 6) →
  lookup (KK-line-point6 p dv t) i ≡ lookup p i ⊕ (t ⊗ lookup dv i)
KK-lookup-line6 p dv t i =
  trans (KK-lookup-plus 6 p (KK-vec-scale 6 t dv) i)
        (cong (λ w → lookup p i ⊕ w) (KK-lookup-scale 6 t dv i))

KK-lookup-cong-≢ : ∀ (i : Fin 6) (u v : GF3Vec 6) →
  lookup u i ≢ lookup v i → u ≢ v
KK-lookup-cong-≢ i u v neq e = neq (cong (λ w → lookup w i) e)

-- 坐标级单射: b ≢ T₀ ⟹ t ↦ a ⊕ t·b 在三点上两两相异 (6 案全显式归约)
KK-coord-line-inj : ∀ (a b : Trit) → b ≢ T₀ →
  (a ⊕ (T₀ ⊗ b) ≢ a ⊕ (T₁ ⊗ b)) ×
  (a ⊕ (T₁ ⊗ b) ≢ a ⊕ (T₂ ⊗ b)) ×
  (a ⊕ (T₀ ⊗ b) ≢ a ⊕ (T₂ ⊗ b))
KK-coord-line-inj a T₀ neq = ⊥-elim (neq refl)
KK-coord-line-inj T₀ T₁ _ = (λ ()) , ((λ ()) , λ ())
KK-coord-line-inj T₁ T₁ _ = (λ ()) , ((λ ()) , λ ())
KK-coord-line-inj T₂ T₁ _ = (λ ()) , ((λ ()) , λ ())
KK-coord-line-inj T₀ T₂ _ = (λ ()) , ((λ ()) , λ ())
KK-coord-line-inj T₁ T₂ _ = (λ ()) , ((λ ()) , λ ())
KK-coord-line-inj T₂ T₂ _ = (λ ()) , ((λ ()) , λ ())

-- [n=6 几何闭合] 过 p 沿非零方向 dv 的直线上三点两两相异 (|线| = 3)
KK-line3-distinct : ∀ (p dv : GF3Vec 6) → KK-nonzero-vec 6 dv →
  (KK-line-point6 p dv T₀ ≢ KK-line-point6 p dv T₁) ×
  (KK-line-point6 p dv T₁ ≢ KK-line-point6 p dv T₂) ×
  (KK-line-point6 p dv T₀ ≢ KK-line-point6 p dv T₂)
KK-line3-distinct p dv nz =
  let (i , neq) = KK-nonzero→coord 6 dv nz
      core = KK-coord-line-inj (lookup p i) (lookup dv i) neq
      step₁ = λ e → proj₁ core
        (trans (sym (KK-lookup-line6 p dv T₀ i))
          (trans (cong (λ w → lookup w i) e)
                 (KK-lookup-line6 p dv T₁ i)))
      step₂ = λ e → proj₁ (proj₂ core)
        (trans (sym (KK-lookup-line6 p dv T₁ i))
          (trans (cong (λ w → lookup w i) e)
                 (KK-lookup-line6 p dv T₂ i)))
      step₃ = λ e → proj₂ (proj₂ core)
        (trans (sym (KK-lookup-line6 p dv T₀ i))
          (trans (cong (λ w → lookup w i) e)
                 (KK-lookup-line6 p dv T₂ i)))
  in  step₁ , (step₂ , step₃)

-- ── 计数组合件 ──────────────────────────────────────────────────────

KK-len≥1 : ∀ {A : Set} (xs : KK-List A) {x : A} → KK-∈L x xs → 1 ≤ KK-length xs
KK-len≥1 KK-nil ()
KK-len≥1 (KK-cons a as) _ = s≤s z≤n

KK-length-ge2 : ∀ {A : Set} (x y : A) (xs : KK-List A) →
  KK-∈L x xs → KK-∈L y xs → x ≢ y → 2 ≤ KK-length xs
KK-length-ge2 x y (KK-cons a as) KK-here KK-here x≢y = ⊥-elim (x≢y refl)
KK-length-ge2 x y (KK-cons a as) KK-here (KK-there y∈) x≢y =
  s≤s (KK-len≥1 as y∈)
KK-length-ge2 x y (KK-cons a as) (KK-there x∈) KK-here x≢y =
  s≤s (KK-len≥1 as x∈)
KK-length-ge2 x y (KK-cons a as) (KK-there x∈) (KK-there y∈) x≢y =
  s≤s (KK-len≥1 as x∈)

KK-length-ge3 : ∀ {A : Set} (x y z : A) (xs : KK-List A) →
  KK-∈L x xs → KK-∈L y xs → KK-∈L z xs →
  x ≢ y → y ≢ z → x ≢ z → 3 ≤ KK-length xs
KK-length-ge3 x y z (KK-cons a as) KK-here KK-here KK-here x≢y _ _ =
  ⊥-elim (x≢y refl)
KK-length-ge3 x y z (KK-cons a as) KK-here KK-here (KK-there z∈) x≢y _ _ =
  ⊥-elim (x≢y refl)
KK-length-ge3 x y z (KK-cons a as) KK-here (KK-there y∈) KK-here _ _ x≢z =
  ⊥-elim (x≢z refl)
KK-length-ge3 x y z (KK-cons a as) (KK-there x∈) KK-here KK-here _ y≢z _ =
  ⊥-elim (y≢z refl)
KK-length-ge3 x y z (KK-cons a as) KK-here (KK-there y∈) (KK-there z∈) _ y≢z _ =
  s≤s (KK-length-ge2 y z as y∈ z∈ y≢z)
KK-length-ge3 x y z (KK-cons a as) (KK-there x∈) KK-here (KK-there z∈) _ _ x≢z =
  s≤s (KK-length-ge2 x z as x∈ z∈ x≢z)
KK-length-ge3 x y z (KK-cons a as) (KK-there x∈) (KK-there y∈) KK-here x≢y _ _ =
  s≤s (KK-length-ge2 x y as x∈ y∈ x≢y)
KK-length-ge3 x y z (KK-cons a as) (KK-there x∈) (KK-there y∈) (KK-there z∈) x≢y y≢z x≢z =
  s≤s (KK-length-ge2 x y as x∈ y∈ x≢y)

KK-cnt≡len-filterB : ∀ {A : Set} (f : A → Bool) (xs : KK-List A) →
  KK-cnt f xs ≡ KK-length (KK-filterB f xs)
KK-cnt≡len-filterB f KK-nil = refl
KK-cnt≡len-filterB f (KK-cons a as) with f a
... | true  = cong suc (KK-cnt≡len-filterB f as)
... | false = KK-cnt≡len-filterB f as

-- ── [n=6 闭合下界] 任何指示函数形挂谷集 |K| ≥ 3 ────────────────────

KK-kakeya6-ge3 : ∀ (K : KK-K6Ind) → KK-IsKakeya6 K → 3 ≤ KK-lenK6 K
KK-kakeya6-ge3 K h =
  let (p , hline) = h KK-d0 KK-d0-∈
      h₀ , hrest = KK-andB-in _ _ hline
      h₁ , h₂ = KK-andB-in _ _ hrest
      x = KK-line-point6 p KK-d0 T₀
      y = KK-line-point6 p KK-d0 T₁
      z = KK-line-point6 p KK-d0 T₂
      dist = KK-line3-distinct p KK-d0 (KK-anyNZB→nonzero 6 KK-d0 refl)
      f = λ v → K (KK-tab6 v)
      x∈ = KK-filterB-∈ f KK-vecs6 (KK-vecs6-complete x) h₀
      y∈ = KK-filterB-∈ f KK-vecs6 (KK-vecs6-complete y) h₁
      z∈ = KK-filterB-∈ f KK-vecs6 (KK-vecs6-complete z) h₂
      l3 = KK-length-ge3 x y z (KK-filterB f KK-vecs6) x∈ y∈ z∈
             (proj₁ dist) (proj₁ (proj₂ dist)) (proj₂ (proj₂ dist))
  in  subst (λ w → 3 ≤ w) (sym (KK-cnt≡len-filterB f KK-vecs6)) l3
