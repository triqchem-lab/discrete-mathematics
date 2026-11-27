{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Algebra.LinearAlgebra.TensorRankHK2GF3
-- M24: Hopcroft–Kerr 的 2×2 排除论证 —— GF(3) 上 ⟨2,2,2⟩ 的秩恰为 7
--
-- 数学背景
--   Hopcroft–Kerr（SIAM J. Appl. Math. 20 (1971); 一手来源是 Cornell 技术报告 TR69-44, 1969）证了
--   p×2 乘 2×n 至少要 ⌈(3pn + max(n,p))/2⌉ 次乘法, p = n = 2 时即 7。**但他们的下界只在 GF(2) 上证**:
--   报告第 15 页原话「we will assume that the elements of the matrix are binary numbers and addition and
--   multiplication are modulo two」, 再靠「整数上的算法取模 2」去约束整数情形, 并明说反方向不一定成立
--   （2a·b 在整数情形要一次乘法, 在模 2 下恒为零）。所以 GF(3) 不在他们的定理范围内。
--   Winograd（Linear Algebra Appl. 4 (1971) 381–388）的下界, 本件只凭 Wang 论文引言的转述, 没有对照原文。
--   **GF(3) 上的 7 不取自这两篇**: 它就是本件的证明。证明树的形状取自 Wang 框架 (arXiv:2603.07280)
--   §2 / 附录 C 对 F₂ 的走例, 数值预言取自框架在 F₃ 上的运行（engineering/wang_f3ext/certs, README §7.7）。
--   与论文走例的一处不同: 论文在残差那一步对 F₂ 枚举 2⁴ 个未知量, 这里对任意未知量 u, v 一次证完（res-flatten）。
--   框架在 F₃ 上对 ⟨2,2,2⟩ 也给出同一个证明树（10 个轨道, 两个超平面轨道各为 6, 全空间 7）:
--     ① 代换（全空间 ≥ 1 + 超平面）: 设 T 有 r 项分解。取第一系数非零的一项 i₀, 令 ℓ = a i₀。
--        把第一变元限制到 ker ℓ: 第 i₀ 项在 ker ℓ 上恒零, 丢掉 ⟹ 限制后的张量只有 r − 1 项。
--     ② 每个超平面都含一个「K 型」子空间: 非零泛函 ℓ 共 80 个。对每个 ℓ 给一对可逆矩阵 (P, Q),
--        W_j = P⁻¹ κ_j Q（κ₀ = J = [[0,1],[-1,0]], κ₁ = E₂₂）,
--        使 ℓ 在 W = span{W₀, W₁} 上恒零, 且 T(W_j, y, z) = Σ_{k,k'} A k y ⊗ B k' z ⊗ TK j k k'
--        （即 T(PXQ⁻¹, Y, Z) = T(X, Q⁻¹Y, PᵀZ)）。W 上的分解沿 (A, cA), (B, cB) 搬到 K = span{J, E₂₂} 上。
--        这 80 个见证列在 §4 的表里, 每行的恒等式由内核归约核对。
--     ③ forced product（K 上 ≥ 6）: TK 在 c₀₀ 与 c₀₁ 处的切片是单个的积 f ⊗ g 与 f ⊗ g'。
--        两次切片规范化 ⟹ 余项只有 r − 3 项; 余项的 y-切片有四个独立的线性组合（恒为 δ₂, δ₃, −δ₀, −δ₁,
--        与两次规范化留下的未知量 u, v 无关）⟹ 4 ≤ r − 3。
--     合起来 6 ≤ r − 1, 即 7 ≤ r。与 M13 的 rank-strassen 合读: 秩恰为 7。
--
-- 为什么 2×2 要单独立一件
--   · 这是库内头注自认的缺口: TensorRankGF3 / TensorRankFlattenGF3 都写着
--     「n = 2 时秩恰为 7 [直觉·未验证]」。本件把它关掉。
--   · 也是立项 C 的试验田: 同一套通用件（M23）后面服务 Bläser 的 19（C-T3）。
--
-- 诚实边界
--   · ② 的分类没有抽象证明: 实现是一张 80 行的见证表, 每行由内核对闭项归约核对。
--     表的正确性不依赖生成它的 oracle; oracle 只负责产出与对账。
--     [直觉·未验证] 「80 个非零泛函在 (P, Q) 作用下按 ℓ 的矩阵秩分两个轨道（秩 1 的 32 个、可逆的 48 个）」
--     ——这是标准事实, 但库内没有对应定理, 本件也不需要它: 见证表逐个泛函给证据, 不经过轨道论证。
--     oracle 只核了计数（`hk2_classify_all` 打印 32 / 48）, 没核「同轨道的泛函核同构」。
--   · ③ 里「余项的 y-切片张成 4 维」用的是 M23 的计数下界, 不是矩阵秩（库内没有秩的不变性理论）。
--   · 本件只处理 GF(3) 与 2×2; n = 3 的下界仍是 r ≥ 9（展平）。
--
-- 复用（先查后写）: Mat2·mulMat2(Matrix2) / mm·RankLE₃·rank-strassen·sc(TensorRankGF3) /
--   TritSolver(TritStdlibRing: Trit 上的标准库交换环 + ring solver) /
--   RankLE·rank-restrict(TensorRankIndexGF3) / ★slice-normalize·SpanGen·★rank-change₂₃·rank-cong
--   (TensorRankAlgebraGF3) / fromFun·toFun·fromFun-toFun(GF3Count) / fromFun-cong(GF3BasisCount) /
--   T₀≢T₁(NumberTheory/DiscreteFibonacci: 库内已有两处同名引理, 不再写第三处)。
--   2×2 矩阵的逆: Synthesis/Representation/Matrix2Inverse 在上层, 层序禁反向依赖;
--   这里的 inv2 只是个计算公式, 它的「正确性」体现在每行见证被核对的两条逆恒等式里。
--
-- 先算后验: engineering/oracle_tensor_rank_gf3.py 的 M23/M24 一节（残差权重 26244/26244;
--   80 个泛函的见证; Strassen 真实分解上的端到端 7/7）。§4 的表由它生成并对账（--hk2-table）。
--
-- 0 postulate / 0 REWRITE 规则 / 0 洞
module Sovereign.Algebra.LinearAlgebra.TensorRankHK2GF3 where

open import Data.Nat using (ℕ; zero; suc; pred; _^_; _≤_; _<_; z≤n; s≤s)
open import Data.Nat.Properties using (<⇒≱; ≤-refl; m≤m+n)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.Fin.Properties using (_≟_)
open import Data.Product using (_×_; _,_; proj₁; proj₂; Σ)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Bool.Base using (T)
open import Data.Unit.Base using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; cong₂)
open import Relation.Nullary using (yes; no; Dec)
open import Relation.Nullary.Decidable.Core using (toWitness; True)

open import Sovereign.Base.Trit using
  (Trit; T₀; T₁; T₂; _⊕_; _⊗_; negate; negate²
  ; ⊕-identityʳ; ⊕-comm; ⊕-assoc; ⊕-inverse
  ; ⊗-identityˡ; ⊗-identityʳ; ⊗-comm; ⊗-assoc; ⊗-zeroˡ; ⊗-zeroʳ
  ; ⊗-distribˡ-⊕; ⊗-distribʳ-⊕)
open import Sovereign.Algebra.LinearAlgebra.GF3LaplacianN using (sumFin; sumFin-cong)
open import Sovereign.Algebra.NumberTheory.DiscreteFibonacci using (T₀≢T₁)
open import Sovereign.Algebra.LinearAlgebra.GF3RankNullity using (sumFin-add)
open import Sovereign.Algebra.LinearAlgebra.GF3Dim using (δc)
open import Sovereign.Algebra.LinearAlgebra.GF3Count using (toFun; fromFun; fromFun-toFun)
open import Sovereign.Algebra.LinearAlgebra.GF3BasisCount using (fromFun-cong)
open import Sovereign.Algebra.LinearAlgebra.Matrix2 using (Mat2; mkMat2; m00; m01; m10; m11; mulMat2)
open import Sovereign.Algebra.LinearAlgebra.TensorRankFlattenGF3 using (rank-lower)
open import Sovereign.Algebra.LinearAlgebra.TensorRankGF3 using (Pos; Out; mm; RankLE₃; rank-strassen; sc)
open import Sovereign.Algebra.RingTheory.TritStdlibRing using (module TritSolver; _≟ₜ_)
open TritSolver using (_:=_; _:+_; _:*_; :-_) renaming (con to conₜ)
open import Sovereign.Algebra.LinearAlgebra.TensorRankIndexGF3
  using (RankLE; rankLE₃→idx; rank-restrict; rank-swap; rank-rot)
open import Sovereign.Algebra.LinearAlgebra.TensorRankAlgebraGF3
open RankLE using (ra; rb; rc; rank-eq)

-- Fin 4 的四个下标（只用于表达式; 模式里写构造子）
ix₀ ix₁ ix₂ ix₃ : Fin 4
ix₀ = fzero
ix₁ = fsuc fzero
ix₂ = fsuc (fsuc fzero)
ix₃ = fsuc (fsuc (fsuc fzero))

--------------------------------------------------------------------------------
-- §1 坐标化: 位置 ↔ Fin 4
--------------------------------------------------------------------------------

-- Fin 4 → 位置（行主序）
unpos : Fin 4 → Pos 2
unpos fzero = fzero , fzero
unpos (fsuc fzero) = fzero , fsuc fzero
unpos (fsuc (fsuc fzero)) = fsuc fzero , fzero
unpos (fsuc (fsuc (fsuc fzero))) = fsuc fzero , fsuc fzero

-- ★ 坐标化的结构常数
T4 : Fin 4 → Fin 4 → Fin 4 → Trit
T4 p y z = mm 2 (unpos p) (unpos y) (unpos z)

-- 位置指标换成坐标（三次拉回）
to-coords : ∀ r → RankLE (Pos 2) (Pos 2) (Out 2) (mm 2) r → RankLE (Fin 4) (Fin 4) (Fin 4) T4 r
to-coords r ρ = record
  { ra = λ i p → ra ρ i (unpos p)
  ; rb = λ i y → rb ρ i (unpos y)
  ; rc = λ i z → rc ρ i (unpos z)
  ; rank-eq = λ p y z → rank-eq ρ (unpos p) (unpos y) (unpos z) }

--------------------------------------------------------------------------------
-- §2 K = span{J, E₂₂} 上的张量与它的两个单积切片
--------------------------------------------------------------------------------

-- K 的基在 Fin 4 上的坐标行: J = [[0,1],[-1,0]], E₂₂
sK : Fin 2 → Fin 4 → Trit
sK fzero fzero = T₀
sK fzero (fsuc fzero) = T₁
sK fzero (fsuc (fsuc fzero)) = T₂
sK fzero (fsuc (fsuc (fsuc fzero))) = T₀
sK (fsuc fzero) fzero = T₀
sK (fsuc fzero) (fsuc fzero) = T₀
sK (fsuc fzero) (fsuc (fsuc fzero)) = T₀
sK (fsuc fzero) (fsuc (fsuc (fsuc fzero))) = T₁

-- ★ K 上的张量: mm 2 沿 sK 的线性限制（X = [[0, a],[-a, d]]）
TK : Fin 2 → Fin 4 → Fin 4 → Trit
TK j y z = sumFin (λ p → (sK j p) ⊗ (T4 p y z))

-- 切片的因子: f x = [x = a];  g = δ 在 b₁₀;  g' = δ 在 b₁₁
fK : Fin 2 → Trit
fK fzero = T₁
fK (fsuc fzero) = T₀

gK : Fin 4 → Trit
gK = δc ix₂

gK' : Fin 4 → Trit
gK' = δc ix₃

-- ★ TK 在 c₀₀ 处的切片是单个的积 f ⊗ g（X = [[0,a],[-a,d]] 时 (XY)₀₀ = a·y₁₀）
TK-slice₀ : ∀ x y → TK x y ix₀ ≡ (fK x) ⊗ (gK y)
TK-slice₀ fzero fzero = refl
TK-slice₀ fzero (fsuc fzero) = refl
TK-slice₀ fzero (fsuc (fsuc fzero)) = refl
TK-slice₀ fzero (fsuc (fsuc (fsuc fzero))) = refl
TK-slice₀ (fsuc fzero) fzero = refl
TK-slice₀ (fsuc fzero) (fsuc fzero) = refl
TK-slice₀ (fsuc fzero) (fsuc (fsuc fzero)) = refl
TK-slice₀ (fsuc fzero) (fsuc (fsuc (fsuc fzero))) = refl

-- ★ TK 在 c₀₁ 处的切片是单个的积 f ⊗ g'（(XY)₀₁ = a·y₁₁）
TK-slice₁ : ∀ x y → TK x y ix₁ ≡ (fK x) ⊗ (gK' y)
TK-slice₁ fzero fzero = refl
TK-slice₁ fzero (fsuc fzero) = refl
TK-slice₁ fzero (fsuc (fsuc fzero)) = refl
TK-slice₁ fzero (fsuc (fsuc (fsuc fzero))) = refl
TK-slice₁ (fsuc fzero) fzero = refl
TK-slice₁ (fsuc fzero) (fsuc fzero) = refl
TK-slice₁ (fsuc fzero) (fsuc (fsuc fzero)) = refl
TK-slice₁ (fsuc fzero) (fsuc (fsuc (fsuc fzero))) = refl

--------------------------------------------------------------------------------
-- §3 残差与它的切片下界
--------------------------------------------------------------------------------

-- ★ 两次规范化后的余项: TK ⊕ −f⊗(g⊗u) ⊕ −f⊗(g'⊗v)（u, v 任意）
Res : (Fin 4 → Trit) → (Fin 4 → Trit) → Fin 2 → Fin 4 → Fin 4 → Trit
Res u v x y z =
  ((TK x y z) ⊕ negate ((fK x) ⊗ ((gK y) ⊗ (u z)))) ⊕ negate ((fK x) ⊗ ((gK' y) ⊗ (v z)))

-- 四个 Fin 4 的点上的全称引入与判定
all₄ : ∀ {P : Fin 4 → Set} → P fzero → P (fsuc fzero) → P (fsuc (fsuc fzero)) → P (fsuc (fsuc (fsuc fzero))) →
       ∀ k → P k
all₄ p0 p1 p2 p3 fzero = p0
all₄ p0 p1 p2 p3 (fsuc fzero) = p1
all₄ p0 p1 p2 p3 (fsuc (fsuc fzero)) = p2
all₄ p0 p1 p2 p3 (fsuc (fsuc (fsuc fzero))) = p3

all₂ : ∀ {P : Fin 2 → Set} → P fzero → P (fsuc fzero) → ∀ j → P j
all₂ p0 p1 fzero = p0
all₂ p0 p1 (fsuc fzero) = p1

dec₄ : ∀ {P : Fin 4 → Set} → ((k : Fin 4) → Dec (P k)) → Dec (∀ k → P k)
dec₄ d with d fzero | d (fsuc fzero) | d (fsuc (fsuc fzero)) | d (fsuc (fsuc (fsuc fzero)))
... | yes a | yes b | yes c | yes e = yes (all₄ a b c e)
... | no ¬a | _ | _ | _ = no (λ h → ¬a (h fzero))
... | yes _ | no ¬b | _ | _ = no (λ h → ¬b (h (fsuc fzero)))
... | yes _ | yes _ | no ¬c | _ = no (λ h → ¬c (h (fsuc (fsuc fzero))))
... | yes _ | yes _ | yes _ | no ¬e = no (λ h → ¬e (h (fsuc (fsuc (fsuc fzero)))))

dec₂ : ∀ {P : Fin 2 → Set} → ((j : Fin 2) → Dec (P j)) → Dec (∀ j → P j)
dec₂ d with d fzero | d (fsuc fzero)
... | yes a | yes b = yes (all₂ a b)
... | no ¬a | _ = no (λ h → ¬a (h fzero))
... | yes _ | no ¬b = no (λ h → ¬b (h (fsuc fzero)))

--------------------------------------------------------------------------------
-- §3a 残差: 取值与切片组合
--------------------------------------------------------------------------------

-- 乘 T₂ 就是取反（右因子）
⊗-T₂ : ∀ x → x ⊗ T₂ ≡ negate x
⊗-T₂ T₀ = refl
⊗-T₂ T₁ = refl
⊗-T₂ T₂ = refl

-- 乘 T₂ 就是取反（左因子）
⊗T₂ : ∀ x → T₂ ⊗ x ≡ negate x
⊗T₂ x = trans (⊗-comm T₂ x) (⊗-T₂ x)

-- 取反是单射
neg-inj : ∀ a b → negate a ≡ negate b → a ≡ b
neg-inj a b h = trans (sym (negate² a)) (trans (cong negate h) (negate² b))

-- 左因子 T₁ 乘上「标量乘」: T₁ ⊗ (c ⊗ x) ≡ sc c x
scal : ∀ c x → (T₁ ⊗ (c ⊗ x)) ≡ sc c x
scal T₀ x = refl
scal T₁ x = trans (⊗-identityˡ (T₁ ⊗ x)) (⊗-identityˡ x)
scal T₂ x = trans (⊗-identityˡ (T₂ ⊗ x)) (⊗T₂ x)

-- Fin 2 与 Fin 4 上的和的「干净」形状
sum₂-eval : ∀ (g : Fin 2 → Trit) → sumFin g ≡ g fzero ⊕ g (fsuc fzero)
sum₂-eval g =
  TritSolver.solve 2 (λ a b → a :+ (b :+ conₜ T₀) := a :+ b) refl (g fzero) (g (fsuc fzero))

quad : (Fin 4 → Trit) → Trit
quad g = ((g fzero ⊕ g (fsuc fzero)) ⊕ g (fsuc (fsuc fzero))) ⊕ g (fsuc (fsuc (fsuc fzero)))

sum₄-eval : ∀ (g : Fin 4 → Trit) → sumFin g ≡ quad g
sum₄-eval g =
  TritSolver.solve 4 (λ a b c d → a :+ (b :+ (c :+ (d :+ conₜ T₀))) := ((a :+ b) :+ c) :+ d) refl
    (g fzero) (g (fsuc fzero)) (g (fsuc (fsuc fzero))) (g (fsuc (fsuc (fsuc fzero))))

-- ★ TK 的两行: a-行 = T4(b₀₁,·,·) ⊕ −T4(b₁₀,·,·);  d-行 = T4(b₁₁,·,·)
TKa : ∀ y z → TK fzero y z ≡ (T4 ix₁ y z) ⊕ negate (T4 ix₂ y z)
TKa y z =
  trans (sum₄-eval (λ p → (sK fzero p) ⊗ (T4 p y z)))
        (TritSolver.solve 4 (λ a b c d → ((conₜ T₀ :* d :+ conₜ T₁ :* a) :+ conₜ T₂ :* b) :+ conₜ T₀ :* c
                                   := a :+ :- b) refl
           (T4 ix₁ y z) (T4 ix₂ y z) (T4 ix₃ y z) (T4 fzero y z))

TKd : ∀ y z → TK (fsuc fzero) y z ≡ T4 ix₃ y z
TKd y z =
  trans (sum₄-eval (λ p → (sK (fsuc fzero) p) ⊗ (T4 p y z)))
        (TritSolver.solve 4 (λ a b c d → ((conₜ T₀ :* a :+ conₜ T₀ :* b) :+ conₜ T₀ :* c) :+ conₜ T₁ :* d
                                   := d) refl
           (T4 fzero y z) (T4 ix₁ y z) (T4 ix₂ y z) (T4 ix₃ y z))

-- ★ Res 的 d-行就是 TK 的 d-行（fK 在 d 处为零, 减掉的两项消失）
Rd : ∀ u v y z → Res u v (fsuc fzero) y z ≡ T4 ix₃ y z
Rd u v y z =
  trans (cong (λ t → (t ⊕ T₀) ⊕ T₀) (TKd y z))
        (TritSolver.solve 1 (λ a → (a :+ conₜ T₀) :+ conₜ T₀ := a) refl (T4 ix₃ y z))

-- ★ Res 的 a-行: TK 的 a-行 ⊕ −(f ⊗ g ⊗ u) ⊕ −(f ⊗ g' ⊗ v)（g, g' 处化成标量乘）
Rc : ∀ u v y z → Res u v fzero y z ≡
     (((T4 ix₁ y z) ⊕ negate (T4 ix₂ y z)) ⊕ negate (sc (gK y) (u z))) ⊕ negate (sc (gK' y) (v z))
Rc u v y z =
  trans (cong (λ t → (t ⊕ negate (T₁ ⊗ (gK y ⊗ (u z)))) ⊕ negate (T₁ ⊗ (gK' y ⊗ (v z)))) (TKa y z))
        (cong₂ (λ p q → (((T4 ix₁ y z) ⊕ negate (T4 ix₂ y z)) ⊕ negate p) ⊕ negate q)
               (scal (gK y) (u z)) (scal (gK' y) (v z)))

-- ★ y-切片的线性组合（不依赖分解本身; 与 SpanGen 的 W 定义等价, 见 ResSpan.W≡WR）
--   WR q u v y = Σ_x Σ_z q x z ⊗ Res u v x y z
WR : (Fin 2 → Fin 4 → Trit) → (Fin 4 → Trit) → (Fin 4 → Trit) → Fin 4 → Trit
WR q u v y = sumFin (λ x → sumFin (λ z → (q x z) ⊗ (Res u v x y z)))

WR-eval : ∀ q u v y → WR q u v y ≡
           (quad (λ z → (q fzero z) ⊗ (Res u v fzero y z))) ⊕
           (quad (λ z → (q (fsuc fzero) z) ⊗ (Res u v (fsuc fzero) y z)))
WR-eval q u v y =
  trans (sum₂-eval (λ x → sumFin (λ z → (q x z) ⊗ (Res u v x y z))))
        (cong₂ _⊕_ (sum₄-eval (λ z → (q fzero z) ⊗ (Res u v fzero y z)))
                    (sum₄-eval (λ z → (q (fsuc fzero) z) ⊗ (Res u v (fsuc fzero) y z))))

-- 四个权重（下标 x ∈ {a, d}, z ∈ Fin 4）: 组合出来恰是 δ₂, δ₃, −δ₀, −δ₁（后两个与 u, v 无关）
lam₁ : Fin 2 → Fin 4 → Trit
lam₁ fzero _ = T₀
lam₁ (fsuc fzero) (fsuc (fsuc fzero)) = T₁
lam₁ (fsuc fzero) _ = T₀

lam₂ : Fin 2 → Fin 4 → Trit
lam₂ fzero _ = T₀
lam₂ (fsuc fzero) (fsuc (fsuc (fsuc fzero))) = T₁
lam₂ (fsuc fzero) _ = T₀

lam₃ : (Fin 4 → Trit) → (Fin 4 → Trit) → Fin 2 → Fin 4 → Trit
lam₃ u v fzero (fsuc (fsuc fzero)) = T₁
lam₃ u v fzero _ = T₀
lam₃ u v (fsuc fzero) (fsuc (fsuc fzero)) = u ix₂
lam₃ u v (fsuc fzero) (fsuc (fsuc (fsuc fzero))) = v ix₂
lam₃ u v (fsuc fzero) _ = T₀

lam₄ : (Fin 4 → Trit) → (Fin 4 → Trit) → Fin 2 → Fin 4 → Trit
lam₄ u v fzero (fsuc (fsuc (fsuc fzero))) = T₁
lam₄ u v fzero _ = T₀
lam₄ u v (fsuc fzero) (fsuc (fsuc fzero)) = u ix₃
lam₄ u v (fsuc fzero) (fsuc (fsuc (fsuc fzero))) = v ix₃
lam₄ u v (fsuc fzero) _ = T₀

-- 权重的组合: 只留下非零的项
lam₁-eval : ∀ u v y → WR lam₁ u v y ≡ Res u v (fsuc fzero) y ix₂
lam₁-eval u v y =
  trans (WR-eval lam₁ u v y)
        (TritSolver.solve 8
           (λ r0 r1 r2 r3 s0 s1 s2 s3 →
              (((conₜ T₀ :* r0 :+ conₜ T₀ :* r1) :+ conₜ T₀ :* r2) :+ conₜ T₀ :* r3) :+
              (((conₜ T₀ :* s0 :+ conₜ T₀ :* s1) :+ conₜ T₁ :* s2) :+ conₜ T₀ :* s3) := s2)
           refl (Res u v fzero y fzero) (Res u v fzero y ix₁) (Res u v fzero y ix₂) (Res u v fzero y ix₃)
           (Res u v (fsuc fzero) y fzero) (Res u v (fsuc fzero) y ix₁) (Res u v (fsuc fzero) y ix₂)
           (Res u v (fsuc fzero) y ix₃))

lam₂-eval : ∀ u v y → WR lam₂ u v y ≡ Res u v (fsuc fzero) y ix₃
lam₂-eval u v y =
  trans (WR-eval lam₂ u v y)
        (TritSolver.solve 8
           (λ r0 r1 r2 r3 s0 s1 s2 s3 →
              (((conₜ T₀ :* r0 :+ conₜ T₀ :* r1) :+ conₜ T₀ :* r2) :+ conₜ T₀ :* r3) :+
              (((conₜ T₀ :* s0 :+ conₜ T₀ :* s1) :+ conₜ T₀ :* s2) :+ conₜ T₁ :* s3) := s3)
           refl (Res u v fzero y fzero) (Res u v fzero y ix₁) (Res u v fzero y ix₂) (Res u v fzero y ix₃)
           (Res u v (fsuc fzero) y fzero) (Res u v (fsuc fzero) y ix₁) (Res u v (fsuc fzero) y ix₂)
           (Res u v (fsuc fzero) y ix₃))

lam₃-eval : ∀ u v y → WR (lam₃ u v) u v y ≡
            (Res u v fzero y ix₂) ⊕ (((u ix₂) ⊗ (Res u v (fsuc fzero) y ix₂)) ⊕ ((v ix₂) ⊗ (Res u v (fsuc fzero) y ix₃)))
lam₃-eval u v y =
  trans (WR-eval (lam₃ u v) u v y)
        (TritSolver.solve 10
           (λ r0 r1 r2 r3 s0 s1 s2 s3 a b →
              (((conₜ T₀ :* r0 :+ conₜ T₀ :* r1) :+ conₜ T₁ :* r2) :+ conₜ T₀ :* r3) :+
              (((conₜ T₀ :* s0 :+ conₜ T₀ :* s1) :+ (a :* s2)) :+ (b :* s3)) := r2 :+ ((a :* s2) :+ (b :* s3)))
           refl (Res u v fzero y fzero) (Res u v fzero y ix₁) (Res u v fzero y ix₂) (Res u v fzero y ix₃)
           (Res u v (fsuc fzero) y fzero) (Res u v (fsuc fzero) y ix₁) (Res u v (fsuc fzero) y ix₂)
           (Res u v (fsuc fzero) y ix₃) (u ix₂) (v ix₂))

lam₄-eval : ∀ u v y → WR (lam₄ u v) u v y ≡
            (Res u v fzero y ix₃) ⊕ (((u ix₃) ⊗ (Res u v (fsuc fzero) y ix₂)) ⊕ ((v ix₃) ⊗ (Res u v (fsuc fzero) y ix₃)))
lam₄-eval u v y =
  trans (WR-eval (lam₄ u v) u v y)
        (TritSolver.solve 10
           (λ r0 r1 r2 r3 s0 s1 s2 s3 a b →
              (((conₜ T₀ :* r0 :+ conₜ T₀ :* r1) :+ conₜ T₀ :* r2) :+ conₜ T₁ :* r3) :+
              (((conₜ T₀ :* s0 :+ conₜ T₀ :* s1) :+ (a :* s2)) :+ (b :* s3)) := r3 :+ ((a :* s2) :+ (b :* s3)))
           refl (Res u v fzero y fzero) (Res u v fzero y ix₁) (Res u v fzero y ix₂) (Res u v fzero y ix₃)
           (Res u v (fsuc fzero) y fzero) (Res u v (fsuc fzero) y ix₁) (Res u v (fsuc fzero) y ix₂)
           (Res u v (fsuc fzero) y ix₃) (u ix₃) (v ix₃))

-- 把 lam₃ 的组合里的 Res 换成取值（a = u 在 c₁₀ 处, b = v 在 c₁₀ 处）
--   得到 (((T4 ix₁ y ix₂ ⊕ −T4 ix₂ y ix₂) ⊕ −sc(gK y) a) ⊕ −sc(gK' y) b) ⊕ ((a ⊗ T4 ix₃ y ix₂) ⊕ (b ⊗ T4 ix₃ y ix₃))
lam₃-val : ∀ u v y → WR (lam₃ u v) u v y ≡
           ((((T4 ix₁ y ix₂) ⊕ negate (T4 ix₂ y ix₂)) ⊕ negate (sc (gK y) (u ix₂))) ⊕ negate (sc (gK' y) (v ix₂))) ⊕
           (((u ix₂) ⊗ (T4 ix₃ y ix₂)) ⊕ ((v ix₂) ⊗ (T4 ix₃ y ix₃)))
lam₃-val u v y =
  trans (lam₃-eval u v y)
        (cong₂ _⊕_ (Rc u v y ix₂)
               (cong₂ _⊕_ (cong (λ t → (u ix₂) ⊗ t) (Rd u v y ix₂))
                          (cong (λ t → (v ix₂) ⊗ t) (Rd u v y ix₃))))

lam₄-val : ∀ u v y → WR (lam₄ u v) u v y ≡
           ((((T4 ix₁ y ix₃) ⊕ negate (T4 ix₂ y ix₃)) ⊕ negate (sc (gK y) (u ix₃))) ⊕ negate (sc (gK' y) (v ix₃))) ⊕
           (((u ix₃) ⊗ (T4 ix₃ y ix₂)) ⊕ ((v ix₃) ⊗ (T4 ix₃ y ix₃)))
lam₄-val u v y =
  trans (lam₄-eval u v y)
        (cong₂ _⊕_ (Rc u v y ix₃)
               (cong₂ _⊕_ (cong (λ t → (u ix₃) ⊗ t) (Rd u v y ix₂))
                          (cong (λ t → (v ix₃) ⊗ t) (Rd u v y ix₃))))

-- ★ W lam₁ = δ₂（逐点: T4 ix₃ y ix₂ 只在 y = b₁₀ 处取 1）
Wlam₁ : ∀ u v y → WR lam₁ u v y ≡ δc ix₂ y
Wlam₁ u v fzero = trans (lam₁-eval u v fzero) (Rd u v fzero ix₂)
Wlam₁ u v (fsuc fzero) = trans (lam₁-eval u v (fsuc fzero)) (Rd u v (fsuc fzero) ix₂)
Wlam₁ u v (fsuc (fsuc fzero)) = trans (lam₁-eval u v (fsuc (fsuc fzero))) (Rd u v (fsuc (fsuc fzero)) ix₂)
Wlam₁ u v (fsuc (fsuc (fsuc fzero))) =
  trans (lam₁-eval u v (fsuc (fsuc (fsuc fzero)))) (Rd u v (fsuc (fsuc (fsuc fzero))) ix₂)

-- ★ W lam₂ = δ₃
Wlam₂ : ∀ u v y → WR lam₂ u v y ≡ δc ix₃ y
Wlam₂ u v fzero = trans (lam₂-eval u v fzero) (Rd u v fzero ix₃)
Wlam₂ u v (fsuc fzero) = trans (lam₂-eval u v (fsuc fzero)) (Rd u v (fsuc fzero) ix₃)
Wlam₂ u v (fsuc (fsuc fzero)) = trans (lam₂-eval u v (fsuc (fsuc fzero))) (Rd u v (fsuc (fsuc fzero)) ix₃)
Wlam₂ u v (fsuc (fsuc (fsuc fzero))) =
  trans (lam₂-eval u v (fsuc (fsuc (fsuc fzero)))) (Rd u v (fsuc (fsuc (fsuc fzero))) ix₃)

-- ★ W lam₃ = −δ₀（与 u, v 无关）
--   y = b₀₀: Res(a,·,c₁₀) = −1, Res(d,·,·) = 0;  y = b₀₁: 全 0
Wlam₃ : ∀ u v y → WR (lam₃ u v) u v y ≡ negate (δc fzero y)
Wlam₃ u v fzero =
  trans (lam₃-val u v fzero)
        (TritSolver.solve 2 (λ a b → ((((conₜ T₀ :+ :- (conₜ T₁)) :+ :- (conₜ T₀)) :+ :- (conₜ T₀)) :+
                                      ((a :* conₜ T₀) :+ (b :* conₜ T₀))) := :- (conₜ T₁)) refl (u ix₂) (v ix₂))
Wlam₃ u v (fsuc fzero) =
  trans (lam₃-val u v (fsuc fzero))
        (TritSolver.solve 2 (λ a b → ((((conₜ T₀ :+ :- (conₜ T₀)) :+ :- (conₜ T₀)) :+ :- (conₜ T₀)) :+
                                      ((a :* conₜ T₀) :+ (b :* conₜ T₀))) := conₜ T₀) refl (u ix₂) (v ix₂))
--   y = b₁₀: Res(a,b₁₀,c₁₀) = −a, Res(d,b₁₀,c₁₀) = 1, Res(d,b₁₀,c₁₁) = 0  ⟹  −a ⊕ a = 0
Wlam₃ u v (fsuc (fsuc fzero)) =
  trans (lam₃-val u v (fsuc (fsuc fzero)))
        (TritSolver.solve 2 (λ a b → ((((conₜ T₀ :+ :- (conₜ T₀)) :+ :- a) :+ :- (conₜ T₀)) :+
                                      ((a :* conₜ T₁) :+ (b :* conₜ T₀))) := conₜ T₀) refl (u ix₂) (v ix₂))
--   y = b₁₁: Res(a,b₁₁,c₁₀) = −b, Res(d,b₁₁,c₁₀) = 0, Res(d,b₁₁,c₁₁) = 1  ⟹  −b ⊕ b = 0
Wlam₃ u v (fsuc (fsuc (fsuc fzero))) =
  trans (lam₃-val u v (fsuc (fsuc (fsuc fzero))))
        (TritSolver.solve 2 (λ a b → ((((conₜ T₀ :+ :- (conₜ T₀)) :+ :- (conₜ T₀)) :+ :- b) :+
                                      ((a :* conₜ T₀) :+ (b :* conₜ T₁))) := conₜ T₀) refl (u ix₂) (v ix₂))

-- ★ W lam₄ = −δ₁（与 u, v 无关）
Wlam₄ : ∀ u v y → WR (lam₄ u v) u v y ≡ negate (δc (fsuc fzero) y)
--   y = b₀₀: 全 0
Wlam₄ u v fzero =
  trans (lam₄-val u v fzero)
        (TritSolver.solve 2 (λ a b → ((((conₜ T₀ :+ :- (conₜ T₀)) :+ :- (conₜ T₀)) :+ :- (conₜ T₀)) :+
                                      ((a :* conₜ T₀) :+ (b :* conₜ T₀))) := conₜ T₀) refl (u ix₃) (v ix₃))
--   y = b₀₁: Res(a,b₀₁,c₁₁) = −1, Res(d,·,·) = 0
Wlam₄ u v (fsuc fzero) =
  trans (lam₄-val u v (fsuc fzero))
        (TritSolver.solve 2 (λ a b → ((((conₜ T₀ :+ :- (conₜ T₁)) :+ :- (conₜ T₀)) :+ :- (conₜ T₀)) :+
                                      ((a :* conₜ T₀) :+ (b :* conₜ T₀))) := :- (conₜ T₁)) refl (u ix₃) (v ix₃))
--   y = b₁₀: Res(a,b₁₀,c₁₁) = −a, Res(d,b₁₀,c₁₀) = 1, Res(d,b₁₀,c₁₁) = 0
Wlam₄ u v (fsuc (fsuc fzero)) =
  trans (lam₄-val u v (fsuc (fsuc fzero)))
        (TritSolver.solve 2 (λ a b → ((((conₜ T₀ :+ :- (conₜ T₀)) :+ :- a) :+ :- (conₜ T₀)) :+
                                      ((a :* conₜ T₁) :+ (b :* conₜ T₀))) := conₜ T₀) refl (u ix₃) (v ix₃))
--   y = b₁₁: Res(a,b₁₁,c₁₁) = 1 ⊕ −b, Res(d,b₁₁,c₁₀) = 0, Res(d,b₁₁,c₁₁) = 1
Wlam₄ u v (fsuc (fsuc (fsuc fzero))) =
  trans (lam₄-val u v (fsuc (fsuc (fsuc fzero))))
        (TritSolver.solve 2 (λ a b → ((((conₜ T₀ :+ :- (conₜ T₀)) :+ :- (conₜ T₀)) :+ :- b) :+
                                      ((a :* conₜ T₀) :+ (b :* conₜ T₁))) := conₜ T₀) refl (u ix₃) (v ix₃))

-- WR 对权重的加性与齐性
WR-add : ∀ p q u v y → WR (λ x z → (p x z) ⊕ (q x z)) u v y ≡ (WR p u v y) ⊕ (WR q u v y)
WR-add p q u v y =
  trans (sum₂-eval (λ x → sumFin (λ z → ((p x z) ⊕ (q x z)) ⊗ (Res u v x y z))))
        (trans (cong₂ _⊕_ (inner fzero) (inner (fsuc fzero)))
               (sym (trans (cong₂ _⊕_ (sum₂-eval prow) (sum₂-eval qrow))
                           (TritSolver.solve 4 (λ a b c d → (a :+ b) :+ (c :+ d) := (a :+ c) :+ (b :+ d)) refl
                              (prow fzero) (prow (fsuc fzero)) (qrow fzero) (qrow (fsuc fzero))))))
  where
  -- 两张权重各自在每一行上的和
  prow : Fin 2 → Trit
  prow x = sumFin (λ z → (p x z) ⊗ (Res u v x y z))
  qrow : Fin 2 → Trit
  qrow x = sumFin (λ z → (q x z) ⊗ (Res u v x y z))
  -- 一行之内: 先分配, 再分项求和
  inner : ∀ x → sumFin (λ z → ((p x z) ⊕ (q x z)) ⊗ (Res u v x y z)) ≡ (prow x) ⊕ (qrow x)
  inner x =
    trans (sumFin-cong (λ z → ⊗-distribʳ-⊕ (p x z) (q x z) (Res u v x y z)))
          (sumFin-add (λ z → (p x z) ⊗ (Res u v x y z)) (λ z → (q x z) ⊗ (Res u v x y z)))

WR-scale : ∀ c q u v y → WR (λ x z → c ⊗ (q x z)) u v y ≡ c ⊗ (WR q u v y)
WR-scale c q u v y =
  trans (sum₂-eval (λ x → sumFin (λ z → (c ⊗ (q x z)) ⊗ (Res u v x y z))))
        (trans (cong₂ _⊕_ (inner fzero) (inner (fsuc fzero)))
               (trans (TritSolver.solve 3 (λ d a b → (d :* a) :+ (d :* b) := d :* (a :+ b)) refl
                                 c (row-sum fzero) (row-sum (fsuc fzero)))
                      (cong (λ t → c ⊗ t) (sym (sum₂-eval row-sum)))))
  where
  row-sum : Fin 2 → Trit
  row-sum x = sumFin (λ z → (q x z) ⊗ (Res u v x y z))
  -- 一行之内: 结合后提出左因子
  inner : ∀ x → sumFin (λ z → (c ⊗ (q x z)) ⊗ (Res u v x y z)) ≡ c ⊗ (row-sum x)
  inner x =
    trans (sumFin-cong (λ z → ⊗-assoc c (q x z) (Res u v x y z)))
          (sumFin-scale c (λ z → (q x z) ⊗ (Res u v x y z)))

-- Fin (3^4) 上的编号 ↦ 四个系数
cv : Fin (3 ^ 4) → Fin 4 → Trit
cv κ j = toFun 4 κ j

-- ★ 把 Fin (3^4) 嵌入权重: 四个系数分别乘四个权重
emb : (Fin 4 → Trit) → (Fin 4 → Trit) → Fin (3 ^ 4) → (Fin 2 → Fin 4 → Trit)
emb u v κ x z =
  (((cv κ fzero) ⊗ (lam₁ x z)) ⊕ ((cv κ (fsuc fzero)) ⊗ (lam₂ x z))) ⊕
  (((cv κ (fsuc (fsuc fzero))) ⊗ (lam₃ u v x z)) ⊕ ((cv κ (fsuc (fsuc (fsuc fzero)))) ⊗ (lam₄ u v x z)))

-- 嵌入后的组合在 y 处的值
val : Fin (3 ^ 4) → Fin 4 → Trit
val κ fzero = negate (cv κ (fsuc (fsuc fzero)))
val κ (fsuc fzero) = negate (cv κ (fsuc (fsuc (fsuc fzero))))
val κ (fsuc (fsuc fzero)) = cv κ fzero
val κ (fsuc (fsuc (fsuc fzero))) = cv κ (fsuc fzero)

-- ★ W (emb κ) = val κ
Wemb : ∀ u v κ y → WR (emb u v κ) u v y ≡ val κ y
Wemb u v κ y = trans steps (cleanup y)
  where
  -- 两次加性
  s1 : WR (emb u v κ) u v y ≡ (WR (λ x z → ((cv κ fzero) ⊗ (lam₁ x z)) ⊕ ((cv κ (fsuc fzero)) ⊗ (lam₂ x z))) u v y) ⊕
                               (WR (λ x z → ((cv κ (fsuc (fsuc fzero))) ⊗ (lam₃ u v x z)) ⊕ ((cv κ (fsuc (fsuc (fsuc fzero)))) ⊗ (lam₄ u v x z))) u v y)
  s1 = WR-add (λ x z → ((cv κ fzero) ⊗ (lam₁ x z)) ⊕ ((cv κ (fsuc fzero)) ⊗ (lam₂ x z)))
          (λ x z → ((cv κ (fsuc (fsuc fzero))) ⊗ (lam₃ u v x z)) ⊕ ((cv κ (fsuc (fsuc (fsuc fzero)))) ⊗ (lam₄ u v x z))) u v y
  s2 : (WR (λ x z → ((cv κ fzero) ⊗ (lam₁ x z)) ⊕ ((cv κ (fsuc fzero)) ⊗ (lam₂ x z))) u v y) ≡
      (WR (λ x z → (cv κ fzero) ⊗ (lam₁ x z)) u v y) ⊕ (WR (λ x z → (cv κ (fsuc fzero)) ⊗ (lam₂ x z)) u v y)
  s2 = WR-add (λ x z → (cv κ fzero) ⊗ (lam₁ x z)) (λ x z → (cv κ (fsuc fzero)) ⊗ (lam₂ x z)) u v y
  s3 : (WR (λ x z → ((cv κ (fsuc (fsuc fzero))) ⊗ (lam₃ u v x z)) ⊕ ((cv κ (fsuc (fsuc (fsuc fzero)))) ⊗ (lam₄ u v x z))) u v y) ≡
      (WR (λ x z → (cv κ (fsuc (fsuc fzero))) ⊗ (lam₃ u v x z)) u v y) ⊕ (WR (λ x z → (cv κ (fsuc (fsuc (fsuc fzero)))) ⊗ (lam₄ u v x z)) u v y)
  s3 = WR-add (λ x z → (cv κ (fsuc (fsuc fzero))) ⊗ (lam₃ u v x z)) (λ x z → (cv κ (fsuc (fsuc (fsuc fzero)))) ⊗ (lam₄ u v x z)) u v y
  -- 四次齐性
  s4 : (WR (λ x z → (cv κ fzero) ⊗ (lam₁ x z)) u v y) ≡ (cv κ fzero) ⊗ (WR lam₁ u v y)
  s4 = WR-scale (cv κ fzero) lam₁ u v y
  s5 : (WR (λ x z → (cv κ (fsuc fzero)) ⊗ (lam₂ x z)) u v y) ≡ (cv κ (fsuc fzero)) ⊗ (WR lam₂ u v y)
  s5 = WR-scale (cv κ (fsuc fzero)) lam₂ u v y
  s6 : (WR (λ x z → (cv κ (fsuc (fsuc fzero))) ⊗ (lam₃ u v x z)) u v y) ≡ (cv κ (fsuc (fsuc fzero))) ⊗ (WR (lam₃ u v) u v y)
  s6 = WR-scale (cv κ (fsuc (fsuc fzero))) (lam₃ u v) u v y
  s7 : (WR (λ x z → (cv κ (fsuc (fsuc (fsuc fzero)))) ⊗ (lam₄ u v x z)) u v y) ≡ (cv κ (fsuc (fsuc (fsuc fzero)))) ⊗ (WR (lam₄ u v) u v y)
  s7 = WR-scale (cv κ (fsuc (fsuc (fsuc fzero)))) (lam₄ u v) u v y
  -- 四个权重的值
  steps : WR (emb u v κ) u v y ≡
          (((cv κ fzero) ⊗ (δc ix₂ y)) ⊕ ((cv κ (fsuc fzero)) ⊗ (δc ix₃ y))) ⊕
          (((cv κ (fsuc (fsuc fzero))) ⊗ (negate (δc fzero y))) ⊕ ((cv κ (fsuc (fsuc (fsuc fzero)))) ⊗ (negate (δc (fsuc fzero) y))))
  steps =
    trans s1
          (trans (cong₂ _⊕_ s2 s3)
                 (trans (cong₂ (λ p q → p ⊕ q) (cong₂ _⊕_ s4 s5) (cong₂ _⊕_ s6 s7))
                        (cong₂ (λ p q → p ⊕ q)
                               (cong₂ _⊕_ (cong (λ t → (cv κ fzero) ⊗ t) (Wlam₁ u v y))
                                          (cong (λ t → (cv κ (fsuc fzero)) ⊗ t) (Wlam₂ u v y)))
                               (cong₂ _⊕_ (cong (λ t → (cv κ (fsuc (fsuc fzero))) ⊗ t) (Wlam₃ u v y))
                                          (cong (λ t → (cv κ (fsuc (fsuc (fsuc fzero)))) ⊗ t) (Wlam₄ u v y))))))
  -- 代入 δ 的值后的环内整理
  cleanup : ∀ y →
            (((cv κ fzero) ⊗ (δc ix₂ y)) ⊕ ((cv κ (fsuc fzero)) ⊗ (δc ix₃ y))) ⊕
            (((cv κ (fsuc (fsuc fzero))) ⊗ (negate (δc fzero y))) ⊕ ((cv κ (fsuc (fsuc (fsuc fzero)))) ⊗ (negate (δc (fsuc fzero) y)))) ≡
            val κ y
  cleanup fzero =
    TritSolver.solve 4 (λ c0 c1 c2 c3 → ((c0 :* conₜ T₀) :+ (c1 :* conₜ T₀)) :+ ((c2 :* :- (conₜ T₁)) :+ (c3 :* :- (conₜ T₀)))
                                   := :- c2) refl (cv κ fzero) (cv κ (fsuc fzero)) (cv κ (fsuc (fsuc fzero))) (cv κ (fsuc (fsuc (fsuc fzero))))
  cleanup (fsuc fzero) =
    TritSolver.solve 4 (λ c0 c1 c2 c3 → ((c0 :* conₜ T₀) :+ (c1 :* conₜ T₀)) :+ ((c2 :* :- (conₜ T₀)) :+ (c3 :* :- (conₜ T₁)))
                                   := :- c3) refl (cv κ fzero) (cv κ (fsuc fzero)) (cv κ (fsuc (fsuc fzero))) (cv κ (fsuc (fsuc (fsuc fzero))))
  cleanup (fsuc (fsuc fzero)) =
    TritSolver.solve 4 (λ c0 c1 c2 c3 → ((c0 :* conₜ T₁) :+ (c1 :* conₜ T₀)) :+ ((c2 :* :- (conₜ T₀)) :+ (c3 :* :- (conₜ T₀)))
                                   := c0) refl (cv κ fzero) (cv κ (fsuc fzero)) (cv κ (fsuc (fsuc fzero))) (cv κ (fsuc (fsuc (fsuc fzero))))
  cleanup (fsuc (fsuc (fsuc fzero))) =
    TritSolver.solve 4 (λ c0 c1 c2 c3 → ((c0 :* conₜ T₀) :+ (c1 :* conₜ T₁)) :+ ((c2 :* :- (conₜ T₀)) :+ (c3 :* :- (conₜ T₀)))
                                   := c1) refl (cv κ fzero) (cv κ (fsuc fzero)) (cv κ (fsuc (fsuc fzero))) (cv κ (fsuc (fsuc (fsuc fzero))))

-- ★ emb 是单射: 四个点上的值分别读出四个系数
emb-inj : ∀ u v κ κ' → (∀ y → WR (emb u v κ) u v y ≡ WR (emb u v κ') u v y) → κ ≡ κ'
emb-inj u v κ κ' h =
  trans (sym (fromFun-toFun 4 κ))
        (trans (fromFun-cong 4 (toFun 4 κ) (toFun 4 κ') coef-eq) (fromFun-toFun 4 κ'))
  where
  -- 各点的值相等
  v-eq : ∀ y → val κ y ≡ val κ' y
  v-eq y = trans (sym (Wemb u v κ y)) (trans (h y) (Wemb u v κ' y))
  e0 : cv κ fzero ≡ cv κ' fzero
  e0 = v-eq (fsuc (fsuc fzero))
  e1 : cv κ (fsuc fzero) ≡ cv κ' (fsuc fzero)
  e1 = v-eq (fsuc (fsuc (fsuc fzero)))
  e2 : cv κ (fsuc (fsuc fzero)) ≡ cv κ' (fsuc (fsuc fzero))
  e2 = neg-inj _ _ (v-eq fzero)
  e3 : cv κ (fsuc (fsuc (fsuc fzero))) ≡ cv κ' (fsuc (fsuc (fsuc fzero)))
  e3 = neg-inj _ _ (v-eq (fsuc fzero))
  coef-eq : ∀ j → (toFun 4 κ) j ≡ (toFun 4 κ') j
  coef-eq = all₄ e0 e1 e2 e3

-- 把第二因子转到首位后的分解上的切片张成
module ResSpan (u v : Fin 4 → Trit) (r : ℕ) (ρ : RankLE (Fin 2) (Fin 4) (Fin 4) (Res u v) r) where

  ρs : RankLE (Fin 4) (Fin 2) (Fin 4) (λ y x z → Res u v x y z) r
  ρs = rank-swap (Res u v) ρ

  open SpanGen (Fin 4) (Fin 2) (Fin 4) (λ y x z → Res u v x y z) r ρs 2 4 (λ j → j) (λ k → k) public

  -- SpanGen 的 W 就是 WR（按定义成立）
  W≡WR : ∀ q y → W q y ≡ WR q u v y
  W≡WR q y = refl

-- ★★ 残差的切片下界: Res u v 有 r 项分解 ⟹ 4 ≤ r
res-flatten : ∀ r (u v : Fin 4 → Trit) → RankLE (Fin 2) (Fin 4) (Fin 4) (Res u v) r → 4 ≤ r
res-flatten r u v ρ = bound-4 inj
  where
  module RS = ResSpan u v r ρ
  -- 单射: 由 W ≡ WR、Wemb 与 emb-inj
  inj : ∀ κ κ' → (∀ y → RS.W (emb u v κ) y ≡ RS.W (emb u v κ') y) → κ ≡ κ'
  inj κ κ' h = emb-inj u v κ κ' (λ y → trans (sym (RS.W≡WR (emb u v κ) y)) (trans (h y) (RS.W≡WR (emb u v κ') y)))
  bound-4 : (∀ κ κ' → (∀ y → RS.W (emb u v κ) y ≡ RS.W (emb u v κ') y) → κ ≡ κ') → 4 ≤ r
  bound-4 i = RS.bound 4 (emb u v) i

--------------------------------------------------------------------------------
-- §4 超平面分类: 80 个非零泛函各一个「K 型子空间」的见证
--------------------------------------------------------------------------------

-- 2×2 矩阵的逆: adj / det（det = 0 时无定义, 取全零; 见证的每行都会核对两条逆恒等式）
inv2 : Mat2 Trit → Mat2 Trit
inv2 m =
  let d = TritInv ((m00 m ⊗ m11 m) ⊕ negate (m01 m ⊗ m10 m)) in
  mkMat2 (d ⊗ m11 m) (negate (d ⊗ m01 m)) (negate (d ⊗ m10 m)) (d ⊗ m00 m)

transpose : Mat2 Trit → Mat2 Trit
transpose m = mkMat2 (m00 m) (m10 m) (m01 m) (m11 m)

-- 矩阵元素（行, 列）
entry : Mat2 Trit → Fin 2 → Fin 2 → Trit
entry m fzero fzero = m00 m
entry m fzero (fsuc fzero) = m01 m
entry m (fsuc fzero) fzero = m10 m
entry m (fsuc fzero) (fsuc fzero) = m11 m

-- Fin 4 下标的行与列
rowOf : Fin 4 → Fin 2
rowOf fzero = fzero
rowOf (fsuc fzero) = fzero
rowOf (fsuc (fsuc fzero)) = fsuc fzero
rowOf (fsuc (fsuc (fsuc fzero))) = fsuc fzero

colOf : Fin 4 → Fin 2
colOf fzero = fzero
colOf (fsuc fzero) = fsuc fzero
colOf (fsuc (fsuc fzero)) = fzero
colOf (fsuc (fsuc (fsuc fzero))) = fsuc fzero

-- 矩阵在 Fin 4 上的坐标（行主序）
coords : Mat2 Trit → Fin 4 → Trit
coords m fzero = m00 m
coords m (fsuc fzero) = m01 m
coords m (fsuc (fsuc fzero)) = m10 m
coords m (fsuc (fsuc (fsuc fzero))) = m11 m

mul2 : Mat2 Trit → Mat2 Trit → Mat2 Trit
mul2 = mulMat2 _⊕_ _⊗_

-- K 的基: J = [[0,1],[-1,0]], E₂₂
kappa : Fin 2 → Mat2 Trit
kappa fzero = mkMat2 T₀ T₁ T₂ T₀
kappa (fsuc fzero) = mkMat2 T₀ T₀ T₀ T₁

-- 只在「同列」处保留的系数
same : Fin 4 → Fin 4 → Trit → Trit
same k w t with colOf k ≟ colOf w
... | yes _ = t
... | no _ = T₀

-- 见证的数据
record Wit : Set where
  field
    row : Fin 2 → Fin 4 → Trit
    matA comA matB comB : Fin 4 → Fin 4 → Trit

-- 由一对可逆矩阵 (P, Q) 算出见证的数据:
--   W_j = P⁻¹ κ_j Q 的坐标就是 row j;
--   matA k w = (Q⁻¹)[k行][w行]·[同列],  comA w k = Q[w行][k行]·[同列]
--   matB k w = P[w行][k行]·[同列],      comB w k = (P⁻ᵀ)[w行][k行]·[同列]
witOf : Mat2 Trit → Mat2 Trit → Wit
witOf P Q = record
  { row = λ j → coords (mul2 (mul2 (inv2 P) (kappa j)) Q)
  ; matA = λ k w → same k w (entry (inv2 Q) (rowOf k) (rowOf w))
  ; comA = λ w k → same k w (entry Q (rowOf w) (rowOf k))
  ; matB = λ k w → same k w (entry P (rowOf w) (rowOf k))
  ; comB = λ w k → same k w (entry (transpose (inv2 P)) (rowOf w) (rowOf k)) }

-- 泛函的四个系数
l4 : Trit → Trit → Trit → Trit → Fin 4 → Trit
l4 l0 l1 l2 l3 fzero = l0
l4 l0 l1 l2 l3 (fsuc fzero) = l1
l4 l0 l1 l2 l3 (fsuc (fsuc fzero)) = l2
l4 l0 l1 l2 l3 (fsuc (fsuc (fsuc fzero))) = l3

-- ★ 见证要满足的四条恒等式
--   ker:   ℓ 在 W 上恒零;
--   inv-A, inv-B: cA·A = I 与 cB·B = I（两组换元矩阵互逆）;
--   move:  T(W_j, y, z) = Σ_{k'} B k' z ⊗ Σ_k A k y ⊗ TK j k k', 即 T(PXQ⁻¹, Y, Z) = T(X, Q⁻¹Y, PᵀZ)。
record Good (w : Wit) (l0 l1 l2 l3 : Trit) : Set where
  field
    ker   : ∀ j → sumFin (λ p → (Wit.row w j p) ⊗ (l4 l0 l1 l2 l3 p)) ≡ T₀
    inv-A : ∀ k k₀ → sumFin (λ w' → (Wit.comA w w' k₀) ⊗ (Wit.matA w k w')) ≡ δc k k₀
    inv-B : ∀ k k₀ → sumFin (λ w' → (Wit.comB w w' k₀) ⊗ (Wit.matB w k w')) ≡ δc k k₀
    move  : ∀ j y z → sumFin (λ p → (Wit.row w j p) ⊗ (T4 p y z)) ≡
            sumFin (λ k' → (Wit.matB w k' z) ⊗ sumFin (λ k → (Wit.matA w k y) ⊗ (TK j k k')))

mkGood : ∀ {w : Wit} {l0 l1 l2 l3 : Trit} →
  (∀ j → sumFin (λ p → (Wit.row w j p) ⊗ (l4 l0 l1 l2 l3 p)) ≡ T₀) →
  (∀ k k₀ → sumFin (λ w' → (Wit.comA w w' k₀) ⊗ (Wit.matA w k w')) ≡ δc k k₀) →
  (∀ k k₀ → sumFin (λ w' → (Wit.comB w w' k₀) ⊗ (Wit.matB w k w')) ≡ δc k k₀) →
  (∀ j y z → sumFin (λ p → (Wit.row w j p) ⊗ (T4 p y z)) ≡
   sumFin (λ k' → (Wit.matB w k' z) ⊗ sumFin (λ k → (Wit.matA w k y) ⊗ (TK j k k')))) →
  Good w l0 l1 l2 l3
mkGood h1 h2 h3 h4 = record { ker = h1 ; inv-A = h2 ; inv-B = h3 ; move = h4 }

-- 判定: 四条恒等式都是闭的 Fin 上的逐点等式
good? : (w : Wit) (l0 l1 l2 l3 : Trit) → Dec (Good w l0 l1 l2 l3)
good? w l0 l1 l2 l3
  with dec₂ (λ j → sumFin (λ p → (Wit.row w j p) ⊗ (l4 l0 l1 l2 l3 p)) ≟ₜ T₀)
       | dec₄ (λ k → dec₄ (λ k₀ → sumFin (λ w' → (Wit.comA w w' k₀) ⊗ (Wit.matA w k w')) ≟ₜ δc k k₀))
       | dec₄ (λ k → dec₄ (λ k₀ → sumFin (λ w' → (Wit.comB w w' k₀) ⊗ (Wit.matB w k w')) ≟ₜ δc k k₀))
       | dec₂ (λ j → dec₄ (λ y → dec₄ (λ z →
           sumFin (λ p → (Wit.row w j p) ⊗ (T4 p y z)) ≟ₜ
           sumFin (λ k' → (Wit.matB w k' z) ⊗ sumFin (λ k → (Wit.matA w k y) ⊗ (TK j k k'))))))
... | yes h1 | yes h2 | yes h3 | yes h4 = yes (mkGood h1 h2 h3 h4)
... | no ¬h | _ | _ | _ = no (λ g → ¬h (Good.ker g))
... | yes _ | no ¬h | _ | _ = no (λ g → ¬h (Good.inv-A g))
... | yes _ | yes _ | no ¬h | _ = no (λ g → ¬h (Good.inv-B g))
... | yes _ | yes _ | yes _ | no ¬h = no (λ g → ¬h (Good.move g))

-- 智能构造: 见证的数据 + 「四条恒等式经计算成立」
--   表里的每一行都走这里, 最后一个实参写 tt: 它的类型是 True (good? …), 只有四条恒等式都成立时
--   才归约成 ⊤; 哪一行不成立, 那里就是 ⊥, 内核当场拒绝（负控制见 PROVEN §二十二）。
mkW : (P Q : Mat2 Trit) (l0 l1 l2 l3 : Trit) → True (good? (witOf P Q) l0 l1 l2 l3) →
      Σ Wit (λ w → Good w l0 l1 l2 l3)
mkW P Q l0 l1 l2 l3 pf = witOf P Q , toWitness {a? = good? (witOf P Q) l0 l1 l2 l3} pf

-- 非零: 四个系数里至少一个不为零
NZ : Trit → Trit → Trit → Trit → Set
NZ l0 l1 l2 l3 = (l0 ≢ T₀) ⊎ ((l1 ≢ T₀) ⊎ ((l2 ≢ T₀) ⊎ (l3 ≢ T₀)))

nz-elim : NZ T₀ T₀ T₀ T₀ → ⊥
nz-elim (inj₁ h) = h refl
nz-elim (inj₂ (inj₁ h)) = h refl
nz-elim (inj₂ (inj₂ (inj₁ h))) = h refl
nz-elim (inj₂ (inj₂ (inj₂ h))) = h refl

-- ★★ 每个非零泛函 ℓ 都有一个 K 型子空间 W = span{P⁻¹κ_j Q} 的见证
--   见证由一对可逆矩阵 (P, Q) 给出; 全部 80 个列在下面。这里**不做**抽象的分类证明:
--   每一行是一个具体的 (P, Q), 四条恒等式由内核归约核对。
--   （非零泛函在 (P, Q) 下分两个轨道的说法是 [直觉·未验证], 见头注; 表不依赖它。）
hyper-wit : (l0 l1 l2 l3 : Trit) → NZ l0 l1 l2 l3 → Σ Wit (λ w → Good w l0 l1 l2 l3)
-- BEGIN hk2-table —— 由 engineering/oracle_tensor_rank_gf3.py --hk2-table 生成, 勿手改
hyper-wit T₀ T₀ T₀ T₁ _ = mkW (mkMat2 T₀ T₁ T₁ T₀) (mkMat2 T₀ T₁ T₁ T₀) T₀ T₀ T₀ T₁ tt
hyper-wit T₀ T₀ T₀ T₂ _ = mkW (mkMat2 T₀ T₁ T₁ T₀) (mkMat2 T₀ T₁ T₁ T₀) T₀ T₀ T₀ T₂ tt
hyper-wit T₀ T₀ T₁ T₀ _ = mkW (mkMat2 T₀ T₁ T₁ T₀) (mkMat2 T₁ T₀ T₀ T₁) T₀ T₀ T₁ T₀ tt
hyper-wit T₀ T₀ T₁ T₁ _ = mkW (mkMat2 T₀ T₁ T₁ T₀) (mkMat2 T₁ T₀ T₁ T₂) T₀ T₀ T₁ T₁ tt
hyper-wit T₀ T₀ T₁ T₂ _ = mkW (mkMat2 T₀ T₁ T₁ T₀) (mkMat2 T₁ T₀ T₂ T₂) T₀ T₀ T₁ T₂ tt
hyper-wit T₀ T₀ T₂ T₀ _ = mkW (mkMat2 T₀ T₁ T₁ T₀) (mkMat2 T₁ T₀ T₀ T₁) T₀ T₀ T₂ T₀ tt
hyper-wit T₀ T₀ T₂ T₁ _ = mkW (mkMat2 T₀ T₁ T₁ T₀) (mkMat2 T₁ T₀ T₂ T₂) T₀ T₀ T₂ T₁ tt
hyper-wit T₀ T₀ T₂ T₂ _ = mkW (mkMat2 T₀ T₁ T₁ T₀) (mkMat2 T₁ T₀ T₁ T₂) T₀ T₀ T₂ T₂ tt
hyper-wit T₀ T₁ T₀ T₀ _ = mkW (mkMat2 T₁ T₀ T₀ T₁) (mkMat2 T₀ T₁ T₁ T₀) T₀ T₁ T₀ T₀ tt
hyper-wit T₀ T₁ T₀ T₁ _ = mkW (mkMat2 T₁ T₁ T₀ T₂) (mkMat2 T₀ T₁ T₁ T₀) T₀ T₁ T₀ T₁ tt
hyper-wit T₀ T₁ T₀ T₂ _ = mkW (mkMat2 T₁ T₂ T₀ T₂) (mkMat2 T₀ T₁ T₁ T₀) T₀ T₁ T₀ T₂ tt
hyper-wit T₀ T₁ T₁ T₀ _ = mkW (mkMat2 T₀ T₁ T₁ T₀) (mkMat2 T₀ T₁ T₁ T₀) T₀ T₁ T₁ T₀ tt
hyper-wit T₀ T₁ T₁ T₁ _ = mkW (mkMat2 T₀ T₁ T₁ T₀) (mkMat2 T₀ T₁ T₁ T₀) T₀ T₁ T₁ T₁ tt
hyper-wit T₀ T₁ T₁ T₂ _ = mkW (mkMat2 T₀ T₁ T₁ T₀) (mkMat2 T₀ T₁ T₁ T₀) T₀ T₁ T₁ T₂ tt
hyper-wit T₀ T₁ T₂ T₀ _ = mkW (mkMat2 T₁ T₀ T₀ T₁) (mkMat2 T₁ T₀ T₀ T₂) T₀ T₁ T₂ T₀ tt
hyper-wit T₀ T₁ T₂ T₁ _ = mkW (mkMat2 T₁ T₀ T₀ T₁) (mkMat2 T₁ T₀ T₂ T₂) T₀ T₁ T₂ T₁ tt
hyper-wit T₀ T₁ T₂ T₂ _ = mkW (mkMat2 T₁ T₀ T₀ T₁) (mkMat2 T₁ T₀ T₁ T₂) T₀ T₁ T₂ T₂ tt
hyper-wit T₀ T₂ T₀ T₀ _ = mkW (mkMat2 T₁ T₀ T₀ T₁) (mkMat2 T₀ T₁ T₁ T₀) T₀ T₂ T₀ T₀ tt
hyper-wit T₀ T₂ T₀ T₁ _ = mkW (mkMat2 T₁ T₂ T₀ T₂) (mkMat2 T₀ T₁ T₁ T₀) T₀ T₂ T₀ T₁ tt
hyper-wit T₀ T₂ T₀ T₂ _ = mkW (mkMat2 T₁ T₁ T₀ T₂) (mkMat2 T₀ T₁ T₁ T₀) T₀ T₂ T₀ T₂ tt
hyper-wit T₀ T₂ T₁ T₀ _ = mkW (mkMat2 T₁ T₀ T₀ T₁) (mkMat2 T₁ T₀ T₀ T₂) T₀ T₂ T₁ T₀ tt
hyper-wit T₀ T₂ T₁ T₁ _ = mkW (mkMat2 T₁ T₀ T₀ T₁) (mkMat2 T₁ T₀ T₁ T₂) T₀ T₂ T₁ T₁ tt
hyper-wit T₀ T₂ T₁ T₂ _ = mkW (mkMat2 T₁ T₀ T₀ T₁) (mkMat2 T₁ T₀ T₂ T₂) T₀ T₂ T₁ T₂ tt
hyper-wit T₀ T₂ T₂ T₀ _ = mkW (mkMat2 T₀ T₁ T₁ T₀) (mkMat2 T₀ T₁ T₁ T₀) T₀ T₂ T₂ T₀ tt
hyper-wit T₀ T₂ T₂ T₁ _ = mkW (mkMat2 T₀ T₁ T₁ T₀) (mkMat2 T₀ T₁ T₁ T₀) T₀ T₂ T₂ T₁ tt
hyper-wit T₀ T₂ T₂ T₂ _ = mkW (mkMat2 T₀ T₁ T₁ T₀) (mkMat2 T₀ T₁ T₁ T₀) T₀ T₂ T₂ T₂ tt
hyper-wit T₁ T₀ T₀ T₀ _ = mkW (mkMat2 T₁ T₀ T₀ T₁) (mkMat2 T₁ T₀ T₀ T₂) T₁ T₀ T₀ T₀ tt
hyper-wit T₁ T₀ T₀ T₁ _ = mkW (mkMat2 T₀ T₁ T₁ T₀) (mkMat2 T₁ T₀ T₀ T₁) T₁ T₀ T₀ T₁ tt
hyper-wit T₁ T₀ T₀ T₂ _ = mkW (mkMat2 T₀ T₁ T₁ T₀) (mkMat2 T₁ T₀ T₀ T₂) T₁ T₀ T₀ T₂ tt
hyper-wit T₁ T₀ T₁ T₀ _ = mkW (mkMat2 T₁ T₁ T₀ T₂) (mkMat2 T₁ T₀ T₀ T₁) T₁ T₀ T₁ T₀ tt
hyper-wit T₁ T₀ T₁ T₁ _ = mkW (mkMat2 T₀ T₁ T₁ T₀) (mkMat2 T₁ T₀ T₀ T₁) T₁ T₀ T₁ T₁ tt
hyper-wit T₁ T₀ T₁ T₂ _ = mkW (mkMat2 T₁ T₁ T₀ T₂) (mkMat2 T₀ T₁ T₁ T₀) T₁ T₀ T₁ T₂ tt
hyper-wit T₁ T₀ T₂ T₀ _ = mkW (mkMat2 T₁ T₂ T₀ T₂) (mkMat2 T₁ T₀ T₀ T₁) T₁ T₀ T₂ T₀ tt
hyper-wit T₁ T₀ T₂ T₁ _ = mkW (mkMat2 T₀ T₁ T₁ T₀) (mkMat2 T₁ T₀ T₀ T₁) T₁ T₀ T₂ T₁ tt
hyper-wit T₁ T₀ T₂ T₂ _ = mkW (mkMat2 T₁ T₂ T₀ T₂) (mkMat2 T₀ T₁ T₁ T₀) T₁ T₀ T₂ T₂ tt
hyper-wit T₁ T₁ T₀ T₀ _ = mkW (mkMat2 T₁ T₀ T₀ T₁) (mkMat2 T₁ T₀ T₁ T₂) T₁ T₁ T₀ T₀ tt
hyper-wit T₁ T₁ T₀ T₁ _ = mkW (mkMat2 T₁ T₀ T₀ T₁) (mkMat2 T₀ T₁ T₁ T₀) T₁ T₁ T₀ T₁ tt
hyper-wit T₁ T₁ T₀ T₂ _ = mkW (mkMat2 T₀ T₁ T₁ T₀) (mkMat2 T₁ T₀ T₁ T₂) T₁ T₁ T₀ T₂ tt
hyper-wit T₁ T₁ T₁ T₀ _ = mkW (mkMat2 T₀ T₁ T₁ T₀) (mkMat2 T₁ T₀ T₁ T₂) T₁ T₁ T₁ T₀ tt
hyper-wit T₁ T₁ T₁ T₁ _ = mkW (mkMat2 T₁ T₁ T₀ T₂) (mkMat2 T₁ T₀ T₁ T₂) T₁ T₁ T₁ T₁ tt
hyper-wit T₁ T₁ T₁ T₂ _ = mkW (mkMat2 T₁ T₀ T₀ T₁) (mkMat2 T₁ T₀ T₂ T₂) T₁ T₁ T₁ T₂ tt
hyper-wit T₁ T₁ T₂ T₀ _ = mkW (mkMat2 T₁ T₀ T₀ T₁) (mkMat2 T₁ T₀ T₀ T₂) T₁ T₁ T₂ T₀ tt
hyper-wit T₁ T₁ T₂ T₁ _ = mkW (mkMat2 T₀ T₁ T₁ T₀) (mkMat2 T₁ T₀ T₁ T₂) T₁ T₁ T₂ T₁ tt
hyper-wit T₁ T₁ T₂ T₂ _ = mkW (mkMat2 T₁ T₂ T₀ T₂) (mkMat2 T₁ T₀ T₁ T₂) T₁ T₁ T₂ T₂ tt
hyper-wit T₁ T₂ T₀ T₀ _ = mkW (mkMat2 T₁ T₀ T₀ T₁) (mkMat2 T₁ T₀ T₂ T₂) T₁ T₂ T₀ T₀ tt
hyper-wit T₁ T₂ T₀ T₁ _ = mkW (mkMat2 T₁ T₀ T₀ T₁) (mkMat2 T₀ T₁ T₁ T₀) T₁ T₂ T₀ T₁ tt
hyper-wit T₁ T₂ T₀ T₂ _ = mkW (mkMat2 T₀ T₁ T₁ T₀) (mkMat2 T₁ T₀ T₂ T₂) T₁ T₂ T₀ T₂ tt
hyper-wit T₁ T₂ T₁ T₀ _ = mkW (mkMat2 T₁ T₀ T₀ T₁) (mkMat2 T₁ T₀ T₀ T₂) T₁ T₂ T₁ T₀ tt
hyper-wit T₁ T₂ T₁ T₁ _ = mkW (mkMat2 T₀ T₁ T₁ T₀) (mkMat2 T₁ T₀ T₂ T₂) T₁ T₂ T₁ T₁ tt
hyper-wit T₁ T₂ T₁ T₂ _ = mkW (mkMat2 T₁ T₁ T₀ T₂) (mkMat2 T₁ T₀ T₂ T₂) T₁ T₂ T₁ T₂ tt
hyper-wit T₁ T₂ T₂ T₀ _ = mkW (mkMat2 T₀ T₁ T₁ T₀) (mkMat2 T₁ T₀ T₂ T₂) T₁ T₂ T₂ T₀ tt
hyper-wit T₁ T₂ T₂ T₁ _ = mkW (mkMat2 T₁ T₂ T₀ T₂) (mkMat2 T₁ T₀ T₂ T₂) T₁ T₂ T₂ T₁ tt
hyper-wit T₁ T₂ T₂ T₂ _ = mkW (mkMat2 T₁ T₀ T₀ T₁) (mkMat2 T₁ T₀ T₁ T₂) T₁ T₂ T₂ T₂ tt
hyper-wit T₂ T₀ T₀ T₀ _ = mkW (mkMat2 T₁ T₀ T₀ T₁) (mkMat2 T₁ T₀ T₀ T₂) T₂ T₀ T₀ T₀ tt
hyper-wit T₂ T₀ T₀ T₁ _ = mkW (mkMat2 T₀ T₁ T₁ T₀) (mkMat2 T₁ T₀ T₀ T₂) T₂ T₀ T₀ T₁ tt
hyper-wit T₂ T₀ T₀ T₂ _ = mkW (mkMat2 T₀ T₁ T₁ T₀) (mkMat2 T₁ T₀ T₀ T₁) T₂ T₀ T₀ T₂ tt
hyper-wit T₂ T₀ T₁ T₀ _ = mkW (mkMat2 T₁ T₂ T₀ T₂) (mkMat2 T₁ T₀ T₀ T₁) T₂ T₀ T₁ T₀ tt
hyper-wit T₂ T₀ T₁ T₁ _ = mkW (mkMat2 T₁ T₂ T₀ T₂) (mkMat2 T₀ T₁ T₁ T₀) T₂ T₀ T₁ T₁ tt
hyper-wit T₂ T₀ T₁ T₂ _ = mkW (mkMat2 T₀ T₁ T₁ T₀) (mkMat2 T₁ T₀ T₀ T₁) T₂ T₀ T₁ T₂ tt
hyper-wit T₂ T₀ T₂ T₀ _ = mkW (mkMat2 T₁ T₁ T₀ T₂) (mkMat2 T₁ T₀ T₀ T₁) T₂ T₀ T₂ T₀ tt
hyper-wit T₂ T₀ T₂ T₁ _ = mkW (mkMat2 T₁ T₁ T₀ T₂) (mkMat2 T₀ T₁ T₁ T₀) T₂ T₀ T₂ T₁ tt
hyper-wit T₂ T₀ T₂ T₂ _ = mkW (mkMat2 T₀ T₁ T₁ T₀) (mkMat2 T₁ T₀ T₀ T₁) T₂ T₀ T₂ T₂ tt
hyper-wit T₂ T₁ T₀ T₀ _ = mkW (mkMat2 T₁ T₀ T₀ T₁) (mkMat2 T₁ T₀ T₂ T₂) T₂ T₁ T₀ T₀ tt
hyper-wit T₂ T₁ T₀ T₁ _ = mkW (mkMat2 T₀ T₁ T₁ T₀) (mkMat2 T₁ T₀ T₂ T₂) T₂ T₁ T₀ T₁ tt
hyper-wit T₂ T₁ T₀ T₂ _ = mkW (mkMat2 T₁ T₀ T₀ T₁) (mkMat2 T₀ T₁ T₁ T₀) T₂ T₁ T₀ T₂ tt
hyper-wit T₂ T₁ T₁ T₀ _ = mkW (mkMat2 T₀ T₁ T₁ T₀) (mkMat2 T₁ T₀ T₂ T₂) T₂ T₁ T₁ T₀ tt
hyper-wit T₂ T₁ T₁ T₁ _ = mkW (mkMat2 T₁ T₀ T₀ T₁) (mkMat2 T₁ T₀ T₁ T₂) T₂ T₁ T₁ T₁ tt
hyper-wit T₂ T₁ T₁ T₂ _ = mkW (mkMat2 T₁ T₂ T₀ T₂) (mkMat2 T₁ T₀ T₂ T₂) T₂ T₁ T₁ T₂ tt
hyper-wit T₂ T₁ T₂ T₀ _ = mkW (mkMat2 T₁ T₀ T₀ T₁) (mkMat2 T₁ T₀ T₀ T₂) T₂ T₁ T₂ T₀ tt
hyper-wit T₂ T₁ T₂ T₁ _ = mkW (mkMat2 T₁ T₁ T₀ T₂) (mkMat2 T₁ T₀ T₂ T₂) T₂ T₁ T₂ T₁ tt
hyper-wit T₂ T₁ T₂ T₂ _ = mkW (mkMat2 T₀ T₁ T₁ T₀) (mkMat2 T₁ T₀ T₂ T₂) T₂ T₁ T₂ T₂ tt
hyper-wit T₂ T₂ T₀ T₀ _ = mkW (mkMat2 T₁ T₀ T₀ T₁) (mkMat2 T₁ T₀ T₁ T₂) T₂ T₂ T₀ T₀ tt
hyper-wit T₂ T₂ T₀ T₁ _ = mkW (mkMat2 T₀ T₁ T₁ T₀) (mkMat2 T₁ T₀ T₁ T₂) T₂ T₂ T₀ T₁ tt
hyper-wit T₂ T₂ T₀ T₂ _ = mkW (mkMat2 T₁ T₀ T₀ T₁) (mkMat2 T₀ T₁ T₁ T₀) T₂ T₂ T₀ T₂ tt
hyper-wit T₂ T₂ T₁ T₀ _ = mkW (mkMat2 T₁ T₀ T₀ T₁) (mkMat2 T₁ T₀ T₀ T₂) T₂ T₂ T₁ T₀ tt
hyper-wit T₂ T₂ T₁ T₁ _ = mkW (mkMat2 T₁ T₂ T₀ T₂) (mkMat2 T₁ T₀ T₁ T₂) T₂ T₂ T₁ T₁ tt
hyper-wit T₂ T₂ T₁ T₂ _ = mkW (mkMat2 T₀ T₁ T₁ T₀) (mkMat2 T₁ T₀ T₁ T₂) T₂ T₂ T₁ T₂ tt
hyper-wit T₂ T₂ T₂ T₀ _ = mkW (mkMat2 T₀ T₁ T₁ T₀) (mkMat2 T₁ T₀ T₁ T₂) T₂ T₂ T₂ T₀ tt
hyper-wit T₂ T₂ T₂ T₁ _ = mkW (mkMat2 T₁ T₀ T₀ T₁) (mkMat2 T₁ T₀ T₂ T₂) T₂ T₂ T₂ T₁ tt
hyper-wit T₂ T₂ T₂ T₂ _ = mkW (mkMat2 T₁ T₁ T₀ T₂) (mkMat2 T₁ T₀ T₁ T₂) T₂ T₂ T₂ T₂ tt
hyper-wit T₀ T₀ T₀ T₀ h = ⊥-elim (nz-elim h)
-- END hk2-table

--------------------------------------------------------------------------------
-- §5 K 上的下界（forced product）
--------------------------------------------------------------------------------

-- 4 ≤ pred (pred r) ⟹ 6 ≤ r
-- pred (pred r) = r ∸ 2: r ≤ 5 时它 < 4, 与 4 ≤ pred (pred r) 矛盾; r ≥ 6 时 6 ≤ r
arith : ∀ r → 4 ≤ pred (pred r) → 6 ≤ r
arith zero h = ⊥-elim (<⇒≱ (s≤s z≤n) h)
arith (suc zero) h = ⊥-elim (<⇒≱ (s≤s z≤n) h)
arith (suc (suc zero)) h = ⊥-elim (<⇒≱ (s≤s z≤n) h)
arith (suc (suc (suc zero))) h = ⊥-elim (<⇒≱ (s≤s (s≤s z≤n)) h)
arith (suc (suc (suc (suc zero)))) h = ⊥-elim (<⇒≱ (s≤s (s≤s (s≤s z≤n))) h)
arith (suc (suc (suc (suc (suc zero))))) h = ⊥-elim (<⇒≱ (s≤s ≤-refl) h)
arith (suc (suc (suc (suc (suc (suc r)))))) h = m≤m+n 6 r

-- ★ K 上的张量至少要 6 项: 两次切片规范化（c₀₀ 与 c₀₁ 两个单积切片）, 余项的切片下界是 4
K-bound : ∀ r → RankLE (Fin 2) (Fin 4) (Fin 4) TK r → 6 ≤ r
K-bound r ρ = arith r (res-flatten (pred (pred r)) u v ρRes)
  where
  -- 第一次规范化: c₀₀ 切片是 f ⊗ g, 在 (a, b₁₀) 处取 T₁
  nz₀ : (fK fzero) ⊗ (gK ix₂) ≢ T₀
  nz₀ = λ ()

  n1 = slice-normalize TK ix₀ fK gK TK-slice₀ fzero ix₂ nz₀ ρ

  w₀ : Fin 4 → Trit
  w₀ = proj₁ n1

  -- 第一次的余项
  R₁ : Fin 2 → Fin 4 → Fin 4 → Trit
  R₁ x y z = (TK x y z) ⊕ negate ((fK x) ⊗ ((gK y) ⊗ (w₀ z)))

  ρ₁ : RankLE (Fin 2) (Fin 4) (Fin 4) R₁ (pred r)
  ρ₁ = proj₂ (proj₂ n1)

  -- 第二次规范化: 余项的 c₀₁ 切片是 f ⊗ g'', 其中 g'' = g' ⊕ −(w₀(c₀₁) ⊗ g)
  g'' : Fin 4 → Trit
  g'' y = (gK' y) ⊕ negate ((w₀ ix₁) ⊗ (gK y))

  R₁-slice : ∀ x y → R₁ x y ix₁ ≡ (fK x) ⊗ (g'' y)
  R₁-slice x y =
    trans (cong (λ t → t ⊕ negate ((fK x) ⊗ ((gK y) ⊗ (w₀ ix₁)))) (TK-slice₁ x y))
          (TritSolver.solve 4 (λ f g g' w → (f :* g') :+ :- (f :* (g :* w)) := f :* (g' :+ :- (w :* g))) refl
             (fK x) (gK y) (gK' y) (w₀ ix₁))

  -- g'' 在 b₁₁ 处: g' = 1, g = 0 ⟹ g'' = 1
  lem₁ : (fK fzero) ⊗ (g'' ix₃) ≡ T₁
  lem₁ = TritSolver.solve 1 (λ w → (conₜ T₁) :* ((conₜ T₁) :+ :- (w :* (conₜ T₀))) := conₜ T₁) refl (w₀ ix₁)

  nz₁ : (fK fzero) ⊗ (g'' ix₃) ≢ T₀
  nz₁ h = T₀≢T₁ (sym (trans (sym lem₁) h))

  n2 = slice-normalize R₁ ix₁ fK g'' R₁-slice fzero ix₃ nz₁ ρ₁

  w₁ : Fin 4 → Trit
  w₁ = proj₁ n2

  ρ₂ = proj₂ (proj₂ n2)

  -- 余项就是 Res u v: u = w₀ ⊕ −(w₀(c₀₁) ⊗ w₁),  v = w₁
  u : Fin 4 → Trit
  u z = (w₀ z) ⊕ negate ((w₀ ix₁) ⊗ (w₁ z))

  v : Fin 4 → Trit
  v = w₁

  R₂≡Res : ∀ x y z → (R₁ x y z ⊕ negate ((fK x) ⊗ ((g'' y) ⊗ (w₁ z)))) ≡ Res u v x y z
  R₂≡Res x y z =
    TritSolver.solve 7
      (λ t f g g' w0 w1 w0c →
         (t :+ :- (f :* (g :* w0))) :+ :- (f :* ((g' :+ :- (w0c :* g)) :* w1)) :=
         (t :+ :- (f :* (g :* (w0 :+ :- (w0c :* w1))))) :+ :- (f :* (g' :* w1)))
      refl (TK x y z) (fK x) (gK y) (gK' y) (w₀ z) (w₁ z) (w₀ ix₁)

  ρRes : RankLE (Fin 2) (Fin 4) (Fin 4) (Res u v) (pred (pred r))
  ρRes = rank-cong R₂≡Res ρ₂

-- ★ 把 W 上的分解搬到 K 上: 先换第三因子, 再换第二因子（两次线性换元）
transfer : (w : Wit) (l0 l1 l2 l3 : Trit) → Good w l0 l1 l2 l3 → ∀ r →
  RankLE (Fin 2) (Fin 4) (Fin 4) (λ j y z → sumFin (λ p → (Wit.row w j p) ⊗ (T4 p y z))) r →
  RankLE (Fin 2) (Fin 4) (Fin 4) TK r
transfer w l0 l1 l2 l3 good r ρ =
  rank-change₂ TK (Wit.matA w) (Wit.comA w) (Good.inv-A good) TK₁ (λ j y k' → refl)
    (rank-change₃ TK₁ (Wit.matB w) (Wit.comB w) (Good.inv-B good) TW (Good.move good) ρ)
  where
  TW : Fin 2 → Fin 4 → Fin 4 → Trit
  TW j y z = sumFin (λ p → (Wit.row w j p) ⊗ (T4 p y z))
  TK₁ : Fin 2 → Fin 4 → Fin 4 → Trit
  TK₁ j y k' = sumFin (λ k → (Wit.matA w k y) ⊗ (TK j k k'))

--------------------------------------------------------------------------------
-- §6 ★★ 主定理
--------------------------------------------------------------------------------

-- ★★ GF(3) 上 ⟨2,2,2⟩ 的每个秩分解至少有 7 项
--   ① 取第一系数非零的一项 i₀, ℓ = a i₀;  ② 限制到 W ⊆ ker ℓ 并丢掉第 i₀ 项;  ③ 搬到 K;  ④ K 上 ≥ 6。
rank-2x2-lower : ∀ r → RankLE₃ 2 r → 7 ≤ r
rank-2x2-lower zero ρ =
  ⊥-elim (T₀≢T₁ (RankLE₃.rank-eq ρ (fzero , fzero) (fzero , fzero) (fzero , fzero)))
rank-2x2-lower (suc r) ρ = s≤s goal
  where
  ρ₄ : RankLE (Fin 4) (Fin 4) (Fin 4) T4 (suc r)
  ρ₄ = to-coords (suc r) (rankLE₃→idx 2 (suc r) ρ)

  -- 每一项
  term : Fin (suc r) → Trit
  term i = (ra ρ₄ i ix₀) ⊗ ((rb ρ₄ i ix₀) ⊗ (rc ρ₄ i ix₀))

  nz-sum : sumFin term ≢ T₀
  nz-sum h = T₀≢T₁ (trans (sym h) (rank-eq ρ₄ ix₀ ix₀ ix₀))

  i₀ : Fin (suc r)
  i₀ = proj₁ (sumFin-nonzero term nz-sum)

  nz : (ra ρ₄ i₀ ix₀) ≢ T₀
  nz = helper (proj₂ (sumFin-nonzero term nz-sum))
    where
    helper : (term i₀) ≢ T₀ → (ra ρ₄ i₀ ix₀) ≢ T₀
    helper h eq =
      h (trans (cong (λ a → a ⊗ ((rb ρ₄ i₀ ix₀) ⊗ (rc ρ₄ i₀ ix₀))) eq)
              (⊗-zeroˡ ((rb ρ₄ i₀ ix₀) ⊗ (rc ρ₄ i₀ ix₀))))

  ℓ : Fin 4 → Trit
  ℓ = ra ρ₄ i₀

  -- ② 的见证
  wit : Σ Wit (λ w → Good w (ℓ ix₀) (ℓ ix₁) (ℓ ix₂) (ℓ ix₃))
  wit = hyper-wit (ℓ ix₀) (ℓ ix₁) (ℓ ix₂) (ℓ ix₃) (inj₁ nz)

  w : Wit
  w = proj₁ wit

  good : Good w (ℓ ix₀) (ℓ ix₁) (ℓ ix₂) (ℓ ix₃)
  good = proj₂ wit

  TW : Fin 2 → Fin 4 → Fin 4 → Trit
  TW j y z = sumFin (λ p → (Wit.row w j p) ⊗ (T4 p y z))

  -- 限制到 W
  ρW : RankLE (Fin 2) (Fin 4) (Fin 4) TW (suc r)
  ρW = rank-restrict T4 (Wit.row w) ρ₄

  l4-ℓ : ∀ p → l4 (ℓ ix₀) (ℓ ix₁) (ℓ ix₂) (ℓ ix₃) p ≡ ℓ p
  l4-ℓ fzero = refl
  l4-ℓ (fsuc fzero) = refl
  l4-ℓ (fsuc (fsuc fzero)) = refl
  l4-ℓ (fsuc (fsuc (fsuc fzero))) = refl

  -- 第 i₀ 项在 W 上恒零
  zero-term : ∀ j → ra ρW i₀ j ≡ T₀
  zero-term j =
    trans (sumFin-cong (λ p → cong (λ a → (Wit.row w j p) ⊗ a) (l4-ℓ p))) (Good.ker good j)

  -- 丢掉第 i₀ 项
  ρW' : RankLE (Fin 2) (Fin 4) (Fin 4) TW r
  ρW' = rank-drop TW ρW i₀ zero-term

  -- 搬到 K
  ρK : RankLE (Fin 2) (Fin 4) (Fin 4) TK r
  ρK = transfer w (ℓ ix₀) (ℓ ix₁) (ℓ ix₂) (ℓ ix₃) good r ρW'

  -- K 上至少 6 项
  goal : 6 ≤ r
  goal = K-bound r ρK

-- 与 M13 合读: GF(3) 上 ⟨2,2,2⟩ 的秩恰为 7
--   下半 rank-2x2-lower（本件）, 上半 rank-strassen（TensorRankGF3, 7 项分解）。
rank₂₂₂-is-7 : (∀ r → RankLE₃ 2 r → 7 ≤ r) × (RankLE₃ 2 7)
rank₂₂₂-is-7 = rank-2x2-lower , rank-strassen

-- 相容性: 库内原有的下界（展平 n² ≤ r 在 n = 2 处给 4 ≤ r）比 7 弱, 没有矛盾
check-weaker : ∀ r → RankLE₃ 2 r → 4 ≤ r
check-weaker r ρ = rank-lower 2 r ρ
