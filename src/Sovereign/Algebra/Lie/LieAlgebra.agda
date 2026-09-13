{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Algebra.Lie.LieAlgebra
-- 离散李代数 — GF(3) 上的括号结构完整形式化 (0 postulate)
--
-- 与 jac_LieGroup (Jacobian 家族) 分开的独立建立; 重复内容为有意为之。
--
-- 结构:
--   §1 局部 2×2 GF(3) 矩阵环 (对式 Mat2T: 加法/取负/乘法)
--   §2 李括号 [X,Y] = XY − YX: 基括号表 + 反称 (81 项穷举)
--      + Jacobi 恒等式 (729 项穷举 — 结合代数交换子恒等式,
--      逐项 refl 同时校验括号定义)
--   §3 三维旋量李代数 (so(3) 的 GF(3) 离散版): 循环括号
--      [x1,x2]=x3, [x2,x3]=x1, [x3,x1]=x2 — 反称 (9 项) + Jacobi (27 项)

module Sovereign.Algebra.Lie.LieAlgebra where

open import Data.Fin using (Fin) renaming (zero to fz; suc to fs)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; sym; trans; module ≡-Reasoning)
open ≡-Reasoning

open import Sovereign.Base.Trit using (Trit; T₀; T₁; T₂; _⊕_; _⊗_; negate; negate²;
  ⊕-comm; ⊕-assoc; ⊕-identityˡ; ⊕-identityʳ; ⊕-inverse;
  ⊗-comm; ⊗-assoc; ⊗-distribˡ-⊕; ⊗-distribʳ-⊕; ⊗-identityˡ; ⊗-identityʳ)
open import Sovereign.Algebra.GF27 using (negate-⊕; negate-⊗; negate-⊗-comm)

--------------------------------------------------------------------------------
-- §1. 局部 2×2 GF(3) 矩阵环 (对式, 全归约)
--------------------------------------------------------------------------------

Mat2T : Set
Mat2T = (Trit × Trit) × (Trit × Trit)

mzero : Mat2T
mzero = (T₀ , T₀) , (T₀ , T₀)

mtadd : Mat2T → Mat2T → Mat2T
mtadd ((a , b) , (c , d)) ((e , f) , (g , h)) =
  ((a ⊕ e) , (b ⊕ f)) , ((c ⊕ g) , (d ⊕ h))

mtneg : Mat2T → Mat2T
mtneg ((a , b) , (c , d)) = ((negate a , negate b) , (negate c , negate d))

mtmul : Mat2T → Mat2T → Mat2T
mtmul ((a , b) , (c , d)) ((e , f) , (g , h)) =
  (((a ⊗ e) ⊕ (b ⊗ g)) , ((a ⊗ f) ⊕ (b ⊗ h))) ,
  (((c ⊗ e) ⊕ (d ⊗ g)) , ((c ⊗ f) ⊕ (d ⊗ h)))

-- 9 矩阵枚举 (构造子 — 供 81/729 项穷举模式匹配)
data M9 : Set where
  m0 m1 m2 m3 m4 m5 m6 m7 m8 : M9

toMat : M9 → Mat2T
toMat m0 = (T₀ , T₀) , (T₀ , T₀)
toMat m1 = (T₁ , T₀) , (T₀ , T₀)    -- E11
toMat m2 = (T₀ , T₁) , (T₀ , T₀)    -- E12
toMat m3 = (T₀ , T₀) , (T₁ , T₀)    -- E21
toMat m4 = (T₀ , T₀) , (T₀ , T₁)    -- E22
toMat m5 = (T₁ , T₀) , (T₀ , T₁)    -- I₂
toMat m6 = (T₁ , T₁) , (T₀ , T₀)    -- E11⊕E12
toMat m7 = (T₀ , T₀) , (T₁ , T₁)    -- E21⊕E22
toMat m8 = (T₁ , T₁) , (T₁ , T₁)    -- 全 1

--------------------------------------------------------------------------------
-- §2. 李括号 [X,Y] = XY − YX
--------------------------------------------------------------------------------

-- 减法即加法 (GF(3): −x = negate x)
br : Mat2T → Mat2T → Mat2T
br X Y = mtadd (mtmul X Y) (mtneg (mtmul Y X))

-- M9 上的括号 (经 toMat 归约)
brM : M9 → M9 → Mat2T
brM X Y = br (toMat X) (toMat Y)

-- 基括号表 ([E11,E12] = E12 等 — 标准 gl(2) 关系的 GF(3) 版)
br-E11-E12 : brM m1 m2 ≡ toMat m2 ; br-E11-E12 = refl
br-E11-E21 : brM m1 m3 ≡ mtneg (toMat m3) ; br-E11-E21 = refl
br-E12-E21 : brM m2 m3 ≡ mtadd (toMat m1) (mtneg (toMat m4)) ; br-E12-E21 = refl
br-I2-any : brM m5 m1 ≡ mzero ; br-I2-any = refl
br-I2-E12 : brM m5 m2 ≡ mzero ; br-I2-E12 = refl
br-E12-E12 : brM m2 m2 ≡ mzero ; br-E12-E12 = refl
-- 反称: [X,Y] + [Y,X] = 0 (81 项穷举)
-- Jacobi: [[X,Y],Z] + [[Y,Z],X] + [[Z,X],Y] = 0 (729 项穷举)
-- 【构造化 2026-09-13】原 jacobi 的 729 = 9³ 条 refl 子句已删除；
-- 改由文件末尾的结构定理 jacobi-sum-zero 一行实例化（见文件尾部 §M9）。



--------------------------------------------------------------------------------
-- §3. 三维旋量李代数 (so(3) 的 GF(3) 离散版)
--------------------------------------------------------------------------------

-- 李代数空间 = GF(3)³ (so(3) 的离散版 — 27 元素, 三维旋量空间)
-- 范畴修正 (2026-08-16): so(3) 是域 GF(3) 上的三维向量空间 (非 Fin 3);
-- 括号 = GF(3) 叉积 (结构常数与 ℝ³ 叉积一致, 反称由 2 ≢ 0 承载)
Lie3 : Set
Lie3 = Trit × Trit × Trit

-- 基向量
x1 x2 x3 : Lie3
x1 = T₁ , T₀ , T₀
x2 = T₀ , T₁ , T₀
x3 = T₀ , T₀ , T₁

-- GF(3) 叉积: (a,b,c) × (d,e,f) =
--   (b⊗f ⊕ negate(c⊗e), c⊗d ⊕ negate(a⊗f), a⊗e ⊕ negate(b⊗d))
br3 : Lie3 → Lie3 → Lie3
br3 (a , b , c) (d , e , f) =
  ((b ⊗ f) ⊕ negate (c ⊗ e)) ,
  ((c ⊗ d) ⊕ negate (a ⊗ f)) ,
  ((a ⊗ e) ⊕ negate (b ⊗ d))

-- 分量加法 (GF(3)³)
add3 : Lie3 → Lie3 → Lie3
add3 (a , b , c) (d , e , f) = (a ⊕ d) , (b ⊕ e) , (c ⊕ f)

-- 零元
zero3 : Lie3
zero3 = T₀ , T₀ , T₀

-- 基循环三式: [x1,x2]=x3, [x2,x3]=x1, [x3,x1]=x2
cyc12 : br3 x1 x2 ≡ x3 ; cyc12 = refl
cyc23 : br3 x2 x3 ≡ x1 ; cyc23 = refl
cyc31 : br3 x3 x1 ≡ x2 ; cyc31 = refl

neg3v : Lie3 → Lie3
neg3v (a , b , c) = negate a , negate b , negate c

-- 基反称对 ([xi,xj] = −[xj,xi], 对角 0)
br3-x1x1 : br3 x1 x1 ≡ zero3 ; br3-x1x1 = refl
br3-x2x2 : br3 x2 x2 ≡ zero3 ; br3-x2x2 = refl
br3-x3x3 : br3 x3 x3 ≡ zero3 ; br3-x3x3 = refl
br3-x1x3 : br3 x1 x3 ≡ neg3v x2 ; br3-x1x3 = refl
br3-x2x1 : br3 x2 x1 ≡ neg3v x3 ; br3-x2x1 = refl
br3-x3x2 : br3 x3 x2 ≡ neg3v x1 ; br3-x3x2 = refl

-- 反称 (27×27 = 729 项穷举): [x,y] + [y,x] = 0
-- 基枚举 (构造子 — 供 Jacobi 27 项穷举模式匹配)
data Basis3 : Set where
  e1 e2 e3 : Basis3

toVec : Basis3 → Lie3
toVec e1 = T₁ , T₀ , T₀
toVec e2 = T₀ , T₁ , T₀
toVec e3 = T₀ , T₀ , T₁

-- 基 Jacobi (3³ = 27 项): [[ei,ej],ek] + [[ej,ek],ei] + [[ek,ei],ej] = 0
jacobi3 : ∀ i j k → add3 (br3 (br3 (toVec i) (toVec j)) (toVec k))
                     (add3 (br3 (br3 (toVec j) (toVec k)) (toVec i))
                           (br3 (br3 (toVec k) (toVec i)) (toVec j))) ≡ zero3
jacobi3 e1 e1 e1 = refl
jacobi3 e1 e1 e2 = refl
jacobi3 e1 e1 e3 = refl
jacobi3 e1 e2 e1 = refl
jacobi3 e1 e2 e2 = refl
jacobi3 e1 e2 e3 = refl
jacobi3 e1 e3 e1 = refl
jacobi3 e1 e3 e2 = refl
jacobi3 e1 e3 e3 = refl
jacobi3 e2 e1 e1 = refl
jacobi3 e2 e1 e2 = refl
jacobi3 e2 e1 e3 = refl
jacobi3 e2 e2 e1 = refl
jacobi3 e2 e2 e2 = refl
jacobi3 e2 e2 e3 = refl
jacobi3 e2 e3 e1 = refl
jacobi3 e2 e3 e2 = refl
jacobi3 e2 e3 e3 = refl
jacobi3 e3 e1 e1 = refl
jacobi3 e3 e1 e2 = refl
jacobi3 e3 e1 e3 = refl
jacobi3 e3 e2 e1 = refl
jacobi3 e3 e2 e2 = refl
jacobi3 e3 e2 e3 = refl
jacobi3 e3 e3 e1 = refl
jacobi3 e3 e3 e2 = refl
jacobi3 e3 e3 e3 = refl

--------------------------------------------------------------------------------
-- §3d. br3 的线性律 (三线性归约的第一批原子 — 目标: 替代 27³ 穷举)
-- 依据: br3 / add3 / zero3 / neg3v 均为分量定义, 故零元律可在定义层直接闭合;
-- 加法律需要 ⊗ 对 ⊕ 的分配律 (Base.Trit).
-- 台账节点: Lie.jacobi.br3-zero
--------------------------------------------------------------------------------

-- 左零元律: br3 zero3 x ≡ zero3 (定义层闭合: T₀ ⊗ _ 与 negate T₀ 均归约)
br3-zeroˡ : ∀ x → br3 zero3 x ≡ zero3
br3-zeroˡ x = refl

-- ⊗ 的右零吸收 (Base.Trit 未提供该引理; 分 3 构造子, 不依赖 _⊗_ 的归约方向)
⊗-zeroʳ : ∀ x → x ⊗ T₀ ≡ T₀
⊗-zeroʳ T₀ = refl
⊗-zeroʳ T₁ = refl
⊗-zeroʳ T₂ = refl

-- 右零元律: br3 x zero3 ≡ zero3
-- 逐分量: (u ⊗ T₀) ⊕ negate (v ⊗ T₀) ≡ T₀ ⊕ T₀ ≡ T₀ (后一步由 ⊕-identityˡ 给出)
br3-zeroʳ : ∀ x → br3 x zero3 ≡ zero3
br3-zeroʳ (a , b , c) = cong₂ _,_ (c0 b c) (cong₂ _,_ (c0 c a) (c0 a b))
  where
    c0 : ∀ u v → (u ⊗ T₀) ⊕ negate (v ⊗ T₀) ≡ T₀
    c0 u v = trans (cong₂ _⊕_ (⊗-zeroʳ u) (cong negate (⊗-zeroʳ v)))
                   (⊕-identityˡ T₀)

-- 标量乘 (分量 ⊗): k · (a,b,c) = (k⊗a, k⊗b, k⊗c)
smul3 : Trit → Lie3 → Lie3
smul3 k (a , b , c) = (k ⊗ a) , (k ⊗ b) , (k ⊗ c)

-- 基坐标分解: 任意元 = a·x1 + b·x2 + c·x3
-- 这是把「一般元 Jacobi」归约到「27 个基例 jacobi3」的桥梁:
-- 有了它 + br3-addˡ/br3-addʳ + 齐性, 三线性展开后只剩 Σ aᵢbⱼcₖ·[xᵢ,xⱼ,xₖ] = 0.
decomp3 : ∀ a b c → (a , b , c) ≡ add3 (add3 (smul3 a x1) (smul3 b x2)) (smul3 c x3)
decomp3 a b c = cong₂ (λ p q → p , q) (sym c1) (cong₂ (λ p q → p , q) (sym c2) (sym c3))
  where
    -- 三分量各自: 两侧 ⊕ 的嵌套是左结合 ((·⊕·)⊕·), 与 add3/add3 的定义一致
    c1 : ((a ⊗ T₁) ⊕ (b ⊗ T₀)) ⊕ (c ⊗ T₀) ≡ a
    c1 = trans (cong₂ _⊕_
                 (trans (cong₂ _⊕_ (⊗-identityʳ a) (⊗-zeroʳ b)) (⊕-identityʳ a))
                 (⊗-zeroʳ c))
               (⊕-identityʳ a)
    c2 : ((a ⊗ T₀) ⊕ (b ⊗ T₁)) ⊕ (c ⊗ T₀) ≡ b
    c2 = trans (cong₂ _⊕_
                 (trans (cong₂ _⊕_ (⊗-zeroʳ a) (⊗-identityʳ b)) (⊕-identityˡ b))
                 (⊗-zeroʳ c))
               (⊕-identityʳ b)
    c3 : ((a ⊗ T₀) ⊕ (b ⊗ T₀)) ⊕ (c ⊗ T₁) ≡ c
    c3 = trans (cong₂ _⊕_
                 (trans (cong₂ _⊕_ (⊗-zeroʳ a) (⊗-zeroʳ b)) (⊕-identityˡ T₀))
                 (⊗-identityʳ c))
               (⊕-identityˡ c)

--------------------------------------------------------------------------------
-- §3g. 齐性: br3 (k·x) y ≡ k·(br3 x y)  (三线性归约的最后一个代数原子)
-- 手法: ⊗-assoc 把标量拉到最外层, negate 用 negate-⊗ + negate-⊗-comm 穿过 ⊗,
--       最后 ⊗-distribˡ-⊕ 把标量分配回 ⊕ 上 —— 全过程无分量穷举.
-- 台账节点: Lie.jacobi.br3-smul
--------------------------------------------------------------------------------

-- negate 穿过双层 ⊗: negate ((k⊗p)⊗q) ≡ k ⊗ negate (p⊗q)
-- 路径: ⊗-assoc → negate-⊗ → negate-⊗-comm (三步, 均在 GF27)
br3-smul-neg : ∀ k p q → negate ((k ⊗ p) ⊗ q) ≡ k ⊗ negate (p ⊗ q)
br3-smul-neg k p q =
  trans (cong negate (⊗-assoc k p q))
    (trans (negate-⊗ k (p ⊗ q)) (negate-⊗-comm k (p ⊗ q)))

-- 单个分量: ((k⊗u)⊗v) ⊕ negate ((k⊗p)⊗q) ≡ k ⊗ ((u⊗v) ⊕ negate (p⊗q))
br3-smul-comp : ∀ k u v p q →
  ((k ⊗ u) ⊗ v) ⊕ negate ((k ⊗ p) ⊗ q) ≡ k ⊗ ((u ⊗ v) ⊕ negate (p ⊗ q))
br3-smul-comp k u v p q =
  trans (cong₂ _⊕_ (⊗-assoc k u v) (br3-smul-neg k p q))
        (sym (⊗-distribˡ-⊕ k (u ⊗ v) (negate (p ⊗ q))))

-- 主引理: 标量与括号对第一槽可交换
br3-smulˡ : ∀ k x y → br3 (smul3 k x) y ≡ smul3 k (br3 x y)
br3-smulˡ k (a , b , c) (d , e , f) =
  cong₂ (λ p q → p , q)
        (br3-smul-comp k b f c e)
        (cong₂ (λ p q → p , q)
               (br3-smul-comp k c d a f)
               (br3-smul-comp k a e b d))

-- 标量换位: u ⊗ (k ⊗ v) ≡ k ⊗ (u ⊗ v)  (先 ⊗-comm 把 k 换到左侧, 再 ⊗-assoc 拉出)
br3-swap : ∀ k u v → u ⊗ (k ⊗ v) ≡ k ⊗ (u ⊗ v)
br3-swap k u v =
  trans (sym (⊗-assoc u k v))
    (trans (cong (λ z → z ⊗ v) (⊗-comm u k)) (⊗-assoc k u v))

-- 第二槽的 negate 处理: negate (p ⊗ (k⊗q)) ≡ k ⊗ negate (p⊗q)
br3-smul-negʳ : ∀ k p q → negate (p ⊗ (k ⊗ q)) ≡ k ⊗ negate (p ⊗ q)
br3-smul-negʳ k p q =
  trans (cong negate (br3-swap k p q))
    (trans (negate-⊗ k (p ⊗ q)) (negate-⊗-comm k (p ⊗ q)))

-- 第二槽单分量: (u ⊗ (k⊗v)) ⊕ negate (p ⊗ (k⊗q)) ≡ k ⊗ ((u⊗v) ⊕ negate (p⊗q))
br3-smul-compʳ : ∀ k u v p q →
  (u ⊗ (k ⊗ v)) ⊕ negate (p ⊗ (k ⊗ q)) ≡ k ⊗ ((u ⊗ v) ⊕ negate (p ⊗ q))
br3-smul-compʳ k u v p q =
  trans (cong₂ _⊕_ (br3-swap k u v) (br3-smul-negʳ k p q))
        (sym (⊗-distribˡ-⊕ k (u ⊗ v) (negate (p ⊗ q))))

-- 主引理: 标量与括号对第二槽可交换
br3-smulʳ : ∀ k x y → br3 x (smul3 k y) ≡ smul3 k (br3 x y)
br3-smulʳ k (a , b , c) (d , e , f) =
  cong₂ (λ p q → p , q)
        (br3-smul-compʳ k b f c e)
        (cong₂ (λ p q → p , q)
               (br3-smul-compʳ k c d a f)
               (br3-smul-compʳ k a e b d))

--------------------------------------------------------------------------------
-- §3h. 一般元 Jacobi 的三元封装 J3 (通向根节点 trilinear-reduction)
-- J3 定义为与 jacobi3 逐字同形的表达式 ⇒ 27 个基例可直接引用, 无需重证.
-- 剩余工作: J3 对每个槽位的加法/齐性 (由 br3-addˡ/ʳ + br3-smulˡ/ʳ 推出),
--           再经 decomp3 拆基坐标 ⇒ Σ aᵢbⱼcₖ·jacobi3 i j k = 0.
--------------------------------------------------------------------------------

J3 : Lie3 → Lie3 → Lie3 → Lie3
J3 x y z = add3 (br3 (br3 x y) z)
                (add3 (br3 (br3 y z) x) (br3 (br3 z x) y))

-- 基三元 Jacobi: 与 jacobi3 定义同形, 故直接复用 27 个 refl 基例
J3-basis : ∀ i j k → J3 (toVec i) (toVec j) (toVec k) ≡ zero3
J3-basis = jacobi3

-- smul3 吸收零元 (把 Σ aᵢbⱼcₖ·jacobi3 的每一项坍缩成 zero3)
smul3-zero : ∀ k → smul3 k zero3 ≡ zero3
smul3-zero k =
  cong₂ (λ p q → p , q) (⊗-zeroʳ k)
        (cong₂ (λ p q → p , q) (⊗-zeroʳ k) (⊗-zeroʳ k))

-- 零元的可加性 (折叠 27 项和)
add3-zero-zero : add3 zero3 zero3 ≡ zero3
add3-zero-zero = refl

-- 诚实边界: 全 Jacobi (27³ 项) 由括号的三线性 (双线性两个槽位) +
-- 基 Jacobi 27 项导出 — **三线性归约已闭合 (2026-09-13)**: 见 §3n `jacobi-general`
--   `∀ x y z → J3 x y z ≡ zero3`, 经 decomp3 拆基坐标 + J3 三槽线性律 ×6 + 27 基例 + 坍缩,
--   **取代 27³ = 19683 项穷举** (未以 postulate 驻留)。

-- 0 postulate.

--------------------------------------------------------------------------------
-- 反称性 asym3 (构造性: br3 双线性, 替代原 729 case 穷举)
--------------------------------------------------------------------------------

swap4 : ∀ A B C D → (A ⊕ B) ⊕ (C ⊕ D) ≡ (A ⊕ C) ⊕ (B ⊕ D)
swap4 A B C D =
  trans (sym (⊕-assoc (A ⊕ B) C D))
    (trans (cong (λ u → u ⊕ D) (⊕-assoc A B C))
      (trans (cong (λ u → (A ⊕ u) ⊕ D) (⊕-comm B C))
        (trans (cong (λ u → u ⊕ D) (sym (⊕-assoc A C B)))
          (⊕-assoc (A ⊕ C) B D))))

-- 注 (2026-09-13): 此处曾误加一份 br3-addˡ / br3-add-comp / cong3v 的重复定义,
-- 编译报 ClashingDefinition 后已撤回 —— 三线性律 br3-addˡ(:987) 与 br3-addʳ(:1029)
-- 在下方早已存在且已证。教训: 查阅既有引理时不可截断 grep 输出。

-- 分量加法交换/结合
add3-comm : ∀ x y → add3 x y ≡ add3 y x
add3-comm (a , b , c) (d , e , f) = cong₃ (λ p q r → p , q , r) (⊕-comm a d) (⊕-comm b e) (⊕-comm c f)
  where
    cong₃ : ∀ {A B C D : Set} {x y : A} {u v : B} {r s : C} (g : A → B → C → D) →
      x ≡ y → u ≡ v → r ≡ s → g x u r ≡ g y v s
    cong₃ g refl refl refl = refl

add3-assoc : ∀ x y z → add3 (add3 x y) z ≡ add3 x (add3 y z)
add3-assoc (a , b , c) (d , e , f) (g , h , i) =
  cong₃ (λ p q r → p , q , r) (⊕-assoc a d g) (⊕-assoc b e h) (⊕-assoc c f i)
  where
    cong₃ : ∀ {A B C D : Set} {x y : A} {u v : B} {r s : C} (g : A → B → C → D) →
      x ≡ y → u ≡ v → r ≡ s → g x u r ≡ g y v s
    cong₃ g refl refl refl = refl

-- br3 保加法 (左线性, 逐分量)
br3-addˡ : ∀ x y z → br3 (add3 x y) z ≡ add3 (br3 x z) (br3 y z)
br3-addˡ (a₁ , b₁ , c₁) (a₂ , b₂ , c₂) (d , e , f) =
  cong₃ (λ p q r → p , q , r) c0 c1 c2
  where
    cong₃ : ∀ {A B C D : Set} {x y : A} {u v : B} {r s : C} (g : A → B → C → D) →
      x ≡ y → u ≡ v → r ≡ s → g x u r ≡ g y v s
    cong₃ g refl refl refl = refl
    c0 : ((b₁ ⊕ b₂) ⊗ f) ⊕ negate ((c₁ ⊕ c₂) ⊗ e)
       ≡ ((b₁ ⊗ f) ⊕ negate (c₁ ⊗ e)) ⊕ ((b₂ ⊗ f) ⊕ negate (c₂ ⊗ e))
    c0 = begin
      ((b₁ ⊕ b₂) ⊗ f) ⊕ negate ((c₁ ⊕ c₂) ⊗ e)
        ≡⟨ cong₂ _⊕_ (⊗-distribʳ-⊕ b₁ b₂ f) (cong negate (⊗-distribʳ-⊕ c₁ c₂ e)) ⟩
      ((b₁ ⊗ f) ⊕ (b₂ ⊗ f)) ⊕ negate ((c₁ ⊗ e) ⊕ (c₂ ⊗ e))
        ≡⟨ cong (((b₁ ⊗ f) ⊕ (b₂ ⊗ f)) ⊕_) (negate-⊕ (c₁ ⊗ e) (c₂ ⊗ e)) ⟩
      ((b₁ ⊗ f) ⊕ (b₂ ⊗ f)) ⊕ (negate (c₁ ⊗ e) ⊕ negate (c₂ ⊗ e))
        ≡⟨ swap4 (b₁ ⊗ f) (b₂ ⊗ f) (negate (c₁ ⊗ e)) (negate (c₂ ⊗ e)) ⟩
      ((b₁ ⊗ f) ⊕ negate (c₁ ⊗ e)) ⊕ ((b₂ ⊗ f) ⊕ negate (c₂ ⊗ e))
      ∎
    c1 : ((c₁ ⊕ c₂) ⊗ d) ⊕ negate ((a₁ ⊕ a₂) ⊗ f)
       ≡ ((c₁ ⊗ d) ⊕ negate (a₁ ⊗ f)) ⊕ ((c₂ ⊗ d) ⊕ negate (a₂ ⊗ f))
    c1 = begin
      ((c₁ ⊕ c₂) ⊗ d) ⊕ negate ((a₁ ⊕ a₂) ⊗ f)
        ≡⟨ cong₂ _⊕_ (⊗-distribʳ-⊕ c₁ c₂ d) (cong negate (⊗-distribʳ-⊕ a₁ a₂ f)) ⟩
      ((c₁ ⊗ d) ⊕ (c₂ ⊗ d)) ⊕ negate ((a₁ ⊗ f) ⊕ (a₂ ⊗ f))
        ≡⟨ cong (((c₁ ⊗ d) ⊕ (c₂ ⊗ d)) ⊕_) (negate-⊕ (a₁ ⊗ f) (a₂ ⊗ f)) ⟩
      ((c₁ ⊗ d) ⊕ (c₂ ⊗ d)) ⊕ (negate (a₁ ⊗ f) ⊕ negate (a₂ ⊗ f))
        ≡⟨ swap4 (c₁ ⊗ d) (c₂ ⊗ d) (negate (a₁ ⊗ f)) (negate (a₂ ⊗ f)) ⟩
      ((c₁ ⊗ d) ⊕ negate (a₁ ⊗ f)) ⊕ ((c₂ ⊗ d) ⊕ negate (a₂ ⊗ f))
      ∎
    c2 : ((a₁ ⊕ a₂) ⊗ e) ⊕ negate ((b₁ ⊕ b₂) ⊗ d)
       ≡ ((a₁ ⊗ e) ⊕ negate (b₁ ⊗ d)) ⊕ ((a₂ ⊗ e) ⊕ negate (b₂ ⊗ d))
    c2 = begin
      ((a₁ ⊕ a₂) ⊗ e) ⊕ negate ((b₁ ⊕ b₂) ⊗ d)
        ≡⟨ cong₂ _⊕_ (⊗-distribʳ-⊕ a₁ a₂ e) (cong negate (⊗-distribʳ-⊕ b₁ b₂ d)) ⟩
      ((a₁ ⊗ e) ⊕ (a₂ ⊗ e)) ⊕ negate ((b₁ ⊗ d) ⊕ (b₂ ⊗ d))
        ≡⟨ cong (((a₁ ⊗ e) ⊕ (a₂ ⊗ e)) ⊕_) (negate-⊕ (b₁ ⊗ d) (b₂ ⊗ d)) ⟩
      ((a₁ ⊗ e) ⊕ (a₂ ⊗ e)) ⊕ (negate (b₁ ⊗ d) ⊕ negate (b₂ ⊗ d))
        ≡⟨ swap4 (a₁ ⊗ e) (a₂ ⊗ e) (negate (b₁ ⊗ d)) (negate (b₂ ⊗ d)) ⟩
      ((a₁ ⊗ e) ⊕ negate (b₁ ⊗ d)) ⊕ ((a₂ ⊗ e) ⊕ negate (b₂ ⊗ d))
      ∎

-- br3 保加法 (右线性)
br3-addʳ : ∀ x y z → br3 x (add3 y z) ≡ add3 (br3 x y) (br3 x z)
br3-addʳ (a , b , c) (d₁ , e₁ , f₁) (d₂ , e₂ , f₂) =
  cong₃ (λ p q r → p , q , r) c0 c1 c2
  where
    cong₃ : ∀ {A B C D : Set} {x y : A} {u v : B} {r s : C} (g : A → B → C → D) →
      x ≡ y → u ≡ v → r ≡ s → g x u r ≡ g y v s
    cong₃ g refl refl refl = refl
    c0 : (b ⊗ (f₁ ⊕ f₂)) ⊕ negate (c ⊗ (e₁ ⊕ e₂))
       ≡ ((b ⊗ f₁) ⊕ negate (c ⊗ e₁)) ⊕ ((b ⊗ f₂) ⊕ negate (c ⊗ e₂))
    c0 = begin
      (b ⊗ (f₁ ⊕ f₂)) ⊕ negate (c ⊗ (e₁ ⊕ e₂))
        ≡⟨ cong₂ _⊕_ (⊗-distribˡ-⊕ b f₁ f₂) (cong negate (⊗-distribˡ-⊕ c e₁ e₂)) ⟩
      ((b ⊗ f₁) ⊕ (b ⊗ f₂)) ⊕ negate ((c ⊗ e₁) ⊕ (c ⊗ e₂))
        ≡⟨ cong (((b ⊗ f₁) ⊕ (b ⊗ f₂)) ⊕_) (negate-⊕ (c ⊗ e₁) (c ⊗ e₂)) ⟩
      ((b ⊗ f₁) ⊕ (b ⊗ f₂)) ⊕ (negate (c ⊗ e₁) ⊕ negate (c ⊗ e₂))
        ≡⟨ swap4 (b ⊗ f₁) (b ⊗ f₂) (negate (c ⊗ e₁)) (negate (c ⊗ e₂)) ⟩
      ((b ⊗ f₁) ⊕ negate (c ⊗ e₁)) ⊕ ((b ⊗ f₂) ⊕ negate (c ⊗ e₂))
      ∎
    c1 : (c ⊗ (d₁ ⊕ d₂)) ⊕ negate (a ⊗ (f₁ ⊕ f₂))
       ≡ ((c ⊗ d₁) ⊕ negate (a ⊗ f₁)) ⊕ ((c ⊗ d₂) ⊕ negate (a ⊗ f₂))
    c1 = begin
      (c ⊗ (d₁ ⊕ d₂)) ⊕ negate (a ⊗ (f₁ ⊕ f₂))
        ≡⟨ cong₂ _⊕_ (⊗-distribˡ-⊕ c d₁ d₂) (cong negate (⊗-distribˡ-⊕ a f₁ f₂)) ⟩
      ((c ⊗ d₁) ⊕ (c ⊗ d₂)) ⊕ negate ((a ⊗ f₁) ⊕ (a ⊗ f₂))
        ≡⟨ cong (((c ⊗ d₁) ⊕ (c ⊗ d₂)) ⊕_) (negate-⊕ (a ⊗ f₁) (a ⊗ f₂)) ⟩
      ((c ⊗ d₁) ⊕ (c ⊗ d₂)) ⊕ (negate (a ⊗ f₁) ⊕ negate (a ⊗ f₂))
        ≡⟨ swap4 (c ⊗ d₁) (c ⊗ d₂) (negate (a ⊗ f₁)) (negate (a ⊗ f₂)) ⟩
      ((c ⊗ d₁) ⊕ negate (a ⊗ f₁)) ⊕ ((c ⊗ d₂) ⊕ negate (a ⊗ f₂))
      ∎
    c2 : (a ⊗ (e₁ ⊕ e₂)) ⊕ negate (b ⊗ (d₁ ⊕ d₂))
       ≡ ((a ⊗ e₁) ⊕ negate (b ⊗ d₁)) ⊕ ((a ⊗ e₂) ⊕ negate (b ⊗ d₂))
    c2 = begin
      (a ⊗ (e₁ ⊕ e₂)) ⊕ negate (b ⊗ (d₁ ⊕ d₂))
        ≡⟨ cong₂ _⊕_ (⊗-distribˡ-⊕ a e₁ e₂) (cong negate (⊗-distribˡ-⊕ b d₁ d₂)) ⟩
      ((a ⊗ e₁) ⊕ (a ⊗ e₂)) ⊕ negate ((b ⊗ d₁) ⊕ (b ⊗ d₂))
        ≡⟨ cong (((a ⊗ e₁) ⊕ (a ⊗ e₂)) ⊕_) (negate-⊕ (b ⊗ d₁) (b ⊗ d₂)) ⟩
      ((a ⊗ e₁) ⊕ (a ⊗ e₂)) ⊕ (negate (b ⊗ d₁) ⊕ negate (b ⊗ d₂))
        ≡⟨ swap4 (a ⊗ e₁) (a ⊗ e₂) (negate (b ⊗ d₁)) (negate (b ⊗ d₂)) ⟩
      ((a ⊗ e₁) ⊕ negate (b ⊗ d₁)) ⊕ ((a ⊗ e₂) ⊕ negate (b ⊗ d₂))
      ∎

--------------------------------------------------------------------------------
-- §3i. J3 的三个角色 P/Q/R 的加法律与齐性 (无重结合, 每条只是 br3 律套一次)
--   P(x,y,z) = [[x,y],z]      Q(x,y,z) = [[y,z],x]      R(x,y,z) = [[z,x],y]
-- 这些是 J3 层线性的工作引理; J3 层只剩 add3 的重排 (下一步).
-- 位置要求: 必须定义在 br3-addˡ/ʳ 之后 (Agda 无前向引用).
--------------------------------------------------------------------------------

-- P: [x+x',y],z = [x,y],z + [x',y],z   (br3-addˡ 两次)
P-addˡ : ∀ x x' y z →
  br3 (br3 (add3 x x') y) z ≡ add3 (br3 (br3 x y) z) (br3 (br3 x' y) z)
P-addˡ x x' y z =
  trans (cong (λ w → br3 w z) (br3-addˡ x x' y)) (br3-addˡ (br3 x y) (br3 x' y) z)

-- Q: [[y,z], x+x'] (x 在第二槽)
Q-addˡ : ∀ x x' y z →
  br3 (br3 y z) (add3 x x') ≡ add3 (br3 (br3 y z) x) (br3 (br3 y z) x')
Q-addˡ x x' y z = br3-addʳ (br3 y z) x x'

-- R: [[z, x+x'], y]   (br3-addʳ 再 br3-addˡ)
R-addˡ : ∀ x x' y z →
  br3 (br3 z (add3 x x')) y ≡ add3 (br3 (br3 z x) y) (br3 (br3 z x') y)
R-addˡ x x' y z =
  trans (cong (λ w → br3 w y) (br3-addʳ z x x')) (br3-addˡ (br3 z x) (br3 z x') y)

-- 齐性: P/Q/R 三者的第一槽标量提取
P-smul : ∀ k x y z → br3 (br3 (smul3 k x) y) z ≡ smul3 k (br3 (br3 x y) z)
P-smul k x y z =
  trans (cong (λ w → br3 w z) (br3-smulˡ k x y)) (br3-smulˡ k (br3 x y) z)

Q-smul : ∀ k x y z → br3 (br3 y z) (smul3 k x) ≡ smul3 k (br3 (br3 y z) x)
Q-smul k x y z = br3-smulʳ k (br3 y z) x

R-smul : ∀ k x y z → br3 (br3 z (smul3 k x)) y ≡ smul3 k (br3 (br3 z x) y)
R-smul k x y z =
  trans (cong (λ w → br3 w y) (br3-smulʳ k z x)) (br3-smulˡ k (br3 z x) y)

--------------------------------------------------------------------------------
-- §3j. 六项重结合 (J3 层线性唯一的非平凡步骤)
-- 关键: 不需要新的 ⊕-assoc/⊕-comm 长链 —— 两次 swap4 即得:
--   第一次把 p,s 提到最外, 第二次把 (q,r),(t,u) 交错开.
--------------------------------------------------------------------------------

⊕-shuffle6 : ∀ p q r s t u →
  (p ⊕ (q ⊕ r)) ⊕ (s ⊕ (t ⊕ u)) ≡ (p ⊕ s) ⊕ ((q ⊕ t) ⊕ (r ⊕ u))
⊕-shuffle6 p q r s t u =
  trans (swap4 p (q ⊕ r) s (t ⊕ u))
        (cong (λ z → (p ⊕ s) ⊕ z) (swap4 q r t u))

-- Lie3 版 (逐分量抬升)
add3-shuffle6 : ∀ P Q R S T U →
  add3 (add3 P (add3 Q R)) (add3 S (add3 T U))
    ≡ add3 (add3 P S) (add3 (add3 Q T) (add3 R U))
add3-shuffle6 (p₁ , p₂ , p₃) (q₁ , q₂ , q₃) (r₁ , r₂ , r₃)
              (s₁ , s₂ , s₃) (t₁ , t₂ , t₃) (u₁ , u₂ , u₃) =
  cong₂ (λ x y → x , y)
        (⊕-shuffle6 p₁ q₁ r₁ s₁ t₁ u₁)
        (cong₂ (λ x y → x , y)
               (⊕-shuffle6 p₂ q₂ r₂ s₂ t₂ u₂)
               (⊕-shuffle6 p₃ q₃ r₃ s₃ t₃ u₃))

--------------------------------------------------------------------------------
-- §3k. J3 的线性 (根定理的最后一块拼图)
-- J3 的角色: P = [[x,y],z], Q = [[y,z],x], R = [[z,x],y]; J3 = P + (Q + R).
-- 加法律: 三段 cong 分别替换 P/Q/R, 末段 sym add3-shuffle6 把和摆回 (J3+J3).
-- 齐性:   三段 cong 分别提出标量, 末段用 smul3-add (⊗ 对 ⊕ 分配) 把标量提回外层.
--------------------------------------------------------------------------------

P3 Q3 R3 : Lie3 → Lie3 → Lie3 → Lie3
P3 x y z = br3 (br3 x y) z
Q3 x y z = br3 (br3 y z) x
R3 x y z = br3 (br3 z x) y

-- smul3 对 add3 分配 (逐分量 ⊗-distribˡ-⊕)
smul3-add : ∀ k x y → smul3 k (add3 x y) ≡ add3 (smul3 k x) (smul3 k y)
smul3-add k (a , b , c) (d , e , f) =
  cong₂ (λ p q → p , q) (⊗-distribˡ-⊕ k a d)
        (cong₂ (λ p q → p , q) (⊗-distribˡ-⊕ k b e) (⊗-distribˡ-⊕ k c f))

J3-addˡ : ∀ x x' y z → J3 (add3 x x') y z ≡ add3 (J3 x y z) (J3 x' y z)
J3-addˡ x x' y z =
  trans (cong (λ p → add3 p (add3 (Q3 (add3 x x') y z) (R3 (add3 x x') y z)))
              (P-addˡ x x' y z))
   (trans (cong (λ q → add3 (add3 (P3 x y z) (P3 x' y z))
                            (add3 q (R3 (add3 x x') y z)))
               (Q-addˡ x x' y z))
    (trans (cong (λ r → add3 (add3 (P3 x y z) (P3 x' y z))
                             (add3 (add3 (Q3 x y z) (Q3 x' y z)) r))
                (R-addˡ x x' y z))
           (sym (add3-shuffle6 (P3 x y z) (Q3 x y z) (R3 x y z)
                               (P3 x' y z) (Q3 x' y z) (R3 x' y z)))))

J3-smulˡ : ∀ k x y z → J3 (smul3 k x) y z ≡ smul3 k (J3 x y z)
J3-smulˡ k x y z =
  trans (cong (λ p → add3 p (add3 (Q3 (smul3 k x) y z) (R3 (smul3 k x) y z)))
              (P-smul k x y z))
   (trans (cong (λ q → add3 (smul3 k (P3 x y z))
                            (add3 q (R3 (smul3 k x) y z)))
               (Q-smul k x y z))
    (trans (cong (λ r → add3 (smul3 k (P3 x y z))
                             (add3 (smul3 k (Q3 x y z)) r))
                (R-smul k x y z))
           (sym (trans (smul3-add k (P3 x y z) (add3 (Q3 x y z) (R3 x y z)))
                       (cong (add3 (smul3 k (P3 x y z)))
                             (smul3-add k (Q3 x y z) (R3 x y z)))))))

--------------------------------------------------------------------------------
-- §3l. P/Q/R 对第二槽 (y) 与第三槽 (z) 的加法律与齐性 (十二条)
-- 与 §3i 同构: 只是把 br3-addˡ/ʳ 与 br3-smulˡ/ʳ 套在不同槽位上.
--------------------------------------------------------------------------------

-- ---- y 槽 ----
P-addʸ : ∀ x y y' z → P3 x (add3 y y') z ≡ add3 (P3 x y z) (P3 x y' z)
P-addʸ x y y' z =
  trans (cong (λ w → br3 w z) (br3-addʳ x y y')) (br3-addˡ (br3 x y) (br3 x y') z)

Q-addʸ : ∀ x y y' z → Q3 x (add3 y y') z ≡ add3 (Q3 x y z) (Q3 x y' z)
Q-addʸ x y y' z =
  trans (cong (λ w → br3 w x) (br3-addˡ y y' z)) (br3-addˡ (br3 y z) (br3 y' z) x)

R-addʸ : ∀ x y y' z → R3 x (add3 y y') z ≡ add3 (R3 x y z) (R3 x y' z)
R-addʸ x y y' z = br3-addʳ (br3 z x) y y'

P-smulʸ : ∀ k x y z → P3 x (smul3 k y) z ≡ smul3 k (P3 x y z)
P-smulʸ k x y z =
  trans (cong (λ w → br3 w z) (br3-smulʳ k x y)) (br3-smulˡ k (br3 x y) z)

Q-smulʸ : ∀ k x y z → Q3 x (smul3 k y) z ≡ smul3 k (Q3 x y z)
Q-smulʸ k x y z =
  trans (cong (λ w → br3 w x) (br3-smulˡ k y z)) (br3-smulˡ k (br3 y z) x)

R-smulʸ : ∀ k x y z → R3 x (smul3 k y) z ≡ smul3 k (R3 x y z)
R-smulʸ k x y z = br3-smulʳ k (br3 z x) y

-- ---- z 槽 ----
P-addᶻ : ∀ x y z z' → P3 x y (add3 z z') ≡ add3 (P3 x y z) (P3 x y z')
P-addᶻ x y z z' = br3-addʳ (br3 x y) z z'

Q-addᶻ : ∀ x y z z' → Q3 x y (add3 z z') ≡ add3 (Q3 x y z) (Q3 x y z')
Q-addᶻ x y z z' =
  trans (cong (λ w → br3 w x) (br3-addʳ y z z')) (br3-addˡ (br3 y z) (br3 y z') x)

R-addᶻ : ∀ x y z z' → R3 x y (add3 z z') ≡ add3 (R3 x y z) (R3 x y z')
R-addᶻ x y z z' =
  trans (cong (λ w → br3 w y) (br3-addˡ z z' x)) (br3-addˡ (br3 z x) (br3 z' x) y)

P-smulᶻ : ∀ k x y z → P3 x y (smul3 k z) ≡ smul3 k (P3 x y z)
P-smulᶻ k x y z = br3-smulʳ k (br3 x y) z

Q-smulᶻ : ∀ k x y z → Q3 x y (smul3 k z) ≡ smul3 k (Q3 x y z)
Q-smulᶻ k x y z =
  trans (cong (λ w → br3 w x) (br3-smulʳ k y z)) (br3-smulˡ k (br3 y z) x)

R-smulᶻ : ∀ k x y z → R3 x y (smul3 k z) ≡ smul3 k (R3 x y z)
R-smulᶻ k x y z =
  trans (cong (λ w → br3 w y) (br3-smulˡ k z x)) (br3-smulˡ k (br3 z x) y)

--------------------------------------------------------------------------------
-- §3m. J3 对第二/第三槽的线性 (与 §3k 的第一槽逐字同构)
--------------------------------------------------------------------------------

J3-addʳ : ∀ x y y' z → J3 x (add3 y y') z ≡ add3 (J3 x y z) (J3 x y' z)
J3-addʳ x y y' z =
  trans (cong (λ p → add3 p (add3 (Q3 x (add3 y y') z) (R3 x (add3 y y') z)))
              (P-addʸ x y y' z))
   (trans (cong (λ q → add3 (add3 (P3 x y z) (P3 x y' z))
                            (add3 q (R3 x (add3 y y') z)))
               (Q-addʸ x y y' z))
    (trans (cong (λ r → add3 (add3 (P3 x y z) (P3 x y' z))
                             (add3 (add3 (Q3 x y z) (Q3 x y' z)) r))
                (R-addʸ x y y' z))
           (sym (add3-shuffle6 (P3 x y z) (Q3 x y z) (R3 x y z)
                               (P3 x y' z) (Q3 x y' z) (R3 x y' z)))))

J3-smulʳ : ∀ k x y z → J3 x (smul3 k y) z ≡ smul3 k (J3 x y z)
J3-smulʳ k x y z =
  trans (cong (λ p → add3 p (add3 (Q3 x (smul3 k y) z) (R3 x (smul3 k y) z)))
              (P-smulʸ k x y z))
   (trans (cong (λ q → add3 (smul3 k (P3 x y z))
                            (add3 q (R3 x (smul3 k y) z)))
               (Q-smulʸ k x y z))
    (trans (cong (λ r → add3 (smul3 k (P3 x y z))
                             (add3 (smul3 k (Q3 x y z)) r))
                (R-smulʸ k x y z))
           (sym (trans (smul3-add k (P3 x y z) (add3 (Q3 x y z) (R3 x y z)))
                       (cong (add3 (smul3 k (P3 x y z)))
                             (smul3-add k (Q3 x y z) (R3 x y z)))))))

J3-addᶻ : ∀ x y z z' → J3 x y (add3 z z') ≡ add3 (J3 x y z) (J3 x y z')
J3-addᶻ x y z z' =
  trans (cong (λ p → add3 p (add3 (Q3 x y (add3 z z')) (R3 x y (add3 z z'))))
              (P-addᶻ x y z z'))
   (trans (cong (λ q → add3 (add3 (P3 x y z) (P3 x y z'))
                            (add3 q (R3 x y (add3 z z'))))
               (Q-addᶻ x y z z'))
    (trans (cong (λ r → add3 (add3 (P3 x y z) (P3 x y z'))
                             (add3 (add3 (Q3 x y z) (Q3 x y z')) r))
                (R-addᶻ x y z z'))
           (sym (add3-shuffle6 (P3 x y z) (Q3 x y z) (R3 x y z)
                               (P3 x y z') (Q3 x y z') (R3 x y z')))))

J3-smulᶻ : ∀ k x y z → J3 x y (smul3 k z) ≡ smul3 k (J3 x y z)
J3-smulᶻ k x y z =
  trans (cong (λ p → add3 p (add3 (Q3 x y (smul3 k z)) (R3 x y (smul3 k z))))
              (P-smulᶻ k x y z))
   (trans (cong (λ q → add3 (smul3 k (P3 x y z))
                            (add3 q (R3 x y (smul3 k z))))
               (Q-smulᶻ k x y z))
    (trans (cong (λ r → add3 (smul3 k (P3 x y z))
                             (add3 (smul3 k (Q3 x y z)) r))
                (R-smulᶻ k x y z))
           (sym (trans (smul3-add k (P3 x y z) (add3 (Q3 x y z) (R3 x y z)))
                       (cong (add3 (smul3 k (P3 x y z)))
                             (smul3-add k (Q3 x y z) (R3 x y z)))))))

--------------------------------------------------------------------------------
-- §3n. **一般元 Jacobi** (根节点 trilinear-reduction): ∀ x y z → J3 x y z ≡ zero3
-- 这是把 27³ = 19683 项穷举替换成「三线性归约」的兑现点:
--   decomp3 拆基坐标 → J3 三槽线性律 ×6 → 27 个基例 J3-basis (= jacobi3) → 坍缩.
-- 工程要点: 展开链的中间类型极大, 全部交给 Agda 推断, **不手写巨型类型声明**.
--------------------------------------------------------------------------------

-- 坍缩引理: 左嵌套三叉树的三个零 → 零
-- 注: 右端 add3 (add3 zero3 zero3) zero3 在构造子上定义性归约 ⇒ 只需两次 cong₂, 无需引理
zero3-treeL : ∀ {A B C} → A ≡ zero3 → B ≡ zero3 → C ≡ zero3
            → add3 (add3 A B) C ≡ zero3
zero3-treeL a b c = cong₂ add3 (cong₂ add3 a b) c

-- 叶子: J3 (a·xᵢ) (b·xⱼ) (c·xₖ) ≡ zero3
--   三次提标量 (smulˡ/ʳ/ᶻ) → J3-basis (27 基例之一) → 三次 smul3-zero
leaf-zero : ∀ i j k a b c →
  J3 (smul3 a (toVec i)) (smul3 b (toVec j)) (smul3 c (toVec k)) ≡ zero3
leaf-zero i j k a b c =
  trans (J3-smulˡ a (toVec i) (smul3 b (toVec j)) (smul3 c (toVec k)))
   (trans (cong (smul3 a) (J3-smulʳ b (toVec i) (toVec j) (smul3 c (toVec k))))
    (trans (cong (smul3 a) (cong (smul3 b) (J3-smulᶻ c (toVec i) (toVec j) (toVec k))))
     (trans (cong (smul3 a) (cong (smul3 b) (cong (smul3 c) (J3-basis i j k))))
      (trans (cong (smul3 a) (cong (smul3 b) (smul3-zero c)))
       (trans (cong (smul3 a) (smul3-zero b)) (smul3-zero a))))))

-- 单槽展开引理 (符号化, 与具体坐标无关)
exp-x : ∀ a₁ a₂ a₃ y z →
  J3 (add3 (add3 (smul3 a₁ x1) (smul3 a₂ x2)) (smul3 a₃ x3)) y z
  ≡ add3 (add3 (J3 (smul3 a₁ x1) y z) (J3 (smul3 a₂ x2) y z)) (J3 (smul3 a₃ x3) y z)
exp-x a₁ a₂ a₃ y z =
  trans (J3-addˡ (add3 (smul3 a₁ x1) (smul3 a₂ x2)) (smul3 a₃ x3) y z)
        (cong (λ u → add3 u (J3 (smul3 a₃ x3) y z))
              (J3-addˡ (smul3 a₁ x1) (smul3 a₂ x2) y z))

exp-y : ∀ b₁ b₂ b₃ x z →
  J3 x (add3 (add3 (smul3 b₁ x1) (smul3 b₂ x2)) (smul3 b₃ x3)) z
  ≡ add3 (add3 (J3 x (smul3 b₁ x1) z) (J3 x (smul3 b₂ x2) z)) (J3 x (smul3 b₃ x3) z)
exp-y b₁ b₂ b₃ x z =
  trans (J3-addʳ x (add3 (smul3 b₁ x1) (smul3 b₂ x2)) (smul3 b₃ x3) z)
        (cong (λ u → add3 u (J3 x (smul3 b₃ x3) z))
              (J3-addʳ x (smul3 b₁ x1) (smul3 b₂ x2) z))

exp-z : ∀ c₁ c₂ c₃ x y →
  J3 x y (add3 (add3 (smul3 c₁ x1) (smul3 c₂ x2)) (smul3 c₃ x3))
  ≡ add3 (add3 (J3 x y (smul3 c₁ x1)) (J3 x y (smul3 c₂ x2))) (J3 x y (smul3 c₃ x3))
exp-z c₁ c₂ c₃ x y =
  trans (J3-addᶻ x y (add3 (smul3 c₁ x1) (smul3 c₂ x2)) (smul3 c₃ x3))
        (cong (λ u → add3 u (J3 x y (smul3 c₃ x3)))
              (J3-addᶻ x y (smul3 c₁ x1) (smul3 c₂ x2)))

jacobi-general : ∀ x y z → J3 x y z ≡ zero3
jacobi-general (a₁ , a₂ , a₃) (b₁ , b₂ , b₃) (c₁ , c₂ , c₃) =
  trans (cong (λ w → J3 w (b₁ , b₂ , b₃) (c₁ , c₂ , c₃)) (decomp3 a₁ a₂ a₃))
   (trans (cong (λ w → J3 X w (c₁ , c₂ , c₃)) (decomp3 b₁ b₂ b₃))
    (trans (cong (λ w → J3 X Y w) (decomp3 c₁ c₂ c₃))
     (trans (exp-x a₁ a₂ a₃ Y Z)
      (trans yexp
       (trans zexp col)))))
  where
    X₁ = smul3 a₁ x1
    X₂ = smul3 a₂ x2
    X₃ = smul3 a₃ x3
    X  = add3 (add3 X₁ X₂) X₃
    Y₁ = smul3 b₁ x1
    Y₂ = smul3 b₂ x2
    Y₃ = smul3 b₃ x3
    Z₁ = smul3 c₁ x1
    Z₂ = smul3 c₂ x2
    Z₃ = smul3 c₃ x3
    Y  = add3 (add3 Y₁ Y₂) Y₃
    Z  = add3 (add3 Z₁ Z₂) Z₃

    -- y 层: 三个 Xᵢ-项各自按 y 展开 (3 → 9)
    yexp = cong₂ add3
             (cong₂ add3 (exp-y b₁ b₂ b₃ X₁ Z) (exp-y b₁ b₂ b₃ X₂ Z))
             (exp-y b₁ b₂ b₃ X₃ Z)

    -- z 层: 九个 (Xᵢ,Yⱼ)-项各自按 z 展开 (9 → 27)
    zexp = cong₂ add3
             (cong₂ add3
                (cong₂ add3
                   (cong₂ add3 (exp-z c₁ c₂ c₃ X₁ Y₁) (exp-z c₁ c₂ c₃ X₁ Y₂))
                   (exp-z c₁ c₂ c₃ X₁ Y₃))
                (cong₂ add3
                   (cong₂ add3 (exp-z c₁ c₂ c₃ X₂ Y₁) (exp-z c₁ c₂ c₃ X₂ Y₂))
                   (exp-z c₁ c₂ c₃ X₂ Y₃)))
             (cong₂ add3
                (cong₂ add3 (exp-z c₁ c₂ c₃ X₃ Y₁) (exp-z c₁ c₂ c₃ X₃ Y₂))
                (exp-z c₁ c₂ c₃ X₃ Y₃))

    -- 坍缩: 27 叶子 → 9 组 → 3 组 → 1
    col = zero3-treeL
            (zero3-treeL
               (zero3-treeL (leaf-zero e1 e1 e1 a₁ b₁ c₁)
                            (leaf-zero e1 e1 e2 a₁ b₁ c₂)
                            (leaf-zero e1 e1 e3 a₁ b₁ c₃))
               (zero3-treeL (leaf-zero e1 e2 e1 a₁ b₂ c₁)
                            (leaf-zero e1 e2 e2 a₁ b₂ c₂)
                            (leaf-zero e1 e2 e3 a₁ b₂ c₃))
               (zero3-treeL (leaf-zero e1 e3 e1 a₁ b₃ c₁)
                            (leaf-zero e1 e3 e2 a₁ b₃ c₂)
                            (leaf-zero e1 e3 e3 a₁ b₃ c₃)))
            (zero3-treeL
               (zero3-treeL (leaf-zero e2 e1 e1 a₂ b₁ c₁)
                            (leaf-zero e2 e1 e2 a₂ b₁ c₂)
                            (leaf-zero e2 e1 e3 a₂ b₁ c₃))
               (zero3-treeL (leaf-zero e2 e2 e1 a₂ b₂ c₁)
                            (leaf-zero e2 e2 e2 a₂ b₂ c₂)
                            (leaf-zero e2 e2 e3 a₂ b₂ c₃))
               (zero3-treeL (leaf-zero e2 e3 e1 a₂ b₃ c₁)
                            (leaf-zero e2 e3 e2 a₂ b₃ c₂)
                            (leaf-zero e2 e3 e3 a₂ b₃ c₃)))
            (zero3-treeL
               (zero3-treeL (leaf-zero e3 e1 e1 a₃ b₁ c₁)
                            (leaf-zero e3 e1 e2 a₃ b₁ c₂)
                            (leaf-zero e3 e1 e3 a₃ b₁ c₃))
               (zero3-treeL (leaf-zero e3 e2 e1 a₃ b₂ c₁)
                            (leaf-zero e3 e2 e2 a₃ b₂ c₂)
                            (leaf-zero e3 e2 e3 a₃ b₂ c₃))
               (zero3-treeL (leaf-zero e3 e3 e1 a₃ b₃ c₁)
                            (leaf-zero e3 e3 e2 a₃ b₃ c₂)
                            (leaf-zero e3 e3 e3 a₃ b₃ c₃)))

-- add3 分量零律
add3-zeroˡ : ∀ x → add3 zero3 x ≡ x
add3-zeroˡ (a , b , c) = cong₃ (λ p q r → p , q , r) (⊕-identityˡ a) (⊕-identityˡ b) (⊕-identityˡ c)
  where
    cong₃ : ∀ {A B C D : Set} {x y : A} {u v : B} {r s : C} (g : A → B → C → D) →
      x ≡ y → u ≡ v → r ≡ s → g x u r ≡ g y v s
    cong₃ g refl refl refl = refl

-- ★ asym3: br3 x y + br3 y x = 0 ★
asym3 : ∀ x y → add3 (br3 x y) (br3 y x) ≡ zero3
asym3 (a , b , c) (d , e , f) = cong₃ (λ p q r → p , q , r) c0 c1 c2
  where
    cong₃ : ∀ {A B C D : Set} {x y : A} {u v : B} {r s : C} (g : A → B → C → D) →
      x ≡ y → u ≡ v → r ≡ s → g x u r ≡ g y v s
    cong₃ g refl refl refl = refl
    neg-add-zero : ∀ u → (negate u) ⊕ u ≡ T₀
    neg-add-zero u = trans (⊕-comm (negate u) u) (⊕-inverse u)
    c0 : ((b ⊗ f) ⊕ negate (c ⊗ e)) ⊕ ((e ⊗ c) ⊕ negate (f ⊗ b)) ≡ T₀
    c0 = begin
      ((b ⊗ f) ⊕ negate (c ⊗ e)) ⊕ ((e ⊗ c) ⊕ negate (f ⊗ b))
        ≡⟨ cong (((b ⊗ f) ⊕ negate (c ⊗ e)) ⊕_) (cong₂ (λ (u v : Trit) → u ⊕ negate v) (⊗-comm e c) (⊗-comm f b)) ⟩
      ((b ⊗ f) ⊕ negate (c ⊗ e)) ⊕ ((c ⊗ e) ⊕ negate (b ⊗ f))
        ≡⟨ swap4 (b ⊗ f) (negate (c ⊗ e)) (c ⊗ e) (negate (b ⊗ f)) ⟩
      ((b ⊗ f) ⊕ (c ⊗ e)) ⊕ (negate (c ⊗ e) ⊕ negate (b ⊗ f))
        ≡⟨ cong (((b ⊗ f) ⊕ (c ⊗ e)) ⊕_) (sym (negate-⊕ (c ⊗ e) (b ⊗ f))) ⟩
      ((b ⊗ f) ⊕ (c ⊗ e)) ⊕ negate ((c ⊗ e) ⊕ (b ⊗ f))
        ≡⟨ cong (λ u → u ⊕ negate ((c ⊗ e) ⊕ (b ⊗ f))) (⊕-comm (b ⊗ f) (c ⊗ e)) ⟩
      ((c ⊗ e) ⊕ (b ⊗ f)) ⊕ negate ((c ⊗ e) ⊕ (b ⊗ f))
        ≡⟨ ⊕-inverse ((c ⊗ e) ⊕ (b ⊗ f)) ⟩
      T₀
      ∎
    c1 : ((c ⊗ d) ⊕ negate (a ⊗ f)) ⊕ ((f ⊗ a) ⊕ negate (d ⊗ c)) ≡ T₀
    c1 = begin
      ((c ⊗ d) ⊕ negate (a ⊗ f)) ⊕ ((f ⊗ a) ⊕ negate (d ⊗ c))
        ≡⟨ cong (((c ⊗ d) ⊕ negate (a ⊗ f)) ⊕_) (cong₂ (λ (u v : Trit) → u ⊕ negate v) (⊗-comm f a) (⊗-comm d c)) ⟩
      ((c ⊗ d) ⊕ negate (a ⊗ f)) ⊕ ((a ⊗ f) ⊕ negate (c ⊗ d))
        ≡⟨ swap4 (c ⊗ d) (negate (a ⊗ f)) (a ⊗ f) (negate (c ⊗ d)) ⟩
      ((c ⊗ d) ⊕ (a ⊗ f)) ⊕ (negate (a ⊗ f) ⊕ negate (c ⊗ d))
        ≡⟨ cong (((c ⊗ d) ⊕ (a ⊗ f)) ⊕_) (sym (negate-⊕ (a ⊗ f) (c ⊗ d))) ⟩
      ((c ⊗ d) ⊕ (a ⊗ f)) ⊕ negate ((a ⊗ f) ⊕ (c ⊗ d))
        ≡⟨ cong (λ u → u ⊕ negate ((a ⊗ f) ⊕ (c ⊗ d))) (⊕-comm (c ⊗ d) (a ⊗ f)) ⟩
      ((a ⊗ f) ⊕ (c ⊗ d)) ⊕ negate ((a ⊗ f) ⊕ (c ⊗ d))
        ≡⟨ ⊕-inverse ((a ⊗ f) ⊕ (c ⊗ d)) ⟩
      T₀
      ∎
    c2 : ((a ⊗ e) ⊕ negate (b ⊗ d)) ⊕ ((d ⊗ b) ⊕ negate (e ⊗ a)) ≡ T₀
    c2 = begin
      ((a ⊗ e) ⊕ negate (b ⊗ d)) ⊕ ((d ⊗ b) ⊕ negate (e ⊗ a))
        ≡⟨ cong (((a ⊗ e) ⊕ negate (b ⊗ d)) ⊕_) (cong₂ (λ (u v : Trit) → u ⊕ negate v) (⊗-comm d b) (⊗-comm e a)) ⟩
      ((a ⊗ e) ⊕ negate (b ⊗ d)) ⊕ ((b ⊗ d) ⊕ negate (a ⊗ e))
        ≡⟨ swap4 (a ⊗ e) (negate (b ⊗ d)) (b ⊗ d) (negate (a ⊗ e)) ⟩
      ((a ⊗ e) ⊕ (b ⊗ d)) ⊕ (negate (b ⊗ d) ⊕ negate (a ⊗ e))
        ≡⟨ cong (((a ⊗ e) ⊕ (b ⊗ d)) ⊕_) (sym (negate-⊕ (b ⊗ d) (a ⊗ e))) ⟩
      ((a ⊗ e) ⊕ (b ⊗ d)) ⊕ negate ((b ⊗ d) ⊕ (a ⊗ e))
        ≡⟨ cong (λ u → u ⊕ negate ((b ⊗ d) ⊕ (a ⊗ e))) (⊕-comm (a ⊗ e) (b ⊗ d)) ⟩
      ((b ⊗ d) ⊕ (a ⊗ e)) ⊕ negate ((b ⊗ d) ⊕ (a ⊗ e))
        ≡⟨ ⊕-inverse ((b ⊗ d) ⊕ (a ⊗ e)) ⟩
      T₀
      ∎

--------------------------------------------------------------------------------
-- 反称性 asym (构造性: br = XY - YX, 替代原 81 case 穷举)
--------------------------------------------------------------------------------

cong4 : ∀ {a b c d a' b' c' d' : Trit} →
  a ≡ a' → b ≡ b' → c ≡ c' → d ≡ d' →
  ((a , b) , (c , d)) ≡ ((a' , b') , (c' , d'))
cong4 refl refl refl refl = refl

mtadd-comm : ∀ X Y → mtadd X Y ≡ mtadd Y X
mtadd-comm ((a , b) , (c , d)) ((e , f) , (g , h)) =
  cong4 (⊕-comm a e) (⊕-comm b f) (⊕-comm c g) (⊕-comm d h)

mtadd-assoc : ∀ X Y Z → mtadd (mtadd X Y) Z ≡ mtadd X (mtadd Y Z)
mtadd-assoc ((a , b) , (c , d)) ((e , f) , (g , h)) ((i , j) , (k , l)) =
  cong4 (⊕-assoc a e i) (⊕-assoc b f j) (⊕-assoc c g k) (⊕-assoc d h l)

mtadd-inverse : ∀ X → mtadd X (mtneg X) ≡ mzero
mtadd-inverse ((a , b) , (c , d)) =
  cong4 (⊕-inverse a) (⊕-inverse b) (⊕-inverse c) (⊕-inverse d)

mtadd-identityˡ : ∀ X → mtadd mzero X ≡ X
mtadd-identityˡ ((a , b) , (c , d)) =
  cong4 (⊕-identityˡ a) (⊕-identityˡ b) (⊕-identityˡ c) (⊕-identityˡ d)

mtadd-identityʳ : ∀ X → mtadd X mzero ≡ X
mtadd-identityʳ ((a , b) , (c , d)) =
  cong4 (⊕-identityʳ a) (⊕-identityʳ b) (⊕-identityʳ c) (⊕-identityʳ d)

mtadd-swap4 : ∀ A B C D → mtadd (mtadd A B) (mtadd C D) ≡ mtadd (mtadd A C) (mtadd B D)
mtadd-swap4 ((a₁ , b₁) , (c₁ , d₁)) ((a₂ , b₂) , (c₂ , d₂))
             ((a₃ , b₃) , (c₃ , d₃)) ((a₄ , b₄) , (c₄ , d₄)) =
  cong4 (swap4-m a₁ a₂ a₃ a₄) (swap4-m b₁ b₂ b₃ b₄) (swap4-m c₁ c₂ c₃ c₄) (swap4-m d₁ d₂ d₃ d₄)
  where
    swap4-m : ∀ A B C D → (A ⊕ B) ⊕ (C ⊕ D) ≡ (A ⊕ C) ⊕ (B ⊕ D)
    swap4-m A B C D =
      trans (sym (⊕-assoc (A ⊕ B) C D))
        (trans (cong (λ u → u ⊕ D) (⊕-assoc A B C))
          (trans (cong (λ u → (A ⊕ u) ⊕ D) (⊕-comm B C))
            (trans (cong (λ u → u ⊕ D) (sym (⊕-assoc A C B)))
              (⊕-assoc (A ⊕ C) B D))))

neg-⊗-pull : ∀ A B → (negate A) ⊗ B ≡ negate (A ⊗ B)
neg-⊗-pull A B = sym (negate-⊗ A B)
neg-⊗-pullʳ : ∀ A B → A ⊗ (negate B) ≡ negate (A ⊗ B)
neg-⊗-pullʳ A B = trans (sym (negate-⊗-comm A B)) (sym (negate-⊗ A B))

swap4t : ∀ A B C D → (A ⊕ B) ⊕ (C ⊕ D) ≡ (A ⊕ C) ⊕ (B ⊕ D)
swap4t A B C D =
  trans (sym (⊕-assoc (A ⊕ B) C D))
    (trans (cong (λ u → u ⊕ D) (⊕-assoc A B C))
      (trans (cong (λ u → (A ⊕ u) ⊕ D) (⊕-comm B C))
        (trans (cong (λ u → u ⊕ D) (sym (⊕-assoc A C B)))
          (⊕-assoc (A ⊕ C) B D))))

mtmul-negˡ : ∀ X Y → mtmul (mtneg X) Y ≡ mtneg (mtmul X Y)
mtmul-negˡ ((a , b) , (c , d)) ((e , f) , (g , h)) =
  cong4
    (trans (cong₂ _⊕_ (neg-⊗-pull a e) (neg-⊗-pull b g)) (sym (negate-⊕ (a ⊗ e) (b ⊗ g))))
    (trans (cong₂ _⊕_ (neg-⊗-pull a f) (neg-⊗-pull b h)) (sym (negate-⊕ (a ⊗ f) (b ⊗ h))))
    (trans (cong₂ _⊕_ (neg-⊗-pull c e) (neg-⊗-pull d g)) (sym (negate-⊕ (c ⊗ e) (d ⊗ g))))
    (trans (cong₂ _⊕_ (neg-⊗-pull c f) (neg-⊗-pull d h)) (sym (negate-⊕ (c ⊗ f) (d ⊗ h))))

mtmul-negʳ : ∀ X Y → mtmul X (mtneg Y) ≡ mtneg (mtmul X Y)
mtmul-negʳ ((a , b) , (c , d)) ((e , f) , (g , h)) =
  cong4
    (trans (cong₂ _⊕_ (neg-⊗-pullʳ a e) (neg-⊗-pullʳ b g)) (sym (negate-⊕ (a ⊗ e) (b ⊗ g))))
    (trans (cong₂ _⊕_ (neg-⊗-pullʳ a f) (neg-⊗-pullʳ b h)) (sym (negate-⊕ (a ⊗ f) (b ⊗ h))))
    (trans (cong₂ _⊕_ (neg-⊗-pullʳ c e) (neg-⊗-pullʳ d g)) (sym (negate-⊕ (c ⊗ e) (d ⊗ g))))
    (trans (cong₂ _⊕_ (neg-⊗-pullʳ c f) (neg-⊗-pullʳ d h)) (sym (negate-⊕ (c ⊗ f) (d ⊗ h))))

mtmul-distribʳ : ∀ X Y Z → mtmul (mtadd X Y) Z ≡ mtadd (mtmul X Z) (mtmul Y Z)
mtmul-distribʳ ((a , b) , (c , d)) ((e , f) , (g , h)) ((i , j) , (k , l)) =
  cong4
    (trans (cong₂ _⊕_ (⊗-distribʳ-⊕ a e i) (⊗-distribʳ-⊕ b f k))
           (sym (swap4t (a ⊗ i) (b ⊗ k) (e ⊗ i) (f ⊗ k))))
    (trans (cong₂ _⊕_ (⊗-distribʳ-⊕ a e j) (⊗-distribʳ-⊕ b f l))
           (sym (swap4t (a ⊗ j) (b ⊗ l) (e ⊗ j) (f ⊗ l))))
    (trans (cong₂ _⊕_ (⊗-distribʳ-⊕ c g i) (⊗-distribʳ-⊕ d h k))
           (sym (swap4t (c ⊗ i) (d ⊗ k) (g ⊗ i) (h ⊗ k))))
    (trans (cong₂ _⊕_ (⊗-distribʳ-⊕ c g j) (⊗-distribʳ-⊕ d h l))
           (sym (swap4t (c ⊗ j) (d ⊗ l) (g ⊗ j) (h ⊗ l))))

mtmul-distribˡ : ∀ X Y Z → mtmul X (mtadd Y Z) ≡ mtadd (mtmul X Y) (mtmul X Z)
mtmul-distribˡ ((a , b) , (c , d)) ((e , f) , (g , h)) ((i , j) , (k , l)) =
  cong4
    (trans (cong₂ _⊕_ (⊗-distribˡ-⊕ a e i) (⊗-distribˡ-⊕ b g k))
           (sym (swap4t (a ⊗ e) (b ⊗ g) (a ⊗ i) (b ⊗ k))))
    (trans (cong₂ _⊕_ (⊗-distribˡ-⊕ a f j) (⊗-distribˡ-⊕ b h l))
           (sym (swap4t (a ⊗ f) (b ⊗ h) (a ⊗ j) (b ⊗ l))))
    (trans (cong₂ _⊕_ (⊗-distribˡ-⊕ c e i) (⊗-distribˡ-⊕ d g k))
           (sym (swap4t (c ⊗ e) (d ⊗ g) (c ⊗ i) (d ⊗ k))))
    (trans (cong₂ _⊕_ (⊗-distribˡ-⊕ c f j) (⊗-distribˡ-⊕ d h l))
           (sym (swap4t (c ⊗ f) (d ⊗ h) (c ⊗ j) (d ⊗ l))))

mtneg-add : ∀ X Y → mtneg (mtadd X Y) ≡ mtadd (mtneg X) (mtneg Y)
mtneg-add ((a , b) , (c , d)) ((e , f) , (g , h)) =
  cong4 (negate-⊕ a e) (negate-⊕ b f) (negate-⊕ c g) (negate-⊕ d h)

mtneg-involutive : ∀ X → mtneg (mtneg X) ≡ X
mtneg-involutive ((a , b) , (c , d)) = cong4 (negate² a) (negate² b) (negate² c) (negate² d)

-- br X Y = mtmul X Y + mtneg (mtmul Y X) (定义)
br-eq : ∀ X Y → br X Y ≡ mtadd (mtmul X Y) (mtneg (mtmul Y X))
br-eq X Y = refl

-- ★ asym: 用 swap4 + inverseʳ ★
asym : ∀ X Y → mtadd (br X Y) (br Y X) ≡ mzero
asym X Y = begin
  mtadd (br X Y) (br Y X)
    ≡⟨⟩
  mtadd (mtadd (mtmul X Y) (mtneg (mtmul Y X)))
        (mtadd (mtmul Y X) (mtneg (mtmul X Y)))
    ≡⟨ mtadd-swap4 (mtmul X Y) (mtneg (mtmul Y X)) (mtmul Y X) (mtneg (mtmul X Y)) ⟩
  mtadd (mtadd (mtmul X Y) (mtmul Y X))
        (mtadd (mtneg (mtmul Y X)) (mtneg (mtmul X Y)))
    ≡⟨ cong₂ (λ (u v : Mat2T) → mtadd u v) refl
             (sym (mtneg-add (mtmul Y X) (mtmul X Y))) ⟩
  mtadd (mtadd (mtmul X Y) (mtmul Y X)) (mtneg (mtadd (mtmul Y X) (mtmul X Y)))
    ≡⟨ cong₂ (λ (u v : Mat2T) → mtadd u v)
             (mtadd-comm (mtmul X Y) (mtmul Y X)) refl ⟩
  mtadd (mtadd (mtmul Y X) (mtmul X Y)) (mtneg (mtadd (mtmul Y X) (mtmul X Y)))
    ≡⟨ mtadd-inverse (mtadd (mtmul Y X) (mtmul X Y)) ⟩
  mzero
  ∎

--------------------------------------------------------------------------------
-- Jacobi: [[X,Y],Z] 展开 (构造性路线, 基础设施见 §asym)
--------------------------------------------------------------------------------

-- ★ 关键: 用显式 lambda 展开 br (避免 br 在抽象参数上卡住) ★
br-mtmul : ∀ X Y Z → mtmul (br X Y) Z ≡ mtadd (mtmul (mtmul X Y) Z) (mtneg (mtmul (mtmul Y X) Z))
br-mtmul X Y Z = begin
  mtmul (mtadd (mtmul X Y) (mtneg (mtmul Y X))) Z
    ≡⟨ mtmul-distribʳ (mtmul X Y) (mtneg (mtmul Y X)) Z ⟩
  mtadd (mtmul (mtmul X Y) Z) (mtmul (mtneg (mtmul Y X)) Z)
    ≡⟨ cong₂ (λ (u v : Mat2T) → mtadd u v) refl (mtmul-negˡ (mtmul Y X) Z) ⟩
  mtadd (mtmul (mtmul X Y) Z) (mtneg (mtmul (mtmul Y X) Z))
  ∎

br-exp : ∀ X Y → br X Y ≡ mtadd (mtmul X Y) (mtneg (mtmul Y X))
br-exp X Y = refl

-- [[X,Y],Z] 四项展开
-- 策略: 把 br (br X Y) Z 用显式 lambda 写成 mtadd (mtmul · Z) (mtneg (mtmul Z ·)),
-- 再对 · 替换为 br X Y 的展开式
br-br : ∀ X Y Z →
  br (br X Y) Z ≡
  mtadd (mtadd (mtmul (mtmul X Y) Z) (mtneg (mtmul (mtmul Y X) Z)))
        (mtadd (mtneg (mtmul Z (mtmul X Y))) (mtmul Z (mtmul Y X)))
br-br X Y Z = begin
  mtadd (mtmul (mtadd (mtmul X Y) (mtneg (mtmul Y X))) Z)
        (mtneg (mtmul Z (mtadd (mtmul X Y) (mtneg (mtmul Y X)))))
    ≡⟨ cong₂ (λ (u v : Mat2T) → mtadd u v)
             (mtmul-distribʳ (mtmul X Y) (mtneg (mtmul Y X)) Z)
             (cong mtneg (mtmul-distribˡ Z (mtmul X Y) (mtneg (mtmul Y X)))) ⟩
  mtadd (mtadd (mtmul (mtmul X Y) Z) (mtmul (mtneg (mtmul Y X)) Z))
        (mtneg (mtadd (mtmul Z (mtmul X Y)) (mtmul Z (mtneg (mtmul Y X)))))
    ≡⟨ cong (λ (u : Mat2T) → mtadd u (mtneg (mtadd (mtmul Z (mtmul X Y)) (mtmul Z (mtneg (mtmul Y X))))))
             (cong₂ (λ (u v : Mat2T) → mtadd u v) refl (mtmul-negˡ (mtmul Y X) Z)) ⟩
  mtadd (mtadd (mtmul (mtmul X Y) Z) (mtneg (mtmul (mtmul Y X) Z)))
        (mtneg (mtadd (mtmul Z (mtmul X Y)) (mtmul Z (mtneg (mtmul Y X)))))
    ≡⟨ cong (λ (u : Mat2T) → mtadd (mtadd (mtmul (mtmul X Y) Z) (mtneg (mtmul (mtmul Y X) Z)))
                                    (mtneg u))
             (cong₂ (λ (u v : Mat2T) → mtadd u v) refl (mtmul-negʳ Z (mtmul Y X))) ⟩
  mtadd (mtadd (mtmul (mtmul X Y) Z) (mtneg (mtmul (mtmul Y X) Z)))
        (mtneg (mtadd (mtmul Z (mtmul X Y)) (mtneg (mtmul Z (mtmul Y X)))))
    ≡⟨ cong₂ (λ (u v : Mat2T) → mtadd u v) refl
             (mtneg-add (mtmul Z (mtmul X Y)) (mtneg (mtmul Z (mtmul Y X)))) ⟩
  mtadd (mtadd (mtmul (mtmul X Y) Z) (mtneg (mtmul (mtmul Y X) Z)))
        (mtadd (mtneg (mtmul Z (mtmul X Y))) (mtneg (mtneg (mtmul Z (mtmul Y X)))))
    ≡⟨ cong (λ (u : Mat2T) → mtadd (mtadd (mtmul (mtmul X Y) Z) (mtneg (mtmul (mtmul Y X) Z)))
                                    (mtadd (mtneg (mtmul Z (mtmul X Y))) u))
             (mtneg-involutive (mtmul Z (mtmul Y X))) ⟩
  mtadd (mtadd (mtmul (mtmul X Y) Z) (mtneg (mtmul (mtmul Y X) Z)))
        (mtadd (mtneg (mtmul Z (mtmul X Y))) (mtmul Z (mtmul Y X)))
  ∎

--------------------------------------------------------------------------------
-- Jacobi: [[X,Y],Z] + [[Y,Z],X] + [[Z,X],Y] = 0
--
-- 展开后 12 项, 每项 (循环置换) 出现两次且符号相反
-- 关键重排: 用 mtadd-comm/assoc 把三项按 XYZ/YXZ/ZXY/ZYX 归类相消
--------------------------------------------------------------------------------

-- 循环展开 (Y,Z,X) 与 (Z,X,Y)
br-br-YZX : ∀ X Y Z →
  br (br Y Z) X ≡
  mtadd (mtadd (mtmul (mtmul Y Z) X) (mtneg (mtmul (mtmul Z Y) X)))
        (mtadd (mtneg (mtmul X (mtmul Y Z))) (mtmul X (mtmul Z Y)))
br-br-YZX X Y Z = br-br Y Z X

br-br-ZXY : ∀ X Y Z →
  br (br Z X) Y ≡
  mtadd (mtadd (mtmul (mtmul Z X) Y) (mtneg (mtmul (mtmul X Z) Y)))
        (mtadd (mtneg (mtmul Y (mtmul Z X))) (mtmul Y (mtmul X Z)))
br-br-ZXY X Y Z = br-br Z X Y

-- 关键: 用结合律把所有项规范为 ((·) ·) · 形式, 再按单项配对
-- (mtmul X Y) Z = X (Y Z), 故六项循环两两相消
mtmul-assoc3 : ∀ X Y Z → mtmul (mtmul X Y) Z ≡ mtmul X (mtmul Y Z)
mtmul-assoc3 ((a , b) , (c , d)) ((e , f) , (g , h)) ((i , j) , (k , l)) =
  cong4 c0 c1 c2 c3
  where
    c0 : ((((a ⊗ e) ⊕ (b ⊗ g)) ⊗ i) ⊕ (((a ⊗ f) ⊕ (b ⊗ h)) ⊗ k))
       ≡ ((a ⊗ ((e ⊗ i) ⊕ (f ⊗ k))) ⊕ (b ⊗ ((g ⊗ i) ⊕ (h ⊗ k))))
    c0 = begin
      ((((a ⊗ e) ⊕ (b ⊗ g)) ⊗ i) ⊕ (((a ⊗ f) ⊕ (b ⊗ h)) ⊗ k))
        ≡⟨ cong₂ _⊕_ (⊗-distribʳ-⊕ (a ⊗ e) (b ⊗ g) i) (⊗-distribʳ-⊕ (a ⊗ f) (b ⊗ h) k) ⟩
      (((a ⊗ e) ⊗ i) ⊕ ((b ⊗ g) ⊗ i)) ⊕ (((a ⊗ f) ⊗ k) ⊕ ((b ⊗ h) ⊗ k))
        ≡⟨ cong₂ _⊕_ (cong₂ _⊕_ (⊗-assoc a e i) (⊗-assoc b g i))
                     (cong₂ _⊕_ (⊗-assoc a f k) (⊗-assoc b h k)) ⟩
      ((a ⊗ (e ⊗ i)) ⊕ (b ⊗ (g ⊗ i))) ⊕ ((a ⊗ (f ⊗ k)) ⊕ (b ⊗ (h ⊗ k)))
        ≡⟨ swap4t (a ⊗ (e ⊗ i)) (b ⊗ (g ⊗ i)) (a ⊗ (f ⊗ k)) (b ⊗ (h ⊗ k)) ⟩
      ((a ⊗ (e ⊗ i)) ⊕ (a ⊗ (f ⊗ k))) ⊕ ((b ⊗ (g ⊗ i)) ⊕ (b ⊗ (h ⊗ k)))
        ≡⟨ cong₂ _⊕_ (sym (⊗-distribˡ-⊕ a (e ⊗ i) (f ⊗ k))) (sym (⊗-distribˡ-⊕ b (g ⊗ i) (h ⊗ k))) ⟩
      (a ⊗ ((e ⊗ i) ⊕ (f ⊗ k))) ⊕ (b ⊗ ((g ⊗ i) ⊕ (h ⊗ k)))
      ∎
    c1 : ((((a ⊗ e) ⊕ (b ⊗ g)) ⊗ j) ⊕ (((a ⊗ f) ⊕ (b ⊗ h)) ⊗ l))
       ≡ ((a ⊗ ((e ⊗ j) ⊕ (f ⊗ l))) ⊕ (b ⊗ ((g ⊗ j) ⊕ (h ⊗ l))))
    c1 = begin
      ((((a ⊗ e) ⊕ (b ⊗ g)) ⊗ j) ⊕ (((a ⊗ f) ⊕ (b ⊗ h)) ⊗ l))
        ≡⟨ cong₂ _⊕_ (⊗-distribʳ-⊕ (a ⊗ e) (b ⊗ g) j) (⊗-distribʳ-⊕ (a ⊗ f) (b ⊗ h) l) ⟩
      (((a ⊗ e) ⊗ j) ⊕ ((b ⊗ g) ⊗ j)) ⊕ (((a ⊗ f) ⊗ l) ⊕ ((b ⊗ h) ⊗ l))
        ≡⟨ cong₂ _⊕_ (cong₂ _⊕_ (⊗-assoc a e j) (⊗-assoc b g j))
                     (cong₂ _⊕_ (⊗-assoc a f l) (⊗-assoc b h l)) ⟩
      ((a ⊗ (e ⊗ j)) ⊕ (b ⊗ (g ⊗ j))) ⊕ ((a ⊗ (f ⊗ l)) ⊕ (b ⊗ (h ⊗ l)))
        ≡⟨ swap4t (a ⊗ (e ⊗ j)) (b ⊗ (g ⊗ j)) (a ⊗ (f ⊗ l)) (b ⊗ (h ⊗ l)) ⟩
      ((a ⊗ (e ⊗ j)) ⊕ (a ⊗ (f ⊗ l))) ⊕ ((b ⊗ (g ⊗ j)) ⊕ (b ⊗ (h ⊗ l)))
        ≡⟨ cong₂ _⊕_ (sym (⊗-distribˡ-⊕ a (e ⊗ j) (f ⊗ l))) (sym (⊗-distribˡ-⊕ b (g ⊗ j) (h ⊗ l))) ⟩
      (a ⊗ ((e ⊗ j) ⊕ (f ⊗ l))) ⊕ (b ⊗ ((g ⊗ j) ⊕ (h ⊗ l)))
      ∎
    c2 : ((((c ⊗ e) ⊕ (d ⊗ g)) ⊗ i) ⊕ (((c ⊗ f) ⊕ (d ⊗ h)) ⊗ k))
       ≡ ((c ⊗ ((e ⊗ i) ⊕ (f ⊗ k))) ⊕ (d ⊗ ((g ⊗ i) ⊕ (h ⊗ k))))
    c2 = begin
      ((((c ⊗ e) ⊕ (d ⊗ g)) ⊗ i) ⊕ (((c ⊗ f) ⊕ (d ⊗ h)) ⊗ k))
        ≡⟨ cong₂ _⊕_ (⊗-distribʳ-⊕ (c ⊗ e) (d ⊗ g) i) (⊗-distribʳ-⊕ (c ⊗ f) (d ⊗ h) k) ⟩
      (((c ⊗ e) ⊗ i) ⊕ ((d ⊗ g) ⊗ i)) ⊕ (((c ⊗ f) ⊗ k) ⊕ ((d ⊗ h) ⊗ k))
        ≡⟨ cong₂ _⊕_ (cong₂ _⊕_ (⊗-assoc c e i) (⊗-assoc d g i))
                     (cong₂ _⊕_ (⊗-assoc c f k) (⊗-assoc d h k)) ⟩
      ((c ⊗ (e ⊗ i)) ⊕ (d ⊗ (g ⊗ i))) ⊕ ((c ⊗ (f ⊗ k)) ⊕ (d ⊗ (h ⊗ k)))
        ≡⟨ swap4t (c ⊗ (e ⊗ i)) (d ⊗ (g ⊗ i)) (c ⊗ (f ⊗ k)) (d ⊗ (h ⊗ k)) ⟩
      ((c ⊗ (e ⊗ i)) ⊕ (c ⊗ (f ⊗ k))) ⊕ ((d ⊗ (g ⊗ i)) ⊕ (d ⊗ (h ⊗ k)))
        ≡⟨ cong₂ _⊕_ (sym (⊗-distribˡ-⊕ c (e ⊗ i) (f ⊗ k))) (sym (⊗-distribˡ-⊕ d (g ⊗ i) (h ⊗ k))) ⟩
      (c ⊗ ((e ⊗ i) ⊕ (f ⊗ k))) ⊕ (d ⊗ ((g ⊗ i) ⊕ (h ⊗ k)))
      ∎
    c3 : ((((c ⊗ e) ⊕ (d ⊗ g)) ⊗ j) ⊕ (((c ⊗ f) ⊕ (d ⊗ h)) ⊗ l))
       ≡ ((c ⊗ ((e ⊗ j) ⊕ (f ⊗ l))) ⊕ (d ⊗ ((g ⊗ j) ⊕ (h ⊗ l))))
    c3 = begin
      ((((c ⊗ e) ⊕ (d ⊗ g)) ⊗ j) ⊕ (((c ⊗ f) ⊕ (d ⊗ h)) ⊗ l))
        ≡⟨ cong₂ _⊕_ (⊗-distribʳ-⊕ (c ⊗ e) (d ⊗ g) j) (⊗-distribʳ-⊕ (c ⊗ f) (d ⊗ h) l) ⟩
      (((c ⊗ e) ⊗ j) ⊕ ((d ⊗ g) ⊗ j)) ⊕ (((c ⊗ f) ⊗ l) ⊕ ((d ⊗ h) ⊗ l))
        ≡⟨ cong₂ _⊕_ (cong₂ _⊕_ (⊗-assoc c e j) (⊗-assoc d g j))
                     (cong₂ _⊕_ (⊗-assoc c f l) (⊗-assoc d h l)) ⟩
      ((c ⊗ (e ⊗ j)) ⊕ (d ⊗ (g ⊗ j))) ⊕ ((c ⊗ (f ⊗ l)) ⊕ (d ⊗ (h ⊗ l)))
        ≡⟨ swap4t (c ⊗ (e ⊗ j)) (d ⊗ (g ⊗ j)) (c ⊗ (f ⊗ l)) (d ⊗ (h ⊗ l)) ⟩
      ((c ⊗ (e ⊗ j)) ⊕ (c ⊗ (f ⊗ l))) ⊕ ((d ⊗ (g ⊗ j)) ⊕ (d ⊗ (h ⊗ l)))
        ≡⟨ cong₂ _⊕_ (sym (⊗-distribˡ-⊕ c (e ⊗ j) (f ⊗ l))) (sym (⊗-distribˡ-⊕ d (g ⊗ j) (h ⊗ l))) ⟩
      (c ⊗ ((e ⊗ j) ⊕ (f ⊗ l))) ⊕ (d ⊗ ((g ⊗ j) ⊕ (h ⊗ l)))
      ∎

-- ★ Jacobi 恒等式 ★
-- 展开后: [[X,Y],Z] 的 4 项 + [[Y,Z],X] 的 4 项 + [[Z,X],Y] 的 4 项
-- 用结合律规范后, 12 项按 (XYZ, YXZ, ZXY, ZYX) 四类, 每类 3 项
-- 其中每类恰有一对互为负元, 加上第三项自消 (char 3 结构)
--
-- 简化策略: 直接验证 6 个"基单项"的循环配对
-- 定义 jacobi-sum 并按项分组
jacobi-sum : Mat2T → Mat2T → Mat2T → Mat2T
jacobi-sum X Y Z =
  mtadd (br (br X Y) Z) (mtadd (br (br Y Z) X) (br (br Z X) Y))

-- 三个展开式代入
jacobi-expand : ∀ X Y Z →
  jacobi-sum X Y Z ≡
  mtadd (mtadd (mtadd (mtmul (mtmul X Y) Z) (mtneg (mtmul (mtmul Y X) Z)))
               (mtadd (mtneg (mtmul Z (mtmul X Y))) (mtmul Z (mtmul Y X))))
        (mtadd (mtadd (mtadd (mtmul (mtmul Y Z) X) (mtneg (mtmul (mtmul Z Y) X)))
                      (mtadd (mtneg (mtmul X (mtmul Y Z))) (mtmul X (mtmul Z Y))))
               (mtadd (mtadd (mtmul (mtmul Z X) Y) (mtneg (mtmul (mtmul X Z) Y)))
                      (mtadd (mtneg (mtmul Y (mtmul Z X))) (mtmul Y (mtmul X Z)))))
jacobi-expand X Y Z = begin
  mtadd (br (br X Y) Z) (mtadd (br (br Y Z) X) (br (br Z X) Y))
    ≡⟨ cong₂ (λ (u v : Mat2T) → mtadd u v) (br-br X Y Z)
             (cong₂ (λ (u v : Mat2T) → mtadd u v) (br-br Y Z X) (br-br Z X Y)) ⟩
  mtadd (mtadd (mtadd (mtmul (mtmul X Y) Z) (mtneg (mtmul (mtmul Y X) Z)))
               (mtadd (mtneg (mtmul Z (mtmul X Y))) (mtmul Z (mtmul Y X))))
        (mtadd (mtadd (mtadd (mtmul (mtmul Y Z) X) (mtneg (mtmul (mtmul Z Y) X)))
                      (mtadd (mtneg (mtmul X (mtmul Y Z))) (mtmul X (mtmul Z Y))))
               (mtadd (mtadd (mtmul (mtmul Z X) Y) (mtneg (mtmul (mtmul X Z) Y)))
                      (mtadd (mtneg (mtmul Y (mtmul Z X))) (mtmul Y (mtmul X Z)))))
  ∎

idp : ∀ {A : Set} (x : A) → x ≡ x
idp x = refl

--------------------------------------------------------------------------------
-- 步骤 1: br X (br Y Z) 的展开 (既有 br-br 只覆盖左嵌套 br (br X Y) Z)
--------------------------------------------------------------------------------

br-brʳ : ∀ X Y Z →
  br X (br Y Z) ≡
  mtadd (mtadd (mtmul X (mtmul Y Z)) (mtmul X (mtneg (mtmul Z Y))))
        (mtneg (mtadd (mtmul (mtmul Y Z) X) (mtmul (mtneg (mtmul Z Y)) X)))
br-brʳ X Y Z =
  cong₂ (λ (u v : Mat2T) → mtadd u v)
        (mtmul-distribˡ X (mtmul Y Z) (mtneg (mtmul Z Y)))
        (cong mtneg (mtmul-distribʳ (mtmul Y Z) (mtneg (mtmul Z Y)) X))

br-brʳ-norm : ∀ X Y Z →
  br X (br Y Z) ≡
  mtadd (mtadd (mtmul X (mtmul Y Z)) (mtneg (mtmul X (mtmul Z Y))))
        (mtadd (mtneg (mtmul (mtmul Y Z) X)) (mtmul (mtmul Z Y) X))
br-brʳ-norm X Y Z =
  trans (br-brʳ X Y Z)
    (cong₂ (λ (u v : Mat2T) → mtadd (mtadd (mtmul X (mtmul Y Z)) u) v)
           (mtmul-negʳ X (mtmul Z Y))
           neg-part)
  where
    neg-part : mtneg (mtadd (mtmul (mtmul Y Z) X) (mtmul (mtneg (mtmul Z Y)) X))
             ≡ mtadd (mtneg (mtmul (mtmul Y Z) X)) (mtmul (mtmul Z Y) X)
    neg-part =
      trans (mtneg-add (mtmul (mtmul Y Z) X) (mtmul (mtneg (mtmul Z Y)) X))
            (cong (mtadd (mtneg (mtmul (mtmul Y Z) X)))
                  (trans (cong mtneg (mtmul-negˡ (mtmul Z Y) X))
                         (mtneg-involutive (mtmul (mtmul Z Y) X))))

--------------------------------------------------------------------------------
-- 步骤 2: 两侧嵌套括号的归一化版 (四项全写成规范形)
--------------------------------------------------------------------------------

-- 左嵌套: br (br X Y) Z 的四项 = X(YZ), −Y(XZ), −Z(XY), (ZY)X
br-br-norm : ∀ X Y Z → br (br X Y) Z ≡
  mtadd (mtadd (mtmul X (mtmul Y Z)) (mtneg (mtmul Y (mtmul X Z))))
        (mtadd (mtneg (mtmul Z (mtmul X Y))) (mtmul (mtmul Z Y) X))
br-br-norm X Y Z =
  trans (br-br X Y Z)
    (cong₂ (λ (u v : Mat2T) → mtadd u v)
           (cong₂ (λ (u v : Mat2T) → mtadd u v)
                  (mtmul-assoc3 X Y Z)
                  (cong mtneg (mtmul-assoc3 Y X Z)))
           (cong (mtadd (mtneg (mtmul Z (mtmul X Y)))) (sym (mtmul-assoc3 Z Y X))))

-- 右嵌套: br Y (br X Z) 的四项 = Y(XZ), −(YZ)X, −X(ZY), Z(XY)
br-brʳ-norm3 : ∀ X Y Z → br Y (br X Z) ≡
  mtadd (mtadd (mtmul Y (mtmul X Z)) (mtneg (mtmul (mtmul Y Z) X)))
        (mtadd (mtneg (mtmul X (mtmul Z Y))) (mtmul Z (mtmul X Y)))
br-brʳ-norm3 X Y Z =
  trans (br-brʳ-norm Y X Z)
    (cong₂ (λ (u v : Mat2T) → mtadd u v)
           (cong (mtadd (mtmul Y (mtmul X Z)))
                 (cong mtneg (sym (mtmul-assoc3 Y Z X))))
           (cong₂ (λ (u v : Mat2T) → mtadd u v)
                  (cong mtneg (mtmul-assoc3 X Z Y))
                  (mtmul-assoc3 Z X Y)))

-- 一对相消项 + 余项 ≡ 余项    (mtneg A + A) + B ≡ B
cancel-pair' : ∀ A B → mtadd (mtadd (mtneg A) A) B ≡ B
cancel-pair' A B =
  trans (cong (λ u → mtadd u B) (trans (mtadd-comm (mtneg A) A) (mtadd-inverse A)))
        (mtadd-identityˡ B)

-- 同上, 但头部是 A + (−A)
cancel-pair : ∀ A B → mtadd (mtadd A (mtneg A)) B ≡ B
cancel-pair A B =
  trans (cong (λ u → mtadd u B) (mtadd-inverse A)) (mtadd-identityˡ B)

--------------------------------------------------------------------------------
-- 步骤 3: 推导律 [[X,Y],Z] + [Y,[X,Z]] ≡ [X,[Y,Z]]
--   归一化后 8 项: (p1+p2)+(p3+p4) + (q1+q2)+(q3+q4)
--     p2 = mtneg q1 与 p3 = mtneg q4 恰好各成一对 (定义层相等)
--   弹出: swap4 把 (t + X) + (−t + Y) 变成 (t + −t) + (X + Y), 再用 cancel-pair'
--   余项 (p4+p1)+(q3+q2) 经 swap4 + comm 整理为 (p1+q3)+(q2+p4)
--   而 (p1+q3)+(q2+p4) 恰是 br X (br Y Z) 的 br-brʳ-norm 展开形 ⇒ 末步 sym
--------------------------------------------------------------------------------

br-deriv : ∀ X Y Z → mtadd (br (br X Y) Z) (br Y (br X Z)) ≡ br X (br Y Z)
br-deriv X Y Z =
  trans vex1
   (trans (cong (λ u → mtadd u vQ) vm1)
    (trans (cong (mtadd (mtadd p2 vX1)) vm2)
     (trans vm3
      (trans (cong (λ u → mtadd u vY1) vm4)
       (trans (cong (mtadd (mtadd p3 vX2)) vm5)
        (trans vm6
         (trans vm7 (sym (br-brʳ-norm X Y Z)))))))))
  where
    p1 = mtmul X (mtmul Y Z)
    p2 = mtneg (mtmul Y (mtmul X Z))
    p3 = mtneg (mtmul Z (mtmul X Y))
    p4 = mtmul (mtmul Z Y) X
    q1 = mtmul Y (mtmul X Z)
    q2 = mtneg (mtmul (mtmul Y Z) X)
    q3 = mtneg (mtmul X (mtmul Z Y))
    q4 = mtmul Z (mtmul X Y)
    vP  = mtadd (mtadd p1 p2) (mtadd p3 p4)
    vQ  = mtadd (mtadd q1 q2) (mtadd q3 q4)
    vX1 = mtadd p1 (mtadd p3 p4)
    vX2 = mtadd p4 p1
    vY1 = mtadd q2 (mtadd q3 q4)
    vY2 = mtadd q3 q2

    vex1 = cong₂ (λ (u v : Mat2T) → mtadd u v)
                 (br-br-norm X Y Z) (br-brʳ-norm3 X Y Z)

    -- vP ≡ p2 + vX1
    vm1 = trans (cong (λ u → mtadd u (mtadd p3 p4)) (mtadd-comm p1 p2))
                (mtadd-assoc p2 p1 (mtadd p3 p4))
    -- vQ ≡ q1 + vY1
    vm2 = mtadd-assoc q1 q2 (mtadd q3 q4)
    -- 弹出第一对 (p2, q1)
    vm3 = trans (mtadd-swap4 p2 vX1 q1 vY1) (cancel-pair' q1 (mtadd vX1 vY1))
    -- vX1 ≡ p3 + vX2
    vm4 = trans (mtadd-comm p1 (mtadd p3 p4)) (mtadd-assoc p3 p4 p1)
    -- vY1 ≡ q4 + vY2
    vm5 = trans (cong (mtadd q2) (mtadd-comm q3 q4))
                (trans (mtadd-comm q2 (mtadd q4 q3)) (mtadd-assoc q4 q3 q2))
    -- 弹出第二对 (p3, q4)
    vm6 = trans (mtadd-swap4 p3 vX2 q4 vY2) (cancel-pair' q4 (mtadd vX2 vY2))
    -- 余项 (p4+p1)+(q3+q2) → (p1+q3)+(q2+p4)
    vm7 = trans (cong (λ u → mtadd u (mtadd q3 q2)) (mtadd-comm p4 p1))
                (trans (mtadd-swap4 p1 p4 q3 q2)
                       (cong (mtadd (mtadd p1 q3)) (mtadd-comm p4 q2)))

--------------------------------------------------------------------------------
-- 步骤 4: 组装 Jacobi 所需的三个辅助件
--------------------------------------------------------------------------------

-- 从 A + B ≡ C 得 A ≡ C + (−B)
from-add : ∀ A B C → mtadd A B ≡ C → A ≡ mtadd C (mtneg B)
from-add A B C h =
  trans (sym (mtadd-identityʳ A))
   (trans (cong (mtadd A) (sym (mtadd-inverse B)))
    (trans (sym (mtadd-assoc A B (mtneg B)))
           (cong (λ w → mtadd w (mtneg B)) h)))

-- 从 A + B ≡ mzero 得 A ≡ mtneg B
from-zero : ∀ A B → mtadd A B ≡ mzero → A ≡ mtneg B
from-zero A B h =
  trans (sym (mtadd-identityʳ A))
   (trans (cong (mtadd A) (sym (mtadd-inverse B)))
    (trans (sym (mtadd-assoc A B (mtneg B)))
     (trans (cong (λ w → mtadd w (mtneg B)) h) (mtadd-identityˡ (mtneg B)))))

-- 反称性: [X,Y] + [Y,X] ≡ mzero   (定义层展开后 = (t + −u) + (u + −t), 一对 swap4 即两对相消)
br-antisy : ∀ X Y → mtadd (br X Y) (br Y X) ≡ mzero
br-antisy X Y =
  trans (cong (λ a → mtadd a (mtadd (mtmul Y X) (mtneg (mtmul X Y))))
              (mtadd-comm (mtmul X Y) (mtneg (mtmul Y X))))
   (trans (mtadd-swap4 (mtneg (mtmul Y X)) (mtmul X Y)
                       (mtmul Y X) (mtneg (mtmul X Y)))
    (trans (cancel-pair' (mtmul Y X) (mtadd (mtmul X Y) (mtneg (mtmul X Y))))
           (mtadd-inverse (mtmul X Y))))

-- neg 线性 (两槽): br (mtneg X) Y ≡ mtneg (br X Y) 与 br X (mtneg Y) ≡ mtneg (br X Y)
br-negˡ : ∀ X Y → br (mtneg X) Y ≡ mtneg (br X Y)
br-negˡ X Y =
  trans (cong₂ (λ (u v : Mat2T) → mtadd u v)
               (mtmul-negˡ X Y)
               (cong mtneg (mtmul-negʳ Y X)))
        (sym (mtneg-add (mtmul X Y) (mtneg (mtmul Y X))))

br-negʳ : ∀ X Y → br X (mtneg Y) ≡ mtneg (br X Y)
br-negʳ X Y =
  trans (cong₂ (λ (u v : Mat2T) → mtadd u v)
               (mtmul-negʳ X Y)
               (cong mtneg (mtmul-negˡ Y X)))
        (sym (mtneg-add (mtmul X Y) (mtneg (mtmul Y X))))

--------------------------------------------------------------------------------
-- 步骤 5: **M9 层 Jacobi** —— jacobi-sum ≡ mzero (取代 729 条穷举子句)
--   记 A = [[X,Y],Z], B = [[Y,Z],X], C = [[Z,X],Y], C' = [X,[Y,Z]], B' = [Y,[X,Z]]
--   (1) br-deriv + from-add  ⇒ A ≡ C' + (−B')
--   (2) br-antisy + from-zero ⇒ B ≡ −C'
--   (3) br-antisy + br-negˡ + from-zero + mtneg-involutive ⇒ C ≡ B'
--   于是 A + (B + C) ≡ (C' + −B') + (−C' + B'), 一次 swap4 得 (C' + −C') + (−B' + B')
--   两对相消 ⇒ mzero
--------------------------------------------------------------------------------

jacobi-sum-zero : ∀ X Y Z → jacobi-sum X Y Z ≡ mzero
jacobi-sum-zero X Y Z =
  trans (cong₂ (λ (u v : Mat2T) → mtadd u v)
               hA
               (cong₂ (λ (u v : Mat2T) → mtadd u v) hB hC))
   (trans (mtadd-swap4 vC' (mtneg vB') (mtneg vC') vB')
    (trans (cancel-pair vC' (mtadd (mtneg vB') vB'))
           (trans (mtadd-comm (mtneg vB') vB') (mtadd-inverse vB'))))
  where
    vB' = br Y (br X Z)
    vC' = br X (br Y Z)

    -- (1) A ≡ C' + (−B')
    hA = from-add (br (br X Y) Z) vB' vC' (br-deriv X Y Z)
    -- (2) B ≡ −C'
    hB = from-zero (br (br Y Z) X) vC' (br-antisy (br Y Z) X)
    -- (3) C ≡ B'
    hC = trans (cong (λ w → br w Y) (from-zero (br Z X) (br X Z) (br-antisy Z X)))
         (trans (br-negˡ (br X Z) Y)
                (trans (cong mtneg (from-zero (br (br X Z) Y) vB' (br-antisy (br X Z) Y)))
                       (mtneg-involutive vB')))

--------------------------------------------------------------------------------
-- §M9. M9 层 Jacobi 的结构定理 (取代原 729 条穷举子句)
-- br X Y = XY − YX 是结合代数(矩阵环)的交换子, 其 Jacobi 恒等式由 mtmul 结合律推出,
-- 无需按 9³ = 729 个元素三元组穷举。核心技术「配对弹出」见 br-deriv 注释。
--------------------------------------------------------------------------------

jacobi : ∀ X Y Z → mtadd (br (brM X Y) (toMat Z)) (mtadd (br (brM Y Z) (toMat X)) (br (brM Z X) (toMat Y))) ≡ mzero
jacobi X Y Z = jacobi-sum-zero (toMat X) (toMat Y) (toMat Z)
