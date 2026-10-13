{-# OPTIONS --rewriting --guardedness #-}

-- | _PK11 —— A3-1 速赢检查点：Serre-in-Mat2 + 单节点正控 + E10 深度 2 判定
--
-- 数学背景：A3 报告钉实「截断商表示 ρ:T_d→Mat2 的提升 ⟺ Serre+Cartan 关系在
-- 生成元矩阵上成立」。本件对 _PK10 的具体矩阵对 (M0, M1) 执行该检查：
--   ① 一节点正控（sl₂ ⊂ gl₂(GF3)）：e=上幂零/f=下幂零/h=对角(1,−1) 满足
--      [h,e]=2e、[e,f]=h——机件自证；
--   ② E10 深度 2 检查点：E10 的 a₀₁=−1 ⇒ Serre 元=(ad e₀)²e₁（深度 2）；
--      在 (M0,M1) 上计算得 (ad M0)²M1 ≡ M1 ≢ 0M——**Serre 不成立**；
--   ③ 判定（主件）：lift-blocks——名义表示不可提升（SerreCheck2 违反）；
--   ④ 结构注（诚实边界）：2×2 维数上界装不下两节点切瓦莱六件组
--      ⇒ A3-2 重设计路线 = Mat4（两节点容量）或维持纯截断（边界句维持）。
--
-- 原则：全部矩阵逐分量 ⊗/⊕ 计算面（refl 定义层）；禁浮点；0 postulate。
--
-- 包含：negM · commM · hM/eM/fM · he-ctrl/ef-ctrl（正控）· serreInner/M1M0 ·
--       serreE01（深度 2 判定）· SerreCheck2/lift-blocks（主件）· 核对层

module _PK11 where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Nat.Properties using (0≢1+n)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; cong; trans)
open import Relation.Nullary using (¬_)
open import Sovereign.Base.Trit using (Trit; T₀; T₁; T₂; _⊕_; _⊗_; negate; tritToℕ)
open import _PK10

-- ────────────────────────────────────────────────────────────────────
-- §1 基础件：矩阵取负 + 交换子（Lie 括号离散形）
-- ────────────────────────────────────────────────────────────────────

-- 第三槽取值（M1 的 1 位——m10 场；第四槽 m11 两值皆 T₀ 无辨识力）
mat-c1 : Mat2 → Trit
mat-c1 (mk2 _ _ c _) = c

negM : Mat2 → Mat2
negM (mk2 a b c d) = mk2 (negate a) (negate b) (negate c) (negate d)

-- 逐项加法（Mat2 无内建 ⊕——Trit 的 ⊕ 是 F₂ 面；矩阵加法经 entries 承载）
plusM : Mat2 → Mat2 → Mat2
plusM (mk2 a b c d) (mk2 e f g h) =
  mk2 (a ⊕ e) (b ⊕ f) (c ⊕ g) (d ⊕ h)

-- Lie 括号：[x,y] = xy − yx（GF(3) 减 = 加 negate）
commM : Mat2 → Mat2 → Mat2
commM x y = plusM (x ⋆ y) (negM (y ⋆ x))

-- ────────────────────────────────────────────────────────────────────
-- §2 一节点正控：sl₂ ⊂ gl₂(GF(3))（机件自证）
--    e = 上幂零 [[0,1],[0,0]]；f = 下幂零（=M1）；h = diag(1,−1)
--    GF(3) 特征：[h,e]=2e（本征值 2≡−1 合法）、[e,f]=h
-- ────────────────────────────────────────────────────────────────────

eM : Mat2
eM = mk2 T₀ T₁ T₀ T₀

hM : Mat2
hM = mk2 T₁ T₀ T₀ T₂

-- 正控①：[h,e] = 2e（本征律）
he-ctrl : commM hM eM ≡ mk2 T₀ T₂ T₀ T₀
he-ctrl = refl

-- 正控②：[e,f] = h
ef-ctrl : commM eM M1 ≡ hM
ef-ctrl = refl

-- ────────────────────────────────────────────────────────────────────
-- §3 E10 深度 2 检查点（核心）：
--    a₀₁ = −1 ⇒ 1−a₀₁ = 2 ⇒ Serre 元 = (ad e₀)² e₁
--    在 _PK10 矩阵对 (M0, M1) 上逐步计算
-- ────────────────────────────────────────────────────────────────────

-- 内部量：M1·M0 ≡ M1（下幂零左乘投影的保守性）
M1M0 : M1 ⋆ M0 ≡ M1
M1M0 = refl

-- 内部量：M0·(2M1) ≡ 0M（上投影吞下半带——逐分量 T₀）
serreInner : M0 ⋆ negM M1 ≡ 0M
serreInner = refl

-- **深度 2 判定**：(ad M0)² M1 ≡ M1 ≢ 0M —— Serre 不成立
serreE01 : commM M0 (commM M0 M1) ≡ M1
serreE01 = refl

-- 非零判据（ℕ 侧辨识——(1,1) 分量 tritToℕ 1 ≢ 0）
m11-inj : M1 ≢ 0M
m11-inj p = 0≢1+n (sym (cong (λ M → tritToℕ (mat-c1 M)) p))

-- ────────────────────────────────────────────────────────────────────
-- §4 主件：提升阻断（名义表示的 Serre 校验违反）
--    SerreCheck2：两节点深度 2 校验谓词（a₀₁=−1 对应形）
--    lift-blocks：M0,M1 违反之 ⇒ 该名表示不可作为 U(g) 表示提升
-- ────────────────────────────────────────────────────────────────────

SerreCheck2 : Mat2 → Mat2 → Set
SerreCheck2 e₀ e₁ = commM e₀ (commM e₀ e₁) ≡ 0M

lift-blocks : ¬ (SerreCheck2 M0 M1)
lift-blocks p = m11-inj (trans serreE01 p)

-- 零型对照（A₃ 链实例：节点 2 ↦ 0M 的 Serre 深度 1 恒可满足）
serre-zero-type : commM M0 0M ≡ 0M
serre-zero-type = refl

-- ────────────────────────────────────────────────────────────────────
-- §5 核对层（值面 refl 级）
-- ────────────────────────────────────────────────────────────────────

check-negM : negM M1 ≡ mk2 T₀ T₀ T₂ T₀
check-negM = refl

check-serreMid : commM M0 M1 ≡ negM M1
check-serreMid = refl   -- 内层：M0⋆M1=0M ⊕ neg(M1⋆M0)=negM M1

-- ────────────────────────────────────────────────────────────────────
-- §6 边界层（立界注记——无空壳签名）
--    (i) 两节点切瓦莱在 gl₂(GF(3))（4 维）的结构性容量上界
--        （h₀,h₁,e₀,e₁,f₀,f₁ 关系挤出降维——一般形随 A3-2）
--    (ii) A3-2 重设计：Mat4（gl₄ ⊇ sl₂×sl₂ 容量）载体 + 保核重调
--        （ker-witness 元素须在新载体重构造——w* 的载体迁移非自动）
--    (iii) E10 本身不忠实（PBW+核元素）= 外部定理标签，边界句维持
-- ────────────────────────────────────────────────────────────────────
