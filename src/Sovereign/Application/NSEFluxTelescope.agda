{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Problem.NavierStokes.NSEFluxTelescope
-- O3 的物理判据（通量型）+ 首条定理：轴向循环净通量恒为零（离散散度/telescoping）
--
-- 背景: `NSE.O3.blowup-physical` 要求「给出**物理意义**上的离散爆聚判据,
--   并证明在该判据下离散演化不爆聚」。判据设计先过**可陈述性筛**（O2 线的教训:
--   先判陈述有无内容, 再谈证明）:
--
--   候选 A（无界增长型）: 爆聚 ⇔ 某 ℕ-值可观察量在演化中无界。
--     ✗ **已排除**（平凡）: `NSEBlowupBound` 已证任何经有限编码的可观察量都有界
--       （`fin-bounded` / `no-discrete-blowup`）——该判据永不触发, 无内容。
--   候选 B（峰值集中度型）: 爆聚 ⇔ 局部密度峰值的集中度加剧。
--     ✗ **在本基座上不可陈述**: 「峰值/大小」需要**序或范数**——GF(3) 无序
--       （这正是 `13-flt-analysis` 的 Archimedes 断层同款: 大小比较是序结构的定理）;
--       可用的两个替代都不合格: 范数 N 是**有损投影**（相位 4→1, `10-norm-collapse:11`）,
--       `phaseAmp` 只是相位的实部标记（不是密度序）。
--   候选 C（通量型, **本模块采纳**）: 爆聚 ⇔ 存在持续的**净流入**（某轴周期通量 ≠ 0）
--     使局部累积。→ 可陈述（纯 GF(3) 组合量）, 且**可证其单步恒不触发**。
--
-- 本模块定理（全部构造性, 0 postulate / 0 hole）:
--   §1 `cancel3`       : GF(3) 三段循环差分之和恒为 T₀（27 case 穷举）
--   §2 `axisFlux-zero` : **轴向循环净通量恒为 T₀**（离散 telescoping,
--                        靠 `shiftAt-cubed` 把第三点折回第一点 + `cancel3`）
--        `axisFlux-via-diffF`: 同型的 diffF 形式（与 `NSEOnT6.diffF` 定义性对齐）
--
-- 物理读法: 单步尺度上**不存在净流入**——任何「向一点持续灌注」的爆聚机制
--   在本离散基座上没有通量通道（每个 3-周期内的流入流出逐点配对相消）。
--
-- ⚠ 诚实边界（见 §3）: 本模块只封**通量型**判据的单步触发; 多步/耦合下的集中
--   （例如涡旋自持造成的长期再分布）**仍开放**——那需要总量守恒或支撑集单调性定理
--   （已登记为下一步, 不在本模块冒充）。
--
-- 依赖: Sovereign.Problem.NavierStokes.NSEOnT6（算子与 shiftAt-cubed）
--       Sovereign.Base.Trit（Trit 表与 negate）

module Sovereign.Problem.NavierStokes.NSEFluxTelescope where

open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; sym; trans; cong; module ≡-Reasoning)

open import Sovereign.Base.Trit using
  (Trit; T₀; T₁; T₂; _⊕_; negate; ⊕-assoc; ⊕-comm; ⊕-identityˡ)
open import Sovereign.Problem.NavierStokes.NSEOnT6 using (
  C3; Torus6; ScalarField; Field; shiftAt; shiftAt-cubed; diffF; div; nsStep; sum3)

open ≡-Reasoning

--------------------------------------------------------------------------------
-- §0. 配对弹出工具三件套（照 `docs/techniques/pair-popping.md` §3；本地副本
--      —— 与 `jac_Matrix` 自备 Trit 版 `⊕-swap4` 同例, 不拉入 Lie 依赖）
--------------------------------------------------------------------------------

-- 置换型: 2 项交换（技术文档 §3 表 `⊕-swap2`）
swap2 : ∀ x y z → x ⊕ (y ⊕ z) ≡ y ⊕ (x ⊕ z)
swap2 x y z =
  trans (sym (⊕-assoc x y z))
  (trans (cong (_⊕ z) (⊕-comm x y))
         (⊕-assoc y x z))

-- 相消型: 弹出后消（技术文档 §3 表 `cancel-pair` 与其头部反向变体, 两种都要）
plus-negate-zero : ∀ t → t ⊕ negate t ≡ T₀
plus-negate-zero T₀ = refl
plus-negate-zero T₁ = refl
plus-negate-zero T₂ = refl

negate-plus-zero : ∀ t → negate t ⊕ t ≡ T₀
negate-plus-zero T₀ = refl
negate-plus-zero T₁ = refl
negate-plus-zero T₂ = refl

cancel-pair : ∀ t z → (t ⊕ negate t) ⊕ z ≡ z
cancel-pair t z = trans (cong (_⊕ z) (plus-negate-zero t)) (⊕-identityˡ z)

cancel-pair' : ∀ t z → (negate t ⊕ t) ⊕ z ≡ z
cancel-pair' t z = trans (cong (_⊕ z) (negate-plus-zero t)) (⊕-identityˡ z)

-- 右缘形状的弹出（`t ⊕ (neg t ⊕ z)` / `neg t ⊕ (t ⊕ z)` —— swap2/相消型的常用后处理）
pop-pair : ∀ t z → t ⊕ (negate t ⊕ z) ≡ z
pop-pair t z = trans (sym (⊕-assoc t (negate t) z)) (cancel-pair t z)

pop-pair' : ∀ t z → negate t ⊕ (t ⊕ z) ≡ z
pop-pair' t z = trans (sym (⊕-assoc (negate t) t z)) (cancel-pair' t z)

--------------------------------------------------------------------------------
-- §1. GF(3) 三段循环差分之和恒为零 —— **配对弹出版**（原 27 条 refl 穷举已替换）
--
-- 判型（技术文档 §2）: 六原子 b/−a/c/−b/a/−c 含 **3 对相反数**（b/−b、c/−c、a/−a）
-- ⇒ **相消型**。结构 = 展平到右缘字（3 × assoc）→ 3 × `swap2` 把 −b 换到 b 旁
--   → 弹出 (b,−b) → 弹出 (a,−a)（`pop-pair'`）→ 弹出 (c,−c) ⇒ T₀。
-- **命题一字不改**（与穷举版同型）; 全程不对任何变量分情形。
--------------------------------------------------------------------------------

cancel3 : ∀ (a b c : Trit) →
  sum3 (b ⊕ negate a) (c ⊕ negate b) (a ⊕ negate c) ≡ T₀
cancel3 a b c = begin
    (b ⊕ negate a) ⊕ ((c ⊕ negate b) ⊕ ((a ⊕ negate c) ⊕ T₀))
  ≡⟨ flatten ⟩
    b ⊕ (negate a ⊕ (c ⊕ (negate b ⊕ (a ⊕ (negate c ⊕ T₀)))))
  ≡⟨ cong (b ⊕_) (swap2 (negate a) c (negate b ⊕ (a ⊕ (negate c ⊕ T₀)))) ⟩
    b ⊕ (c ⊕ (negate a ⊕ (negate b ⊕ (a ⊕ (negate c ⊕ T₀)))))
  ≡⟨ cong (b ⊕_) (cong (c ⊕_) (swap2 (negate a) (negate b) (a ⊕ (negate c ⊕ T₀)))) ⟩
    b ⊕ (c ⊕ (negate b ⊕ (negate a ⊕ (a ⊕ (negate c ⊕ T₀)))))
  ≡⟨ cong (b ⊕_) (swap2 c (negate b) (negate a ⊕ (a ⊕ (negate c ⊕ T₀)))) ⟩
    b ⊕ (negate b ⊕ (c ⊕ (negate a ⊕ (a ⊕ (negate c ⊕ T₀)))))
  ≡⟨ pop-pair b (c ⊕ (negate a ⊕ (a ⊕ (negate c ⊕ T₀)))) ⟩
    c ⊕ (negate a ⊕ (a ⊕ (negate c ⊕ T₀)))
  ≡⟨ cong (c ⊕_) (pop-pair' a (negate c ⊕ T₀)) ⟩
    c ⊕ (negate c ⊕ T₀)
  ≡⟨ pop-pair c T₀ ⟩
    T₀
  ∎
  where
    flatten :
      (b ⊕ negate a) ⊕ ((c ⊕ negate b) ⊕ ((a ⊕ negate c) ⊕ T₀))
      ≡ b ⊕ (negate a ⊕ (c ⊕ (negate b ⊕ (a ⊕ (negate c ⊕ T₀)))))
    flatten =
      trans (⊕-assoc b (negate a) ((c ⊕ negate b) ⊕ ((a ⊕ negate c) ⊕ T₀)))
      (cong (b ⊕_)
        (trans (cong (negate a ⊕_) (⊕-assoc c (negate b) ((a ⊕ negate c) ⊕ T₀)))
               (cong (λ z → negate a ⊕ (c ⊕ (negate b ⊕ z)))
                     (⊕-assoc a (negate c) T₀))))

-- 对抗验证（技术文档 §7④: 删去的逐 case 证据以**具体点 refl** 补回）
cancel3-spot₁ : sum3 (T₁ ⊕ negate T₂) (T₂ ⊕ negate T₁) (T₂ ⊕ negate T₂) ≡ T₀
cancel3-spot₁ = refl

cancel3-spot₂ : sum3 (T₂ ⊕ negate T₂) (T₀ ⊕ negate T₂) (T₂ ⊕ negate T₀) ≡ T₀
cancel3-spot₂ = refl

cancel3-spot₃ : sum3 (T₁ ⊕ negate T₁) (T₁ ⊕ negate T₁) (T₁ ⊕ negate T₁) ≡ T₀
cancel3-spot₃ = refl

cancel3-spot₄ : sum3 (T₂ ⊕ negate T₀) (T₁ ⊕ negate T₂) (T₀ ⊕ negate T₁) ≡ T₀
cancel3-spot₄ = refl

-- 判型备注（为什么表定义类**不改**）: `rotate-4`/`plus-negate-zero`/`negate-plus-zero`
-- 等是**表事实**（运算由表子句给出）, 按技术文档 §2 反例行「表 vs 公式 ⇒ 穷举就是内容」
-- 保留小规模穷举 —— 这是「先判型再动手」纪律本身。

--------------------------------------------------------------------------------
-- §2. 轴向循环净通量恒为零（判据 C 的量 = axisFlux）
--
-- 定义取**展开形式**（f (shiftAt …) 直写）, 使第三项的 f(s³x) 在语法上可见,
-- 从而 `rewrite cong f (shiftAt-cubed i x)` 能把它折回 f x。
--------------------------------------------------------------------------------

-- 判据 C 的可观察量: 沿轴 i 的一个 3-周期内的净通量（三段差分之和）
axisFlux : C3 → ScalarField → Torus6 → Trit
axisFlux i f x =
  sum3 (f (shiftAt i x) ⊕ negate (f x))
       (f (shiftAt i (shiftAt i x)) ⊕ negate (f (shiftAt i x)))
       (f (shiftAt i (shiftAt i (shiftAt i x))) ⊕ negate (f (shiftAt i (shiftAt i x))))

-- **主定理**: 净通量恒为 T₀ —— 单步无净流入, 通量型爆聚判据永不触发
axisFlux-zero : ∀ (i : C3) (f : ScalarField) (x : Torus6) →
  axisFlux i f x ≡ T₀
axisFlux-zero i f x rewrite cong f (shiftAt-cubed i x) =
  cancel3 (f x) (f (shiftAt i x)) (f (shiftAt i (shiftAt i x)))

-- 同型的 diffF 形式（与 NSEOnT6.diffF / shiftF 定义性对齐, 便于与 div 对接）
axisFlux-via-diffF : ∀ (i : C3) (f : ScalarField) (x : Torus6) →
  sum3 (diffF i f x) (diffF i f (shiftAt i x)) (diffF i f (shiftAt i (shiftAt i x))) ≡ T₀
axisFlux-via-diffF i f x = axisFlux-zero i f x

--------------------------------------------------------------------------------
-- §3. 判据 C 的定理化与诚实边界
--
-- 判据 C（通量型）: 称离散场在演化中**通量型爆聚**, 若存在轴向周期净通量持续非零
--   （局部点被持续灌注 ⇒ 累积）。
--
-- ✓ 已证（本模块）: **axisFlux ≡ T₀ 恒成立** ⇒ 判据 C 的触发条件在
--   单步、逐 3-周期尺度上**不可能满足**——通量型爆聚在本基座上被封死。
--
-- ✗ 未证（开放, 不冒充）:
--   ① **多步/耦合集中**: 长期再分布（如涡旋自持）能否把场集中到小子集,
--      需要总量守恒（Σ 场量不变）或支撑集单调性定理——**未证**;
--   ② 候选 B（峰值集中度）在本基座**不可陈述**（无序）, 若改用范数投影
--      则是**有损**（4→1）⇒ 不构成合法判据;
--   ③ 与连续统「爆聚」（Navier–Stokes 正则性）的关系: **不声称**——
--      本框架不主张连续极限（`NSEPhaseField:420` O4 边界）。
--------------------------------------------------------------------------------
