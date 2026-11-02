{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Synthesis.A4.SL23ToBT
--
-- **SL(2,3) ≅ 2A₄ ≅ Q₈ ⋊ C₃**——两张独立构造的 24 元素群之间的**群同构**。
--
-- 库里此前有两条互不相接的线：
--   · `BinaryTetrahedral`：2A₄ = Q₈ ⋊ C₃（`data Q8` + `data C3G` + `record BT`），
--     乘法是少数几条规则（`_*q_` 64 / `_*c_` 7 / `act` 24）；
--   · `BinaryTetrahedralDefiningRep` + `SL23Cayley`：SL(2,3) = {det=1 的 GF(3) 2×2 矩阵}，
--     乘法是 **576 条不透明查找表**。
--   两边都是「24 个元素」，但从未证明是同一个群。本文件补上这一环。
--
-- 【为什么值得做】同构一通，`BT` 侧的半直积结构（Q₈ 正规、C₃ 三循环作用、
--   中心 Z₂ = {(1,c₀),(−1,c₀)}）立刻可搬到 SL(2,3) 侧；`V2Orbit`/`V2Simple`/
--   `V2GMapWeight` 那条「V₂ 是正则表示的商」的链，所依赖的「24 槽 = Q₈×C₃ 坐标化」
--   由此获得群论底座。
--
-- 【证明策略：表对表，576 案不可约】
--   SL23 是不透明 24 构造子 data，`_⊗_` 是 576 条查找表，无生成元/字表示可归纳；
--   `toBT` 自身也是 24 条显式表。命题内容是「两张表相容」的 576 条独立事实，
--   逐条归约不可约。按「单引理 ≤27 案」纪律，按第一参数分解成 24 个行引理
--   （每个 ∀ y，24 案）再组装——与 `ToA4Hom.toA4-hom`、`BilinearSchur2A4.toME-hom`
--   同一纪律（BilinearSchur2A4.agda:252）。
--
-- 【表的来源：机器生成 + 双重验证，非手抄】
--   `scripts/gen_sl23_to_bt.py` 就地解析所依赖的四个 Agda 表并检验：
--     ① Q₈ ⊂ SL23（64 对）、C₃ ⊂ SL23（9 对）；
--     ② `act(c,·)` 恰等于 SL23 中按 c ∈ C₃ 的**共轭**（24 条）——这是半直积能与
--        SL23 相容的**充要条件**，无它则 `toBT` 不可能保乘法；
--     ③ Q₈·C₃ 覆盖全部 24 元素且互异（Q₈ ∩ C₃ = {1} ⇒ 分解唯一）；
--     ④ 576 对逐条验证 `toBT (a ⊗ b) ≡ toBT a *bt toBT b`。
--   任一检查不过，脚本 exit 1、不产出文件。
--   本文件内的 `toBT-hom` 576 条 refl 是 Agda 侧对同一结论的**独立复核**。
--
-- 【层级边界（重要）】本模块只做**群层**同构：对象是 24 个符号及其乘法表，
--   不涉及系数域。Z[ω] 只在把 2A₄ **线性化**成二维旋量表示时才进场
--   （`SpinNoInvariantLine` / `BilinearSchur2A4` 那一层）；把本同构读成
--   「Z[ω] 上的表示等价」是越级。群层同构是表示层的**前置**，不是替代。
--
-- ═══════════════════════════════════════════════════════════════
-- 八要素对照（形状规范: docs/maps/八要素统一形状-2026-10-14.md）
-- ═══════════════════════════════════════════════════════════════
--  ① 载体      `toBT` / `fromBT`：SL23 ↔ BT 的 24↔24 双射表（§1、§2）
--  ② 生成元    Q₈ 的 i/j/k = g0/g10/g14（阶 4、反交换），C₃ 的 ω = g2（阶 3）
--  ③ 关系      `toBT-hom`（576 案）+ `fromBT-is-section`/`fromBT-is-retraction`（各 24 案）
--  ④ 相位      `act c1` 的三循环 i→j→k→i —— C₃ 在 Q₈ 上的自同构相位
--  ⑤ 时钟      C₃ 的 ω³ = 1（`c2 = c1*c1`，本文件经 `_*c_` 表复用）
--  ⑥ 归零      `toBT-minus1`：中心 −1 ↦ (`qm1`, `c0`)
--  ⑦ 刚性      Q₈ ∩ C₃ = {1} ⇒ 分解唯一（脚本 ③ 已验，§1 表逐项体现）
--  ⑧ 核对      `iso`：`fromBT-is-section` / `fromBT-is-retraction` 共 48 条 refl + `toBT-injective`
--
-- 形状贴合: **8/8**
--
-- 0 postulate / 0 hole；零浮点。
module Sovereign.Synthesis.A4.SL23ToBT where

open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; cong; cong₂; module ≡-Reasoning)
open ≡-Reasoning

open import Sovereign.Synthesis.A4.BinaryTetrahedral
  using ( Q8; q1; qm1; qi; qmi; qj; qmj; qk; qmk
        ; C3G; c0; c1; c2
        ; BT; mkBT; _*bt_; bt-id; act; _*q_; _*c_ )
open import Sovereign.Synthesis.A4.BinaryTetrahedralDefiningRep
  using ( SL23; g0; g1; g2; g3; g4; g5; g6; g7; g8; g9; g10; g11
        ; g12; g13; g14; g15; g16; g17; g18; g19; g20; g21; g22; g23 )
open import Sovereign.Synthesis.Representation.SL23Cayley using (_⊗_)

--------------------------------------------------------------------------------
-- §1. 分解表 SL23 → Q₈ × C₃
--
-- 每个 g 唯一写成 q·c（q ∈ Q₈，c ∈ C₃）。表由 `scripts/gen_sl23_to_bt.py`
-- 从 `_⊗_` 表解析得到，并已验证 576 对同态性（见文件头「表的来源」）。
--------------------------------------------------------------------------------

toBT : SL23 → BT
toBT g0   = mkBT qi   c0
toBT g1   = mkBT qmj  c2
toBT g2   = mkBT q1   c1
toBT g3   = mkBT qmi  c0
toBT g4   = mkBT qm1  c1
toBT g5   = mkBT qj   c2
toBT g6   = mkBT q1   c0
toBT g7   = mkBT qi   c2
toBT g8   = mkBT qmj  c1
toBT g9   = mkBT qmi  c1
toBT g10  = mkBT qj   c0
toBT g11  = mkBT qm1  c2
toBT g12  = mkBT qk   c2
toBT g13  = mkBT qk   c1
toBT g14  = mkBT qk   c0
toBT g15  = mkBT qm1  c0
toBT g16  = mkBT qj   c1
toBT g17  = mkBT qmi  c2
toBT g18  = mkBT qmk  c2
toBT g19  = mkBT qmk  c0
toBT g20  = mkBT qmk  c1
toBT g21  = mkBT qi   c1
toBT g22  = mkBT q1   c2
toBT g23  = mkBT qmj  c0

fromBT : BT → SL23
fromBT (mkBT q1   c0) = g6
fromBT (mkBT qm1  c0) = g15
fromBT (mkBT qi   c0) = g0
fromBT (mkBT qmi  c0) = g3
fromBT (mkBT qj   c0) = g10
fromBT (mkBT qmj  c0) = g23
fromBT (mkBT qk   c0) = g14
fromBT (mkBT qmk  c0) = g19
fromBT (mkBT q1   c1) = g2
fromBT (mkBT qm1  c1) = g4
fromBT (mkBT qi   c1) = g21
fromBT (mkBT qmi  c1) = g9
fromBT (mkBT qj   c1) = g16
fromBT (mkBT qmj  c1) = g8
fromBT (mkBT qk   c1) = g13
fromBT (mkBT qmk  c1) = g20
fromBT (mkBT q1   c2) = g22
fromBT (mkBT qm1  c2) = g11
fromBT (mkBT qi   c2) = g7
fromBT (mkBT qmi  c2) = g17
fromBT (mkBT qj   c2) = g5
fromBT (mkBT qmj  c2) = g1
fromBT (mkBT qk   c2) = g12
fromBT (mkBT qmk  c2) = g18

--------------------------------------------------------------------------------
-- §2. 双射：往返恒等（24 + 24 案，全 refl——两张表互为逆）
--------------------------------------------------------------------------------

fromBT-is-section : ∀ (b : BT) → toBT (fromBT b) ≡ b
fromBT-is-section (mkBT q1   c0) = refl
fromBT-is-section (mkBT qm1  c0) = refl
fromBT-is-section (mkBT qi   c0) = refl
fromBT-is-section (mkBT qmi  c0) = refl
fromBT-is-section (mkBT qj   c0) = refl
fromBT-is-section (mkBT qmj  c0) = refl
fromBT-is-section (mkBT qk   c0) = refl
fromBT-is-section (mkBT qmk  c0) = refl
fromBT-is-section (mkBT q1   c1) = refl
fromBT-is-section (mkBT qm1  c1) = refl
fromBT-is-section (mkBT qi   c1) = refl
fromBT-is-section (mkBT qmi  c1) = refl
fromBT-is-section (mkBT qj   c1) = refl
fromBT-is-section (mkBT qmj  c1) = refl
fromBT-is-section (mkBT qk   c1) = refl
fromBT-is-section (mkBT qmk  c1) = refl
fromBT-is-section (mkBT q1   c2) = refl
fromBT-is-section (mkBT qm1  c2) = refl
fromBT-is-section (mkBT qi   c2) = refl
fromBT-is-section (mkBT qmi  c2) = refl
fromBT-is-section (mkBT qj   c2) = refl
fromBT-is-section (mkBT qmj  c2) = refl
fromBT-is-section (mkBT qk   c2) = refl
fromBT-is-section (mkBT qmk  c2) = refl

fromBT-is-retraction : ∀ (x : SL23) → fromBT (toBT x) ≡ x
fromBT-is-retraction g0   = refl
fromBT-is-retraction g1   = refl
fromBT-is-retraction g2   = refl
fromBT-is-retraction g3   = refl
fromBT-is-retraction g4   = refl
fromBT-is-retraction g5   = refl
fromBT-is-retraction g6   = refl
fromBT-is-retraction g7   = refl
fromBT-is-retraction g8   = refl
fromBT-is-retraction g9   = refl
fromBT-is-retraction g10  = refl
fromBT-is-retraction g11  = refl
fromBT-is-retraction g12  = refl
fromBT-is-retraction g13  = refl
fromBT-is-retraction g14  = refl
fromBT-is-retraction g15  = refl
fromBT-is-retraction g16  = refl
fromBT-is-retraction g17  = refl
fromBT-is-retraction g18  = refl
fromBT-is-retraction g19  = refl
fromBT-is-retraction g20  = refl
fromBT-is-retraction g21  = refl
fromBT-is-retraction g22  = refl
fromBT-is-retraction g23  = refl

-- 双射的直接推论：toBT 单射（不重新枚举，走往返消去）
toBT-injective : ∀ {x y : SL23} → toBT x ≡ toBT y → x ≡ y
toBT-injective {x} {y} p =
  begin
    x                      ≡⟨ sym (fromBT-is-retraction x) ⟩
    fromBT (toBT x)        ≡⟨ cong fromBT p ⟩
    fromBT (toBT y)        ≡⟨ fromBT-is-retraction y ⟩
    y                      ∎

--------------------------------------------------------------------------------
-- §3. 单位与中心
--------------------------------------------------------------------------------

toBT-e : toBT g6 ≡ bt-id
toBT-e = refl

-- 中心 −1（Q₈ 的中心，被 C₃ 固定）在 SL23 侧是 g15
toBT-minus1 : toBT g15 ≡ mkBT qm1 c0
toBT-minus1 = refl

--------------------------------------------------------------------------------
-- §4. 同态性：toBT (x ⊗ y) ≡ toBT x *bt toBT y（24 行 × 24 案 = 576 对）
--
-- 【为何是穷举】见文件头「证明策略」：`_⊗_` 与 `toBT` 都是不透明 24 条表，
-- 命题是两张表相容的 576 条独立事实。按第一参数分解成 24 个行引理再组装。
--------------------------------------------------------------------------------

-- g0 行
toBT-hom-g0 : ∀ (y : SL23) → toBT (g0 ⊗ y) ≡ toBT g0 *bt toBT y
toBT-hom-g0 g0   = refl
toBT-hom-g0 g1   = refl
toBT-hom-g0 g2   = refl
toBT-hom-g0 g3   = refl
toBT-hom-g0 g4   = refl
toBT-hom-g0 g5   = refl
toBT-hom-g0 g6   = refl
toBT-hom-g0 g7   = refl
toBT-hom-g0 g8   = refl
toBT-hom-g0 g9   = refl
toBT-hom-g0 g10  = refl
toBT-hom-g0 g11  = refl
toBT-hom-g0 g12  = refl
toBT-hom-g0 g13  = refl
toBT-hom-g0 g14  = refl
toBT-hom-g0 g15  = refl
toBT-hom-g0 g16  = refl
toBT-hom-g0 g17  = refl
toBT-hom-g0 g18  = refl
toBT-hom-g0 g19  = refl
toBT-hom-g0 g20  = refl
toBT-hom-g0 g21  = refl
toBT-hom-g0 g22  = refl
toBT-hom-g0 g23  = refl

-- g1 行
toBT-hom-g1 : ∀ (y : SL23) → toBT (g1 ⊗ y) ≡ toBT g1 *bt toBT y
toBT-hom-g1 g0   = refl
toBT-hom-g1 g1   = refl
toBT-hom-g1 g2   = refl
toBT-hom-g1 g3   = refl
toBT-hom-g1 g4   = refl
toBT-hom-g1 g5   = refl
toBT-hom-g1 g6   = refl
toBT-hom-g1 g7   = refl
toBT-hom-g1 g8   = refl
toBT-hom-g1 g9   = refl
toBT-hom-g1 g10  = refl
toBT-hom-g1 g11  = refl
toBT-hom-g1 g12  = refl
toBT-hom-g1 g13  = refl
toBT-hom-g1 g14  = refl
toBT-hom-g1 g15  = refl
toBT-hom-g1 g16  = refl
toBT-hom-g1 g17  = refl
toBT-hom-g1 g18  = refl
toBT-hom-g1 g19  = refl
toBT-hom-g1 g20  = refl
toBT-hom-g1 g21  = refl
toBT-hom-g1 g22  = refl
toBT-hom-g1 g23  = refl

-- g2 行
toBT-hom-g2 : ∀ (y : SL23) → toBT (g2 ⊗ y) ≡ toBT g2 *bt toBT y
toBT-hom-g2 g0   = refl
toBT-hom-g2 g1   = refl
toBT-hom-g2 g2   = refl
toBT-hom-g2 g3   = refl
toBT-hom-g2 g4   = refl
toBT-hom-g2 g5   = refl
toBT-hom-g2 g6   = refl
toBT-hom-g2 g7   = refl
toBT-hom-g2 g8   = refl
toBT-hom-g2 g9   = refl
toBT-hom-g2 g10  = refl
toBT-hom-g2 g11  = refl
toBT-hom-g2 g12  = refl
toBT-hom-g2 g13  = refl
toBT-hom-g2 g14  = refl
toBT-hom-g2 g15  = refl
toBT-hom-g2 g16  = refl
toBT-hom-g2 g17  = refl
toBT-hom-g2 g18  = refl
toBT-hom-g2 g19  = refl
toBT-hom-g2 g20  = refl
toBT-hom-g2 g21  = refl
toBT-hom-g2 g22  = refl
toBT-hom-g2 g23  = refl

-- g3 行
toBT-hom-g3 : ∀ (y : SL23) → toBT (g3 ⊗ y) ≡ toBT g3 *bt toBT y
toBT-hom-g3 g0   = refl
toBT-hom-g3 g1   = refl
toBT-hom-g3 g2   = refl
toBT-hom-g3 g3   = refl
toBT-hom-g3 g4   = refl
toBT-hom-g3 g5   = refl
toBT-hom-g3 g6   = refl
toBT-hom-g3 g7   = refl
toBT-hom-g3 g8   = refl
toBT-hom-g3 g9   = refl
toBT-hom-g3 g10  = refl
toBT-hom-g3 g11  = refl
toBT-hom-g3 g12  = refl
toBT-hom-g3 g13  = refl
toBT-hom-g3 g14  = refl
toBT-hom-g3 g15  = refl
toBT-hom-g3 g16  = refl
toBT-hom-g3 g17  = refl
toBT-hom-g3 g18  = refl
toBT-hom-g3 g19  = refl
toBT-hom-g3 g20  = refl
toBT-hom-g3 g21  = refl
toBT-hom-g3 g22  = refl
toBT-hom-g3 g23  = refl

-- g4 行
toBT-hom-g4 : ∀ (y : SL23) → toBT (g4 ⊗ y) ≡ toBT g4 *bt toBT y
toBT-hom-g4 g0   = refl
toBT-hom-g4 g1   = refl
toBT-hom-g4 g2   = refl
toBT-hom-g4 g3   = refl
toBT-hom-g4 g4   = refl
toBT-hom-g4 g5   = refl
toBT-hom-g4 g6   = refl
toBT-hom-g4 g7   = refl
toBT-hom-g4 g8   = refl
toBT-hom-g4 g9   = refl
toBT-hom-g4 g10  = refl
toBT-hom-g4 g11  = refl
toBT-hom-g4 g12  = refl
toBT-hom-g4 g13  = refl
toBT-hom-g4 g14  = refl
toBT-hom-g4 g15  = refl
toBT-hom-g4 g16  = refl
toBT-hom-g4 g17  = refl
toBT-hom-g4 g18  = refl
toBT-hom-g4 g19  = refl
toBT-hom-g4 g20  = refl
toBT-hom-g4 g21  = refl
toBT-hom-g4 g22  = refl
toBT-hom-g4 g23  = refl

-- g5 行
toBT-hom-g5 : ∀ (y : SL23) → toBT (g5 ⊗ y) ≡ toBT g5 *bt toBT y
toBT-hom-g5 g0   = refl
toBT-hom-g5 g1   = refl
toBT-hom-g5 g2   = refl
toBT-hom-g5 g3   = refl
toBT-hom-g5 g4   = refl
toBT-hom-g5 g5   = refl
toBT-hom-g5 g6   = refl
toBT-hom-g5 g7   = refl
toBT-hom-g5 g8   = refl
toBT-hom-g5 g9   = refl
toBT-hom-g5 g10  = refl
toBT-hom-g5 g11  = refl
toBT-hom-g5 g12  = refl
toBT-hom-g5 g13  = refl
toBT-hom-g5 g14  = refl
toBT-hom-g5 g15  = refl
toBT-hom-g5 g16  = refl
toBT-hom-g5 g17  = refl
toBT-hom-g5 g18  = refl
toBT-hom-g5 g19  = refl
toBT-hom-g5 g20  = refl
toBT-hom-g5 g21  = refl
toBT-hom-g5 g22  = refl
toBT-hom-g5 g23  = refl

-- g6 行
toBT-hom-g6 : ∀ (y : SL23) → toBT (g6 ⊗ y) ≡ toBT g6 *bt toBT y
toBT-hom-g6 g0   = refl
toBT-hom-g6 g1   = refl
toBT-hom-g6 g2   = refl
toBT-hom-g6 g3   = refl
toBT-hom-g6 g4   = refl
toBT-hom-g6 g5   = refl
toBT-hom-g6 g6   = refl
toBT-hom-g6 g7   = refl
toBT-hom-g6 g8   = refl
toBT-hom-g6 g9   = refl
toBT-hom-g6 g10  = refl
toBT-hom-g6 g11  = refl
toBT-hom-g6 g12  = refl
toBT-hom-g6 g13  = refl
toBT-hom-g6 g14  = refl
toBT-hom-g6 g15  = refl
toBT-hom-g6 g16  = refl
toBT-hom-g6 g17  = refl
toBT-hom-g6 g18  = refl
toBT-hom-g6 g19  = refl
toBT-hom-g6 g20  = refl
toBT-hom-g6 g21  = refl
toBT-hom-g6 g22  = refl
toBT-hom-g6 g23  = refl

-- g7 行
toBT-hom-g7 : ∀ (y : SL23) → toBT (g7 ⊗ y) ≡ toBT g7 *bt toBT y
toBT-hom-g7 g0   = refl
toBT-hom-g7 g1   = refl
toBT-hom-g7 g2   = refl
toBT-hom-g7 g3   = refl
toBT-hom-g7 g4   = refl
toBT-hom-g7 g5   = refl
toBT-hom-g7 g6   = refl
toBT-hom-g7 g7   = refl
toBT-hom-g7 g8   = refl
toBT-hom-g7 g9   = refl
toBT-hom-g7 g10  = refl
toBT-hom-g7 g11  = refl
toBT-hom-g7 g12  = refl
toBT-hom-g7 g13  = refl
toBT-hom-g7 g14  = refl
toBT-hom-g7 g15  = refl
toBT-hom-g7 g16  = refl
toBT-hom-g7 g17  = refl
toBT-hom-g7 g18  = refl
toBT-hom-g7 g19  = refl
toBT-hom-g7 g20  = refl
toBT-hom-g7 g21  = refl
toBT-hom-g7 g22  = refl
toBT-hom-g7 g23  = refl

-- g8 行
toBT-hom-g8 : ∀ (y : SL23) → toBT (g8 ⊗ y) ≡ toBT g8 *bt toBT y
toBT-hom-g8 g0   = refl
toBT-hom-g8 g1   = refl
toBT-hom-g8 g2   = refl
toBT-hom-g8 g3   = refl
toBT-hom-g8 g4   = refl
toBT-hom-g8 g5   = refl
toBT-hom-g8 g6   = refl
toBT-hom-g8 g7   = refl
toBT-hom-g8 g8   = refl
toBT-hom-g8 g9   = refl
toBT-hom-g8 g10  = refl
toBT-hom-g8 g11  = refl
toBT-hom-g8 g12  = refl
toBT-hom-g8 g13  = refl
toBT-hom-g8 g14  = refl
toBT-hom-g8 g15  = refl
toBT-hom-g8 g16  = refl
toBT-hom-g8 g17  = refl
toBT-hom-g8 g18  = refl
toBT-hom-g8 g19  = refl
toBT-hom-g8 g20  = refl
toBT-hom-g8 g21  = refl
toBT-hom-g8 g22  = refl
toBT-hom-g8 g23  = refl

-- g9 行
toBT-hom-g9 : ∀ (y : SL23) → toBT (g9 ⊗ y) ≡ toBT g9 *bt toBT y
toBT-hom-g9 g0   = refl
toBT-hom-g9 g1   = refl
toBT-hom-g9 g2   = refl
toBT-hom-g9 g3   = refl
toBT-hom-g9 g4   = refl
toBT-hom-g9 g5   = refl
toBT-hom-g9 g6   = refl
toBT-hom-g9 g7   = refl
toBT-hom-g9 g8   = refl
toBT-hom-g9 g9   = refl
toBT-hom-g9 g10  = refl
toBT-hom-g9 g11  = refl
toBT-hom-g9 g12  = refl
toBT-hom-g9 g13  = refl
toBT-hom-g9 g14  = refl
toBT-hom-g9 g15  = refl
toBT-hom-g9 g16  = refl
toBT-hom-g9 g17  = refl
toBT-hom-g9 g18  = refl
toBT-hom-g9 g19  = refl
toBT-hom-g9 g20  = refl
toBT-hom-g9 g21  = refl
toBT-hom-g9 g22  = refl
toBT-hom-g9 g23  = refl

-- g10 行
toBT-hom-g10 : ∀ (y : SL23) → toBT (g10 ⊗ y) ≡ toBT g10 *bt toBT y
toBT-hom-g10 g0   = refl
toBT-hom-g10 g1   = refl
toBT-hom-g10 g2   = refl
toBT-hom-g10 g3   = refl
toBT-hom-g10 g4   = refl
toBT-hom-g10 g5   = refl
toBT-hom-g10 g6   = refl
toBT-hom-g10 g7   = refl
toBT-hom-g10 g8   = refl
toBT-hom-g10 g9   = refl
toBT-hom-g10 g10  = refl
toBT-hom-g10 g11  = refl
toBT-hom-g10 g12  = refl
toBT-hom-g10 g13  = refl
toBT-hom-g10 g14  = refl
toBT-hom-g10 g15  = refl
toBT-hom-g10 g16  = refl
toBT-hom-g10 g17  = refl
toBT-hom-g10 g18  = refl
toBT-hom-g10 g19  = refl
toBT-hom-g10 g20  = refl
toBT-hom-g10 g21  = refl
toBT-hom-g10 g22  = refl
toBT-hom-g10 g23  = refl

-- g11 行
toBT-hom-g11 : ∀ (y : SL23) → toBT (g11 ⊗ y) ≡ toBT g11 *bt toBT y
toBT-hom-g11 g0   = refl
toBT-hom-g11 g1   = refl
toBT-hom-g11 g2   = refl
toBT-hom-g11 g3   = refl
toBT-hom-g11 g4   = refl
toBT-hom-g11 g5   = refl
toBT-hom-g11 g6   = refl
toBT-hom-g11 g7   = refl
toBT-hom-g11 g8   = refl
toBT-hom-g11 g9   = refl
toBT-hom-g11 g10  = refl
toBT-hom-g11 g11  = refl
toBT-hom-g11 g12  = refl
toBT-hom-g11 g13  = refl
toBT-hom-g11 g14  = refl
toBT-hom-g11 g15  = refl
toBT-hom-g11 g16  = refl
toBT-hom-g11 g17  = refl
toBT-hom-g11 g18  = refl
toBT-hom-g11 g19  = refl
toBT-hom-g11 g20  = refl
toBT-hom-g11 g21  = refl
toBT-hom-g11 g22  = refl
toBT-hom-g11 g23  = refl

-- g12 行
toBT-hom-g12 : ∀ (y : SL23) → toBT (g12 ⊗ y) ≡ toBT g12 *bt toBT y
toBT-hom-g12 g0   = refl
toBT-hom-g12 g1   = refl
toBT-hom-g12 g2   = refl
toBT-hom-g12 g3   = refl
toBT-hom-g12 g4   = refl
toBT-hom-g12 g5   = refl
toBT-hom-g12 g6   = refl
toBT-hom-g12 g7   = refl
toBT-hom-g12 g8   = refl
toBT-hom-g12 g9   = refl
toBT-hom-g12 g10  = refl
toBT-hom-g12 g11  = refl
toBT-hom-g12 g12  = refl
toBT-hom-g12 g13  = refl
toBT-hom-g12 g14  = refl
toBT-hom-g12 g15  = refl
toBT-hom-g12 g16  = refl
toBT-hom-g12 g17  = refl
toBT-hom-g12 g18  = refl
toBT-hom-g12 g19  = refl
toBT-hom-g12 g20  = refl
toBT-hom-g12 g21  = refl
toBT-hom-g12 g22  = refl
toBT-hom-g12 g23  = refl

-- g13 行
toBT-hom-g13 : ∀ (y : SL23) → toBT (g13 ⊗ y) ≡ toBT g13 *bt toBT y
toBT-hom-g13 g0   = refl
toBT-hom-g13 g1   = refl
toBT-hom-g13 g2   = refl
toBT-hom-g13 g3   = refl
toBT-hom-g13 g4   = refl
toBT-hom-g13 g5   = refl
toBT-hom-g13 g6   = refl
toBT-hom-g13 g7   = refl
toBT-hom-g13 g8   = refl
toBT-hom-g13 g9   = refl
toBT-hom-g13 g10  = refl
toBT-hom-g13 g11  = refl
toBT-hom-g13 g12  = refl
toBT-hom-g13 g13  = refl
toBT-hom-g13 g14  = refl
toBT-hom-g13 g15  = refl
toBT-hom-g13 g16  = refl
toBT-hom-g13 g17  = refl
toBT-hom-g13 g18  = refl
toBT-hom-g13 g19  = refl
toBT-hom-g13 g20  = refl
toBT-hom-g13 g21  = refl
toBT-hom-g13 g22  = refl
toBT-hom-g13 g23  = refl

-- g14 行
toBT-hom-g14 : ∀ (y : SL23) → toBT (g14 ⊗ y) ≡ toBT g14 *bt toBT y
toBT-hom-g14 g0   = refl
toBT-hom-g14 g1   = refl
toBT-hom-g14 g2   = refl
toBT-hom-g14 g3   = refl
toBT-hom-g14 g4   = refl
toBT-hom-g14 g5   = refl
toBT-hom-g14 g6   = refl
toBT-hom-g14 g7   = refl
toBT-hom-g14 g8   = refl
toBT-hom-g14 g9   = refl
toBT-hom-g14 g10  = refl
toBT-hom-g14 g11  = refl
toBT-hom-g14 g12  = refl
toBT-hom-g14 g13  = refl
toBT-hom-g14 g14  = refl
toBT-hom-g14 g15  = refl
toBT-hom-g14 g16  = refl
toBT-hom-g14 g17  = refl
toBT-hom-g14 g18  = refl
toBT-hom-g14 g19  = refl
toBT-hom-g14 g20  = refl
toBT-hom-g14 g21  = refl
toBT-hom-g14 g22  = refl
toBT-hom-g14 g23  = refl

-- g15 行
toBT-hom-g15 : ∀ (y : SL23) → toBT (g15 ⊗ y) ≡ toBT g15 *bt toBT y
toBT-hom-g15 g0   = refl
toBT-hom-g15 g1   = refl
toBT-hom-g15 g2   = refl
toBT-hom-g15 g3   = refl
toBT-hom-g15 g4   = refl
toBT-hom-g15 g5   = refl
toBT-hom-g15 g6   = refl
toBT-hom-g15 g7   = refl
toBT-hom-g15 g8   = refl
toBT-hom-g15 g9   = refl
toBT-hom-g15 g10  = refl
toBT-hom-g15 g11  = refl
toBT-hom-g15 g12  = refl
toBT-hom-g15 g13  = refl
toBT-hom-g15 g14  = refl
toBT-hom-g15 g15  = refl
toBT-hom-g15 g16  = refl
toBT-hom-g15 g17  = refl
toBT-hom-g15 g18  = refl
toBT-hom-g15 g19  = refl
toBT-hom-g15 g20  = refl
toBT-hom-g15 g21  = refl
toBT-hom-g15 g22  = refl
toBT-hom-g15 g23  = refl

-- g16 行
toBT-hom-g16 : ∀ (y : SL23) → toBT (g16 ⊗ y) ≡ toBT g16 *bt toBT y
toBT-hom-g16 g0   = refl
toBT-hom-g16 g1   = refl
toBT-hom-g16 g2   = refl
toBT-hom-g16 g3   = refl
toBT-hom-g16 g4   = refl
toBT-hom-g16 g5   = refl
toBT-hom-g16 g6   = refl
toBT-hom-g16 g7   = refl
toBT-hom-g16 g8   = refl
toBT-hom-g16 g9   = refl
toBT-hom-g16 g10  = refl
toBT-hom-g16 g11  = refl
toBT-hom-g16 g12  = refl
toBT-hom-g16 g13  = refl
toBT-hom-g16 g14  = refl
toBT-hom-g16 g15  = refl
toBT-hom-g16 g16  = refl
toBT-hom-g16 g17  = refl
toBT-hom-g16 g18  = refl
toBT-hom-g16 g19  = refl
toBT-hom-g16 g20  = refl
toBT-hom-g16 g21  = refl
toBT-hom-g16 g22  = refl
toBT-hom-g16 g23  = refl

-- g17 行
toBT-hom-g17 : ∀ (y : SL23) → toBT (g17 ⊗ y) ≡ toBT g17 *bt toBT y
toBT-hom-g17 g0   = refl
toBT-hom-g17 g1   = refl
toBT-hom-g17 g2   = refl
toBT-hom-g17 g3   = refl
toBT-hom-g17 g4   = refl
toBT-hom-g17 g5   = refl
toBT-hom-g17 g6   = refl
toBT-hom-g17 g7   = refl
toBT-hom-g17 g8   = refl
toBT-hom-g17 g9   = refl
toBT-hom-g17 g10  = refl
toBT-hom-g17 g11  = refl
toBT-hom-g17 g12  = refl
toBT-hom-g17 g13  = refl
toBT-hom-g17 g14  = refl
toBT-hom-g17 g15  = refl
toBT-hom-g17 g16  = refl
toBT-hom-g17 g17  = refl
toBT-hom-g17 g18  = refl
toBT-hom-g17 g19  = refl
toBT-hom-g17 g20  = refl
toBT-hom-g17 g21  = refl
toBT-hom-g17 g22  = refl
toBT-hom-g17 g23  = refl

-- g18 行
toBT-hom-g18 : ∀ (y : SL23) → toBT (g18 ⊗ y) ≡ toBT g18 *bt toBT y
toBT-hom-g18 g0   = refl
toBT-hom-g18 g1   = refl
toBT-hom-g18 g2   = refl
toBT-hom-g18 g3   = refl
toBT-hom-g18 g4   = refl
toBT-hom-g18 g5   = refl
toBT-hom-g18 g6   = refl
toBT-hom-g18 g7   = refl
toBT-hom-g18 g8   = refl
toBT-hom-g18 g9   = refl
toBT-hom-g18 g10  = refl
toBT-hom-g18 g11  = refl
toBT-hom-g18 g12  = refl
toBT-hom-g18 g13  = refl
toBT-hom-g18 g14  = refl
toBT-hom-g18 g15  = refl
toBT-hom-g18 g16  = refl
toBT-hom-g18 g17  = refl
toBT-hom-g18 g18  = refl
toBT-hom-g18 g19  = refl
toBT-hom-g18 g20  = refl
toBT-hom-g18 g21  = refl
toBT-hom-g18 g22  = refl
toBT-hom-g18 g23  = refl

-- g19 行
toBT-hom-g19 : ∀ (y : SL23) → toBT (g19 ⊗ y) ≡ toBT g19 *bt toBT y
toBT-hom-g19 g0   = refl
toBT-hom-g19 g1   = refl
toBT-hom-g19 g2   = refl
toBT-hom-g19 g3   = refl
toBT-hom-g19 g4   = refl
toBT-hom-g19 g5   = refl
toBT-hom-g19 g6   = refl
toBT-hom-g19 g7   = refl
toBT-hom-g19 g8   = refl
toBT-hom-g19 g9   = refl
toBT-hom-g19 g10  = refl
toBT-hom-g19 g11  = refl
toBT-hom-g19 g12  = refl
toBT-hom-g19 g13  = refl
toBT-hom-g19 g14  = refl
toBT-hom-g19 g15  = refl
toBT-hom-g19 g16  = refl
toBT-hom-g19 g17  = refl
toBT-hom-g19 g18  = refl
toBT-hom-g19 g19  = refl
toBT-hom-g19 g20  = refl
toBT-hom-g19 g21  = refl
toBT-hom-g19 g22  = refl
toBT-hom-g19 g23  = refl

-- g20 行
toBT-hom-g20 : ∀ (y : SL23) → toBT (g20 ⊗ y) ≡ toBT g20 *bt toBT y
toBT-hom-g20 g0   = refl
toBT-hom-g20 g1   = refl
toBT-hom-g20 g2   = refl
toBT-hom-g20 g3   = refl
toBT-hom-g20 g4   = refl
toBT-hom-g20 g5   = refl
toBT-hom-g20 g6   = refl
toBT-hom-g20 g7   = refl
toBT-hom-g20 g8   = refl
toBT-hom-g20 g9   = refl
toBT-hom-g20 g10  = refl
toBT-hom-g20 g11  = refl
toBT-hom-g20 g12  = refl
toBT-hom-g20 g13  = refl
toBT-hom-g20 g14  = refl
toBT-hom-g20 g15  = refl
toBT-hom-g20 g16  = refl
toBT-hom-g20 g17  = refl
toBT-hom-g20 g18  = refl
toBT-hom-g20 g19  = refl
toBT-hom-g20 g20  = refl
toBT-hom-g20 g21  = refl
toBT-hom-g20 g22  = refl
toBT-hom-g20 g23  = refl

-- g21 行
toBT-hom-g21 : ∀ (y : SL23) → toBT (g21 ⊗ y) ≡ toBT g21 *bt toBT y
toBT-hom-g21 g0   = refl
toBT-hom-g21 g1   = refl
toBT-hom-g21 g2   = refl
toBT-hom-g21 g3   = refl
toBT-hom-g21 g4   = refl
toBT-hom-g21 g5   = refl
toBT-hom-g21 g6   = refl
toBT-hom-g21 g7   = refl
toBT-hom-g21 g8   = refl
toBT-hom-g21 g9   = refl
toBT-hom-g21 g10  = refl
toBT-hom-g21 g11  = refl
toBT-hom-g21 g12  = refl
toBT-hom-g21 g13  = refl
toBT-hom-g21 g14  = refl
toBT-hom-g21 g15  = refl
toBT-hom-g21 g16  = refl
toBT-hom-g21 g17  = refl
toBT-hom-g21 g18  = refl
toBT-hom-g21 g19  = refl
toBT-hom-g21 g20  = refl
toBT-hom-g21 g21  = refl
toBT-hom-g21 g22  = refl
toBT-hom-g21 g23  = refl

-- g22 行
toBT-hom-g22 : ∀ (y : SL23) → toBT (g22 ⊗ y) ≡ toBT g22 *bt toBT y
toBT-hom-g22 g0   = refl
toBT-hom-g22 g1   = refl
toBT-hom-g22 g2   = refl
toBT-hom-g22 g3   = refl
toBT-hom-g22 g4   = refl
toBT-hom-g22 g5   = refl
toBT-hom-g22 g6   = refl
toBT-hom-g22 g7   = refl
toBT-hom-g22 g8   = refl
toBT-hom-g22 g9   = refl
toBT-hom-g22 g10  = refl
toBT-hom-g22 g11  = refl
toBT-hom-g22 g12  = refl
toBT-hom-g22 g13  = refl
toBT-hom-g22 g14  = refl
toBT-hom-g22 g15  = refl
toBT-hom-g22 g16  = refl
toBT-hom-g22 g17  = refl
toBT-hom-g22 g18  = refl
toBT-hom-g22 g19  = refl
toBT-hom-g22 g20  = refl
toBT-hom-g22 g21  = refl
toBT-hom-g22 g22  = refl
toBT-hom-g22 g23  = refl

-- g23 行
toBT-hom-g23 : ∀ (y : SL23) → toBT (g23 ⊗ y) ≡ toBT g23 *bt toBT y
toBT-hom-g23 g0   = refl
toBT-hom-g23 g1   = refl
toBT-hom-g23 g2   = refl
toBT-hom-g23 g3   = refl
toBT-hom-g23 g4   = refl
toBT-hom-g23 g5   = refl
toBT-hom-g23 g6   = refl
toBT-hom-g23 g7   = refl
toBT-hom-g23 g8   = refl
toBT-hom-g23 g9   = refl
toBT-hom-g23 g10  = refl
toBT-hom-g23 g11  = refl
toBT-hom-g23 g12  = refl
toBT-hom-g23 g13  = refl
toBT-hom-g23 g14  = refl
toBT-hom-g23 g15  = refl
toBT-hom-g23 g16  = refl
toBT-hom-g23 g17  = refl
toBT-hom-g23 g18  = refl
toBT-hom-g23 g19  = refl
toBT-hom-g23 g20  = refl
toBT-hom-g23 g21  = refl
toBT-hom-g23 g22  = refl
toBT-hom-g23 g23  = refl

toBT-hom : ∀ (x y : SL23) → toBT (x ⊗ y) ≡ toBT x *bt toBT y
toBT-hom g0   = toBT-hom-g0
toBT-hom g1   = toBT-hom-g1
toBT-hom g2   = toBT-hom-g2
toBT-hom g3   = toBT-hom-g3
toBT-hom g4   = toBT-hom-g4
toBT-hom g5   = toBT-hom-g5
toBT-hom g6   = toBT-hom-g6
toBT-hom g7   = toBT-hom-g7
toBT-hom g8   = toBT-hom-g8
toBT-hom g9   = toBT-hom-g9
toBT-hom g10  = toBT-hom-g10
toBT-hom g11  = toBT-hom-g11
toBT-hom g12  = toBT-hom-g12
toBT-hom g13  = toBT-hom-g13
toBT-hom g14  = toBT-hom-g14
toBT-hom g15  = toBT-hom-g15
toBT-hom g16  = toBT-hom-g16
toBT-hom g17  = toBT-hom-g17
toBT-hom g18  = toBT-hom-g18
toBT-hom g19  = toBT-hom-g19
toBT-hom g20  = toBT-hom-g20
toBT-hom g21  = toBT-hom-g21
toBT-hom g22  = toBT-hom-g22
toBT-hom g23  = toBT-hom-g23

--------------------------------------------------------------------------------
-- §5. 打包：群同构（4 个 field 把上面的结论固定成一条可复用命题）
--------------------------------------------------------------------------------

record GroupIso : Set where
  field
    to   : SL23 → BT
    from : BT → SL23
    hom  : ∀ (x y : SL23) → to (x ⊗ y) ≡ to x *bt to y
    -- `from` 是 `to` 的 section：to ∘ from ≡ id
    from-is-section    : ∀ (b : BT) → to (from b) ≡ b
    -- `from` 是 `to` 的 retraction：from ∘ to ≡ id
    from-is-retraction : ∀ (x : SL23) → from (to x) ≡ x

-- [主定理] SL(2,3) ≅ 2A₄ = Q₈ ⋊ C₃
sl23≅bt : GroupIso
sl23≅bt = record
  { to                 = toBT
   ; from               = fromBT
   ; hom                = toBT-hom
   ; from-is-section    = fromBT-is-section
   ; from-is-retraction = fromBT-is-retraction
  }
