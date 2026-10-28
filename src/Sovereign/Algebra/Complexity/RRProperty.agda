{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Algebra.Complexity.RRProperty
-- GF(3) monic 不可约精确计数 + Razborov-Rudich 自然性质分类（W4c-B）
--
-- 衔接（PvsNP 路线图 W4c）：对抗自检已定案——「全息不可约」性质满足 RR
-- 构造性但极小（smallness）。本件把该判断的**计数基础**变成库内定理：
--   • monic 二次不可约精确计数 = 3（9 个中，§2）
--   • monic 三次不可约精确计数 = 8（27 个中，§4；核对 (27−3)/3 = 8）
--   • 密度 3/9 与 8/27 以 pair 记录；一般 N 渐近密度 ~1/N **立界**（§6）。
-- 由此支撑分类结论：该性质 constructive（✓ 判定器存在）∧ large（✗ 计数
-- 定理 + 渐近立界），故非 RR 自然性质——规避 RR 屏障（屏障只约束自然
-- 性质），但同时非通用下界技术（自然性正是自然证明法威力的来源）。
--
-- 层向纪律：Sovereign.Algebra **禁止 import Sovereign.Application**
--（层向禁止反向引用）。根检验器范本是
-- Application.Problems.PvsNP.Complexity §4 的 eval-quad/has-root（只读
-- 对照，不引用），本件在 §1/§3 **本地重建**同形判定器并加 RR- 前缀；
-- 返回类型由范本的 Trit（T₀=不可约）改为 Bool（true=无根=不可约），
-- 以直接支撑 §2/§4 的逐项计数。
--
-- 定名纪律：全部符号加 RR- 前缀（库内已有 Lang/W/addVec3/P2 撞名前科；
-- 建档前 grep 自检零撞名）。
--
-- 分级标注约定（全库诚实分级纪律，同 BooleanSim/TimeBound）：
--   〔结构定义〕= 数据/record 定义；〔refl 枚举〕= 有限情形逐点 refl；
--   〔立界注记〕= 深件边界，不设空壳签名。
--
-- 0 postulate / 0 hole。

module Sovereign.Algebra.Complexity.RRProperty where

open import Data.Nat using (ℕ; suc; _*_; _≤_)
open import Data.Nat.Properties using (≤-refl; m≤n+m)
open import Data.Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_; _++_; map)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

-- 引用边界（跨层仅指向 Base，同 BooleanSim 形态）：
open import Sovereign.Base.Trit using (Trit; T₀; T₁; T₂; _⊕_; _⊗_)

--------------------------------------------------------------------------------
-- §1 二次根检验〔本地重建；层向禁止反向引用〕
--
-- 范本: Application.Problems.PvsNP.Complexity §4 eval-quad/has-root（只读
-- 对照，本件不 import 该层）。同形重建 + RR- 前缀 + Bool 返回值。
-- GF(3) 特性: 二次多项式有根 ⟺ 可约；无根 ⟺ 不可约。
--------------------------------------------------------------------------------

-- monic 二次多项式 x² + a·x + b 在 x 处的值（括号化同范本左嵌套形态）
RR-evalQuad : Trit → Trit → Trit → Trit
RR-evalQuad a b x = ((x ⊗ x) ⊕ (a ⊗ x)) ⊕ b

-- 三值代入检查: 三个点值全非零 ⇒ 无根（任一为零 ⇒ 有根）
--〔结构定义〕返回 Bool（true=无根=不可约; 范本 has-root 返回 Trit, 此处改型以支撑计数）
RR-noRootAt : Trit → Trit → Trit → Bool
RR-noRootAt T₀ _     _     = false
RR-noRootAt _     T₀ _     = false
RR-noRootAt _     _     T₀ = false
RR-noRootAt _     _     _  = true

-- monic 二次无根判定器: x² + a·x + b 代入 T₀/T₁/T₂ 全非零
RR-noRootQ : Trit → Trit → Bool
RR-noRootQ a b =
  RR-noRootAt (RR-evalQuad a b T₀) (RR-evalQuad a b T₁) (RR-evalQuad a b T₂)

--------------------------------------------------------------------------------
-- §2 GF(3) monic 二次不可约精确计数 = 3〔refl 枚举〕
--
-- 数学（Python 实证后落笔，非猜测）: 9 = 3² 个 monic 二次中不可约者恰
-- 3 个 = (3²−3)/2，即 x²+1、x²+x+2、x²+2x+2。二次特性行: GF(3) 上
-- 无根 ⟺ 不可约，有根 ⟺ 可约（= (x−r)(x−s)）。
--------------------------------------------------------------------------------

-- 9 个 (a,b) 显式枚举（a 外层 b 内层，与判定表同序）
RR-quadList : List (Trit × Trit)
RR-quadList =
  (T₀ , T₀) ∷ (T₀ , T₁) ∷ (T₀ , T₂) ∷
  (T₁ , T₀) ∷ (T₁ , T₁) ∷ (T₁ , T₂) ∷
  (T₂ , T₀) ∷ (T₂ , T₁) ∷ (T₂ , T₂) ∷ []

-- 逐项判定表（字面 Bool；Python 实证 [0,1,0, 0,0,1, 0,0,1]）
RR-quadFlags : List Bool
RR-quadFlags =
  false ∷ true  ∷ false ∷
  false ∷ false ∷ true  ∷
  false ∷ false ∷ true  ∷ []

-- 逐项闭合: 表中每一项都必须与判定器归约一致——refl 对 9 项逐项核对，
-- 任一字面错则整条 lemma 编译失败
RR-quadFlags-sound :
  RR-quadFlags ≡ map (λ ab → RR-noRootQ (proj₁ ab) (proj₂ ab)) RR-quadList
RR-quadFlags-sound = refl

-- 三个不可约型命名实例（文档级逐项证据；x²+1 即范本 irred-example 同例）
RR-irrQ-a0-b1 : RR-noRootQ T₀ T₁ ≡ true;  RR-irrQ-a0-b1 = refl  -- x²+1
RR-irrQ-a1-b2 : RR-noRootQ T₁ T₂ ≡ true;  RR-irrQ-a1-b2 = refl  -- x²+x+2
RR-irrQ-a2-b2 : RR-noRootQ T₂ T₂ ≡ true;  RR-irrQ-a2-b2 = refl  -- x²+2x+2
-- 可约命名实例（x²+2x+1 = (x+1)²，即范本 red-example 同例）
RR-redQ-a2-b1 : RR-noRootQ T₂ T₁ ≡ false; RR-redQ-a2-b1 = refl

-- 计数器
RR-countTrue : List Bool → ℕ
RR-countTrue []            = 0
RR-countTrue (true  ∷ xs)  = suc (RR-countTrue xs)
RR-countTrue (false ∷ xs)  = RR-countTrue xs

RR-countIrrQ : ℕ
RR-countIrrQ = RR-countTrue RR-quadFlags

-- 主定理: monic 二次不可约精确计数 = 3
RR-countIrrQ-3 : RR-countIrrQ ≡ 3
RR-countIrrQ-3 = refl

--------------------------------------------------------------------------------
-- §3 三次根检验〔本地重建；同 §1 形态〕
--
-- monic 三次多项式 x³ + a·x² + b·x + c。三次特性行: 可约三次必含一次
-- 因子 ⟹ 有根；反之有根 ⟹ 可约。故无根 ⟺ 不可约（次数 ≤ 3 特有）。
-- ⊕ 无 fixity 声明（非结合），全式显式括号化，书写方向 = 左嵌套。
--------------------------------------------------------------------------------

RR-evalCubic : Trit → Trit → Trit → Trit → Trit
RR-evalCubic a b c x =
  ((((x ⊗ x) ⊗ x) ⊕ ((a ⊗ x) ⊗ x)) ⊕ (b ⊗ x)) ⊕ c

-- monic 三次无根判定器: 代入 T₀/T₁/T₂ 全非零
RR-noRootC : Trit → Trit → Trit → Bool
RR-noRootC a b c =
  RR-noRootAt (RR-evalCubic a b c T₀) (RR-evalCubic a b c T₁) (RR-evalCubic a b c T₂)

--------------------------------------------------------------------------------
-- §4 GF(3) monic 三次不可约精确计数 = 8〔refl 枚举，分段〕
--
-- 数学核对: 27 = 3³ 个 monic 三次中不可约者 8 个 = (27−3)/3（x³−x 的根
-- 0,±1 排除 + 首一商三等分；Python 实证 8 项后落笔，非猜测）。
-- 本节分三段: 4a List 枚举 → 4b 判定表 + 逐项闭合 → 4c 命名实例 + 主定理。
--------------------------------------------------------------------------------

-- §4a 27 个 (a,b,c) 显式枚举——按 a 分三块（每块 b 外层 c 内层）
RR-cubicListA0 : List (Trit × Trit × Trit)
RR-cubicListA0 =
  (T₀ , T₀ , T₀) ∷ (T₀ , T₀ , T₁) ∷ (T₀ , T₀ , T₂) ∷
  (T₀ , T₁ , T₀) ∷ (T₀ , T₁ , T₁) ∷ (T₀ , T₁ , T₂) ∷
  (T₀ , T₂ , T₀) ∷ (T₀ , T₂ , T₁) ∷ (T₀ , T₂ , T₂) ∷ []

RR-cubicListA1 : List (Trit × Trit × Trit)
RR-cubicListA1 =
  (T₁ , T₀ , T₀) ∷ (T₁ , T₀ , T₁) ∷ (T₁ , T₀ , T₂) ∷
  (T₁ , T₁ , T₀) ∷ (T₁ , T₁ , T₁) ∷ (T₁ , T₁ , T₂) ∷
  (T₁ , T₂ , T₀) ∷ (T₁ , T₂ , T₁) ∷ (T₁ , T₂ , T₂) ∷ []

RR-cubicListA2 : List (Trit × Trit × Trit)
RR-cubicListA2 =
  (T₂ , T₀ , T₀) ∷ (T₂ , T₀ , T₁) ∷ (T₂ , T₀ , T₂) ∷
  (T₂ , T₁ , T₀) ∷ (T₂ , T₁ , T₁) ∷ (T₂ , T₁ , T₂) ∷
  (T₂ , T₂ , T₀) ∷ (T₂ , T₂ , T₁) ∷ (T₂ , T₂ , T₂) ∷ []

RR-cubicList : List (Trit × Trit × Trit)
RR-cubicList = RR-cubicListA0 ++ RR-cubicListA1 ++ RR-cubicListA2

-- §4b 逐项判定表（字面 Bool，与 §4a 同序分三块; Python 实证）
-- a=T₀: [0,0,0, 0,0,0, 0,1,1]; a=T₁: [0,0,1, 0,0,1, 0,1,0];
-- a=T₂: [0,1,0, 0,1,0, 0,0,1] —— 合计 8 项 true。
RR-cubicFlagsA0 : List Bool
RR-cubicFlagsA0 =
  false ∷ false ∷ false ∷
  false ∷ false ∷ false ∷
  false ∷ true  ∷ true  ∷ []

RR-cubicFlagsA1 : List Bool
RR-cubicFlagsA1 =
  false ∷ false ∷ true  ∷
  false ∷ false ∷ true  ∷
  false ∷ true  ∷ false ∷ []

RR-cubicFlagsA2 : List Bool
RR-cubicFlagsA2 =
  false ∷ true  ∷ false ∷
  false ∷ true  ∷ false ∷
  false ∷ false ∷ true  ∷ []

RR-cubicFlags : List Bool
RR-cubicFlags = RR-cubicFlagsA0 ++ RR-cubicFlagsA1 ++ RR-cubicFlagsA2

-- 逐项闭合: 27 项字面逐一与判定器归约核对，任一错则 refl 失败
RR-cubicFlags-sound :
  RR-cubicFlags ≡
  map (λ abc → RR-noRootC (proj₁ abc) (proj₁ (proj₂ abc)) (proj₂ (proj₂ abc)))
      RR-cubicList
RR-cubicFlags-sound = refl

-- §4c 8 个不可约三次型命名实例（文档级逐项证据；Python 实证清单落笔）
RR-irrC-a0-b2-c1 : RR-noRootC T₀ T₂ T₁ ≡ true; RR-irrC-a0-b2-c1 = refl  -- x³+2x+1
RR-irrC-a0-b2-c2 : RR-noRootC T₀ T₂ T₂ ≡ true; RR-irrC-a0-b2-c2 = refl  -- x³+2x+2
RR-irrC-a1-b0-c2 : RR-noRootC T₁ T₀ T₂ ≡ true; RR-irrC-a1-b0-c2 = refl  -- x³+x²+2
RR-irrC-a1-b1-c2 : RR-noRootC T₁ T₁ T₂ ≡ true; RR-irrC-a1-b1-c2 = refl  -- x³+x²+x+2
RR-irrC-a1-b2-c1 : RR-noRootC T₁ T₂ T₁ ≡ true; RR-irrC-a1-b2-c1 = refl  -- x³+x²+2x+1
RR-irrC-a2-b0-c1 : RR-noRootC T₂ T₀ T₁ ≡ true; RR-irrC-a2-b0-c1 = refl  -- x³+2x²+1
RR-irrC-a2-b1-c1 : RR-noRootC T₂ T₁ T₁ ≡ true; RR-irrC-a2-b1-c1 = refl  -- x³+2x²+x+1
RR-irrC-a2-b2-c2 : RR-noRootC T₂ T₂ T₂ ≡ true; RR-irrC-a2-b2-c2 = refl  -- x³+2x²+2x+2
-- 可约命名实例: x³−x = x(x−1)(x+1) 恒有根 0,±1（核对项之一）
RR-redC-a0-b2-c0 : RR-noRootC T₀ T₂ T₀ ≡ false; RR-redC-a0-b2-c0 = refl

-- 三次计数（复用 §2 计数器）
RR-countIrrC : ℕ
RR-countIrrC = RR-countTrue RR-cubicFlags

-- 主定理: monic 三次不可约精确计数 = 8 = (27−3)/3
RR-countIrrC-8 : RR-countIrrC ≡ 8
RR-countIrrC-8 = refl

--------------------------------------------------------------------------------
-- §5 密度与 RR 自然性质分类
--
-- RR 屏障（Razborov-Rudich 1997）两条件: (a) 构造性——存在多项式时间
-- 判定器; (b) 大性——性质类占全空间份额不随规模衰减到 0。二者兼备（再
-- 加「有用」）即触及屏障: 不能用以证明电路下界（PRG 存在假定下）。
--------------------------------------------------------------------------------

-- 密度以 pair (不可约数, 全空间) 记录，不做有理数算术〔结构定义〕
-- 第一分量取自计数定理，定义性归约为 3 / 8
RR-densityQ : ℕ × ℕ
RR-densityQ = RR-countIrrQ , 9

RR-densityC : ℕ × ℕ
RR-densityC = RR-countIrrC , 27

-- 闭合: 密度对与计数定理一致（第一分量归约核对）
RR-densityQ-3-9 : RR-densityQ ≡ (3 , 9)
RR-densityQ-3-9 = refl

RR-densityC-8-27 : RR-densityC ≡ (8 , 27)
RR-densityC-8-27 = refl

-- 极小性在两个实测点的量化形态（闭合）: 覆盖至多 1/3
--（3·3=9≤9, 3·8=24≤27; 常数上界，渐近趋零见 §6 立界）
RR-smallQ : 3 * RR-countIrrQ ≤ 9
RR-smallQ = ≤-refl

RR-smallC : 3 * RR-countIrrC ≤ 27
RR-smallC = m≤n+m 24 3

-- 分类结论枚举〔结构定义; status 枚举惯例，同库内猜想 status 字段〕
data RR-Verdict : Set where
  RR-natural                 : RR-Verdict  -- 自然性质: 受 RR 屏障约束
  RR-nonnatural-nonuniversal : RR-Verdict  -- 非自然: 规避 RR 屏障, 同时非通用下界技术

-- RR 自然性质分类 record
record RR-IsNatural : Set₁ where
  constructor RR-classify
  field
    -- (a) 构造性达成? ✓ —— 判定器存在: RR-noRootQ/RR-noRootC 显式全定义（§1/§3）,
    --     固定次数代入 3 点 × 3 值, 常数代价; 一般次数的多项式计账立界（§6）
    RR-constructive : Bool
    -- (b) 大性达成? ✗ —— 计数定理: 精确密度 3/9 与 8/27（§2/§4）,
    --     渐近密度 ~1/N 衰减到 0（立界, §6）
    RR-large        : Bool
    -- 结论字段: 非自然性质 ⇒ 规避 RR 屏障（屏障只约束自然性质）;
    -- 但同时非通用下界技术（自然性正是自然证明法威力的来源, 失去大性
    -- 即失去对随机函数的区分力）〔推断链的文字注记 + 枚举记录〕
    RR-verdict      : RR-Verdict

-- 本件分类实例:「全息不可约」= monic GF(3) 不可约性
RR-holo-irreducible : RR-IsNatural
RR-holo-irreducible = RR-classify true false RR-nonnatural-nonuniversal

--------------------------------------------------------------------------------
-- §6 立界清单（本件边界，不冒充）与结论
--
--   ✅ GF(3) monic 二次/三次根检验判定器（§1/§3, 本地重建, 层向合规）
--   ✅ 精确计数定理 RR-countIrrQ-3 / RR-countIrrC-8（§2/§4, refl 枚举）
--   ✅ 密度对 (3,9)/(8,27) 与极小性实测点上界 ≤1/3（§5, 闭合）
--   ✅ RR 分类 record + 枚举记录（§5, 闭合）
--   〔立界〕一般 N 渐近密度 ~1/N：需参数化 GF(3^k) / 一般次数载体（路线图
--      W3），本件仅在 N=9,27 两个实测点闭合；
--   〔立界〕RR 原定理（自然+有用 ⟹ 破 PRG）的形式化: 需 PRG/电路类基础设施,
--      本件以枚举记录分类结论 + 文字注记, 不设空壳签名;
--   〔立界〕「非通用下界技术」的最后一步（失去大性 ⟹ 失去区分力）是世界级
--      方法论判断的库内投影, 以 RR-nonnatural-nonuniversal 枚举承载, 不冒充
--      形式化定理。
--
--   0 postulate / 0 hole。
--------------------------------------------------------------------------------

