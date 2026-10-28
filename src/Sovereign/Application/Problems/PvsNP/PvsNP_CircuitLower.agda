{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Application.Problems.PvsNP.PvsNP_CircuitLower
-- PvsNP_CircuitLower — 全息猜想真命题类型（PvsNP 路线图 W4a）·电路下界陈述层
--
-- 与 PvsNP_Conjecture（旧 stub）的关系：本件是 stub 的 no-poly 字段（占位型
-- ℕ → ℕ）的**真命题类型化**——以 BooleanSim 的 BS-Circuit / BS-size /
-- BS-evalT（全 trit 域总求值）给出「多项式大小一致电路族」与「无此电路族」
-- 的实型（PC-PolyCircuitFam / PC-NoPolyCircuit），并把全息猜想整理成陈述
-- record PC-HoloLower。stub 本身不动、不被引用（本件仅头注对照其 status 风格）。
--
-- ★ 一致性局限（头注强制）：族索引类型 (n : ℕ) → BS-Circuit (suc n) 在 Agda
--   中自动是**可计算一致族**（族由函数给出，构造即程序）——本陈述限于一致
--   族，弱于经典非一致电路下界（P/poly 对任意电路序列陈述）；非一致族表述
--   立界（§5 (i)）。
--
-- ★ 索引平移（相对普查精确形态的强制修正）：普查形态写 (n : ℕ) → BS-Circuit n，
--   但 BS-Circuit 无叶常量构造子（BS-var 需 Fin n，门构造子均带子电路），
--   n = 0 时 Fin 0 空 ⟹ BS-Circuit 0 为空类型（§1 PC-circuit0-empty 内证）⟹ 全
--   ℕ 索引的族无居民：PolyCircuitFam 恒空、NoPolyCircuit 恒真，陈述空洞化。
--   故族与函数族索引平移到非空输入（suc n）——与 headT 族的口径一致。
--
-- 分级标注约定（全库诚实分级纪律，同 TimeBound/BooleanSim/RRProperty）：
--   〔结构定义〕= 数据/record 定义；〔结构证明〕= 穷尽/结构情形；
--   〔refl 枚举〕= 有限情形逐点 refl；〔立界注记〕= 深件边界，不设空壳签名。
-- 层向：Application → Algebra.Complexity.{TimeBound,BooleanSim,RRProperty}
--   （合法方向；Algebra 禁止反向 import Application）。
--
-- 0 postulate / 0 hole。

module Sovereign.Application.Problems.PvsNP.PvsNP_CircuitLower where

open import Data.Nat using (ℕ; suc; _≤_)
open import Data.Nat.Properties using (≤-refl)
open import Data.Bool using (true)
open import Data.Fin using (Fin) renaming (zero to fzero)
open import Data.Empty using (⊥)
open import Data.Product using (Σ; _×_; _,_)
open import Data.Vec using (Vec; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Sovereign.Base.Trit using (Trit)
open import Sovereign.Algebra.Complexity.TimeBound using (Mono; Pos)
open import Sovereign.Algebra.Complexity.BooleanSim
  using (BS-Circuit; BS-size; BS-evalT; BS-var; BS-not; BS-and; BS-or; BS-xor)
open import Sovereign.Algebra.Complexity.RRProperty using (RR-noRootC)

-- ────────────────────────────────────────────────────────────────────
-- §1 索引平移的内证：BS-Circuit 0 为空〔结构证明（穷尽 + 构造子空参）〕
-- ────────────────────────────────────────────────────────────────────

-- 定名注记：此内证名不得以符号字符结尾（如 …-⊥），否则定义子句 LHS 会被
-- 解析器当算子式而拒绝（NoParseForLHS）——定名纪律实证。
PC-circuit0-empty : BS-Circuit 0 → ⊥
PC-circuit0-empty (BS-var ())  -- Fin 0 无构造子
PC-circuit0-empty (BS-not c)   = PC-circuit0-empty c
PC-circuit0-empty (BS-and a b) = PC-circuit0-empty a
PC-circuit0-empty (BS-or a b)  = PC-circuit0-empty a
PC-circuit0-empty (BS-xor a b) = PC-circuit0-empty a

-- ────────────────────────────────────────────────────────────────────
-- §2 真命题类型〔结构定义〕
-- ────────────────────────────────────────────────────────────────────

-- 多项式大小一致电路族：界 p（Mono × Pos）+ 一致族 fam +
-- 规模计账（size ≤ p）+ 全 trit 域逐点正确（evalT ≡ F）。
PC-PolyCircuitFam : ((n : ℕ) → Vec Trit (suc n) → Trit) → Set
PC-PolyCircuitFam F =
  Σ (ℕ → ℕ) λ p → Mono p × Pos p ×
    Σ ((n : ℕ) → BS-Circuit (suc n)) λ fam →
      (∀ n → BS-size (fam n) ≤ p n) ×
      (∀ n ys → BS-evalT (fam n) ys ≡ F n ys)

-- 「F 无多项式大小一致电路族」——stub no-poly 字段的实型
PC-NoPolyCircuit : ((n : ℕ) → Vec Trit (suc n) → Trit) → Set
PC-NoPolyCircuit F = PC-PolyCircuitFam F → ⊥

-- ────────────────────────────────────────────────────────────────────
-- §3 陈述 record（仿 PvsNP_Conjecture 的 status 风格）〔结构定义〕
-- ────────────────────────────────────────────────────────────────────

record PC-HoloLower (a b c : Trit) : Set₁ where
  field
    -- 候选显式函数族 F（如全息特征函数族）——本体实型（§2 口径）
    F : (n : ℕ) → Vec Trit (suc n) → Trit
    -- 「F 具全息特征」——Set 值假设字段：非空即假设成立；
    --   具体构造立界（§5 (ii)），本件不冒充。
    holo-asm : Set
    -- irred 侧：F 的候选特征多项式 x³+ax²+bx+c 在 GF(3) 上无根
    --   （= 不可约，次数 ≤ 3 特有），以 RRProperty 判定器 RR-noRootC 裁决
    --   （Application → Algebra 层向合法）；「F 的矩阵表 ⟹ 该系数」的
    --   耦合立界（§5 (iii)）。
    irred-asm : RR-noRootC a b c ≡ true
    -- 真命题内核：F 无多项式大小一致电路族（stub no-poly 的类型化）
    lower : PC-NoPolyCircuit F
    -- status = 0（未解决）：两字段合力把值钉死在 0
    status : ℕ
    status-0 : status ≡ 0

PC-status : ℕ
PC-status = 0  -- 0 = 未解决（stub status 惯例的模块级镜像）

-- ────────────────────────────────────────────────────────────────────
-- §4 sanity 实例：headT 族〔refl 枚举〕——PolyCircuitFam 非空，
--    NoPolyCircuit 的「否定」才有实质内容
-- ────────────────────────────────────────────────────────────────────

PC-F-head : (n : ℕ) → Vec Trit (suc n) → Trit
PC-F-head n (x ∷ xs) = x

PC-headFam : (n : ℕ) → BS-Circuit (suc n)
PC-headFam n = BS-var fzero

-- 正确性分量（复用 BooleanSim 现成电路 BS-var，定义性归约到 x）
PC-head-corr : ∀ n ys → BS-evalT (PC-headFam n) ys ≡ PC-F-head n ys
PC-head-corr n (x ∷ xs) = refl

-- 完整构造：p = 常值 1（mono / pos / size 三项 ≤-refl），正确性一项 refl
PC-head-poly : PC-PolyCircuitFam PC-F-head
PC-head-poly =
  (λ _ → 1) , (λ _ → ≤-refl) , (λ _ → ≤-refl) ,
  ( PC-headFam
  , (λ n → ≤-refl)
  , PC-head-corr )

-- 否定面核对：PC-NoPolyCircuit 对 headT 族**不可证**（poly 族成员即反例注入）
PC-head-not-nopoly : PC-NoPolyCircuit PC-F-head → ⊥
PC-head-not-nopoly np = np PC-head-poly

-- ────────────────────────────────────────────────────────────────────
-- §5 立界注记（诚实边界——不设空壳签名）
-- ────────────────────────────────────────────────────────────────────
-- (i)   非一致族：经典电路下界（P/poly 形态）对**非一致**电路序列陈述；
--       本件的族索引 (n : ℕ) → BS-Circuit (suc n) 在 Agda 中自动可计算一致
--       （一致族），故即使对某候选 F 证出 lower，也弱于经典非一致下界。
--       非一致族载体（无一致性保证的无穷序列给法）立界，未排期。
-- (ii)  F 的显式构造：满足 holo-asm 的真候选（全息特征函数族）的具体构造
--       未排期——§3 的 holo-asm 仅以 Set 值假设字段承载；§4 sanity 用 headT
--       族证明载型非空，不冒充全息实例。
-- (iii) irred ⟺ F 耦合：「F 的矩阵表特征多项式 = x³+ax²+bx+c」的系数提取 +
--       RR-noRootC 裁决 + 多项式计账立界（依赖参数化 GF(3^k) 载体，同
--       RRProperty §6 / 路线图 W3）。
-- (iv)  与 PvsNP_Separation 的关系：该件是 Eval/Invert 在 GF(3) 上的代数
--       分离**模拟件**（其头注自警：非复杂性类分离）；本件给的是电路模型
--       下界的**陈述类型**。两者都不是 P≠NP 的证明：真正的分离 = 对具体
--       候选 F 证出 lower（世界级开放，status 因此钉 0）。
-- (v)   计账口径：下界只对 BS-size（电路规模）陈述；与 TimeBound 的 steps
--       计账经 BooleanSim §5 的 steps ≡ size 等式换算；渐近 Big-O 层立界
--       同 BooleanSim §8(iv)。

-- 0 postulate / 0 hole。
-- 本文件由 agda +RTS -M8G -H6G -A128M -RTS 编译，EXIT=0 为完成判据。
