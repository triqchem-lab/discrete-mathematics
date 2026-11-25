{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Synthesis.Geometry.SpinTorsionCoupling
-- 挠率-自旋耦合的离散类比（M9 · G3, EC 谱系）
--
-- 数学背景（EC: 挠率的源 = 物质自旋密度, 如能量-动量是曲率之源）:
--   离散类比的三层构造（本件全部构造性, 零 postulate）:
--   · **自旋源** = 手征串 SpinConfig = List Chirality（LeftHanded/RightHanded,
--     承 Base.WuXing）;
--   · **自旋密度差** spinImbalance = 手征电荷和（左 +1, 右 −1）;
--   · **挠率 = 源场**（κ = 1 单位耦合常数）: spinTorsion cfg 的 torsionValue
--     **定义性等于** spinImbalance cfg —— EC 耦合方程的离散形态
--     （`coupling` 定理, refl 即得）。
--   · 非零挠率条件 = 配置不平衡（imbalance ≢ 0）; 平衡配置闭合归零
--     （ClosedTorsion, 镜像 CartanTorsion 的 2026-08 P0-3 修复）。
--
-- ★ 仲吕桥（G3 → CartanTorsion 实例）:
--   repL 11（11 个左手的自旋配置）的挠率值 ≡ + 11 ≡ `zhonglvTorsion` 的挠率值
--   （`zhonglv-spin-bridge`）—— CartanTorsion 的「仲吕不交」+11 挠率
--   获得自旋源解释: **11 个净左手的自旋失衡**。
--
-- 诚实边界:
--   · κ = 1 是构造选择（EC 的 κ 量纲/数值层未形式化）;
--   · 本件是 EC 谱系离散类比, 不对俄系物理主张作任何承载
--     （[物理假说·未验证] 隔离, 同 TeleparallelA4 头注）。

module Sovereign.Synthesis.Geometry.SpinTorsionCoupling where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥)
open import Data.Integer using (ℤ; +_; -[1+_]) renaming (_+_ to _+ℤ_)
open import Data.List using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong)
open import Sovereign.Base.WuXing using (Chirality; LeftHanded; RightHanded)
open import Sovereign.Synthesis.Geometry.CartanTorsion
  using (DiscreteTorsion; ClosedTorsion; closeTorsion; zhonglvTorsion)
open DiscreteTorsion
open ClosedTorsion

--------------------------------------------------------------------------------
-- §1. 自旋源: 手征串与自旋密度差
--------------------------------------------------------------------------------

SpinConfig : Set
SpinConfig = List Chirality

-- 手征电荷（EC: 自旋密度差的符号承载; 左 +1, 右 −1）
chiralCharge : Chirality → ℤ
chiralCharge LeftHanded = + 1
chiralCharge RightHanded = -[1+ 0 ]

-- 两手征电荷相异（符号结构, 1 条）
charge-ne : chiralCharge LeftHanded ≢ chiralCharge RightHanded
charge-ne ()

-- 自旋密度差（源场）: 手征电荷之和
spinImbalance : SpinConfig → ℤ
spinImbalance [] = + 0
spinImbalance (c ∷ cs) = chiralCharge c +ℤ spinImbalance cs

--------------------------------------------------------------------------------
-- §2. EC 耦合的离散形态: 挠率 = 源场（κ = 1）
--------------------------------------------------------------------------------

-- 一般配置 → 闭合挠率（闭合后恒 +0, 镜像 closeTorsion 语义; 不走 DiscreteTorsion
-- —— 那里需要 torsionNonzero, 平衡配置给不出, 正是 P0-3 矛盾的同款）
spinTorsionClosed : SpinConfig → ClosedTorsion
spinTorsionClosed cfg = record
  { phaseIndexAfter12 = 0
  ; octavePhaseRequired = 0
  ; torsionValue = + 0
  }

-- 非平衡配置 → 完整挠率（torsionNonzero 由前提传递）
spinTorsion : (cfg : SpinConfig) → spinImbalance cfg ≢ + 0 → DiscreteTorsion
spinTorsion cfg nz = record
  { phaseIndexAfter12 = 0
  ; octavePhaseRequired = 0
  ; torsionValue = spinImbalance cfg
  ; torsionNonzero = nz
  }

-- ★ EC 耦合方程（离散形态）: 挠率值定义性等于自旋密度差（κ = 1, refl 即得）
coupling : ∀ (cfg : SpinConfig) (nz : spinImbalance cfg ≢ + 0)
         → DiscreteTorsion.torsionValue (spinTorsion cfg nz) ≡ spinImbalance cfg
coupling cfg nz = refl

-- 平衡闭合归零（镜像 torsionClosedAfterZhonglv 的构造形态）
coupling-closed : ∀ (cfg : SpinConfig)
                → ClosedTorsion.torsionValue (spinTorsionClosed cfg) ≡ + 0
coupling-closed cfg = refl

--------------------------------------------------------------------------------
-- §3. 仲吕桥: 11 个净左手 ⟺ zhonglvTorsion（+11）
--------------------------------------------------------------------------------

repL : ℕ → SpinConfig
repL zero = []
repL (suc k) = LeftHanded ∷ repL k

-- repL k 的失衡 = + k（归纳, 逐步定义归约）
imbalance-repL : ∀ k → spinImbalance (repL k) ≡ + k
imbalance-repL zero = refl
imbalance-repL (suc k) = cong (+ 1 +ℤ_) (imbalance-repL k)

-- + 11 ≢ + 0（构造子层 absurd）
nzh : + 11 ≢ + 0
nzh ()

nz11 : spinImbalance (repL 11) ≢ + 0
nz11 he = nzh (trans (sym (imbalance-repL 11)) he)

-- ★ 仲吕桥: 11 净左手的自旋失衡挠率 ≡ zhonglvTorsion 的挠率值（+11 同值）
zhonglv-spin-bridge :
  DiscreteTorsion.torsionValue (spinTorsion (repL 11) nz11)
  ≡ DiscreteTorsion.torsionValue zhonglvTorsion
zhonglv-spin-bridge = trans (coupling (repL 11) nz11) (imbalance-repL 11)
