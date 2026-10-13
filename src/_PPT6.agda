{-# OPTIONS --rewriting --guardedness #-}

-- | _PPT6 —— PT 线终件：迭代 Ω 截断性质（i > n 平凡——组合形判据骨架）
--
-- 数学背景：Postnikov 塔 n 阶段抹除 >n 阶同伦信息：πᵢ(Xₙ) = 0（i > n）。
--   离散形（Ωⁿ 迭代路线——_PPI5d 迭代模式注记）：πᵢᵈ = π₀(Ωⁱᵈ)；
--   「i > n 平凡」= (n+1) 阶起的 Ω 迭代 walk 空间单类。
--   本件为**判据骨架**（分层：i=2 全形 / i=3 bubble 弱形代理 / i≥4 立界）
--   + 实例核对（Gskel 两阶全证 / S²ᵈ n=2 案具象面对账）。
--
-- 核心原则：
-- 1. 判据即类型（TrivΩ2 = 基点 2-腔单类——逐点关系形，免 funext）
-- 2. 实例先行（Gskel 全证 + trunc₂ 面对账；S²ᵈ 引已证件零重证）
-- 3. GAP 收窄：i≥4 需 Ω⁴+ 机件——立界注记不硬造（空签名禁）
--
-- 包含：TrivΩ2 / TrivΩ3⁺ 判据｜TruncAbove 分层骨架｜
--       Gskel 全证实例（≡ 形 ⟹ Ω3Walk 形加强）｜S²ᵈ n=2 实例｜立界注记

module _PPT6 where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Fin using (Fin) renaming (zero to fzero)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)

open import Sovereign.Topology.BarceloAHomotopy using (DiGraph; Walk; nil)
open import _PPT2 using (PostnikovTower; tower-gskel; tower-s2; Ω2-triv-gskel)
open import _PPI2 using (π₁ᵈ)
open import _PPI4 using (Gskel)
open import Sovereign.Synthesis.McCordPi0 using (two-chain)
open import _PPI5d using (Ω2Walk; nil2; Ω2ᵈ; s2-adj; s2v0; w3; w3b; omega2-wit)
open import _PPI5f using (Ω3Walk; refl3; omega2-witb; omega2-wit-triv; omega2-witb-triv)
open import _PPI5g using (BubbleMove; Ω3Walk⁺; bubble-complete)

-- ────────────────────────────────────────────────────────────────────
-- §1. 判据层（组合形——πᵢᵈ 单类性）
-- ────────────────────────────────────────────────────────────────────

-- i=2 平凡（π₂ᵈ 单类）：基点处任意 2-腔经 Ω3Walk 相连
--   （塔 trunc₂ 面的加强形：≡ 形 ⟹ 关系形——见证可构造携带）
TrivΩ2 : (G : DiGraph) (x : DiGraph.V G) → Set
TrivΩ2 G x = (p q : Ω2ᵈ G x) → Ω3Walk G x p q

-- i=3 弱形代理（π₃ 面 bubble 生成性——Ω⁴ 机件立界前的可构造代理）
--   （= bubble-complete 的类型面：bubble 面全可解 ⇒ 粗化 π₃⁺ 单类）
TrivΩ3⁺ : (G : DiGraph) (x : DiGraph.V G) → Set
TrivΩ3⁺ G x = {w : Walk G x x} {c c' : Ω2Walk G x w w} → BubbleMove G x c c' → Ω3Walk⁺ G x c c'

-- 分层截断骨架（i > n 平凡——迭代 Ω 形的可构造判据面）
--   at2 = n=1 案（i=2 平凡）；at3 = n=2 案（i=3 bubble 代理）；
--   i≥4 案需 Ω⁴+ 机件（_PPI5d 迭代模式泛化面）——立界 §4。
record TruncAbove (G : DiGraph) (x : DiGraph.V G) : Set where
  field
    at2 : TrivΩ2 G x
    at3 : TrivΩ3⁺ G x

-- ────────────────────────────────────────────────────────────────────
-- §2. Gskel two-chain 全证实例（真内容——trunc₂ 面加强对账）
-- ────────────────────────────────────────────────────────────────────

-- i=2 全证：Ω2-triv-gskel（p ≡ q）经 refl3 + subst 升为 Ω3Walk 关系形
trivΩ2-gskel : TrivΩ2 (Gskel two-chain) fzero
trivΩ2-gskel p q = subst (λ z → Ω3Walk (Gskel two-chain) fzero p z)
                    (Ω2-triv-gskel p q) (refl3 p)

-- i=3 bubble 代理：bubble-complete 直引（零重证）
trivΩ3⁺-gskel : TrivΩ3⁺ (Gskel two-chain) fzero
trivΩ3⁺-gskel = bubble-complete

-- 分层骨架实例
trunc-above-gskel : TruncAbove (Gskel two-chain) fzero
trunc-above-gskel = record { at2 = trivΩ2-gskel ; at3 = trivΩ3⁺-gskel }

-- trunc₂ 面对账：tower-gskel 的 trunc-wit (suc zero) 与 Ω2-triv-gskel 同项（defeq）
check-agree-trunc2 : PostnikovTower.trunc-wit tower-gskel (suc zero) ≡ Ω2-triv-gskel
check-agree-trunc2 = refl

-- ────────────────────────────────────────────────────────────────────
-- §3. S²ᵈ n=2 案（具象面对账——omega2-wit 邻域 + bubble 弱形）
-- ────────────────────────────────────────────────────────────────────

-- 已证面对账（_PPI5f 零重证直引）：w3/w3b 两面 3-可缩
check-s2-w3 : Ω3Walk s2-adj s2v0 omega2-wit (nil2 w3)
check-s2-w3 = omega2-wit-triv

check-s2-w3b : Ω3Walk s2-adj s2v0 omega2-witb (nil2 w3b)
check-s2-w3b = omega2-witb-triv

-- n=2 案 bubble 弱形（i=3 代理——S²ᵈ 全 bubble 面可解）
trivΩ3⁺-s2 : TrivΩ3⁺ s2-adj s2v0
trivΩ3⁺-s2 = bubble-complete

-- 分层骨架实例（S²ᵈ 侧——at2 全形立界 §4，此处先供 i=3 面）
--   ⚠ S²ᵈ 的 TrivΩ2 全形（任意基点 2-腔单类）属 Dir2 邻域立界——
--     omega2-wit 双面已闭 + bubble 面可解为具象代理（不冒充全形）。

-- ────────────────────────────────────────────────────────────────────
-- §4. 立界注记（GAP 收窄范式——无空壳签名）
--   (i) i≥4 案：Ω⁴+ 机件未造（_PPI5d 迭代模式泛化面——索引族泛化）；
--   (ii) S²ᵈ TrivΩ2 全形：任意 2-腔对单类（Dir2/3-塌缩完备性邻域——_PPI5h 同族）；
--   (iii) G2s 自环面高阶平凡性（tower-g2s trunc₂ 以 ⊤ 供给——自环 AStep 面待补）；
--   (iv) 一般塔 Xₙ（裸 Set 阶段）的 πᵢ 承载需阶段带图结构（PT-3 (ii) 同界）。
-- ────────────────────────────────────────────────────────────────────
