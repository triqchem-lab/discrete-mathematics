{-# OPTIONS --rewriting --guardedness #-}

-- | GAP-M3：∂²=0（Forman 路径配对论证）
-- 数学背景：Morse 边界算子 ∂ 的平方为零。∂² 的 (σ,τ) 系数 = Σ_ν coeff(ν,σ) ⊗ coeff(τ,ν)；
--   Forman 配对论证 = 中间胞腔贡献两两相消（配对表形）——或按出口互补律单元分解（出口形）。
-- 核心原则：
--   ① K₃ 实例形先行（对账 MorseSqZeroK3 数据 m3-cancel/m3-assembly）；
--   ② 泛型形以 **record 前提**（FormanPairing/ExitDecomp）承载配对律——M3 里程碑 3 分水岭范式
--      （假设参数而非 postulate）；
--   ③ cr-via 系数传播面阻则立界（与 _PM2r 立界合并，不硬证）。
-- 包含：§1 路由级 ∂² 系数 ｜ §2 出口分解形（oneStepPair 复用）｜ §3 配对表形（FormanPairing）
--      ｜ §4 K₃ 实例对账 ｜ §5 核对层

module _PM3 where

open import Sovereign.Base.Trit using
  (Trit; T₀; T₁; T₂; _⊕_; _⊗_; ⊕-identityˡ; ⊕-identityʳ; ⊕-comm)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; sym; trans; cong)
open import Data.List using (List; []; _∷_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.List.Relation.Unary.Any using (Any; here; there)
open import Data.List.Membership.Propositional using (_∈_)
open import Sovereign.Topology.MorseSqZeroK3 using (m3-cancel; m3-assembly)
open import Sovereign.Topology.MorsePairingLaw using
  (PairingLaw; oneStepPair; oneStepPair-zero)

------------------------------------------------------------------------
-- §1 路由级 ∂² 系数
------------------------------------------------------------------------

-- 中间胞腔 ν 对 (σ,τ) 的贡献项：∂σ 的 ν 系数 ⊗ ∂ν 的 τ 系数
module RouteD2 (K : Set) (coeff : K → K → Trit) (σ τ : K) where

  term : K → Trit
  term ν = coeff ν σ ⊗ coeff τ ν

  -- 配对表形求和：按 (w,w') 成对累加——Forman 配对结构的原生呈现
  d2-sumP : List (K × K) → Trit
  d2-sumP [] = T₀
  d2-sumP ((w , w') ∷ ps) = (term w ⊕ term w') ⊕ d2-sumP ps

  -- 线性表求和（一般形；与配对表经 flatten 连通——§3 附带）
  d2-sum : List K → Trit
  d2-sum [] = T₀
  d2-sum (ν ∷ νs) = term ν ⊕ d2-sum νs

------------------------------------------------------------------------
-- §2 出口分解形（单元贡献相消——oneStepPair 复用，PairingLaw 门径）
------------------------------------------------------------------------

-- 每中间胞腔的 τ-系数分解为面出口 ⊕ V 出口且两出口互补 ⟹ 该项贡献 = T₀
module ExitForm (K : Set) (coeff : K → K → Trit) (σ τ : K) where
  open RouteD2 K coeff σ τ

  -- 出口分解前提（record 假设参数——非 postulate）
  record ExitDecomp : Set where
    field
      b   : K → Trit              -- 面出口系数
      e   : K → Trit              -- V 出口系数
      decomp : ∀ ν → coeff τ ν ≡ b ν ⊕ e ν
      exit-opp : ∀ ν → b ν ⊕ e ν ≡ T₀

  -- 单元相消主件：term ν ≡ T₀（oneStepPair-zero 直调——复用零重证）
  term-exit-zero : (dec : ExitDecomp) → (a : K → Trit) →
    (∀ ν → coeff ν σ ≡ a ν) → (ν : K) → term ν ≡ T₀
  term-exit-zero dec a a-eq ν =
    trans (cong (λ z → z ⊗ coeff τ ν) (a-eq ν))
      (trans (cong (λ z → a ν ⊗ z) (ExitDecomp.decomp dec ν))
        (oneStepPair-zero (a ν) (ExitDecomp.b dec ν) (ExitDecomp.e dec ν)
          (ExitDecomp.exit-opp dec ν)))

  -- 全表归零（线性表归纳）
  d2-exit-zero : (dec : ExitDecomp) → (a : K → Trit) →
    (∀ ν → coeff ν σ ≡ a ν) → (νs : List K) → d2-sum νs ≡ T₀
  d2-exit-zero dec a a-eq [] = refl
  d2-exit-zero dec a a-eq (ν ∷ νs) =
    trans (cong (_⊕ d2-sum νs) (term-exit-zero dec a a-eq ν))
      (trans (⊕-identityˡ (d2-sum νs))
        (d2-exit-zero dec a a-eq νs))

------------------------------------------------------------------------
-- §3 配对表形（FormanPairing——成对中间胞腔贡献相消）
------------------------------------------------------------------------

module PairForm (K : Set) (coeff : K → K → Trit) (σ τ : K) where
  open RouteD2 K coeff σ τ

  -- Forman 配对前提（record 假设参数——非 postulate）：
  --   中间路由以配对表呈现，每对贡献相消（经典 Forman 论证的离散形）
  record FormanPairing (ps : List (K × K)) : Set where
    field
      pair-cancel : ∀ {w w'} → (w , w') ∈ ps → term w ⊕ term w' ≡ T₀

  -- 配对表主件：d2-sumP ps ≡ T₀（对归纳：T₀ ⊕ IH 经 ⊕-identityˡ）
  d2-pairs-zero : (ps : List (K × K)) → FormanPairing ps → d2-sumP ps ≡ T₀
  d2-pairs-zero [] law = refl
  d2-pairs-zero ((w , w') ∷ ps) law =
    trans (cong (_⊕ d2-sumP ps) (FormanPairing.pair-cancel law (here refl)))
      (trans (⊕-identityˡ (d2-sumP ps))
        (d2-pairs-zero ps record { pair-cancel = λ {_} {_} m → FormanPairing.pair-cancel law (there m) }))

------------------------------------------------------------------------
-- §4 K₃ 实例（对账 MorseSqZeroK3 数据）
------------------------------------------------------------------------

-- K₃ 形路由面：源 s、两中间 w1 w2、靶 t
data K3 : Set where
  s w1 w2 t : K3

coeffK3 : K3 → K3 → Trit
coeffK3 w1 s = T₁
coeffK3 w2 s = T₁
coeffK3 t w1 = T₁
coeffK3 t w2 = T₂
coeffK3 _  _ = T₀

open RouteD2 K3 coeffK3 s t public using (d2-sumP) renaming (term to termK3)
open PairForm K3 coeffK3 s t

-- 配对表：单对 (w1,w2)
psK3 : List (K3 × K3)
psK3 = (w1 , w2) ∷ []

-- 配对律核对（FormanPairing 实例——term w1 = T₁⊗T₁ = T₁；term w2 = T₁⊗T₂ = T₂）
pairK3 : FormanPairing psK3
pairK3 = record { pair-cancel = pc }
  where
  pc : ∀ {x y} → (x , y) ∈ psK3 → termK3 x ⊕ termK3 y ≡ T₀
  pc (here refl) = m3-cancel
  pc (there ())

-- 主件：K₃ 的 ∂²(s,t) = T₀
d2-k3-zero : d2-sumP psK3 ≡ T₀
d2-k3-zero = d2-pairs-zero psK3 pairK3

------------------------------------------------------------------------
-- §5 核对层
------------------------------------------------------------------------

-- 对账件 ①：K₃ 配对算术 = MorseSqZeroK3 的 m3-cancel（数据一致）
check-m3-align : T₁ ⊕ T₂ ≡ T₀
check-m3-align = m3-cancel

-- 对账件 ②：装配形 = MorseSqZeroK3 的 m3-assembly（oneStepPair 结构数据一致）
check-assembly : T₂ ⊗ (T₁ ⊕ T₂) ≡ T₀
check-assembly = m3-assembly

-- 核对件 ③：K₃ 项值逐点（termK3 w1 ≡ T₁ / termK3 w2 ≡ T₂，refl 级）
check-term-w1 : termK3 w1 ≡ T₁
check-term-w1 = refl
check-term-w2 : termK3 w2 ≡ T₂
check-term-w2 = refl

-- 核对件 ④：d2-sumP 尾项归零形（T₀ ⊕ T₀）
check-d2-shape : d2-sumP psK3 ≡ (T₁ ⊕ T₂) ⊕ T₀
check-d2-shape = refl

------------------------------------------------------------------------
-- §6 立界（cr-via 面——与 _PM2r 立界合并）
------------------------------------------------------------------------
-- cr-direct 面：配对表/出口分解双形主件已证（§2/§3）——Forman 论证的直连层。
-- cr-via 面：系数传播律（cr-via 构造子的 μ-in ⊗ i ⊗ (T₂ ⊗ ν) 复合系数的配对传递）
--   需 cr-via 系数传播律（~60-100 行，_PM2r 立界同款）——传播链的配对分解待立。
--   泛型 route 级 ∂²=0 的完整形 = cr-direct 主件 + cr-via 传播配对（本件立界）。
