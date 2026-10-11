{-# OPTIONS --rewriting --guardedness #-}

-- | _PM3c
-- Morse route 级 ∂²=0 对接件（_PM3b 立界清偿）：
--   CoefRoute 归纳 × 配对表的对接——route 跳贡献两形 + 三消去律 + 链归纳主件。
--
-- 核心原则：
-- 1. 直连跳（hop-direct）单跳归零走 oneStepPair-zero 门径（出口互补相消）；
-- 2. 复合跳对（hop-via）相消走 _PM3b 传播合成形（前缀配对/尾配对）+ 尾递归 IH；
-- 3. cr-via 构造子自带跳贡献数据（μ-in/i/ν——复合形 = 路由总系数形）；
--    cr-direct 出口对由 DirectExit 前提供给（V/Face 具体化——M3 分水岭 record 范式）；
-- 4. 0 postulate / 0 hole——配对前提由构造子证据承载。
--
-- 包含：§1 跳贡献两形 ｜ §2 三消去律 ｜ §3 跳链归纳主件 ｜ §4 CoefRoute 对接 ｜ §5 K₃ 对账

module _PM3c where

open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; trans; cong)

open import Sovereign.Base.Trit using (Trit; T₀; T₁; T₂; _⊕_; _⊗_)
open import Sovereign.Topology.MorsePairingLaw using
  (oneStepPair; oneStepPair-zero; ⊗-zeroʳ-loc)
open import _PM3b using
  (via-tail-cancel; via-prefix-cancel; via-propagate; via-propagate-tail)
open import Sovereign.Topology.MorseSqZeroK3 using (m3-cancel; m3-assembly)
open import Sovereign.Topology.MorseCoeffRoute using (module CoeffRouteDef)

------------------------------------------------------------------------
-- §1 路由跳贡献项（两形——与 CoefRoute 两构造子对齐）
------------------------------------------------------------------------

data HopEntry : Set where
  hop-direct : (a b e' : Trit) → HopEntry
  hop-via    : (μ i t ν : Trit) → HopEntry

hopVal : HopEntry → Trit
hopVal (hop-direct a b e') = oneStepPair a b e'
hopVal (hop-via μ i t ν)   = (μ ⊗ i) ⊗ (t ⊗ ν)

------------------------------------------------------------------------
-- §2 三消去律（跳级相消——真实证明内容）
------------------------------------------------------------------------

-- ① 直连跳单跳归零（门径直引——出口互补）
direct-hop-zero : (a b e' : Trit) → b ⊕ e' ≡ T₀ →
                  hopVal (hop-direct a b e') ≡ T₀
direct-hop-zero a b e' h = oneStepPair-zero a b e' h

-- ② 复合跳对前缀配对相消（传播合成形 A）
via-pair-zero : (μ i μ' i' t ν : Trit) → (μ ⊗ i) ⊕ (μ' ⊗ i') ≡ T₀ →
                hopVal (hop-via μ i t ν) ⊕ hopVal (hop-via μ' i' t ν) ≡ T₀
via-pair-zero μ i μ' i' t ν h = via-propagate μ i μ' i' t ν h

-- ③ 复合跳对尾配对相消（传播合成形 B）
via-tail-zero : (μ i t ν ν' : Trit) → ν ⊕ ν' ≡ T₀ →
                hopVal (hop-via μ i t ν) ⊕ hopVal (hop-via μ i t ν') ≡ T₀
via-tail-zero μ i t ν ν' h = via-propagate-tail μ i t ν ν' h

------------------------------------------------------------------------
-- §3 跳链归纳主件（route 级 ∂²=0 全形）
------------------------------------------------------------------------

-- 跳链：route 级 ∂² 贡献的配对组织（构造子携带相消证据）
data HopChain : Set where
  hc-nil      : HopChain
  hc-direct   : (a b e' : Trit) → b ⊕ e' ≡ T₀ → HopChain → HopChain
  hc-via-pair : (μ i μ' i' t ν : Trit) → (μ ⊗ i) ⊕ (μ' ⊗ i') ≡ T₀ → HopChain → HopChain
  hc-via-tail : (μ i t ν ν' : Trit) → ν ⊕ ν' ≡ T₀ → HopChain → HopChain

-- 链贡献和（直连单跳 + 复合对双跳）
chainSum : HopChain → Trit
chainSum hc-nil = T₀
chainSum (hc-direct a b e' h rest) =
  hopVal (hop-direct a b e') ⊕ chainSum rest
chainSum (hc-via-pair μ i μ' i' t ν h rest) =
  (hopVal (hop-via μ i t ν) ⊕ hopVal (hop-via μ' i' t ν)) ⊕ chainSum rest
chainSum (hc-via-tail μ i t ν ν' h rest) =
  (hopVal (hop-via μ i t ν) ⊕ hopVal (hop-via μ i t ν')) ⊕ chainSum rest

-- 主件：route 级 ∂²=0（对归纳——三形各走消去律 + ⊕-identityˡ 收口）
d2-route-zero : (c : HopChain) → chainSum c ≡ T₀
d2-route-zero hc-nil = refl
d2-route-zero (hc-direct a b e' h rest) =
  trans (cong (_⊕ chainSum rest) (direct-hop-zero a b e' h))
        (trans (⊕-identityˡ-loc (chainSum rest)) (d2-route-zero rest))
  where
  ⊕-identityˡ-loc : (x : Trit) → T₀ ⊕ x ≡ x
  ⊕-identityˡ-loc T₀ = refl
  ⊕-identityˡ-loc T₁ = refl
  ⊕-identityˡ-loc T₂ = refl
d2-route-zero (hc-via-pair μ i μ' i' t ν h rest) =
  trans (cong (_⊕ chainSum rest) (via-pair-zero μ i μ' i' t ν h))
        (trans (⊕-identityˡ-loc (chainSum rest)) (d2-route-zero rest))
  where
  ⊕-identityˡ-loc : (x : Trit) → T₀ ⊕ x ≡ x
  ⊕-identityˡ-loc T₀ = refl
  ⊕-identityˡ-loc T₁ = refl
  ⊕-identityˡ-loc T₂ = refl
d2-route-zero (hc-via-tail μ i t ν ν' h rest) =
  trans (cong (_⊕ chainSum rest) (via-tail-zero μ i t ν ν' h))
        (trans (⊕-identityˡ-loc (chainSum rest)) (d2-route-zero rest))
  where
  ⊕-identityˡ-loc : (x : Trit) → T₀ ⊕ x ≡ x
  ⊕-identityˡ-loc T₀ = refl
  ⊕-identityˡ-loc T₁ = refl
  ⊕-identityˡ-loc T₂ = refl

------------------------------------------------------------------------
-- §4 CoefRoute 对接（构造子数据 → 跳贡献桥）
------------------------------------------------------------------------

module RouteDock (K : Set) (V : K → Maybe K) (Face : K → K → Set)
                 (coeff : K → K → Trit) where

  open CoeffRouteDef K V Face coeff

  -- cr-direct 跳的出口分解前提（V/Face 具体化——record 假设参数非 postulate）
  record DirectExit (μ : Trit) : Set where
    field
      b e' : Trit
      opp  : b ⊕ e' ≡ T₀

  -- 路由首跳贡献桥：cr-via 构造子数据直填（复合形 = 总系数形）；
  -- cr-direct 由出口前提供给
  entryOf : ∀ {σ τ μ} → CoefRoute σ τ μ → DirectExit μ → HopEntry
  entryOf (cr-direct σ τ μ hface hcoef hcrit) de =
    hop-direct μ (DirectExit.b de) (DirectExit.e' de)
  entryOf (cr-via σ w e' τ μ-in i ν hface hw hcoef hinv tail) de =
    hop-via μ-in i T₂ ν


  -- 对接推论①（直连形归零——不递归，门径直引；尾递归 IH 由 §3 链归纳承载）
  route-direct-zero : (μ b e' : Trit) → b ⊕ e' ≡ T₀ →
                      hopVal (hop-direct μ b e') ≡ T₀
  route-direct-zero = direct-hop-zero

  -- 对接核对（definitional）：cr-via 首跳值 = 复合形（路由总系数形）
  entryOf-via-val :
      ∀ {τ} (σ' : K) (w e'' : K) (μ-in i ν : Trit)
      (hface : Face w σ') (hw : V w ≡ just e'')
      (hcoef : coeff w σ' ≡ μ-in) (hinv : coeff w e'' ⊗ i ≡ T₁)
      (tail : CoefRoute e'' τ ν)
      (de : DirectExit ((μ-in ⊗ i) ⊗ (T₂ ⊗ ν))) →
      hopVal (entryOf (cr-via σ' w e'' τ μ-in i ν hface hw hcoef hinv tail) de)
        ≡ (μ-in ⊗ i) ⊗ (T₂ ⊗ ν)
  entryOf-via-val σ' w e'' μ-in i ν hface hw hcoef hinv tail de = refl

------------------------------------------------------------------------
-- §5 K₃ route 级对账（m3-cancel/m3-assembly 同款数据）
------------------------------------------------------------------------

-- route 级配对（前缀配对形）：K₃ 双路由 (T₂⊗T₂=T₁) vs (T₂⊗T₁=T₂) 相消
check-route-k3-pair :
    hopVal (hop-via T₂ T₂ T₁ T₂) ⊕ hopVal (hop-via T₂ T₁ T₁ T₂) ≡ T₀
check-route-k3-pair = via-pair-zero T₂ T₂ T₂ T₁ T₁ T₂ m3-cancel

-- route 级链主件实例：K₃ 单对链归零（d2-route-zero 调用）
check-route-k3-chain : chainSum
    (hc-via-pair T₂ T₂ T₂ T₁ T₁ T₂ m3-cancel hc-nil) ≡ T₀
check-route-k3-chain = d2-route-zero
    (hc-via-pair T₂ T₂ T₂ T₁ T₁ T₂ m3-cancel hc-nil)

-- 直连跳门径实例：出口互补 (T₁,T₂) 单跳归零
check-route-k3-direct : hopVal (hop-direct T₂ T₁ T₂) ≡ T₀
check-route-k3-direct = direct-hop-zero T₂ T₁ T₂ m3-cancel

-- 组装形对账（MorseSqZeroK3 m3-assembly 同款）
check-route-k3-assembly : T₂ ⊗ (T₁ ⊕ T₂) ≡ T₀
check-route-k3-assembly = m3-assembly
