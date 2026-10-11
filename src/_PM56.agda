{-# OPTIONS --rewriting --guardedness #-}

-- | _PM56 —— GAP-M56 骨架：M5 Ψ 同构映射 + M6 链同伦核心（分阶段交付）
-- 数学背景：Morse 线 M5（临界链群 ↔ Morse 链复形的同构映射 Ψ）与 M6（收缩/扩张对的链同伦）。
--   本探针为 GAP 立界性质（收窄即价值）：交付 Ψ/φ 链骨架 + 链同伦 record 前提形 + 收缩对核心系数引理 + K₃ 对账。
-- 核心原则：
--   1. record 前提范式（ChainCpx/ChainHomotopy/PairConnector 承载一般恒等式——非 postulate）；
--   2. 复用零重证（Trit 环律 / MorseBoundaryK3 的 ∂M-e₂₀=(T₁,T₂) 数据 / m3-cancel 同源形）；
--   3. 诚实分阶段——一般 ∂ 上的 hom-id 实例化与 Collapse 族对接立界（§4）。
--
-- 包含：§1 泛型链形｜§2 M5 ψ/φ 与性质｜§3 M6 ChainHomotopy + 收缩对核心引理｜§4 K₃ 对账与立界

module _PM56 where

open import Data.List using (List; []; _∷_; _++_)
open import Data.Product using (_×_; _,_)
open import Data.Bool using (Bool; true; false)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong₂; trans)

open import Sovereign.Base.Trit using (Trit; T₀; T₁; T₂; _⊕_; _⊗_)

-------------------------------------------------------------------------
-- §1 泛型链形（Cell 参数化——Trit 系数自由链）
-------------------------------------------------------------------------

Chain : Set → Set
Chain Cell = List (Cell × Trit)

-------------------------------------------------------------------------
-- §2 M5：Ψ（临界含入）与 φ（配对坍缩）——链骨架与性质
-------------------------------------------------------------------------

module M5 (Cell : Set) where

  -- ψ 的 Bool 参数形（生成元层面——b ≡ isCritB c 于调用点接线）
  ψ-b : Bool → Cell → Chain Cell
  ψ-b true  c = (c , T₁) ∷ []
  ψ-b false c = []

  -- φ 的 Bool 参数形（项层面：非临界项坍缩为空，临界项保留）
  φ-b : Bool → Trit → Cell → Chain Cell
  φ-b true  a c = (c , a) ∷ []
  φ-b false a c = []

  -- φ 的链层提升（逐项坍缩后拼接）
  φ₁ : Bool → Chain Cell → Chain Cell
  φ₁ b []             = []
  φ₁ b ((c , a) ∷ xs) = φ-b b a c ++ φ₁ b xs

  -- 性质①（M5 关键性质）：φ 于 ψ 像恒等（φ∘ψ ≡ ψ——临界面不动）
  φψ-id : (b : Bool) (c : Cell) → φ₁ b (ψ-b b c) ≡ ψ-b b c
  φψ-id true  c = refl
  φψ-id false c = refl

  -- 性质②：ψ 只产出临界支撑（b ≡ true 时像为单位系数单项链）
  ψ-crit-support : (b : Bool) (c : Cell) → b ≡ true → ψ-b b c ≡ (c , T₁) ∷ []
  ψ-crit-support true  c refl = refl
  ψ-crit-support false c ()

  -- 性质③：非临界项坍缩为空（φ 的消去面）
  φ-b-kill : (c : Cell) (a : Trit) → φ-b false a c ≡ []
  φ-b-kill c a = refl

-------------------------------------------------------------------------
-- §3 M6：ChainHomotopy（record 前提形）+ 收缩对核心系数引理
-------------------------------------------------------------------------

-- 链复形前提（∂ 承载——一般恒等式的舞台）
record ChainCpx (Cell : Set) : Set₁ where
  field
    ∂C : Chain Cell → Chain Cell

-- 链同伦 record（ι=恒等含入 / π=坍缩投影；hom-id = ∂H + H∂ ≡ ι ⊖ π——前提形承载）
record ChainHomotopy {Cell : Set} (C : ChainCpx Cell)
                     (π ι : Chain Cell → Chain Cell) : Set₁ where
  open ChainCpx C
  field
    H       : Chain Cell → Chain Cell
    negC    : Chain Cell → Chain Cell
    hom-id  : (x : Chain Cell) →
              (∂C (H x) ++ H (∂C x)) ≡ (ι x ++ negC (π x))

-- 收缩对连接器（V 场配对 (τ,σ) 的系数数据——PairingLaw 同族前提形）
record PairConnector (Cell : Set) : Set where
  field
    τ σ   : Cell
    b e'  : Trit
    pair-ann : b ⊕ e' ≡ T₀

-- 核心系数引理（M6 的系数面）：配对相消前提 ⟹ 单位缩放下的相消
unit-r : (a : Trit) → a ⊗ T₁ ≡ a
unit-r T₀ = refl
unit-r T₁ = refl
unit-r T₂ = refl

pair-hom-kernel : (b e' : Trit) → b ⊕ e' ≡ T₀ → (b ⊗ T₁) ⊕ (e' ⊗ T₁) ≡ T₀
pair-hom-kernel b e' h = trans (cong₂ _⊕_ (unit-r b) (unit-r e')) h

-- 连接器核（record 上的派生件——非字段）
conn-hom-kernel : {Cell : Set} (pc : PairConnector Cell) →
  (PairConnector.b pc ⊗ T₁) ⊕ (PairConnector.e' pc ⊗ T₁) ≡ T₀
conn-hom-kernel pc = pair-hom-kernel (PairConnector.b pc) (PairConnector.e' pc) (PairConnector.pair-ann pc)

-------------------------------------------------------------------------
-- §4 K₃ 对账 + 立界
-------------------------------------------------------------------------

-- K₃ 系数对账（m3-cancel 同源数据：T₁ ⊕ T₂ ≡ T₀）
k3-cancel : T₁ ⊕ T₂ ≡ T₀
k3-cancel = refl

check-pair-hom-k3 : (T₁ ⊗ T₁) ⊕ (T₂ ⊗ T₁) ≡ T₀
check-pair-hom-k3 = pair-hom-kernel T₁ T₂ k3-cancel

-- K₃ 收缩对探针本地枚举（e20 对 v1 的 ∂M-e₂₀ ≡ (T₁,T₂) 数据——MorseBoundaryK3 对账锚）
data K3Cell : Set where
  k-e20 k-v1 k-v2 : K3Cell

k3-conn : PairConnector K3Cell
k3-conn = record { τ = k-e20 ; σ = k-v1 ; b = T₁ ; e' = T₂ ; pair-ann = refl }

check-k3-conn : (PairConnector.b k3-conn ⊗ T₁) ⊕ (PairConnector.e' k3-conn ⊗ T₁) ≡ T₀
check-k3-conn = conn-hom-kernel k3-conn

-- ψ/φ K₃ 实例核对（M5 性质于 K3Cell 接线）
module K3M5 = M5 K3Cell

check-φψ-k3 : K3M5.φ₁ true ((k-e20 , T₁) ∷ []) ≡ (k-e20 , T₁) ∷ []
check-φψ-k3 = K3M5.φψ-id true k-e20

check-ψ-k3 : K3M5.ψ-b true k-v1 ≡ (k-v1 , T₁) ∷ []
check-ψ-k3 = refl

-- §4 立界（精确剩余——GAP 节点收窄即价值）：
--   (i) hom-id 于一般 ∂ 的实例化：需 Sx 全边界表（MorseBoundaryDT/Full 面）——
--       K₃ 三对（e01/e12/t）逐对构造 ChainHomotopy 实例（H 像 = 连接链）~60-100 行；
--   (ii) H 的链层拼接律（φ₁ 与 H 的复合分配）~30-50 行；
--   (iii) 与 Collapse 族对接（CollapseToMorse 的收缩映射 = π 的具体形）~40 行；
--   (iv) Ψ 的同构性（ψ 单满 + φ 往返）于商面（MorseCriticalHomology 的 C₀ᶜ/C₁ᶜ 对账）~40-80 行。
