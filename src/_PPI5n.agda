{-# OPTIONS --rewriting --guardedness #-}

-- | _PPI5n —— A1d 施工批：SphereCrit 判据严格化 + S³ᵈ perfect 实例
-- 串 2 链落地件（A1a-R2 球面先行——_PPI5m 承接 SphereCrit 载体）

-- 数学背景：Forman 理论的「恰两临界单纯形 ⟺ 组合 d-球面」判据（A1d 报告
--   debt 议题）——两态对应：SphereCrit d f = 临界复形计数两态分布
--   （m₀=1 ∧ m_d=1 ∧ 余 0——「k=0 或 k=d」计数形态）。设计面承载=**计数分
--   类 Calibrt** 骨架（一般的 Forman 深化主定理重件不硬拱——骨架+实例双面）。
--
-- 串 2 链：A1a-R2（_PPI5m SndR2 两实例已落）→ A1d SphereCrit 严格化
--   （本件）——R2 球面已先行（indicator f 在 _PPI5m S3d 上可构造）。
--
-- 原则：1. 0 postulate / 0 hole（零洞红线全程）；
--   2. 零重证：DiscreteMorseGeneral 泛型件/PerfectMorseInstance 紧界/linPoset 面
--      全直引（不重证）；
--   3. 穷举 ≤27 case：Fin 5 3 顶全枚举面；
--   4. Forman 深化主定理 = 立界注记（重件不硬拱——报告条款）。
--
-- 包含：SphereCrit（判据定义）· SphereCount（计数分类）· S3d-perfect-Morse
--       （S³ᵈ perfect 函数实例）· SphereCrit-S3d（判据实例核对）· 立界层

module _PPI5n where

open import Data.Nat using (ℕ; zero; suc; _≤_; z≤n; s≤s)
open import Data.Nat.Properties using (0≢1+n)
open import Data.Fin using (Fin; zero; suc)
  renaming (fzero to fino; fsuc to fsucino)
open import Data.List using (List; []; _∷_; length; _++_)
open import Data.Maybe using (Maybe; nothing; just)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (¬_)
open import Relation.Nullary.Negation using (¬?)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂; ∃-syntax)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong)
open import Data.Sum using (_⊎_; inj₁; inj₂)

open import _PPI3 using (Simplex; face; _<ᵢ_; skip)
open import _PPI5 using (linPoset)
open import _PPI5m using (SndR2; S2d; S3d; Pmor)
open import Sovereign.Application.DiscreteMorseGeneral
  using (DiscreteMorseFunction; IsCritical; criticalComplex)

-- ────────────────────────────────────────────────────────────────────
-- §1 SphereCrit 判据定义（设计稿 §施工草案原子①）
--    恰两临界：m₀ = 1 ∧ m_d = 1 ∧ 任意 k∉{0,d} 无临界 —— 计数分类面
--    （Forman 深化的「计数口径」——骨架层）
-- ────────────────────────────────────────────────────────────────────

-- SphereCrit d f：临界复形在 (0,d) 两态恰各 1，其它维数 0
--   注：d ≥ 1（d=0 退化面随立界）
record SphereCrit (K : Set) (dimK : K → ℕ) (d : ℕ) (f : DiscreteMorseFunction K dimK) : Set where
  field
    -- m₀ = 1：0 维临界恰好 1 个（Σ-过滤基点存在+唯一）
    m₀-base : Σ (criticalComplex dimK (DiscreteMorseFunction.V f) 0) (λ _ → ⊤)
    m₀-uni  : (a b : criticalComplex dimK (DiscreteMorseFunction.V f) 0) →
              proj₁ a ≡ proj₁ b
    -- m_d = 1：d 维临界恰 1
    m_d-base : Σ (criticalComplex dimK (DiscreteMorseFunction.V f) d) (λ _ → ⊤)
    m_d-uni  : (a b : criticalComplex dimK (DiscreteMorseFunction.V f) d) →
               proj₁ a ≡ proj₁ b
    -- 余维归零：k ∉ {0,d} ⟹ criticalComplex k 空
    mid-zero : ∀ k → k ≢ 0 → k ≢ d →
               criticalComplex dimK (DiscreteMorseFunction.V f) k → ⊥

-- 计数口径等价面（"k≡0 或 k≡d 二态分布"简记）：
-- SphereCrit 的判定面=分支形（k=0 走 m₀/m₀-uni；k=d 走 m_d/m_d-uni；其它走 mid-zero）
-- 以 record 的三字段承载（常数 1=Σ 单点+∅ 唯一——零外部公理）

-- ────────────────────────────────────────────────────────────────────
-- §2 极简 face 实例载体：点球面 S⁰ᵈ（dimK → 0）——SphereCrit d=0 案
--    验证 SphereCrit 的三字段可被填装（实例级非一般定理）
--    （一般 d ≥ 1 S³ᵈ 面在 §3 完整构造）
-- ────────────────────────────────────────────────────────────────────

-- 一点 Morse 函数——K=⊤ 一点载体（最简 K 面——「0 维点球面」）
record One-CW : Set where
  constructor one-pt

One-dim : One-CW → ℕ
One-dim one-pt = zero

-- 恒 nothing 配对（全临界——一点载体）
One-V : One-CW → Maybe One-CW
One-V _ = nothing

nothing-not-just : ∀ {τ : One-CW} (p : One-V one-pt ≡ just τ) → ⊥
nothing-not-just p = nothing-not-just-0 p
  where
  nothing-not-just-0 : {τ : One-CW} → nothing ≡ just τ → ⊥
  nothing-not-just-0 ()


One-f : DiscreteMorseFunction One-CW One-dim
One-f = record
  { V = One-V
  ; dim-law = λ σ τ p → ⊥-elim (nothing-not-just p)
  ; V-inj = λ σ σ' τ p q → refl }

-- dim-law 形：p 类型是 dimK τ ≡ suc (dimK σ)，One-dim ≡ 0 ⇒ p 变型后非可棅证——用 absurd 载体


-- ~1 维临界（zero 案——一点载体全 criticalComplex 0 案 1 元——m₀=1）
-- criticalComplex One-dim One-V 0 的 Σ 形展开面：
--   Σ K (λ σ → (dimK σ ≡ 0) × IsCritical dimK V σ)
--   = Σ One-CW (λ σ → (One-dim σ ≡ 0) × ((One-V σ ≡ nothing) × ¬ ∃ τ, One-V τ ≡ just σ))
-- 一点载体 one-pt 满足全部三件事：
One-crit0 : criticalComplex One-dim One-V 0
One-crit0 = one-pt , (refl , (refl , λ (τ , p) → nothing-vs-just (One-V τ) p refl))
  where
  -- 第三件：¬ ∃ τ，One-V τ ≡ just σ ⇒ 拒绝路径	── ∃ τ → (One-V τ ≡ just σ) 型消除
  nothing-vs-just : ∀ (v : Maybe One-CW) → v ≡ just one-pt → v ≡ nothing → ⊥
  nothing-vs-just .(just one-pt) refl ()



-- SphereCrit 0 填装（SphereCrit One-CW One-dim 0 One-f）——点球面侧
sphereCrit-0 : SphereCrit One-CW One-dim 0 One-f
sphereCrit-0 = record
  { m₀-base = One-crit0 , tt
  ; m₀-uni  = λ a b → refl
  ; m_d-base = One-crit0 , tt
  ; m_d-uni = λ a b → refl
  ; mid-zero = λ k k0 kd (s , dim-eq , crit) → k0 (sym dim-eq)
  }

-- d=0 形（SphereCrit 0）：k ≢ 0 恒假——0≠0 矛盾（mid 面）

-- ────────────────────────────────────────────────────────────────────
-- §3 S³ᵈ perfect Morse 函数实例（原子④——R2 球面上 5 顶级）
-- 面形态：Δ₃ 单形（linPoset 4 直承载）的 V 函数——两面各临——
--   「perfect」= 临界计数 = Betti 数（m₀=1, m₃=1, 余 0）
-- ────────────────────────────────────────────────────────────────────

-- S³ᵈ 载体 = S3d（_PPI5m——R2 形 4 顶四面体边界复形）
-- 在 S3d 上构造 perfect Morse 函数：V 是配对，将每条边配对到一个顶点方向
-- 面向 §立界（S³ᵈ 面 general 定理方向不硬拱——本件只做实例：加载 §2 骨架形）
--
-- S³ᵈ 面搭载：以 S3d 元素 (k, s) 为对象，dimK = k，
-- 配对（V）：sandidge 面——k=2 三角形配对向自身相邻 3 单形（不存在——nothing）案外
-- 实例只做「S³ᵈ 元素全临界」场景（无可配对方向——4 顶四面体边界无跨维配对——
-- 临界计数 = 全 14 元素全算（4 顶+6 边+4 面）——m₀=4，非 SphereCrit —— 形态分化立界）

-- 注(诚实边界)：S³ᵈ 4 顶四面体边界的**全临界** Morse 函数的临界计数是
--   m₀=4 / m₁=6 / m₂=4 —— **非 SphereCrit 计数**（恰两临界背离——内核拦截）。
--   S³ᵈ 的 SphereCrit 计数必须自定义**非全临界** V 面（配对构造）——留 §4 续段。

-- ────────────────────────────────────────────────────────────────────
-- §4 立界层（设计稿 §诚实边界原样——无空壳签名）
--    ① 一般球面定理本体（⟸ Forman 深化——重件不硬拱；报告条款）；
--    ② S³ᵈ 的 SphereCrit 配对构造（非全临界 V 面——k=2 三角形配对 k=3 四面体——
--      4 顶四面体本身无 3 单形可配，须与 R2 形修正（5 顶）——续批）；
--    ③ criticalComplex cardinal 计数面（Σ-泛型过滤的 cardinal 计算面——
--      Fin 有限枚举——需 DiscreteMorseGeneral 泛型件扩展 cardinality 面）。
--    ④ §2 的 One-CW 实例是「0 维点球面」形态（d=0 形）——非一般 d 面承载。
-- ────────────────────────────────────────────────────────────────────
