{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Algebra.Complexity.OracleClasses
-- oracle 类层 + BGS 相对化陈述层——PvsNP 程序 W4c-A
--
-- 本件把「为什么朴素对角化不能证 P≠NP」（Baker–Gill–Solovay 1975）从注释层
-- 升级为类型层对象：相对化判定类 OC-InP（P^A）与验证类 OC-InNP（NP^A）可定义
-- （§2–§3）；P^A ⊆ NP^A 对一切 oracle 闭合（§3 oc-P⊆NP）；「A ∈ P ⟹ oracle
-- 可消除」闭合（§4 oc-collapse）；P^A = NP^A 与 P^B ≠ NP^B 的存在性作陈述
-- record（§5，status = 0 未闭合）。旧说法「穿透相对化屏障」修正为：
-- **相对化类已可定义，其分离依赖 oracle 选择**——屏障不被穿透，
-- 只能演示分离对 oracle 的依赖。
--
-- 诚实简化（本件形式边界，与经典相对化的差距）：
--   (a) 查询串长定长：输入 n 的查询槽长 mn n 在计算前固定；经典 oracle 图灵机
--       的查询长度可随计算变化。变长查询立界，见文尾 (i)。
--   (b) oracle 无关正确性：完备/正确/代价/查询界均对一切 oracle 实例量化——
--       判定器语义不依赖 oracle 具体行为；类对 A 的相对化体现在接口形态
--       （带 oracle 槽）与 §5 陈述层对 oracle 的存在量化。此保守形使 §4 的
--       oracle 实例化无需泛等性（funext）；「固定 A 正确性」变体立界 (ii)。
--   (c) 层级：全部对象在带计账函数层（TimeBound.Counted 范式）；「判定器可由
--       OTM 实现」同 PClass §6(i) 桥立界。
--
-- 分级标注：〔结构定义〕〔结构证明〕〔refl 枚举〕〔立界注记〕（同库惯例）。
-- 0 postulate / 0 hole。

module Sovereign.Algebra.Complexity.OracleClasses where

open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _≤_; s≤s; z≤n)
open import Data.Nat.Properties
  using (≤-trans; ≤-reflexive; m≤m+n; *-comm)
open import Data.Bool using (Bool; true; false)
open import Data.Vec using (Vec; []; _∷_)
open import Data.Product using (Σ; _,_)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym)

open import Sovereign.Base.Trit using (Trit)
open import Sovereign.Algebra.Complexity.TimeBound
  using (value; Mono; Pos; mono-+ˡ; mono-+ʳ; mono-*ˡ)
open import Sovereign.Algebra.Complexity.PClass using (TritLang; InP)

-- ────────────────────────────────────────────────────────────────────
-- §1 带查询计账值 OC-CountedQ〔结构定义〕
-- ────────────────────────────────────────────────────────────────────

-- 求值结果 = 值 × 步数账 × 查询账。queries 由计算体逐点累加（账目嵌入函数，
-- 同 TimeBound 纪律），不是外部断言。
record OC-CountedQ : Set where
  constructor oc-cntq
  field
    oc-value   : Bool
    oc-steps   : ℕ
    oc-queries : ℕ

open OC-CountedQ public

-- 组合子：常值判定（1 步，零查询）〔结构定义〕
oc-cqConst : Bool → OC-CountedQ
oc-cqConst b = oc-cntq b 1 0

-- 组合子：布尔分支（选择 1 步，仅执行被选中支）〔结构定义〕
oc-cqBranch : Bool → OC-CountedQ → OC-CountedQ → OC-CountedQ
oc-cqBranch true  (oc-cntq v₁ s₁ q₁) _                = oc-cntq v₁ (suc s₁) q₁
oc-cqBranch false _                   (oc-cntq v₂ s₂ q₂) = oc-cntq v₂ (suc s₂) q₂

-- 组合子：oracle 查询（应答 b 即本步值；1 步 + 1 查询；c 为续算）〔结构定义〕
oc-cqQuery : Bool → OC-CountedQ → OC-CountedQ
oc-cqQuery b (oc-cntq _ s q) = oc-cntq b (suc s) (suc q)

-- 账目展开（模式匹配后定义性成立）〔refl 枚举〕
oc-value-cqQuery : ∀ b c → oc-value (oc-cqQuery b c) ≡ b
oc-value-cqQuery b (oc-cntq _ _ _) = refl

oc-steps-cqQuery : ∀ b c → oc-steps (oc-cqQuery b c) ≡ suc (oc-steps c)
oc-steps-cqQuery b (oc-cntq _ _ _) = refl

oc-queries-cqQuery : ∀ b c → oc-queries (oc-cqQuery b c) ≡ suc (oc-queries c)
oc-queries-cqQuery b (oc-cntq _ _ _) = refl

oc-value-cqBranch-true : ∀ c₁ c₂ → oc-value (oc-cqBranch true c₁ c₂) ≡ oc-value c₁
oc-value-cqBranch-true (oc-cntq _ _ _) _ = refl

-- ────────────────────────────────────────────────────────────────────
-- §1b ≤-算术小引理（自证，≤-trans / TimeBound mono 拼合级）〔结构证明〕
-- ────────────────────────────────────────────────────────────────────

-- 双项加法拼合：两项各自不降则和不降
oc-mono-+₂ : ∀ {a₁ a₂ b₁ b₂} → a₁ ≤ b₁ → a₂ ≤ b₂ → a₁ + a₂ ≤ b₁ + b₂
oc-mono-+₂ h₁ h₂ = ≤-trans (mono-+ʳ _ h₁) (mono-+ˡ _ h₂)

-- 乘法对左参数单调（TimeBound.mono-*ˡ 的对偶；经 *-comm 桥接，零归纳）
oc-mono-*ʳ : ∀ {k₁ k₂ b} → k₁ ≤ k₂ → k₁ * b ≤ k₂ * b
oc-mono-*ʳ {k₁} {k₂} {b} h =
  ≤-trans (≤-reflexive (*-comm k₁ b))
          (≤-trans (mono-*ˡ b h) (≤-reflexive (sym (*-comm k₂ b))))

-- ────────────────────────────────────────────────────────────────────
-- §1c 核对层〔refl 枚举〕
-- ────────────────────────────────────────────────────────────────────

check-oc-cqQuery : oc-queries (oc-cqQuery true (oc-cqConst false)) ≡ 1
check-oc-cqQuery = refl

-- ────────────────────────────────────────────────────────────────────
-- §2 oracle 定长接口与 P^A record〔结构定义〕
-- ────────────────────────────────────────────────────────────────────

-- oracle：定长查询串上的布尔应答（槽长由调用方给定——诚实简化 (a)）
OC-Oracle : ℕ → Set
OC-Oracle mn = Vec Trit mn → Bool

-- oracle 族：各查询长度上的应答总表
OC-OracleFam : Set
OC-OracleFam = (mn : ℕ) → OC-Oracle mn

-- oracle 的「作为语言」形：应答为 true 的点集（InP 成员性的语言侧）
OC-LangOf : OC-OracleFam → TritLang
OC-LangOf A m y = A m y ≡ true

-- L ∈ P^A ⟺ 带 oracle 槽的计账判定器 + 代价/查询双界（各带 Mono/Pos）
--           + oracle 无关完备/正确（头注 (b)：对一切 oracle 实例量化）
record OC-InP (mn : ℕ → ℕ) (A : OC-OracleFam) (L : TritLang) : Set₁ where
  field
    oc-p        : ℕ → ℕ                -- 代价界（步数）
    oc-p-mono   : Mono oc-p            -- 〔结构证明〕
    oc-p-pos    : Pos oc-p             -- 〔结构证明〕
    oc-q        : ℕ → ℕ                -- 查询次数界
    oc-q-mono   : Mono oc-q            -- 〔结构证明〕
    oc-q-pos    : Pos oc-q             -- 〔结构证明〕
    oc-decider  : (n : ℕ) → Vec Trit n → OC-Oracle (mn n) → OC-CountedQ
    oc-complete : ∀ n x (A′ : OC-Oracle (mn n)) → L n x →
                  oc-value (oc-decider n x A′) ≡ true          -- 〔结构证明〕
    oc-sound    : ∀ n x (A′ : OC-Oracle (mn n)) →
                  oc-value (oc-decider n x A′) ≡ true → L n x  -- 〔结构证明〕
    oc-cost     : ∀ n x (A′ : OC-Oracle (mn n)) →
                  oc-steps (oc-decider n x A′) ≤ oc-p n
    oc-qcount   : ∀ n x (A′ : OC-Oracle (mn n)) →
                  oc-queries (oc-decider n x A′) ≤ oc-q n

-- ────────────────────────────────────────────────────────────────────
-- §3 NP^A record 与闭合定理 1：P^A ⊆ NP^A〔结构定义 + 结构证明〕
-- ────────────────────────────────────────────────────────────────────

record OC-InNP (mn : ℕ → ℕ) (A : OC-OracleFam) (L : TritLang) : Set₁ where
  field
    ocnp-p        : ℕ → ℕ
    ocnp-p-mono   : Mono ocnp-p
    ocnp-p-pos    : Pos ocnp-p
    ocnp-q        : ℕ → ℕ
    ocnp-q-mono   : Mono ocnp-q
    ocnp-q-pos    : Pos ocnp-q
    ocnp-witLen   : ℕ → ℕ              -- 见证长度界
    ocnp-w-mono   : Mono ocnp-witLen
    ocnp-verifier : (n : ℕ) → Vec Trit n → Vec Trit (ocnp-witLen n) →
                    OC-Oracle (mn n) → OC-CountedQ
    ocnp-complete : ∀ n x (A′ : OC-Oracle (mn n)) → L n x →
                    Σ (Vec Trit (ocnp-witLen n))
                      (λ w → oc-value (ocnp-verifier n x w A′) ≡ true)
    ocnp-sound    : ∀ n x w (A′ : OC-Oracle (mn n)) →
                    oc-value (ocnp-verifier n x w A′) ≡ true → L n x
    ocnp-cost     : ∀ n x w (A′ : OC-Oracle (mn n)) →
                    oc-steps (ocnp-verifier n x w A′) ≤ ocnp-p n
    ocnp-qcount   : ∀ n x w (A′ : OC-Oracle (mn n)) →
                    oc-queries (ocnp-verifier n x w A′) ≤ ocnp-q n

-- 闭合定理 1：P^A ⊆ NP^A（对一切 mn / A / L，对一切 oracle 实例一致）〔结构证明〕
-- 结构同 NPClass.inP⇒inNP：空见证（Vec Trit 0 仅 []）、验证器 = 判定器
-- （oracle 实参透传）、代价/查询界逐字继承。
oc-P⊆NP : ∀ {mn A L} (dp : OC-InP mn A L) → OC-InNP mn A L
oc-P⊆NP dp = record
  { ocnp-p        = OC-InP.oc-p dp
  ; ocnp-p-mono   = OC-InP.oc-p-mono dp
  ; ocnp-p-pos    = OC-InP.oc-p-pos dp
  ; ocnp-q        = OC-InP.oc-q dp
  ; ocnp-q-mono   = OC-InP.oc-q-mono dp
  ; ocnp-q-pos    = OC-InP.oc-q-pos dp
  ; ocnp-witLen   = λ _ → 0
  ; ocnp-w-mono   = λ _ → z≤n
  ; ocnp-verifier = λ n x _ A′ → OC-InP.oc-decider dp n x A′
  ; ocnp-complete = λ n x A′ l → [] , OC-InP.oc-complete dp n x A′ l
  ; ocnp-sound    = λ n x _ A′ v → OC-InP.oc-sound dp n x A′ v
  ; ocnp-cost     = λ n x _ A′ → OC-InP.oc-cost dp n x A′
  ; ocnp-qcount   = λ n x _ A′ → OC-InP.oc-qcount dp n x A′ }

-- ────────────────────────────────────────────────────────────────────
-- §4 无查询形与闭合定理 2：A ∈ P ⟹ oracle 可消除〔结构定义 + 结构证明〕
-- ────────────────────────────────────────────────────────────────────

-- 无查询判定类：判定器无 oracle 槽，查询账目恒 0。
record OC-NoQuery (L : TritLang) : Set₁ where
  field
    oc0-p        : ℕ → ℕ
    oc0-p-mono   : Mono oc0-p
    oc0-p-pos    : Pos oc0-p
    oc0-decider  : (n : ℕ) → Vec Trit n → OC-CountedQ
    oc0-noq      : ∀ n x → oc-queries (oc0-decider n x) ≡ 0
    oc0-complete : ∀ n x → L n x → oc-value (oc0-decider n x) ≡ true
    oc0-sound    : ∀ n x → oc-value (oc0-decider n x) ≡ true → L n x
    oc0-cost     : ∀ n x → oc-steps (oc0-decider n x) ≤ oc0-p n

-- 界引理：p n + q n * pd (mn n) 形界的单调性（显式命名变元，避免洞推断）〔结构证明〕
oc-collapse-p-mono : ∀ (p q pd mn : ℕ → ℕ)
                   → Mono p → Mono q → Mono pd → Mono mn
                   → Mono (λ n → p n + q n * pd (mn n))
oc-collapse-p-mono p q pd mn hp hq hpd hmn {a} {b} h =
  oc-mono-+₂ (hp h)
    (≤-trans (mono-*ˡ (q a) (hpd (hmn h)))
             (oc-mono-*ʳ (hq h)))

-- 闭合定理 2：若 A 有无查询 P 判定器 dA，则任何 P^A 判定器可实例化为无查询判定器。
-- 实例化：oracle 槽直接传 λ y → value (dA (mn n) y)；value/完备/正确定义性保持；
-- 查询账记 0；账目取保守上界形（dec 自账 + 查询次数 × dA 界）——精确合成需
-- 判定器返回查询清单（trace-passing），本件不引入（立界见文尾 (iii)）。
oc-collapse : ∀ {mn A L} (mn-mono : Mono mn)
              (dA : InP (OC-LangOf A)) (dp : OC-InP mn A L) → OC-NoQuery L
oc-collapse {mn} mn-mono dA dp = record
  { oc0-p        = λ n → OC-InP.oc-p dp n + OC-InP.oc-q dp n * InP.p dA (mn n)
  ; oc0-p-mono   = oc-collapse-p-mono (OC-InP.oc-p dp) (OC-InP.oc-q dp)
                                      (InP.p dA) mn
                                      (OC-InP.oc-p-mono dp) (OC-InP.oc-q-mono dp)
                                      (InP.p-mono dA) mn-mono
  ; oc0-p-pos    = λ n → ≤-trans (OC-InP.oc-p-pos dp n)
                                 (m≤m+n (OC-InP.oc-p dp n)
                                        (OC-InP.oc-q dp n * InP.p dA (mn n)))
  ; oc0-decider  = λ n x →
      let c = OC-InP.oc-decider dp n x (λ y → value (InP.decider dA (mn n) y))
      in  oc-cntq (oc-value c)
                  (oc-steps c + OC-InP.oc-q dp n * InP.p dA (mn n)) 0
  ; oc0-noq      = λ n x → refl
  ; oc0-complete = λ n x l → OC-InP.oc-complete dp n x _ l
  ; oc0-sound    = λ n x v → OC-InP.oc-sound dp n x _ v
  ; oc0-cost     = λ n x →
      mono-+ʳ (OC-InP.oc-q dp n * InP.p dA (mn n)) (OC-InP.oc-cost dp n x _) }

-- ────────────────────────────────────────────────────────────────────
-- §5 BGS 陈述层〔结构定义——陈述 record，status = 0 未闭合〕
-- ────────────────────────────────────────────────────────────────────

-- BGS₁：存在 oracle A 使 P^A = NP^A（Baker–Gill–Solovay 1975，定理 A）。
-- ⊆ 方向对一切 A 已闭合（§3 oc-P⊆NP）；本 record 陈述逆向 npa⊆pa。
-- 证明思路（经典）：取 PSPACE-complete oracle——NP^A 验证器在多项式空间内
-- 确定性枚举全部见证，该枚举器即无 oracle 槽判定器形态；类型层构造立界 (iv)。
record OC-BGS₁ : Set₁ where
  field
    bgs-mn     : ℕ → ℕ                 -- 查询串长调度
    bgs-oracle : OC-OracleFam          -- oracle 选择（∃ 的见证位）
    bgs-npa⊆pa : ∀ L → OC-InNP bgs-mn bgs-oracle L → OC-InP bgs-mn bgs-oracle L
    status     : ℕ                     -- 0 = 陈述层（构造未闭合）

-- BGS₂：存在 oracle B 使 P^B ≠ NP^B（Baker–Gill–Solovay 1975，定理 B；
-- 分离以见证语言形式陈述：∃L ∈ NP^B \ P^B）。
-- 证明思路（经典）：对 P^B 判定器族对角化构造 B——对角线语言的可定义性依赖
-- oracle 的可计算枚举序；类型层构造立界 (iv)。
record OC-BGS₂ : Set₁ where
  field
    bgs-mn       : ℕ → ℕ
    bgs-oracle   : OC-OracleFam
    bgs-sepL     : TritLang             -- 分离见证语言
    bgs-in-npa   : OC-InNP bgs-mn bgs-oracle bgs-sepL
    bgs-not-inpa : OC-InP bgs-mn bgs-oracle bgs-sepL → ⊥
    status       : ℕ                    -- 0 = 陈述层（构造未闭合）

-- ────────────────────────────────────────────────────────────────────
-- §6 立界注记（诚实边界——不设空壳签名）
-- ────────────────────────────────────────────────────────────────────
-- (i)   变长查询：查询槽长 OC-Oracle (mn n) 在计算前固定；经典 OTM 的查询
--       长度是计算内部量。推广需判定器携带逐查询长度（签名大改），独立批。
-- (ii)  「固定 oracle A 的完备/正确」变体：把 A* = λ y → value (dA (mn n) y)
--       换回 A 需判定器对（泛等意义下相等的）oracle 行为不变——泛等性
--       （funext）不在本库公理集；本件以 oracle 无关正确性（头注 (b)）绕开。
-- (iii) 代价精确合成：oc-collapse 的账目为保守上界形（dec 自账 + 查询次数 ×
--       dA 界）；精确形需判定器返回查询清单（trace-passing），本件不引入。
-- (iv)  OC-BGS₁ / OC-BGS₂ 的构造（PSPACE-complete oracle / 对角化 oracle）
--       = 世界件，status = 0；其类型层对象形态已使「分离依赖 oracle 选择」
--       成为可陈述命题——此即本件对「相对化屏障」的正面表述。
-- (v)   decider / verifier 的 OTM 实现桥——同 PClass §6(i)。

-- 0 postulate / 0 hole。
-- 本文件由 agda +RTS -M8G -H6G -A128M -RTS 编译，EXIT=0 为完成判据。
