{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Foundation.FMTK-ESO
-- ESO（二阶存在量词）语义层——PvsNP 批四 F6，Fagin 链（NP=ESO）前置语义层
--
-- 定位：FMTK（k 变元 FO 片段）之上的**语义**层。ESO 公式 ψ = ∃R̄. φ：
--   存在 pool 个新关系谓词符号 R̄（各解释为载体 Fin n 上的**一元**关系，
--   解释向量型 = Fin pool → Fin n → Bool），量化自由核 φ 取 FTK-Formula k
--   经 FTK-ESO-up 升格入扩展词汇（唯一语法增量：新谓词原子 FTK-ESO-atomP）。
--   关系解释扩展 record FTK-ESO-Ext（底结构 + R̄ 解释）：给 R̄ 一组解释后
--   核公式即可求值（FTK-ESO-evalExt）。M ⊨ ψ := Σ R̄ 解释使核真（Σ 型承载，
--   FTK-ESO-Sat）；解释空间 2^(n·pool) 有限 ⟹ 可判定求值走枚举
--   （FTK-ESO-decide，Bool 通道），枚举命中 ⟹ Σ 见证（FTK-ESO-decide-sound）。
--
--   本件是 Fagin 定理（NP=ESO）的前置语义层：只立「∃R̄ 解释」的承载面与
--   判定面。**Fagin 定理本体 W2 立界不排期**（归译/抵达性均不在本件）。
--
-- 分级标注：〔结构定义〕〔结构证明〕〔核对〕〔立界注记〕（同库惯例）。
-- 0 postulate / 0 hole。

module Sovereign.Foundation.FMTK-ESO where

open import Data.List using (List; []; _∷_; map; concatMap)
open import Data.Bool using (Bool; true; false; not; _∧_; _∨_)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (Σ-syntax; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂)

import Sovereign.Foundation.FiniteModelTheory as FMT
import Sovereign.Foundation.FMTK as FTK

-- ────────────────────────────────────────────────────────────────────
-- §1 FTK-ESO-Formula：扩展词汇 FO 片段〔结构定义〕
-- ────────────────────────────────────────────────────────────────────
-- 核语法与 FTK-Formula k 同构（R/S/等式原子 + ¬/∧/∨/逐变元 ∃ 语义枚举），
-- 唯一增量 FTK-ESO-atomP：二阶存在谓词原子（p : Fin pool 选符号，
-- x : Fin k 变元）。自由核本体仍是 FTK-Formula k，经 §3 FTK-ESO-up 升格。

data FTK-ESO-Formula (pool k : ℕ) : Set where
  FTK-ESO-atomR  : Fin k → FTK-ESO-Formula pool k
  FTK-ESO-atomS  : Fin k → Fin k → FTK-ESO-Formula pool k
  FTK-ESO-atomEq : Fin k → Fin k → FTK-ESO-Formula pool k
  FTK-ESO-atomP  : Fin pool → Fin k → FTK-ESO-Formula pool k
  FTK-ESO-bot    : FTK-ESO-Formula pool k
  FTK-ESO-neg    : FTK-ESO-Formula pool k → FTK-ESO-Formula pool k
  FTK-ESO-or     : FTK-ESO-Formula pool k → FTK-ESO-Formula pool k → FTK-ESO-Formula pool k
  FTK-ESO-and    : FTK-ESO-Formula pool k → FTK-ESO-Formula pool k → FTK-ESO-Formula pool k
  FTK-ESO-ex     : Fin k → FTK-ESO-Formula pool k → FTK-ESO-Formula pool k

-- ────────────────────────────────────────────────────────────────────
-- §2 关系解释扩展 record 与求值器〔结构定义〕
-- ────────────────────────────────────────────────────────────────────
-- FTK-ESO-Ext = 底结构（FMT.Structure 口径不变）+ R̄ 一元解释向量。
-- 「给 R̄ 一组解释后核公式可 evalF」：FTK-ESO-ext 包装 → FTK-ESO-evalExt 求值。

record FTK-ESO-Ext (n pool : ℕ) : Set where
  field
    ext-base : FMT.Structure n
    ext-P    : Fin pool → Fin n → Bool

FTK-ESO-ext : ∀ {n pool : ℕ} → FMT.Structure n → (Fin pool → Fin n → Bool) → FTK-ESO-Ext n pool
FTK-ESO-ext M R = record { ext-base = M ; ext-P = R }

FTK-ESO-env : ℕ → ℕ → Set
FTK-ESO-env n k = Fin k → Fin n

-- 平展求值器（M 与 R̄ 分列——Σ 承载与枚举的工作马）
FTK-ESO-evalFlat : ∀ {n k pool : ℕ} → FMT.Structure n → (Fin pool → Fin n → Bool) →
  FTK-ESO-env n k → FTK-ESO-Formula pool k → Bool
FTK-ESO-evalFlat M R ρ (FTK-ESO-atomR x)    = FMT.Structure.R₁ M (ρ x)
FTK-ESO-evalFlat M R ρ (FTK-ESO-atomS x y)  = FMT.Structure.S₂ M (ρ x) (ρ y)
FTK-ESO-evalFlat M R ρ (FTK-ESO-atomEq x y) = FTK.FTK-ρeq ρ x y
FTK-ESO-evalFlat M R ρ (FTK-ESO-atomP p x)  = R p (ρ x)
FTK-ESO-evalFlat M R ρ FTK-ESO-bot          = false
FTK-ESO-evalFlat M R ρ (FTK-ESO-neg φ)      = not (FTK-ESO-evalFlat M R ρ φ)
FTK-ESO-evalFlat M R ρ (FTK-ESO-or φ ψ)     = FTK-ESO-evalFlat M R ρ φ ∨ FTK-ESO-evalFlat M R ρ ψ
FTK-ESO-evalFlat M R ρ (FTK-ESO-and φ ψ)    = FTK-ESO-evalFlat M R ρ φ ∧ FTK-ESO-evalFlat M R ρ ψ
FTK-ESO-evalFlat M R ρ (FTK-ESO-ex x φ)     =
  FTK.FTK-anyOf (λ v → FTK-ESO-evalFlat M R (FTK.FTK-extend ρ x v) φ)

-- Ext 形求值（①的直陈面）
FTK-ESO-evalExt : ∀ {n k pool : ℕ} → FTK-ESO-Ext n pool → FTK-ESO-env n k →
  FTK-ESO-Formula pool k → Bool
FTK-ESO-evalExt E ρ ψ =
  FTK-ESO-evalFlat (FTK-ESO-Ext.ext-base E) (FTK-ESO-Ext.ext-P E) ρ ψ

-- ────────────────────────────────────────────────────────────────────
-- §3 FTK-ESO-up：自由核升格与求值守恒〔结构定义/结构证明〕
-- ────────────────────────────────────────────────────────────────────
-- 量化自由核 = FTK-Formula k（不动其语法），升格映射逐构造子嵌入；
-- 守恒定理：升格核对**任意** R̄ 解释下与 FTK 求值逐点一致——ESO 层对
-- 纯 FO 核零语义漂移（③ AtLeast-k 对照的技术基座）。

FTK-ESO-up : ∀ {k pool : ℕ} → FTK.FTK-Formula k → FTK-ESO-Formula pool k
FTK-ESO-up (FTK.FTK-atomR x)    = FTK-ESO-atomR x
FTK-ESO-up (FTK.FTK-atomS x y)  = FTK-ESO-atomS x y
FTK-ESO-up (FTK.FTK-atomEq x y) = FTK-ESO-atomEq x y
FTK-ESO-up FTK.FTK-bot          = FTK-ESO-bot
FTK-ESO-up (FTK.FTK-neg φ)      = FTK-ESO-neg (FTK-ESO-up φ)
FTK-ESO-up (FTK.FTK-or φ ψ)     = FTK-ESO-or (FTK-ESO-up φ) (FTK-ESO-up ψ)
FTK-ESO-up (FTK.FTK-and φ ψ)    = FTK-ESO-and (FTK-ESO-up φ) (FTK-ESO-up ψ)
FTK-ESO-up (FTK.FTK-ex x φ)     = FTK-ESO-ex x (FTK-ESO-up φ)

-- ∃ 枚举的外延同余（up-eval 的 ∃ 案所需；泛型 n 归纳）
FTK-ESO-anyOf-cong : ∀ {n : ℕ} (f g : Fin n → Bool) → (∀ v → f v ≡ g v) →
  FTK.FTK-anyOf f ≡ FTK.FTK-anyOf g
FTK-ESO-anyOf-cong {zero}  f g h = refl
FTK-ESO-anyOf-cong {suc n} f g h =
  cong₂ _∨_ (h fzero)
    (FTK-ESO-anyOf-cong (λ i → f (fsuc i)) (λ i → g (fsuc i)) (λ v → h (fsuc v)))

-- 求值守恒：逐案归纳，原子/bot 案 refl、命题案 cong/cong₂、∃ 案 anyOf-cong
FTK-ESO-up-eval : ∀ {n k pool : ℕ} (M : FMT.Structure n) (R : Fin pool → Fin n → Bool)
  (ρ : FTK-ESO-env n k) (φ : FTK.FTK-Formula k) →
  FTK-ESO-evalFlat M R ρ (FTK-ESO-up φ) ≡ FTK.FTK-evalF M ρ φ
FTK-ESO-up-eval M R ρ (FTK.FTK-atomR x)    = refl
FTK-ESO-up-eval M R ρ (FTK.FTK-atomS x y)  = refl
FTK-ESO-up-eval M R ρ (FTK.FTK-atomEq x y) = refl
FTK-ESO-up-eval M R ρ FTK.FTK-bot          = refl
FTK-ESO-up-eval M R ρ (FTK.FTK-neg φ)      = cong not (FTK-ESO-up-eval M R ρ φ)
FTK-ESO-up-eval M R ρ (FTK.FTK-or φ ψ)     =
  cong₂ _∨_ (FTK-ESO-up-eval M R ρ φ) (FTK-ESO-up-eval M R ρ ψ)
FTK-ESO-up-eval M R ρ (FTK.FTK-and φ ψ)    =
  cong₂ _∧_ (FTK-ESO-up-eval M R ρ φ) (FTK-ESO-up-eval M R ρ ψ)
FTK-ESO-up-eval M R ρ (FTK.FTK-ex x φ)     =
  FTK-ESO-anyOf-cong _ _ (λ v → FTK-ESO-up-eval M R (FTK.FTK-extend ρ x v) φ)

-- ────────────────────────────────────────────────────────────────────
-- §4 FTK-ESO-Sat / FTK-ESO-decide：ESO-SAT 语义与可判定枚举〔结构定义/结构证明〕
-- ────────────────────────────────────────────────────────────────────
-- ② M ⊨ ψ（赋值 ρ 下）⟺ ∃ R̄ 解释使核真——Σ 型承载。解释空间有限
--   （一元表 2^n × pool 折笛卡尔积 = 2^(n·pool)），可判定求值走枚举：
--   FTK-ESO-decide 沿 Bool 通道 anyList 扫全解释列表。

FTK-ESO-Sat : ∀ (n k pool : ℕ) → FMT.Structure n → FTK-ESO-env n k →
  FTK-ESO-Formula pool k → Set
FTK-ESO-Sat n k pool M ρ ψ =
  Σ[ R ∈ (Fin pool → Fin n → Bool) ] FTK-ESO-evalFlat M R ρ ψ ≡ true

-- 解释空间枚举：一元真值表（2^n 个，头位扩展递推）→ pool 折笛卡尔积
FTK-ESO-bools : List Bool
FTK-ESO-bools = true ∷ false ∷ []

FTK-ESO-ext1 : ∀ {n : ℕ} → (Fin n → Bool) → Bool → Fin (suc n) → Bool
FTK-ESO-ext1 t b fzero    = b
FTK-ESO-ext1 t b (fsuc i) = t i

FTK-ESO-extP : ∀ {p n : ℕ} → (Fin p → Fin n → Bool) → (Fin n → Bool) →
  Fin (suc p) → Fin n → Bool
FTK-ESO-extP f t fzero    = t
FTK-ESO-extP f t (fsuc i) = f i

FTK-ESO-tables : (n : ℕ) → List (Fin n → Bool)
FTK-ESO-tables zero    = (λ ()) ∷ []
FTK-ESO-tables (suc n) =
  concatMap (λ t → map (FTK-ESO-ext1 t) FTK-ESO-bools) (FTK-ESO-tables n)

FTK-ESO-vec : (pool n : ℕ) → List (Fin pool → Fin n → Bool)
FTK-ESO-vec zero    n = (λ ()) ∷ []
FTK-ESO-vec (suc p) n =
  concatMap (λ f → map (FTK-ESO-extP f) (FTK-ESO-tables n)) (FTK-ESO-vec p n)

-- Bool 通道 anyList（List 上的 ∨ 折叠；免引 stdlib any——本件自带前缀名）
FTK-ESO-anyList : ∀ {a} → {A : Set a} → (A → Bool) → List A → Bool
FTK-ESO-anyList _ []         = false
FTK-ESO-anyList f (x ∷ xs)  = f x ∨ FTK-ESO-anyList f xs

-- 析取反演（anyList 声音性的分解件；显式 ⊎ 承载，不靠 with 抽象摸黑）
FTK-ESO-∨-inv : ∀ (a b : Bool) → (a ∨ b) ≡ true → (a ≡ true) ⊎ (b ≡ true)
FTK-ESO-∨-inv true  b p = inj₁ refl
FTK-ESO-∨-inv false b p = inj₂ p

-- 枚举声音性：命中 ⟹ Σ 见证（anyList 析取分解，逐案归纳）
FTK-ESO-anyList-sound : ∀ {a} → {A : Set a} (f : A → Bool) (l : List A) →
  FTK-ESO-anyList f l ≡ true → Σ[ x ∈ A ] f x ≡ true
FTK-ESO-anyList-sound f []         ()
FTK-ESO-anyList-sound f (x ∷ xs)  p
  with FTK-ESO-∨-inv (f x) (FTK-ESO-anyList f xs) p
... | inj₁ fx   = x , fx
... | inj₂ rest = FTK-ESO-anyList-sound f xs rest

-- 可判定求值：沿解释列表扫「核真」
FTK-ESO-decide : ∀ (n k pool : ℕ) → FMT.Structure n → FTK-ESO-env n k →
  FTK-ESO-Formula pool k → Bool
FTK-ESO-decide n k pool M ρ ψ =
  FTK-ESO-anyList (λ R → FTK-ESO-evalFlat M R ρ ψ) (FTK-ESO-vec pool n)

-- 判定器声音性：decide ≡ true ⟹ Σ 见证实取（②的构造性半边）
FTK-ESO-decide-sound : ∀ (n k pool : ℕ) (M : FMT.Structure n) (ρ : FTK-ESO-env n k)
  (ψ : FTK-ESO-Formula pool k) →
  FTK-ESO-decide n k pool M ρ ψ ≡ true → FTK-ESO-Sat n k pool M ρ ψ
FTK-ESO-decide-sound n k pool M ρ ψ p =
  FTK-ESO-anyList-sound (λ R → FTK-ESO-evalFlat M R ρ ψ) (FTK-ESO-vec pool n) p

-- ────────────────────────────────────────────────────────────────────
-- §5 核对层〔核对〕
-- ────────────────────────────────────────────────────────────────────
-- 5.1 ESO 原生实例：ψSplit = ∃P.(P 非空 ∧ P 非全域)——可满足 ⟺ 载体 ≥ 2
--     （二阶量词承载力的最小语义锚：二阶解释 R̄ 真正进入求值）

FTK-ESO-ψSplit : FTK-ESO-Formula 1 2
FTK-ESO-ψSplit =
  FTK-ESO-and (FTK-ESO-ex fzero (FTK-ESO-atomP fzero fzero))
              (FTK-ESO-ex fzero (FTK-ESO-neg (FTK-ESO-atomP fzero fzero)))

FTK-ESO-M1 : FMT.Structure 1
FTK-ESO-M1 = record { R₁ = λ _ → true ; S₂ = λ _ _ → true }

FTK-ESO-ρ02 : FTK-ESO-env 2 2
FTK-ESO-ρ02 = λ _ → fzero

FTK-ESO-ρ12 : FTK-ESO-env 1 2
FTK-ESO-ρ12 = λ _ → fzero

-- 核对①：2 元结构上 ψSplit 可满足——Σ 见证经枚举声音性**实取**
--         （4 个解释逐扫：全真/全假两解释落空，混合解释命中）
FTK-ESO-check-split-yes : FTK-ESO-Sat 2 2 1 FMT.M2 FTK-ESO-ρ02 FTK-ESO-ψSplit
FTK-ESO-check-split-yes =
  FTK-ESO-decide-sound 2 2 1 FMT.M2 FTK-ESO-ρ02 FTK-ESO-ψSplit refl

-- 核对②：1 元结构上 ψSplit 不可满足（2 个解释全假，闭式归 false）
FTK-ESO-check-split-no :
  FTK-ESO-decide 1 2 1 FTK-ESO-M1 FTK-ESO-ρ12 FTK-ESO-ψSplit ≡ false
FTK-ESO-check-split-no = refl

-- 5.2 ③ AtLeast-k 的 ESO 表达：pool = 0 退化面（无二阶符号，纯 FO 核）
--     与 FTK 已有形逐点对照——ESO 层对纯 FO 核零语义漂移（§3 守恒）。

FTK-ESO-R0 : ∀ {n : ℕ} → Fin 0 → Fin n → Bool
FTK-ESO-R0 = λ ()

FTK-ESO-ψAL3 : FTK-ESO-Formula 0 3
FTK-ESO-ψAL3 = FTK-ESO-up (FTK.FTK-AtLeast 3)

FTK-ESO-ρ03 : FTK-ESO-env 3 3
FTK-ESO-ρ03 = λ _ → fzero

FTK-ESO-ρ23 : FTK-ESO-env 2 3
FTK-ESO-ρ23 = λ _ → fzero

-- 核对③：对照 FTK 已有形——升格核求值 ≡ FTK-AtLeast 3 求值（守恒引理实例）
FTK-ESO-check-AL3-cons : ∀ (M : FMT.Structure 3) (ρ : FTK-ESO-env 3 3) →
  FTK-ESO-evalFlat M FTK-ESO-R0 ρ FTK-ESO-ψAL3 ≡
  FTK.FTK-evalF M ρ (FTK.FTK-AtLeast 3)
FTK-ESO-check-AL3-cons M ρ = FTK-ESO-up-eval M FTK-ESO-R0 ρ (FTK.FTK-AtLeast 3)

-- 核对④：3 元结构 ⊨ ψAL3（枚举单解释 [λ ()] 命中，27 支闭式归 true）
FTK-ESO-check-AL3-yes :
  FTK-ESO-decide 3 3 0 FTK.FTK-M3 FTK-ESO-ρ03 FTK-ESO-ψAL3 ≡ true
FTK-ESO-check-AL3-yes = refl

-- 核对⑤：2 元结构 ⊭ ψAL3——对照 FMTK 核对⑧（鸽笼，8 支闭式归 false）
FTK-ESO-check-AL3-no :
  FTK-ESO-decide 2 3 0 FMT.M2 FTK-ESO-ρ23 FTK-ESO-ψAL3 ≡ false
FTK-ESO-check-AL3-no = refl

-- ────────────────────────────────────────────────────────────────────
-- §6 尾注：立界清单（诚实边界——不设空壳签名）〔立界注记〕
-- ────────────────────────────────────────────────────────────────────
-- (i)   枚举完备方向（Sat ⟹ decide ≡ true）：需「任意解释 R̄ 出现在
--       FTK-ESO-vec 列表中」——函数外延面（funext 或库内 OF 件逐点吻合
--       表示）不可免，本件只闭合 decide-sound（命中 ⟹ Σ 见证）；
--       完备方向沿逐点吻合范式另批立。
-- (ii)  句子性类型证书：本件核对实例均为闭式（全变元经 FTK-exBlock 类
--       量化，ρ 无关性是语义事实）；类型级句子证书沿用 FMTK §6(i) 立界
--       （index-weakening / de Bruijn 机器），本件不闭合。
-- (iii) 二阶符号 arity 限**一元**（pool 个 P̄ 各一元）；k 元谓词向量与
--       多元词汇泛化随 Fagin 归译（W2）需要再立。
-- (iv)  Fagin 定理本体（NP = ESO）：归译方向（NP ⟹ ESO，TM 运行形 ⟹
--       关系结构编码）与抵达性方向（ESO ⟹ NP，含枚举的多项式记账）
--       W2 立界不排期——本件只提供其语义承载面与判定面。
-- (v)   枚举代价 2^(n·pool)：可判定 ≠ 多项式；ESO 求值的复杂度计账归
--       W2（Fagin 的 NP 侧恰需该指数面），本件不做复杂度宣称。
-- (vi)  AtLeast-k 对照只立 k = 3 两点（3 元 ⊨ / 2 元 ⊭）；一般 k 沿
--       FMTK §4 公式形与 §3 守恒引理逐 k 可得，未逐一枚举。

-- 0 postulate / 0 hole。
-- 本文件由 agda +RTS -M8G -H6G -A128M -RTS 编译，EXIT=0 为完成判据。
