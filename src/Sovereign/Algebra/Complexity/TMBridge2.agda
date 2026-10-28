{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Algebra.Complexity.TMBridge2
-- Counted↔TM 实例级桥第二旗舰——PvsNP W1 桥接件批三（TMC：双读机 + Dir=L 首实例覆盖）
-- 【边界声明（头注，必须先读）】本件把 TMBridge 实例级桥从「单旗舰 1 步」扩展到「2 步 +
-- 记忆态 + L 移」：语言 L = {w : 首符 ≠ 次符}（长度 ≥2 且 w₀ ≢ w₁ 接受；长度 <2 拒绝），
-- 6 态机 tmc 第二步 δ 出 (qAcc/qRej, t, L) 左移停机——全库 L 支（moveH 的 L 支 + leftLof
-- 非空左带支）首个有居民实例，为 SAT 验证器 TM 化铺范式。「任意 Counted 函数可实现为 TM」
-- 的通用编码桥维持 TMBridge §5(i)（= PClass §6(i) / TimeBound §8(i)）立界，本件不冒充其
-- 闭合；实例提升只对本旗舰对成立，不外推。
-- 【Σ 偏差声明（头注第二必读）】Σ=Trit/空白=T₀ 下「次符=T₀」与「无次符（右带空读出空白）」
-- 在第二步 δ 层不可区分（记忆态面对同一 scan 符 T₀），无法同时闭合 (T₁,T₀)→接受 与 单位串
-- (T₁)→拒绝——故引入独立空白符 4 符字母表 TMC-Σ（□ + 三 trit 码）；函数层仍在 Vec Trit
--（TMC-dec），TMC-tapeOf 编码过桥。TMH-halt-mono（全泛型）直接 import 复用；TMH-tapeOf/
-- hdOf/AcceptsIn 因 Σ 与右带编码不合，以 TMC- 同构件复刻（尾注 ii/iii）——对「直接复用」
-- 的最小必要偏差，任务核对集所迫。
-- 内容六节：§1 字母表/6 态/δ 表（16 显式项 + 停机自持 2 通配）/tmc + L 移停机步 3 项核对；
-- §2 TMC-self + TMC-mono（复用 TMH-halt-mono）；§3 2 步运行核对 6 项 + 冻结 1 项；
-- §4 TMC-neq/TMC-dec（9 案真值表，计账 2 步）；§5 TMC-bridge（双向 9+2 案）；§6 尾注立界。
-- 分级标注约定（与 TMBridge/PClass 一致）：〔结构定义〕/〔结构证明〕/〔refl 枚举〕/〔立界注记〕。
-- 工程注记：runN 的 goN 对泛型 halt 不透明（TMBridge 头注已证）；本件不设泛型步进引理，
-- 步进语义全部走具体实例 defeq（先例 TMH-check-freeze）。
-- 0 postulate / 0 hole。

module Sovereign.Algebra.Complexity.TMBridge2 where

open import Data.Nat using (ℕ; zero; suc; s≤s; z≤n)
open import Data.List using (List; []; _∷_)
open import Data.Bool using (Bool; true; false)
open import Data.Vec using (Vec; []; _∷_)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Sovereign.Base.Trit using (Trit; T₀; T₁; T₂)
open import Sovereign.Algebra.Automata.TuringMachine
  using (TM; TConfig; mkTC; step; runN; HaltsAt; Dir; R; L; tlOf)
open import Sovereign.Algebra.Complexity.TimeBound
  using (Counted; value; steps; StepsLE)
  renaming (cnt to mkCnt)
open import Sovereign.Algebra.Complexity.TMBridge
  using (TMH-halt-mono)

-- ═══ §1 字母表·6 态·δ 表·tmc〔结构定义 + L 移停机步核对〕════════════════════

-- 4 符字母表（Σ 偏差声明见头注）：独立空白符 □ + 三 trit 码。
data TMC-Σ : Set where
  TMC-□ TMC-s₀ TMC-s₁ TMC-s₂ : TMC-Σ

-- 6 态（任务书定名）：扫描态 + 三记忆态 + 接受态 + 拒绝态。接受语义由状态编码
--（库内 TM record 无接受/拒绝双态字段，先例 TMH-QH）。
data TMC-Q : Set where
  qScan qSawT₀ qSawT₁ qSawT₂ qAcc qRej : TMC-Q

TMC-sym : Trit → TMC-Σ
TMC-sym T₀ = TMC-s₀
TMC-sym T₁ = TMC-s₁
TMC-sym T₂ = TMC-s₂

-- δ 表：qScan×4 + 记忆态 3×4 = 16 显式项 + 停机自持 2 通配（语义 6 项）。
-- 记忆态行全部 δ 出 (…, t, L) 左移停机——Dir=L 与 leftLof 非空左带支的全库
-- 首实例；qScan 读 □（空带）1 步即拒 R。停机态自持（§2 self 基座；step 对
-- halt 态短路，方向语义自由，取 R 从 TMH 先例）。
TMC-δ : TMC-Q → TMC-Σ → TMC-Q × TMC-Σ × Dir
TMC-δ qScan  TMC-□  = (qRej   , TMC-□  , R)  -- 空带：1 步即拒
TMC-δ qScan  TMC-s₀ = (qSawT₀ , TMC-s₀ , R)  -- 读首符记入状态
TMC-δ qScan  TMC-s₁ = (qSawT₁ , TMC-s₁ , R)
TMC-δ qScan  TMC-s₂ = (qSawT₂ , TMC-s₂ , R)
TMC-δ qSawT₀ TMC-□  = (qRej   , TMC-□  , L)  -- 无次符（右带空）→ 拒
TMC-δ qSawT₀ TMC-s₀ = (qRej   , TMC-s₀ , L)  -- 相同 → 拒
TMC-δ qSawT₀ TMC-s₁ = (qAcc   , TMC-s₁ , L)  -- 不同 → 接受
TMC-δ qSawT₀ TMC-s₂ = (qAcc   , TMC-s₂ , L)
TMC-δ qSawT₁ TMC-□  = (qRej   , TMC-□  , L)
TMC-δ qSawT₁ TMC-s₀ = (qAcc   , TMC-s₀ , L)  -- (T₁,T₀)≠ → 接受（TMH 系不可闭合案）
TMC-δ qSawT₁ TMC-s₁ = (qRej   , TMC-s₁ , L)
TMC-δ qSawT₁ TMC-s₂ = (qAcc   , TMC-s₂ , L)
TMC-δ qSawT₂ TMC-□  = (qRej   , TMC-□  , L)
TMC-δ qSawT₂ TMC-s₀ = (qAcc   , TMC-s₀ , L)
TMC-δ qSawT₂ TMC-s₁ = (qAcc   , TMC-s₁ , L)
TMC-δ qSawT₂ TMC-s₂ = (qRej   , TMC-s₂ , L)
TMC-δ qAcc   a      = (qAcc   , a      , R)  -- 停机自持 ×2 通配（语义 6 项）
TMC-δ qRej   a      = (qRej   , a      , R)

TMC-halt : TMC-Q → Bool
TMC-halt qScan  = false
TMC-halt qSawT₀ = false
TMC-halt qSawT₁ = false
TMC-halt qSawT₂ = false
TMC-halt qAcc   = true
TMC-halt qRej   = true

tmc : TM TMC-Q TMC-Σ
tmc = record { δ = TMC-δ ; q₀ = qScan ; halt = TMC-halt }

-- 输入词的带表示（对偶 TMH-tapeOf；Σ 换形）
TMC-tapeOf : ∀ (n : ℕ) → Vec Trit n → List TMC-Σ
TMC-tapeOf zero    []       = []
TMC-tapeOf (suc n) (t ∷ ts) = TMC-sym t ∷ TMC-tapeOf n ts

-- 带首（对偶 TMH-hdOf；空带读空白 □）
TMC-hdOf : List TMC-Σ → TMC-Σ
TMC-hdOf []      = TMC-□
TMC-hdOf (t ∷ _) = t

-- 计账谓词（对偶 TMH-AcceptsIn；初头在首符号、空带头在空白格 □——TMBridge
-- §2.2 约定同款）。⚠ 两处工程要点：①停机态参数名取 qEnd——具体 TMC-Q 下参数名
-- qAcc 会被 Agda 解析为构造子模式（TMH 先例靠 Q 抽象才绑定成功）；②右带编码取
-- (TMC-hdOf w, tlOf w)（scan=cell₀、右带=余部）而非 TMH 的 (hdOf w, w)——后者
-- 在 2 步机上首步 R 移后 hdOf □ r 重读 cell 0、双读语义尽失（尾注 iii）。
TMC-AcceptsIn : (M : TM TMC-Q TMC-Σ) (qEnd : TMC-Q) (n : ℕ) (w : List TMC-Σ) → Set
TMC-AcceptsIn M qEnd n w =
  (TConfig.st (runN M TMC-□ n (mkTC [] (TM.q₀ M) (TMC-hdOf w) (tlOf w))) ≡ qEnd)
  × TM.halt M qEnd ≡ true

-- 核对层〔refl 枚举〕——编码小桥
TMC-check-tapeOf : TMC-tapeOf 2 (T₁ ∷ T₀ ∷ []) ≡ (TMC-s₁ ∷ TMC-s₀ ∷ [])
TMC-check-tapeOf = refl

TMC-check-tapeOf-empty : TMC-tapeOf 0 [] ≡ []
TMC-check-tapeOf-empty = refl

-- L 移停机步核对〔refl 枚举〕——**全库 L 支 + leftLof 非空左带支首例**，
-- 三形态全覆盖：①右带非空 ②右带空 ③左带≥2（任务书要求至少两种）。
TMC-check-L1 : step tmc TMC-□ (mkTC (TMC-s₁ ∷ []) qSawT₁ TMC-s₀ (TMC-s₁ ∷ [])) ≡ mkTC [] qAcc TMC-s₁ (TMC-s₀ ∷ TMC-s₀ ∷ TMC-s₁ ∷ [])
TMC-check-L1 = refl
TMC-check-L2 : step tmc TMC-□ (mkTC (TMC-s₁ ∷ []) qSawT₁ TMC-s₀ []) ≡ mkTC [] qAcc TMC-s₁ (TMC-s₀ ∷ TMC-s₀ ∷ [])
TMC-check-L2 = refl
TMC-check-L3 : step tmc TMC-□ (mkTC (TMC-s₂ ∷ TMC-s₁ ∷ []) qSawT₂ TMC-s₂ []) ≡ mkTC (TMC-s₁ ∷ []) qRej TMC-s₂ (TMC-s₂ ∷ TMC-s₂ ∷ [])
TMC-check-L3 = refl

-- 停机判据核对〔refl 枚举〕
TMC-check-haltAcc : TMC-halt qAcc ≡ true
TMC-check-haltAcc = refl

TMC-check-haltRej : TMC-halt qRej ≡ true
TMC-check-haltRej = refl

-- ═══ §2 停机自持前提与燃料单调实例化〔结构证明〕══════════════════════════

-- 停机态 step 冻结（先例 tm-head-self；具体实例 defeq，4 个非停机态无居民）
TMC-self : ∀ (q : TMC-Q) (a : TMC-Σ) (l r : List TMC-Σ)
         → TMC-halt q ≡ true
         → step tmc TMC-□ (mkTC l q a r) ≡ mkTC l q a r
TMC-self qScan  a l r ()
TMC-self qSawT₀ a l r ()
TMC-self qSawT₁ a l r ()
TMC-self qSawT₂ a l r ()
TMC-self qAcc   a l r h = refl
TMC-self qRej   a l r h = refl

-- 燃料单调实例化：TMH-halt-mono（全泛型，TMBridge §2.3）对 tmc 特化——「直接
-- import 复用」的兑现点（泛型 Q Σ 恰容 TMC 的 4 符字母表）。
TMC-mono : ∀ (n : ℕ) (c : TConfig TMC-Q TMC-Σ)
         → HaltsAt tmc TMC-□ n c → HaltsAt tmc TMC-□ (suc n) c
TMC-mono = TMH-halt-mono tmc TMC-□ TMC-self

-- ═══ §3 2 步运行核对层〔refl 枚举〕════════════════════════════════════════

-- ①(T₁∷T₀∷T₁) 2 步停 qAcc——L 移步右带非空形态；②(T₁∷T₁) 2 步停 qRej——
-- L 移步右带空形态；③(T₀∷T₂) 停 qAcc ④(T₂∷T₂) 停 qRej（qSawT₀/qSawT₂ 行各一）；
-- ⑤单位串 (T₁) 2 步拒（记忆态读空白 □ 分派拒绝）；⑥空带 1 步即拒。
TMC-check-run1 : TConfig.st (runN tmc TMC-□ 2 (mkTC [] qScan TMC-s₁ (TMC-s₀ ∷ TMC-s₁ ∷ []))) ≡ qAcc
TMC-check-run1 = refl
TMC-check-run2 : TConfig.st (runN tmc TMC-□ 2 (mkTC [] qScan TMC-s₁ (TMC-s₁ ∷ []))) ≡ qRej
TMC-check-run2 = refl
TMC-check-run3 : TConfig.st (runN tmc TMC-□ 2 (mkTC [] qScan TMC-s₀ (TMC-s₂ ∷ []))) ≡ qAcc
TMC-check-run3 = refl
TMC-check-run4 : TConfig.st (runN tmc TMC-□ 2 (mkTC [] qScan TMC-s₂ (TMC-s₂ ∷ []))) ≡ qRej
TMC-check-run4 = refl
TMC-check-run5 : TConfig.st (runN tmc TMC-□ 2 (mkTC [] qScan TMC-s₁ [])) ≡ qRej
TMC-check-run5 = refl
TMC-check-run6 : TConfig.st (runN tmc TMC-□ 1 (mkTC [] qScan TMC-□ [])) ≡ qRej
TMC-check-run6 = refl

-- L 移停机冻结核对（先例 TMH-check-freeze）：2 步 L 移停机后加燃料不改局。
TMC-check-freeze : runN tmc TMC-□ 5 (mkTC [] qScan TMC-s₁ (TMC-s₀ ∷ []))
                 ≡ runN tmc TMC-□ 2 (mkTC [] qScan TMC-s₁ (TMC-s₀ ∷ []))
TMC-check-freeze = refl

-- ═══ §4 函数层对照判定器〔结构定义 + refl 枚举〕═══════════════════════════

-- GF(3) 三值不等真值表（isT₁ 式逐案显式；9 项 = 首二符 3×2 有序对全表，与
-- 记忆态 δ 表的接受/拒绝行一一对应）
TMC-neq : Trit → Trit → Bool
TMC-neq T₀ T₀ = false
TMC-neq T₀ T₁ = true
TMC-neq T₀ T₂ = true
TMC-neq T₁ T₀ = true
TMC-neq T₁ T₁ = false
TMC-neq T₁ T₂ = true
TMC-neq T₂ T₀ = true
TMC-neq T₂ T₁ = true
TMC-neq T₂ T₂ = false

-- 值提取：首二符不等；长度 <2 即 false（不足即拒）。
TMC-neqv : ∀ (n : ℕ) → Vec Trit n → Bool
TMC-neqv (suc (suc n)) (a ∷ b ∷ xs) = TMC-neq a b
TMC-neqv _              _           = false

-- 判定器：dec-Head₁ 范式（单子句 + 值入辅助 + 常数计账）——账目恒 2 步，与
-- tmc 的 2 步停机口径对齐；单子句保证泛型 steps refl（多子句对抽象 x 卡死）。
TMC-dec : ∀ (n : ℕ) → Vec Trit n → Counted Bool
TMC-dec n x = mkCnt (TMC-neqv n x) 2

-- 核对层〔refl 枚举〕
TMC-check-dec-acc : value (TMC-dec 2 (T₁ ∷ T₀ ∷ [])) ≡ true
TMC-check-dec-acc = refl
TMC-check-dec-rej : value (TMC-dec 2 (T₂ ∷ T₂ ∷ [])) ≡ false
TMC-check-dec-rej = refl
TMC-check-dec-short : value (TMC-dec 1 (T₁ ∷ [])) ≡ false
TMC-check-dec-short = refl
TMC-check-dec-empty : value (TMC-dec 0 []) ≡ false
TMC-check-dec-empty = refl

-- 计账对齐〔refl 枚举〕：函数层 steps = TM 层燃料 2，桥两侧时间同阶
--（对偶 TMH-head-steps/StepsLE）。
TMC-dec-steps : ∀ (n : ℕ) (x : Vec Trit n) → steps (TMC-dec n x) ≡ 2
TMC-dec-steps n x = refl

TMC-dec-StepsLE : ∀ (n : ℕ) (x : Vec Trit n) → StepsLE (TMC-dec n x) 2
TMC-dec-StepsLE n x = s≤s (s≤s z≤n)

-- ═══ §5 兼容定理 TMC-bridge——实例级 Counted↔TM 双向闭合（2 步口径）══════

-- → 方向：函数层接受 ⟹ tmc 恰 2 步接受〔refl 枚举 + absurd〕。6 个「≠」案：
-- 首二符具体 → 两步全 definitional（第二步 L 移停机于 qAcc，尾部 xs 开放不碍
-- 状态归约）；3 个「=」案 + 单位串 + 空带：TMC-neqv 归 false，前提无居民。
TMC-bridge→ : ∀ (n : ℕ) (x : Vec Trit n)
            → value (TMC-dec n x) ≡ true
            → TMC-AcceptsIn tmc qAcc 2 (TMC-tapeOf n x)
TMC-bridge→ _ (T₀ ∷ T₁ ∷ _) _ = refl , refl
TMC-bridge→ _ (T₀ ∷ T₂ ∷ _) _ = refl , refl
TMC-bridge→ _ (T₁ ∷ T₀ ∷ _) _ = refl , refl
TMC-bridge→ _ (T₁ ∷ T₂ ∷ _) _ = refl , refl
TMC-bridge→ _ (T₂ ∷ T₀ ∷ _) _ = refl , refl
TMC-bridge→ _ (T₂ ∷ T₁ ∷ _) _ = refl , refl
TMC-bridge→ _ (T₀ ∷ T₀ ∷ _) ()
TMC-bridge→ _ (T₁ ∷ T₁ ∷ _) ()
TMC-bridge→ _ (T₂ ∷ T₂ ∷ _) ()
TMC-bridge→ _ (t ∷ [])        ()
TMC-bridge→ _ []              ()

-- ← 方向：tmc 恰 2 步接受 ⟹ 函数层接受〔refl 枚举 + absurd〕。6 个「≠」案：
-- TMC-neq 值 true 由定义性归约自足（前提冗余不引用，先例 TMH-head-bridge←）；
-- 3 个「=」案 + 空带：2 步必停 qRej，接受前提给出 qRej ≡ qAcc 无居民；单位串
-- 3 案：抽象 t 下 δ(qScan, TMC-sym t) 不归约（工程注记），按 trit 三分后各一 absurd。
TMC-bridge← : ∀ (n : ℕ) (x : Vec Trit n)
            → TMC-AcceptsIn tmc qAcc 2 (TMC-tapeOf n x)
            → value (TMC-dec n x) ≡ true
TMC-bridge← _ (T₀ ∷ T₁ ∷ _) _  = refl
TMC-bridge← _ (T₀ ∷ T₂ ∷ _) _  = refl
TMC-bridge← _ (T₁ ∷ T₀ ∷ _) _  = refl
TMC-bridge← _ (T₁ ∷ T₂ ∷ _) _  = refl
TMC-bridge← _ (T₂ ∷ T₀ ∷ _) _  = refl
TMC-bridge← _ (T₂ ∷ T₁ ∷ _) _  = refl
TMC-bridge← _ (T₀ ∷ T₀ ∷ _) (() , _)
TMC-bridge← _ (T₁ ∷ T₁ ∷ _) (() , _)
TMC-bridge← _ (T₂ ∷ T₂ ∷ _) (() , _)
TMC-bridge← _ (T₀ ∷ [])    (() , _)
TMC-bridge← _ (T₁ ∷ [])    (() , _)
TMC-bridge← _ (T₂ ∷ [])    (() , _)
TMC-bridge← _ []           (() , _)

-- 兼容定理（双向合取）：value (TMC-dec n x) ≡ true ⇔ tmc 于带 TMC-tapeOf n x
-- 恰 2 步接受——9 案首二符有序对 + 单位串/空带 2 案全闭。
TMC-bridge : ∀ (n : ℕ) (x : Vec Trit n)
  → (value (TMC-dec n x) ≡ true → TMC-AcceptsIn tmc qAcc 2 (TMC-tapeOf n x))
  × (TMC-AcceptsIn tmc qAcc 2 (TMC-tapeOf n x) → value (TMC-dec n x) ≡ true)
TMC-bridge n x = TMC-bridge→ n x , TMC-bridge← n x

-- ═══ §6 立界注记（诚实边界——不设空壳签名）═══════════════════════════════
-- (i)   通用编码桥立界（TMBridge §5(i) 延续）：仍只闭合旗舰对 TMC-dec ⇌ tmc（恰 2 步
--       口径）；「任意 Counted 函数可实现为 TM」维持 PClass §6(i) / TimeBound §8(i) /
--       TMBridge §5(i) 立界；实例提升只为 SAT 验证器 TM 化铺范式，不外推。
-- (ii)  Σ 偏差立界：引入 TMC-Σ 的代价是 TMH 复用面收缩——TMH-halt-mono（泛型）原样
--       复用（§2）；TMH-tapeOf/hdOf/AcceptsIn 以 TMC- 同构件复刻，右带编码修正见 (iii)。
-- (iii) 右带编码立界：TMC-AcceptsIn 取 (TMC-hdOf w, tlOf w)；TMH 的 (hdOf w, w) 在 2 步
--       机上首步 R 移后重读 cell 0、双读语义尽失——1 步旗舰未暴露的编码自由度，本件起
--       固定标准形；TMH 是否回改属既有件禁区，立界。
-- (iv)  L 移左带空支（leftLof 的 [] 支）不可达：初头在 cell0 ⇒ 首步 R 移后左带恒非空，
--       本机 L 移步全落非空支（§1 三形态核对即证）；空支覆盖属「头在输入左侧」约定
--      （Automata §4 cfg0）的机器族，不在本件。
-- (v)   等式级口径（TMBridge §5(v) 延续）：value ≡ true ⇔ 恰 2 步接受的等式级闭合，
--       非渐近；大 O 层维持 TimeBound §8(ii)；接受语义由状态编码（同 TMH §5(iv)）。

-- 0 postulate / 0 hole。
-- 本文件由 agda +RTS -M8G -H6G -A128M -RTS 编译，EXIT=0 为完成判据。
