{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Algebra.Complexity.NPClass-TM
-- 机器级 NP（`InNP-TM`）与它到 `InNP` 的桥 —— Cook–Levin 里程碑 M2
--
-- 【为什么需要这一层】库内 `InNP` 的 `np-verifier` 是**任意 Agda 总函数**
-- （NPClass:48）：能跑，但没有转移表 ⟹ 读不出「第 t 步第 i 格是什么」⟹
-- Cook–Levin 的 tableau 无从下手（SATRed §6(i) 已立此界）。本件给出**带转移表**的
-- NP 定义：验证 = 「把输入与猜测拼在带上，跑 p n 步，看是否停在接受态」。
--
-- 【方向纪律（普查的核心判断）】
--   · `InNP-TM ⟹ InNP`（本件 §4）：**工程**——`TM` 是 record、`runN` 是构造性
--     函数，验证器就是一次 `runN` 调用的计账包装。
--   · `InNP ⟹ InNP-TM`（反向）：**Church–Turing 深件**，本库立界不碰
--     （PClass §6(i) / TMBridge §5(i) / TimeBound §8(i) 同一条界）。
--
-- 【计账口径（与 SATMember 的「实数账」不同，明写）】`Counted` 的 `steps` 这里取
-- **上界** `p n`（机器最多跑 p n 步），不另算「实际停机前的步数」：
--   · 好处：`np-cost` 精确成立（`p n ≤ p n`），且不需要「步数计时器」这一额外件；
--   · 代价：账目是上界而非实数（`satFormulaC` 是实数账）。
--   两条都记在 §3 的引理里（`NPT-steps` 为精确等式，值即上界）。
--
-- 【接受语义（Bool 通道，同 TM.halt 的范式）】TM record 只有 `halt : Q → Bool`，
-- 无接受/拒绝双态。本件给 `tm-acc : Q → Bool` 作接受判据，并强制一条**冻结前提**
-- `tm-acc-halt : acc q ≡ true → halt q ≡ true`：于是「第 p n 步在 acc 态」等价于
-- 「≤ p n 步内接受并停住」（`runN` 对 halt 冻结）。
--
-- 分级约定：〔结构定义〕/〔结构证明〕/〔refl 枚举〕/〔立界注记〕（同 TimeBound）。
-- 0 postulate / 0 hole。

module Sovereign.Algebra.Complexity.NPClass-TM where

open import Data.Nat using (ℕ; zero; suc; _≤_; s≤s; z≤n)
open import Data.Bool using (Bool; true; false; _∨_; _∧_)
open import Data.List using (List; []; _∷_; _++_)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.Vec using (Vec) renaming ([] to vNil; _∷_ to _v∷_)
open import Data.Nat.Properties using (≤-refl)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂)

open import Sovereign.Base.Trit using (Trit; T₀; T₁; T₂; negate)
open import Sovereign.Algebra.Automata.TuringMachine
  using (TM; TConfig; mkTC; hdOf; tlOf; runN)
open import Sovereign.Algebra.Complexity.TimeBound
  using (Counted; value; steps; Mono; Pos)
  renaming (cnt to mkCnt)
open import Sovereign.Algebra.Complexity.PClass
  using (TritLang; L-Head₁; headT; isT₁)
open import Sovereign.Algebra.Complexity.NPClass using (InNP)
open import Sovereign.Algebra.Complexity.TMBridge
  using (TMH-QH; qScan; qAcc; qRej; tm-head; TMH-haltH)

-- ────────────────────────────────────────────────────────────────────
-- §0 小件〔refl 枚举 + 3 案〕
-- ────────────────────────────────────────────────────────────────────

NPT-false≢true : false ≡ true → ⊥
NPT-false≢true ()

-- 三值的「真」只有 T₁（真值通道是 Bool ⟹ 反推回 trit 需 3 案）
isT₁-true : ∀ (t : Trit) → isT₁ t ≡ true → t ≡ T₁
isT₁-true T₀ ()
isT₁-true T₁ h = refl
isT₁-true T₂ ()

-- ────────────────────────────────────────────────────────────────────
-- §1 运行面：带表示、初始格局、p n 步后的接受判定〔结构定义〕
-- ────────────────────────────────────────────────────────────────────

-- 输入/猜测符号表：Vec Trit ⟹ List A（经 emb）
-- ⚠ 方向：机器读的是 `emb` 的像；`emb` 单射与否不影响本件（M3 才需要单射性）
NPT-tapeOf : ∀ {n : ℕ} {A : Set} → (Trit → A) → Vec Trit n → List A
NPT-tapeOf emb vNil       = []
NPT-tapeOf emb (t v∷ ts)  = emb t ∷ NPT-tapeOf emb ts

-- 初始格局：头在**首符号**上（空带读空白 blk）——与 TMBridge 的输入约定一致
NPT-initCfg : ∀ {Q A : Set} → (M : TM Q A) → A → List A → TConfig Q A
NPT-initCfg M blk inp = mkTC [] (TM.q₀ M) (hdOf blk inp) inp

-- 判定：输入 ++ 猜测 放在带上，跑 p n 步，问接受态
NPT-run : ∀ {Q A : Set} → (M : TM Q A) (blk : A) (emb : Trit → A)
                       → (acc : Q → Bool) (p : ℕ → ℕ)
        → (n : ℕ) (x : Vec Trit n) {k : ℕ} (w : Vec Trit k) → Bool
NPT-run M blk emb acc p n x w =
  acc (TConfig.st (runN M blk (p n)
        (NPT-initCfg M blk (NPT-tapeOf emb x ++ NPT-tapeOf emb w))))

-- ────────────────────────────────────────────────────────────────────
-- §2 机器级 NP〔结构定义〕
-- ────────────────────────────────────────────────────────────────────

record InNP-TM (L : TritLang) : Set₁ where
  field
    tm-Q         : Set                       -- 状态集（有限性不进类型——本库口径）
    tm-A         : Set                       -- 带字母表
    tm-M         : TM tm-Q tm-A              -- 转移表（确定性由函数形自证）
    tm-blk       : tm-A                      -- 空白符
    tm-emb       : Trit → tm-A               -- 输入/猜测符号嵌入
    tm-acc       : tm-Q → Bool               -- 接受判据（Bool 通道）
    tm-acc-halt  : ∀ q → tm-acc q ≡ true → TM.halt tm-M q ≡ true   -- 冻结前提
    tm-p         : ℕ → ℕ                     -- 步数界（多项式）
    tm-p-mono    : Mono tm-p                 -- 〔结构证明〕
    tm-p-pos     : Pos tm-p                  -- 〔结构证明〕
    tm-w         : ℕ → ℕ                     -- 猜测长度界
    tm-w-mono    : Mono tm-w                 -- 〔结构证明〕
    tm-complete  : ∀ n x → L n x
                 → Σ (Vec Trit (tm-w n))
                     (λ w → NPT-run tm-M tm-blk tm-emb tm-acc tm-p n x w ≡ true)
    tm-sound     : ∀ n x (w : Vec Trit (tm-w n))
                 → NPT-run tm-M tm-blk tm-emb tm-acc tm-p n x w ≡ true → L n x

-- ────────────────────────────────────────────────────────────────────
-- §3 计账伴生版 + 两条精确等式〔结构定义 + refl〕
-- ────────────────────────────────────────────────────────────────────

NPT-verdict : ∀ {L : TritLang} (X : InNP-TM L)
            → (n : ℕ) (x : Vec Trit n) {k : ℕ} (w : Vec Trit k) → Bool
NPT-verdict X =
  NPT-run (InNP-TM.tm-M X) (InNP-TM.tm-blk X) (InNP-TM.tm-emb X)
          (InNP-TM.tm-acc X) (InNP-TM.tm-p X)

NPT-verifier : ∀ {L : TritLang} (X : InNP-TM L)
             → (n : ℕ) (x : Vec Trit n) {k : ℕ} (w : Vec Trit k) → Counted Bool
NPT-verifier X n x w = mkCnt (NPT-verdict X n x w) (InNP-TM.tm-p X n)

-- 值一致（定义性）
NPT-value : ∀ {L : TritLang} (X : InNP-TM L) (n : ℕ) (x : Vec Trit n)
            {k : ℕ} (w : Vec Trit k)
          → value (NPT-verifier X n x w) ≡ NPT-verdict X n x w
NPT-value X n x w = refl

-- 账目（精确等式：取上界 p n，见头注「计账口径」）
NPT-steps : ∀ {L : TritLang} (X : InNP-TM L) (n : ℕ) (x : Vec Trit n)
            {k : ℕ} (w : Vec Trit k)
          → steps (NPT-verifier X n x w) ≡ InNP-TM.tm-p X n
NPT-steps X n x w = refl

-- ────────────────────────────────────────────────────────────────────
-- §4 桥：`InNP-TM ⟹ InNP`〔结构封装，无深证明〕
-- ────────────────────────────────────────────────────────────────────
-- 这一步是**方向的工程面**：机器型验证器就是一次 runN 调用的计账包装。
-- 反方向（任意总函数 ⟹ 转移表）是 Church–Turing 深件，本库立界不碰。

InNP-TM→InNP : ∀ {L : TritLang} → InNP-TM L → InNP L
InNP-TM→InNP {L} X = record
  { np-p        = tm-p
  ; np-p-mono   = tm-p-mono
  ; np-p-pos    = tm-p-pos
  ; np-witLen   = tm-w
  ; np-w-mono   = tm-w-mono
  ; np-verifier = λ n x w → NPT-verifier X n x w
  ; np-complete = λ n x h → tm-complete n x h
  ; np-sound    = λ n x w h → tm-sound n x w h
  ; np-cost     = λ n x w → ≤-refl
  }
  where
  open InNP-TM X

-- ────────────────────────────────────────────────────────────────────
-- §5 实例：L-Head₁ ∈ NP-TM（用库内既有 tm-head，直接 refl 验算）
-- ────────────────────────────────────────────────────────────────────
-- 走「直接算」而不复用 TMH-head-bridge：后者陈述在 `TMH-tapeOf` / `TMH-hdOf`
-- 的带上约定上，与本件的 `NPT-tapeOf` / `hdOf T₀` 差一层转换引理；而 1 步运行只
-- 看 `st`（不碰带尾），直接 refl 更短且同时核对了本件约定与手算一致。

TMH-acc : TMH-QH → Bool
TMH-acc qAcc  = true
TMH-acc qScan = false
TMH-acc qRej  = false

TMH-acc-sound : ∀ (q : TMH-QH) → TMH-acc q ≡ true → q ≡ qAcc
TMH-acc-sound qAcc  h = refl
TMH-acc-sound qScan h = ⊥-elim (NPT-false≢true h)
TMH-acc-sound qRej  h = ⊥-elim (NPT-false≢true h)

TMH-acc-halt : ∀ (q : TMH-QH) → TMH-acc q ≡ true → TM.halt tm-head q ≡ true
TMH-acc-halt q h = cong TMH-haltH (TMH-acc-sound q h)

head-NP-TM : InNP-TM L-Head₁
head-NP-TM = record
  { tm-Q        = TMH-QH
  ; tm-A        = Trit
  ; tm-M        = tm-head
  ; tm-blk      = T₀
  ; tm-emb      = λ t → t
  ; tm-acc      = TMH-acc
  ; tm-acc-halt = TMH-acc-halt
  ; tm-p        = λ _ → 1
  ; tm-p-mono   = λ _ → ≤-refl
  ; tm-p-pos    = λ _ → ≤-refl
  ; tm-w        = λ _ → 0
  ; tm-w-mono   = λ _ → ≤-refl
  ; tm-complete = head-complete
  ; tm-sound    = head-sound
  }
  where
  -- 1 步后停在 qAcc ⟺ 首符号是 T₁（带尾无关 ⟹ 不必规约带尾）
  head-complete : ∀ (n : ℕ) (x : Vec Trit n) → L-Head₁ n x
                → Σ (Vec Trit 0) (λ w → NPT-run tm-head T₀ (λ t → t) TMH-acc (λ _ → 1) n x w ≡ true)
  head-complete n (T₁ v∷ xs) h = vNil , refl
  head-complete n (T₀ v∷ xs) ()
  head-complete n (T₂ v∷ xs) ()
  head-complete n vNil       ()

  head-sound : ∀ (n : ℕ) (x : Vec Trit n) (w : Vec Trit 0)
             → NPT-run tm-head T₀ (λ t → t) TMH-acc (λ _ → 1) n x w ≡ true → L-Head₁ n x
  head-sound n (T₁ v∷ xs) w h = refl
  head-sound n (T₀ v∷ xs) w ()
  head-sound n (T₂ v∷ xs) w ()
  head-sound n vNil       vNil ()

-- ────────────────────────────────────────────────────────────────────
-- §6 核对层〔refl 枚举〕
-- ────────────────────────────────────────────────────────────────────

-- 桥的界与账目（P ⊆ NP 的机器版口径：p = 1、wLen = 0）
NPT-check-head-p : InNP.np-p (InNP-TM→InNP head-NP-TM) 5 ≡ 1
NPT-check-head-p = refl

NPT-check-head-wit : InNP.np-witLen (InNP-TM→InNP head-NP-TM) 5 ≡ 0
NPT-check-head-wit = refl

-- 验证器在两条具体输入上的值（首符号 T₁ ⟹ 真 / 首符号 T₀ ⟹ 假）
NPT-check-verdict-hit :
  NPT-verdict head-NP-TM 1 (T₁ v∷ vNil) vNil ≡ true
NPT-check-verdict-hit = refl

NPT-check-verdict-miss :
  NPT-verdict head-NP-TM 1 (T₀ v∷ vNil) vNil ≡ false
NPT-check-verdict-miss = refl

-- 非空带尾不影响判定（1 步只看首符号）
NPT-check-verdict-tail :
  NPT-verdict head-NP-TM 3 (T₁ v∷ (T₂ v∷ (T₀ v∷ vNil))) vNil ≡ true
NPT-check-verdict-tail = refl

-- ────────────────────────────────────────────────────────────────────
-- §7 尾注立界（诚实边界——不设空壳签名）
-- ────────────────────────────────────────────────────────────────────
-- (i)   **反方向不碰**：`InNP ⟹ InNP-TM`（任意 Agda 总函数 ⟹ 转移表）=
--       Church–Turing 深件（PClass §6(i) / TMBridge §5(i) / TimeBound §8(i)）。
--       本件只闭合 `InNP-TM ⟹ InNP` 这一个方向。
-- (ii)  **状态集/字母表的有限性不进类型**：`tm-Q` / `tm-A` 是任意 `Set`
--       （同库内 `TM` record 的口径）。Cook–Levin 的 tableau 需要**可枚举**
--       的状态与符号（才能编号成变元）⟹ M3 必须再要求有限性（或直接给出
--       `Fin` 形态的机器）；本件不假装已经够用。
-- (iii) **计账是上界**：`steps (verifier) = p n`（不是「实际停机步数」）。
--       若要实数账需另加「步数计时器」件；本库 `np-cost` 只要 `≤`。
-- (iv)  接受判据是 `tm-acc : Q → Bool` + 冻结前提 `acc ⟹ halt`；
--       这使「第 p n 步在 acc 态」⟺「≤ p n 步内接受并停住」。若省掉冻结前提，
--       则只表示「第 p n 步恰在 acc 态」，语义更弱。
-- (v)   实例只给了 `L-Head₁`（猜测长 0）——它验证了定义与桥的形状，但**没有**
--       用到非空猜测；非空猜测的实例（含位置/见证编码）属 M3 的 tableau 接线。
-- (vi)  `NPT-tapeOf` 用 `emb` 而非单射假设：本件不需要单射性；M3 若要用
--       「猜出的符号被机器正确读回」需补 `emb` 单射（或取 `emb = id`）。

-- 0 postulate / 0 hole。
