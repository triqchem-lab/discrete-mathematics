{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Algebra.Complexity.Tableau-Tape
-- 带索引层：**相对头偏移**的局部视图 + 一步演化的窗口事实 —— 里程碑 M3b
--
-- 【为什么用相对偏移而不是绝对格号】tableau 的转移子句说的是「头及其左右邻」，
-- 即**相对头**的窗口；绝对格号（`i−1`、`i+1`）会引入 `∸`、边界比较与一串
-- 算术引理。本件把视图定义成 `tH`（头格）/ `tL k`（头左第 k 格）/ `tR k`（头右第 k 格），
-- 于是「新头读旧右侧第 0 格」「写符号落在旧头格」这类事实都是**定义性相等**。
-- 绝对格号的对齐留给 M3c（tableau 的行要对齐同一格，那时才需要编号）。
--
-- 【库内带约定（实测 TuringMachine §2）】`left` = 头**左侧逆序**，`scan` = 头格符号，
-- `right` = 头**右侧**（不含头格）：
--   · 右移：`left′ = w′ ∷ left`、`scan′ = hdOf blk right`、`right′ = tlOf right`；
--   · 左移（左非空）：`left′ = tl left`、`scan′ = hd left`、`right′ = w′ ∷ scan ∷ right`；
--   · 左移（左空）：`left′ = []`、`scan′ = w′`、`right′ = scan ∷ right`。
-- 三条都直接读成 §2 的窗口事实。
--
-- 分级约定：〔结构定义〕/〔结构证明〕/〔refl 枚举〕/〔立界注记〕（同 TimeBound）。
-- 0 postulate / 0 hole。

module Sovereign.Algebra.Complexity.Tableau-Tape where

open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Bool using (Bool; true; false)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong)

open import Sovereign.Base.Trit using (Trit; T₀; T₁; T₂)
open import Sovereign.Algebra.Automata.TuringMachine
  using (Dir; L; R; TM; TConfig; mkTC; step; stepH; moveH; hdOf; tlOf)
open import Sovereign.Algebra.Complexity.NPClass-TM using (NPT-initCfg)

-- ────────────────────────────────────────────────────────────────────
-- §1 相对偏移视图〔结构定义 + 结构证明〕
-- ────────────────────────────────────────────────────────────────────

data TOff : Set where
  tH : TOff            -- 头格
  tL : ℕ → TOff        -- 头左侧第 k 格（k = 0 紧邻头）
  tR : ℕ → TOff        -- 头右侧第 k 格（k = 0 紧邻头）

-- 列表第 i 项（越界给默认值 = 空白）
nth : ∀ {A : Set} → A → List A → ℕ → A
nth d []       i       = d
nth d (x ∷ xs) zero    = x
nth d (x ∷ xs) (suc i) = nth d xs i

-- 局部视图：头格取 `scan`，左/右按偏移取 `left`/`right`
tSym : ∀ {Q A : Set} → A → TConfig Q A → TOff → A
tSym blk c tH      = TConfig.scan c
tSym blk c (tL k)  = nth blk (TConfig.left c) k
tSym blk c (tR k)  = nth blk (TConfig.right c) k

-- `hdOf` 与 `nth … 0` 同值（两者都在列表上分案，故需一条 2 案引理）
hdOf-nth : ∀ {A : Set} (d : A) (xs : List A) → hdOf d xs ≡ nth d xs zero
hdOf-nth d []       = refl
hdOf-nth d (x ∷ xs) = refl

-- 右带「去掉一格」= 偏移前移一位（对 `r` 分案，两案均定义性）
nth-tlOf : ∀ {A : Set} (d : A) (r : List A) (k : ℕ)
         → nth d (tlOf r) k ≡ nth d r (suc k)
nth-tlOf d []       k = refl
nth-tlOf d (x ∷ xs) k = refl

-- ────────────────────────────────────────────────────────────────────
-- §2 一步演化的窗口事实〔结构证明〕
-- ────────────────────────────────────────────────────────────────────
-- 三条（右移 / 左移·左非空 / 左移·左空）：把「新格局的局部视图」逐格对齐到
-- 「旧格局的局部视图」，每个分量都是定义性相等；只有「新头读旧右第 0 格」
-- 需要 `hdOf-nth` 这一步换形。

-- 右移
tstep-R : ∀ {Q A : Set} (blk : A) (M : TM Q A) (q′ : Q) (w′ : A)
            (l : List A) (s : Q) (a : A) (r : List A)
        → TM.δ M s a ≡ (q′ , w′ , R)
        → TM.halt M s ≡ false
        →   (tSym blk (step M blk (mkTC l s a r)) tH ≡ tSym blk (mkTC l s a r) (tR zero))
          × (tSym blk (step M blk (mkTC l s a r)) (tL zero) ≡ w′)
          × (∀ k → tSym blk (step M blk (mkTC l s a r)) (tL (suc k))
                     ≡ tSym blk (mkTC l s a r) (tL k))
          × (∀ k → tSym blk (step M blk (mkTC l s a r)) (tR k)
                     ≡ tSym blk (mkTC l s a r) (tR (suc k)))
tstep-R blk M q′ w′ l s a r hδ hhalt = P1 , P2 , P3 , P4
  where
  stp : step M blk (mkTC l s a r) ≡ mkTC (w′ ∷ l) q′ (hdOf blk r) (tlOf r)
  stp = trans (cong (λ h → stepH M blk h (mkTC l s a r)) hhalt)
              (trans (cong (λ d → moveH blk d l a r) hδ) refl)

  P1 : tSym blk (step M blk (mkTC l s a r)) tH ≡ tSym blk (mkTC l s a r) (tR zero)
  P1 = trans (cong (λ c → tSym blk c tH) stp) (hdOf-nth blk r)

  P2 : tSym blk (step M blk (mkTC l s a r)) (tL zero) ≡ w′
  P2 = cong (λ c → tSym blk c (tL zero)) stp

  P3 : ∀ k → tSym blk (step M blk (mkTC l s a r)) (tL (suc k))
             ≡ tSym blk (mkTC l s a r) (tL k)
  P3 k = cong (λ c → tSym blk c (tL (suc k))) stp

  P4 : ∀ k → tSym blk (step M blk (mkTC l s a r)) (tR k)
             ≡ tSym blk (mkTC l s a r) (tR (suc k))
  P4 k = trans (cong (λ c → tSym blk c (tR k)) stp) (nth-tlOf blk r k)

-- 左移·左空（头已在最左）：新头是写符号，左邻全空白
tstep-L-nil : ∀ {Q A : Set} (blk : A) (M : TM Q A) (q′ : Q) (w′ : A)
                (s : Q) (a : A) (r : List A)
            → TM.δ M s a ≡ (q′ , w′ , L)
            → TM.halt M s ≡ false
            →   (tSym blk (step M blk (mkTC [] s a r)) tH ≡ w′)
              × (∀ k → tSym blk (step M blk (mkTC [] s a r)) (tL k) ≡ blk)
              × (tSym blk (step M blk (mkTC [] s a r)) (tR zero) ≡ tSym blk (mkTC [] s a r) tH)
              × (∀ k → tSym blk (step M blk (mkTC [] s a r)) (tR (suc k))
                         ≡ tSym blk (mkTC [] s a r) (tR k))
tstep-L-nil blk M q′ w′ s a r hδ hhalt = P1 , P2 , P3 , P4
  where
  stp : step M blk (mkTC [] s a r) ≡ mkTC [] q′ w′ (a ∷ r)
  stp = trans (cong (λ h → stepH M blk h (mkTC [] s a r)) hhalt)
              (trans (cong (λ d → moveH blk d [] a r) hδ) refl)

  P1 : tSym blk (step M blk (mkTC [] s a r)) tH ≡ w′
  P1 = cong (λ c → tSym blk c tH) stp

  P2 : ∀ k → tSym blk (step M blk (mkTC [] s a r)) (tL k) ≡ blk
  P2 k = cong (λ c → tSym blk c (tL k)) stp

  P3 : tSym blk (step M blk (mkTC [] s a r)) (tR zero)
     ≡ tSym blk (mkTC [] s a r) tH
  P3 = cong (λ c → tSym blk c (tR zero)) stp

  P4 : ∀ k → tSym blk (step M blk (mkTC [] s a r)) (tR (suc k))
             ≡ tSym blk (mkTC [] s a r) (tR k)
  P4 k = cong (λ c → tSym blk c (tR (suc k))) stp

-- 左移·左非空：新头是旧左邻，写符号落在旧头格
tstep-L-cons : ∀ {Q A : Set} (blk : A) (M : TM Q A) (q′ : Q) (w′ : A)
                 (x : A) (xs : List A) (s : Q) (a : A) (r : List A)
             → TM.δ M s a ≡ (q′ , w′ , L)
             → TM.halt M s ≡ false
             →   (tSym blk (step M blk (mkTC (x ∷ xs) s a r)) tH
                    ≡ tSym blk (mkTC (x ∷ xs) s a r) (tL zero))
               × (∀ k → tSym blk (step M blk (mkTC (x ∷ xs) s a r)) (tL k)
                          ≡ tSym blk (mkTC (x ∷ xs) s a r) (tL (suc k)))
               × (tSym blk (step M blk (mkTC (x ∷ xs) s a r)) (tR zero) ≡ w′)
               × (tSym blk (step M blk (mkTC (x ∷ xs) s a r)) (tR (suc zero))
                    ≡ tSym blk (mkTC (x ∷ xs) s a r) tH)
               × (∀ k → tSym blk (step M blk (mkTC (x ∷ xs) s a r)) (tR (suc (suc k)))
                          ≡ tSym blk (mkTC (x ∷ xs) s a r) (tR k))
tstep-L-cons blk M q′ w′ x xs s a r hδ hhalt = P1 , P2 , P3 , P4 , P5
  where
  stp : step M blk (mkTC (x ∷ xs) s a r) ≡ mkTC xs q′ x (w′ ∷ a ∷ r)
  stp = trans (cong (λ h → stepH M blk h (mkTC (x ∷ xs) s a r)) hhalt)
              (trans (cong (λ d → moveH blk d (x ∷ xs) a r) hδ) refl)

  P1 : tSym blk (step M blk (mkTC (x ∷ xs) s a r)) tH
     ≡ tSym blk (mkTC (x ∷ xs) s a r) (tL zero)
  P1 = cong (λ c → tSym blk c tH) stp

  P2 : ∀ k → tSym blk (step M blk (mkTC (x ∷ xs) s a r)) (tL k)
             ≡ tSym blk (mkTC (x ∷ xs) s a r) (tL (suc k))
  P2 k = cong (λ c → tSym blk c (tL k)) stp

  P3 : tSym blk (step M blk (mkTC (x ∷ xs) s a r)) (tR zero) ≡ w′
  P3 = cong (λ c → tSym blk c (tR zero)) stp

  P4 : tSym blk (step M blk (mkTC (x ∷ xs) s a r)) (tR (suc zero))
     ≡ tSym blk (mkTC (x ∷ xs) s a r) tH
  P4 = cong (λ c → tSym blk c (tR (suc zero))) stp

  P5 : ∀ k → tSym blk (step M blk (mkTC (x ∷ xs) s a r)) (tR (suc (suc k)))
             ≡ tSym blk (mkTC (x ∷ xs) s a r) (tR k)
  P5 k = cong (λ c → tSym blk c (tR (suc (suc k)))) stp

-- ────────────────────────────────────────────────────────────────────
-- §3 初值视图〔refl 枚举〕
-- ────────────────────────────────────────────────────────────────────
-- `NPT-initCfg M blk inp = mkTC [] (q₀ M) (hdOf blk inp) inp`：
-- 头在第 0 格，右侧就是输入串，左侧全空白。

tinit-tH : ∀ {Q A : Set} (M : TM Q A) (blk : A) (inp : List A)
         → tSym blk (NPT-initCfg M blk inp) tH ≡ hdOf blk inp
tinit-tH M blk inp = refl

tinit-tL : ∀ {Q A : Set} (M : TM Q A) (blk : A) (inp : List A) (k : ℕ)
         → tSym blk (NPT-initCfg M blk inp) (tL k) ≡ blk
tinit-tL M blk inp k = refl

tinit-tR : ∀ {Q A : Set} (M : TM Q A) (blk : A) (inp : List A) (k : ℕ)
         → tSym blk (NPT-initCfg M blk inp) (tR k) ≡ nth blk inp k
tinit-tR M blk inp k = refl

-- ────────────────────────────────────────────────────────────────────
-- §4 核对层〔refl 枚举〕
-- ────────────────────────────────────────────────────────────────────

Tp-check-nth-0 : nth T₀ (T₁ ∷ (T₂ ∷ [])) zero ≡ T₁
Tp-check-nth-0 = refl

Tp-check-nth-1 : nth T₀ (T₁ ∷ (T₂ ∷ [])) (suc zero) ≡ T₂
Tp-check-nth-1 = refl

-- 越界取空白
Tp-check-nth-out : nth T₀ (T₁ ∷ []) (suc (suc zero)) ≡ T₀
Tp-check-nth-out = refl

Tp-check-tlOf : nth T₀ (tlOf (T₁ ∷ (T₂ ∷ []))) zero ≡ nth T₀ (T₁ ∷ (T₂ ∷ [])) (suc zero)
Tp-check-tlOf = refl

Tp-check-hdOf : hdOf T₀ (T₁ ∷ (T₂ ∷ [])) ≡ nth T₀ (T₁ ∷ (T₂ ∷ [])) zero
Tp-check-hdOf = refl

-- ────────────────────────────────────────────────────────────────────
-- §5 尾注立界（诚实边界——不设空壳签名）
-- ────────────────────────────────────────────────────────────────────
-- (i)   本件只给**相对头**的局部视图与三条一步事实。tableau 的子句要对齐
--       **绝对格号**（时刻 t 与 t+1 的同一格）⟹ 还需要「绝对 = 头位置 + 偏移」
--       的对齐层（含 `left` 逆序的下标换算），属 M3c 的编号工作。
-- (ii)  §2 三条已覆盖「头邻之外的格不动」这一事实（以相对形式：`tL (suc k)` /
--       `tR (suc k)` 精确表达移位），**不另立**绝对形态的「非相邻不变」。
-- (iii) 「赋值 ⟹ 运行存在」的提取（M3c 的硬核）不在本件；本件只提供它要用的
--       一步事实。
-- (iv)  `tstep-*` 以 `halt ≡ false` 为前提：停机态自持由 `stepH` 的 `true` 分支
--       保证（`stepH M b true c = c`），故不在本件重复陈述。

-- 0 postulate / 0 hole。

-- ────────────────────────────────────────────────────────────────────
-- §2b 行对齐原语：偏移平移〔结构定义 + 结构证明〕
-- ────────────────────────────────────────────────────────────────────
-- 相对行方案（路线 B）把 tableau 的行按**相对头的偏移**索引，于是「时刻 t 与 t+1 的
-- 同一格」正是**偏移平移**：
--   · 头右移一格 ⟹ 旧 `tR k` 变新 `tR (k−1)`、旧 `tH` 变新 `tL 0`、旧 `tL k` 变新 `tL (k+1)`；
--   · 头左移一格（左非空）⟹ 镜像；
--   · 头左移而左带为空 ⟹ 头**没真动**（`leftLof` 的 `[]` 支原地写入）⟹ 平移是**恒等**。
-- 平移在 `TOff` 上是**全函数、零算术**（只有 `suc` 与「零/后继」两支）。
--
-- 逐点形式把 §2 的四/五个分量收成**一条等式**：除「被写入的旧头格」(`o = tH`) 之外，
-- 每个格子的符号都等于它在新一行对应偏移上的符号。转移子句族（M3c）用的正是这条。

tShiftR : TOff → TOff
tShiftR tH            = tL zero
tShiftR (tL k)        = tL (suc k)
tShiftR (tR zero)     = tH
tShiftR (tR (suc k))  = tR k

tShiftL : TOff → TOff
tShiftL tH            = tR (suc zero)
tShiftL (tL zero)     = tH
tShiftL (tL (suc k))  = tL k
tShiftL (tR k)        = tR (suc (suc k))

-- 右移：`o ≠ tH` 的格子逐点对齐
tstep-R-pt : ∀ {Q A : Set} (blk : A) (M : TM Q A) (q′ : Q) (w′ : A)
               (l : List A) (s : Q) (a : A) (r : List A)
           → TM.δ M s a ≡ (q′ , w′ , R) → TM.halt M s ≡ false
           → ∀ (o : TOff) → (o ≡ tH → ⊥)
           → tSym blk (step M blk (mkTC l s a r)) (tShiftR o)
             ≡ tSym blk (mkTC l s a r) o
tstep-R-pt blk M q′ w′ l s a r hδ hhalt (tL k) h =
  cong (λ c → tSym blk c (tL (suc k))) stp
  where
  stp : step M blk (mkTC l s a r) ≡ mkTC (w′ ∷ l) q′ (hdOf blk r) (tlOf r)
  stp = trans (cong (λ h → stepH M blk h (mkTC l s a r)) hhalt)
              (trans (cong (λ d → moveH blk d l a r) hδ) refl)
tstep-R-pt blk M q′ w′ l s a r hδ hhalt (tR zero) h =
  trans (cong (λ c → tSym blk c tH) stp) (hdOf-nth blk r)
  where
  stp : step M blk (mkTC l s a r) ≡ mkTC (w′ ∷ l) q′ (hdOf blk r) (tlOf r)
  stp = trans (cong (λ h → stepH M blk h (mkTC l s a r)) hhalt)
              (trans (cong (λ d → moveH blk d l a r) hδ) refl)
tstep-R-pt blk M q′ w′ l s a r hδ hhalt (tR (suc k)) h =
  trans (cong (λ c → tSym blk c (tR k)) stp) (nth-tlOf blk r k)
  where
  stp : step M blk (mkTC l s a r) ≡ mkTC (w′ ∷ l) q′ (hdOf blk r) (tlOf r)
  stp = trans (cong (λ h → stepH M blk h (mkTC l s a r)) hhalt)
              (trans (cong (λ d → moveH blk d l a r) hδ) refl)
tstep-R-pt blk M q′ w′ l s a r hδ hhalt tH h = ⊥-elim (h refl)

-- 左移（左非空）：同一形式，平移换成 `tShiftL`
tstep-L-cons-pt : ∀ {Q A : Set} (blk : A) (M : TM Q A) (q′ : Q) (w′ : A)
                    (x : A) (xs : List A) (s : Q) (a : A) (r : List A)
                → TM.δ M s a ≡ (q′ , w′ , L) → TM.halt M s ≡ false
                → ∀ (o : TOff) → (o ≡ tH → ⊥)
                → tSym blk (step M blk (mkTC (x ∷ xs) s a r)) (tShiftL o)
                  ≡ tSym blk (mkTC (x ∷ xs) s a r) o
tstep-L-cons-pt blk M q′ w′ x xs s a r hδ hhalt (tL zero) h =
  cong (λ c → tSym blk c tH) stp
  where
  stp : step M blk (mkTC (x ∷ xs) s a r) ≡ mkTC xs q′ x (w′ ∷ a ∷ r)
  stp = trans (cong (λ h → stepH M blk h (mkTC (x ∷ xs) s a r)) hhalt)
              (trans (cong (λ d → moveH blk d (x ∷ xs) a r) hδ) refl)
tstep-L-cons-pt blk M q′ w′ x xs s a r hδ hhalt (tL (suc j)) h =
  cong (λ c → tSym blk c (tL j)) stp
  where
  stp : step M blk (mkTC (x ∷ xs) s a r) ≡ mkTC xs q′ x (w′ ∷ a ∷ r)
  stp = trans (cong (λ h → stepH M blk h (mkTC (x ∷ xs) s a r)) hhalt)
              (trans (cong (λ d → moveH blk d (x ∷ xs) a r) hδ) refl)
tstep-L-cons-pt blk M q′ w′ x xs s a r hδ hhalt (tR k) h =
  cong (λ c → tSym blk c (tR (suc (suc k)))) stp
  where
  stp : step M blk (mkTC (x ∷ xs) s a r) ≡ mkTC xs q′ x (w′ ∷ a ∷ r)
  stp = trans (cong (λ h → stepH M blk h (mkTC (x ∷ xs) s a r)) hhalt)
              (trans (cong (λ d → moveH blk d (x ∷ xs) a r) hδ) refl)
tstep-L-cons-pt blk M q′ w′ x xs s a r hδ hhalt tH h = ⊥-elim (h refl)
