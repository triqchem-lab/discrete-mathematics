{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Synthesis.Homotopy.WalkCounting
--
-- **走计数机件（核心层）**：让「π₁ᵈ(G) 的基数」这句人话变成可陈述的命题。
--
-- ## 为什么需要这个模块
--
-- `Pi1dCardinality` 已证：无三角形时 `AHomotopy` 退化为命题相等
-- ⇒ 每个等价类**恰是单点**（`pi1d-class-is-point`）⇒ 商与闭走等基数。
-- 但「**等多少**」还需要**数值**：长度 n 的 u→v 走有多少条？
-- 那正是邻接矩阵幂 `(A^n)_{uv}` —— 本模块给出它的组合定义。
--
-- ## 定义（对有限顶点 `V = Fin n`）
--
-- ```
-- sumFin  : (Fin n → ℕ) → ℕ                       -- 有限和
-- delta   : Fin n → Fin n → ℕ                     -- Kronecker δ（靠 Fin 的可判定相等）
-- WCount  : (Fin n → Fin n → ℕ) → ℕ → Fin n → Fin n → ℕ
-- WCount E zero    u v = delta u v
-- WCount E (suc k) u v = Σ_w ( WCount E k u w · E w v )
-- ```
--
-- ⇒ 这就是「先走 k 步到 w，再走一条边 w→v」的计数递归 ✓
--
-- ## 本模块（核心层）证了什么
--
--   · `sumFin-zero`  —— 项项为零 ⇒ 和为零
--   · `sumFin-cong`  —— 和尊重逐点相等
--   · `delta-refl`   —— `δ(i,i) = 1`
--   · `delta-neq`    —— `i ≠ j ⇒ δ(i,j) = 0`
--   · `WCount-zero`  —— `WCount E 0 u v = δ(u,v)`（定义性）
--   · `sumFin-deltaˡ`—— **δ 挑选项**：`Σ_w δ(u,w)·g(w) = g(u)` ★
--   · `WCount-one`   —— `WCount E 1 u v = E u v`（走一条边）
--   · `sumFin-scale` / `sumFin-swap` —— 提公因子、**两尺寸** Fubini ★（`sumFin-+` 等复用 Burnside）
--
-- ## ⚠ 本模块**不**证什么（诚实边界）
--
--   · **不**证 `WCount` 等于走数 —— 那需要 `Walk`（长度 n）与「边序列」的双射 ✗
--   · **不**给出 `|π₁ᵈ|` 的数值公式 ✗
--   这些是后续节点，见台账 `PIO-1.count.*`。
--
-- ## 核心原则
--   · 只依赖 `Fin` 的可判定相等（不需要 `edge` 可判定）✓
--   · 0 postulate / 0 hole

module Sovereign.Synthesis.Homotopy.WalkCounting where

open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
open import Data.Nat.Properties
  using (+-identityʳ; *-identityˡ; *-identityʳ; *-zeroʳ; *-assoc; *-distribʳ-+; *-distribˡ-+)

-- ★ 复用：有限和基础设施（不重写）—— 初版重写这 5 条被 check_duplicate 拦下
open import Sovereign.Algebra.GroupTheory.Burnside
  using (sumFin; sumFin-cong; sumFin-zero; sumFin-+; +-interchange')
open import Data.Fin using (Fin; _≟_)
import Data.Fin as Fin
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; cong; cong₂; trans; sym; module ≡-Reasoning)
open ≡-Reasoning

--------------------------------------------------------------------------------
-- §1.（已删除）有限和基础设施 —— 复用 Burnside.agda
--
-- ⚠ 2026-10-21 自查纠错：本模块初版**重写了** `sumFin` / `sumFin-cong` /
--   `sumFin-zero` / `sumFin-+` / `+-swap`（后者与 `+-interchange'` 逐字相同），
--   被 `.git/hooks/pre-commit` 的 `check_duplicate.sh` 拦下 ⇒ 改为 `open import` 引用 ✓
--   位置：`Sovereign.Algebra.GroupTheory.Burnside`（`:48/:52/:59/:69/:78`）
--------------------------------------------------------------------------------

--------------------------------------------------------------------------------
-- §2. Kronecker δ
--------------------------------------------------------------------------------

delta : ∀ {n : ℕ} → Fin n → Fin n → ℕ
delta i j with i ≟ j
... | yes _ = 1
... | no  _ = 0

delta-refl : ∀ {n : ℕ} (i : Fin n) → delta i i ≡ 1
delta-refl i with i ≟ i
... | yes _ = refl
... | no ¬p = ⊥-elim (¬p refl)

-- ⚠ 关键：`delta (Fin.suc u) (Fin.suc i)` 与 `delta u i` **不是**定义性相等
--   （两处 `with` 抽象出不同的 stuck 项，2026-10-21 实测），必须显式桥接。
delta-suc : ∀ {m : ℕ} (u i : Fin m)
          → delta (Fin.suc u) (Fin.suc i) ≡ delta u i
delta-suc u i with u ≟ i
... | yes _ = refl
... | no  _ = refl

delta-zero-suc : ∀ {m : ℕ} (i : Fin m) → delta Fin.zero (Fin.suc i) ≡ 0
delta-zero-suc i = refl

delta-suc-zero : ∀ {m : ℕ} (u : Fin m) → delta (Fin.suc u) Fin.zero ≡ 0
delta-suc-zero u = refl

delta-neq : ∀ {n : ℕ} {i j : Fin n} → i ≢ j → delta i j ≡ 0
delta-neq {i = i} {j = j} neq with i ≟ j
... | yes p = ⊥-elim (neq p)
... | no  _ = refl

--------------------------------------------------------------------------------
-- §3. 走计数 = 邻接矩阵幂
--------------------------------------------------------------------------------

WCount : ∀ {n : ℕ} → (Fin n → Fin n → ℕ) → ℕ → Fin n → Fin n → ℕ
WCount E zero    u v = delta u v
WCount E (suc k) u v = sumFin (λ w → E u w * WCount E k w v)

-- 基态律（定义性）
WCount-zero : ∀ {n : ℕ} (E : Fin n → Fin n → ℕ) (u v : Fin n)
            → WCount E zero u v ≡ delta u v
WCount-zero E u v = refl

-- 递归律（定义性，作为具名引理供下游引用）
WCount-suc : ∀ {n : ℕ} (E : Fin n → Fin n → ℕ) (k : ℕ) (u v : Fin n)
           → WCount E (suc k) u v
             ≡ sumFin (λ w → E u w * WCount E k w v)
WCount-suc E k u v = refl

--------------------------------------------------------------------------------
-- §4. ★ δ 挑选项：`Σ_w δ(u,w)·g(w) = g(u)`
--
-- 这是把 `WCount` 与「真实走数」连起来的第一个环节：
-- 长度 1 的走数必须等于边数，否则递归语义就错了。
--------------------------------------------------------------------------------

sumFin-deltaˡ : ∀ {n : ℕ} (u : Fin n) (g : Fin n → ℕ)
              → sumFin (λ w → delta u w * g w) ≡ g u
sumFin-deltaˡ {n = zero}  () g
sumFin-deltaˡ {n = suc m} Fin.zero g =
  trans (cong₂ _+_
          (*-identityˡ (g Fin.zero))
          (sumFin-zero (λ i → delta Fin.zero (Fin.suc i) * g (Fin.suc i))
                       (λ i → refl)))
        (+-identityʳ (g Fin.zero))
sumFin-deltaˡ {n = suc m} (Fin.suc u) g =
  trans (sumFin-cong (λ i → cong (λ z → z * g (Fin.suc i)) (delta-suc u i)))
        (sumFin-deltaˡ u (λ i → g (Fin.suc i)))

-- 右 δ 挑选项：`Σ_w f(w)·δ(w,v) = f(v)`（边优先递推需要）
sumFin-deltaʳ : ∀ {n : ℕ} (v : Fin n) (f : Fin n → ℕ)
              → sumFin (λ w → f w * delta w v) ≡ f v
sumFin-deltaʳ {n = zero}  () f
sumFin-deltaʳ {n = suc m} Fin.zero f =
  trans (cong₂ _+_
          (*-identityʳ (f Fin.zero))
          (sumFin-zero (λ i → f (Fin.suc i) * delta (Fin.suc i) Fin.zero)
                       (λ i → *-zeroʳ (f (Fin.suc i)))))
        (+-identityʳ (f Fin.zero))
sumFin-deltaʳ {n = suc m} (Fin.suc v) f =
  trans (cong₂ _+_
          (*-zeroʳ (f Fin.zero))
          (sumFin-cong (λ i → cong (λ z → f (Fin.suc i) * z) (delta-suc i v))))
        (sumFin-deltaʳ v (λ i → f (Fin.suc i)))

-- 一阶计数律：走一条边 = 边数
WCount-one : ∀ {n : ℕ} (E : Fin n → Fin n → ℕ) (u v : Fin n)
           → WCount E 1 u v ≡ E u v
WCount-one E u v = sumFin-deltaʳ v (λ w → E u w)

--------------------------------------------------------------------------------
-- §5. 有限和的两条额外结构律（Burnside 没有的）
--------------------------------------------------------------------------------

-- 提公因子
sumFin-scale : ∀ {n : ℕ} (c : ℕ) (f : Fin n → ℕ)
             → sumFin (λ i → f i * c) ≡ sumFin f * c
sumFin-scale {n = zero}  c f = refl
sumFin-scale {n = suc m} c f =
  trans (cong₂ _+_ refl (sumFin-scale c (λ i → f (Fin.suc i))))
        (sym (*-distribʳ-+ c (f Fin.zero) (sumFin (λ i → f (Fin.suc i)))))

-- 左提公因子
sumFin-scaleˡ : ∀ {n : ℕ} (c : ℕ) (f : Fin n → ℕ)
              → sumFin (λ i → c * f i) ≡ c * sumFin f
sumFin-scaleˡ {n = zero}  c f = sym (*-zeroʳ c)
sumFin-scaleˡ {n = suc m} c f =
  trans (cong₂ _+_ refl (sumFin-scaleˡ c (λ i → f (Fin.suc i))))
        (sym (*-distribˡ-+ c (f Fin.zero) (sumFin (λ i → f (Fin.suc i)))))

-- Fubini（双重和可换序）
-- ⚠ 必须对**两个尺寸分别量化**：外层与内层求和的指标集大小可以不同
--   （同一个 `suc m` 情形的外层尾和是 `Fin m`、内层是 `Fin (suc m)`）。
--   只用单一 `n` 会报 `m` 与 `suc m` 不等（2026-10-21 实测）。
sumFin-swap : ∀ {m n : ℕ} (f : Fin m → Fin n → ℕ)
            → sumFin (λ i → sumFin (λ j → f i j))
            ≡ sumFin (λ j → sumFin (λ i → f i j))
sumFin-swap {m = zero} {n = n} f =
  sym (sumFin-zero {n = n} (λ j → sumFin {n = zero} (λ i → f i j)) (λ j → refl))
sumFin-swap {m = suc k} {n = n} f =
  trans (cong₂ _+_ refl (sumFin-swap {m = k} {n = n} (λ i j → f (Fin.suc i) j)))
        (sym (sumFin-+ {n = n}
                       (λ j → f Fin.zero j)
                       (λ j → sumFin {n = k} (λ i → f (Fin.suc i) j))))

--------------------------------------------------------------------------------
-- §6. ★ 矩阵幂半群律：`WCount (k + l) = WCount k · WCount l`
--
-- 这就是「先走 k 步、再走 l 步」= 「一次走 k+l 步」✓
-- 边优先递推（`Σ_w E u w · WCount E k w v`）让两侧归纳后同形，只需 Fubini 换序。
--------------------------------------------------------------------------------

WCount-split : ∀ {n : ℕ} (E : Fin n → Fin n → ℕ) (k l : ℕ) (u v : Fin n)
             → WCount E (k + l) u v
               ≡ sumFin (λ w → WCount E k u w * WCount E l w v)
WCount-split E zero l u v =
  sym (sumFin-deltaˡ u (λ w → WCount E l w v))
WCount-split E (suc k) l u v = begin
  WCount E (suc k + l) u v
    ≡⟨ sumFin-cong (λ w → cong (E u w *_) (WCount-split E k l w v)) ⟩
  sumFin (λ w → E u w * sumFin (λ x → WCount E k w x * WCount E l x v))
    ≡⟨ sumFin-cong (λ w →
         sym (sumFin-scaleˡ (E u w) (λ x → WCount E k w x * WCount E l x v))) ⟩
  sumFin (λ w → sumFin (λ x → E u w * (WCount E k w x * WCount E l x v)))
    ≡⟨ sumFin-cong (λ w → sumFin-cong (λ x →
         sym (*-assoc (E u w) (WCount E k w x) (WCount E l x v)))) ⟩
  sumFin (λ w → sumFin (λ x → (E u w * WCount E k w x) * WCount E l x v))
    ≡⟨ sumFin-swap (λ w x → (E u w * WCount E k w x) * WCount E l x v) ⟩
  sumFin (λ x → sumFin (λ w → (E u w * WCount E k w x) * WCount E l x v))
    ≡⟨ sumFin-cong (λ x →
         sumFin-scale (WCount E l x v)
                      (λ w → E u w * WCount E k w x)) ⟩
  sumFin (λ x → (sumFin (λ w → E u w * WCount E k w x)) * WCount E l x v)
  ∎
