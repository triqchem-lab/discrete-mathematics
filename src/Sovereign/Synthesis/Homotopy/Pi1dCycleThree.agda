{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Synthesis.Homotopy.Pi1dCycleThree
--
-- **关键证据：Barcelo 口径下 3-环图的 π₁ᵈ 不是 C₃**
--
-- ## 为什么需要这个模块
--
-- 人类 2026-10-21 指出：本地基座是 **3^k / 特征 3**，不是连续统 / 特征 0；
-- 而一般图同伦的半群是在各种**同伦类约束**下的探索，同伦类都带信息截断。
--
-- 我此前的 π₁ᵈ 线全程用 `walk-len : ℕ` 当度量 —— 那是**特征 0 的尺子**。
-- 本模块把这一点的**最尖锐后果**做成内核事实：
--
-- ```
--   3-环图 C₃(qraph)：顶点 Fin 3，边 0→1→2→0，无弦
--   ⇒ 无有向三角形（G3-triangle-free）
--   ⇒ AHomotopy = 命题相等（no-collapse-iff-triangle-free）
--   ⇒ 3 轮走 g³ 与空走 nil **不同伦**（cyc3w³≢nil，靠 walk-len：9 ≠ 0）
--   ⇒ π₁ᵈ ≅ (ℕ, +, 0)（单生成元自由幺半群）
-- ```
--
-- 而本地 C1 判据（`docs/plan/A1-pi-n-paths-abcd-research.md:71`）要求
--
-- ```
--   π₁ᵈ(S¹ᵈ) ≅ C₃        （三阶循环群 ⇒ g³ = e）
-- ```
--
-- **⇒ 两者不可能同口径成立** ✓ —— 本模块把「g³ ≠ e」证成项，
--   `cyc3w³≢nil` 就是「Barcelo 口径给不出 3 阶循环」的项级证据。
--
-- ## 这不裁决什么
--
-- 本模块**不**选边。它只固定一个事实：**Barcelo 口径（任意 DiGraph、无八要素）
-- 的 3-环读数住在 ℕ 侧**。是否因此把 π₁ᵈ 定为投影层备选、以及特征 3 度量如何落地，
-- 属待裁决事项（`proof_dag` journal `decision open`），不在本模块内自行选边。
--
-- ## 核心原则
--   · 0 postulate / 0 hole
--   · 边用**索引具体的 data**（不是 `⊤/⊥` 函数）—— 三角形成立性检查因此只有 3 案 ✓
--   · 顶点 = `Fin 3` = Z/3，与本地 3 进制基座同域 ✓

module Sovereign.Synthesis.Homotopy.Pi1dCycleThree where

open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
open import Data.Nat.Properties using (*-cancelʳ-≡)
open import Data.Fin using (Fin)
import Data.Fin as Fin
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (proj₂)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong; trans; sym)

open import Sovereign.Synthesis.Homotopy.BarceloAHomotopy
  using (DiGraph; Walk; nil; cons; _++w_; AHomotopy)
open import Sovereign.Synthesis.Homotopy.Pi1dCardinality
  using (TriangleFree; NoCollapse; no-collapse-iff-triangle-free;
         AH→≡; walk-len; walk-len-++w)

--------------------------------------------------------------------------------
-- §1. 3-环图：顶点 Fin 3（= Z/3），边 0→1→2→0，无弦
--------------------------------------------------------------------------------

data E3 : Fin 3 → Fin 3 → Set where
  e01 : E3 Fin.zero (Fin.suc Fin.zero)
  e12 : E3 (Fin.suc Fin.zero) (Fin.suc (Fin.suc Fin.zero))
  e20 : E3 (Fin.suc (Fin.suc Fin.zero)) Fin.zero

G3 : DiGraph
G3 = record { V = Fin 3 ; edge = E3 }

--------------------------------------------------------------------------------
-- §2. 无有向三角形（只有 3 组可复合边，弦全部不存在）
--------------------------------------------------------------------------------

G3-triangle-free : TriangleFree G3
G3-triangle-free e01 e12 = λ ()
G3-triangle-free e12 e20 = λ ()
G3-triangle-free e20 e01 = λ ()

-- ⇒ AHomotopy 退化为命题相等
G3-no-collapse : NoCollapse G3
G3-no-collapse = proj₂ (no-collapse-iff-triangle-free {G = G3}) G3-triangle-free

--------------------------------------------------------------------------------
-- §3. ★ 3 轮走与空走**不同伦** —— Barcelo 口径给不出 3 阶循环
--------------------------------------------------------------------------------

-- 走一圈
cyc3w : Walk G3 Fin.zero Fin.zero
cyc3w = cons e01 (cons e12 (cons e20 (nil Fin.zero)))

-- 走三圈
cyc3w³ : Walk G3 Fin.zero Fin.zero
cyc3w³ = cyc3w ++w (cyc3w ++w cyc3w)

-- 长度核算：3 + (3 + 3) ≡ 9
len³ : walk-len cyc3w³ ≡ 9
len³ = trans (walk-len-++w cyc3w (cyc3w ++w cyc3w))
        (cong (walk-len cyc3w +_)
          (trans (walk-len-++w cyc3w cyc3w) refl))

9≢0 : 9 ≡ 0 → ⊥
9≢0 ()

-- ★★ 主结论：三圈走**不**A-同伦于空走
cyc3w³≢nil : ¬ (AHomotopy G3 cyc3w³ (nil Fin.zero))
cyc3w³≢nil ah = 9≢0 (trans (sym len³) (cong walk-len (AH→≡ G3-triangle-free ah)))

-- 附带：单圈走也不是空走（π₁ᵈ 非平凡）
cyc3w≢nil : ¬ (AHomotopy G3 cyc3w (nil Fin.zero))
cyc3w≢nil ah = 3≢0 (cong walk-len (AH→≡ G3-triangle-free ah))
  where
    3≢0 : 3 ≡ 0 → ⊥
    3≢0 ()

--------------------------------------------------------------------------------
-- §4. ★★ 加强：ℕ **单射**进 π₁ᵈ ⇒ π₁ᵈ 无限 ⇒ 一定不是 C₃
--
-- `cyc3w³≢nil` 只是「g³ ≠ e」；本节证的是更强的事实：
-- 圈数 m ↦ 同伦类 [g^m] 是**单射** ⇒ π₁ᵈ(G3) 有无穷多个元素
-- ⇒ **任何有限群都不可能与之同构**，尤其不是 C₃ ✓
--------------------------------------------------------------------------------

cycpow : ℕ → Walk G3 Fin.zero Fin.zero
cycpow zero    = nil Fin.zero
cycpow (suc n) = cyc3w ++w cycpow n

-- 长度核账：`_*_` 按第一参数递归，故写 `n * 3` 才与上面的递归同形 ✓
len-pow : ∀ n → walk-len (cycpow n) ≡ n * 3
len-pow zero    = refl
len-pow (suc n) =
  trans (walk-len-++w cyc3w (cycpow n))
        (cong (walk-len cyc3w +_) (len-pow n))

-- ★★ 主结论：不同圈数给出**不同**同伦类
cycpow-injective : ∀ {m n : ℕ} → m ≢ n → ¬ (AHomotopy G3 (cycpow m) (cycpow n))
cycpow-injective {m} {n} neq ah =
  neq (*-cancelʳ-≡ m n 3
        (trans (sym (len-pow m))
          (trans (cong walk-len (AH→≡ G3-triangle-free ah))
                 (len-pow n))))

-- 具体对照：0 圈与 3 圈不同类（C₃ 要求它们同类）
cycpow-0≢3 : ¬ (AHomotopy G3 (cycpow 0) (cycpow 3))
cycpow-0≢3 = cycpow-injective {m = 0} {n = 3} (λ ())
