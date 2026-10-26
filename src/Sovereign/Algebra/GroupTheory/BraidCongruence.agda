{-# OPTIONS --guardedness #-}

-- | Sovereign.Algebra.GroupTheory.BraidCongruence
-- **B₃ 在词层的同余**：由定义关系 `aba ≈ bab` 生成的等价闭包，含消去与单边替换。
--
-- 为什么单独成模块：
--   本件只依赖 `Word`（零依赖语法层），**不 import Trit / 不 import --rewriting 模块**。
--   于是 `--cubical` 的商模块（`BraidQuotientCubical`）可以只导入
--   `Word` + 本件，导入锥内没有 REWRITE 规则——不会触发「cubical 静默丢弃规则」。
--
-- 设计要点（两次纠错的结果，详见 §① 与 §④ 注释）：
--   ① 替换规则用**两条单边**（b-appendˡ/ʳ），不用「中间挖孔」的 b-context——
--      后者因 `ε ++W p` 不定义性等于 `p` 而不可组合；
--   ② 词的逆用**前插**（pre* 系列）而非右接——`(w·a) ++W q` 不拆左因子，
--      右接逆会让 `a` 与 `a⁻¹` 被中间词隔开。
--
-- 包含：_≈b_（7 构造子）/ ≈b-cong / unitˡ,unitʳ,assoc≈ / pre{ai,bi,a,b} /
--       step-{a,b,ai,bi} / ι / invʳ / idem / invˡ
-- 0 postulate / 0 hole。

module Sovereign.Algebra.GroupTheory.BraidCongruence where

open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)

open import Sovereign.Algebra.GroupTheory.Word using
  ( Word; ε; _·a; _·b; _·ai; _·bi; _++W_; aba; bab
  ; ++W-assoc; ++W-idˡ; ++W-idʳ )

--------------------------------------------------------------------------------
-- ① 同余：等价闭包 + 两条单边替换 + 语法相等 + 四条消去 + 关系步
--------------------------------------------------------------------------------

infix 4 _≈b_

data _≈b_ : Word → Word → Set where
  b-refl    : ∀ {w} → w ≈b w
  b-sym     : ∀ {w v} → w ≈b v → v ≈b w
  b-trans   : ∀ {w v u} → w ≈b v → v ≈b u → w ≈b u
  -- 右接替换：w ≈ v ⇒ w ++ q ≈ v ++ q
  b-appendˡ : ∀ {w v} (q : Word) → w ≈b v → (w ++W q) ≈b (v ++W q)
  -- 左接替换：w ≈ v ⇒ p ++ w ≈ p ++ v
  b-appendʳ : ∀ {w v} (p : Word) → w ≈b v → (p ++W w) ≈b (p ++W v)
  -- 语法相等（使 `≡` 级的拼接律可以直接抬进同余）
  b-same    : ∀ {w v} → w ≡ v → w ≈b v
  -- 消去规则（与 eval-cancel-* 一一对应；词层的逆由此可算）
  b-cancel-a  : ∀ (w : Word) → (((w ·a)  ·ai)) ≈b w
  b-cancel-b  : ∀ (w : Word) → (((w ·b)  ·bi)) ≈b w
  b-cancel-ai : ∀ (w : Word) → (((w ·ai) ·a))  ≈b w
  b-cancel-bi : ∀ (w : Word) → (((w ·bi) ·b))  ≈b w
  -- 定义关系本体
  b-braid   : aba ≈b bab

--------------------------------------------------------------------------------
-- ② 同余对拼接的相容（商上的乘法需要它）
--------------------------------------------------------------------------------

≈b-cong : ∀ {p p' q q'} → p ≈b p' → q ≈b q' → (p ++W q) ≈b (p' ++W q')
≈b-cong {p} {p'} {q} {q'} hp hq =
  b-trans (b-appendˡ q hp) (b-appendʳ p' hq)

--------------------------------------------------------------------------------
-- ③ 单位律与结合律（抬入同余）
--------------------------------------------------------------------------------

unitˡ : ∀ w → (ε ++W w) ≈b w
unitˡ w = b-same (++W-idˡ w)

unitʳ : ∀ w → (w ++W ε) ≈b w
unitʳ w = b-same refl

assoc≈ : ∀ p q r → ((p ++W q) ++W r) ≈b (p ++W (q ++W r))
assoc≈ p q r = b-same (++W-assoc p q r)

--------------------------------------------------------------------------------
-- ④ 词上的逆：前插（Q1d）与消去步（Q1e）
--
-- `_++W_` 递归在第二元 ⇒ `(w·a) ++W q` 不会把左因子拆开。
-- 要让 `a` 与 `a⁻¹` 相邻，逆必须把 `a⁻¹` 放到词的**最前面**（前插）；
-- 于是 `(w·a) ++W preai u` 在 u 上归纳时，最后一次展开恰好给出 `((w·a)·ai)`。
--------------------------------------------------------------------------------

preai : Word → Word
preai ε       = ε ·ai
preai (v ·a)  = (preai v) ·a
preai (v ·b)  = (preai v) ·b
preai (v ·ai) = (preai v) ·ai
preai (v ·bi) = (preai v) ·bi

prebi : Word → Word
prebi ε       = ε ·bi
prebi (v ·a)  = (prebi v) ·a
prebi (v ·b)  = (prebi v) ·b
prebi (v ·ai) = (prebi v) ·ai
prebi (v ·bi) = (prebi v) ·bi

prea : Word → Word
prea ε       = ε ·a
prea (v ·a)  = (prea v) ·a
prea (v ·b)  = (prea v) ·b
prea (v ·ai) = (prea v) ·ai
prea (v ·bi) = (prea v) ·bi

preb : Word → Word
preb ε       = ε ·b
preb (v ·a)  = (preb v) ·a
preb (v ·b)  = (preb v) ·b
preb (v ·ai) = (preb v) ·ai
preb (v ·bi) = (preb v) ·bi

step-a : ∀ (w u : Word) → ((w ·a) ++W preai u) ≈b (w ++W u)
step-a w ε        = b-cancel-a w
step-a w (u ·a)   = b-appendˡ (ε ·a)  (step-a w u)
step-a w (u ·b)   = b-appendˡ (ε ·b)  (step-a w u)
step-a w (u ·ai)  = b-appendˡ (ε ·ai) (step-a w u)
step-a w (u ·bi)  = b-appendˡ (ε ·bi) (step-a w u)

step-b : ∀ (w u : Word) → ((w ·b) ++W prebi u) ≈b (w ++W u)
step-b w ε        = b-cancel-b w
step-b w (u ·a)   = b-appendˡ (ε ·a)  (step-b w u)
step-b w (u ·b)   = b-appendˡ (ε ·b)  (step-b w u)
step-b w (u ·ai)  = b-appendˡ (ε ·ai) (step-b w u)
step-b w (u ·bi)  = b-appendˡ (ε ·bi) (step-b w u)

step-ai : ∀ (w u : Word) → ((w ·ai) ++W prea u) ≈b (w ++W u)
step-ai w ε        = b-cancel-ai w
step-ai w (u ·a)   = b-appendˡ (ε ·a)  (step-ai w u)
step-ai w (u ·b)   = b-appendˡ (ε ·b)  (step-ai w u)
step-ai w (u ·ai)  = b-appendˡ (ε ·ai) (step-ai w u)
step-ai w (u ·bi)  = b-appendˡ (ε ·bi) (step-ai w u)

step-bi : ∀ (w u : Word) → ((w ·bi) ++W preb u) ≈b (w ++W u)
step-bi w ε        = b-cancel-bi w
step-bi w (u ·a)   = b-appendˡ (ε ·a)  (step-bi w u)
step-bi w (u ·b)   = b-appendˡ (ε ·b)  (step-bi w u)
step-bi w (u ·ai)  = b-appendˡ (ε ·ai) (step-bi w u)
step-bi w (u ·bi)  = b-appendˡ (ε ·bi) (step-bi w u)

--------------------------------------------------------------------------------
-- ⑤ 词的逆与双侧逆律（Q1f）
--
-- invʳ 直接由 step-x 归纳；invˡ 走经典路线：
--   y := ι w ++W w 幂等（y·y ≈ y），而 y 有右逆 ⇒ y ≈ ε。
--------------------------------------------------------------------------------

ι : Word → Word
ι ε       = ε
ι (w ·a)  = preai (ι w)
ι (w ·b)  = prebi (ι w)
ι (w ·ai) = prea (ι w)
ι (w ·bi) = preb (ι w)

invʳ : ∀ w → (w ++W ι w) ≈b ε
invʳ ε       = b-same refl
invʳ (w ·a)  = b-trans (step-a  w (ι w)) (invʳ w)
invʳ (w ·b)  = b-trans (step-b  w (ι w)) (invʳ w)
invʳ (w ·ai) = b-trans (step-ai w (ι w)) (invʳ w)
invʳ (w ·bi) = b-trans (step-bi w (ι w)) (invʳ w)

idem : ∀ w → (((ι w ++W w) ++W (ι w ++W w))) ≈b (ι w ++W w)
idem w =
  b-trans (assoc≈ (ι w) w (ι w ++W w))                         -- 展平左结合
    (b-trans (b-appendʳ (ι w) (b-sym (assoc≈ w (ι w) w)))      -- 内层重新结合
      (b-trans (b-appendʳ (ι w) (b-appendˡ w (invʳ w)))        -- w·(ιw) 消去
              (b-appendʳ (ι w) (unitˡ w))))                    -- ε·w → w

invˡ : ∀ w → ((ι w) ++W w) ≈b ε
invˡ w =
  b-trans (b-sym (unitʳ y))                                    -- y ≈ y·ε
    (b-trans (b-appendʳ y (b-sym (invʳ y)))                    -- ε ≈ y·ιy
      (b-trans (b-sym (assoc≈ y y (ι y)))                      -- 重新结合
        (b-trans (b-appendˡ (ι y) (idem w))                    -- y·y → y
                 (invʳ y))))                                   -- y·ιy → ε
  where
    y = ι w ++W w
