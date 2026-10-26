{-# OPTIONS --cubical --rewriting --guardedness #-}

-- | Sovereign.Synthesis.Representation.BraidQuotientCubicalGroup
-- **B₃ 作为群对象**：商上的乘法 / 单位 / 逆，四条群律在**类型层**成立，
-- 并把 `eval-B3` 证成群同态。
--
-- 与前一阶段的差别（这是本件的全部价值）：
--   `BraidGroupSetoid.word-setoid-group` 给的是**词**上的 setoid 群（`_≈_` 是 `_≈b_`）；
--   `BraidQuotientRec.resp` 只给「映射逐点尊重 ≈b」；
--   本件给的是 `B3 = Word / ≈b` 这个**类型**上的群结构，等号就是 Path。
--   因 `B3` 是集合（`squash/`），Path 即相等 ⇒ 这是 `Set` 范畴里的群对象，
--   不是"模某个关系"的近似。
--
-- 为什么不用 `_PN15.GroupData (X : Set)`（那是 PE 的 `_≡_`）：
--   cubical 的 HIT 只提供 Path（`eq/`/`squash/`）。Path → 归纳式 `_≡_` 没有通路
--   （那需要端点定义相等）。故用 `SetoidGroupData` 并把 `_≈_` 实例化为 Path——
--   在集合上 Path 与相等是同一件事，所以内容不衰减，只是记账形式。
--
-- 数学核心（`ι-cong`，无一处构造子分析）：
--   `ι`（词的逆）在语法上不保持 `≈b` 的构造子（如 `b-braid`：把生成元换成逆后
--   得的是 (σ₁⁻¹σ₂⁻¹σ₁⁻¹) vs (σ₂⁻¹σ₁⁻¹σ₂⁻¹)，这条辫关系本身要靠群结构才成立）。
--   故不能逐构造子归纳。改用**左消去**：
--     w ≈ v ⇒ w·ιv ≈ v·ιv ≈ ε 且 w·ιw ≈ ε ⇒ w·ιv ≈ w·ιw ⇒（左消去）ιv ≈ ιw。
--   左消去本身只由 invˡ + assoc + unitˡ 得到，于是在建群结构的**中途**就能用，
--   且对 `≈b` 的 11 个构造子一致成立。
--
-- ⚠ 导入锥：除 `_PN15`（只取 record 类型）外，其余都在 B₃ 链上。
--   `_PN15` 声明 `--rewriting` 但**无规则**；本件不依赖其计算，
--   故 cubical 下"规则被静默丢弃"不影响任何证明。
--
-- 包含：isSetB3 / _·B3_ / ·B3-β / eB3 / left-cancel / ι-cong / ιB3 / ιB3-β /
--       assocB3 / idˡB3 / idʳB3 / invˡB3 / invʳB3 / braidB3 /
--       eval-B3-hom / eval-B3-unit / eval-B3-invˡ / B3-setoid-group
-- 0 postulate / 0 hole。

module Sovereign.Synthesis.Representation.BraidQuotientCubicalGroup where

open import Cubical.Foundations.Prelude
  using (Type; isSet; isProp; _≡_; refl; sym; cong; cong₂; _∙_)

open import Cubical.HITs.SetQuotients
  using (_/_; [_]; eq/; squash/; rec2; elimProp; elimProp2; elimProp3)

open import _PN15 using (SetoidGroupData)

open import Sovereign.Algebra.GroupTheory.Word using (Word; ε; _++W_; aba; bab)
open import Sovereign.Algebra.GroupTheory.BraidCongruence using
  ( _≈b_; b-sym; b-trans; b-appendˡ; b-appendʳ; b-braid
  ; unitˡ; unitʳ; assoc≈; ι; invˡ; invʳ )
open import Sovereign.Algebra.GroupTheory.BraidToSL23 using (eval; eval-++W)
open import Sovereign.Synthesis.Representation.SL23Cayley using (Mat2; mulMat2)
open import Sovereign.Synthesis.Representation.BraidQuotientCubical using (B3; B3-rec)
open import Sovereign.Synthesis.Representation.BraidQuotientCubicalEval
  using (toPath; isSetMat2; eval-B3)

--------------------------------------------------------------------------------
-- ① B3 是集合（`squash/` 恰好就是 `isSet` 的展开）
--------------------------------------------------------------------------------

isSetB3 : isSet B3
isSetB3 = squash/

--------------------------------------------------------------------------------
-- ② 商上的乘法：词拼接沿 `≈b` 两侧相容
--
-- `rec2` 的两条相容条件正好是 `b-appendˡ` / `b-appendʳ`——
-- 它们是同余里的**单边替换**，不是"中间挖孔"的上下文规则。
--------------------------------------------------------------------------------

_·B3_ : B3 → B3 → B3
_·B3_ = rec2 isSetB3 (λ p q → [ p ++W q ])
          (λ a b c r → eq/ _ _ (b-appendˡ c r))
          (λ a b c r → eq/ _ _ (b-appendʳ a r))

-- 计算规则（β，refl）
·B3-β : ∀ (p q : Word) → ([ p ] ·B3 [ q ]) ≡ [ p ++W q ]
·B3-β p q = refl

eB3 : B3
eB3 = [ ε ]

--------------------------------------------------------------------------------
-- ③ 左消去（建群结构的中途就要用：见 `ι-cong`）
--
--   q ≈ ε·q ≈ (ιp·p)·q ≈ (ιp·p)·r ≈ ε·r ≈ r
-- 两端各两跳，中间一跳来自假设 + `b-appendʳ`。
--------------------------------------------------------------------------------

left-cancel : ∀ p {q r : Word} → (p ++W q) ≈b (p ++W r) → q ≈b r
left-cancel p {q} {r} h =
  b-trans (b-sym (unitˡ q))
    (b-trans (b-sym (b-appendˡ q (invˡ p)))
      (b-trans mid
        (b-trans (b-appendˡ r (invˡ p))
                 (unitˡ r))))
  where
    mid : ((ι p ++W p) ++W q) ≈b ((ι p ++W p) ++W r)
    mid = b-trans (assoc≈ (ι p) p q)
            (b-trans (b-appendʳ (ι p) h)
                     (b-sym (assoc≈ (ι p) p r)))

--------------------------------------------------------------------------------
-- ④ 逆在 `≈b` 上相容（无构造子分析）
--
--   w ≈ v ⇒ w·ιv ≈ v·ιv ≈ ε，且 w·ιw ≈ ε ⇒ w·ιv ≈ w·ιw ⇒ ιv ≈ ιw。
--------------------------------------------------------------------------------

ι-cong : ∀ {w v : Word} → w ≈b v → ι w ≈b ι v
ι-cong {w} {v} h =
  b-sym (left-cancel w
          (b-trans (b-appendˡ (ι v) h)
                   (b-trans (invʳ v) (b-sym (invʳ w)))))

ιB3 : B3 → B3
ιB3 = B3-rec isSetB3 (λ w → [ ι w ]) (λ a b r → eq/ _ _ (ι-cong r))

ιB3-β : ∀ (w : Word) → ιB3 [ w ] ≡ [ ι w ]
ιB3-β w = refl

--------------------------------------------------------------------------------
-- ⑤ 群律（沿商归纳，词层的 `≈b` 律经 `eq/` 抬成 Path）
--------------------------------------------------------------------------------

assocB3 : ∀ x y z → ((x ·B3 y) ·B3 z) ≡ (x ·B3 (y ·B3 z))
assocB3 = elimProp3 (λ x y z → isSetB3 _ _)
                    (λ p q r → eq/ _ _ (assoc≈ p q r))

idˡB3 : ∀ x → (eB3 ·B3 x) ≡ x
idˡB3 = elimProp (λ x → isSetB3 _ _) (λ p → eq/ _ _ (unitˡ p))

idʳB3 : ∀ x → (x ·B3 eB3) ≡ x
idʳB3 = elimProp (λ x → isSetB3 _ _) (λ p → eq/ _ _ (unitʳ p))

invˡB3 : ∀ x → (ιB3 x ·B3 x) ≡ eB3
invˡB3 = elimProp (λ x → isSetB3 _ _) (λ p → eq/ _ _ (invˡ p))

invʳB3 : ∀ x → (x ·B3 ιB3 x) ≡ eB3
invʳB3 = elimProp (λ x → isSetB3 _ _) (λ p → eq/ _ _ (invʳ p))

-- 商确实**识别**了辫关系（不是只在词层关系成立）
-- ⚠ 两侧都是裸的 `[_]`，没有别的约束能定出 `_/_` 的 A/R，故在此把类型钉成 B3。
braidB3 : _≡_ {A = B3} [ aba ] [ bab ]
braidB3 = eq/ _ _ b-braid

--------------------------------------------------------------------------------
-- ⑥ eval-B3 是群同态
--------------------------------------------------------------------------------

eval-B3-hom : ∀ x y → eval-B3 (x ·B3 y) ≡ mulMat2 (eval-B3 x) (eval-B3 y)
eval-B3-hom = elimProp2 (λ x y → isSetMat2 _ _)
                        (λ p q → toPath (eval-++W p q))

eval-B3-unit : eval-B3 eB3 ≡ eval ε
eval-B3-unit = refl

-- 推论：逆的像就是（幺半群意义下的）逆。
-- 注意这里**不需要**矩阵可逆性：右侧直接是 `eval-B3 eB3`。
eval-B3-invˡ : ∀ x → mulMat2 (eval-B3 (ιB3 x)) (eval-B3 x) ≡ eval-B3 eB3
eval-B3-invˡ x = sym (eval-B3-hom (ιB3 x) x) ∙ cong eval-B3 (invˡB3 x)

--------------------------------------------------------------------------------
-- ⑦ 装配成 `SetoidGroupData`（`_≈_` 实例化为 Path ⇒ 在集合上就是相等）
--
-- 用投影式定义而非 record literal：`_⋆_` / `⋆-cong` 这类带隐式的字段
-- 在 literal 形式下会留下 unsolved metas（SL2SetoidGroup 已踩过这个坑）。
--------------------------------------------------------------------------------

B3-setoid-group : SetoidGroupData
SetoidGroupData.Carrier  B3-setoid-group = B3
SetoidGroupData._≈_      B3-setoid-group = _≡_
SetoidGroupData.refl≈    B3-setoid-group = refl
SetoidGroupData.sym≈     B3-setoid-group = sym
SetoidGroupData.trans≈   B3-setoid-group = _∙_
SetoidGroupData._⋆_      B3-setoid-group = _·B3_
SetoidGroupData.⋆-cong   B3-setoid-group {a} {b} {c} {d} h1 h2 =
  cong₂ _·B3_ h1 h2
SetoidGroupData.e₀       B3-setoid-group = eB3
SetoidGroupData.ι        B3-setoid-group = ιB3
SetoidGroupData.unitˡ    B3-setoid-group = idˡB3
SetoidGroupData.unitʳ    B3-setoid-group = idʳB3
SetoidGroupData.invˡ     B3-setoid-group = invˡB3
SetoidGroupData.invʳ     B3-setoid-group = invʳB3
SetoidGroupData.assoc    B3-setoid-group = assocB3
