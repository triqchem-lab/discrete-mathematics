{-# OPTIONS --rewriting --guardedness #-}

-- | _PM3b — cr-via 系数传播律（配对传递——_PM2r/_PM3 合并立界清偿）
-- 数学背景：
--   cr-via 路由的复合系数 = (μ-in ⊗ i) ⊗ (T₂ ⊗ ν)（MorseCoeffRoute.CoefRouteDef）：
--   μ-in = 入段系数、i = 入口逆（coeff w e' ⊗ i ≡ T₁）、T₂ = ε 一次 V-箭头、ν = 尾段总系数。
--   「传播律」= Forman 配对的相消性质经 ⊗ 复合传递到尾段——两形态：
--   ①同前缀尾配对消去（传播本体：配对经 ⊗ 复合传递到尾段）；
--   ②配对前缀消去（入口对的复合相消）。合成 cr-via 面「中间贡献两两相消」。
--
-- 核心原则：
--   1. record 前提范式（FormanViaPairing——非 postulate，M3 里程碑 3 分水岭范式）；
--   2. 复用零重证（Trit 环律直引；viaTerm 镜像 _PM3 RouteD2.term；归纳形镜像 d2-pairs-zero）；
--   3. ∎ 链 ≤3（via-tail-cancel 2 trans；via-prefix-cancel 1 trans + cong₂）。
--
-- 包含：§1 因子桥（via-reassoc）｜§2 消去律（tail/prefix + 传播合成形 A/B）
--       §3 配对表归纳（FormanViaPairing + d2-via-pairs-zero）｜§4 K₃ 实例核对 ×5

module _PM3b where

open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; sym; trans; cong; cong₂)
open import Data.List using (List; []; _∷_)
open import Data.Product using (_×_; _,_)
open import Data.List.Relation.Unary.Any using (Any; here; there)
open import Data.List.Membership.Propositional using (_∈_)
open import Sovereign.Base.Trit using
  (Trit; T₀; T₁; T₂; _⊕_; _⊗_; ⊕-identityˡ; ⊗-assoc; ⊗-comm; ⊗-distribˡ-⊕)

------------------------------------------------------------------------
-- §0 本地零律（3-case 直证——Trit 无导出零律时的可靠形）
------------------------------------------------------------------------

⊗-zeroʳ-loc : (x : Trit) → x ⊗ T₀ ≡ T₀
⊗-zeroʳ-loc T₀ = refl
⊗-zeroʳ-loc T₁ = refl
⊗-zeroʳ-loc T₂ = refl

------------------------------------------------------------------------
-- §1 因子桥：复合系数形 (μ ⊗ i) ⊗ (t ⊗ ν) 的重排
------------------------------------------------------------------------

-- 复合系数右嵌套 ⟹ 左嵌套（sym ⊗-assoc 一步）
via-reassoc : (μ i t ν : Trit) → ((μ ⊗ i) ⊗ (t ⊗ ν)) ≡ ((μ ⊗ i) ⊗ t) ⊗ ν
via-reassoc μ i t ν = sym (⊗-assoc (μ ⊗ i) t ν)

------------------------------------------------------------------------
-- §2 消去律（传播律两形态）
------------------------------------------------------------------------

-- 传播本体：同前缀 + 尾配对 ⟹ 复合相消（配对经 ⊗ 复合传递到尾段）
via-tail-cancel : (p ν ν' : Trit) → ν ⊕ ν' ≡ T₀ → (p ⊗ ν) ⊕ (p ⊗ ν') ≡ T₀
via-tail-cancel p ν ν' h =
  trans (sym (⊗-distribˡ-⊕ p ν ν'))          -- (p⊗ν)⊕(p⊗ν') ≡ p⊗(ν⊕ν')   [分配律逆用]
  (trans (cong (λ z → p ⊗ z) h)              -- p⊗(ν⊕ν') ≡ p⊗T₀            [尾配对搬运]
         (⊗-zeroʳ-loc p))                     -- p⊗T₀ ≡ T₀                  [零律]

-- 配对前缀 + 同尾 ⟹ 复合相消（⊗-comm 翻到尾配对形）
via-prefix-cancel : (q q' ν : Trit) → q ⊕ q' ≡ T₀ → (q ⊗ ν) ⊕ (q' ⊗ ν) ≡ T₀
via-prefix-cancel q q' ν h =
  trans (cong₂ _⊕_ (⊗-comm q ν) (⊗-comm q' ν))  -- 转 (ν⊗q)⊕(ν⊗q')  [⊗ 交换]
        (via-tail-cancel ν q q' h)               -- 尾配对消去       [传播本体]

-- 传播合成形 A：入口前缀配对（μ-in⊗i 对）+ 同尾段 ⟹ 复合相消
via-propagate : (μ i μ' i' t ν : Trit) → (μ ⊗ i) ⊕ (μ' ⊗ i') ≡ T₀ →
                ((μ ⊗ i) ⊗ (t ⊗ ν)) ⊕ ((μ' ⊗ i') ⊗ (t ⊗ ν)) ≡ T₀
via-propagate μ i μ' i' t ν h = via-prefix-cancel (μ ⊗ i) (μ' ⊗ i') (t ⊗ ν) h

-- 传播合成形 B：同前缀 + 尾段配对（IH 传递形——两段尾配对复合传递）
via-propagate-tail : (μ i t ν ν' : Trit) → ν ⊕ ν' ≡ T₀ →
                     ((μ ⊗ i) ⊗ (t ⊗ ν)) ⊕ ((μ ⊗ i) ⊗ (t ⊗ ν')) ≡ T₀
via-propagate-tail μ i t ν ν' h =
  via-tail-cancel (μ ⊗ i) (t ⊗ ν) (t ⊗ ν') (via-tail-cancel t ν ν' h)

------------------------------------------------------------------------
-- §3 配对表归纳（镜像 _PM3 d2-pairs-zero 形）
------------------------------------------------------------------------

module ViaSum (K : Set) (coeff : K → K → Trit) (σ τ : K) where

  -- 中间胞腔贡献项（镜像 _PM3 RouteD2.term）
  viaTerm : K → Trit
  viaTerm ν = coeff ν σ ⊗ coeff τ ν

  -- 配对表形求和（按 (w,w') 成对累加）
  d2-via-sumP : List (K × K) → Trit
  d2-via-sumP [] = T₀
  d2-via-sumP ((w , w') ∷ ps) = (viaTerm w ⊕ viaTerm w') ⊕ d2-via-sumP ps

  -- cr-via 配对前提（record 假设参数——非 postulate，M3 分水岭范式）
  record FormanViaPairing (ps : List (K × K)) : Set where
    field
      via-cancel : ∀ {w w' : K} → (w , w') ∈ ps → viaTerm w ⊕ viaTerm w' ≡ T₀

  -- 归纳辅助：配对表尾段继承（成员弱化）
  weaken : ∀ {ps : List (K × K)} {p : K × K} →
           FormanViaPairing (p ∷ ps) → FormanViaPairing ps
  weaken {ps} {p} law = record
    { via-cancel = λ {w} {w'} m → FormanViaPairing.via-cancel law {w} {w'} (there m) }

  -- 主件：配对表逐对相消 ⟹ 全表归零（对归纳 + ⊕-identityˡ 收口）
  d2-via-pairs-zero : (ps : List (K × K)) → FormanViaPairing ps → d2-via-sumP ps ≡ T₀
  d2-via-pairs-zero [] law = refl
  d2-via-pairs-zero ((w , w') ∷ ps) law =
    trans (cong (λ z → z ⊕ d2-via-sumP ps)        -- 首对相消搬运        [via-cancel]
                (FormanViaPairing.via-cancel law {w} {w'} (here refl)))
    (trans (⊕-identityˡ (d2-via-sumP ps))          -- T₀ ⊕ rest ≡ rest    [单位律]
           (d2-via-pairs-zero ps (weaken law)))    -- rest ≡ T₀           [归纳假设]

------------------------------------------------------------------------
-- §4 K₃ 实例核对（MorseSqZeroK3 族值——cr-via 复合系数面）
------------------------------------------------------------------------

-- 入口逆数据形（K₃：coeff w e' ⊗ i ≡ T₁ 两解）
check-entry-inv₁ : T₂ ⊗ T₂ ≡ T₁
check-entry-inv₁ = refl

check-entry-inv₂ : T₁ ⊗ T₁ ≡ T₁
check-entry-inv₂ = refl

-- 传播合成形 A 核对：前缀配对 (T₂⊗T₂=T₁) ⊕ (T₂⊗T₁=T₂) ≡ T₀ + 同尾 t=T₁ ν=T₂
check-via-propagate : ((T₂ ⊗ T₂) ⊗ (T₁ ⊗ T₂)) ⊕ ((T₂ ⊗ T₁) ⊗ (T₁ ⊗ T₂)) ≡ T₀
check-via-propagate = via-propagate T₂ T₂ T₂ T₁ T₁ T₂ refl

-- 传播合成形 B 核对：同前缀 + 尾配对 (T₁,T₂)
check-via-tail : ((T₂ ⊗ T₂) ⊗ (T₁ ⊗ T₁)) ⊕ ((T₂ ⊗ T₂) ⊗ (T₁ ⊗ T₂)) ≡ T₀
check-via-tail = via-propagate-tail T₂ T₂ T₁ T₁ T₂ refl

-- 因子桥核对
check-via-reassoc : ((T₂ ⊗ T₂) ⊗ (T₂ ⊗ T₁)) ≡ ((T₂ ⊗ T₂) ⊗ T₂) ⊗ T₁
check-via-reassoc = via-reassoc T₂ T₂ T₂ T₁
