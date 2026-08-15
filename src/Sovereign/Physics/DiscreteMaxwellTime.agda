{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Physics.DiscreteMaxwellTime
-- 78 电磁学 — 离散 Maxwell 时间演化层 (0 postulate, 无洞)
--
-- 先符号设计, 再落链。离散全息框架中时间是格点步进 t : ℕ, 时间差分
--   Δt F(t,p) = F(t+1,p) − F(t,p)   (GF(3) 上用 add3/neg3)
-- 四律的离散形式:
--   法拉第  Δt B = −curl E
--   安培    Δt E = curl B − J
--   高斯    div E = ρ
--   连续性  Δt ρ = −div J      (安培 + 高斯 的相容性推论)
--
-- 元定理 (符号证明, 对任意场成立, 无点态枚举):
--   divE-step   安培步进 ⇒ div E(t+1) = div E(t) − div J(t)   (div∘curl=0)
--   charge-conservation  安培步进 + 高斯 ⇒ Δt ρ = −div J
--   faraday-preserves-divB  法拉第步进 ⇒ div B 随时间守恒 (磁高斯自洽)
--   faraday/amp-diff-from-step  构造动力学 ⇒ 差分形式定律逐点成立
--
-- 修正上一稿三处类型缺陷:
--   1) proj₃ 不存在 — 分量用 proj₁ / proj₁∘proj₂ / proj₂∘proj₂ 投影;
--   2) "div (addVec3 (E t) ...) p" 类型错误 — div 吃场(函数), 不吃三元组;
--   3) 逐点安培律代入 div 需要邻点值 ⇒ 需要场级方程 (函数外延性无法
--      0-postulate 取得), 故步进定律以"场级等式"表述 (构造性动力学),
--      再证明其差分形式逐点成立 (cancel-right 向量代数), 闭环。

module Sovereign.Physics.DiscreteMaxwellTime where

open import Data.Nat using (ℕ; suc)
open import Data.Fin using (Fin) renaming (zero to fz; suc to fs)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; trans; sym; cong; cong₂; module ≡-Reasoning)
open ≡-Reasoning

-- 第二基石: GF3 域律 + 差分 + div/curl + dx/dy/dz-add/neg + 交换性
open import Sovereign.Physics.DiscreteEMField3D
-- 核心定理层: addVec3(+零元) + shuffle22 + div-curl-zero 全形式
open import Sovereign.Physics.DiscreteEMCore

------------------------------------------------------------------------------
-- §1. 向量代数 (三元组, 分量投影实现 — 不模式匹配, 保证对变量归约)
------------------------------------------------------------------------------

negVec3 : GF3 × GF3 × GF3 → GF3 × GF3 × GF3
negVec3 u = (neg3 (proj₁ u) , neg3 (proj₁ (proj₂ u)) , neg3 (proj₂ (proj₂ u)))

zeroVec : GF3 × GF3 × GF3
zeroVec = (fz , fz , fz)

addVec3-assoc : ∀ u v w → addVec3 (addVec3 u v) w ≡ addVec3 u (addVec3 v w)
addVec3-assoc u v w =
  cong₂ _,_
    (add3-assoc (proj₁ u) (proj₁ v) (proj₁ w))
    (cong₂ _,_
      (add3-assoc (proj₁ (proj₂ u)) (proj₁ (proj₂ v)) (proj₁ (proj₂ w)))
      (add3-assoc (proj₂ (proj₂ u)) (proj₂ (proj₂ v)) (proj₂ (proj₂ w))))

addVec3-comm : ∀ u v → addVec3 u v ≡ addVec3 v u
addVec3-comm u v =
  cong₂ _,_
    (add3-comm (proj₁ u) (proj₁ v))
    (cong₂ _,_
      (add3-comm (proj₁ (proj₂ u)) (proj₁ (proj₂ v)))
      (add3-comm (proj₂ (proj₂ u)) (proj₂ (proj₂ v))))

addVec3-neg-cancel : ∀ u → addVec3 u (negVec3 u) ≡ zeroVec
addVec3-neg-cancel u =
  cong₂ _,_
    (add3-inverse (proj₁ u))
    (cong₂ _,_
      (add3-inverse (proj₁ (proj₂ u)))
      (add3-inverse (proj₂ (proj₂ u))))

addVec3-left-identity : ∀ u → addVec3 zeroVec u ≡ u
addVec3-left-identity u = refl

-- 消去引理: (u + x) + (−u) ≡ x —— 差分方程求解的向量代数内核
cancel-right : ∀ u x → addVec3 (addVec3 u x) (negVec3 u) ≡ x
cancel-right u x = begin
  addVec3 (addVec3 u x) (negVec3 u)
    ≡⟨ addVec3-assoc u x (negVec3 u) ⟩
  addVec3 u (addVec3 x (negVec3 u))
    ≡⟨ cong (addVec3 u) (addVec3-comm x (negVec3 u)) ⟩
  addVec3 u (addVec3 (negVec3 u) x)
    ≡⟨ sym (addVec3-assoc u (negVec3 u) x) ⟩
  addVec3 (addVec3 u (negVec3 u)) x
    ≡⟨ cong (λ v → addVec3 v x) (addVec3-neg-cancel u) ⟩
  addVec3 zeroVec x
    ≡⟨ addVec3-left-identity x ⟩
  x ∎

------------------------------------------------------------------------------
-- §2. 散度代数 (div-linear / div-neg; div∘curl=0 引用核心定理层)
------------------------------------------------------------------------------

-- 六项 33 归并: (a+b)+((c+d)+(e+f)) ≡ (a+(c+e))+(b+(d+f))
-- div-linear 的关键重排 (17 步 GF(3) 符号链, 与 shuffle22 同族)。
div-rearrange : ∀ a b c d e f →
  add3 (add3 a b) (add3 (add3 c d) (add3 e f))
    ≡ add3 (add3 a (add3 c e)) (add3 b (add3 d f))
div-rearrange a b c d e f = begin
  add3 (add3 a b) (add3 (add3 c d) (add3 e f))
    ≡⟨ sym (add3-assoc (add3 a b) (add3 c d) (add3 e f)) ⟩
  add3 (add3 (add3 a b) (add3 c d)) (add3 e f)
    ≡⟨ shuffle22 (add3 a b) (add3 c d) e f ⟩
  add3 (add3 (add3 a b) e) (add3 (add3 c d) f)
    ≡⟨ cong (λ t → add3 t (add3 (add3 c d) f)) (add3-assoc a b e) ⟩
  add3 (add3 a (add3 b e)) (add3 (add3 c d) f)
    ≡⟨ cong (λ t → add3 t (add3 (add3 c d) f)) (cong (add3 a) (add3-comm b e)) ⟩
  add3 (add3 a (add3 e b)) (add3 (add3 c d) f)
    ≡⟨ cong (λ t → add3 t (add3 (add3 c d) f)) (sym (add3-assoc a e b)) ⟩
  add3 (add3 (add3 a e) b) (add3 (add3 c d) f)
    ≡⟨ add3-assoc (add3 a e) b (add3 (add3 c d) f) ⟩
  add3 (add3 a e) (add3 b (add3 (add3 c d) f))
    ≡⟨ cong (add3 (add3 a e)) (sym (add3-assoc b (add3 c d) f)) ⟩
  add3 (add3 a e) (add3 (add3 b (add3 c d)) f)
    ≡⟨ cong (add3 (add3 a e)) (cong (λ t → add3 t f) (sym (add3-assoc b c d))) ⟩
  add3 (add3 a e) (add3 (add3 (add3 b c) d) f)
    ≡⟨ cong (add3 (add3 a e)) (cong (λ t → add3 t f) (cong (λ u → add3 u d) (add3-comm b c))) ⟩
  add3 (add3 a e) (add3 (add3 (add3 c b) d) f)
    ≡⟨ cong (add3 (add3 a e)) (cong (λ t → add3 t f) (add3-assoc c b d)) ⟩
  add3 (add3 a e) (add3 (add3 c (add3 b d)) f)
    ≡⟨ cong (add3 (add3 a e)) (add3-assoc c (add3 b d) f) ⟩
  add3 (add3 a e) (add3 c (add3 (add3 b d) f))
    ≡⟨ cong (add3 (add3 a e)) (cong (add3 c) (add3-assoc b d f)) ⟩
  add3 (add3 a e) (add3 c (add3 b (add3 d f)))
    ≡⟨ sym (add3-assoc (add3 a e) c (add3 b (add3 d f))) ⟩
  add3 (add3 (add3 a e) c) (add3 b (add3 d f))
    ≡⟨ cong (λ t → add3 t (add3 b (add3 d f))) (add3-assoc a e c) ⟩
  add3 (add3 a (add3 e c)) (add3 b (add3 d f))
    ≡⟨ cong (λ t → add3 t (add3 b (add3 d f))) (cong (add3 a) (add3-comm e c)) ⟩
  add3 (add3 a (add3 c e)) (add3 b (add3 d f)) ∎

-- 散度线性: div (A + B) ≡ div A + div B (符号证明, 任意场)
div-linear : ∀ A B p →
  div (λ q → addVec3 (A q) (B q)) p ≡ add3 (div A p) (div B p)
div-linear A B p = begin
  div (λ q → addVec3 (A q) (B q)) p
    ≡⟨ refl ⟩
  add3 (dx (λ q → add3 (vx A q) (vx B q)) p)
       (add3 (dy (λ q → add3 (vy A q) (vy B q)) p)
             (dz (λ q → add3 (vz A q) (vz B q)) p))
    ≡⟨ cong₂ add3 (dx-add (vx A) (vx B) p)
                  (cong₂ add3 (dy-add (vy A) (vy B) p) (dz-add (vz A) (vz B) p)) ⟩
  add3 (add3 (dx (vx A) p) (dx (vx B) p))
       (add3 (add3 (dy (vy A) p) (dy (vy B) p))
             (add3 (dz (vz A) p) (dz (vz B) p)))
    ≡⟨ div-rearrange (dx (vx A) p) (dx (vx B) p)
                     (dy (vy A) p) (dy (vy B) p)
                     (dz (vz A) p) (dz (vz B) p) ⟩
  add3 (add3 (dx (vx A) p) (add3 (dy (vy A) p) (dz (vz A) p)))
       (add3 (dx (vx B) p) (add3 (dy (vy B) p) (dz (vz B) p)))
    ≡⟨ refl ⟩
  add3 (div A p) (div B p) ∎

-- 散度负向: div (−A) ≡ −div A (neg3-add 双向 + 差分负号引理)
div-neg : ∀ A p → div (λ q → negVec3 (A q)) p ≡ neg3 (div A p)
div-neg A p = begin
  div (λ q → negVec3 (A q)) p
    ≡⟨ refl ⟩
  add3 (dx (λ q → neg3 (vx A q)) p)
       (add3 (dy (λ q → neg3 (vy A q)) p) (dz (λ q → neg3 (vz A q)) p))
    ≡⟨ cong₂ add3 (dx-neg (vx A) p)
                  (cong₂ add3 (dy-neg (vy A) p) (dz-neg (vz A) p)) ⟩
  add3 (neg3 (dx (vx A) p)) (add3 (neg3 (dy (vy A) p)) (neg3 (dz (vz A) p)))
    ≡⟨ cong (add3 (neg3 (dx (vx A) p)))
            (sym (neg3-add (dy (vy A) p) (dz (vz A) p))) ⟩
  add3 (neg3 (dx (vx A) p)) (neg3 (add3 (dy (vy A) p) (dz (vz A) p)))
    ≡⟨ sym (neg3-add (dx (vx A) p) (add3 (dy (vy A) p) (dz (vz A) p))) ⟩
  neg3 (add3 (dx (vx A) p) (add3 (dy (vy A) p) (dz (vz A) p)))
    ≡⟨ refl ⟩
  neg3 (div A p) ∎

------------------------------------------------------------------------------
-- §3. 时间层: 依赖时间的场与时间差分
------------------------------------------------------------------------------

Time : Set
Time = ℕ

VecFieldTime : Set
VecFieldTime = Time → Point3D → GF3 × GF3 × GF3

ScalFieldTime : Set
ScalFieldTime = Time → Point3D → GF3

ΔtV : VecFieldTime → Time → Point3D → GF3 × GF3 × GF3
ΔtV F t p = addVec3 (F (suc t) p) (negVec3 (F t p))

ΔtS : ScalFieldTime → Time → Point3D → GF3
ΔtS f t p = add3 (f (suc t) p) (neg3 (f t p))

------------------------------------------------------------------------------
-- §4. 四律 (0 postulate 谓词定义)
------------------------------------------------------------------------------

FaradayHolds : VecFieldTime → VecFieldTime → Set
FaradayHolds B E = ∀ t p → ΔtV B t p ≡ negVec3 (curl (E t) p)

AmpereHolds : VecFieldTime → VecFieldTime → VecFieldTime → Set
AmpereHolds E B J = ∀ t p → ΔtV E t p ≡ addVec3 (curl (B t) p) (negVec3 (J t p))

GaussHolds : VecFieldTime → ScalFieldTime → Set
GaussHolds E ρ = ∀ t p → div (E t) p ≡ ρ t p

-- 场级 Yee 步进 (构造性动力学; 逐点形式因无 funext 无法达到场级, 故以
-- 场级等式直接声明步进 — 与用户约定一致: 构造而非空口断言)
FaradayStep : VecFieldTime → VecFieldTime → Set
FaradayStep B E = ∀ t → B (suc t) ≡ λ q → addVec3 (B t q) (negVec3 (curl (E t) q))

AmpereStep : VecFieldTime → VecFieldTime → VecFieldTime → Set
AmpereStep E B J = ∀ t → E (suc t) ≡
  λ q → addVec3 (E t q) (addVec3 (curl (B t) q) (negVec3 (J t q)))

------------------------------------------------------------------------------
-- §5. 构造动力学 ⟹ 差分形式定律 (逐点成立, cancel-right 向量代数)
------------------------------------------------------------------------------

faraday-diff-from-step : ∀ B E → FaradayStep B E → FaradayHolds B E
faraday-diff-from-step B E Bstep t p = begin
  ΔtV B t p
    ≡⟨ refl ⟩
  addVec3 (B (suc t) p) (negVec3 (B t p))
    ≡⟨ cong (λ F → addVec3 (F p) (negVec3 (B t p))) (Bstep t) ⟩
  addVec3 (addVec3 (B t p) (negVec3 (curl (E t) p))) (negVec3 (B t p))
    ≡⟨ cancel-right (B t p) (negVec3 (curl (E t) p)) ⟩
  negVec3 (curl (E t) p) ∎

amp-diff-from-step : ∀ E B J → AmpereStep E B J → AmpereHolds E B J
amp-diff-from-step E B J Estep t p = begin
  ΔtV E t p
    ≡⟨ refl ⟩
  addVec3 (E (suc t) p) (negVec3 (E t p))
    ≡⟨ cong (λ F → addVec3 (F p) (negVec3 (E t p))) (Estep t) ⟩
  addVec3 (addVec3 (E t p) (addVec3 (curl (B t) p) (negVec3 (J t p)))) (negVec3 (E t p))
    ≡⟨ cancel-right (E t p) (addVec3 (curl (B t) p) (negVec3 (J t p))) ⟩
  addVec3 (curl (B t) p) (negVec3 (J t p)) ∎

------------------------------------------------------------------------------
-- §6. 自洽性元定理 (先符号设计, 再落链)
--   divE-step:  安培步进 ⇒ div E(t+1) = div E(t) − div J(t)
--   其中 div∘curl=0 (核心定理层) 吃掉旋度项 — 磁场无源性的时间推论。
--   faraday-preserves-divB: 法拉第步进 ⇒ div B(t+1) = div B(t)
--   charge-conservation: 安培步进 + 高斯 ⇒ Δt ρ = −div J (连续性方程)
------------------------------------------------------------------------------

divE-step : ∀ E B J → AmpereStep E B J →
  ∀ t p → div (E (suc t)) p ≡ add3 (div (E t) p) (neg3 (div (J t) p))
divE-step E B J Estep t p = begin
  div (E (suc t)) p
    ≡⟨ cong (λ F → div F p) (Estep t) ⟩
  div (λ q → addVec3 (E t q) (addVec3 (curl (B t) q) (negVec3 (J t q)))) p
    ≡⟨ div-linear (E t) (λ q → addVec3 (curl (B t) q) (negVec3 (J t q))) p ⟩
  add3 (div (E t) p) (div (λ q → addVec3 (curl (B t) q) (negVec3 (J t q))) p)
    ≡⟨ cong (add3 (div (E t) p))
            (div-linear (curl (B t)) (λ q → negVec3 (J t q)) p) ⟩
  add3 (div (E t) p)
       (add3 (div (curl (B t)) p) (div (λ q → negVec3 (J t q)) p))
    ≡⟨ cong (add3 (div (E t) p))
            (cong (add3 (div (curl (B t)) p)) (div-neg (J t) p)) ⟩
  add3 (div (E t) p) (add3 (div (curl (B t)) p) (neg3 (div (J t) p)))
    ≡⟨ cong (add3 (div (E t) p))
            (cong (λ x → add3 x (neg3 (div (J t) p))) (div-curl-zero (B t) p)) ⟩
  add3 (div (E t) p) (add3 fz (neg3 (div (J t) p)))
    ≡⟨ refl ⟩
  add3 (div (E t) p) (neg3 (div (J t) p)) ∎

faraday-preserves-divB : ∀ B E → FaradayStep B E →
  ∀ t p → div (B (suc t)) p ≡ div (B t) p
faraday-preserves-divB B E Bstep t p = begin
  div (B (suc t)) p
    ≡⟨ cong (λ F → div F p) (Bstep t) ⟩
  div (λ q → addVec3 (B t q) (negVec3 (curl (E t) q))) p
    ≡⟨ div-linear (B t) (λ q → negVec3 (curl (E t) q)) p ⟩
  add3 (div (B t) p) (div (λ q → negVec3 (curl (E t) q)) p)
    ≡⟨ cong (add3 (div (B t) p)) (div-neg (curl (E t)) p) ⟩
  add3 (div (B t) p) (neg3 (div (curl (E t)) p))
    ≡⟨ cong (add3 (div (B t) p)) (cong neg3 (div-curl-zero (E t) p)) ⟩
  add3 (div (B t) p) (neg3 fz)
    ≡⟨ refl ⟩
  add3 (div (B t) p) fz
    ≡⟨ add3-identity (div (B t) p) ⟩
  div (B t) p ∎

-- 电荷守恒 (连续性方程): 安培步进 + 高斯 ⇒ Δt ρ = −div J
-- 符号推演: ρ(t+1) ≡ div E(t+1) [高斯 t+1]
--                    ≡ div (E t + curl B t − J t) [安培步进]
--                    ≡ div E t + div(curl B t) − div J t [div-linear/div-neg]
--                    ≡ ρ t + 0 − div J t [高斯 t; div∘curl=0]
charge-conservation : ∀ E B J ρ → AmpereStep E B J → GaussHolds E ρ →
  ∀ t p → ΔtS ρ t p ≡ neg3 (div (J t) p)
charge-conservation E B J ρ Estep gauss t p = begin
  ΔtS ρ t p
    ≡⟨ refl ⟩
  add3 (ρ (suc t) p) (neg3 (ρ t p))
    ≡⟨ cong (λ x → add3 x (neg3 (ρ t p))) (sym (gauss (suc t) p)) ⟩
  add3 (div (E (suc t)) p) (neg3 (ρ t p))
    ≡⟨ cong (λ x → add3 x (neg3 (ρ t p))) (divE-step E B J Estep t p) ⟩
  add3 (add3 (div (E t) p) (neg3 (div (J t) p))) (neg3 (ρ t p))
    ≡⟨ cong (λ x → add3 (add3 x (neg3 (div (J t) p))) (neg3 (ρ t p))) (gauss t p) ⟩
  add3 (add3 (ρ t p) (neg3 (div (J t) p))) (neg3 (ρ t p))
    ≡⟨ add3-assoc (ρ t p) (neg3 (div (J t) p)) (neg3 (ρ t p)) ⟩
  add3 (ρ t p) (add3 (neg3 (div (J t) p)) (neg3 (ρ t p)))
    ≡⟨ cong (add3 (ρ t p)) (add3-comm (neg3 (div (J t) p)) (neg3 (ρ t p))) ⟩
  add3 (ρ t p) (add3 (neg3 (ρ t p)) (neg3 (div (J t) p)))
    ≡⟨ sym (add3-assoc (ρ t p) (neg3 (ρ t p)) (neg3 (div (J t) p))) ⟩
  add3 (add3 (ρ t p) (neg3 (ρ t p))) (neg3 (div (J t) p))
    ≡⟨ cong (λ x → add3 x (neg3 (div (J t) p))) (add3-inverse (ρ t p)) ⟩
  add3 fz (neg3 (div (J t) p))
    ≡⟨ refl ⟩
  neg3 (div (J t) p) ∎

-- 0 postulate.
