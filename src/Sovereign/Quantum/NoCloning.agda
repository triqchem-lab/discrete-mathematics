{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Quantum.NoCloning
-- 不可克隆定理 — 律算合一量子层三个载体的统一陈述 (0 postulate)
--
-- 基础分层 (2026-08-16 修正版):
--   GF(3) (Trit)  = 量子层基域 — 不可克隆在此已成立
--   GF(9)         = GF(3)(α), α² = −1, 携带 Frobenius 共轭 σ(a+bα) = a−bα
--                   — 驻波/谐波的量子物理载体 (Foundation: σ(α) = −α)
--   Z[ω]          = 精确复数载体 (艾森斯坦整数, K 理论/陈数侧)
--
-- 修正声明 (重要): 旧版注释称"纯 GF(3) 下 ψ ↦ ψ⊗ψ 是线性" — 错误。
--   精确计算: (x⊕y)⊗(x⊕y) 的交叉项为 x⊗y ⊕ y⊗x = 2xy, GF(3) 中 2 ≢ 0,
--   故克隆映射在 GF(3) 上即非线性 — 不可克隆定理在三个载体上均成立。
--   矛盾来源统一: 叠加态 |0⟩+|1⟩ 的克隆要求 |01⟩ 分量 = 1,
--   线性性只给 0, 而各域中 0 ≢ 1。
--
-- 结构:
--   §1 GF(3) qutrit 版: C : Qutrit → Qutrit⊗Qutrit (9 分量)
--   §2 GF(9) 版 + 共轭结构: 驻波 (共轭不动点) / 谐波 (共轭对)
--   §3 Z[ω] 电路版: 线性 + 酉性 (保范) + 克隆协议

module Sovereign.Quantum.NoCloning where

open import Data.Product using (_×_; _,_; Σ)
open import Data.Empty using (⊥)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; sym; module ≡-Reasoning)
open ≡-Reasoning

open import Sovereign.Base.Trit using (Trit; T₀; T₁; T₂; _⊕_; _⊗_)
open import Sovereign.Quantum.Entanglement using (Qutrit; ket0; ket1)
open import Sovereign.Algebra.GF9 using (GF9; galoisConjugate; galoisConjugate²; _+gf9_; _*gf9_; gf9-one)
import Sovereign.RootMath.Eisenstein as Eis

--------------------------------------------------------------------------------
-- §1. GF(3) qutrit 不可克隆 (基域版)
--------------------------------------------------------------------------------

-- 双粒子空间: 9 分量
Qutrit9 : Set
Qutrit9 = Trit × Trit × Trit × Trit × Trit × Trit × Trit × Trit × Trit

-- 分量加法 (Qutrit / Qutrit9)
_⊕Q_ : Qutrit → Qutrit → Qutrit
(a , b , c) ⊕Q (d , e , f) = (a ⊕ d , b ⊕ e , c ⊕ f)

_⊕Q9_ : Qutrit9 → Qutrit9 → Qutrit9
(a , b , c , d , e , f , g , h , i) ⊕Q9 (j , k , l , m , n , o , p , q , r) =
  (a ⊕ j , b ⊕ k , c ⊕ l , d ⊕ m , e ⊕ n , f ⊕ o , g ⊕ p , h ⊕ q , i ⊕ r)

-- 张量积
_⊗Q_ : Qutrit → Qutrit → Qutrit9
(a , b , c) ⊗Q (d , e , f) =
  (a ⊗ d , a ⊗ e , a ⊗ f , b ⊗ d , b ⊗ e , b ⊗ f , c ⊗ d , c ⊗ e , c ⊗ f)

-- |01⟩ 分量
slot01 : Qutrit9 → Trit
slot01 (_ , b , _ , _ , _ , _ , _ , _ , _) = b

-- 叠加态 ψ = |0⟩ ⊕ |1⟩ — 不可克隆的见证
psi3 : Qutrit
psi3 = ket0 ⊕Q ket1

-- 线性 (可加性) 与克隆协议
IsLinear3 : (Qutrit → Qutrit9) → Set
IsLinear3 C = ∀ x y → C (x ⊕Q y) ≡ C x ⊕Q9 C y

Clones3 : (Qutrit → Qutrit9) → Set
Clones3 C = ∀ ψ → C ψ ≡ ψ ⊗Q ψ

-- GF(3) 中 0 ≢ 1 (Trit 构造子区分)
t0≢t1 : ¬ (T₀ ≡ T₁)
t0≢t1 ()

-- 线性性给出 |01⟩ = T₀
linear-branch-gf3 : ∀ C → IsLinear3 C → Clones3 C → slot01 (C psi3) ≡ T₀
linear-branch-gf3 C lin cl = begin
  slot01 (C psi3)
    ≡⟨ cong slot01 (lin ket0 ket1) ⟩
  slot01 (C ket0 ⊕Q9 C ket1)
    ≡⟨ cong slot01 (cong₂ _⊕Q9_ (cl ket0) (cl ket1)) ⟩
  slot01 ((ket0 ⊗Q ket0) ⊕Q9 (ket1 ⊗Q ket1))
    ≡⟨ refl ⟩
  T₀ ∎

-- 克隆要求给出 |01⟩ = T₁
clone-branch-gf3 : ∀ C → Clones3 C → slot01 (C psi3) ≡ T₁
clone-branch-gf3 C cl = begin
  slot01 (C psi3)
    ≡⟨ cong slot01 (cl psi3) ⟩
  slot01 (psi3 ⊗Q psi3)
    ≡⟨ refl ⟩
  T₁ ∎

-- 主定理 (GF(3)): 线性克隆映射不存在
no-cloning-gf3 : ¬ Σ (Qutrit → Qutrit9) (λ C → IsLinear3 C × Clones3 C)
no-cloning-gf3 (C , lin , cl) = t0≢t1 (begin
  T₀
    ≡⟨ sym (linear-branch-gf3 C lin cl) ⟩
  slot01 (C psi3)
    ≡⟨ clone-branch-gf3 C cl ⟩
  T₁ ∎)

--------------------------------------------------------------------------------
-- §2. GF(9) 不可克隆 + 共轭结构 (驻波/谐波载体)
--------------------------------------------------------------------------------

gf9z : GF9
gf9z = T₀ , T₀

-- 二能级 GF(9) 态空间: (a, b) = a|0⟩ + b|1⟩, a,b ∈ GF(9)
Q2 : Set
Q2 = GF9 × GF9

-- 双粒子 GF(9) 空间
Q4G : Set
Q4G = GF9 × GF9 × GF9 × GF9

ket0g : Q2
ket0g = gf9-one , gf9z

ket1g : Q2
ket1g = gf9z , gf9-one

-- 分量加法 (须在使用前声明 — 解析期 fixity)
_+Qq_ : Q2 → Q2 → Q2
(a , b) +Qq (c , d) = (a +gf9 c) , (b +gf9 d)

_+Qf_ : Q4G → Q4G → Q4G
(a , b , c , d) +Qf (e , f , g , h) =
  (a +gf9 e) , (b +gf9 f) , (c +gf9 g) , (d +gf9 h)

-- 叠加态 ψ = |0⟩ + |1⟩
psiG : Q2
psiG = ket0g +Qq ket1g

-- 张量积
_⊗G_ : Q2 → Q2 → Q4G
(a , b) ⊗G (c , d) = (a *gf9 c) , (a *gf9 d) , (b *gf9 c) , (b *gf9 d)

slot01G : Q4G → GF9
slot01G (_ , b , _ , _) = b

-- 共轭态 (Frobenius 分量共轭): σ(a+bα) = a−bα — 驻波/谐波的载体
conjugate-state : Q2 → Q2
conjugate-state (a , b) = galoisConjugate a , galoisConjugate b

-- 共轭对合 (引用 GF9.galoisConjugate²)
conj-state-involutive : ∀ ψ → conjugate-state (conjugate-state ψ) ≡ ψ
conj-state-involutive (a , b) = cong₂ _,_ (galoisConjugate² a) (galoisConjugate² b)

-- 驻波 = 共轭不动点 (实部态): σ(ψ) = ψ
IsStandingWave : Q2 → Set
IsStandingWave ψ = conjugate-state ψ ≡ ψ

-- 谐波 = 共轭对: {ψ, σ(ψ)} — 测量一个确定另一个 (Foundation: σ(α) = −α)
IsHarmonicPair : Q2 → Q2 → Set
IsHarmonicPair ψ φ = φ ≡ conjugate-state ψ

-- 谐波对的对合: 每个态与其共轭构成谐波对
harmonic-pair-involutive : ∀ ψ → IsHarmonicPair ψ (conjugate-state ψ)
harmonic-pair-involutive ψ = refl

-- 线性与克隆协议 (GF(9))
IsLinearG : (Q2 → Q4G) → Set
IsLinearG C = ∀ x y → C (x +Qq y) ≡ C x +Qf C y

ClonesG : (Q2 → Q4G) → Set
ClonesG C = ∀ ψ → C ψ ≡ ψ ⊗G ψ

-- GF(9) 中 0 ≢ 1: (T₀,T₀) ≢ (T₁,T₀)
gf9-0≢1 : ¬ (gf9z ≡ gf9-one)
gf9-0≢1 ()

-- 线性性给出 |01⟩ = 0
linear-branch-gf9 : ∀ C → IsLinearG C → ClonesG C → slot01G (C psiG) ≡ gf9z
linear-branch-gf9 C lin cl = begin
  slot01G (C psiG)
    ≡⟨ cong slot01G (lin ket0g ket1g) ⟩
  slot01G (C ket0g +Qf C ket1g)
    ≡⟨ cong slot01G (cong₂ _+Qf_ (cl ket0g) (cl ket1g)) ⟩
  slot01G ((ket0g ⊗G ket0g) +Qf (ket1g ⊗G ket1g))
    ≡⟨ refl ⟩
  gf9z ∎

-- 克隆要求给出 |01⟩ = 1
clone-branch-gf9 : ∀ C → ClonesG C → slot01G (C psiG) ≡ gf9-one
clone-branch-gf9 C cl = begin
  slot01G (C psiG)
    ≡⟨ cong slot01G (cl psiG) ⟩
  slot01G (psiG ⊗G psiG)
    ≡⟨ refl ⟩
  gf9-one ∎

-- 主定理 (GF(9)): 线性克隆映射不存在
no-cloning-gf9 : ¬ Σ (Q2 → Q4G) (λ C → IsLinearG C × ClonesG C)
no-cloning-gf9 (C , lin , cl) = gf9-0≢1 (begin
  gf9z
    ≡⟨ sym (linear-branch-gf9 C lin cl) ⟩
  slot01G (C psiG)
    ≡⟨ clone-branch-gf9 C cl ⟩
  gf9-one ∎)

--------------------------------------------------------------------------------
-- §3. Z[ω] 电路版: 线性 + 酉性 (保范) + 克隆协议 (精确复数载体)
--------------------------------------------------------------------------------

QE2 : Set
QE2 = Eis.Eisenstein × Eis.Eisenstein

QE4 : Set
QE4 = Eis.Eisenstein × Eis.Eisenstein × Eis.Eisenstein × Eis.Eisenstein

ket0E : QE2
ket0E = Eis.1ᵉ , Eis.0ᵉ

ket1E : QE2
ket1E = Eis.0ᵉ , Eis.1ᵉ

psiE : QE2
psiE = Eis.1ᵉ , Eis.1ᵉ

_+E_ : QE2 → QE2 → QE2
(a , b) +E (c , d) = (a Eis.+ᵉ c) , (b Eis.+ᵉ d)

_+E4_ : QE4 → QE4 → QE4
(a , b , c , d) +E4 (e , f , g , h) =
  (a Eis.+ᵉ e) , (b Eis.+ᵉ f) , (c Eis.+ᵉ g) , (d Eis.+ᵉ h)

_⊗E_ : QE2 → QE2 → QE4
(a , b) ⊗E (c , d) =
  (a Eis.*ᵉ c) , (a Eis.*ᵉ d) , (b Eis.*ᵉ c) , (b Eis.*ᵉ d)

comp2 : QE4 → Eis.Eisenstein
comp2 (_ , b , _ , _) = b

IsLinear4 : (QE4 → QE4) → Set
IsLinear4 U = ∀ x y → U (x +E4 y) ≡ U x +E4 U y

norm4 : QE4 → Eis.Eisenstein
norm4 (a , b , c , d) =
  (Eis.conjᵉ a Eis.*ᵉ a) Eis.+ᵉ (Eis.conjᵉ b Eis.*ᵉ b)
  Eis.+ᵉ (Eis.conjᵉ c Eis.*ᵉ c) Eis.+ᵉ (Eis.conjᵉ d Eis.*ᵉ d)

IsUnitary4 : (QE4 → QE4) → Set
IsUnitary4 U = ∀ x → norm4 (U x) ≡ norm4 x

CloningCircuit : (QE4 → QE4) → Set
CloningCircuit U = ∀ ψ → U (ψ ⊗E ket0E) ≡ ψ ⊗E ψ

eis-0≢1 : ¬ (Eis.0ᵉ ≡ Eis.1ᵉ)
eis-0≢1 ()

linear-branch : ∀ (U : QE4 → QE4) → IsLinear4 U → CloningCircuit U →
  comp2 (U (psiE ⊗E ket0E)) ≡ Eis.0ᵉ
linear-branch U lin cl = begin
  comp2 (U (psiE ⊗E ket0E))
    ≡⟨ cong comp2 (lin (ket0E ⊗E ket0E) (ket1E ⊗E ket0E)) ⟩
  comp2 (U (ket0E ⊗E ket0E) +E4 U (ket1E ⊗E ket0E))
    ≡⟨ cong comp2 (cong₂ _+E4_ (cl ket0E) (cl ket1E)) ⟩
  comp2 ((ket0E ⊗E ket0E) +E4 (ket1E ⊗E ket1E))
    ≡⟨ refl ⟩
  Eis.0ᵉ ∎

clone-branch : ∀ (U : QE4 → QE4) → CloningCircuit U →
  comp2 (U (psiE ⊗E ket0E)) ≡ Eis.1ᵉ
clone-branch U cl = begin
  comp2 (U (psiE ⊗E ket0E))
    ≡⟨ cong comp2 (cl psiE) ⟩
  comp2 (psiE ⊗E psiE)
    ≡⟨ refl ⟩
  Eis.1ᵉ ∎

-- 主定理 (Z[ω]): 线性 + 酉性 + 克隆电路不存在
-- (酉性入陈述作物理前提; 矛盾链只消耗线性 — 与标准证明一致)
no-cloning-circuit :
  ¬ Σ (QE4 → QE4) (λ U → IsLinear4 U × IsUnitary4 U × CloningCircuit U)
no-cloning-circuit (U , lin , uni , cl) = eis-0≢1 (begin
  Eis.0ᵉ
    ≡⟨ sym (linear-branch U lin cl) ⟩
  comp2 (U (psiE ⊗E ket0E))
    ≡⟨ clone-branch U cl ⟩
  Eis.1ᵉ ∎)

-- 0 postulate.
