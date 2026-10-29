{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Algebra.FieldTower.ZomegaMod3
-- Z[ω] 的 mod 3 退化与 F₃ 约化射：③ 裁决点（mod 3 幂零退化）的形式化锚。
-- 载体复用 A4Representation.Zω（勿重定义）；F₃ 复用 Sovereign.Base.Trit。
--
-- ═══════════════════════════════════════════════════════════════════
-- §A 展示与四条关系层级
--   Z[ω] = ℤ[X]/(X²+X+1) = ⟨ω | ω²+ω+1 = 0⟩，ℤ 的 3-分圆扩张。
--   关系层级：
--   (1) 生成：ω²+ω+1 = 0 是唯一生成关系（二次，分圆多项式 Φ₃）；
--   (2) 周期：ω³ = 1（由 (1) 导出：ω³−1 = (ω−1)(ω²+ω+1)）；
--   (3) 非平凡：ω ≢ 1（本库形式化锚：Zomega.omega-not-one；
--       特征 3 下此式失效——x³−1 = (x−1)³ 在 F₃ 上单根塌缩）；
--   (4) 归零：1+ω+ω² = 0（三项和作为【元素】恒等归零；
--       这是 char 0 中的非平凡归零，与 char 3 的 1+1+1=0【特征归零】机制不同）。
--
-- §B 三个阶的区分（易混点，逐层钉死）
--   加法群 (Z[ω],+) ≅ ℤ² 自由模（秩 2）：ω 加法【无限阶】——n·ω = 0 ⟹ n = 0；
--   乘法幺半群：ω 是【3 阶】元（3 次单位根，ω³=1 且 ω≢1）；
--   单位群 Z[ω]^× = {±1, ±ω, ±ω²} ≅ C₆（Zomega §9 全枚举）：
--   ⟨ω⟩ ≅ C₃ ⊂ C₆，±ω 为 6 次单位根（(−ω)³ = −1）。三阶互不等价。
--
-- §C 环结构（文档判定 + 库内形式锚）
--   交换环 ✓（环公理 8 条：Eisenstein §7 全证 + Zomega 迁移）；整环 ✓（经范数：
--   xy=0 ⟹ N(x)N(y)=0 于 ℤ ⟹ N(x)=0 或 N(y)=0 ⟹ x=0 或 y=0；正定性
--   a²−ab+b²>0 用 ℕ 序，本模块立界）；整闭 ✓（文献判定，未形式化）；
--   特征 0（n·1=0 ⟹ n=0）；分式域 Q(ω) = Q(√−3)；判别式 −3；
--   Gal(Z[ω]/ℤ) ≅ ℤ/2 = ⟨conj⟩（Zomega.conjZω-involutive + conjZω-add/mul/neg
--   全证——conj 是环自同构）。注意 conj 是 Galois 共轭，【不是】Frobenius：
--   x↦x³ 在 char 0 不保加法（非环同态）；Frobenius 4 阶共轭属于 GF(9) 层。
--
-- §D mod 3 约化退化（③ 裁决点）
--   x²+x+1 = (x−1)² (mod 3)（因 −2 ≡ 1）⟹ 3 在 Z[ω] 完全分歧：
--   Z[ω]/(3) ≅ F₃[X]/((X−1)²) = F₃[ε]/(ε²)，ε = ω−1，ε² = 0——幂零环【非域】。
--   形式锚（本模块）：ε² = −3ω ∈ (3)（Zωm3-w1-sq-In3，refl）而
--   ε ∉ (3)（Zωm3-w1-NotIn3，经 b-系数 3n≢1 归约定理）——ε 是 (3) 中非零幂零元。
--   到 GF(9) 的路径 = mod (ω−1) 先得 F₃（本模块 InW1Ideal：3 ∈ (ω−1)，refl），
--   再二次扩张 F₃(α)，α²=−1（库内 FieldTower.GF9，未在本模块接线）。
--   完整 ρ: Z[ω]→F₃ 同态性立界：需 ℤ→Trit 的 mod-3 加/乘同态引理
--   （ℤ 符号三分支 + ℕ 三步归纳的独立开发，估 ~200 行），本模块只给点态锚。
--
-- §E 本源/投影定位（关键判定）
--   Z[ω] 是【表示论投影】——特征标值域（A₄ 的 χ₁′/χ₁″ 值 ∈ {1,ω,ω²}、
--   χ₃ 值 ∈ {3,0,−1} ⊂ Z[ω]，见 Eisenstein §6），非大衍本源、非大衍投影。
--   八要素核对（3/8）：
--     ✓ 载体（Z² 逐坐标）、✓ 生成元（ω）、✓ 关系（ω²+ω+1=0）；
--     ✗ C₄ 相位（90° 相位层不在——±ω 只给 6 次根，无 4 阶元）；
--     ✗ 时钟 12（C₁₂/Doz 结构不在）；
--     ✗ Frobenius（x↦x³ 非自同构；4 阶共轭是 GF(9) 层专属）；
--     ✗ 核对（GF(9) 8 阶乘法群 / Frobenius 轨道核对机制不在）；
--     ✗ 归零不等价（char 0 元素归零 1+ω+ω²=0 ≠ char 3 特征归零 1+1+1=0；
--       形式锚：Zωm3-emb-add-fails——T₂↦−1 的加法嵌入被 2 ≢ −1 证伪）。
--   丢失清单（相对大衍本源）：C₄ 相位、时钟 12、Frobenius 4 阶、
--     特征 3 加法塌缩、GF(3^k) 有限域结构。
--   保留清单（相对大衍本源）：自由模 ℤ² 加法结构、3 次单位根乘法相位、
--     单位群 C₆、范数 N 与 Gal ≅ ℤ/2 共轭、A₄ 特征标值域（三代费米子分支
--     1⊕1′⊕1″ 的系数环）。
--   对照：ComplexProjection.agda 判「GF(9) 本源 → ℂ 连续投影」；本模块判
--   「Z[ω] 表示论投影」——Z[ω] 与 GF(9) 各自服务（A₄ 3 阶对称 vs E⊥B 90°），
--   与 A4Representation 头注「两者不可互相替代」一致。
--
-- 定级表：refl 级 = redF3 点锚/embF3 乘法/w1²/3∈(ω−1)/poly-shift；
--         定理级 = Zωm3-w1-NotIn3（经 3n≢1）、mul-compat×2、emb-red；
--         立界   = ρ 完整同态性、整环正定性、整闭性（§D/§C，理由见上）。
-- 0 postulate / 0 hole / 0 sorry。

module Sovereign.Algebra.FieldTower.ZomegaMod3 where

open import Data.Nat as ℕ using (ℕ; zero; suc; _≤_; z≤n; s≤s)
open import Data.Nat.Properties as ℕP using (≤-trans; m≤m+n; m≤n+m)
open import Data.Integer.Base using (ℤ; +_; -[1+_]; +[1+_]; _+_; _-_; _*_; -_; ∣_∣)
open import Data.Integer.Properties using (*-zeroˡ; *-zeroʳ; +-identityˡ; +-identityʳ)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; cong; cong₂; sym; trans; subst; module ≡-Reasoning)
open import Data.Empty using (⊥)
open import Data.Product using (Σ; Σ-syntax; _,_)

open ≡-Reasoning

open import Sovereign.Base.Trit using (Trit; T₀; T₁; T₂; _⊕_; _⊗_; negate)
open import Sovereign.Synthesis.A4.A4Representation
  using (Zω; mkZω; addZω; negZω; subZω; mulZω; zeroZω; oneZω; ω; ω²)
open import Sovereign.Algebra.FieldTower.Zomega
  using (mulZω-distribˡ; mulZω-distribʳ; mulZω-assoc; mulZω-comm)

--------------------------------------------------------------------------------
-- §0. 常数
--------------------------------------------------------------------------------

-- 3 = 3 + 0·ω（常数项）
Zωm3-three : Zω
Zωm3-three = mkZω (+ 3) (+ 0)

-- ε := ω − 1（3 在 Z[ω] 的素理想生成元; N(ω−1) = 3）
Zωm3-w1 : Zω
Zωm3-w1 = subZω ω oneZω

Zωm3-w1-form : Zωm3-w1 ≡ mkZω (-[1+ 0 ]) (+ 1)
Zωm3-w1-form = refl

--------------------------------------------------------------------------------
-- §1. 约化射 redF3 : Z[ω] → F₃（点态; 完整同态性立界见头注 §D）
--   ω ↦ 1（mod (ω−1)），即 a+bω ↦ a+b (mod 3)。
--   核对应为理想 (ω−1)：ω ≡ 1 ⟹ 1+1+1 = 3 ≡ 0 ✓（候选 (1−ω) 同理想）。
--   【勘误记录】任务书曾以 ω ≡ −1 检验：1−1+1 = 1 ≢ 0 ✗——ω ≡ −1 不是
--   同余候选，核是 (ω−1) 而非 (ω+1)；此勘误由 Zωm3-red-w1 形式钉死。
--------------------------------------------------------------------------------

mod3ℕ : ℕ → Trit
mod3ℕ zero = T₀
mod3ℕ (suc zero) = T₁
mod3ℕ (suc (suc zero)) = T₂
mod3ℕ (suc (suc (suc n))) = mod3ℕ n

mod3ℤ : ℤ → Trit
mod3ℤ (+ n) = mod3ℕ n
mod3ℤ (-[1+ n ]) = negate (mod3ℕ (suc n))

redF3 : Zω → Trit
redF3 (mkZω a b) = mod3ℤ (a + b)

-- 点态锚（全 refl）
Zωm3-red-one : redF3 oneZω ≡ T₁
Zωm3-red-one = refl

Zωm3-red-omega : redF3 ω ≡ T₁
Zωm3-red-omega = refl

Zωm3-red-omega2 : redF3 ω² ≡ T₁
Zωm3-red-omega2 = refl

Zωm3-red-three : redF3 Zωm3-three ≡ T₀
Zωm3-red-three = refl

Zωm3-red-w1 : redF3 Zωm3-w1 ≡ T₀
Zωm3-red-w1 = refl

-- 关系保持：ρ(1+ω+ω²) = T₀ —— ρ 与定义关系一致（商映射良定的必要条件）
Zωm3-red-rel : redF3 (addZω (addZω oneZω ω) ω²) ≡ T₀
Zωm3-red-rel = refl

--------------------------------------------------------------------------------
-- §2. 分解式 σ : F₃ → Z[ω]（乘法嵌入; ρ∘σ = id）
--   T₀↦0, T₁↦1, T₂↦−1。σ 乘法【精确】成立（9 案 refl）且是 ρ 的截面；
--   加法【不可】成立（§3 特征障碍）——F₃ 只以乘法幺半群 + 截面身份活在 Z[ω] 里。
--------------------------------------------------------------------------------

embF3 : Trit → Zω
embF3 T₀ = zeroZω
embF3 T₁ = oneZω
embF3 T₂ = mkZω (-[1+ 0 ]) (+ 0)

Zωm3-emb-mul : ∀ u v → mulZω (embF3 u) (embF3 v) ≡ embF3 (u ⊗ v)
Zωm3-emb-mul T₀ T₀ = refl
Zωm3-emb-mul T₀ T₁ = refl
Zωm3-emb-mul T₀ T₂ = refl
Zωm3-emb-mul T₁ T₀ = refl
Zωm3-emb-mul T₁ T₁ = refl
Zωm3-emb-mul T₁ T₂ = refl
Zωm3-emb-mul T₂ T₀ = refl
Zωm3-emb-mul T₂ T₁ = refl
Zωm3-emb-mul T₂ T₂ = refl

Zωm3-emb-red : ∀ u → redF3 (embF3 u) ≡ u
Zωm3-emb-red T₀ = refl
Zωm3-emb-red T₁ = refl
Zωm3-emb-red T₂ = refl

--------------------------------------------------------------------------------
-- §3. 特征障碍：σ 不能加法嵌入（char 0 vs char 3 的形式锚，八要素第 8 项）
--   反例 T₁,T₁：σT₁+σT₁ = 1+1 = 2，而 σ(T₁⊕T₁) = σT₂ = −1；Z[ω] 中 2 ≢ −1。
--------------------------------------------------------------------------------

Zωm3-emb-add-fails :
  ((u v : Trit) → addZω (embF3 u) (embF3 v) ≡ embF3 (u ⊕ v)) → ⊥
Zωm3-emb-add-fails H = absurd (cong Zω.a (H T₁ T₁))
  where
  -- 2 ≢ −1 于 ℤ（构造子相异）
  absurd : (+ 2) ≡ (-[1+ 0 ]) → ⊥
  absurd = λ ()

--------------------------------------------------------------------------------
-- §4. 理想 (3) 的同余机制（无商类型化的理想同余，纯分配律闭合）
--------------------------------------------------------------------------------

InIdeal3 : Zω → Set
InIdeal3 x = Σ[ q ∈ Zω ] x ≡ mulZω Zωm3-three q

-- 左乘对 (3)-挠扰动的兼容：x → x + 3d 使 xy 平移 3(dy)（distribʳ + assoc 重排）
Zωm3-mul-compatˡ : ∀ x y d
  → mulZω (addZω x (mulZω Zωm3-three d)) y
  ≡ addZω (mulZω x y) (mulZω Zωm3-three (mulZω d y))
Zωm3-mul-compatˡ x y d =
  trans (mulZω-distribʳ x (mulZω Zωm3-three d) y)
    (cong (addZω (mulZω x y)) (mulZω-assoc Zωm3-three d y))

-- 右乘同理（distribˡ + assoc/comm 重排：x(3d) = 3(xd)）
Zωm3-mul-compatʳ : ∀ x y d
  → mulZω x (addZω y (mulZω Zωm3-three d))
  ≡ addZω (mulZω x y) (mulZω Zωm3-three (mulZω x d))
Zωm3-mul-compatʳ x y d =
  trans (mulZω-distribˡ x y (mulZω Zωm3-three d))
    (cong (addZω (mulZω x y))
      (trans (sym (mulZω-assoc x Zωm3-three d))
        (trans (cong (λ t → mulZω t d) (mulZω-comm x Zωm3-three))
               (mulZω-assoc Zωm3-three x d))))

-- ε² = −3ω 精确恒等（refl）——幂零性的载体层事实
Zωm3-w1-sq : mulZω Zωm3-w1 Zωm3-w1 ≡ mkZω (+ 0) (-[1+ 2 ])
Zωm3-w1-sq = refl

-- ε² ∈ (3)，见证 q = −ω（refl）——【ε 是 (3) 中幂零元】的成员侧锚
Zωm3-w1-sq-In3 : InIdeal3 (mulZω Zωm3-w1 Zωm3-w1)
Zωm3-w1-sq-In3 = (mkZω (+ 0) (-[1+ 0 ])) , refl

-- 多项式退化锚：x²+x+1 与 (x−1)² 在 x=ω 处只差 3ω ∈ (3)——
-- x²+x+1 = (x−1)² (mod 3) 的点态形式化（头注 §D 的判别式退化）
Zωm3-poly-shift : InIdeal3 (subZω (mulZω Zωm3-w1 Zωm3-w1) (addZω (addZω ω² ω) oneZω))
Zωm3-poly-shift = (mkZω (+ 0) (-[1+ 0 ])) , refl

--------------------------------------------------------------------------------
-- §5. 理想 (ω−1) 与 F₃ 约化的理想侧
--------------------------------------------------------------------------------

InW1Ideal : Zω → Set
InW1Ideal x = Σ[ q ∈ Zω ] x ≡ mulZω Zωm3-w1 q

-- 3 ∈ (ω−1)，见证 q = −2−ω（refl）——Z[ω]/(ω−1) 中 3=0，约化到 F₃ 的理想侧锚
Zωm3-three-InW1 : InW1Ideal Zωm3-three
Zωm3-three-InW1 = (mkZω (-[1+ 1 ]) (-[1+ 0 ])) , refl

--------------------------------------------------------------------------------
-- §6. ε ∉ (3)：非域定理——(ω−1)² ∈ (3) 而 (ω−1) ∉ (3)
--   路线：若 (ω−1) = 3q，比对 ω-系数：3·q_b ≡ 1 于 ℤ，无解（ℤ 三分支 +
--   ℕ 不等式 2 ≤ 3(k+1)）。这是 Z[ω]/(3) 含非零幂零元的形式化主体。
--------------------------------------------------------------------------------

private
  nat3skNot1 : ∀ k → ℕ._*_ 3 (suc k) ≢ 1
  nat3skNot1 k eq = twoLeOne (subst (λ t → 2 ℕ.≤ t) eq twoLe)
    where
    -- 2 ≤ 2·(k+1)：1 ≤ k+1 ≤ (k+1)+((k+1)+0)（后一式即 2·(k+1) 的归约形）
    inner : 1 ℕ.≤ ℕ._*_ 2 (suc k)
    inner = ≤-trans (s≤s z≤n) (m≤m+n (suc k) (suc k ℕ.+ 0))
    hB' : 1 ℕ.≤ k ℕ.+ ℕ._*_ 2 (suc k)
    hB' = ≤-trans inner (m≤n+m (ℕ._*_ 2 (suc k)) k)
    -- 3·(k+1) = (k+1) + 2·(k+1) 定义层成立；s≤s hB' 给 2 ≤ suc(k+2·(k+1)) ≡ 2 ≤ 3·(k+1)
    twoLe : 2 ℕ.≤ ℕ._*_ 3 (suc k)
    twoLe = s≤s hB'

    twoLeOne : 2 ℕ.≤ 1 → ⊥
    twoLeOne (s≤s ())

  z3mulNot1 : ∀ (n : ℤ) → + 3 * n ≢ + 1
  z3mulNot1 (+ 0) = λ ()
  z3mulNot1 +[1+ k ] = λ eq → nat3skNot1 k (cong ∣_∣ eq)
  z3mulNot1 -[1+ k ] = λ ()

Zωm3-w1-NotIn3 : ∀ q → mulZω Zωm3-three q ≢ Zωm3-w1
Zωm3-w1-NotIn3 (mkZω qa qb) eq = z3mulNot1 qb h2
  where
  -- 3q 的 ω-系数 ≡ 3·q_b（ℤ 链：消去两个 0-乘积与两个 +0 尾）
  b3 : Zω.b (mulZω Zωm3-three (mkZω qa qb)) ≡ + 3 * qb
  b3 = begin
      Zω.b (mulZω Zωm3-three (mkZω qa qb))
    ≡⟨ refl ⟩
      (+ 3) * qb + (+ 0) * qa - (+ 0) * qb
    ≡⟨ cong (λ t → (+ 3) * qb + t - (+ 0) * qb) (*-zeroˡ qa) ⟩
      (+ 3) * qb + (+ 0) - (+ 0) * qb
    ≡⟨ cong (λ t → (+ 3) * qb + (+ 0) - t) (*-zeroˡ qb) ⟩
      (+ 3) * qb + (+ 0) - (+ 0)
    ≡⟨ cong (λ t → t - (+ 0)) (+-identityʳ ((+ 3) * qb)) ⟩
      (+ 3) * qb - (+ 0)
    ≡⟨ +-identityʳ ((+ 3) * qb) ⟩
      (+ 3) * qb
    ∎

  h1 : Zω.b (mulZω Zωm3-three (mkZω qa qb)) ≡ Zω.b Zωm3-w1
  h1 = cong Zω.b eq

  h2 : + 3 * qb ≡ + 1
  h2 = trans (sym b3) h1

-- 0 postulate.
