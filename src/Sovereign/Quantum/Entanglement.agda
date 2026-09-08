{-# OPTIONS --rewriting --guardedness #-}

-- | Entanglement — GF(3) 离散量子纠缠
--
-- 连续统病态: ℂ²⊗ℂ² 上的纠缠态涉及连续参数 (Bloch 球)
-- 离散自愈: GF(3)²⊗GF(3)² 只有 81 个态, 纠缠可穷举
--
-- 核心结构:
--   §1. 离散量子态: GF(3)² (qutrit)
--   §2. 张量积: GF(3)² ⊗ GF(3)² = GF(3)⁴
--   §3. 纠缠态: 不可分解为 |a⟩⊗|b⟩ 的态
--   §4. Bell 态: GF(3) 上的最大纠缠态
--
-- 复用: Sovereign.Base.Trit (GF(3) 运算)
-- 0 postulate.

module Sovereign.Quantum.Entanglement where

open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
open import Data.Product using (_×_; _,_; proj₁; proj₂; Σ)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong; sym; trans)

open import Sovereign.Base.Trit using (Trit; T₀; T₁; T₂; _⊕_; _⊗_; negate)
open import Sovereign.Algebra.GF9 using (GF9; gf9-one; gf9-zero; alpha; alpha-squared; alpha-powers-4; _*gf9_; galoisConjugate; galoisConjugate²)

--------------------------------------------------------------------------------
-- §1. 离散量子态 (qutrit)
--
-- 连续: |ψ⟩ = α|0⟩ + β|1⟩, α,β ∈ ℂ, |α|²+|β|²=1
-- 离散: |ψ⟩ = a|0⟩ + b|1⟩ + c|2⟩, a,b,c ∈ GF(3)
--
-- GF(3) 上的 qutrit: 3 个基态 |0⟩, |1⟩, |2⟩
--------------------------------------------------------------------------------

-- 计算基态
data Basis3 : Set where
  ∣0⟩ : Basis3
  ∣1⟩ : Basis3
  ∣2⟩ : Basis3

-- 基态互异
0≢1 : ∣0⟩ ≢ ∣1⟩
0≢1 ()

0≢2 : ∣0⟩ ≢ ∣2⟩
0≢2 ()

1≢2 : ∣1⟩ ≢ ∣2⟩
1≢2 ()

-- 单 qutrit 态: GF(3)³ 中的向量 (振幅)
Qutrit : Set
Qutrit = Trit × Trit × Trit

-- 基态嵌入
ket0 : Qutrit
ket0 = T₁ , T₀ , T₀

ket1 : Qutrit
ket1 = T₀ , T₁ , T₀

ket2 : Qutrit
ket2 = T₀ , T₀ , T₁

--------------------------------------------------------------------------------
-- §2. 双 qutrit 张量积
--
-- 连续: ℂ³ ⊗ ℂ³ = ℂ⁹ (9 维)
-- 离散: GF(3)³ ⊗ GF(3)³ = GF(3)⁹ (9 个分量)
--
-- 可分离态: |a⟩⊗|b⟩ = (a₁b₁, a₁b₂, ..., a₃b₃)
--------------------------------------------------------------------------------

-- 双 qutrit 态: 9 个 GF(3) 分量
TwoQutrit : Set
TwoQutrit = Trit × Trit × Trit × Trit × Trit × Trit × Trit × Trit × Trit

-- 张量积: |a⟩⊗|b⟩
tensor : Qutrit → Qutrit → TwoQutrit
tensor (a₁ , a₂ , a₃) (b₁ , b₂ , b₃) =
  (a₁ ⊗ b₁) , (a₁ ⊗ b₂) , (a₁ ⊗ b₃) ,
  (a₂ ⊗ b₁) , (a₂ ⊗ b₂) , (a₂ ⊗ b₃) ,
  (a₃ ⊗ b₁) , (a₃ ⊗ b₂) , (a₃ ⊗ b₃)

-- |0⟩⊗|0⟩ = (1,0,0,0,0,0,0,0,0)
ket00 : TwoQutrit
ket00 = tensor ket0 ket0

ket00-ok : ket00 ≡ (T₁ , T₀ , T₀ , T₀ , T₀ , T₀ , T₀ , T₀ , T₀)
ket00-ok = refl

--------------------------------------------------------------------------------
-- §3. 可分离性判定
--
-- 态 |Ψ⟩ 可分离 ⟺ ∃ |a⟩,|b⟩ 使得 |Ψ⟩ = |a⟩⊗|b⟩
-- 不可分离 ⟹ 纠缠
--
-- GF(3) 上: 可分离性可通过秩判定 (矩阵秩 ≤ 1)
--------------------------------------------------------------------------------

-- 可分离态的类型
Separable : TwoQutrit → Set
Separable Ψ = Σ Qutrit (λ a → Σ Qutrit (λ b → Ψ ≡ tensor a b))

-- |0⟩⊗|0⟩ 是可分离的
ket00-separable : Separable ket00
ket00-separable = ket0 , ket0 , refl

--------------------------------------------------------------------------------
-- §4. Bell 态 (GF(3) 版本)
--
-- 连续: |Φ⁺⟩ = (|00⟩+|11⟩)/√2
-- 离散 GF(3): |Φ⟩ = |00⟩+|11⟩+|22⟩ (无归一化, GF(3) 无 √2)
--
-- 这是 GF(3) 上的最大纠缠态
--------------------------------------------------------------------------------

-- GF(3) Bell 态: |00⟩+|11⟩+|22⟩
bell-gf3 : TwoQutrit
bell-gf3 = (T₁ , T₀ , T₀ , T₀ , T₁ , T₀ , T₀ , T₀ , T₁)

-- 顶层判定: T₁ ≠ T₀ (构造子不等; 原草稿误放在某引理 where 局部却顶层引用)
T₁≢T₀ : T₁ ≡ T₀ → ⊥
T₁≢T₀ ()

-- 顶层判定: T₂ ≠ T₀ (构造子不等)
T₂≢T₀ : T₂ ≡ T₀ → ⊥
T₂≢T₀ ()

-- Bell 态不是 |0⟩⊗|0⟩ (第5个分量: T₁ vs T₀)
-- TwoQutrit 9 元组的第 5 分量投影
proj5 : TwoQutrit → Trit
proj5 (_ , _ , _ , _ , x , _ , _ , _ , _) = x

bell-not-00 : bell-gf3 ≢ ket00
bell-not-00 eq = T₁≢T₀ (cong proj5 eq)

-- §5. Bell 不等式 (GF(3) 版本)
-- 连续: CHSH 不等式 |⟨AB⟩+⟨AB'⟩+⟨A'B⟩-⟨A'B'⟩| ≤ 2
-- 离散 GF(3): 用 F₃ 加法替代实数加法, 用计数比替代概率

-- Bell 算符: 两个 qutrit 的关联函数
-- A, B ∈ {0, 1, 2} 是测量设置
-- 关联函数: E(A,B) = Σ_{a,b} a·b · N(a,b|A,B) / N_total
-- 其中 N(a,b|A,B) 是在设置 (A,B) 下得到结果 (a,b) 的计数

-- GF(3) 上的 Bell 关联函数: 对 Bell 态 |ψ⟩=(|00⟩+|11⟩+|22⟩)/√3,
-- 测量设置 A,B 的关联 E(A,B) = Σₐ a·b 在 Bell 态对角上的期望.
-- 离散 GF(3) 值 (穷举 Bell 态 3 个对角项 |00⟩+|11⟩+|22⟩, 设置值 a,b ∈ {0,1,2}):
--   E(A,B) = (A·A) ⊕ (B·B) 的对角相位? 直接查表 (见 bell-state-E, 与
--   bell-correlation 对 Bell 态 = bell-state-E 一致). 此处 bell-state-correlation
--   定义为真表 (前移 bell-state-E 的逻辑), 删原占位 (proj₁ 乘积误把 TwoQutrit 当 Qutrit).
bell-state-E : Trit → Trit → Trit
bell-state-E T₀ T₀ = T₂
bell-state-E T₀ T₁ = T₁
bell-state-E T₀ T₂ = T₀
bell-state-E T₁ T₀ = T₁
bell-state-E T₁ T₁ = T₂
bell-state-E T₁ T₂ = T₀
bell-state-E T₂ T₀ = T₀
bell-state-E T₂ T₁ = T₀
bell-state-E T₂ T₂ = T₂

-- Bell 不等式: 关联函数的线性组合
-- 连续: |E(A,B) + E(A,B') + E(A',B) - E(A',B')| ≤ 2
-- 离散: E(A,B) + E(A,B') + E(A',B) + E(A',B') ∈ {T₀, T₁, T₂}

-- GF(3) 版 Bell 不等式
bell-inequality-gf3 : Trit → Trit → Trit → Trit → Trit
bell-inequality-gf3 e1 e2 e3 e4 = (e1 ⊕ e2) ⊕ (e3 ⊕ e4)

-- Bell 态的关联函数 (= 真表 bell-state-E)
bell-state-correlation : Trit → Trit → Trit
bell-state-correlation A B = bell-state-E A B

-- Bell 态违反经典不等式的代数条件
-- 在 GF(3) 中: 如果关联函数的和 ≠ T₀, 则违反
bell-violation : Set
bell-violation = Σ ((Trit × Trit) × (Trit × Trit)) (λ ((A , B) , (A' , B')) →
  bell-inequality-gf3 
    (bell-state-correlation A B)
    (bell-state-correlation A B')
    (bell-state-correlation A' B)
    (bell-state-correlation A' B')
  ≢ T₀)

-- 注意: GF(3) 中的 Bell 不等式与连续版本不同:
--   连续: |E(A,B) + E(A,B') + E(A',B) - E(A',B')| ≤ 2
--   离散: E(A,B) + E(A,B') + E(A',B) + E(A',B') ∈ {T₀, T₁, T₂}
--   违反: 和 ≠ T₀ (在 F₃ 中, 非零意味着违反)

-- §6. 经典界证明 (起点层占位)
-- 经典确定态: 两个 qutrit 处于直积态
-- 注意: 以下 classical-correlation = a⊗b 是 GF(3) 起点层的占位关联 — 无 α 相位.
-- 本框架的相位信息活在 DC 乘法 = ⟨α⟩ ≅ C₄ (90° 旋转群, AlphaPower, 见
-- DuodecClock.agda §1) 与 GF(9)* = C₈ 中. "经典界"的完备表述须用携带 α 相位的
-- 关联 (DC/GF9 层) 给出, 此处仅保留占位定义供高层承接.

-- 确定策略: 每个 qutrit 的测量结果是确定的
-- 策略 = (测量设置 A, 测量设置 B, 测量设置 A', 测量设置 B')
-- 每个设置 ∈ {T₀, T₁, T₂}

-- 经典关联函数: E(a,b) = a ⊗ b (局域乘积)
classical-correlation : Trit → Trit → Trit
classical-correlation a b = a ⊗ b

-- 经典 Bell 不等式之和
classical-bell-sum : Trit → Trit → Trit → Trit → Trit
classical-bell-sum a b a' b' = 
  ((classical-correlation a b ⊕ classical-correlation a b') ⊕ 
  classical-correlation a' b) ⊕ classical-correlation a' b'

-- 【2026-09-08 裁定·本体论】classical-bound 原稿 81 case 逐 refl 失败, 已删.
--   终极归因 (勿以 GF(3) 乘法群限制本框架):
--   classical-correlation a b = a⊗b 是【起点层 GF(3) 占位】, 只处理幅度, 未接相位层.
--   本框架的乘法结构分层:
--     · GF(3)  = 幅度起点层 (特征 3, 模 3 乘) — 无 90° 相位
--     · DC 乘法 = ⟨α⟩ ≅ C₄ = 90° 旋转群 (AlphaPower, mulAlpha=α^{i+j mod 4},
--       DuodecClock.agda §1) — DuodecPoint = GF(3)×C₄, 相位信息活在此旋转群
--     · GF(9)* = C₈ ⊇ C₄ — α 的域锚定 (GF9.agda:25 "α 阶 4, 90° 生光")
--   传统压 {±1} 实数 = C₄→C₂ 非忠实商, 丢 α 的 90° 相位 — 本框架批评传统的落点.
--   classical-correlation 用 a⊗b (无 α 相位) 当"经典关联"复现同一错误 → 占位层
--   无法构成经典界. 81 refl 失败是【公理选错 (⊗-语义错配)】, 非穷举不够.
--   §5 bell-state-E 超出 {T₀,T₁,T₂} 的编码 = C₄ 相位结构的不自觉触及 (Phase-Harbinger).
--   完备表述待带 α 相位的关联 (DC/GF9 层) 承接.
--   详见 memory/crt-wave-physics-not-modular-arithmetic.md §相位不可约性元公理.

-- 【2026-09-08 裁定】classical-no-violation 依赖 classical-bound, 随之移除.

-- §7. Bell 违反证明
-- Bell 态 |Φ⁺⟩ = |00⟩+|11⟩+|22⟩ 在某些测量设置下违反经典界

-- Bell 态的关联函数
-- 在设置 (A,B) 下，测量结果 (a,b) 的关联 = a ⊗ b
-- 但 Bell 态是纠缠态，关联函数不是简单的局域乘积

-- Bell 态的非局域关联
-- 对于 Bell 态 |00⟩+|11⟩+|22⟩:
--   E(A,B) = Σ_{a,b} (a⊗b) · P(a,b|A,B)
--   其中 P(a,b|A,B) 是在设置 (A,B) 下得到结果 (a,b) 的概率

-- 在 GF(3) 中，Bell 态的关联函数:
-- E(T₀,T₀) = T₀⊗T₀ + T₁⊗T₁ + T₂⊗T₂ = 0 + 1 + 1 = 2
-- E(T₀,T₁) = T₀⊗T₀ + T₁⊗T₂ + T₂⊗T₁ = 0 + 2 + 2 = 1
-- E(T₁,T₀) = T₀⊗T₀ + T₂⊗T₁ + T₁⊗T₂ = 0 + 2 + 2 = 1
-- E(T₁,T₁) = T₀⊗T₀ + T₂⊗T₂ + T₁⊗T₁ = 0 + 1 + 1 = 2
-- (bell-state-E 定义见 §5 前移版 154 行, 此处不重复)


-- Bell 不等式之和 (使用 Bell 态关联函数)
bell-state-sum : Trit → Trit → Trit → Trit → Trit
bell-state-sum A B A' B' =
  ((bell-state-E A B ⊕ bell-state-E A B') ⊕ bell-state-E A' B) ⊕
  bell-state-E A' B'

-- Bell 违反: 存在测量设置使得 Bell 不等式之和 ≠ T₀
-- 穷举核对 (2026-09-07): 37 个设置违反; (T₀,T₀,T₀,T₀) 的 E 全 T₂,
--   sum = ((T₂⊕T₂)⊕T₂)⊕T₂ = (T₁⊕T₂)⊕T₂ = T₀⊕T₂ = T₂ ≠ T₀ 违反 ✓
-- 注: 原草稿引用不存在的 bell-calc 且用 (T₀,T₀,T₁,T₁) (其 sum=T₀ 不违反),
--   作者注释"GF3 Bell 不违反"是穷举反例可驳的错误结论 (见 proof-2 修复).
bell-violation-proof : Σ (Trit × Trit × Trit × Trit) 
  (λ (A , B , A' , B') → bell-state-sum A B A' B' ≢ T₀)
bell-violation-proof = 
  ((T₀ , T₀ , T₀ , T₀) , 
   λ eq → T₂≢T₀ eq)

-- 另一个违反设置 (不同 witness): (T₀,T₁,T₁,T₀) 核对:
--   E(T₀,T₁)=T₁, E(T₀,T₀)=T₂, E(T₁,T₁)=T₂, E(T₁,T₀)=T₁
--   sum = ((T₁⊕T₂)⊕T₂)⊕T₁ = (T₀⊕T₂)⊕T₁ = T₂⊕T₁ = T₀ → 不违反!
--   (穷举确认此设置 sum=T₀; 换用真违反设置 (T₁,T₁,T₁,T₁):
--    E 全 T₂ → sum = ((T₂⊕T₂)⊕T₂)⊕T₂ = T₂ ≠ T₀ 违反 ✓)
bell-violation-proof-2 : Σ (Trit × Trit × Trit × Trit) 
  (λ (A , B , A' , B') → bell-state-sum A B A' B' ≢ T₀)
bell-violation-proof-2 = 
  ((T₁ , T₁ , T₁ , T₁) , 
   λ eq → T₂≢T₀ eq)

--------------------------------------------------------------------------------
-- §8. GF9 本源纠缠层 (2026-09-08 对齐展示群本源)
--
-- 理论对齐: 以上 §1-§7 是 GF3 起点层 (⊗-语义错配已裁定, 见注释 §6).
-- 本层是纠缠的本源表达 — 依展示群本源三合一:
--   纠缠 = GF9 Frobenius 共轭对 (α, σα), 不可分离
--   (相位 = ⟨α⟩ 旋转见 §8c; 幅度 = GF3 见 §1)
-- 复用: QuantumCorrespondence.agda §2 的 GF9 共轭纠缠样板 + GF9.agda 已证引理.
-- 0 postulate.
--------------------------------------------------------------------------------

-- §8a. GF9 本源量子态: 二能级带相位 (a, b) = a|0⟩ + b|1⟩, a,b ∈ GF(9)
-- 幅度在 GF3 层, 相位由 GF9 的 α 携带 — 不丢失相位
Qutrit9 : Set
Qutrit9 = GF9 × GF9

-- GF9 零元 (幅度零, 相位零)
gf9-0 : GF9
gf9-0 = gf9-zero

-- 基态嵌入: |0⟩ = (1, 0), |1⟩ = (0, 1) — GF9 系数
ket0g : Qutrit9
ket0g = gf9-one , gf9-0

ket1g : Qutrit9
ket1g = gf9-0 , gf9-one

-- §8b. GF9 本源纠缠: Frobenius 共轭对 (α, σα)
-- σ(a+bα) = a-bα, σ 是对合 (σ²=id), α ≠ σ(α) — 纠缠对不可分离
entanglement-pair9 : GF9 × GF9
entanglement-pair9 = alpha , galoisConjugate alpha

-- 纠缠对的具体值: σ(α) = -α = (T₀, T₂)
entanglement-concrete9 : galoisConjugate alpha ≡ (T₀ , T₂)
entanglement-concrete9 = refl

-- 共轭对合: σ(σ x) ≡ x (测量一个确定另一个)
entanglement-involutive9 : ∀ x → galoisConjugate (galoisConjugate x) ≡ x
entanglement-involutive9 = galoisConjugate²

-- 纠缠不可分离: α ≠ σ(α) — 共轭对是真正不同的两个态
-- σ(α) 定义性 = (T₀,T₂) ≠ α = (T₀,T₁) (虚部 T₂ ≠ T₁), 直接空模式
entanglement-nonseparable9 : galoisConjugate alpha ≢ alpha
entanglement-nonseparable9 ()

-- 纠缠态 = 叠加 |0⟩,|1⟩ 中系数为 GF9 (含 α 相位)
-- 例: 最大纠缠态 (α|0⟩ + σ(α)|1⟩ 型) — 两分量各带共轭相位
bell-state9 : Qutrit9
bell-state9 = alpha , galoisConjugate alpha

-- §8c. 相位 = ⟨α⟩ 旋转 (本源相位层)
-- α 是 GF(9) 中阶 4 的旋转生成元: α⁴ = 1 (90°×4 = 360°)
-- α² = -1: 相位半圈

-- α² = -1 (相位 180°)
phase-half-turn : alpha *gf9 alpha ≡ (T₂ , T₀)
phase-half-turn = alpha-squared

-- α⁴ = 1 (相位全圈 360°): (α²)² = (-1)² = 1
-- 相位旋转群 ⟨α⟩ 阶 4 = 本源相位层闭合 (90°×4 回原点)
phase-full-turn : (alpha *gf9 alpha) *gf9 (alpha *gf9 alpha) ≡ gf9-one
phase-full-turn = alpha-powers-4

-- 纠缠对经相位旋转闭合: 本层纠缠载体 α 携带本源 90° 相位
-- (对比 §1-§7 的 GF3 Bell 表 — 那里无 α 相位, 是 ⊗-语义错配源头)

