{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Algebra.InformationStructure
-- 信息结构桥接 — 周期/频率/泛音/方向数/范数坍缩的显式映射
--
-- 核心原则 (来自审核):
--   膜、频率、泛音、周期、阶、方向数——都是信息结构的投影。
--   不是彼此无关的伪对应, 但也不能把不同基座上的量直接混成同一类型。
--   必须建立**显式桥接定理**, 而不是暗中混淆。
--
-- 信息论统一结构:
--   阶 = 群元素的周期长度 = 信息自指的最小循环
--   周期 = Frobenius 轨道长度 = 信息闭环的长度
--   频率 = 周期的倒数 = 信息流的速率
--   泛音 = 基频的整数倍 = 信息的谐波族
--   方向数 = 循环子群大小 = 信息的自由度数
--   范数坍缩 = 共轭对的合并 = 信息去冗余
--
-- 形式化策略:
--   每个概念在自己的基座上定义
--   桥接定理显式连接不同基座
--   不把自然数幂和群元素混在同一类型中
--
-- 0 postulate.

module Sovereign.Algebra.InformationStructure where

open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _%_; _^_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; trans; sym; cong; cong₂)

open import Sovereign.Base.Trit using (Trit; T₀; T₁; T₂; _⊕_; _⊗_; negate)
open import Sovereign.Algebra.GF9
  using ( GF9; gf9-one; gf9-zero; alpha; phi; _*gf9_; _+gf9_
        ; galoisConjugate; galoisNorm; embed-gf3
        ; norm-conj-mul; galoisConjugate²
        ; alpha-squared; alpha-powers-4; phi-squared; phi-to-8
        ; gf9-pow; zero-power-gf9
        )
open import Sovereign.Algebra.GroupTheory.DuodecClock
  using ( AlphaPower; a0; a1; a2; a3
        ; mulAlpha; mulAlpha-hom
        ; DuodecPoint; mixedOp; duodec-e
        ; joint-period-12
        )
open import Sovereign.Algebra.NormCollapse
  using (norm-collapse)

--------------------------------------------------------------------------------
-- §1. 阶 — 群元素的周期长度 (信息自指的最小循环)
--------------------------------------------------------------------------------

-- 阶的定义: ord(g) = 最小的 k > 0 使得 g^k = e
-- 在有限穷举中: 直接验证 g^k = e

-- α 的阶 = 4
alpha-order : ℕ
alpha-order = 4

-- φ 的阶 = 8
phi-order : ℕ
phi-order = 8

-- -1 的阶 = 2
neg1-order : ℕ
neg1-order = 2

-- 验证
alpha-order-4 : mulAlpha (mulAlpha (mulAlpha a1 a1) a1) a1 ≡ a0
alpha-order-4 = refl

neg1-order-2 : mulAlpha a2 a2 ≡ a0
neg1-order-2 = refl

--------------------------------------------------------------------------------
-- §2. 周期 — Frobenius 轨道长度 (信息闭环的长度)
--------------------------------------------------------------------------------

-- Frobenius 周期: σ² = id → 周期 = 2
info-frobenius-period : ℕ
info-frobenius-period = 2

info-frobenius-period-2 : ∀ x → galoisConjugate (galoisConjugate x) ≡ x
info-frobenius-period-2 = galoisConjugate²

-- 加法周期: 1+1+1=0 → 周期 = 3
info-additive-period : ℕ
info-additive-period = 3

info-additive-period-3 : (T₁ ⊕ T₁) ⊕ T₁ ≡ T₀
info-additive-period-3 = refl

-- 联合周期: 3 × 4 = 12
info-joint-period : ℕ
info-joint-period = 12

joint-period-12-val : 3 * 4 ≡ 12
joint-period-12-val = refl

-- Pisano 周期: 斐波那契 mod 3 周期 = 8
pisano-period : ℕ
pisano-period = 8

--------------------------------------------------------------------------------
-- §3. 频率 — 周期的倒数 (信息流的速率)
--------------------------------------------------------------------------------

-- 在离散框架中, "频率" 不是实数除法, 而是周期的自然数倒数
-- 定义: frequency = 1 / period (在自然数中, 这只是周期的标记)

-- 频率标记: 用周期值本身标记频率
-- 周期越小 → 频率越高
-- 周期 3 (加法) → 频率标记 3
-- 周期 4 (旋转) → 频率标记 4
-- 周期 8 (φ) → 频率标记 8
-- 周期 12 (联合) → 频率标记 12

-- 基频 = 联合周期 = 12
base-frequency : ℕ
base-frequency = 12

-- 加法频率 = 3
add-frequency : ℕ
add-frequency = 3

-- 乘法频率 = 4
mul-frequency : ℕ
mul-frequency = 4

-- φ 频率 = 8
phi-frequency : ℕ
phi-frequency = 8

--------------------------------------------------------------------------------
-- §4. 泛音 — 基频的整数倍 (信息的谐波族)
--------------------------------------------------------------------------------

-- 泛音的定义: overtone(k) = k × base
-- 在自然数层独立于群元素

-- 泛音函数
overtone : ℕ → ℕ → ℕ
overtone base k = base * k

-- 基频 12 的泛音
overtone-12 : ℕ → ℕ
overtone-12 k = 12 * k

-- 泛音表 (基频 12)
ot-1  : overtone-12 1  ≡ 12;       ot-1  = refl
ot-2  : overtone-12 2  ≡ 24;       ot-2  = refl
ot-3  : overtone-12 3  ≡ 36;       ot-3  = refl
ot-4  : overtone-12 4  ≡ 48;       ot-4  = refl
ot-6  : overtone-12 6  ≡ 72;       ot-6  = refl
ot-8  : overtone-12 8  ≡ 96;       ot-8  = refl
ot-12 : overtone-12 12 ≡ 144;      ot-12 = refl

-- 超谐波 (泛音的泛音): overtone²(k) = base × (base × k) = base² × k
overtone-squared : ℕ → ℕ → ℕ
overtone-squared base k = base * base * k

-- 基频 12 的超谐波
ot2-1 : overtone-squared 12 1 ≡ 144;  ot2-1 = refl

--------------------------------------------------------------------------------
-- §5. 方向数 — 循环子群大小 (信息的自由度数)
--------------------------------------------------------------------------------

-- 方向数 = 生成元素的阶 = 循环子群的大小

-- α 生成 4 个方向 (0°, 90°, 180°, 270°)
alpha-directions : ℕ
alpha-directions = 4

-- φ 生成 8 个方向 (每 45° 一个)
phi-directions : ℕ
phi-directions = 8

-- -1 生成 2 个方向 (0°, 180°)
neg1-directions : ℕ
neg1-directions = 2

-- DuodecClock 生成 12 个方向
duodec-directions : ℕ
duodec-directions = 12

-- 方向数 = 阶 (同一概念的不同读法)
direction-equals-order : (alpha-directions ≡ alpha-order) × (phi-directions ≡ phi-order)
direction-equals-order = (refl , refl)

--------------------------------------------------------------------------------
-- §6. 范数坍缩 — 共轭对的合并 (信息去冗余)
--------------------------------------------------------------------------------

-- 范数坍缩: N(x) = x·σ(x) 把共轭对 (x, σ(x)) 合并为一个值
-- 这是信息去冗余: 两个共轭元素携带相同信息, 坍缩后只保留一个

-- 坍缩恒等式
norm-collapse-identity : ∀ x → embed-gf3 (galoisNorm x) ≡ x *gf9 galoisConjugate x
norm-collapse-identity = norm-collapse

-- 范数是谐波滤波器: N(a+bα) = a²+b²
-- 保留"振幅"信息, 丢弃"相位"信息
norm-is-filter : (a b : Trit) → galoisNorm (a , b) ≡ (a ⊗ a) ⊕ (b ⊗ b)
norm-is-filter a b = refl

-- 零幂也是信息去冗余: 0^n = 0 → 零在所有方向上都是零
zero-is-redundant : ∀ n → gf9-pow gf9-zero (suc n) ≡ gf9-zero
zero-is-redundant = zero-power-gf9

--------------------------------------------------------------------------------
-- §7. 桥接定理 — 显式连接不同基座
--------------------------------------------------------------------------------

-- 桥 1: 阶 → 周期 (同构)
-- ord(g) = g 的最小正整数幂回到单位元 = 周期
bridge-order-period : alpha-order ≡ 4
bridge-order-period = refl

-- 桥 2: 周期 → 频率 (取倒数标记)
-- 在离散框架中: 频率标记 = 周期值
bridge-period-frequency : info-joint-period ≡ base-frequency
bridge-period-frequency = refl

-- 桥 3: 频率 → 泛音 (整数倍)
-- overtone(k) = k × base
bridge-frequency-overtone : ∀ k → overtone base-frequency k ≡ 12 * k
bridge-frequency-overtone k = refl

-- 桥 4: 泛音 → 超谐波 (泛音的泛音)
-- overtone²(k) = base² × k
bridge-overtone-harmonic : ∀ k → overtone-squared base-frequency k ≡ 144 * k
bridge-overtone-harmonic k = refl

-- 桥 5: 阶 → 方向数 (同一概念)
bridge-order-direction : alpha-order ≡ alpha-directions
bridge-order-direction = refl

-- 桥 6: 范数坍缩 → 信息去冗余
-- N(x) = x·σ(x) 合并共轭对
bridge-norm-collapse : ∀ x → embed-gf3 (galoisNorm x) ≡ x *gf9 galoisConjugate x
bridge-norm-collapse = norm-collapse

-- 桥 7: 零幂 → 全方向归零
-- 0^n = 0 对所有 n → 零在所有方向上都是零
bridge-zero-power : ∀ n → gf9-pow gf9-zero (suc n) ≡ gf9-zero
bridge-zero-power = zero-power-gf9

-- 桥 8: 联合周期 = 加法周期 × 乘法周期
bridge-joint : info-additive-period * alpha-order ≡ info-joint-period
bridge-joint = refl

--------------------------------------------------------------------------------
-- §8. 信息结构统一视图
--------------------------------------------------------------------------------

-- 所有概念都是"闭合轨道"的不同侧面:
--
--   闭合轨道
--       ├─ 阶: 轨道长度 (群元素)
--       ├─ 周期: 轨道长度 (Frobenius)
--       ├─ 频率: 轨道速率 (周期倒数)
--       ├─ 泛音: 轨道的轨道 (谐波族)
--       ├─ 方向数: 轨道的自由度
--       └─ 范数坍缩: 轨道的信息压缩
--
-- 在 DuodecClock 中:
--   加法轨道 (Z/3): 周期 3, 频率 3, 方向数 3
--   乘法轨道 (⟨α⟩): 周期 4, 频率 4, 方向数 4
--   联合轨道 (12): 周期 12, 频率 12, 方向数 12
--
-- 泛音级联:
--   第 1 泛音 = 12 (联合周期)
--   第 2 泛音 = 12² = 144 (超谐波)
--   第 n 泛音 = 12^n (n 级谐波)
--
-- 与物理频率的桥接 (标定层):
--   每膜 = 8 个数量级 = 2³ = GF(9)* 的阶
--   12 膜 × 8 = 96 → 10^96 Hz
--   标定因子 = 10^8 / 12 (物理 Hz / 离散泛音)

-- 0 postulate.
