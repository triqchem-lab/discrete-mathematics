{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Format.CRTMeasurement
-- CRT 的中国原始含义："周期丈量"，不是西方片面的同余代数
--
-- CRT.agda 处理 POW2=2¹⁶, POW3=3¹¹（互质，标准 CRT 代数同构）
-- CRTMeasurement.agda 处理 144/46（gcd=2，物理周期丈量）
-- 两者互补：CRT.agda 是代数同构，CRTMeasurement.agda 是物理丈量
--
-- 核心洞见：
--   144 和 46 是丈量尺，不是模数
--   gcd(144,46) = 2 不是代数障碍，是双振子拍频的数学签名
--   FULL_TOUR = 144×46 = 6624（直积），不是 LCM(144,46) = 3312
--   直积保留双残余的完整信息，LCM 折叠相位丢失信息
--   M₄ 幻方本征谱正交性替代 gcd=1 的互质条件

module Sovereign.Format.CRTMeasurement where

open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _%_; _/_; _∸_; _^_; _<_)
open import Data.Nat.Properties
  using (*-comm; *-assoc; +-identityʳ; *-identityʳ; *-zeroʳ)
open import Data.Nat.DivMod
  using (%-distribˡ-+; %-distribˡ-*; m%n%n≡m%n; m≡m%n+[m/n]*n)
open import Data.Product using (_×_; _,_; Σ; proj₁; proj₂)
open import Data.Vec using (Vec; []; _∷_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; cong₂; sym; trans; module ≡-Reasoning)
open import Relation.Nullary using (¬_)

-- 复用已有主权常量
open import Sovereign.Structology.Winding
  using (PolarWinding; ToroidalWinding)
open import Sovereign.Structology.MagicSquare144
  using (FULL_TOUR; fullTourCorrect)
open import Sovereign.Base.Invariants
  using (CHERN_NUMBER)
open import Sovereign.Format.CRT
  using (POW2; POW3; M; crtProject)

--------------------------------------------------------------------------------
-- §1 丈量尺定义 (Ruler Definitions)
--
-- 144 和 46 是丈量尺，不是模数：
--   144 = 极向缠绕（I_h(120) + Merkaba(24)）
--   46  = 环向缠绕（C₆₀ 振动模 I_h 不可约分解）
--------------------------------------------------------------------------------

POLAR-RULER : ℕ
POLAR-RULER = 144

TOROIDAL-RULER : ℕ
TOROIDAL-RULER = 46

-- 与 Winding 模块的一致性
polar-ruler≡winding : POLAR-RULER ≡ PolarWinding
polar-ruler≡winding = refl

toroidal-ruler≡winding : TOROIDAL-RULER ≡ ToroidalWinding
toroidal-ruler≡winding = refl

-- 144 = I_h(120) + Merkaba(24)（正十二面体 + 梅尔卡巴）
polar-decomposition : POLAR-RULER ≡ 120 + 24
polar-decomposition = refl

--------------------------------------------------------------------------------
-- §2 公约因子与 Euclidean 算法 (GCD & Beat Frequency Signature)
--
-- gcd(144,46) = 2 不是代数障碍，是双振子拍频的数学签名
-- 用 Euclidean 算法穷举证明（每步 refl）
--------------------------------------------------------------------------------

GCD-144-46 : ℕ
GCD-144-46 = 2

-- 2 整除 144 和 46（公约因子存在性）
2∣144 : 144 % 2 ≡ 0
2∣144 = refl

2∣46 : 46 % 2 ≡ 0
2∣46 = refl

-- Euclidean 算法四步：gcd(144, 46) = 2
-- 144 = 3 × 46 + 6
euclid-step1 : 144 % 46 ≡ 6
euclid-step1 = refl

-- 46 = 7 × 6 + 4
euclid-step2 : 46 % 6 ≡ 4
euclid-step2 = refl

-- 6 = 1 × 4 + 2
euclid-step3 : 6 % 4 ≡ 2
euclid-step3 = refl

-- 4 = 2 × 2 + 0（终止）
euclid-step4 : 4 % 2 ≡ 0
euclid-step4 = refl

-- 约化对：144/2 = 72, 46/2 = 23
reduced-polar : ℕ
reduced-polar = 72

reduced-toroidal : ℕ
reduced-toroidal = 23

reduced-polar-correct : 144 / 2 ≡ reduced-polar
reduced-polar-correct = refl

reduced-toroidal-correct : 46 / 2 ≡ reduced-toroidal
reduced-toroidal-correct = refl

-- 约化对 (72, 23) 互素：Euclidean 算法穷举
-- 72 = 3 × 23 + 3
coprime-step1 : 72 % 23 ≡ 3
coprime-step1 = refl

-- 23 = 7 × 3 + 2
coprime-step2 : 23 % 3 ≡ 2
coprime-step2 = refl

-- 3 = 1 × 2 + 1
coprime-step3 : 3 % 2 ≡ 1
coprime-step3 = refl

-- 2 = 2 × 1 + 0（终止，gcd = 1）
coprime-step4 : 2 % 1 ≡ 0
coprime-step4 = refl

-- Bézout 系数：8 × 72 − 25 × 23 = 1
-- 即 8 × 72 ≡ 1 (mod 23)
bezout-72 : (8 * 72) % 23 ≡ 1
bezout-72 = refl

-- 即 47 × 23 ≡ 1 (mod 72)  [47 = 72 ∸ 25]
bezout-23 : (47 * 23) % 72 ≡ 1
bezout-23 = refl

--------------------------------------------------------------------------------
-- §3 直积 vs LCM (Direct Product vs LCM)
--
-- FULL_TOUR = 144 × 46 = 6624（直积，保留完整信息）
-- LCM(144,46) = 3312（折叠相位，丢失信息）
-- 直积 = 拍频 × 拍频周期 = 2 × 3312
--------------------------------------------------------------------------------

FULL-TOUR : ℕ
FULL-TOUR = 144 * 46

LCM-144-46 : ℕ
LCM-144-46 = 3312

full-tour-value : FULL-TOUR ≡ 6624
full-tour-value = refl

-- 与 MagicSquare144 的 FULL_TOUR 一致
full-tour≡magic : FULL-TOUR ≡ FULL_TOUR
full-tour≡magic = refl

-- 核心定理：直积 = 拍频 × 拍频周期
full-tour-is-2-lcm : FULL-TOUR ≡ 2 * LCM-144-46
full-tour-is-2-lcm = refl

-- LCM = 144 × 23（约化环向尺）
lcm-formula : LCM-144-46 ≡ 144 * 23
lcm-formula = refl

-- 信息含量比：直积 6624 态 / LCM 3312 态 = 2
-- 直积保留完整双残余信息，LCM 折叠丢失一半
info-ratio : FULL-TOUR / LCM-144-46 ≡ 2
info-ratio = refl

--------------------------------------------------------------------------------
-- §4 丈量投影 (Measurement Projection)
--
-- 不是 x mod 144 和 x mod 46（同余代数）
-- 而是 x 在 144 尺上的余数和 x 在 46 尺上的余数（物理丈量）
--------------------------------------------------------------------------------

measure : ℕ → ℕ × ℕ
measure x = x % POLAR-RULER , x % TOROIDAL-RULER

-- 丈量示例
measure-0 : measure 0 ≡ (0 , 0)
measure-0 = refl

measure-1 : measure 1 ≡ (1 , 1)
measure-1 = refl

measure-46 : measure 46 ≡ (46 , 0)
measure-46 = refl

measure-144 : measure 144 ≡ (0 , 6)
measure-144 = refl

-- 拍频周期处归零
measure-at-lcm : measure LCM-144-46 ≡ (0 , 0)
measure-at-lcm = refl

-- 完整周期处也归零
measure-at-full-tour : measure FULL-TOUR ≡ (0 , 0)
measure-at-full-tour = refl

-- 半周期偏移：3312 + 1 的丈量
measure-half-plus-1 : measure (LCM-144-46 + 1) ≡ (1 , 1)
measure-half-plus-1 = refl

--------------------------------------------------------------------------------
-- §5 奇偶一致性定理 (Parity Consistency Theorem)
--
-- 因为 2 | 144 且 2 | 46，丈量结果的奇偶性必然相同
-- 这是 gcd=2 的物理表现：两把尺每 2 个单位产生一次干涉
-- 可解条件：a ≡ b (mod 2)
--------------------------------------------------------------------------------

-- 辅助引理：(q × 144) % 2 ≡ 0（因为 144 % 2 ≡ 0）
private
  q*144%2≡0 : ∀ q → (q * 144) % 2 ≡ 0
  q*144%2≡0 q = begin
    (q * 144) % 2
      ≡⟨ %-distribˡ-* q 144 2 ⟩
    (q % 2 * (144 % 2)) % 2
      ≡⟨ cong (λ r → (q % 2 * r) % 2) 2∣144 ⟩
    (q % 2 * 0) % 2
      ≡⟨ cong (_% 2) (*-zeroʳ (q % 2)) ⟩
    0 % 2
      ≡⟨⟩
    0 ∎
    where open ≡-Reasoning

  q*46%2≡0 : ∀ q → (q * 46) % 2 ≡ 0
  q*46%2≡0 q = begin
    (q * 46) % 2
      ≡⟨ %-distribˡ-* q 46 2 ⟩
    (q % 2 * (46 % 2)) % 2
      ≡⟨ cong (λ r → (q % 2 * r) % 2) 2∣46 ⟩
    (q % 2 * 0) % 2
      ≡⟨ cong (_% 2) (*-zeroʳ (q % 2)) ⟩
    0 % 2
      ≡⟨⟩
    0 ∎
    where open ≡-Reasoning

-- 核心引理：x % 144 与 x 同奇偶
%2-via-%144 : ∀ x → (x % 144) % 2 ≡ x % 2
%2-via-%144 x = sym (begin
  x % 2
    ≡⟨ cong (_% 2) (m≡m%n+[m/n]*n x 144) ⟩
  (x % 144 + (x / 144) * 144) % 2
    ≡⟨ %-distribˡ-+ (x % 144) ((x / 144) * 144) 2 ⟩
  ((x % 144) % 2 + ((x / 144) * 144) % 2) % 2
    ≡⟨ cong (λ r → ((x % 144) % 2 + r) % 2) (q*144%2≡0 (x / 144)) ⟩
  ((x % 144) % 2 + 0) % 2
    ≡⟨ cong (_% 2) (+-identityʳ ((x % 144) % 2)) ⟩
  (x % 144) % 2 % 2
    ≡⟨ m%n%n≡m%n (x % 144) 2 ⟩
  (x % 144) % 2 ∎)
  where open ≡-Reasoning

-- 核心引理：x % 46 与 x 同奇偶
%2-via-%46 : ∀ x → (x % 46) % 2 ≡ x % 2
%2-via-%46 x = sym (begin
  x % 2
    ≡⟨ cong (_% 2) (m≡m%n+[m/n]*n x 46) ⟩
  (x % 46 + (x / 46) * 46) % 2
    ≡⟨ %-distribˡ-+ (x % 46) ((x / 46) * 46) 2 ⟩
  ((x % 46) % 2 + ((x / 46) * 46) % 2) % 2
    ≡⟨ cong (λ r → ((x % 46) % 2 + r) % 2) (q*46%2≡0 (x / 46)) ⟩
  ((x % 46) % 2 + 0) % 2
    ≡⟨ cong (_% 2) (+-identityʳ ((x % 46) % 2)) ⟩
  (x % 46) % 2 % 2
    ≡⟨ m%n%n≡m%n (x % 46) 2 ⟩
  (x % 46) % 2 ∎)
  where open ≡-Reasoning

-- 奇偶一致性定理：丈量结果的两分量必然同奇偶
-- 这是 gcd(144,46)=2 的物理表现
measure-parity : ∀ x → (x % POLAR-RULER) % 2 ≡ (x % TOROIDAL-RULER) % 2
measure-parity x = trans (%2-via-%144 x) (sym (%2-via-%46 x))

--------------------------------------------------------------------------------
-- §6 可重构性 (Reconstructibility)
--
-- 因为 gcd=2，不是所有 (a,b) 都有解
-- 可解条件：a ≡ b (mod 2)（奇偶一致）
-- 解在 mod LCM(144,46) = 3312 下唯一
--------------------------------------------------------------------------------

-- 可重构谓词
Reconstructible : ℕ → ℕ → Set
Reconstructible a b = Σ ℕ (λ x → x % POLAR-RULER ≡ a × x % TOROIDAL-RULER ≡ b)

-- 具体可重构实例（奇偶一致的 (a,b) 对）
reconstruct-0-0 : Reconstructible 0 0
reconstruct-0-0 = 0 , refl , refl

reconstruct-1-1 : Reconstructible 1 1
reconstruct-1-1 = 1 , refl , refl

reconstruct-2-2 : Reconstructible 2 2
reconstruct-2-2 = 2 , refl , refl

reconstruct-46-0 : Reconstructible 46 0
reconstruct-46-0 = 46 , refl , refl

-- 143 % 144 = 143, 143 % 46 = 5（同奇：143 奇，5 奇）
reconstruct-143-5 : Reconstructible 143 5
reconstruct-143-5 = 143 , refl , refl

-- 3311 % 144 = 143, 3311 % 46 = 45（同奇：143 奇，45 奇）
-- 需要 Bézout 重构：x = 143 + 144 × 22 = 3311
reconstruct-143-45 : Reconstructible 143 45
reconstruct-143-45 = 3311 , refl , refl

-- 不可重构实例的否定：奇偶不一致
-- (0, 1) 不可重构：0 是偶数，1 是奇数
-- 证明：如果 x % 144 ≡ 0 且 x % 46 ≡ 1，
--       则 0 ≡ (x % 144) % 2 ≡ (x % 46) % 2 ≡ 1，矛盾
private
  0≢1 : ¬ (0 ≡ 1)
  0≢1 ()

  1≢0 : ¬ (1 ≡ 0)
  1≢0 ()

¬reconstruct-0-1 : ¬ Reconstructible 0 1
¬reconstruct-0-1 (x , p , q) =
  0≢1 (trans (sym (cong (_% 2) p)) (trans (measure-parity x) (cong (_% 2) q)))

-- (1, 0) 同理不可重构
¬reconstruct-1-0 : ¬ Reconstructible 1 0
¬reconstruct-1-0 (x , p , q) =
  1≢0 (trans (sym (cong (_% 2) p)) (trans (measure-parity x) (cong (_% 2) q)))

--------------------------------------------------------------------------------
-- §7 拍频干涉 (Beat Frequency Interference)
--
-- 拍频 = gcd(144,46) = 2
-- 两把尺每 2 个单位产生一次干涉
-- 拍频周期 = LCM(144,46) = 3312
-- 完整周期 = 144×46 = 6624 = 2 × 拍频周期
--------------------------------------------------------------------------------

BEAT-FREQUENCY : ℕ
BEAT-FREQUENCY = 2

beat-is-gcd : BEAT-FREQUENCY ≡ GCD-144-46
beat-is-gcd = refl

-- 深层联系：拍频 = 陈数
beat-is-chern : BEAT-FREQUENCY ≡ CHERN_NUMBER
beat-is-chern = refl

-- 拍频周期 = LCM
BEAT-PERIOD : ℕ
BEAT-PERIOD = LCM-144-46

beat-period-value : BEAT-PERIOD ≡ 3312
beat-period-value = refl

-- 完整周期 = 拍频 × 拍频周期
full-tour-beat : FULL-TOUR ≡ BEAT-FREQUENCY * BEAT-PERIOD
full-tour-beat = refl

--------------------------------------------------------------------------------
-- §8 M₄ 幻方正交 (Magic Square Orthogonality)
--
-- M₄ 幻方本征谱 {34, 0, ±16} 正交
-- 正交性替代 gcd=1 的互质条件
-- 将 1D 巡游序列投影为 2D（极向×环向）频率域
--------------------------------------------------------------------------------

data M4Eigenvalue : Set where
  e34  : M4Eigenvalue   -- 幻和（4×(4²+1)/2 = 34）
  e0   : M4Eigenvalue   -- 零模
  e16⁺ : M4Eigenvalue   -- 正频率
  e16⁻ : M4Eigenvalue   -- 负频率

m4eigenvalue→ℕ : M4Eigenvalue → ℕ
m4eigenvalue→ℕ e34  = 34
m4eigenvalue→ℕ e0   = 0
m4eigenvalue→ℕ e16⁺ = 16
m4eigenvalue→ℕ e16⁻ = 16

-- 本征谱（简化为 ℕ 表示，丢失 ±符号）
M4-SPECTRUM : Vec ℕ 4
M4-SPECTRUM = 34 ∷ 0 ∷ 16 ∷ 16 ∷ []

-- 幻和 = 4 × (4² + 1) / 2 = 34
magic-constant : (4 * (4 * 4 + 1)) / 2 ≡ 34
magic-constant = refl

-- 正交性：非零本征值互异
eigenvalue-distinct : ¬ (34 ≡ 16)
eigenvalue-distinct = λ ()

-- 零模正交性：0 与任何本征值正交（乘积为 0）
zero-orthogonal-34 : 0 * 34 ≡ 0
zero-orthogonal-34 = refl

zero-orthogonal-16 : 0 * 16 ≡ 0
zero-orthogonal-16 = refl

-- 本征值与拍频的关系
-- 34 = 2 × 17（拍频 × 素数）
eigenvalue-34-beat : 34 ≡ 2 * 17
eigenvalue-34-beat = refl

-- 16 = 2⁴（拍频的幂次结构）
eigenvalue-16-power : 16 ≡ 2 ^ 4
eigenvalue-16-power = refl

--------------------------------------------------------------------------------
-- §9 与 Z/12Z 的连接 (Connection to Z/12Z)
--
-- 十二律是底层生成元：
--   144 = 12²（十二律的平方）
--   46  = 12 × 4 ∸ 2（十二律×四象 − 拍频）
--   6624 = 12² × 46
--------------------------------------------------------------------------------

-- 144 = 12 × 12（十二律的平方）
polar-is-12-sq : POLAR-RULER ≡ 12 * 12
polar-is-12-sq = refl

-- 46 = 12 × 4 ∸ 2（十二律×四象 − 拍频）
toroidal-relation : TOROIDAL-RULER ≡ 12 * 4 ∸ 2
toroidal-relation = refl

-- 6624 = 12 × 552
full-tour-12 : FULL-TOUR ≡ 12 * 552
full-tour-12 = refl

-- 552 = 12 × 46
inner-552 : 552 ≡ 12 * 46
inner-552 = refl

-- 6624 = 12 × 12 × 46 = 12² × 46
full-tour-12-12-46 : FULL-TOUR ≡ 12 * 12 * 46
full-tour-12-12-46 = refl

-- 3312 = 12 × 276
lcm-12 : LCM-144-46 ≡ 12 * 276
lcm-12 = refl

-- 276 = 12 × 23（约化环向尺 × 十二律）
inner-276 : 276 ≡ 12 * 23
inner-276 = refl

-- 3312 = 144 × 23 = 12² × 23
lcm-12-sq-23 : LCM-144-46 ≡ 12 * 12 * 23
lcm-12-sq-23 = refl

--------------------------------------------------------------------------------
-- §10 Christoffel 螺旋连接 (Christoffel Spiral Connection)
--
-- Christoffel 螺旋 {1,2,4,8,7,5}：2 的幂次 mod 9
-- 周期 6，与 FULL_TOUR 的整除关系
--------------------------------------------------------------------------------

CHRISTOFFEL-PERIOD : ℕ
CHRISTOFFEL-PERIOD = 6

christoffel-period-value : CHRISTOFFEL-PERIOD ≡ 6
christoffel-period-value = refl

-- 6624 / 6 = 1104 个完整螺旋周期
christoffel-cycles : FULL-TOUR / CHRISTOFFEL-PERIOD ≡ 1104
christoffel-cycles = refl

-- 3312 / 6 = 552 个拍频周期内的螺旋周期
christoffel-beat-cycles : LCM-144-46 / CHRISTOFFEL-PERIOD ≡ 552
christoffel-beat-cycles = refl

-- 1104 = 2 × 552（直积包含两倍拍频周期的螺旋）
christoffel-double : 1104 ≡ 2 * 552
christoffel-double = refl

-- Christoffel 螺旋元素：2 的幂次 mod 9
christoffel-1 : (2 ^ 0) % 9 ≡ 1
christoffel-1 = refl

christoffel-2 : (2 ^ 1) % 9 ≡ 2
christoffel-2 = refl

christoffel-4 : (2 ^ 2) % 9 ≡ 4
christoffel-4 = refl

christoffel-8 : (2 ^ 3) % 9 ≡ 8
christoffel-8 = refl

christoffel-7 : (2 ^ 4) % 9 ≡ 7
christoffel-7 = refl

christoffel-5 : (2 ^ 5) % 9 ≡ 5
christoffel-5 = refl

-- 周期闭合：2⁶ ≡ 1 (mod 9)
christoffel-closure : (2 ^ 6) % 9 ≡ 1
christoffel-closure = refl

--------------------------------------------------------------------------------
-- §11 与标准 CRT 的关系 (Relation to Standard CRT)
--
-- CRT.agda：POW2=2¹⁶, POW3=3¹¹, gcd=1 → 代数同构
-- CRTMeasurement：144/46, gcd=2 → 物理丈量
-- 两者互补，不是替代关系
--------------------------------------------------------------------------------

-- 标准 CRT 的模数
STANDARD-CRT-MOD1 : ℕ
STANDARD-CRT-MOD1 = POW2  -- 65536 = 2¹⁶

STANDARD-CRT-MOD2 : ℕ
STANDARD-CRT-MOD2 = POW3  -- 177147 = 3¹¹

-- 标准 CRT 的模数互质（gcd = 1）
-- 验证：2¹⁶ % 3 ≠ 0（2¹⁶ 不被 3 整除）
standard-crt-coprime-evidence : POW2 % 3 ≡ 1
standard-crt-coprime-evidence = refl

-- 丈量尺的 gcd = 2 ≠ 1（不互质）
measurement-gcd-nontrivial : GCD-144-46 ≡ 2
measurement-gcd-nontrivial = refl

-- 标准 CRT 的乘积 M = 2¹⁶ × 3¹¹ = 11609505792
-- 丈量尺的直积 FULL-TOUR = 144 × 46 = 6624
-- M / FULL-TOUR = 1752642（主权 LCM 包含多个完整巡游）
sovereign-lcm-contains-tours : M / FULL-TOUR ≡ 1752642
sovereign-lcm-contains-tours = refl

-- 标准 CRT 投影 vs 丈量投影
-- crtProject : ℕ → ℕ × ℕ  (POW2, POW3 互质 → 代数同构)
-- measure    : ℕ → ℕ × ℕ  (144, 46 gcd=2 → 物理丈量)
-- 两者结构相同（都是取余数对），但数学含义不同

-- 丈量投影在标准 CRT 投影下的像
-- 144 在 (POW2, POW3) 下的 CRT 投影
polar-crt-projection : crtProject POLAR-RULER ≡ (144 , 144)
polar-crt-projection = refl

-- 46 在 (POW2, POW3) 下的 CRT 投影
toroidal-crt-projection : crtProject TOROIDAL-RULER ≡ (46 , 46)
toroidal-crt-projection = refl
