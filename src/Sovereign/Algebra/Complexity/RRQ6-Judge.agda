{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Algebra.Complexity.RRQ6-Judge
-- GF(3) monic 六次不可约判定器（PvsNP 路线图批三 RRQ6 判定件；密度阶梯 N=6 阶）
--
-- 衔接（渐近密度阶梯，逐阶落地；证据链 3/9 → 8/27 → 18/81 → 116/729 四点）:
--   • N=2,3: RRProperty §2/§4（9 中 3 个、27 中 8 个，refl 枚举已闭合）
--   • N=4:   RRQuartic（81 中 18 = (81−9)/4）
--   • N=6:   本件判定器 + RRQ6-Count 精确计数 729 中 116 = (729−27−9+3)/6
--
-- 判据（已裁决，§1 次数簿记闭合）: monic 六次 f 在 GF(3)[x] 可约 ⟺
-- f 有 deg∈{1,2,3} 因子。次数簿记: f = gh 非平凡 ⟹ deg g + deg h = 6,
-- 两侧 ≥ 1 ⟹ 合法形态仅 (1,5)/(2,4)/(3,3)/(4,2)/(5,1) 五种——左因子
-- deg 1/2/3 直接给出结论, deg 4 必配 deg 2、deg 5 必配 deg 1（和为 6 钉死,
-- 右因子给出结论）。反向构造性显见: 因子本身即分解 witness, 无需引理。
--
-- 由此判定器三支（GF(3) 全点代入 + 3 个不可约二次型 + 8 个不可约三次型
-- 整除检验）:
--   • RRQ6-noRootQ6:      三点代入全非零 ⟺ 无一次因子（§2）
--   • RRQ6-noQuadFactor:  x²+1、x²+x+2、x²+2x+2（RRProperty §2 名单）除法
--     核对余式非零 ⟺ 无二次因子（§3）
--   • RRQ6-noCubicFactor: RRProperty §4c 已计数的 8 个不可约三次型除法核对
--     ⟺ 无三次因子（§4）——注释锚定复用: 名单是 refl 引理非机器可读数据,
--     本件按系数重列数据（RRQ6-cubicForms）
-- （二次/三次因子若可约则 f 有根, 已被第一支排除; 三次支不可省的教学例:
--   x⁶+2x²+2 无根 ∧ 无二次因子 ∧ 有三次因子, §5。）
--
-- 数学核对（Python 实证先行, probes/rrq6_count.py 复跑三路一致）:
-- 判定器法 116 = 暴力全分解法 116 = Möbius (729−27−9+3)/6, 九块 (a₅,a₄)
-- 计数 15,11,12,13,13,13,13,13,13 与计数件（RRQ6-Count）一致。
--
-- 层向纪律: 同 RRQuartic——Sovereign.Algebra 禁止 import
-- Sovereign.Application; GF(3) 常数算术复用 Base.Trit 的 ⊕/⊗（不建第三份
-- 算术块）; neg3/and2/zeroPair 微件复用 RRQuartic 顶层定义（import 复用,
-- 非第三份重建）。
--
-- 定名纪律: 全部新符号加 RRQ6- 前缀（建档前 grep 自检零撞名; 库内
-- Lang/W/addVec3/P2 撞名前科）。
--
-- 分级标注约定（同 RRProperty/RRQuartic）: 〔结构定义〕= 数据/定义;
-- 〔refl 枚举〕= 有限情形逐点 refl/荒谬模式; 〔立界注记〕= 深件边界,
-- 不设空壳签名。
--
-- 0 postulate / 0 hole。

module Sovereign.Algebra.Complexity.RRQ6-Judge where

open import Data.Nat using (ℕ; zero; suc; _+_; _≤_)
open import Data.Bool using (Bool; true; false; not)
open import Data.List using (List; []; _∷_)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

-- 引用边界（同层 Complexity 复用 + Base 层, 层向合规）:
open import Sovereign.Base.Trit using (Trit; T₀; T₁; T₂; _⊕_; _⊗_)
open import Sovereign.Algebra.Complexity.RRProperty using
  ( RR-noRootAt; RR-IsNatural; RR-classify; RR-nonnatural-nonuniversal )
open import Sovereign.Algebra.Complexity.RRQuartic using
  ( RRQ-neg3; RRQ-and2; RRQ-zeroPair )

--------------------------------------------------------------------------------
-- §1 判据等价性: 次数簿记引理〔refl/荒谬模式枚举; 判据已裁决〕
--
-- 非平凡两因子分解 (deg g, deg h) 满足两侧 ≥ 1 且和为 6, 合法形态五种:
-- (1,5)/(2,4)/(3,3)/(4,2)/(5,1)。左因子 deg∈{1,2,3} 直接给出结论; deg 4
-- 必配 deg 2、deg 5 必配 deg 1（和为 6 钉死）⟹ 右因子给出结论。即
-- 「可约 ⟹ ∃ 因子, deg ∈ {1,2,3}」。左因子分案 {0,1,2,3,4,5,恰6,≥7} ×
-- 右因子分案共 19 子句（m=zero 荒谬 1 + 合法 5 + 荒谬形态 13）, 0 hole。
-- （m ≥ 6 必须再分「恰 6」/「≥ 7」: 见下方子句处注释。）
--------------------------------------------------------------------------------

-- 〔结构定义〕因子判定的三种结局（deg ∈ {1,2,3} 的哪一档）
data RRQ6-FactorVerdict : Set where
  RRQ6-lin   : RRQ6-FactorVerdict  -- 有一次因子 ⟹ 有根
  RRQ6-quad  : RRQ6-FactorVerdict  -- 有二次因子（必为 RRProperty §2 三型之一）
  RRQ6-cubic : RRQ6-FactorVerdict  -- 有三次因子（必为 RRProperty §4c 八型之一）

RRQ6-degBook : (m n : ℕ) → 1 ≤ m → 1 ≤ n → m + n ≡ 6 → RRQ6-FactorVerdict
RRQ6-degBook zero n () _ _                                    -- 1 ≤ 0 荒谬
RRQ6-degBook (suc zero) n _ _ _ = RRQ6-lin                    -- (1,n): 一次因子
RRQ6-degBook (suc (suc zero)) n _ _ _ = RRQ6-quad             -- (2,n): 二次因子
RRQ6-degBook (suc (suc (suc zero))) zero _ _ ()               -- 3+0 = 3 ≠ 6
RRQ6-degBook (suc (suc (suc zero))) (suc zero) _ _ ()         -- 4 ≠ 6
RRQ6-degBook (suc (suc (suc zero))) (suc (suc zero)) _ _ ()   -- 5 ≠ 6
RRQ6-degBook (suc (suc (suc zero))) (suc (suc (suc zero))) _ _ _ = RRQ6-cubic        -- (3,3)
RRQ6-degBook (suc (suc (suc zero))) (suc (suc (suc (suc n)))) _ _ ()                 -- ≥ 7
RRQ6-degBook (suc (suc (suc (suc zero)))) zero _ () _         -- 1 ≤ 0 荒谬
RRQ6-degBook (suc (suc (suc (suc zero)))) (suc zero) _ _ ()   -- 5 ≠ 6
RRQ6-degBook (suc (suc (suc (suc zero)))) (suc (suc zero)) _ _ _ = RRQ6-quad         -- (4,2): 右因子 deg 2
RRQ6-degBook (suc (suc (suc (suc zero)))) (suc (suc (suc n))) _ _ ()                 -- ≥ 7
RRQ6-degBook (suc (suc (suc (suc (suc zero))))) zero _ () _   -- 1 ≤ 0 荒谬
RRQ6-degBook (suc (suc (suc (suc (suc zero))))) (suc zero) _ _ _ = RRQ6-lin          -- (5,1): 右因子 deg 1
RRQ6-degBook (suc (suc (suc (suc (suc zero))))) (suc (suc n)) _ _ ()                 -- ≥ 7
-- m ≥ 6 再分「恰 6」/「≥ 7」: 恰 6 时零侧归约彻底（zero + suc n = suc n）,
-- ≥ 7 时超额 1 个 suc 直接荒谬——suc⁶ m' + n 中 m' 中性, m' + n 卡死,
-- 不再细分则荒谬模式不成立（§1 首编译实证）。
RRQ6-degBook (suc (suc (suc (suc (suc (suc zero)))))) zero _ () _   -- 1 ≤ 0 荒谬
RRQ6-degBook (suc (suc (suc (suc (suc (suc zero)))))) (suc n) _ _ ()                 -- ≥ 7
RRQ6-degBook (suc (suc (suc (suc (suc (suc (suc m))))))) n _ _ ()                    -- ≥ 8

--------------------------------------------------------------------------------
-- §2 六次根检验〔本地重建; 同 RRQuartic §2 形态〕
--
-- monic 六次 x⁶ + a·x⁵ + b·x⁴ + c·x³ + d·x² + e·x + f（参数序 (a,b,c,d,e,f)
-- 从高到低, 与 RRQuartic (a,b,c,d) 同惯例; 即数学记号 a₅,…,a₀）。x⁶ 项的
-- 点值贡献显式保留——RRQuartic 头注记载的教训（漏计首项点值）: x=1 时
-- x⁶ 贡献 1, x=2 时 64 ≡ 1。⊕ 无 fixity 声明（非结合）, 全式显式括号化,
-- 书写方向 = 左嵌套。
--------------------------------------------------------------------------------

RRQ6-evalSextic : Trit → Trit → Trit → Trit → Trit → Trit → Trit → Trit
RRQ6-evalSextic a b c d e f0 x =
  (((((((((((x ⊗ x) ⊗ x) ⊗ x) ⊗ x) ⊗ x)
     ⊕ (((((a ⊗ x) ⊗ x) ⊗ x) ⊗ x) ⊗ x))
     ⊕ ((((b ⊗ x) ⊗ x) ⊗ x) ⊗ x))
     ⊕ (((c ⊗ x) ⊗ x) ⊗ x))
     ⊕ ((d ⊗ x) ⊗ x))
     ⊕ (e ⊗ x))
     ⊕ f0)

-- monic 六次无根判定器: GF(3) 全点（3 点）代入全非零〔复用 RR-noRootAt〕
RRQ6-noRootQ6 : Trit → Trit → Trit → Trit → Trit → Trit → Bool
RRQ6-noRootQ6 a b c d e f0 =
  RR-noRootAt (RRQ6-evalSextic a b c d e f0 T₀)
              (RRQ6-evalSextic a b c d e f0 T₁)
              (RRQ6-evalSextic a b c d e f0 T₂)

--------------------------------------------------------------------------------
-- §3 二次因子检验〔内联除法; 全 GF(3) 常数运算; 复用 RRQuartic 微件〕
--
-- f = x⁶+a·x⁵+b·x⁴+c·x³+d·x²+e·x+f₀ 除以 g = x²+g₁·x+g₀（monic）。商
-- x⁴+q₃x³+q₂x²+q₁x+q₀（deg4 四系数）, 余 r₁x+r₀, 系数逐位消去:
--   q₃ = a − g₁,            q₂ = b − q₃g₁ − g₀,
--   q₁ = c − q₃g₀ − q₂g₁,   q₀ = d − q₂g₀ − q₁g₁,
--   r₁ = e − q₁g₀ − q₀g₁,   r₀ = f₀ − q₀g₀
-- g 整除 f ⟺ r₁ = r₀ = T₀。减法 = ⊕ RRQ-neg3（RRQ-neg3 复用）。商的四个
-- q 系数中 q₃…q₁ 是后续 q₀/r 系数的输入, 全部保留。
-- 判据衔接: 二次因子若可约则 f 有根（§2 已排除）, 故只需查 RRProperty
-- §2 的 3 个不可约二次型（名单 import 复用, 与 RRQuartic §3 同型）。
--------------------------------------------------------------------------------

RRQ6-divRemQ6-quad : Trit → Trit → Trit → Trit → Trit → Trit → Trit → Trit → Trit × Trit
RRQ6-divRemQ6-quad a b c d e f0 g1 g0 = r1 , r0
  where
    q3 : Trit
    q3 = a ⊕ (RRQ-neg3 g1)
    q2 : Trit
    q2 = b ⊕ (RRQ-neg3 ((q3 ⊗ g1) ⊕ g0))
    q1 : Trit
    q1 = c ⊕ (RRQ-neg3 ((q3 ⊗ g0) ⊕ (q2 ⊗ g1)))
    q0 : Trit
    q0 = d ⊕ (RRQ-neg3 ((q2 ⊗ g0) ⊕ (q1 ⊗ g1)))
    r1 : Trit
    r1 = e ⊕ (RRQ-neg3 ((q1 ⊗ g0) ⊕ (q0 ⊗ g1)))
    r0 : Trit
    r0 = f0 ⊕ (RRQ-neg3 (q0 ⊗ g0))

-- 单型检验: g 不整除 f ⟺ f 无该二次因子〔复用 RRQ-zeroPair〕
RRQ6-noQuadBy : Trit → Trit → Trit → Trit → Trit → Trit → Trit → Trit → Bool
RRQ6-noQuadBy g1 g0 a b c d e f0 =
  not (RRQ-zeroPair (RRQ6-divRemQ6-quad a b c d e f0 g1 g0))

-- 无二次因子判定器: 对 3 个已知不可约二次型逐一通过
RRQ6-noQuadFactor : Trit → Trit → Trit → Trit → Trit → Trit → Bool
RRQ6-noQuadFactor a b c d e f0 =
  RRQ-and2 (RRQ6-noQuadBy T₀ T₁ a b c d e f0)   -- x²+1:    (g₁,g₀) = (T₀,T₁)
  (RRQ-and2 (RRQ6-noQuadBy T₁ T₂ a b c d e f0)  -- x²+x+2:  (g₁,g₀) = (T₁,T₂)
            (RRQ6-noQuadBy T₂ T₂ a b c d e f0)) -- x²+2x+2: (g₁,g₀) = (T₂,T₂)

--------------------------------------------------------------------------------
-- §4 三次因子检验〔内联除法; 名单注释锚定复用 RRProperty §4c〕
--
-- f 除以 g = x³+g₂·x²+g₁·x+g₀（monic）。商 x³+q₂x²+q₁x+q₀（deg3 三系数）,
-- 余 r₂x²+r₁x+r₀, 系数逐位消去（公式组已普查验证）:
--   q₂ = a − g₂,             q₁ = b − q₂g₂ − g₁,
--   q₀ = c − q₁g₂ − q₂g₁ − g₀,
--   r₂ = d − q₀g₂ − q₁g₁ − q₂g₀,
--   r₁ = e − q₀g₁ − q₁g₀,    r₀ = f₀ − q₀g₀
-- g 整除 f ⟺ r₂ = r₁ = r₀ = T₀。
-- 名单复用说明: RRProperty §4c 的 8 个不可约三次型是 refl 引理（注释
-- 锚定）非机器可读数据, 本件按系数重列数据 RRQ6-cubicForms, 8 型逐一
-- 对应 RRProperty §4c: (0,2,1)/(0,2,2)/(1,0,2)/(1,1,2)/(1,2,1)/(2,0,1)/
-- (2,1,1)/(2,2,2)。
--------------------------------------------------------------------------------

RRQ6-cubicForms : List (Trit × Trit × Trit)
RRQ6-cubicForms =
  (T₀ , T₂ , T₁) ∷ (T₀ , T₂ , T₂) ∷   -- x³+2x+1    x³+2x+2
  (T₁ , T₀ , T₂) ∷ (T₁ , T₁ , T₂) ∷   -- x³+x²+2    x³+x²+x+2
  (T₁ , T₂ , T₁) ∷ (T₂ , T₀ , T₁) ∷   -- x³+x²+2x+1 x³+2x²+1
  (T₂ , T₁ , T₁) ∷ (T₂ , T₂ , T₂) ∷ [] -- x³+2x²+x+1 x³+2x²+2x+2

RRQ6-divRemQ6-cubic : Trit → Trit → Trit → Trit → Trit → Trit → Trit → Trit → Trit → Trit × Trit × Trit
RRQ6-divRemQ6-cubic a b c d e f0 g2 g1 g0 = r2 , r1 , r0
  where
    q2 : Trit
    q2 = a ⊕ (RRQ-neg3 g2)
    q1 : Trit
    q1 = b ⊕ (RRQ-neg3 ((q2 ⊗ g2) ⊕ g1))
    q0 : Trit
    q0 = c ⊕ (RRQ-neg3 (((q1 ⊗ g2) ⊕ (q2 ⊗ g1)) ⊕ g0))
    r2 : Trit
    r2 = d ⊕ (RRQ-neg3 (((q0 ⊗ g2) ⊕ (q1 ⊗ g1)) ⊕ (q2 ⊗ g0)))
    r1 : Trit
    r1 = e ⊕ (RRQ-neg3 ((q0 ⊗ g1) ⊕ (q1 ⊗ g0)))
    r0 : Trit
    r0 = f0 ⊕ (RRQ-neg3 (q0 ⊗ g0))

-- 〔结构定义〕余式为零三元组
RRQ6-zeroTriple : Trit × Trit × Trit → Bool
RRQ6-zeroTriple (T₀ , T₀ , T₀) = true
RRQ6-zeroTriple _              = false

-- 单型检验: g 不整除 f ⟺ f 无该三次因子
RRQ6-noCubicBy : Trit → Trit → Trit → Trit → Trit → Trit → Trit → Trit → Trit → Bool
RRQ6-noCubicBy g2 g1 g0 a b c d e f0 =
  not (RRQ6-zeroTriple (RRQ6-divRemQ6-cubic a b c d e f0 g2 g1 g0))

-- 无三次因子判定器: 对 8 个已知不可约三次型逐一通过
RRQ6-noCubicFactor : Trit → Trit → Trit → Trit → Trit → Trit → Bool
RRQ6-noCubicFactor a b c d e f0 = RRQ6-cubicPass RRQ6-cubicForms
  where
    RRQ6-cubicPass : List (Trit × Trit × Trit) → Bool
    RRQ6-cubicPass [] = true
    RRQ6-cubicPass ((g2 , g1 , g0) ∷ gs) =
      RRQ-and2 (RRQ6-noCubicBy g2 g1 g0 a b c d e f0) (RRQ6-cubicPass gs)

-- 判据合成: 不可约 ⟺ 无根 ∧ 无二次因子 ∧ 无三次因子（§1 判据的判定器投影;
-- 短路形态: 有根时 and2 不再展开因子除法）
RRQ6-irrQ6 : Trit × Trit × Trit × Trit × Trit × Trit → Bool
RRQ6-irrQ6 (a , b , c , d , e , f0) =
  RRQ-and2 (RRQ6-noRootQ6 a b c d e f0)
  (RRQ-and2 (RRQ6-noQuadFactor a b c d e f0)
            (RRQ6-noCubicFactor a b c d e f0))

--------------------------------------------------------------------------------
-- §5 命名实例与 RR 分类续接〔refl 枚举; Python 实证清单照抄〕
--
-- 九块 (a₅,a₄) 各取首项立 9 个不可约命名实例（完整 116 项清单与九块
-- 计数在 RRQ6-Count）; 教学例证明三支缺一不可。判定器法逐项核对与
-- probes/rrq6_count.py 一致。
--------------------------------------------------------------------------------

-- 9 个不可约六次型（每块 (a₅,a₄) 首项; refl 逐项过三支判定器）
RRQ6-irr6-b00-first : RRQ6-irrQ6 (T₀ , T₀ , T₀ , T₀ , T₁ , T₂) ≡ true
RRQ6-irr6-b00-first = refl  -- x⁶+x+2
RRQ6-irr6-b01-first : RRQ6-irrQ6 (T₀ , T₁ , T₀ , T₂ , T₀ , T₁) ≡ true
RRQ6-irr6-b01-first = refl  -- x⁶+x⁴+2x²+1
RRQ6-irr6-b02-first : RRQ6-irrQ6 (T₀ , T₂ , T₀ , T₀ , T₀ , T₁) ≡ true
RRQ6-irr6-b02-first = refl  -- x⁶+2x⁴+1
RRQ6-irr6-b10-first : RRQ6-irrQ6 (T₁ , T₀ , T₀ , T₀ , T₀ , T₂) ≡ true
RRQ6-irr6-b10-first = refl  -- x⁶+x⁵+2
RRQ6-irr6-b11-first : RRQ6-irrQ6 (T₁ , T₁ , T₀ , T₀ , T₀ , T₁) ≡ true
RRQ6-irr6-b11-first = refl  -- x⁶+x⁵+x⁴+1
RRQ6-irr6-b12-first : RRQ6-irrQ6 (T₁ , T₂ , T₀ , T₁ , T₀ , T₂) ≡ true
RRQ6-irr6-b12-first = refl  -- x⁶+x⁵+2x⁴+x²+2
RRQ6-irr6-b20-first : RRQ6-irrQ6 (T₂ , T₀ , T₀ , T₀ , T₀ , T₂) ≡ true
RRQ6-irr6-b20-first = refl  -- x⁶+2x⁵+2
RRQ6-irr6-b21-first : RRQ6-irrQ6 (T₂ , T₁ , T₀ , T₀ , T₀ , T₁) ≡ true
RRQ6-irr6-b21-first = refl  -- x⁶+2x⁵+x⁴+1
RRQ6-irr6-b22-first : RRQ6-irrQ6 (T₂ , T₂ , T₀ , T₁ , T₀ , T₂) ≡ true
RRQ6-irr6-b22-first = refl  -- x⁶+2x⁵+2x⁴+x²+2

-- 教学例: x⁶+2x²+2——无根 ∧ 无二次因子 ∧ 有三次因子, 判定器正确判可约:
-- 三次检验不可省（省略则误判不可约）。分解 = (x³+x²+2x+1)(x³+2x²+2x+2),
-- 两因子皆 RRProperty §4c 名单内型（故恰有两个三次型整除它, 3+3 分解）。
RRQ6-red6-teach-noRoot : RRQ6-noRootQ6 T₀ T₀ T₀ T₂ T₀ T₂ ≡ true
RRQ6-red6-teach-noRoot = refl
RRQ6-red6-teach-noQuad : RRQ6-noQuadFactor T₀ T₀ T₀ T₂ T₀ T₂ ≡ true
RRQ6-red6-teach-noQuad = refl
RRQ6-red6-teach-hasCubic : RRQ6-noCubicFactor T₀ T₀ T₀ T₂ T₀ T₂ ≡ false
RRQ6-red6-teach-hasCubic = refl
RRQ6-red6-teach : RRQ6-irrQ6 (T₀ , T₀ , T₀ , T₂ , T₀ , T₂) ≡ false
RRQ6-red6-teach = refl

-- 可约补例一: x⁶+1 无根但有二次因子 x²+1（二次检验不可省; 同 RRQuartic
-- RRQ-red4-a0-b0-c0-d1 的六次版）——x⁶+1 = (x²+1)(x⁴+2x²+1)
RRQ6-red6-noRoot-hasQuad : RRQ6-irrQ6 (T₀ , T₀ , T₀ , T₀ , T₀ , T₁) ≡ false
RRQ6-red6-noRoot-hasQuad = refl
-- 可约补例二: x⁶+x = x(x⁵+1) 有根 T₀（根检验一击即中）
RRQ6-red6-hasRoot : RRQ6-irrQ6 (T₀ , T₀ , T₀ , T₀ , T₁ , T₀) ≡ false
RRQ6-red6-hasRoot = refl

-- RR 分类续接（复用 RR-IsNatural, 同 RRProperty §5/RRQuartic §5）:
-- constructive ✓（三支判定器显式全定义, 常数代价: 3 点代入 × 3 型二次
-- 除法 × 8 型三次除法）∧ large ✗（RRQ6-Count 精确计数 116/729 + 渐近
-- 衰减, 3·116 = 348 ≤ 729 仍极小）⟹ 非自然性质: 规避 RR 屏障, 同时非
-- 通用下界技术。密度证据链四点: 3/9 → 8/27 → 18/81 → 116/729。
RRQ6-holo-irreducible-6 : RR-IsNatural
RRQ6-holo-irreducible-6 = RR-classify true false RR-nonnatural-nonuniversal

--------------------------------------------------------------------------------
-- §6 立界清单（本件边界，不冒充）与结论
--
--   ✅ 判据等价性次数簿记 RRQ6-degBook（§1, 19 子句枚举闭合, 0 hole;
--      m ≥ 6 的「恰 6/≥ 7」再分是本件首编译实证所得, 与 RRQ-degBook
--      的 m ≥ 5 单子句形态不同——N=4 差额 1 个 suc 可荒谬, N=6 差额 0
--      不可）
--   ✅ 三支判定器 RRQ6-noRootQ6 / RRQ6-noQuadFactor / RRQ6-noCubicFactor
--      （§2/§3/§4, 本地重建 + 内联除法; 二次型名单 import 复用 RRProperty
--      §2, 三次型名单注释锚定复用 §4c 按系数重列 RRQ6-cubicForms;
--      neg3/and2/zeroPair 微件复用 RRQuartic）
--   ✅ 判据合成 RRQ6-irrQ6 + 命名实例 15 条（§5, 含三支不可省教学例）
--   ✅ RR 分类续接 RRQ6-holo-irreducible-6（§5, 复用 RR-IsNatural）
--   〔立界〕精确计数 116 与九块 81 项枚举在本批伴件 RRQ6-Count（本件只
--      立判定器; (729−27−9+3)/6 的 Möbius 四项核对在计数件闭合）;
--   〔立界〕N 一般化（参数化次数的枚举与密度 ~1/N 渐近）与 Möbius 全式
--      Σ_{d|n} μ(d)·3^{n/d}: 需 GF(3^k) 载体（路线图 W3）, 本件仅在
--      N=6 实测点闭合;
--   〔立界〕载体提升: 判定器级判据 ⟹ GF(3)[x] 多项式环分解 witness 的
--      最后一公里（Deg 簇基础设施）, 同 RRQuartic §5 立界, 不重复设签名;
--   〔立界〕RR 原定理（自然+有用 ⟹ 破 PRG）的形式化: 同 RRProperty/
--      RRQuartic, 需 PRG/电路类基础设施, 以 RR-IsNatural 枚举记录,
--      不设空壳签名。
--
--   0 postulate / 0 hole。
--------------------------------------------------------------------------------
