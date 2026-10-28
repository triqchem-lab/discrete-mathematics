{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Algebra.Complexity.RRQuartic
-- GF(3) monic 四次不可约精确计数（PvsNP 路线图批二 RRQ；渐近密度阶梯 N=4 阶）
--
-- 衔接（渐近密度阶梯，逐阶落地）:
--   • N=2,3: RRProperty §2/§4（9 中 3 个、27 中 8 个，refl 枚举已闭合）
--   • N=4:   本件——81 个 monic 四次中不可约恰 18 个 = (81−9)/4
--   • N=6:   下批（729 个，27 块 × 27-case 结构立界，§5）
--
-- 判据（已裁决，§1 次数簿记闭合）: monic 四次 f 在 GF(3)[x] 可约 ⟺
-- f 有一次因子或有二次因子。次数簿记: f = gh 非平凡 ⟹ deg g + deg h = 4,
-- 两侧 ≥ 1 ⟹ 仅 (1,3)/(2,2)/(3,1) 三种——deg 3 必配 deg 1 ⟹ 有一次因子;
-- 2+2 ⟹ 有二次因子。即「可约 ⟹ ∃ 因子, deg ∈ {1,2}」（RRQ-degBook，对
-- 左因子次数分案 1/2/3/4/≥5 完全枚举闭合）。反向构造性显见: 一次/二次
-- 因子本身就是分解 witness。
--
-- 由此不可约判定器两支（GF(3) 全点代入 + 三已知不可约二次型整除检验）:
--   • RRQ-noRootQ4:  三点（T₀/T₁/T₂）代入全非零 ⟺ 无一次因子
--   • RRQ-noQuadFactor: 对 x²+1、x²+x+2、x²+2x+2（RRProperty §2 已计数的
--     3 个不可约二次型）各做一次内联除法核对余式非零 ⟺ 无二次因子
-- （二次因子若可约则 f 有根，已被第一支排除; 故只需查 3 个不可约型。）
--
-- 数学核对（Python 实证先行，非猜测）: 81 个 (a,b,c,d) 逐一判定得 18 项
-- 清单照抄 §4，与 Möbius 公式 N₄ = (3⁴−3²)/4 = 18 一致（RRQ-mobius4 以
-- 4·18 ≡ 72 = 81−9 形态闭合）。实证记录: 首版 Python 判定器漏计 monic
-- 首项 x⁴ 的点值贡献（x=1 时 +1、x=2 时 16≡+1）误得 16，触发「计数与
-- 已知核对不符即停」纪律后排查修正——最终 18 项与 (81−9)/4 对齐。
--
-- 层向纪律: 同 RRProperty——Sovereign.Algebra 禁止 import
-- Sovereign.Application; GF(3) 常数算术复用 Base.Trit 的 ⊕/⊗（本件不建
-- 第三份算术块，ᴵ 后缀块留在 Irreducible/GF36 侧）。二次型知识复用
-- RRProperty §2 的 3 型名单（import 复用，非重复枚举）。
--
-- 定名纪律: 全部新符号加 RRQ- 前缀（建档前 grep 自检零撞名; 库内
-- Lang/W/addVec3/P2 撞名前科）。
--
-- 分级标注约定（同 RRProperty）: 〔结构定义〕= 数据/定义; 〔refl 枚举〕
-- = 有限情形逐点 refl/荒谬模式; 〔立界注记〕= 深件边界，不设空壳签名。
--
-- 0 postulate / 0 hole。

module Sovereign.Algebra.Complexity.RRQuartic where

open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _≤_)
open import Data.Nat.Properties using (m≤n+m)
open import Data.Bool using (Bool; true; false; not)
open import Data.List using (List; []; _∷_; _++_; map)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

-- 引用边界（同层 Complexity 复用 + Base 层，层向合规）:
open import Sovereign.Base.Trit using (Trit; T₀; T₁; T₂; _⊕_; _⊗_)
open import Sovereign.Algebra.Complexity.RRProperty using
  ( RR-noRootAt; RR-countTrue
  ; RR-IsNatural; RR-classify; RR-nonnatural-nonuniversal )

--------------------------------------------------------------------------------
-- §1 判据等价性: 次数簿记引理〔refl/荒谬模式枚举; 判据已裁决〕
--
-- 非平凡两因子分解 (deg g, deg h) 满足两侧 ≥ 1 且和为 4，故仅三种:
-- (1,3)/(2,2)/(3,1)。deg 3 必配 deg 1 ⟹ 有一次因子（⟹ 有根）; 2+2 ⟹
-- 有二次因子。结论「有一次因子或二次因子」即「可约 ⟹ ∃ 因子,
-- deg ∈ {1,2}」。反向（有一次/二次因子 ⟹ 可约）构造性显见: 因子本身
-- 就是分解 witness，无需引理。载体级边界注记见 §5 立界清单。
--------------------------------------------------------------------------------

-- 〔结构定义〕因子判定的两种结局（哪一侧因子不重要，判定器只关心存在性）
data RRQ-FactorVerdict : Set where
  RRQ-lin  : RRQ-FactorVerdict  -- 有一次因子 ⟹ 有根
  RRQ-quad : RRQ-FactorVerdict  -- 有二次因子（必为 §3 三型之一, RRProperty §2）

-- 次数簿记核心引理: 对左因子次数分案 1/2/3/4/≥5，右因子分案 0/1/≥2，
-- 九种组合逐一闭合——三种合法形态给出结论，六种非法形态荒谬模式排除。
RRQ-degBook : (m n : ℕ) → 1 ≤ m → 1 ≤ n → m + n ≡ 4 → RRQ-FactorVerdict
RRQ-degBook (suc zero) n _ _ _ = RRQ-lin                        -- (1,n): 一次因子
RRQ-degBook (suc (suc zero)) n _ _ _ = RRQ-quad                 -- (2,n): 二次因子
RRQ-degBook (suc (suc (suc zero))) zero _ _ ()                  -- 3+0 = 3 ≠ 4
RRQ-degBook (suc (suc (suc zero))) (suc zero) _ _ _ = RRQ-lin   -- (3,1): 配 deg 1
RRQ-degBook (suc (suc (suc zero))) (suc (suc n)) _ _ ()          -- 3+(2+n) ≥ 5
RRQ-degBook (suc (suc (suc (suc zero)))) zero _ () _             -- 1 ≤ 0 荒谬
RRQ-degBook (suc (suc (suc (suc zero)))) (suc zero) _ _ ()       -- 4+1 = 5 ≠ 4
RRQ-degBook (suc (suc (suc (suc zero)))) (suc (suc n)) _ _ ()    -- ≥ 6
RRQ-degBook (suc (suc (suc (suc (suc m))))) n _ _ ()             -- ≥ 5 ≠ 4

--------------------------------------------------------------------------------
-- §2 四次根检验〔本地重建; 同 RRProperty §1/§3 形态〕
--
-- monic 四次 x⁴ + a·x³ + b·x² + c·x + d（参数序 (a,b,c,d) 从高到低，与
-- RRProperty (a,b,c) 同惯例; 即数学记号 a₃,a₂,a₁,a₀）。x⁴ 项的点值贡献
-- 显式保留——Python 实证首版正是漏了它（x=1 贡献 1, x=2 贡献 16≡1）。
-- ⊕ 无 fixity 声明（非结合），全式显式括号化，书写方向 = 左嵌套。
--------------------------------------------------------------------------------

RRQ-evalQuartic : Trit → Trit → Trit → Trit → Trit → Trit
RRQ-evalQuartic a b c d x =
  ((((((x ⊗ x) ⊗ x) ⊗ x) ⊕ (((a ⊗ x) ⊗ x) ⊗ x)) ⊕ ((b ⊗ x) ⊗ x)) ⊕ (c ⊗ x)) ⊕ d

-- monic 四次无根判定器: GF(3) 全点（3 点）代入全非零〔复用 RR-noRootAt〕
RRQ-noRootQ4 : Trit → Trit → Trit → Trit → Bool
RRQ-noRootQ4 a b c d =
  RR-noRootAt (RRQ-evalQuartic a b c d T₀)
              (RRQ-evalQuartic a b c d T₁)
              (RRQ-evalQuartic a b c d T₂)

--------------------------------------------------------------------------------
-- §3 二次因子检验〔内联除法; 全 GF(3) 常数运算〕
--
-- f = x⁴+a·x³+b·x²+c·x+d 除以 g = x²+g₁·x+g₀（monic; g₁ 为一次项系数,
-- g₀ 为常数项）。商 = x²+q₁·x+q₀, 余 = r₁·x+r₀, 系数逐位消去:
--   q₁ = a − g₁,  q₀ = b − q₁·g₁ − g₀
--   r₁ = c − q₁·g₀ − q₀·g₁,  r₀ = d − q₀·g₀
-- g 整除 f ⟺ r₁ = r₀ = T₀。减法用 RRQ-neg3 + ⊕。
-- 判据衔接: f 若有二次因子则该因子可约 ⟹ f 有根（§2 已排除），故只需
-- 对 3 个不可约二次型（RRProperty §2 名单）做整除检验。
--------------------------------------------------------------------------------

RRQ-neg3 : Trit → Trit
RRQ-neg3 T₀ = T₀
RRQ-neg3 T₁ = T₂
RRQ-neg3 T₂ = T₁

RRQ-and2 : Bool → Bool → Bool
RRQ-and2 true  y = y
RRQ-and2 false _ = false

RRQ-divRemQ4 : Trit → Trit → Trit → Trit → Trit → Trit → Trit × Trit
RRQ-divRemQ4 a b c d g1 g0 = r1 , r0
  where
    q1 : Trit
    q1 = a ⊕ (RRQ-neg3 g1)
    q0 : Trit
    q0 = b ⊕ (RRQ-neg3 ((q1 ⊗ g1) ⊕ g0))
    r1 : Trit
    r1 = c ⊕ (RRQ-neg3 ((q1 ⊗ g0) ⊕ (q0 ⊗ g1)))
    r0 : Trit
    r0 = d ⊕ (RRQ-neg3 (q0 ⊗ g0))

-- 〔结构定义〕余式为零对
RRQ-zeroPair : Trit × Trit → Bool
RRQ-zeroPair (T₀ , T₀) = true
RRQ-zeroPair _         = false

-- 单型检验: g 不整除 f ⟺ f 无该二次因子
RRQ-noQuadBy : Trit → Trit → Trit → Trit → Trit → Trit → Bool
RRQ-noQuadBy g1 g0 a b c d =
  not (RRQ-zeroPair (RRQ-divRemQ4 a b c d g1 g0))

-- 无二次因子判定器: 对 3 个已知不可约二次型逐一通过
RRQ-noQuadFactor : Trit → Trit → Trit → Trit → Bool
RRQ-noQuadFactor a b c d =
  RRQ-and2 (RRQ-noQuadBy T₀ T₁ a b c d)   -- x²+1:      (g₁,g₀) = (T₀,T₁)
  (RRQ-and2 (RRQ-noQuadBy T₁ T₂ a b c d)  -- x²+x+2:    (g₁,g₀) = (T₁,T₂)
            (RRQ-noQuadBy T₂ T₂ a b c d)) -- x²+2x+2:   (g₁,g₀) = (T₂,T₂)

--------------------------------------------------------------------------------
-- §4 GF(3) monic 四次不可约精确计数 = 18〔refl 枚举，分段〕
--
-- 数学核对: 81 = 3⁴ 个 monic 四次中不可约恰 18 个 = (81−9)/4（Möbius 公式
-- N₄ = (3⁴−3²)/4, 本件以 RRQ-mobius4 形态闭合）。本节分三段: 4a List 枚举
-- → 4b 判定表 + 逐项闭合 → 4c 命名实例 + 主定理。Python 实证（每 a 块恰
-- 6 项, 6+6+6 = 18）后落笔，非猜测。
--------------------------------------------------------------------------------

-- 判据合成: 不可约 ⟺ 无根 ∧ 无二次因子（§1 判据的判定器投影）
RRQ-irrQ4 : Trit → Trit → Trit → Trit → Bool
RRQ-irrQ4 a b c d = RRQ-and2 (RRQ-noRootQ4 a b c d) (RRQ-noQuadFactor a b c d)

-- §4a 81 个 (a,b,c,d) 显式枚举——按 a 分三块（每块 b 外层 c 次之 d 最内）
RRQ-quarticListA0 : List (Trit × Trit × Trit × Trit)
RRQ-quarticListA0 =
  (T₀ , T₀ , T₀ , T₀) ∷ (T₀ , T₀ , T₀ , T₁) ∷ (T₀ , T₀ , T₀ , T₂) ∷
  (T₀ , T₀ , T₁ , T₀) ∷ (T₀ , T₀ , T₁ , T₁) ∷ (T₀ , T₀ , T₁ , T₂) ∷
  (T₀ , T₀ , T₂ , T₀) ∷ (T₀ , T₀ , T₂ , T₁) ∷ (T₀ , T₀ , T₂ , T₂) ∷
  (T₀ , T₁ , T₀ , T₀) ∷ (T₀ , T₁ , T₀ , T₁) ∷ (T₀ , T₁ , T₀ , T₂) ∷
  (T₀ , T₁ , T₁ , T₀) ∷ (T₀ , T₁ , T₁ , T₁) ∷ (T₀ , T₁ , T₁ , T₂) ∷
  (T₀ , T₁ , T₂ , T₀) ∷ (T₀ , T₁ , T₂ , T₁) ∷ (T₀ , T₁ , T₂ , T₂) ∷
  (T₀ , T₂ , T₀ , T₀) ∷ (T₀ , T₂ , T₀ , T₁) ∷ (T₀ , T₂ , T₀ , T₂) ∷
  (T₀ , T₂ , T₁ , T₀) ∷ (T₀ , T₂ , T₁ , T₁) ∷ (T₀ , T₂ , T₁ , T₂) ∷
  (T₀ , T₂ , T₂ , T₀) ∷ (T₀ , T₂ , T₂ , T₁) ∷ (T₀ , T₂ , T₂ , T₂) ∷ []

RRQ-quarticListA1 : List (Trit × Trit × Trit × Trit)
RRQ-quarticListA1 =
  (T₁ , T₀ , T₀ , T₀) ∷ (T₁ , T₀ , T₀ , T₁) ∷ (T₁ , T₀ , T₀ , T₂) ∷
  (T₁ , T₀ , T₁ , T₀) ∷ (T₁ , T₀ , T₁ , T₁) ∷ (T₁ , T₀ , T₁ , T₂) ∷
  (T₁ , T₀ , T₂ , T₀) ∷ (T₁ , T₀ , T₂ , T₁) ∷ (T₁ , T₀ , T₂ , T₂) ∷
  (T₁ , T₁ , T₀ , T₀) ∷ (T₁ , T₁ , T₀ , T₁) ∷ (T₁ , T₁ , T₀ , T₂) ∷
  (T₁ , T₁ , T₁ , T₀) ∷ (T₁ , T₁ , T₁ , T₁) ∷ (T₁ , T₁ , T₁ , T₂) ∷
  (T₁ , T₁ , T₂ , T₀) ∷ (T₁ , T₁ , T₂ , T₁) ∷ (T₁ , T₁ , T₂ , T₂) ∷
  (T₁ , T₂ , T₀ , T₀) ∷ (T₁ , T₂ , T₀ , T₁) ∷ (T₁ , T₂ , T₀ , T₂) ∷
  (T₁ , T₂ , T₁ , T₀) ∷ (T₁ , T₂ , T₁ , T₁) ∷ (T₁ , T₂ , T₁ , T₂) ∷
  (T₁ , T₂ , T₂ , T₀) ∷ (T₁ , T₂ , T₂ , T₁) ∷ (T₁ , T₂ , T₂ , T₂) ∷ []

RRQ-quarticListA2 : List (Trit × Trit × Trit × Trit)
RRQ-quarticListA2 =
  (T₂ , T₀ , T₀ , T₀) ∷ (T₂ , T₀ , T₀ , T₁) ∷ (T₂ , T₀ , T₀ , T₂) ∷
  (T₂ , T₀ , T₁ , T₀) ∷ (T₂ , T₀ , T₁ , T₁) ∷ (T₂ , T₀ , T₁ , T₂) ∷
  (T₂ , T₀ , T₂ , T₀) ∷ (T₂ , T₀ , T₂ , T₁) ∷ (T₂ , T₀ , T₂ , T₂) ∷
  (T₂ , T₁ , T₀ , T₀) ∷ (T₂ , T₁ , T₀ , T₁) ∷ (T₂ , T₁ , T₀ , T₂) ∷
  (T₂ , T₁ , T₁ , T₀) ∷ (T₂ , T₁ , T₁ , T₁) ∷ (T₂ , T₁ , T₁ , T₂) ∷
  (T₂ , T₁ , T₂ , T₀) ∷ (T₂ , T₁ , T₂ , T₁) ∷ (T₂ , T₁ , T₂ , T₂) ∷
  (T₂ , T₂ , T₀ , T₀) ∷ (T₂ , T₂ , T₀ , T₁) ∷ (T₂ , T₂ , T₀ , T₂) ∷
  (T₂ , T₂ , T₁ , T₀) ∷ (T₂ , T₂ , T₁ , T₁) ∷ (T₂ , T₂ , T₁ , T₂) ∷
  (T₂ , T₂ , T₂ , T₀) ∷ (T₂ , T₂ , T₂ , T₁) ∷ (T₂ , T₂ , T₂ , T₂) ∷ []

RRQ-quarticList : List (Trit × Trit × Trit × Trit)
RRQ-quarticList = RRQ-quarticListA0 ++ RRQ-quarticListA1 ++ RRQ-quarticListA2

-- §4b 逐项判定表（字面 Bool，与 §4a 同序分三块; Python 实证后照抄）
-- a=T₀: [0,0,0, 0,0,1, 0,0,1,  0,0,1, 0,1,0, 0,1,0,  0,1,0, 0,0,0, 0,0,0]
-- a=T₁: [0,0,1, 0,0,0, 0,1,0,  0,1,0, 0,1,0, 0,0,1,  0,0,0, 0,0,0, 0,0,1]
-- a=T₂: [0,0,1, 0,1,0, 0,0,0,  0,1,0, 0,0,1, 0,1,0,  0,0,0, 0,0,1, 0,0,0]
-- —— 合计 18 项 true（每块 6）。
RRQ-quarticFlagsA0 : List Bool
RRQ-quarticFlagsA0 =
  false ∷ false ∷ false ∷
  false ∷ false ∷ true ∷
  false ∷ false ∷ true ∷
  false ∷ false ∷ true ∷
  false ∷ true  ∷ false ∷
  false ∷ true  ∷ false ∷
  false ∷ false ∷ true ∷
  false ∷ false ∷ false ∷
  false ∷ false ∷ false ∷ []

RRQ-quarticFlagsA1 : List Bool
RRQ-quarticFlagsA1 =
  false ∷ false ∷ true ∷
  false ∷ false ∷ false ∷
  false ∷ true  ∷ false ∷
  false ∷ true  ∷ false ∷
  false ∷ true  ∷ false ∷
  false ∷ false ∷ true ∷
  false ∷ false ∷ false ∷
  false ∷ false ∷ false ∷
  false ∷ false ∷ true ∷ []

RRQ-quarticFlagsA2 : List Bool
RRQ-quarticFlagsA2 =
  false ∷ false ∷ true ∷
  false ∷ true  ∷ false ∷
  false ∷ false ∷ false ∷
  false ∷ true  ∷ false ∷
  false ∷ false ∷ true ∷
  false ∷ true  ∷ false ∷
  false ∷ false ∷ false ∷
  false ∷ false ∷ true ∷
  false ∷ false ∷ false ∷ []

RRQ-quarticFlags : List Bool
RRQ-quarticFlags =
  RRQ-quarticFlagsA0 ++ RRQ-quarticFlagsA1 ++ RRQ-quarticFlagsA2

-- 逐项闭合: 81 项字面逐一与判定器归约核对，任一错则 refl 失败
RRQ-quarticFlags-sound :
  RRQ-quarticFlags ≡
  map (λ abcd → RRQ-irrQ4 (proj₁ abcd) (proj₁ (proj₂ abcd))
                          (proj₁ (proj₂ (proj₂ abcd)))
                          (proj₂ (proj₂ (proj₂ abcd))))
      RRQ-quarticList
RRQ-quarticFlags-sound = refl

-- §4c 18 个不可约四次型命名实例（文档级逐项证据; Python 实证清单照抄）
RRQ-irr4-a0-b0-c1-d2 : RRQ-irrQ4 T₀ T₀ T₁ T₂ ≡ true
RRQ-irr4-a0-b0-c1-d2 = refl  -- x⁴+x+2
RRQ-irr4-a0-b0-c2-d2 : RRQ-irrQ4 T₀ T₀ T₂ T₂ ≡ true
RRQ-irr4-a0-b0-c2-d2 = refl  -- x⁴+2x+2
RRQ-irr4-a0-b1-c0-d2 : RRQ-irrQ4 T₀ T₁ T₀ T₂ ≡ true
RRQ-irr4-a0-b1-c0-d2 = refl  -- x⁴+x²+2
RRQ-irr4-a0-b1-c1-d1 : RRQ-irrQ4 T₀ T₁ T₁ T₁ ≡ true
RRQ-irr4-a0-b1-c1-d1 = refl  -- x⁴+x²+x+1
RRQ-irr4-a0-b1-c2-d1 : RRQ-irrQ4 T₀ T₁ T₂ T₁ ≡ true
RRQ-irr4-a0-b1-c2-d1 = refl  -- x⁴+x²+2x+1
RRQ-irr4-a0-b2-c0-d2 : RRQ-irrQ4 T₀ T₂ T₀ T₂ ≡ true
RRQ-irr4-a0-b2-c0-d2 = refl  -- x⁴+2x²+2
RRQ-irr4-a1-b0-c0-d2 : RRQ-irrQ4 T₁ T₀ T₀ T₂ ≡ true
RRQ-irr4-a1-b0-c0-d2 = refl  -- x⁴+x³+2
RRQ-irr4-a1-b0-c2-d1 : RRQ-irrQ4 T₁ T₀ T₂ T₁ ≡ true
RRQ-irr4-a1-b0-c2-d1 = refl  -- x⁴+x³+2x+1
RRQ-irr4-a1-b1-c0-d1 : RRQ-irrQ4 T₁ T₁ T₀ T₁ ≡ true
RRQ-irr4-a1-b1-c0-d1 = refl  -- x⁴+x³+x²+1
RRQ-irr4-a1-b1-c1-d1 : RRQ-irrQ4 T₁ T₁ T₁ T₁ ≡ true
RRQ-irr4-a1-b1-c1-d1 = refl  -- x⁴+x³+x²+x+1
RRQ-irr4-a1-b1-c2-d2 : RRQ-irrQ4 T₁ T₁ T₂ T₂ ≡ true
RRQ-irr4-a1-b1-c2-d2 = refl  -- x⁴+x³+x²+2x+2
RRQ-irr4-a1-b2-c2-d2 : RRQ-irrQ4 T₁ T₂ T₂ T₂ ≡ true
RRQ-irr4-a1-b2-c2-d2 = refl  -- x⁴+x³+2x²+2x+2
RRQ-irr4-a2-b0-c0-d2 : RRQ-irrQ4 T₂ T₀ T₀ T₂ ≡ true
RRQ-irr4-a2-b0-c0-d2 = refl  -- x⁴+2x³+2
RRQ-irr4-a2-b0-c1-d1 : RRQ-irrQ4 T₂ T₀ T₁ T₁ ≡ true
RRQ-irr4-a2-b0-c1-d1 = refl  -- x⁴+2x³+x+1
RRQ-irr4-a2-b1-c0-d1 : RRQ-irrQ4 T₂ T₁ T₀ T₁ ≡ true
RRQ-irr4-a2-b1-c0-d1 = refl  -- x⁴+2x³+x²+1
RRQ-irr4-a2-b1-c1-d2 : RRQ-irrQ4 T₂ T₁ T₁ T₂ ≡ true
RRQ-irr4-a2-b1-c1-d2 = refl  -- x⁴+2x³+x²+x+2
RRQ-irr4-a2-b1-c2-d1 : RRQ-irrQ4 T₂ T₁ T₂ T₁ ≡ true
RRQ-irr4-a2-b1-c2-d1 = refl  -- x⁴+2x³+x²+2x+1
RRQ-irr4-a2-b2-c1-d2 : RRQ-irrQ4 T₂ T₂ T₁ T₂ ≡ true
RRQ-irr4-a2-b2-c1-d2 = refl  -- x⁴+2x³+2x²+x+2

-- 可约命名实例（教学代表: 两者皆**无根**但可约——展示 §3 判据衔接的
-- 必要性, 无根只是必要条件, 二次因子检验不可省）
RRQ-red4-a0-b0-c0-d1 : RRQ-irrQ4 T₀ T₀ T₀ T₁ ≡ false
RRQ-red4-a0-b0-c0-d1 = refl  -- x⁴+1 = (x²+x+2)(x²+2x+2), 无根但被整除
RRQ-red4-a0-b2-c0-d1 : RRQ-irrQ4 T₀ T₂ T₀ T₁ ≡ false
RRQ-red4-a0-b2-c0-d1 = refl  -- x⁴+2x²+1 = (x²+1)², 无根但被整除

-- 计数器复用 RRProperty 的 RR-countTrue
RRQ-countIrrQ4 : ℕ
RRQ-countIrrQ4 = RR-countTrue RRQ-quarticFlags

-- 主定理: monic 四次不可约精确计数 = 18 = (81−9)/4
RRQ-countIrrQ4-18 : RRQ-countIrrQ4 ≡ 18
RRQ-countIrrQ4-18 = refl

--------------------------------------------------------------------------------
-- §5 密度与分类续接（N=4 阶; 续接 RRProperty §5/§6）
--------------------------------------------------------------------------------

-- 密度对 (不可约数, 全空间)〔结构定义; 第一分量定义性归约为 18〕
RRQ-density4 : ℕ × ℕ
RRQ-density4 = RRQ-countIrrQ4 , 81

RRQ-density4-18-81 : RRQ-density4 ≡ (18 , 81)
RRQ-density4-18-81 = refl

-- 极小性实测点: 3·18 = 54 ≤ 81（覆盖份额至多 2/3; 渐近趋零的形态证据
-- 链: 3/9 → 8/27 → 18/81, 每阶 ~1/N 衰减, 一般 N 见尾注立界）
RRQ-smallQ4 : 3 * RRQ-countIrrQ4 ≤ 81
RRQ-smallQ4 = m≤n+m 54 27

-- Möbius 公式 N₄ = (3⁴−3²)/4 的库内核对形态: 4·18 ≡ 72 = 81−9
--（一般公式 (1/n)Σ_{d|n} μ(d)·3^{n/d} 的 μ 簿记以注记承载, 见尾注立界）
RRQ-mobius4 : 4 * RRQ-countIrrQ4 ≡ 72
RRQ-mobius4 = refl

-- RR 分类续接: 与 N=2,3 阶同判——constructive ✓（RRQ-noRootQ4/
-- RRQ-noQuadFactor 显式全定义, 常数代价: 3 点代入 × 3 型除法）∧
-- large ✗（RRQ-countIrrQ4-18 精确计数 + 渐近衰减）⟹ 非自然性质:
-- 规避 RR 屏障, 同时非通用下界技术
RRQ-holo-irreducible-4 : RR-IsNatural
RRQ-holo-irreducible-4 = RR-classify true false RR-nonnatural-nonuniversal

--------------------------------------------------------------------------------
-- §6 立界清单（本件边界，不冒充）与结论
--
--   ✅ 判据等价性次数簿记 RRQ-degBook（§1, 九形态枚举闭合, 0 hole）
--   ✅ 四次判定器 RRQ-noRootQ4 / RRQ-noQuadFactor（§2/§3, 本地重建 +
--      内联除法, 复用 RRProperty 二次型名单）
--   ✅ 精确计数定理 RRQ-countIrrQ4-18（§4, 81 项 refl 枚举, 一次闭合）
--   ✅ 密度对 (18,81) + 极小性 54 ≤ 81 + Möbius 4·18 ≡ 72（§5, 闭合）
--   ✅ RR 分类续接 RRQ-holo-irreducible-4（§5, 复用 RR-IsNatural）
--   〔立界〕判据的载体级最后一公里: 「任意非平凡因子分解可规范化为
--      两因子分解形态」需多项式环/次数引理基础设施（Deg 簇），本件在
--      次数簿记层完全闭合, 分解形态 → GF(3)[x] 载体的提升留待载体层;
--   〔立界〕N=6 阶: 729 = 3⁶ 个 monic 六次, 27 块 × 27-case 枚举结构
--      同本件（Möbius 四项核对: N₆ = (3⁶−3³−3²+3)/6 = (729−27−9+3)/6
--      = 116, 注意 μ(3)、μ(6) 两项不可漏）, 留下一批——文件规模与
--      归约代价先行评估后再落笔;
--   〔立界〕一般 N 渐近密度 ~1/N 与 Möbius 公式全式: 需参数化 GF(3^k)
--      载体（路线图 W3）, 本件仅在 N=81 实测点闭合;
--   〔立界〕RR 原定理（自然+有用 ⟹ 破 PRG）的形式化: 同 RRProperty,
--      需 PRG/电路类基础设施, 以 RR-IsNatural 枚举记录, 不设空壳签名。
--
--   0 postulate / 0 hole。
--------------------------------------------------------------------------------
