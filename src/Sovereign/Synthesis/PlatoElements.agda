{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Synthesis.PlatoElements
{- | Sovereign.Synthesis.PlatoElements

  Plato 元素-多面体对应（任务书 v2.0 §8.2 层——P3 随缘尾件）。

  数学背景：柏拉图本身的对应（Timaeus 53c-56c）只有**四**元素
  （火/土/空气/水 ↔ tetra/hexa/octa/icosa），亚里士多德补第五体
  (aether ↔ dodecahedron)。本库 PlatonicSolid 是**六**枚举（五 solids
  + SphereA4 = S²/A₄ 商空间）。
  本模块的**对应语义** = 本地 WuXing 五元素（模数 2/5/4/6/8）↔
  PlatonicSolid 五几何体（SphereA4 空除外——笼统配对是数媒
  层面的自由构造，不是数学事实）。
-}

module Sovereign.Synthesis.PlatoElements where

open import Data.Nat using (ℕ; zero; suc; _+_; _∸_; _*_)
open import Data.Fin using (Fin) renaming (zero to fino; suc to sucino)
open import Data.Bool using (Bool; true; false)
open import Data.List using (List; _∷_; []; length)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans)
open import Relation.Nullary using (¬_)
open import Data.Empty using (⊥; ⊥-elim)
open import Function using (_∘_)

open import Sovereign.Base.ZeroGeometry
  using (PlatonicSolid; Tetrahedron; Hexahedron; Dodecahedron; Icosahedron; Octahedron)

-- §1 本地 WuXing 的独立承载面（模数形——WuXing.agda :30-35 全验证）
-- ---------------------------------------------------------------

-- WuXing 五元素列表（如 WuXing.agda :30-35 全验证）
-- 模数：Fire 2 / Earth 5 / Metal 4 / Water 6 / Wood 8
data WuXing5 : Set where
  w-fire w-earth w-metal w-water w-wood : WuXing5

-- 本库 PlatonicSolid 枚举面（ZeroGeometry :25-31 六案——含 SphereA4 空）
-- 本库 Platonic 有 6 构造子（五体 + S²/A₄ 商空间面）——
-- 本模块的 Plato 对表只对五几何体（SphereA4 另线）。

-- §2 配对的**射**构造（WuXing 模数序 ↦ Platonic 图形侧）
-- 射的语义锚注：
--   WuXing 模数序 2/5/4/6/8 是**模数域**不走 Platonic 枚举序——
--   配对是**本地选取（enforced pairing）**，配对依据=Timaeus
--   四元素 + 亚里士多德 ether 的经典对应（四元素）+ 本地模数序：

element5 : Set
element5 = Fin 5

-- 五常数具名形（避免裸 suc 括号递归歧义）
fzero5 : element5
fzero5 = fino
fone5 : element5
fone5 = sucino fino
ftwo5 : element5
ftwo5 = sucino (sucino fino)
fthree5 : element5
fthree5 = sucino (sucino (sucino fino))
ffour5 : element5
ffour5 = sucino (sucino (sucino (sucino fino)))           -- 0=Fire / 1=Earth / 2=Metal / 3=Water / 4=Wood

plato5 : Set
plato5 = Fin 5             -- 0=Tetra / 1=Hexa / 2=Dodeca / 3=Icosa / 4=Octa

-- 本地选取配对（mod 序 ↦ 依序对表）——enforced pairing 非定理
mod-pair : element5 → plato5
mod-pair x = x

-- §3 对偶多面体对偶（tetra 自对偶/hexa↔octa/icosa↔dodeca）
-- ---------------------------------------------------------------

dual : plato5 → plato5
dual x = inv5 x
  where
  inv5 : plato5 → plato5
  inv5 fzero5 = fzero5
  inv5 fone5 = ffour5
  inv5 ftwo5 = fthree5
  inv5 fthree5 = ftwo5
  inv5 ffour5 = fone5

dual-inv : (x : plato5) → dual (dual x) ≡ x                 -- 5 案穷举对合证（纯有限案分派）
dual-inv fzero5 = refl
dual-inv fone5 = refl
dual-inv ftwo5 = refl
dual-inv fthree5 = refl
dual-inv ffour5 = refl

-- §4 WuXing 生成序的 Platonic 侧（模数序独立核对）
-- ---------------------------------------------------------------

-- WuXing 模数（本地 WuXing.agda 语义面，data 构造子+模数注释）
mathrm : WuXing5 → ℕ
mathrm w-fire = 2
mathrm w-earth = 5
mathrm w-metal = 4
mathrm w-water = 6
mathrm w-wood = 8

-- WuXing 模数序的**双序对表**：是否有 mod-pair 的 mod-num 一致性？
-- 注意：本地配对是纯枚举对表（非定理）——以下是序的独立核查件：
mod-nums : List ℕ
mod-nums = 2 ∷ 5 ∷ 4 ∷ 6 ∷ 8 ∷ []

mod-num-5-elems : length mod-nums ≡ 5
mod-num-5-elems = refl

-- §5 核对层
-- ---------------------------------------------------

-- mod-pair 的单射（对账件——Fin 5 案辨识沿 ∅ 正解）
mod-pair-inj : ∀ x y → mod-pair x ≡ mod-pair y → x ≡ y
mod-pair-inj x y hyp = hyp  -- 恒等函数面（mod-pair-id 泛型直证）——穷举边界注记 25 案化简为 id 单射

-- EOF
