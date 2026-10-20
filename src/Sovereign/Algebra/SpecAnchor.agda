{-# OPTIONS --cubical --rewriting --guardedness #-}
-- | SpecAnchor — 跨语言实现的 Agda 规范锚 (等级 3 等价)
--
-- 目的: 把 cpp/rust/hs 三语言对账表 (dump_tables 的 DCCRT/DCMIX/GF3* 等节)
-- 的**每一个值**在 discrete-mathematics 规范层用 refl 判定一遍。
-- 链路: 规范 (本模块, 内核检查) ≡ 三语言实现 (dump 逐行一致, oracle 回执在册)
--       ⇒ 端到端锚定到 Agda 内核。
--
-- 本体论: 只锚定**投影层数值** (Z/12 是 DC 的投影); DC 本源事实
-- (mixedOp-12-cycle / dcZeroOblivion) 由库内既有证明承载, 本模块引用而非重证。
module Sovereign.Algebra.SpecAnchor where

open import Sovereign.Base.Trit
open import Sovereign.Algebra.FieldTower.GF9 using (GF9; _*gf9_)
open import Sovereign.Algebra.GroupTheory.DuodecClock
open import Sovereign.Algebra.GroupTheory.DCGroup using (sigmaDC; DuodecPoint)
open import Sovereign.Algebra.GroupTheory.Duodecimal
open import Sovereign.Foundation.Eisenstein
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_×_; _,_)
open import Data.Integer using (ℤ; +_)
open import Data.Fin using (Fin; zero; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

--------------------------------------------------------------------------------
-- §1. GF(3) 运算表 — 9 加法 + 9 乘法 (镜像 dump GF3ADD/GF3MUL 18 项)
--------------------------------------------------------------------------------

-- 加法表 9 项 (镜像 dump GF3ADD)
add-00 : T₀ ⊕ T₀ ≡ T₀
add-00 = refl
add-01 : T₀ ⊕ T₁ ≡ T₁
add-01 = refl
add-02 : T₀ ⊕ T₂ ≡ T₂
add-02 = refl
add-10 : T₁ ⊕ T₀ ≡ T₁
add-10 = refl
add-11 : T₁ ⊕ T₁ ≡ T₂
add-11 = refl
add-12 : T₁ ⊕ T₂ ≡ T₀
add-12 = refl
add-20 : T₂ ⊕ T₀ ≡ T₂
add-20 = refl
add-21 : T₂ ⊕ T₁ ≡ T₀
add-21 = refl
add-22 : T₂ ⊕ T₂ ≡ T₁
add-22 = refl

-- 乘法表 9 项 (镜像 dump GF3MUL)
mul-00 : T₀ ⊗ T₀ ≡ T₀
mul-00 = refl
mul-01 : T₀ ⊗ T₁ ≡ T₀
mul-01 = refl
mul-02 : T₀ ⊗ T₂ ≡ T₀
mul-02 = refl
mul-10 : T₁ ⊗ T₀ ≡ T₀
mul-10 = refl
mul-11 : T₁ ⊗ T₁ ≡ T₁
mul-11 = refl
mul-12 : T₁ ⊗ T₂ ≡ T₂
mul-12 = refl
mul-20 : T₂ ⊗ T₀ ≡ T₀
mul-20 = refl
mul-21 : T₂ ⊗ T₁ ≡ T₂
mul-21 = refl
mul-22 : T₂ ⊗ T₂ ≡ T₁
mul-22 = refl        -- 宪法: T₂⊗T₂ = T₁

-- char-3 归零: (t ⊕ t) ⊕ t = T₀ (零冥族 addZero 分量, 镜像 hs dcChar3)
anchor-char3 : ∀ (t : Trit) → (t ⊕ t) ⊕ t ≡ T₀
anchor-char3 T₀ = refl
anchor-char3 T₁ = refl
anchor-char3 T₂ = refl

--------------------------------------------------------------------------------
-- §2. C4 相位: α⁴ = a0 (相位归零, 镜像 mulAlphaCycle)
--------------------------------------------------------------------------------

anchor-alpha4 : mulAlpha (mulAlpha (mulAlpha a1 a1) a1) a1 ≡ a0
anchor-alpha4 = refl

anchor-alpha2 : mulAlpha a1 a1 ≡ a2          -- α² = 180°
anchor-alpha2 = refl

anchor-alpha3 : mulAlpha a2 a1 ≡ a3          -- α³ = 270°
anchor-alpha3 = refl

--------------------------------------------------------------------------------
-- §3. EC 单位元与 mixedOp 锚 (镜像 hs/rust/cpp dc_zero_oblivion)
--------------------------------------------------------------------------------

anchor-e : duodec-e ≡ (T₀ , a0)
anchor-e = refl

anchor-mixedop-zeroR : ∀ (x : Trit) (a : AlphaPower)
                     → mixedOp (x , a) duodec-e ≡ (x , a)
anchor-mixedop-zeroR T₀ a0 = refl
anchor-mixedop-zeroR T₀ a1 = refl
anchor-mixedop-zeroR T₀ a2 = refl
anchor-mixedop-zeroR T₀ a3 = refl
anchor-mixedop-zeroR T₁ a0 = refl
anchor-mixedop-zeroR T₁ a1 = refl
anchor-mixedop-zeroR T₁ a2 = refl
anchor-mixedop-zeroR T₁ a3 = refl
anchor-mixedop-zeroR T₂ a0 = refl
anchor-mixedop-zeroR T₂ a1 = refl
anchor-mixedop-zeroR T₂ a2 = refl
anchor-mixedop-zeroR T₂ a3 = refl

-- 联合生成元 g = (T₁, a1) 的平移锚: mixedOp g (T₀,a₀) = (T₁,a₁)
anchor-gen : mixedOp (T₁ , a1) duodec-e ≡ (T₁ , a1)
anchor-gen = refl

-- 损益抵消: (T₁,a0) mixedOp (T₂,a0) = (T₀,a0) — 04-zero-oblivion §1.1 的加法归零
anchor-cancel : mixedOp (T₁ , a0) (T₂ , a0) ≡ duodec-e
anchor-cancel = refl

--------------------------------------------------------------------------------
-- §4. CRT 投影 12 点 (镜像 dump DCCRT 12 项; crt12 是规范的唯一事实源)
--------------------------------------------------------------------------------

-- 12 点全表: toℕ₁₂ (crt12 t k) 的规范值 (镜像 dump DCCRT 12 项)
crt-00 : toℕ₁₂ (crt12 T₀ zero) ≡ 0
crt-00 = refl
crt-01 : toℕ₁₂ (crt12 T₀ (suc zero)) ≡ 9
crt-01 = refl
crt-02 : toℕ₁₂ (crt12 T₀ (suc (suc zero))) ≡ 6
crt-02 = refl
crt-03 : toℕ₁₂ (crt12 T₀ (suc (suc (suc zero)))) ≡ 3
crt-03 = refl
crt-10 : toℕ₁₂ (crt12 T₁ zero) ≡ 4
crt-10 = refl
crt-11 : toℕ₁₂ (crt12 T₁ (suc zero)) ≡ 1
crt-11 = refl
crt-12 : toℕ₁₂ (crt12 T₁ (suc (suc zero))) ≡ 10
crt-12 = refl
crt-13 : toℕ₁₂ (crt12 T₁ (suc (suc (suc zero)))) ≡ 7
crt-13 = refl
crt-20 : toℕ₁₂ (crt12 T₂ zero) ≡ 8
crt-20 = refl
crt-21 : toℕ₁₂ (crt12 T₂ (suc zero)) ≡ 5
crt-21 = refl
crt-22 : toℕ₁₂ (crt12 T₂ (suc (suc zero))) ≡ 2
crt-22 = refl
crt-23 : toℕ₁₂ (crt12 T₂ (suc (suc (suc zero)))) ≡ 11
crt-23 = refl

-- 与三语言测试的 4 个锚完全对应 (e→0, g→1, (T₀,α)→9, (T₁,a₀)→4)
anchor-crt-e : toℕ₁₂ (crt12 T₀ zero) ≡ 0
anchor-crt-e = crt-00
anchor-crt-g : toℕ₁₂ (crt12 T₁ (suc zero)) ≡ 1
anchor-crt-g = crt-11
anchor-crt-a : toℕ₁₂ (crt12 T₀ (suc zero)) ≡ 9
anchor-crt-a = crt-01
anchor-crt-t : toℕ₁₂ (crt12 T₁ zero) ≡ 4
anchor-crt-t = crt-10

--------------------------------------------------------------------------------
-- §5. Eisenstein 单位群 (镜像 hs/rust 测试: ω³=1, ω·ω²=1, |ω|=1)
--------------------------------------------------------------------------------

anchor-omega3 : ωᵉ *ᵉ ωᵉ *ᵉ ωᵉ ≡ 1ᵉ
anchor-omega3 = ω³≡1

anchor-omega2 : ωᵉ *ᵉ ωᵉ ≡ ω²ᵉ
anchor-omega2 = ω²≡ω*ω

anchor-omega-inv : ωᵉ *ᵉ ω²ᵉ ≡ 1ᵉ
anchor-omega-inv = ω*ω²≡1

-- |ω| = 1 (范数, 镜像 hs Eis normE / rust Eis::norm) — normᵉ : Eisenstein → ℤ
anchor-omega-norm : normᵉ ωᵉ ≡ (+ 1)
anchor-omega-norm = refl

--------------------------------------------------------------------------------
-- §5. GF(9) 乘法表 81 项（镜像 dump `GF9MUL`，编码 idx = a*3 + b ↦ a + b·α）
--
-- GF(9) = GF(3)[x]/(x²+1)，元素 (a,b) 表示 a + b·α，α² = −1 = 2 (mod 3)。
-- 81 项逐一由内核 `refl` 判定：Agda 的 GF(9) 乘法 ⟷ sov-math 三语言实现的 `GF9MUL`。
-- 编码一致性已由 oracle 前置核对：dump 81/81 项与 (a+bα)(c+dα) 相符 ✅
--------------------------------------------------------------------------------

gm-00 : (T₀ , T₀) *gf9 (T₀ , T₀) ≡ (T₀ , T₀)
gm-00 = refl

gm-01 : (T₀ , T₀) *gf9 (T₀ , T₁) ≡ (T₀ , T₀)
gm-01 = refl

gm-02 : (T₀ , T₀) *gf9 (T₀ , T₂) ≡ (T₀ , T₀)
gm-02 = refl

gm-03 : (T₀ , T₀) *gf9 (T₁ , T₀) ≡ (T₀ , T₀)
gm-03 = refl

gm-04 : (T₀ , T₀) *gf9 (T₁ , T₁) ≡ (T₀ , T₀)
gm-04 = refl

gm-05 : (T₀ , T₀) *gf9 (T₁ , T₂) ≡ (T₀ , T₀)
gm-05 = refl

gm-06 : (T₀ , T₀) *gf9 (T₂ , T₀) ≡ (T₀ , T₀)
gm-06 = refl

gm-07 : (T₀ , T₀) *gf9 (T₂ , T₁) ≡ (T₀ , T₀)
gm-07 = refl

gm-08 : (T₀ , T₀) *gf9 (T₂ , T₂) ≡ (T₀ , T₀)
gm-08 = refl

gm-10 : (T₀ , T₁) *gf9 (T₀ , T₀) ≡ (T₀ , T₀)
gm-10 = refl

gm-11 : (T₀ , T₁) *gf9 (T₀ , T₁) ≡ (T₂ , T₀)
gm-11 = refl

gm-12 : (T₀ , T₁) *gf9 (T₀ , T₂) ≡ (T₁ , T₀)
gm-12 = refl

gm-13 : (T₀ , T₁) *gf9 (T₁ , T₀) ≡ (T₀ , T₁)
gm-13 = refl

gm-14 : (T₀ , T₁) *gf9 (T₁ , T₁) ≡ (T₂ , T₁)
gm-14 = refl

gm-15 : (T₀ , T₁) *gf9 (T₁ , T₂) ≡ (T₁ , T₁)
gm-15 = refl

gm-16 : (T₀ , T₁) *gf9 (T₂ , T₀) ≡ (T₀ , T₂)
gm-16 = refl

gm-17 : (T₀ , T₁) *gf9 (T₂ , T₁) ≡ (T₂ , T₂)
gm-17 = refl

gm-18 : (T₀ , T₁) *gf9 (T₂ , T₂) ≡ (T₁ , T₂)
gm-18 = refl

gm-20 : (T₀ , T₂) *gf9 (T₀ , T₀) ≡ (T₀ , T₀)
gm-20 = refl

gm-21 : (T₀ , T₂) *gf9 (T₀ , T₁) ≡ (T₁ , T₀)
gm-21 = refl

gm-22 : (T₀ , T₂) *gf9 (T₀ , T₂) ≡ (T₂ , T₀)
gm-22 = refl

gm-23 : (T₀ , T₂) *gf9 (T₁ , T₀) ≡ (T₀ , T₂)
gm-23 = refl

gm-24 : (T₀ , T₂) *gf9 (T₁ , T₁) ≡ (T₁ , T₂)
gm-24 = refl

gm-25 : (T₀ , T₂) *gf9 (T₁ , T₂) ≡ (T₂ , T₂)
gm-25 = refl

gm-26 : (T₀ , T₂) *gf9 (T₂ , T₀) ≡ (T₀ , T₁)
gm-26 = refl

gm-27 : (T₀ , T₂) *gf9 (T₂ , T₁) ≡ (T₁ , T₁)
gm-27 = refl

gm-28 : (T₀ , T₂) *gf9 (T₂ , T₂) ≡ (T₂ , T₁)
gm-28 = refl

gm-30 : (T₁ , T₀) *gf9 (T₀ , T₀) ≡ (T₀ , T₀)
gm-30 = refl

gm-31 : (T₁ , T₀) *gf9 (T₀ , T₁) ≡ (T₀ , T₁)
gm-31 = refl

gm-32 : (T₁ , T₀) *gf9 (T₀ , T₂) ≡ (T₀ , T₂)
gm-32 = refl

gm-33 : (T₁ , T₀) *gf9 (T₁ , T₀) ≡ (T₁ , T₀)
gm-33 = refl

gm-34 : (T₁ , T₀) *gf9 (T₁ , T₁) ≡ (T₁ , T₁)
gm-34 = refl

gm-35 : (T₁ , T₀) *gf9 (T₁ , T₂) ≡ (T₁ , T₂)
gm-35 = refl

gm-36 : (T₁ , T₀) *gf9 (T₂ , T₀) ≡ (T₂ , T₀)
gm-36 = refl

gm-37 : (T₁ , T₀) *gf9 (T₂ , T₁) ≡ (T₂ , T₁)
gm-37 = refl

gm-38 : (T₁ , T₀) *gf9 (T₂ , T₂) ≡ (T₂ , T₂)
gm-38 = refl

gm-40 : (T₁ , T₁) *gf9 (T₀ , T₀) ≡ (T₀ , T₀)
gm-40 = refl

gm-41 : (T₁ , T₁) *gf9 (T₀ , T₁) ≡ (T₂ , T₁)
gm-41 = refl

gm-42 : (T₁ , T₁) *gf9 (T₀ , T₂) ≡ (T₁ , T₂)
gm-42 = refl

gm-43 : (T₁ , T₁) *gf9 (T₁ , T₀) ≡ (T₁ , T₁)
gm-43 = refl

gm-44 : (T₁ , T₁) *gf9 (T₁ , T₁) ≡ (T₀ , T₂)
gm-44 = refl

gm-45 : (T₁ , T₁) *gf9 (T₁ , T₂) ≡ (T₂ , T₀)
gm-45 = refl

gm-46 : (T₁ , T₁) *gf9 (T₂ , T₀) ≡ (T₂ , T₂)
gm-46 = refl

gm-47 : (T₁ , T₁) *gf9 (T₂ , T₁) ≡ (T₁ , T₀)
gm-47 = refl

gm-48 : (T₁ , T₁) *gf9 (T₂ , T₂) ≡ (T₀ , T₁)
gm-48 = refl

gm-50 : (T₁ , T₂) *gf9 (T₀ , T₀) ≡ (T₀ , T₀)
gm-50 = refl

gm-51 : (T₁ , T₂) *gf9 (T₀ , T₁) ≡ (T₁ , T₁)
gm-51 = refl

gm-52 : (T₁ , T₂) *gf9 (T₀ , T₂) ≡ (T₂ , T₂)
gm-52 = refl

gm-53 : (T₁ , T₂) *gf9 (T₁ , T₀) ≡ (T₁ , T₂)
gm-53 = refl

gm-54 : (T₁ , T₂) *gf9 (T₁ , T₁) ≡ (T₂ , T₀)
gm-54 = refl

gm-55 : (T₁ , T₂) *gf9 (T₁ , T₂) ≡ (T₀ , T₁)
gm-55 = refl

gm-56 : (T₁ , T₂) *gf9 (T₂ , T₀) ≡ (T₂ , T₁)
gm-56 = refl

gm-57 : (T₁ , T₂) *gf9 (T₂ , T₁) ≡ (T₀ , T₂)
gm-57 = refl

gm-58 : (T₁ , T₂) *gf9 (T₂ , T₂) ≡ (T₁ , T₀)
gm-58 = refl

gm-60 : (T₂ , T₀) *gf9 (T₀ , T₀) ≡ (T₀ , T₀)
gm-60 = refl

gm-61 : (T₂ , T₀) *gf9 (T₀ , T₁) ≡ (T₀ , T₂)
gm-61 = refl

gm-62 : (T₂ , T₀) *gf9 (T₀ , T₂) ≡ (T₀ , T₁)
gm-62 = refl

gm-63 : (T₂ , T₀) *gf9 (T₁ , T₀) ≡ (T₂ , T₀)
gm-63 = refl

gm-64 : (T₂ , T₀) *gf9 (T₁ , T₁) ≡ (T₂ , T₂)
gm-64 = refl

gm-65 : (T₂ , T₀) *gf9 (T₁ , T₂) ≡ (T₂ , T₁)
gm-65 = refl

gm-66 : (T₂ , T₀) *gf9 (T₂ , T₀) ≡ (T₁ , T₀)
gm-66 = refl

gm-67 : (T₂ , T₀) *gf9 (T₂ , T₁) ≡ (T₁ , T₂)
gm-67 = refl

gm-68 : (T₂ , T₀) *gf9 (T₂ , T₂) ≡ (T₁ , T₁)
gm-68 = refl

gm-70 : (T₂ , T₁) *gf9 (T₀ , T₀) ≡ (T₀ , T₀)
gm-70 = refl

gm-71 : (T₂ , T₁) *gf9 (T₀ , T₁) ≡ (T₂ , T₂)
gm-71 = refl

gm-72 : (T₂ , T₁) *gf9 (T₀ , T₂) ≡ (T₁ , T₁)
gm-72 = refl

gm-73 : (T₂ , T₁) *gf9 (T₁ , T₀) ≡ (T₂ , T₁)
gm-73 = refl

gm-74 : (T₂ , T₁) *gf9 (T₁ , T₁) ≡ (T₁ , T₀)
gm-74 = refl

gm-75 : (T₂ , T₁) *gf9 (T₁ , T₂) ≡ (T₀ , T₂)
gm-75 = refl

gm-76 : (T₂ , T₁) *gf9 (T₂ , T₀) ≡ (T₁ , T₂)
gm-76 = refl

gm-77 : (T₂ , T₁) *gf9 (T₂ , T₁) ≡ (T₀ , T₁)
gm-77 = refl

gm-78 : (T₂ , T₁) *gf9 (T₂ , T₂) ≡ (T₂ , T₀)
gm-78 = refl

gm-80 : (T₂ , T₂) *gf9 (T₀ , T₀) ≡ (T₀ , T₀)
gm-80 = refl

gm-81 : (T₂ , T₂) *gf9 (T₀ , T₁) ≡ (T₁ , T₂)
gm-81 = refl

gm-82 : (T₂ , T₂) *gf9 (T₀ , T₂) ≡ (T₂ , T₁)
gm-82 = refl

gm-83 : (T₂ , T₂) *gf9 (T₁ , T₀) ≡ (T₂ , T₂)
gm-83 = refl

gm-84 : (T₂ , T₂) *gf9 (T₁ , T₁) ≡ (T₀ , T₁)
gm-84 = refl

gm-85 : (T₂ , T₂) *gf9 (T₁ , T₂) ≡ (T₁ , T₀)
gm-85 = refl

gm-86 : (T₂ , T₂) *gf9 (T₂ , T₀) ≡ (T₁ , T₁)
gm-86 = refl

gm-87 : (T₂ , T₂) *gf9 (T₂ , T₁) ≡ (T₂ , T₀)
gm-87 = refl

gm-88 : (T₂ , T₂) *gf9 (T₂ , T₂) ≡ (T₀ , T₂)
gm-88 = refl

--------------------------------------------------------------------------------
-- §6. Frobenius σ 在 12 个 DC 点上的作用（镜像 dump `DCSIGMA`）
--
-- 库内 `DCGroup.sigmaDC (t , a) = (t , alphaInv a)`；dump 的编码是 `(t, k) ↦ (t, 3k mod 4)`。
-- 12 项逐一由内核 `refl` 判定：**库内 sigmaDC** ⟷ sov-math 三语言实现的 `DCSIGMA`。
--------------------------------------------------------------------------------

ds-00 : sigmaDC (T₀ , a0) ≡ (T₀ , a0)
ds-00 = refl

ds-01 : sigmaDC (T₀ , a1) ≡ (T₀ , a3)
ds-01 = refl

ds-02 : sigmaDC (T₀ , a2) ≡ (T₀ , a2)
ds-02 = refl

ds-03 : sigmaDC (T₀ , a3) ≡ (T₀ , a1)
ds-03 = refl

ds-10 : sigmaDC (T₁ , a0) ≡ (T₁ , a0)
ds-10 = refl

ds-11 : sigmaDC (T₁ , a1) ≡ (T₁ , a3)
ds-11 = refl

ds-12 : sigmaDC (T₁ , a2) ≡ (T₁ , a2)
ds-12 = refl

ds-13 : sigmaDC (T₁ , a3) ≡ (T₁ , a1)
ds-13 = refl

ds-20 : sigmaDC (T₂ , a0) ≡ (T₂ , a0)
ds-20 = refl

ds-21 : sigmaDC (T₂ , a1) ≡ (T₂ , a3)
ds-21 = refl

ds-22 : sigmaDC (T₂ , a2) ≡ (T₂ , a2)
ds-22 = refl

ds-23 : sigmaDC (T₂ , a3) ≡ (T₂ , a1)
ds-23 = refl

--------------------------------------------------------------------------------
-- §7. DC 群运算表 144 项（镜像 dump `DCMIX`）
--
-- `mixedOp (x , a) (y , b) = (x ⊕ y , mulAlpha a b)`（库内定义）；dump 的结果编码为
-- `r ≡ 4t − 3k (mod 12)`（已由 oracle 前置反推核对：144/144 匹配）。
-- 144 项逐一由内核 `refl` 判定 ⇒ **库内 mixedOp** ⟷ sov-math 三语言实现的 `DCMIX`。
--------------------------------------------------------------------------------

dm-0000 : mixedOp (T₀ , a0) (T₀ , a0) ≡ (T₀ , a0)
dm-0000 = refl

dm-0001 : mixedOp (T₀ , a0) (T₀ , a1) ≡ (T₀ , a1)
dm-0001 = refl

dm-0002 : mixedOp (T₀ , a0) (T₀ , a2) ≡ (T₀ , a2)
dm-0002 = refl

dm-0003 : mixedOp (T₀ , a0) (T₀ , a3) ≡ (T₀ , a3)
dm-0003 = refl

dm-0010 : mixedOp (T₀ , a0) (T₁ , a0) ≡ (T₁ , a0)
dm-0010 = refl

dm-0011 : mixedOp (T₀ , a0) (T₁ , a1) ≡ (T₁ , a1)
dm-0011 = refl

dm-0012 : mixedOp (T₀ , a0) (T₁ , a2) ≡ (T₁ , a2)
dm-0012 = refl

dm-0013 : mixedOp (T₀ , a0) (T₁ , a3) ≡ (T₁ , a3)
dm-0013 = refl

dm-0020 : mixedOp (T₀ , a0) (T₂ , a0) ≡ (T₂ , a0)
dm-0020 = refl

dm-0021 : mixedOp (T₀ , a0) (T₂ , a1) ≡ (T₂ , a1)
dm-0021 = refl

dm-0022 : mixedOp (T₀ , a0) (T₂ , a2) ≡ (T₂ , a2)
dm-0022 = refl

dm-0023 : mixedOp (T₀ , a0) (T₂ , a3) ≡ (T₂ , a3)
dm-0023 = refl

dm-0100 : mixedOp (T₀ , a1) (T₀ , a0) ≡ (T₀ , a1)
dm-0100 = refl

dm-0101 : mixedOp (T₀ , a1) (T₀ , a1) ≡ (T₀ , a2)
dm-0101 = refl

dm-0102 : mixedOp (T₀ , a1) (T₀ , a2) ≡ (T₀ , a3)
dm-0102 = refl

dm-0103 : mixedOp (T₀ , a1) (T₀ , a3) ≡ (T₀ , a0)
dm-0103 = refl

dm-0110 : mixedOp (T₀ , a1) (T₁ , a0) ≡ (T₁ , a1)
dm-0110 = refl

dm-0111 : mixedOp (T₀ , a1) (T₁ , a1) ≡ (T₁ , a2)
dm-0111 = refl

dm-0112 : mixedOp (T₀ , a1) (T₁ , a2) ≡ (T₁ , a3)
dm-0112 = refl

dm-0113 : mixedOp (T₀ , a1) (T₁ , a3) ≡ (T₁ , a0)
dm-0113 = refl

dm-0120 : mixedOp (T₀ , a1) (T₂ , a0) ≡ (T₂ , a1)
dm-0120 = refl

dm-0121 : mixedOp (T₀ , a1) (T₂ , a1) ≡ (T₂ , a2)
dm-0121 = refl

dm-0122 : mixedOp (T₀ , a1) (T₂ , a2) ≡ (T₂ , a3)
dm-0122 = refl

dm-0123 : mixedOp (T₀ , a1) (T₂ , a3) ≡ (T₂ , a0)
dm-0123 = refl

dm-0200 : mixedOp (T₀ , a2) (T₀ , a0) ≡ (T₀ , a2)
dm-0200 = refl

dm-0201 : mixedOp (T₀ , a2) (T₀ , a1) ≡ (T₀ , a3)
dm-0201 = refl

dm-0202 : mixedOp (T₀ , a2) (T₀ , a2) ≡ (T₀ , a0)
dm-0202 = refl

dm-0203 : mixedOp (T₀ , a2) (T₀ , a3) ≡ (T₀ , a1)
dm-0203 = refl

dm-0210 : mixedOp (T₀ , a2) (T₁ , a0) ≡ (T₁ , a2)
dm-0210 = refl

dm-0211 : mixedOp (T₀ , a2) (T₁ , a1) ≡ (T₁ , a3)
dm-0211 = refl

dm-0212 : mixedOp (T₀ , a2) (T₁ , a2) ≡ (T₁ , a0)
dm-0212 = refl

dm-0213 : mixedOp (T₀ , a2) (T₁ , a3) ≡ (T₁ , a1)
dm-0213 = refl

dm-0220 : mixedOp (T₀ , a2) (T₂ , a0) ≡ (T₂ , a2)
dm-0220 = refl

dm-0221 : mixedOp (T₀ , a2) (T₂ , a1) ≡ (T₂ , a3)
dm-0221 = refl

dm-0222 : mixedOp (T₀ , a2) (T₂ , a2) ≡ (T₂ , a0)
dm-0222 = refl

dm-0223 : mixedOp (T₀ , a2) (T₂ , a3) ≡ (T₂ , a1)
dm-0223 = refl

dm-0300 : mixedOp (T₀ , a3) (T₀ , a0) ≡ (T₀ , a3)
dm-0300 = refl

dm-0301 : mixedOp (T₀ , a3) (T₀ , a1) ≡ (T₀ , a0)
dm-0301 = refl

dm-0302 : mixedOp (T₀ , a3) (T₀ , a2) ≡ (T₀ , a1)
dm-0302 = refl

dm-0303 : mixedOp (T₀ , a3) (T₀ , a3) ≡ (T₀ , a2)
dm-0303 = refl

dm-0310 : mixedOp (T₀ , a3) (T₁ , a0) ≡ (T₁ , a3)
dm-0310 = refl

dm-0311 : mixedOp (T₀ , a3) (T₁ , a1) ≡ (T₁ , a0)
dm-0311 = refl

dm-0312 : mixedOp (T₀ , a3) (T₁ , a2) ≡ (T₁ , a1)
dm-0312 = refl

dm-0313 : mixedOp (T₀ , a3) (T₁ , a3) ≡ (T₁ , a2)
dm-0313 = refl

dm-0320 : mixedOp (T₀ , a3) (T₂ , a0) ≡ (T₂ , a3)
dm-0320 = refl

dm-0321 : mixedOp (T₀ , a3) (T₂ , a1) ≡ (T₂ , a0)
dm-0321 = refl

dm-0322 : mixedOp (T₀ , a3) (T₂ , a2) ≡ (T₂ , a1)
dm-0322 = refl

dm-0323 : mixedOp (T₀ , a3) (T₂ , a3) ≡ (T₂ , a2)
dm-0323 = refl

dm-1000 : mixedOp (T₁ , a0) (T₀ , a0) ≡ (T₁ , a0)
dm-1000 = refl

dm-1001 : mixedOp (T₁ , a0) (T₀ , a1) ≡ (T₁ , a1)
dm-1001 = refl

dm-1002 : mixedOp (T₁ , a0) (T₀ , a2) ≡ (T₁ , a2)
dm-1002 = refl

dm-1003 : mixedOp (T₁ , a0) (T₀ , a3) ≡ (T₁ , a3)
dm-1003 = refl

dm-1010 : mixedOp (T₁ , a0) (T₁ , a0) ≡ (T₂ , a0)
dm-1010 = refl

dm-1011 : mixedOp (T₁ , a0) (T₁ , a1) ≡ (T₂ , a1)
dm-1011 = refl

dm-1012 : mixedOp (T₁ , a0) (T₁ , a2) ≡ (T₂ , a2)
dm-1012 = refl

dm-1013 : mixedOp (T₁ , a0) (T₁ , a3) ≡ (T₂ , a3)
dm-1013 = refl

dm-1020 : mixedOp (T₁ , a0) (T₂ , a0) ≡ (T₀ , a0)
dm-1020 = refl

dm-1021 : mixedOp (T₁ , a0) (T₂ , a1) ≡ (T₀ , a1)
dm-1021 = refl

dm-1022 : mixedOp (T₁ , a0) (T₂ , a2) ≡ (T₀ , a2)
dm-1022 = refl

dm-1023 : mixedOp (T₁ , a0) (T₂ , a3) ≡ (T₀ , a3)
dm-1023 = refl

dm-1100 : mixedOp (T₁ , a1) (T₀ , a0) ≡ (T₁ , a1)
dm-1100 = refl

dm-1101 : mixedOp (T₁ , a1) (T₀ , a1) ≡ (T₁ , a2)
dm-1101 = refl

dm-1102 : mixedOp (T₁ , a1) (T₀ , a2) ≡ (T₁ , a3)
dm-1102 = refl

dm-1103 : mixedOp (T₁ , a1) (T₀ , a3) ≡ (T₁ , a0)
dm-1103 = refl

dm-1110 : mixedOp (T₁ , a1) (T₁ , a0) ≡ (T₂ , a1)
dm-1110 = refl

dm-1111 : mixedOp (T₁ , a1) (T₁ , a1) ≡ (T₂ , a2)
dm-1111 = refl

dm-1112 : mixedOp (T₁ , a1) (T₁ , a2) ≡ (T₂ , a3)
dm-1112 = refl

dm-1113 : mixedOp (T₁ , a1) (T₁ , a3) ≡ (T₂ , a0)
dm-1113 = refl

dm-1120 : mixedOp (T₁ , a1) (T₂ , a0) ≡ (T₀ , a1)
dm-1120 = refl

dm-1121 : mixedOp (T₁ , a1) (T₂ , a1) ≡ (T₀ , a2)
dm-1121 = refl

dm-1122 : mixedOp (T₁ , a1) (T₂ , a2) ≡ (T₀ , a3)
dm-1122 = refl

dm-1123 : mixedOp (T₁ , a1) (T₂ , a3) ≡ (T₀ , a0)
dm-1123 = refl

dm-1200 : mixedOp (T₁ , a2) (T₀ , a0) ≡ (T₁ , a2)
dm-1200 = refl

dm-1201 : mixedOp (T₁ , a2) (T₀ , a1) ≡ (T₁ , a3)
dm-1201 = refl

dm-1202 : mixedOp (T₁ , a2) (T₀ , a2) ≡ (T₁ , a0)
dm-1202 = refl

dm-1203 : mixedOp (T₁ , a2) (T₀ , a3) ≡ (T₁ , a1)
dm-1203 = refl

dm-1210 : mixedOp (T₁ , a2) (T₁ , a0) ≡ (T₂ , a2)
dm-1210 = refl

dm-1211 : mixedOp (T₁ , a2) (T₁ , a1) ≡ (T₂ , a3)
dm-1211 = refl

dm-1212 : mixedOp (T₁ , a2) (T₁ , a2) ≡ (T₂ , a0)
dm-1212 = refl

dm-1213 : mixedOp (T₁ , a2) (T₁ , a3) ≡ (T₂ , a1)
dm-1213 = refl

dm-1220 : mixedOp (T₁ , a2) (T₂ , a0) ≡ (T₀ , a2)
dm-1220 = refl

dm-1221 : mixedOp (T₁ , a2) (T₂ , a1) ≡ (T₀ , a3)
dm-1221 = refl

dm-1222 : mixedOp (T₁ , a2) (T₂ , a2) ≡ (T₀ , a0)
dm-1222 = refl

dm-1223 : mixedOp (T₁ , a2) (T₂ , a3) ≡ (T₀ , a1)
dm-1223 = refl

dm-1300 : mixedOp (T₁ , a3) (T₀ , a0) ≡ (T₁ , a3)
dm-1300 = refl

dm-1301 : mixedOp (T₁ , a3) (T₀ , a1) ≡ (T₁ , a0)
dm-1301 = refl

dm-1302 : mixedOp (T₁ , a3) (T₀ , a2) ≡ (T₁ , a1)
dm-1302 = refl

dm-1303 : mixedOp (T₁ , a3) (T₀ , a3) ≡ (T₁ , a2)
dm-1303 = refl

dm-1310 : mixedOp (T₁ , a3) (T₁ , a0) ≡ (T₂ , a3)
dm-1310 = refl

dm-1311 : mixedOp (T₁ , a3) (T₁ , a1) ≡ (T₂ , a0)
dm-1311 = refl

dm-1312 : mixedOp (T₁ , a3) (T₁ , a2) ≡ (T₂ , a1)
dm-1312 = refl

dm-1313 : mixedOp (T₁ , a3) (T₁ , a3) ≡ (T₂ , a2)
dm-1313 = refl

dm-1320 : mixedOp (T₁ , a3) (T₂ , a0) ≡ (T₀ , a3)
dm-1320 = refl

dm-1321 : mixedOp (T₁ , a3) (T₂ , a1) ≡ (T₀ , a0)
dm-1321 = refl

dm-1322 : mixedOp (T₁ , a3) (T₂ , a2) ≡ (T₀ , a1)
dm-1322 = refl

dm-1323 : mixedOp (T₁ , a3) (T₂ , a3) ≡ (T₀ , a2)
dm-1323 = refl

dm-2000 : mixedOp (T₂ , a0) (T₀ , a0) ≡ (T₂ , a0)
dm-2000 = refl

dm-2001 : mixedOp (T₂ , a0) (T₀ , a1) ≡ (T₂ , a1)
dm-2001 = refl

dm-2002 : mixedOp (T₂ , a0) (T₀ , a2) ≡ (T₂ , a2)
dm-2002 = refl

dm-2003 : mixedOp (T₂ , a0) (T₀ , a3) ≡ (T₂ , a3)
dm-2003 = refl

dm-2010 : mixedOp (T₂ , a0) (T₁ , a0) ≡ (T₀ , a0)
dm-2010 = refl

dm-2011 : mixedOp (T₂ , a0) (T₁ , a1) ≡ (T₀ , a1)
dm-2011 = refl

dm-2012 : mixedOp (T₂ , a0) (T₁ , a2) ≡ (T₀ , a2)
dm-2012 = refl

dm-2013 : mixedOp (T₂ , a0) (T₁ , a3) ≡ (T₀ , a3)
dm-2013 = refl

dm-2020 : mixedOp (T₂ , a0) (T₂ , a0) ≡ (T₁ , a0)
dm-2020 = refl

dm-2021 : mixedOp (T₂ , a0) (T₂ , a1) ≡ (T₁ , a1)
dm-2021 = refl

dm-2022 : mixedOp (T₂ , a0) (T₂ , a2) ≡ (T₁ , a2)
dm-2022 = refl

dm-2023 : mixedOp (T₂ , a0) (T₂ , a3) ≡ (T₁ , a3)
dm-2023 = refl

dm-2100 : mixedOp (T₂ , a1) (T₀ , a0) ≡ (T₂ , a1)
dm-2100 = refl

dm-2101 : mixedOp (T₂ , a1) (T₀ , a1) ≡ (T₂ , a2)
dm-2101 = refl

dm-2102 : mixedOp (T₂ , a1) (T₀ , a2) ≡ (T₂ , a3)
dm-2102 = refl

dm-2103 : mixedOp (T₂ , a1) (T₀ , a3) ≡ (T₂ , a0)
dm-2103 = refl

dm-2110 : mixedOp (T₂ , a1) (T₁ , a0) ≡ (T₀ , a1)
dm-2110 = refl

dm-2111 : mixedOp (T₂ , a1) (T₁ , a1) ≡ (T₀ , a2)
dm-2111 = refl

dm-2112 : mixedOp (T₂ , a1) (T₁ , a2) ≡ (T₀ , a3)
dm-2112 = refl

dm-2113 : mixedOp (T₂ , a1) (T₁ , a3) ≡ (T₀ , a0)
dm-2113 = refl

dm-2120 : mixedOp (T₂ , a1) (T₂ , a0) ≡ (T₁ , a1)
dm-2120 = refl

dm-2121 : mixedOp (T₂ , a1) (T₂ , a1) ≡ (T₁ , a2)
dm-2121 = refl

dm-2122 : mixedOp (T₂ , a1) (T₂ , a2) ≡ (T₁ , a3)
dm-2122 = refl

dm-2123 : mixedOp (T₂ , a1) (T₂ , a3) ≡ (T₁ , a0)
dm-2123 = refl

dm-2200 : mixedOp (T₂ , a2) (T₀ , a0) ≡ (T₂ , a2)
dm-2200 = refl

dm-2201 : mixedOp (T₂ , a2) (T₀ , a1) ≡ (T₂ , a3)
dm-2201 = refl

dm-2202 : mixedOp (T₂ , a2) (T₀ , a2) ≡ (T₂ , a0)
dm-2202 = refl

dm-2203 : mixedOp (T₂ , a2) (T₀ , a3) ≡ (T₂ , a1)
dm-2203 = refl

dm-2210 : mixedOp (T₂ , a2) (T₁ , a0) ≡ (T₀ , a2)
dm-2210 = refl

dm-2211 : mixedOp (T₂ , a2) (T₁ , a1) ≡ (T₀ , a3)
dm-2211 = refl

dm-2212 : mixedOp (T₂ , a2) (T₁ , a2) ≡ (T₀ , a0)
dm-2212 = refl

dm-2213 : mixedOp (T₂ , a2) (T₁ , a3) ≡ (T₀ , a1)
dm-2213 = refl

dm-2220 : mixedOp (T₂ , a2) (T₂ , a0) ≡ (T₁ , a2)
dm-2220 = refl

dm-2221 : mixedOp (T₂ , a2) (T₂ , a1) ≡ (T₁ , a3)
dm-2221 = refl

dm-2222 : mixedOp (T₂ , a2) (T₂ , a2) ≡ (T₁ , a0)
dm-2222 = refl

dm-2223 : mixedOp (T₂ , a2) (T₂ , a3) ≡ (T₁ , a1)
dm-2223 = refl

dm-2300 : mixedOp (T₂ , a3) (T₀ , a0) ≡ (T₂ , a3)
dm-2300 = refl

dm-2301 : mixedOp (T₂ , a3) (T₀ , a1) ≡ (T₂ , a0)
dm-2301 = refl

dm-2302 : mixedOp (T₂ , a3) (T₀ , a2) ≡ (T₂ , a1)
dm-2302 = refl

dm-2303 : mixedOp (T₂ , a3) (T₀ , a3) ≡ (T₂ , a2)
dm-2303 = refl

dm-2310 : mixedOp (T₂ , a3) (T₁ , a0) ≡ (T₀ , a3)
dm-2310 = refl

dm-2311 : mixedOp (T₂ , a3) (T₁ , a1) ≡ (T₀ , a0)
dm-2311 = refl

dm-2312 : mixedOp (T₂ , a3) (T₁ , a2) ≡ (T₀ , a1)
dm-2312 = refl

dm-2313 : mixedOp (T₂ , a3) (T₁ , a3) ≡ (T₀ , a2)
dm-2313 = refl

dm-2320 : mixedOp (T₂ , a3) (T₂ , a0) ≡ (T₁ , a3)
dm-2320 = refl

dm-2321 : mixedOp (T₂ , a3) (T₂ , a1) ≡ (T₁ , a0)
dm-2321 = refl

dm-2322 : mixedOp (T₂ , a3) (T₂ , a2) ≡ (T₁ , a1)
dm-2322 = refl

dm-2323 : mixedOp (T₂ , a3) (T₂ , a3) ≡ (T₁ , a2)
dm-2323 = refl
