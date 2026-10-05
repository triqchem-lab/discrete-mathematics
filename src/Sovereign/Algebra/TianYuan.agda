{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Algebra.TianYuan
-- 筹算 Agda 化第五实例：天元术（李冶《测圆海镜》1248）
--
-- 本体论：天元术是证明模式（非状态机）。三步：立天元一→推演→消元。
--   Agda 对应：函数组合（introduce → derive → extract）。
--
-- 0 postulate / 0 hole。
module Sovereign.Algebra.TianYuan where

open import Data.Nat using (ℕ; zero; suc; _*_; _+_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Product using (Σ; _×_; _,_)
open import Data.Unit using (⊤; tt)

--------------------------------------------------------------------------------
-- §1. 天元术通用模式 record（三步接口）
--------------------------------------------------------------------------------

record TianYuanPattern (Input Middle Relation Result : Set) : Set where
  field
    liTianYuan : Input → Middle
    tuiYan     : Middle → Relation
    xiaoYuan   : Relation → Result

-- 三步组合函数（在 record 外定义——避免 infix 解析问题）
tianYuanExec : ∀ {I M R Res : Set} → TianYuanPattern I M R Res → I → Res
tianYuanExec pat input =
  TianYuanPattern.xiaoYuan pat
    (TianYuanPattern.tuiYan pat
      (TianYuanPattern.liTianYuan pat input))

--------------------------------------------------------------------------------
-- §2. 天元术实例：律管闭合推导
--------------------------------------------------------------------------------

open import Sovereign.Algebra.SunyiBase
  using (CLOSURE_NUM; CLOSURE_DEN; SOVEREIGN_LCM)

record TianYuan : Set where
  constructor tian-yuan
  field
    fenZi : ℕ
    fenMu : ℕ

闭合比 : TianYuan
闭合比 = tian-yuan CLOSURE_NUM CLOSURE_DEN

消元得LCM : TianYuan → ℕ
消元得LCM (tian-yuan n d) = n * d

闭合比消元 : 消元得LCM 闭合比 ≡ SOVEREIGN_LCM
闭合比消元 = refl

--------------------------------------------------------------------------------
-- §3. 天元术 pattern 实例化
--------------------------------------------------------------------------------

lvGuan-ty : TianYuanPattern ⊤ TianYuan TianYuan ℕ
lvGuan-ty = record
  { liTianYuan = λ _ → 闭合比
  ; tuiYan     = λ r → r
  ; xiaoYuan   = 消元得LCM
  }

-- 验证
执行验证 : tianYuanExec lvGuan-ty tt ≡ SOVEREIGN_LCM
执行验证 = refl
