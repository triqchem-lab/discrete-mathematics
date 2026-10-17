{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Algebra.RingTheory.LaurentBase
-- Laurent 多项式环的统一基础层：类型、运算、常数。
--
-- 数学背景：Z[t,t⁻¹] = ℤ 上的 Laurent 多项式环。
-- 项 = (系数, 指数) 对，多项式 = 项列表（可含同指数项，规范形需合并）。
-- 运算：加法 = 列表拼接；乘法 = 逐项展开 + 拼接。
--
-- 设计原则（Round-17 类型身份统一定型）：
--   本模块是 LaurentTerm / Laurent / 运算 / 常数的**唯一定义处**。
--   所有 Laurent 系模块从这里导入，消除 5 处重复定义的类型身份分裂。
--   重复定义 = 5 个不同类型的定义（Agda 语义），引理不可跨模块复用。
--
-- 0 postulate / 0 hole。
-- 包含：LaurentTerm / Laurent / mulTerm / _++L_ / R0——全部 Laurent 系模块的唯一定义处
module Sovereign.Algebra.RingTheory.LaurentBase where

open import Data.Integer using (ℤ; +_; _+_; _*_; -[1+_])
open import Data.List using (List; []; _∷_; _++_; foldr)
open import Data.Product using (_×_; _,_)

-- ────────────────────────────────────────────────────────────────────
-- 核心类型（唯一定义处）
-- ────────────────────────────────────────────────────────────────────

-- Laurent 项：(系数, 指数)
LaurentTerm : Set
LaurentTerm = ℤ × ℤ

-- Laurent 多项式：项列表
Laurent : Set
Laurent = List LaurentTerm

-- ────────────────────────────────────────────────────────────────────
-- 运算（唯一定义处）
-- ────────────────────────────────────────────────────────────────────

-- 项乘法：(c₁,n₁) · (c₂,n₂) = (c₁·c₂, n₁+n₂)
mulTerm : LaurentTerm → LaurentTerm → LaurentTerm
mulTerm (c₁ , n₁) (c₂ , n₂) = (c₁ * c₂ , n₁ + n₂)

-- 项映射
mapL : (LaurentTerm → LaurentTerm) → Laurent → Laurent
mapL f [] = []
mapL f (x ∷ xs) = f x ∷ mapL f xs

-- 多项式加法 = 列表拼接
_++L_ : Laurent → Laurent → Laurent
_++L_ = _++_

-- 多项式乘法 = 逐项展开 + 拼接
_*L_ : Laurent → Laurent → Laurent
xs *L ys = foldr (λ x acc → mapL (mulTerm x) ys ++L acc) [] xs

-- ────────────────────────────────────────────────────────────────────
-- 标准常数（唯一定义处）
-- ────────────────────────────────────────────────────────────────────

-- 零多项式
R0 : Laurent
R0 = []

-- 单位多项式
R1 : Laurent
R1 = (+ 1 , + 0) ∷ []

-- 变元 t
tvar : Laurent
tvar = (+ 1 , + 1) ∷ []

-- 逆元 t⁻¹
tinv : Laurent
tinv = (+ 1 , -[1+ 0 ]) ∷ []
