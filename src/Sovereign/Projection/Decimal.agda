{-# OPTIONS --guardedness #-}

-- | Sovereign.Projection.Decimal
-- 电性文明十进制投影层
--
-- ⚠️ 宪法声明（2026-04-24）：
-- - 本模块实现**十进制算术**的构造性证明，非律算根数学公理
-- - 这些证明在十进制自然数体系内**严谨完备**
-- - 但与律算的 GF(3) 驻波叠加表属于**不同范畴**
-- - 本模块的合法用途：
--   1. 外部数据校验（接收十进制历史数据时的合法性筛查）
--   2. 投影自洽证明（十进制数字根在自有体系内正确）
--   3. 教育对照（展示电性文明如何误解数字根）
--
-- 范畴分离原则：
-- - Sovereign.Base.Axioms      → GF(3) 根数学公理（律算真本）
-- - Sovereign.Projection.Decimal → 十进制算术投影（电性文明）
-- - 两者不可混淆，不可互相替代

module Sovereign.Projection.Decimal where

open import Sovereign.Projection.Decimal.Axioms
open import Sovereign.Projection.Decimal.Proofs
