{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Base.Lü
-- 十二律共享定义
--
-- 提供 LüName（律名）类型和索引映射，供 Structology、RootMath、T6 等模块共享

-- 数学背景：十二律 = 损益三分法生成的音名系（黄钟基准、损一/益一交替）——律算共享枚举层
-- 核心原则：
--   1. LüName 为十二律唯一命名源（Structology/RootMath/T6 共享，禁重复定义）
--   2. 索引映射保持损益生成序（非音高序）
-- 包含：LüName 枚举（十二律名）+ 索引映射
module Sovereign.Base.Lü where

open import Data.Fin using (Fin; zero; suc)

--------------------------------------------------------------------------------
-- 十二律枚举
--------------------------------------------------------------------------------

data LüName : Set where
  HuangZhong : LüName  -- 黄钟（基准）
  LinZhong   : LüName  -- 林钟（损一）
  TaiCu      : LüName  -- 太簇（益一）
  NanLu      : LüName  -- 南吕（损一）
  GuXian     : LüName  -- 姑洗（益一）
  YingZhong  : LüName  -- 应钟（损一）
  RuiBin     : LüName  -- 蕤宾（益一）
  DaLu       : LüName  -- 大吕（损一）
  YiZe       : LüName  -- 夷则（益一）
  JiaZhong   : LüName  -- 夹钟（损一）
  WuShe      : LüName  -- 无射（益一）
  ZhongLu    : LüName  -- 仲吕（损一 → 触发相位同步）

--------------------------------------------------------------------------------
-- 律名 ↔ 索引映射
--------------------------------------------------------------------------------

lüToIndex : LüName → Fin 12
lüToIndex HuangZhong = zero
lüToIndex LinZhong   = suc zero
lüToIndex TaiCu      = suc (suc zero)
lüToIndex NanLu      = suc (suc (suc zero))
lüToIndex GuXian     = suc (suc (suc (suc zero)))
lüToIndex YingZhong  = suc (suc (suc (suc (suc zero))))
lüToIndex RuiBin     = suc (suc (suc (suc (suc (suc zero)))))
lüToIndex DaLu       = suc (suc (suc (suc (suc (suc (suc zero))))))
lüToIndex YiZe       = suc (suc (suc (suc (suc (suc (suc (suc zero)))))))
lüToIndex JiaZhong   = suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))
lüToIndex WuShe      = suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))
lüToIndex ZhongLu    = suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))

indexToLü : Fin 12 → LüName
indexToLü zero                                                          = HuangZhong
indexToLü (suc zero)                                                    = LinZhong
indexToLü (suc (suc zero))                                              = TaiCu
indexToLü (suc (suc (suc zero)))                                        = NanLu
indexToLü (suc (suc (suc (suc zero))))                                  = GuXian
indexToLü (suc (suc (suc (suc (suc zero)))))                            = YingZhong
indexToLü (suc (suc (suc (suc (suc (suc zero))))))                      = RuiBin
indexToLü (suc (suc (suc (suc (suc (suc (suc zero)))))))                = DaLu
indexToLü (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))          = YiZe
indexToLü (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))    = JiaZhong
indexToLü (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))) = WuShe
indexToLü (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))) = ZhongLu
