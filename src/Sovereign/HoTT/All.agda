{-# OPTIONS --cubical --guardedness #-}

-- | Sovereign.HoTT.All
-- 律算合一同伦类型论 (HoTT) 模块总集
--
-- 本模块整合了律算合一系统在 Cubical Agda 下的所有高维拓扑定义与证明。
-- 它是连接“几何公理”与“物理演化”的数学桥梁。

module Sovereign.HoTT.All where

-- 1. 几何基础 (Geometry)
-- 定义 T⁶ 环面结构、极向/环向缠绕数、陈数 C=2、能隙 Δ=√3
public
  import Sovereign.HoTT.Geometry

-- 2. 纤维丛结构 (Bundle)
-- 定义底流形、主权纤维 (30 Trit)、全空间与截面
public
  import Sovereign.HoTT.Bundle

-- 3. 联络与和乐 (Connection)
-- 定义离散传输 (损益操作)、和乐环路、仲吕闭合 (Holonomy = Zhonglv)
public
  import Sovereign.HoTT.Connection

-- 4. 陈类与拓扑守恒 (ChernClass)
-- 定义离散曲率、全局陈数 C=2、拓扑不变性证明
public
  import Sovereign.HoTT.ChernClass

-- 5. 相变路径 (PhaseTransitionPaths)
-- 将五行相生 (火→土→金→水→木) 定义为状态空间中的同伦环路
public
  import Sovereign.HoTT.PhaseTransitionPaths

-- 6. 等价性 (Equivalence)
-- 证明 2D 工程代码 (StateMachine) 与高维纤维丛模型的同伦等价性
public
  import Sovereign.HoTT.Equivalence

-- 7. 路径基础 (Paths)
-- 基础的路径代数与环路定义
public
  import Sovereign.HoTT.Paths
