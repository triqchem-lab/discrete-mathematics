# 目录 `src/Sovereign/Projection/` 逐模块审计记录

共 2 个模块。


## `src/Sovereign/Projection/Binary.agda`

- **module**: `Sovereign.Projection.Binary`
- **行数**: 174（代码 90 / 注释 56）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | Sovereign.Projection.Binary
  - 投影链：二进制与三进制的有损降维与上下文拾起
  - 宪法定义：
  - 1. projectTritToBit 是有损投影 (Lossy Projection)，仅用于外部 I/O 输出。
  - T₁(平衡) → 1, T₀(吸收)/T₂(表达) → 0。
  - 2. restoreTritWithContext 必须携带 CurrentPhase 与 WuxingMask。
  - **更新**：使用“五行掩码 (WuXing Mask)”替代“相位奇偶性”进行启发式恢复。
  - 这符合宪法中关于五行模数区决定能量态/手性倾向的定义。
- **导入 (11)**: `Data.Fin`, `Data.Bool`, `Data.Maybe`, `Data.Product`, `Data.Sum`, `Data.Empty`, `Relation.Nullary`, `Relation.Binary.PropositionalEquality`, `Sovereign.Coding.Trit`, `Data.Empty`, `Data.Empty`
- **record 类型**: `Context`
- **顶层签名 (10)**: `Bit`, `B₀`, `B₁`, `projectTritToBit`, `t0≢t2`, `projectionIsLossy`, `restoreTritWithContext`, `restoreT1Perfect`, `restoreT0CorrectInNonEarthRegions`, `restoreT2CorrectInEarthRegion`
- **质量**: `refl`×12；无 postulate / 无 hole

## `src/Sovereign/Projection/Decimal.agda`

- **module**: `Sovereign.Projection.Decimal`
- **行数**: 24（代码 4 / 注释 16）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | Sovereign.Projection.Decimal
  - 电性文明十进制投影层
  - ⚠️ 宪法声明（2026-04-24）：
  - 本模块实现**十进制算术**的构造性证明，非律算根数学公理
  - 这些证明在十进制自然数体系内**严谨完备**
  - 但与律算的 GF(3) 驻波叠加表属于**不同范畴**
  - 本模块的合法用途：
  - 1. 外部数据校验（接收十进制历史数据时的合法性筛查）
  - 2. 投影自洽证明（十进制数字根在自有体系内正确）
  - 3. 教育对照（展示电性文明如何误解数字根）
  - 范畴分离原则：
  - Sovereign.Base.Axioms      → GF(3) 根数学公理（律算真本）
  - Sovereign.Projection.Decimal → 十进制算术投影（电性文明）
  - 两者不可混淆，不可互相替代
- **导入 (2)**: `Sovereign.Projection.Decimal.Axioms`, `Sovereign.Projection.Decimal.Proofs`
- **质量**: `refl`×0；无 postulate / 无 hole
