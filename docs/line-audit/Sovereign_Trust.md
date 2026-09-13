# 目录 `src/Sovereign/Trust/` 逐模块审计记录

共 1 个模块。


## `src/Sovereign/Trust/External.agda`

- **module**: `Sovereign.Trust.External`
- **行数**: 132（代码 71 / 注释 36）
- **OPTIONS**: `--rewriting --cubical --guardedness`
- **头部注释（数学背景）**:
  - | Sovereign.Trust.External
  - 信任边界：标记所有外部引用为信用0
  - 宪法原则：
  - 1. 所有 Agda 标准库引理初始信任度为 0 (UNTRUSTED)。
  - 2. 必须经过高维几何审查 (Geometric Review) 后才能标记为 TRUSTED。
  - 3. 核心宪法模块 (LCM, HoTT) 禁止直接使用未审查的外部引理。
  - 审查状态追踪：
  - UNTRUSTED     : 未审查，禁止用于宪法级证明
  - UNDER_REVIEW  : 审查中，需高维几何验证
  - TRUSTED       : 已审查，可在宪法级证明中使用
- **导入 (3)**: `Data.Bool`, `Data.String`, `Data.Vec`
- **data 类型**: `TrustLevel`
- **record 类型**: `ReviewStatus`
- **顶层签名 (14)**: `dataNatTrust`, `dataNatPropertiesTrust`, `dataNatDivModTrust`, `dataIntegerTrust`, `dataRationalTrust`, `dataFinTrust`, `dataVecTrust`, `relationBinaryPropositionalEqualityTrust`, `relationBinaryPropositionalEqualityPropertiesTrust`, `cubicalFoundationsPreludeTrust`, `cubicalCoreEverythingTrust`, `review_log`, `require_trusted`, `isTrustedForConstitutionalUse`
- **质量**: `refl`×1；无 postulate / 无 hole
