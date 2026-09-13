# 目录 `src/Sovereign/Format/` 逐模块审计记录

共 4 个模块。


## `src/Sovereign/Format/CRT.agda`

- **module**: `Sovereign.Format.CRT`
- **行数**: 264（代码 192 / 注释 30）
- **OPTIONS**: `--rewriting --cubical --guardedness`
- **导入 (22)**: `Data.Nat`, `Data.Nat.Properties`, `Data.Nat.DivMod`, `Data.Product`, `Data.Unit`, `Relation.Binary.PropositionalEquality`, `Cubical.Foundations.Prelude`, `Cubical.Foundations.Isomorphism`, `Sovereign.Arithmetic.CRTLemmas`, `Data.Nat`, `Data.Nat.DivMod`, `Data.Product`, `Relation.Binary.PropositionalEquality`, `Cubical.Foundations.Prelude`, `Cubical.Foundations.Isomorphism`, `Data.Nat.Properties`, `Data.Nat.Properties`, `Data.Nat.DivMod`, `Data.Nat.Properties`, `Data.Nat.DivMod`, `Data.Nat`, `Data.Nat.DivMod`
- **data 类型**: `CRTEigenvalue`
- **顶层签名 (22)**: `kT1`, `kT2`, `T1`, `T2`, `T1-proj1`, `T1-proj2`, `T2-proj1`, `T2-proj2`, `crtProject`, `crtReconstruct`, `crtTheorem`, `CRT216`, `sqCongruence`, `divides216`, `crtLabel`, `e16-label-same`, `lemma-mod-cross-POW2`, `lemma-mod-cross-POW3`, `lemma-linear-POW2`, `lemma-linear-POW3`, `crtSec-core`, `crtSec`
- **质量**: `refl`×13；⚠️ 1 postulate

## `src/Sovereign/Format/CRTMeasurement.agda`

- **module**: `Sovereign.Format.CRTMeasurement`
- **行数**: 544（代码 264 / 注释 168）
- **OPTIONS**: `--rewriting --guardedness`
- **头部注释（数学背景）**:
  - | Sovereign.Format.CRTMeasurement
  - CRT 的中国原始含义："周期丈量"，不是西方片面的同余代数
  - CRT.agda 处理 POW2=2¹⁶, POW3=3¹¹（互质，标准 CRT 代数同构）
  - CRTMeasurement.agda 处理 144/46（gcd=2，物理周期丈量）
  - 两者互补：CRT.agda 是代数同构，CRTMeasurement.agda 是物理丈量
  - 核心洞见：
  - 144 和 46 是丈量尺，不是模数
  - gcd(144,46) = 2 不是代数障碍，是双振子拍频的数学签名
  - FULL_TOUR = 144×46 = 6624（直积），不是 LCM(144,46) = 3312
  - 直积保留双残余的完整信息，LCM 折叠相位丢失信息
  - M₄ 幻方本征谱正交性替代 gcd=1 的互质条件
- **导入 (11)**: `Data.Nat`, `Data.Nat.Properties`, `Data.Nat.DivMod`, `Data.Product`, `Data.Vec`, `Relation.Binary.PropositionalEquality`, `Relation.Nullary`, `Sovereign.Structology.Winding`, `Sovereign.Structology.MagicSquare144`, `Sovereign.Base.Invariants`, `Sovereign.Format.CRT`
- **data 类型**: `M4Eigenvalue`
- **顶层签名 (87)**: `POLAR-RULER`, `TOROIDAL-RULER`, `polar-ruler≡winding`, `toroidal-ruler≡winding`, `polar-decomposition`, `GCD-144-46`, `2∣144`, `2∣46`, `euclid-step1`, `euclid-step2`, `euclid-step3`, `euclid-step4`, `reduced-polar`, `reduced-toroidal`, `reduced-polar-correct`, `reduced-toroidal-correct`, `coprime-step1`, `coprime-step2`, `coprime-step3`, `coprime-step4`, `bezout-72`, `bezout-23`, `FULL-TOUR`, `LCM-144-46`, `full-tour-value`, `full-tour≡magic`, `full-tour-is-2-lcm`, `lcm-formula`, `info-ratio`, `measure`, `measure-0`, `measure-1`, `measure-46`, `measure-144`, `measure-at-lcm`, `measure-at-full-tour`, `measure-half-plus-1`, `measure-parity`, `Reconstructible`, `reconstruct-0-0`, `reconstruct-1-1`, `reconstruct-2-2`, `reconstruct-46-0`, `reconstruct-143-5`, `reconstruct-143-45`, `¬reconstruct-0-1`, `¬reconstruct-1-0`, `BEAT-FREQUENCY`, `beat-is-gcd`, `beat-is-chern`, `BEAT-PERIOD`, `beat-period-value`, `full-tour-beat`, `M4-SPECTRUM`, `magic-constant`, `eigenvalue-distinct`, `zero-orthogonal-34`, `zero-orthogonal-16`, `eigenvalue-34-beat`, `eigenvalue-16-power`
  - … 其余 27 项
- **质量**: `refl`×76；无 postulate / 无 hole

## `src/Sovereign/Format/ModulusGeneration.agda`

- **module**: `Sovereign.Format.ModulusGeneration`
- **行数**: 108（代码 42 / 注释 38）
- **OPTIONS**: `--rewriting --cubical --guardedness`
- **头部注释（数学背景）**:
  - | Sovereign.Format.ModulusGeneration
  - 幻方正交拓扑：CRT 模数生成协议
  - 给定环面测地线步数 k，用 M₄ 本征谱 + 克里斯托螺旋
  - 生成 CRT 模数 m_i(k)。正交判据 Orth 取代传统 gcd 互质。
- **导入 (9)**: `Data.Nat`, `Data.Integer`, `Data.Vec`, `Data.Fin`, `Data.Product`, `Relation.Binary.PropositionalEquality`, `Sovereign.Base.Invariants`, `Sovereign.RootMath.DigitalRoot`, `Sovereign.Structology.MagicSquareM4`
- **顶层签名 (15)**: `SOVEREIGN_M`, `Q`, `Φ`, `modulusGen`, `m₁`, `m₂`, `m₃`, `m₄`, `modulusSequence`, `coPhase`, `verify1to8`, `verify2to7`, `verify4to5`, `orthModulusPair`, `orthModulusTheMain`
- **质量**: `refl`×4；无 postulate / 无 hole

## `src/Sovereign/Format/TQ10.agda`

- **module**: `Sovereign.Format.TQ10`
- **行数**: 151（代码 72 / 注释 53）
- **OPTIONS**: `--rewriting --cubical --guardedness`
- **头部注释（数学背景）**:
  - | Sovereign.Format.TQ10
  - 格式定义：主权 TQ1_0 格式 (16 字节主权块)
  - 核心概念：
  - 主权块是高维拓扑状态在二维硅基介质上的**物理投影**。
  - 它将 30 个 GF(3) Trit (逻辑态) 压缩存储，并携带拓扑控制信息。
  - 宪法约束：
  - 1. 禁止浮点：所有字段必须是整数或位域。
  - 2. 奇点捕获：字节值 243-255 为能隙奇点 (Gap Singularity)，非法。
  - 3. 16 字节对齐：对应 128 位全息通道。
- **导入 (9)**: `Data.Nat`, `Data.Nat.DivMod`, `Data.Fin`, `Data.Vec`, `Data.Bool`, `Data.Product`, `Sovereign.Base.Trit`, `Sovereign.Base.Invariants`, `Sovereign.Geometry.Tryte`
- **record 类型**: `TQ10Block`
- **顶层签名 (12)**: `Tryte`, `PackedByte`, `isPackedValid`, `tritToBase3`, `base3ToTrit`, `tritToFin`, `finToTrit`, `pack5`, `unpack5`, `isBlockValid`, `getPolarPhase`, `getLocalChern`
- **质量**: `refl`×0；无 postulate / 无 hole
