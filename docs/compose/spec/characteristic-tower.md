---
feature: characteristic-tower
status: designed
updated: 2026-08-17
branch: master
---

# 特征塔与进制层级形式化

## [S1] Problem

离散全息框架的根本定义需要形式化：
1. 坍缩判据：特征 p 域中 xᵖ−1=(x−1)ᵖ，p 次单位根全部坍缩到 1
2. 余数判据：奇 q 时有 90° 旋转 ⟺ q≡1 (mod 4)
3. 进制层级表：GF(2)/GF(4)/GF(3)/GF(9)/Z/12 的代数结构对比

## [S2] Design

### 坍缩判据（证明层）
- char 2 全塔无 90°：x⁴−1=(x−1)⁴，|GF(2ᵏ)|=2ᵏ−1 恒奇，4∤(2ᵏ−1)
- char 3 全塔无 120°（3 阶元）：x³−1=(x−1)³，GF(9) 无 3 阶元

### 余数判据（证明层）
- GF(3) 中 x²+1 无根（q=3≡3 mod 4）
- GF(9) 中 α 阶 4（q=9≡1 mod 4）

### 进制层级表（证明层）
- GF(2)：char 2，乘法群 {1}，无 90°
- GF(4)：char 2 扩张，C₃，无 90°
- GF(3)：char 3，C₂，无 90°
- GF(9)：char 3 扩张，C₈，有 90°（α 阶 4）
- 十二进制：加法步进 Z/3 ⊕ 乘法旋转 ⟨α⟩，联合周期 3×4（Z/12 仅为抽象加法群投影；模 12 环乘法零因子不参与）

## [S3] Out of Scope

- 不修改已有 GF9.agda / Trit.agda
- 不引入 postulate
- 不做物理标定（纯代数）

## Tasks

- [ ] T1: 创建 `Algebra/CharacteristicTower.agda` — 坍缩判据 (covers: S2)
- [ ] T2: 余数判据 — GF(3) 无根 + GF(9) 有 α (covers: S2; depends: T1)
- [ ] T3: 进制层级表 — GF(2)/GF(4)/GF(3)/GF(9)/Z/12 对比 (covers: S2; depends: T2)
- [ ] T4: 编译验证 — exit 0, 0 postulate (covers: S2; depends: T3)
