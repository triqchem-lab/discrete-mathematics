---
feature: electromagnetic-unit-bridge
status: delivered
updated: 2026-08-17
branch: master
commits: 
---

# 电磁学单位桥：频率单标定 + 范数坍缩投影

## Report

**What was built** — 频率单标定的离散全息电磁学标定层。标定参数从 6 个简化为 2 个（主频 ν + 换算常数 C_conv）。空间 = C/ν²，时间 = 1/ν，光速残影 = C/ν。GF(9) 范数坍缩 N(a+bα)=a²+b² 已形式化验证（N(α)=1 ≠ α²=2）。所有结构定理（grad-curl-zero、div-curl-zero、规范不变性、电荷守恒、高斯保持）在标定下自动保持。

**Verification** — `agda src/Sovereign/Physics/ElectromagneticUnitBridge.agda` exit 0，0 error，0 postulate。

**Journey log** —
1. 初版用 6 个独立标定参数，stdlib 2.4 的 ℚ÷ℚ 不支持导致多次类型错误
2. 改为预计算比率方案（4 基本 + 2 组合），编译通过
3. 用户提出频率单标定革命：光是频率不是速度，空间是频率逆平方投影
4. 重写为 2 参数版：EMUnitScale 只有 fundamentalFrequency + conversionConst
5. 新增 §3 范数坍缩：N(α)=1 (refl)，N(σ(α))=1 (引用已证)，α²=2 (refl)，见证分离

## Report

(待交付)

## [S1] Problem

电磁学模块群（6 模块, ~2700 行）已在 GF(9)/T⁶ 上以 0-postulate 完成代数闭环：
旋度、散度、规范不变性、时间演化、电荷守恒、GF9 统一 Maxwell 方程全部可证。

但离散场量（Trit 势差、旋度单位、格点间距、Frobenius 周期）与经典物理单位
（伏特、特斯拉、米、秒）之间没有映射。需要一个**标定层**模块，以显式参数
（非 postulate）定义离散→经典的线性映射，并证明结构关系在标定下自动保持。

## [S2] Design

### 核心原则：频率单标定

- **光是频率，不是速度**。标定层只保留一个基本量：Frobenius 主频 ν。
- **空间是频率的逆平方投影**：Δx = C/ν²（语料反比律：半径增大频率降低）。
- **时间是频率倒数**：τ = 1/ν。
- **光速是频率投影残影**：c_res = ν·Δx = C/ν（非恒定）。
- **范数坍缩是跌落机制**：N(a+bα)=a²+b²，9 个 GF(9) 元素 → 3 个 GF(3) 值。

### 标定参数（2 个）

| 参数 | 含义 |
|------|------|
| fundamentalFrequency | 主频 ν (Hz)，语料给出 2.93×10⁸ |
| conversionConst | 频率→长度换算常数 C_conv（待确定） |

### 范数坍缩（已证）

| 事实 | 内容 | 状态 |
|------|------|------|
| N(α)=1 | α 的范数是 1 | refl |
| α²=2 | 180° 翻转像 | refl |
| N(σ(α))=1 | 共轭不改变范数 | 引用已证 |
| N(α)≠α² | 范数与平方像分离 | 见证 |

### 模块结构

```
Sovereign.Physics.ElectromagneticUnitBridge
  §1 EMUnitScale record (频率单标定: 2 个参数)
  §2 频率→空间/时间投影 (Δx=C/ν², τ=1/ν, c_res=C/ν)
  §3 GF9 范数坍缩 (N(α)=1, N(σ(α))=1, 值域 {0,1,2})
  §4 离散场量→ℚ 映射
  §5 结构定理保标定
  §6 Maxwell 方程标定保持
  §7 命名层锚点 (注释级)
```

### 依赖

- `Data.Rational` (ℚ, 已在多个物理模块使用)
- `Data.Integer` (ℤ)
- `Sovereign.Base.Trit` (GF(3) 代数)
- `Sovereign.Physics.DiscreteEMField3D` (3D 场运算)
- `Sovereign.Physics.DiscreteEMCore` (div-curl-zero, 规范不变性)
- `Sovereign.Physics.DiscreteMaxwellTime` (四律)
- `Sovereign.Algebra.GF9` (GF(9) 域)

## [S3] Out of Scope

- 不预测经典常数数值（外部输入）
- 不建立光子频率量化（依赖环面几何的进一步推导）
- 不修改已有电磁学模块（纯增量）
- 不引入 postulate（标定参数是 record 字段）
- ℚ 倒数 (1/ν) 的精确实现待定（当前用占位）

## Tasks

- [x] T1: 创建 `ElectromagneticUnitBridge.agda` — EMUnitScale record + 离散→ℚ 映射 (covers: S2)
- [x] T2: 结构定理保标定 — 证明 grad/curl/div 关系在标定下保持 (covers: S2; depends: T1)
- [x] T3: Maxwell 方程标定保持 — 证明统一 Maxwell 方程在标定下形式不变 (covers: S2; depends: T2)
- [x] T4: 编译验证 — `agda src/Sovereign/Physics/ElectromagneticUnitBridge.agda` exit 0 (covers: S2; depends: T3)
- [x] T5: 频率单标定重写 — 6 参数→2 参数, 新增 §2 频率投影 + §3 范数坍缩 (covers: S2)
- [x] T6: 范数坍缩验证 — N(α)=1 refl, N(σ(α))=1 引用已证, α²=2 refl (covers: S2; depends: T5)
- [ ] T7: ℚ 倒数实现 — 用 mkℚ 或 stdlib 倒数替换 invν 占位 (covers: S2; depends: T5)
