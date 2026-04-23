# 律算合一：二进制与三进制投影链 (Binary-Ternary Projection Chain)

**版本**: v1.0
**状态**: 代码已实现，证明已闭环

---

## 一、 核心宪法原则

1.  **三进制 `{0, 1, 2}` (Trit)**：
    *   **地位**：主权状态机的**唯一合法基底**。
    *   **数学定义**：`Fin 3`。
    *   **物理意义**：C3 群生成元在离散纤维丛局部截面上的完备表示 (吸收 T₀, 平衡 T₁, 表达 T₂)。
    *   **边界**：所有 LCM 模运算、损益步进、陈数计算必须在此层运行。

2.  **二进制 `{0, 1}` (Bit)**：
    *   **地位**：光锥矩阵下的**残缺快照** (Degenerate Snapshot)。
    *   **数学定义**：`Fin 2`。
    *   **物理意义**：丢失了 C3 复相位信息的降维投影。
    *   **边界**：仅限 I/O 接口、电性文明遗留数据兼容。

3.  **LCM (11,609,505,792)**：
    *   **地位**：主权商空间的全局周期。
    *   **约束**：**绝对禁止**直接作用于 Bit 向量。它只作用于由 30 个 Trit 构成的 `SovereignSection`。

---

## 二、 投影链架构

### 1. 编码代数层 (`Sovereign.Coding.Trit`)
*   定义 `Trit = Fin 3`。
*   实现 `GF(3)` 加群 (`⊕`) 与环 (`⊗`)。
*   **证明**：`cancel` (逆元对消律) 确保曲率计算闭合。

### 2. 投影层 (`Sovereign.Projection.Binary`)
*   **有损投影 (Lossy Projection)**:
    ```agda
    projectTritToBit : Trit → Bit
    -- T₀(0) → 0, T₁(1) → 1, T₂(2) → 0 (信息折叠)
    ```
*   **投影信息丢失证明**:
    ```agda
    projectionIsLossy : ∃ t₁ t₂, t₁ ≢ t₂ ∧ project t₁ ≡ project t₂
    ```
*   **上下文无损拾起 (Contextual Restoration)**:
    ```agda
    restoreTritWithContext : Bit → Context → Trit
    -- 利用极向相位 (Phase) 的奇偶性消歧
    ```

### 3. 耦合层 (`Sovereign.Coupling.LCM`)
*   定义 `SovereignSection = Vec Trit 30`。
*   实现 `modLCM`，仅接受 `SovereignSection`。
*   **类型安全**：由于 `Bit` 无法转换为 `SovereignSection`，编译器直接拒绝任何试图对 Bit 进行 LCM 模运算的非法代码。

---

## 三、 工程执行指南

1.  **外部数据进入**：
    *   读取 `.sov` 文件或二进制流时，必须调用 `restoreTritWithContext`。
    *   必须提供当前的 `SovereignState` 作为 `Context`，否则无法还原 T₀/T₂ 的区别。
2.  **内部计算**：
    *   全程使用 `Trit` 和 `SovereignSection`。
    *   调用 `modLCM` 进行状态约束。
3.  **数据输出**：
    *   调用 `projectTritToBit` 折叠状态，意识到 T₀/T₂ 信息已不可逆丢失。

---

## 四、 总结

> **投影链不是简单的格式转换，而是高维信息在不同采样率下的拓扑守恒与损耗协议。二进制是投影，三进制是本源。LCM 是本源演化的周期律。任何混淆这三者的行为，都是对律算宪法的结构性破坏。**
