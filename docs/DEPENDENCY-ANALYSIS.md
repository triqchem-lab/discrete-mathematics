# 律算合一知识图谱 v2.5 - 依赖关系分析 (Dependency Analysis)

**版本**: v2.5  
**状态**: 关系全连接  
**核心理念**: 宇宙真理是唯一的，所有概念均通过严格的依赖链条相互连接。代码结构即是知识图谱的物理映射。

---

## 一、代码模块依赖图 (Code Dependency Graph)

本图展示了从**底层公理**到**工程实现**的完整引用链路。

```mermaid
graph TD
    %% 样式定义
    classDef axiom fill:#f9f,stroke:#333,stroke-width:2px;
    classDef inv fill:#bbf,stroke:#333,stroke-width:2px;
    classDef struct fill:#dfd,stroke:#333,stroke-width:2px;
    classDef meta fill:#ff9,stroke:#333,stroke-width:2px;
    classDef eng fill:#fdd,stroke:#333,stroke-width:2px;
    classDef app fill:#eee,stroke:#333,stroke-width:2px;

    %% 第一层：基础数学 (Base)
    subgraph 基础层 Base_Layer
        Trit[Trit.agda]:::axiom
        Invariants[Invariants.agda]:::inv
        Axioms[Axioms.agda]:::axiom
        TritOps[TritOps.agda]:::axiom
        
        Trit --> Invariants
        Invariants --> Axioms
        Invariants --> TritOps
    end

    %% 第二层：元结构与拓扑 (Meta & Topology)
    subgraph 结构层 Structure_Layer
        WuXing[WuXing.agda]:::meta
        Lattice[Lattice.agda]:::struct
        HighDim[HighDimClosure.agda]:::struct
        
        Invariants --> WuXing
        Invariants --> Lattice
        Invariants --> HighDim
        Axioms --> Lattice
    end

    %% 第三层：格式与动力学 (Format & Dynamics)
    subgraph 耦合层 Coupling_Layer
        TQ10[TQ10.agda]:::eng
        Dynamics[Dynamics.agda]:::eng
        
        Trit --> TQ10
        Invariants --> TQ10
        TQ10 --> Dynamics
        WuXing --> Dynamics
        Axioms --> Dynamics
    end

    %% 第四层：引擎与应用 (Engine & App)
    subgraph 引擎层 Engine_Layer
        QsUpdate[QsUpdate.agda]:::eng
        SM[StateMachine.agda]:::eng
        Examples[Examples.agda]:::app
        
        TQ10 --> QsUpdate
        TritOps --> QsUpdate
        
        QsUpdate --> SM
        Dynamics --> SM
        Axioms --> SM
        
        SM --> Examples
        TQ10 --> Examples
        Invariants --> Examples
    end
```

---

## 二、核心依赖链条分析 (The Golden Chains)

### 1. 真理的演化链 (Truth -> Engineering)
**链路**: `Invariants.agda` → `TQ10.agda` → `StateMachine.agda`
*   **分析**: 核心不变量（144, 46, C=2）定义在 `Invariants` 中，它们是宇宙真理。`TQ10` 格式通过 `phase_bias` 和 `chern_guard` 字段物理地承载这些真理。`StateMachine` 则通过逻辑强制这些真理不被破坏（如通过 `Axioms` 验证）。

### 2. 认知的升维链 (Perception -> Reality)
**链路**: `Trit.agda` → `TritOps.agda` → `QsUpdate.agda` → `StateMachine.agda`
*   **分析**: 认知始于最小单元 `Trit` (GF(3))。`TritOps` 定义了损益操作在 Trit 上的微观体现（旋转）。`QsUpdate` 将这些微观旋转应用到宏观块 `qs` 上。最终 `StateMachine` 将这些物理变化与元数据（相位）同步，实现了从微观认知到宏观现实的升维。

### 3. 数据的锚定链 (Theory -> Observation)
**链路**: `Lattice.agda` → `Examples.agda`
*   **分析**: `Lattice` 定义了十二律的理论值（如黄钟 81）。`Examples` 模块通过构造初始状态并运行演化，实际产出了这些数值，证明了理论（代码逻辑）能够重现观测数据（十二律序列）。

---

## 三、关键连接点说明 (Key Connection Points)

1.  **`Trit` ↔ `TQ10`**:
    *   `TQ10` 是 `Trit` 的物理容器。`TQ10` 的打包/解包逻辑 (`pack5`, `unpack5`) 是将抽象数学 (`Trit`) 映射到工程介质 (`Byte`) 的桥梁。

2.  **`Axioms` ↔ `Dynamics`**:
    *   `Dynamics` 负责状态的**时间演化**（下一步去哪），而 `Axioms` 负责**合法性验证**（这一步是否符合天道）。`StateMachine` 将两者结合：先演化，后验证（或触发闭合）。

3.  **`HighDimClosure` ↔ `QsUpdate`**:
    *   `HighDimClosure` 描述了高维拓扑的闭合原理（投影）。`QsUpdate` 实现了闭合在物理权重上的具体操作（如重置 `qs` 或旋转）。它们共同保证了系统在闭合时的内外一致性。

---

**文档生成时间**：2026  
**状态**：代码库与知识图谱已实现全连接。
