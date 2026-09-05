# 十二进制关系图谱

**日期**: 2026-08-25  
**状态**: 概念关系  
**格式**: Mermaid 图表 + 文字说明

---

## 一、层次关系图

```mermaid
graph TD
    subgraph "GF 域层"
        GF3["GF(3) = Trit<br/>char=3"]
        GF9["GF(9) = GF(3)[α]/(α²+1)<br/>ord(α)=4"]
        GF3 -->|二次扩张| GF9
    end

    subgraph "本源十二进制"
        DC["DuodecPoint<br/>= Trit × AlphaPower<br/>周期 12 = 3×4"]
        GF3 -->|第一分量| DC
        GF9 -->|⟨α⟩ = 第二分量| DC
    end

    subgraph "投影层"
        C12["C₁₂ = (Duodec, +12)<br/>加法投影"]
        R12["R₁₂ = (Duodec, +12, *12)<br/>环投影 (有零因子)"]
        D12["Doz 位值系统<br/>记数法"]
        DC -->|群同构| C12
        C12 -->|另赋 *12| R12
        R12 -->|位权 12^i| D12
    end

    subgraph "物理层"
        TwelveLaw["十二律<br/>d0=黄钟, d1=大吕, ..."]
        Holonomy["和乐归零<br/>n%144=0 ∧ n%46=0"]
        C12 --> TwelveLaw
        DC --> Holonomy
    end
```

---

## 二、零冥族关系图

```mermaid
graph LR
    subgraph "零冥族"
        Z["零 = 多维相位<br/>同时回到单位元"]
    end

    subgraph "加法零冥"
        A1["T₁ ⊕ T₂ = T₀<br/>(损益对消灭)"]
        A2["x +₁₂ neg₁₂(x) = d0<br/>(逆元消去)"]
    end

    subgraph "乘法零冥"
        M1["α⁴ = 1<br/>(相位闭环)"]
        M2["mulAlpha^4 = id<br/>(周期 4)"]
    end

    subgraph "联合零冥"
        J1["mixedOp^12 = id<br/>(双周期同步)"]
        J2["+1^12 = id<br/>(12步归零)"]
        J3["holonomyToIdentity<br/>(和乐归零)"]
    end

    Z --> A1
    Z --> A2
    Z --> M1
    Z --> M2
    Z --> J1
    Z --> J2
    Z --> J3
```

---

## 三、CRT 分解关系图

```mermaid
graph TD
    Duodec["Duodec<br/>{d0, d1, ..., d11}"]
    
    subgraph "CRT 分解"
        Pi3["π₃ : Duodec → Trit<br/>(mod 3)"]
        Pi4["π₄ : Duodec → Fin 4<br/>(mod 4)"]
    end
    
    subgraph "重构"
        CRT["crt12 : Trit × Fin 4 → Duodec"]
    end
    
    Duodec -->|投影| Pi3
    Duodec -->|投影| Pi4
    Pi3 -->|输入| CRT
    Pi4 -->|输入| CRT
    CRT -->|输出| Duodec
    
    subgraph "往返恒等"
        RT["crt12 (π₃ x) (π₄ x) = x"]
    end
    
    CRT --> RT
```

---

## 四、代数极关系图

```mermaid
graph TD
    subgraph "代数极核心"
        AP["代数极 = DC 核<br/>(Trit ⊕ ⟨α⟩)"]
    end
    
    subgraph "投影接口"
        AS12["asC₁₂ : DC → C₁₂<br/>(群同构)"]
        AR12["asR₁₂ : DC → R₁₂<br/>(环结构)"]
    end
    
    subgraph "判定接口"
        DET["四极判定<br/>代数极 ⊥ 拓扑极<br/>代数极 ⊥ GF9极<br/>代数极 ⊥ 几何极"]
    end
    
    AP --> AS12
    AP --> AR12
    AP --> DET
    
    subgraph "其他三极"
        Topo["拓扑极<br/>144/46"]
        GF9P["GF9 极<br/>σ 对合"]
        Geo["几何极<br/>A₄/T⁶"]
    end
    
    DET -->|正交| Topo
    DET -->|正交| GF9P
    DET -->|正交| Geo
```

---

## 五、模块依赖图

```mermaid
graph TD
    Trit["Sovereign.Base.Trit<br/>GF(3) 定义"]
    GF9["Sovereign.Algebra.GF9<br/>GF(9) 定义"]
    DC["Sovereign.Algebra.GroupTheory.DuodecClock<br/>本源十二进制"]
    Duo["Sovereign.Algebra.Duodecimal<br/>扁平投影"]
    APU["Sovereign.Algebra.AlgebraicPoleUnified<br/>代数极入口"]
    ZPS["Sovereign.Coupling.ZhonglvPhaseSync<br/>仲吕闭合"]
    
    Trit --> GF9
    Trit --> DC
    GF9 --> DC
    DC --> Duo
    DC --> APU
    Duo --> APU
    DC --> ZPS
```

---

## 六、术语映射表

| 代码名 | 数学名 | 语义 |
|--------|--------|------|
| `Trit` | \(\mathbb{F}_3\) | 三进制损益域 |
| `AlphaPower` | \(\langle\alpha\rangle\) | α 的幂次（阶 4） |
| `DuodecPoint` | \(\mathbb{Z}/3\mathbb{Z} \times \langle\alpha\rangle\) | 本源十二进制坐标 |
| `Duodec` | \(\mathbb{Z}/12\mathbb{Z}\) | 扁平十二进制标签 |
| `mixedOp` | \(\oplus \times \mathrm{mulAlpha}\) | 混合运算（加法 × 乘法） |
| `+12` | \(+_{12}\) | 模 12 加法 |
| `*12` | \(\times_{12}\) | 模 12 乘法（有零因子） |
| `π₃` | \(\pi_3\) | mod 3 投影 |
| `π₄` | \(\pi_4\) | mod 4 投影 |
| `crt12` | CRT | 中国剩余定理重构 |
| `d0` | \(0\) | 加法单位元 |
| `(T₀, a0)` | \((0, 1)\) | 联合单位元 |

---

## 七、同构关系

```mermaid
graph LR
    DC["DuodecPoint<br/>Trit × AlphaPower"]
    C12["C₁₂<br/>(Duodec, +12)"]
    
    DC -->|toDuodec| C12
    C12 -->|fromDuodec| DC
    
    DC -.->|"群同构"| C12
```

**注意**：同构 ≠ 同一。Duodecimal 的 `+12` 是 `mixedOp` 的**同构像**，不是本源定义。

---

## 八、物理对应

| 代数结构 | 物理对应 | 文档 |
|----------|---------|------|
| Trit 三态 | 吸收态/平衡态/表达态 | 驻波叠加 |
| α 阶 4 | 90° 旋转 | GF(9) 相位 |
| 12 = 3×4 | 联合周期 | 双周期同步 |
| d0 | 黄钟 | 十二律起点 |
| 和乐归零 | 144/46 同时归零 | 仲吕闭合 |
