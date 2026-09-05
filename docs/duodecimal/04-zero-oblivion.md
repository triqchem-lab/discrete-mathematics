# 零冥族：相位归零的数学本质

**日期**: 2026-08-25  
**状态**: 核心概念  
**来源**: DuodecClock.agda, Duodecimal.agda, ZhonglvPhaseSync.agda

---

## 核心洞察

「零冥族」（Zero Oblivion）是连接 Duodecimal、DuodecClock 和仲吕闭合的**共同不动点**：

> **零不是「空」，是多维相位同时回到单位元的状态。**

---

## 一、三种归零的统一

### 1.1 加法归零（损益消灭）

```agda
-- Trit
T₁ ⊕ T₂ = T₀     -- 1 + 2 = 3 ≡ 0 (mod 3)
-- 损一和益一碰面 = 归零（虚实对消灭）

-- DuodecClock
(T₁, a0) mixedOp (T₂, a0) = (T₀, a0)  -- 损益抵消，相位不动
```

**物理语义**：吸收态 + 表达态 = 平衡态（驻波叠加的三态归零）

### 1.2 乘法/相位归零（旋转闭环）

```agda
-- AlphaPower
mulAlpha^4 a0 = a0    -- 90° × 4 = 360° = 归零

-- DuodecClock
(T₀, a1) mixedOp^4 = (T₀, a0)  -- 纯旋转 4 步归零
```

**物理语义**：α⁴=1 是 GF(9) 的四相位闭环，是「宇宙 12 进制」里 4 的来源

### 1.3 联合归零（双周期同步 = 十二）

```agda
-- Duodecimal
+1^12-id : ∀ x → +1^12 x ≡ x   -- 12 步后继 = 恒等

-- DuodecClock 分解为：
⊕³ = id  (损益周期 3)
α⁴ = id  (相位周期 4)
LCM(3,4) = 12 → mixedOp^12 = id

-- 仲吕闭合（另一个 12 的实例）
holonomyToIdentity : n % 144 ≡ 0 → n % 46 ≡ 0 → n 是公共倍数
```

**物理语义**：12 不是「选了个好看的数」，是**两个独立旋转同时回到原点的最短时间**。

---

## 二、零冥族的定义（草案）

```text
零冥族定义
━━━━━━━━━━━━━━━━━━

在一个多周期系统中，"零"不是空/无，
而是所有独立分量**同时回到单位元**的状态。

对于 12 进制系统：
  · 损益分量（周期 3）：T₀ = 吸收态 = 加法单位
  · 相位分量（周期 4）：a₀ = 1 = 乘法单位  
  · 联合零：(T₀, a₀) = d0 = 12 步后继的不动点

性质：
  · 加法零冥：x ⊕ neg(x) = T₀     （损益对消灭）
  · 乘法零冥：α⁴ = 1               （相位全闭合）
  · 联合零冥：mixedOp^12 = id       （双周期同步）
  · 和乐零冥：holonomyToIdentity    （平行移动归零）

非本源投影：
  · R₁₂ 零因子：2×6=0, 3×4=0      （环乘法的吸收态投影）
  · ≠ DC 本源（DC 没有非零乘零得零）
```

---

## 三、Duodecimal 的零冥族表现

### 3.1 加法单位元

```agda
+12-identityˡ : ∀ x → d0 +12 x ≡ x
+12-identityʳ : ∀ x → x +12 d0 ≡ x
```

`d0` 是加法的「什么都不做」。

### 3.2 周期归零

```agda
+1^12-id : ∀ x → +1^12 x ≡ x
```

12 步后继回到原点。这是**联合零冥**的扁平表现。

### 3.3 逆元消去

```agda
+12-inverse : ∀ x → x +12 neg12 x ≡ d0
```

任何元素加上它的逆 = d0。这是**加法零冥**的扁平表现。

### 3.4 零因子（R₁₂ 专用）

```agda
zero-divisor-2×6 : d2 *12 d6 ≡ d0  -- 2×6 = 0 (mod 12)
zero-divisor-3×4 : d3 *12 d4 ≡ d0  -- 3×4 = 0 (mod 12)
```

这是 R₁₂ 环乘法的**投影产物**，在 DuodecClock 里没有对应。

---

## 四、DuodecClock 的零冥族表现

### 4.1 联合单位元

```agda
duodec-e : DuodecPoint
duodec-e = (T₀ , a0)
```

- T₀ = 损益分量的单位元（吸收态）
- a0 = 相位分量的单位元（1 = α⁰）

两者**同时**是单位元 = 联合零。

### 4.2 分量独立归零

```agda
-- 损益归零（加法逆）
⊕-inverse : ∀ x → x ⊕ negate x ≡ T₀

-- 相位归零（周期 4）
mulAlpha-identityʳ : ∀ x → mulAlpha x a0 ≡ x
-- α⁴ = 1 → 绕 4 圈回原点
```

两个分量**各自独立**归零，互不干扰。

### 4.3 联合归零（12 步）

```agda
-- mixedOp^12 = id
-- 证明策略：
--   ⊕³ = id （损益周期 3）
--   α⁴ = id （相位周期 4）
--   LCM(3,4) = 12 → mixedOp^12 = id
```

**这就是 12 的来源**：不是选了个好看的数，是两个独立周期的最小公倍数。

---

## 五、仲吕闭合的零冥族表现

### 5.1 和乐归零

```agda
-- ZhonglvPhaseSync.agda
holonomyToIdentity :
  ∀ (n : ℕ) → n % 144 ≡ 0 → n % 46 ≡ 0
  → n 是 144 和 46 的公共倍数
```

- 极向缠绕 144 步归零
- 环向缠绕 46 步归零
- 同时归零 = 和乐归零 = 平行移动的零冥族

### 5.2 不可通约性

```agda
periodNotDivisible : ¬ (HOLOGRAPHIC_PERIOD % PRIMARY_PERIOD ≡ 0)
```

144 和 46 互质（gcd=2），所以它们的联合周期是 LCM(144,46) = 3312。

这是另一个「零冥族」：3312 步后，极向和环向**同时**回到原点。

---

## 六、零冥族的三副面孔

| 层 | 零冥表现 | 代码 |
|----|---------|------|
| **Duodecimal** | `d0` + `+1^12-id` | 扁平标签的周期不动点 |
| **DuodecClock** | `(T₀, a0)` + `mixedOp^12` | 本源坐标的联合不动点 |
| **仲吕闭合** | `n%144=0 ∧ n%46=0` | 极向+环向同时归零 |

它们共享的数学本质：

> 12 = 3×4 是两个独立周期的**最小公倍闭合点**。  
> 到达 d0 / (T₀,a0) 意味着**所有独立分量同时回到单位元**。  
> 这就是零冥族：零不是「空」，是**多维相位同时归位**的状态。

---

## 七、零因子 vs 零冥族

| 概念 | 零因子 | 零冥族 |
|------|--------|--------|
| **定义** | a ≠ 0, b ≠ 0, 但 a·b = 0 | 所有分量同时回到单位元 |
| **来源** | 环乘法的吸收态 | 多周期系统的联合不动点 |
| **在 DC 里** | **不存在**（mulAlpha 无零因子） | **存在**（(T₀,a0) 是联合零） |
| **在 R₁₂ 里** | 存在（2×6=0, 3×4=0） | 存在（d0 是加法零） |
| **本源性** | 投影产物 | 本源概念 |

**关键**：零因子是 R₁₂ 环乘法的投影效应，不是本源 DuodecClock 的。  
零冥族是 DuodecClock 的**本源不动点**，Duodecimal 和仲吕闭合都是它的不同投影。

---

## 八、形式化建议

建议在 `DuodecClock.agda` 里加一个 `ZeroOblivion` record：

```agda
record ZeroOblivion : Set where
  field
    carrier : Set
    zero : carrier
    addZeroR : ∀ x → mixedOp x zero ≡ x
    addZeroL : ∀ x → mixedOp zero x ≡ x
    mulAlphaCycle : ∀ a → mulAlpha^4 a ≡ a
    tritCycle : ∀ t → ⊕^3 t ≡ t
    jointCycle : ∀ p → mixedOp^12 p ≡ p
```

然后证明：
1. `toDuodec` 把 `ZeroOblivion.zero` 映到 `d0`
2. `jointCycle` 映到 `+1^12-id`
3. Duodecimal 的零因子是 R₁₂ 投影层的，**不进** ZeroOblivion
