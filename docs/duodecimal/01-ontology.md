# 十二进制本体论：谁是本源，谁是投影

**日期**: 2026-08-25  
**状态**: 宪法级裁决  
**依据**: `DuodecClock.agda` + `README.md` 第 96-105 行

---

## 核心裁决

| 名字 | 是什么 | 本体还是投影 |
|------|--------|--------------|
| **十二进制（本源）** | \(\mathbb{Z}/3\mathbb{Z}_{\text{加}} \oplus \langle\alpha\rangle_{\text{乘}}\)，即 `DuodecPoint = Trit × AlphaPower` | **本源时钟结构** |
| **Duodec / C₁₂** | 与上面**加法群同构**的 12 元循环群 | **抽象加法投影**（同构像，不是生成定义） |
| **R₁₂ 环** | 带零因子的交换环 \(\mathbb{Z}/12\mathbb{Z}\) | **更粗的环投影**（乘法来自整数模 12，**不是** GF(9) 的 \(\langle\alpha\rangle\) 乘法） |
| **Doz 位值** | 以 12 为底的位值制 | **记数法层**（尚未系统形式化） |

---

## README 宪法原文

> **十二进制 = 加法步进 Z/3 ⊕ 乘法旋转 ⟨α⟩**  
> **不是**传统 Z/12 环（模 12 乘法有零因子），**不是** A₄（非交换）。  
> **Z/12 仅为抽象加法群投影。**  
> \(12 = 3\times 4 = \mathrm{char}\times\mathrm{ord}(\alpha)\)

---

## 为什么 DuodecClock 是本源

### 1. 生成方式

DuodecClock 由两个**独立的代数域**共同生成：

```agda
-- DuodecClock.agda
DuodecPoint = Trit × AlphaPower

-- 第一分量：GF(3) 加法群
Trit = {T₀, T₁, T₂}    -- 阶 3
_⊕_ : Trit → Trit → Trit  -- 模 3 加法

-- 第二分量：GF(9)* 的 4 阶子群
AlphaPower = {a0, a1, a2, a3}  -- 阶 4
mulAlpha : AlphaPower → AlphaPower → AlphaPower  -- 循环乘法
```

- **3** = char(GF(3))：损益的代数周期
- **4** = ord(α)：相位的代数周期
- **12** = LCM(3,4)：两个周期同时回到原点的最短时间

### 2. 运算语义

```agda
-- 混合运算：第一分量加法，第二分量乘法
mixedOp : DuodecPoint → DuodecPoint → DuodecPoint
mixedOp (x , a) (y , b) = (x ⊕ y , mulAlpha a b)

-- 单位元
duodec-e = (T₀ , a0)
```

- 损益运算在第一分量（Trit 加法）
- 相位运算在第二分量（α 幂乘法）
- 两者**正交**：损益不影响相位，相位不影响损益

### 3. 与 Duodecimal 的同构

```agda
-- DuodecClock.agda
toDuodec : DuodecPoint → Duodec
toDuodec (x , a) = crt12 x (alphaToFin4 a)

fromDuodec : Duodec → DuodecPoint
fromDuodec n = π3 n , fin4ToAlpha (π4 n)

-- 往返恒等
duodec-clock-roundtrip : ∀ n → toDuodec (fromDuodec n) ≡ n
clock-duodec-roundtrip : ∀ p → fromDuodec (toDuodec p) ≡ p

-- 运算投影
mixed-to-+12 : ∀ p q → toDuodec (mixedOp p q) ≡ toDuodec p +12 toDuodec q
```

**关键**：同构 ≠ 同一。Duodecimal 的 `+12` 是 `mixedOp` 的**同构像**，不是本源定义。

---

## 为什么 Duodecimal 是投影

### 1. 载体是扁平标签

```agda
-- Duodecimal.agda
data Duodec : Set where
  d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 : Duodec
```

没有内部结构，只有 12 个构造子。

### 2. 乘法是外加的

```agda
-- Duodecimal.agda
_*12_ : Duodec → Duodec → Duodec
d0 *12 _ = d0
d1 *12 y = y
d2 *12 y = y +12 y
-- ...
```

这个乘法来自**整数模 12 乘法**，不是 `mulAlpha` 的投影。

### 3. 零因子是投影产物

```agda
-- Duodecimal.agda
zero-divisor-2×6 : d2 *12 d6 ≡ d0  -- 2×6=0 (mod 12)
zero-divisor-3×4 : d3 *12 d4 ≡ d0  -- 3×4=0 (mod 12)
```

在 DuodecClock 里没有对应物：`mulAlpha` 没有零因子（它是域子群的乘法）。

---

## 四种含义的拆分

数学上同一个符号「Z/12Z」被库里至少用了 **4 种含义**：

| 符号建议 | 对象 | 运算 | 与本源关系 |
|----------|------|------|------------|
| **DC**（DuodecClock） | `Trit × AlphaPower` | `(⊕, mulAlpha)` | **本源** |
| **C₁₂** | `(Duodec, +12)` | 仅加法 | DC 的**加法群同构像**（投影） |
| **R₁₂** | `(Duodec, +12, *12)` | 整数模 12 环 | **环投影**；有零因子；`*12 ≠ mulAlpha` |
| **Doz**（dozenal） | 位值数字串 | 底 12 的位权 | **记数/编码层** |

**禁止**再写笼统的「基于 Z12 的代数极」——必须写成 DC / C₁₂ / R₁₂ / Doz 之一。

---

## V₄ 与 C₄ 的区别

| 群 | 阶 | 来源 | 结构 |
|----|----|------|------|
| \(\langle\alpha\rangle\) | 4 | GF(9)* | **C₄**（循环，有 90°） |
| \((R_{12})^\times=\{1,5,7,11\}\) | 4 | 环单位 | **V₄ ≅ C₂×C₂**（无 4 阶元） |

都叫「四象/四」会在表述上把本源相位和环单位群焊死——**错误**。

---

## 历史认知与当前裁决

| 阶段 | 认知 | 正确性 |
|------|------|--------|
| 早期（Duodecimal 时期） | Z/12Z 是本体 | **投影误当本源** |
| 中期（DuodecClock 时期） | DC 是本源，Z/12 是投影 | **正确** |
| 当前 | 代数极应挂 DC，R₁₂/C₁₂ 为投影 | **宪法锁定** |

---

## 相关代码

| 文件 | 作用 |
|------|------|
| `src/Sovereign/Algebra/GroupTheory/DuodecClock.agda` | **本源定义**（DuodecPoint, mixedOp） |
| `src/Sovereign/Algebra/Duodecimal.agda` | **投影定义**（Duodec, +12, *12） |
| `src/Sovereign/Algebra/AlgebraicPoleUnified.agda` | **代数极入口**（需修订） |
| `README.md` 第 96-105 行 | **宪法原文** |
