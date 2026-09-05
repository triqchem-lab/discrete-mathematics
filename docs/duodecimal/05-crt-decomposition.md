# CRT 分解：12 ≅ 3 × 4

**日期**: 2026-08-25  
**状态**: 核心定理  
**来源**: Duodecimal.agda, DuodecClock.agda

---

## 核心定理

\[
\mathbb{Z}/12\mathbb{Z} \cong \mathbb{Z}/3\mathbb{Z} \times \mathbb{Z}/4\mathbb{Z}
\quad\text{因为}\quad \gcd(3,4)=1
\]

**中国剩余定理（CRT）**：如果两个模数互质，则它们的直积同构于它们乘积的模。

---

## 一、为什么 12 = 3 × 4

### 1.1 独立周期

- **3** = char(GF(3))：损益的代数周期
  - `T₁ ⊕ T₂ = T₀`（损益对消灭）
  - `⊕³ = id`（损益分量周期 3）

- **4** = ord(α)：相位的代数周期
  - `α⁴ = 1`（相位旋转 360° 回原点）
  - `mulAlpha^4 = id`（相位分量周期 4）

- **12** = LCM(3,4)：两个周期同时回到原点的最短时间
  - `mixedOp^12 = id`（联合周期 12）

### 1.2 互质性

\[
\gcd(3,4) = 1
\]

这保证了 CRT 分解的存在性。如果 gcd ≠ 1，则分解不成立。

---

## 二、投影映射

### 2.1 π₃：Duodec → Trit（mod 3）

```agda
π3 : Duodec → Trit
π3 d0 = T₀; π3 d1 = T₁; π3 d2 = T₂; π3 d3 = T₀
π3 d4 = T₁; π3 d5 = T₂; π3 d6 = T₀; π3 d7 = T₁
π3 d8 = T₂; π3 d9 = T₀; π3 d10 = T₁; π3 d11 = T₂
```

**语义**：提取 12 进制标签的「损益分量」。

### 2.2 π₄：Duodec → Fin 4（mod 4）

```agda
π4 : Duodec → Fin 4
π4 d0 = zero;        π4 d1 = suc zero;        π4 d2 = suc (suc zero);        π4 d3 = suc (suc (suc zero))
π4 d4 = zero;        π4 d5 = suc zero;        π4 d6 = suc (suc zero);        π4 d7 = suc (suc (suc zero))
π4 d8 = zero;        π4 d9 = suc zero;        π4 d10 = suc (suc zero);       π4 d11 = suc (suc (suc zero))
```

**语义**：提取 12 进制标签的「相位分量」。

---

## 三、重构映射

### 3.1 crt12：Trit × Fin 4 → Duodec

```agda
crt12 : Trit → Fin 4 → Duodec
crt12 T₀ zero                  = d0   -- 0 mod 3, 0 mod 4 → 0
crt12 T₀ (suc zero)           = d9   -- 0 mod 3, 1 mod 4 → 9
crt12 T₀ (suc (suc zero))    = d6   -- 0 mod 3, 2 mod 4 → 6
crt12 T₀ (suc (suc (suc zero))) = d3   -- 0 mod 3, 3 mod 4 → 3
crt12 T₁ zero                  = d4   -- 1 mod 3, 0 mod 4 → 4
crt12 T₁ (suc zero)           = d1   -- 1 mod 3, 1 mod 4 → 1
crt12 T₁ (suc (suc zero))    = d10  -- 1 mod 3, 2 mod 4 → 10
crt12 T₁ (suc (suc (suc zero))) = d7   -- 1 mod 3, 3 mod 4 → 7
crt12 T₂ zero                  = d8   -- 2 mod 3, 0 mod 4 → 8
crt12 T₂ (suc zero)           = d5   -- 2 mod 3, 1 mod 4 → 5
crt12 T₂ (suc (suc zero))    = d2   -- 2 mod 3, 2 mod 4 → 2
crt12 T₂ (suc (suc (suc zero))) = d11  -- 2 mod 3, 3 mod 4 → 11
```

**公式**：\(x = (4a + 9b) \bmod 12\)，其中 \(a = x \bmod 3\)，\(b = x \bmod 4\)

### 3.2 往返恒等

```agda
crt12-roundtrip : ∀ x → crt12 (π3 x) (π4 x) ≡ x
crt12-roundtrip d0 = refl;  crt12-roundtrip d1 = refl;  crt12-roundtrip d2 = refl
crt12-roundtrip d3 = refl;  crt12-roundtrip d4 = refl;  crt12-roundtrip d5 = refl
crt12-roundtrip d6 = refl;  crt12-roundtrip d7 = refl;  crt12-roundtrip d8 = refl
crt12-roundtrip d9 = refl;  crt12-roundtrip d10 = refl; crt12-roundtrip d11 = refl
```

**含义**：投影后重构 = 恒等。CRT 分解是**无损**的。

---

## 四、投影同态

### 4.1 π₃ 保持加法

```agda
π3-homo-+ : ∀ x y → π3 (x +12 y) ≡ π3 x ⊕ π3 y
π3-homo-+ d0 d0 = refl; π3-homo-+ d0 d1 = refl; π3-homo-+ d0 d2 = refl; π3-homo-+ d0 d3 = refl
-- ...（144 case 穷举 refl）
```

**含义**：先加再投影 = 先投影再加。π₃ 是**环同态**。

### 4.2 π₃ 保持乘法

```agda
π3-homo-* : ∀ x y → π3 (x *12 y) ≡ π3 x ⊗ π3 y
π3-homo-* d0 d0 = refl; π3-homo-* d0 d1 = refl; π3-homo-* d0 d2 = refl; π3-homo-* d0 d3 = refl
-- ...（144 case 穷举 refl）
```

**含义**：先乘再投影 = 先投影再乘。π₃ 是**环同态**。

---

## 五、CRT 表

| x | π₃(x) | π₄(x) | crt12(π₃,π₄) |
|---|-------|-------|---------------|
| d0 | T₀ | 0 | d0 |
| d1 | T₁ | 1 | d1 |
| d2 | T₂ | 2 | d2 |
| d3 | T₀ | 3 | d3 |
| d4 | T₁ | 0 | d4 |
| d5 | T₂ | 1 | d5 |
| d6 | T₀ | 2 | d6 |
| d7 | T₁ | 3 | d7 |
| d8 | T₂ | 0 | d8 |
| d9 | T₀ | 1 | d9 |
| d10 | T₁ | 2 | d10 |
| d11 | T₂ | 3 | d11 |

---

## 六、与 DuodecClock 的关系

### 6.1 AlphaPower ↔ Fin 4 双射

```agda
alphaToFin4 : AlphaPower → Fin 4
alphaToFin4 a0 = zero
alphaToFin4 a1 = suc zero
alphaToFin4 a2 = suc (suc zero)
alphaToFin4 a3 = suc (suc (suc zero))

fin4ToAlpha : Fin 4 → AlphaPower
fin4ToAlpha zero                   = a0
fin4ToAlpha (suc zero)             = a1
fin4ToAlpha (suc (suc zero))       = a2
fin4ToAlpha (suc (suc (suc zero))) = a3
```

**语义**：Fin 4 的「0,1,2,3」对应 AlphaPower 的「a0,a1,a2,a3」=「1,α,α²,α³」。

### 6.2 同构映射

```agda
toDuodec : DuodecPoint → Duodec
toDuodec (x , a) = crt12 x (alphaToFin4 a)

fromDuodec : Duodec → DuodecPoint
fromDuodec n = π3 n , fin4ToAlpha (π4 n)
```

**语义**：
- `toDuodec` 把本源坐标 (Trit, AlphaPower) 编码成扁平标签
- `fromDuodec` 把扁平标签解码回本源坐标

### 6.3 运算投影

```agda
mixed-to-+12 : ∀ p q → toDuodec (mixedOp p q) ≡ toDuodec p +12 toDuodec q
```

**含义**：本源的混合运算投影到扁平标签上 = 扁平的模 12 加法。

---

## 七、CRT 的意义

### 7.1 结构分解

CRT 告诉我们：12 不是不可分的原子，而是 **3 和 4 的直积**。

- 3 = 损益周期
- 4 = 相位周期
- 12 = 联合周期

### 7.2 本源 vs 投影

CRT 分解在**加法群**上找回了本源结构：

\[
C_{12} \cong C_3 \times C_4
\]

但 R₁₂ 的**环乘法**（`*12`）不是 `mulAlpha` 的投影。这是两套独立的乘法。

### 7.3 与 GF(9) 的连接

CRT 的 mod 4 分量 = Fin 4 ↔ AlphaPower ↔ ⟨α⟩ ⊂ GF(9)*

这把扁平的 `Duodec` 接回了域论的 `GF(9)`。

---

## 八、未解决的问题

1. **π₄ 的同态性**：π₄ 是否保持 `+12`？需要证明。
2. **CRT 与 *12**：crt12 是否保持环乘法？需要证明。
3. **CRT 与 mulAlpha**：如何从 CRT 分量重构 mulAlpha？
