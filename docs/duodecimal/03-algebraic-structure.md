# 十二进制代数结构：群、环、域的层次

**日期**: 2026-08-25  
**状态**: 结构分析  
**来源**: GF9AlgebraicChain.agda, Duodecimal.agda, DuodecClock.agda

---

## 层次总览

```text
                    ┌─────────────────────────────┐
                    │  GF(3)=Trit     GF(9)∋α     │
                    │  char=3         ord(α)=4    │
                    └──────────┬──────────┬───────┘
                               │          │
                               ▼          ▼
                    ┌─────────────────────────────┐
         本源 AP*   │  DC = Trit × ⟨α⟩            │
                    │  mixedOp = ⊕  ×  mulAlpha   │
                    │  周期 12 = 3×4              │
                    └──────────┬──────────────────┘
                               │ 群同构 toDuodec
                               ▼
                    ┌─────────────────────────────┐
         投影 P1    │  C₁₂ = (Duodec, +12)        │
                    │  十二律时钟、益一后继         │
                    └──────────┬──────────────────┘
                               │ 另赋 *12（ℤ 模乘）
                               ▼
                    ┌─────────────────────────────┐
         投影 P2    │  R₁₂ = (Duodec, +12, *12)   │
                    │  零因子环；单位群 V₄         │
                    └──────────┬──────────────────┘
                               │ 位权 12^i
                               ▼
                    ┌─────────────────────────────┐
         记数 D     │  Doz  十二进位值系统         │
                    │  digit∈Duodec, 进位规则      │
                    └─────────────────────────────┘
```

---

## 一、GF(3) — 有限域（素域）

### 结构

- **载体**: `Trit = {T₀, T₁, T₂}`
- **加法**: `_⊕_`（模 3 加法）
- **乘法**: `_⊗_`（模 3 乘法）
- **特征**: char = 3

### 公理（已证）

```agda
-- 加法结合律（27 case 穷举）
⊕-assoc : ∀ x y z → (x ⊕ y) ⊕ z ≡ x ⊕ (y ⊕ z)

-- 加法交换律（9 case 穷举）
⊕-comm : ∀ x y → x ⊕ y ≡ y ⊕ x

-- 加法单位元
⊕-identityˡ : ∀ x → T₀ ⊕ x ≡ x
⊕-identityʳ : ∀ x → x ⊕ T₀ ≡ x

-- 加法逆元
⊕-inverse : ∀ x → x ⊕ negate x ≡ T₀

-- 乘法结合律（27 case 穷举）
⊗-assoc : ∀ x y z → (x ⊗ y) ⊗ z ≡ x ⊗ (y ⊗ z)

-- 乘法交换律（9 case 穷举）
⊗-comm : ∀ x y → x ⊗ y ≡ y ⊗ x

-- 乘法单位元
⊗-identityˡ : ∀ x → T₁ ⊗ x ≡ x
⊗-identityʳ : ∀ x → x ⊗ T₁ ≡ x

-- 分配律（27 case 穷举）
⊗-distribˡ-⊕ : ∀ x y z → x ⊗ (y ⊕ z) ≡ (x ⊗ y) ⊕ (x ⊗ z)
⊗-distribʳ-⊕ : ∀ x y z → (x ⊕ y) ⊗ z ≡ (x ⊗ z) ⊕ (y ⊗ z)
```

---

## 二、GF(3)* — 乘法群

### 结构

- **载体**: `{T₁, T₂}`
- **乘法**: `_⊗_`（限制到非零元素）
- **阶**: |GF(3)*| = 2

### 公理（已证）

```agda
-- GF(3)* 是循环群 ⟨T₂⟩，阶 2
-- T₂² = T₂ ⊗ T₂ = T₁（单位元）

-- 自逆性
⊗-self-inverse : ∀ x → x ⊗ x ≡ T₁
⊗-self-inverse T₁ = refl
⊗-self-inverse T₂ = refl
```

---

## 三、GF(9) — 二次扩张域

### 结构

- **载体**: `GF9 = GF3 × GF3`（即 `(a, b) = a + bα`）
- **加法**: 分量分别加
- **乘法**: `(a+bα)(c+dα) = (ac-bd) + (ad+bc)α`（因为 α² = -1）
- **单位元**: `gf9-one = (T₁, T₀)`
- **特征**: char = 3

### 关键元素

```agda
-- α 满足 α² = -1 ≡ T₂ (mod 3)
alpha : GF9
alpha = T₀ , T₁

-- α 的阶 = 4
alpha-powers-4 : (alpha *gf9 alpha) *gf9 (alpha *gf9 alpha) ≡ gf9-one
alpha-powers-4 = refl
```

---

## 四、GF(9)* — 乘法群

### 结构

- **阶**: |GF(9)*| = 8
- **生成元**: φ = 1+2α（阶 8）
- **子群链**: ⟨-1⟩ ⊂ ⟨α⟩ ⊂ ⟨φ⟩

### 子群 ⟨α⟩（4 阶循环群）

```agda
-- ⟨α⟩ = {1, α, α², α³} = {a0, a1, a2, a3}
-- 这就是 DuodecClock 的第二分量

AlphaPower = {a0, a1, a2, a3}
mulAlpha : AlphaPower → AlphaPower → AlphaPower
-- （已证结合律、单位元、逆元、周期 4）
```

---

## 五、DuodecPoint — 本源十二进制群

### 结构

- **载体**: `DuodecPoint = Trit × AlphaPower`
- **运算**: `mixedOp = ⊕ × mulAlpha`
- **单位元**: `duodec-e = (T₀, a0)`
- **逆元**: `duodec-inv (x,a) = (negate x, alphaInv a)`
- **阶**: |DuodecPoint| = 3 × 4 = 12

### 公理（已证）

```agda
-- 结合律
mixedOp-assoc : ∀ p q r → mixedOp (mixedOp p q) r ≡ mixedOp p (mixedOp q r)

-- 交换律
mixedOp-comm : ∀ p q → mixedOp p q ≡ mixedOp q p

-- 单位元
mixedOp-identityˡ : ∀ p → mixedOp duodec-e p ≡ p
mixedOp-identityʳ : ∀ p → mixedOp p duodec-e ≡ p

-- 逆元
mixedOp-inverse : ∀ p → mixedOp p (duodec-inv p) ≡ duodec-e
```

### 性质

- **无零因子**：因为 `mulAlpha` 来自域子群，`Trit` 的乘法零只在乘以 `T₀` 时出现
- **周期 12**：`mixedOp^12 = id`（3 步 ⊕ 归零 × 4 步 α 归零 = LCM(3,4)=12）

---

## 六、C₁₂ — 加法投影群

### 结构

- **载体**: `Duodec = {d0, …, d11}`
- **运算**: `+12`（后继链模 12）
- **单位元**: `d0`
- **逆元**: `neg12`
- **阶**: |C₁₂| = 12

### 公理（已证）

```agda
-- 周期 12
+1^12-id : ∀ x → +1^12 x ≡ x

-- 结合律（12 case × 12 case = 144 case）
+12-assoc : ∀ x y z → (x +12 y) +12 z ≡ x +12 (y +12 z)

-- 交换律（144 case 穷举）
+12-comm : ∀ x y → x +12 y ≡ y +12 x

-- 单位元
+12-identityˡ : ∀ x → d0 +12 x ≡ x
+12-identityʳ : ∀ x → x +12 d0 ≡ x

-- 逆元（12 case）
+12-inverse : ∀ x → x +12 neg12 x ≡ d0
```

### 与 DuodecPoint 的关系

```agda
-- 群同构
toDuodec : DuodecPoint → Duodec
fromDuodec : Duodec → DuodecPoint

-- 往返恒等
duodec-clock-roundtrip : ∀ n → toDuodec (fromDuodec n) ≡ n
clock-duodec-roundtrip : ∀ p → fromDuodec (toDuodec p) ≡ p

-- 运算投影
mixed-to-+12 : ∀ p q → toDuodec (mixedOp p q) ≡ toDuodec p +12 toDuodec q
```

---

## 七、R₁₂ — 零因子环

### 结构

- **载体**: `Duodec = {d0, …, d11}`
- **加法**: `+12`
- **乘法**: `*12`（整数模 12 乘法，**不是** mulAlpha 的投影）
- **单位元 (加法)**: `d0`
- **单位元 (乘法)**: `d1`
- **特征**: 非域（有零因子）

### 零因子

```agda
zero-divisor-2×6 : d2 *12 d6 ≡ d0  -- 2×6 = 0 (mod 12)
zero-divisor-3×4 : d3 *12 d4 ≡ d0  -- 3×4 = 0 (mod 12)

-- 证据：d2 ≠ d0, d6 ≠ d0, 但 d2 *12 d6 ≡ d0
not-a-field : Σ Duodec (λ a → Σ Duodec (λ b → a *12 b ≡ d0))
not-a-field = d2 , (d6 , refl)
```

### 单位群

```agda
-- (R₁₂)* = {1, 5, 7, 11} ≅ V₄ (Klein 四元群)
DuodecUnit = {u1, u5, u7, u11}

u5² : u5 *u u5 ≡ u1   -- 5² = 25 ≡ 1 (mod 12)
u7² : u7 *u u7 ≡ u1   -- 7² = 49 ≡ 1 (mod 12)
u11² : u11 *u u11 ≡ u1  -- 11² = 121 ≡ 1 (mod 12)
```

### 为什么不是域

R₁₂ 有零因子，所以**不是域**。  
GF(12) 不存在（12 不是素数幂）。

---

## 八、CRT 分解

### 定理

\[
\mathbb{Z}/12\mathbb{Z} \cong \mathbb{Z}/3\mathbb{Z} \times \mathbb{Z}/4\mathbb{Z}
\quad\text{因为}\quad \gcd(3,4)=1
\]

### 代码

```agda
-- 投影
π3 : Duodec → Trit
π4 : Duodec → Fin 4

-- 重构
crt12 : Trit → Fin 4 → Duodec

-- 往返恒等
crt12-roundtrip : ∀ x → crt12 (π3 x) (π4 x) ≡ x

-- 投影同态
π3-homo-+ : ∀ x y → π3 (x +12 y) ≡ π3 x ⊕ π3 y
π3-homo-* : ∀ x y → π3 (x *12 y) ≡ π3 x ⊗ π3 y
```

---

## 九、层次对比

| 层 | 载体 | 加法 | 乘法 | 零因子 | 特征 |
|----|------|------|------|--------|------|
| GF(3) | Trit | ⊕ | ⊗ | 无 | char=3 |
| GF(3)* | {T₁,T₂} | — | ⊗ | — | 阶 2 |
| GF(9) | GF3×GF3 | 分量加 | 域乘 | 无 | char=3 |
| GF(9)* | 8 元 | — | 域乘 | — | 阶 8 |
| ⟨α⟩ | AlphaPower | — | mulAlpha | 无 | 阶 4 |
| **DC** | **Trit × ⟨α⟩** | **mixedOp** | — | **无** | **阶 12** |
| C₁₂ | Duodec | +12 | — | — | 阶 12 |
| R₁₂ | Duodec | +12 | *12 | **有** | 环 |
| Doz | 数字串 | 位加 | 位乘 | — | 位值制 |
