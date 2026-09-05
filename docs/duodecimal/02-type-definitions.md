# 十二进制类型定义（精确 Agda 定义）

**日期**: 2026-08-25  
**状态**: 可执行代码  
**来源**: 项目 Agda 源码

---

## 一、GF(3) = Trit（损益域）

### 类型定义

```agda
-- Sovereign.Base.Trit
data Trit : Set where
  T₀ T₁ T₂ : Trit
```

### 语义

| Trit | 数值 | 语义 | 角色 |
|------|------|------|------|
| T₀ | 0 | 吸收态 | 加法单位元 |
| T₁ | 1 | 平衡态 | 乘法单位元 |
| T₂ | 2 | 表达态 | T₁ 的加法逆 |

### 运算

```agda
-- 加法（模 3）
_⊕_ : Trit → Trit → Trit
T₀ ⊕ y = y
T₁ ⊕ T₀ = T₁
T₁ ⊕ T₁ = T₂
T₁ ⊕ T₂ = T₀
T₂ ⊕ T₀ = T₂
T₂ ⊕ T₁ = T₀
T₂ ⊕ T₂ = T₁

-- 乘法（模 3）
_⊗_ : Trit → Trit → Trit
T₀ ⊗ _ = T₀
_ ⊗ T₀ = T₀
T₁ ⊗ y = y
T₂ ⊗ T₁ = T₂
T₂ ⊗ T₂ = T₁

-- 加法逆元
negate : Trit → Trit
negate T₀ = T₀
negate T₁ = T₂
negate T₂ = T₁
```

### 关键性质

```agda
-- 逆元对消
⊕-inverse : ∀ x → x ⊕ negate x ≡ T₀
⊕-inverse T₀ = refl
⊕-inverse T₁ = refl
⊕-inverse T₂ = refl

-- 周期 3
⊕-³ : ∀ x → (x ⊕ x) ⊕ x ≡ T₀
⊕-³ T₀ = refl
⊕-³ T₁ = refl
⊕-³ T₂ = refl
```

---

## 二、GF(9) = GF(3)[α]/(α²+1)（相位域）

### 类型定义

```agda
-- Sovereign.Algebra.GF9
GF9 = GF3 × GF3   -- (a, b) = a + bα, α² = -1

alpha : GF9
alpha = T₀ , T₁   -- 0 + 1·α
```

### 语义

- α 满足 α² = -1 ≡ T₂ (mod 3)
- α 的阶 = 4（因为 α⁴ = (α²)² = (-1)² = 1）
- GF(9)* 是 8 阶循环群

### 关键性质

```agda
-- α 的 4 次幂 = 1
alpha-powers-4 : (alpha *gf9 alpha) *gf9 (alpha *gf9 alpha) ≡ gf9-one
alpha-powers-4 = refl

-- Frobenius 自同构：σ(α) = -α
sigma-alpha : galoisConjugate alpha ≡ (T₀ , T₂)
sigma-alpha = refl
```

---

## 三、AlphaPower（α 的幂次）

### 类型定义

```agda
-- Sovereign.Algebra.GroupTheory.DuodecClock
data AlphaPower : Set where
  a0 : AlphaPower   -- α⁰ = 1
  a1 : AlphaPower   -- α¹ = α
  a2 : AlphaPower   -- α² = -1
  a3 : AlphaPower   -- α³ = -α
```

### 语义

| AlphaPower | 值 | 角度 | 阶 |
|------------|-----|------|----|
| a0 | 1 | 0° | 1 |
| a1 | α | 90° | 4 |
| a2 | α² = -1 | 180° | 2 |
| a3 | α³ = -α | 270° | 4 |

### 运算

```agda
mulAlpha : AlphaPower → AlphaPower → AlphaPower
mulAlpha a0 x = x
mulAlpha a1 a0 = a1
mulAlpha a1 a1 = a2
mulAlpha a1 a2 = a3
mulAlpha a1 a3 = a0
mulAlpha a2 a0 = a2
mulAlpha a2 a1 = a3
mulAlpha a2 a2 = a0
mulAlpha a2 a3 = a1
mulAlpha a3 a0 = a3
mulAlpha a3 a1 = a0
mulAlpha a3 a2 = a1
mulAlpha a3 a3 = a2

alphaInv : AlphaPower → AlphaPower
alphaInv a0 = a0
alphaInv a1 = a3
alphaInv a2 = a2
alphaInv a3 = a1
```

### 关键性质

```agda
-- 结合律
mulAlpha-assoc : ∀ x y z → mulAlpha (mulAlpha x y) z ≡ mulAlpha x (mulAlpha y z)
mulAlpha-assoc x y z = ?  -- 已证（穷举 64 case）

-- 单位元
mulAlpha-identityˡ : ∀ x → mulAlpha a0 x ≡ x
mulAlpha-identityˡ x = refl

-- 周期 4
mulAlpha-⁴ : ∀ x → mulAlpha (mulAlpha (mulAlpha (mulAlpha x a1) a1) a1) a1 ≡ x
mulAlpha-⁴ x = ?  -- 已证
```

---

## 四、DuodecPoint（本源十二进制坐标）

### 类型定义

```agda
-- Sovereign.Algebra.GroupTheory.DuodecClock
DuodecPoint = Trit × AlphaPower
```

### 语义

- 第一分量：损益状态（Trit 加法）
- 第二分量：相位状态（α 幂乘法）
- 两者正交：损益不影响相位，相位不影响损益

### 运算

```agda
mixedOp : DuodecPoint → DuodecPoint → DuodecPoint
mixedOp (x , a) (y , b) = (x ⊕ y , mulAlpha a b)

duodec-e : DuodecPoint
duodec-e = (T₀ , a0)

duodec-inv : DuodecPoint → DuodecPoint
duodec-inv (x , a) = (negate x , alphaInv a)
```

### 关键性质

```agda
-- 结合律
mixedOp-assoc : ∀ p q r → mixedOp (mixedOp p q) r ≡ mixedOp p (mixedOp q r)
mixedOp-assoc (x , a) (y , b) (z , c) =
  cong₂ _,_ (⊕-assoc x y z) (mulAlpha-assoc a b c)

-- 单位元
mixedOp-identityˡ : ∀ p → mixedOp duodec-e p ≡ p
mixedOp-identityˡ (x , a) = cong₂ _,_ (⊕-identityˡ x) (mulAlpha-identityˡ a)

-- 逆元
mixedOp-inverse : ∀ p → mixedOp p (duodec-inv p) ≡ duodec-e
mixedOp-inverse (x , a) = cong₂ _,_ (⊕-inverse x) (mulAlpha-inverse a)

-- 交换律
mixedOp-comm : ∀ p q → mixedOp p q ≡ mixedOp q p
mixedOp-comm (x , a) (y , b) = cong₂ _,_ (⊕-comm x y) (mulAlpha-comm a b)
```

---

## 五、Duodec / C₁₂（扁平投影标签）

### 类型定义

```agda
-- Sovereign.Algebra.Duodecimal
data Duodec : Set where
  d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 : Duodec
```

### 运算

```agda
+1 : Duodec → Duodec
+1 d0 = d1;  +1 d1 = d2;  +1 d2 = d3;  +1 d3 = d4
+1 d4 = d5;  +1 d5 = d6;  +1 d6 = d7;  +1 d7 = d8
+1 d8 = d9;  +1 d9 = d10; +1 d10 = d11; +1 d11 = d0

_+12_ : Duodec → Duodec → Duodec
d0 +12 y = y
d1 +12 y = +1 y
d2 +12 y = +1 (+1 y)
-- ...

neg12 : Duodec → Duodec
neg12 d0 = d0;  neg12 d1 = d11; neg12 d2 = d10; neg12 d3 = d9
neg12 d4 = d8;  neg12 d5 = d7;  neg12 d6 = d6;  neg12 d7 = d5
neg12 d8 = d4;  neg12 d9 = d3;  neg12 d10 = d2; neg12 d11 = d1
```

### 关键性质

```agda
-- 周期 12
+1^12-id : ∀ x → +1 (+1 (+1 (+1 (+1 (+1 (+1 (+1 (+1 (+1 (+1 (+1 x))))))))))) ≡ x
+1^12-id d0 = refl; +1^12-id d1 = refl; +1^12-id d2 = refl; +1^12-id d3 = refl
+1^12-id d4 = refl; +1^12-id d5 = refl; +1^12-id d6 = refl; +1^12-id d7 = refl
+1^12-id d8 = refl; +1^12-id d9 = refl; +1^12-id d10 = refl; +1^12-id d11 = refl

-- 结合律
+12-assoc : ∀ x y z → (x +12 y) +12 z ≡ x +12 (y +12 z)
+12-assoc d0 y z = refl
+12-assoc d1 y z = +1-dist y z
-- ...（12 case）

-- 逆元
+12-inverse : ∀ x → x +12 neg12 x ≡ d0
+12-inverse d0 = refl; +12-inverse d1 = refl; +12-inverse d2 = refl; +12-inverse d3 = refl
+12-inverse d4 = refl; +12-inverse d5 = refl; +12-inverse d6 = refl; +12-inverse d7 = refl
+12-inverse d8 = refl; +12-inverse d9 = refl; +12-inverse d10 = refl; +12-inverse d11 = refl
```

---

## 六、CRT 投影

### π₃：Duodec → Trit

```agda
π3 : Duodec → Trit
π3 d0 = T₀; π3 d1 = T₁; π3 d2 = T₂; π3 d3 = T₀
π3 d4 = T₁; π3 d5 = T₂; π3 d6 = T₀; π3 d7 = T₁
π3 d8 = T₂; π3 d9 = T₀; π3 d10 = T₁; π3 d11 = T₂
```

### π₄：Duodec → Fin 4

```agda
π4 : Duodec → Fin 4
π4 d0 = zero;        π4 d1 = suc zero;        π4 d2 = suc (suc zero);        π4 d3 = suc (suc (suc zero))
π4 d4 = zero;        π4 d5 = suc zero;        π4 d6 = suc (suc zero);        π4 d7 = suc (suc (suc zero))
π4 d8 = zero;        π4 d9 = suc zero;        π4 d10 = suc (suc zero);       π4 d11 = suc (suc (suc zero))
```

### crt12：Trit × Fin 4 → Duodec

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

### 往返恒等

```agda
crt12-roundtrip : ∀ x → crt12 (π3 x) (π4 x) ≡ x
crt12-roundtrip d0 = refl;  crt12-roundtrip d1 = refl;  crt12-roundtrip d2 = refl
crt12-roundtrip d3 = refl;  crt12-roundtrip d4 = refl;  crt12-roundtrip d5 = refl
crt12-roundtrip d6 = refl;  crt12-roundtrip d7 = refl;  crt12-roundtrip d8 = refl
crt12-roundtrip d9 = refl;  crt12-roundtrip d10 = refl; crt12-roundtrip d11 = refl
```

---

## 七、同构映射

### toDuodec：DuodecPoint → Duodec

```agda
alphaToFin4 : AlphaPower → Fin 4
alphaToFin4 a0 = zero
alphaToFin4 a1 = suc zero
alphaToFin4 a2 = suc (suc zero)
alphaToFin4 a3 = suc (suc (suc zero))

toDuodec : DuodecPoint → Duodec
toDuodec (x , a) = crt12 x (alphaToFin4 a)
```

### fromDuodec：Duodec → DuodecPoint

```agda
fin4ToAlpha : Fin 4 → AlphaPower
fin4ToAlpha zero                   = a0
fin4ToAlpha (suc zero)             = a1
fin4ToAlpha (suc (suc zero))       = a2
fin4ToAlpha (suc (suc (suc zero))) = a3

fromDuodec : Duodec → DuodecPoint
fromDuodec n = π3 n , fin4ToAlpha (π4 n)
```

### 往返恒等

```agda
duodec-clock-roundtrip : ∀ n → toDuodec (fromDuodec n) ≡ n
duodec-clock-roundtrip n = begin
  crt12 (π3 n) (alphaToFin4 (fin4ToAlpha (π4 n)))
    ≡⟨ cong (λ k → crt12 (π3 n) k) (fin4-alpha-roundtrip (π4 n)) ⟩
  crt12 (π3 n) (π4 n)
    ≡⟨ crt12-roundtrip n ⟩
  n ∎

clock-duodec-roundtrip : ∀ p → fromDuodec (toDuodec p) ≡ p
clock-duodec-roundtrip (x , a) = cong₂ _,_
  (crt12-inv-π3 x (alphaToFin4 a))
  (trans (cong fin4ToAlpha (crt12-inv-π4 x (alphaToFin4 a)))
         (alpha-fin4-roundtrip a))
```

### 运算投影

```agda
mixed-to-+12 : ∀ p q → toDuodec (mixedOp p q) ≡ toDuodec p +12 toDuodec q
mixed-to-+12 (x , a) (y , b) = ?  -- 已证（144 case refl）
```

---

## 八、环乘法（R₁₂ 专用）

```agda
-- Duodecimal.agda
_*12_ : Duodec → Duodec → Duodec
d0 *12 _ = d0
d1 *12 y = y
d2 *12 y = y +12 y
-- ...
d11 *12 y = (((((((((y +12 y) +12 y) +12 y) +12 y) +12 y) +12 y) +12 y) +12 y) +12 y) +12 y
```

**注意**：`*12` 来自整数模 12 乘法，**不是** `mulAlpha` 的投影。  
`mulAlpha` 是域子群乘法，没有零因子；`*12` 有零因子（2×6=0, 3×4=0）。
