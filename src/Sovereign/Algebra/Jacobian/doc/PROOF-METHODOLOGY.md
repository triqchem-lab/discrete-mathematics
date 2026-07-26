# 离散雅可比猜想——形式化证明思路

## 核心结论

**有限集上，全局函数表矩阵 det(M_F) ≠ 0 ⟺ F 双射。逐点雅可比（形式导数/差分算子）不充分。**

## 三层雅可比强度

```
形式导数 det J (逐点)    → GF(3)²/GF(9)² 反例 (Frobenius 盲区)
  < 差分算子 det J_Δ (逐点) → GF(9)² 反例 (局部→全局 鸿沟)
    < 全局矩阵 det(M_F)     → 精确判定双射 (鸽巢原理, 0 postulate)
```

## 证明链 (全部 0 postulate)

```
det(M_F) ≠ 0
  ⟺ NoZeroRow ∧ ColDistinct        (§1 函数表矩阵结构)
  ⟺ Surj2 F ∧ Inj2 F               (§2 行列性质)
  ⟺ Inj2 F × Surj2 F               (交换)
  ⟺ F 双射                          (pigeonhole-2 + surj→inj)
```

### 关键模块

| 模块 | 角色 | 行数 |
|------|------|------|
| `jac_GF3.agda` | GF(3)² 反例 (形式导数 + 差分算子) | 324 |
| `jac_FrobeniusBlind.agda` | GF(9)² 反例 (Frobenius σ 恒等式) | 284 |
| `jac_Pigeonhole.agda` | 鸽巢原理 Fin 9→8 (REWRITE decode9-encode9) | 325 |
| `jac_Matrix.agda` | 2×2 矩阵全理论 (det-mul, inverse, rank) | 7215 |
| `jac_Injectivity.agda` | 单射↔满射 (右逆构造 + pigeonhole) | 174 |
| `jac_FunctionTable.agda` | 函数表矩阵等价性论证 | 131 |
| `jac_NMatrix.agda` | 9×9 函数表构造 (toTrit, DetNonzero, 0 postulate) | 166 |
| `jac_Conjecture.agda` | 离散 JC 陈述 + 实质定理 | 112 |
| `jac_DiscreteJC.agda` | 三层综合 + 与连续统 JC 关系 | 324 |
| `jac_CRTSpectrum.agda` | CRT 四极 × 矩阵谱 | 606 |
| `jac_4320DClosure.agda` | 729 点鸽巢推广 + 环面有界性 | 408 |

## 关键证明技巧

### 1. Fin 编码 + 标准库 pigeonhole

GF3² (9 点) 双射判定：`encode9/decode9` 双射 + `Data.Fin.Properties.pigeonhole` 直接给 Fin 9→8 碰撞。

```agda
pigeonhole-2 : ∀ F → Inj2 F → Surj2 F
```

### 2. 右逆构造 (Surj → Inj)

```agda
surj→inj : ∀ F → Surj2 F → Inj2 F
surj→inj F surj {p} {q} Fp≡Fq =
  let g x = proj₁ (surj x)                 -- 右逆选择
      F∘g≡id x = proj₂ (surj x)
      g-inj : Inj2 g                       -- g 单射 (F∘g≡id)
      g-surj = pigeonhole-2 g g-inj         -- g 满射 (鸽巢)
      (s , gs≡p) = g-surj p
      (t , gt≡q) = g-surj q
      s≡t = trans (sym (F∘g≡id s)) ...      -- Fp≡Fq → s≡t
  in trans (sym gs≡p) (trans (cong g s≡t) gt≡q)
```

### 3. REWRITE 规则消除 encode9/decode9 环路

`decode9(encode9 p)` 在 Agda 2.9.0 中不可归约（命题等 ≠ 定义等）。
按 T6.agda 模式添加 REWRITE 规则：

```agda
{-# REWRITE decode9-encode9 #-}
```

需要 `open import Agda.Builtin.Equality.Rewrite` 注册 REWRITE 关系。

### 4. toTrit 绕过 with-abstraction

`funcTable` 原定义用 `with` 导致 Agda 无法对命题等式归约。
改为 `toTrit : Dec A → Trit` 函数调用：

```agda
toTrit (yes _) = T₁
toTrit (no  _) = T₀
funcTable F i j = toTrit (encode9 (F (decode9 j)) ≟ i)
```

### 5. 引用已编译模块避免递归超限

对新模块，不重定义 `compress`/`expand`（Fin 递归 >100 层会超时）。
直接 import 已编译的 `jac_Pigeonhole` 版本——Agda 只检查接口签名，不展开函数体。

### 6. ≡-Reasoning + ≤3 层 trans

复杂等式链分离为独立引理，每步一个代数变换。外链引用内链，不超过 3 层 trans。

### 7. 策略选择优先级

| 优先级 | 策略 | 适用场景 |
|--------|------|---------|
| 1 | 代数链 (≤3 trans) | 引理清晰、每步可标注 |
| 2 | 穷举法 (3/9/27 case) | 论域有限 |
| 3 | 分离引理 + 组合 | 复杂证明 |
| 4 | REWRITE | fromℕ< / mod-helper 阻塞 |
| 5 | postulate (仅项目既定模式) | 递归深度 > Agda 限制 |

## 当前状态

- **14 模块, ~10400 行**
- **0 postulate**
- **全部编译通过** (Agda 2.9.0 + stdlib 2.4)
- **入口** `Jacobian.agda` — 0 错误

## 参考

- wiki 02-geometric-pole.md: REWRITE 规则 (div3k/mod3k)
- wiki 17-4320d-holographic-information.md: 4320D 归约 vs βη-归约
- wiki 15-conversion-framework.md: 四极框架等价判定
- proof-engineer 技能: 附录 1-6 (REWRITE, 递归限制, trans 嵌套, fixity, 策略优先级, Fin 深度)
