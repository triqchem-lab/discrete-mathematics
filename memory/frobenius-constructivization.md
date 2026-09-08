# Frobenius 构造化范式 (GF(3^n) 有限域)

> 沉淀于 2026-09-09。来源: GF729Field → GF27 → GF81 → GF243 四模块 frobenius-is-cube 构造化。

## 问题: refl 穷举不是构造性证明

`frobenius-is-cube : ∀ x → frobenius x ≡ x³` 在 GF(3^n) 上原本用 **3^n 条 refl 穷举**
(GF27: 27 条, GF81: 81 条, GF243: 243 条, GF729: 729 条)。这是暴力计算:
- 编译期逐点求值, 不含数学论证
- 模块体积膨胀 (GF729 1910 行中 730 行是枚举)
- 无法迁移到更高维 (GF2187 会是 2187 条)

**判定标准**: 穷举 ≤ 27 case 可接受 (GF(3) 环公理); 81/243/729 必须符号化。

## 范式: 线性/半线性框架 + 基展开

有限域 GF(3^n) 是 GF(3) 上的 n 维向量空间。若两个映射都是 GF(3)-线性的,
且在基 {1, α, α², …, α^(n-1)} 上一致, 则全域相等。

```
record Lin (f : F → F) : Set where
  field ladd : ∀ a b → f (a + b) ≡ f a + f b      -- 加法性
        lscalar : ∀ c w → f (c · w) ≡ c · f w     -- 标量性 (GF3)
```

**关键简化 (GF81/GF243)**: GF(3) 标量 = 重复加法 (0/1/2 倍), 故 `lscalar` 可由
`ladd` 导出, 无需坐标级标量提取证明:

```agda
lscalar-der f ladd T₀ w = f0-zero f ladd      -- f 0 ≡ 0 (幂等消去)
lscalar-der f ladd T₁ w = refl
lscalar-der f ladd T₂ w = ladd w w
```

**框架三件套**:
1. `record Lin/Lin27/Lin81/Lin243` (只含 ladd, 或 ladd+lscalar)
2. `expandN : Linear f → f (a,b,…) ≡ a·f(1) + (b·f(α) + …)` — 用基分解 `decompN`
3. `linear-extN : Linear f → Linear g → 基上一致 → ∀ x → f x ≡ g x`

**证明链**:
```
cube-add (Freshman's dream, 特征3)  ─┐
cube-scalar (立方映射保标量)        ─┼→ Lin cubeMap
frobenius-add (σ 保加)             ─┐
frobenius-scalar (σ 保标量)        ─┼→ Lin frobenius
                                    ↓
frobenius-is-cube = linear-extN frobenius cubeMap LF LC refl…
```

**frobenius-mul 由 cube 导出** (不独立硬算):
```
σ(xy) = (xy)³ = x³y³ = σx·σy   [需结合律 + 交换律]
经 cube-mul + mul-square + mul-perm 三步
```

## 各模块规模与结果

| 模块 | 维度 | 基 | 穷举删除 | 框架 | 提交 |
|------|------|----|---------|------|------|
| GF729Field | 3 (GF9-系数) | {1,t,t²} | 729 → 0 | Semilinear (σ 不固定 GF9) | 6c63f6a |
| GF27 | 3 | {1,α,α²} | 27 → 0 | Linear27 (ladd+lscalar) | b409a9b |
| GF81 | 4 | {1,α,α²,α³} | 81 → 0 | Lin81 (ladd 导出 lscalar) | 91f1644 |
| GF243 | 5 | {1,α,α²,α³,α⁴} | 243 → 0 | Lin243 (ladd 导出 lscalar) | f1b0551 |

**GF729Field 特殊**: 系数域是 GF9 而非 GF3, σ 不固定 GF9 (σ(c)=c³≠c),
故用 `Semilinear` (sscalar: f(c·x) ≡ σ(c)·f(x)) 而非 `Linear`。

## 前置条件: 乘法结合律

`cube-add` 的展开必然用到 `*gf-assoc`。GF27/81/243 原本只证了交换律和分配律
(都在 Poly 层证), **结合律缺失**。用同一线性框架三级嵌套闭合:
- z-层: 固定基 b1,b2, 对 z 线性扩展
- y-层: 固定基 b1, 对 y 线性扩展
- x-层: 对 x 线性扩展 → `*gf-assoc`

基三元组数: GF27 27 个, GF81 64 个, GF243 125 个 (全是 refl, 因基元素乘积已约化)。

## 工程陷阱 (踩过的坑)

1. **`let` 绑定破坏归约**: 域乘法/坐标映射必须 let-free 直接模式匹配,
   否则复合项上的 `cong` 失败 (详见 proof-engineer 附录 10)。
2. **裸 `cong₂ _+gf_` 在复合项上失败**: 需显式标注 λ
   `cong-+N p q = cong₂ (λ (u v : F) → u +gfN v) p q`。
3. **`sym` 方向**: `*gf-assoc a b c` 给 `(a·b)·c ≡ a·(b·c)`,
   首步用 `sym` 还是裸用要看清目标方向。
4. **零乘需要显式引理**: `T₀ *s x` 归约成 `gf-zero`, 但 `gf-zero *gf y`
   不会自动归约成 `gf-zero`, 需 `zero-mul-l/r` (由幂等消去 + 分配律导出)。
5. **标量作用展开**: `T₂ *s w` = `w +gf w`, 不是简单坐标替换, 需 `two-mul-sq` 等桥接。

## 验证协议 (每模块)

1. 草稿模块编译绿 (不动原文件)
2. 对抗验证: 具体点 (原点/生成元/混合点/同态/结合律) 上构造性定理实例
   与独立 `refl` 计算交叉比对
3. 合并回原文件 + 删穷举 + 编译绿
4. 下游模块 (TowerConnection) 编译绿
5. 0 postulate / 0 hole / 0 sorry 审计
6. 全库 `check_all_modules_parallel.sh` 绿
7. 提交 (附验证证据)
