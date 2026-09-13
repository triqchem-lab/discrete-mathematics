# Burnside 块 4：`#orbits` 的判据无关性 + oracle 群段类型错误复盘

**状态**：proven（0 postulate / 0 hole），2026-09-10
**台账节点**：`B.orb.criterion-free` / `B.burnside.any-rep` / `B.burnside.app-dbl`
**回执**：`0b987aeb…`（BurnsideCriterion）｜`7c6d3c89…`（BurnsideInstance）
**oracle 回执**：`93a261e4…`（domain = points = 3700）
**修正的块 3 oracle 回执**：`61f11f56…`（domain = points = 121718，替换失效的 `661a09c3…`）

---

## 一、块 4 结论

块 3 的模块头明写了一条诚实边界：

> 「`#orbits` 的定义取『轨道内 `toℕ` 最小元』作判据 —— 换判据结论不变，本模块不证这一点。」

块 4 把它补上：

```
rep-count-invariant : 任意 r : Fin p → Fin p，若
    ① lands : ∀ x → orbEq (r x) x            （落在 x 自己的轨道内）
    ② const : ∀ {x y} → orbEq x y → r x ≡ r y（只依赖轨道，不依赖轨道内的点）
  则  |{x | r x ≡ x}|  ≡  numOrbits

burnside-any-rep    : n * |{x | r x ≡ x}| ≡ Σ_x |Stab x|      （推论）
```

### 证明骨架

两条条件说明 `r` **在每条轨道上取唯一值** ⇒ `r` 的不动点集 = 「每轨道恰一个代表元」的系统；
`orbRep` 的不动点集也是。两个这样的系统必然等势：

```
φ : {x | r x ≡ x} → {b | orbRep b ≡ b}     x ↦ orbRep x
ψ : {b | orbRep b ≡ b} → {x | r x ≡ x}     b ↦ r b
```

- `φ` 单射：像相同 ⟹ 同轨道 ⟹ `const` 给 `r a ≡ r b` ⟹ `a ≡ b`（两者都是 `r` 的不动点）
- `ψ` 单射：像相同 ⟹ `r a ≡ r b` ⟹ 同轨道 ⟹ `orbRep a ≡ orbRep b` ⟹ `a ≡ b`（两者都是不动代表元）

交给 stdlib `cantor-schröder-bernstein` 收口，不自己写基数搬运。

### 两点设计决定

1. **幂等不作假设**：`r (r x) ≡ r x` 由 `lands + const` 导出
   （`lands` 给 `orbEq (r x) x`，取对称得 `orbEq x (r x)`，再用 `const`）。
   故 `IsRepCriterion` 只有两个字段 —— 假设越少，反例越好找。
2. **`orbRep` 本身是实例**（`orbRep-criterion`）：`burnside-any-rep` 在 `r = orbRep` 处
   退化为块 3 的 `burnside-lemma`。这一条防止「泛化其实是另一个定理」。

### 这不是空定理

| 判据 | 合法？ | 不动点计数 |
|---|---|---|
| `orbRep`（轨道最小元） | ✅ | = `#orbits` |
| 轨道最大元 / 有序中位元 | ✅ | = `#orbits`（oracle 3700 完备核对） |
| `id`（恒等） | 仅当作用平凡 | = `p`，一般 ≠ `#orbits`（**假设必要性反例**） |

`BurnsideInstance.agda §4` 用 `idF` 在平凡作用上做了 refl 交叉验证（`3 ≡ 3`）。

---

## 二、块 4 应用实例：非传递 + 非自由的平移作用

```
t g = 2·(q₂ g) ∈ {0,2} ⊂ Z/4       act g x = x +4 t g
```
即 C₄ 经商 `Z/4 ↠ Z/2` 再嵌入 `2Z/4` 的平移作用。

| 量 | 值 | 独立 refl |
|---|---|---|
| `#orbits` | 2（`{0,2}`、`{1,3}`） | ✅ |
| `Σ_x \|Stab x\|` | 8（每点稳定子 `{0,2}` 阶 2） | ✅ |
| Burnside 实例 | `4 * 2 ≡ 8` | ✅ |

**比块 3 的三个实例更有价值**：块 3 只有 `#orbits ∈ {1, 3}`（传递，或平凡到每点自成一轨）；
本实例是**中间情形**，同时压到「轨道划分 / 共轭拉平 / orbit-stabilizer / 纤维分解」四条链。

### 踩坑记录（纪律）

初版把 `t` 写成 `ι(q₂ g) +4 ι(q₂ g)`，直觉是「在 Z/4 里翻倍」。
但 **`2 +4 2 = 0`** —— `t ≡ 0`，作用退化成平凡作用，`#orbits` 算出 **4** 而非 2。
是 §4 的 `refl` 交叉验证当场挡回的（`numOrbitsOf C4 C4-dbl ≡ 2` 报 `4 与 2 不等`）。
**这正是对抗验证存在的理由**：形式化没有「看起来对」，只有算出来的数。

---

## 三、重要复盘：块 3 oracle 的群段是**空转**的

### 症状

块 4 写 oracle 时输出 `domain = 100`，而块 3 那次是 `120998`。反推：
块 3 的 `domain` 里纤维段贡献 120978，**群段只贡献了 20 条**。

### 根因（类型错误）

```python
def hom_ok(G, gen_imgs):
    for word, target in G.rels:
        r = ident(len(gen_imgs[0]))
        for i in word:
            r = compose(gen_imgs[i], r)      # r : Fin p 的置换
        if r != target:                      # target : 群元素（1-元组 / 置换）
            return False
```

左端折叠出的是 **`Fin p` 的置换**，右端是**硬编码的群元素**。二者类型不同，
几乎恒不相等 ⇒ 所有非平凡关系判定失败 ⇒ 群段几乎枚举不出任何同态。

对 `S3` 更隐蔽：它的元素**本身就是 `Fin 3` 的置换**，所以 `p = 3` 时碰巧能比对上 ——
于是「20 条」里有一部分是巧合，不是正确性。

### 修复

关系两端都写成**生成元字**，各自折叠成 `Fin p` 的置换再比较（空字 = 恒等置换）：

```python
def fold(word, gen_imgs, p):
    r = ident(p)
    for i in word:
        r = compose(gen_imgs[i], r)
    return r

def hom_ok(G, gen_imgs, p):
    return all(fold(lhs, gen_imgs, p) == fold(rhs, gen_imgs, p)
               for lhs, rhs in G.rels)
```
关系表改成 `a^n = ε` ⟹ `((0,)*n, ())`，`(ab)² = ε` ⟹ `((0,1,0,1), ())` 等。

### 修复后的逐群核对（**人工验证，不是「跑通了」**）

| 群 | p=1..5 作用数 | 独立核对 |
|---|---|---|
| C1 | 1,1,1,1,1 | 平凡群只有一个作用 ✅ |
| C2 | 1,2,4,10,26 | Sym(p) 中的对合数 = 1 + C(p,2) + 双对换 ✅ |
| C3 | 1,1,3,9,21 | 阶整除 3 的元素 = 1 + 2·C(p,3) ✅ |
| C4 | 1,2,4,16,56 | p=4 时阶整除 4 = 1 + 9 + 6 = 16 ✅ |
| V4 | 1,4,10,52,196 | 交换对合对 ✅ |
| C5 | 1,1,1,1,25 | 只有 5-轮换（1+24=25）✅ |
| C6 | 1,2,6,18,66 | p=4 时阶整除 6 = 1+9+8 = 18（S₄ 无 6 阶元，4-轮换被正确排除）✅ |
| S3 | 1,2,10,34,146 | — |
| **合计** | **740** | |

### 教训（最重要的一条）

**「回执有效」≠「断言成立」。**
`proof_oracle` 校验的是「脚本跑过、退出 0、points ≥ domain」，
它**不知道** `points` 数的是不是你以为的东西。块 3 的 `120998` 看起来完备，
实际群段空转、纤维段正常 —— 而我的断言文本把两者混在一起写成一句话。

纪律增量：
1. **断言文本要按段拆开写**，每段给各自的 domain，别用一句 `claim` 盖住多段。
2. **每段的 domain 要有独立的量级预期**，对不上就是 bug（本次 100 vs 预期 ≥ 740）。
3. **对枚举出的对象做逐类人工核对**（上表），不要只看「总数通过」。
4. 修脚本会**失效该脚本的所有回执** —— 故块 4 另建 `oracle_burnside_block4.py`
   而不是改块 3 的；但块 3 脚本本身有 bug，只能改了重签 9 个节点。

---

## 四、模块与复用账

| 模块 | 行数 | 内容 | 回执 |
|---|---|---|---|
| `GroupTheory/BurnsideCriterion.agda` | 167 | `IsRepCriterion` / `FixEnum` / `r-idem` / `rep-count-invariant` / `orbRep-criterion` / `burnside-any-rep` | `0b987aeb` |
| `GroupTheory/BurnsideInstance.agda` | 148 | 平移作用实例 + §4 对抗验证 | `7c6d3c89` |

依赖方向（无环）：`BurnsideMain → BurnsideCriterion → BurnsideInstance`（后者为叶）。

复用：`orbEq` / `orbRep` / `orbRep-eq` / `orbRep-idem` / `orbRep-eq-of-eq` / `RepEnum` 全部来自
`OrbitPartition`；CSB 来自 stdlib；`_+4_` / `+4-assoc` / `+4-comm` / `q₂` 来自 `Lagrange`。
**本块真新增只有 `IsRepCriterion` 双向单射与 `t`/`act` 这一组。**

## 五、诚实边界

- 作用仍限**有限集 `Fin p`**（`#orbits` 才有限）。
- 证的是「**合法**判据都给同一个数」，不是「任意判据都给同一个数」——`id` 是显式反例。
- `BurnsideInstance` 的 `t-hom` 是 16-case 穷举（≤27 合规）；`act-⊙` 走代数链而非 64-case 穷举。
- oracle 覆盖阶 ≤ 6 的群；Agda 证明本身对任意 `n` 成立，不依赖 oracle。
- 编译通过 ≠ 物理正确。
