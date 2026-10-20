# 交接：`Ring3pow11` 逐位乘法（**M1–M4 全部完成 ✅**）

> 生成于 2026-10-20（会话交接）。接手请先读本文件 + 跑 `proof_dag action:"brief"`。

## 一、任务

`src/Sovereign/Algebra/RingTheory/Ring3pow11.agda` 中补齐**逐位乘法**，
使 sov-math C ABI 的 `sov_ring_mul`（逐位实现）获得形式化背书。
与**已完成的加法**（§12–§14）对称。

## 二、当前状态（已证 ✓）

| 阶段 | 内容 | 回执 |
|---|---|---|
| M1 | `shiftV` / `shiftV-toℕ` / `allZero` / `allZero-toℕ` | `fa3b9394` |
| 加法全链 | `addCarryV` → `addCarryV-toℕ` → `addCarry≡add` | `2cbc866b` / `3256add4` / `08e847e5` |

模块现有 **21 个 `-- §` 分节**、815 行、**0 postulate / 0 hole** ✓。

## 三、状态：**全部完成 ✅**

```
M1 移位值语义              ✅ fa3b9394
M2 缩放 scaleV + 值语义     ✅ a0c6359d
M3a truncate / shiftMul     ✅ 60060884
M3b 值语义                  ✅ cee5a927
M3c 累加器定义 + 基例        ✅ 53439bdc
M3d 展平引理                ✅ 4d617a3e
M3e Cong 同余关系            ✅ 63154a79
M3f 归纳步（mulGo-key + mulGo-toℕ） ✅ 978b7678
M4 主定理（mulCarry-toℕ + mulCarry≡mul） ✅ 978b7678
```

**最终交付**（回执 `978b7678`，0 postulate / 0 hole）：
```agda
mulGo-toℕ    : toℕ (mulGo a bs acc) ≡ modp (toℕ a * toℕ bs + toℕ acc) k
mulCarry-toℕ : toℕ (mulCarry a b) ≡ modp (toℕ a * toℕ b) k
mulCarry≡mul : mulCarry a b ≡ mul a b            -- 表示层相等（与 §14 的加法同构）
```
⇒ sov-math C ABI 的 `sov_ring_mul`（逐位实现）正确性**形式化背书完成** ✓

**做这件事的关键武器**（都留在模块里可复用）：
`Cong`（§20）/ `modp-*-flatten`（§19）/ `modp-add-cong`·`modp-mul-cong`（§18）/
`shiftMul-toℕ`·`truncate-toℕ`（§17）/ `scaleV-toℕ`（§16）/ `addCarryV-toℕ`（§13）/ `solve`。

## 四、必须遵守的已证技法（本会话踩过的坑，**别再踩**）

1. **`sym` 方向**：本会话在此错了 **6 次**。判据——`lem : A ≡ B`，目标 LHS 是 `A` 用 `lem`，是 `B` 用 `sym lem`。
   **写之前先把四个参数的完整类型签名抄一遍**。
2. **ℕ 上的纯多项式重排一律用 `Data.Nat.Solver` 的 `solve`**（`+-*-Solver`），别手写 `+-assoc`/`*-comm` 链。
   **但** `Algebra.Solver.Ring` 对 ℤ 需要 `RawRing`（不行）；`Data.Nat.Solver` 对 ℕ 开箱即用 ✓。已用 4 次，全部一次过。
3. **`where` 块禁止前向引用**（Agda 硬限制）—— 扁平化，引理全部顶层具名。
4. **`begin` 链首行必须已展开**（本模块的局部 `≡-Reasoning` **没有** `≡⟨⟩` 空步）。
5. **`% pow3 k` 不可用**（`NonZero (pow3 k)` 无实例）—— 一律用 `modp`（定义等价，显式带实例）。
6. **`with` 的 scrutinee 必须是中性项**：`with (suc a * suc b) % 9 ≟ 0` 会因 `_*_` 归约导致抽象失配 ✗；
   用 `dec-split` 包一层（`DigitalRootClassic.agda` §8 有现成写法定式）。
7. **`x * zero` 在中性项上不归约**（`_*_` 匹配第一参）—— 用 `*-zeroʳ`。
8. **`3 * x` 在 ℕ 上归约成 `x + 2 * x`** —— `cong (3 *_)` 才对，`cong (zero +_)` 不匹配。
9. **`Fin` 的 `zero` 与 `Data.Nat.zero` 冲突** —— `renaming (zero to fzero)`；`fsuc` 直接 import。
10. **0 hole 是红线**：起草时写 `{!!}` 也必须**立刻撤下**（WIP ≠ 留洞）。

## 五、参考范式

- **照抄对象**：`agda-stdlib/src/Data/Nat/Binary/{Base,Properties}.agda`
  —— `_+_`/`_*_` 的模式匹配进位递归 + `toℕ-homo-+`/`toℕ-homo-*` 的归纳证明。
  本模块 §12–§14 就是它的 base-3/定长镜像（加法部分）。
- **现成可复用**：`addCarryV` / `addCarryV-toℕ` / `addCarry≡add` / `shiftV` / `allZero`。

## 六、验收

```
agda --guardedness src/Sovereign/Algebra/RingTheory/Ring3pow11.agda   → exit 0
剥注释统计 postulate + {!  = 0
proof_compile 签回执；proof_dag update FORMAL.ring-3pow11 带 receipt
```
