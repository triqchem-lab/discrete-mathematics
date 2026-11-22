# Frobenius 迭代与 θ-lift 链的离散对译

> 本文回答一个具体问题：Alpöge 证明里长度 ≈ √X 的迭代 θ-lift 链，
> 在 Sovereign 的 GF(3^k) 离散宇宙里的对应物是什么、差在哪里、能不能搬。
> 这是**技术对译**，不是路线宣言；四阶段 Roadmap 见同目录
> `Sovereign-RH-Constructive-Path.md`。

---

## 零、结论先行

**θ-lift 链在离散侧没有「链」——它退化成一次 Frobenius 迭代 σⁿ(x)=x^(3ⁿ)，
重数 m 退化成扩域次数 n，分析误差退化成 0。**
但「对应」不等于「等价」：Alpöge 用链在特征 0 里**造** Frobenius 的功能，
我们的 σ 是域结构**白送**的。因此离散对译的价值不是复刻他的证明，
而是暴露他的链在构造性框架下的**不可替代成本**。

---

## 一、两侧对象的字典

| Alpöge（特征 0，Lean） | Sovereign（GF(3^k)，Agda） | 对应关系 |
|---|---|---|
| θ-lift 链 `chainOp w K m`（m 次复合） | Frobenius 迭代 `σⁿ(x) = x^(3ⁿ)` | **功能对应**：都产生「重数」 |
| 重数 m ≈ √X（Claude 的关键一跳） | 扩域次数 n ∈ ℕ（`FieldExtensionTower`） | 离散侧 m 就是 n，无近似 |
| π ↦ π ⊞ μⱼ[t]（酉群间迭代提升） | GF(3) → GF(3ⁿ) 的塔扩张 | 都是「逐级加层」 |
| `algSat n q B := B.map (λ α ↦ q^((n-1)/2) · α)` 手工注入 √q | `weil-norm-E1 : t1² + 3·2² ≡ 4·q3 = refl` | **本质差异**：他的 √q 是外挂归一化，我们的 √q 编码在 `ℤ[ω]` 范数里 |
| `FrobEig` + `PhiPol` 钉 charPol | `alpha-E1 ∈ Eisenstein`，`norm-product-E1 : α·conj(α) ≡ 3ᵉ` | 都是钉扎 Frobenius 本征值 |
| Rallis seesaw → Bessel 周期与 Hecke 无关 | Frobenius 共轭 `conjᵉ: ω ↔ ω²` 与 σ(x)=x³ 同构 | 离散侧无需 seesaw：共轭是原生对合 |
| Bost 斜率不等式（正性/非退化） | 有限组合事实 `detNonzero ↔ bij` | 离散侧正性是穷举可判的，不需分析 |
| 2^k 分圆塔共轭类 `OrdGrp s = (ZMod 2^(s+2))ˣ ⧸ ±1` | GF(3^k) 上 `Gal(GF(3ⁿ)/GF(3)) ≅ Cₙ` 由 σ 生成 | 他补的是**共轭类的影子**，我们的是**真自同构群** |

来源：Alpöge 侧路径见 `Formalism/ThetaLiftIndependence/Statement.lean`、
`Formalism/BehrendSets/Statement.lean:9-19`、
`Development/AutomorphicArithmetic/Foundations/GaloisRepresentations/IntegralStructures/`
下 `FrobEig`/`PhiPol`/`algSat`；Sovereign 侧见
`src/Sovereign/Application/Problems/RH/WeilRigidity.agda`、
`src/Sovereign/Foundation/Eisenstein.agda`、
`src/Sovereign/Algebra/FieldTower/FieldExtensionTower.agda`。

---

## 二、递推层：t-rec 已经是参数化的

Roadmap 阶段一说「把 q=3 硬编码参数化为 ∀ (p : Prime) (k : ℕ)」。
核查结果是：**递推层已经参数化，卡住的不在这一层**。

`src/Sovereign/Application/Problems/BSD/BSD_L3.agda:27-34`：

```agda
step  : ℤ → ℤ → ℤ → ℤ → ℤ
step q t1 tn1 tn = (t1 * tn1) - (q * tn)

t-rec : ℤ → ℤ → ℕ → ℤ
t-rec q t1 zero       = t1
t-rec q t1 (suc zero) = (t1 * t1) - (+ 2 * q)
t-rec q t1 (suc (suc n)) = step q t1 (t-rec q t1 (suc n)) (t-rec q t1 n)
```

`q` 和 `t1` 都是参数，递推本身对任意整数 q 成立；
硬编码在**实例层**：`q3` / `tE1` / `tE2` / `tE6` 共 109 处 `q3` 引用分布在
RH/BSD 轨道。所以阶段一的真实工作不是「写递推」，而是：

1. 把 `t-rec q t1 n` 的**保范性**证明参数化：现证的是
   `t1²+3s²=4q` 对 q=3 的实例（`weil-norm-E1/E2/E6 = refl`），
   需要一般命题 `∀ q t1 n, ∃ s, (t-rec q t1 n)² + d s² = 4 q^(n+1)` 的形式。
2. 这里有个**数学障碍**：`d=3` 只对 Eisenstein 整数环 `ℤ[ω]` 成立
   （`Eisenstein.agda` 的 `normᵉ (eis a b) = a²−ab+b²` 写死了判别式 −3）。
   推广到任意素数 p 需要换二次虚整数环 `ℤ[√−d]`，类数 ≠ 1 时唯一分解失败——
   **这是阶段一真正的深水区，不是 `forall p k` 一行能解决的**。

---

## 三、离散对译的边界：三件搬不过来的东西

1. **√q 的来源不可搬**。他的 `algSat` 是手工乘 `q^((n-1)/2)`；
   我们的 `√q` 是 `ℤ[ω]` 上 `normᵉ` 的推论（`norm-mul` 已证）。
   把他的链映射到我们的范数方程，第一步就要把外挂归一化因子内化——
   这正是阶段三「不可逆扭曲」的着力点。
2. **m 的取值不可搬**。他的 m ≈ √X 是分析优化（误差与链长的权衡）；
   我们的 n 是代数次数，没有「最优截断」问题。若强行定义
   `m : ℕ → ℕ` 的极限模拟，得到的不是逼近链而是另一个域塔。
3. **非构造性不可搬**（存在争议，见下节）。Lean 侧 23,535 个文件用
   `classical` / `Classical.choice`（占 175,187 的 13%），
   但 `Main.lean`、`Supplements/Kernels/MainTheorems*.lean` 三件主入口
   的 `Classical` 计数是 **0**。因此「他的证明依赖选择公理」这个论断
   在整个仓库层面为真、在主链文件表面为假——必须追到依赖闭包里
   的具体引理才能定论，不能凭顶层文件计数下结论。

---

## 四、创建日期

2026-11-21
