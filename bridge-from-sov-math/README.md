# bridge-from-sov-math — 从 sov-math（cpp/rust/hs）C ABI 反推的形式化

本目录由 sov-math C ABI 的核对与修复工作产生，**不属于上游跟踪树**，供 review 后合并。
迁移方案见 [`PATCHES.md`](PATCHES.md)。

## 模块清单

| 模块 | 状态 | 内容 |
|---|---|---|
| `RotBridge.agda` | ✅ exit 0，0 postulate/0 hole | GF(3) 矩阵桥 `Rot : ⟨α⟩ → ⟨R⟩`；`R = [[0,2],[1,0]]`；`Rot-hom`（16/16 refl）、`Rot-injective`、`R²≡2I`、`R⁴≡I`、`det R ≡ 1`（⇒ SL(2,3)=2A₄）；§6 给 ℓ=1 三重态骨架 |
| `HopfSpinLift.agda` | ✅ exit 0，0 postulate/0 hole | A₄ → 2A₄ 自旋提升：`SpinTotal = TotalSpace × GF(3)²`、`phaseAct`、`phaseAct⁴≡id-inst`（实例化 `g₀ = A4.Flip zero`，**无参数假设**）、`phase-equivariant`（保 A₄ 轨道） |
| `DigitalRootClassic.agda` | ✅ exit 0，0 postulate/0 hole | 经典数字根 `classicRoot`（9↦9）+ 与上游 `digitalRoot`（n%9）的精确关系 + 幂等/周期 + ABI 语义 `abiRoot ≡ classicRoot`（46 个签名，含 8 条模 9 枢纽） |
| `DayanNatFix.agda` | ✅ exit 0，0 postulate/0 hole | 大衍修正形（系数取模）+ 上游三义务全证（`init-invariant`/`step-invariant`/`terminate-correct`/`dayan-correct`）+ 原版内核级反例 `¬ (3·乘率(3,5) ≡ 1 mod 5)` |
| `NSE6Axis.agda` | ✅ exit 0，0 postulate/0 hole | NSE Q5 修复：6 轴 `div6`/`grad6`/`laplacian6`；`div-grad6 = refl`；判别引理 `laplacian6≢laplacian3Replica`、`div6≢div3Replica`、`laplacian6-not-identically-zero`（证明「refl 不证轴分配正确」） |
| `Ring3pow11.agda` | ✅ exit 0，0 postulate/0 hole | Z/3¹¹ 环：`toℕ`/`repr` 互逆（全域）、`add`/`mul` 值语义、**交换/结合/单位/逆/左右分配全给**；核心引理 `split3`（模 3^{k+1} 余数 = 最低位 + 3·高位余数）；配套 `oracle_ring_z3_11.py`（domain 177147 = points 177147） |
| `SpecAnchor.agda` | 🗂 早期锚点草稿 | — |

## 编译命令（全部模块通用）

```bash
cd /data/work/discrete-mathematics
agda --guardedness -i bridge-from-sov-math -i src \
     -i /data/work/functional-programming/agda-stdlib/src \
     bridge-from-sov-math/<模块>.agda
```

## 关键诚实边界（各模块自报）

- **数字根**：上游 `DigitalRoot.agda` 文件层面仍未改（本模块是桥不是补丁）；未做经典版加性/乘性同态。
- **大衍**：整术**终止性**（`rt` 严格递减，上游 roadmap S-D3）未证；12231/12231 是 Python oracle 事实，不是 Agda 定理。
- **NSE**：上游全局前提 `Δ ≡ T₀` 可满足性为假 ⇒ 该条件式定理空洞；真正可用的是逐场版
  （前提 `Δ₆(div₆ v) ≡ 0`）；`adv6`/Leray 投影/Δ 秩-核维数未做；GF(3) 幅度层结论**不可**外推到相位层。
- **自旋提升**：`SpinTotal` 是 GF(3) 上的平凡自旋丛；未处理非平凡转移函数（S² 层化）。
- **矩阵桥**：证的是 ⟨α⟩ ≅ ⟨R⟩ ⊂ SL(2,ℤ)，不是 SO(2)/球谐的连续实现等价。

## 与 sov-math 的关系

这些模块是 C ABI 语义的形式化背书（`docs/abi.md` §9 强验证表的 Agda 锚点）；
ABI 侧的实测证据（全域穷尽、随机差分、负向控制）在 `/home/yanli/work/math/hs/sov-math/engineering/`。
