# 筹算 Agda 化操作手册与规范

> **日期**: 2026-10-04
> **性质**: 操作手册 + 编码规范——筹算方法论在 Agda 类型系统中的应用
> **本体论**: 筹算是**本源**（操作体系），Agda 是**实现载体**——不是"把古董搬进博物馆"，而是发现筹算操作模式与 Agda 类型系统的**结构同构**，用这个同构指导代码设计
> **配套**: 27-crt-original-texts.md（原文）+ 28-dayan-terminology.md（术语）+ DayanState.agda（首个实例）

---

## 一、筹算 Agda 化的原理

### 1.1 结构同构

| 筹算 | Agda | 为什么天然同构 |
|---|---|---|
| **算筹布局**（位值位置重要） | record 字段 / 函数参数位置 | 两者都是**位置敏感**的 |
| **摆放**（置一百四十） | 构造子调用 | 都是**建立状态** |
| **操作**（递互除之/累乘） | 函数应用 / rewrite | 都是**状态转移** |
| **终止**（奇一而止/中位并尽） | 终止谓词 / 归纳基底 | 都是**停止条件** |
| **读数**（左上所得） | 投影函数 | 都是**从状态提取结果** |
| **验算**（并准此） | `refl`（定义性相等检查） | 都是**自证一致性** |

**筹算是最早的"状态机"——Agda 的类型系统可以精确编码状态机。**

### 1.2 两个层面（不可混淆）

| 层面 | 含义 | 状态 |
|---|---|---|
| **层面 1：形式化对象** | 把中国方法作为 Agda 形式化的对象（博物馆式保全） | ✅ SunyiBase, DayanState |
| **层面 2：证明方法论** | 把中国方法作为 Agda 证明和计算的范式（活的传承） | 本手册定义 |

---

## 二、通用筹算 record 规范

### 2.1 标准接口

```agda
record SuanChou (Board : Set) : Set where
  field
    布局 : (⋯ : ℕ) → Board              -- 初始摆盘（立天元/置数）
    操作 : Board → Board                 -- 一步操作（递互除乘/损益/正负加减）
    终止 : Board → Set                   -- 终止判定（奇一而止/中位并尽）
    读数 : Board → ℕ                     -- 从盘面提取结果（左上所得/不满数）
```

### 2.2 命名规范

| 筹算操作 | Agda 命名 | 命名语言 |
|---|---|---|
| 布局/摆盘 | `xxx-init` 或 `布局` | 中文或拼音 |
| 操作/运筹 | `xxx-step` 或 `运筹` | — |
| 终止/截止 | `xxx-terminates` 或 `终止` | — |
| 读数/取结果 | `xxx-result` 或 `读数` | — |

**命名红线**：优先使用中文术语音译或汉字（如 `dayan-init`, `sun`, `yi`, `zhonglvClosure`）——不翻译为西方术语（如 `modInverse`, `closureCondition`）。

---

## 三、已实现实例

### 3.1 大衍求一术（DayanState）✅

```agda
record DayanState : Set where
  field
    left-top     : ℕ    -- 天元一（初始为 1，终止时为乘率）
    left-bottom  : ℕ    -- 递互累乘的结果
    right-top    : ℕ    -- 奇数（初始为奇，终止时为 1）
    right-bottom : ℕ    -- 定母

dayan-init : (奇 定 : ℕ) → DayanState    -- 立天元一于左上，置奇右上，定居右下
dayan-step : (s : DayanState) → ⦃ NonZero (right-top s) ⦄ → DayanState
                                          -- 递互除乘
dayan-terminates : DayanState → Set       -- 奇一而止
dayan-result : DayanState → ℕ             -- 左上所得为乘率
```

**回执**: `bab3a34d` exit 0 ✅

### 3.2 三分损益术（SunyiBase）✅

```agda
-- 损益操作（非状态机——纯函数，因为损益无"盘面"）
sun : ℕ → ℕ     -- sun n = (n*2)/3  损一
yi : ℕ → ℕ      -- yi n = (n*4)/3   益一

-- 十二律精确分数（Frac record，信息完整对象）
record Frac : Set where
  constructor frac
  field
    num : ℕ    -- 分子（2 的幂次累积）
    den : ℕ    -- 分母（3 的幂次累积）

-- SOVEREIGN_LCM 推导（核心贡献）
CLOSURE_NUM = 177147   -- 3¹¹（闭合比分子）
CLOSURE_DEN = 65536    -- 2¹⁶（闭合比分母）
SOVEREIGN_LCM = CLOSURE_NUM * CLOSURE_DEN  -- 11609505792
```

**回执**: `6092a46a` exit 0 ✅

### 3.3 仲吕闭合（ZhonglvClosure + FixedPointQ16）✅

```agda
-- Q16 定点数（禁浮点的合规表示）
Q16 = ℕ  -- 真值 = Q16值 / 65536
SQRT3_Q16 = 113511  -- floor(√3 × 65536)，精确截断

-- 仲吕闭合
zhonglvClosure : ℕ → ℕ
zhonglvClosure acc = (acc * CLOSURE_NUM) / CLOSURE_DEN

-- 闭合验证
zhonglv-30-closes : zhonglvClosure 30 ≡ 81
zhonglv-30-closes = refl  -- 30 × 177147 / 65536 = 81 ✓
```

**回执**: `394fe7f5` / `6592ba95` exit 0 ✅

---

## 四、待实现术的 Agda 设计规范

### 4.1 开方术（少广章 → Pell 方程递推）

**来源**: 《九章算术》少广章——开方术（连续分数/逐次逼近）

**Pell 方程递推**:
```agda
-- Pell 方程 x² - 3y² = 1 的递推生成
-- 初始解: (2, 1) → 4 - 3 = 1 ✓
-- 递推: (x', y') = (2x + 3y, x + 2y)
-- 性质: x'² - 3y'² = x² - 3y² = 1（不变量保持）

pell-init : ℕ × ℕ
pell-init = 2 , 1

pell-step : ℕ × ℕ → ℕ × ℕ
pell-step (x , y) = (2 * x + 3 * y , x + 2 * y)

-- √3 的第 n 个近似 = xₙ / yₙ
-- Q16 表示 = xₙ × 65536 / yₙ
-- n 越大越精确——无限收敛到 √3
```

**解决的问题**: DELTA_Q16 = 113506 的代数推导缺口——用 Pell 递推生成 √3 的任意精度精确分数，不再依赖来源不明的魔数。

**预估**: ~60 行

### 4.2 天元术（测圆海镜 → Σ-witness + ≡-Reasoning）

**来源**: 李冶《测圆海镜》——立天元一（引入未知量）

**天元术三步在 Agda 中的对应**:

| 天元术步骤 | Agda 对应 | 工具 |
|---|---|---|
| **立天元一**（引入未知量） | Σ-type witness / let binding | `Σ ℕ (λ x → P x)` |
| **推演**（从条件推导关系） | ≡-Reasoning 链 | `begin ... ≡⟨⟩ ... ∎` |
| **消元**（消去未知量得结果） | `subst` / `transport` | `subst P eq x` |

**规范**：
```agda
-- 天元术证明模板
-- 第一步：立天元一
--   Agda: Σ ℕ (λ x → ...)

-- 第二步：推演（从已知推导）
--   Agda: ≡⟨⟩ 链

-- 第三步：消元（从方程得结果）
--   Agda: subst / pattern match on refl
```

**预估**: 文档 ~40 行 + 应用模块按需

### 4.3 方程术（九章算术 → 矩阵消元状态机）

**来源**: 《九章算术》方程章——方程术（Gaussian 消元的中国原型，早 1800 年）

**筹算状态机映射**:
```agda
record FangChengBoard : Set where
  field
    matrix : Vec (Vec ℕ n) m    -- 系数矩阵（算筹方阵）
    -- 方程术操作：偏乘/直除（行变换）

fangcheng-step : FangChengBoard → FangChengBoard
-- 偏乘：以某行乘某数
-- 直除：从另一行减去此行（= Gaussian 消元的行减法）
```

**预估**: ~80–120 行

### 4.4 正负术（九章算术 → 有符号数）

**来源**: 《九章算术》方程章——正负术（正负数加减法则，早欧洲 1200 年）

**原文法则**：
> "同名相除，异名相益；正无入负之，负无入正之。"

**Agda 映射**：
```agda
data 正负 : Set where
  正 : ℕ → 正负
  负 : ℕ → 正负
  零 : 正负

-- 正负加法：同名相除（同号绝对值相减），异名相益（异号绝对值相加）
_加_ : 正负 → 正负 → 正负
-- 正负减法：减去正等于加负，减去负等于加正
```

**预估**: ~40 行

---

## 五、编码红线

### 5.1 术语红线

| 规则 | 正确 | 错误 |
|---|---|---|
| 命名 | `dayan-init`, `sun`, `yi`, `zhonglvClosure` | `modInverse`, `closureCondition` |
| 注释 | 中文术语（定母/衍数/奇数/乘率） | 英文翻译（modulus/inverse） |
| 结构 | 保留四格布局/天元一/递互除乘 | 压缩为函数签名 |
| 陈述 | 术文条件 → 乘率性质 | 函数实现 → 模逆元正确性 |

### 5.2 证明红线

| 规则 | 正确 | 错误 |
|---|---|---|
| 正确性证明 | "术文条件满足时左上所得满足乘率×奇≡1(mod 定)" | "此函数计算了模逆元" |
| 正确性证明 | "损益链 11 步后闭合比 = 3¹¹/2¹⁶" | "SOVEREIGN_LCM = 11609505792（定义）" |
| 验证方式 | `refl`（定义性相等）——筹算验算的 Agda 对应 | 事后测试——非类型级验证 |

### 5.3 禁浮点红线

| 场景 | 合规方案 | 违规方案 |
|---|---|---|
| √3 表示 | Pell 递推精确分数 或 Q16 floor 截断 | `sqrt(3.0)`（Float） |
| 精确比较 | ℚ (Data.Rational) 或整数交叉乘 | 浮点 `==` |
| 无理数 | `Sqrt3 = Q(√3)` 代数数 record | `Double` / `Float` |

---

## 六、筹算 Agda 化与项目架构的关系

### 6.1 在五层架构中的位置

| 层 | 筹算 Agda 化模块 | 本体 |
|---|---|---|
| L0 公理 | 损益公理 → SunyiBase | 本源 |
| L1 基座 | DayanState（四格状态）+ FixedPointQ16（定点） | 本源 |
| L2 结构 | SunyiChain（十二律链）+ DayanIter（迭代） | 本源 |
| L3 合成 | ZhonglvClosure（仲吕闭合）+ FangCheng（方程消元） | 投影 |
| L4 应用 | SOVEREIGN_LCM + Pell √3 + 具体计算 | 投影 |

### 6.2 与西方框架的关系

| 维度 | 筹算 Agda 化 | 西方形式化 |
|---|---|---|
| **定义方式** | record（布局+操作+终止+读数） | 函数（输入→输出） |
| **验证方式** | `refl`（筹算验算） | 证明（归纳/推理） |
| **结构保全** | 保留布局/操作/术语/口诀 | 压缩为函数签名 |
| **命名** | 中文术语（定母/衍数/奇数/乘率） | 英文/希腊术语 |
| **来源** | 项目自有（《九章》/《律吕》/《数书》） | 参考（Mathlib/unimath） |

---

## 七、实施路线图

| 优先 | 任务 | 内容 | 依赖 | 行数 |
|---|---|---|---|---|
| ~~1~~ | ~~DayanState~~ | ~~大衍求一术四格状态~~ | — | ✅ proven |
| ~~2~~ | ~~SunyiBase~~ | ~~三分损益基元~~ | — | ✅ proven |
| ~~3~~ | ~~FixedPointQ16~~ | ~~Q16 定点算术~~ | S1a | ✅ proven |
| ~~4~~ | ~~ZhonglvClosure~~ | ~~仲吕闭合~~ | S1b+S2 | ✅ proven |
| **5** | **KaiFang (开方术)** | Pell 递推→√3 精确分数 | 无 | ~60 |
| **6** | **TianYuan (天元术)** | Σ-witness + ≡-Reasoning 规范文档 | 无 | ~40 文档 |
| **7** | **ZhengFu (正负术)** | 有符号数 data + 加减法则 | 无 | ~40 |
| **8** | **FangCheng (方程术)** | 矩阵消元状态机 | jac_Matrix | ~120 |
| **9** | **DayanStep 完整** | 递互除乘的完整转移规则+终止性 | S-D1 ✅ | ~60–100 |
| **10** | **DayanCorrect** | 正确性证明（术文→乘率性质） | S-D2 | ~80–120 |

**优先 5（开方术）直接解决 DELTA_Q16 缺口——最高 ROI。**
