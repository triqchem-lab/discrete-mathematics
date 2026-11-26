# RH 全称化计划：从三曲线实例到 F₃/F₉ 上 ∀ 定理（含原子分解与复用清单）

> 日期：2026-11-24。性质：**提案 + 已开工首件**（A1.1 不依赖批准，纯枚举件）。
> 模式：按 Cook–Levin 线先例（`docs/decisions/Cook-Levin-路线提案-2026-10-30.md`），
> 提案 → 里程碑 → 逐件验收（EXIT=0 + 0 postulate + 0 hole + 回执）。
> 范围红线：本计划交付的都是 **F₃/F₉ 上 Weil 离散 RH 的构造性形式化**（Weil 1948 已证定理），
> **不**声称通往经典 RH；经典 RH 已由 Alpöge Lean 形式化并通过多重独立验证（见
> `Sovereign-RH-Constructive-Path.md` 零·补 F6）。

---

## 一、陈述冻结（oracle 先行，2026-11-24 实测）

一般 Weierstrass 形（特征 3 下 x² 项不可消去）：E(a₂,a₄,a₆): y² = x³ + a₂x² + a₄x + a₆。
判别式 Δ = a₂²a₄² − a₄³ − a₂³a₆（两公式交叉验证一致）。

| 项 | 冻结值 |
|---|---|
| 参数空间 | 27 组 (a₂,a₄,a₆) ∈ GF(3)³ |
| 非奇异 | **18 组**；奇异 9 组（c000/c001/c002/c100/c110/c122/c200/c210/c221） |
| 迹集 | 恰 7 值 {−3,−2,−1,0,1,2,3}；Hasse t² ≤ 12 全部满足 |
| 迹→见证 | −3: c021(=E₂)；−2: c101,c111,c120；−1: c201,c211,c222；0: c010,c011,c012,c020；+1: c102,c112,c121；+2: c202,c212,c220；+3: c022(=E₆) |
| 与旧件衔接 | E₁=c011(t=0)、E₂=c021(t=−3)、E₆=c022(t=+3)——现有三曲线是 18 条的真子集 |

逐组 Δ 表（枚举脚本留档于会话，A1.1 内 27 条 refl 即机器重签）：

```
c000:0 c001:0 c002:0 c010:2 c011:2 c012:2 c020:1 c021:1 c022:1
c100:0 c101:2 c102:1 c110:0 c111:2 c112:1 c120:2 c121:1 c122:0
c200:0 c201:1 c202:2 c210:0 c211:1 c212:2 c220:2 c221:0 c222:1
```

---

## 二、里程碑与原子件（27 件）

### M0 清欠
- **A0.1** 提交 `NoNormT0Even`（已修，含 NoNormPrelude 子模块）+ WeilRigidity 头注勘误。验收：Linux 机 `check_duplicate.sh` 通过。
- **A0.2** 本提案文档落盘（已完成）。

### M1 F₃ 全称化
- **A1.1** `RH/CurveF3.agda`：record + `discF3` + 27 条 Δ refl（**已完成**，见 §四）。
- **A1.2** 同文件：`IsNonSing` + 18 非奇异见证（λ()）+ 9 奇异（refl）（**已完成**）。
- **A1.3** `RH/CountF3.agda`：一般形点计数（27 格点+∞，模式照抄 BSD.agda:64-72 推广为四系数）。
- **A1.4** 同文件：18 条 `#E` 与迹 `t = 4 ∸ #E`（§一逐条表为验收对照）。
- **A1.5** `RH/HasseAllF3.agda`：**∀①** `∀ E → Nonsingular E → t E * t E ≤ 12`（18 case）。
- **A1.6** `RH/TraceTableF3.agda`：迹集 = {−3..3} + 每值见证（§一表）。
- **A1.7a** `RH/ZetaFrame.agda`：把 ZetaFunctional §0（Quad/Quart/recipClear/mulLin/evalE）提取为公共件；原文件改 import，回归绿。
- **A1.7b** `RH/ZetaAllF3.agda`：函数方程 + 零点刚性 ∀ 18 条（复用 A1.7a + Eisenstein norm-mul）。

### M2 ℤ 层全称（独立轨道，不依赖 M1）
- **A2.1** oracle 陈述冻结（✅ `engineering/oracle_rh_tables.py` norm v2）：t²+3s²=4·3ⁿ 解分类（n≤12 全域枚举定案）：
  n=2k+1（奇）t∈{0,±3^(k+1)} 恰三值；n=2k（偶）t∈{±3^k,±2·3^k} 恰四值；解集 = 3·解集(n−2) 递降。
  v1「整除式判据」已被 n=7 反例（t=±2·3⁴）否证——**早先"n=3 时 t=±3 无解 ⟹ 奇不可解"的手算线索是错的**：
  n=3 有解 (t,s)=(±9,±3)，奇 n 恰可解。以此为准。
- **A2.2** `RH/Witness.agda`：`witness : ℕ → ℤ×ℤ` + `witness-satisfies`（见证**范数方程**，头注明示）。
- **A2.3** `RH/NormClassify.agda`：**∀②** 解分类（无穷递降，复用 NoNormPrelude 全套 3-adic 引理）。
  **base0 全称分类已完成**（2026-11-24，exit=0）：16 格全覆盖——12 格枚举（10 absurd + 2 冻结解见证 (1,1)/(2,0)）
  + 4 格 catch-all 反证核（t≥3 / s≥3，全显式签名引理 t3-absurd/hi3s/lo3s/s3-absurd + 9≤4/27≤4 空型）。
  （✅ 已收口 2026-11-24/25: base1/base2 枚举 + 递降核 descent1 全部完成——Mod3Core 基建
  （tri3-split/no-suc-mult3/sq-suc 等）落地后机械收敛; 现状见 §四 A2.3 行。）
  工程勘误入档：2.9.0-nightly 下 ① --cubical absurd 只看顶层构造子（9≤4 须 ≤1↓ 降层到 suc _ ≤ zero）；
  ② 签名级未使用显式参数触发 UnsolvedMetaVariables（探针二分实证；子句级未使用 h 不触发）。
- **A2.4** `RH/NoNormT0General.agda`：t=0 无解谱系并入。现状：偶侧已证 `no-norm-t0-even`/`no-sq-4pow3-odd`，
  奇侧可解已证 `witness-sat`（Witness），**唯一性方向 ✅ 已证**（`t0-odd`: sol n 0 s ⟹ n=2k+1 ∧ s=2·3^k,
  2026-11-25 提交 4379eb6c; Mod3Core 基建承载）。

### M3 分类定理
- **A3.1** `RH/SupersingularF3.agda`：定义（3∣t，标注为定义选择）+ **∀③** 超奇异迹集 = {−3,0,3}。
- **A3.2** `RH/WaterhouseF3.agda`：**∀④** 界内每迹可实现（`water-surj` = trace-witness 别名）
  **外加双向 iff**：`water-iff`（IsSup ↔ t∈{−3,0,+3}；⟹ 复用 sup-trace，⟸ 新证 water-bwd，27 形状分派）。
- **A3.3** 注记件：t=0 ↔ π ∈ ℚ(i) ↔ NoNormT0Even 无解（按 00 号三层判据标注本源/投影，文档件）。

### M4 F₉ 全称化（可选；编译内存 -M2G 纪律）
- **A4.1** `RH/CountF9All.agda`：18 条 #E(F₉)（81 点×18）。**A4.2** `RH/WeilRecurrenceAll.agda`：**∀⑤** t₂ = t₁²−6 全 18 条。

### M5 立项不排期
- A5.1 GF(27/81/243) `frobenius-mul` 补全（duodecimal/21 明文未证）｜A5.2 WaterhouseGeneral（∀n，先写 ⑦B 边界）｜A5.3 d=3 参数化边界文档（ℤ[√−d] 类数问题）。
- **边界件已交付**（2026-11-24）：`docs/Riemann/WaterhouseGeneral与d3参数化-边界注记-A5.md`（A5.2 ⑦B 三缺口 + A5.3 类数边界 + 续作动作）。「不排期」部分保持不排期。

---

## 三、复用清单（不重做）

**本地**：`Trit` 公理族（Base/Trit.agda:94-281）｜BSD 短形计数模式（:64-72，模式照抄推广）｜WeilRigidity 实例层（保留为回归基线）｜ZetaFunctional §0（经 A1.7a 搬移复用）｜**NoNormPrelude 全套 3-adic 引理**（NoNormT0Even，M2 直接 open）｜Eisenstein `normᵉ/norm-form/conjᵉ-mul/norm-mul`（:646-906）｜`check_fermat_chain.sh` 作 `check_rh_chain.sh` 模板。

**标准库**：`Data.Integer`（ℤ 载体，WeilRigidity 先例）｜`Data.Nat._∸_`（迹）｜`Data.Fin`｜PropEq（cong/cong₂/≡-Reasoning）｜`Data.Product/Data.Sum`。不用：`Data.Complex`（宪法禁）、`Data.Nat.GCD`（ABC 线专用）。

**防重复闸**：① 开工前 PROVEN.md + rg 全库查重（本机无 proof_dag，rg 替代并声明）；② 通用名进 `XxxPrelude` 子模块；③ 提交时 Linux 机跑 `check_duplicate.sh`。

---

## 四、执行状态

| 件 | 状态 |
|---|---|
| A0.2 | ✅ 本文档 |
| A1.1 + A1.2 | ✅ `RH/CurveF3.agda`（27 Δ refl + 18/9 分类），exit=0 |
| A1.3 + A1.4 | ✅ `RH/CountF3.agda`（一般形计数器 + 18 条 #E + 18 条 ℤ 迹），exit=0；c011≡4 与 BSD `#E1-is-4` 交叉一致 |
| A1.5 | ✅ `RH/HasseAllF3.agda`：**∀①** `hasse-all : ∀ (c : CurveF3) → IsNonSing c → HasseForm c`（HasseForm = 1 ≤ #E ≤ 7，⟺ t∈{−3..3}）。27 构造子分派：9 奇异分支 `⊥-elim (h refl)`（假设被真正使用），18 非奇异分支 ≤ 链收口。exit=0 |
| A1.6 | ✅ `RH/TraceTableF3.agda`：**迹集恰 7 值**三件套——全覆盖 `trace-in-Tr3`（∀ c → IsNonSing c → Σ Tr3 …）、实现 `trace-witness`（7 值各一条见证曲线，−3↦c021(=E₂)、+3↦c022(=E₆)）、`val-inj`（49 案）。exit=0 |
| A1.7a + A1.7b | ✅ `RH/ZetaFrame.agda`（公共 §0 框架）+ `RH/ZetaAllF3.agda`（**∀ 函数方程 + ∀ 零点刚性** 18 条；原 ZetaFunctional 改 import 回归绿）。exit=0 |
| A0.1 | ✅ `NoNormT0Even` 修复（NoNormPrelude 子模块化，44→3 顶层声明）+ WeilRigidity 头注勘误（ℤ[ω]⊗𝔽₃≅𝔽₃[ε]/ε² 非域；GF(9) 载体是 ℤ[i]）。exit=0 |
| A2.1 | ✅ `engineering/oracle_rh_tables.py`（check/emit/norm 三模式，零依赖；v2 有限值形式冻结，v1 整除式被 n=7 反例否证） |
| A2.2 | ✅ `RH/Witness.agda`：wt/ws 两步递归 + `two-ind` + `witness-sat`（∀n 方程）。exit=0 |
| A2.3 | ✅ **全称分类 classify 完成**（2026-11-24）：base0 16 格 + base1 17 格 + base2 36 格全覆盖 +
  递降核（Mod3Core: tri3-split 右乘三分/no-suc-mult3 互递归/sq3ʳ；sol-next 剥层 + r1/r2 反证 +
  descent1）+ BSol 族 + BSol×3 提升 + 两步归纳合成。exit=0，0 postulate。|
| A3.1 | ✅ `RH/SupersingularF3.agda`：**∀③** sup-trace 27 分派 + 6 超奇异见证 + IsSup 可判定定义。exit=0 |
| A3.2 | ✅ `RH/WaterhouseF3.agda`：`water-iff`（双向）+ `water-surj`（存在性别名）+ 值层 `val3→sup`（21 全覆盖）+ 12+6 互斥 ⊥ 引理。exit=0 |
| A3.3 | ✅ `docs/Riemann/ProjectionMismatch-t0-pi-Qi-NoNorm-注记-2026-11-24.md`（本源/投影三层判据标注） |
| 门禁 | ✅ `engineering/check_rh_chain.sh`：14 模块拓扑序 + postulate/hole 词法扫描，2026-11-24 全绿（含 WeilRigidity/ZetaFunctional/ZetaAllF3 回归） |
| A4.1 | ✅ `RH/CountF9All.agda`：F9 = GF(3)[α]/(α²+1) 算术（f9add/f9mul/tritEq）+ 9×9 全枚举计数 + 18 条 pe9（oracle emit9 逐字）。
  Agda 独立实现与 Python 全枚举 18/18 对上；E₁/E₂/E₆ 与 WeilRigidity 旧件交叉一致（16/7/7）。exit=0 |
| A4.2 | ✅ `RH/WeilRecurrenceAll.agda`：**∀⑤** recurrence-all（t₂ = t₁²−2q, 27 分派 ×18 refl）+ ∀BSD9（bsd9-all）。
  数值与 oracle emit9 (t₁,t₂) 表 18/18 校验一致。exit=0 |
| §五基建 | ✅ `RH/Mod3Core.agda`：tri3-split（**右乘形式**三分, +3 平移=纯 cong）/no-suc-mult3（互递归）/mult3-inj（stdlib *-cancelˡ-≡）/sq-suc/sq3ʳ。递降核落点见 §四 A2.3 行 |
| 门禁 | ✅ 18 模块拓扑序全绿（2026-11-24 二跑, 含 NoNormT0General/Mod3Core/CountF9All/WeilRecurrenceAll 新件）|
| **M6 · B0** | ✅ oracle `frob`/`emit-frob`：σ 全枚举（封闭/σ²=id/pe9 对账 ✓; Fix=#E(F₃) 18/18 ✓; #E9=Fix+2·pairs ✓; 首跑漏 ∞ 被 B0 自核对拦截修正） |
| **M6 · B1** | ✅ `RH/FrobF9.agda`：f9conj（σ=a+bα↦a−bα）+ σ²=id + 环自同（neg 分配 27 格）+ rhs9-conj（σ-等变）+ frob-closed（σ 置换载体）。exit=0 |
| **M6 · B2/B3** | ✅ `RH/FrobFix.agda`：conj-fix-im 点级嵌入判据 + **fe 18 条 Fix(σ)=#E(F₃)** + **split 18 条 #E(F₉)=Fix+2·pairs**（pairs emit-frob 冻结）。exit=0 |
| **M6 · B4** | ✅ `RH/SupersingularDiv3.agda`：Div3V 层 + **div3V-sup/sup-div3V 双向**（「p∣t」算术表述 ⟺ 迹集表述）——「定义选择」升级为两等价表述互推。exit=0 |
| **M6 · B5** | **G0 ✅**（oracle group: 群公理/σ 自同/特征方程全点 ✓）+ **G1-G3 ✅**（`GroupCls0..7.agda` 8 模块, 243–909 行, 全部 exit=0——`addE` 1348 格 + **σ 群自同 sig-hom 1348 条** + commE/unit/inv + **charEq 特征方程点级**; 试点 cls6 另含结合律 343 条全量）——门禁 30 模块全绿。剩余: End(E) 环论层（π 特征多项式于 End、E[3] 破灭）需群律公式层, 未排期（A5.2 注记 §三/§四） |
| **A1 · D0–D3 d=1 范数线全称分类** | ✅ **收口（2026-11-25）**: oracle `norm-d1`（n≤12 全枚举: 可解⟺n 偶 ✓）+ `RH/NormD1.agda`（exit=0, 0 postulate, 门禁 35 模块收录）。
  §4/§5 基案（base0 9 格 + base1 n=1 无解定理）✅（D0/D1 行）;
  **§6 递降形状件**（D2）✅: `nm3s2` suc²(3·A) ≢ 3·q —— 定案形态为「剥两层 suc 后
    sym 落入 no-suc-mult3」（3 行; 原「A 归纳重写」设计被否定——no-suc-mult3 直接复用更短）;
  `x1-shape`（r=1: x² ≡ suc(3·K₁), ≡-Reasoning 形态——内联 trans 链撞 UnequalTerms, 分步显项后过）;
  `x2-shape`（r=2: x² ≡ **suc(3·suc J)** —— suc⁴ 经 `sym (cong suc (3suc J))` 一行归一,
    免去原设计 suc⁴ 载体与 no-suc4-mult3 复用; r2 全链 inner1/2/3 镜像自 NormClassify.r2-absurd）;
  `s1s0`/`s0s1`/`s1s1` 和式件 ⇒ 六个非零 mod-3 组合全部化归 no-suc-mult3/nm3s2 两核;
  **§7 递降核**（D2）✅: `descentD1` tri3-split 双坐标 9 案 = 8 矛盾 + `sol-nextD1` 双剥层
    （9·(t₀²+s₀²) ≡ 4·3^(m+2) ⟹ t₀²+s₀² ≡ 4·3^m, mul4-3out ×2 + mult3-inj ×2）;
  **§8 全称分类**（D3）✅: `pow3-dub`（3^(2k) = (3^k)²）+ `witness-satD1`（(2·3^k)² + 0 = 4·3^(2k)）
    + `liftD1`（索引 k ↦ suc k, dub-suc 归位——初版忘升层被类型器当场拦截）
    ⇒ ★ `classifyD1`（∀② d=1 镜像, two-ind 两步归纳; 边界同 NormClassify §8: 正向分类,
    逆向不作陈述）。**A1 阵列全部完工**。 |
| **M11 · N0/N1 End(E) 公式层第一砖（Deuring 失真映射）** | ✅（2026-11-25）oracle `distortion` 模式（新增）+ `RH/EndDistortion0.agda`（exit=0, 0 postulate, 门禁 36 模块收录）:
  **N0 全枚举核对**（cls0=c010 y²=x³+x 与 cls5=c020 y²=x³−x, 两个 a₆=0 超奇异类）:
  封闭 ✓ + **256 对 hom 零失败** + ρ²=neg ✓ + σ²=id ✓ + [4]=0 ✓（Z[σ]-作用合法域定案）
  + Z[σ]-作用映射 P↦[a]P+[b]·σP（a,b∈{0..3}）去重: cls0 16 个 / cls5 8 个, ρ 与每个都有分离点 ✓。
  **手算勘误入档**: σρ=ρσ 被 oracle 当场否证——正确关系是 **σρ = −ρσ**（反交换; Galois 共轭
  作用于 CM: σρσ = −ρ, 因 ρ 含 α ∉ F₃）——先算后验纪律又一次兜底。
  **N1 Agda**（表驱动, 全部 oracle distortion 逐字）: `rho` 16 条 + ★ `rho-hom`（**256 条 refl,
  End(E) 成员判据**）+ `rho-sq-neg`（16, ρ²=[−1] 即 CM by ℤ[i] 谱系）+ `rho-sig-anticomm`
  （16, σρ=−ρσ）+ ★ **`rho-ne-act1..16`**（Z[σ]-作用去重映射逐个分离见证, () 归约构造子冲突）。
  工程坑: ①语句里的裸 λ 应用 `(λ _ → ptInf) pw` 触发 UnsolvedMetaVariables——改具名 `act0/act1`;
  ②emit 复用 GroupCls0 的 mul2/mul3（不重造）; ③emit 时 check 打印须静音（否则混入模块头前）。
  **诚实边界**: 本件是点级映射层的分离定理（End(E) ⊋ ℤ[σ]-作用 的构造性离散见证）;
  「End(E) 是 F₃-四元代数序」的完整环论表述不作陈述。
  **N2 ✅ cls5 镜像**（`EndDistortion5.agda` exit=0; emit 模块名/点类型名参数化——
  踩坑: emit 段引用循环残留变量 k(=5) 而非 emit_k, cls0 错 import GroupCls5 被类型器当场拦截）。
  **N3 ✅ oracle `endact`**（ℤ[σ,ρ] 秩-4 作用）: 256 候选（a,b,c,d∈{0..3}, basis {1,σ,ρ,σρ}）
  → **去重 64**（两类一致）; 核 = 4 元: cls0 ⟨2(σ+ρ)⟩ = {(0,0,0,0),(0,2,2,0),(2,0,0,2),(2,2,2,2)},
  cls5 ⟨2ρ(1+σ)⟩; 合成封闭抽样 8×256 零失败 ✓; 群阶分布 {1, 3×2, 12×4} ⟹ **E(F₉) ≅ ℤ/4×ℤ/4**
  （End(群) = Mat₂(ℤ/4) 256 元, 作用环 64 元 = 商掉 2(σ+ρ) 的非交换子环——rank-4 种子含一部压缩）。
  生成关系 Agda 承载齐: `sig-sq-id`（16, 补齐 {σ²=1, ρ²=−1, σρ=−ρσ} 三关系）。
  **N4 ✅ 普通类侧缺席**（oracle `endordinary`/`emit-absent` + `DistortionAbsent.agda` exit=0, 门禁 38 模块）:
  普通 4 类代表元全部 a₆≠0 ⟹ rho-候选**曲线封闭恒等式 (α·y)² = rhs(−x) 即失败**
  （逐类 absurd 见证: cls1 7/11 失败点、cls2/3 10/14、cls4 7/11; ℤ[σ]-作用去重数据 12/15/15/12 冻结）——
  Deuring 对照的第二半: 超奇异 ⟹ rho ∈ End ∖ ℤ[σ]-作用（N0-N3）, 普通 ⟹ 同一候选连曲线映射都不是。
  **[构造性缺席·候选级]**: 只证 rho-候选缺席, 「End 的 F₉-有理部分 = ℤ[π]」全域陈述不作。
  **N5 ✅ 作用环核特征化**（oracle `emit-ring` + `EndRing0/5.agda` 双 exit=0, 门禁 40 模块）:
  设计从「4096 合成全表」收窄为**结构事实优先**: §K 核三引理（actK*: 非平凡核元素
  (0,2,2,0)/(2,0,0,2)/(2,2,2,2) 系 cls0、(0,0,2,2)/(2,2,0,0)/(2,2,2,2) 系 cls5 ——
  逐点作用恒 ptInf, 16 refl ×3 ×2 类）+ §R 典范代表 64 个具名映射 + ★ §S **商忠实性
  分离见证 63 条 ×2**（每个非零代表有分离点, act ≡ 零映射 → ⊥）
  ⟹ **核 = 恰为「零作用元素」全体**（64 元作用环结构定案; 4096 合成全表不作——
  合成封闭已 oracle 抽样冻结, 「商环 ≅ Mat₂(ℤ/4) 子环」的环同构表述亦不作）。
  **M11 全线收口（N0–N5）**。 |
| **M12 · W-筛网形式化（WitneSieve）** | ✅ 部分（2026-11-25, 门禁 41 模块）: 五路线诊断文档（7e8c5fe8）的筛网 record 化——`Coincidence`（W1·双结构同格; 实例 F₉: f9add 交换/单位 + c8pow 8 步回卷 + 幂 0≠1 承 dist-g0-1）+ `RigidityCert`（W2·共轭可承证; 实例 Pt0/sig: sig-sq-id 对合 + sig-hom 256 条逐对群自同）+ `SeparationCert`（W4·非循环分离; 实例 cls0 rho-vs-零作用, 直接承 rho-ne-act1）。exit=0, 0 postulate。
  **W3 ✅ 收口（2026-11-25 续, `NormFormPositive.agda` exit=0, 门禁 42 模块）**:
  `W3-skeleton : RHS ≡ P1form + (M4form + ((+4)*(+q))*(b*b))`（prem : t²+c ≡ 4q 乘入后
  t²b² + cb² = 4qb²——平方根屏障的序上算术骨架）+ 八类 prem 证书全 refl + 七实例。
  收口三钥匙（坑 #8 定案入册）: ①望远镜未用变量泛化（q → W）②算子 section 全换显式 λ
  ③总装改「四步全签名顶层引理 + 纯组合」且 sq2-comb 内部需**双重 sq2**（外层平方展开 +
  内层 (a+a)² 展开——漏内层是 25+ 迭代的真根因, 非 elaborator bug）。 |
| **M11 · 野同构判词入册** | ✅（73ba0c59, 对勘文档补充 [未验证·路线推测]）: σᵗσ = q 是对应层恒等式——特征 p 的 σ 图恰为自同构（本体）; 特征 0 刚性自同构不在货架（Spec ℤ 仅恒等; Aut(ℂ) 2^beth 野元依赖选择公理, 边界外）——五路线「寻找自同构」= 范畴找错; Alpöge 造重数 = 对应层投影（成立非本体）。 |
| **M14 · 12×12 矩阵乘法指数上下界（duodecimal 展示群寄存器）** | ✅（2026-11-26, standalone exit=0, 3 件）: 背景 = OpenAI ω ≤ 9/4 审计（docs/techniques/OpenAI-omega-9-4-只读审计-2026-11-25.md）+ 用户指令（展示群/八要素/12×12/12^12 塔/拉丁正交/trirv 三进制 VM）。交付: `Matrix12Bounds.agda`（上界 1728 ⊗ = 12³ definitional + 下界 rank ≥ 144 登记件 + TriRV 实测 71,264 步/checksum 64 = 宿主逐字一致 + ★三进制语义发现: `&` → TAND 逐 trit min, C 位与惯用法失效——fib 基准未炸仅因返回值 < 256）; `Matrix12LowerWitness.agda`（δ-表 144 条 mulEii 实例 + E-inj 单射性: eqN-range 二分 + eqN-prod→both + toℕ-injective; 首版自乘对误写被 refl 当场拦截）; 注记 `M14-12x12矩阵指数上下界-2026-11-26.md`（含 §六-a 见证件落地 + Vec.lookup vec-first 坑）。诚实边界: 维数论证（单射 ⇒ 秩 ≥ 144 的最终步）[构造性缺席·候选级]; 置换子类 0-⊗ 已形式化（P_ρ² = I 承 DCCayleyGraph）; 12 层塔 4 次重复平方（oracle 账本）。 ⚠ **勘误 2026-11-26**: 本行「144 ≤ · ≤ 1728」不是已证结论——1728 只是 `12*12*12 ≡ 1728`（无形式代价模型）; 144 下界未证, 当时「输出两两不同 ⇒ 秩 ≥ 144」是无效推理; `Matrix12LowerWitness` 只证了基矩阵两两不同 + 144 条 `E_ii·E_ik = E_ik`。详见注记顶部勘误。 |
| **M13 · GF(3) 矩阵乘法次数账本（ω 问题的离散寄存器答案）** | ✅ N0/N1（2026-11-25, standalone exit=0）: 背景 = OpenAI ω ≤ 9/4 形式化审计（docs/techniques/OpenAI-omega-9-4-只读审计-2026-11-25.md）。`oracle_strassen_gf3.py`: Strassen 2×2 七乘方案 **GF(3) 全枚举 6561 对零失败** + 次数账本（Strassen 7⊗+18 加减 vs 朴素 8⊗+4 加）+ 16 基例表; `StrassenGF3.agda`（6621 行）: 七门定义 + **全枚举正确性 6561 条 refl**（3⁸ 组合逐字发射, oracle 逐字冻结——先算后验最纯粹形态; 顺带实测 ⊗ 表抽象首参 catch-all 落 T₁ 的坑, 全枚举形态天然免疫）。诚实边界: 7-极小性下界（Hopcroft–Kerr）与渐近 ω 不在本库边界 [边界外]; 独立 L2 件（不在 RH 链）。 ⚠ **勘误 2026-11-26**: 本行背景所引审计的负面结论（OpenAI 库无下界）已撤回, 见 `OpenAI-omega-9-4-只读审计` 顶部勘误; StrassenGF3 本身（GF(3) 上七乘方案正确性）不受影响。 |
| **M15 · ListBounds——软核的不用实数镜像（ω 审计 §G 第三条 / 「第 3 件」）** | ✅（2026-11-26, `6982c9a1`, standalone exit=0, 0 postulate）: `ListBounds.agda`（1222 行, 仅标准库）: ★ `lb-incompatible`（lb-Grow → lb-Seed → lb-Many → lb-Comp → ⊥; n、h 抽象为满足增长条件的函数）+ ★ `lb-incompatible-lists`（取 N := listBits、H := w², 即 Lean `Iteration.lean:76` `incompatible` 的 ℕ 形态）+ ★ `lb-wk≤2w`（2^(k+4) ≤ w ⟹ w^k ≤ 2^w）。不用实数: 分数次幂只在不等式里 → 乘方成整数不等式; w 取子序列 W^N0; h 的分数次幂写成「∀ u v 满足侧条件」。★ **非空真**（§11）: `lb-consistent-SMG`/`SCG`/`MCG`/`SMC`（去掉任一假设其余三条对具体 P 同时成立）+ `lb-necessary-C/M/S/G`（四条缺一不可）。oracle `oracle_list_bounds.py` 11 项 ALL_PASS（含桥接 G1–G3 分数精确抽样、非空真回声）+ unittest。**边界**: 「Lean 实数陈述 ⟹ ℕ 陈述」的桥未形式化 [手工论证·未验证]（左端要 ℝ, 宪法禁无理数）⇒ 这是软核在 ℕ 上的**独立**定理, 非 Lean 定理的形式化推论; 只镜像软核, 不是任何域上的下界证明, 不改变 ω = 9/4 审计状态; 本件顺序与先算后验相反（Agda 先行）。登记 `PROVEN.md` §十五。 |
| **M16 · 秩分解谓词 + M13 接桥 + 展平下界（ω = 9/4 在 GF(3) 上的陈述层）** | ✅ A+B（2026-11-26, standalone exit=0, 0 postulate, 2 件）: 背景 = 证明阅读记录（docs/techniques/OpenAI-omega-9-4-证明阅读-2026-11-26.md）之后的差距分析——外部定理在 GF(3) 上的全部内容是「∀ n ≥ 2, r: `RankLE₃ n r → n^9 ≤ r^4`」, 而本库此前**没有这个谓词**。交付: `TensorRankGF3.agda`（297 行）: record `RankLE₃`（镜像 Lean `RationalCircuits.lean:48 RankLE`）+ ★ `strassen-is-rank-form`（由 M13 的 `strassen-correct` 承证）+ ★ `rank-strassen : RankLE₃ 2 7` + 外部边界类型 `ω₃-boundary`（**无居民**）; `TensorRankFlattenGF3.agda`（281 行）: ★ `rank-lower : ∀ n r → RankLE₃ n r → n * n ≤ r`（镜像 Lean `Flattening.lean:6 rank_lower`; 证法不同——Lean 走展平后矩阵的秩, 本库走计数: 标准基落在张成里 ⟹ ★ `span-full` ⟹ 单射 `Fin (3^(n²)) → Fin (3^r)`）。旁证: `oracle_tensor_rank_gf3.py` 五组核对 ALL_PASS（64 / 26244 / 64 / 1616 / 2061 次）+ 12 个 unittest（含 2 个负控制）。**边界**: `ω₃-boundary` 是外部定理的陈述, M16 **没有**推进它; `rank-lower` 只对 GF(3); n = 2 处库内 r ≥ 4（`rank-lower`）且 r ≤ 7（`rank-strassen`）, 外部定理按算术给 r ≥ 5, 「秩恰为 7」[直觉·未验证]; Lean `RankLE` 与 `RankLE₃` 的逐字对应未形式化 [手工论证·未验证]。下一步 M16-C: 秩相乘 / 取幂（Lean `RankPower.lean`）[未验证·路线推测: 核对动作 = 读 `RankPower.lean` 的 rank_map / rank_mul / rank_pow 陈述并逐字镜像到 `RankLE₃`]。登记 `PROVEN.md` §十五。 |
| **M9 · G4 相干放大二分** | ✅ `Synthesis/Geometry/CoherentPhase.agda`（exit=0）——AmplificationDichotomy record inhabited：自由 ℤ 载体忠实线性放大（coherent-linear/coherent-inj posInj）× 有限阶截断（trunc3/trunc8/C₁₂ 引用 DuodecClock）——「相干放大」离散类比存在性判据 = 载体含自由部分；物理层 [物理假说·未验证] 隔离不变。**M9 全线收官**（G1-G4 + A₄ 试点） |
| **M9 · G3 挠率-自旋耦合** | ✅ `Synthesis/Geometry/SpinTorsionCoupling.agda`（exit=0）——EC 离散形态：源场 = 手征串失衡 + ★ coupling（挠率值定义性 = 失衡, κ=1）+ 平衡闭合归零 + ★ **zhonglv-spin-bridge**（repL 11 挠率 ≡ +11 ≡ zhonglvTorsion——「仲吕不交」获得自旋源解释） |
| **M9 · A₄ 绝对平行** | ✅ `Synthesis/Geometry/TeleparallelA4.agda` 试点（exit=0）——Shipov 数学骨架离散化：零曲率定理 plaquette-collapse（六步含逆 = 2×换位 + 2×三次归零）+ A₄ 共存 record inhabited（flat × zhonglvTorsion +11）——对 Shipov 自洽性给离散正面数据点；物理诠释 [物理假说·未验证] 严格隔离（A5.2 注记 §六） |
| **M8 · F₉\*≅C₈** | ✅ `RH/F9MultC8.agda`（exit=0）——原生共轭性乘法群来源形式化：g=1+α 生成 C₈（dist 28 条）+ σ=k↦3k（8 条）+ **Norm∈F₃*={±1}**（8 条; 修正「α⁴=q=9」初版陈述——枚举否证）; 注记 docs/Riemann/原生共轭性代数来源-注记 |
| **M7 · E[3] 破灭** | ✅ `RH/E3Tor.agda`（exit=0）——超奇异 4 类 e3-triv（3-挠破灭）+ 普通 4 类非平凡 C₃ 见证 + notsup 桥——「p∣t 超奇异 ⟺ E[3](F₉) 破灭」逐类成立（Deuring 代数侧表驱动承载; 与 B4 合流为三表述等价） |
| 门禁 | ✅ 22 模块拓扑序全绿（2026-11-25, 含 M6 四件 + CurveIsoF3） |

命名记录：判别式函数定名 `discF3`——`disc` 已被 `DiscreteKTheory.agda:573`（Witt 判别式）占用。迹函数定名 `tℤ`（ℤ 层；ℕ 的 `_∸_` 对负迹会钳 0，不可用）。

---

## 五、递降核基建评估（A2.3-续 / A2.4 前置）

递降步（sol n t s, n≥2 ⇒ (t,s)=3·(t',s') ∧ sol (n−2) t' s'）需要的 mod-3 事实（ℕ 层）：

| 需求 | 形式 | 现状 |
|---|---|---|
| t² ≡ 0 (mod 3) ⇒ 3∣t | 按 t = 3q+r, r∈{0,1,2} 三案枚举 | **库内待建**（NoNormPrelude 无此引理）[未验证·路线推测] |
| 3s² ≡ 0 (mod 3) 分离 | 平凡 | 可由加法/乘法定义性处理 |
| 9(t'²+3s'²) = 4·3ⁿ ⇔ t'²+3s'² = 4·3^(n−2) | ℕ 除法/约去 | 可用两步归纳（Witness 的 two-ind 风格） |

执行回执（2026-11-24）：基建以 `RH/Mod3Core.agda` 落地——三案枚举取「右乘形式」t ≡ q·3
（+3 平移 = cong suc∘suc∘suc，零算术链）；「平方≡0⇒3∣」由 tri3-split + no-suc-mult3
（suc (3·A) ≢ 3·q 互递归归纳）合成；3 消去直接用 stdlib *-cancelˡ-≡。递降核与 classify 见 §四 A2.3 行。

---

## 六、Agda 2.9.0-nightly 工程事实（2026-11-24 会话四坑, 供后续避让）

| # | 坑 | 症状 | 绕行 |
|---|---|---|---|
| 1 | --cubical 下 absurd 只看**顶层**构造子 | `9 ≤ 4 → ⊥` 用 `()` 报 ShouldBeEmpty（顶层 s≤s 合法） | `≤1↓` 显式降层到 `suc _ ≤ zero` 再 `()` |
| 2 | 签名级**未使用显式参数** | UnsolvedMetaVariables 卡在 binder（探针二分实证; 子句级未使用 h 不触发） | 所有签名参数必须在体内出现 |
| 3 | stuck ≡ 型的 absurd | `pow3 (suc k) ≡ zero` 用 `()` 报 "Is empty (stuck)" | 归约到 `c * suc x ≡ zero`（+ 递归落构造子 ⇒ suc 头）再 `()` |
| 4 | **对 telescope 函数参数施应用**（domain 为 ≤ 型, --cubical） | `cap : X ≤ Y → ⊥` 在体内 `cap (…)` 报 CannotApply「cap 非函数」——codomain 被吞（变量作参数/整体传递正常, domain 为 ℕ 正常） | 助手引理**返回 ≤ 证据**，调用方对**具名**空型引理施应用 |

| 5 | **分派子句块之前悬置其他「已声明未定义」签名**（--cubical） | 后续子句的 refl 检查被污染（CannotApply/UnequalTerms; 同一内容改独立具名引理形态则通过——M1-M4 二分实证, CurveIsoF3） | 全件独立具名引理形态; 必须保持函数形态的（如 cls-of）令签名与子句块**零间隔** |

| 6 | 表驱动函数的 ∀ 命题在抽象变元上卡死 | `∀ p → addE p ptInf ≡ p` 的 refl 报 UnequalTerms（归约需首参构造子） | 命题改具体 n 条子句形态（unit/inv 范式）; 乘法字面量先行同源（xshift 范式） |
| 7 | [n]P 枚举从 P 起加 n 次 = [n+1]P | 「超奇异 ⟺ 3-挠破灭」判据首跑 4 处不符（实为 4-挠表） | 从 ∞ 起加; 判据交叉核对当场拦截（先算后验活例） |

另: NoNormPrelude 的 `*-distribˡ` 是**右分配**形式 `(a+b)*c ≡ a*c+b*c`（Witness.distribʳ 同款）；左分配需 comm 绕行（NormClassify.ldistr）。`⊥`/`_≢_` 有两套（Data.Empty vs NoNormPrelude 自带），不可混用。Trit 乘法在抽象首参处卡死——涉及具体 r 的展开一律**字面量先行**（CurveIsoF3.xshift 范式）。
