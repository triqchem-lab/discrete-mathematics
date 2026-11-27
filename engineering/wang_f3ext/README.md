# Wang 张量秩下界框架：F₃ 扩展 + 手工构建（`engineering/wang_f3ext/`）

> 立项 A-T3 的工程件（见 `docs/plan/matrix-rank-line-plan.md`）：把
> [`wcgbg/tensor-rank-lower-bound`](https://github.com/wcgbg/tensor-rank-lower-bound) @ `9db3d21`
> （arXiv:2603.07280 的下界搜索框架，公开版矩阵族只有 F₂ 实现）扩到素域 F₃，
> 用同一套四技术（flatten / forced product / degenerate reduction / backtracking）
> 给 **GF(3) 上 ⟨3,3,3⟩** 出机器可查的下界证书。
>
> **权威顺序**：verifier 与独立核对器的输出 > 本文的叙述。下文凡写「实测」的地方都附了可重跑的命令。

## 1. 目录

| 路径 | 内容 |
|---|---|
| `f3_extension.patch` | 对上游的补丁：`problems/matrix/symmetry.h`（新增 `SymmetryGroupFq` + 分发）、`problem.h`（注释、`kN0..kN2`）、`BUILD`；**外加 core / search / problems 的 F₃ 挂钩**（`constraints.h`、`dynamic_matrix.cc`、`rank_lower_bound_flatten.h`、`rank_lower_bound_forced_product.h`、`search/rank_lower_bound_degenerate.h`、`search/orbit_map.h`、`search/rank_lower_bound_backtracking.h`、`problems/matrix/symmetry.h`，见 §5.1 / §5.4） |
| `fq_matrix.h` | 新文件：base-P 数位打包的小矩阵（`FqMatrix<P,N0,N1>`，转置 / 乘积 / 求逆 / 秩） |
| `fq_matrix_tables.h` | 新文件：GL 表、逆表、按行查表乘积表（`FqMatrixTables<P,N0,N1>`） |
| `fq_matrix_test.cc` | 新文件：上游 gtest 风格的扩展单元测试（bazel 下跑） |
| `rank_f3_fast.h` | 新文件（放进上游 `core/`）：F₃ 求秩 / 展平秩快路径（性能专用，语义不变，见 §5） |
| `get_f3_simd.h` | 新文件（放进上游 `core/`）：`OrbitMap::Get` 的批量探针内核（NEON 16 路 + 标签预筛表，语义不变，见 §5.2） |
| `shim/` | 手工构建用的垫片头文件树（`ng-log`、`gflags`、`tbb`、`boost/{unordered,iostreams}`、`google/protobuf`、`core/certificate.pb.h`），共 16 个文件 |
| `build.sh` | clang++ 直编脚本（不依赖 bazel / Xcode） |
| `shim_test/` | 垫片分块的回归测试（`run.sh` 对 `SHIM_THREADS=1..8` 各跑一遍） |
| `standalone/` | 不编译整个框架也能跑的自检：`fq_matrix_test_main.cc`、`f3_problem_check.cc`（F₃ 扩展）+ `rank_f3_fast_check.cc` / `apply_check.cc` / `get_simd_check.cc`（快路径与 Get 内核的对拍 + 微基准）+ 一份极简串行 tbb 垫片 |
| `verify.sh` | 一份 F₃ 证书的三重验证（C++ verifier / 独立核对器 / 负控制） |
| `certs/` | 证书：`matrix_q03_n333_v1.{pb.txt,btp}`（F₃ ⟨3,3,3⟩ ≥ 17，见 §7） |
| `offline/` | 离线 bazel 路线的脚本（BCR 快照镜像、模块闭包抓取、distdir 预取）；**本机构建阶段不可用**，见 §3 |

配套的独立核对器在上两级目录：`engineering/wang_cert_check.py`（F₂）、`engineering/wang_cert_check_fq.py`（素域，含 GF(3)）、`engineering/forced_fq_c/forced_fq.c`（forced product 的独立 C 实现）。

## 2. 准备上游副本

```bash
git clone https://github.com/wcgbg/tensor-rank-lower-bound /tmp/wang-tensor-rank
# 需要代理时: git -c http.proxy=socks5h://127.0.0.1:10808 -c https.proxy=socks5h://127.0.0.1:10808 clone …
git -C /tmp/wang-tensor-rank checkout 9db3d21
HERE=/Users/zesheng/work/discrete-mathematics/engineering/wang_f3ext
git -C /tmp/wang-tensor-rank apply "$HERE/f3_extension.patch"
cp "$HERE/fq_matrix.h" "$HERE/fq_matrix_tables.h" "$HERE/fq_matrix_test.cc" /tmp/wang-tensor-rank/problems/matrix/
cp "$HERE/rank_f3_fast.h" "$HERE/get_f3_simd.h" /tmp/wang-tensor-rank/core/
```

**实测（2026-11-27）**：从 `git archive 9db3d21` 得到的干净副本出发执行上面几步，用本目录 `build.sh` 构建，
与工作副本构建的产物相比：`__TEXT` 代码、`__DATA_CONST`、`__DATA` **逐字节相同**；全部差异都在 Mach-O 头部的
`LC_UUID`（16 字节）与 ad-hoc 代码签名里（签名覆盖可执行文件名——换个输出名，签名就变，长度还会差 8 字节）。
所以别用 `cmp` 整文件比较不同名字的产物；要比较就按段比（`otool -l` 取段的 fileoff/filesize）。
同一棵树、同名输出重建是逐字节确定的。

## 3. 为什么不走 bazel

本机（2026-11-27 实测，macOS arm64 / darwin 25.6.0，只有 Command Line Tools、没有 Xcode.app）：

- Bazel 8.3.1（仓库 `.bazeliskrc` 钉的版本）读 macOS 系统代理后报
  `Proxy address socks5h://127.0.0.1:10808 is not a valid URL`，环境变量覆盖无效。
  绕法是离线路线（`offline/`）：完整 BCR 快照 + 按模块闭包预取 distdir，
  **fetch 阶段已验证成功**（`bazelisk fetch` 通过）。
- 但 **build 阶段崩溃**：apple 工具链报 `DottedVersion ... got 'None'`；Homebrew LLVM 23.1.5
  不被 `apple_cc_toolchain` 识别；把 `--crosstool_top` 指到 `@local_config_cc//:toolchain` 也没救。

所以改走 **clang++ 直编 + 垫片**（§4）。有 Xcode 的机器可直接 `bazel build`，`offline/` 的脚本仍可用于 fetch。

## 4. 构建与流水线

```bash
WANG_REPO=/tmp/wang-tensor-rank
bash "$HERE/build.sh" 3 enumerator /tmp/wang-f3/enumerator_f3     # P=3, ⟨3,3,3⟩
bash "$HERE/build.sh" 3 lower      /tmp/wang-f3/lower_f3
bash "$HERE/build.sh" 3 verifier   /tmp/wang-f3/verifier_f3
```

依赖：Homebrew LLVM（缺省 `/opt/homebrew/opt/llvm/bin/clang++`，可用 `CXX=` 覆盖）、zlib、pthread。
`build.sh` 内部用 **bash 数组**传 `-D` 列表——zsh 不对未加引号的 `$VAR` 分词，
在 zsh 里手敲 `$DEFS` 会把整串当成一个参数（本次调试第一轮就栽在这里）。

三步流水线（对应上游 `run.py` 的 `search_pipeline`；**`lower` 会原地覆盖输入并写 `.btp` 旁车，务必在副本上跑**）：

```bash
cd /tmp/wang-run
/tmp/wang-f3/enumerator_f3 --output_path f3_orbits.pb.txt          # ① 轨道枚举
cp f3_orbits.pb.txt f3_lb.pb.txt
/tmp/wang-f3/lower_f3 f3_lb.pb.txt --ignore_rank_lower_bound \
    --backtracking_step_limit=10000000 --forced_product_max_iterations_log2=32   # ② 下界 DP（pass 0）
/tmp/wang-f3/verifier_f3 f3_lb.pb.txt                              # ③ 框架自带的 verifier
```

② 的参数是上游 `run.py` 给 F₂ 3×3×3 用的同一组（`backtracking_step_limit=10_000_000`,
`forced_product_max_iterations_log2=32`）。上游对更大的格式还做第二遍
（`dim_min=4` / `dim_max=3` 分段，见 `run.py` 的 `search_matrix` 注释块），F₃ 是否需要见 §7。

独立核对（与 C++ 实现无关的第二实现；`forced_fq` 是 forced product 的独立 C 核）：

```bash
python3 -I engineering/wang_cert_check_fq.py /tmp/wang-run/f3_lb.pb.txt
python3 -I engineering/wang_cert_check_fq.py /tmp/wang-run/f3_lb.pb.txt --corrupt 1   # 负控制：必须转红
```

## 5. F₃ 扩展的设计

上游 `search/` 与 `verifier/` **没有 F₂ 特化**；`core/` 的特化都是带通用 F_q 回退的 `constexpr` 分支。
唯一的阻塞点是 `problems/matrix/symmetry.h`（BitVec 约束 + F₂ 的 GL 表，`static_assert P == 2`）。

- **群**：A 侧对称群 G = (GL_{N0} × GL_{N1}) ⋊ C₂（C₂ = 转置，仅立方格式），
  √|G| 分裂与 F₂ 相同：Store = {X ↦ X·R}（右乘），Query = {X ↦ L·τᵗ(X)}（左乘 + 可选转置）。
  与 GL(n,2) 不同，GL(n,P) 的中心 F_P^* 非平凡，两边都保留完整 GL（轨道枚举多出 |F_P^*| 倍冗余，不影响正确性）。
- **约束 ↔ 矩阵**：`Vec.data[k]` 是 base-P 数位、平铺下标 `ij = i·N1 + j`，与 `EncodeGFVec` 同序。
- **见证打包**：`Store::Elem` = 矩阵数据（uint32），`QuerySet::Elem` = `{l, transpose}`，打包方式与 F₂ 相同
  （`l | transpose << 16`），所以证书的 witness 字段格式不变。
- **分发**：`SymmetryGroupDispatch`（类模板偏特化）而不是 `std::conditional`——后者会实例化两个分支，
  而 F₂ 分支对 P = 3 会触发 `static_assert`。
- **上限**：见证打包要求 P^(N0·N0) ≤ 2^16，所以 P = 3 只到 GL(3,3)（|GL(3,3)| = 11232）。

### 5.1 F₃ 快路径（性能专用，语义不变）

上游的 forced product 对每个组合都要算三次展平秩（9×81 的矩阵）。F₂ 有位打包快路径，**F₃ 走的是通用 F_q 路径**：

- `DynamicMatrix<3,1>::Rank()`：每次调用把矩阵拷进 `std::vector<std::vector<>>`（堆分配），做**完整** Gauss–Jordan（求秩只需前向消元，上面一半是多余的），内层每个元素走带分支的 GF 运算；
- `RankLowerBoundFlatten`：先做两次 `CyclicTranspose`（各 729 字节的分散写），再三次构造 `DynamicMatrix`（各一次堆分配）。

实测合计**每次迭代约 20 µs**，3^18 = 3.87 亿次枚举要 **16 分钟 / 投影位**（8 线程）。
所以 `rank_f3_fast.h` 给这些热点加了快路径，由补丁里的 `if constexpr (P == 3 && M == 1)` 挂钩调用：

- 求秩：栈上平铺 `uint8` 数组、只消下方行、不归一化主元行（把主元的逆并进消元系数）、取模写成「比较-减法」；
- 展平秩：直接按跨度从张量读出三个循环位的展平矩阵，不做转置、不堆分配；次序与短路条件和通用实现相同；
- forced product 的「组合叠加」步（把被选中的强制行按系数 1 或 2 叠进张量）：从带分支的 GF 运算改成无分支取模。
  这一步没有单独的对拍件，验证方式是新旧二进制在 dim 9–7 上的结果（证明类型 / 投影位 / 界值）**逐项相同**。

第四处不是算术层面的，是**搜索层面的剪枝**（只对 F₃ 开启，F₂ 保持上游原样以便回归逐字对上公开证书）：

- 退化归约对每个候选额外行做一次 `OrbitMap::Get`（约 7500 次探针 × 2.1 µs ≈ 16 ms；7500 是期望值 22464/3，不是实测）。但候选行只要相差一个基向量，
  张成的就是同一个 (d+1) 维超空间——dim 5 时 9841 个候选里只有 40 个不同的超空间，却查了约 9700 次。
  F₂ 的查找只有 336 个探针所以上游没觉得慢。剪枝 = 只访问「关于基极小」的候选行（在基的每个主元位置为 0），
  每个超空间恰好访问一次，max 不变；平局时记录的见证可能不同（不影响证明有效性）。
- 验证：① `rank_f3_fast_check.cc` 的「极小扫描 = 全扫」一节——25 个随机基（dim 0–8）× 候选行全枚举，
  两种扫描访问的超空间集合相同、极小候选数 = (3^(9−d) − 1)/2，0 不匹配；
  ② 新旧二进制在 dim 9–6 上 736 条轨道的结果（证明类型 / 界值）**完全相同**；
  实测 dim 7: 5.0 s → 0.1 s，dim 6: 251 s → 92 s（且是在与另两个运行抢 CPU 时测的）。

**只对 (P, M) = (3, 1) 生效**；其余域、以及超出缓冲尺寸（行 > 16 或列 > 128，返回 −1）的矩阵走通用实现。
实测（空闲 8 核，2026-11-27）：9×9×9 张量的展平秩 1118 ns（独立参考实现 5237 ns），9×81 求秩 469 ns。

另外两处：

- 规范形 `GaussJordanRREF`（OrbitMap / 枚举器 / verifier 的键都靠它）：同样的前向做法。7×9 的规范形含拷贝实测
  250–300 ns，通用实现 475–520 ns——快约 1.7 倍，但它本来就不是热点。
  （更正：此前这里写「不比通用实现快」，是照第一次在抢 CPU 时的读数 679 对 478 ns 写的，与同一段引用的数字自相矛盾。）
- **群作用 `Apply`（真正的大头）**：微基准显示 `OrbitMap::Get` 的一次探针约 2.1 µs，其中对约束组每行做一次
  `query.Apply` 占 1.4–1.8 µs（表驱动的逐行打包/解包 + 查表），RREF 只有 0.45 µs，哈希查找可忽略。
  `SymmetryGroupFq` 在 P=3、N0=N1=3 时改用查表：对每个矩阵数据（3^9 种）、每个输出行、每个输入三元组（27 种）
  预先算好线性泛函 `Σ_k M[o][k]·x_k`（左乘、右乘各一张表，约 1.6 MB），每次 `Apply` 只做三次「取三元组 → 查表」。
  一次探针降到约 0.55 µs（原先 2.1 µs；中间先试过直接的 3×3 数位运算，约 1.0 µs）。
  现在 `Get` 里的大头变成了 RREF（约 0.25–0.4 µs）。
  **这一步是先量再改的**：我起初以为 RREF 是热点，写完快路径一测才发现不是。

### 5.2 `Get` 的批量探针内核（搜索的真正热点，语义不变）

回溯搜索（dim ≤ 5）的时间几乎全在 `OrbitMap::Get`：对一组约束 q，把全部 22464 个 Query 元素逐个试过去，
平均几千个探针才命中一次。即便群作用已经查表化，标量版满扫描平均每个探针仍要 0.17–0.29 µs（群作用 + 规范形 + 查表）。
`get_f3_simd.h` 改成：

- **16 个探针一批**：用 NEON 对 16 个 Query 元素同时做「群作用 → 逐列消元求规范形 → 标签」，
  数据按道分开存放（`X[行][列]` 是 16 个探针的数位向量）。消元是无分支的：主元列从 8 到 0，
  每列在还没当过主元的行里取最小的非零行。规范形由行空间唯一决定，所以与逐个算的结果逐位相同。
- **32 位标签预筛**：每个键有一个与行序无关的标签 `Σ_rows mix32(行编码 | 主元列 << 22)`。
  `Set` 首次插入一个键时把标签放进「按键维数分表」的开放寻址表；`Get` 先查标签表，命中再回到
  权威的哈希表核对。标签表只可能假阳性（由权威表排除），不可能假阴性。
- 回溯搜索会把多条额外行加在基上，q 可以超过 9 行且线性相关；探针循环先把 q 约化成行空间的基
  （像的行空间只依赖 q 的跨度，所以结果与见证不变）。
- 返回值与标量版逐项相同：按下标顺序的第一个命中、同一个界、同一对见证。没有 NEON 的机器走标量块内核
  （同一算法的另一份实现，也是 NEON 版的对拍参考），同样享受标签表。

实测（M2 空闲，2026-11-27，`standalone/get_simd_check.cc`）：满扫描平均每个探针 24–61 ns（标量 171–291 ns）；
命中场景下一次 `Get` 从 765–1071 µs 降到 142–226 µs（4.6–6.4 倍，表越大倍数越高）。
搜索端的回归：在同一份 v1 证书上重跑 dim 9–6（回溯步数 1e7），结束时 102 条轨道与 v1 逐项一致
（维数 / 界 / 证明类型 / 投影位，0 条差异），dim 6 用时 21.6 s。
  （旧二进制没有同一配置的计时；从零重算的 v3 运行里 dim 6 是 105.8 s，但那次还跑了 forced product，配置不同，只能当量级参考。）

等价性见 §6。

### 5.3 回溯证明在证什么（读 `rank_lower_bound_backtracking.h` / `backtracking_verifier.h` 与论文后的小结）

回溯证明容易被误读，这里把核对过的几点写下来（2026-11-27）。论文指 arXiv 2603.07280；
下面的引文是经网页抽取读到的句子，**没有读 PDF 原文**；论证的复述是我按代码自己推的。

- **验证端检查的是**：对基约束 B（维数 d）与声明 L，重放「候选下标非增序列」i₁ ≥ i₂ ≥ … 的**整棵树**
  （深度 < L−1）；每个记录闭合一个节点，条件是 `popcount(mask) + 表中的界 ≥ L`，其中 mask 选中路径的一部分行
  （必须含最新一行），查的是「B ∪ 选中的行」所在轨道的界。整棵树必须被记录闭合完。
- **路径的每一项是「假想分解里的一个乘积项」，不是一条约束。** 论文的原话：
  「As the factors are unordered, we assume the factors are non-decreasing.」，以及 Orbit 6 的例子
  「If a₀,₀ appears at least twice in the decomposition scheme, we set a₀,₀ = 0.」→「R(T₆) ≥ R(T₅) + 2」。
  所以**同一个候选在路径上重复出现是设计的一部分**：两项的第一因子成比例时，把它置零一次消掉两项。
- **为什么这证明秩 ≥ L（我的复述）**：反设有一个 L−1 项的分解。把各项按「第一因子关于基的规范代表」的下标排成非增序列，
  这条序列是树里的一条路径。在深度 j 的节点选一个含第 j 项的 mask，把这些项的因子置零（作为约束加上），
  至少消掉 `popcount(mask)` 个**不同的**项，剩下的张量落在查到的轨道里，于是
  (L−1) − popcount(mask) ≥ 表中的界，与 `popcount(mask) + 界 ≥ L` 矛盾。
- **不能按「线性无关的约束条数」去数。** 我一度把叶子处「行组线性相关」当成可靠性缺口，还写了一个按无关行数计数的
  「严格」重放：v1 证书 18,822,872 个叶子里有 4,669,134 个（307 / 339 条回溯轨道）属于这种，按无关行数数全部「不达标」。
  查了论文的论证之后确认这是误读，**证书没有问题**；那个「严格」重放的结论作废，核对器保持与框架验证端逐条一致。
  上面的数字保留下来，只是说明这份证书对重复因子的依赖有多重。
- **搜索的代价结构（由代码的 min / max 与 v1 的界值推出，没有实跑验证）**：节点值 =
  max(本节点各 mask 的最好值, 所有子节点值的最小值)，任何一个子节点没闭合，父节点就闭合不了。
  v1 下直线 16、平面 15、3 维空间 ≤ 15，所以 dim 0 要证 18 时，9841 个一阶分支都要下探，
  约 4.84e7 个二阶节点 [x, y] 的**每一个子节点** [x, y, z]（z ≤ y）都得闭合——至少 C(9843, 3) ≈ 1.59e11 个深度 3 的节点要访问
  （非增三元组的个数）。若平面的界先涨到 16，这 4.84e7 个二阶节点就能就地闭合（2 + 16 = 18）。
  换言之，18 的瓶颈不在 `Get` 的速度，而在 dim ≥ 2 的界能不能先涨；那些维度是同一结构的小号版本（dim 2 的候选数 1093）。

### 5.4 回溯搜索的去重键（搜索层，语义与轨迹逐条不变）

§5.3 说过：链上同一个候选可以重复出现。上游的缓存键是「mask 选中的路径行 + 最后一行」这个**含重复的行组**，
于是张成同一个子空间、只是重复模式不同的键各查一次 `Get`。先量再改（dim 6，v1 证书，1e7 步，插桩统计）：

| 量 | 上游 | 去重后 |
|---|---|---|
| `Get` 次数 | 2,380,069 | 263,587（只有这些是不同的子空间） |
| 每个节点的键求值次数（合计） | 8.25 亿（= Σ 2^(j−1)，逐 mask） | 1.44 亿（= Σ 2^c，c = 可掩码位置上的不同候选数） |
| 闭合叶子占节点的比例 | 23%；叶子闭合前平均只有 0.04 次 `Get` | 同左（叶子本来就便宜，贵的是非叶节点） |

`search/rank_lower_bound_backtracking.h` 的 F₃ 分支（`kF3Dedup`；F₂ 保持上游原样）：

- **键 = 去重后的候选序列**。链的下标非增，所以同一组候选在每个节点都得到同一个序列，同一个子空间在所有节点命中同一个缓存项。
  `Get(q)` 只依赖 q 的行空间（`get_simd_check.cc` 的 E 项：随机重复行 / 随机线性组合行 vs 去重后的规范行，2000 次 0 不匹配）。
- **按类子集求值**。节点值 = max over 类子集 K（(K 里各类的重数之和) + 1 + 界(K ∪ 末行类)），
  与「max over mask（popcount(mask) + 1 + 界）」相同，因为同一组类的 mask 里重数最大的那个 popcount 最大。
- **闭合时仍按原顺序扫描 mask**，记录的还是原顺序下第一个达到 target 的那个，返回值也是它的取值——轨迹逐条不变。
- 类数超过 20 时退回上游的逐 mask 循环（键仍是去重键；F₃ 的 claim ≤ 17 时深度 ≤ 16，实际走不到）。
- `SOVEREIGN_F3_RAWKEYS=1` 退回上游行为，`SOVEREIGN_F3_MAX_CLASSES` 调低阈值；只用于回归对拍。

**等价性（实测，2026-11-27）**：同一个二进制从零算 dim 9–6（`--ignore_rank_lower_bound --dim_min=6`，1e7 步，forced product 2^28），
四种模式——上游行为 / 新实现 / 阈值 3（大部分节点走回退分支）/ 阈值 12——的证书 sha256 全是 `c56c8678…`、
`.btp` 轨迹档案 sha256 全是 `9a8c65b2…`，即**记录下来的证明逐字节相同**。CPU 时间：上游行为 56.79 s，新实现 **5.92 s（9.6 倍）**；
只换键不换枚举方式（阈值 3）42.41 s（1.35 倍）——大头来自按类子集枚举，不是少查了 `Get`。

这只改变每个搜索步的代价，不改变 §5.3 的计数：dim 0 证 18 仍要 ~1.59e11 次闭合。它的用处是同样的预算下能多走约一个数量级的步数。

**边界**：「逐字节相同」只在 dim 9–6 上验证过（claim ≤ 13、深度 ≤ 13）。更深的维度没有做与上游行为的对比——
上游行为在 dim 5–0 上跑一遍要两个小时量级。不过即使有差别，影响的也只是「搜得全不全」：
每条记录仍由框架 verifier 与独立核对器逐条检查，轨迹本身不会因此变得不可靠。
dim 5–0 的实测见 §7.4 与之后的续跑记录。

## 6. 验证证据（2026-11-27）

| 检查 | 做法 | 结果 |
|---|---|---|
| F₂ 回归（verifier） | `verifier_f2 real_cert_matrix_q02_n333.pb.txt` | `UNCONSTRAINED TENSOR RANK LOWER BOUND: 20` / `OK. Verified` |
| F₂ 回归（枚举） | `enumerator_f2` 输出 vs 公开证书，按轨道逐条比较约束字节串 | 496 条，序列完全一致 |
| F₃ 群作用 | 框架 `store.Apply` / `query.Apply` / `ApplyInverse` / 单位元 vs **独立朴素实现**（直接按 X·R、L·τᵗ(X) 循环），全部 3⁹ 个向量 × 全部群元 | 0 个不匹配 |
| F₃ 枚举**完整性** | 轨道大小守恒：对每条代表 c 数 (Q,S) 对中满足 Q·c ≡ S·c 的对数 → \|Stab\| → \|orbit\| = \|H\|/\|Stab\|，各维求和对比高斯二项系数 | 10 个维度**全部精确相等**（见下表） |
| 垫片分块 | `shim_test/run.sh` | 1–8 线程全过；对旧垫片的负控制报错 |
| F₃ 求秩快路径 | `standalone/rank_f3_fast_check.cc`：与**独立写的**通用 Gauss–Jordan 随机对拍，8 种形状（9×81、9×9、16×128、…）× 均匀 / 低秩 / 全零 | 20 万次 **0 不匹配**；直方图显示每种形状的各秩都被采到 |
| F₃ 展平秩快路径 | 同一件：随机张量 × 随机阈值，形状 (9,9,9) / (2,3,4) / (5,4,6) | 9 万次 **0 不匹配**；返回值覆盖 0–9 |
| F₃ 规范形快路径 | `rank_f3_fast_check.cc` 的「规范形」一节：随机 0–12 行 × 9（或 4）列，与通用 `GaussJordanEliminationFq` 比输出与秩 | 1.2 万次 **0 不匹配**；各秩都被采到 |
| F₃ 群作用快路径 | `standalone/apply_check.cc`：**全部** 19683 个向量 × 11232 个 store 元 × 22464 个 query 元，与独立朴素实现比 `Apply`，另查 `ApplyInverse ∘ Apply = id` 与单位元 | **0 不匹配**（store / query / 逆 / 单位元）；数位运算版与查表版各跑过一遍 |
| Get 批量内核：块内核 | `standalone/get_simd_check.cc`：随机 q（1–9 行）× 真实 Query 元素，NEON 版 vs 标量版比行 / 主元标志 / 标签，并与「逐个探针用框架的 `query.Apply` + `GaussJordanRREF`」核对 | **0 不匹配**（32000 道） |
| Get 批量内核：端到端 | 同一件：真实 `OrbitMap` 的 `Get` vs 独立重写的标量逻辑，比首命中下标 / 界 / 见证；其中 2 个键 × 全部 22464 个 Query 元素逐一枚举（无假阴性），并核对见证满足命中方程；一半查询带 1–3 条相关行（204 次超过 9 行） | **0 不匹配**（47928 次 Get） |
| Get 批量内核：未命中 | 同一件：300 个随机 q（209 个不在任何轨道里）上 `ProbeAll` 与标量逻辑同未命中 / 同命中 | **0 不匹配** |
| 快路径后的回归 | F₂ verifier / F₂ 枚举 / F₃ verifier / F₃ 枚举 / 轨道大小守恒 | 20 / OK；496 条逐条一致；OK；736 条不变；10 维精确相等 |
| 复现性 | 干净上游 + 补丁 + 新文件 + 本目录垫片（`otool -l` 按段比较） | 代码段 / 数据段逐字节相同；差异只在 `LC_UUID` 与代码签名 |
| 回溯叶子里的重复因子（审计，不是门禁） | 在 `bt_fq.c` 上加计数的审计内核：叶子处「基 ∪ 选中的行」的秩 < 行数的叶子数 | v1：18,822,872 个叶子里 4,669,134 个（307 / 339 条回溯轨道，最大重复 6 次）；属设计，见 §5.3 |
| 独立核对器的缓冲 | `test_wang_cert_check_fq.py`：同一因子重复 2 / 3 / 17 次的记录 | 修复前深度 17 的记录写越界 abort；修复后接受，且多报 1 的声明被拒 |
| Get 只依赖行空间 | `standalone/get_simd_check.cc` E 项：已存键的行随机重复 / 随机线性组合 / 打乱行序（可超过 9 行）后 `Get` vs 去重后的规范行 vs 标量逻辑 | **0 不匹配**（2000 次；界 + 一对见证逐项相同） |
| 回溯搜索去重键 | `test_wang_f3ext_fastpath.py::test_backtracking_dedup_keys_same_as_upstream`：同一二进制三种模式从零算 dim 9–6，比证书与 `.btp` 的 sha256 | **逐字节相同**（证书 `c56c8678…` / 轨迹 `9a8c65b2…`）；CPU 56.79 s → 5.92 s |

`engineering/tests/test_wang_f3ext_fastpath.py` 是这些对拍的 unittest 版（求秩 / 展平秩 / 规范形 / 剪枝各 4000 次；群作用按步长 17 抽样，`WANG_SLOW=1` 跑全量；Get 批量内核跑 `get_simd_check`，非 ARM64 机器跳过；上游副本缺失时跳过）。

轨道大小守恒（`Σ|orbit|` 与 `[9 choose d]₃`）：

| d | 轨道数 | Σ\|orbit\| = 子空间总数 |
|---|---|---|
| 0 / 9 | 1 / 1 | 1 |
| 1 / 8 | 3 / 3 | 9,841 |
| 2 / 7 | 14 / 14 | 8,069,620 |
| 3 / 6 | 84 / 84 | 678,468,820 |
| 4 / 5 | 266 / 266 | 6,174,066,262 |

合计 **736 条轨道**（F₂ 同格式是 496 条）。同一检验在 F₂ 公开证书上也逐维相等
（1, 3, 14, 68, 162, …），这是对计数方法本身的校验。枚举耗时 22.4 s 实时 / 200 MB 峰值内存（8 核）。

## 7. F₃ 下界搜索结果

### 7.1 证书 v1：GF(3) 上 ⟨3,3,3⟩ 的秩 ≥ 17（2026-11-27）

文件：`certs/matrix_q03_n333_v1.pb.txt`（322 KB）+ `certs/matrix_q03_n333_v1.btp`（13.0 MB，回溯证明的轨迹档案）。

```
sha256  5b6885472c0c77a82673da90fdaac941f888e3ad42bc490b9d326b0695ae302c  matrix_q03_n333_v1.pb.txt
sha256  23c35902b20edfb50b417806877677bbe1145b0d29d2ac86c39f931d87bd6bd1  matrix_q03_n333_v1.btp
```

重跑三重验证（需要先按 §2、§4 构建出 `/tmp/wang-f3/verifier_f3`）：

```bash
bash engineering/wang_f3ext/verify.sh engineering/wang_f3ext/certs/matrix_q03_n333_v1.pb.txt
```

实测结果（2026-11-27）：

| 步骤 | 结果 |
|---|---|
| ① 框架 C++ verifier | `Verified. Rank lower bound for matrix_q03_n333 is 17.` / `OK.`（8.7 s CPU） |
| ② 独立核对器（Python + `forced_fq` + `bt_fq`） | 736/736 轨道 OK：flatten 15 + forced 2 + backtracking 339 + degenerate 380；回溯重放 22,520,923 个节点（60 s CPU） |
| ③ 负控制（终轨道 17 → 24） | `orbit 735: backtracking kernel rejected: claim > proved` |

逐维的界与证明类型、和 F₂ 公开证书的对照，见 `docs/techniques/OpenAI-omega-9-4-只读审计-2026-11-25.md` §M.6。

### 7.2 这份证书是怎么跑出来的

枚举（22 s）之后分两段续跑，每段做完一个维度落一次检查点：

| 段 | 维度 | forced product 预算 | 回溯步数上限 / 轨道 | 耗时（8 核，与其它搜索共享 CPU） |
|---|---|---|---|---|
| 第一段 | 9 → 5 | 2^28 | 1e7 | dim 5: 2252 s |
| 第二段（在第一段的检查点上续跑，不加 `--ignore_rank_lower_bound`） | 4 → 0（`--dim_max=4`） | 2^28 | 1e6 | dim 4: 3858 s；dim 3: 2667 s；dim 2: 463 s；dim 1: 138 s；dim 0: 36 s |

命令（在 `/tmp/wang-run` 下的副本上）：

```bash
# 第一段
lower_f3 f3.pb.txt --ignore_rank_lower_bound --backtracking_step_limit=10000000 \
    --forced_product_max_iterations_log2=28 --backtracking_max_map_size=2000000
# 第二段: 直接在同一条证书上续跑, 只处理 dim ≤ 4
lower_f3 f3.pb.txt --dim_max=4 --backtracking_step_limit=1000000 \
    --forced_product_max_iterations_log2=28 --backtracking_max_map_size=2000000
```

### 7.3 这个结果不说明什么

- **17 低于域泛型已知的下界 19**（Bläser 2003），所以这份证书**没有刷新 F₃ 的下界**。它的价值是「机器可查」+「基础设施」。
- 它是下界：说明秩 ≥ 17，不说明秩 = 17。已知上界仍是 23（Laderman 方案，库内 `rank-laderman`）。
- 搜索有随机性（回溯缓存的随机减半、线程时序）：重跑不保证得到同一份证书。可复现的是**核验**，不是搜索。
- 加预算不等于能涨：按 §5.3 的代价结构，dim 0 的 18 要等 dim ≥ 2 的界先涨，而那些维度受同一结构约束。
  F₂ 用满了 2^32 + 1e7 步全程；F₃ 这边同样的预算能不能涨、涨到哪里 [未验证·路线推测]。
  能确定的只有一件事：只调大回溯步数、不动别的，在 dim 0 上离 18 很远（§5.3 的计数）。

### 7.4 续跑 v2：1e7 步全程（2026-11-27，旧二进制）

在 v1 上不加 `--ignore_rank_lower_bound` 续跑 dim 5–0，回溯步数上限 1e7（v1 在 dim ≤ 4 只用了 1e6）：

| 维 | v1 的界（轨道数） | v2 的界（轨道数） | 用时 |
|---|---|---|---|
| 5 | 10: 1，11: 4，12: 95，13: 166 | **不变**（266 条逐项一致） | 1264 s |
| 4 | 12: 3，13: 112，14: 151 | 12: 3，13: 91，**14: 172** | 3834 s |
| 3 | 13: 1，14: 80，15: 3 | 13: 1，14: 48，**15: 35** | 2321 s |
| 2 | 15（全部 14 条） | **不变** | 529 s |
| 1 | 16（3 条） | **不变** | 95 s |
| 0 | **17** | **17（不变）** | 24 s |

合计 53 条轨道改进、0 条退步；8070 s 实时 / 52,497 CPU 秒。**终界没有动**：dim 2 的 14 张平面一张都没到 16，
所以 dim 1 停在 16、dim 0 停在 17。按 §5.3 的结构，平面的界至少是「过它的 3 维空间里界最小的那个 + 1」，要再高只能靠更深的闭合；
dim 3 到 15 的轨道从 3 条涨到 35 条之后 dim 2 仍然一张都没到 16 [未验证: 各平面过了多少个 L ≤ 14 的 3 维空间我没有逐条数]。

三重验证：① 框架 verifier `OK`；② 独立核对器 736/736（flatten 15 + forced 2 + backtracking **392** + degenerate 327，
回溯重放 184,940,900 个节点，302 s CPU，峰值内存 2.7 GB）；
③ 负控制（终轨道 17 → 24）：`orbit 735: backtracking kernel rejected: claim > proved`，rc = 1。
重跑：`bash engineering/wang_f3ext/verify.sh ~/work/wang-f3-certs/matrix_q03_n333_v2.pb.txt`。

证书没有进 git：轨迹档案 114 MB（v1 是 13 MB；dim 3 与 dim 4 各约 1 GB 未压缩）。文件在
`~/work/wang-f3-certs/matrix_q03_n333_v2.{pb.txt,btp}`：

```
sha256  ca9cfebf94d7a0eb19b4160d1788a89d75957e27587dcb2f6a3e2015945339ac  matrix_q03_n333_v2.pb.txt
sha256  040336bb6687a5f4eb5d5b82d583e3f53206815c87df567917c741d67875b982  matrix_q03_n333_v2.btp
```

续跑的两条经验：

- A 段（dim 9–6，`--forced_product_max_iterations_log2=30`）24 秒跑完、0 条变化——forced product 对已有界的轨道不重跑（§8 第 7 条）。
  dim 6 那一遍的唯一作用是回归：102 条轨道与 v1 逐项一致。
- dim 5 在 1e7 步下重跑也与 v1 逐项一致（266 条），说明 v1 的 dim 5 在这个预算下已经饱和，涨不动是因为 dim 6 没涨。

## 8. 踩坑记录

1. **垫片分块的差一错误（已修，`shim_test/` 防回归）**。
   现象：F₃ 下界搜索在 dim = 6 处 `F Constraints not found in OrbitMap (size=7)`。
   定位：给 `OrbitMap::Get` 加转储，发现失败的约束组 **7 行只有秩 6**；再给回溯调用点加转储，
   看到 `max_constraint_idx = 13` 而 `n_minimal = 13`——回溯搜索顶层的 `parallel_for` 访问了越界下标。
   根因：垫片的 `parallel_for` 只让**最后一个线程**把区间终点钳到 `last`；分块不整除、且末块起点已 ≥ `last` 时，
   该线程直接不运行，于是**倒数第二块**的终点越过 `last`（n = 13、8 线程时块长 2，区间成了 `[12, 14)`）。
   越界读到零向量 → 约束组秩不足 → 跨度等于基本身、尚未入图 → FATAL。
   修法：区间终点一律 `std::min(last, …)`（`parallel_for.h` 两处、`parallel_reduce.h` 一处）。
   **F₂ 的各维轨道数（1, 3, 14, 68, 162）恰好都不触发这个组合，所以修复前的 F₂ 回归「碰巧」是绿的。**
   这提醒：回归通过 ≠ 垫片正确，要针对垫片自己的逻辑单写测试。
2. **排查顺序的教训**：先怀疑了自己的 F₃ 群作用实现和上游枚举器的完整性，各写了一个独立检验
   （§6 的第 3、4 行），两项都通过之后才转去给框架本身加转储。如果一开始就在崩溃点打印输入
   （秩、调用者），一轮就能定位。
3. **zsh 不分词**：`$DEFS`、`$COMMON` 这类装着多个参数的字符串变量在 zsh 里不会被拆开；
   要么用数组，要么用 `bash -c`。
4. **forced product 在 F₃ 上更容易被上限截断**：枚举量是 `3^(r2p·r1)` 而不是 `2^(…)`，
   默认 `--forced_product_max_iterations_log2=24` 下 dim ≤ 7 的多数轨道直接
   `Cancel Forced Product … exceeds 2^24`；正式参数用 32。
5. **`verifier` 需要 `.btp` 旁车**：证书与旁车必须同名同目录（`x.pb.txt` + `x.btp`），
   只拷 `.pb.txt` 会在打开旁车时 `CHECK failed`。
6. **速度边界**：F₃ 没有位打包快路径，forced product 的代价由枚举量 q^(r2p·r1) 决定——
   默认 `--forced_product_max_iterations_log2=24` 会把 dim ≤ 7 的大多数轨道直接
   `Cancel Forced Product … exceeds 2^24`。加大预算能改进界（实测 log2 = 32 把 dim 7 的三条轨道
   从 10–11 提到 12），但 3^18 的枚举在没有快路径时是 16 分钟 / 投影位。所以跑法是**分阶段**：
   先用中等预算拿一份完整可验证的证书，再用大预算只对高维做改进、然后向低维传播
   （上游对大格式也是这么做的：`run.py` 里 `dim_min` / `dim_max` 分两遍）。
7. **续跑时 forced product 根本不跑**：`ProcessOrbit` 里 flatten 与 forced product 都挂在
   `!rt.has_rank_lower_bound()` 后面——已有界的轨道直接跳过，只有 degenerate 与 backtracking 会重算。
   2026-11-27 的 v2 续跑 A 段（dim 9–6，`--forced_product_max_iterations_log2=30`）24 秒跑完、0 条变化，
   就是因为这个。要在已有证书上重算 forced product，只能带 `--ignore_rank_lower_bound` 从头算。
8. **差点把设计当漏洞**：见 §5.3。教训是「叶子处行组线性相关」这种观察，在对称群 / 子空间那一层看像错，
   在「假想分解的乘积项」那一层看才对。下结论前先读论文的论证，再写对拍。
9. **独立核对器的两处越界（已修，带回归测试）**：`bt_fq.c` 的路径 / 行组缓冲按 16 开，claim > 17 时
   `path_idx[16]` 写越界（对上游 F₂ ⟨3,3,3⟩ 证书 dim ≤ 4 重放时 abort）；记录数组是 1<<22 的静态数组，
   上游 dim 4 的证明超过 419 万条，直接拒收。现在缓冲 40（claim ≤ 32）、记录动态分配。
   F₃ 证书目前 claim ≤ 17，没有触发过；但往上做就会触发。
10. **去重键的第一版越界（已修）**：末行自成一类时它的代表位置不在 `rep_of_cls` 里，第一版照样去取
    `rep_of_cls[maskable]`，dim 6 一跑就段错误。修法是把末行单独处理（`f3_build_key`）。
    教训：新增一种「类」时，代表表、重数表、下标范围三处要一起过一遍；等价回归一跑就抓到了，说明回归本身是值得先写的。
11. **存盘的补丁要和上游树对账**：`f3_extension.patch` 不含 `MODULE.bazel.lock`（抓依赖时被改写，与补丁无关），
   直接 `git diff` 全树会和存盘的不一致。对账命令：
   `git -C /tmp/wang-tensor-rank diff -- core search problems/matrix/BUILD problems/matrix/problem.h problems/matrix/symmetry.h`。
12. **zsh 的 `set -- $var` 不分词**：`for spec in "tag ENV=1"; do set -- $spec` 在 zsh 里 `$spec` 是一个整体，目录名里带上了空格和等号。
    循环体里要分词的变量，用 bash 跑脚本，或者写成数组。

## 9. 垫片的边界（诚实声明）

- **tbb**：`std::thread` 分块实现，嵌套并行区域退化为串行。它**不是** oneTBB 的任务调度：
  回溯搜索里的「缓存随机减半」和「提前退出」依赖线程时序，所以**搜索结果不保证与 bazel 版逐位一致**，
  不同次运行也可能得到不同的（都是合法的）证书。证书的正确性由 verifier 与独立核对器保证，不靠搜索的可复现性。
- **protobuf**：手写的反射层，只实现框架用到的消息、字段与文本/二进制编解码，不是通用实现。
- **ng-log / gflags**：`LOG` 打到 stderr，旗标是进程内注册表；没有实现日志文件轮转等特性。
