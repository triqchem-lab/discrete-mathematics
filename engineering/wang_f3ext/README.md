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
| `f3_extension.patch` | 对上游的补丁：`problems/matrix/symmetry.h`（新增 `SymmetryGroupFq` + 分发）、`problem.h`（注释、`kN0..kN2`）、`BUILD` |
| `fq_matrix.h` | 新文件：base-P 数位打包的小矩阵（`FqMatrix<P,N0,N1>`，转置 / 乘积 / 求逆 / 秩） |
| `fq_matrix_tables.h` | 新文件：GL 表、逆表、按行查表乘积表（`FqMatrixTables<P,N0,N1>`） |
| `fq_matrix_test.cc` | 新文件：上游 gtest 风格的扩展单元测试（bazel 下跑） |
| `shim/` | 手工构建用的垫片头文件树（`ng-log`、`gflags`、`tbb`、`boost/{unordered,iostreams}`、`google/protobuf`、`core/certificate.pb.h`），共 16 个文件 |
| `build.sh` | clang++ 直编脚本（不依赖 bazel / Xcode） |
| `shim_test/` | 垫片分块的回归测试（`run.sh` 对 `SHIM_THREADS=1..8` 各跑一遍） |
| `standalone/` | 不编译整个框架也能跑的 F₃ 扩展自检（`fq_matrix_test_main.cc`、`f3_problem_check.cc` + 一份极简串行 tbb 垫片） |
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
```

**实测（2026-11-27）**：从 `git archive 9db3d21` 得到的干净副本出发执行上面四步，
用本目录 `build.sh` 构建出的 `verifier_f3`、`enumerator_f3` 与工作副本构建的二进制**逐字节相同**（`cmp` 无差异）。

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

## 6. 验证证据（2026-11-27）

| 检查 | 做法 | 结果 |
|---|---|---|
| F₂ 回归（verifier） | `verifier_f2 real_cert_matrix_q02_n333.pb.txt` | `UNCONSTRAINED TENSOR RANK LOWER BOUND: 20` / `OK. Verified` |
| F₂ 回归（枚举） | `enumerator_f2` 输出 vs 公开证书，按轨道逐条比较约束字节串 | 496 条，序列完全一致 |
| F₃ 群作用 | 框架 `store.Apply` / `query.Apply` / `ApplyInverse` / 单位元 vs **独立朴素实现**（直接按 X·R、L·τᵗ(X) 循环），全部 3⁹ 个向量 × 全部群元 | 0 个不匹配 |
| F₃ 枚举**完整性** | 轨道大小守恒：对每条代表 c 数 (Q,S) 对中满足 Q·c ≡ S·c 的对数 → \|Stab\| → \|orbit\| = \|H\|/\|Stab\|，各维求和对比高斯二项系数 | 10 个维度**全部精确相等**（见下表） |
| 垫片分块 | `shim_test/run.sh` | 1–8 线程全过；对旧垫片的负控制报错 |
| 复现性 | 干净上游 + 补丁 + 新文件 + 本目录垫片 | 二进制逐字节相同 |

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

（见本文件同目录的提交说明与 `docs/plan/matrix-rank-line-plan.md` 的 A-T3 状态栏；本节只记可复跑的事实。）

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

## 9. 垫片的边界（诚实声明）

- **tbb**：`std::thread` 分块实现，嵌套并行区域退化为串行。它**不是** oneTBB 的任务调度：
  回溯搜索里的「缓存随机减半」和「提前退出」依赖线程时序，所以**搜索结果不保证与 bazel 版逐位一致**，
  不同次运行也可能得到不同的（都是合法的）证书。证书的正确性由 verifier 与独立核对器保证，不靠搜索的可复现性。
- **protobuf**：手写的反射层，只实现框架用到的消息、字段与文本/二进制编解码，不是通用实现。
- **ng-log / gflags**：`LOG` 打到 stderr，旗标是进程内注册表；没有实现日志文件轮转等特性。
