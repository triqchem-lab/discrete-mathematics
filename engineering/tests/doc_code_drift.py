#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""文档承诺 ↔ 代码存在性 交叉校验（只读扫描器）。

背景（2026-09-10 考古）：本仓库反复出现「文档/注释承诺的符号 ≠ 代码里存在的符号」，
已确认 3 次，全部由人工追问触发。本脚本把其中**最机械可查的那一类**自动化。

能抓 / 不能抓（诚实边界，勿高估）：
  ✅ **A 类：文档/注释承诺的符号名在代码中不存在**
     历史实例：`CyclicGroupStructure.agda` 头注释承诺 `mixedOp-power-add` 与 `dc-order-12`，
     而两者在代码里都不存在（后被块 7 实现）。
  ❌ **B 类：符号存在但语义不符** —— 历史实例：`07-proof-status.md` 的 G4 条标题写 `mulAlpha`，
     但证明里的算子是 `mixedOp`（`mulAlpha` 定义在 AlphaPower 上，`toDuodec` 不接受该类型）。
     名字都能 grep 到，grep 抓不到这种错位。
  ❌ **C 类：文档陈述的规则本身不可执行** —— 历史实例：`proof-engineer` 附录 4
     「在使用的模块顶部添加 fixity 声明」写在文档里，但 Agda 报 `UnknownNamesInFixityDecl`。
     规则不是符号名，抓不到。

分级（避免淹没在噪声里）：
  Tier-1  .agda 头注释里形如 `--   name : 说明` / `-- 包含：a / b / c` 的名字  → 高置信错位
  Tier-2  .md 反引号里的标识符                                              → 候选，需人工过

已知**假阳性类**（Tier-1 里也会出现，数量少、易人工剔除）：
  · 外部语料锚：如 `LatticeMembrane.agda` 头注释 `-- 语料锚 (word_5, word_72):` 里的
    `word_5` / `word_72` —— 是语料标签，不是 Agda 符号承诺。
  · 小节/层级标签：如 `P3-C`。
  （形状过滤 `sym_like` 已剔掉大写开头的标签；语料锚是小写开头 + 含 `_`/数字，形状上与真符号无法区分，
    故保留为待人工判定项。）

用法：
  python3 doc_code_drift.py                 # 扫当前工作区
  python3 doc_code_drift.py --rev HEAD~5     # 回放历史提交（回归测试用）
  python3 doc_code_drift.py --tier 1         # 只看 Tier-1

只读：不写任何文件。
"""

import argparse
import glob
import os
import re
import subprocess
from collections import defaultdict

from oracle_kit import manifest  # noqa: E402

ROOT = "/data/work/discrete-mathematics"
AGDA_GLOB = "src/**/*.agda"

# 标识符形（Agda 常见命名字符；含 Unicode 下标与撇号）
IDENT = re.compile(r"^[A-Za-z][A-Za-z0-9′₀-₉_\-']*$")
# .agda 头注释：`--   name : ...`
HDR_NAME = re.compile(r"^--\s+([A-Za-z][A-Za-z0-9′₀-₉_\-']*)\s*:")
# .agda 头注释：`-- 包含：a / b / c` 或 `-- 包含: a、b`
HDR_LIST = re.compile(r"^--\s*包含[：:]\s*(.+)$")
BACKTICK = re.compile(r"`([^`\n]+)`")

def sym_like(tok):
    """形状过滤：本库的 Agda 定义名几乎都是**小写开头**且含 `-` / `_` / 内部大写 / 数字。

    不加这层会怎样（实测）：Tier-1 从 93 条错位里冒出 `BCW`（`-- 包含：` 后面的散文列表）、
    `Dvir`（数学家名作小节标签）、`P3-C`（层级标签）—— 三个采样的假阳性全部是**大写开头**。
    而两条真阳性 `mixedOp-power-add` / `dc-order-12` 都是小写开头且含 `-`。
    """
    if not tok or not tok[0].islower() or len(tok) < 4:
        return False
    if not IDENT.match(tok):
        return False
    return ("-" in tok or "_" in tok
            or any(c.isupper() for c in tok[1:])
            or any(c.isdigit() for c in tok))


# 默认排除的文档（**不是本库的符号承诺**）。每条附理由，运行时打印，便于审计。
# 判据：文档讲的是「Agda 语言/编译器」或「别的项目」，其符号属外部生态。
EXCLUDED_DOCS = (
    ("docs/agda/", "Agda 语言语法参考（讲 Agda 本身；符号属语言/stdlib，非本库承诺）"),
    ("docs/agda-3733-injectivity-deep-analysis.md", "Agda 编译器内部机制分析（符号属 Agda 源码）"),
    ("docs/agda-compiler-architecture.md", "同上"),
    ("docs/agda-p0-p3-proof-plan.md", "计划文档（名字是待办，不是承诺）"),
    ("docs/1lab-README.md", "第三方 README（1Lab 项目）"),
    ("docs/千禧年基础设施路线图.md", "路线图（计划性）"),
)

# 已知的**假阳性类**（2026-09-10 用 424 条未命中逐类量过，量在注释里）：
#   · 文档来源是外部生态（Agda 语言参考 / Lean 项目 / 第三方 README）→ 由 EXCLUDED_DOCS 处理（约 313 条）
#   · token 出现在**路径**里（如 `/data/work/leanprover/fermats-last-theorem`）→ 约 50 条
#   · **共享前缀缩写**（如文档写 `pow12-zero-suc/six-nilpotent` 代指 `pow12-six-nilpotent`）→ 约 5 条
#   · 数学**公式片段**（如 `ac-bd`）、**反例引证**（如 `chern2Proof = refl` 作反面例子）、
#     **审计记录里被点名的历史错误名**（如 `rho-inverse`，文档已注明其 NotInScope）
#   · ⚠ 曾假设「纯 snake_case = 外来符号」—— **被实测否掉**：本库代码里本身就有 49 个
#     snake_case 标识符，故该假设**不可用**作过滤条件。


def in_path_context(line, tok):
    """token 是否出现在路径串里（`/a/b/<tok>` 或 `<tok>/...`）。"""
    return bool(re.search(r"/[\w./-]*" + re.escape(tok) + r"(?![\w-])", line)
                or re.search(re.escape(tok) + r"/", line))


# --- 文档类别：决定「未命中」算不算错位 ---------------------------------------
# spec     承诺**当下**代码形态（`docs/duodecimal/` 权威规范、README、接口说明）
#          → 未命中 = 真错位（Tier-1 全部属此类）
# snapshot 记录**某个时点**的状态（逐模块审计记录、带审查日期的报告）
#          → 未命中 = 历史引用，**不算错位**：代码之后重写过，记录本身没写错
#
# 为什么必须分开（实测）：`docs/line-audit/Sovereign_Geometry.md` 声称
# `ConformalCore.agda` 顶层有 `tritOf-finOf` / `scaleElem` / `ofFin-toFin` …… 全部
# `code:0`；`docs/MATH-COMPLETENESS-REVIEW.md` 头部写「审查日期 2026-04-27、审查范围
# 79 文件」——而现在是 512 个 .agda。把这类历史名当错位去「修」，等于**篡改历史记录**。
SNAPSHOT_PATHS = ("docs/line-audit/",)
SNAPSHOT_WORDS = ("审计记录", "审计日期", "审查日期", "快照", "snapshot", "Snapshot",
                  "审查范围", "截至", "本报告基于", "历史记录", "已被移除")
# 文件名里带日期的文档 = 记录该日期的状态（实测：`*_2026-04-24.md` 三份共 47 条未命中）。
SNAPSHOT_DATE = re.compile(r"20\d\d-\d\d-\d\d")


def doc_class(path, txt):
    if any(path.startswith(d) for d in SNAPSHOT_PATHS):
        return "snapshot"
    if SNAPSHOT_DATE.search(path):
        return "snapshot"
    head = txt[:2000]
    return "snapshot" if any(w in head for w in SNAPSHOT_WORDS) else "spec"


def doc_reason(path, txt):
    """snapshot 的判据（打印出来便于反驳，不藏在代码里）。"""
    if any(path.startswith(d) for d in SNAPSHOT_PATHS):
        return "路径 %s（逐模块审计记录）" % SNAPSHOT_PATHS[0]
    m = SNAPSHOT_DATE.search(path)
    if m:
        return "文件名含日期 %s" % m.group(0)
    head = txt[:2000]
    for w in SNAPSHOT_WORDS:
        if w in head:
            return "头部含时点标记 %r" % w
    return ""


# --- Tier-3：文档引用的 .agda **路径**是否存在 --------------------------------
# 这是**机械可核**的一类（不像 Tier-2 靠名字形状猜）：文档说「文件: X.agda」，
# 那个文件在不在，没有歧义。实测：`docs/duodecimal/README.md:125` 引用
# `src/Sovereign/Algebra/Dihedral/ShortExactSequence.agda` —— 该文件不存在且
# `git log --diff-filter=AD` 为空（**从未入库**，是工作区草稿被删）；这是 Tier-1/2 都
# 抓不到的真错位。
#
# 解析必须容忍文档里实际出现的四种写法（实测全部存在）：
#   `Physics/NSE.agda`（相对 Sovereign）/ `src/Sovereign/.../X.agda` / `../../src/...`
#   / `Sovereign.Structology.A4Group.agda`（**点号模块名又加 .agda**，常见笔法）
# 最后退化到「basename 唯一」匹配，避免把 `Axioms.agda` 误判为悬空。
EXTERNAL_PATH_MARKERS = ("agda-stdlib", "cubical", "agda-categories", "agda-algebras",
                         ".stack-work", "1lab", "mathlib", "node_modules")


def norm_modpath(m):
    m = m.strip()
    if m.endswith(".agda"):
        m = m[:-5]
    m = m.lstrip("./")
    while m.startswith("../"):
        m = m[3:]
    if m.startswith("src/"):
        m = m[4:]
    if m.startswith("Sovereign/"):
        m = m[len("Sovereign/"):]
    return m


def make_resolver(rev):
    # ⚠ `agda_paths_for` **已经**返回相对 ROOT 的 `src/...` 形式；**不要**再套一层
    # `os.path.relpath(p, ROOT)`——那样会按 CWD（`engineering/tests`）解析成
    # `engineering/tests/src/...`，路径表全废，精确匹配恒失败（实测把 228 条虚报成 860 条）。
    paths = agda_paths_for(rev)
    bydot = {p[len("src/"):-5].replace("/", "."): p for p in paths}
    bybase = {}
    for p in paths:
        bybase.setdefault(os.path.basename(p), []).append(p)

    def resolve(m):
        """返回 (命中路径, 命中方式)：
        `exact`     文档写的约定写法直接命中；
        `loose`     只靠 basename 唯一命中 → **路径已迁移**（文件在别处）；
        `ambiguous` basename 命中 ≥2 个 → 文档只写了文件名，**信息不足**，不是错位；
        (None, None) 完全无命中 → 悬空。"""
        n = norm_modpath(m)
        for c in ("src/Sovereign/" + n + ".agda", "src/" + n + ".agda"):
            if c in paths:
                return c, "exact"
        d = n.replace("/", ".")
        if d in bydot:
            return bydot[d], "exact"
        if "Sovereign." in d:                      # Sovereign.X.Y.agda 写法
            k = d[d.index("Sovereign.") + len("Sovereign."):]
            if k in bydot:
                return bydot[k], "exact"
        cand = bybase.get(os.path.basename(n) + ".agda", [])
        if len(cand) == 1:
            return cand[0], "loose"
        if len(cand) > 1:
            return cand[0], "ambiguous"

        # 系统性改名：`jac_X.agda` 原在 `Algebra/Jacobian/`（该目录现只剩 15 个），
        # 千年问题模块整体搬到 `Problem/<问题>/X.agda` —— 规则就是**去掉 `jac_` 前缀**。
        # 实测：旧 `jac_*` 名 18 个全部在现库中一一对应（BSD/RH/Hodge/Langlands/
        # PvsNP_Separation/YM_DetMul/FrobeniusBlind/4320DClosure/Complexity/
        # EscapeAnalysis/Galois/WeilRH/ChainComplex/CubicRootTest/S4Burnside/…）。
        b = os.path.basename(n)
        if b.startswith("jac_"):
            tgt = bybase.get(b[len("jac_"):] + ".agda", [])
            if len(tgt) == 1:
                return tgt[0], "renamed"
        return None, None

    return resolve


def tier3_candidates(rev, md_paths, moved=True):
    """返回 (被引路径, 文档, 行号, 行内容, 文档类别)。

    默认**同时**收集两类（第三元素之后用 `moved` 标志区分）：
      · 悬空（`resolve` 完全失败）—— 文档指的文件根本不存在
      · 已迁移（只靠 basename 唯一命中）—— 文件还在，但**不在文档写的路径上**
    """
    resolve = make_resolver(rev)
    apath = re.compile(r"[A-Za-z0-9_./-]*[A-Za-z0-9_-]+\.agda")
    out = []
    for p in md_paths:
        txt = readsrc(p, rev)
        if txt is None:
            continue
        cls = doc_class(p, txt)
        for n, line in enumerate(txt.split("\n"), 1):
            for m in apath.findall(line):
                if any(e in m for e in EXTERNAL_PATH_MARKERS):
                    continue
                hit, how = resolve(m)
                if hit is None:
                    out.append((m, p, n, line.strip()[:90], cls, "dangling"))
                elif how == "ambiguous":
                    out.append((m, p, n, line.strip()[:90], cls, "ambiguous"))
                elif how == "renamed":
                    out.append((m, p, n, line.strip()[:90], cls, "renamed"))
                elif how == "loose" and "/" in m:
                    # 文档**写了路径**却只靠 basename 命中 → 文件真被搬走了
                    out.append((m, p, n, line.strip()[:90], cls, "moved"))
                elif how == "loose":
                    # 文档只写文件名（`T6.agda`）→ 短引，不是错位
                    out.append((m, p, n, line.strip()[:90], cls, "shortform"))
    return out


# 反引号里的常见非符号内容（叙述、命令、文件名、Agda 关键字、英文词）
STOP = set("""
agda git docs src make pnpm python pytest bash shell oracle proof_dag
postulate data record module where using open import renaming hiding public
refl sym trans cong subst funext Set Set1 Level Goal
true false yes no Bool Dec
readme md json yaml toml lib
Tier Tier-1 Tier-2
""".split())


def git(*args):
    return subprocess.run(("git",) + args, cwd=ROOT, capture_output=True,
                          text=True).stdout


def readsrc(path, rev):
    """路径 -> 文本；rev=None 时读工作区（相对路径），否则读该 rev（仓库相对路径）。"""
    if rev is None:
        full = os.path.join(ROOT, path)
        if not os.path.exists(full):
            return None
        with open(full, encoding="utf-8") as fh:
            return fh.read()
    return git("show", "%s:%s" % (rev, path)) or None


def agda_paths_for(rev):
    if rev is None:
        # 注意：不能用 `ls src/**/*.agda`（bash 默认不递归，只匹配两层）
        #
        # ⚠ 必须排除 `_standalone/`：它是**指向外部论文目录**的符号链接
        #   `src/Sovereign/Algebra/Jacobian/_standalone -> /data/work/dissertation/Jacobian`，
        #   `glob` 会**跟随**它，把外部项目的 32 个 .agda 混进本库索引（本库真实数 557，
        #   加上它才是 589）。后果有二：(a) 「符号存在」可能被**外来文件**满足，检查失真；
        #   (b) 它复制了整库文件名，制造 41 组重名 basename，使「只写文件名」的引用
        #   被误判成悬空（实测 `GF9.agda`/`A4Group.agda` 等一律假阳性）。
        return sorted(os.path.relpath(p, ROOT) for p in
                      glob.glob(os.path.join(ROOT, "src", "**", "*.agda"),
                                recursive=True)
                      if "/_standalone/" not in p)
    out = git("ls-tree", "-r", "--name-only", rev, "src/")
    return [p for p in out.split()
            if p.endswith(".agda") and "/_standalone/" not in p]


def strip_comments(txt):
    """剥掉 Agda 注释（`--` 行注释 + 可嵌套的 `{- -}` 块注释，含 `{-# ... #-}` 编译指示）。

    ⚠ 关键（第二次踩坑，是设计层的错）：**索引必须排除注释**。
    否则「只出现在注释里的名字」会被算作「代码中存在」，扫描器**永远抓不到
    注释承诺型错位** —— 而那正是它要抓的那一类。
    实测：HEAD 的 `CyclicGroupStructure.agda` 里 `git grep -c mixedOp-power-add` 命中 1 次，
    但那唯一一次就是**头注释那一行本身**。
    """
    out = []
    depth = 0
    i, n = 0, len(txt)
    while i < n:
        if txt.startswith("{-", i):
            depth += 1
            i += 2
            continue
        if depth > 0 and txt.startswith("-}", i):
            depth -= 1
            i += 2
            continue
        if depth == 0 and txt.startswith("--", i):
            j = txt.find("\n", i)
            i = n if j < 0 else j
            continue
        if depth == 0:
            out.append(txt[i])
        i += 1
    return "".join(out)


def code_index(rev):
    """返回 {token: [file,...]}；token = 每个 .agda 的**代码部分**（剥注释后）出现的全部标识符。

    ⚠ 首次踩坑：用 `ls src/**/*.agda` 取文件列表（bash 默认不递归）只拿到 17 个文件，
    索引残缺 → 几乎全部候选被误报为缺失。
    """
    idx = defaultdict(list)
    for p in agda_paths_for(rev):
        txt = readsrc(p, rev)
        if txt is None:
            continue
        for tok in set(re.findall(r"[A-Za-z][A-Za-z0-9′₀-₉_\-']*",
                                  strip_comments(txt))):
            idx[tok].append(p)
    return idx


def tier1_candidates(rev):
    """从 .agda 头注释抽取「承诺的名字」——只取 module 声明之前的注释块。"""
    out = []
    for p in agda_paths_for(rev):
        txt = readsrc(p, rev)
        if txt is None:
            continue
        for n, line in enumerate(txt.split("\n"), 1):
            if line.startswith("module "):
                break
            m = HDR_NAME.match(line)
            if m and sym_like(m.group(1)):
                out.append((m.group(1), p, n, line.strip()))
                continue
            m = HDR_LIST.match(line)
            if m:
                for tok in re.split(r"[ /、,，]+", m.group(1)):
                    tok = tok.strip()
                    if sym_like(tok):
                        out.append((tok, p, n, line.strip()))
    return out


def tier2_candidates(rev, md_paths):
    out = []
    for p in md_paths:
        txt = readsrc(p, rev)
        if txt is None:
            continue
        cls = doc_class(p, txt)
        for n, line in enumerate(txt.split("\n"), 1):
            for span in BACKTICK.findall(line):
                for tok in re.split(r"[ /、,，()（）]+", span):
                    tok = tok.strip()
                    if tok in STOP or not sym_like(tok):
                        continue
                    out.append((tok, p, n, line.strip()[:90], cls))
    return out


def md_paths_for(rev, all_docs=False):
    if rev is None:
        ps = sorted(os.path.relpath(p, ROOT) for p in
                    glob.glob(os.path.join(ROOT, "docs", "**", "*.md"),
                              recursive=True))
    else:
        ps = [p for p in git("ls-tree", "-r", "--name-only", rev, "docs/").split()
              if p.endswith(".md")]
    if all_docs:
        return ps
    return [p for p in ps if not any(p.startswith(d) for d, _ in EXCLUDED_DOCS)]


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--rev", default=None, help="回放历史提交（回归测试用）")
    ap.add_argument("--tier", type=int, default=3, choices=(1, 2, 3))
    ap.add_argument("--all-docs", action="store_true",
                    help="不排除外部生态文档（Agda 语言参考 / 第三方 README 等）")
    args = ap.parse_args()

    idx = code_index(args.rev)
    known = set(idx)  # 代码中存在的标识符

    t1 = tier1_candidates(args.rev)
    misses1 = [c for c in t1 if c[0] not in known]

    t2 = tier2_candidates(args.rev, md_paths_for(args.rev, args.all_docs))
    misses2 = [c for c in t2 if c[0] not in known
               and not in_path_context(c[3], c[0])]
    miss_spec = [c for c in misses2 if c[4] == "spec"]
    miss_snap = [c for c in misses2 if c[4] == "snapshot"]

    t3 = tier3_candidates(args.rev, md_paths_for(args.rev, args.all_docs))
    t3d = [c for c in t3 if c[5] == "dangling"]
    t3m = [c for c in t3 if c[5] == "moved"]
    t3a = [c for c in t3 if c[5] == "ambiguous"]
    t3s = [c for c in t3 if c[5] == "shortform"]
    t3r = [c for c in t3 if c[5] == "renamed"]
    t3r_spec = [c for c in t3r if c[4] == "spec"]
    t3d_spec = [c for c in t3d if c[4] == "spec"]
    t3d_snap = [c for c in t3d if c[4] == "snapshot"]
    t3m_spec = [c for c in t3m if c[4] == "spec"]

    where = args.rev or "工作区"
    print("=== 文档承诺 ↔ 代码存在性（rev=%s） ===" % where)
    print("代码标识符索引: %d 个 token / %d 个 .agda"
          % (len(known), len(agda_paths_for(args.rev))))
    if not args.all_docs:
        print("已排除 %d 个**外部生态**文档（--all-docs 可关）:" % len(EXCLUDED_DOCS))
        for d, why in EXCLUDED_DOCS:
            print("    %-46s %s" % (d, why))
    print("Tier-1 候选: %d ｜ 其中代码中不存在: **%d**" % (len(t1), len(misses1)))
    print("Tier-2 候选: %d ｜ 其中代码中不存在: %d" % (len(t2), len(misses2)))
    print("    ├ 快照文档的历史引用（**不算错位**）: %d 条 / %d 个 token"
          % (len(miss_snap), len({t for t, *_ in miss_snap})))
    print("    └ spec 文档的待核条目（**可能是真错位**）: %d 条 / %d 个 token"
          % (len(miss_spec), len({t for t, *_ in miss_spec})))
    print("Tier-3 路径核对（文档引用的 .agda 在不在）: %d 条 / %d 个不同路径"
          % (len(t3), len({m for m, *_ in t3})))
    print("    ├ 悬空（文件不存在）: %d 条 —— spec %d / snapshot %d"
          % (len(t3d), len(t3d_spec), len(t3d_snap)))
    print("    ├ 已迁移（文件在、但不在文档写的路径上）: %d 条 —— spec %d / snapshot %d"
          % (len(t3m), len(t3m_spec), len(t3m) - len(t3m_spec)))
    print("    ├ 旧名引用（`jac_X.agda` → `Problem/**/X.agda`，系统性改名）: %d 条 —— spec %d"
          % (len(t3r), len(t3r_spec)))
    print("    └ 信息不足/短引（只写文件名、库内重名或唯一）: %d 条（**不算错位**）"
          % (len(t3a) + len(t3s)))
    print()
    print("--- Tier-1 高置信错位（.agda 头注释承诺 / 包含列表） ---")
    if not misses1:
        print("（无）")
    for tok, p, n, line in misses1:
        print("  %-28s %s:%d" % (tok, p, n))
        print("      %s" % line)
    if args.tier == 2:
        print()
        print("--- Tier-2 待核（spec 文档：`docs/` 权威规范/接口说明里的符号） ---")
        seen = set()
        for tok, p, n, line, _ in miss_spec:
            if tok in seen:
                continue
            seen.add(tok)
            print("  %-28s %s:%d" % (tok, p, n))
            print("      %s" % line)
        if not miss_spec:
            print("（无）")

        print()
        print("--- Tier-2 快照文档历史引用（按文件计数，**不代表错位**） ---")
        byl = {}
        for tok, p, n, line, _ in miss_snap:
            byl.setdefault(p, set()).add(tok)
        ranked = sorted(byl.items(), key=lambda kv: -len(kv[1]))
        for p, toks in ranked[:12]:
            print("  %-50s %3d 个 token ｜ %s"
                  % (p, len(toks), doc_reason(p, readsrc(p, args.rev) or "")))
        if len(ranked) > 12:
            print("  …另有 %d 个快照文档" % (len(ranked) - 12))
        if ranked:
            allsnap = sorted({doc_reason(p, readsrc(p, args.rev) or "")
                              for p, _ in ranked} - {""})
            print("  判据汇总: %s" % " ／ ".join(allsnap))

    if args.tier == 3:
        print()
        print("--- Tier-3a spec 文档**悬空**路径（机械可核，逐条要人看） ---")
        seenp = set()
        for m, p, n, line, _, _ in t3d_spec:
            if m in seenp:
                continue
            seenp.add(m)
            print("  %-42s %s:%d" % (m, p, n))
            print("      %s" % line)
        if not t3d_spec:
            print("（无）")
        print()
        print("--- Tier-3b spec 文档**已迁移**路径（文件在别处，前 20 条） ---")
        seenq = set()
        shown = 0
        for m, p, n, line, _, _ in t3m_spec:
            if m in seenq:
                continue
            seenq.add(m)
            hit, _ = make_resolver(args.rev)(m)
            print("  %-34s → %-44s %s:%d" % (m, hit, p, n))
            shown += 1
            if shown >= 20:
                print("  …（spec 类已迁移路径合计 %d 个）"
                      % len({x[0] for x in t3m_spec}))
                break
        print()
        print("--- Tier-3c spec 文档**旧名引用**（`jac_X.agda` → 现址） ---")
        seenr = set()
        for m, p, n, line, _, _ in t3r_spec:
            if m in seenr:
                continue
            seenr.add(m)
            hit, _how = make_resolver(args.rev)(m)
            print("  %-34s → %-44s %s:%d" % (m, hit, p, n))
        if not t3r_spec:
            print("（无）")
        print()
        print("--- Tier-3 快照文档路径问题（历史架构，按文件计数） ---")
        byf = {}
        for m, p, n, line, _, k in t3d + t3m:
            if _ != "snapshot":
                continue
            byf.setdefault(p, set()).add(m)
        for p, ms in sorted(byf.items(), key=lambda kv: -len(kv[1]))[:10]:
            print("  %-50s %2d 个路径 ｜ %s"
                  % (p, len(ms), doc_reason(p, readsrc(p, args.rev) or "")))

    domain = len(t1) + len(t2) + len(t3)
    points = domain  # 逐个核对，无抽样
    manifest(
        basis="exhaustive",
        domain=domain,
        points=points,
        claim=("对 rev=%s：穷举全部 .agda 头注释里的承诺符号名（%d 个）、docs/*.md 反引号里的"
               "标识符（%d 个）、以及文档引用的 .agda 路径（%d 条），逐个在 %d 个 .agda 的"
               "词表/路径表中核对；报告 Tier-1 符号错位 %d 个；Tier-2 未命中 %d 条"
               "（快照历史引用 %d / spec 待核 %d）；Tier-3 路径异常 %d 条"
               "（悬空 %d = spec %d + snapshot %d；已迁移 %d = spec %d；"
               "旧名引用 %d = spec %d；短引/重名 %d 不算错位），按文档类别分开计数。"
               "⚠ 只覆盖「符号名/路径不存在」这一类（A 类）；语义不符（B 类）与规则不可执行（C 类）抓不到。"
               % (where, len(t1), len(t2), len(t3), len(agda_paths_for(args.rev)),
                  len(misses1), len(misses2), len(miss_snap), len(miss_spec),
                  len(t3), len(t3d), len(t3d_spec), len(t3d_snap), len(t3m), len(t3m_spec),
                  len(t3r), len(t3r_spec), len(t3a) + len(t3s)))
    )


if __name__ == "__main__":
    main()
