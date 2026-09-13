#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""fixity 审核 oracle —— 把「Agda 默认 fixity 是什么」这类断言交给编译器，不靠记忆。

被审核的两份论证都建立在可实测的事实断言上：
  过去态论证：① Agda 默认是 infixl 9（左结合最高优先级）  ② 无声明会导致**静默**错值
              ③ 应加 infixl 6/7 对齐标准库
  未来态论证：④ 本库用的是 infixr（右结合）「未来态」语义  ⑤ 右结合=未来态展开是项目本体论
              ⑥ 守卫类型论的 ▷ 是右结合的    ⑦ 库里用 mixedOp^_ 中缀算子
              ⑧ Agda fixity 不继承          ⑨ 各域模块重复声明是因为不继承

做法：在临时目录里生成最小探针模块，**真的调用 Agda**，按编译器输出判定每条断言。
不碰工作区（探针写 /tmp），不改任何库文件。

约定：每项检查 = (断言, 声称值, 实测值, 声称是否成立)。
      ✅ = 声称成立；❌ = 声称被实测推翻。计数只数 ❌。

【自身 bug 修复记录（2026-09-10，对抗自检抓出）】
  · 原版 ok 语义在不同检查间不一致（有的用「声称成立」有的用「声称被推翻」），
    导致 `1 默认级别` 出现「✅ + 声称 level 9 / 实测 level 20」的自相矛盾输出。
  · 原版 P_use / P_redecl 探针各自重复 `data A`，`open import P_lib` 撞名，
    「fixity 不继承」的结论被撞名错误污染（手工对照探针其实是编译通过的）。
  · 原版用 `mixedOp\\^` 搜「是否有该中缀算子」，会命中**散文注释**（误报 4 处）。
"""

import glob
import os
import re
import subprocess
import tempfile
from shutil import which

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
import os as _os


def _configured_agda():
    """从 preset 的 local-paths.json 读 agdaBin（与 proof_compile 同源，避免两处漂移）。"""
    p = _os.path.expanduser("~/.dsh/.agent-presets/math-proof/impl/local-paths.json")
    try:
        import json
        with open(p, encoding="utf-8") as f:
            return json.load(f)["paths"]["agdaBin"]["value"]
    except Exception:
        return None


# 优先级：环境变量 SOVEREIGN_AGDA > preset 配置 local-paths.json > 历史路径 > PATH 上的 agda。
# ⚠ 2026-09-11: 原先硬编码 /opt/agda/agda —— 系统 Agda 已切到 merged master 构建，
#   硬编码会静默使用旧二进制，故改为配置驱动。
AGDA_CANDIDATES = tuple(
    [c for c in (_os.environ.get("SOVEREIGN_AGDA"), _configured_agda(),
                 "/opt/agda/agda", "agda") if c])
HEADER = "{-# OPTIONS --guardedness #-}\nmodule %s where\n"
DATATYPE = "data A : Set where a b c : A\n"
OPS = ("_⊕_ : A → A → A\nx ⊕ y = a\n"
       "_⊗_ : A → A → A\nx ⊗ y = b\n")
FIXITY = "infixl 6 _⊕_\ninfixl 7 _⊗_\n"


def find_agda():
    for c in AGDA_CANDIDATES:
        if os.path.isabs(c) and os.path.exists(c):
            return c
        if not os.path.isabs(c):
            p = which(c)
            if p:
                return p
    raise RuntimeError("找不到 agda")


def write_mod(tmp, name, body):
    path = os.path.join(tmp, name + ".agda")
    with open(path, "w", encoding="utf-8") as f:
        f.write((HEADER % name) + body)
    return path


def compile_mod(binary, tmp, name, body):
    path = write_mod(tmp, name, body)
    r = subprocess.run([binary, "--guardedness", "-i", tmp, path],
                       capture_output=True, text=True, timeout=180)
    return r.returncode, (r.stdout + r.stderr)


def code_lines(txt):
    """去掉行注释后的代码行（判「有没有这个算子」必须看代码，不能看散文）。"""
    return [re.sub(r"--.*$", "", ln) for ln in txt.split("\n")]


def all_agda():
    for p in glob.glob(os.path.join(ROOT, "src", "**", "*.agda"), recursive=True):
        if "/_standalone/" not in p:
            yield p


def main():
    binary = find_agda()
    checks = []

    with tempfile.TemporaryDirectory() as tmp:
        # ── ① 未声明 fixity 的默认行为：混合运算符 ──────────────────
        rc, out = compile_mod(binary, tmp, "P_default", DATATYPE + OPS + "t : A\nt = a ⊕ b ⊗ c\n")
        parse_err = "NoParseForApplication" in out
        lvl20 = "level 20" in out
        lvl9 = re.search(r"level 9\b", out) is not None
        checks.append(("① 默认 fixity = infixl 9", "infixl 9",
                       ("ParseError" if parse_err else "编译通过") +
                       ("，级别 level 20" if lvl20 else ""), lvl9))
        checks.append(("② 无声明 ⇒ 编译通过（静默）", "编译通过",
                       "ParseError" if parse_err else "编译通过", not parse_err))

        # ── ①b 同算子连写 ────────────────────────────────────────────
        rc2, out2 = compile_mod(binary, tmp, "P_same",
                                DATATYPE + "_⊕_ : A → A → A\nx ⊕ y = a\nt : A\nt = a ⊕ b ⊕ c\n")
        same_err = "NoParseForApplication" in out2
        checks.append(("②b 同算子连写 ⇒ 静默左结合", "编译通过",
                       "ParseError" if same_err else "编译通过", not same_err))

        # ── ③ 在定义处声明 fixity 是否生效 ───────────────────────────
        rc3, _ = compile_mod(binary, tmp, "P_decl", DATATYPE + OPS + FIXITY + "t : A\nt = a ⊕ b ⊗ c\n")
        checks.append(("③ 定义处声明 infixl 6/7 后编译通过", "成立",
                       "编译通过" if rc3 == 0 else "失败", rc3 == 0))

        # ── ⑧ fixity 是否随 open import 继承 ─────────────────────────
        # ⚠ P_use **不得**重复定义 data A（否则撞名，结论无效——这是本脚本修掉的 bug）
        write_mod(tmp, "P_lib", DATATYPE + OPS + FIXITY)
        rcq, outq = compile_mod(binary, tmp, "P_use", "open import P_lib\nt : A\nt = a ⊕ b ⊗ c\n")
        inherited = rcq == 0
        checks.append(("⑧ fixity 不继承（需重复声明）", "不继承，应编译失败",
                       "编译通过（继承）" if inherited else "编译失败", not inherited))

        # ── ⑨ 能否为 import 来的名字声明 fixity ──────────────────────
        rcr, outr = compile_mod(binary, tmp, "P_redecl", "open import P_lib\ninfixl 6 _⊕_\n")
        redec = "UnknownNamesInFixityDecl" in outr
        checks.append(("⑨ 可为 import 来的名字声明 fixity", "合法",
                       "UnknownNamesInFixityDecl" if redec else "合法", not redec))

    # ── ④ 全库 fixity 实测（枚举，无抽样）───────────────────────────
    decls = []
    for p in all_agda():
        try:
            txt = open(p, encoding="utf-8", errors="replace").read()
        except OSError:
            continue
        for m in re.finditer(r"^\s*(infixl|infixr|infix)\s+(\d+)\s+([^\s;]+)", txt, re.M):
            decls.append((m.group(1), int(m.group(2)), m.group(3), os.path.relpath(p, ROOT)))
    additive = [d for d in decls if re.search(r"[+⊕⊞]", d[2])]
    mult = [d for d in decls if re.search(r"[*⊗·×⊠]", d[2])]
    add_l, add_r = sum(1 for d in additive if d[0] == "infixl"), sum(1 for d in additive if d[0] == "infixr")
    mul_l, mul_r = sum(1 for d in mult if d[0] == "infixl"), sum(1 for d in mult if d[0] == "infixr")
    checks.append(("④ 加法类方向 = infixr", "infixr",
                   "infixl %d / infixr %d" % (add_l, add_r), add_r > add_l))
    checks.append(("④b 乘法类方向 = infixr", "infixr",
                   "infixl %d / infixr %d" % (mul_l, mul_r), mul_r > mul_l))

    # ── ⑥ _▷_ 的实际声明 ────────────────────────────────────────────
    fab = os.path.join(ROOT, "src", "Sovereign", "HoTT", "Fibration.agda")
    fabtxt = open(fab, encoding="utf-8", errors="replace").read() if os.path.exists(fab) else ""
    m = re.search(r"^\s*infix([lr]?)\s+(\d+)\s+(_▷_)", fabtxt, re.M)
    dtri = ("infix" + (m.group(1) or "") + " " + m.group(2)) if m else "未声明"
    checks.append(("⑥ ▷ 是右结合", "infixr",
                   dtri, m is not None and m.group(1) == "r"))

    # ── ⑦ 库里有没有 ^ 类中缀算子（只看代码，去掉注释）──────────────
    # ⚠ 原来的 `mixedOp\^` 会命中散文；这里只认「定义」或「fixity 声明」。
    caret_defs = []
    for p in all_agda():
        try:
            txt = open(p, encoding="utf-8", errors="replace").read()
        except OSError:
            continue
        for ln in code_lines(txt):
            if re.search(r"_\^_\s*:", ln) or re.search(r"^\s*infix[lr]?\s+\d+\s+_\^_", ln):
                caret_defs.append((os.path.relpath(p, ROOT), ln.strip()[:60]))
    checks.append(("⑦ 存在 mixedOp^_ 形式的中缀迭代算子", "存在",
                   "找到 %d 处（代码行）" % len(caret_defs), len(caret_defs) > 0))

    # ── ⑤ 「未来态」是否与 fixity 结合方向绑定 ──────────────────────
    hits = []
    for p in glob.glob(os.path.join(ROOT, "docs", "**", "*.md"), recursive=True):
        try:
            txt = open(p, encoding="utf-8", errors="replace").read()
        except OSError:
            continue
        for line in txt.split("\n"):
            if "未来态" in line:
                hits.append(os.path.relpath(p, ROOT) + ": " + line.strip()[:70])
    bound = [h for h in hits if re.search(r"infix|结合|fixity", h)]
    checks.append(("⑤ 「未来态」绑定 fixity 结合方向", "是",
                   "docs 命中 %d 行，其中绑定 fixity 的 %d 行" % (len(hits), len(bound)),
                   len(bound) > 0))
    # 「未来态」的真实用法
    method = [h for h in hits if "锚定" in h or "规划" in h or "方法论" in h]

    # ── 报告 ────────────────────────────────────────────────────────
    print("=== fixity 断言审核（Agda 编译器与仓库为唯一判据）===")
    print("agda: %s" % binary)
    print("全库 fixity 声明: %d 条 ｜ 加法类 infixl %d / infixr %d ｜ 乘法类 infixl %d / infixr %d"
          % (len(decls), add_l, add_r, mul_l, mul_r))
    print()
    refuted = 0
    for name, alleged, measured, holds in checks:
        if not holds:
            refuted += 1
        print("  %s %-38s 声称: %-18s 实测: %s"
              % ("✅" if holds else "❌", name, alleged, measured))
    print()
    print("载入审核的 %d 条断言：成立 %d 条，**被实测推翻 %d 条**。"
          % (len(checks), len(checks) - refuted, refuted))
    print()
    print("「未来态」在 docs/ 的既有含义（证明策略，与 fixity 无关）:")
    for h in (method or hits)[:4]:
        print("    " + h)

    total = len(checks)
    print('ORACLE-MANIFEST {"basis": "exhaustive", "domain": %d, "points": %d, '
          '"claim": "对提交审核的 fixity 论证所依赖的 %d 条事实断言（默认 fixity 值/无声明时是否编译/'
          '同算子连写/定义处声明是否生效/fixity 是否继承/能否为 import 名声明/全库方向枚举/'
          '▷ 方向/^ 类中缀算子是否存在/未来态术语是否绑定 fixity），逐条用 Agda 探针实跑或全库枚举核对；'
          '其中 %d 条被实测推翻，%d 条成立。"}'
          % (total, total, total, refuted, total - refuted))


if __name__ == "__main__":
    main()
