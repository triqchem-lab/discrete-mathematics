#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""结构 lint：不编译地找出「隐形文件」。

背景（2026-09-13 实测）：`engineering/check_all_modules_parallel.sh:27` 只扫
`src/Sovereign`，于是 `src/01-electric-12d`、`src/02-magnetic-24d`、
`src/03-neutral-144d` 这些目录里的草稿**从未被编译、也从未进门禁**；它们声明的
模块名与路径不匹配（`module Sovereign.Coupling.X` 却在 `02-magnetic-24d/X.agda`），
在 `include: src` 下永远编不了 —— 既不是库的一部分，又看起来像库的一部分。

本脚本只做**静态**检查（不调用 Agda），用于把这类文件在提交前暴露出来。
检查项：
  1. module-path-mismatch : `module` 声明名 != 相对 include 根的路径（ERROR）
  2. bad-dir-component    : 路径分量含 `-` 等非法模块名字符（ERROR）
  3. illegal-name         : 标识符中 `_` 后紧跟字面量（Agda 实测报
                            “the part 5 is not valid because it is a literal”）（ERROR）
  4. illegal-where        : `where` 挂在 postulate/data/record/类型签名上
                            （Agda 只允许函数子句带 where）（ERROR，启发式）
  5. hole                 : `?` 洞（WARN；`--strict-holes` 时升级为 ERROR）

注意（防误报）：**名字含 `-` 是合法的**（stdlib 的 `+-comm`/`≤-refl`、本库的
`c3-id` 都如此），故本脚本**不**把连字符名字报错 —— 只有 `_` 接字面量才是真错误。

用法：
  python3 engineering/lint_agda_structure.py --root src
  python3 engineering/lint_agda_structure.py --root archive --json
退出码：0 = 无 ERROR；1 = 有 ERROR；2 = 用法/路径错误。
"""

import argparse
import json
import os
import re
import sys

SKIP_DIRS = {"_build", "MAlonzo", "Generated", ".git"}

MODULE_RE = re.compile(r"^\s*module\s+([^\s(]+)", re.M)  # 参数化 module 亦可（`(base : ℕ) … where`）
# `_` 后紧跟字面量（数字）：真错误（比率名 ratio8_5 之类）
ILLEGAL_NAME_RE = re.compile(r"\b[A-Za-z][A-Za-z0-9_']*_[0-9][A-Za-z0-9_']*")
WHERE_RE = re.compile(r"^([ \t]*)where\s*$")
DECL_START_RE = re.compile(r"^([ \t]*)(postulate|data|record|field|variable|module)\b")
SIG_RE = re.compile(r"^[ \t]*[^\s:=]+[^\n]*:[^\n=]*$")  # 形如 `name : Type`（无 `=`）
VALID_COMPONENT_RE = re.compile(r"^[A-Za-z][A-Za-z0-9_']*$")


def strip_comments(text):
    """去掉行注释与（嵌套）块注释，字符串字面量不特殊处理（本库不使用）。"""
    out, i, depth = [], 0, 0
    while i < len(text):
        if depth == 0 and text.startswith("--", i):
            j = text.find("\n", i)
            i = len(text) if j < 0 else j
            continue
        if text.startswith("{-", i):
            depth += 1
            i += 2
            continue
        if depth > 0 and text.startswith("-}", i):
            depth -= 1
            i += 2
            continue
        if depth == 0:
            out.append(text[i])
        elif text[i] == "\n":
            out.append("\n")
        i += 1
    return "".join(out)


def expected_module_name(rel_path):
    return rel_path[:-len(".agda")].replace(os.sep, ".")


def check_file(abs_path, rel_path, strict_holes):
    """返回 (errors, warnings)，每项为 (kind, line, detail)。"""
    errors, warnings = [], []
    with open(abs_path, encoding="utf-8") as fh:
        raw = fh.read()
    code = strip_comments(raw)

    parts = rel_path.split(os.sep)[:-1]
    for comp in parts:
        if not VALID_COMPONENT_RE.match(comp):
            errors.append(("bad-dir-component", 0,
                           "目录分量 %r 不是合法模块名分量（Agda 在 include 根下无法解析）" % comp))
            break

    m = MODULE_RE.search(code)
    if m is None:
        errors.append(("no-module-decl", 0, "找不到 `module … where` 声明"))
    else:
        want = expected_module_name(rel_path)
        got = m.group(1)
        if got != want:
            line = code[:m.start()].count("\n") + 1
            errors.append(("module-path-mismatch", line,
                           "声明 `module %s` 与路径推出的 `%s` 不符" % (got, want)))

    lines = code.split("\n")
    for idx, line in enumerate(lines, 1):
        for hit in ILLEGAL_NAME_RE.finditer(line):
            errors.append(("illegal-name", idx,
                           "`%s`：`_` 后不得接字面量" % hit.group(0)))

    # where 滥用（启发式）：向上找所在布局块的起始行
    for idx, line in enumerate(lines):
        mw = WHERE_RE.match(line)
        if not mw:
            continue
        indent = len(mw.group(1))
        j = idx - 1
        while j >= 0 and (lines[j].strip() == "" or lines[j].strip().startswith("--")):
            j -= 1
        block_start = j
        k = j
        while k >= 0:
            s = lines[k]
            if s.strip() == "":
                k -= 1
                continue
            lead = len(s) - len(s.lstrip())
            if lead < indent and not s.lstrip().startswith(("--", "{-")):
                block_start = k
                break
            k -= 1
        header = lines[block_start] if block_start >= 0 else ""
        verdict = None
        if DECL_START_RE.match(header):
            keyword = DECL_START_RE.match(header).group(2)
            # 注意：`module` 不在此列 —— `module X …\n  where` 是**合法**的（参数化/多行
            # module 头把 where 单列一行），报它是误报（实测 OrbitStabilizer.agda:78）。
            if keyword in ("postulate", "data", "record", "field", "variable"):
                verdict = "`where` 挂在 %s 声明上" % keyword
        elif SIG_RE.match(header) and "=" not in header:
            verdict = "类型签名带 `where`"
        if verdict:
            errors.append(("illegal-where", idx + 1, verdict))

    holes = code.count("?")
    if holes:
        entry = ("hole", 0, "%d 个 `?` 洞" % holes)
        (errors if strict_holes else warnings).append(entry)
    return errors, warnings


def main():
    ap = argparse.ArgumentParser(description="Agda 结构 lint（不编译）")
    ap.add_argument("--root", default="src", help="扫描根（默认 src）")
    ap.add_argument("--json", action="store_true", help="输出 JSON")
    ap.add_argument("--strict-holes", action="store_true", help="把 `?` 洞升级为 ERROR")
    ap.add_argument("--limit", type=int, default=40, help="每个检查项最多打印条数")
    args = ap.parse_args()

    if not os.path.isdir(args.root):
        print("路径不存在：%s" % args.root, file=sys.stderr)
        return 2

    report, n_err, n_warn, n_files, n_skip = [], 0, 0, 0, 0
    for dirpath, dirnames, filenames in os.walk(args.root):
        dirnames[:] = [d for d in dirnames if d not in SKIP_DIRS]
        for name in sorted(filenames):
            if not name.endswith(".agda"):
                continue
            abs_path = os.path.join(dirpath, name)
            rel_path = os.path.relpath(abs_path, args.root)
            n_files += 1
            errors, warnings = check_file(abs_path, rel_path, args.strict_holes)
            n_err += len(errors)
            n_warn += len(warnings)
            if errors or warnings:
                report.append({"file": os.path.join(args.root, rel_path),
                               "errors": errors, "warnings": warnings})
    skipped = sum(1 for d in SKIP_DIRS if os.path.isdir(os.path.join(args.root, d)))
    n_skip = skipped

    if args.json:
        print(json.dumps({"root": args.root, "files": n_files, "errors": n_err,
                          "warnings": n_warn, "report": report},
                         ensure_ascii=False, indent=2))
    else:
        print("=== 结构 lint: %s（%d 个 .agda 文件，跳过 %d 个生成目录）===" %
              (args.root, n_files, n_skip))
        shown = 0
        for item in report:
            for kind, line, detail in item["errors"]:
                shown += 1
                if shown <= args.limit:
                    print("  [ERROR] %-22s %s:%s  %s" % (kind, item["file"], line, detail))
            for kind, line, detail in item["warnings"]:
                shown += 1
                if shown <= args.limit:
                    print("  [WARN ] %-22s %s:%s  %s" % (kind, item["file"], line, detail))
        if shown > args.limit:
            print("  …另有 %d 条（用 --json 取全量）" % (shown - args.limit))
        print("--- ERROR %d / WARN %d ---" % (n_err, n_warn))
    return 1 if n_err else 0


if __name__ == "__main__":
    sys.exit(main())
