#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""结构 lint（engineering/lint_agda_structure.py）的对抗自检：12 个样例**全枚举**。

为什么需要它：第一版 lint 有**两个误报**（实测）——
  · `module P (x : Set) where`（参数化 module）被误判为「找不到 module 声明」；
  · 多行嵌套 module 的 `where`（OrbitStabilizer.agda:78）被误判为「where 挂在 module 上」。
这两个用例因此被固定成回归测试；同时固定我另一处**假规则**的反面：
名字里的 `-` 是合法的（stdlib `+-comm`），而 `_` 后接字面量才是真错误。

域 = 12 个样例（正 6：故意违规 / 反 6：合法或只该 WARN），全部枚举 ⇒ points == domain。

用法：python3 engineering/tests/test_lint_agda_structure.py
输出末行为 ORACLE-MANIFEST；全部样例符合预期则退出码 0。
"""

import json
import os
import subprocess
import sys
import tempfile

LINT = os.path.join(os.path.dirname(__file__), "..", "lint_agda_structure.py")

# (名称, {相对路径: 内容}, 期望的 ERROR kind 集合)
CASES = [
    ("clean", {"Foo/Bar.agda": "module Foo.Bar where\nx : Set\nx = Set\n"}, set()),
    ("module-path-mismatch", {"Foo.agda": "module Baz where\nx : Set\nx = Set\n"},
     {"module-path-mismatch"}),
    ("bad-dir-component", {"a-b/C.agda": "module a-b.C where\nx : Set\nx = Set\n"},
     {"bad-dir-component"}),
    ("illegal-name-underscore-digit", {"D.agda": "module D where\nratio8_5 : Set\nratio8_5 = Set\n"},
     {"illegal-name"}),
    ("hyphen-name-is-legal", {"E.agda": "module E where\nfoo-bar : Set\nfoo-bar = Set\n"}, set()),
    ("hole-only-warns", {"F.agda": "module F where\nf : Set\nf = ?\n"}, set()),
    ("illegal-where-postulate",
     {"G.agda": "module G where\npostulate\n  p : Set\n  where\n    postulate A : Set\n"},
     {"illegal-where"}),
    ("illegal-where-data",
     {"H.agda": "module H where\ndata T : Set where\n  mk : T\n  where\n    postulate A : Set\n"},
     {"illegal-where"}),
    ("legal-where-on-clause",
     {"I.agda": "module I where\nf : Set\nf = X\n  where\n    X : Set\n    X = Set\n"}, set()),
    ("legal-multiline-nested-module",
     {"J.agda": "module J where\nmodule Inner\n  (x : Set)\n  where\n  y : Set\n  y = x\n"},
     set()),
    ("legal-parameterised-module",
     {"K.agda": "module K (x : Set) where\ny : Set\ny = x\n"}, set()),
    ("no-module-decl", {"L.agda": "x : Set\nx = Set\n"}, {"no-module-decl"}),
]


def run_case(name, files, expected):
    with tempfile.TemporaryDirectory() as tmp:
        for rel, content in files.items():
            path = os.path.join(tmp, rel)
            os.makedirs(os.path.dirname(path), exist_ok=True)
            with open(path, "w", encoding="utf-8") as fh:
                fh.write(content)
        proc = subprocess.run([sys.executable, LINT, "--root", tmp, "--json"],
                              capture_output=True, text=True)
        try:
            data = json.loads(proc.stdout)
        except json.JSONDecodeError:
            return False, "lint 未输出 JSON：%s" % proc.stderr.strip()[:120]
        got = {kind for item in data["report"] for kind, _, _ in item["errors"]}
        ok = got == expected
        return ok, "期望 %s 实得 %s" % (sorted(expected) or "∅", sorted(got) or "∅")


def main():
    n_pass = 0
    for name, files, expected in CASES:
        ok, detail = run_case(name, files, expected)
        n_pass += ok
        print("  [%s] %-30s %s" % ("PASS" if ok else "FAIL", name, detail))
    total = len(CASES)
    print("=== %d/%d 样例符合预期 ===" % (n_pass, total))
    print('ORACLE-MANIFEST {"basis":"工程 lint 的 12 个手写样例（含 2 个历史误报回归用例）",'
          '"domain":%d,"points":%d,"claim":"lint 对正/反样例的分类与预期集合完全一致"}' %
          (total, total))
    return 0 if n_pass == total else 1


def test_lint_cases():
    """pytest 入口：全部样例必须符合预期。"""
    for name, files, expected in CASES:
        ok, detail = run_case(name, files, expected)
        assert ok, "%s: %s" % (name, detail)


if __name__ == "__main__":
    sys.exit(main())
