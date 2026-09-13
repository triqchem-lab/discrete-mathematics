#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""验证归档草稿「解析干净」：archive/civlayers-2026-07/ 的三份 where 滥用草稿。

为什么单独验证：这些草稿声明了 `Sovereign.*` 模块名却不在 `src/Sovereign/` 下，
**无法用 `proof_compile` 签回执**（Agda 会先报 ModuleNameDoesntMatchFileName）。
做法：把模块名替换成 `Scratch.<Name>` 并放到匹配路径，再原样用
`agda --cubical --guardedness -i <tmp> -i src` 编译 —— 这样测的是**语法+内容**，
唯一放宽的是「模块名与路径」这一项（那正是它们被归档的原因）。

判据：Agda 先解析后类型检查 ⇒ **首错不再是 [ParseError]** 等价于整文件解析成功。
域 = 3 个文件，全部枚举 ⇒ points == domain。

用法：python3 engineering/tests/verify_civlayers_parse_clean.py
输出末行为 ORACLE-MANIFEST；三文件 ParseError 计数均为 0 则退出码 0。
"""

import os
import re
import subprocess
import sys
import tempfile

AGDA = os.environ.get("AGDA_BIN", "/home/yanli/.local/bin/agda")
ROOT = os.path.join("archive", "civlayers-2026-07")
FILES = [
    os.path.join("02-magnetic-24d", "SpinTwistor.agda"),
    os.path.join("03-neutral-144d", "Entanglement.agda"),
    os.path.join("03-neutral-144d", "ZhonglvClosure.agda"),
]


def main():
    n_pass = 0
    with tempfile.TemporaryDirectory() as tmp:
        scratch = os.path.join(tmp, "Scratch")
        os.makedirs(scratch)
        for rel in FILES:
            name = os.path.basename(rel)[:-len(".agda")]
            with open(os.path.join(ROOT, rel), encoding="utf-8") as fh:
                src = fh.read()
            src = re.sub(r"^module .* where$", "module Scratch.%s where" % name,
                         src, count=1, flags=re.M)
            dst = os.path.join(scratch, name + ".agda")
            with open(dst, "w", encoding="utf-8") as fh:
                fh.write(src)
            proc = subprocess.run([AGDA, "--cubical", "--guardedness",
                                   "-i", tmp, "-i", "src", dst],
                                  capture_output=True, text=True, timeout=900)
            log = proc.stdout + proc.stderr
            n_parse = log.count("ParseError")
            first = next((ln for ln in log.split("\n") if ".agda:" in ln and "error" in ln),
                         "(无错误)")
            print("  [%s] %-18s exit=%s ParseError=%d  首错=%s" %
                  ("PASS" if n_parse == 0 else "FAIL", name, proc.returncode,
                   n_parse, first[:100]))
            n_pass += 1 if n_parse == 0 else 0
    total = len(FILES)
    print("=== %d/%d 归档稿解析干净（内容层错误不计入本判据）===" % (n_pass, total))
    print('ORACLE-MANIFEST {"basis":"archive/civlayers-2026-07 的三份 where 滥用草稿",'
          '"domain":%d,"points":%d,"claim":"三文件在 agda --cubical --guardedness 下 '
          'ParseError 计数为 0（模块名归一化以绕开路径↔模块名不匹配）"}' % (total, total))
    return 0 if n_pass == total else 1


def test_parse_clean():
    """pytest 入口：三文件都必须解析干净。"""
    assert main() == 0


if __name__ == "__main__":
    sys.exit(main())
