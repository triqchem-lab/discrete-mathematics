#!/usr/bin/env python3
"""过期「未证/未做」标注检测（2026-10-21）

## 为什么存在
本会话实测 5 处「文档声称未证/未做，实际已在别处证出」：
  Pi2dFunctionLayer 右逆 / T6CayleyDec 的 Dec 版 / Omega3Suffix 的 suffix-resp /
  Pi2dQuotient 的转述 / AStepStdGroup 的一般走层逆。
它们会让人白写一遍。本脚本把这类缺陷机械化。

## 判据（保守，宁少报）
注释行同时满足：含「未证/未做/待做/⬜/未完成」 + 用反引号点了一个名字，
而该名字在**另一个文件**里有顶层定义(`name :` 行首) ⇒ 报「可疑过期标注」。

## ⚠ 精度边界（实测 2026-10-21，11 条命中里多数是误报）
本脚本只做**词面共现**判定，不理解语义，因此会误报：
  · 注释在描述「已更正/已推翻」的旧判断（如 `T6AStepMap` §6 的 toStepCode）；
  · 注释说「本模块不重复实现 `foldT`」（点名≠声称缺失）；
  · 需要的是某条**性质**（`updAt` 的某引理），而非该名字本身。
⇒ 因此**默认只报告、不判失败**（exit 0）；要当门禁用 `--strict`（exit 1）。
   命中的每一条都必须**人工回源码核**（看那个函数是否已全定义）。

## 用法
  python3 engineering/check_stale_claims.py            # 扫描 src/（只报，exit 0）
  python3 engineering/check_stale_claims.py --strict   # 有可疑即 exit 1（门禁用法）
  python3 engineering/check_stale_claims.py --all      # 连同「同文件已定义」也列（噪声多）
  python3 engineering/check_stale_claims.py --markers  # **高精度**：只看含 ⬜ 的小节行
"""
import pathlib
import re
import sys

ROOT = pathlib.Path(__file__).resolve().parent.parent
SRC = ROOT / "src"

TOP = re.compile(r"^([A-Za-z_][\w'′\-]*)\s*:", re.M)
IDENT = re.compile(r"`([A-Za-z_][\w'′\-]*)`")
CLAIM = ("未证", "未做", "待做", "⬜", "未完成")

# 否定 / 完成语境：这类句子里的「未证」**不是**在声称「还没做」，而是
#   · 「闭合 X 的未证」= 已证完；
#   · 「原写『未证』… 已改为」= 就在修这件事；
#   · 「不再是未证」= 已证。
# ⇒ 词面匹配 ≠ 语义：含这些词的句子**一律不算可疑**。
NEGATED = ("闭合", "已证", "已完成", "已过期", "不再是", "原文写", "原写", "改为",
           "已改为", "已标注", "未验证·路线推测", "[未验证·路线推测]")
# 太通用的名字不作数（跨模块重名合法/噪声大）
IGNORE = {"refl", "sym", "trans", "cong", "subst", "nil", "cons", "id", "not"}
# 这些行是在描述「旧判断已被推翻/注释已更正」或「不重复实现」，不算声称缺失
EXCLUDE = ("已更正", "已推翻", "已过期", "不重复", "不再", "已被证明", "见 §")


def main() -> int:
    show_same = "--all" in sys.argv
    strict = "--strict" in sys.argv
    markers = "--markers" in sys.argv   # 只看含 ⬜ 的注释行（高精度模式）
    files = sorted(SRC.rglob("*.agda"))
    defs: dict[str, list[pathlib.Path]] = {}
    for f in files:
        txt = f.read_text(errors="ignore")
        for m in TOP.finditer(txt):
            defs.setdefault(m.group(1), []).append(f)

    hits = []
    for f in files:
        for i, line in enumerate(f.read_text(errors="ignore").splitlines(), 1):
            st = line.lstrip()
            if not st.startswith("--"):
                continue
            if not any(w in line for w in CLAIM):
                continue
            # ← 否定/完成语境：词面有「未证」但语义是「已证」或「正在修」
            if any(w in line for w in NEGATED):
                continue
            if any(x in line for x in EXCLUDE):
                continue
            if markers and "⬜" not in line:
                continue
            for name in IDENT.findall(line):
                if name in IGNORE or len(name) < 4:
                    continue
                if f in defs.get(name, []):   # 本文件已定义 ⇒ 不是「缺失」
                    continue
                others = [g for g in defs.get(name, []) if g != f]
                if others:
                    hits.append((f, i, name, others[0], False))
                elif show_same and name in defs:
                    hits.append((f, i, name, defs[name][0], True))

    if not hits:
        print(f"✅ 无可疑过期标注（扫描 {len(files)} 个 .agda）")
        return 0
    print(f"⚠ 可疑过期标注 {len(hits)} 条（扫描 {len(files)} 个 .agda）")
    print("  判据：注释声称「未证/未做」却又点了一个**别处已有顶层定义**的名字")
    for f, i, name, where, same in hits:
        tag = "同文件" if same else f"别处 {where.relative_to(ROOT)}"
        print(f"  {f.relative_to(ROOT)}:{i}  声称缺 `{name}`，但它在 {tag} 有定义")
    print("\n⚠ 词面共现判定，**每一条都要人工回源码核**（看是否已全定义）；默认不判失败。")
    return 1 if strict else 0


if __name__ == "__main__":
    sys.exit(main())
