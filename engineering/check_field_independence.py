#!/usr/bin/env python3
"""假公理静态筛查（**只查一类**：记录字段独立性）。

背景：2026-10-22 在 `Zhonglv.agda` 一次审计发现 3 条假 postulate：

  chernInvariant  : ∀ s → chern (evolveStep s) ≡ + 2          -- evolveStep 保持原 chern
  polarClosure    : ∀ s → stepCount s ≡ 144 → windingPolar s ≡ 144
  toroidalClosure : ∀ s → stepCount s ≡ 144 → windingToroidal s ≡ 46

它们的共同形状是：
  **结论**断言记录 `R` 的某个字段 `f` 取值恒定/等于某个字面量，
  而**前提**只约束了 `R` 的**别的**字段（或根本没约束 `f`），
  且记录定义里 `f` 与那些前提字段**没有依赖关系**。

⇒ 此时取 `f` 为任意合法值即可反驳，属**可静态判定**的一类。

本脚本只做这件事：扫 §record 字段表 + §postulate 签名，报出
「结论落在字段 f 上、前提却不涉及 f」的 postulate。**不试图判定其它类别的真假**
（`∀ + ≡` 里还有 REWRITE 规则、不透明常量+值、否定式等，那些需要人工或内核探针）。

用法：
  python3 engineering/check_field_independence.py            # 扫描全库
  python3 engineering/check_field_independence.py --strict   # 有命中则 exit 1

退出码：0 = 无命中（或默认非严格模式）；1 = --strict 且有命中；2 = 用法错误。

诚实边界：
· 这是**必要条件式**的启发（命中 ⇒ 高度可疑；不命中 ≠ 无问题）。
· 记录的字段若有**类型层面**的依赖（如 `Field` 里 `p : a ≡ b` 约束其它字段），
  本脚本**看不见**（它只做名字级匹配）—— 命中时仍需回源码核。
"""
from __future__ import annotations

import argparse
import pathlib
import re
import sys

SRC = "src/Sovereign"

RECORD_RE = re.compile(r"^\s*record\s+([\w\-′]+)[^:]*:\s*Set[^=]*?where(.*?)(?=^\S|\Z)", re.M | re.S)
FIELD_RE = re.compile(r"^\s+([a-zA-Z][\w\-′]*)\s*:", re.M)
POST_BLOCK_RE = re.compile(r"^\s*postulate\b(.*?)(?=^\S|\Z)", re.M | re.S)
SIG_RE = re.compile(r"^\s+([a-zA-Z][\w\-′]*)\s*:\s*([\s\S]*?)(?=^\s+[a-zA-Z][\w\-′]*\s*:|\Z)", re.M)


def collect_records(src: str) -> dict[str, set[str]]:
    """record 名 -> 字段名集合。"""
    out: dict[str, set[str]] = {}
    for p in pathlib.Path(src).rglob("*.agda"):
        t = p.read_text(encoding="utf-8", errors="ignore")
        for m in RECORD_RE.finditer(t):
            name, body = m.group(1), m.group(2)
            body = re.sub(r"--[^\n]*", "", body)
            fields = set(FIELD_RE.findall(body))
            if fields:
                out[name] = fields
    return out


def collect_postulates(src: str):
    """产出 (文件, 行号, 名字, 签名)。

    ⚠ 块边界的判定是行级的：`postulate` 之后一直消费
    **空行 / 任何注释行（含列 0 的 `--`）/ 缩进行**，
    直到遇到「非注释、非空、且落在列 0」的代码行为止。
    （早前用单个正则 `(?=^\S|\\Z)` 会在块内**列 0 的注释行**处提前截断，
      导致 `Zhonglv.agda` 里 polarClosure / toroidalClosure 被漏掉。)
    """
    for p in pathlib.Path(src).rglob("*.agda"):
        lines = p.read_text(encoding="utf-8", errors="ignore").split("\n")
        i = 0
        while i < len(lines):
            if not re.match(r"^\s*postulate\s*$", lines[i]):
                i += 1
                continue
            i += 1
            block: list[tuple[int, str]] = []
            while i < len(lines):
                l = lines[i]
                if l.strip() == "" or l.lstrip().startswith("--") or l[:1] in (" ", "\t"):
                    block.append((i + 1, l))
                    i += 1
                else:
                    break
            # 从块里抽签名（缩进 + name :）
            j = 0
            while j < len(block):
                ln, l = block[j]
                m = re.match(r"^\s+([a-zA-Z][\w\-′]*)\s*:\s*(.*)$", l)
                if m:
                    name, typ = m.group(1), m.group(2)
                    k = j + 1
                    while k < len(block):
                        ln2, l2 = block[k]
                        if re.match(r"^\s+[a-zA-Z][\w\-′]*\s*:", l2):
                            break
                        if l2.strip() == "" or l2.lstrip().startswith("--"):
                            k += 1
                            continue
                        typ += " " + l2.strip()
                        k += 1
                    yield str(p.relative_to(src)), ln, name, " ".join(typ.split())
                    j = k
                else:
                    j += 1


def field_hits(typ: str, records: dict[str, set[str]]):
    """若签名的结论是 `<Rec>.<field> <var>` 且前提不涉及该字段，返回 (Rec, field)。"""
    # 只看结论（最后一个 → 之后的部分，或整体）
    concl = typ.split("→")[-1].strip()
    m = re.search(r"\b([\w\-′]+)\.([\w\-′]+)\b", concl)
    if not m:
        return None
    rec, fld = m.group(1), m.group(2)
    if rec not in records or fld not in records[rec]:
        return None
    premises = typ[: typ.rfind("→")] if "→" in typ else ""
    # 前提里若出现同一字段 → 可能是合理的（例如 f x ≡ f y 型）；否则可疑
    if re.search(r"\b" + re.escape(fld) + r"\b", premises):
        return None
    return rec, fld


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--strict", action="store_true")
    ap.add_argument("--src", default=SRC)
    args = ap.parse_args()

    records = collect_records(args.src)
    print(f"=== 记录类型 {len(records)} 个；开始扫 postulate 的「字段独立性」 ===")

    hits = []
    total = 0
    for f, ln, name, typ in collect_postulates(args.src):
        total += 1
        h = field_hits(typ, records)
        if h:
            hits.append((f, ln, name, h, typ))

    print(f"postulate 签名总数：{total}\n")
    if not hits:
        print("✅ 无命中：没有「结论落在某字段上、前提却不涉及该字段」的 postulate。")
        return 0

    print(f"⚠ 可疑 {len(hits)} 条（结论断言字段取值，前提不涉及该字段）：\n")
    for f, ln, name, (rec, fld), typ in hits:
        print(f"  {f}:{ln}  [{rec}.{fld}]")
        print(f"    {name} : {typ[:130]}")
        print(f"    ⇒ 若 {rec} 的 {fld} 与前提字段无依赖，取 {fld} 为任意值即可反驳\n")

    print("⚠ 这是**启发式**：命中高度可疑，但不命中 ≠ 无问题；命中时须回源码核。")
    return 1 if args.strict else 0


if __name__ == "__main__":
    sys.exit(main())
