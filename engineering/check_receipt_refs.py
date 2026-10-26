#!/usr/bin/env python3
"""(一次性分析脚本，**非门禁**；门禁一律住系统层) 文档引用的回执 vs 台账 对账。

回执是哈希绑定的：改一个注释字符，回执就失效；而文档里的回执是手抄的。
本脚本扫指定文档中形如 `xxxxxxxx…` 的回执前缀，逐个在最新台账 JSON 全文里查存在性。

用法:
  python3 engineering/check_receipt_refs.py                    # 默认 4 份文档
  python3 engineering/check_receipt_refs.py --docs a.md b.md   # 指定文档
  python3 engineering/check_receipt_refs.py --ledger PATH      # 指定台账

退出码: 0 = 全部命中；1 = 有死链（供人手动排查，不接入门禁）。
"""
import argparse
import glob
import os
import re
import sys
from pathlib import Path

DEFAULT_DOCS = [
    "/data/training/cli/scholar-loop/docs/endofullerene-rotor-report.md",
    "/data/work/discrete-mathematics/docs/handoff-endofullerene-line.md",
    "/data/work/discrete-mathematics/PROVEN.md",
    "/data/work/docs/wiki/105-c60-ih-neutrino-verification.md",
    "/data/work/docs/wiki/08-constants.md",
]
PAT = re.compile(r"`([0-9a-f]{8})…`")


def newest_ledger() -> Path:
    files = glob.glob(str(Path.home() / ".dsh/state/math-proof/dag-*.json"))
    if not files:
        raise SystemExit("未找到台账文件（~/.dsh/state/math-proof/dag-*.json）")
    return Path(max(files, key=os.path.getmtime))


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--docs", nargs="*", default=DEFAULT_DOCS)
    ap.add_argument("--ledger", default=None)
    a = ap.parse_args()

    ledger_path = Path(a.ledger) if a.ledger else newest_ledger()
    ledger = ledger_path.read_text()
    print(f"台账: {ledger_path.name}（{len(ledger)} 字符）\n")

    total = stale_total = 0
    for d in a.docs:
        p = Path(d)
        if not p.exists():
            print(f"⚠ 文档不存在: {d}")
            continue
        found = PAT.findall(p.read_text())
        stale = [h for h in found if h not in ledger]
        total += len(found)
        stale_total += len(stale)
        status = "✅" if not stale else "❌ " + ", ".join(stale)
        print(f"{p.name}: 引用 {len(found)} 个回执 → {status}")

    print(f"\n合计: {total} 个引用｜死链 {stale_total}")
    return 0 if stale_total == 0 else 1


if __name__ == "__main__":
    sys.exit(main())
