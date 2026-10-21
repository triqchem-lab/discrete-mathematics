#!/usr/bin/env python3
"""「注释声称反例、但没有否定定理」筛查（2026-10-21）

## 为什么存在
本会话实测 4 处「注释写着『不成立 / 反例』，但模块里没有对应的 ¬ 或 ≢ 定理」：
  NSESupportBound（界不决定分布 / GaoYangRigidLock（每点返回不成立 /
  CRT（无界 ℕ 无同构）/ DigitalRootClassic（周期律 n=0 失效）。
它们属「散文断言规则」的反向违规：**声称已给反例、实际没给**。

本会话已把 4 处全部补成定理（成本各 1–3 轮），本脚本把「找候选」机械化。

## ⚠ 精度边界（实测）
粗判据（模块有反例类注释 + 无顶层 ≢/¬/⊥ 定理）在 908 个模块上给出 **55** 个候选，
其中多数是**误报**：反例在别的模块、或用 ⊥-elim/否定引理间接表达、或注释本身在
描述「已证的否命题」。⇒ 它是**分诊列表**，不是判据；每条都要人回源码核。

## 用法
  python3 engineering/check_unwitnessed_refutations.py            # 只报（exit 0）
  python3 engineering/check_unwitnessed_refutations.py --strict   # 有候选即 exit 1
"""
import pathlib
import re
import sys

ROOT = pathlib.Path(__file__).resolve().parent.parent
SRC = ROOT / "src" / "Sovereign"
CLAIM = ("反例", "不成立", "已证否", "被证伪")
NEG = re.compile(r"^[a-zA-Z][\w'′\-]* : .*(≢|¬|⊥)", re.M)


def main() -> int:
    strict = "--strict" in sys.argv
    cands = []
    files = list(SRC.rglob("*.agda"))
    for f in files:
        try:
            t = f.read_text(errors="ignore")
        except OSError:
            continue
        claims = [
            (i, l.strip()[:90])
            for i, l in enumerate(t.split("\n"), 1)
            if l.lstrip().startswith("--") and any(c in l for c in CLAIM)
        ]
        if not claims:
            continue
        if not NEG.search(t):
            cands.append((f.relative_to(ROOT), claims[0]))
    if not cands:
        print(f"✅ 无可疑（扫描 {len(files)} 个 .agda）")
        return 0
    print(f"⚠ 候选 {len(cands)} 个（扫描 {len(files)} 个 .agda）")
    print("  判据：注释出现「反例/不成立/已证否」，但模块无顶层 ≢/¬/⊥ 定理")
    for f, (ln, text) in cands:
        print(f"  {f}:{ln}  {text}")
    print("\n⚠ 粗判据，**每一条都要回源码核**（反例可能在别的模块/经引理间接表达）。")
    return 1 if strict else 0


if __name__ == "__main__":
    sys.exit(main())
