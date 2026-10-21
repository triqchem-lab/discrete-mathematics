#!/usr/bin/env python3
"""增量门禁：只编译「改动模块 + 它们的所有传递下游」。

背景：`check_all_modules_parallel.sh` 每次都把 915 个模块全部独立编译一遍
（实测 120 模块 40s ⇒ 全库约 305s）。但绝大多数改动只影响很小的下游闭包：
  例：`Entanglement.agda` / `DCGroup.agda` 的直接下游 = 0，
      `DCCharacter.agda` 的直接下游 = 1。
对这类改动跑全库门禁是浪费机器时间。

本脚本做相反的事 —— 只编译**受影响**的那一小撮。

用法：
  python3 engineering/check_dependents.py src/Sovereign/Path/To/Mod.agda
  python3 engineering/check_dependents.py <file> [<file> ...] [--jobs N] [--heap 6G]
  python3 engineering/check_dependents.py <file> --dry-run      # 只列清单不编译
  python3 engineering/check_dependents.py --all                 # 回落到全库（等价旧门禁）

退出码：0 = 全部 PASS；1 = 有 FAIL；2 = 用法错误（含文件不存在 / 无法解析 module 名）。

设计取舍（诚实边界）：
· 依赖边只解析 `open import` / `import` 的**显式**模块名；Agda 的实例解析、
  模块别名、`using` 里重命名等不影响边集（改的都是同一批 API）。
· 反向闭包按**传递**计算，所以改一个底层模块（如 `Base/Trit.agda`）会把
  全库都拉进来 —— 那时它自然退化成全库门禁，行为正确但不再省时。
· 不做 `.agdai` 时间戳判断：Agda 自己会复用 `_build` 里的接口；
  本脚本只决定「启动多少个 Agda 进程」。
"""
from __future__ import annotations

import argparse
import os
import re
import subprocess
import sys
from concurrent.futures import ThreadPoolExecutor

SRC = "src/Sovereign"
AGDA = os.environ.get("AGDA", os.path.expanduser("~/.local/bin/agda"))

IMPORT_RE = re.compile(r"^\s*(?:open\s+)?import\s+(Sovereign\.[\w.]+)", re.M)
MODULE_RE = re.compile(r"^\s*module\s+([\w.]+)", re.M)


def module_of(path: str) -> str | None:
    """从 .agda 文件里读 `module X.Y.Z where` 得到模块名。"""
    try:
        s = open(path, encoding="utf-8").read()
    except Exception:
        return None
    m = MODULE_RE.search(s)
    return m.group(1) if m else None


def build_graph(src: str) -> tuple[dict[str, str], dict[str, set[str]]]:
    """返回 (模块名 -> 文件路径, 模块名 -> 直接依赖集合)。"""
    paths: dict[str, str] = {}
    for root, _, fs in os.walk(src):
        for f in fs:
            if not f.endswith(".agda"):
                continue
            p = os.path.join(root, f)
            mod = module_of(p)
            if mod:
                paths[mod] = p
    deps: dict[str, set[str]] = {}
    for mod, p in paths.items():
        try:
            s = open(p, encoding="utf-8").read()
        except Exception:
            deps[mod] = set()
            continue
        deps[mod] = {d for d in IMPORT_RE.findall(s) if d in paths}
    return paths, deps


def reverse_closure(seeds: set[str], deps: dict[str, set[str]]) -> set[str]:
    """传递反向闭包：包含 seeds 自身。"""
    rev: dict[str, set[str]] = {m: set() for m in deps}
    for m, ds in deps.items():
        for d in ds:
            rev.setdefault(d, set()).add(m)
    seen = set(seeds)
    queue = list(seeds)
    while queue:
        cur = queue.pop()
        for up in rev.get(cur, ()):
            if up not in seen:
                seen.add(up)
                queue.append(up)
    return seen


def compile_one(path: str, heap: str) -> tuple[bool, str]:
    cmd = [AGDA, "+RTS", f"-M{heap}", "-RTS", "--guardedness", path]
    try:
        r = subprocess.run(cmd, stdout=subprocess.DEVNULL,
                           stderr=subprocess.DEVNULL, timeout=600)
        return r.returncode == 0, path
    except subprocess.TimeoutExpired:
        return False, path


def main() -> int:
    ap = argparse.ArgumentParser(add_help=True)
    ap.add_argument("files", nargs="*", help="改动的 .agda 文件")
    ap.add_argument("--jobs", type=int, default=28, help="并发进程数（默认 28）")
    ap.add_argument("--heap", default=os.environ.get("HEAP", "6G"))
    ap.add_argument("--dry-run", action="store_true", help="只列清单，不编译")
    ap.add_argument("--all", action="store_true", help="回落到全库编译")
    args = ap.parse_args()

    paths, deps = build_graph(SRC)
    if not paths:
        print(f"错误：在 {SRC} 下没找到任何模块", file=sys.stderr)
        return 2

    if args.all:
        targets = sorted(paths.values())
    else:
        if not args.files:
            print("用法：check_dependents.py <改动的 .agda> ... [--dry-run]", file=sys.stderr)
            print("      或 --all 回落到全库", file=sys.stderr)
            return 2
        seeds: set[str] = set()
        for f in args.files:
            if not os.path.exists(f):
                print(f"错误：文件不存在 {f}", file=sys.stderr)
                return 2
            mod = module_of(f)
            if mod is None:
                print(f"错误：无法从 {f} 解析 module 名", file=sys.stderr)
                return 2
            if mod not in paths:
                # 文件存在但不在扫描根下：按路径直接编译它本身
                print(f"⚠ {f} 的模块名 {mod} 不在 {SRC} 索引中，只编译该文件本身",
                      file=sys.stderr)
                seeds.add(mod)
                paths[mod] = f
            else:
                seeds.add(mod)
        affected = reverse_closure(seeds, deps)
        targets = sorted(paths[m] for m in affected if m in paths)

    total = len(targets)
    print(f"=== 增量门禁：将编译 {total} 个模块（并发 {args.jobs}，堆上限 {args.heap}）===")
    for t in targets:
        print("   ", t)
    if args.dry_run:
        print("（--dry-run：不编译）")
        return 0
    if total == 0:
        print("（无受影响模块）")
        return 0

    fails: list[str] = []
    with ThreadPoolExecutor(max_workers=max(1, args.jobs)) as ex:
        for ok, path in ex.map(lambda p: compile_one(p, args.heap), targets):
            if not ok:
                fails.append(path)
            print(("PASS " if ok else "FAIL ") + path)

    print(f"\n=== 增量门禁: {total - len(fails)} 通过 / {len(fails)} 失败 / 共 {total} ===")
    if fails:
        print("--- 失败模块 ---")
        for f in fails:
            print("   ", f)
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
