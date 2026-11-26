#!/usr/bin/env python3
"""bcr_mirror.py — 递归镜像 BCR(Bazel Central Registry)的模块闭包到本地目录。
用法: python3 bcr_mirror.py <输出目录> [根 MODULE.bazel 路径]
直连 bcr.bazel.build(该域无需代理)。
"""
import json
import os
import re
import sys
import urllib.request

OUT = sys.argv[1] if len(sys.argv) > 1 else "/tmp/bcr-mirror"
ROOT_MOD = sys.argv[2] if len(sys.argv) > 2 else "/tmp/wang-tensor-rank/MODULE.bazel"
BASE = "https://bcr.bazel.build"


def fetch(url):
    req = urllib.request.Request(url, headers={"User-Agent": "bcr-mirror/1"})
    with urllib.request.urlopen(req, timeout=60) as r:
        return r.read()


def deps_of(module_text):
    out = []
    for m in re.finditer(r'bazel_dep\(\s*name\s*=\s*"([^"]+)"\s*,\s*version\s*=\s*"([^"]+)"', module_text):
        out.append((m.group(1), m.group(2)))
    return out


def mirror_module(name, version, seen):
    key = (name, version)
    if key in seen:
        return
    seen.add(key)
    base = f"{BASE}/modules/{name}/{version}"
    ddir = os.path.join(OUT, "modules", name, version)
    os.makedirs(ddir, exist_ok=True)
    mod_path = os.path.join(ddir, "MODULE.bazel")
    if not os.path.exists(mod_path):
        try:
            data = fetch(f"{base}/MODULE.bazel")
        except Exception as e:
            print(f"  SKIP {name}/{version}: MODULE.bazel {e}")
            seen.discard(key)
            return
        open(mod_path, "wb").write(data)
    text = open(mod_path, encoding="utf-8").read()
    sj_path = os.path.join(ddir, "source.json")
    if not os.path.exists(sj_path):
        try:
            data = fetch(f"{base}/source.json")
            open(sj_path, "wb").write(data)
        except Exception as e:
            print(f"  (no source.json for {name}/{version}: {e})")
            return
    sj = json.load(open(sj_path, encoding="utf-8"))
    for p in sj.get("patches", []):
        pp = os.path.join(ddir, p)
        os.makedirs(os.path.dirname(pp), exist_ok=True)
        if not os.path.exists(pp):
            try:
                open(pp, "wb").write(fetch(f"{base}/{p}"))
            except Exception as e:
                print(f"  patch {p}: {e}")
    # 源码包 → distdir(github 包经 socks 代理 curl)
    url = sj.get("url")
    if url and "distdir" in OUT:
        fname = url.rsplit("/", 1)[-1]
        dpath = os.path.join(os.path.dirname(OUT.rstrip("/")) , "distdir", fname)
        if not os.path.exists(dpath):
            os.makedirs(os.path.dirname(dpath), exist_ok=True)
            try:
                import subprocess
                r = subprocess.run(["curl", "-sfL", "--proxy", "socks5h://127.0.0.1:10808",
                                    url, "-o", dpath], timeout=300)
                print(f"  distdir {fname}: exit {r.returncode}")
            except Exception as e:
                print(f"  distdir {fname}: {e}")
    print(f"mirrored {name}/{version}")
    for dn, dv in deps_of(text):
        mirror_module(dn, dv, seen)


def main():
    os.makedirs(OUT, exist_ok=True)
    seen = set()
    root_text = open(ROOT_MOD, encoding="utf-8").read()
    for name, version in deps_of(root_text):
        mirror_module(name, version, seen)
    print("closure:", len(seen), "modules")


if __name__ == "__main__":
    main()
