#!/usr/bin/env python3
"""bcr_add_module.py — 把指定 (name, version) 模块完整镜像进本地 registry, 并归档源码包。
用法: python3 bcr_add_module.py <registry目录> <distdir目录> <name>@<version> ...
经用户 socks5 代理访问 github 源码包; bcr.bazel.build 直连。
"""
import base64
import hashlib
import json
import os
import re
import subprocess
import sys
import urllib.request

REG = sys.argv[1]
DIST = sys.argv[2]
BASE = "https://bcr.bazel.build"


def fetch(url, tries=3):
    last = None
    for _ in range(tries):
        try:
            req = urllib.request.Request(url, headers={"User-Agent": "bcr-mirror/1"})
            with urllib.request.urlopen(req, timeout=60) as r:
                return r.read()
        except Exception as e:  # noqa: BLE001
            last = e
    raise last


def mirror(name, version, seen):
    key = (name, version)
    if key in seen:
        return
    seen.add(key)
    base = f"{BASE}/modules/{name}/{version}"
    ddir = os.path.join(REG, "modules", name, version)
    os.makedirs(ddir, exist_ok=True)
    try:
        data = fetch(f"{base}/MODULE.bazel")
    except Exception as e:  # noqa: BLE001
        print(f"  SKIP {name}@{version}: {e}")
        return
    open(os.path.join(ddir, "MODULE.bazel"), "wb").write(data)
    mdir = os.path.join(REG, "modules", name)
    mpath = os.path.join(mdir, "metadata.json")
    if not os.path.exists(mpath):
        try:
            open(mpath, "wb").write(fetch(f"{BASE}/modules/{name}/metadata.json"))
        except Exception as e:  # noqa: BLE001
            print(f"  no metadata.json for {name}: {e}")
    text = data.decode("utf-8")
    # source.json(可能不存在; 不存在也必须继续递归依赖)
    try:
        sj_raw = fetch(f"{base}/source.json")
    except Exception:
        sj_raw = None
    if sj_raw is not None:
        open(os.path.join(ddir, "source.json"), "wb").write(sj_raw)
        sj = json.loads(sj_raw)
        for p in sj.get("patches", []):
            pp = os.path.join(ddir, p)
            os.makedirs(os.path.dirname(pp), exist_ok=True)
            if not os.path.exists(pp):
                try:
                    open(pp, "wb").write(fetch(f"{base}/{p}"))
                except Exception as e:  # noqa: BLE001
                    print(f"  patch {name}@{version}/{p}: {e}")
        url = sj.get("url")
        if url:
            fname = url.rsplit("/", 1)[-1]
            dpath = os.path.join(DIST, fname)
            want = sj.get("integrity", "")
            ok = False
            if os.path.exists(dpath) and "-" in want:
                got = "sha256-" + base64.b64encode(
                    hashlib.sha256(open(dpath, "rb").read()).digest()).decode()
                ok = (got == want)
            if not ok:
                os.makedirs(DIST, exist_ok=True)
                subprocess.run(["curl", "-sfL", "--proxy", "socks5h://127.0.0.1:10808",
                                "--max-time", "900", url, "-o", dpath], check=False)
                got = "sha256-" + base64.b64encode(
                    hashlib.sha256(open(dpath, "rb").read()).digest()).decode()
                print(f"  archive {fname}: integrity {'ok' if got == want else 'MISMATCH'}")
    print(f"mirrored {name}@{version}")
    # 递归(兼容 name 在后 / version 在前的写法)
    for m in re.finditer(r'bazel_dep\(([^)]*)\)', text, re.S):
        body = m.group(1)
        if "dev_dependency" in body and "dev_dependency = False" not in body:
            pass  # dev 依赖也镜像(保守)
        nm = re.search(r'name\s*=\s*"([^"]+)"', body)
        vr = re.search(r'version\s*=\s*"([^"]+)"', body)
        if nm and vr:
            mirror(nm.group(1), vr.group(1), seen)


seen = set()
for arg in sys.argv[3:]:
    name, version = arg.split("@")
    try:
        mirror(name, version, seen)
    except Exception as e:  # noqa: BLE001
        print(f"  FAIL {name}@{version}: {e}")
        seen.discard((name, version))
print("added:", len(seen))
