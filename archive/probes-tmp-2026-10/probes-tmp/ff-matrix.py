#!/usr/bin/env python3
"""Firefox 全矩阵执行器：geckodriver + W3C WebDriver（纯 HTTP）。
逐用例：起内嵌静态服务（复用仓库 tools/serve.py 的全部测试端点，随机端口=新 origin，
共享组固定端口）→ navigate → 轮询 document.title（页面自设 'PASS'/'FAIL'）→
读 #result 文本计 PASS 行。
输出约束：TSV 只经 os.write 写标准输出；sys.stdout 全程重定向（吞 serve.py 启动回显）。
安全自限：全部 HTTP 目标限本机环回；所有文件路径均为常量。
输出行: CASE\t<name>\t<verdict>\t<passcount>\t<耗时s>；非 PASS 附 #result 摘要。
用法: python3 ff-matrix.py [名字子串过滤]（计划固定读 /data/tmp/ff-plan.jsonl）"""
import importlib.util
import io
import json
import os
import socket
import subprocess
import sys
import threading
import time
import urllib.parse
import urllib.request

ROOT = "/data/training/cli/arkui-dom-runtime"
SERVE_PY = "/data/training/cli/arkui-dom-runtime/tools/serve.py"
PLAN_JSONL = "/data/tmp/ff-plan.jsonl"
DRIVER_PORT = 9555
DRIVER_URL = "http://127.0.0.1:9555"
POLL0, POLL, CASE_TIMEOUT = 1.5, 0.4, 25
ELEMENT_KEY = "element-6066-11e4-a52e-4f735466cecf"

sys.stdout = io.StringIO()   # 吞掉 serve.py 模块级回显；本脚本输出只走 os.write(1,...)

def out(s):
    os.write(1, (s + "\n").encode())

def local_http(url, body=None, method=None):
    """仅允许本机环回 http 请求。"""
    u = urllib.parse.urlparse(url)
    if u.scheme != "http" or u.hostname not in ("127.0.0.1", "localhost"):
        raise ValueError("只允许本机环回请求: " + url)
    req = urllib.request.Request(
        url, data=json.dumps(body).encode() if body is not None else None,
        method=method or ("POST" if body is not None else "GET"),
        headers={"Content-Type": "application/json"})
    with urllib.request.urlopen(req, timeout=60) as r:
        v = json.loads(r.read() or b"null")
    if isinstance(v, dict) and v.get("error"):
        raise RuntimeError(url + " -> " + json.dumps(v["error"], ensure_ascii=False)[:200])
    return v

def driver(method, path, body=None):
    return local_http(DRIVER_URL + path, body, method)

def free_port():
    s = socket.socket(); s.bind(("127.0.0.1", 0))
    p = s.getsockname()[1]; s.close(); return p

def start_server(want_port):
    """在同进程起一份 serve.py（守护线程；独立模块实例=独立 flaky 计数，对齐
    run.sh 每用例新服务的语义）。返回端口号。"""
    if not want_port:
        want_port = free_port()
    sys.argv = ["serve.py", str(want_port)]
    spec = importlib.util.spec_from_file_location("arksrv_" + str(want_port), SERVE_PY)
    mod = importlib.util.module_from_spec(spec)
    t = threading.Thread(target=spec.loader.exec_module, args=(mod,), daemon=True)
    t.start()
    probe = f"http://127.0.0.1:{want_port}/test/index.html"
    last = None
    for _ in range(60):
        try:
            u = urllib.parse.urlparse(probe)
            if u.hostname not in ("127.0.0.1", "localhost"):
                raise ValueError("只允许本机环回请求")
            urllib.request.urlopen(probe, timeout=2)
            return want_port
        except Exception as e:
            last = e
            time.sleep(0.2)
    raise RuntimeError(f"serve.py 未就绪 (port={want_port}): {type(last).__name__}: {last}")

def main():
    os.chdir(ROOT)   # serve.py 以 cwd 为服务根，必须在仓库根运行
    with open(PLAN_JSONL) as f:
        plan = [json.loads(l) for l in f if l.startswith("{")]
    if len(sys.argv) > 1:
        plan = [c for c in plan if sys.argv[1] in c["name"]]

    drv = subprocess.Popen(["/data/tmp/geckodriver", "--port", str(DRIVER_PORT)],
                           stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
    time.sleep(1.0)
    sid = None
    stats = {"PASS": 0, "FAIL": 0, "TIMEOUT": 0, "ERROR": 0}
    try:
        v = driver("POST", "/session", {"capabilities": {"alwaysMatch": {
            "browserName": "firefox",
            "moz:firefoxOptions": {"args": ["-headless"]}}}})
        sid = v["value"]["sessionId"]

        cur_group, port = None, None
        for c in plan:
            try:
                if c["group"] != cur_group:
                    cur_group = c["group"]
                    port = start_server(0)
                url = f"http://127.0.0.1:{port}/{c['page'].lstrip('/')}{c['query']}"
                t0 = time.time()
                driver("POST", f"/session/{sid}/url", {"url": url})
                time.sleep(POLL0)
                verdict, deadline = None, time.time() + CASE_TIMEOUT
                while time.time() < deadline:
                    try:
                        t = driver("GET", f"/session/{sid}/title")["value"]
                        if t in ("PASS", "FAIL"):
                            verdict = t
                            break
                    except Exception:
                        pass
                    time.sleep(POLL)
                el = driver("POST", f"/session/{sid}/element",
                            {"using": "css selector", "value": "#result"})["value"]
                text = driver("GET", f"/session/{sid}/element/{el[ELEMENT_KEY]}/text")["value"]
                if verdict is None:
                    # 部分页不设 title（判定只看 #result 文本，与 Chrome 驱动同约定）
                    if "=== ALL PASS" in text:
                        verdict = "PASS"
                    elif "FAILURES" in text or "=== HAS FAILURE" in text:
                        verdict = "FAIL"
                npass = sum(1 for ln in text.splitlines() if ln.startswith("PASS "))
                stats[verdict] += 1
                print(f"CASE\t{c['name']}\t{verdict}\t{npass}\t{time.time()-t0:.1f}", flush=True)
                if verdict != "PASS" or os.environ.get("FF_DEBUG_DUMP"):
                    out(f"---- {c['name']} #result 摘要 ----")
                    for ln in text.splitlines()[:14]:
                        out("  " + ln)
            except Exception as e:
                stats["ERROR"] += 1
                out(f"CASE\t{c['name']}\tERROR\t0\t0.0")
                out(f"  ERR {type(e).__name__}: {e}")
        out(f"SUMMARY\tPASS={stats['PASS']}\tFAIL={stats['FAIL']}\t"
            f"TIMEOUT={stats['TIMEOUT']}\tERROR={stats['ERROR']}\tTOTAL={len(plan)}")
    finally:
        if sid:
            try: driver("DELETE", f"/session/{sid}")
            except Exception: pass
        drv.terminate()

if __name__ == "__main__":
    main()
