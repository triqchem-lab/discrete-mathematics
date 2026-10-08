#!/usr/bin/env python3
"""Firefox BiDi 冒烟：session.new → navigate → 等 7s → captureScreenshot。
截图以 base64 打到 stdout（不落盘，由外层 shell 解码），每页一段：
  SHOT<TAB><url>
  <base64 单行>
用法: python3 ff-smoke.py <端口> <url> [<url>...]"""
import json, sys, time, base64
import websocket

port = sys.argv[1]
urls = sys.argv[2:]

ws = websocket.create_connection(f"ws://127.0.0.1:{port}/session", timeout=90,
                                 suppress_origin=True)
seq = [0]
def rpc(method, params=None, wait=60):
    seq[0] += 1
    ws.send(json.dumps({"id": seq[0], "method": method, "params": params or {}}))
    deadline = time.time() + wait
    while time.time() < deadline:
        m = json.loads(ws.recv())
        if m.get("id") == seq[0]:
            if m.get("type") == "error" or "error" in m:
                raise RuntimeError(f"{method} -> {json.dumps(m.get('error'), ensure_ascii=False)[:300]}")
            return m["result"]
    raise TimeoutError(method)

rpc("session.new", {"capabilities": {"alwaysMatch": {}}})
ctx = rpc("browsingContext.getTree")["contexts"][0]["context"]

for url in urls:
    try:
        rpc("browsingContext.navigate", {"context": ctx, "url": url, "wait": "complete"})
        time.sleep(7)  # rAF/定时器断言收敛窗口
        shot = rpc("browsingContext.captureScreenshot", {"context": ctx})
        sys.stdout.write("SHOT\t" + url + "\n" + shot["data"] + "\n")
    except Exception as e:
        print(f"ERR {url}: {e}")
try:
    rpc("session.end", wait=8)
except Exception:
    pass
ws.close()
