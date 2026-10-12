#!/usr/bin/env python3
"""Firefox BiDi 冒烟驱动：加载测试页 → 等断言完成 → 读 #result 终态文本。
用法: python3 ff-bidi.py <url> [<url>...]
前置: firefox --headless --remote-debugging-port=9333 已起。"""
import json, sys, time
import websocket
import urllib.request

WS = "ws://127.0.0.1:9333/session"

def rpc(ws, seq, method, params=None, wait=30):
    ws.send(json.dumps({"id": seq, "method": method, "params": params or {}}))
    deadline = time.time() + wait
    while time.time() < deadline:
        msg = json.loads(ws.recv())
        if msg.get("id") == seq:
        if "error" in msg:
            raise RuntimeError(f"{method} -> {json.dumps(msg.get('error'), ensure_ascii=False)}")
            return msg.get("result", {})
    raise TimeoutError(method)

def main():
    urls = sys.argv[1:]
    ws = websocket.create_connection(WS, timeout=60, suppress_origin=True)
    rpc(ws, 1, "session.new", {"capabilities": {"alwaysMatch": {"acceptInsecureCerts": True}}})
    for url in urls:
        try:
            tree = rpc(ws, 2, "browsingContext.getTree")
            ctx = tree["contexts"][0]["context"]
            rpc(ws, 3, "browsingContext.navigate",
                {"context": ctx, "url": url, "wait": "complete"}, wait=40)
            time.sleep(7)  # rAF/定时器断言收敛窗口（对齐 Chrome 8000ms 虚拟预算的实时刻度）
            res = rpc(ws, 4, "script.evaluate", {
                "expression": "document.querySelector('#result') ? document.querySelector('#result').innerText : 'NO-RESULT-NODE'",
                "target": {"context": ctx}})
            print(f"==== {url} ====")
            print(res.get("result", {}).get("value", json.dumps(res)[:300]))
        except Exception as e:
            print(f"==== {url} ====\nERROR {e}")
    try:
        rpc(ws, 9, "session.end", wait=5)
    except Exception:
        pass
    ws.close()

if __name__ == "__main__":
    main()
