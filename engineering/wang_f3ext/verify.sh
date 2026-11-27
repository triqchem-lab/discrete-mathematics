#!/bin/bash
# verify.sh <证书.pb.txt> —— 对一份 F₃ 证书做三重验证:
#   ① 框架自带的 C++ verifier(在副本上跑; 旁车 .btp 须与证书同名同目录)
#   ② 独立的 Python / C 核对器(engineering/wang_cert_check_fq.py + forced_fq + bt_fq)
#   ③ 负控制: 把终轨道的声明抬高 7, 核对器必须转红
# 可用环境变量: BIN_DIR(verifier_f3 所在目录, 缺省 /tmp/wang-f3)、WORK(临时目录, 缺省 /tmp/wang-run)。
# 权威顺序: 这三步的输出 > 任何文档里的数字。
set -u
CERT=$1
if [ -z "$CERT" ] || [ ! -f "$CERT" ]; then
  echo "usage: verify.sh <cert.pb.txt>" >&2
  exit 2
fi
HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ENG="$(cd "$HERE/.." && pwd)"
BIN_DIR="${BIN_DIR:-/tmp/wang-f3}"
WORK="${WORK:-/tmp/wang-run}"
mkdir -p "$WORK"
TAG="$WORK/verify_$$_$(basename "$CERT" .pb.txt)"
cp "$CERT" "$TAG.pb.txt" || exit 2
cp "${CERT%.pb.txt}.btp" "$TAG.btp" || { echo "missing sidecar ${CERT%.pb.txt}.btp" >&2; exit 2; }

echo "== ① C++ verifier ($BIN_DIR/verifier_f3) =="
/usr/bin/time -l "$BIN_DIR/verifier_f3" "$TAG.pb.txt" > "$TAG.verifier.log" 2>&1
rc=$?
python3 -I - "$TAG.verifier.log" "$rc" <<'PY'
import sys
for l in open(sys.argv[1], errors='replace').read().split('\n'):
    if ('Verified' in l or 'BOUND' in l or 'OK.' in l or 'CHECK' in l or 'FAIL' in l
            or 'Abort' in l or ' real' in l or 'maximum resident' in l):
        print('  ', l[:120])
print('   verifier rc =', sys.argv[2])
PY

echo "== ② independent Python/C checker =="
/usr/bin/time -l python3 -I "$ENG/wang_cert_check_fq.py" "$TAG.pb.txt" > "$TAG.checker.log" 2>&1
rc=$?
python3 -I - "$TAG.checker.log" "$rc" <<'PY'
import sys
for l in open(sys.argv[1], errors='replace').read().split('\n'):
    if 'BOUND' in l or 'OK.' in l or 'Error' in l or ' real' in l or 'maximum resident' in l:
        print('  ', l[:260])
print('   checker rc =', sys.argv[2])
PY

echo "== ③ negative control (final orbit's claim += 7) =="
LAST=$(python3 -I - "$TAG.pb.txt" <<'PY'
import re, sys
t = open(sys.argv[1], errors='replace').read()
idx = [int(x) for x in re.findall(r'(?m)^\s*index:\s*(\d+)\s*$', t)]
print(max(idx) if idx else -1)
PY
)
python3 -I "$ENG/wang_cert_check_fq.py" "$TAG.pb.txt" --corrupt "$LAST" > "$TAG.corrupt.log" 2>&1
rc=$?
tail -1 "$TAG.corrupt.log" | cut -c1-200
echo "   corrupted run rc = $rc  (must be non-zero; orbit $LAST)"

echo "logs: $TAG.{verifier,checker,corrupt}.log"
