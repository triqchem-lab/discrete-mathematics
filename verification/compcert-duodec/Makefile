# 12进制数学库 DuodecClock 双编译器验证（CompCert + gcc）
#
# CompCert 3.17 带数学验证器的 C 编译器（汇编语义 = C 语义，机器证明）
#   - CompCert 路径默认 /opt/CompCert/bin/ccomp，可覆盖：make COMPCERT=xxx
#   - 未安装 CompCert 时可只用 gcc 验证数学正确性：make verify-gcc

COMPCERT ?= /opt/CompCert/bin/ccomp
CC       ?= gcc
CFLAGS   ?= -O2 -Wall

.PHONY: all verify-gcc verify-compcert compare clean

all: verify-gcc compare

# 数学正确性：62 项断言对照 Agda 定理（Trit/AlphaPower/GF9/Duodec/φ/常量）
verify-gcc: duodec_verify.c
	$(CC) $(CFLAGS) -o duodec_gcc duodec_verify.c
	./duodec_gcc

# 编译正确性：同一份源码经 CompCert 编译运行，断言必须同样全过
verify-compcert: duodec_verify.c
	$(COMPCERT) -O2 -o duodec_cc duodec_verify.c
	./duodec_cc

# 交叉验证：CompCert 与 gcc 输出逐行一致
compare: duodec_verify.c
	$(CC) $(CFLAGS) -o duodec_gcc duodec_verify.c
	$(COMPCERT) -O2 -o duodec_cc duodec_verify.c
	./duodec_gcc > /tmp/duodec_gcc.out
	./duodec_cc > /tmp/duodec_cc.out
	diff /tmp/duodec_gcc.out /tmp/duodec_cc.out
	@echo "OK: CompCert 与 gcc 输出一致"

clean:
	rm -f duodec_cc duodec_gcc
