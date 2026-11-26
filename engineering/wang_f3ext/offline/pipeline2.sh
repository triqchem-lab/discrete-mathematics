#!/bin/bash
# A-T3 流水线 v2: 本地 registry + distdir 全离线。
# [1] fetch → [2] FqMatrix/F₃ 群单测 + F₂ 回归测试 → [3] 构建 F₂ verifier → [4] C++ 地面真值
LOG=/tmp/pipeline2.log
REG="--registry=file:///tmp/bcr-mirror-full --distdir=/tmp/distdir"
cd /tmp/wang-tensor-rank || exit 1
echo "=== pipeline2 start $(date) ===" >> $LOG

# [1] fetch(全部走本地)
~/tools/bin/bazelisk fetch $REG //verifier:verifier_main //verifier:verifier_test \
  //problems/matrix:fq_matrix_test //problems/matrix:symmetry_test >> $LOG 2>&1
R=$?; echo "=== [1] fetch exit=$R $(date) ===" >> $LOG
[ $R -ne 0 ] && { echo "=== FETCH FAILED ===" >> $LOG; exit 1; }

# [2] 单测: F₃ 新测试 + F₂ 回归(现有 symmetry_test / verifier_test)
~/tools/bin/bazelisk test $REG //problems/matrix:fq_matrix_test \
  //problems/matrix:symmetry_test //problems/matrix:f2_matrix_test \
  //problems/matrix:f2_matrix_tables_test //problems/matrix:tensor_test >> $LOG 2>&1
R=$?; echo "=== [2] matrix tests exit=$R $(date) ===" >> $LOG

~/tools/bin/bazelisk test $REG //verifier:verifier_test >> $LOG 2>&1
R=$?; echo "=== [2b] verifier_test exit=$R $(date) ===" >> $LOG

# [3] 构建 F₂ verifier
~/tools/bin/bazelisk build $REG --config=opt //verifier:verifier_main \
  --per_file_copt='.*_main\.cc@-DCP_MATRIX,-DCP_P=2,-DCP_M=1,-DCP_N0=3,-DCP_N1=3,-DCP_N2=3' >> $LOG 2>&1
R=$?; echo "=== [3] build exit=$R $(date) ===" >> $LOG
[ $R -ne 0 ] && { echo "=== BUILD FAILED ===" >> $LOG; exit 1; }

# [4] C++ 地面真值(真身证书 + .btp 同目录)
cp /tmp/wang-tensor-rank/real_cert_matrix_q02_n333.pb.txt /tmp/wang-tensor-rank/certs/matrix/cert_matrix_q02_n333.pb.txt
cp /tmp/wang-tensor-rank/real_cert_matrix_q02_n333.btp /tmp/wang-tensor-rank/certs/matrix/cert_matrix_q02_n333.btp
./bazel-bin/verifier/verifier_main certs/matrix/cert_matrix_q02_n333.pb.txt >> $LOG 2>&1
R=$?; echo "=== [4] C++ verifier exit=$R (期望 0 且下界 20) $(date) ===" >> $LOG
echo "=== pipeline2 done $(date) ===" >> $LOG
