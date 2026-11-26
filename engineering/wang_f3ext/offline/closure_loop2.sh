#!/bin/bash
LOG=/tmp/closure_loop2.log
REG=/tmp/bcr-mirror-full
DIST=/tmp/distdir
cd /tmp/wang-tensor-rank || exit 1
echo "=== closure loop2 start $(date) ===" > $LOG
for i in $(seq 1 120); do
  OUT=$(~/tools/bin/bazelisk fetch --registry=file://$REG --distdir=$DIST \
        //verifier:verifier_main //verifier:verifier_test \
        //problems/matrix:fq_matrix_test //problems/matrix:symmetry_test \
        //search:orbit_enumerator_main //search:rank_lower_bound_main 2>&1)
  if [ $? -eq 0 ]; then echo "=== FETCH OK at iteration $i $(date) ===" >> $LOG; echo "$OUT" | tail -3 >> $LOG; exit 0; fi
  echo "--- iteration $i ---" >> $LOG
  echo "$OUT" | grep -E "ERROR|not found|FAIL" | head -4 >> $LOG
  MISSING=$(echo "$OUT" | grep -oE "modules/[A-Za-z0-9_.+-]+/[^/]+/MODULE\.bazel" | sed 's|modules/||; s|/MODULE.bazel||' | awk -F/ '{print $1"@"$2}' | sort -u)
  if [ -z "$MISSING" ]; then echo "$OUT" | tail -15 >> $LOG; echo "=== NON-REGISTRY FAILURE ===" >> $LOG; exit 2; fi
  echo "missing: $MISSING" >> $LOG
  python3 -I /tmp/wang-shim/bcr_add_module.py $REG $DIST $MISSING >> $LOG 2>&1
done
echo "=== NOT CONVERGED after 120 iterations ===" >> $LOG
exit 3
