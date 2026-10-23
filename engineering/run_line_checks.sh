#!/usr/bin/env bash
# 富勒烯 + NSE 两线的证据回归（**便利脚本，非门禁**——门禁一律住系统层）。
# 逐项跑、逐项报退出码；任一项非 0 最终退出 1。
#
# 用法: bash engineering/run_line_checks.sh
set -u
fail=0
run() {  # run <名称> <命令...>
  local name="$1"; shift
  if "$@" >/tmp/_line_check.out 2>&1; then
    echo "✅ $name"
  else
    echo "❌ $name（exit $?）"; tail -5 /tmp/_line_check.out; fail=1
  fi
}

SL=/data/training/cli/scholar-loop
run "数据校验（reference_levels）"     python3 "$SL/engines/h2o_c60/validate_reference_levels.py"
run "拟合诊断（fit_v6）"               python3 -c "import sys; sys.path.insert(0,'$SL'); from engines.h2o_c60 import fit_v6; fit_v6.report()"
run "轨道核验（I_h on 1770 对）"        python3 "$SL/engines/h2o_c60/verify_ih_orbits.py"
run "特征标正交性（ℚ(√5) 精确）"        python3 engineering/verify_polyhedral_characters.py
run "A₄ 闭包（精确整数）"               python3 engineering/verify_a4_closure.py
run "V6 不可约结构（J=1..6）"          python3 "$SL/engines/h2o_c60/verify_v6_structure.py"
run "V6 不变子空间唯一性（rank=1）"   python3 "$SL/engines/h2o_c60/verify_v6_uniqueness.py"
run "文档数字 vs 重算（11 项）"        bash -c "cd $SL && python3 -m engines.h2o_c60.verify_claims"
run "晶体场：偶极-四极三分子排序"   bash -c "cd $SL && python3 -m engines.h2o_c60.crystal_field_electrostatic >/dev/null"
run "NSE 秩 454/275（精确整数）"        python3 engineering/verify_nse_rank6.py
run "文档回执对账"                      python3 engineering/check_receipt_refs.py

echo
if [ "$fail" -eq 0 ]; then echo "全部通过"; else echo "有失败项"; fi
exit "$fail"
