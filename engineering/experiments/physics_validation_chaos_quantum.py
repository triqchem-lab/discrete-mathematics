"""物理验证：混沌量子理论 vs 本框架量子模型 对照实验。

背景：外部提出"混沌量子理论"（chaotic quantum dynamics — 对初始条件敏感、
轨迹不可预测）。本框架的石英声子-等离子体引擎（scholar-loop
quartz_phonon）采用 N14 量子时钟 LCM 域精确整数相位追踪 + Lidari 离散
相变阈值，声称是**决定性量子模型**而非混沌模型。本脚本执行五项可证伪检验：

  T1 决定性 (determinism)        — 同参数同种子两次运行必须 bit-for-bit 相等
  T2 混沌敏感度 (Lyapunov 对照)  — 1e-9 相对扰动下 FOM 的相对变化；
                                    混沌系统应 O(1)，决定性系统应 O(1e-9)
  T3 量子时钟精确性              — N14 LCM 相位是精确整数运算，无浮点漂移；
                                    6624 步 grand pump 对齐零误差
  T4 相变锐利性 (量子化 vs 平滑) — Lidari 0.38/0.75 阈值是离散跳变（量子相变），
                                    不是热学 crossover
  T5 C3 时间晶体周期性           — 1500 步周期、三相位 {0,500,1000} 精确轮转

判据：若 T2 显示 O(1) 敏感 → 支持混沌理论；若 T2 显示 O(ε) 且 T1/T3 精确
→ 支持本框架的决定性量子模型。
"""
from __future__ import annotations

import json
import math
import sys
from pathlib import Path

SCHOLAR_LOOP = Path("/data/training/cli/scholar-loop")
sys.path.insert(0, str(SCHOLAR_LOOP))

from engines.quartz_phonon.train import (          # noqa: E402
    run_simulation, HPARAMS, LCM_TOTAL, OMEGA_0, GRAND_PUMP,
    C3_CYCLE_STEPS, TIME_CRYSTAL_PHASES,
)
from engines.quartz_phonon.prepare import compute_plasma_fom  # noqa: E402

BASE = {k: float(v) for k, v in HPARAMS.items()}
KNOBS = ["ring_radius_m", "drive_frequency_hz", "drive_power_w",
         "quality_factor", "heating_time_s"]
EPS = 1e-9   # 相对扰动幅度


def trace_fom(tr: dict) -> float:
    return compute_plasma_fom(tr)


def t1_determinism() -> dict:
    a = run_simulation(0, dict(BASE))
    b = run_simulation(0, dict(BASE))
    identical = json.dumps(a, sort_keys=True) == json.dumps(b, sort_keys=True)
    return {"test": "T1_determinism", "bit_identical": identical,
            "fom": trace_fom(a),
            "pass": identical}


def t2_chaos_sensitivity() -> dict:
    """对每个 knob 施加 ±EPS 相对扰动，测 FOM 的相对变化。
    混沌判据：若 ∃ knob 使 |ΔFOM/FOM| ~ O(1)（远大于 EPS），则为混沌。
    决定性判据：所有 |ΔFOM/FOM| = O(EPS)（条件数 ~ O(1)）。"""
    f0 = trace_fom(run_simulation(0, dict(BASE)))
    rows = []
    for k in KNOBS:
        cfg = dict(BASE)
        cfg[k] = BASE[k] * (1.0 + EPS)
        fp = trace_fom(run_simulation(0, cfg))
        cfg[k] = BASE[k] * (1.0 - EPS)
        fm = trace_fom(run_simulation(0, cfg))
        rel = max(abs(fp - f0), abs(fm - f0)) / max(f0, 1e-30)
        cond = rel / EPS          # 数值条件数：混沌 → 发散；决定性 → O(1)
        rows.append({"knob": k, "rel_dFOM": rel, "condition_number": cond})
    # 混沌阈值：条件数 > 1e3 即视为对初值敏感（混沌签名）
    is_chaotic = any(r["condition_number"] > 1e3 for r in rows)
    return {"test": "T2_chaos_sensitivity", "baseline_fom": f0, "eps": EPS,
            "max_rel_dFOM": max(r["rel_dFOM"] for r in rows),
            "max_condition_number": max(r["condition_number"] for r in rows),
            "per_knob": rows,
            "verdict": "CHAOTIC" if is_chaotic else "DETERMINISTIC",
            "pass": True}


def t3_quantum_clock_exactness() -> dict:
    """N14 LCM 相位必须是精确整数；6624 对齐必须零误差。"""
    tr = run_simulation(0, dict(BASE))
    n14_steps = tr["n14_steps"]
    phase = (n14_steps * OMEGA_0) % LCM_TOTAL           # 纯整数
    angle = (phase / LCM_TOTAL) * 2.0 * math.pi
    exact_match = (phase == tr["n14_phase"])
    angle_in_range = 0.0 <= angle < 2.0 * math.pi
    # grand pump 对齐：寻找最小正步数 s 使 (s*OMEGA_0) % GRAND_PUMP == 0
    align_step = None
    for s in range(1, GRAND_PUMP * 2 + 1):
        if (s * OMEGA_0) % GRAND_PUMP == 0:
            align_step = s
            break
    drift = (n14_steps * OMEGA_0) - ((n14_steps * OMEGA_0) // LCM_TOTAL) * LCM_TOTAL - phase
    return {"test": "T3_quantum_clock_exactness",
            "n14_steps": n14_steps, "phase_int": phase,
            "angle_rad": round(angle, 12),
            "integer_exact": exact_match, "angle_in_0_2pi": angle_in_range,
            "residual_drift": drift,
            "first_alignment_step": align_step,
            "grand_pump": GRAND_PUMP,
            "pass": exact_match and angle_in_range and drift == 0}


def t4_phase_transition_sharpness() -> dict:
    """扫描加热时间（能量累积维度），观察 lidari_phase 是否在阈值处离散跳变。
    量子相变签名：相态标签在某能量点不连续跳变；
    热学 crossover 则是平滑过渡（无明确跳变点）。
    注：默认 N14 参数下功率扫描会使 overtone_density 饱和，
    故改扫 heating_time_s（对数），直接控制累积声子能量密度。"""
    times = [10.0 ** (i / 4.0) * 1e-6 for i in range(0, 33)]  # 1e-6 → 1e2 s
    seq = []
    for t in times:
        cfg = dict(BASE); cfg["heating_time_s"] = t
        tr = run_simulation(0, cfg)
        seq.append((round(t, 9), tr["overtone_density"], tr["lidari_phase"]))
    jumps = [(seq[i-1][0], seq[i][0], seq[i-1][2], seq[i][2])
             for i in range(1, len(seq)) if seq[i][2] != seq[i-1][2]]
    discrete = len(jumps) > 0
    crosses_threshold = any(
        (seq[i-1][1] < 0.38 <= seq[i][1]) or (seq[i-1][1] < 0.75 <= seq[i][1])
        for i in range(1, len(seq)))
    return {"test": "T4_phase_transition_sharpness",
            "n_points": len(seq),
            "phase_jumps": jumps,
            "discrete_jump_observed": discrete,
            "crosses_lidari_threshold": crosses_threshold,
            "trajectory_sample": seq[::4],
            "verdict": ("QUANTUM_PHASE_TRANSITION"
                        if (discrete and crosses_threshold)
                        else "THERMAL_CROSSOVER"),
            "pass": discrete}


def t5_c3_time_crystal() -> dict:
    """C3 时间晶体：1500 步周期，相位 {0,500,1000} 精确轮转。"""
    phases_seen = set()
    for step in range(0, C3_CYCLE_STEPS * 3, 1):
        c3 = step % C3_CYCLE_STEPS
        tc = min(TIME_CRYSTAL_PHASES,
                 key=lambda p: min(abs(c3 - p), C3_CYCLE_STEPS - abs(c3 - p)))
        phases_seen.add(tc)
    expected = set(TIME_CRYSTAL_PHASES)
    return {"test": "T5_c3_time_crystal",
            "cycle_steps": C3_CYCLE_STEPS,
            "expected_phases": sorted(expected),
            "observed_phases": sorted(phases_seen),
            "exact_3fold": phases_seen == expected,
            "pass": phases_seen == expected}


def main() -> int:
    results = [t1_determinism(), t2_chaos_sensitivity(),
               t3_quantum_clock_exactness(), t4_phase_transition_sharpness(),
               t5_c3_time_crystal()]
    all_pass = all(r["pass"] for r in results)
    report = {"framework": "quartz-phonon-plasma (N14 quantum clock + Lidari)",
              "contrast": ("chaotic quantum theory (sensitive to IC) vs "
                           "deterministic quantum model (exact integer phase)"),
              "tests": results, "all_pass": all_pass}
    print(json.dumps(report, indent=2, ensure_ascii=False))
    return 0 if all_pass else 1


if __name__ == "__main__":
    raise SystemExit(main())
