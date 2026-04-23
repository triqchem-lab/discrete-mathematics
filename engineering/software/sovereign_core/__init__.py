"""
Sovereign Core - 律算合一核心库 (认知升维版)
Sovereign Core - LvSuan HeYi (Cognitive Ascension Edition)

============================================================
⚠️ 认知升维说明
============================================================
- 废除“宪法/违宪”术语 -> 改用“定式/失算”。
- 废除浮点数 -> 全量使用整数与定点数学。
- 几何拓扑 (陈数/能隙/弦长) 是通用真理，非文明独占。
============================================================
"""

# --- 卷一：公理 (Axioms) ---
from .axioms import (
    MAGIC_120, MAGIC_24, TOTAL_144,
    POLAR_WINDING, TOROIDAL_WINDING,
    SOVEREIGN_LCM, FACTOR_3_11, FACTOR_2_16,
    GF3Trit,
    calculate_length,
    digital_root, is_stable_wave,
    check_wuxing_modulus,
    zhonglv_closure,
    check_holistic_closure
)

# --- 卷二：五行与情感/通信投影 (WuXing & Projections) ---
from .wuxing import (
    WuXing, Chirality,
    WUXING_BASE_MAP, WUXING_GENERATE_PATH, WUXING_OVERCOME_MAP,
    get_chirality_from_trit,
    resonance_check, emotional_cycle_step,
    calculate_channel_id, check_isolation_wall
)

# --- 卷三：结构学与几何拓扑 (Structology & Geometry) ---
from .geometry import (
    Tryte, SovereignFiber, PackedIO
)
