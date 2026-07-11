"""
Reasonix 系统提示词评估任务集 v3 — 项目专属

全部任务来源于 discrete-mathematics 项目真实需求:
- Agda 证明填充（postulate消除 / hole填补）
- Python bug 修复（已知bug / 宪法违规）
- 跨语言一致性验证
- 多文件重构

设计原则:
- 每个任务含完整上下文（不需要 agent 猜测项目结构）
- 验证标准可自动化检查（agda typecheck / python -m pytest / shell exit code）
- 难度分级:  easy(Python修bug) → medium(简单Agda hole) → hard(多postulate消除+证明链)
- 覆盖Fable5原则: 拓扑扫描(读imports)/多路径(证明策略选择)/沙盒验证(agda check)

任务结构:
{
  "id": str,
  "source": "实际文件和行号",
  "difficulty": "easy|medium|hard",
  "category": "bugfix|agda_hole|agda_postulate|refactor|cross_lang|shell",
  "fable5_principles": [涉及的Fable5原则],
  "context": "给agent的前置上下文",
  "instruction": "自然语言任务",
  "verify": [{"cmd": "shell命令", "expect": "期望的exit code或输出模式"}],
  "anti_patterns": ["禁止的行为"],
}
"""

EVAL_TASKS_V3 = [
    # ================================================================
    # 🟢 EASY — Python bug修复 (已知bug, 单文件, 明确修复)
    # ================================================================

    {
        "id": "fix_loss_gain_validation",
        "source": "engineering/software/sovereign_core/loss_gain.py:127-135",
        "difficulty": "easy",
        "category": "bugfix",
        "fable5_principles": [1, 5, 9],
        "context": """
loss_gain.py 的 validate_loss_gain() 函数引用了三个不存在的函数。
需要实现它们，使其与已有的十二律数据一致。

关键背景:
- TWELVE_LU_LENGTHS = [81, 54, 72, 48, 64, 43, 57, 38, 51, 34, 45, 30]
- loss(81) 应返回损益操作后的值: 81→54 (三分损一)
- gain(54) 应返回益操作后的值: 54→72 (三分益一)
- generate_twelve_lu_chain(81) 应从黄钟(81)开始生成完整十二律链
- 损益规则: 损 = n * 2/3, 益 = n * 4/3 (均用整数)
""",
        "instruction": "实现 loss()、gain()、generate_twelve_lu_chain() 三个函数，使 validate_loss_gain() 能正确运行。使用整数运算（不允许浮点）。完成后运行 python3 loss_gain.py 验证。",
        "verify": [
            {"cmd": "cd /data/work/discrete-mathematics && python3 engineering/software/sovereign_core/loss_gain.py 2>&1", "expect": "exit=0"},
            {"cmd": "cd /data/work/discrete-mathematics && python3 -c \"from engineering.software.sovereign_core.loss_gain import loss, gain; assert loss(81) == 54; assert gain(54) == 72; print('OK')\"", "expect": "OK"},
        ],
        "anti_patterns": [
            "使用浮点数",
            "只改注释不变实现",
        ],
    },

    {
        "id": "fix_tq10_constructor",
        "source": "engineering/software/sovereign_core/tq10_format.py:238-244",
        "difficulty": "easy",
        "category": "bugfix",
        "fable5_principles": [2, 5],
        "context": """
tq10_format.py 的 validate_tq10() 函数调用 SovereignBlock 时传了错误的参数名。
SovereignBlock.__init__ 的参数是 trytes (不是 qs)。
""",
        "instruction": "修复 validate_tq10() 中 SovereignBlock 的构造函数调用：将参数名从 qs 改为 trytes。完成后运行 python3 tq10_format.py 验证。不要改变其他任何代码。",
        "verify": [
            {"cmd": "cd /data/work/discrete-mathematics && python3 engineering/software/sovereign_core/tq10_format.py 2>&1", "expect": "exit=0"},
        ],
        "anti_patterns": [
            "改变 validate 逻辑",
            "修改 SovereignBlock 的 __init__",
        ],
    },

    {
        "id": "defeat_magnetic_civilization",
        "source": "engineering/software/sovereign_core/magnetic_civilization.py",
        "difficulty": "easy",
        "category": "refactor",
        "fable5_principles": [4, 8],
        "context": """
magnetic_civilization.py 多处使用浮点数，违反项目宪法"严禁使用浮点数"。
需要用 Fraction 或整数比替换所有 float。

需要修改的地方:
- wuxing_weights: List[float] → 全部改为 Fraction
- chiral_beta: float → Fraction
- PI_355_113 = 355 / 113 → Fraction(355, 113) 
- calculate_emotional_coherence() → 使用 Fraction 算术
""",
        "instruction": "将 magnetic_civilization.py 中的全部浮点数替换为 fractions.Fraction，确保计算精确。修改后运行现有测试确保不引入回归: python3 -m pytest engineering/tests/test_sovereign_core.py -v -k 'not magnetic' 2>&1（先确认非magnetic测试通过）。",
        "verify": [
            {"cmd": "cd /data/work/discrete-mathematics && grep -c 'float' engineering/software/sovereign_core/magnetic_civilization.py", "expect": "0"},
            {"cmd": "cd /data/work/discrete-mathematics && python3 -c \"from engineering.software.sovereign_core.magnetic_civilization import PI_355_113; from fractions import Fraction; assert isinstance(PI_355_113, Fraction); print('OK')\"", "expect": "OK"},
        ],
        "anti_patterns": [
            "保留任何 float 类型",
            "只是加注释不改代码",
        ],
    },

    # ================================================================
    # 🟡 MEDIUM — Agda hole填充 (简单证明, 1-2个hole)
    # ================================================================

    {
        "id": "prove_sun_yi_not_invertible",
        "source": "src/Sovereign/Constitution/WindingAsymmetry.agda",
        "difficulty": "medium",
        "category": "agda_hole",
        "fable5_principles": [1, 3, 5],
        "context": """
WindingAsymmetry.agda 中有两个未填充的 hole:
- sunNotInvertible : 损操作不可逆（损之后再益不一定回到原值，因为整数除法截断）
- yiNotInvertible : 益操作不可逆

损益规则（整数域）:
  sun(n) = n * 2 / 3   (向下取整)
  yi(n)  = n * 4 / 3   (向下取整)

要证明: 存在 n 使得 yi(sun(n)) ≠ n（或 sun(yi(n)) ≠ n）
提示: 尝试 n=81 (黄钟) 作为反例。
81 → sun→ 54 → yi→ 72 ≠ 81
""",
        "instruction": "在 WindingAsymmetry.agda 中填充 sunNotInvertible 和 yiNotInvertible 的证明（= ? 替换为具体证明）。用具体反例构造证明——不需要泛型全称量化，存在性即足够。完成后运行 agda 检查该文件。",
        "verify": [
            {"cmd": "cd /data/work/discrete-mathematics && agda src/Sovereign/Constitution/WindingAsymmetry.agda 2>&1 | tail -5", "expect": "exit=0"},
            {"cmd": "cd /data/work/discrete-mathematics && grep -c '= ?' src/Sovereign/Constitution/WindingAsymmetry.agda", "expect": "7"},  # 9→7, 减少了2个
        ],
        "anti_patterns": [
            "添加新的 postulate",
            "改变现有类型签名",
        ],
    },

    {
        "id": "prove_digital_root_converges",
        "source": "src/Sovereign/Projection/Decimal/Proofs.agda",
        "difficulty": "medium",
        "category": "agda_hole",
        "fable5_principles": [1, 5],
        "context": """
Decimal/Proofs.agda 包含四个未填充的 hole, 其中两个是:
- digitalRootConverges : 数字根迭代最终收敛
- digitalRootStable : 收敛后不再变化

数字根定义: 反复求各位数字之和，直到得到一位数。
如 12345 → 1+2+3+4+5=15 → 1+5=6。数字根 = 6。

关键引理: 对任意 n > 9, digitSum(n) < n（数字和严格小于原数）。
这保证了有限步内收敛。
""",
        "instruction": "用 digitSum(n) < n (n > 9) 的引理，证明 digitalRootConverges 和 digitalRootStable。先读文件理解现有结构和可用引理，然后填充 = ? 为具体证明。完成后 agda 检查。",
        "verify": [
            {"cmd": "cd /data/work/discrete-mathematics && agda src/Sovereign/Projection/Decimal/Proofs.agda 2>&1 | tail -5", "expect": "exit=0"},
        ],
        "anti_patterns": [
            "添加 postulate",
        ],
    },

    {
        "id": "prove_lemma_q_lt_and_sum_lt",
        "source": "src/Sovereign/Projection/Decimal/Proofs.agda",
        "difficulty": "medium",
        "category": "agda_hole",
        "fable5_principles": [1, 5],
        "context": """
Decimal/Proofs.agda 中还有两个 hole:
- lemma_q_lt : 商小于被除数（当除数>1时）
- lemma_sum_lt : digitSum 的辅助引理

这两个是 digitalRootConverges 的前置引理。需要先填这两个，再填主定理。
""",
        "instruction": "填充 lemma_q_lt 和 lemma_sum_lt 两个辅助引理。完成后 agda 检查 Decimal/Proofs.agda 通过。",
        "verify": [
            {"cmd": "cd /data/work/discrete-mathematics && agda src/Sovereign/Projection/Decimal/Proofs.agda 2>&1 | tail -5", "expect": "exit=0"},
        ],
        "anti_patterns": [
            "添加 postulate",
        ],
    },

    # ================================================================
    # 🟡 MEDIUM — Shell / 跨语言 / CI
    # ================================================================

    {
        "id": "cross_check_zhonglv_closure",
        "source": "loss_gain.py ↔ Coupling/ZhonglvClosure.agda",
        "difficulty": "medium",
        "category": "cross_lang",
        "fable5_principles": [1, 2, 5, 9],
        "context": """
Python 的 loss_gain.py 实现了仲吕闭合检查:
  zhonglv_closure() — 从黄钟(81)出发，经损益链应回到或接近黄钟

Agda 的 Coupling/ZhonglvClosure.agda 形式化证明了闭合性。

需要验证两个实现是否一致。
""",
        "instruction": "写一个 Python 脚本检查 loss_gain.py 的 zhonglv_closure() 返回值是否与 Agda 中声明的常量一致。具体：\n1. 从 Python 运行 zhonglv_closure() 获取结果\n2. 读取 Agda 文件中的相关常量声明\n3. 比较并报告一致性\n4. 如果不一致，分析差异来源（整数截断？定义不同？）",
        "verify": [
            {"cmd": "cd /data/work/discrete-mathematics && python3 -c \"exec(open('.reasonix/autoresearch/20260704-043019-builder-spec-silent-compliance-defect-builder-spec-archi/textgrad-opt/check_zhonglv.py').read())\" 2>&1 | grep -c '一致\\|consistent'", "expect": "1"},
        ],
        "anti_patterns": [
            "修改任一原有文件来'修复'不一致",
            "不读 Agda 文件就声称一致",
        ],
    },

    {
        "id": "create_ci_check_script",
        "source": "项目根目录",
        "difficulty": "medium",
        "category": "shell",
        "fable5_principles": [1, 5, 9],
        "context": """
项目需要 CI 脚本验证:
1. agda src/Sovereign/All.agda 通过（0错误）
2. python3 -m pytest engineering/tests/ -v 全部通过
3. 无浮点违规: ! grep -r 'float' engineering/software/sovereign_core/*.py | grep -v 'Fraction'
""",
        "instruction": "写一个 ci_check.sh 脚本放在项目根目录。依次运行三个检查，任何一个失败则脚本退出码非零。输出清晰标注每步通过/失败。",
        "verify": [
            {"cmd": "cd /data/work/discrete-mathematics && bash ci_check.sh 2>&1; echo \"EXIT=$?\"", "expect": "exit=0"},
        ],
        "anti_patterns": [
            "跳过任何检查",
            "用 set +e 隐藏失败",
        ],
    },

    # ================================================================
    # 🔴 HARD — Agda postulate消除 (多步,需要深度推理)
    # ================================================================

    {
        "id": "construct_a4_group",
        "source": "src/Sovereign/Coupling/CartanTorsion.agda",
        "difficulty": "hard",
        "category": "agda_postulate",
        "fable5_principles": [1, 2, 3, 5],
        "context": """
CartanTorsion.agda 将 A4 群声明为 postulate:
  postulate A4Group : Set

需要将其替换为具体构造。A4 是 4 个元素的交错群，同构于:
- 四面体的旋转群
- {(), (123), (132), (124), (142), (134), (143), (234), (243), (12)(34), (13)(24), (14)(23)}
- 或模4的加法群 Z/4Z 的某个子群

最简单的方式: 用 Fin 4 上的置换表示，或用 data 类型列举12个元素。
但模块后续需要群公理（结合律/单位元/逆元），所以最简单是:
  A4Group = Z/3Z ⋊ Z/2Z 或直接用置换群表示。

提示: A4 有12个元素。如果太大，可以用更小的群 (如 Z/3Z) 验证方法正确性，
然后在注释中说明扩展到 A4 的方式。
""",
        "instruction": "将 CartanTorsion.agda 中的 postulate A4Group 替换为具体构造。用置换表示或有限集合表示。同时填充模块中的群公理 hole（结合律/单位元/逆元）。完成后 agda 检查该文件。如果 A4 太大，可以先用 Z/3Z 作为简化版本实现完整证明链，留 A4 作为 TODO。",
        "verify": [
            {"cmd": "cd /data/work/discrete-mathematics && agda src/Sovereign/Coupling/CartanTorsion.agda 2>&1 | tail -10", "expect": "exit=0"},
        ],
        "anti_patterns": [
            "保留 postulate A4Group",
            "不填群公理",
        ],
    },

    {
        "id": "prove_entanglement_stateAB",
        "source": "src/Sovereign/Coupling/Entanglement.agda",
        "difficulty": "hard",
        "category": "agda_hole",
        "fable5_principles": [1, 3, 5],
        "context": """
Entanglement.agda 定义了 standardEntangledPair 记录，但 stateA 和 stateB 字段是 hole。
需要根据模块的 CRT 调和定义，构造这两个纠缠态的具体值。

模块背景:
- 纠缠对基于 CRT 双振子系统 (65536, 177147)
- stateA/B 应该是满足特定相位关系的 CRT 投影对
- 可以参考 CRT 模块中的具体数值: X₀=5148246160 等
""",
        "instruction": "填充 Entanglement.agda 中 standardEntangledPair 的 stateA 和 stateB 字段。先读模块理解纠缠态的定义规范，再读 CRT 相关模块找可用的构造值。完成后 agda 检查该文件。",
        "verify": [
            {"cmd": "cd /data/work/discrete-mathematics && agda src/Sovereign/Coupling/Entanglement.agda 2>&1 | tail -5", "expect": "exit=0"},
            {"cmd": "cd /data/work/discrete-mathematics && grep -c '= ?' src/Sovereign/Coupling/Entanglement.agda", "expect": "9"},  # 11→9
        ],
        "anti_patterns": [
            "添加 postulate",
            "填随机值不验证类型",
        ],
    },

    {
        "id": "prove_constitution_basisLock",
        "source": "src/Sovereign/AI/Constitution.agda",
        "difficulty": "hard",
        "category": "agda_postulate",
        "fable5_principles": [1, 2, 3, 5, 8],
        "context": """
AI/Constitution.agda 有 3 个 postulate + 12 个 hole, 其中核心是 basisLock:
对四种基底（连续统实数/二进制浮点/欧氏几何/微积分极限）的锁定证明。

每个 basisLock 是一个不可构造性证明: 
证明该基底在 GF(3) 离散系统中不可表达。

最简单的入口: ContinuumReal — 证明实数不可数（对角线论证），
因此无法用有限 GF(3) 序列表示。
""",
        "instruction": "实现 ContinuumReal 的 basisLock 证明（用对角线论证或其他不可数性论证）。至少完成这一个基底锁定，其他三个留 TODO 注释说明证明策略。完成后 agda 检查 AI/Constitution.agda。",
        "verify": [
            {"cmd": "cd /data/work/discrete-mathematics && agda src/Sovereign/AI/Constitution.agda 2>&1 | tail -5", "expect": "exit=0"},
        ],
        "anti_patterns": [
            "把 postulate 改成另一个 postulate",
            "用循环论证（用待证命题证自己）",
        ],
    },
]

# 难度分布: easy=3, medium=5, hard=3 = 11 tasks
# 类别分布: bugfix=2, refactor=1, agda_hole=3, agda_postulate=2, cross_lang=1, shell=1
# Fable5 覆盖: 原则1(7) 原则2(4) 原则3(4) 原则4(1) 原则5(10) 原则8(2) 原则9(3)
