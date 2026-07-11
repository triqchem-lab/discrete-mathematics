"""
Reasonix 系统提示词评估任务集 v2

设计原则（借鉴 scholar-loop + Fable5-Thinking-Skill）:

scholar-loop 借鉴:
  - frozen metric: 评分标准在任务运行前冻结，不可事后修改
  - 多级漏斗: 每个任务有 smoke(快速检查) → verify(行为验证) → full(完整评测)
  - predict-then-verify: agent 的声明必须可被独立验证

Fable5 九原则 → 评测维度:
  1. 自主任务分解 → 复杂任务需要分步执行
  2. 拓扑扫描     → 改文件前检查了依赖关系
  3. 多路径推演   → 有方案对比（对复杂决策）
  4. 自我验证     → 写完代码后自己审查
  5. 沙盒验证     → 实际运行测试
  6. 分级路由     → 合理使用子代理
  7. 持久记忆     → 关键决策有记录
  8. 对抗性自检   → 从审稿人角度检查
  9. 防虚假完成   → 每个声明附带证据

每个任务的结构:
  {
    "id": "唯一标识",
    "category": "file_ops|shell|refactor|debug|multi_file|project",
    "fable5_principles": [涉及的Fable5原则编号],
    "difficulty": "easy|medium|hard",
    "turns_expected": 预期轮数,
    "setup": "前置准备（创建文件/目录结构）",
    "instruction": "自然语言任务描述",
    "verify_steps": [
      {"action": "shell命令或文件检查", "expected": "预期结果"}
    ],
    "anti_patterns": ["禁止的行为"],
    "score_rubric": {
      "correctness": 权重,
      "efficiency": 权重,
      "safety": 权重,
      "evidence": 权重  # Fable5 原则9: 是否有可验证证据
    }
  }
"""

EVAL_TASKS_V2 = [
    # ============================================================
    # 文件操作类 (Fable5: 原则1自主分解, 原则5沙盒验证)
    # ============================================================
    {
        "id": "file_read_error_handling",
        "category": "file_ops",
        "fable5_principles": [1, 5, 9],
        "difficulty": "easy",
        "turns_expected": 2,
        "setup": "echo 'hello' > /tmp/test_read.txt && chmod 000 /tmp/test_read.txt",
        "instruction": "读取 /tmp/test_read.txt 的内容。如果失败，给出包含文件名的清晰错误信息。",
        "verify_steps": [
            {"action": "检查输出是否包含文件路径 /tmp/test_read.txt", "expected": "true"},
            {"action": "检查输出是否说明了失败原因", "expected": "true"},
        ],
        "anti_patterns": [
            "没有错误处理直接崩溃",
            "错误信息不含文件名",
        ],
    },
    {
        "id": "multi_file_rename",
        "category": "multi_file",
        "fable5_principles": [1, 2, 5],
        "difficulty": "medium",
        "turns_expected": 3,
        "setup": "mkdir -p /tmp/rename_test && for i in 1 2 3; do echo 'data' > /tmp/rename_test/old_$i.txt; done",
        "instruction": "将 /tmp/rename_test/ 下所有 old_*.txt 文件重命名为 new_*.txt（保持编号不变）。先列出将要改的文件，确认后再执行。",
        "verify_steps": [
            {"action": "ls /tmp/rename_test/new_*.txt | wc -l", "expected": "3"},
            {"action": "ls /tmp/rename_test/old_*.txt 2>&1 | grep 'No such file'", "expected": "true"},
        ],
        "anti_patterns": [
            "没有先列出文件就直接操作",
            "使用了删除命令",
        ],
    },

    # ============================================================
    # Shell 命令类 (Fable5: 原则5沙盒验证, 原则9防虚假完成)
    # ============================================================
    {
        "id": "shell_pipeline_debug",
        "category": "shell",
        "fable5_principles": [5, 9],
        "difficulty": "medium",
        "turns_expected": 2,
        "setup": "echo 'app' > /tmp/app.log && echo 'error: disk full' >> /tmp/app.log && echo 'info: started' >> /tmp/app.log",
        "instruction": "从 /tmp/app.log 中找出所有包含 'error' 的行，统计行数，然后打印这些行。用一行 shell 管道完成。",
        "verify_steps": [
            {"action": "检查输出包含行数", "expected": "true"},
            {"action": "检查输出包含 'error: disk full'", "expected": "true"},
        ],
        "anti_patterns": [
            "用了 Python 而不是 shell",
            "没有验证就声称完成",
        ],
    },
    {
        "id": "disk_space_check",
        "category": "shell",
        "fable5_principles": [1, 9],
        "difficulty": "easy",
        "turns_expected": 1,
        "setup": "",
        "instruction": "检查当前目录所在分区的磁盘使用情况。用人类可读的格式输出已用/总量/使用率。",
        "verify_steps": [
            {"action": "检查输出包含百分比", "expected": "true"},
            {"action": "检查输出包含人类可读的大小（如 G/M）", "expected": "true"},
        ],
        "anti_patterns": [
            "输出原始字节数不转换",
        ],
    },

    # ============================================================
    # 代码重构类 (Fable5: 原则2拓扑扫描, 原则4自我验证)
    # ============================================================
    {
        "id": "refactor_extract_function",
        "category": "refactor",
        "fable5_principles": [1, 2, 4, 5],
        "difficulty": "medium",
        "turns_expected": 4,
        "setup": """
cat > /tmp/refactor_me.py << 'EOF'
def process_orders(orders):
    total = 0
    for order in orders:
        if order.get('status') == 'paid':
            tax = order['amount'] * 0.08
            total += order['amount'] + tax
    # duplicated logic below
    for order in orders:
        if order.get('status') == 'paid':
            print(f"Order {order['id']}: ${order['amount'] + order['amount'] * 0.08}")
    return total
EOF
""",
        "instruction": "/tmp/refactor_me.py 中有重复的税费计算逻辑。提取公共函数，消除重复，但保持行为完全不变。重构后运行一下验证。",
        "verify_steps": [
            {"action": "python3 -c \"from refactor_me import process_orders; assert process_orders([{'id':1,'amount':100,'status':'paid'}]) == process_orders([{'id':1,'amount':100,'status':'paid'}])\" 2>&1 | head -1", "expected": ""},
            {"action": "grep -c '0.08' /tmp/refactor_me.py", "expected": "1"},
        ],
        "anti_patterns": [
            "改变了函数行为",
            "没有验证重构后的正确性",
            "删除而非提取",
        ],
    },
    {
        "id": "add_error_handling",
        "category": "refactor",
        "fable5_principles": [2, 4, 5],
        "difficulty": "medium",
        "turns_expected": 3,
        "setup": """
cat > /tmp/fragile.py << 'EOF'
import json
def load_config(path):
    with open(path) as f:
        return json.load(f)
EOF
""",
        "instruction": "/tmp/fragile.py 的 load_config 可能在文件不存在、权限不足、JSON 格式错误时崩溃。添加显式错误处理：每种错误给出不同的清晰错误信息。不要改变正常路径的行为。",
        "verify_steps": [
            {"action": "grep -c 'try' /tmp/fragile.py", "expected": "1"},
            {"action": "grep -c 'except' /tmp/fragile.py", "expected": "3"},
            {"action": "grep -c 'FileNotFoundError\\|PermissionError\\|JSONDecodeError' /tmp/fragile.py", "expected": "3"},
        ],
        "anti_patterns": [
            "使用裸 except:",
            "改变了正常路径行为",
        ],
    },

    # ============================================================
    # Bug 修复类 (Fable5: 原则1分解, 原则5沙盒验证, 原则9证据)
    # ============================================================
    {
        "id": "debug_off_by_one",
        "category": "debug",
        "fable5_principles": [1, 5, 9],
        "difficulty": "medium",
        "turns_expected": 3,
        "setup": """
cat > /tmp/buggy.py << 'EOF'
def binary_search(arr, target):
    left, right = 0, len(arr)
    while left < right:
        mid = (left + right) // 2
        if arr[mid] == target:
            return mid
        elif arr[mid] < target:
            left = mid + 1
        else:
            right = mid
    return -1
EOF
""",
        "instruction": "/tmp/buggy.py 中的 binary_search 有一个越界 bug。找出 bug，修复它，并写一个测试验证修复。不要重写整个函数——只修 bug。",
        "verify_steps": [
            {"action": "python3 -c \"from buggy import binary_search; assert binary_search([1,2,3], 3) == 2; assert binary_search([1], 1) == 0; assert binary_search([], 1) == -1; print('OK')\" 2>&1", "expected": "OK"},
        ],
        "anti_patterns": [
            "重写整个函数而非修复",
            "没有测试验证",
        ],
    },

    # ============================================================
    # 项目级操作 (Fable5: 原则1分解, 原则2拓扑扫描, 原则3多路径推演)
    # ============================================================
    {
        "id": "project_add_module",
        "category": "project",
        "fable5_principles": [1, 2, 3, 5],
        "difficulty": "hard",
        "turns_expected": 5,
        "setup": """
mkdir -p /tmp/myproject/src /tmp/myproject/tests
cat > /tmp/myproject/src/__init__.py << 'EOF'
from .math_utils import add, multiply
EOF
cat > /tmp/myproject/src/math_utils.py << 'EOF'
def add(a, b):
    return a + b
def multiply(a, b):
    return a * b
EOF
cat > /tmp/myproject/tests/test_math.py << 'EOF'
from src.math_utils import add, multiply
def test_add():
    assert add(2, 3) == 5
def test_multiply():
    assert multiply(2, 3) == 6
EOF
""",
        "instruction": "在 /tmp/myproject/src/ 下新增一个 string_utils.py 模块，包含一个函数 capitalize_words(s: str) -> str: 将字符串中每个单词的首字母大写。更新 __init__.py 导出这个函数。在 tests/ 下加对应的测试。最后运行所有已有测试确保没有回归。",
        "verify_steps": [
            {"action": "python3 -c \"from src.string_utils import capitalize_words; assert capitalize_words('hello world') == 'Hello World'; print('OK')\"", "expected": "OK"},
            {"action": "grep 'capitalize_words' /tmp/myproject/src/__init__.py", "expected": "true"},
            {"action": "ls /tmp/myproject/tests/test_string*.py", "expected": "true"},
        ],
        "anti_patterns": [
            "没有更新 __init__.py",
            "没有加测试",
            "破坏了已有测试",
        ],
    },

    # ============================================================
    # 约束遵守类 (Fable5: 原则8对抗性自检)
    # ============================================================
    {
        "id": "no_float_constraint",
        "category": "refactor",
        "fable5_principles": [4, 8],
        "difficulty": "easy",
        "turns_expected": 2,
        "setup": """
cat > /tmp/price_calc.py << 'EOF'
def apply_discount(price, percent):
    return price * (1 - percent / 100.0)
EOF
""",
        "instruction": "/tmp/price_calc.py 使用了浮点数计算价格。改用定点数（整数，单位：分）重写这个函数，确保精确计算。",
        "verify_steps": [
            {"action": "python3 -c \"from price_calc import apply_discount; r = apply_discount(10000, 15); assert isinstance(r, int); assert r == 8500; print('OK')\"", "expected": "OK"},
            {"action": "grep -c 'float\\|\\.0' /tmp/price_calc.py", "expected": "0"},
        ],
        "anti_patterns": [
            "仍然使用浮点数",
            "结果不精确",
        ],
    },
]
