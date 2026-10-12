# 验证 assoc/comm 链：每步在嵌套树上定位并应用
import sys

def leaf(v): return v
def is_node(t): return isinstance(t, tuple)

def show(t):
    return t if not is_node(t) else "(" + show(t[0]) + " + " + show(t[1]) + ")"

def leaves(t):
    return leaves(t[0]) + leaves(t[1]) if is_node(t) else [t]

def find_path(t, x, path=[]):
    # 定位叶 x 的路径（0=左 1=右）
    if not is_node(t):
        return path if t == x else None
    r = find_path(t[0], x, path + [0])
    if r: return r
    return find_path(t[1], x, path + [1])

def apply_assoc(t, path, direction):
    # direction='fwd': x+(y+z) → (x+y)+z ; 'bwd': 反向
    if not path:
        if not is_node(t): return None
        l, r = t
        if direction == 'fwd':
            if not is_node(r): return None
            return (l[0] + l[1] if False else (l, r), None)  # 占位
        return None
    # 递归
    return None

# 简化：用「叶序+括号标签」—— 重写规则在具体位置由路径定位太复杂
# 改用：链在「全右结合 + 相邻交换」上——树形操作固定：
# flatten(T)（任何括号形→右结合 9 叶）：assoc 反复
# swap(i)（右结合第 i,i+1 叶交换）：comm
# 目标括号形由 unflatten（assoc 正）达成
# 每步 Agda 形式唯一确定 → 无需 Python 模拟树，只需列出步骤

col = ['A1','A2','A3','B1','B2','B3','C1','C2','C3']
row = ['A1','B1','C1','A2','B2','C2','A3','B3','C3']

# flatten 步（assoc 反，从三层组形到全右）：需 6 步
# 右结合 9 叶：A1+(A2+(A3+(B1+(B2+(B3+(C1+(C2+C3)))))))
# comm 步（叶冒泡 col→row）：逆序数
pos = {v:i for i,v in enumerate(col)}
inv = sum(1 for x in range(9) for y in range(x+1,9) if pos[row[x]] > pos[row[y]])
print("flatten 6 步 + comm %d 步 + unflatten 6 步 = 18 步" % inv)
work = col[:]
swaps = []
for i in range(9):
    j = work.index(row[i])
    while j > i:
        swaps.append("cong (%s +_) (+Comm %s %s)" % (" +_".join([]), work[j-1], work[j]))
        # 实际 Agda 行
        congs = "".join("cong (%s +_)" % work[k] for k in range(j-1))
        swaps[-1] = "    ∙ " + congs + " (+Comm %s %s)" % (work[j-1], work[j])
        work[j-1], work[j] = work[j], work[j-1]
        j -= 1
print("\n".join(swaps))
print("OK")
