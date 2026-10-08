# 生成 9 步 comm 的 Agda cong 前缀（跟踪当前树形）
work = ['v1','v2','v3','v4','v5','v6','v7','v8','v9']
target = ['v1','v4','v7','v2','v5','v8','v3','v6','v9']
lines = []
for i in range(9):
    if work[i] == target[i]:
        continue
    j = work.index(target[i])
    while j > i:
        a, b = work[j-1], work[j]
        d = j - 1
        congs = ""
        for k in range(d):
            congs = congs + "cong (" + work[k] + " +_)"
        if d == 0:
            lines.append("    ∙ " + "+Comm " + a + " " + b)
        else:
            lines.append("    ∙ " + congs + " (" + "+Comm " + a + " " + b + ")")
        work[j-1], work[j] = work[j], work[j-1]
        j -= 1
open("/data/tmp/comm_lines.agda","w").write("\n".join(lines))
print("\n".join(lines))
print("（%d 步）" % len(lines))
