# sum3-comm：col 序 [00,01,02,10,11,12,20,21,22] → row 序 [00,10,20,01,11,21,02,12,22]
col = ['f00','f01','f02','f10','f11','f12','f20','f21','f22']
row = ['f00','f10','f20','f01','f11','f21','f02','f12','f22']
work = col[:]
swaps = []
for i in range(9):
    if work[i] == row[i]:
        continue
    j = work.index(row[i])
    while j > i:
        swaps.append((work[j-1], work[j]))
        work[j-1], work[j] = work[j], work[j-1]
        j -= 1
print("逆序数 =", len(swaps))
for a, b in swaps:
    print("+Comm %s %s" % (a, b))
assert work == row
print("OK")
