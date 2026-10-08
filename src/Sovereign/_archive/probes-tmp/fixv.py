p='src/Sovereign/Cubical/Fin3.agda'
s=open(p).read()
fixes = [
("cong (v1 +_) (cong (v2 +_) (+Comm A3 B1))", "cong (A1 +_) (cong (A2 +_) (+Comm A3 B1))"),
("cong (v1 +_) (+Comm A2 B1)", "cong (A1 +_) (+Comm A2 B1)"),
("cong (v1 +_) (cong (v2 +_) (cong (v3 +_) (cong (v4 +_) (cong (v5 +_) (+Comm B3 C1))))))",
 "cong (A1 +_) (cong (A2 +_) (cong (B1 +_) (cong (A3 +_) (cong (B2 +_) (+Comm B3 C1))))))"),
("cong (v1 +_) (cong (v2 +_) (cong (v3 +_) (cong (v4 +_) (+Comm B2 C1)))))",
 "cong (A1 +_) (cong (A2 +_) (cong (B1 +_) (cong (A3 +_) (+Comm B2 C1)))))"),
("cong (v1 +_) (cong (v2 +_) (cong (v3 +_) (+Comm A3 C1))))",
 "cong (A1 +_) (cong (A2 +_) (cong (B1 +_) (+Comm A3 C1))))"),
("cong (v1 +_) (cong (v2 +_) (+Comm A2 C1)))",
 "cong (A1 +_) (cong (B1 +_) (+Comm A2 C1)))"),
("cong (v1 +_) (cong (v2 +_) (cong (v3 +_) (cong (v4 +_) (+Comm A3 B2)))))",
 "cong (A1 +_) (cong (B1 +_) (cong (C1 +_) (cong (A2 +_) (+Comm A3 B2))))"),
("cong (v1 +_) (cong (v2 +_) (cong (v3 +_) (cong (v4 +_) (cong (v5 +_) (cong (v6 +_) (+Comm B3 C2)))))))",
 "cong (A1 +_) (cong (B1 +_) (cong (C1 +_) (cong (A2 +_) (cong (B2 +_) (cong (A3 +_) (+Comm B3 C2))))))))"),
("cong (v1 +_) (cong (v2 +_) (cong (v3 +_) (cong (v4 +_) (cong (v5 +_) (+Comm A3 C2))))))",
 "cong (A1 +_) (cong (B1 +_) (cong (C1 +_) (cong (A2 +_) (cong (B2 +_) (+Comm A3 C2)))))))"),
]
for old, new in fixes:
    if old in s:
        s = s.replace(old, new)
open(p,'w').write(s)
print('v-names fixed')
