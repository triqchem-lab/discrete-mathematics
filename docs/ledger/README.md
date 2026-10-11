# docs/ledger/ —— 命题级台账（人类可读镜像）

每个顶层定理一条 YAML。**机器权威 = `proof_dag` 台账**（回执哈希绑定源码），
本目录是人类镜像：`id` 与 proof_dag 节点 id 同名对齐；冲突以 proof_dag 为准。

## Schema

```yaml
id: <proof_dag 节点 id>            # 必填，同名对齐
module: Sovereign.X.Y              # Agda 模块全名
statement: <命题原文，可直接变签名>   # 必填
level: A | B | C                   # A=proven（唯一计数）/ B=verified / C=declared
evidence:
  compile_receipt: <proof_compile 回执 id>   # A 级必填；无则不判 A
  oracle: <脚本>（回执 id，domain/points）
  cross_check: <具体点 refl 交叉 / 双路径 / 数学推导>
dependencies: [<上游节点 id>…]
proof_strategy: <策略名组合，见 docs/principles.md §一>
human_notes: |
  数学背景、诚实边界、踩坑沉淀
git_witness: <见证链摘要>
updated: YYYY-MM-DD
```

## 规则

1. **A 级四要件**（缺一降 B）：0 postulate + 0 hole + 具体证明体 + 内核回执（+ 核心定理名入账）；
2. **有界实例不证明泛化**——statement 含 ∀ 而证据是抽样 ⇒ `incomplete`，不判 A；
3. 改源码 ⇒ 回执失效 ⇒ 该条目降 B 并更新 `updated`；
4. `engineering/audit_content_grades.sh` 是静态初筛（B/C 启发式），**判 A 必须回执 + 人工四问验收**（SKILL.md L0）。
