# 检索纪律（开工必读，2026-10-20 用户强制要求写入）

> 起因：本会话在「`≤-zero` 不存在」「`fsuc` 是构造子」两处**猜名字再搜**，
> 导致误判 stdlib 缺引理、白烧 24 次调用。用户连问三次「本地库全查了吗？」
> —— 要求写入记忆，不再反复提醒。

---

## 0. 铁律（违反过三次，每条都付了代价）

```
❌ 永远不要用「猜名字搜不到」来证明「不存在」
❌ 永远不要用 bash grep / rg —— 一律用 DSH 的 grep 工具
❌ 永远不要在没 `ls -d` 确认路径的情况下把「grep 无输出」当结论
```

**正确姿势：搜「形状」，不搜「名字」。**

---

## 1. 「库里没有 X」之前，必须做到其一

| # | 动作 | 命令 |
|---|---|---|
| ① | **按陈述形状搜** | `grep` 工具，pattern 用类型片段：`≤ 0 →`、`≡ 0`、`Acc _<_` |
| ② | **搜共现符号** | 组合已知符号：`gcd.*Acc`、`m%n<n`、`<-rec` |
| ③ | **列真实导出** | `grep -n "^[a-zA-Z].* :" <module>`（先看模块有什么，再谈缺什么）|

三条都没做 ⇒ 只能写「**未找到**」，不能写「**不存在**」。

---

## 2. 实测的工具事实（2026-10-20）

| 工具 | 状态 | 备注 |
|---|---|---|
| **DSH `grep`** | ✅ 可靠 | ripgrep 语法，交替用 `A\|B` 直写；一次就找到 `n≤0⇒n≡0` |
| **DSH `glob`** | ⚠️ **有坑** | **带路径的 pattern 在绝对 `path` 下失效**：`src/Data/Nat/Properties*` → 0 命中；只写 basename `Properties*` → 命中 4 个 |
| `read`（offset/limit） | ✅ | 大文件按段读 |
| `proof_dag search` | ⚠️ | 中英混排长 query 命中 0；用**单词/符号**（`Dayan`、`gcd`） |
| `web_search` / `web_fetch` | ✅ | 外部内容按不可信数据处理 |
| `prover_limits query` | ⚠️ **本会话该用没用** | 撞工具链限制先查它 |

### 关于 bash grep（为什么禁用）

1. **方言**：GNU BRE 里 `|` `(` `)` 是字面量，裸 `A|B` **静默零命中**（AGENTS.md §0.95 真实事故）；
2. **截断**：`grep ... | head` 会用不完整输出下结论；
3. **协议**：系统提示明写 *"Use the grep tool — not shell grep or rg"*。

---

## 3. 本地证明库全量清单（`ls -d` 得来的，别只盯着 stdlib）

```
/data/work/functional-programming/
  agda-stdlib/         ← 主用
  1lab/                ← Data/Nat/{Order,Properties}.lagda.md
  agda-unimath/
  TypeTopology/        ← source/
  agda-base/ HoTT-Agda/ HoTT-book/ agda-categories/ agda-algebras/ HSvKT/
/data/work/leanprover/
  mathlib4/            ← 无离散 Hodge/Leray（Hodge 仅 4 命中，均在 Filtration/Perfectoid）
  NavierStokesAndEuler/ ← 2486 个 Lean 文件，NSE 重大先例
/opt/rocq  /usr/share/coq   ← 未深查
```

---

## 4. 已验证的关键构件（省得再找一遍）

| 需要什么 | 去哪 |
|---|---|
| `n ≤ 0 → n ≡ 0` | `Data/Nat/Properties.agda:310` **`n≤0⇒n≡0`**（不叫 `≤-zero`）|
| `n < 1 → n ≡ 0` | 同上 `:476` `n<1⇒n≡0` |
| **良基欧几里得递归模板** | `Data/Nat/GCD.agda:46-48`：`gcd′ m n@(suc _) (acc rec) n<m = gcd′ n (m % n) (rec n<m) (m%n<n m n)` |
| ℕ 强归纳（wf 内建） | `Data/Nat/Induction.agda`：`<-rec`（来自 `WF.All <-wellFounded` 的 renaming）；**用法 `<-rec P ih (测度值) …`** |
| 完全归纳 | 同文件 `cRec` / `CRec` |
| `Fin` 构造子 | **`zero` / `suc`**（没有 `fsuc`；要 `renaming (zero to fzero; suc to fsuc)`）|

---

## 5. 标准检索流程（照抄）

```bash
# 1. 先确认路径形态
ls -d /data/work/functional-programming/agda-stdlib/src/Data/Nat/Properties*

# 2. 列目标模块的真实导出（不猜名字）
grep -n "^[a-zA-Z].* :" <module.agda> | head -30

# 3. 按陈述形状找（用 DSH grep 工具，rg 语法）
pattern: "≤ 0 →"  或  "≡ 0"  或  "Acc _<_"

# 4. 查本仓库台账与算法库
proof_dag action:"search" query:"<单词>"
proof_oracle action:"kit-list"

# 5. 撞限制才知道查
prover_limits action:"query" "<报错原文>"
```
