## list_sessions 工具对 V5 events 格式会话报告 turns=0

### 问题

AI 调用的 `list_sessions` 工具（`internal/tool/sessiontool/sessiontool.go`）对采用 V5 events 存储格式的会话（`.jsonl` 为 0 字节，实际数据在 `.events.jsonl` 中）报告 `turns=0`。

**实际表现：**
- 会话 `.meta` 记录 8 turns，`.events.jsonl` 有 115KB 数据，但 `list_sessions` 返回 0 turns
- 用户看到会话列表标记为"空"，无法通过 `read_session` 恢复

### 根因

`internal/tool/sessiontool/sessiontool.go:58`：

```go
ordered, err := agent.ListSessionOrder(t.sessionDir)  // ✅ 已从 .meta sidecar 读到 turns/preview
...
preview, turns := agent.SessionPreview(s.Path)         // ❌ 丢弃 sidecar，重新解码
```

**调用链：**
1. `ListSessionOrder` 通过 `LoadBranchMeta` 正确读了 `.meta` 的 `Turns`
2. 第 58 行忽略 sidecar 值，调 `SessionPreview` → `previewSession` → `loadSessionMessages`
3. 当 `.events.jsonl` probe 失败或未识别为 native → 回退到 `loadSessionMessagesFromJSONL` → 读 0 字节 `.jsonl` → 空消息 → turns=0
4. 就算 probe 成功，这也是对每个会话重复解码，纯浪费

### 复现

1. 用 Reasonix CLI 或桌面版创建 V5 events 格式会话（`.jsonl` 空，数据全在 `.events.jsonl`）
2. 桌面版调用 `list_sessions` 工具
3. 该会话 turns 列显示 0

### 修复

**推荐**：直接用 `agent.ListSessions(dir)`。它正确处理 sidecar 缓存（`SchemaVersion >= 1` 时 O(1)），并回填旧格式：

```diff
- ordered, err := agent.ListSessionOrder(t.sessionDir)
+ sessions, err := agent.ListSessions(t.sessionDir)
```

**或者**：复用 `ListSessionOrder` 已加载的 sidecar 数据：

```diff
- preview, turns := agent.SessionPreview(s.Path)
+ preview, turns := s.Preview, s.Turns
```

### 环境

- 桌面版 v1.17.x（main-v2 @ 07c65c22）
- V5 events 存储格式
