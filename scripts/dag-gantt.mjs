#!/usr/bin/env node
// scripts/dag-gantt.mjs —— 台账 → 甘特面（mermaid gantt + 批次表 + 缺口单列）
//
// 纪律依据：`>3 节点课题在报告「六、依赖与优先」与本批收尾必附甘特面`。
// 输出是**投影**，权威永远是台账本身（本脚本只读，不改台账）。
//
// 用法：
//   node scripts/dag-gantt.mjs                 # 默认台账（~/.dsh/state/math-proof/dag-*.json）
//   node scripts/dag-gantt.mjs <ledger.json>   # 指定台账
//   node scripts/dag-gantt.mjs --md            # 附带 markdown 表格
//
// 退出码：0 = 正常；1 = 台账读不到/为空；2 = 用法错误。

import { readFileSync, readdirSync } from "node:fs";
import { homedir } from "node:os";
import { join } from "node:path";

const STATE_ORDER = ["proven", "refuted", "artifact", "abandoned", "blocked", "needs_review", "active", "pending"];
const STATE_LABEL = {
  proven: "已证", refuted: "已否证", artifact: "非命题已完成",
  abandoned: "已放弃", blocked: "阻塞", needs_review: "待复核",
  active: "进行中", pending: "未开工",
};

function findLedger() {
  const dir = join(homedir(), ".dsh", "state", "math-proof");
  try {
    const files = readdirSync(dir).filter((f) => /^dag-.*\.json$/.test(f));
    if (files.length === 0) return null;
    // 同一目录下可能有多个台账（不同会话/子代理各一份）⇒ 取**节点最多**的那份，
    // 并在 stderr 提示，避免默默用了一份只有几个节点的台账。
    let best = null, bestN = -1;
    for (const f of files) {
      try {
        const d = JSON.parse(readFileSync(join(dir, f), "utf8"));
        const n = Object.keys(d.nodes || {}).length;
        if (n > bestN) { bestN = n; best = f; }
      } catch { /* 跳过坏文件 */ }
    }
    if (files.length > 1) {
      console.error(`dag-gantt: 目录下有 ${files.length} 份台账，选用节点最多的一份 (${bestN} 节点)：${best}`);
    }
    return best ? join(dir, best) : null;
  } catch {
    return null;
  }
}

function main(argv) {
  const wantMd = argv.includes("--md");
  const explicit = argv.find((a) => !a.startsWith("--"));
  const path = explicit || findLedger();
  if (!path) {
    console.error("dag-gantt: 找不到台账（~/.dsh/state/math-proof/dag-*.json）");
    return 1;
  }

  let data;
  try {
    data = JSON.parse(readFileSync(path, "utf8"));
  } catch (e) {
    console.error(`dag-gantt: 台账解析失败 ${path}: ${e.message}`);
    return 1;
  }
  const nodes = data.nodes || {};
  const ids = Object.keys(nodes);
  if (ids.length === 0) {
    console.error("dag-gantt: 台账为空");
    return 1;
  }

  const byState = new Map(STATE_ORDER.map((s) => [s, []]));
  for (const id of ids) {
    const st = nodes[id].state || "pending";
    if (!byState.has(st)) byState.set(st, []);
    byState.get(st).push(id);
  }

  const lines = [];
  lines.push(`# 台账甘特面（投影，非权威）`);
  lines.push("");
  lines.push(`- 台账：\`${path}\``);
  lines.push(`- 节点总数：**${ids.length}**`);
  lines.push("");
  lines.push("## 一、mermaid gantt（按状态分段：已定局 → 阻塞 → 未开工）");
  lines.push("");
  lines.push("```mermaid");
  lines.push("gantt");
  lines.push("  dateFormat YYYY-MM-DD");
  lines.push("  axisFormat %m-%d");
  lines.push("  title 证明台账状态分布（宽度按节点数等比，非时间）");
  for (const st of STATE_ORDER) {
    const list = byState.get(st) || [];
    if (list.length === 0) continue;
    lines.push(`  section ${STATE_LABEL[st] || st} (${list.length})`);
    // 每段一个占位任务，长度 = 节点数（相对宽度，表达规模而非日期）
    lines.push(`    段-${st} :done, ${st}, 2026-01-01, ${list.length}d`);
  }
  lines.push("```");
  lines.push("");

  lines.push("## 二、批次表（状态 → 数量 → 占比）");
  lines.push("");
  lines.push("| 状态 | 含义 | 数量 | 占比 |");
  lines.push("| --- | --- | ---: | ---: |");
  for (const st of STATE_ORDER) {
    const list = byState.get(st) || [];
    if (list.length === 0) continue;
    const pct = ((list.length / ids.length) * 100).toFixed(1);
    lines.push(`| \`${st}\` | ${STATE_LABEL[st] || st} | ${list.length} | ${pct}% |`);
  }
  lines.push("");

  // 缺口 = 未完成口径（不含 artifact：它是非命题终态）
  const DONE = new Set(["proven", "refuted", "artifact", "abandoned"]);
  const gaps = ids.filter((id) => !DONE.has(nodes[id].state));
  lines.push(`## 三、缺口（**单列**，共 ${gaps.length} 条）`);
  lines.push("");
  if (gaps.length === 0) {
    lines.push("无 ✅");
  } else {
    lines.push("| id | 状态 | 陈述（截断） |");
    lines.push("| --- | --- | --- |");
    for (const id of gaps.sort()) {
      const n = nodes[id];
      const stmt = (n.statement || "").replace(/\|/g, "\\|").slice(0, 80);
      lines.push(`| \`${id}\` | ${n.state} | ${stmt} |`);
    }
  }
  lines.push("");

  if (wantMd) {
    lines.push("## 四、全部节点（按状态）");
    lines.push("");
    for (const st of STATE_ORDER) {
      const list = byState.get(st) || [];
      if (list.length === 0) continue;
      lines.push(`### ${STATE_LABEL[st] || st}（${list.length}）`);
      for (const id of list.sort()) lines.push(`- \`${id}\``);
      lines.push("");
    }
  }

  process.stdout.write(lines.join("\n") + "\n");
  return 0;
}

process.exit(main(process.argv.slice(2)));
