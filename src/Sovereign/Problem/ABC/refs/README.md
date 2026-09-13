# ABC / IUTT 参考文献溯源记录

**获取日期**: 2026-09-13
**来源**: 望月新一 RIMS 主页（唯一权威出处）— <https://www.kurims.kyoto-u.ac.jp/~motizuki/papers-english.html>
**用途**: `Sovereign.Problem.ABC` 的文献依据。**目录内的 PDF 不入库**（见 `.gitignore`），
本文件入库，记录"取了什么、从哪取、校验和是多少"。

---

## 一、文件清单（6 份 / 858 页 / 5.6 MB）

| 本地文件 | 页 | PDF 内首页标题 | PDF 内部日期 | 字节 | sha256 |
|---|---|---|---|---|---|
| `IUTT-I.pdf` | 186 | INTER-UNIVERSAL TEICHMÜLLER THEORY I: CONSTRUCTION OF HODGE THEATERS | May 2020 | 1280589 | `7360e3ed27c235b5497a0743d3ed1646fbb97688547d16b7c784fc7f127f1f03` |
| `IUTT-II.pdf` | 174 | INTER-UNIVERSAL TEICHMÜLLER THEORY II: HODGE-ARAKELOV-THEORETIC EVALUATION | December 2020 | 1203855 | `180bfa6aaddc4ae37af37acaad51f61e0a47b33b8255ad3169e28a970ae39b7c` |
| `IUTT-III.pdf` | 199 | INTER-UNIVERSAL TEICHMÜLLER THEORY III: CANONICAL SPLITTINGS OF THE LOG-THETA-LATTICE | May 2020 | 1307865 | `9a7ee3c77b1c7717210c0613eb39b6844649d0040dc3d9e1be7d544f8f91a0b9` |
| `IUTT-IV.pdf` | 87 | INTER-UNIVERSAL TEICHMÜLLER THEORY IV: LOG-VOLUME COMPUTATIONS AND SET-THEORETIC FOUNDATIONS | April 2020 | 632447 | `5bf4b1e0a8c2686562a6859e5009d301335044cfb5efec5d3a9edf764e4af87f` |
| `Panoramic-Overview.pdf` | 45 | A Panoramic Overview of Inter-universal Teichmüller Theory | 2013-08 | 372426 | `eb42575f73d69d1f28e949eb9e52593dd17d1b85c15cc8b44fdfd12ae86b708b` |
| `Essential-Logical-Structure.pdf` | 167 | ON THE ESSENTIAL LOGICAL STRUCTURE OF IUTT IN TERMS OF LOGICAL AND "∧"/LOGICAL OR "∨" RELATIONS: REPORT ON THE OCCASION OF THE PUBLICATION OF THE FOUR MAIN PAPERS ON IUTT | March 2024 | 1021306 | `c0e63b629aa174aa065e93d08defe3e5d0837c8778aab527383798baf8ca6e32` |

⚠️ **命名勘误**：这四篇论文常被称为「2012 年四篇」（PRIMS 2021 第 4 期正式发表），
但 RIMS 主页当前提供的 PDF **内部日期是 2020 年**（5 月 / 12 月），即**修订版**。
本地文件名用 `IUTT-I…IV`（不带年份），年份以本表为准——不要凭文件名推断版本。

## 二、复现下载

```sh
mkdir -p src/Sovereign/Problem/ABC/refs && cd src/Sovereign/Problem/ABC/refs
B="https://www.kurims.kyoto-u.ac.jp/~motizuki"
curl -sSL --fail -O "$B/Inter-universal%20Teichmuller%20Theory%20I.pdf"
# … II / III / IV 同式；另两份为
#   Panoramic%20Overview%20of%20Inter-universal%20Teichmuller%20Theory.pdf
#   Essential%20Logical%20Structure%20of%20Inter-universal%20Teichmuller%20Theory.pdf
sha256sum -c <(sed -n 's/^| `\(.*\)` |.*| `\([0-9a-f]\{64\}\)` |$/\2  \1/p' README.md)
```

## 三、为什么 PDF 不入库

- 体积：这 6 份 5.6 MB；`.git` 目前 24 MB，直接入库会明显膨胀，且 PDF 是**二进制不可 diff** 资产。
- 来源与授权：论文在作者主页公开可下载，但**再分发**（放入公开仓库）与"个人参考下载"是两回事。
  本目录只保留**溯源记录 + 复现命令**，任何人可自行按上表校验取到同一份。
- 若确需入库，请先确认授权口径，再从 `.gitignore` 里去掉这一行：
  `src/Sovereign/Problem/ABC/refs/*.pdf`

## 四、与本文献相关的**已核实**事实（供诊断文档引用）

| 事实 | 依据 |
|---|---|
| abc 猜想 = Oesterlé–Masser 猜想，1985；与**修正 Szpiro 猜想**等价 | 维基百科 *abc conjecture*（conjectured by / Equivalent to） |
| 质量 `q(a,b,c) = log c / log rad(abc)`；`q(4,127,131) = 0.46820…`，`q(3,125,128) = 1.426565…` | 同上（Examples / Formulations） |
| **已知**：`q > 1` 的三元组有**无穷多**；猜想断言 `q > 1+ε` 只有有限多 | 同上 |
| 望月 2012 年声称证明；**主流数学界仍视为未证明** | 同上（Claimed proofs，引 Ball / Nature 2020） |
| Scholze–Stix 的反驳意见《Why abc is still a conjecture》 | <https://www.semanticscholar.org/paper/0253b621d24779fad66e6c24312138bcc509f9da> |
| abc ⟹ Fermat 大定理、Fermat–Catalan、Beal、Roth、Tijdeman、Erdős–Ulam | 维基百科（Consequences） |

> 本表只记录**能指到来源**的事实。凡涉及"某证明对/错"的**判断**，一律标注为**争议未决**，
> 本目录不代替数学界下结论。

---

*相关*: [../README.md](../README.md)（`Sovereign.Problem.ABC` 研究索引）
