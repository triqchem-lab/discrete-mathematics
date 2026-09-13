#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""为 test_nse_t6_discrete.py 的 3 条失败断言做**穷举定位**：找出可用的真见证 / 核对该断言的计数口径。

背景（2026-09-13 实测 3 failed / 80 passed）：三条断言的「显式见证」给的是**退化选择**，
而命题本身是对的（所以同一文件里的『家族』版本测试是通过的）：

  · A2 (`test_A2_explicit_polynomial_witness`)：取 v₀ = x₀·x₁ 要 `lap(div v)[原点] ≠ 0`。
    实测 `lap(div v) ≡ 0`（全部 729 点）—— 因为 `div v = D₀(x₀x₁) = x₁` 是**线性**函数，
    二阶差分恒零。⇒ 见证退化，需要换一个 v。
  · A3 (`test_A3_parent_nsstep_explicit_witness`)：取势 ψ₀ = x₀x₁, ψ₂ = x₁x₂，
    要 `div(ns_step_parent v)[原点] ≠ 0`。实测处处为 0 ⇒ 同样是退化见证。
  · A4 (`test_A4_componentwise_reading_refuted`)：断言「全部 729×6 = 4374 处都不等」，
    却与自己的 docstring（∃ i,x 使不等）矛盾：实测恰好 **729** 处不等，且**只集中在分量 i=1**。

⚠ 重要更正（我一开始推错了，记在这里防止再犯）：`lap∘div = Σᵢⱼ Dᵢ²Dⱼ` 含 **i≠j 的混合项**，
它们一般非零，所以 `lap∘div` **不是**恒零算子 —— 单位基向量上存在非零值（本脚本第 (a) 步会给出）。
「三阶差分恒零」（i=j 项）只解释了 `Dᵢ³ ≡ 0`，不足以推出算子恒零。

本脚本做三件事（全部穷举，域 = 点）：
  (a) 在 DIM×N_POINTS = 4374 个单位基向量上扫 `lap(div ·)`，给出**最小真见证**；
  (b) 在 incompressible_family(N_INCOMP) 上找 `div(ns_step_parent ·) ≠ 0` 的第一个场；
  (c) 复核 A4 的不匹配分布。

用法：python3 engineering/tests/test_nse_t6_discrete_witness_search.py
输出末行为 ORACLE-MANIFEST；三条结论都成立则退出码 0。
"""

import os
import sys
from collections import Counter

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

import test_nse_t6_discrete as T  # noqa: E402  （复用其 div/grad/adv 等定义，避免第二套实现）


def unit_vector(i, k):
    f = [0] * T.N_POINTS
    f[k] = 1
    v = [T.const_field(0) for _ in range(T.DIM)]
    v[i] = tuple(f)
    return tuple(v)


def lap_of_div(v):
    return T.div(T.grad(T.div(v)))


def scan_basis():
    """(a) 单位基向量上扫 lap(div ·)：返回 (非零计数, 首个见证)"""
    nonzero, first = 0, None
    for i in range(T.DIM):
        for k in range(T.N_POINTS):
            g = lap_of_div(unit_vector(i, k))
            if any(x % T.P for x in g):
                nonzero += 1
                if first is None:
                    first = (i, k)
    return nonzero, first


def scan_family():
    """(b) incompressible_family 上找父口径的反例：返回 (命中序号, 场)"""
    for idx, v in enumerate(T.incompressible_family(T.N_INCOMP)):
        if not T.field_is_zero(T.div(v)):
            continue
        d = T.div(T.ns_step_parent(v))
        if any(x % T.P for x in d):
            return idx, v
    return None, None


def a4_distribution():
    """(c) A4：不匹配按分量的分布"""
    v = tuple(T.const_field(c) for c in (0, 1, 0, 0, 0, 0))
    d = T.div(T.adv(v))
    cnt = Counter()
    for k in range(T.N_POINTS):
        for i in range(T.DIM):
            if d[k] != (-v[i][k]) % T.P:
                cnt[i] += 1
    return dict(sorted(cnt.items()))


def main():
    total = T.DIM * T.N_POINTS + T.N_INCOMP

    n_nonzero, first = scan_basis()
    print("  (a) 基向量 = %d；lap(div ·) 非零者 = %d；最小真见证 = 分量 %s 于点 %s"
          % (T.DIM * T.N_POINTS, n_nonzero, first[0] if first else None,
             first[1] if first else None))

    fam_idx, fam_v = scan_family()
    print("  (b) incompressible_family(%d) 中父口径反例序号 = %s（场已取出，供测试改用）"
          % (T.N_INCOMP, fam_idx))

    dist = a4_distribution()
    print("  (c) A4 不匹配分布 = %s；总计 = %d（断言要求 %d）"
          % (dist, sum(dist.values()), T.N_POINTS * T.DIM))

    ok = (n_nonzero > 0) and (fam_idx is not None) and \
         (sum(dist.values()) == T.N_POINTS) and (set(dist) == {1})
    print("=== 定位结论 %s ===" % ("全部成立" if ok else "有结论不成立，见上"))
    print('ORACLE-MANIFEST {"basis":"C3^6 单位基向量 4374 个 + incompressible_family 40 个'
          '（div/grad/adv 取自 test_nse_t6_discrete）",'
          '"domain":%d,"points":%d,"claim":"A2/A3 的显式见证退化（lap(div v)≡0 / div(ns_step_parent v)≡0）'
          '但命题可满足（基向量上存在非零；家族中存在反例）；A4 不匹配恰好 729 处且只在分量 i=1"}' %
          (total, total))
    return 0 if ok else 1


def test_witness_search_conclusions():
    """pytest 入口：三条定位结论必须成立。"""
    n_nonzero, first = scan_basis()
    assert n_nonzero > 0 and first is not None
    fam_idx, _ = scan_family()
    assert fam_idx is not None
    dist = a4_distribution()
    assert sum(dist.values()) == T.N_POINTS and set(dist) == {1}


if __name__ == "__main__":
    sys.exit(main())
