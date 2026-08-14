#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
N 序列第一性推导探索（2026-08-14, leo: "我需试试推导"）

目标: 从框架内部推出胶球质量谱 m_G = √N·M₀ 的 N 序列, 而非拟合。
  三方向诠释 N={3,6,7} (0++/2++/0-+), 两胶子诠释 N={2,4,5}

★ 新线索: 三维各向同性谐振子能级简并度
    d(n) = (n+1)(n+2)/2 = 1, 3, 6, 10, 15, 21, ...
    N={3,6} 精确落在 n=1,2 简并度上 (0++→3, 2++→6)!
    0-+→7 = d(3) − 3 = 10 − 3 (n=3 去掉与 0++ 共享的 n=1 对称性模式)?

物理图像: 胶球 = 空间三方向流动的约束量子
  空间三方向 (平面 + 法向量) 各自是谐振子方向,
  胶球 = 三个方向流动扰动的驻波组合, 质量² ∝ 模式数 × M₀²
  M₀ = ℏω₀/c² (ω₀ = 流动扰动最低驻波频率, 空间性质)

对照: 二维谐振子 d(n) = n+1 = 1,2,3,4,5 (两胶子诠释 N={2,4,5})
  N=2→n=1, N=4→n=3, N=5→n=4: 无干净对齐 (缺 n=2→3) ⟹ 若此线索成立,
  三方向诠释 A 获得独立于格点数据的结构支持

格点数据: 0++=1.71±0.05, 2++=2.40±0.12, 0-+=2.56±0.15 GeV (M₀=0.987 GeV)
"""
import math

print("=" * 72)
print("N 序列第一性推导探索: 胶球 = 空间流动的约束量子")
print("=" * 72)

# 1. 各向同性谐振子简并度 (d 维)
def degeneracy_iso(dim, n):
    """d 维各向同性谐振子第 n 能级简并度 = C(n+d-1, d-1)"""
    return math.comb(n + dim - 1, dim - 1)

print("\n[1] 谐振子简并度")
print("    n :  0   1   2   3   4   5")
for dim, label in [(2, "二维(两胶子)"), (3, "三维(三方向)")]:
    ds = [degeneracy_iso(dim, n) for n in range(6)]
    print(f"    {label}: {ds}")

# 2. N 序列映射
print("\n[2] 格点映射")
lattice = {"0++": (1.71, 0.05), "2++": (2.40, 0.12), "0-+": (2.56, 0.15)}
M0 = 0.987  # GeV, 从 0++=√3·M₀ 拟合

print("\n    ★ 三维谐振子诠释 A: N = d_3(n) 或 d_3(n)−d_3(1)")
mapping_A = {"0++": (3, "d(1)=3, n=1 第一激发(基态禁闭排除)"),
             "2++": (6, "d(2)=6, n=2"),
             "0-+": (7, "d(3)−d(1)=10−3, n=3 去 n=1 对称性模式")}
for state, (N, rule) in mapping_A.items():
    m, err = lattice[state]
    pred = math.sqrt(N) * M0
    dev = (pred - m) / err
    print(f"    {state}: N={N} ({rule})")
    print(f"        m_pred = √{N}·{M0} = {pred:.3f} GeV vs 格点 {m}±{err}  (偏差 {dev:+.2f}σ)")

print("\n    ★ 二维谐振子诠释 B: N = d_2(n)")
mapping_B = {"0++": (2, "d(1)=2, n=1"), "2++": (4, "d(3)=4, n=3"),
             "0-+": (5, "d(4)=5, n=4")}
for state, (N, rule) in mapping_B.items():
    m, err = lattice[state]
    pred = math.sqrt(N) * M0
    dev = (pred - m) / err
    print(f"    {state}: N={N} ({rule})")
    print(f"        m_pred = √{N}·{M0} = {pred:.3f} GeV vs 格点 {m}±{err}  (偏差 {dev:+.2f}σ)")

# 3. 预测未观测态 (可证伪预言!)
print("\n[3] 三维诠释 A 的后续预言 (n=4,5,6)")
print("    d(4)=15 → 15·M₀², m = √15·0.987 = %.3f GeV" % (math.sqrt(15) * M0))
print("    d(5)=21 → 21·M₀², m = √21·0.987 = %.3f GeV" % (math.sqrt(21) * M0))
print("    d(6)=28 → 28·M₀², m = √28·0.987 = %.3f GeV" % (math.sqrt(28) * M0))
print("    (若 0-+ 规则 d(n)−d(1) 成立: n=4 → 15−3=12 → √12·0.987 = %.3f GeV)" % (math.sqrt(12) * M0))

# 4. M₀ 的物理解释 (第一性形式的候选)
print("\n[4] M₀ 的第一性形式候选")
print("    M₀ = ℏω₀/c², ω₀ = 空间流动扰动的最低驻波频率")
print("    r₀ = ℏ/(M₀c) = 0.200 fm = 胶球康普顿波长")
print("    驻波条件: ω₀ = πc/L, L = 2·r₀?  ⟹ M₀ = πℏ/(Lc) = π·M₀/2 ⟹ 不自洽")
print("    (L 仍是自由参数——M₀ 的数值来源未闭合, 需要禁闭尺度输入)")

# 5. 统计对比 (A vs B 的加权偏差, 非拟合通道)
print("\n[5] 加权偏差对比 (2++ 和 0-+ 为非拟合通道, 0++ 用于定 M₀)")
def weighted_sigma(states, mapping):
    s = 0.0
    for state, (N, _) in mapping.items():
        if state == "0++":
            continue  # 拟合通道
        m, err = lattice[state]
        pred = math.sqrt(N) * M0
        s += ((pred - m) / err) ** 2
    return math.sqrt(s / 2)

sigA = weighted_sigma(lattice, mapping_A)
sigB = weighted_sigma(lattice, mapping_B)
print(f"    诠释 A (三维, N=3,6,7): 加权 σ = {sigA:.3f}")
print(f"    诠释 B (二维, N=2,4,5): 加权 σ = {sigB:.3f}")
print(f"    → {'A 优于 B' if sigA < sigB else 'B 优于 A'} (差 {abs(sigA-sigB):.2f}σ)")

print("\n[结论 (诚实)]")
print("  1. 三维谐振子简并度 d(n)=(n+1)(n+2)/2 = 1,3,6,10,... 与 N={3,6} 精确对齐")
print("     (n=1,2)——这是独立于格点数据的模式计数规则, 非拟合")
print("  2. 0-+→7 = d(3)−d(1) 是 ad-hoc 规则 (10−3), 需要对称性论证才成立")
print("  3. 二维谐振子 N={2,4,5} 无干净对齐 ⟹ 三方向诠释获结构支持")
print("  4. M₀ 数值来源未闭合 (ω₀/L 自由参数), 需禁闭尺度输入")
print("  5. 可证伪预言: n=4,5,6 模式 → √15/√21/√28·M₀ 质量 (格点未来数据可检验)")
