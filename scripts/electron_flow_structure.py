#!/usr/bin/env python3
"""电子 = 空间流动结构（探讨演示）：
自旋（涡旋 ∇×C ≠ 0）+ 电荷（源 ∇·C ≠ 0）+ 质量（锚定 MC1）。

结构对应（诚实：2 层类比，非推导）：
  库仑场 E = q r̂/4πε₀r² 与流体点汇 v_r = −q'/(4πr²) 形状相同（1/r²）
  ⟹ 电荷 ↔ 空间流动的源（∇·C ≠ 0）
  自旋 ↔ 空间流动的涡旋（∇×C ≠ 0，环流）
  电子 = 源 + 涡旋 = 空间流动的"龙卷风"（向内吸入 + 旋转）
  光子 = 空间流动的波动（涟漪）；电子 = 局域结构（龙卷风）

自能检查（经典电磁 + 仓库 r₀ 截止）：
  U = e²/(8πε₀r₀)（静电自能），m = U/c²
  r₀ = 0.2 fm（仓库 M₀≈1GeV 尺度）→ U ≈ 3.6 MeV vs m_e = 0.511 MeV
  r₀ = r_e = 2.82 fm（经典电子半径）→ U ≈ 0.26 MeV vs m_e（经典 4/3 因子问题）
  ——数量级相近但因子不干净（经典电磁自能模型的已知困难）
"""
import json
import os

import numpy as np
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
import matplotlib.font_manager as fm

for _fp in ("/System/Library/Fonts/PingFang.ttc",
            "/System/Library/Fonts/Hiragino Sans GB.ttc"):
    if os.path.exists(_fp):
        fm.fontManager.addfont(_fp)
        plt.rcParams["font.sans-serif"] = [fm.FontProperties(fname=_fp).get_name()]
        break
plt.rcParams["axes.unicode_minus"] = False

OUT = os.path.join(os.path.dirname(__file__), "..", "artifacts", "electron")
os.makedirs(OUT, exist_ok=True)

# 物理常数（MeV·fm 单位制）
ALPHA = 1 / 137.036
HBARC = 197.326  # MeV·fm
ME = 0.511       # MeV
M0 = 987.0       # 仓库胶球拟合尺度 MeV（≈1 GeV）
R0 = HBARC / M0  # 仓库尺度 ≈ 0.2 fm


def self_energy_mev(r_fm):
    """静电自能 U = e²/(8πε₀r) = αℏc/(2r)（MeV）。"""
    return ALPHA * HBARC / (2.0 * r_fm)


def electron_flow(x, y, r0=0.2, q=1.0, gam=1.0):
    """电子流动结构：源（径向吸入 q/r² 截止 r0）+ 涡旋（环流 gam/r 截止）。
    返回 (vx, vy)。仅探讨结构对应，|v| 不作 c 归一（局部模型）。"""
    r = np.hypot(x, y)
    r = np.maximum(r, 0.05)
    sink = -q / r ** 2          # 径向吸入（电荷 = 源强度）
    swirl = gam / r             # 环流（自旋 = 涡旋强度）
    vx = sink * (x / r) + swirl * (-y / r)
    vy = sink * (y / r) + swirl * (x / r)
    return vx, vy


def main():
    report = {"model": "electron as space-flow structure (sink+swirl)",
              "results": {}}

    # ---- 自能表 ----
    u_r0 = self_energy_mev(R0)
    u_re = self_energy_mev(2.82)
    report["results"]["self_energy"] = {
        "U(r0=0.20fm, 仓库尺度) MeV": round(u_r0, 3),
        "U/r0 vs m_e": round(u_r0 / ME, 2),
        "U(re=2.82fm, 经典电子半径) MeV": round(u_re, 3),
        "U/re vs m_e": round(u_re / ME, 2),
        "m_e MeV": ME,
        "M0(仓库拟合) MeV": M0,
        "note": "经典电磁自能 = 电子质量的候选：量级接近但因子不干净"
                "（经典 4/3 因子 + ½ 因子问题）；r0 是拟合输入非推导"}

    # ---- 图 1: 电子龙卷风 ----
    fig, ax = plt.subplots(figsize=(8, 8))
    g = np.linspace(-3, 3, 29)
    X, Y = np.meshgrid(g, g)
    VX, VY = electron_flow(X, Y)
    ax.quiver(X, Y, VX, VY, color="steelblue", alpha=0.7)
    th = np.linspace(0, 2 * np.pi, 100)
    ax.plot(R0 * np.cos(th), R0 * np.sin(th), "r-", lw=2,
            label="r₀ = ℏ/M₀c ≈ 0.2 fm（结构核）")
    ax.scatter([0], [0], s=120, color="darkred", zorder=10)
    ax.text(0.3, 0.3, "电子核\n(自旋涡旋+电荷源)", fontsize=9, color="darkred")
    ax.set_xlim(-3, 3)
    ax.set_ylim(-3, 3)
    ax.set_aspect("equal")
    ax.set_title("电子 = 空间流动的'龙卷风'\n"
                 "（径向吸入=电荷源 ∇·C≠0 + 环流=自旋涡旋 ∇×C≠0）")
    ax.legend(loc="upper right", fontsize=9)
    fig.tight_layout()
    fig.savefig(os.path.join(OUT, "electron_tornado.png"), dpi=150)
    plt.close(fig)

    # ---- 图 2: 库仑场 vs 流动汇（形状一致 1/r²）----
    rr = np.linspace(0.3, 5, 200)
    fig, ax = plt.subplots(figsize=(8, 5))
    ax.plot(rr, 1 / rr ** 2, "C0-", lw=2, label="库仑场 E ∝ q/r²")
    ax.plot(rr, 1 / rr ** 2, "C1--", lw=2, label="流动汇 v_r ∝ q'/r²")
    ax.set_xlabel("r")
    ax.set_ylabel("场强（任意单位）")
    ax.set_title("结构对应：电荷 ↔ 空间流动源（同 1/r² 形状）")
    ax.legend()
    ax.grid(alpha=0.3)
    fig.tight_layout()
    fig.savefig(os.path.join(OUT, "coulomb_vs_sink.png"), dpi=150)
    plt.close(fig)

    # ---- 图 3: 自能柱状图 ----
    fig, ax = plt.subplots(figsize=(8, 5))
    labels = ["U(r₀=0.2fm)", "m_e", "U(r_e=2.82fm)", "M₀(胶球拟合)"]
    vals = [u_r0, ME, u_re, M0]
    ax.bar(labels, vals, color=["#1f77b4", "#2ca02c", "#d62728", "#888888"], alpha=0.85)
    for i, v in enumerate(vals):
        ax.text(i, v * 1.02, f"{v:.2f}", ha="center", fontsize=10, fontweight="bold")
    ax.set_ylabel("MeV")
    ax.set_title("经典电磁自能 vs 电子质量 vs 仓库尺度（量级关系，非推导）")
    ax.grid(axis="y", alpha=0.3)
    fig.tight_layout()
    fig.savefig(os.path.join(OUT, "self_energy.png"), dpi=150)
    plt.close(fig)

    report["conclusion"] = (
        "探讨结构：电子 = 空间流动的三重结合——① 自旋 = 涡旋（∇×C≠0）"
        "⟹ 锚定质量（MC1，已证）② 电荷 = 源（∇·C≠0）⟹ 静电场（库仑 1/r² "
        "与点汇同形）③ 电磁波 = 流动波动（MF4，已证）。"
        "统一图像：电子 = 龙卷风（局域结构），光子 = 涟漪（传播波），"
        "都是空间流动的形态。诚实：这是 2 层结构对应，不是推导——"
        "麦克斯韦线性无孤子、无电荷量子化、自能发散需 r₀ 截止（输入非推导）；"
        "自能量级接近 m_e（因子 ~2-7 不干净）。")
    with open(os.path.join(OUT, "report.json"), "w", encoding="utf-8") as f:
        json.dump(report, f, ensure_ascii=False, indent=2)

    print(json.dumps(report["results"], ensure_ascii=False, indent=2))
    print("\n→ 产物:", os.path.abspath(OUT))


if __name__ == "__main__":
    main()
