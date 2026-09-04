#!/usr/bin/env python3
"""反引力约束稳态自维持聚变环——工程图（材料 / 磁力线走向 / 磁场强度分布）

对应 docs/wiki/theory-antigravity-confinement.md 的设计。
leo（2026-09-04）：时变引力场 μ(t) 替代 FRC 分段压缩，稳态自维持。
本脚本在结构多视图（views/）之上补工程层（artifacts/antigravityconfinement/）：
  1. fig_material.png     —— 材料标注（左：径向截面 + 右：BOM 材料表）
  2. fig_field_line.png   —— 磁力线走向矢量图（FRC 场反位形：分离面内闭合 + 外部开放）
  3. fig_field_map.png    —— 磁场强度分布色带 |B_z(r,z)|（拉长位形 2D）

FRC 磁场模型（轴对称 (r, z)，完全反转位形，分离面精确在 r=rs）：
  B_z(r,z) = −B_pk·exp(−(r/rs)²)·exp(−(z/λ)²) + B_ext·(1−exp(−(r/rs)²))
  B_r(r,z) = −B_pk·(2z/λ²)·r·exp(−(r/rs)²)·exp(−(z/λ)²)/2   （轴正则，r→0 时 Br→0）
  B_pk = (e−1)·B_ext ⟹ 中心 B_z=−1.718·B_ext（反向）、r=rs 处 B_z=0（分离面）、
        大 r ⟹ B_z→+B_ext（外部正向）。
"""
import os
import numpy as np

OUT = os.path.join(os.path.dirname(__file__), "..", "artifacts",
                   "antigravityconfinement")
os.makedirs(OUT, exist_ok=True)

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
from matplotlib.patches import Circle
import matplotlib.font_manager as fm

for _fp in ("/Library/Fonts/Arial Unicode.ttf",
            "/System/Library/Fonts/STHeiti Light.ttc",
            "/System/Library/Fonts/PingFang.ttc",
            "/System/Library/Fonts/Hiragino Sans GB.ttc"):
    if os.path.exists(_fp):
        fm.fontManager.addfont(_fp)
        plt.rcParams["font.sans-serif"] = [fm.FontProperties(fname=_fp).get_name()]
        break
plt.rcParams["axes.unicode_minus"] = False

C_SHELL = "#34495e"
C_VAC = "#eef2f5"
C_RMF = "#27ae60"
C_FORM = "#1e8449"
C_CU = "#b03a2e"
C_H = "#2e86de"
C_FUEL = "#e67e22"
C_SEP = "#7f8c8d"
C_BG = "#faf8f5"

# 几何（cm）
R_SHELL = 16.0
R_RMF = 20.0
R_FORM = 21.5
R_PLASMA = 10.0
R_CU = 8.0
R_H = 5.0
R_FUEL = 2.5
L_PLASMA = 40.0

RS = R_PLASMA
LAM = L_PLASMA / 2
B_EXT = 1.0
B_PK = (np.e - 1.0) * B_EXT   # 中心反向峰值


def B_field(x, y):
    """返回 (B_r, B_z)。x=径向（含符号），y=轴向。"""
    r = np.abs(x)
    r = np.clip(r, 1e-6, None)
    g_r = np.exp(-(r / RS) ** 2)
    g_z = np.exp(-(y / LAM) ** 2)
    Bz = -B_PK * g_r * g_z + B_EXT * (1 - g_r)
    Br = -B_PK * (2 * y / LAM ** 2) * r * g_r * g_z / 2
    return np.sign(x) * Br, Bz


# ---------------------------------------------------------------------------
# 图 1：材料标注（左：径向截面 + 右：BOM 材料表）
# ---------------------------------------------------------------------------
def draw_material():
    fig, (ax0, ax1) = plt.subplots(
        1, 2, figsize=(13, 7.2),
        gridspec_kw={"width_ratios": [1.35, 1]},
        facecolor=C_BG)

    # —— 左：径向截面 ——
    ax0.set_facecolor(C_BG)
    ax0.set_aspect("equal")
    ax0.axis("off")
    S = 1.0 / R_FORM   # 归一化尺度
    # 分层圆
    ax0.add_patch(Circle((0, 0), R_FUEL * S, facecolor=C_FUEL,
                         edgecolor="none", zorder=2))
    for rad, col, ls in ((R_H, C_H, "-"), (R_CU, C_CU, "-"),
                         (R_PLASMA, C_SEP, "--"), (R_SHELL, C_SHELL, "-"),
                         (R_RMF, C_RMF, "--"), (R_FORM, C_FORM, ":")):
        ax0.add_patch(Circle((0, 0), rad * S, fill=False, color=col,
                             lw=2.0, ls=ls, zorder=3))
    # RMF / 形成线圈截面点
    for rad, col in ((R_RMF, C_RMF), (R_FORM, C_FORM)):
        for k in range(8):
            a = k * np.pi / 4 + np.pi / 8
            ax0.add_patch(Circle((rad * S * np.cos(a), rad * S * np.sin(a)),
                                 0.045, color=col, zorder=4))

    # 材料标注（引线 + 圆点）
    def label(r, ang, text, color, dx=0.07, dy=0.05):
        x, y = r * S * np.cos(ang), r * S * np.sin(ang)
        ax0.plot([x], [y], "o", color=color, ms=4, zorder=6)
        ax0.text(x + dx, y + dy, text, color=color, fontsize=8,
                 ha="left", va="center", zorder=6, fontweight="bold")

    label(R_FUEL, 0.02, "D-T燃料", C_FUEL, dx=0.10)
    label(R_H, np.pi * 0.30, "H快流环", C_H, dy=0.08)
    label(R_CU, np.pi * 0.28, "Cu慢流环", C_CU, dy=-0.05)
    label(R_PLASMA, np.pi * 1.30, "separatrix", C_SEP, dy=0.12)
    label(R_SHELL, np.pi * 1.60, "外壳316L", C_SHELL, dy=0.10)
    label(R_RMF, np.pi * 0.12, "RMF线圈", C_RMF, dx=0.11, dy=0.04)
    label(R_FORM, -np.pi * 0.22, "形成线圈", C_FORM, dy=0.13)

    ax0.set_xlim(-1.25, 1.25)
    ax0.set_ylim(-1.15, 1.15)
    ax0.set_title("径向截面（材料标注）", fontsize=12, color="#2c3e50",
                  fontweight="bold", pad=8)

    # —— 右：BOM 材料表（独立 axes，竖排不重叠）——
    ax1.set_facecolor(C_BG)
    ax1.axis("off")
    ax1.set_xlim(0, 1)
    ax1.set_ylim(0, 1)
    ax1.text(0.5, 0.97, "材料清单（BOM）", fontsize=12, color="#2c3e50",
             fontweight="bold", ha="center")

    bom = [("外壳/真空腔", "316L 不锈钢", "¥30/kg"),
           ("RMF 线圈", "无氧铜(水冷) / REBCO·HTS", "¥72/kg · ¥8000/kg"),
           ("形成线圈(θ-pinch)", "无氧铜", "¥72/kg"),
           ("绝缘层", "聚酰亚胺 Kapton", "—"),
           ("真空密封", "铜垫圈 / 氟橡胶 O-ring", "—"),
           ("端口窗", "石英 / 蓝宝石", "—"),
           ("等离子体", "D-T + Cu-H 双流环", "氘气 ¥3000/瓶"),
           ("储能", "脉冲电容（本设计无压缩，省略）", "省 ¥100万")]

    # 表头
    ax1.text(0.04, 0.88, "组件", fontsize=8.5, color="#2c3e50", fontweight="bold")
    ax1.text(0.34, 0.88, "材料", fontsize=8.5, color="#2c3e50", fontweight="bold")
    ax1.text(0.70, 0.88, "参考价", fontsize=8.5, color="#2c3e50", fontweight="bold")
    y = 0.82
    for row in bom:
        ax1.text(0.04, y, row[0], fontsize=7.5, color="#444444")
        ax1.text(0.34, y, row[1], fontsize=7.5, color="#444444")
        ax1.text(0.70, y, row[2], fontsize=7.5, color="#444444")
        y -= 0.090

    fig.tight_layout()
    fig.savefig(os.path.join(OUT, "fig_material.png"), dpi=160,
                bbox_inches="tight", facecolor=C_BG)
    plt.close(fig)
    print("wrote fig_material.png")


# ---------------------------------------------------------------------------
# 图 2：磁力线走向矢量图
# ---------------------------------------------------------------------------
def draw_field_line():
    fig, ax = plt.subplots(figsize=(9, 7))
    fig.patch.set_facecolor(C_BG)
    ax.set_facecolor(C_BG)

    xs = np.linspace(-R_FORM + 0.5, R_FORM - 0.5, 220)
    ys = np.linspace(-LAM - 4, LAM + 4, 180)
    X, Y = np.meshgrid(xs, ys)
    Br, Bz = B_field(X, Y)
    mag = np.sqrt(Br ** 2 + Bz ** 2)

    strm = ax.streamplot(X, Y, Br, Bz, color=mag, cmap="coolwarm",
                         linewidth=1.1, density=1.5, arrowsize=1.1,
                         arrowstyle="->")
    # 分离面（B_z=0）
    ax.contour(X, Y, Bz, levels=[0], colors=C_SEP, linewidths=2.0, linestyles="--")
    ax.add_patch(Circle((0, 0), R_SHELL, fill=False, color=C_SHELL, lw=2.2))

    ax.set_xlabel("径向 r（cm）", fontsize=10)
    ax.set_ylabel("轴向 z（cm）", fontsize=10)
    ax.set_title("FRC 场反位形磁力线走向（分离面内闭合反转 / 外部开放）",
                 fontsize=12, color="#2c3e50", fontweight="bold")
    cb = fig.colorbar(strm.lines, ax=ax, shrink=0.8)
    cb.set_label("|B|（归一化）", fontsize=9)

    ax.text(0, LAM + 2, "外部开放磁力线(轴向场)", fontsize=8, color="#c0392b",
            ha="center", va="center")
    ax.text(-R_SHELL, -LAM * 0.7, "分离面内闭合磁力线\n(场反位形,内部场反向)",
            fontsize=8, color="#2980b9", ha="right", va="center")
    ax.text(2.5, 3.0, "中心反向\nB_z≈−1.7", fontsize=8, color="#7f8c8d",
            ha="left", va="center")
    ax.plot([0], [0], "x", color="black", ms=6)

    fig.tight_layout()
    fig.savefig(os.path.join(OUT, "fig_field_line.png"), dpi=160,
                bbox_inches="tight", facecolor=C_BG)
    plt.close(fig)
    print("wrote fig_field_line.png")


# ---------------------------------------------------------------------------
# 图 3：磁场强度分布色带
# ---------------------------------------------------------------------------
def draw_field_map():
    fig, ax = plt.subplots(figsize=(9, 7))
    fig.patch.set_facecolor(C_BG)
    ax.set_facecolor(C_BG)

    xs = np.linspace(-R_FORM + 0.5, R_FORM - 0.5, 260)
    ys = np.linspace(-LAM - 4, LAM + 4, 220)
    X, Y = np.meshgrid(xs, ys)
    Br, Bz = B_field(X, Y)

    p = ax.pcolormesh(X, Y, Bz, shading="auto", cmap="RdBu_r", vmin=-1.8, vmax=1.0)
    ax.contour(X, Y, Bz, levels=[0], colors="black", linewidths=1.8)
    ax.add_patch(Circle((0, 0), R_SHELL, fill=False, color=C_SHELL, lw=2.2))

    ax.set_xlabel("径向 r（cm）", fontsize=10)
    ax.set_ylabel("轴向 z（cm）", fontsize=10)
    ax.set_title("轴向磁场 B_z(r,z)：完全反转场反位形（内部反向→分离面归零→边缘正向）",
                 fontsize=12, color="#2c3e50", fontweight="bold")
    cb = fig.colorbar(p, ax=ax, shrink=0.8)
    cb.set_label("B_z（归一化：蓝=反向 / 白=零 / 红=正向）", fontsize=9)

    ax.text(-R_SHELL, -LAM * 0.7, "内部(蓝):反向场\n≈−1.7·B_ext", fontsize=8,
            color="#2e86de", ha="right", va="center")
    ax.text(R_SHELL, LAM * 0.55, "边缘(红):\n正向场最大", fontsize=8,
            color="#c0392b", ha="left", va="center")
    ax.text(0.6, 0, "分离面 B_z=0", fontsize=8, color="black",
            ha="left", va="center")

    fig.tight_layout()
    fig.savefig(os.path.join(OUT, "fig_field_map.png"), dpi=160,
                bbox_inches="tight", facecolor=C_BG)
    plt.close(fig)
    print("wrote fig_field_map.png")


if __name__ == "__main__":
    draw_material()
    draw_field_line()
    draw_field_map()
    print("done ->", OUT)
