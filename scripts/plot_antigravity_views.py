#!/usr/bin/env python3
"""反引力约束稳态自维持聚变环——装置多视图工程示意图

对应 docs/wiki/theory-antigravity-confinement.md 的设计。
leo（2026-09-04）：时变引力场 μ(t) 替代 FRC 分段压缩，稳态自维持。

本脚本画"带外壳 + 截面"的多视图图集（artifacts/antigravityconfinement/views/）：
  1. fig_elevation.png        —— 侧视图（纵剖面）：外壳 + 端盖 + RMF/形成线圈
                                 + 等离子体分层(对称拉长椭球) + 闭合磁力线
                                 + 端口 + 尺寸线
  2. fig_cross_section.png    —— 径向横剖面：同心分层全结构 + separatrix
  3. fig_top_view.png         —— 俯视图：外壳顶 + 端口布局 + 线圈分布
  4. fig_isometric.png        —— 轴测 3D 示意：整体外观 + 线圈环 + 端口

装置几何（FRC 拉长位形，elongation~4）：L=50cm、R_shell=16cm、
R_plasma(separatrix)=10cm、Cu 环 8cm、H 环 5cm、D-T 柱 2.5cm。
"""
import os

import numpy as np

OUT = os.path.join(os.path.dirname(__file__), "..", "artifacts",
                   "antigravityconfinement", "views")
os.makedirs(OUT, exist_ok=True)

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
from matplotlib.patches import Circle, Rectangle, FancyArrowPatch, Polygon
import matplotlib.font_manager as fm

# —— 中文字体探测（优先单 face 的 Arial Unicode MS，覆盖最全）——
for _fp in ("/Library/Fonts/Arial Unicode.ttf",
            "/System/Library/Fonts/STHeiti Light.ttc",
            "/System/Library/Fonts/PingFang.ttc",
            "/System/Library/Fonts/Hiragino Sans GB.ttc"):
    if os.path.exists(_fp):
        fm.fontManager.addfont(_fp)
        plt.rcParams["font.sans-serif"] = [fm.FontProperties(fname=_fp).get_name()]
        break
plt.rcParams["axes.unicode_minus"] = False

# —— 统一配色 ——
C_SHELL = "#34495e"    # 外壳（深灰蓝）
C_VAC = "#eef2f5"      # 真空（淡灰）
C_RMF = "#27ae60"      # RMF 线圈（绿）
C_FORM = "#1e8449"     # 形成线圈（深绿）
C_CU = "#b03a2e"       # Cu 慢流环（铜）
C_H = "#2e86de"        # H 快流环（蓝）
C_FUEL = "#e67e22"     # D-T 燃料（橙）
C_SEP = "#7f8c8d"      # separatrix（灰）
C_DIM = "#2c3e50"      # 尺寸线
C_BG = "#faf8f5"       # 背景米白
C_PORT = "#8e44ad"     # 端口（紫）

# —— 装置几何（cm）——
L = 50.0          # 装置总长（z 向）
R_SHELL = 16.0
R_RMF = 20.0
R_FORM = 21.5
R_PLASMA = 10.0   # separatrix
R_CU = 8.0
R_H = 5.0
R_FUEL = 2.5
L_PLASMA = 40.0   # 等离子体长度


def _ellip(r_, zp, zs):
    """拉长椭球剖面（对称）：y = r*√(1−(z/zp)²)，z∈[−zp,zp]。
    zs 用 clip 到 [−zp,zp]，避免 sqrt 负数。"""
    zc = np.clip(zs, -zp, zp)
    return r_ * np.sqrt(np.maximum(1 - (zc / zp) ** 2, 0.0))


# ---------------------------------------------------------------------------
# 图 1：侧视图（纵剖面）
# ---------------------------------------------------------------------------
def draw_elevation():
    fig, ax = plt.subplots(figsize=(11.5, 6))
    fig.patch.set_facecolor(C_BG)
    ax.set_facecolor(C_BG)
    ax.set_aspect("equal")
    ax.axis("off")

    z_half = L / 2
    zp = L_PLASMA / 2
    zs = np.linspace(-zp, zp, 400)

    # —— 真空腔体（内部填充）——
    ax.add_patch(Rectangle((-z_half, -R_SHELL), L, 2 * R_SHELL,
                           facecolor=C_VAC, edgecolor="none", zorder=1))
    # —— 外壳壁（上下 + 端盖 + 法兰）——
    ax.plot([-z_half, z_half], [R_SHELL, R_SHELL], color=C_SHELL, lw=3, zorder=4)
    ax.plot([-z_half, z_half], [-R_SHELL, -R_SHELL], color=C_SHELL, lw=3, zorder=4)
    for sgn in (-1, 1):
        ax.plot([sgn * z_half, sgn * z_half], [-R_SHELL, R_SHELL],
                color=C_SHELL, lw=3, zorder=4)
        ax.add_patch(Rectangle((sgn * z_half - 0.7, -R_SHELL - 1.4), 0.7,
                               2 * R_SHELL + 2.8, facecolor=C_SHELL,
                               edgecolor="none", zorder=4, alpha=0.92))

    # —— 形成线圈（θ-pinch，端部）——
    for sgn in (-1, 1):
        zc = sgn * (z_half - 2.5)
        ax.add_patch(Rectangle((zc - 1.4, R_SHELL + 0.5), 2.8, R_FORM - R_SHELL,
                               facecolor=C_FORM, edgecolor="none", zorder=3, alpha=0.9))
        ax.add_patch(Rectangle((zc - 1.4, -R_FORM), 2.8, R_FORM - R_SHELL,
                               facecolor=C_FORM, edgecolor="none", zorder=3, alpha=0.9))

    # —— RMF 线圈（沿轴 6 个环形环）——
    for zc in np.linspace(-z_half + 7, z_half - 7, 6):
        ax.add_patch(Rectangle((zc - 1.1, R_SHELL + 0.4), 2.2, R_RMF - R_SHELL,
                               facecolor=C_RMF, edgecolor="none", zorder=3, alpha=0.85))
        ax.add_patch(Rectangle((zc - 1.1, -R_RMF), 2.2, R_RMF - R_SHELL,
                               facecolor=C_RMF, edgecolor="none", zorder=3, alpha=0.85))

    # —— 等离子体分层（对称拉长椭球）——
    # separatrix（虚线外壳）
    ax.plot(zs, _ellip(R_PLASMA, zp, zs), color=C_SEP, lw=1.7, ls="--", zorder=2)
    ax.plot(zs, -_ellip(R_PLASMA, zp, zs), color=C_SEP, lw=1.7, ls="--", zorder=2)
    # 内层闭合磁力线（虚线）
    for rr in (0.62, 0.82):
        ax.plot(zs, _ellip(R_PLASMA * rr, zp, zs), color=C_SEP, lw=0.8, ls=":", zorder=2)
        ax.plot(zs, -_ellip(R_PLASMA * rr, zp, zs), color=C_SEP, lw=0.8, ls=":", zorder=2)
    # D-T 燃料（实心）
    ax.fill_between(zs, -_ellip(R_FUEL, zp, zs), _ellip(R_FUEL, zp, zs),
                    color=C_FUEL, alpha=0.75, zorder=2)
    # H 环 / Cu 环（轮廓线）
    ax.plot(zs, _ellip(R_H, zp, zs), color=C_H, lw=2.0, zorder=2)
    ax.plot(zs, -_ellip(R_H, zp, zs), color=C_H, lw=2.0, zorder=2)
    ax.plot(zs, _ellip(R_CU, zp, zs), color=C_CU, lw=2.0, zorder=2)
    ax.plot(zs, -_ellip(R_CU, zp, zs), color=C_CU, lw=2.0, zorder=2)

    # —— 端口 ——
    ax.add_patch(Rectangle((-2.0, R_SHELL - 0.3), 4, 2.4, facecolor=C_PORT,
                           edgecolor="none", zorder=5, alpha=0.92))
    ax.text(0, R_SHELL + 2.8, "诊断窗", color=C_PORT, fontsize=8,
            ha="center", va="bottom")
    ax.add_patch(FancyArrowPatch((z_half + 2.5, 3), (z_half + 0.5, 3),
                                 arrowstyle="->", color=C_PORT, lw=2))
    ax.text(z_half + 3.0, 3, "气体馈入", color=C_PORT, fontsize=8, va="center")
    ax.add_patch(FancyArrowPatch((-z_half - 0.5, -4), (-z_half - 2.5, -4),
                                 arrowstyle="->", color=C_PORT, lw=2))
    ax.text(-z_half - 3.0, -4, "抽气", color=C_PORT, fontsize=8, va="center")

    # —— 标注（引线 + 圆点），全部放在图内，避免溢出 ——
    def label(z, y, text, color, dz=1.8, dy=0.5, ha="left"):
        ax.plot([z], [y], "o", color=color, ms=3.5, zorder=6)
        ax.text(z + dz, y + dy, text, color=color, fontsize=8, va="center", ha=ha,
                zorder=6)

    label(3.0, R_FUEL + 0.6, "① D-T 燃料(反引力约束区)", C_FUEL, dz=1.8)
    label(5.0, R_H + 0.5, "② H 快流环", C_H, dz=1.8)
    label(8.0, R_CU + 0.5, "② Cu 慢流环", C_CU, dz=1.8)
    label(0, R_PLASMA + 0.8, "separatrix", C_SEP, dz=-1.8, ha="right")
    label(0, R_RMF + 1.0, "RMF 线圈(时变电磁场)", C_RMF, dz=0, dy=0.6, ha="center")
    label(-z_half + 4, R_FORM + 1.0, "θ-pinch 形成线圈", C_FORM, dz=0, dy=0.6,
          ha="center")
    label(-z_half + 6, R_SHELL - 1.5, "外壳(真空腔)", C_SHELL, dz=0, dy=-0.8,
          ha="center")

    # —— 尺寸标注 ——
    ax.annotate("", xy=(-z_half - 1.5, R_PLASMA), xytext=(-z_half - 1.5, -R_PLASMA),
                arrowprops=dict(arrowstyle="<->", color=C_DIM, lw=1.2))
    ax.text(-z_half - 2.2, 0, f"2R_plasma\n{2 * R_PLASMA:.0f}cm", color=C_DIM,
            fontsize=7.5, ha="right", va="center", rotation=90)
    ax.annotate("", xy=(-z_half - 4.5, R_SHELL), xytext=(-z_half - 4.5, -R_SHELL),
                arrowprops=dict(arrowstyle="<->", color="#a0a0a0", lw=1.0))
    ax.text(-z_half - 5.2, 0, f"2R_shell\n{2 * R_SHELL:.0f}cm", color="#a0a0a0",
            fontsize=7, ha="right", va="center", rotation=90)
    ax.annotate("", xy=(-zp, -R_RMF - 4), xytext=(zp, -R_RMF - 4),
                arrowprops=dict(arrowstyle="<->", color=C_DIM, lw=1.2))
    ax.text(0, -R_RMF - 3.2, f"等离子体长度 {L_PLASMA:.0f}cm", color=C_DIM,
            fontsize=8, ha="center", va="top")

    ax.set_xlim(-z_half - 9, z_half + 9)
    ax.set_ylim(-R_RMF - 7, R_RMF + 7)
    ax.set_title("反引力约束稳态聚变环 · 侧视图（纵剖面）",
                 fontsize=13, color="#2c3e50", fontweight="bold", pad=10)
    fig.tight_layout()
    fig.savefig(os.path.join(OUT, "fig_elevation.png"), dpi=160,
                bbox_inches="tight", facecolor=C_BG)
    plt.close(fig)
    print("wrote fig_elevation.png")


# ---------------------------------------------------------------------------
# 图 2：径向横剖面
# ---------------------------------------------------------------------------
def draw_cross_section():
    fig, ax = plt.subplots(figsize=(8.5, 8.5))
    fig.patch.set_facecolor(C_BG)
    ax.set_facecolor(C_BG)
    ax.set_aspect("equal")
    ax.axis("off")

    R = R_RMF + 2.2
    ax.add_patch(Circle((0, 0), R_SHELL, facecolor=C_VAC, edgecolor="none", zorder=1))
    ax.add_patch(Circle((0, 0), R_SHELL, fill=False, color=C_SHELL, lw=3, zorder=4))
    ax.add_patch(Circle((0, 0), R_PLASMA, fill=False, color=C_SEP, lw=1.6,
                        ls="--", zorder=3))
    ax.add_patch(Circle((0, 0), R_CU, fill=False, color=C_CU, lw=2.2, zorder=3))
    ax.add_patch(Circle((0, 0), R_H, fill=False, color=C_H, lw=2.2, zorder=3))
    ax.add_patch(Circle((0, 0), R_FUEL, facecolor=C_FUEL, alpha=0.9, zorder=2))
    for k in range(8):
        a = k * np.pi / 4 + np.pi / 8
        ax.add_patch(Circle((R_RMF * np.cos(a), R_RMF * np.sin(a)), 1.3,
                            color=C_RMF, zorder=4))
    for rr in (0.62, 0.82):
        ax.add_patch(Circle((0, 0), R_PLASMA * rr, fill=False, color=C_SEP,
                            lw=0.8, ls=":", zorder=2))

    # 标注（角度分散，避免右上拥挤）
    def label(r, ang, text, color):
        x, y = r * np.cos(ang), r * np.sin(ang)
        ax.plot([x], [y], "o", color=color, ms=3.5, zorder=6)
        ax.text(x * 1.18, y * 1.18, text, color=color, fontsize=8.5,
                ha="center", va="center", zorder=6)

    label(R_FUEL, np.pi * 0.25, "① D-T燃料", C_FUEL)
    label(R_H, np.pi * 2.6, "② H快流环", C_H)
    label(R_CU, np.pi * 0.55, "② Cu慢流环", C_CU)
    label(R_PLASMA, np.pi * 1.35, "separatrix", C_SEP)
    label(R_SHELL, np.pi * 1.75, "外壳", C_SHELL)
    label(R_RMF, np.pi * 0.0, "RMF线圈", C_RMF)

    # 中心 μ 约束箭头
    ax.annotate("", xy=(0, R_FUEL + 0.6), xytext=(0, 0),
                arrowprops=dict(arrowstyle="->", color=C_FUEL, lw=2))
    # （μ(t) 约束区标注由侧视图/轴测表达，横剖面聚焦同心结构，保持干净）

    ax.set_xlim(-R, R)
    ax.set_ylim(-R, R)
    ax.set_title("反引力约束稳态聚变环 · 径向横剖面",
                 fontsize=13, color="#2c3e50", fontweight="bold", pad=10)
    fig.tight_layout()
    fig.savefig(os.path.join(OUT, "fig_cross_section.png"), dpi=160,
                bbox_inches="tight", facecolor=C_BG)
    plt.close(fig)
    print("wrote fig_cross_section.png")


# ---------------------------------------------------------------------------
# 图 3：俯视图
# ---------------------------------------------------------------------------
def draw_top_view():
    fig, ax = plt.subplots(figsize=(8.5, 8.5))
    fig.patch.set_facecolor(C_BG)
    ax.set_facecolor(C_BG)
    ax.set_aspect("equal")
    ax.axis("off")

    R = R_FORM + 2.5
    ax.add_patch(Circle((0, 0), R_SHELL + 1.2, facecolor="#dfe6ec",
                        edgecolor=C_SHELL, lw=1.5, zorder=2))
    ax.add_patch(Circle((0, 0), R_SHELL, fill=False, color=C_SHELL, lw=3, zorder=3))
    ax.add_patch(Circle((0, 0), R_RMF, fill=False, color=C_RMF, lw=2, ls="--", zorder=3))
    ax.add_patch(Circle((0, 0), R_FORM, fill=False, color=C_FORM, lw=2, ls=":", zorder=3))

    ax.add_patch(Circle((0, 0), 2.0, facecolor=C_PORT, edgecolor="none", zorder=4))
    ax.text(0, 0, "中心\n诊断口", color="white", fontsize=7, ha="center",
            va="center", zorder=5)
    for k in range(4):
        a = k * np.pi / 2 + np.pi / 4
        x, y = 10 * np.cos(a), 10 * np.sin(a)
        ax.add_patch(Circle((x, y), 1.4, facecolor=C_PORT, edgecolor="none", zorder=4))
        ax.text(x, y, "端口", color="white", fontsize=6, ha="center",
                va="center", zorder=5)

    ax.text(R_RMF * 0.75, R_RMF * 0.80, "RMF线圈(虚线)", color=C_RMF, fontsize=8)
    ax.text(R_FORM * 0.75, -R_FORM * 0.80, "形成线圈(点线)", color=C_FORM, fontsize=8)
    ax.text(R_SHELL + 1.8, 0, "端盖法兰", color=C_SHELL, fontsize=8, va="center")

    ax.set_xlim(-R, R)
    ax.set_ylim(-R, R)
    ax.set_title("反引力约束稳态聚变环 · 俯视图",
                 fontsize=13, color="#2c3e50", fontweight="bold", pad=10)
    fig.tight_layout()
    fig.savefig(os.path.join(OUT, "fig_top_view.png"), dpi=160,
                bbox_inches="tight", facecolor=C_BG)
    plt.close(fig)
    print("wrote fig_top_view.png")


# ---------------------------------------------------------------------------
# 图 4：轴测 3D 示意图
# ---------------------------------------------------------------------------
def draw_isometric():
    from mpl_toolkits.mplot3d import Axes3D  # noqa
    fig = plt.figure(figsize=(11, 7))
    fig.patch.set_facecolor(C_BG)
    ax = fig.add_subplot(111, projection="3d")
    ax.set_facecolor(C_BG)

    z_half = L / 2
    zp = L_PLASMA / 2
    theta = np.linspace(0, 2 * np.pi, 80)

    # 外壳（半透明圆柱）
    zc = np.linspace(-z_half, z_half, 2)
    T, Z = np.meshgrid(theta, zc)
    ax.plot_surface(R_SHELL * np.cos(T), R_SHELL * np.sin(T), Z,
                    color=C_SHELL, alpha=0.16, rstride=1, cstride=1,
                    linewidth=0, antialiased=True)

    # 等离子体（半透明拉长椭球，用较小半径，避免撑破外壳观感）
    zp_n = np.linspace(-zp, zp, 30)
    T2, Z2 = np.meshgrid(theta, zp_n)
    Xp = R_H * np.cos(T2) * np.sqrt(np.maximum(1 - (Z2 / zp) ** 2, 0))
    Yp = R_H * np.sin(T2) * np.sqrt(np.maximum(1 - (Z2 / zp) ** 2, 0))
    ax.plot_surface(Xp, Yp, Z2, color=C_FUEL, alpha=0.45, rstride=1, cstride=1,
                    linewidth=0, antialiased=True)

    # RMF 线圈环（绕在外部，少而清晰）
    for zc2 in np.linspace(-z_half + 4, z_half - 4, 4):
        ax.plot(R_RMF * np.cos(theta), R_RMF * np.sin(theta),
                np.full_like(theta, zc2), color=C_RMF, lw=3.0)

    # 端盖
    for sgn in (-1, 1):
        ax.plot(R_SHELL * np.cos(theta), R_SHELL * np.sin(theta),
                np.full_like(theta, sgn * z_half), color=C_SHELL, lw=2.5)

    # 端口（诊断窗，侧面小凸起）
    ax.plot([R_SHELL, R_SHELL + 2.5], [0, 0], [0, 0], color=C_PORT, lw=3)
    ax.plot([R_SHELL, R_SHELL + 2.5], [0, 0], [zp, zp], color=C_PORT, lw=3)

    ax.set_axis_off()
    ax.set_box_aspect((1.5, 1.5, 1.6))
    ax.view_init(elev=20, azim=-65)

    ax.text(0, R_RMF + 2, z_half * 0.5, "RMF 线圈", color=C_RMF, fontsize=9)
    ax.text(0, 0, z_half + 2, "端盖", color=C_SHELL, fontsize=9)
    ax.text(0, R_H + 1, 0, "D-T 燃料等离子体", color=C_FUEL, fontsize=8)

    ax.set_title("反引力约束稳态聚变环 · 轴测示意图",
                 fontsize=13, color="#2c3e50", fontweight="bold", pad=-8)
    fig.tight_layout()
    fig.savefig(os.path.join(OUT, "fig_isometric.png"), dpi=160,
                bbox_inches="tight", facecolor=C_BG)
    plt.close(fig)
    print("wrote fig_isometric.png")


if __name__ == "__main__":
    draw_elevation()
    draw_cross_section()
    draw_top_view()
    draw_isometric()
    print("done ->", OUT)
