#!/usr/bin/env python3
"""反引力约束稳态自维持聚变环——装置图纸（绘图）

对应 docs/wiki/theory-antigravity-confinement.md 的设计。
leo（2026-09-04）：时变引力场 μ(t) 替代 FRC 分段压缩，稳态自维持。

图纸：
  1. fig_confinement_ring.png —— 装置系统示意图（三层同心结构）
     D-T 燃料区 / separatrix / H 快流环 / Cu 慢流环 / RMF 线圈，每环标注
     旋转方向箭头，环标注用"引点→引线→文字块"三点一线锚定，白底圆角防重叠。
  2. fig_mu_working_window.png —— μ 工作区间图（FC4 约束提升曲线 +
     FC11 RMF 天花板 + 反引力约束可行工作带）。
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

# —— 中文字体探测（优先单 face 的 Arial Unicode MS，覆盖最全；
#    PingFang.ttc 是 TTC，matplotlib 解析其 cmap 不完整会误报"稳"缺失）——
for _fp in ("/Library/Fonts/Arial Unicode.ttf",
            "/System/Library/Fonts/STHeiti Light.ttc",
            "/System/Library/Fonts/PingFang.ttc",
            "/System/Library/Fonts/Hiragino Sans GB.ttc"):
    if os.path.exists(_fp):
        fm.fontManager.addfont(_fp)
        plt.rcParams["font.sans-serif"] = [fm.FontProperties(fname=_fp).get_name()]
        break
plt.rcParams["axes.unicode_minus"] = False


# 统一配色（暖色协调主题）
C_FUEL = "#e67e22"   # D-T 燃料（能量核心，橙）
C_H = "#2e86de"      # H 快流环（青蓝）
C_CU = "#a04000"     # Cu 慢流环（铜棕）
C_SEP = "#95a5a6"    # separatrix（灰）
C_RMF = "#27ae60"    # RMF 线圈（绿）
C_CH = "#8e44ad"     # 时变/引力通道（紫）
C_BG = "#faf8f5"     # 背景米白


def ring_arrow(ax, r, ang, color, direction, length=0.42):
    """在环上角度 ang 处画一个切线方向箭头。direction=+1 逆时针，-1 顺时针。"""
    x0, y0 = r * np.cos(ang), r * np.sin(ang)
    tx, ty = -direction * np.sin(ang), direction * np.cos(ang)
    ax.annotate("", xy=(x0 + length * tx, y0 + length * ty), xytext=(x0, y0),
                arrowprops=dict(arrowstyle="->", color=color, lw=1.5,
                                shrinkA=0, shrinkB=0))


# ---------------------------------------------------------------------------
# 图 1：装置系统示意图
# ---------------------------------------------------------------------------
def draw_ring_schematic():
    fig, ax = plt.subplots(figsize=(11.5, 11.5))
    fig.patch.set_facecolor(C_BG)
    ax.set_facecolor(C_BG)
    ax.set_xlim(-4.7, 4.7)
    ax.set_ylim(-4.7, 4.7)
    ax.set_aspect("equal")
    ax.axis("off")

    # 同心层半径（由内到外）
    r_fuel, r_sep, r_h, r_cu, r_rmf = 0.9, 2.2, 1.7, 2.85, 3.85

    # ① D-T 燃料区
    ax.add_patch(Circle((0, 0), r_fuel, color=C_FUEL, alpha=0.92, zorder=3))
    ax.add_patch(Circle((0, 0), r_fuel, fill=False, color="#b3541e", lw=1, zorder=4))
    ax.text(0, 0.10, "① D-T 燃料", ha="center", va="center",
            fontsize=11, color="white", zorder=5, fontweight="bold")
    ax.text(0, -0.34, "反引力约束区", ha="center", va="center",
            fontsize=8.5, color="white", zorder=5)

    # ② 双流环（H 快 + Cu 慢）
    ax.add_patch(Circle((0, 0), r_h, fill=False, color=C_H, lw=2.4, zorder=2))
    ax.add_patch(Circle((0, 0), r_cu, fill=False, color=C_CU, lw=2.4, zorder=2))

    # separatrix（场反位形边界，闭合磁力线锚点）
    ax.add_patch(Circle((0, 0), r_sep, fill=False, color=C_SEP, lw=1.6,
                        ls="--", zorder=2))

    # ③ RMF 线圈（最外虚线环 + 截面点）
    ax.add_patch(Circle((0, 0), r_rmf, fill=False, color=C_RMF, lw=2.6,
                        ls="--", zorder=1))
    for k in range(8):
        a = k * np.pi / 4 + np.pi / 8
        ax.add_patch(Circle((r_rmf * np.cos(a), r_rmf * np.sin(a)), 0.13,
                            color=C_RMF, zorder=3))

    # —— 环旋转方向箭头（多标几个）——
    # H 环顺时针（-1）、Cu 环逆时针（+1）—— DR2b 反向环流抵消
    # RMF 顺时针（旋转磁场），separatrix 闭合（顺）
    for k in range(5):
        ring_arrow(ax, r_h, 2 * np.pi * k / 5, C_H, -1)
    for k in range(5):
        ring_arrow(ax, r_cu, 2 * np.pi * k / 5 + np.pi / 5, C_CU, +1)
    for k in range(5):
        ring_arrow(ax, r_rmf, 2 * np.pi * k / 5 + np.pi / 10, C_RMF, -1)
    for k in range(2):
        ring_arrow(ax, r_sep, 2 * np.pi * k / 2 + np.pi / 4, C_SEP, -1)

    # —— 文字块：白底圆角，避免视觉重叠 ——
    def blk(x, y, text, color, ha="left", fs=7.5):
        ax.text(x, y, text, fontsize=fs, color=color, ha=ha, va="center",
                zorder=7, linespacing=1.35,
                bbox=dict(boxstyle="round,pad=0.18", fc="white", ec=color,
                          lw=0.8, alpha=0.92))

    # —— 环标注：环上引点 → 引线 → 文字块（三点一线，位置匹配）——
    def ring_note(r, ang, bx, by, text, color, ha="center", fs=7.5, rad=0.28):
        x0, y0 = r * np.cos(ang), r * np.sin(ang)
        ax.plot([x0], [y0], "o", color=color, ms=4.5, zorder=6)
        ax.annotate("", xy=(bx, by), xytext=(x0, y0),
                    arrowprops=dict(arrowstyle="-", color=color, lw=1.1,
                                    shrinkB=3, connectionstyle="arc3,rad=0.12"))
        blk(bx, by, text, color, ha=ha, fs=fs)

    # ② H 快流环 —— 左（引点在环左，文字块放左下外侧）
    ring_note(r_h, np.pi, -2.95, 0.0, "② H 快流环\n(轻离子,快流)", C_H,
              ha="right", fs=7.5)
    # ② Cu 慢流环 —— 左下
    ring_note(r_cu, 1.10 * np.pi, -3.05, -2.35, "② Cu 慢流环\n(重离子,惯性锚定)",
              C_CU, ha="center", fs=7.5)
    # separatrix / 闭合磁力线 —— 右下
    ring_note(r_sep, -0.65 * np.pi, 2.55, -2.7, "闭合磁力线\n(separatrix, 场反位形)",
              C_SEP, ha="center", fs=7.0)
    # ③ RMF 线圈 —— 右上
    ring_note(r_rmf, 0.35 * np.pi, 2.7, 2.5, "③ RMF 线圈\n(时变电磁场)", C_RMF,
              ha="center", fs=7.5)

    # 时变通道：RMF → μ(t)（右上角）
    ax.annotate("", xy=(2.9, 3.0), xytext=(3.6, 3.7),
                arrowprops=dict(arrowstyle="->", color=C_CH, lw=1.8, ls="--"))
    blk(3.55, 3.85, "时变磁场→μ(t)\n(PA4)", C_CH, ha="left", fs=7.5)

    # μ 约束通道：中心向上箭头 + 左上标注（引线）
    ax.annotate("", xy=(0, 1.15), xytext=(0, 0.4),
                arrowprops=dict(arrowstyle="->", color=C_FUEL, lw=2.2))
    ax.annotate("", xy=(-0.05, 1.25), xytext=(-1.55, 2.05),
                arrowprops=dict(arrowstyle="->", color=C_FUEL, lw=1.2,
                                connectionstyle="arc3,rad=0.15"))
    blk(-1.65, 2.0, "μ(t)→m_eff↓\nρ_i↓ / τ_E↑", C_FUEL, ha="right", fs=7.5)

    # 反向环流抵消 —— 右下角
    ax.text(3.55, -1.35, "反向环流抵消\nDR2b Γ(v)+Γ(−v)=0", fontsize=7,
            color="#7d3c98", ha="center", va="center", zorder=7, linespacing=1.35,
            bbox=dict(boxstyle="round,pad=0.18", fc="white", ec="#7d3c98",
                      lw=0.8, alpha=0.92))

    # 标题
    ax.set_title("反引力约束稳态自维持聚变环（装置系统示意图）",
                 fontsize=14, color="#2c3e50", pad=14, fontweight="bold")
    ax.text(0, -4.45, "FRC 场反位形 + 时变引力场 μ(t)——砍掉分段压缩\n"
                      "（H 环顺时针 / Cu 环逆时针：反向环流抵消）",
            fontsize=9.5, color="#2c3e50", ha="center")

    fig.savefig(os.path.join(OUT, "fig_confinement_ring.png"), dpi=160,
                bbox_inches="tight")
    plt.close(fig)
    print("wrote fig_confinement_ring.png")


# ---------------------------------------------------------------------------
# 图 2：μ 工作区间图（FC4 约束提升 + FC11 RMF 天花板）
# ---------------------------------------------------------------------------
def draw_mu_window():
    fig, ax = plt.subplots(figsize=(10.5, 5.5))
    fig.patch.set_facecolor("white")

    mu = np.linspace(0.0, 0.9999, 2000)
    tau_ratio = 1.0 / np.sqrt(1.0 - mu)
    ax.plot(mu, tau_ratio, color="#16a085", lw=2.2,
            label="τ_E/τ_E(0) = 1/√(1−μ)（FC4 反引力约束提升）")

    m_e, m_i = 0.000548579909, 2.5
    mu_crit = 1.0 - m_e / m_i
    ax.axvline(mu_crit, color="red", lw=2.2, ls="--",
               label=f"FC11 RMF 天花板 μ<{mu_crit:.5f}")
    ax.axvline(0.999, color="#8e44ad", lw=1.3, ls=":",
               label="μ=0.999（α 加热窄窗下缘，参考）")
    ax.axvspan(0.99, mu_crit, color="#f9e79f", alpha=0.55,
               label="反引力约束可行工作带")

    for mu_ref in (0.99, 0.999, mu_crit):
        r = 1.0 / np.sqrt(1.0 - mu_ref)
        ax.plot(mu_ref, r, "o", color="#e67e22", ms=6.5, zorder=5)
        ax.annotate(f"μ={mu_ref:.4g} → τ_E×{r:.1f}",
                    xy=(mu_ref, r), xytext=(-0.085, 0.0),
                    textcoords="offset points", fontsize=8, color="#e67e22",
                    ha="right", va="center",
                    arrowprops=dict(arrowstyle="->", color="#e67e22", lw=0.9))

    ax.set_xlabel("μ（反引力强度）", fontsize=11)
    ax.set_ylabel("τ_E / τ_E(0)（约束时间提升倍数）", fontsize=11)
    ax.set_yscale("log")
    ax.set_xlim(0.90, 1.0)
    ax.set_ylim(1, 160)
    ax.set_title("反引力约束的 μ 工作区间：FC4 提升 vs FC11 天花板",
                 fontsize=13, color="#2c3e50", fontweight="bold")
    ax.legend(loc="upper left", fontsize=8, framealpha=0.9, edgecolor="#dddddd")
    ax.grid(alpha=0.28, which="both", linestyle="--")

    fig.tight_layout()
    fig.savefig(os.path.join(OUT, "fig_mu_working_window.png"), dpi=160,
                bbox_inches="tight")
    plt.close(fig)
    print("wrote fig_mu_working_window.png")


if __name__ == "__main__":
    draw_ring_schematic()
    draw_mu_window()
    print("done ->", OUT)
