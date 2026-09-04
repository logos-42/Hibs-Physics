#!/usr/bin/env python3
"""人工场（空间场调制）——最优频率图集

对应项目里"人工场介于电磁场基态与引力场之间"的选频分析。
leo（2026-09-04）：算人工场在什么频率最好用、速度最快、成本最低。

图纸（artifacts/artificialfield/）：
  1. fig_rmf_window.png   —— RMF 窗口 + 最优频率随磁场 B 变化
  2. fig_field_triage.png —— 三判据（好用/快/便宜）在频率轴的适用范围，
                             最优=三带重叠区（图例说明判据）
  3. fig_cost_freq.png    —— 成本-频率权衡（趋肤损耗∝√f、RF电源成本、VHF最优）
"""
import os
import math

import numpy as np

OUT = os.path.join(os.path.dirname(__file__), "..", "artifacts",
                   "artificialfield")
os.makedirs(OUT, exist_ok=True)

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
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

# —— 物理常数（D-T FRC 稳态）——
e = 1.60218e-19
m_e = 9.10938e-31
m_i = 2.5 * 1.66054e-27      # D-T 平均离子
c = 2.9979e8
L = 0.5                       # 装置长（m）
F_MAX = c / L                 # 装置光速响应上限

C_BG = "#faf8f5"
C_CI = "#2e86de"              # 离子回旋（蓝）
C_CE = "#c0392b"              # 电子回旋（红）
C_OPT = "#e67e22"             # 最优（橙）
C_LIM = "#8e44ad"             # 上限（紫）
C_EM = "#c0392b"              # 电磁基态
C_ART = "#27ae60"             # 人工场（绿）


def f_ci(B):
    return e * B / (2 * math.pi * m_i)


def f_ce(B):
    return e * B / (2 * math.pi * m_e)


def _font_setup():
    pass


# ---------------------------------------------------------------------------
# 图 1：RMF 窗口 + 最优频率 vs B
# ---------------------------------------------------------------------------
def draw_rmf_window():
    fig, ax = plt.subplots(figsize=(9, 6))
    fig.patch.set_facecolor(C_BG)
    ax.set_facecolor(C_BG)

    B = np.linspace(0.05, 10, 400)
    fci = np.array([f_ci(b) for b in B])
    fce = np.array([f_ce(b) for b in B])

    ax.fill_between(B, fci, fce, color="#b8d4e3", alpha=0.35,
                    label="RMF 有效窗口 [f_ci, f_ce]")
    ax.fill_between(B, 2 * fci, 5 * fci, color="#f5b041", alpha=0.55,
                    label="最优 (2-5)×f_ci")

    ax.plot(B, fci, color=C_CI, lw=2.2, label="f_ci = eB/(2πm_i)（下界）")
    ax.plot(B, fce, color=C_CE, lw=2.2, ls="--", label="f_ce = eB/(2πm_e)（上界）")
    ax.axhline(F_MAX, color=C_LIM, lw=2, ls=":", label=f"c/L={F_MAX/1e6:.0f}MHz (装置上限)")

    ax.set_xlabel("磁场 B（T）", fontsize=11)
    ax.set_ylabel("频率（Hz）", fontsize=11)
    ax.set_yscale("log")
    ax.set_ylim(1e5, 1e12)
    ax.set_xlim(0, 10)
    ax.set_title("人工场 RMF 窗口与最优频率 vs 磁场（D-T）",
                 fontsize=13, color="#2c3e50", fontweight="bold")
    ax.legend(loc="lower right", fontsize=8, framealpha=0.92)
    ax.grid(alpha=0.28, which="both", ls="--")

    for Bt in (1, 5, 9):
        val = 2.5 * f_ci(Bt)
        ax.scatter([Bt], [f_ci(Bt)], color=C_CI, s=22, zorder=5)
        ax.scatter([Bt], [val], color=C_OPT, s=22, zorder=5)
        ax.annotate(f"B={Bt}T\nf_ci={f_ci(Bt)/1e6:.0f}MHz\n最优={val/1e6:.0f}MHz",
                    xy=(Bt, val), xytext=(Bt + 0.4, val * 1.7), fontsize=6.5,
                    color="#555555", arrowprops=dict(arrowstyle="->", color="#555555", lw=0.7))

    fig.tight_layout()
    fig.savefig(os.path.join(OUT, "fig_rmf_window.png"), dpi=160,
                bbox_inches="tight", facecolor=C_BG)
    plt.close(fig)
    print("wrote fig_rmf_window.png")


# ---------------------------------------------------------------------------
# 图 2：三判据（好用/快/便宜）× 频率，最优=三带重叠区（图例说明判据）
# ---------------------------------------------------------------------------
def draw_field_triage():
    fig, ax = plt.subplots(figsize=(9.5, 5.5))
    fig.patch.set_facecolor(C_BG)
    ax.set_facecolor(C_BG)

    B = 9.0
    f_lo = f_ci(B)
    f_hi = f_ce(B)
    f_opt = 2.5 * f_lo
    f_opt2 = 5.0 * f_lo

    # 三判据带（label → 图例）
    ax.hlines(3, f_lo, f_hi, color=C_CI, lw=16, alpha=0.35,
              label="① 好用 [f_ci, f_ce]（离子磁化驱动）")
    ax.hlines(2, f_lo, F_MAX, color=C_LIM, lw=16, alpha=0.35,
              label="② 快 [f_ci, c/L]（光速上限）")
    ax.hlines(1, f_lo, f_hi * 0.5, color=C_ART, lw=16, alpha=0.35,
              label="③ 便宜（低频RF省, 损耗∝√f）")
    ax.hlines([1, 2, 3], f_opt, f_opt2, color=C_OPT, lw=16, alpha=0.78,
              label="★ 最优 (2-5)×f_ci")

    # 关键频率竖线（label → 图例，避免图上文字与标题重叠）
    for f, col, lab in ((f_lo, C_CI, f"f_ci={f_lo/1e6:.0f}MHz"),
                        (f_opt, C_OPT, f"最优={f_opt/1e6:.0f}MHz"),
                        (F_MAX, C_LIM, f"c/L={F_MAX/1e6:.0f}MHz"),
                        (f_hi, C_CE, f"f_ce={f_hi/1e9:.4g}GHz")):
        ax.axvline(f, color=col, lw=1.5, ls="--", alpha=0.9, label=lab)

    ax.set_xlabel("频率（Hz，对数）", fontsize=11)
    ax.set_ylabel("三判据", fontsize=10)
    ax.set_xscale("log")
    ax.set_xlim(1e5, 1e12)
    ax.set_ylim(0.6, 3.9)
    ax.set_yticks([])   # y 轴不用数字刻度（判据由图例说明）
    ax.set_title("人工场三判据 × 频率（D-T, B=9T）：最优=三带重叠区",
                 fontsize=12.5, color="#2c3e50", fontweight="bold", pad=12)
    ax.legend(loc="upper left", fontsize=6.7, framealpha=0.93,
              handlelength=1.4, borderpad=0.5)
    ax.grid(alpha=0.25, which="both", ls="--")

    fig.tight_layout()
    fig.savefig(os.path.join(OUT, "fig_field_triage.png"), dpi=160,
                bbox_inches="tight", facecolor=C_BG)
    plt.close(fig)
    print("wrote fig_field_triage.png")


# ---------------------------------------------------------------------------
# 图 3：成本-频率权衡
# ---------------------------------------------------------------------------
def draw_cost_freq():
    fig, ax = plt.subplots(figsize=(9, 6))
    fig.patch.set_facecolor(C_BG)
    ax.set_facecolor(C_BG)

    f = np.logspace(6, 10, 300)
    f_ref = f_ci(9.0)
    skin = np.sqrt(f / f_ref)
    cost = (f / f_ref) ** 0.9

    ax2 = ax.twinx()
    ax.plot(f, skin, color=C_EM, lw=2.2, label="趋肤/欧姆损耗 ∝ √f（左轴）")
    ax2.plot(f, cost, color=C_OPT, lw=2.2, ls="--", label="RF 电源相对成本(右轴)")
    ax.set_xscale("log")
    ax.set_yscale("log")
    ax2.set_yscale("log")

    ax.set_xlabel("频率（Hz）", fontsize=11)
    ax.set_ylabel("损耗系数（以 f_ci=1 归一）", fontsize=10)
    ax2.set_ylabel("RF 电源相对成本", fontsize=10)

    ax.axvspan(f_ci(1.0), 5 * f_ci(9.0), color=C_ART, alpha=0.18,
               label="VHF 最优区(便宜+损耗小)")
    ax.axvline(f_ci(9.0), color=C_CI, lw=1.6, ls="--")
    ax.axvline(5 * f_ci(9.0), color=C_CI, lw=1.6, ls="--")

    ax.set_title("人工场成本-频率权衡：VHF 最优（1-9T → 6-280MHz）",
                 fontsize=13, color="#2c3e50", fontweight="bold")
    h1, l1 = ax.get_legend_handles_labels()
    h2, l2 = ax2.get_legend_handles_labels()
    ax.legend(h1 + h2, l1 + l2, loc="upper left", fontsize=7.5, framealpha=0.92)
    ax.grid(alpha=0.25, which="both", ls="--")

    ax.annotate("VHF: 损耗小 + RF便宜", xy=(f_ci(3.0), 0.6),
                xytext=(f_ci(1.0) * 0.5, 1.4), fontsize=8, color=C_ART,
                arrowprops=dict(arrowstyle="->", color=C_ART, lw=0.9))
    ax.annotate("微波(GHz): 损耗大+贵", xy=(3e9, 7), xytext=(6e8, 3),
                fontsize=8, color=C_EM, arrowprops=dict(arrowstyle="->", color=C_EM, lw=0.9))

    fig.tight_layout()
    fig.savefig(os.path.join(OUT, "fig_cost_freq.png"), dpi=160,
                bbox_inches="tight", facecolor=C_BG)
    plt.close(fig)
    print("wrote fig_cost_freq.png")


if __name__ == "__main__":
    draw_rmf_window()
    draw_field_triage()
    draw_cost_freq()
    print("done ->", OUT)
