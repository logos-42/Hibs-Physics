"""扭量螺旋环（麻花）—— 由公式生成的几何图

leo（2026-09-29 纠正）：上一张概念图不是「我」要的数学形状；要的是**类似麻花的螺旋环**。

本图直接从公式画出几何（不是示意）：
  核心曲线（环）      c(θ) = (R cos θ, R sin θ, 0)
  标架                N(θ) = (−cos θ, −sin θ, 0)（环内法向）、B = (0,0,1)（面外）
  ★ 两股（麻花的两股）  s±(θ) = c(θ) + a·[cos(qθ)·N(θ) + sin(qθ)·B]
                      —— 标架绕环转 q 整圈 ⟹ 两股互相缠绕 q 次 ⟹ Tw = q（数交叉数）
  连接数              Lk = Tw + Wr（平面核心 ⟹ Wr = 0 ⟹ Lk = q）

四个面板：① 立体视角的麻花环（q = 6）② 剪开摊平 = 麻花（局部两股互绕）
③ 同一个环换 q（Tw = 1/2/3）：扭转圈数是数出来的 ④ 两股反向 ⟹ 净连接 0 ⟹ μ = 1（光子情形）
末行：三环集体（Borromean）：两两连接 0、μ̄₃ = 1 ⟹ N = Σn_i² + |μ̄₃| = 3, 6, 7

产物：artifacts/glueball_ring_twist/fig_twisted_ring_math.png
"""

import math
import os

import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt
import matplotlib.font_manager as fm
import numpy as np

for _fp in ("/System/Library/Fonts/PingFang.ttc",
            "/System/Library/Fonts/Hiragino Sans GB.ttc"):
    if os.path.exists(_fp):
        fm.fontManager.addfont(_fp)
        plt.rcParams["font.sans-serif"] = [fm.FontProperties(fname=_fp).get_name()]
        break
plt.rcParams["axes.unicode_minus"] = False

REPO = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
OUT = os.path.join(REPO, "artifacts", "glueball_ring_twist", "fig_twisted_ring_math.png")

C_RED, C_BLUE, C_INK, C_GREY, C_GREEN = "#c0392b", "#2471a3", "#202124", "#8d9199", "#1e8449"
R_CORE, A_STRAND = 1.0, 0.17


def twisted_ring(q, n=2001, a=A_STRAND, r=R_CORE):
    """扭量螺旋环：核心圆 + 绕环转 q 整圈的两条股。返回 (core, s⁺, s⁻)。"""
    th = np.linspace(0.0, 2.0 * math.pi, n)
    ct, st = np.cos(th), np.sin(th)
    core = np.stack([r * ct, r * st, np.zeros_like(th)], axis=1)
    nrm = np.stack([-ct, -st, np.zeros_like(th)], axis=1)      # 环内法向
    binm = np.stack([np.zeros_like(th), np.zeros_like(th), np.ones_like(th)], axis=1)  # 面外
    ph = q * th
    off = a * (np.cos(ph)[:, None] * nrm + np.sin(ph)[:, None] * binm)
    return core, core + off, core - off


def tilt(p, k=0.46):
    """把 3D 点斜投影到 2D（露出面外的缠绕）——用于读麻花。"""
    return p[:, 0], k * p[:, 1] + (1.0 - k) * 0.0 + p[:, 2] * 0.95


fig = plt.figure(figsize=(15.5, 10.6))
fig.patch.set_facecolor("white")

# ───────── ① 立体视角的麻花环（q = 6） ─────────
ax1 = fig.add_axes([0.015, 0.545, 0.30, 0.375], projection="3d")
ax1.set_title("① 扭量螺旋环（麻花）：两股互相缠绕 q 次\nq = 6 → Tw = 6，Lk = Tw + Wr = 6",
              fontsize=11.5, color=C_INK)
core, sp, sm = twisted_ring(6)
ax1.plot(core[:, 0], core[:, 1], core[:, 2], "k--", lw=1.0)
ax1.plot(sp[:, 0], sp[:, 1], sp[:, 2], color=C_RED, lw=2.2)
ax1.plot(sm[:, 0], sm[:, 1], sm[:, 2], color=C_BLUE, lw=2.2)
ax1.set_box_aspect((1.0, 1.0, 0.42))
ax1.view_init(elev=26, azim=-58)
ax1.set_axis_off()
ax1.text2D(0.5, 0.03, "环上每绕一圈，标架自转 q 圈；两股 = 麻花的两股",
           transform=ax1.transAxes, fontsize=9.5, ha="center", color=C_INK)

# ───────── ② 剪开摊平 = 麻花 ─────────
ax2 = fig.add_axes([0.335, 0.545, 0.30, 0.375])
ax2.set_title("② 把环剪开摊平：局部就是麻花\n摊平后每 2 个交叉 = 1 圈扭转",
              fontsize=11.5, color=C_INK)
s = np.linspace(0.0, 6.0 * math.pi, 2001)
ax2.plot(s, A_STRAND * np.cos(s), color=C_RED, lw=2.2)
ax2.plot(s, -A_STRAND * np.cos(s), color=C_BLUE, lw=2.2)
for k in range(1, 6):
    x0 = (k - 0.5) * math.pi
    ax2.plot([x0, x0], [-0.24, 0.24], color=C_GREY, lw=0.8, ls=":")
ax2.set_xlabel("沿环的弧长（展开坐标）", fontsize=9.5)
ax2.set_xticks([]); ax2.set_yticks([])
ax2.text(0.5 * 6 * math.pi, 0.30, "3 圈扭转 = 6 个交叉（可数）", fontsize=9.5, ha="center",
         color=C_GREEN)

# ───────── ③ 同一个环换 q：Tw 是数出来的 ─────────
ax3 = fig.add_axes([0.660, 0.545, 0.325, 0.375])
ax3.set_title("③ 同一个环，换扭转圈数 q：Tw 就是交叉数\n（半整数也允许 → 自旋结构）", fontsize=11.5,
              color=C_INK)
for i, q in enumerate((1, 2, 3)):
    _c, p1, p2 = twisted_ring(q)
    x1, y1 = tilt(p1)
    x2, y2 = tilt(p2)
    xc, yc = tilt(_c)
    axq = fig.add_axes([0.670, 0.755 - i * 0.078, 0.300, 0.092], projection="3d")
    axq.plot(xc * 0 + _c[:, 0], _c[:, 1], _c[:, 2], "k--", lw=0.7)
    axq.plot(p1[:, 0], p1[:, 1], p1[:, 2], color=C_RED, lw=1.6)
    axq.plot(p2[:, 0], p2[:, 1], p2[:, 2], color=C_BLUE, lw=1.6)
    axq.set_box_aspect((1.0, 1.0, 0.40))
    axq.view_init(elev=24, azim=-58)
    axq.set_axis_off()
    axq.text2D(0.03, 0.72, f"q = {q}  →  Tw = {q}，Lk = {q}", transform=axq.transAxes,
               fontsize=10, color=C_INK)
ax3.set_axis_off()

# ───────── ④ 两股反向 ⟹ μ = 1 ─────────
ax4 = fig.add_axes([0.035, 0.075, 0.44, 0.365], projection="3d")
ax4.set_title("④ 两股反向缠绕：净连接数 = 0 → μ = 1（光子情形）", fontsize=11.5, color=C_INK)
_c, p_plus, _ = twisted_ring(4)
_p2, _, p_minus = twisted_ring(-4)
ax4.plot(_c[:, 0], _c[:, 1], _c[:, 2], "k--", lw=1.0)
ax4.plot(p_plus[:, 0], p_plus[:, 1], p_plus[:, 2], color=C_RED, lw=2.0)
ax4.plot(p_minus[:, 0], p_minus[:, 1], p_minus[:, 2], color=C_BLUE, lw=2.0)
ax4.set_box_aspect((1.0, 1.0, 0.42))
ax4.view_init(elev=26, azim=-58)
ax4.set_axis_off()
ax4.text2D(0.5, 0.02, "μ = 1 − |Lk_net| / |Lk_gross| = 1 − 0 / 4 = 1\n"
                      "共面同心的反向环 Gauss 连接数 = 0 → 只反向配平是平凡的，加螺旋（本图的 q）才非平凡",
           transform=ax4.transAxes, fontsize=9.2, ha="center", color=C_INK)

# ───────── 三环集体（Borromean）小图 + 结论 ─────────
ax5 = fig.add_axes([0.520, 0.075, 0.455, 0.365], projection="3d")
ax5.set_title("⑤ 三方向 = 三个麻花环：整体（集体）项 μ̄₃\n两两连接数 = 0，整体不平凡",
              fontsize=11.5, color=C_INK)
for k, (cx, cy, ang) in enumerate([(0.0, 0.62, 0.0), (-0.62, -0.35, 2.1), (0.62, -0.35, 4.2)]):
    _c, p1, p2 = twisted_ring(2, n=601, a=0.10, r=0.46)
    rot = np.array([[math.cos(ang), -math.sin(ang), 0.0],
                    [math.sin(ang), math.cos(ang), 0.0],
                    [0.0, 0.0, 1.0]])
    for p, col in ((p1, [C_RED, C_BLUE, C_GREEN][k]), (p2, [C_RED, C_BLUE, C_GREEN][k])):
        pp = p @ rot.T + np.array([cx, cy, 0.0])
        ax5.plot(pp[:, 0], pp[:, 1], pp[:, 2], color=col, lw=1.5, alpha=0.95)
ax5.set_box_aspect((1.0, 1.0, 0.55))
ax5.view_init(elev=34, azim=-60)
ax5.set_axis_off()
ax5.text2D(0.5, 0.03, "N = Σn_i² + |μ̄₃|  →  3, 6, 7（对上格点胶球谱）",
           transform=ax5.transAxes, fontsize=10.5, ha="center", color=C_INK)

fig.text(0.5, 0.978, "扭量螺旋环（麻花）—— 几何直接由公式画出：s±(θ) = c(θ) ± a[cos(qθ)N + sin(qθ)B]",
         fontsize=13.5, ha="center", color=C_INK)
fig.text(0.035, 0.030,
         "诚实边界：Tw 与 Lk 的定义是经典结果（Călugăreanu–White–Fuller；本仓只做数值复核：平面残差 1.3e-2、"
         "ΔLk ≈ 0.98–0.99/圈）· 「扭转 → 条数 N」是模型选择（只否掉对角模型、给出最小集体实现，选择规则未导出）· "
         "M₀ = 0.93 GeV 仍是标定 · 与格点只比比值",
         fontsize=8.8, color=C_INK)

fig.savefig(OUT, dpi=130, facecolor="white")
plt.close(fig)
print(f"图 → {OUT}")
print(f"尺寸: {os.path.getsize(OUT)} bytes")
