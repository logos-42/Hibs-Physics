"""胶球环扭转 —— 「我对 leo 的环形螺旋扭转的理解」概念图（非数据图）

leo（2026-09-29）：希望在原扭量数学上做环扭转，形成比普通螺旋线圈更扭转的
「扭量螺旋环」；环本身也带时空的变化 ⟹ 或许能解释胶球质量来源。

本图画的是助手读到的东西（四格 + 一行诚实边界），不是新数据：
  ① 环 + 标架 ⟹ Lk = Tw + Wr；半整数扭转 ⟹ 2π 回 −1 ⟹ 自旋
  ② 三方向 = 三环，关键在集体：两两连接 0、整体不平凡（Borromean / μ̄₃）
  ③ 条数阶梯 N = Σnᵢ² + |μ̄₃| ⟹ {3,6,7} → 1.611/2.278/2.461 GeV（对上格点区间）
  ④ 同一条扭环几何同时给出 N（质量²）与 μ（抵消度）⟹ 过度决定检验
  底：诚实边界（模型选择 / 选择规则未导出 / M₀ 仍标定 / Lk=Tw+Wr 是经典定理）

产物：artifacts/glueball_ring_twist/fig_understanding_ring_twist.png
"""

import math
import os

import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt
import matplotlib.font_manager as fm
import numpy as np
from matplotlib.patches import Circle, FancyArrowPatch, FancyBboxPatch

for _fp in ("/System/Library/Fonts/PingFang.ttc",
            "/System/Library/Fonts/Hiragino Sans GB.ttc"):
    if os.path.exists(_fp):
        fm.fontManager.addfont(_fp)
        plt.rcParams["font.sans-serif"] = [fm.FontProperties(fname=_fp).get_name()]
        break
plt.rcParams["axes.unicode_minus"] = False

REPO = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
OUT = os.path.join(REPO, "artifacts", "glueball_ring_twist",
                   "fig_understanding_ring_twist.png")

C_RED, C_BLUE, C_INK, C_GREY, C_GREEN = "#c0392b", "#2471a3", "#202124", "#8d9199", "#1e8449"

fig = plt.figure(figsize=(15.0, 10.2))
fig.patch.set_facecolor("white")

# ───────────────────── ① 环 + 标架（2D 示意：投影成「带」） ─────────────────────
ax1 = fig.add_axes([0.030, 0.500, 0.285, 0.350])
ax1.set_title("① 环 + 标架：扭转是可数的\nLk = Tw + Wr（Călugăreanu–White–Fuller）",
              fontsize=11.5, color=C_INK)
t = np.linspace(0, 2 * math.pi, 1201)
r1 = 1.0 + 0.135 * np.cos(3.0 * t)
r2 = 1.0 - 0.135 * np.cos(3.0 * t)
ax1.plot(r1 * np.cos(t), r1 * np.sin(t), color=C_RED, lw=2.0)
ax1.plot(r2 * np.cos(t), r2 * np.sin(t), color=C_BLUE, lw=2.0)
ax1.plot(1.0 * np.cos(t), 1.0 * np.sin(t), "k--", lw=0.9)
ax1.text(0, 0, "ribbon\n（环是有宽度的带，\n不是一条线）", fontsize=9, ha="center",
         va="center", color=C_INK)
ax1.text(0, 1.62, "Tw = 3（整数圈扭转）", fontsize=10, ha="center", color=C_RED)
ax1.text(0, 1.38, "Wr = 0（平面环不自拧）→ Lk = 3", fontsize=10, ha="center", color=C_BLUE)
ax1.text(0, -1.50, "扭转取半整数时：转 2π 回到 −1 ⟹ 自旋结构（RT5）", fontsize=9.5,
         ha="center", color=C_INK)
ax1.text(0, -1.80, "Lk、Tw、Wr 都是整数/半整数 ⟹ 可数（这就是「数条数」）", fontsize=9,
         ha="center", color=C_GREY)
ax1.set_xlim(-1.65, 1.65); ax1.set_ylim(-2.0, 1.82); ax1.set_aspect("equal")
ax1.set_axis_off()

# ───────────────────── ② 三环集体（Borromean） ─────────────────────
ax2 = fig.add_axes([0.345, 0.500, 0.285, 0.350])
ax2.set_title("② 三方向 = 三个环：关键在「集体」\n两两连接数 = 0，整体不平凡（Borromean）",
              fontsize=11.5, color=C_INK)
for k, (dx, dy) in enumerate([(0.0, 0.60), (-0.52, -0.32), (0.52, -0.32)]):
    ax2.add_patch(Circle((dx, dy), 0.60, fill=False, lw=2.0,
                         color=[C_RED, C_BLUE, C_GREEN][k]))
    ax2.text(dx, dy, ["环 1", "环 2", "环 3"][k], fontsize=9.5, ha="center", va="center",
             color=[C_RED, C_BLUE, C_GREEN][k])
ax2.text(0, -1.30, "两两连接数 = 0（谁也扣不住谁）\n三重积 μ̄₃ = 1（整体被锁住）",
         fontsize=9.5, ha="center", color=C_INK)
ax2.text(0, 1.42, "与 SH3 同构：非对角项被反对称消灭，整体 = 3I", fontsize=9.5, ha="center",
         color=C_GREEN)
ax2.text(0, 1.20, "⟹ 集体整数只有 0 / 1 两种取值（可数）", fontsize=9.5, ha="center",
         color=C_GREEN)
ax2.set_xlim(-1.30, 1.30); ax2.set_ylim(-1.72, 1.72); ax2.set_aspect("equal")
ax2.set_axis_off()

# ───────────────────── ③ 条数阶梯 ─────────────────────
ax3 = fig.add_axes([0.030, 0.130, 0.44, 0.300])
ax3.set_title("③ 条数阶梯：N = Σnᵢ² + |μ̄₃|（集体型）⟹ {3, 6, 7}",
              fontsize=11.5, color=C_INK)
ladder = [("0++", 3, "1.611", (1, 1, 1, 0), (1.475, 1.75)),
          ("2++", 6, "2.278", (2, 1, 1, 0), (2.15, 2.40)),
          ("0-+", 7, "2.461", (2, 1, 1, 1), (2.30, 2.60))]
for i, (st, N, mv, impl, (lo, hi)) in enumerate(ladder):
    ax3.fill_betweenx([i - 0.32, i + 0.32], lo, hi, color=C_GREY, alpha=0.40)
    ax3.plot([float(mv)], [i], "o", color=C_RED, ms=9)
    ax3.text(float(mv) + 0.035, i, f"{st}  N = {N}  →  {mv} GeV", fontsize=10.5, va="center",
             color=C_INK)
    ax3.text(1.425, i, f"(n₁,n₂,n₃,μ̄₃) = {impl}", fontsize=8.5, va="center", color=C_GREY)
ax3.set_yticks([]); ax3.set_xlim(1.40, 2.72); ax3.set_ylim(-0.95, 2.75)
ax3.set_xlabel("m = √N·M₀ (GeV)，M₀ = 0.93（标定值）", fontsize=9.5)
ax3.grid(alpha=0.25, axis="x")
ax3.text(1.425, -0.72, "被排除：N = 4（变体 I 多出的 1.86 GeV 奇宇称态）", fontsize=8.5,
         color=C_INK)
ax3.text(2.70, -0.72, "灰带 = 格点观测区间（只比比值）", fontsize=8.5, ha="right",
         color=C_GREY)

# ───────────────────── ④ 过度决定 ─────────────────────
ax4 = fig.add_axes([0.520, 0.130, 0.455, 0.300])
ax4.set_title("④ 同一条扭环几何同时给出 N（质量²）与 μ（抵消度）",
              fontsize=11.5, color=C_INK)
ax4.add_patch(FancyBboxPatch((0.015, 0.42), 0.19, 0.22, boxstyle="round,pad=0.012",
                             fc="#fdecea", ec=C_RED, lw=1.6))
ax4.text(0.11, 0.53, "扭转角 θ\n（环被扭多少）", fontsize=10, ha="center", va="center",
         color=C_INK)
for y, lab, col, detail in [
        (0.72, "条数 N(θ)  ⟹  m² = N·M₀²", C_RED, "对上胶球阶梯 3 / 6 / 7（格点区间）"),
        (0.22, "抵消度 μ(θ) = 1 − |Lk_net| / |Lk_gross|", C_BLUE,
         "对上 FRC 窗口；FC11 地板 2.194e-4 ⟹ 毛连接数 ≈ 4558")]:
    ax4.add_patch(FancyBboxPatch((0.42, y - 0.105), 0.565, 0.21,
                                 boxstyle="round,pad=0.012", fc="#f4f8fb", ec=col, lw=1.6))
    ax4.text(0.702, y + 0.048, lab, fontsize=10, ha="center", va="center", color=col)
    ax4.text(0.702, y - 0.048, detail, fontsize=9, ha="center", va="center", color=C_INK)
    ax4.add_patch(FancyArrowPatch((0.215, 0.53), (0.41, y), arrowstyle="-|>",
                                  mutation_scale=13, color=col, lw=1.5))
ax4.text(0.702, 0.055, "过度决定：同一个 θ 要同时对上两件事\n任一边错了，另一边都会把它抓住",
         fontsize=9.5, ha="center", va="center", color=C_GREEN)
ax4.text(0.702, 0.945, "左边是「生成」，右边是「记账」—— 两条都要接上账本才算数",
         fontsize=9, ha="center", va="center", color=C_GREY)
ax4.set_xlim(0, 1); ax4.set_ylim(0, 1); ax4.set_axis_off()

fig.text(0.5, 0.975, "leo 的「环形螺旋扭转」—— 助手读到的东西（2026-09-29）",
         fontsize=14, ha="center", color=C_INK)
fig.text(0.030, 0.028,
         "诚实边界：质量 = 两扭量的辛内积（Penrose 标准结果，本页未改）· Lk = Tw + Wr 是经典定理（本页只做数值复核："
         "平面残差 1.3e-2、非平面 ΔLk ≈ 0.98–0.99/圈）\n"
         "「扭转 → N」是模型选择：只否掉了对角模型（三个独立绕数取不到 7，Legendre 三平方定理）、给出最小集体实现，"
         "选择规则仍未导出 · M₀ = 0.93 GeV 仍是标定 · 与格点只比比值（不是预言）· 不含 QCD 推导",
         fontsize=8.8, color=C_INK, linespacing=1.55)

fig.savefig(OUT, dpi=130, facecolor="white")
plt.close(fig)
print(f"图 → {OUT}")
print(f"尺寸: {os.path.getsize(OUT)} bytes")
