"""三股以上麻花辫 + 环本身的时空变化

leo（2026-09-29）：要「三股以上的麻花辫」以及「环本身也带时空变化」。

这一张把两件事画在一起（数字全部取自 artifacts/glueball_ring_twist/report.json 的 RT-D，
不是手填的）：

  ① 三股麻花环（q = 3）  s_k(θ) = c(θ) + a[cos(qθ + 2πk/3) e_r + sin(qθ + 2πk/3) e_z]
  ② 四股麻花环（q = 2）  同上，k = 0..3（m ≥ 3 才出现不可交换的编织生成元 σ1σ2 ≠ σ2σ1）
  ③ 环上的时空变化：沿环的环流 Φ(θ)（切向箭头）+ 绕环的自转（截面旋转箭头）
                     ⟹ 非零梯度 ∇Φ ⟹ 质量化（SG11 Φ = ½v²；MC1 质量 = 锚定）
  ④ 数值账（RT-D）：两两连接数 = q、成对总数 = C(m,2)·q、收敛性对照、三阶集体量缺口

产物：artifacts/glueball_ring_twist/fig_braid_ring_spacetime.png
"""

import json
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
ART = os.path.join(REPO, "artifacts", "glueball_ring_twist")
OUT = os.path.join(ART, "fig_braid_ring_spacetime.png")

C_INK, C_GREY, C_GREEN = "#202124", "#8d9199", "#1e8449"
STRAND_COLORS = ["#c0392b", "#2471a3", "#1e8449", "#8e44ad"]


def braid_strands(m, twist, n=1401, R=1.0, a=0.19):
    """m 股麻花环的每股曲线（与 verify 脚本同一公式）。"""
    th = np.linspace(0.0, 2.0 * math.pi, n)
    base = np.stack([R * np.cos(th), R * np.sin(th), np.zeros_like(th)], axis=1)
    e_r = np.stack([np.cos(th), np.sin(th), np.zeros_like(th)], axis=1)
    e_z = np.stack([np.zeros_like(th), np.zeros_like(th), np.ones_like(th)], axis=1)
    out = []
    for k in range(m):
        ph = twist * th + 2.0 * math.pi * k / m
        out.append(base + a * (np.cos(ph)[:, None] * e_r + np.sin(ph)[:, None] * e_z))
    return base, out


# 读 RT-D 实测数字（缺失就报错,不手填）
rp = os.path.join(ART, "report.json")
with open(rp, encoding="utf-8") as fh:
    rd = json.load(fh)["results"].get("RT_D_braid")
if rd is None:
    raise SystemExit("report.json 里没有 RT_D_braid —— 先跑 scripts/verify_glueball_ring_twist.py")
row_map = {(r["股数 m"], r["扭转 q"]): r for r in rd["rows"]}
r32 = row_map[(3, 2)]
r42 = row_map[(4, 2)]
conv = rd["收敛性 (4 股 q=2)"]

fig = plt.figure(figsize=(15.5, 10.4))
fig.patch.set_facecolor("white")

# ───────── ① 三股麻花环 ─────────
ax1 = fig.add_axes([0.010, 0.545, 0.31, 0.375], projection="3d")
ax1.set_title("① 三股麻花辫（m = 3，q = 3）\n两两连接数 = 3（实测）", fontsize=11.5, color=C_INK)
b3, s3 = braid_strands(3, 3, n=1201)
ax1.plot(b3[:, 0], b3[:, 1], b3[:, 2], "k--", lw=0.9)
for k, c in enumerate(s3):
    ax1.plot(c[:, 0], c[:, 1], c[:, 2], color=STRAND_COLORS[k], lw=2.1)
ax1.set_box_aspect((1, 1, 0.42)); ax1.view_init(elev=24, azim=-58); ax1.set_axis_off()
ax1.text2D(0.5, 0.02, "s_k(θ) = c(θ) + a[cos(qθ + 2πk/3) e_r + sin(qθ + 2πk/3) e_z]",
           transform=ax1.transAxes, fontsize=9.5, ha="center", color=C_INK)

# ───────── ② 四股麻花环 ─────────
ax2 = fig.add_axes([0.330, 0.545, 0.31, 0.375], projection="3d")
ax2.set_title("② 四股麻花辫（m = 4，q = 2）\n两两连接数 = 2；m ≥ 3 编织生成元不可交换", fontsize=11.5,
              color=C_INK)
b4, s4 = braid_strands(4, 2, n=1201)
ax2.plot(b4[:, 0], b4[:, 1], b4[:, 2], "k--", lw=0.9)
for k, c in enumerate(s4):
    ax2.plot(c[:, 0], c[:, 1], c[:, 2], color=STRAND_COLORS[k], lw=2.1)
ax2.set_box_aspect((1, 1, 0.42)); ax2.view_init(elev=24, azim=-58); ax2.set_axis_off()
ax2.text2D(0.5, 0.02, "σ1σ2σ3 生成的编织词：顺序不可交换（与 TD15–TD17 同源）",
           transform=ax2.transAxes, fontsize=9.5, ha="center", color=C_INK)

# ───────── ③ 环上的时空变化 ─────────
ax3 = fig.add_axes([0.660, 0.545, 0.330, 0.375], projection="3d")
ax3.set_title("③ 环本身也带时空的变化\n沿环的环流 Φ(θ) + 绕环的自转（标架转 q 圈）", fontsize=11.5,
              color=C_INK)
b3c, s3c = braid_strands(3, 3, n=801)
ax3.plot(b3c[:, 0], b3c[:, 1], b3c[:, 2], "k--", lw=1.1)
for k, c in enumerate(s3c):
    ax3.plot(c[:, 0], c[:, 1], c[:, 2], color=STRAND_COLORS[k], lw=1.2, alpha=0.35)

# (a) 沿环的环流:切向箭头（长度 ∝ 1 + 0.5cos2θ,示意流速的空间变化）
th_f = np.linspace(0.0, 2.0 * math.pi, 9)[:-1]
pf = np.stack([1.0 * np.cos(th_f), 1.0 * np.sin(th_f), np.zeros_like(th_f)], axis=1)
tf = np.stack([-np.sin(th_f), np.cos(th_f), np.zeros_like(th_f)], axis=1)
mag = 0.62 * (1.0 + 0.5 * np.cos(2.0 * th_f))
ax3.quiver(pf[:, 0], pf[:, 1], pf[:, 2], tf[:, 0] * mag, tf[:, 1] * mag, tf[:, 2] * mag,
           color="#e67e22", arrow_length_ratio=0.30, lw=2.6)
ax3.text2D(0.02, 0.92, "橙 = 沿环流动 Φ(θ)（切向,长度 ∝ 流速示意）", transform=ax3.transAxes,
           fontsize=9.5, color="#e67e22")

# (b) 绕环的自转:三个截面上的旋转箭头（截面圆 + 一周 8 个箭头）
for th0 in (0.0, 2.0 * math.pi / 3.0, 4.0 * math.pi / 3.0):
    cc = np.array([math.cos(th0), math.sin(th0), 0.0])
    er = np.array([math.cos(th0), math.sin(th0), 0.0])
    ez = np.array([0.0, 0.0, 1.0])
    phc = np.linspace(0.0, 2.0 * math.pi, 121)
    cyl = cc[None, :] + 0.42 * (np.cos(phc)[:, None] * er[None, :] +
                                np.sin(phc)[:, None] * ez[None, :])
    ax3.plot(cyl[:, 0], cyl[:, 1], cyl[:, 2], color="#7f8c8d", lw=1.0, alpha=0.8)
    ph = np.linspace(0.0, 2.0 * math.pi, 9)[:-1]
    for p0 in ph:
        pos = cc + 0.42 * (math.cos(p0) * er + math.sin(p0) * ez)
        dirv = (-math.sin(p0) * er + math.cos(p0) * ez)
        ax3.quiver([pos[0]], [pos[1]], [pos[2]], [0.22 * dirv[0]], [0.22 * dirv[1]],
                   [0.22 * dirv[2]], color="#7f8c8d", arrow_length_ratio=0.55, lw=1.8)
ax3.text2D(0.02, 0.85, "灰 = 截面上的自转（每绕环一圈转 q 圈 = 扭转率）", transform=ax3.transAxes,
           fontsize=9.5, color="#7f8c8d")
ax3.text2D(0.5, 0.02, "两层变化 ⟹ ∇Φ ≠ 0 ⟹ 质量化（SG11: Φ = ½v²；MC1: 质量 = 锚定）\n"
                      "（箭头长度是示意：只表示存在空间变化,不是算出来的场；股线画淡以便看箭头）",
           transform=ax3.transAxes, fontsize=9.2, ha="center", color=C_INK)
ax3.set_box_aspect((1, 1, 0.62)); ax3.view_init(elev=26, azim=-60)
ax3.set_xlim(-1.7, 1.7); ax3.set_ylim(-1.7, 1.7); ax3.set_zlim(-1.3, 1.3)
ax3.set_axis_off()

# ───────── ④ 数值账（RT-D） ─────────
ax4 = fig.add_axes([0.075, 0.075, 0.40, 0.375])
ax4.set_title("④ 数值账（RT-D，Gauss 双积分实测，非手填）", fontsize=11.5, color=C_INK)
ax4.set_axis_off()
lines = [
    "m 股两两连接数（自连接/framing 口径）：",
    f"  m = 2, q = 1  ⟹  Lk = {row_map[(2, 1)]['两两连接数'][0]:+.4f}   （应 = +1）",
    f"  m = 2, q = 2  ⟹  Lk = {row_map[(2, 2)]['两两连接数'][0]:+.4f}   （应 = +2）",
    f"  m = 3, q = 2  ⟹  3 对 = {[round(v, 3) for v in r32['两两连接数']]}",
    f"  m = 4, q = 2  ⟹  6 对 = {[round(v, 3) for v in r42['两两连接数']]}",
    f"  m = 4, q = 2，N=1401 时 max|Lk − q| = {r42['max|Lk − q|']:.4f}",
    f"                  N=2801 时 max|Lk − q| = {conv['N=2801']:.4f}  （加密 ⟹ 离散误差）",
    "",
    "成对连接总数 Σ_{i<j} Lk = C(m,2)·q：",
    f"  m = 3, q = 2  ⟹  {rd['成对连接总数 Σ_{i<j} Lk']['m=3, q=2']:.0f}",
    f"  m = 4, q = 2  ⟹  {rd['成对连接总数 Σ_{i<j} Lk']['m=4, q=2']:.0f}",
    "",
    "μ = 1 − |Lk_net| / |Lk_gross|：",
    "  残余 1 个连接单位 ⟹ 毛连接数 ≈ 4558（FC11 地板 2.194e-4 的读法）",
    "  两两看得见的部分 = C(m,2)·q；三阶集体量 μ̄₃ 本脚本无数值算法（缺口）",
]
for i, t in enumerate(lines):
    ax4.text(0.02, 0.95 - i * 0.062, t, transform=ax4.transAxes, fontsize=9.6,
             color=C_INK if not t.startswith("  ") else "#333333", va="top")

fig.text(0.5, 0.977, "三股以上麻花辫 + 环本身的时空变化（几何与连接数都由公式算出）",
         fontsize=13.5, ha="center", color=C_INK)
fig.text(0.075, 0.032,
         "诚实边界：两两连接数是 Gauss 双积分实测（偏差 1e-3–1e-2 为离散化，加密后下降）· Lk = Tw + Wr 是经典定理（本页只做数值复核）\n"
         "「扭转 → 条数 N」与「梯度 → 质量化」是模型选择/结构对应，选择规则未导出 · ③ 的箭头长度为示意（不是算出来的场）· M₀ = 0.93 GeV 仍是标定",
         fontsize=8.8, color=C_INK, linespacing=1.5)

fig.savefig(OUT, dpi=130, facecolor="white")
plt.close(fig)
print(f"图 → {OUT}")
print(f"尺寸: {os.path.getsize(OUT)} bytes")
