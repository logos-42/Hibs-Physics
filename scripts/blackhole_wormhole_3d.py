#!/usr/bin/env python3
"""黑洞与虫洞的 3D 流动结构可视化（空间流动假设）

  blackhole_3d.png     黑洞 = 空间内向流动漏斗 + 视界球 + 光子轨迹
  wormhole_3d.png      虫洞 = 双漏斗嵌入面（Morris–Thorne）+ 流线 + 喉部
  wormhole_traverse.gif 光子随空间流动穿越虫洞（dτ ≡ 0 全程）

物理：视界 = v = c 面（BH1）；向外光子视界处冻结（BH3）；
虫洞 = 亚光速流管通道（喉部 v 峰值 < c，WH1）。
"""
import os

import numpy as np
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
import matplotlib.font_manager as fm
from mpl_toolkits.mplot3d import Axes3D  # noqa: F401
from mpl_toolkits.mplot3d.art3d import Poly3DCollection
from matplotlib.animation import FuncAnimation, PillowWriter

for _fp in ("/System/Library/Fonts/PingFang.ttc",
            "/System/Library/Fonts/Hiragino Sans GB.ttc"):
    if os.path.exists(_fp):
        fm.fontManager.addfont(_fp)
        plt.rcParams["font.sans-serif"] = [fm.FontProperties(fname=_fp).get_name()]
        break
plt.rcParams["axes.unicode_minus"] = False

OUT = os.path.join(os.path.dirname(__file__), "..", "artifacts", "blackhole")
os.makedirs(OUT, exist_ok=True)

RS = 1.0


# ---------- 黑洞 ----------

def blackhole_3d():
    fig = plt.figure(figsize=(9, 8))
    ax = fig.add_subplot(111, projection="3d")
    # 内向流动箭头：v ∝ 1/√r（径向向内，强度随 r 增大而减小）
    rs = np.linspace(1.3, 3.0, 5)
    phis = np.linspace(0, 2 * np.pi, 8, endpoint=False)
    thetas = np.linspace(0.3, np.pi - 0.3, 4)
    R, P, T = np.meshgrid(rs, phis, thetas, indexing="ij")
    X = R * np.sin(T) * np.cos(P)
    Y = R * np.sin(T) * np.sin(P)
    Z = R * np.cos(T)
    U = -X / np.maximum(R, 1e-9) * (1.0 / np.sqrt(R))
    V = -Y / np.maximum(R, 1e-9) * (1.0 / np.sqrt(R))
    W = -Z / np.maximum(R, 1e-9) * (1.0 / np.sqrt(R))
    ax.quiver(X, Y, Z, U, V, W, length=0.4, color="steelblue", alpha=0.5,
              normalize=True, linewidth=0.9)
    # 视界球（v = c 面，半透明红）
    u = np.linspace(0, 2 * np.pi, 40)
    vv = np.linspace(0, np.pi, 40)
    Xs = RS * np.outer(np.cos(u), np.sin(vv))
    Ys = RS * np.outer(np.sin(u), np.sin(vv))
    Zs = RS * np.outer(np.ones_like(u), np.cos(vv))
    ax.plot_surface(Xs, Ys, Zs, color="red", alpha=0.22, linewidth=0)
    # 视界环标注
    th = np.linspace(0, 2 * np.pi, 60)
    ax.plot(RS * np.cos(th), RS * np.sin(th), np.zeros_like(th),
            color="red", lw=2)
    ax.text(1.35, 0, 0, "视界 r_s（v = c）", color="red", fontsize=9)
    # 光子轨迹：外部从 r=3 落向视界（冻结）；内部虚线继续向奇点
    r_ext = np.linspace(3.0, RS, 200)
    ax.plot(r_ext, np.zeros_like(r_ext), np.zeros_like(r_ext),
            color="gold", lw=2.5, label="向外光子（外部：落到视界冻结）")
    ax.scatter([3.0], [0], [0], s=60, color="gold", depthshade=False)
    r_int = np.linspace(RS, 0.15, 100)
    ax.plot(r_int, np.zeros_like(r_int), np.zeros_like(r_int),
            color="gold", ls="--", lw=1.8, label="内部：超光速流拖向奇点")
    ax.scatter([0], [0], [0], s=120, color="black", depthshade=False, zorder=10)
    ax.text(0.1, 0.1, -0.2, "奇点", fontsize=9)
    ax.set_xlim(-3.2, 3.2)
    ax.set_ylim(-3.2, 3.2)
    ax.set_zlim(-3.2, 3.2)
    ax.set_xlabel("x")
    ax.set_ylabel("y")
    ax.set_zlabel("z")
    ax.view_init(elev=22, azim=-60)
    ax.set_title("黑洞 = 空间内向流动漏斗\n"
                 "（箭头 = 空间流动 v(r)=√(r_s/r)；红球 = 光速面视界）")
    ax.legend(loc="upper left", fontsize=8)
    fig.tight_layout()
    fig.savefig(os.path.join(OUT, "blackhole_3d.png"), dpi=150)
    plt.close(fig)
    print("→", os.path.join(OUT, "blackhole_3d.png"))


# ---------- 虫洞 ----------

def mt_embed(r, r0=0.6):
    """Morris–Thorne 嵌入函数：z(r) = 2√(r₀)·√(r − r₀)（双漏斗）。"""
    return 2.0 * np.sqrt(r0) * np.sqrt(np.maximum(r - r0, 0.0))


def wormhole_3d():
    fig = plt.figure(figsize=(9, 8))
    ax = fig.add_subplot(111, projection="3d")
    r0 = 0.6
    r = np.linspace(r0, 2.6, 80)
    phi = np.linspace(0, 2 * np.pi, 60)
    R, P = np.meshgrid(r, phi, indexing="ij")
    X = R * np.cos(P)
    Y = R * np.sin(P)
    Zp = mt_embed(R, r0)
    ax.plot_surface(X, Y, Zp, color="steelblue", alpha=0.30, linewidth=0)
    ax.plot_surface(X, Y, -Zp, color="steelblue", alpha=0.30, linewidth=0)
    # 喉部环（v 峰值处）
    th = np.linspace(0, 2 * np.pi, 60)
    ax.plot(r0 * np.cos(th), r0 * np.sin(th), np.zeros_like(th),
            color="orange", lw=2.5)
    ax.text(0.95, 0, 0.15, "喉部 r₀（v 峰值 < c，可穿越）",
            color="darkorange", fontsize=9)
    # 流线：从一侧渐近区穿过喉部到另一侧（空间流动方向 +s）
    s = np.linspace(-3.2, 3.2, 60)
    for off in (-0.45, 0.0, 0.45):
        # 沿通道的流线：x = off（喉部收缩），嵌入面外? 简化：沿 +x 方向的管
        pass
    # 用嵌入面的径向流线：从 (2.4, 0, ±z(2.4)) 沿表面到喉部
    rs_line = np.linspace(2.4, r0, 60)
    for sign, col in ((1, "#1f77b4"), (-1, "#d62728")):
        x = rs_line
        y = np.zeros_like(rs_line)
        z = sign * mt_embed(rs_line, r0)
        ax.plot(x, y, z, color=col, lw=2.2)
    # 流线箭头（沿通道 +s：从 −z 侧到 +z 侧）
    s_arr = np.linspace(-2.0, 2.0, 9)
    for sa in s_arr:
        # 流管轴线（简化画在 y=0 平面上方通道）
        ax.quiver(sa, 0, 0.25, 0.35, 0, 0, color="steelblue",
                  alpha=0.7, arrow_length_ratio=0.5, linewidth=1.0)
    ax.text(0, 0, 2.4, "渐近区 A（空间流入）", fontsize=9, color="#1f77b4")
    ax.text(0, 0, -2.4, "渐近区 B（空间流出）", fontsize=9, color="#d62728")
    ax.set_xlim(-3.0, 3.0)
    ax.set_ylim(-2.6, 2.6)
    ax.set_zlim(-2.6, 2.6)
    ax.set_xlabel("通道坐标 s")
    ax.set_ylabel("y")
    ax.set_zlabel("z（嵌入方向）")
    ax.view_init(elev=25, azim=-70)
    ax.set_title("虫洞 = 亚光速流管通道（双漏斗嵌入）\n"
                 "（流线从 A 穿过喉部到 B；喉部 v 峰值 < c 无冻结）")
    fig.tight_layout()
    fig.savefig(os.path.join(OUT, "wormhole_3d.png"), dpi=150)
    plt.close(fig)
    print("→", os.path.join(OUT, "wormhole_3d.png"))


# ---------- 虫洞穿越动画 ----------

def wormhole_traverse():
    fig = plt.figure(figsize=(9, 7))
    ax = fig.add_subplot(111, projection="3d")
    r0 = 0.6

    def draw_base():
        r = np.linspace(r0, 2.6, 60)
        phi = np.linspace(0, 2 * np.pi, 50)
        R, P = np.meshgrid(r, phi, indexing="ij")
        X = R * np.cos(P)
        Y = R * np.sin(P)
        Zp = mt_embed(R, r0)
        ax.plot_surface(X, Y, Zp, color="steelblue", alpha=0.18, linewidth=0)
        ax.plot_surface(X, Y, -Zp, color="steelblue", alpha=0.18, linewidth=0)
        th = np.linspace(0, 2 * np.pi, 60)
        ax.plot(r0 * np.cos(th), r0 * np.sin(th), np.zeros_like(th),
                color="orange", lw=2)
        ax.plot([-2.8, 2.8], [0, 0], [0, 0], color="gray", ls=":", lw=0.8)
        ax.text(-2.6, 0.25, 0, "A（流入）", color="#1f77b4", fontsize=9)
        ax.text(2.3, 0.25, 0, "B（流出）", color="#d62728", fontsize=9)
        ax.set_xlim(-3.0, 3.0)
        ax.set_ylim(-2.4, 2.4)
        ax.set_zlim(-2.4, 2.4)
        ax.set_xlabel("通道坐标 s")
        ax.set_ylabel("y")
        ax.set_zlabel("z（嵌入）")
        ax.view_init(elev=20, azim=-75)

    draw_base()
    (line,) = ax.plot([], [], [], color="gold", lw=3, alpha=0.95)
    (tail,) = ax.plot([], [], [], color="gold", lw=6, alpha=0.25)
    ax.set_title("光子随空间流动穿越虫洞：全程 dτ = 0（零时通道）")

    def update(frame):
        s_pos = -2.6 + frame * (5.2 / 90)
        z_ph = mt_embed(max(abs(s_pos), r0), r0) * (1 if s_pos > 0 else -1)
        # 路径：光子沿通道 +s，嵌入高度随 |s| 变化（喉部最低）
        tail_n = 18
        ss = np.linspace(max(-2.6, s_pos - 1.2), s_pos, tail_n)
        zz = np.array([mt_embed(max(abs(s_), r0), r0) * (1 if s_ > 0 else -1)
                       for s_ in ss])
        tail.set_data(ss, np.zeros_like(ss))
        tail.set_3d_properties(zz)
        line.set_data([s_pos], [0])
        line.set_3d_properties([z_ph])
        return [line, tail]

    anim = FuncAnimation(fig, update, frames=90, interval=50, blit=False)
    anim.save(os.path.join(OUT, "wormhole_traverse.gif"),
              writer=PillowWriter(fps=15))
    plt.close(fig)
    print("→", os.path.join(OUT, "wormhole_traverse.gif"))


if __name__ == "__main__":
    blackhole_3d()
    wormhole_3d()
    wormhole_traverse()
