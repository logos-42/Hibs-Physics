#!/usr/bin/env python3
"""三维光线模型：流动空间中的双螺旋纠缠对（可视化）

物理（leo, 2026-08-14）：
  - 空间以等效速度 c 流动（矢量光速 SLS1）；光子 = 完全随空间流动（SLS2）。
  - 纠缠光子对 = 同一流动管内的双螺旋：两股相位差 π（反相），
    沿公共轴随空间流动；相位由流动携带。
  - 源点（z=0）产生纠缠对 → 两股沿相反方向随流动展开 → 检偏器测量。

本脚本只做几何可视化（物理结论见 verify_entanglement_helix.py 与
Explorations/EntanglementHelix.lean）。产物：
  artifacts/entanglement/helix_3d.png   （静态）
  artifacts/entanglement/helix_3d.gif   （动画：相位随流动前进 + 脉冲传播）
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

# macOS CJK 字体（图内中文标题）
for _fp in ("/System/Library/Fonts/PingFang.ttc",
            "/System/Library/Fonts/Hiragino Sans GB.ttc"):
    if os.path.exists(_fp):
        fm.fontManager.addfont(_fp)
        plt.rcParams["font.sans-serif"] = [fm.FontProperties(fname=_fp).get_name()]
        break
plt.rcParams["axes.unicode_minus"] = False

OUT = os.path.join(os.path.dirname(__file__), "..", "artifacts", "entanglement")
os.makedirs(OUT, exist_ok=True)

R = 1.0        # 螺旋半径
K = 1.2        # 螺旋角频率（rad / 单位 z）
L = 3.0        # 半长
N_POINTS = 800


def strand(z, phase, sign=1.0):
    """双螺旋的一股：x = R cos(Kz + phase), y = R sin(Kz + phase)。"""
    th = K * z + phase
    return R * np.cos(th), R * np.sin(th), z


def make_fig():
    fig = plt.figure(figsize=(9, 8))
    ax = fig.add_subplot(111, projection="3d")
    ax.set_box_aspect((1.2, 1.2, 2.4))
    return fig, ax


def draw_tube(ax):
    """半透明流动管 + 流动方向箭头。"""
    zz = np.linspace(-L, L, 40)
    th = np.linspace(0, 2 * np.pi, 40)
    Z, T = np.meshgrid(zz, th, indexing="ij")
    X = 1.15 * R * np.cos(T)
    Y = 1.15 * R * np.sin(T)
    ax.plot_surface(X, Y, Z, alpha=0.08, color="steelblue", linewidth=0)
    # 流动箭头：沿 +z（空间流动方向），带微弱螺旋分量
    zq = np.linspace(-2.2, 2.2, 7)
    tq = np.linspace(0, 2 * np.pi, 6, endpoint=False)
    ZQ, TQ = np.meshgrid(zq, tq, indexing="ij")
    XQ = 1.15 * R * np.cos(TQ)
    YQ = 1.15 * R * np.sin(TQ)
    U = -0.08 * np.sin(TQ)
    V = 0.08 * np.cos(TQ)
    W = np.full_like(ZQ, 0.55)
    ax.quiver(XQ, YQ, ZQ, U, V, W, length=0.35, color="steelblue",
              alpha=0.45, normalize=True, linewidth=0.8)
    # 轴线
    ax.plot([0, 0], [0, 0], [-L, L], color="gray", lw=0.8, ls=":")


def draw_detectors(ax):
    """两端检偏器：圆盘 + 检偏轴标记线。"""
    for zs, ang in ((-L + 0.25, 0.6), (L - 0.25, 0.6 + np.pi / 4)):
        th = np.linspace(0, 2 * np.pi, 60)
        x = 1.3 * R * np.cos(th)
        y = 1.3 * R * np.sin(th)
        # 圆盘
        verts = [list(zip(x, y, np.full_like(x, zs)))]
        disc = Poly3DCollection(verts, alpha=0.18, color="orange",
                                edgecolor="darkorange", linewidth=0.6)
        ax.add_collection3d(disc)
        # 检偏轴（极化方向）
        ax.plot([-1.25 * R * np.cos(ang), 1.25 * R * np.cos(ang)],
                [-1.25 * R * np.sin(ang), 1.25 * R * np.sin(ang)],
                [zs, zs], color="darkorange", lw=2)
        ax.text(0, 0, zs + 0.15, "检偏器", color="darkorange", fontsize=9,
                ha="center")


def draw_strands(ax, phase, pulse_pos=None, alpha_pulse=0.9):
    zz = np.linspace(-L, L, N_POINTS)
    x1, y1, _ = strand(zz, phase, +1.0)
    x2, y2, _ = strand(zz, phase + np.pi, -1.0)
    ax.plot(x1, y1, zz, color="#d62728", lw=2.2, label="光子 1（相位 λ）")
    ax.plot(x2, y2, zz, color="#1f77b4", lw=2.2, label="光子 2（相位 λ+π，反相）")
    # 脉冲：随流动传播的光点
    if pulse_pos is not None:
        zp = np.clip(pulse_pos, -L + 0.3, L - 0.3)
        for sign, col in ((1, "#d62728"), (-1, "#1f77b4")):  # 脉冲同时向两端
            pass
        p1 = L - 0.3 - zp  # 光子1 沿 +z 到达右端
        p2 = -L + 0.3 + zp  # 光子2 沿 -z 到达左端
        # 光子1 脉冲
        x, y, _ = strand(np.array([p1]), phase)
        ax.scatter(x, y, [p1], s=180, color="#d62728", alpha=alpha_pulse,
                   depthshade=False, edgecolors="white", linewidths=1.2)
        # 光子2 脉冲
        x, y, _ = strand(np.array([p2]), phase + np.pi)
        ax.scatter(x, y, [p2], s=180, color="#1f77b4", alpha=alpha_pulse,
                   depthshade=False, edgecolors="white", linewidths=1.2)
    return (x1, y1, x2, y2)


def draw_source(ax):
    ax.scatter([0], [0], [0], s=320, color="gold", depthshade=False,
               edgecolors="black", linewidths=1.0, zorder=10, label="纠缠源（z=0）")


def setup_ax(ax):
    ax.set_xlim(-1.6, 1.6)
    ax.set_ylim(-1.6, 1.6)
    ax.set_zlim(-L, L)
    ax.set_xlabel("x")
    ax.set_ylabel("y")
    ax.set_zlabel("z（空间流动方向）")
    ax.view_init(elev=18, azim=-55)
    ax.legend(loc="upper left", fontsize=8, bbox_to_anchor=(0.0, 1.0))


def static(phase):
    fig, ax = make_fig()
    draw_tube(ax)
    draw_detectors(ax)
    draw_source(ax)
    draw_strands(ax, phase)
    setup_ax(ax)
    ax.set_title("流动空间中的双螺旋纠缠光子对\n"
                 "（两股反相 λ 与 λ+π，随空间流展开；动画见 helix_3d.gif）")
    fig.tight_layout()
    fig.savefig(os.path.join(OUT, "helix_3d.png"), dpi=150)
    plt.close(fig)
    print("→", os.path.join(OUT, "helix_3d.png"))


def animate():
    fig, ax = make_fig()
    draw_tube(ax)
    draw_detectors(ax)
    draw_source(ax)
    draw_strands(ax, 0.0)
    setup_ax(ax)
    ax.set_title("双螺旋纠缠：相位随流动前进，脉冲从源点向两端检偏器传播")

    def update(frame):
        phase = frame * 0.14          # 螺旋相位随"流动时间"前进
        pulse = (frame % 48) / 48.0 * 2.4  # 脉冲传播 0 → 2.4
        ax.cla()
        draw_tube(ax)
        draw_detectors(ax)
        draw_source(ax)
        draw_strands(ax, phase, pulse_pos=pulse)
        setup_ax(ax)
        return []

    anim = FuncAnimation(fig, update, frames=96, interval=60, blit=False)
    anim.save(os.path.join(OUT, "helix_3d.gif"), writer=PillowWriter(fps=16))
    plt.close(fig)
    print("→", os.path.join(OUT, "helix_3d.gif"))


if __name__ == "__main__":
    static(phase=0.7)
    animate()
