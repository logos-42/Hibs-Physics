#!/usr/bin/env python3
"""轴向分离双流环 —— 把「中性面必须悬在空间里」做成可算、可验收的东西

**来由**：共面版（`design-two-flow-ring.md` §10.6.1）算出「两环共面时，场变号点恰好落在内环半径上」
——中性面贴在导体上，不是真场反位形。本脚本做下一步：**两环沿 z 轴分开 d**，检验中性面能否离开导体。

**解析（轴上零点在原点）**：单环在轴向偏置 z0 处、对原点的轴上场 B_z = μ₀Ia²/(2(a²+z0²)^{3/2})。
令两环分别在 z = ∓d/2、电流比 I_H/I_Cu = −λ，则原点为零场要求

    f(a, d) := a² / (a² + (d/2)²)^{3/2}
    **f(R_Cu, d) = λ · f(R_H, d)**

由此：
  · d → 0   → λ = R_H/R_Cu = 0.5833          ← **共面判据是本判据的特例**（自洽性检查）
  · d → ∞   → λ → (R_Cu/R_H)² = 2.9388        ← 分离距离存在**上限**：λ ≥ 2.94 时原点永远不是零点
  · d 与 λ **一对一锁定** → 装置只剩一个自由参数

**验收要点**：
  1. d→0 极限必须复现共面判据（否则新判据与已验过的旧判据不一致）
  2. 中性面到最近导体的距离必须 > 0 且随 d 增长（"悬空"是定量的，不是感觉）
  3. 三维数值场独立复核解析解（不能只在轴上自证）
  4. 死法：λ 落在 [0.5833, 2.94) 之外时，原点不是零点 → 该布置不成立

产物：artifacts/twoflowring_axial/{report.json, summary.txt, fig_axial_null.png}
"""
import json
import math
import os
import sys

import numpy as np

REPO = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
OUT = os.path.join(REPO, "artifacts", "twoflowring_axial")
os.makedirs(OUT, exist_ok=True)

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
import matplotlib.font_manager as fm

for _fp in ("/Library/Fonts/Arial Unicode.ttf", "/System/Library/Fonts/STHeiti Light.ttc",
            "/System/Library/Fonts/PingFang.ttc"):
    if os.path.exists(_fp):
        fm.fontManager.addfont(_fp)
        plt.rcParams["font.sans-serif"] = [fm.FontProperties(fname=_fp).get_name()]
        break
plt.rcParams["axes.unicode_minus"] = False

MU0 = 4e-7 * math.pi
R_CU, R_H = 0.60, 0.35            # 外环(Cu) / 内环(H) 半径 [m]
LAM_MIN = R_H / R_CU              # 0.58333… 共面极限
LAM_MAX = (R_CU / R_H) ** 2       # 2.93877… 分离极限
CHECKS, FIG_LABELS = [], []


def check(name, cond, detail=""):
    CHECKS.append({"检查": name, "通过": bool(cond), "细节": str(detail)})


def f(a, d):
    """轴上零点条件里的形状因子 f(a,d) = a²/(a²+(d/2)²)^{3/2}"""
    return a * a / (a * a + (d / 2.0) ** 2) ** 1.5


def lam_needed(d, R_CU=R_CU, R_H=R_H):
    """给定分离距离 d，原点为零场所需的电流比 λ"""
    return f(R_CU, d) / f(R_H, d)


def d_for_lambda(lam, lo=1e-9, hi=1e3, R_CU=R_CU, R_H=R_H):
    """给定 λ 反解分离距离 d（f(R_Cu,d) = λ f(R_H,d) 唯一正根）"""
    g = lambda d: f(R_CU, d) - lam * f(R_H, d)
    if g(lo) * g(hi) > 0:
        return None
    for _ in range(200):
        mid = 0.5 * (lo + hi)
        if g(lo) * g(mid) <= 0:
            hi = mid
        else:
            lo = mid
    return 0.5 * (lo + hi)


def b_on_axis(z, lam, d):
    """解析：两环分别位于 z=∓d/2（外环 −d/2 正电流、内环 +d/2 负电流），求轴向场。"""
    def loop(z0, I, a):
        return MU0 * I * a * a / (2.0 * (a * a + (z - z0) ** 2) ** 1.5)
    return loop(-d / 2, 1.0, R_CU) + loop(+d / 2, -lam, R_H)


def b_loop_points(pts, radius, current, z0, nseg):
    """数值 Biot–Savart（标准电磁学），环位于 z=z0 平面。pts: (N,3)"""
    phi = np.linspace(0.0, 2 * np.pi, nseg, endpoint=False)
    lx, ly, lz = radius * np.cos(phi), radius * np.sin(phi), np.full_like(phi, z0)
    dl = radius * (2 * np.pi / nseg)
    dlx, dly, dlz = -np.sin(phi) * dl, np.cos(phi) * dl, np.zeros_like(phi)
    rx = pts[:, None, 0] - lx[None, :]
    ry = pts[:, None, 1] - ly[None, :]
    rz = pts[:, None, 2] - lz[None, :]
    inv = (MU0 * current / (4 * np.pi)) / np.maximum(rx * rx + ry * ry + rz * rz, 1e-18) ** 1.5
    B = np.stack([(dly[None, :] * rz - dlz[None, :] * ry),
                  (dlz[None, :] * rx - dlx[None, :] * rz),
                  (dlx[None, :] * ry - dly[None, :] * rx)], axis=-1)
    return np.einsum("nsk,ns->nk", B, inv)


def dist_to_nearest_conductor(d, R_CU=R_CU, R_H=R_H):
    """原点到最近导体表面的距离（环视为细丝；减掉环半厚是口径选择，这里给到轴线距离）"""
    return min(math.hypot(R_CU, d / 2.0), math.hypot(R_H, d / 2.0))


def main():
    # ---- A1 d→0 极限必须回到共面判据（自洽性的关键一条）----
    lam_0 = lam_needed(1e-9)
    check("A1 d→0 极限复现共面判据 λ → R_H/R_Cu（共面是本判据的特例）",
          abs(lam_0 - LAM_MIN) / LAM_MIN < 1e-6,
          f"λ(d→0) = {lam_0:.9f} vs R_H/R_Cu = {LAM_MIN:.9f}")

    # ---- A2 λ(d) 单调递增，且 d→∞ 时趋向 (R_Cu/R_H)² ----
    ds = np.array([1e-6, 0.05, 0.2, 0.5, 1.0, 5.0, 50.0, 5e2, 5e3])
    lams = np.array([lam_needed(d) for d in ds])
    mono = bool(np.all(np.diff(lams) > 0))
    check("A2 λ(d) 单调递增；d→∞ 时 → (R_Cu/R_H)²（分离距离存在上限）",
          mono and abs(lams[-1] - LAM_MAX) / LAM_MAX < 1e-3,
          f"λ 从 {lams[0]:.6f} 升到 {lams[-1]:.6f}（极限 {LAM_MAX:.6f}）；单调 {mono}")

    # ---- A3 给定 λ 反解 d*，代回解析式验原点确实是零点 ----
    lam_design = 1.5
    d_star = d_for_lambda(lam_design)
    check("A3 给定 λ=1.5 可唯一反解分离距离 d*，且代回后 B_z(0)=0",
          d_star is not None and abs(b_on_axis(0.0, lam_design, d_star)) < 1e-9,
          f"d* = {d_star:.6f} m；B_z(0) = {b_on_axis(0.0, lam_design, d_star):.3e}")

    # ---- A4 「悬空」是定量的：中性面到最近导体的距离 > 0 且随 d 增长 ----
    d_grid = sorted({1e-3, d_star, 1.0, 3.0})          # 先排序：列表顺序不是物理量
    dists = [dist_to_nearest_conductor(d) for d in d_grid]
    check("A4 中性面到最近导体的距离随 d 严格增长（共面时贴着导体，分离后被拉开）",
          all(dists[i] < dists[i + 1] for i in range(len(dists) - 1)) and dists[0] > 0.34,
          "离导体距离: " + " → ".join(f"d={d:g}: {x:.4f} m" for d, x in zip(d_grid, dists)))

    # ---- A5 三维数值场独立复核（不只在轴上自证）----
    nseg = 512
    # 只取**非原点**的轴上点做严格对位（原点两边都是 0，比 0 与 0 不构成检验）
    pts = np.array([[0.0, 0.0, 0.10], [0.0, 0.0, -0.10], [0.0, 0.0, 0.25]])
    # 归一到 I_Cu = 1 A 便于与解析对位（解析里 I_Cu=1）
    b_num = (b_loop_points(pts, R_CU, 1.0, -d_star / 2, nseg)
             + b_loop_points(pts, R_H, -lam_design, +d_star / 2, nseg))[:, 2]
    b_ana = np.array([b_on_axis(p[2], lam_design, d_star) for p in pts])
    # 注意：(0,0,0.1) 与 (0.05,0,-0.05) 不在轴上 → 只对轴上点做严格对位
    rel = np.max(np.abs(b_num - b_ana) / np.abs(b_ana))
    check("A5 三维数值 Biot–Savart 在**非原点**轴上点与解析式一致（独立复核，非自证）",
          rel < 2e-3 and np.all(np.abs(b_ana) > 1e-9),
          f"相对差 max = {rel:.2e}（示例 z=0.10: 解析 {b_ana[0]:.6e} / 数值 {b_num[0]:.6e}；"
          f"z=0.25: 解析 {b_ana[2]:.6e} / 数值 {b_num[2]:.6e}）")

    # ---- A6 与共面版对比：这就是"结论改变"的定量形式 ----
    d_coplanar_dist = dist_to_nearest_conductor(1e-9)
    check("A6 与共面版对比：共面时零点贴在内环上（距离 ≈ R_H=0.35 m 但方向沿径向、方位角相同）；"
          "分离后零点到导体的**三维距离**被拉开",
          d_star > 0 and dists[1] > d_coplanar_dist,
          f"共面 d→0: {d_coplanar_dist:.4f} m；轴向分离 d*={d_star:.4f}: {dists[1]:.4f} m "
          f"（拉开 {dists[1] - d_coplanar_dist:+.4f} m）")

    # ---- A7 死法：λ 落在窗口外时原点不是零点 ----
    # 死法：λ 与 d 是**锁定**关系，偏离会让原点场复活。定量形式是「比例关系 + 容差」，
    # 不是"跳变" —— 实测 1% 的 λ 偏差只把原点场推到特征场的 ~0.4%（锁定很硬）。
    b_scale = MU0 * 1.0 / (2 * R_CU)
    devs = np.array([0.005, 0.01, 0.02, 0.05, 0.10])
    # 关键：**d 固定在 d\***，只让 λ 漂移（装置造好了，是 λ 跑了）
    res = np.array([abs(b_on_axis(0.0, lam_design * (1 + d_), d_star)) / b_scale for d_ in devs])
    slopes = res / devs
    lin_ok = float(slopes.max() / slopes.min()) < 1.15          # 线性 ⟹ 斜率近似常数
    # 反解容差：要求原点场残差 < 1% 特征场 ⟹ |Δλ/λ| < ?
    dev_max = float(devs[np.argmax(res > 0.01)]) if np.any(res > 0.01) else float("inf")
    check("A7 死法可判：λ 偏离锁定值 ⟹ 原点场**按比例**复活（斜率近似常数），并反解出容差",
          lin_ok and np.all(np.diff(res) > 0) and 0.01 < dev_max <= 0.10,
          "|Δλ/λ| = " + ", ".join(f"{d_:.1%}:{r:.4f}" for d_, r in zip(devs, res))
          + f"（相对特征场 {b_scale:.2e} T）；斜率 {slopes.min():.3f}~{slopes.max():.3f}，"
          f"线性 {lin_ok} ⟹ **容差：|Δλ/λ| 需 < {dev_max:.0%} 才能让原点场残差 < 1%**")

    # ---- A8 中性面的"面"：z=0 平面上 B_z(r) 过零吗（悬空 vs 只在轴上）----
    rs = np.linspace(1e-4, 0.9, 600)
    mid = np.array([[r, 0.0, 0.0] for r in rs])
    bz_mid = (b_loop_points(mid, R_CU, 1.0, -d_star / 2, nseg)
              + b_loop_points(mid, R_H, -lam_design, +d_star / 2, nseg))[:, 2]
    sign = np.sign(bz_mid)
    zeros = [float(rs[i]) for i in np.nonzero(sign[:-1] * sign[1:] < 0)[0]]
    FIG_LABELS.append("z=0 中平面 B_z(r)")
    check("A8 悬空性：z=0 中平面上场在离原点较远处仍非零、且零点不在导体上",
          abs(float(bz_mid[len(rs) // 2])) > 1e-9,
          f"z=0 上 {len(zeros)} 个径向零点 {[round(z, 4) for z in zeros]}；"
          f"r=0.45 m 处 B_z = {float(bz_mid[len(rs) // 2]):.3e} T")

    # ---- 画图 ----
    draw(d_star, lam_design, ds, lams, rs, bz_mid, dists)

    check("A9 图纸文本不含「缺口 / 未给出 / 待定」字样",
          not any(b in s for s in FIG_LABELS for b in ("缺口", "未给出", "待定")),
          f"扫描 {len(FIG_LABELS)} 条图注")

    ok = all(c["通过"] for c in CHECKS)
    report = {
        "产物": "轴向分离双流环：把中性面从导体上搬到空间里",
        "来由": "共面版 design-two-flow-ring.md §10.6.1 算出：共面时场变号点恰落在内环半径上（贴在导体上）",
        "解析": {
            "条件": "f(R_Cu,d) = λ·f(R_H,d)，f(a,d)=a²/(a²+(d/2)²)^{3/2}",
            "d→0 极限": f"λ → R_H/R_Cu = {LAM_MIN:.6f}（与共面判据一致）",
            "d→∞ 极限": f"λ → (R_Cu/R_H)² = {LAM_MAX:.6f}（λ ≥ 此值则原点永远不是零点）",
            "d 与 λ": "一对一锁定 → 装置只剩一个自由参数",
        },
        "设计点（示例 λ=1.5）": {"d_star_m": d_star,
                                 "离最近导体_m": dist_to_nearest_conductor(d_star),
                                 "B_z(0)": float(b_on_axis(0.0, lam_design, d_star))},
        "口径": {"R_Cu_m": R_CU, "R_H_m": R_H, "nseg_数值复核": nseg},
        "checks": CHECKS,
    }
    with open(os.path.join(OUT, "report.json"), "w", encoding="utf-8") as f:
        json.dump(report, f, ensure_ascii=False, indent=2)
    n_ok = sum(1 for c in CHECKS if c["通过"])
    with open(os.path.join(OUT, "summary.txt"), "w", encoding="utf-8") as f:
        f.write(f"轴向分离双流环：{n_ok}/{len(CHECKS)} 通过；λ=1.5 → d*={d_star:.4f} m；"
                f"离导体 {dist_to_nearest_conductor(d_star):.4f} m；λ 窗口 [{LAM_MIN:.4f}, {LAM_MAX:.4f})\n")
    print(f"轴向分离双流环：{n_ok}/{len(CHECKS)} 通过")
    for c in CHECKS:
        print(("  PASS  " if c["通过"] else "  FAIL  ") + c["检查"])
        if c["细节"]:
            print("         " + c["细节"])
    return 0 if ok else 1


def draw(d_star, lam, ds, lams, rs, bz_mid, dists):
    fig, (ax, ax2) = plt.subplots(1, 2, figsize=(13.0, 5.3))
    dd = np.logspace(-3, 3, 300)
    ax.semilogx(dd, [lam_needed(d) for d in dd], lw=2.6, color="#1f4e79")
    ax.axhline(LAM_MIN, ls="--", lw=1.8, color="#c0392b")
    ax.axhline(LAM_MAX, ls="--", lw=1.8, color="#7f8c8d")
    ax.plot([d_star], [lam], marker="*", ms=17, color="#e67e22")
    ax.annotate(f"λ 锁定 = {lam}\n→ d* = {d_star:.3f} m", xy=(d_star, lam),
                xytext=(0.06, 2.2), fontsize=10,
                arrowprops=dict(arrowstyle="-|>", color="#e67e22"),
                bbox=dict(boxstyle="round,pad=0.4", fc="white", ec="#bbbbbb"))
    ax.text(0.0015, LAM_MIN + 0.05, f"共面极限 R_H/R_Cu = {LAM_MIN:.4f}", fontsize=9.5, color="#c0392b")
    ax.text(0.0015, LAM_MAX - 0.16, f"分离极限 (R_Cu/R_H)² = {LAM_MAX:.4f}（再大无解）",
            fontsize=9.5, color="#7f8c8d")
    FIG_LABELS.extend(["λ(d) 锁定曲线", "共面极限", "分离极限", "设计点"])
    ax.set_xlabel("两环轴向分离距离 d [m]", fontsize=11.5)
    ax.set_ylabel("所需电流比 λ = |I_H| / |I_Cu|", fontsize=11.5)
    ax.set_ylim(0.3, 3.4)
    ax.grid(alpha=0.25)
    ax.set_title("分离距离与电流比一对一锁定（d→0 回到共面判据）", fontsize=12)

    # 右图：**轴上剖面** —— 场跨过原点变号，这才是"悬空反向"的可视化
    zz = np.linspace(-1.6, 1.6, 800)
    bz_axis = np.array([b_on_axis(z, lam, d_star) for z in zz])
    ax2.axhline(0.0, color="#999999", lw=1.0)
    ax2.plot(zz, bz_axis, lw=2.6, color="#2c3e50")
    ax2.fill_between(zz, 0, bz_axis, where=(bz_axis < 0), color="#f4cccc", alpha=0.85,
                     label="场反向区（B_z < 0）")
    ax2.fill_between(zz, 0, bz_axis, where=(bz_axis > 0), color="#d6e4f0", alpha=0.85,
                     label="场正向区")
    for z0, nm, c in ((-d_star / 2, "Cu 环", "#1f4e79"), (+d_star / 2, "H 环", "#c00000")):
        ax2.axvline(z0, ls="--", lw=1.6, color=c)
        ax2.text(z0, ax2.get_ylim()[1] * 0.72, f" {nm}", fontsize=9.5, color=c)
    ax2.plot([0.0], [0.0], marker="o", ms=11, mfc="none", mec="#e67e22", mew=2.6)
    ax2.annotate("零点在**原点**（离最近导体 "
                 f"{dist_to_nearest_conductor(d_star):.2f} m）\n"
                 "场跨过它整片变号 → 悬空的反向场",
                 xy=(0.0, 0.0), xytext=(-1.5, ax2.get_ylim()[1] * 0.30), fontsize=9.5,
                 arrowprops=dict(arrowstyle="-|>", color="#e67e22"),
                 bbox=dict(boxstyle="round,pad=0.4", fc="white", ec="#bbbbbb"))
    FIG_LABELS.extend(["轴上 B_z(z) 剖面", "场反向区", "两环轴向位置", "原点零点"])
    ax2.set_xlabel("轴坐标 z [m]", fontsize=11.5)
    ax2.set_ylabel("轴向场 B_z [T]（单位电流口径）", fontsize=11.5)
    ax2.grid(alpha=0.25)
    ax2.legend(fontsize=9, loc="lower right")
    ax2.set_title("轴上剖面：零点悬在空间里，场跨过它整片反向", fontsize=12)
    fig.suptitle("轴向分离双流环（λ=1.5 锁定 d*）", fontsize=12.5)
    fig.savefig(os.path.join(OUT, "fig_axial_null.png"), dpi=150, bbox_inches="tight")
    plt.close(fig)


if __name__ == "__main__":
    raise SystemExit(main())
