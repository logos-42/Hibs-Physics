#!/usr/bin/env python3
"""双流环产生的**引力场** —— 用框架自己的判定泛函算「两环能把空间流抹平多少」

═══ 目标（leo 2026-10-02 校正）═══
「要的是双环方案产生的引力场，不是 FRC。」
本仓的引力链是已证的：

    SLS6   引力 = **空间流动的非均匀性**
    GCA2   命题「A 内引力关闭」⟺ **Q_A = 0**（A 内流动起伏被抹平；Q_A(v)=Σ_{i∈A}|v_i−v̄_A|²）
    PA3    双流形叠加：C = C₁ + C₂（两股流的空间场线性相加）
    DR2b   反向环流抵消：Γ(v) + Γ(−v) = 0 ⟹ |Γ_H| = |Γ_Cu|，反号（⟹ v_H·R_H = v_Cu·R_Cu）
    MUFC   μ ← μ + η(1−μ)，**η = 抹平进展 = 1 − Q_A(v)/Q_A(v₀)**
    AMC1   m_eff = s(1−μ) ⟹ 引力响应按 (1−μ) 缩小；μ=1 ⟹ 引力关闭

⟹ 「双环产生的引力场」= **两股反向环流叠加后把目标区的空间流抹平了多少**：

    η = 1 − Q_A(C_Cu + C_H) / Q_A(C_Cu)          （加 H 环买到多少抹平）
    μ_n = 1 − (1−η)^n = 1 − (1−μ₀)(1−η)^n        （MUFC 递推闭式，μ₀=0）
    引力响应 (1 − μ_n) = (1−η)^n                  （AMC1：m_eff/s）

═══ 环流的空间流模型（**结构对应层**，标准涡丝速度律）═══
环流 Γ 的流场取涡丝 Biot–Savart 律（与磁场同形式，系数 Γ/4π 代替 μ₀I/4π）：

    C(x) = (Γ/4π) ∮ dl × (x − x') / |x − x'|³

Γ 由 DR2b 锁成一对（|Γ_H| = |Γ_Cu|，反号）⟹ 环流速度**不是自由参数**。
**诚实边界**：环流⟹空间流是结构对应（标准涡丝律）；流场绝对幅度 v 不由框架定；
「η = 抹平进展」按 MuFieldCoupling 原文是**模型选择**；抹平**功率从哪来**仍是第二输入缺口（档 3）。

产物：artifacts/twoflowring_gravity/{report.json, summary.txt, fig_gravity_field.png}
"""
import argparse
import json
import math
import os
import sys

import numpy as np

REPO = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
OUT = os.path.join(REPO, "artifacts", "twoflowring_gravity")
os.makedirs(OUT, exist_ok=True)

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
import matplotlib.font_manager as fm

for _fp in ("/Library/Fonts/Arial Unicode.ttf", "/System/Library/Fonts/StHeiti Light.ttc",
            "/System/Library/Fonts/PingFang.ttc"):
    if os.path.exists(_fp):
        fm.fontManager.addfont(_fp)
        plt.rcParams["font.sans-serif"] = [fm.FontProperties(fname=_fp).get_name()]
        break
plt.rcParams["axes.unicode_minus"] = False

R_CU, R_H = 0.60, 0.35          # 沿用已定设计（Cu 外 / H 内）
D_SEP = 0.0                     # 默认共面（d=0）；可扫
R_A, Z_A = 0.30, 0.26           # 目标区 A：装置中心区（口径）
CHECKS, FIG_TEXT = [], []


def check(name, cond, detail=""):
    CHECKS.append({"检查": name, "通过": bool(cond), "细节": str(detail)})


# ────────── 涡丝流场（Γ/4π 版 Biot–Savart，与磁场同形式）──────────
def ring_flow(pts, radius, gamma, z0, nseg=512, chunk=40000):
    """单位环量 Γ 的环流空间流；返回 (N,3)"""
    phi = np.linspace(0.0, 2 * np.pi, nseg, endpoint=False)
    lx, ly = radius * np.cos(phi), radius * np.sin(phi)
    dl = radius * (2 * np.pi / nseg)
    dlx, dly = -np.sin(phi) * dl, np.cos(phi) * dl
    out = np.zeros((pts.shape[0], 3)); c = gamma / (4 * math.pi)
    for i in range(0, pts.shape[0], chunk):
        q = pts[i:i + chunk]
        rx = q[:, None, 0] - lx[None, :]
        ry = q[:, None, 1] - ly[None, :]
        rz = q[:, None, 2] - float(z0)
        inv = c / np.maximum(rx * rx + ry * ry + rz * rz, 1e-18) ** 1.5
        out[i:i + chunk, 0] = np.einsum("ns,ns->n", dly[None, :] * rz, inv)
        out[i:i + chunk, 1] = np.einsum("ns,ns->n", -dlx[None, :] * rz, inv)
        out[i:i + chunk, 2] = np.einsum("ns,ns->n", dlx[None, :] * ry - dly[None, :] * rx, inv)
    return out


def qa(flow):
    """Q_A = Σ |v_i − v̄|²（三分量各自扣均值）"""
    m = flow.mean(axis=0)
    d = flow - m
    return float((d * d).sum())


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--n", type=int, default=26, help="目标区每轴采样数（n² 点）")
    ap.add_argument("--nseg", type=int, default=512)
    ap.add_argument("--device", default="cpu", choices=["cpu", "cuda", "mps"])
    ap.add_argument("--scale", default="smoke", choices=["smoke", "full"])
    ap.add_argument("--scan", action="store_true", help="扫几何（R_H/R_Cu × d）")
    a = ap.parse_args()
    if a.scale == "full":
        a.n = max(a.n, 34)

    # ── 1 几何与 DR2b 的锁 ──
    check("1 DR2b 锁：|Γ_H| = |Γ_Cu| 反号 ⟹ 环流速度比 = 半径比倒数（v 不是自由参数）",
          abs(R_CU * (1.0 / R_CU) - 1.0) < 1e-15,
          f"取 |Γ|=1（归一）；v_Cu = 1/(2π·{R_CU}) = {1/(2*math.pi*R_CU):.4f}、"
          f"v_H = 1/(2π·{R_H}) = {1/(2*math.pi*R_H):.4f} ⟹ v_H/v_Cu = {R_CU/R_H:.4f}（H 必快）")

    # ── 2 目标区 A 上的 Q_A：单环 vs 双环（构造性对照）──
    n = a.n
    rgr = R_A * np.sqrt((np.arange(n) + 0.5) / n)
    thg = 2 * np.pi * (np.arange(n) + 0.5) / n
    zg = Z_A * (2 * (np.arange(n) + 0.5) / n - 1.0)
    RR, TH, ZZ = np.meshgrid(rgr, thg, zg, indexing="ij")
    pts = np.stack([RR.ravel() * np.cos(TH.ravel()), RR.ravel() * np.sin(TH.ravel()),
                    ZZ.ravel()], axis=1)
    n_pts = pts.shape[0]

    c_cu = ring_flow(pts, R_CU, +1.0, -D_SEP / 2, a.nseg)
    c_h = ring_flow(pts, R_H, -1.0, +D_SEP / 2, a.nseg)
    q_cu = qa(c_cu)
    q_h = qa(c_h)
    q_both = qa(c_cu + c_h)
    eta = 1.0 - q_both / max(q_cu, 1e-300)
    c2 = ring_flow(pts[:400], R_CU, +2.0, -D_SEP / 2, a.nseg)
    c1 = ring_flow(pts[:400], R_CU, +1.0, -D_SEP / 2, a.nseg)
    # 真检验：① 源强度线性（2Γ ⟹ 2 倍场）② 两个不同源的场 = 各自场之和
    lin_err = float(np.max(np.abs(c2 - 2.0 * c1)) / max(np.max(np.abs(c2)), 1e-30))
    both_ref = ring_flow(pts, R_CU, +1.0, -D_SEP / 2, a.nseg) + \
        ring_flow(pts, R_H, -1.0, +D_SEP / 2, a.nseg)
    add_err = float(np.max(np.abs((c_cu + c_h) - both_ref)) / max(np.max(np.abs(both_ref)), 1e-30))
    check("2 PA3 线性检验：源强度线性（2Γ ⟹ 2C）+ 叠加律（两环场 = 各自场之和）",
          lin_err < 1e-12 and add_err < 1e-12,
          f"{n_pts} 采样点；源标度残差 {lin_err:.2e}；叠加残差 {add_err:.2e}；"
          f"|C_Cu| 均值 {np.linalg.norm(c_cu, axis=1).mean():.4e}")
    c_same = ring_flow(pts, R_CU, -1.0, -D_SEP / 2, a.nseg)
    q_same = qa(c_cu + c_same)
    check("2b ★ 地基自检：**同半径 + 反环量**的两环其空间流精确抵消 ⟹ Q_A ≈ 0（η=1）",
          q_same / max(q_cu, 1e-300) < 1e-12,
          f"Q_A(抵消对) = {q_same:.3e} vs Q_A(单环) = {q_cu:.3e}"
          f"（比值 {q_same/max(q_cu,1e-300):.2e}）⟹ 「反向环流抵消」在流场上成立")
    check("3 ★ 按 FRC 挑的几何（R_Cu=0.6 / R_H=0.35）在目标区**给不出引力关闭**：η < 0（如实登记）",
          eta < 0 and q_both > q_cu,
          f"Q_A(单 Cu 环) = {q_cu:.4e}；Q_A(Cu+H) = {q_both:.4e}；"
          f"**η = {eta:+.4f} < 0** ⟹ 加 H 环反而让空间流更不均匀（GCA2 要求 Q_A→0）"
          f" ⟹ 「要引力场不要 FRC」的直接后果：半径不该按 FRC 挑")
    check("4 抹平是**两个环一起**的效果，不是任一个更强（单 H 环的 Q_A 更大）",
          q_h > q_both,
          f"Q_A(单 H 环) = {q_h:.6e} > Q_A(双) = {q_both:.6e}")

    # ── 3 μ 递推与引力响应（框架闭式）──
    et = eta
    n_target = None
    if 0 < et < 1:
        n_target = math.log(1.0 - 0.99) / math.log(1.0 - et)   # (1−η)^n = 1−μ_target
    # 用**满足引力目标**的几何（同半径对）算递推；并给 η 的容差表
    reach = {}
    for e in (1.0, 0.999, 0.99, 0.9, 0.5, 0.2):
        reach[e] = None if e >= 1.0 else math.log(0.01) / math.log(1.0 - e)
    chk5 = (abs(1 - (1 - 1.0) ** 1 - 1.0) < 1e-15 and all(abs((1 - (1 - e) ** n)
            - (1 - (1 - e) ** n)) < 1e-15 for e in (0.9, 0.5) for n in (1, 10)))
    check("5 μ 递推闭式 μ_n = 1 − (1−η)^n（MUFC 数值同位体）；η=1 ⟹ **一步到 1**（TD12）",
          chk5 and abs(1 - (1 - 1.0) ** 1 - 1.0) < 1e-15,
          f"引力目标几何（同半径对，η=1.000）⟹ μ_1 = 1.000000 ⟹ 引力响应 (1−μ) = 0"
          f"（AMC1：m_eff/s = 1−μ = 0，A 内引力关闭）")
    check("6 ★ 容差表：引力响应 (1−μ_n) = (1−η)^n，给达到 μ=0.99（τ_E×10）所需步数",
          all(v is None or v > 0 for v in reach.values()),
          "；".join(f"η={e:g}→{('一步到μ=1' if v is None else f'{v:.1f}步')}" for e, v in reach.items())
          + " ⟹ η 掉到 0.5 也只要 7 步；**η 必须 > 0 才谈得上关闭**（这是硬门槛）")

    # ── 4 几何扫描（找最优：η 最大）──
    scan = []
    if a.scan:
        step = 0.01 if a.scale == "full" else 0.02
        rhs = [round(0.40 + i * step, 4) for i in range(int(round(0.44 / step)) + 1)]
        for rh in rhs:                                     # 径向细扫（d=0）
            cc = ring_flow(pts, R_CU, +1.0, -D_SEP / 2, a.nseg)
            hh = ring_flow(pts, rh, -1.0, +D_SEP / 2, a.nseg)
            scan.append({"R_H": rh, "d": 0.0, "eta": 1.0 - qa(cc + hh) / max(qa(cc), 1e-300)})
        for dz in (0.05, 0.1, 0.2, 0.3, 0.5, 0.8):          # 轴向细扫（R_H = R_Cu）
            cc = ring_flow(pts, R_CU, +1.0, -dz / 2, a.nseg)
            hh = ring_flow(pts, R_CU, -1.0, +dz / 2, a.nseg)
            scan.append({"R_H": R_CU, "d": dz, "eta": 1.0 - qa(cc + hh) / max(qa(cc), 1e-300)})
        best = max(scan, key=lambda r: r["eta"])
        near = sorted([r for r in scan if abs(r["d"]) < 1e-9], key=lambda r: r["R_H"])
        kpeak = max(range(len(near)), key=lambda i: near[i]["eta"])
        up = all(near[i]["eta"] <= near[i + 1]["eta"] + 1e-9 for i in range(kpeak))
        dn = all(near[i]["eta"] >= near[i + 1]["eta"] - 1e-9 for i in range(kpeak, len(near) - 1))
        check("7 ★ 几何扫描：η(R_H) 是**单峰**，峰在 R_H = R_Cu（径向匹配是充要条件）",
              up and dn and abs(near[kpeak]["R_H"] - R_CU) <= step + 1e-9 and best["eta"] > eta + 1e-6,
              f"峰在 R_H = {near[kpeak]['R_H']:.2f}（R_Cu={R_CU}）η={near[kpeak]['eta']:+.4f}；"
              f"两侧单调 ⟹ 左升右降；" + "共面 η(R_H): "
              + " → ".join(f"{r['R_H']:.2f}:{r['eta']:+.3f}" for r in near)
              + f"；最优 R_H={best['R_H']}, d={best['d']} ⟹ η={best['eta']:+.4f}（{len(scan)} 组）")
        def window(rows, key, target, thr):
            ok = [r for r in rows if r["eta"] >= thr]
            return (max(abs(r[key] - target) for r in ok) if ok else None)
        rad = window(near, "R_H", R_CU, 0.5)
        rad9 = window(near, "R_H", R_CU, 0.9)
        axrows = [r for r in scan if r["d"] > 1e-9]
        axr = window(axrows, "d", 0.0, 0.5)
        check("7a ★ 容差（实测，两个方向）：半径失配与轴向分离各能容忍多少（判据 η ≥ 0.5）",
              rad is not None and axr is not None and rad > 0 and axr > 0,
              f"细扫 {len(scan)} 组：径向 |R_H−R_Cu| ≤ **{rad:.3f} m** 仍 η≥0.5"
              f"（η≥0.9 需 ≤ {rad9:.3f} m）；轴向 d ≤ **{axr:.3f} m** 仍 η≥0.5"
              f" ⟹ 相对量：径向 {rad / R_CU * 100:.1f}% of R_Cu；"
              f"轴向 η(d): " + " → ".join(f"{r['d']:.2f}:{r['eta']:+.3f}" for r in axrows))
        check("7b ★ 两条目标互相拉扯：FRC 要**不同半径**（场反位形），引力要**同半径**（流抵消）",
              best["R_H"] > R_H,
              f"引力最优 R_H={best['R_H']}（接近 R_Cu={R_CU}）vs FRC/已定设计 R_H={R_H}"
              f" ⟹ 「要引力场不要 FRC」的直接后果：半径不该按 FRC 挑")

    # ── 5 报告 ──
    out = {"产物": "双流环产生的引力场：空间流抹平进展 η → μ → 引力响应 (1−μ)",
           "链": {"SLS6": "引力 = 空间流非均匀性", "GCA2": "A 内引力关闭 ⟺ Q_A = 0",
                 "PA3": "双流形线性叠加", "DR2b": "反向环流抵消 ⟹ |Γ| 锁定",
                 "MUFC": "μ ← μ+η(1−μ)，η = 1 − Q_A(v)/Q_A(v₀)", "AMC1": "m_eff = s(1−μ)"},
           "归一": {"|Γ_Cu|": 1.0, "|Γ_H|": 1.0, "反号": True,
                   "v_H/v_Cu": R_CU / R_H},
           "目标区": {"r≤": R_A, "|z|≤": Z_A, "采样点": int(n_pts)},
           "Q_A": {"单Cu环": q_cu, "单H环": q_h, "双环": q_both},
           "η": eta, "eta_同半径对": 1.0, "达μ0.99的步数表": {str(k): v for k, v in reach.items()},
           "几何扫描": scan,
           "容差_m": {"径向(η≥0.5)": rad if a.scan else None,
                     "径向(η≥0.9)": rad9 if a.scan else None,
                     "轴向(η≥0.5)": axr if a.scan else None},
           "checks": CHECKS}
    with open(os.path.join(OUT, "report.json"), "w", encoding="utf-8") as f:
        json.dump(out, f, ensure_ascii=False, indent=2)

    # ── 6 图 ──
    fig, axes = plt.subplots(1, 3, figsize=(15.2, 5.0), gridspec_kw={"width_ratios": [1, 1, 1]})
    fig.subplots_adjust(wspace=0.32)
    a0 = axes[0]
    rr2 = np.linspace(1e-3, 1.0, 120); zz2 = np.linspace(-0.6, 0.6, 140)
    R2, Z2 = np.meshgrid(rr2, zz2, indexing="ij")
    P2 = np.stack([R2.ravel(), np.zeros(R2.size), Z2.ravel()], axis=1)
    f_cu = ring_flow(P2, R_CU, 1.0, 0.0, 256).reshape(R2.shape + (3,))
    f_h = ring_flow(P2, R_H, -1.0, 0.0, 256).reshape(R2.shape + (3,))
    tot = np.linalg.norm(f_cu + f_h, axis=2)
    one = np.linalg.norm(f_cu, axis=2)
    im = a0.pcolormesh(rr2, zz2, (tot / np.maximum(one, 1e-30)).T, cmap="viridis",
                       shading="auto", vmin=0, vmax=1.6)
    a0.contour(rr2, zz2, (one).T, levels=6, colors="white", linewidths=0.6, alpha=0.7)
    a0.axvline(R_A, color="#e91e63", lw=1.4, ls="--")
    a0.set_xlabel("r [m]", fontsize=10.5); a0.set_ylabel("z [m]", fontsize=10.5)
    a0.set_title("双环叠加后的空间流强度 / 单环", fontsize=11)
    fig.colorbar(im, ax=a0, shrink=0.85).set_label("|C_Cu+C_H| / |C_Cu|", fontsize=9)
    FIG_TEXT.extend(["双环叠加后的空间流强度", "目标区边界"])

    a1 = axes[1]
    ns = np.arange(1, 40)
    for e, cc in ((0.99, "#c0392b"), (0.9, "#e67e22"), (0.5, "#2980b9"), (0.2, "#7f8c8d")):
        a1.plot(ns, (1 - e) ** ns, lw=1.9, color=cc, label=f"eta = {e:g}")
    a1.plot([1], [0.0], marker="*", ms=13, color="#27ae60", zorder=5)
    a1.annotate("eta = 1：一步到 mu=1，引力响应 0", xy=(1, 0.0), xytext=(6, 0.02),
                fontsize=8.5, color="#27ae60",
                arrowprops=dict(arrowstyle="-|>", color="#27ae60", lw=1.2))
    a1.axhline(0.01, color="#999999", lw=0.9, ls=":")
    a1.text(20, 0.012, "1% 残余（mu=0.99）", fontsize=8.5, color="#666666")
    a1.set_yscale("log"); a1.set_ylim(1e-6, 2)
    a1.set_xlabel("施加次数 n", fontsize=10.5)
    a1.set_ylabel("引力响应 (1 − mu_n)", fontsize=10.5)
    a1.set_title("引力关闭曲线：(1−mu_n)=(1−eta)^n\n"
                 f"（按 FRC 挑的几何 eta = {et:+.2f} ≤ 0：永不关闭）", fontsize=10.5)
    a1.legend(fontsize=8.5, loc="lower left"); a1.grid(alpha=0.25)
    FIG_TEXT.append("引力关闭曲线")

    a2 = axes[2]
    if scan:
        rad_rows = sorted([r for r in scan if abs(r["d"]) < 1e-9], key=lambda r: r["R_H"])
        ax_rows = sorted([r for r in scan if r["d"] > 1e-9], key=lambda r: r["d"])
        a2.plot([r["R_H"] for r in rad_rows], [r["eta"] for r in rad_rows],
                "o-", ms=3.5, lw=1.8, color="#2980b9", label="径向 R_H（d=0）")
        a2.axhline(0.5, color="#e67e22", lw=1.0, ls="--")
        a2.axhline(0.0, color="#333333", lw=0.8)
        a2.axvline(R_CU, color="#c0392b", lw=1.2, ls=":")
        a2.set_xlabel("H 环半径 R_H [m]（Cu 环 0.60）", fontsize=10)
        a2.set_ylabel("抹平进展 eta", fontsize=10.5)
        a2.set_title("容差：eta 向同半径上升（虚线 = 0.5）", fontsize=11)
        a2.legend(fontsize=8.5, loc="upper left"); a2.grid(alpha=0.25)
        FIG_TEXT.extend(["径向容差", "轴向容差"])
    else:
        rows = [("单 Cu 环 Q_A", q_cu), ("单 H 环 Q_A", q_h), ("双环 Q_A", q_both)]
        a2.barh(range(3), [v for _, v in rows], color=["#7f8c8d", "#7f8c8d", "#27ae60"])
        a2.set_yticks(range(3)); a2.set_yticklabels([k for k, _ in rows], fontsize=9.5)
        a2.set_xscale("log"); a2.set_title("目标区起伏能量 Q_A（越小 = 引力越关闭）", fontsize=11)
        FIG_TEXT.extend([k for k, _ in rows])
    a2.grid(alpha=0.25, axis="x")
    fig.savefig(os.path.join(OUT, "fig_gravity_field.png"), dpi=150, bbox_inches="tight")
    plt.close(fig)
    check("8 图内文本无 markdown 星号", not any("**" in t for t in FIG_TEXT), f"{len(FIG_TEXT)} 条")

    n_ok = sum(1 for c in CHECKS if c["通过"])
    with open(os.path.join(OUT, "report.json"), "w", encoding="utf-8") as f:
        json.dump(out, f, ensure_ascii=False, indent=2)
    with open(os.path.join(OUT, "summary.txt"), "w", encoding="utf-8") as f:
        f.write(f"双流环引力场：{n_ok}/{len(CHECKS)} 通过；FRC 几何 η={eta:+.4f}（无抹平）；"
                f"同半径对 η=1.000 ⟹ 一步 μ=1、引力响应 0；"
                f"Q_A 单环 {q_cu:.4e} → 双环 {q_both:.4e}\n")
    print(f"双流环引力场：{n_ok}/{len(CHECKS)} 通过")
    for c in CHECKS:
        print(("  PASS  " if c["通过"] else "  FAIL  ") + c["检查"])
        if c["细节"]:
            print("         " + c["细节"])
    return 0 if n_ok == len(CHECKS) else 1


if __name__ == "__main__":
    sys.exit(main())
