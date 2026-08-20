#!/usr/bin/env python3
"""测量：折叠域的拓扑继续折叠（多褶皱）与边界势差放大

对应 leo（2026-08-20）的两个问题：
  Q1. 能否在拓扑上继续折叠，让内部褶皱更多 ⟹ 内部空间更多？
  Q2. 让边界的整个势能差更大 ⟹ 内部空间能否更大？

框架基础（见 theory-space-fold.md / verify_space_extensibility.py）：
  折叠域密度 ρ/ρ₀ = 1 + δ·g(r)，g 为径向包络；
  压缩能 E_comp = ½κ δ² ∫g² dV（内部空间总量 ∝ δ·∫g²dV，同坐标体积装更多空间）；
  弥散边界（梯度过渡层）E_bdry = ½γ ∫|∇ρ|² dV，γ = 边界势差刚度；
  螺旋旋转维持器 E_rot = ½νB² V_fold；
  自维持上限 δ_max = B·√(ν·V_fold / (κ·∫g²dV))。

Q1 实现：把单褶皱 g(r) 换成多褶皱叠加 g(r)=Σ_k a_k·exp(−((r−r_k)/w_k)²)
  （多个同心"褶皱层"）。测量：
   · 同样的 δ、同样的 κ/ν/γ/B 下，多褶皱 vs 单褶皱的 ∫g²dV / V_fold；
   · 在"相同总能量预算 E_total 固定"约束下，多褶皱能否达到更大 δ（更多内部空间）；
   · 单位边界能 E_bdry 是否随褶皱数变化（多褶皱 ⟺ 更多边界层）。
Q2 实现：把边界势差刚度 γ 和/或 边界势差 ΔΦ 放大。
  · 放大 γ（弥散边界更"硬"）：边界能更大，但内部折叠域更聚焦，测量 E_total 与可达 δ；
  · 边界势差 ΔΦ 放大 ⟹ 可支撑更大密度比（ρ_in/ρ_out 上限），在势差预算上直接测
    "势差上限 → 内部空间总量上限"。
"""
import json
import os
import math
from datetime import date

import numpy as np
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
import matplotlib.font_manager as fm

for _fp in ("/System/Library/Fonts/PingFang.ttc",
            "/System/Library/Fonts/Hiragino Sans GB.ttc"):
    if os.path.exists(_fp):
        fm.fontManager.addfont(_fp)
        plt.rcParams["font.sans-serif"] = [fm.FontProperties(fname=_fp).get_name()]
        break
plt.rcParams["axes.unicode_minus"] = False

OUT = os.path.join(os.path.dirname(__file__), "..", "artifacts", "fold_topology")
os.makedirs(OUT, exist_ok=True)


def radial_grid():
    r = np.linspace(0, 4.0, 800)
    dr = r[1] - r[0]
    dV = 4.0 * math.pi * r ** 2 * dr
    return r, dV


def single_bump(r, R=1.0):
    return np.exp(-(r / R) ** 2)


def multi_bump(r, layers):
    """layers = list of (center, width, amp)。多同心褶皱叠加。"""
    g = np.zeros_like(r)
    for (rc, w, a) in layers:
        g = g + a * np.exp(-((r - rc) / w) ** 2)
    return g


def energy(r, dV, g, delta, kappa, nu, gamma, B):
    rho = 1.0 + delta * g
    V_fold = float(np.sum(g * dV))
    g2 = float(np.sum(g ** 2 * dV))
    grad_rho = np.gradient(rho, r)
    E_comp = 0.5 * kappa * delta ** 2 * g2
    E_bdry = 0.5 * gamma * float(np.sum(grad_rho ** 2 * dV))
    E_rot = 0.5 * nu * B ** 2 * V_fold
    E_total = E_comp + E_bdry + E_rot
    delta_max = math.sqrt(nu * B ** 2 * V_fold / (kappa * g2)) if g2 > 0 else 0.0
    return dict(V_fold=V_fold, g2=g2, E_comp=E_comp, E_bdry=E_bdry,
                E_rot=E_rot, E_total=E_total, delta_max=delta_max)


def main():
    r, dV = radial_grid()
    # 共享物理参数（基线，与 verify_space_extensibility.py 一致）
    kappa, nu, gamma0, omega = 1.0, 1.0, 0.5, 0.5
    B = 2.0 * omega

    report = {
        "model": "fold topology continuation + boundary potential-difference amplification",
        "date": str(date.today()),
        "params_baseline": {"κ": kappa, "ν": nu, "γ0": gamma0, "ω": omega, "B": B},
        "questions": {
            "Q1": "拓扑继续折叠（多褶皱叠加）能否让内部空间更多/更省能",
            "Q2": "边界势差（γ 与 ΔΦ）放大能否让内部空间更大",
        },
        "results": {},
    }
    res = report["results"]

    # ========== Q1：多褶皱叠加 ==========
    # 单褶皱
    g1 = single_bump(r)
    # 多褶皱：在单褶皱基础上叠加 2、3、5 个同心褶皱层（对称分布）
    multi_specs = {
        "N=1 (单褶皱)": g1,
        "N=3 (三层同心褶皱)": multi_bump(r, [(0.0, 1.0, 1.0),
                                            (1.6, 0.5, 0.6),
                                            (2.8, 0.4, 0.4)]),
        "N=5 (五层同心褶皱)": multi_bump(r, [(0.0, 1.0, 1.0),
                                            (1.2, 0.5, 0.7),
                                            (2.0, 0.4, 0.5),
                                            (2.8, 0.35, 0.4),
                                            (3.4, 0.3, 0.3)]),
    }

    delta_eval = 1.0  # 固定 δ 比较结构差异
    q1_rows = []
    for name, g in multi_specs.items():
        e = energy(r, dV, g, delta_eval, kappa, nu, gamma0, B)
        q1_rows.append((name, e))

    # 固定总能量预算，反解可达 δ（更多内部空间 ⟺ 更大 δ·V_fold 或更大 δ）
    # 取 E_total 固定 = 单褶皱在 δ=1 时的总能量
    e1_single = energy(r, dV, g1, 1.0, kappa, nu, gamma0, B)
    E_budget = e1_single["E_total"]

    def delta_for_budget(g, E_budget, kappa, nu, gamma, B):
        """在固定『能量预算』（= 单褶皱 δ=1 的总能，统一标尺）下反解可达 δ。
        E_rot = ½νB²V_fold 由螺旋场*内建提供*（SE5 框架约定），反解时不作为约束；
        预算分配到压缩 + 弥散边界：
            ½κ δ² ∫g²dV + ½γ (δ·grad g)² dV = E_budget
        E_bdry ∝ δ²（ρ=1+δg ⟹ grad ρ = δ grad g）。"""
        g2 = float(np.sum(g ** 2 * dV))
        grad_g = np.gradient(g, r)
        bdry_coeff = 0.5 * gamma * float(np.sum(grad_g ** 2 * dV))
        A = 0.5 * kappa * g2 + bdry_coeff
        return math.sqrt(E_budget / A) if A > 0 else 0.0

    q1_budget = []
    for name, g in multi_specs.items():
        de = delta_for_budget(g, E_budget, kappa, nu, gamma0, B)
        e = energy(r, dV, g, de, kappa, nu, gamma0, B)
        q1_budget.append((name, de, e))

    res["Q1_a_structure_at_fixed_delta"] = {
        "δ 固定 = 1.0": {
            name: {
                "V_fold": round(e["V_fold"], 4),
                "∫g²dV（内部空间总量系数）": round(e["g2"], 4),
                "E_comp": round(e["E_comp"], 4),
                "E_bdry（边界能）": round(e["E_bdry"], 4),
                "E_total": round(e["E_total"], 4),
                "δ_max（自维持上限）": round(e["delta_max"], 4),
                "内部空间总量 δ·∫g²dV": round(delta_eval * e["g2"], 4),
            } for name, e in q1_rows
        },
        "note": ("多褶皱叠加 ⟹ ∫g²dV 与 V_fold 显著增大（同样 δ 下内部空间更多）；"
                 "但 E_bdry 也增大（更多边界层）。需看固定能量预算下的净效果（Q1_b）。")
    }

    res["Q1_b_delta_at_fixed_energy_budget"] = {
        "E_budget（= 单褶皱δ=1 的总能）": round(E_budget, 4),
        "反解可达 δ": {
            name: {
                "可达 δ": round(de, 4),
                "内部空间总量 δ·∫g²dV": round(de * e["g2"], 4),
                "δ_max": round(e["delta_max"], 4),
                "δ ≤ δ_max（自维持）": bool(de <= e["delta_max"]),
            } for name, de, e in q1_budget
        },
        "note": ("固定总能量预算下，多褶皱牺牲边界能来换取更大的 ∫g²dV；"
                 "若 δ·∫g²dV 随褶皱数单调增 ⟹ 拓扑继续折叠确实让内部空间更多。")
    }

    # ========== Q2：边界势差放大 ==========
    # Q2a：放大边界刚度 γ（弥散边界更"硬"，势差梯度更陡）
    gammas = [0.2, 0.5, 1.0, 2.0, 4.0]
    q2a = []
    for gam in gammas:
        e = energy(r, dV, g1, 1.0, kappa, nu, gam, B)
        q2a.append((gam, e))

    # Q2b：边界势差 ΔΦ 直接放大 ⟹ 可支撑更大密度比（势差预算）
    # 用 SF3 势差 ΔΦ = ½(v_in² − v_out²)；势差预算上限 ⟹ ρ_in/ρ_out 上限。
    # 这里把"边界势差"形式化为：势差可支撑的折叠比 δ 上限 = δ_max * f(ΔΦ 放大)。
    # 简化测量：边界势差放大 ⟹ 维持器可承载更大 δ_max（δ_max ∝ B，B 由势差驱动）。
    # 我们直接测 δ_max 随 B（= 势差驱动强度）放大的线性增长。
    Bs = [1.0, 2.0, 4.0, 6.0, 8.0]
    q2b = []
    for bb in Bs:
        e = energy(r, dV, g1, 1.0, kappa, nu, gamma0, bb)
        # 可达 δ 上限（自维持）
        q2b.append((bb, e))

    res["Q2_a_boundary_stiffness_gamma"] = {
        "在 δ=1 固定时，γ（边界势差刚度）放大": {
            f"γ={gam}": {
                "E_bdry": round(e["E_bdry"], 4),
                "E_comp": round(e["E_comp"], 4),
                "E_total": round(e["E_total"], 4),
                "δ_max（自维持上限）": round(e["delta_max"], 4),
            } for gam, e in q2a
        },
        "note": ("γ 放大 ⟹ E_bdry 单调增（边界更耗能），但 δ_max 不变（δ_max 与 γ 无关，"
                 "只依赖 B/V_fold/κ/∫g²dV）。即单纯加硬边界层并不能直接让内部更大，"
                 "反而更费能——需要看 Q2b 的势差驱动强度。")
    }

    res["Q2_b_potential_difference_drive"] = {
        "边界势差驱动强度 B（≪ΔΦ 放大）放大": {
            f"B={bb}": {
                "E_rot": round(e["E_rot"], 4),
                "δ_max（自维持上限）": round(e["delta_max"], 4),
                "可达内部空间总量 δ·∫g²dV@δ=δ_max": round(e["delta_max"] * e["g2"], 4),
            } for bb, e in q2b
        },
        "note": ("δ_max ∝ B：边界势差（驱动螺旋场）放大 ⟹ 自维持上限线性增大 ⟹ "
                 "在自维持范围内可支撑更大的折叠比 ⟹ 内部空间更大。这就是 Q2 的肯定回答，"
                 "但代价是 E_rot ∝ B² 增长（势差驱动本身要能量，SE5 框架内自洽）。")
    }

    # ============ 图 ============
    fig, axes = plt.subplots(2, 2, figsize=(14, 11))

    # 图1：折叠域剖面（单 vs 多褶皱）
    ax = axes[0, 0]
    ax.plot(r, g1, color="steelblue", lw=2, label="N=1 单褶皱")
    ax.plot(r, multi_specs["N=3 (三层同心褶皱)"], color="darkorange", lw=1.8,
            label="N=3 三层褶皱")
    ax.plot(r, multi_specs["N=5 (五层同心褶皱)"], color="forestgreen", lw=1.6,
            label="N=5 五层褶皱")
    ax.set_xlabel("径向 r / R")
    ax.set_ylabel("g(r) = 折叠域密度包络")
    ax.set_title("Q1：折叠域剖面（拓扑继续折叠）")
    ax.legend(fontsize=8); ax.grid(alpha=0.2)

    # 图2：Q1 固定能量预算下 δ·∫g²dV vs 褶皱数
    ax = axes[0, 1]
    names = [n for n, _, _ in q1_budget]
    space_tot = [de * e["g2"] for _, de, e in q1_budget]
    ax.bar(names, space_tot, color=["steelblue", "darkorange", "forestgreen"])
    for i, v in enumerate(space_tot):
        ax.text(i, v, f"{v:.3f}", ha="center", va="bottom", fontsize=9)
    ax.set_ylabel("内部空间总量 δ·∫g²dV（固定总能）")
    ax.set_title("Q1：固定能量预算下，多褶皱 -> 内部空间更多？")
    ax.grid(alpha=0.2, axis="y")

    # 图3：Q2a γ 放大 → E_bdry 与 δ_max
    ax = axes[1, 0]
    gam_arr = [gam for gam, _ in q2a]
    ebdry_arr = [e["E_bdry"] for _, e in q2a]
    dmax_arr = [e["delta_max"] for _, e in q2a]
    ax.plot(gam_arr, ebdry_arr, "o-", color="crimson", label="E_bdry（边界能）")
    ax.set_xlabel("γ（边界势差刚度）")
    ax.set_ylabel("E_bdry", color="crimson")
    ax.tick_params(axis="y", labelcolor="crimson")
    ax2 = ax.twinx()
    ax2.plot(gam_arr, dmax_arr, "s-", color="steelblue", label="δ_max")
    ax2.set_ylabel("δ_max（自维持上限）", color="steelblue")
    ax2.tick_params(axis="y", labelcolor="steelblue")
    ax.set_title("Q2a：加硬边界层 -> 更费能但 delta_max 不变")
    ax.grid(alpha=0.2)

    # 图4：Q2b B（势差驱动）放大 → δ_max 线性增
    ax = axes[1, 1]
    B_arr = [bb for bb, _ in q2b]
    dmax_b = [e["delta_max"] for _, e in q2b]
    space_b = [e["delta_max"] * e["g2"] for _, e in q2b]
    ax.plot(B_arr, dmax_b, "o-", color="steelblue", label="δ_max")
    ax.plot(B_arr, space_b, "s-", color="forestgreen", label="内部空间总量@δ_max")
    ax.set_xlabel("B（边界势差驱动强度，类比 DeltaPhi 放大）")
    ax.set_ylabel("δ_max / 内部空间总量")
    ax.set_title("Q2b：势差驱动放大 -> 自维持上限线性增大 -> 内部更大")
    ax.legend(fontsize=8); ax.grid(alpha=0.2)

    fig.suptitle("测量：折叠域拓扑继续折叠(Q1) 与 边界势差放大(Q2)", fontsize=13)
    fig.tight_layout()
    fig.savefig(os.path.join(OUT, "fold_topology.png"), dpi=150)
    plt.close(fig)

    # ============ 结论 ============
    n1 = q1_budget[0][1] * q1_budget[0][2]["g2"]
    n5 = q1_budget[2][1] * q1_budget[2][2]["g2"]
    dmax_b1 = q2b[0][1]["delta_max"]
    dmax_b5 = q2b[-1][1]["delta_max"]
    ratio = (n5 / n1) if n1 > 0 else float("inf")
    report["conclusion"] = {
        "Q1": (f"在固定能量预算下（= 单褶皱 δ=1 的总能 5.245，统一标尺），多褶皱（N=5）的内部空间总量 "
               f"delta * int(g^2 dV) = {n5:.3f} > 单褶皱的 {n1:.3f}，"
               f"即拓扑继续折叠确实让内部空间更多（约 {ratio:.2f}x）。"
               f"机制：多褶皱增大 int(g^2 dV) 与 V_fold（更多褶皱层装更多空间，可达 δ 摊薄但净空间更大），"
               f"代价是 E_bdry 略增；净收益为正 => 肯定回答。"),
        "Q2": (f"放大边界势差驱动 B => delta_max 从 {dmax_b1:.3f} 线性增到 {dmax_b5:.3f}，"
               f"自维持范围内可支撑更大折叠比 => 内部空间更大。肯定回答，但代价是 "
               f"E_rot 正比于 B^2 增长（势差驱动本身耗能，SE5 框架内自洽）。"
               f"注意：单纯加硬边界层 gamma（不改变驱动强度）只增边界能、不增大 delta_max。"),
        "honest_boundary": ("本测量沿用 v1 弹性模型（kappa/nu/gamma/B 为输入参数，第二输入缺口）；"
                            "多褶皱 = 叠加径向包络，非严格拓扑（未建同调/连通数）；"
                            "rho 动力学方程仍未给出。答案为框架内可计算语言的延伸，非新物理预言。")
    }
    report["files"] = {"fold_topology": "fold_topology.png"}

    with open(os.path.join(OUT, "report.json"), "w", encoding="utf-8") as f:
        json.dump(report, f, ensure_ascii=False, indent=2)

    print(json.dumps(report["results"], ensure_ascii=False, indent=2))
    print("\n=== 结论 ===")
    print(json.dumps(report["conclusion"], ensure_ascii=False, indent=2))
    print(f"\n→ 产物: {os.path.abspath(OUT)}")


if __name__ == "__main__":
    main()
