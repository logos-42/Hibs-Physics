#!/usr/bin/env python3
"""魔角石墨烯 × 聚变：场天花板七层账本数值验证（M1–M8）

对应计划页 docs/wiki/moire-field-ceiling-plan.md（E1）。
leo（2026-09-23）：魔角石墨烯（1° 夹角）方案若用来产生磁场、再由磁场引发
引力场约束实现可控核聚变，数据如何变化？

本脚本不做新物理，只做一件事：把仓库已证条目
  · PF3   B_min = √(2μ₀nkT)        （β ≤ 1 的最小场强）
  · FC1   n_max = βB²/(4μ₀kT)      （FRC β≈1 密度上限）
  · 二轮修正链  τ_E = τ₀/√(1−μ)，τ₀ = a²/D₀
  · FC11b μ < 1 − m_e/m_i ⟺ 1−μ > m_e/m_i（RMF 窗口硬天花板）
里的"场源"换成一个魔角石墨烯（或同族多层）线圈，看那一串数字变成什么，
以及死在哪一层。外部材料的 B_c2 / n_s 取文献报道值（上界/乐观包络，见 §6 表）。

数值检验（对应 verify_all.py 断言区 MF-M1..M8）：
  M1  材料层：MATBG/MATTG 的 Tc、B_c2⊥/∥ 上限表
  M2  场-密度层：B_min(n_design) 与各场源 n_max(B)、场门 χ_B
  M3  功率层：P ∝ B⁴、同功率体积 ∝ B^-4（相对 B=9T, β=1 基准）
  M4  μ 窗口层：X_req(B) = (τ₀n/A)² vs FC11 地板 m_e/m_i，可行性与裕度
  M5  ★死活判据：B_death(a) —— 场天花板低于它 ⟹ μ 窗口关闭 ⟹ 无解
  M6  载流层：二维超导片超流密度 vs REBCO 片电流（安匝缺口）
  M7  制冷层：亚开尔文容量 vs 装置冷量（Carnot + 容量缺口）
  M8  数据变化总表（本轮交付物）
"""
import json
import math
import os
from datetime import date

import numpy as np

OUT = os.path.join(os.path.dirname(__file__), "..", "artifacts", "moirefield")
os.makedirs(OUT, exist_ok=True)

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

# ---------------------------------------------------------------- 常数
MU0 = 4 * math.pi * 1e-7          # 真空磁导率 H/m
KB = 1.380649e-23                 # 玻尔兹曼常数 J/K
EV = 1.602176634e-19              # 电子伏 J
ME = 9.1093837015e-31             # 电子质量 kg
U = 1.66053906660e-27             # 原子质量单位
MI = 2.5 * U                      # D-T 平均离子质量（沿用 verify_frc_compact）
T_KEV = 15.0
KT_J = T_KEV * 1e3 * EV

BETA = 1.0                        # FRC β≈1
N_DESIGN = 1e20                   # 仓库参考设计密度（μ≥0.9997 那一轮的口径）
A_REF = 0.2                       # 参考装置尺寸 a=0.2 m（0.6m 环）
D0 = 1.11                         # m²/s，ITER 级 μ=0 标定（二轮修正）
TAU0 = A_REF ** 2 / D0            # s
# 劳森：n·T·τ = 3e21 keV·s/m³ @15keV ⟹ n·τ = 2e20
NT_LAWSON = 2e20
FLOOR = ME / MI                   # FC11 地板：1−μ > m_e/m_i

SIGMA_V_DT = 2.6e-22              # m³/s @15 keV
E_FUS_DT = 17.6e6 * EV

# ---------------------------------------------------------------- 外部材料上限（§6 表）
SOURCES = {
    "MATBG_N2_perp": dict(B=0.12, label="MATBG (N=2) 面外 B_c2",
                          src="Díez-Mérida 2023 NatCommun 14,2396"),
    "MATBG_N2_par": dict(B=1.6, label="MATBG (N=2) 面内 B_c",
                         src="Qin&MacDonald 2021 PRL 127,097001"),
    "MATTG_N3_par": dict(B=10.0, label="MATTG (N=3) 面内 B_c（下界）",
                         src="Cao 2021 Nature 595,526"),
    "ITER_TF": dict(B=5.3, label="ITER TF 导体级场", src="ITER 公开参数"),
    "SPARC_TF": dict(B=12.2, label="SPARC TF", src="PF 轮引用"),
    "CFR2_vac": dict(B=9.0, label="CFR2 真空场（紧凑 FRC 基准）",
                     src="Slough 2025 Nucl.Fusion 65,106019"),
    "CFR2_comp": dict(B=35.0, label="CFR2 压缩后场（脉冲）", src="同上"),
}


def n_max(B, beta=BETA):
    """FC1: FRC β≈1 平衡密度上限 n = βB²/(4μ₀kT)"""
    return beta * B * B / (4 * MU0 * KT_J)


def B_min(n, beta=BETA):
    """PF3 反解: β≤1 要求 B² ≥ 2μ₀nkT/β ... 取 n = βB²/(4μ₀kT) 的逆"""
    return math.sqrt(4 * MU0 * KT_J * n / beta)


def n_op(B):
    """运行密度 = min(设计密度, 该场下的密度上限)"""
    return min(N_DESIGN, n_max(B))


def tau_lawson(n):
    """劳森要求的最小约束时间 τ = 2e20 / n"""
    return NT_LAWSON / n


def X_req(B, a=A_REF):
    """所需 (1−μ) 的上限：τ_E = τ₀/√(1−μ) ≥ τ_L ⟹ 1−μ ≤ (τ₀/τ_L)²"""
    tau0 = a ** 2 / D0
    return (tau0 / tau_lawson(n_op(B))) ** 2


def B_death(a=A_REF):
    """使 X_req(B) = FLOOR 的场：B 低于它 ⟹ μ 窗口关闭（无解）。
    X_req ∝ n² 且 n = βB²/(4μ₀kT) ⟹ B_death ∝ 1/a。"""
    tau0 = a ** 2 / D0
    n_cross = (NT_LAWSON / tau0) * math.sqrt(FLOOR)
    return math.sqrt(4 * MU0 * KT_J * n_cross / BETA)


def p_rel(B, B_ref=9.0):
    """满 β 分支：同一装置几何可及的功率密度 P ∝ n_max²⟨σv⟩ ∝ (B/B_ref)⁴"""
    return (n_max(B) / n_max(B_ref)) ** 2


def v_rel(B, B_ref=9.0):
    """同功率所需体积（满 β 分支，∝ B^-4）"""
    return 1.0 / p_rel(B, B_ref)


def chi_mu(B, a=A_REF):
    """μ 门裕度：X_req/FLOOR > 1 ⟹ 可行"""
    return X_req(B, a) / FLOOR


# ---------------------------------------------------------------- M1
def M1_material():
    rows = []
    for k in ("MATBG_N2_perp", "MATBG_N2_par", "MATTG_N3_par"):
        s = SOURCES[k]
        rows.append(dict(key=k, label=s["label"], B_c2_T=s["B"], source=s["src"]))
    # 临界温度与工作温区（外部实验值）
    temps = [
        dict(system="MATBG (N=2, θ≈1.1°)", Tc_K=[1.1, 2.1], Tc_max_reported=3.5,
             T_op_K=0.5, note="栅定义器件，稀释制冷机 20–40 mK 基温测量"),
        dict(system="MATTG/MAT4G/MAT5G (N≥3)", Tc_K=[2.0, 3.5], Tc_max_reported=3.5,
             T_op_K=1.0, note="面内场 >10T 仍超导（Pauli 违背 2–3×）"),
        dict(system="REBCO 带材（工程基准）", Tc_K=[90.0, 92.0], Tc_max_reported=92.0,
             T_op_K=20.0, note="4.2–20 K 运行，非 1 K 级"),
    ]
    return dict(field_ceilings=rows, operating_temperatures=temps)


# ---------------------------------------------------------------- M2
def M2_field_density():
    b_min = B_min(N_DESIGN)
    rows = []
    for k, s in SOURCES.items():
        B = s["B"]
        rows.append(dict(
            key=k, label=s["label"], B_cap_T=B,
            chi_B_required_over_cap=B_min(N_DESIGN) / B,   # <1 ⟹ 该场源够用
            n_max_perm3=n_max(B), n_op_perm3=n_op(B),
            density_ratio=n_op(B) / N_DESIGN,
            beta_impossible=(B < B_min(N_DESIGN)),
        ))
    return dict(n_design_perm3=N_DESIGN, B_min_design_T=b_min, rows=rows)


# ---------------------------------------------------------------- M3
def M3_power():
    rows = []
    for k, s in SOURCES.items():
        B = s["B"]
        rows.append(dict(key=k, label=s["label"], B_cap_T=B,
                         p_rel=p_rel(B), V_rel_for_same_power=v_rel(B),
                         p_fus_dens_Wm3=n_max(B) ** 2 / 4 * SIGMA_V_DT * E_FUS_DT))
    return dict(baseline="B=9T, β=1 (CFR2 真空场)，满 β 分支 P ∝ B⁴", rows=rows)


# ---------------------------------------------------------------- M4
def M4_mu_window():
    rows = []
    for k, s in SOURCES.items():
        B = s["B"]
        X = X_req(B)
        rows.append(dict(key=k, label=s["label"], B_cap_T=B,
                         tau_lawson_s=tau_lawson(n_op(B)),
                         X_req_cap=X, floor_FC11=FLOOR,
                         chi_mu=X / FLOOR, feasible=(X > FLOOR)))
    # 设计密度固定分支（n = n_design，场只用于满足 β≤1）
    return dict(tau0_s=TAU0, floor_FC11=FLOOR,
                x_req_at_design=(TAU0 / tau_lawson(N_DESIGN)) ** 2,
                chi_mu_at_design=((TAU0 / tau_lawson(N_DESIGN)) ** 2) / FLOOR,
                rows=rows)


# ---------------------------------------------------------------- M5
def M5_death_threshold():
    scan = []
    for a in (0.05, 0.1, 0.15, 0.2, 0.3, 0.5, 1.0, 2.0):
        scan.append(dict(a_m=a, B_death_T=B_death(a),
                         verdict_sources={
                             k: ("open" if s["B"] > B_death(a) else "CLOSED")
                             for k, s in SOURCES.items()}))
    return dict(a_ref_m=A_REF, B_death_ref_T=B_death(A_REF), scan=scan)


# ---------------------------------------------------------------- M6
def M6_current_gate():
    # REBCO 片超流密度：n_s = m*/(μ₀ e² λ²)，λ_ab(0)=150 nm，m*=3 m_e，d=100 nm
    lam, mstar, d = 150e-9, 3 * ME, 100e-9
    n_s_3d = mstar / (MU0 * EV ** 2 * lam ** 2)      # m^-3
    rebco_sheet_cm2 = n_s_3d * d * 1e-4              # cm^-2
    matbg_opt, matbg_full = 1.96e11, 2.88e12         # cm^-2（最优掺杂 / 满填充）
    # 实测片电流（乐观化：250 nA 体临界电流 / 1 μm 宽，宽度为假设）
    matbg_K_A_cm = 250e-9 / 1e-6 * 1e-2              # A/cm
    rebco_K_A_cm = 1000.0                            # A/cm（4.2K, 19T 实测 Ic/width）
    return dict(rebco_sheet_ns_cm2=rebco_sheet_cm2,
                matbg_ns_opt_cm2=matbg_opt, matbg_ns_full_cm2=matbg_full,
                ns_gap_opt=rebco_sheet_cm2 / matbg_opt,
                ns_gap_full=rebco_sheet_cm2 / matbg_full,
                matbg_K_A_cm=matbg_K_A_cm, rebco_K_A_cm=rebco_K_A_cm,
                K_gap=rebco_K_A_cm / matbg_K_A_cm,
                note="片电流用 250 nA/1μm 宽（宽度为假设）；超流面密度比不需宽度")


# ---------------------------------------------------------------- M7
def M7_cryo_gate():
    iter_cryo_W = 75e3          # ITER 低温工厂当量（4.5 K）
    dil_W_05K = 20e-3           # 稀释制冷机 ~20 mW @0.5 K（量级）
    dil_W_01K = 1.5e-3          # ~1–2 mW @0.1 K
    T_hot = 293.0
    carnot = lambda Tc: T_hot / Tc - 1
    return dict(iter_cryo_W=iter_cryo_W, dil_capacity_05K_W=dil_W_05K,
                dil_capacity_01K_W=dil_W_01K,
                capacity_gap_05K=iter_cryo_W / dil_W_05K,
                capacity_gap_01K=iter_cryo_W / dil_W_01K,
                carnot_45K=carnot(4.5), carnot_05K=carnot(0.5),
                carnot_ratio=carnot(0.5) / carnot(4.5),
                matbg_T_op_K=0.5, rebco_T_op_K=20.0)


# ---------------------------------------------------------------- M8
def M8_summary(m2, m3, m4, m5, m6, m7):
    rows = []
    for k, s in SOURCES.items():
        B = s["B"]
        rows.append(dict(
            source=s["label"], B_cap_T=B,
            n_op_perm3=n_op(B),
            P_rel=p_rel(B), V_rel=v_rel(B),
            chi_mu=chi_mu(B), mu_feasible=(X_req(B) > FLOOR),
            verdict=("可用（物理层过门；工程层见 M6/M7）" if X_req(B) > FLOOR
                     else "无解（μ 窗口关闭，FC11）"),
        ))
    return dict(rows=rows,
                B_death_ref_T=m5["B_death_ref_T"],
                floor_FC11=m4["floor_FC11"])


# ---------------------------------------------------------------- 图
def figure1(m3):
    Bs = np.logspace(math.log10(0.05), math.log10(60), 400)
    fig, ax1 = plt.subplots(figsize=(9, 5.6))
    ax1.loglog(Bs, [n_max(B) for B in Bs], "k-", lw=2, label="密度上限 n_max(B) ∝ B²")
    ax1.axhline(N_DESIGN, color="gray", ls=":", lw=1.4, label="参考设计密度 1e20 m^-3")
    ax1.set_xlabel("场源天花板 B_cap (T)")
    ax1.set_ylabel("可约束密度 n (m^-3)", color="k")
    ax1.grid(alpha=0.3, which="both")

    ax2 = ax1.twinx()
    ax2.loglog(Bs, [p_rel(B) for B in Bs], "C3--", lw=2, label="功率 P ∝ B⁴（相对 9T）")
    ax2.loglog(Bs, [v_rel(B) for B in Bs], "C0-.", lw=2, label="同功率体积 V ∝ B^-4")
    ax2.set_ylabel("相对值（基准 B=9T, β=1）")

    marks = [("MATBG⊥ 0.12T", 0.12), ("MATBG∥ 1.6T", 1.6), ("CFR2 9T", 9.0),
             ("MATTG∥ 10T", 10.0), ("压缩 35T", 35.0)]
    h, l = ax1.get_legend_handles_labels()
    h2, l2 = ax2.get_legend_handles_labels()
    ax1.legend(h + h2, l + l2, loc="lower right", fontsize=8.5)
    for name, x in marks:
        ax1.axvline(x, color="C1", alpha=0.25, lw=1)
        ax1.text(x * 1.06, 2.2 * n_max(x), name, rotation=90, fontsize=8,
                 color="C1", va="bottom", ha="left")
    ax1.set_title("场天花板 → 密度/功率天花板（FC1 + PF3 标度）")
    fig.subplots_adjust(left=0.11, right=0.89, top=0.92, bottom=0.11)
    fig.savefig(os.path.join(OUT, "fig_field_ceiling_scaling.png"), dpi=150)
    plt.close(fig)


def figure2(m4, m5):
    Bs = np.logspace(math.log10(0.02), math.log10(20), 500)
    fig, ax = plt.subplots(figsize=(9, 5.6))
    ax.loglog(Bs, [X_req(B) for B in Bs], "C3-", lw=2.2, label="所需 1−μ 上限 X_req(B)")
    ax.axhline(FLOOR, color="C0", lw=2.2,
               label=f"FC11 地板 m_e/m_i = {FLOOR:.3e}（窗口下界）")
    bd = m5["B_death_ref_T"]
    ax.axvline(bd, color="k", ls="--", lw=1.6, label=f"B_death = {bd:.3f} T")
    ax.fill_between([0.02, bd], 1e-12, 1e2, color="red", alpha=0.10)
    ax.text(0.03, 1e-2, "死区：B < B_death\nμ 窗口关闭（无解）", fontsize=10, color="red")
    for k in ("MATBG_N2_perp", "MATBG_N2_par", "MATTG_N3_par", "CFR2_comp"):
        s = SOURCES[k]
        ax.plot([s["B"]], [X_req(s["B"])], "ko", ms=6)
        dy = 26 if k == "MATBG_N2_perp" else 12
        ha = "left" if k == "MATBG_N2_perp" else "right"
        ax.annotate(s["label"], (s["B"], X_req(s["B"])), textcoords="offset points",
                    xytext=(8 if ha == "left" else -6, dy), fontsize=8.5, ha=ha)
    ax.annotate(f"设计密度分支裕度 {m4['chi_mu_at_design']:.2f}×（贴着地板）",
                (2.2, m4["floor_FC11"]), textcoords="offset points",
                xytext=(0, -18), fontsize=8.5, color="C0")
    ax.set_xlim(0.02, 20)
    ax.set_ylim(1e-12, 1e2)
    ax.set_xlabel("场源天花板 B_cap (T)")
    ax.set_ylabel("所需 (1−μ) 上限")
    ax.grid(alpha=0.3, which="both")
    ax.set_title("μ 窗口判决：X_req(B) 与 FC11 地板的交点（a=0.2m, β=1, T=15keV）")
    ax.legend(loc="upper left", fontsize=9)
    fig.subplots_adjust(left=0.11, right=0.96, top=0.92, bottom=0.11)
    fig.savefig(os.path.join(OUT, "fig_mu_window_verdict.png"), dpi=150)
    plt.close(fig)


def figure3(m5):
    a_s = np.logspace(math.log10(0.04), math.log10(3.0), 200)
    fig, ax = plt.subplots(figsize=(9, 5.6))
    ax.loglog(a_s, [B_death(a) for a in a_s], "k-", lw=2.4,
              label="B_death(a) = 0.997·(0.2/a) T（μ 窗口边界）")
    for k, col in (("MATBG_N2_perp", "C3"), ("MATBG_N2_par", "C1"), ("MATTG_N3_par", "C0")):
        s = SOURCES[k]
        ax.axhline(s["B"], color=col, ls="--", lw=1.8,
                   label=f"{s['label']} = {s['B']} T")
    ax.fill_between([0.04, 3.0], 1e-3, 1.0, color="red", alpha=0.08)
    ax.set_xlim(0.04, 3.0)
    ax.set_ylim(0.05, 40)
    ax.set_xlabel("装置尺寸 a (m)")
    ax.set_ylabel("所需场天花板 B_cap (T)")
    ax.grid(alpha=0.3, which="both")
    ax.set_title("每条材料线的水平线与 B_death(a) 曲线：线在下 = 该材料使该尺寸无解")
    ax.legend(loc="upper right", fontsize=9)
    fig.subplots_adjust(left=0.11, right=0.96, top=0.92, bottom=0.11)
    fig.savefig(os.path.join(OUT, "fig_Bdeath_vs_size.png"), dpi=150)
    plt.close(fig)


def figure4(m6, m7):
    labels = [f"场门（1e20 需 {B_min(N_DESIGN):.2f} T\nvs MATBG⊥ 0.12 T）",
              "载流门（片电流）", "载流门（片超流密度）", "制冷门（容量@0.5K）"]
    vals = [B_min(N_DESIGN) / 0.12, m6["K_gap"], m6["ns_gap_full"],
            m7["capacity_gap_05K"]]
    fig, ax = plt.subplots(figsize=(9, 5.0))
    y = np.arange(len(vals))
    ax.barh(y, vals, color=["C3", "C1", "C2", "C0"], alpha=0.85)
    ax.set_yticks(y)
    ax.set_yticklabels(labels, fontsize=9)
    ax.set_xscale("log")
    ax.set_xlim(5, max(vals) * 12)
    for yi, v in zip(y, vals):
        ax.text(v * 1.2, yi, f"{v:.2e}×", va="center", fontsize=9)
    ax.set_xlabel("缺口倍数（>1 = 该层否决）")
    ax.set_title("四条工程门的缺口（MATBG, N=2）")
    ax.grid(alpha=0.3, axis="x")
    fig.subplots_adjust(left=0.30, right=0.94, top=0.90, bottom=0.13)
    fig.savefig(os.path.join(OUT, "fig_gate_gaps.png"), dpi=150)
    plt.close(fig)


# ---------------------------------------------------------------- 主流程
def main():
    m1 = M1_material()
    m2 = M2_field_density()
    m3 = M3_power()
    m4 = M4_mu_window()
    m5 = M5_death_threshold()
    m6 = M6_current_gate()
    m7 = M7_cryo_gate()
    m8 = M8_summary(m2, m3, m4, m5, m6, m7)

    # ---- 断言（回归锚点，确立后不可改） ----
    assert abs(m2["B_min_design_T"] - 1.0991) < 5e-3, m2["B_min_design_T"]
    rows = {r["key"]: r for r in m2["rows"]}
    assert abs(rows["MATBG_N2_perp"]["n_max_perm3"] / 1.194e18 - 1) < 5e-3
    assert abs(rows["MATBG_N2_par"]["n_max_perm3"] / 2.12e20 - 1) < 5e-3
    assert abs(rows["CFR2_comp"]["n_max_perm3"] / 1.015e23 - 1) < 5e-3
    # 场门：0.12 T 场源在 1e20 设计下连 β≤1 都做不到
    assert rows["MATBG_N2_perp"]["beta_impossible"] is True
    assert rows["MATBG_N2_par"]["beta_impossible"] is False
    # μ 门：0.12 T 死、1.6 T 与 10 T 活
    m4r = {r["key"]: r for r in m4["rows"]}
    assert m4r["MATBG_N2_perp"]["feasible"] is False
    assert m4r["MATBG_N2_perp"]["chi_mu"] < 1e-3
    assert m4r["MATBG_N2_par"]["feasible"] is True
    assert m4r["MATTG_N3_par"]["feasible"] is True
    # 设计密度分支裕度只有 ~1.5×（仓库自身贴着 FC11 地板）
    assert abs(m4["chi_mu_at_design"] - 1.476) < 0.03, m4["chi_mu_at_design"]
    # B_death 锚点与 1/a 标度
    assert abs(m5["B_death_ref_T"] - 0.9966) < 3e-3, m5["B_death_ref_T"]
    assert abs(B_death(0.1) / m5["B_death_ref_T"] - 2.0) < 0.02
    assert abs(B_death(1.0) / m5["B_death_ref_T"] - 0.2) < 0.02
    # 功率/体积标度
    p = {r["key"]: r for r in m3["rows"]}
    assert abs(p["CFR2_vac"]["p_rel"] - 1.0) < 1e-12
    assert abs(p["MATBG_N2_par"]["p_rel"] / 9.99e-4 - 1) < 0.02
    assert abs(p["MATBG_N2_par"]["V_rel_for_same_power"] / 1001.0 - 1) < 0.02
    assert abs(p["MATBG_N2_perp"]["p_rel"] / 3.16e-8 - 1) < 0.03
    assert abs(p["MATBG_N2_perp"]["V_rel_for_same_power"] / 3.16e7 - 1) < 0.05
    assert abs(p["CFR2_comp"]["p_rel"] / 229.0 - 1) < 0.02
    # 载流门与制冷门量级
    assert 1e3 < m6["ns_gap_full"] < 1e5
    assert 1e5 < m6["K_gap"] < 1e6
    assert 3e6 < m7["capacity_gap_05K"] < 5e6

    figure1(m3)
    figure2(m4, m5)
    figure3(m5)
    figure4(m6, m7)

    report = dict(
        meta=dict(title="魔角石墨烯 × 聚变：场天花板七层账本",
                  script="scripts/verify_moire_field.py",
                  date=str(date.today()), script_version="1.0",
                  constants=dict(mu0=MU0, k_B=KB, T_keV=T_KEV, beta=BETA,
                                 n_design=N_DESIGN, a_ref=A_REF, D0=D0,
                                 tau0_s=TAU0, floor_FC11=FLOOR,
                                 B_death_ref_T=m5["B_death_ref_T"]),
                  sources={k: v["src"] for k, v in SOURCES.items()}),
        results=dict(M1_material=m1, M2_field_density=m2, M3_power=m3,
                     M4_mu_window=m4, M5_death_threshold=m5,
                     M6_current_gate=m6, M7_cryo_gate=m7, M8_summary=m8),
        honesty=["全部结论 = PF3/FC1/FC11b/AMC1 已证条目的直接代入（真但平凡），无新物理预言",
                 "μ 主动产生机制 = 第二输入缺口（未变）；本轮只算\"需要多少 μ、窗口是否打开\"",
                 "二维材料 B_c2/n_s/I_c 取文献上界（乐观包络），多器件分散",
                 "载流门与制冷门是量级账，不是装置设计；片电流用 1μm 宽假设",
                 "FET 栅控是 MATBG 超导的必要条件，线圈化需逐层栅极——未计工程代价"],
    )

    with open(os.path.join(OUT, "report.json"), "w", encoding="utf-8") as f:
        json.dump(report, f, ensure_ascii=False, indent=2)

    lines = []
    lines.append("魔角石墨烯 × 聚变：场天花板七层账本（M1–M8）")
    lines.append(f"参考装置 a={A_REF} m, β={BETA}, T={T_KEV} keV, 设计密度 {N_DESIGN:.0e} m⁻³")
    lines.append(f"劳森 n·τ = {NT_LAWSON:.0e}；τ₀ = {TAU0:.4f} s；FC11 地板 m_e/m_i = {FLOOR:.4e}")
    lines.append("")
    lines.append(f"M2  β≤1 所需最小场（n=1e20）: B_min = {m2['B_min_design_T']:.3f} T")
    lines.append("    → 两道 ~1T 门槛：B<1.099T 撑不住 1e20（β>1）；"
                 f"B<{m5['B_death_ref_T']:.3f}T 任何密度都无解（μ 窗口关闭）")
    lines.append(f"    设计密度分支自身裕度 χ_μ = {m4['chi_mu_at_design']:.3f}（仓库设计贴着 FC11 地板）")
    lines.append("")
    lines.append("M8 数据变化总表")
    hdr = f"{'场源':<28}{'B_cap/T':>9}{'n_op/m⁻³':>12}{'P_rel':>10}{'V_rel':>10}{'χ_μ':>10}  判决"
    lines.append(hdr)
    for r in m8["rows"]:
        lines.append(f"{r['source']:<28}{r['B_cap_T']:>9.2f}{r['n_op_perm3']:>12.3e}"
                     f"{r['P_rel']:>10.3e}{r['V_rel']:>10.3e}{r['chi_mu']:>10.3e}  {r['verdict']}")
    lines.append("")
    lines.append(f"M5 死活判据 B_death(a=0.2m) = {m5['B_death_ref_T']:.4f} T"
                 "（B_cap 低于它 ⟹ μ 窗口关闭 ⟹ 无解，不是更难）")
    for row in m5["scan"][:5]:
        closed = [k for k, v in row["verdict_sources"].items() if v == "CLOSED"]
        lines.append(f"    a={row['a_m']:>5.2f} m  B_death={row['B_death_T']:>7.3f} T"
                     f"  CLOSED 场源={closed}")
    lines.append("")
    lines.append(f"M6 载流门: REBCO 片超流密度 {m6['rebco_sheet_ns_cm2']:.2e} cm⁻²"
                 f" vs MATBG 满填充 {m6['matbg_ns_full_cm2']:.2e} cm⁻² ⟹ {m6['ns_gap_full']:.2e}×")
    lines.append(f"            片电流: MATBG {m6['matbg_K_A_cm']:.2e} A/cm vs REBCO"
                 f" {m6['rebco_K_A_cm']:.0f} A/cm ⟹ {m6['K_gap']:.2e}×")
    lines.append(f"M7 制冷门: ITER 冷量 {m7['iter_cryo_W']/1e3:.0f} kW @4.5K vs 稀释制冷机"
                 f" {m7['dil_capacity_05K_W']*1e3:.0f} mW @0.5K ⟹ {m7['capacity_gap_05K']:.2e}×")
    lines.append(f"            Carnot 因子 {m7['carnot_45K']:.1f}(4.5K) → {m7['carnot_05K']:.0f}(0.5K)"
                 f" = {m7['carnot_ratio']:.1f}×")

    with open(os.path.join(OUT, "summary.txt"), "w", encoding="utf-8") as f:
        f.write("\n".join(lines) + "\n")

    print("\n".join(lines))


if __name__ == "__main__":
    main()
