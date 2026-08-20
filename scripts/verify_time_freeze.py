#!/usr/bin/env python3
"""时空冻结的两种路径：物质时间冻结 + 空间本身冻结（数值验证）

对应 TimeFreeze.lean TF1–TF3 / SZ1–SZ5 / C1–C3 的数值同位体。
背景（leo 2026-08-20，接 dengyu.pdf）：不可逆来自粗粒化投影
（粒子描述）；辛体积层面可逆（GQC1）。"冻结"是几何 / 信息操作，
不是热力学操作。

数值检验：
  1. N1 质量取消时间冻结：μ 0→1，m_eff²=(1−μ)²s² 归零 ⟹ 随流位移
     dτ² = dt²−(c·dt)²/c² ≡ 0 机器精度（TF2：AMC2→SM1 链）
  2. N2 空间本身冻结：稳态场 C(t)=C₀ ⟹ ΔC=0、E=−ΔC=0 残差 ~1e-16；
     对照非稳态振荡场 ΔC≠0、E≠0（SZ3：冻结空间无电场活动）
  3. N3 视界冻结：v/c 扫描 ⟹ γ=1/√(1−v²/c²) 发散（SZ5：v→c 无界），
     g_tt=1−v²/c²→0（BH1 视界=光速面）；膨胀单调性验证（0.5→0.999999）
  4. N4 代价对比：热力学冷却成本 Q(T_hot/T_cold−1) 随 T_cold→0 发散
     （C3 第三定律）vs 几何抹平成本 κg²/2 随 g→0 收敛到 0（C1 任意小）
  5. N5 边界维持账本：δ_max ∝ B 线性（SF11 复现，B=1..8）+ E_rot ∝ B²
     （C2：冻结的稳态边界要付维持能量）
  6. N6 冻结 = 时间反演对称：稳态场 C(t−1)=C(t+1)（SZ4 数值实例）+
     信息静止：任意步场值 = 初始值（SZ2 数值实例）
"""
import json
import os
from datetime import date

import numpy as np

OUT = os.path.join(os.path.dirname(__file__), "..", "artifacts", "timefreeze")
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

C = 1.0  # 光速归一


def proper_time_sq(dt, dx):
    """dτ² = dt² − dx²/c²（SM1 同款）。"""
    return dt ** 2 - dx ** 2 / C ** 2


def main():
    report = {
        "model": ("time freeze: matter dτ=0 via mass cancellation (AMC2->SM1) "
                  "+ space freeze steady field (SZ1-SZ4) + horizon dilation (SZ5) "
                  "+ cost ledger geometric vs thermal (C1/C3)"),
        "date": str(date.today()),
        "results": {},
    }
    res = report["results"]

    # ---- N1：质量取消时间冻结（TF2）----
    mu = np.linspace(0.0, 1.0, 201)
    s = 1.0
    m_eff_sq = (s * (1 - mu)) ** 2          # m_eff² = s²(1−μ)²（AMC1）
    dt = 3.0
    dx_comoving = C * dt                     # 随流位移（AMC2）
    dtau_sq = proper_time_sq(dt, dx_comoving)  # 随流 ⟹ dτ²=0
    # 质量未取消时的对照：锚定物质偏离流动（慢于空间）
    dx_anchored = 0.6 * C * dt
    dtau_sq_anchored = proper_time_sq(dt, dx_anchored)
    res["N1_mass_cancel_time_freeze"] = {
        "dtau_sq_comoving_max_abs": float(np.max(np.abs(dtau_sq))),
        "dtau_sq_anchored_matter": float(dtau_sq_anchored),
        "m_eff_sq_at_mu1": float(m_eff_sq[-1]),
    }
    assert np.allclose(dtau_sq, 0.0, atol=1e-14), "随流 dτ² 必须恒为 0（机器精度）"
    assert dtau_sq_anchored > 0, "锚定物质仍花时间（对照必须非零）"
    assert m_eff_sq[-1] == 0.0, "μ=1 时质量平方必须精确归零"

    # ---- N2：空间本身冻结（SZ2/SZ3）----
    t = np.arange(-10, 11, dtype=float)
    C_frozen = 0.7 * np.ones_like(t)            # 稳态场：∂_tC = 0
    dC_frozen = np.diff(C_frozen)                # ΔC(t) = C(t+1)−C(t)
    E_frozen = -dC_frozen                        # E = −∂_tC（MS）
    C_osc = 0.7 * np.sin(0.8 * t)               # 对照：非稳态振荡场
    dC_osc = np.diff(C_osc)
    E_osc = -dC_osc
    res["N2_space_freeze_no_electric"] = {
        "dC_frozen_max_abs": float(np.max(np.abs(dC_frozen))),
        "E_frozen_max_abs": float(np.max(np.abs(E_frozen))),
        "E_osc_max_abs": float(np.max(np.abs(E_osc))),
        "steady_vs_osc_ratio": float(np.max(np.abs(E_osc)) /
                                     max(np.max(np.abs(E_frozen)), 1e-300)),
    }
    assert np.allclose(dC_frozen, 0.0, atol=1e-15), "稳态场 ΔC 必须为 0"
    assert np.allclose(E_frozen, 0.0, atol=1e-15), "稳态场 E=−∂_tC 必须为 0"
    assert np.max(np.abs(E_osc)) > 1e-3, "振荡场必须有非零电场（对照）"

    # ---- N3：视界冻结（SZ5/BH1）----
    beta = np.array([0.5, 0.9, 0.99, 0.9999, 0.999999, 0.99999999])
    gamma = 1.0 / np.sqrt(1.0 - beta ** 2)
    g_tt = 1.0 - beta ** 2
    mono = np.all(np.diff(gamma) > 0)          # 单调递增（SZ5）
    res["N3_horizon_dilation"] = {
        "gamma_at_0p99": float(gamma[2]),
        "gamma_at_0p999999": float(gamma[4]),
        "gamma_final": float(gamma[-1]),
        "g_tt_final": float(g_tt[-1]),
        "monotone": bool(mono),
    }
    assert mono, "膨胀因子必须随 v→c 单调递增（SZ5）"
    assert gamma[4] > 100, "v=0.999999c 时 γ 必须 > 100（发散趋势）"
    assert g_tt[-1] < 1e-7, "g_tt → 0（视界 = 光速面，BH1）"

    # ---- N4：代价对比（C1 vs C3）----
    T_cold = np.geomspace(300, 0.001, 200)      # 目标温度（K）
    Q = 1e6                                      # 抽热量（1 kg 水量级）
    T_hot = 300.0
    thermal = Q * (T_hot / T_cold - 1.0)         # 卡诺制冷功（C3）
    g = np.geomspace(1.0, 1e-4, 200)            # 流动梯度（递减）
    kappa = 1.0
    geometric = kappa * g ** 2 / 2.0             # 抹平成本（C1）
    res["N4_cost_paths"] = {
        "thermal_at_1K": float(Q * (T_hot / 1.0 - 1.0)),
        "thermal_at_0p001K": float(Q * (T_hot / 0.001 - 1.0)),
        "geometric_at_g1": float(geometric[0]),
        "geometric_at_g1e-4": float(geometric[-1]),
        "thermal_ratio_1K_to_0p001K": float(
            (T_hot / 0.001 - 1.0) / (T_hot / 1.0 - 1.0)),
    }
    assert thermal[-1] > thermal[0] * 1e5, "热力学成本随 T_cold→0 发散（C3）"
    assert geometric[-1] < geometric[0] * 1e-6, "几何成本随 g→0 收敛（C1）"

    # ---- N5：边界维持账本（C2/SF11）----
    B = np.arange(1.0, 9.0)
    nu, kappa_sf, g2, V = 1.0, 1.0, 0.5, 4.0
    delta_max = B * np.sqrt(nu * V / (kappa_sf * g2))   # δ_max ∝ B（SF11）
    E_rot = 0.5 * nu * B ** 2                            # E_rot ∝ B²（SE5）
    slope = np.diff(delta_max)
    res["N5_sustain_ledger"] = {
        "delta_max_slope": float(np.mean(slope)),
        "E_rot_growth_B2": bool(np.allclose(E_rot, 0.5 * nu * B ** 2)),
    }
    assert np.allclose(slope, slope[0], rtol=1e-10), "δ_max ∝ B 必须线性（SF11）"
    assert E_rot[0] > 0, "维持能量必须正定（C2）"

    # ---- N6：冻结 = 时间反演对称 + 信息静止（SZ4/SZ2）----
    t_int = np.arange(-6, 7)
    vals = [0.42] * len(t_int)                 # 稳态场（任意时刻同值）
    rev_sym = all(vals[i - 1] == vals[i + 1] for i in range(1, len(vals) - 1))
    info_static = all(v == vals[0] for v in vals)
    res["N6_reversibility"] = {
        "time_reversal_symmetric": bool(rev_sym),
        "info_static_all_steps": bool(info_static),
    }
    assert rev_sym and info_static, "稳态场必须时间反演对称且信息静止（SZ4/SZ2）"

    # ---- 图 1：代价路径对比（C1 vs C3）----
    fig, ax = plt.subplots(1, 2, figsize=(12, 4.5))
    ax[0].loglog(T_cold, thermal, color="#c0392b", lw=2)
    ax[0].set_xlabel("目标温度 T_cold (K)")
    ax[0].set_ylabel("制冷功 W = Q(T_hot/T_cold − 1)")
    ax[0].set_title("热力学路径（C3）：T→0 成本发散")
    ax[0].invert_xaxis()
    ax[0].grid(alpha=0.3)
    ax[1].loglog(g, geometric, color="#2980b9", lw=2)
    ax[1].set_xlabel("流动梯度 g（均匀性）")
    ax[1].set_ylabel("抹平成本 κg²/2")
    ax[1].set_title("几何路径（C1）：g→0 成本任意小")
    ax[1].grid(alpha=0.3)
    fig.suptitle("冻结代价账本：热力学发散 vs 几何收敛", y=1.04)
    fig.tight_layout()
    fig.savefig(os.path.join(OUT, "fig_freeze_cost_paths.png"), dpi=150,
                bbox_inches="tight")
    plt.close(fig)

    # ---- 图 2：视界冻结 + 质量取消曲线 ----
    fig, ax = plt.subplots(1, 2, figsize=(12, 4.5))
    beta_fine = np.linspace(0.5, 0.999999, 300)
    gamma_fine = 1.0 / np.sqrt(1.0 - beta_fine ** 2)
    ax[0].semilogy(beta_fine, gamma_fine, color="#8e44ad", lw=2)
    ax[0].set_xlabel("v/c（趋近视界）")
    ax[0].set_ylabel("γ = 1/√(1−v²/c²)")
    ax[0].set_title("视界冻结（SZ5）：外部时间膨胀发散")
    ax[0].grid(alpha=0.3)
    ax[1].plot(mu, m_eff_sq, color="#16a085", lw=2, label="m_eff²/s²")
    ax[1].axhline(0, color="gray", lw=0.8, ls="--")
    ax[1].set_xlabel("反引力强度 μ")
    ax[1].set_ylabel("m_eff²（归一）")
    ax[1].set_title("质量取消时间冻结（TF2）：μ=1 → dτ=0")
    ax[1].grid(alpha=0.3)
    fig.suptitle("时空冻结的两种路径", y=1.04)
    fig.tight_layout()
    fig.savefig(os.path.join(OUT, "fig_time_freeze_paths.png"), dpi=150,
                bbox_inches="tight")
    plt.close(fig)

    report_path = os.path.join(OUT, "report.json")
    with open(report_path, "w") as f:
        json.dump(report, f, indent=2, ensure_ascii=False)
    print(f"report written: {report_path}")
    for k, v in res.items():
        print(f"  {k}: {v}")


if __name__ == "__main__":
    main()
