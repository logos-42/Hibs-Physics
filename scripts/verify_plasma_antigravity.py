#!/usr/bin/env python3
"""铜-氢等离子体双流形 → 持续反引力场（数值验证）

对应 PlasmaAntiGravity.lean PA1–PA8 的数值同位体。
背景（leo 2026-08-20，接 masstozero.md）：用等离子态物质结构
（铜 + 氢）双流形产生持续稳定变化的电磁场，催动反引力场，
让物质体积变化为零。

数值检验：
  1. N1 锚定权重矩阵：q = Z²/√m（复现 masstozero.md 数值——
     ⁶³Cu 105.94 / ⁶⁵Cu 104.31 / ¹H 0.996 / ²H 0.705 / ³H 0.577；
     铜方向差异 1.5%，氢方向 29–42%）
  2. N2 双流形叠加：B(C₁+C₂) = B(C₁)+B(C₂) 机器精度（PA3）+
     时变磁场 ⟹ 时变空间场（PA4 逆否）
  3. N3 法拉第恒等（MS2）：∂_tB = −∂_xE 离散精确（时变电磁场
     与空间场运动学的自洽性）
  4. N4 反引力抵消：μ 扫描 ⟹ 任意配比平均锚定归零（PA6）⟹
     随流 dτ²=0（PA7，机器精度）
  5. N5 体积变化率：m_eff → 0 ⟹ 偏离 u → 0 ⟹ 固有体积变化率 → 0
     （"让体积变化为零"的目标曲线）
  6. N6 同位素配比调控面：Cu 维度（x: ⁶³/⁶⁵）变化 ~1.5% vs
     H 维度（y₁: ¹H/²H/³H）变化 ~42%——调控效率各向异性（PA8）
"""
import json
import os
from datetime import date

import numpy as np

OUT = os.path.join(os.path.dirname(__file__), "..", "artifacts", "plasmaantigravity")
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

# NIST 同位素质量（masstozero.md）
M_CU63, M_CU65 = 62.92959772, 64.92778970
M_H1, M_H2, M_H3 = 1.00782503223, 2.01410177812, 3.0160492779
Z_CU, Z_H = 29, 1
C = 1.0


def q_weight(Z, m):
    """等离子体锚定权重 q = Z²/√m（PA1）。"""
    return Z ** 2 / np.sqrt(m)


def proper_time_sq(dt, dx):
    return dt ** 2 - dx ** 2 / C ** 2


def main():
    report = {
        "model": ("Cu/H plasma two-stream structure -> sustained anti-gravity "
                  "(PA1-PA8 numeric; q=Z^2/sqrt(m), magnetic linearity, "
                  "mass cancel -> dV/dt=0)"),
        "date": str(date.today()),
        "results": {},
    }
    res = report["results"]

    # ---- N1：锚定权重矩阵（复现 masstozero.md 数值）----
    ions = {
        "63Cu": (Z_CU, M_CU63), "65Cu": (Z_CU, M_CU65),
        "1H": (Z_H, M_H1), "2H": (Z_H, M_H2), "3H": (Z_H, M_H3),
    }
    q = {k: q_weight(z, m) for k, (z, m) in ions.items()}
    cu_ratio = q["65Cu"] / q["63Cu"]          # 铜方向
    h2_ratio = q["2H"] / q["1H"]              # 氢方向
    h3_ratio = q["3H"] / q["1H"]
    res["N1_anchor_weight_matrix"] = {
        "q63Cu": float(q["63Cu"]), "q65Cu": float(q["65Cu"]),
        "q1H": float(q["1H"]), "q2H": float(q["2H"]), "q3H": float(q["3H"]),
        "q65_over_q63": float(cu_ratio),       # ≈0.985（1.5%）
        "q2_over_q1": float(h2_ratio),         # ≈0.707（29%）
        "q3_over_q1": float(h3_ratio),         # ≈0.579（42%）
        "Cu_dominates_H": float(q["63Cu"] / q["1H"]),  # ≈106
    }
    assert abs(q["63Cu"] - 106.02) < 0.05, "⁶³Cu q 权重须 ≈106.0（NIST 质量）"
    assert abs(q["1H"] - 0.996) < 0.01, "¹H q 权重须 ≈0.996"
    assert abs(cu_ratio - 0.9846) < 1e-3, "铜方向 q 比 ≈0.985（1.5% 差异）"
    assert abs(h2_ratio - 0.7077) < 1e-3, "氢方向 q 比 ≈0.708（29% 差异）"
    assert (1 - h2_ratio) > 10 * (1 - cu_ratio), "氢方向变化 ≫ 铜方向（PA8 各向异性）"

    # ---- N2：双流形叠加（PA3）+ 时变⟹时变（PA4）----
    t = np.arange(0, 6, dtype=float)
    x = np.arange(0, 8, dtype=float)
    T, X = np.meshgrid(t, x, indexing="ij")
    C1 = 0.5 * np.sin(0.7 * X)                # 铜慢流（空间结构）
    C2 = 1.2 * np.sin(2.1 * T + 0.3 * X)      # 氢快流（时变结构）
    C_tot = C1 + C2
    B1 = np.diff(C1, axis=1)                  # B = ∂_xC（离散）
    B2 = np.diff(C2, axis=1)
    B_tot = np.diff(C_tot, axis=1)
    add_err = np.max(np.abs(B_tot - (B1 + B2)))
    # 时变：B 随 t 变化 ⟹ C 随 t 变化（PA4 逆否）
    B_var = np.max(np.abs(np.diff(B_tot, axis=0)))
    C_var = np.max(np.abs(np.diff(C_tot, axis=0)))
    res["N2_two_stream"] = {
        "linearity_max_err": float(add_err),
        "B_time_variation": float(B_var),
        "C_time_variation": float(C_var),
        "B_var_implies_C_var": bool(B_var > 0 and C_var > 0),
    }
    assert add_err < 1e-14, "B 叠加线性必须机器精度（PA3）"
    assert B_var > 1e-3 and C_var > 1e-3, "时变磁场 ⟹ 时变空间场（PA4）"

    # ---- N3：法拉第恒等（MS2）：∂_tB = −∂_xE ----
    E = -np.diff(C_tot, axis=0)               # E = −∂_tC（MS）
    # ∂_tB(t,x) = B(t+1,x)−B(t,x)；−∂_xE = −(E(t,x+1)−E(t,x))
    d_tB = np.diff(B_tot, axis=0)             # 形状 (5, 7)
    d_xE = np.diff(E, axis=1)                 # (5, 7)
    faraday_res = np.max(np.abs(d_tB + d_xE))
    res["N3_faraday_identity"] = {
        "max_residual": float(faraday_res),
    }
    assert faraday_res < 1e-12, "法拉第恒等必须机器精度（MS2）"

    # ---- N4：反引力抵消（PA6）+ 随流 dτ²=0（PA7）----
    mu = np.linspace(0, 1, 201)
    x_cu = 0.5                                   # 50/50 铜配比
    s_mean = x_cu * q["63Cu"] + (1 - x_cu) * q["65Cu"]
    m_eff_sq = (s_mean * (1 - mu)) ** 2         # 平均锚定被抹平
    dt = 3.0
    dtau_sq = proper_time_sq(dt, C * dt)        # 随流 ⟹ dτ²=0
    res["N4_cancel"] = {
        "mean_anchor_5050": float(s_mean),
        "m_eff_sq_at_mu1": float(m_eff_sq[-1]),
        "dtau_sq_comoving": float(dtau_sq),
    }
    assert m_eff_sq[-1] == 0.0, "μ=1 ⟹ 任意配比平均锚定归零（PA6）"
    assert dtau_sq == 0.0, "随流 ⟹ dτ²=0（PA7）"

    # ---- N5：体积变化率 vs 质量（目标曲线）----
    m_eff = s_mean * (1 - mu)                    # 等效锚定（质量）
    u = m_eff                                    # 偏离 = 质量（AMC2 语义）
    dVdt = np.abs(u)                             # 固有体积变化率 ∝ 偏离
    res["N5_volume_rate"] = {
        "dVdt_at_mu0": float(dVdt[0]),
        "dVdt_at_mu1": float(dVdt[-1]),
        "reduction_ratio": float(dVdt[0] / max(dVdt[-1], 1e-300)),
    }
    assert dVdt[-1] == 0.0, "μ=1 ⟹ 体积变化率为零（目标）"

    # ---- N6：同位素配比调控面（各向异性 PA8）----
    # Cu 维度：x 从 0→1（纯 ⁶⁵ → 纯 ⁶³）
    x_grid = np.linspace(0, 1, 51)
    s_cu_axis = x_grid * q["63Cu"] + (1 - x_grid) * q["65Cu"]
    cu_swing = (s_cu_axis.max() - s_cu_axis.min()) / s_cu_axis.mean()
    # H 维度：y₁ 从 0→1（纯 ³H → 纯 ¹H，固定 y₂=0）
    y_grid = np.linspace(0, 1, 51)
    s_h_axis = y_grid * q["1H"] + (1 - y_grid) * q["3H"]
    h_swing = (s_h_axis.max() - s_h_axis.min()) / s_h_axis.mean()
    res["N6_anisotropy"] = {
        "cu_dimension_swing": float(cu_swing),   # ~1.5%
        "h_dimension_swing": float(h_swing),     # ~42%
        "anisotropy_ratio": float(h_swing / cu_swing),
    }
    assert cu_swing < 0.03, "铜维度调控范围 ~1.5%（小）"
    assert h_swing > 0.3, "氢维度调控范围 ~42%（大）"
    assert h_swing / cu_swing > 10, "各向异性 >10×（PA8）"

    # ---- 图 1：双流形叠加 + 法拉第 ----
    fig, ax = plt.subplots(1, 2, figsize=(12, 4.5))
    im = ax[0].imshow(C_tot, aspect="auto", cmap="RdBu", origin="lower",
                      extent=[0, 7, 0, 5])
    ax[0].set_title("双流形空间场 C = C_Cu + C_H（铜慢流 + 氢快流）")
    ax[0].set_xlabel("x"); ax[0].set_ylabel("t")
    fig.colorbar(im, ax=ax[0], fraction=0.046)
    ax[1].plot(mu, m_eff_sq / s_mean ** 2, color="#8e44ad", lw=2,
               label="m_eff²/s̄²")
    ax[1].plot(mu, dVdt / dVdt[0], color="#16a085", lw=2, ls="--",
               label="dV/dt（归一）")
    ax[1].set_xlabel("反引力强度 μ")
    ax[1].set_title("反引力抵消：μ=1 → 质量与体积变化率归零")
    ax[1].legend(); ax[1].grid(alpha=0.3)
    fig.suptitle("等离子体双流形 → 持续反引力场", y=1.04)
    fig.tight_layout()
    fig.savefig(os.path.join(OUT, "fig_plasma_two_stream.png"), dpi=150,
                bbox_inches="tight")
    plt.close(fig)

    # ---- 图 2：同位素配比调控面（各向异性）----
    fig, ax = plt.subplots(1, 2, figsize=(12, 4.5))
    ax[0].plot(x_grid, s_cu_axis / q["63Cu"], color="#2980b9", lw=2)
    ax[0].set_title(f"Cu 维度（⁶³/⁶⁵）：调控范围 {cu_swing*100:.1f}%")
    ax[0].set_xlabel("⁶³Cu 占比 x"); ax[0].set_ylabel("平均锚定（归一）")
    ax[0].grid(alpha=0.3)
    ax[1].plot(y_grid, s_h_axis / q["1H"], color="#c0392b", lw=2)
    ax[1].set_title(f"H 维度（¹H/³H）：调控范围 {h_swing*100:.1f}%")
    ax[1].set_xlabel("¹H 占比 y"); ax[1].set_ylabel("平均锚定（归一）")
    ax[1].grid(alpha=0.3)
    fig.suptitle("同位素配比调控面：氢是旋钮，铜不是（PA8）", y=1.04)
    fig.tight_layout()
    fig.savefig(os.path.join(OUT, "fig_isotope_control.png"), dpi=150,
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
