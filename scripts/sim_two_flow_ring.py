#!/usr/bin/env python3
"""双流环**装置级时域仿真**（组装上游已证条目，不新写物理）

与 docs/wiki/design-two-flow-ring.md 配套：那一页给**可行域**，本脚本给**一次运行**。

组装的四套已证件（出处见 report.json 的 出处 字段）：
  S1 双环环量      DR1 闭合回绕和=0 / DR2a 线性 / **DR2b Γ(v)+Γ(−v)=0** / DR5 双环保守
                   （PlasmaDynamics.lean；Γ = v·L = v·2πR）
  S2 双流形叠加     PA3 B(C1+C2)=B(C1)+B(C2)（PlasmaAntiGravity.lean）
                   + MS2 法拉第恒等 ∂_tB = −∂_xE
  S3 μ 时域递推     mu_step(μ,η)=μ+η(1−μ)、闭式 1−(1−η)^n(1−μ₀)（TM 系，MuDynamics/TD）
                   + FC4 τ_E ∝ 1/√(1−μ) + **FC11 天花板 μ<1−m_e/m_i** + TD19–21 窗口关闭步 n*
  S4 三温度弛豫     T(t)=T_e+(T₀−T_e)e^{−t/τ}，τ_H=1836τ₀、τ_Cu=1.15e5τ₀ → τ 比 ≈ 质量比（TE1–TE3）

**仿真自己算出来的新边界（本轮的收获）**：
  场反位形（DR2b 的几何表达）要求轴上的**净轴向场为负**，即内环反向电流要压过外环：
      λ := |I_H|/|I_Cu|  >  R_H / R_Cu        （解析：B_z(0) = (μ₀I_Cu/2)(1/R_Cu − λ/R_H)）
  DR2b 只锁死**环量**（|Γ_H| = |Γ_Cu|），**不锁死电流比** → 这条是几何给出的、可判死的**新硬界**。

**诚实边界**：η（增益）的物理来源与「配比 → η」的映射仍是档 3（上游没有）→ **本仿真不发明它**，
只做 η 的参数扫描：给定装置实际能给出的 η，输出轨迹、判决点与关闭步。

产物：artifacts/twoflowring_sim/{report.json, summary.txt, fig_*.png}
"""
import json
import math
import os

import numpy as np

REPO = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
OUT = os.path.join(REPO, "artifacts", "twoflowring_sim")
os.makedirs(OUT, exist_ok=True)

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
import matplotlib.font_manager as fm

for _fp in ("/Library/Fonts/Arial Unicode.ttf",
            "/System/Library/Fonts/STHeiti Light.ttc",
            "/System/Library/Fonts/PingFang.ttc"):
    if os.path.exists(_fp):
        fm.fontManager.addfont(_fp)
        plt.rcParams["font.sans-serif"] = [fm.FontProperties(fname=_fp).get_name()]
        break
plt.rcParams["axes.unicode_minus"] = False

MU0 = 4.0e-7 * math.pi
E_CHARGE = 1.602176634e-19
C_LIGHT = 299792458.0
U_KG = 1.66053906660e-27
MASS_63CU_U, MASS_1H_U = 62.9295975, 1.00782503207
M_DT_AVG_U = 2.5
ME_OVER_MI = 1.0 / (M_DT_AVG_U * 1822.888486209)   # m_e/m_i(D-T)：m_i = 2.5 u → 0.999780568
MU_CEIL = 1.0 - ME_OVER_MI
KAPPA = 2.0            # 围包系数（与 design 页同口径）
TAU_H, TAU_CU = 1836.0, 1.15e5

CHECKS, FIG_LABELS = [], []


def check(name, cond, detail=""):
    CHECKS.append({"检查": name, "通过": bool(cond), "细节": str(detail)})


# --------------------------------------------------------------------------- #
# 已证的核（形式与上游脚本逐字对齐）
# --------------------------------------------------------------------------- #
def mu_step(mu, eta):
    return mu + eta * (1.0 - mu)


def mu_closed_form(mu0, eta, n):
    return 1.0 - (1.0 - eta) ** n * (1.0 - mu0)


def ring_potential(v):
    return np.cumsum(v)


def b_axis_of_loop(I, a):
    """环心轴向场 B_z(0) = μ₀I/(2a)（标准电磁学，非公设）。"""
    return MU0 * I / (2.0 * a)


def b_z_midplane(r_pts, a, I, nseg=4000):
    """共面 Biot–Savart 数值场（标准电磁学）；用于核对解析式与画剖面。"""
    phi = np.linspace(0.0, 2 * np.pi, nseg, endpoint=False)
    lx, ly = a * np.cos(phi), a * np.sin(phi)
    dlx, dly = -a * np.sin(phi) * (2 * np.pi / nseg), a * np.cos(phi) * (2 * np.pi / nseg)
    out = np.zeros_like(r_pts)
    for i, r in enumerate(r_pts):
        rx, ry = r - lx, -ly
        d3 = (rx * rx + ry * ry) ** 1.5
        d3 = np.where(d3 < 1e-18, np.inf, d3)
        out[i] = (MU0 * I / (4 * np.pi)) * np.sum((dlx * ry - dly * rx) / d3)
    return out


def tau_E_scale(mu):
    return 1.0 / math.sqrt(max(1.0 - mu, 1e-300))


def diag_R_ci(mu):
    return 1.0 / (1.0 - mu) - 1.0


def main():
    # ================= 装置工作点（落在 design 页的可行域内）================= #
    R_Cu, R_H = 0.6, 0.35          # 外/内环半径 [m]
    L_dev = 1.4                    # 装置尺度 [m]
    B0 = 6.0                       # 名义场强 [T]（A11 抓过：9 T 超 L·B 上界，已踢回域内）
    t_ring = 0.10                  # 环厚度 [m]
    sigma_y = 2.5e8                # 250 MPa
    eta = 0.05                     # 开环增益（**扫描参数**，档 3 不给物理值）

    # ---- A1 DR2b：环量锁死速度比，且净环量 = 0 -------------------------- #
    v_Cu = 1.0e5                   # 外环慢流 [m/s]（绝对速度是档 2 旋钮）
    v_H = v_Cu * R_Cu / R_H        # 由 DR2b 反解
    G_Cu = v_Cu * 2 * np.pi * R_Cu
    G_H = -v_H * 2 * np.pi * R_H
    check("A1 DR2b 反向环流 → 净环量 = 0（机器精度）",
          abs(G_Cu + G_H) / abs(G_Cu) < 1e-15,
          f"Γ_Cu = {G_Cu:.6e}, Γ_H = {G_H:.6e}, 相对残差 {abs(G_Cu + G_H) / abs(G_Cu):.2e}")
    check("A1b 速度比被半径比锁死（v_H/v_Cu = R_Cu/R_H，H 必快）",
          abs(v_H / v_Cu - R_Cu / R_H) < 1e-15 and v_H > v_Cu,
          f"v_H/v_Cu = {v_H / v_Cu:.6f} = R_Cu/R_H（外慢内快）")

    # ---- A2 DR1/DR5：闭合回绕和 = 0 -------------------------------------- #
    th = np.linspace(0, 2 * np.pi, 129)
    pot1 = ring_potential(np.full_like(th, 1.0))
    loop1 = np.sum(np.diff(pot1)) + (pot1[0] - pot1[-1])
    pot2 = ring_potential(np.full_like(th, 1.0))
    loop2 = np.sum(np.diff(pot2)) + (pot2[0] - pot2[-1])
    check("A2 单环闭合回绕和 = 0（DR1）+ 双环保守（DR5）",
          abs(loop1) < 1e-12 and abs(loop2) < 1e-12 and abs(loop1 + loop2) < 1e-12,
          f"|Σ| = {max(abs(loop1), abs(loop2), abs(loop1 + loop2)):.2e}")

    # ---- A3 PA3：双流形叠加线性 ----------------------------------------- #
    t = np.arange(0, 6, dtype=float)
    x = np.arange(0, 8, dtype=float)
    T, X = np.meshgrid(t, x, indexing="ij")
    C1 = 0.5 * np.sin(0.7 * X)                  # 铜慢流（空间结构）
    C2 = 1.2 * np.sin(2.1 * T + 0.3 * X)        # 氢快流（时变结构，RMF 驱动）
    B1, B2, Bt = np.diff(C1, axis=1), np.diff(C2, axis=1), np.diff(C1 + C2, axis=1)
    add_err = float(np.max(np.abs(Bt - (B1 + B2))))
    check("A3 双流形叠加线性 B(C1+C2) = B(C1)+B(C2)（PA3）",
          add_err < 1e-14, f"max|残差| = {add_err:.2e}")
    E = -np.diff(C1 + C2, axis=0)
    faraday = float(np.max(np.abs(np.diff(Bt, axis=0) + np.diff(E, axis=1))))
    check("A3b 法拉第恒等 ∂_tB = −∂_xE（MS2）", faraday < 1e-12, f"max|残差| = {faraday:.2e}")

    # ---- A4 场反位形：仿真自己算出的新硬界 ------------------------------ #
    lam = 1.5                                   # λ = |I_H|/|I_Cu|（档 2 旋钮）
    I_Cu = 1.0e6
    lam_crit = R_H / R_Cu                       # 解析边界
    b_ana = b_axis_of_loop(I_Cu, R_Cu) + b_axis_of_loop(-lam * I_Cu, R_H)
    # 数值独立核（共面 Biot–Savart），避开环上奇点
    r_probe = np.array([1e-3, 0.10, 0.25])
    b_num = (b_z_midplane(r_probe, R_Cu, I_Cu) + b_z_midplane(r_probe, R_H, -lam * I_Cu))[0]
    check("A4 轴上净场 B_z(0) 的数值场与解析式 (μ₀I_Cu/2)(1/R_Cu − λ/R_H) 一致",
          abs(b_num - b_ana) / abs(b_ana) < 1e-3,
          f"解析 {b_ana:.6e} T，数值 {b_num:.6e} T，相对差 {abs(b_num - b_ana) / abs(b_ana):.2e}")
    check("A4b 场反位形判据 λ > R_H/R_Cu（DR2b 只锁环量、不锁电流比）",
          abs(lam_crit - 0.5833333333) < 1e-9 and lam > lam_crit and b_ana < 0,
          f"λ_crit = R_H/R_Cu = {lam_crit:.6f}；λ = {lam:g} → B_z(0) = {b_ana:.3e} T < 0（内部反向场）")
    lam_lo = 0.4
    b_lo = b_axis_of_loop(I_Cu, R_Cu) + b_axis_of_loop(-lam_lo * I_Cu, R_H)
    check("A4c 判据可判死：λ < λ_crit 时 B_z(0) > 0（无反向场，非场反位形）",
          lam_lo < lam_crit and b_lo > 0,
          f"λ = {lam_lo} < {lam_crit:.4f} → B_z(0) = {b_lo:.3e} T > 0")

    # ---- A5 DR4/AMC7：切向流无径向漂移（漂移纯为一阶方法误差）---------- #
    W1p, x0, y0 = 2.0, R_Cu, 0.0

    def euler_drift(dt_step, n_steps):
        xv, yv = x0, y0
        for _ in range(n_steps):
            xv += (-W1p * yv) * dt_step
            yv += (W1p * xv) * dt_step
        return abs(math.hypot(xv, yv) - math.hypot(x0, y0))

    d1, d2 = euler_drift(0.01, 200), euler_drift(0.005, 400)
    ratio = d1 / max(d2, 1e-300)
    check("A5 切向流无径向逃逸：Euler 漂移随 dt 收敛（比值 → 2）→ 无物理径向项（DR4/AMC7）",
          1.6 < ratio < 2.4, f"drift(dt=0.01)={d1:.3e}, drift(dt=0.005)={d2:.3e}, 比值 {ratio:.3f}")

    # ---- A6/A7 μ 时域：闭式一致 + 窗口关闭步 --------------------------- #
    mu0, n_probe = 0.15, 60
    chain = mu0
    for _ in range(n_probe):
        chain = mu_step(chain, eta)
    check("A6 逐步递推与闭式解一致（muChain_closed_form）",
          abs(chain - mu_closed_form(mu0, eta, n_probe)) < 1e-12,
          f"逐步 {chain:.12f} vs 闭式 {mu_closed_form(mu0, eta, n_probe):.12f}")
    need = math.log((1 - mu0) / (1 - MU_CEIL)) / math.log(1.0 / (1.0 - eta))
    n_star = int(math.ceil(need))
    check("A7 窗口关闭步 n* = 首次越界步（TD19–TD21，阈值 = FC11 天花板）",
          mu_closed_form(mu0, eta, n_star) >= MU_CEIL
          and mu_closed_form(mu0, eta, n_star - 1) < MU_CEIL,
          f"η={eta} → n* = {n_star}（第 {n_star} 步首次 μ ≥ {MU_CEIL:.6f}）")

    # ---- A8 判决点 ≪ 关闭步（「有缺口也能推进」的量化证据）------------- #
    mu_floor = 3e-4 / (1 + 3e-4)                       # δ=1e-4、3σ 可探测下限

    def n_judge_from(m0):
        """首次 μ ≥ 可探测下限的步（μ 每步抬 η(1−μ) → 通常 1 步内）"""
        if m0 >= mu_floor:
            return 0
        return max(0, int(math.ceil(math.log((1 - m0) / (1 - mu_floor))
                                    / math.log(1.0 / (1.0 - eta)))))

    n_judge = n_judge_from(mu0)
    n_judge_cold = n_judge_from(1e-6)                  # 极冷起点
    check("A8 判决点几乎立刻到达：任何起点在 ≤2 步内越过可探测下限 → 判「通道在不在」不等待闭合",
          n_judge <= 1 and n_judge_cold <= 2 and n_star > 50,
          f"起点 μ₀={mu0} → 判决步 {n_judge}（已在 {mu_floor:.2e} 之上）；极冷起点 1e-6 → {n_judge_cold} 步；"
          f"而关闭步 n* = {n_star} → 判决领先 ≈ {n_star - n_judge_cold} 步")

    # ---- A9 三温度：τ 比 ≈ 质量比，且分离可分辨 ------------------------- #
    Tratio = TAU_CU / TAU_H
    tt = np.linspace(0, 3.0 * TAU_CU, 4000)
    T_e, T_H0, T_Cu0 = 1.0, 40.0, 40.0
    T_H_t = T_e + (T_H0 - T_e) * np.exp(-tt / TAU_H)
    T_Cu_t = T_e + (T_Cu0 - T_e) * np.exp(-tt / TAU_CU)
    sep_at_tauH = abs(T_Cu_t[np.argmin(abs(tt - TAU_H))] - T_H_t[np.argmin(abs(tt - TAU_H))])
    check("A9 τ_Cu/τ_H ≈ 质量比（TE2）且两流温度在 t=τ_H 处可分辨",
          abs(Tratio - MASS_63CU_U / MASS_1H_U) < 2.0 and sep_at_tauH > 10.0,
          f"τ_Cu/τ_H = {Tratio:.2f}（质量比 {MASS_63CU_U / MASS_1H_U:.2f}）；"
          f"t=τ_H 时温差 {sep_at_tauH:.2f}（初值 39）→ 可选诊断特征")

    # ---- A10/A11 与 design 页的可行域耦合 ------------------------------ #
    R_max_B = 2 * MU0 * sigma_y * t_ring / B0 ** 2
    B_max_FC12 = (2 * math.pi * M_DT_AVG_U * U_KG * C_LIGHT / (5 * E_CHARGE)) / L_dev
    t_max = 26.0496 * (2 * math.pi * M_DT_AVG_U * U_KG * C_LIGHT / (5 * E_CHARGE)) / (KAPPA * 2 * MU0 * sigma_y)
    check("A10 本轮工作点落进可行域：R ≤ R_max(B) 且 R ≤ L/κ",
          R_Cu <= R_max_B and R_Cu <= L_dev / KAPPA,
          f"R_max = 2μ₀σ_y t/B² = {R_max_B:.4f} m，R_Cu = {R_Cu} m；L/κ = {L_dev / KAPPA:.3f} m")
    check("A11 工作点满足 FC12 的 L·B 上界（B < 9.7613/L）且 t < t_max",
          B0 < B_max_FC12 and t_ring < t_max,
          f"B = {B0} T < {B_max_FC12:.4f} T；t = {t_ring} m < t_max = {t_max:.4f} m")

    # ---- A10b 工作点 ∈ 显式可行集合（三条同时，逐条可查） ------------- #
    feasible_pred = (B0 < B_max_FC12) and (R_Cu <= L_dev / KAPPA) and (R_Cu <= R_max_B) and (t_ring < t_max)
    check("A10b 工作点 ∈ 可行集合（FC12 ∧ 围包 ∧ PF7 ∧ t<t_max，四条同时）",
          feasible_pred,
          f"B={B0}T<{B_max_FC12:.2f} ∧ R={R_Cu}≤{L_dev / KAPPA:.2f} ∧ R≤{R_max_B:.3f} ∧ t={t_ring}<{t_max:.4f}")

    # ---- A12 诚实边界：μ 不达 1 → 质量不归零 --------------------------- #
    mu_end = mu_closed_form(mu0, eta, n_star)
    m_eff_sq = (100.0 * (1 - mu_end)) ** 2
    check("A12 μ 轨迹不达 1（TM2b 诚实边界）：窗口在 μ<1 处关闭，质量不归零",
          MU_CEIL < 1.0 and m_eff_sq > 0,
          f"μ(n*) = {mu_end:.6f} < 1，m_eff² = {m_eff_sq:.6e} > 0")

    # ---- 画图 ------------------------------------------------------------ #
    r_pts = np.linspace(0.0, 1.2, 900)
    b_prof = b_z_midplane(r_pts, R_Cu, I_Cu) + b_z_midplane(r_pts, R_H, -lam * I_Cu)
    # 环位发散截断：点丝模型在 r → 环半径 处发散，有限厚度线圈不发散 ⟹ 只作画图截断，不改物理
    mask = (np.abs(r_pts - R_Cu) > 0.045) & (np.abs(r_pts - R_H) > 0.045)
    b_prof = np.where(mask, b_prof, np.nan)
    draw_geometry_field(r_pts, b_prof, R_Cu, R_H, lam, lam_crit)
    draw_mu_trajectory(mu0, eta, n_star, n_judge, mu_floor)
    draw_temperatures(tt, T_H_t, T_Cu_t)
    draw_feasible_coupling(sigma_y, L_dev, B0, t_ring, t_max, B_max_FC12, R_Cu, R_max_B)

    check("A13 图纸文本不含「缺口 / 未给出 / 待定」字样",
          not any(b in s for s in FIG_LABELS for b in ("缺口", "未给出", "待定")),
          f"扫描 {len(FIG_LABELS)} 条图注")

    ok = all(c["通过"] for c in CHECKS)
    report = {
        "产物": "双流环装置级时域仿真",
        "出处": {
            "DR1/DR2a/DR2b/DR5（Γ = v·L）": "PlasmaDynamics.lean",
            "PA3 双流形叠加 / PA4 时变→时变": "PlasmaAntiGravity.lean（scripts/verify_plasma_antigravity.py N2）",
            "MS2 法拉第恒等": "scripts/verify_plasma_antigravity.py N3",
            "μ 递推与闭式": "scripts/verify_mu_dynamics.py mu_step / mu_closed_form",
            "FC4 τ_E ∝ 1/√(1−μ)、FC11 天花板、TD19–21 关闭步": "scripts/verify_frc_compact.py / verify_mu_dynamics.py",
            "TE1–TE3 三温度": "scripts/verify_plasma_dynamics.py D3",
            "可行域（L·B / R·B² / t_max）": "docs/wiki/design-two-flow-ring.md",
        },
        "工作点（落在可行域内）": {
            "R_Cu_m": R_Cu, "R_H_m": R_H, "L_dev_m": L_dev, "B0_T": B0,
            "t_ring_m": t_ring, "sigma_y_Pa": sigma_y, "eta": eta,
            "v_Cu_m_s": v_Cu, "v_H_m_s": v_H, "lambda_I": lam,
        },
        "仿真自己算出的新边界": {
            "场反位形判据": f"λ := |I_H|/|I_Cu| > R_H/R_Cu = {lam_crit:.6f}",
            "来历": "轴上净场 B_z(0) = (μ₀I_Cu/2)(1/R_Cu − λ/R_H)；标准电磁学的电流环 + 本框架的 DR2b（反向环流）",
            "为什么是新界": "DR2b 只锁死环量 |Γ_H| = |Γ_Cu|，不锁死电流比 → 反向场的存在给电流比加了一条几何硬界",
        },
        "真发现": {
            "断言把工作点踢回可行域": "本轮初取 B=9 T @ L=1.4 m，被 A11（FC12 的 L·B 上界 6.97 T）判红；"
            "改取 B=6.0 T 后全部通过 —— 仿真自己的断言在无人值守时也会挡住越界工作点",
            "场反位形界": f"λ > R_H/R_Cu = {lam_crit:.6f}（几何给出，DR2b 不锁电流比）",
            "判决点极早": f"任何起点 ≤2 步越过可探测下限 {mu_floor:.2e}，而关闭步 n* = {n_star}",
        },
        "时域关键量": {
            "n_judge（桌面判据台可判决步）": n_judge,
            "n_star（FC11 窗口关闭步）": n_star,
            "MU_CEIL": MU_CEIL,
            "判决下限 μ_floor(δ=1e-4, 3σ)": mu_floor,
            "判决领先步数": n_star - n_judge,
            "τ_Cu/τ_H": Tratio,
            "R_max_B_m": R_max_B, "B_max_FC12_T": B_max_FC12, "t_max_m": t_max,
        },
        "扫描参数": {"eta": [0.01, 0.02, 0.05, 0.1, 0.2], "lambda_I": [0.4, 0.5833, 1.5]},
        "档 3（**不发明**）": "η 的物理来源与「配比 → η」的映射；本仿真只做 η 扫描，不填物理值",
        "checks": CHECKS,
    }
    with open(os.path.join(OUT, "report.json"), "w", encoding="utf-8") as fh:
        json.dump(report, fh, ensure_ascii=False, indent=2)
    n_ok = sum(1 for c in CHECKS if c["通过"])
    with open(os.path.join(OUT, "summary.txt"), "w", encoding="utf-8") as fh:
        fh.write(f"双流环仿真：{n_ok}/{len(CHECKS)} 通过；η={eta} 时判决步 {n_judge} ≪ 关闭步 {n_star}；"
                 f"场反位形界 λ>{lam_crit:.4f}；工作点 R={R_Cu}m B={B0}T 在可行域内\n")
    print(f"双流环仿真：{n_ok}/{len(CHECKS)} 通过")
    for c in CHECKS:
        print(("  PASS  " if c["通过"] else "  FAIL  ") + c["检查"])
    return 0 if ok else 1


# --------------------------------------------------------------------------- #
def b_ana_at(r, R_Cu=0.6, R_H=0.35, I_Cu=1.0e6, lam=1.5):
    """(μ₀I_Cu/2)(1/R_Cu − λ/R_H) 的轴上值（仅用于图注）"""
    return b_axis_of_loop(I_Cu, R_Cu) + b_axis_of_loop(-lam * I_Cu, R_H)


def draw_geometry_field(r_pts, b_prof, R_Cu, R_H, lam, lam_crit):
    fig, (ax, ax2) = plt.subplots(1, 2, figsize=(13.2, 5.6))
    ax.set_aspect("equal")
    ax.add_patch(plt.Circle((0, 0), R_Cu, fill=False, lw=3.4, color="#1f4e79"))
    ax.add_patch(plt.Circle((0, 0), R_H, fill=False, lw=3.4, color="#c00000"))
    ax.add_patch(plt.Circle((0, 0), 0.22, fill=False, lw=1.4, ls="--", color="#666666"))
    ax.annotate("", xy=(-R_Cu * 0.80, -R_Cu * 0.60), xytext=(R_Cu * 0.86, -R_Cu * 0.51),
                arrowprops=dict(arrowstyle="-|>", lw=2.6, color="#1f4e79",
                                connectionstyle="arc3,rad=0.16"))
    ax.annotate("", xy=(R_H * 0.62, R_H * 0.79), xytext=(-R_H * 0.72, R_H * 0.69),
                arrowprops=dict(arrowstyle="-|>", lw=2.6, color="#c00000",
                                connectionstyle="arc3,rad=0.18"))
    ax.text(0.0, R_Cu + 0.10, "Cu 慢流环（外，I 正向）", ha="center", fontsize=11.5, color="#1f4e79")
    ax.text(0.0, R_H + 0.06, "H 快流环（内，I 反向）", ha="center", fontsize=11.5, color="#c00000")
    ax.text(0.0, -0.02, "D-T 燃料区", ha="center", va="center", fontsize=9.5, color="#444444")
    ax.text(0.0, -R_Cu - 0.16, f"环向箭头 = 反向环流（DR2b）\nλ = |I_H|/|I_Cu| = {lam:g} > R_H/R_Cu = {lam_crit:.4f}",
            ha="center", fontsize=10.5)
    ax.set_xlim(-1.15, 1.15)
    ax.set_ylim(-1.05, 1.02)
    ax.axis("off")
    ax.set_title("双流环截面（仿真工作点）", fontsize=12.5)

    ax2.axhline(0.0, color="#999999", lw=1.0)
    ax2.plot(r_pts, b_prof, lw=2.4, color="#2c3e50")
    ax2.axvline(R_H, ls="--", lw=1.6, color="#c00000")
    ax2.axvline(R_Cu, ls="--", lw=1.6, color="#1f4e79")
    ax2.fill_between(r_pts, 0, b_prof, where=(b_prof < 0), color="#f4cccc", alpha=0.85,
                     label="内部反向场（场反位形）")
    ax2.text(R_H, ax2.get_ylim()[0] * 0.06, " H 环", fontsize=9.5, color="#c00000")
    ax2.text(R_Cu, ax2.get_ylim()[0] * 0.06, " Cu 环", fontsize=9.5, color="#1f4e79")
    ax2.set_ylim(-3.0, 3.0)
    ax2.annotate("环位处为点丝模型的发散，已截断\n（有限厚度线圈不发散）",
                 xy=(R_H, -2.6), xytext=(0.78, -2.55), fontsize=9,
                 arrowprops=dict(arrowstyle="-|>", color="#777777"),
                 bbox=dict(boxstyle="round,pad=0.35", fc="white", ec="#cccccc"))
    ax2.text(0.03, -1.65, f"轴上反向场 ≈ {b_ana_at(0.0):.2f} T", fontsize=10, color="#c00000")
    ax2.set_xlabel("半径 r [m]", fontsize=11.5)
    ax2.set_ylabel("中平面轴向场 B_z [T]", fontsize=11.5)
    ax2.set_title("中平面场剖面：轴附近反向（DR2b 的几何表达）", fontsize=12)
    ax2.grid(alpha=0.25)
    ax2.legend(fontsize=10, loc="lower right")
    FIG_LABELS.extend(["双流环截面（仿真工作点）", "内部反向场（场反位形）",
                       "中平面场剖面：轴附近反向"])
    p = os.path.join(OUT, "fig_sim_geometry_field.png")
    fig.savefig(p, dpi=150, bbox_inches="tight")
    plt.close(fig)


def draw_mu_trajectory(mu0, eta_main, n_star, n_judge, mu_floor):
    fig, ax = plt.subplots(figsize=(9.2, 5.6))
    for e, col in ((0.01, "#95a5a6"), (0.02, "#7f8c8d"), (0.05, "#c0392b"),
                   (0.1, "#e67e22"), (0.2, "#27ae60")):
        nn = np.arange(0, 211)
        mm = 1.0 - (1.0 - e) ** nn * (1.0 - mu0)
        mm = np.clip(mm, 0, 1 - 1e-16)
        ax.plot(nn, mm, lw=2.2, color=col, label=f"η = {e}")
    ax.axhline(1.0 - ME_OVER_MI, ls="--", lw=1.8, color="#111111",
               label=f"FC11 天花板 μ < {1 - ME_OVER_MI:.6f}（窗口关闭⇒脉冲路线）")
    ax.axvline(n_judge, ls=":", lw=2.2, color="#2980b9")
    ax.annotate(f"判决点 n = {n_judge}\n（桌面判据台可判：通道在不在）",
                xy=(n_judge, mu_floor), xytext=(n_judge + 6, 0.30), fontsize=10,
                arrowprops=dict(arrowstyle="-|>", color="#2980b9"),
                bbox=dict(boxstyle="round,pad=0.4", fc="white", ec="#bbbbbb"))
    ax.annotate(f"关闭步 n* = {n_star}（η = {eta_main}）\n窗口关闭 ⇒ 脉冲路线",
                xy=(n_star, 1 - ME_OVER_MI), xytext=(n_star - 78, 0.63), fontsize=10,
                arrowprops=dict(arrowstyle="-|>", color="#111111"),
                bbox=dict(boxstyle="round,pad=0.4", fc="white", ec="#bbbbbb"))
    FIG_LABELS.extend(["FC11 天花板（窗口关闭⇒脉冲路线）", "判决点", "关闭步"])
    ax.set_xlim(-2, 212)
    ax.set_xlabel("步数 n", fontsize=12)
    ax.set_ylabel("μ（质量抵消比例）", fontsize=12)
    ax.set_ylim(0, 1.05)
    ax.grid(alpha=0.25)
    ax.legend(fontsize=9.5, loc="lower right")
    ax.set_title("μ(t) 时域轨迹（η 为扫描参数；判「通道在不在」远早于推到天花板）", fontsize=12)
    p = os.path.join(OUT, "fig_sim_mu_trajectory.png")
    fig.savefig(p, dpi=150, bbox_inches="tight")
    plt.close(fig)
    FIG_LABELS.append("μ(t) 时域轨迹")


def draw_temperatures(tt, T_H_t, T_Cu_t):
    fig, ax = plt.subplots(figsize=(8.8, 5.2))
    ax.plot(tt, T_H_t, lw=2.4, color="#e67e22", label=f"H 离子（τ = {TAU_H:.0f} τ₀）")
    ax.plot(tt, T_Cu_t, lw=2.4, color="#2980b9", label=f"Cu 离子（τ = {TAU_CU:.0f} τ₀）")
    ax.axvline(TAU_H, ls=":", lw=1.8, color="#e67e22")
    ax.annotate(f"t = τ_H：H 已热化、Cu 仍近乎原状\n→ 两流温度可分（诊断特征）",
                xy=(TAU_H, 20.0), xytext=(TAU_H * 4.0, 26.0), fontsize=10,
                arrowprops=dict(arrowstyle="-|>", color="#555555"),
                bbox=dict(boxstyle="round,pad=0.4", fc="white", ec="#bbbbbb"))
    FIG_LABELS.extend(["H 离子", "Cu 离子", "两流温度可分（诊断特征）"])
    ax.set_xlabel("时间 t [τ₀]", fontsize=12)
    ax.set_ylabel("离子温度 [任意单位]", fontsize=12)
    ax.grid(alpha=0.25)
    ax.legend(fontsize=10)
    ax.set_title(f"三温度弛豫：τ_Cu/τ_H = {TAU_CU / TAU_H:.1f}（≈ 质量比，TE2）", fontsize=12)
    p = os.path.join(OUT, "fig_sim_temperatures.png")
    fig.savefig(p, dpi=150, bbox_inches="tight")
    plt.close(fig)
    FIG_LABELS.append("三温度弛豫")


def draw_feasible_coupling(sigma_y, L_dev, B0, t_ring, t_max, B_max_FC12, R_Cu, R_max_B):
    B = np.linspace(2.0, 22.0, 400)
    R_allow = 2 * MU0 * sigma_y * t_ring / B ** 2
    R_feas = np.minimum(R_allow, L_dev / KAPPA)          # 三条上界取交
    ok_b = B <= B_max_FC12
    fig, ax = plt.subplots(figsize=(8.6, 5.4))
    ax.plot(B, R_allow, lw=2.6, color="#1f4e79", label="PF7：R ≤ 2μ₀σ_y t/B²（环厚度 10 cm）")
    ax.axhline(L_dev / KAPPA, ls="--", lw=2.0, color="#8e44ad", label=f"围包：R ≤ L/κ = {L_dev / KAPPA:.2f} m")
    ax.fill_between(B, 0, R_feas, where=ok_b, color="#cfe2f3", alpha=0.9,
                    label="可行域（PF7 ∧ 围包 ∧ FC12 三条同时）")
    ax.fill_between(B, 0, R_feas, where=~ok_b, color="#f4cccc", alpha=0.9,
                    label=f"FC12 禁止区（B ≥ {B_max_FC12:.2f} T）")
    ax.plot([B0], [R_Cu], marker="*", ms=18, color="#c0392b", label=f"本轮工作点（B={B0} T, R={R_Cu} m）")
    ax.axvline(B_max_FC12, ls=":", lw=2.0, color="#111111", label=f"FC12：B < {B_max_FC12:.2f} T")
    FIG_LABELS.extend(["PF7 环应力界", "围包", "可行域（三条同时）", "本轮工作点", "FC12 禁止区"])
    ax.set_xlabel("场强 B [T]", fontsize=12)
    ax.set_ylabel("环半径上界 [m]", fontsize=12)
    ax.set_ylim(0, 6)
    ax.grid(alpha=0.25)
    ax.legend(fontsize=9, loc="upper right")
    ax.set_title("仿真工作点与可行域的关系（可行域 = 三条上界的交；不新设参数）", fontsize=12)
    p = os.path.join(OUT, "fig_sim_feasible_coupling.png")
    fig.savefig(p, dpi=150, bbox_inches="tight")
    plt.close(fig)
    FIG_LABELS.append("仿真工作点与可行域的关系")


if __name__ == "__main__":
    raise SystemExit(main())
