#!/usr/bin/env python3
"""振动闭包 => 费米/玻色：统计性、频率与秩的正交性验证（VibrationStatistics.lean VBS1–VBS8）

leo（2026-10-01）问题：
  「把费米子和玻色子的基本属性用量子场论描述，通过我的方法实现会怎么样？
   量子力学里所有粒子本身是一个场——有没有可能只是因为振动频率不同产生了
   不同的场，但实际上所有的场都是同一种场？」

本脚本把问题拆成三个可算命题：

  N1 闭包相因子 sigma(k)：f_k(theta) = exp(i k theta)
       sigma = f(theta + 2pi) / f(theta) = exp(2pi i k)
       整数 k  -> sigma = +1  （玻色型：2pi 复原）
       半整数 k -> sigma = -1 （费米型：2pi 变号，4pi 复原）
       一般 k  -> |sigma| = 1 但 sigma != +-1（任意子/分数统计）
  N2 费米型 2pi 变号、4pi 复原（数值钉住 VBS2）
  N3 统计相位可加：sigma(k1)*sigma(k2) = sigma(k1+k2)  =>  Z2 群律（VBS4/VBS5）
  N4 ★ 频率正交于秩（对 leo 假设的裁决）：
       同一个 omega（同一频率/德布罗意频率）下，光子（秩 1，det = 0）与
       电子（秩 2，det = |<pi1,pi2>|^2 > 0）并存
       => 频率（omega）不能产生费米/玻色的差别
  N5 耗散 = 闭包缺陷：eps(theta) = |f(theta+2pi) - sigma f(theta)|
       相位/频率漂移 delta = 0  => eps 恒 0（守恒，GQC1 一致）
       delta > 0               => eps > 0 且随 delta 单调（泄漏来源 = 第二输入缺口）

产物：artifacts/vibrationstatistics/{report.json, summary.txt, fig_*.png}
"""
import json
import os
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

OUT = os.path.join(os.path.dirname(__file__), "..", "artifacts", "vibrationstatistics")
os.makedirs(OUT, exist_ok=True)

I = complex(0, 1)
TWO_PI = 2.0 * np.pi


def wave(k, theta):
    """f_k(theta) = exp(i k theta)——振动（基础频率 k，绕数 k）。"""
    return np.exp(1j * k * np.asarray(theta, dtype=float))


def closure_factor(k):
    """sigma(k) = exp(2 pi i k)——旋转 2pi 后的闭包相因子。"""
    return np.exp(2j * np.pi * np.asarray(k, dtype=float))


def classify(sigma, tol=1e-9):
    """由闭包相因子判定统计类别。"""
    if abs(sigma - 1.0) < tol:
        return "玻色型"
    if abs(sigma + 1.0) < tol:
        return "费米型"
    return "任意子"


def twistor_momentum(pi):
    """p_AA' = pi pi^dagger —— rank-1 厄米矩阵。"""
    return np.outer(pi, np.conj(pi))


def main():
    report = {"model": "vibration closure => fermion/boson (statistics vs frequency vs rank)",
              "date": str(date.today()), "results": {}}
    theta = np.linspace(0.0, 4.0 * np.pi, 4001)

    # ------------------------------------------------------------------ N1
    k_bose = [0.0, 1.0, 2.0, 3.0]
    k_fermi = [0.5, 1.5, 2.5]
    k_any = [1.0 / 3.0, 0.25, 1.7]

    err_bose = max(abs(closure_factor(k) - 1.0) for k in k_bose)
    err_fermi = max(abs(closure_factor(k) + 1.0) for k in k_fermi)
    any_distance = min(min(abs(closure_factor(k) - 1.0),
                           abs(closure_factor(k) + 1.0)) for k in k_any)

    table = []
    for k in k_bose + k_fermi + k_any:
        sg = closure_factor(k)
        table.append({"k (绕数)": k, "sigma 实部": float(sg.real),
                      "sigma 虚部": float(sg.imag), "类别": classify(sg)})

    report["results"]["N1_closure_factor"] = {
        "公式": "sigma(k) = exp(2 pi i k)，k = 绕数（基础频率）",
        "整数 k 的 |sigma - 1| 最大值": float(err_bose),
        "半整数 k 的 |sigma + 1| 最大值": float(err_fermi),
        "一般 k 到 {+1,-1} 的最小距离": float(any_distance),
        "分类表": table,
    }

    # ------------------------------------------------------------------ N2
    f_fermi = wave(0.5, theta)
    fermi_2pi = float(np.max(np.abs(wave(0.5, theta + TWO_PI) + f_fermi)))
    fermi_4pi = float(np.max(np.abs(wave(0.5, theta + 4.0 * np.pi) - f_fermi)))
    f_bose = wave(1.0, theta)
    bose_2pi = float(np.max(np.abs(wave(1.0, theta + TWO_PI) - f_bose)))
    bose_4pi = float(np.max(np.abs(wave(1.0, theta + 4.0 * np.pi) - f_bose)))

    report["results"]["N2_period"] = {
        "费米型 k=0.5 的 max|f(t+2pi) + f(t)|（应为 0：变号）": fermi_2pi,
        "费米型 k=0.5 的 max|f(t+4pi) - f(t)|（应为 0：复原）": fermi_4pi,
        "玻色型 k=1 的 max|f(t+2pi) - f(t)|（应为 0：复原）": bose_2pi,
        "玻色型 k=1 的 max|f(t+4pi) - f(t)|": bose_4pi,
        "结论": "费米型 2pi 变号（|f(t+2pi)+f(t)| = 0）、4pi 复原（|f(t+4pi)-f(t)| = 0）；玻色型 2pi 即复原",
    }

    # ------------------------------------------------------------------ N3
    rng = np.random.default_rng(20261001)

    def z2(k):
        # 统计类别：2k 偶 -> 玻色(0)；2k 奇 -> 费米(1)（只对 0.5 的整数倍有定义）
        return round(2.0 * k) % 2

    worst = 0.0
    ok_class = True
    pairs = []
    for _ in range(12):
        k1, k2 = 0.5 * rng.integers(-6, 7, 2)
        prod = closure_factor(k1) * closure_factor(k2)
        summ = closure_factor(k1 + k2)
        worst = max(worst, abs(prod - summ))
        lhs = z2(k1 + k2)
        rhs = (z2(k1) + z2(k2)) % 2
        pairs.append([float(k1), float(k2), int(z2(k1)), int(z2(k2)), int(lhs)])
        if lhs != rhs:
            ok_class = False

    report["results"]["N3_phase_additive"] = {
        "公式": "sigma(k1) * sigma(k2) = sigma(k1 + k2)",
        "12 组随机 k1,k2 的 max|乘积 - 和|": float(worst),
        "Z2 类别可加性（整数/半整数奇偶）全过": bool(ok_class),
        "样例 (k1, k2, 类1, 类2, 类和)": pairs,
        "群律": "玻色 x 玻色 = 玻色；玻色 x 费米 = 费米；费米 x 费米 = 玻色",
    }

    # ------------------------------------------------------------------ N4 ★
    # 固定"同一个频率"：对扭量施加相位调制 pi -> exp(i omega t) pi
    pi1 = np.array([1.0 + 0.3j, 0.4 - 0.9j])
    pi2 = np.array([0.2 + 1.1j, 0.7 + 0.5j])

    p1 = twistor_momentum(pi1)
    p2 = twistor_momentum(pi2)
    det_photon = abs(np.linalg.det(p1))                     # 秩 1 -> 0
    det_electron = abs(np.linalg.det(p1 + p2))              # 秩 2 -> |<pi1,pi2>|^2
    # TW6/GQN：<pi1,pi2> 是**辛内积（Pluecker 括号）** pi1_0*pi2_1 - pi1_1*pi2_0
    bracket = pi1[0] * pi2[1] - pi1[1] * pi2[0]
    inner = abs(bracket) ** 2                               # |<pi1,pi2>|^2
    identity_err = abs(det_electron - inner)

    omegas = np.linspace(0.0, 4.0 * np.pi, 401)
    max_det_photon = 0.0
    max_rel_dev_electron = 0.0
    for w in omegas:
        c = np.exp(1j * w)
        q1 = twistor_momentum(c * pi1)
        q2 = twistor_momentum(c * pi2)
        max_det_photon = max(max_det_photon, abs(np.linalg.det(q1)))
        d = abs(np.linalg.det(q1 + q2))
        max_rel_dev_electron = max(max_rel_dev_electron, abs(d - det_electron) / det_electron)

    report["results"]["N4_rank_vs_frequency"] = {
        "建模": "光子 = 单扭量 rank1；电子 = 双扭量 rank2；频率 = 相位调制 pi -> exp(i w) pi",
        "光子 det（秩 1，应为 0）": float(det_photon),
        "电子 det（秩 2，= |<pi1,pi2>|^2，辛内积）": float(det_electron),
        "det(p1+p2) 与 |<pi1,pi2>|^2（辛内积）的偏差": float(identity_err),
        "同一频率扫描（401 个 w）光子 max|det|": float(max_det_photon),
        "同一频率扫描（401 个 w）电子 det 最大相对偏差": float(max_rel_dev_electron),
        "裁决": "同一个 omega 下光子（det=0）与电子（det>0）并存 => 频率不决定秩/质量/统计类别",
    }

    # ------------------------------------------------------------------ N5
    def defect(delta, k0=0.5, n=2001):
        t = np.linspace(0.0, 4.0 * np.pi, n)
        k = k0 + delta * t                     # 相位/频率漂移
        f_t = wave(k, t)
        f_shift = wave(k0 + delta * (t + TWO_PI), t + TWO_PI)
        return float(np.max(np.abs(f_shift - closure_factor(k0) * f_t)))

    deltas = [0.0, 0.001, 0.002, 0.004]
    defects = [defect(d) for d in deltas]

    report["results"]["N5_dissipation_defect"] = {
        "公式": "eps(theta) = |f(theta+2pi) - sigma f(theta)|，k(theta) = k0 + delta*theta",
        "delta 列表": deltas,
        "max eps 列表": defects,
        "delta=0（闭包）max eps": defects[0],
        "严格单调（泄漏随漂移增）": all(defects[i] < defects[i + 1] for i in range(len(defects) - 1)),
        "结论": "闭包（delta=0）=> 守恒（与 GQC1 信息守恒一致）；漂移（delta>0）=> 泄漏，来源 = 第二输入缺口",
    }

    # ------------------------------------------------------------------ 图 1
    fig, axes = plt.subplots(2, 1, figsize=(9, 8))
    ax = axes[0]
    kk = np.linspace(0.0, 3.0, 1201)
    sg = closure_factor(kk)
    ax.plot(kk, sg.real, "C0-", lw=1.5, label="Re sigma(k) = cos(2 pi k)")
    ax.plot(kk, sg.imag, "C1--", lw=1.2, label="Im sigma(k) = sin(2 pi k)")
    ax.axhspan(-1.05, -0.95, color="C3", alpha=0.10)
    ax.axhspan(0.95, 1.05, color="C0", alpha=0.10)
    for k in [0, 1, 2, 3]:
        ax.plot([k], [closure_factor(k).real], "o", color="C0", ms=7)
    for k in [0.5, 1.5, 2.5]:
        ax.plot([k], [closure_factor(k).real], "o", color="C3", ms=7)
    ax.axhline(0, color="k", lw=0.8)
    ax.set_xlabel("k = 绕数（振动的基础频率 / 每 2 pi 的圈数）")
    ax.set_ylabel("闭包相因子 sigma")
    ax.set_title("统计性 = 闭包相因子 sigma(k) = exp(2 pi i k)\n"
                 "整数 k -> sigma = +1（玻色型）；半整数 k -> sigma = -1（费米型）；"
                 "一般 k -> 任意子")
    ax.set_ylim(-1.35, 1.45)
    ax.legend(loc="upper right", fontsize=9)
    ax.grid(alpha=0.3)

    ax = axes[1]
    tt = np.linspace(0.0, 4.0 * np.pi, 2001)
    ax.plot(tt, np.abs(wave(0.5, tt + TWO_PI) - wave(0.5, tt)), "C3-", lw=1.5,
            label="费米型 k=0.5：|f(t+2pi) - f(t)|（= 2，2pi 不复原）")
    ax.plot(tt, np.abs(wave(0.5, tt + 4.0 * np.pi) - wave(0.5, tt)), "C2--", lw=1.5,
            label="费米型 k=0.5：|f(t+4pi) - f(t)|（= 0，4pi 复原）")
    ax.plot(tt, np.abs(wave(1.0, tt + TWO_PI) - wave(1.0, tt)), "C0:", lw=1.5,
            label="玻色型 k=1：|f(t+2pi) - f(t)|（= 0，2pi 即复原）")
    ax.set_xlabel("theta")
    ax.set_ylabel("闭包残差")
    ax.set_title("闭合周期：玻色型 2 pi，费米型 4 pi —— 两者是同一个振动，只差基础周期")
    ax.legend(loc="center right", fontsize=9)
    ax.grid(alpha=0.3)
    fig.subplots_adjust(left=0.10, right=0.96, top=0.92, bottom=0.08, hspace=0.42)
    fig.savefig(os.path.join(OUT, "fig_closure_statistics.png"), dpi=150)
    plt.close(fig)

    # ------------------------------------------------------------------ 图 2
    fig, ax = plt.subplots(figsize=(9, 5))
    ax.plot(omegas, [det_photon] * len(omegas), "C0-", lw=2.0,
            label="光子（秩 1 单扭量）：det = 0，无质量")
    ax.plot(omegas, [det_electron] * len(omegas), "C3-", lw=2.0,
            label="电子（秩 2 双扭量）：det = |<pi1,pi2>|^2 > 0，有质量")
    ax.axvline(np.pi, color="k", ls="--", lw=1.0)
    ax.axvline(2.0 * np.pi, color="k", ls="--", lw=1.0)
    ax.text(np.pi, 0.05, " w = pi\n (半整数频率)", fontsize=9, va="bottom")
    ax.text(2.0 * np.pi, 0.05, " w = 2 pi\n (整数频率)", fontsize=9, va="bottom")
    ax.set_ylim(-0.035, 0.58)
    ax.set_xlabel("同一频率 omega（相位调制 pi -> exp(i w) pi）")
    ax.set_ylabel("det(P)（秩判据 / 质量平方）")
    ax.set_title("频率正交于秩：同一个 omega 下光子与电子并存\n"
                 "=> 「同一个场只是频率不同」不能产生费米 / 玻色的差别")
    ax.legend(loc="center right", fontsize=10)
    ax.grid(alpha=0.3)
    fig.tight_layout()
    fig.savefig(os.path.join(OUT, "fig_rank_vs_frequency.png"), dpi=150)
    plt.close(fig)

    report["conclusion"] = (
        "三段判定（4 层口径）：① 统计性 = 闭包相因子 sigma（整数 -> 玻色 / 半整数 -> 费米 /"
        " 一般 -> 任意子），N1/N2 数值钉住；② 统计相位可加（N3，Z2 群律）——「同一种场 +"
        " 不同振动」能走到的最远处就是这条群律；③ ★ 频率正交于秩（N4）：同一个 omega 下"
        " 光子（rank1 / det=0）与电子（rank2 / det>0）并存 => 费米/玻色的差别不是 omega，"
        " 而是**闭包相因子（闭合周期 2pi vs 4pi）**与**秩**；④ 耗散 = 闭包缺陷 (N5)："
        " 闭包 => 守恒（GQC1 一致），漂移 => 泄漏，泄漏的来源 = 仓库的**第二输入缺口**（未变）。"
        " 诚实：闭包相因子是定义选择（与 SFS5 的 SU(2) 双重覆盖同构，本脚本不重证 SFS）；"
        " 秩判据 det=|det_N|^2 是 QFTFlow/GQN 已证恒等（真但平凡）；无新可检验预言。"
    )
    report["files"] = {"fig_closure_statistics": "fig_closure_statistics.png",
                       "fig_rank_vs_frequency": "fig_rank_vs_frequency.png"}

    with open(os.path.join(OUT, "report.json"), "w", encoding="utf-8") as f:
        json.dump(report, f, ensure_ascii=False, indent=2)

    lines = [
        "振动闭包 => 费米/玻色（VibrationStatistics VBS1–VBS8）",
        "=" * 60,
        f"N1 整数 k 的 |sigma-1| max      = {err_bose:.3e}",
        f"N1 半整数 k 的 |sigma+1| max    = {err_fermi:.3e}",
        f"N1 一般 k 到 ±1 的最小距离     = {any_distance:.3f}（任意子带）",
        f"N2 费米型 2pi 残差 / 4pi 残差  = {fermi_2pi:.3e} / {fermi_4pi:.3e}",
        f"N3 统计相位可加 max|乘积-和|    = {worst:.3e}；Z2 可加 = {ok_class}",
        f"N4 光子 det / 电子 det          = {det_photon:.3e} / {det_electron:.6f}",
        f"N4 同频扫描 max 相对偏差        = {max_rel_dev_electron:.3e}",
        f"N5 max eps(delta)               = {['%.3e' % d for d in defects]}",
        "=" * 60,
        "结论：统计性 = 闭包相因子（可加）；频率正交于秩 —— 同频下光子与电子并存。",
        "耗散 = 闭包缺陷；缺陷来源 = 第二输入缺口（未变）。",
    ]
    with open(os.path.join(OUT, "summary.txt"), "w", encoding="utf-8") as f:
        f.write("\n".join(lines) + "\n")

    print(json.dumps(report["results"], ensure_ascii=False, indent=2))
    print("\n-> 产物:", os.path.abspath(OUT))


if __name__ == "__main__":
    main()
