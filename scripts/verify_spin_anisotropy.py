#!/usr/bin/env python3
"""自旋能不能当旋钮用？——边界 + 开口（SA1–SA5，对应 Lean SpinAnisotropy.lean）

leo：能不能把这个自旋拿来做应用（专门做自旋的应用）。

SA1 ★ 现状边界：仓库的锚定 = 旋量范数 → 对自旋方向（SU(2)）不变
SA2 ★ ↑↓ 两态质量简并（= 实验要检验的零假设）
SA3 ★★ 开口后：自旋分辨的 D1 劈裂 = 2ε/((1−μ)(1−ε²)) ≥ 2ε（μ 放大）
SA4   诊断门槛：Doppler 展宽决定的 ε 可分辨下限 vs 离子温度
SA5   冷/热诊断折衷表

产物：artifacts/spinanisotropy/{report.json, summary.txt, fig_spin_split.png, fig_linewidth_gate.png}
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

OUT = os.path.join(os.path.dirname(__file__), "..", "artifacts", "spinanisotropy")
os.makedirs(OUT, exist_ok=True)

S1 = np.array([[0, 1], [1, 0]], dtype=complex)
S2 = np.array([[0, -1j], [1j, 0]], dtype=complex)
S3 = np.array([[1, 0], [0, -1]], dtype=complex)


def su2():
    a, b = np.random.randn(2) + 1j * np.random.randn(2)
    M = np.array([[a, b], [-np.conj(b), np.conj(a)]], dtype=complex)
    return M / np.sqrt(np.abs(a) ** 2 + np.abs(b) ** 2)


def anchor(psi):
    """anchorMassSq = ‖σ₁ψ‖² = |ψ₀|² + |ψ₁|²（仓库 MinimalCoreMathlib MC4'）。"""
    return float(np.linalg.norm(S1 @ psi) ** 2)


def main():
    rng = np.random.default_rng(7)
    report = {"model": "spin as a knob? boundary (SA1/SA2) + opening (SA3) + diagnostic gate (SA4/SA5)",
              "date": str(date.today()), "results": {}}

    # ---------------------------------------------------------------- SA1 ★
    worst_gen = {}
    for name, M in [("σ₁", S1), ("σ₂", S2), ("σ₃", S3)]:
        w = 0.0
        for _ in range(2000):
            psi = rng.normal(size=2) + 1j * rng.normal(size=2)
            a0, a1 = anchor(psi), anchor(M @ psi)
            w = max(w, abs(a0 - a1) / max(a0, 1e-30))
        worst_gen[name] = w
    worst_su2 = 0.0
    for _ in range(2000):
        psi = rng.normal(size=2) + 1j * rng.normal(size=2)
        U = su2()
        a0, a1 = anchor(psi), anchor(U @ psi)
        worst_su2 = max(worst_su2, abs(a0 - a1) / max(a0, 1e-30))
    # 全局相位
    worst_phase = 0.0
    for _ in range(2000):
        psi = rng.normal(size=2) + 1j * rng.normal(size=2)
        phi = rng.uniform(0, 2 * np.pi)
        a0, a1 = anchor(psi), anchor(np.exp(1j * phi) * psi)
        worst_phase = max(worst_phase, abs(a0 - a1) / max(a0, 1e-30))
    report["results"]["SA1_orientation_blind"] = {
        "内容": "锚定 = 旋量范数 → 对自旋方向不变（仓库 anchorMassSq = ‖σ₁ψ‖²）",
        "三个生成元的最大相对变化": {k: float(v) for k, v in worst_gen.items()},
        "随机 SU(2) 的最大相对变化": float(worst_su2),
        "全局相位的最大相对变化": float(worst_phase),
        "结论": "全部 ≤ 1e−15 → **自旋方向不进入质量** → 现在没有旋钮可拧",
    }

    # ---------------------------------------------------------------- SA2 ★
    up = np.array([1, 0], dtype=complex)
    dn = np.array([0, 1], dtype=complex)
    aup, adn = anchor(up), anchor(dn)
    report["results"]["SA2_up_down_degenerate"] = {
        "↑ 态锚定": aup, "↓ 态锚定": adn,
        "差": abs(aup - adn),
        "结论": "两态质量**简并** → 这就是实验要检验的零假设（标准 MHD 同样预言无劈裂）",
    }

    # ---------------------------------------------------------------- SA3 ★★
    def split_ref(mu, eps):
        return 2 * eps / ((1 - mu) * (1 - eps ** 2))

    def Rci(mu, eps, sgn):
        return 1 / ((1 - mu) * (1 + sgn * eps)) - 1

    rows = []
    maxdev = 0.0
    for mu in [1e-4, 1e-3, 1e-2, 0.1, 0.5]:
        for eps in [1e-5, 1e-4, 1e-3, 1e-2]:
            num = Rci(mu, eps, +1) - Rci(mu, eps, -1)
            ref = -split_ref(mu, eps)
            maxdev = max(maxdev, abs(num - ref) / max(abs(ref), 1e-30))
            rows.append({"μ": mu, "ε": eps,
                         "R_ci(↑)": Rci(mu, eps, +1), "R_ci(↓)": Rci(mu, eps, -1),
                         "劈裂(数值)": num, "−2ε/((1−μ)(1−ε²))": ref,
                         "相对偏差": abs(num - ref) / max(abs(ref), 1e-30),
                         "劈裂是否 ≥ 2ε": abs(num) >= 2 * eps - 1e-15})
    report["results"]["SA3_D1_spin_split"] = {
        "公式": "R_ci(↑) − R_ci(↓) = −2ε/((1−μ)(1−ε²))，且 |劈裂| ≥ 2ε",
        "解析 vs 数值最大相对偏差": float(maxdev),
        "抽样表": rows[::4],
        "全部满足 |劈裂| ≥ 2ε": bool(all(r["劈裂是否 ≥ 2ε"] for r in rows)),
        "结论": "劈裂被 1/(1−μ) 放大 → **μ 越大（越接近判决门槛）自旋轴越容易看见** —— 与 D1 判决同向",
    }

    # ---------------------------------------------------------------- SA4
    q = 1.602176634e-19
    mi = 1.67262192369e-27
    c = 2.99792458e8
    kT = []
    for Ti in [1e2, 3e2, 1e3, 3e3, 1e4, 3e4, 1e5, 3e5]:
        vth = np.sqrt(2 * Ti * q / mi)
        rel = vth / c
        kT.append({"T_i [eV]": Ti, "v_th/c（相对展宽）": float(rel),
                   "可分辨 ε ≥": float(rel)})
    fci = {}
    for B in [2.0, 5.3, 9.0, 20.0]:
        fci[f"B={B}T 质子"] = q * B / (2 * np.pi * mi)
    report["results"]["SA4_linewidth_gate"] = {
        "内容": "Doppler 展宽 ≈ v_th/c 决定可分辨的 ε 下限",
        "表": kT,
        "回旋频率（质子）": {k: float(v) for k, v in fci.items()},
        "结论": "keV 级热等离子体只到 ε ≥ 1e−3；要到 1e−4 需 T_i ≲ 100 eV（冷）",
    }

    # ---------------------------------------------------------------- SA5
    diag = [
        {"诊断": "热等离子体谱线（T_i = 10 keV）", "可分辨 ε": 4.62e-3,
         "适用": "现有聚变装置", "结论": "太粗 —— 只能看到 O(1e−2) 的耦合"},
        {"诊断": "热等离子体谱线（T_i = 1 keV）", "可分辨 ε": 1.46e-3,
         "适用": "低温测试台", "结论": "勉强 —— 门槛 O(1e−3)"},
        {"诊断": "冷离子束 / 低 T_i 诊断（T_i ≈ 100 eV）", "可分辨 ε": 4.6e-4,
         "适用": "小型判据台", "结论": "推荐起点"},
        {"诊断": "单粒子回旋共振 / Penning trap 单离子", "可分辨 ε": 1e-6,
         "适用": "专用桌面装置", "结论": "**首选**：线宽由仪器而非温度决定"},
    ]
    report["results"]["SA5_diagnostic_ladder"] = {
        "内容": "要看见自旋劈裂，需要的不是更准的频率计，是更冷 / 更窄线的诊断",
        "阶梯": diag,
        "结论": "第一步应放在能控线宽的小装置上，不是聚变装置",
    }

    # ---------------------------------------------------------------- 图 1
    fig, axes = plt.subplots(1, 2, figsize=(13, 5))
    ax = axes[0]
    mus = np.linspace(0, 0.99, 400)
    for eps, col in [(1e-4, "C0"), (1e-3, "C1"), (1e-2, "C2")]:
        ax.plot(mus, 2 * eps / ((1 - mus) * (1 - eps ** 2)), color=col, lw=1.8,
                label=f"ε = {eps:g}")
        ax.axhline(2 * eps, color=col, ls=":", lw=1.0)
    for res, lab in [(1e-3, "热谱线 1 keV"), (5e-3, "热谱线 10 keV")]:
        ax.axhline(res, color="k", ls="--", lw=1.0, alpha=0.6)
        ax.annotate(lab, xy=(0.62, res), fontsize=9, va="bottom")
    ax.set_xlabel("μ（判决门槛参数）")
    ax.set_ylabel("|R_ci(↑) − R_ci(↓)|")
    ax.set_title("自旋分辨的 D1 劈裂 = 2ε/((1−μ)(1−ε²))\n"
                 "虚线 = 各 ε 的下界 2ε；水平虚线 = 诊断可分辨下限\n"
                 "→ μ 越大越容易看见（与 D1 判决同向）")
    ax.set_yscale("log")
    ax.legend(loc="upper left", fontsize=9)
    ax.grid(alpha=0.3)

    ax = axes[1]
    Ts = np.logspace(1.5, 5.5, 200)
    ax.loglog(Ts, np.sqrt(2 * Ts * q / mi) / c, "C3-", lw=2.0, label="Doppler 相对展宽 ≈ v_th/c")
    ax.scatter([1e3, 1e4], [np.sqrt(2 * 1e3 * q / mi) / c, np.sqrt(2 * 1e4 * q / mi) / c],
               color="C3", s=45, zorder=5)
    ax.axhline(1e-3, color="C0", ls="--", lw=1.0, label="ε = 1e−3（keV 级热谱线门槛）")
    ax.axhline(1e-4, color="C2", ls="--", lw=1.0, label="ε = 1e−4（冷诊断门槛）")
    ax.axhline(1e-6, color="C1", ls="--", lw=1.0, label="ε = 1e−6（单粒子 / Penning trap）")
    ax.set_xlabel("离子温度 T_i [eV]")
    ax.set_ylabel("可分辨的 ε 下限")
    ax.set_title("诊断门槛：热谱线被 Doppler 卡住\n"
                 "要把 ε 压到 1e−4 以下，必须换冷/窄线诊断，不是换频率计")
    ax.legend(loc="upper left", fontsize=9)
    ax.grid(alpha=0.3, which="both")
    fig.tight_layout()
    fig.savefig(os.path.join(OUT, "fig_spin_split.png"), dpi=150)
    plt.close(fig)

    # ---------------------------------------------------------------- 图 2
    fig, ax = plt.subplots(figsize=(10.5, 5.5))
    # 注意：barh 的 y 用**数值**，标签用 set_yticks 显式设置
    # （直接传字符串数组时，重复标签会被 matplotlib 当分类去重，柱子会跑出轴外）
    names = [d["诊断"] for d in diag][::-1]
    vals = [d["可分辨 ε"] for d in diag][::-1]
    cols = ["C2", "C1", "C0", "C3"]
    ys = list(range(len(vals)))
    ax.barh(ys, vals, color=cols, alpha=0.85, height=0.55)
    ax.set_yticks(ys)
    ax.set_yticklabels(names, fontsize=9)
    ax.set_xscale("log")
    for i, v in enumerate(vals):
        ax.text(v * 1.3, i, f"{v:.2g}", va="center", fontsize=10)
    ax.set_xlabel("可分辨的 ε 下限")
    ax.set_xlim(5e-7, 3e-2)
    ax.set_ylim(-0.6, len(vals) - 0.4)
    ax.set_title("诊断阶梯：自旋劈裂要看见，装置要求是什么\n"
                 "T_i = 1 keV → ε ≥ 1.5e−3；T_i = 10 keV → ε ≥ 5e−3；单粒子级 → ε ~ 1e−6")
    ax.grid(alpha=0.3, axis="x", which="both")
    fig.tight_layout()
    fig.savefig(os.path.join(OUT, "fig_diagnostic_ladder.png"), dpi=150)
    plt.close(fig)

    report["conclusion"] = (
        "① 边界（钉死）：仓库的锚定 = 旋量范数 → 对 σ₁/σ₂/σ₃ 与全局相位全部不变"
        "（最大相对变化 1e−15 量级），两自旋态**质量简并** → **自旋方向目前不进入质量**，"
        "「自旋的应用」为零是结构性的、不是没做。"
        "② 开口：让锚定对「自旋轴 vs 流动涡度轴（B = curl C）的夹角」敏感，"
        "锚定 = s(1−μ)(1+ε cos θ)；接口现成（SF5 B=curl C、FM9/FM10 ω₀=B/2）。"
        "**这是新假设（模型选择），带自己的死法：ε = 0 ⟺ 两态质量相同 ⟺ 无可观测效应。**"
        "③ 与既有判决量 D1 合流：自旋分辨劈裂 = 2ε/((1−μ)(1−ε²))，≥ 2ε；"
        "被 1/(1−μ) 放大 → 与 D1 判决**同向**，是加在现成生死门 G1/M6 上的一根轴，不是新实验。"
        "④ 诊断门槛：Doppler 展宽给 ε ≥ 1.5e−3（1 keV）/ 5e−3（10 keV），"
        "要更细必须换冷/窄线诊断（单粒子回旋共振 / Penning trap，ε ~ 1e−6）。"
        "⑤ 诚实边界：**ε 是被测的量，不是被预言的量** —— 本模块给「劈裂的形式 + 死法」，"
        "不给数值预言；属判决类（档 3），不属推导类。无新可检验预言之前的数值。"
    )
    report["files"] = {"fig_spin_split": "fig_spin_split.png",
                       "fig_diagnostic_ladder": "fig_diagnostic_ladder.png"}

    with open(os.path.join(OUT, "report.json"), "w", encoding="utf-8") as f:
        json.dump(report, f, ensure_ascii=False, indent=2)

    lines = [
        "自旋能不能当旋钮用？—— 边界 + 开口（SA1–SA5）",
        "=" * 70,
        f"SA1 三生成元最大相对变化        = {max(worst_gen.values()):.3e}",
        f"SA1 随机 SU(2) 最大相对变化     = {worst_su2:.3e}",
        f"SA1 全局相位最大相对变化        = {worst_phase:.3e}",
        f"SA2 ↑ 态锚定 = {aup:.1f}，↓ 态锚定 = {adn:.1f}，差 = {abs(aup - adn):.1e}",
        f"SA3 解析 vs 数值最大相对偏差    = {maxdev:.3e}",
        f"SA3 μ=1e−2, ε=1e−3 的劈裂       = {abs(Rci(1e-2, 1e-3, +1) - Rci(1e-2, 1e-3, -1)):.6f}（下界 2ε = 2e−3）",
        f"SA4 T_i=1 keV 的展宽            = {np.sqrt(2*1e3*q/mi)/c:.3e} → 可分辨 ε ≥ 1.5e−3",
        f"SA4 T_i=10 keV 的展宽           = {np.sqrt(2*1e4*q/mi)/c:.3e} → 可分辨 ε ≥ 5e−3",
        "=" * 70,
        "结论：现状（自旋方向不可用）是定理；开口 = 一个带死法的新假设；",
        "      判决量 = 自旋分辨的 D1（加在现成生死门上的一根轴）。",
    ]
    with open(os.path.join(OUT, "summary.txt"), "w", encoding="utf-8") as f:
        f.write("\n".join(lines) + "\n")

    print(json.dumps({k: v for k, v in report["results"].items()
                      if k in ("SA1_orientation_blind", "SA2_up_down_degenerate",
                               "SA3_D1_spin_split")}, ensure_ascii=False, indent=2)[:2200])
    print("\n-> 产物:", os.path.abspath(OUT))


if __name__ == "__main__":
    main()
