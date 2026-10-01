#!/usr/bin/env python3
"""把 σ ∈ {±1} 从「定义」升级成「定理」：自旋-统计的代数内核（VSS1–VSS8）

缺口 A（上一轮登记）：「为什么自然界只取 σ = ±1 这个二元子群，而不是一般任意子相」。
本脚本给出数值见证：

  S1 ★★ σ² = 1 在单位圆上只有两个解（玻色 σ=+1 / 费米 σ=−1）
       扫描 σ = e^{iα}, α ∈ [0, 2π)：|σ² − 1| 的零点只在 α = 0 与 α = π
  S2 ❌ 任意子被排除：α = 2π/3（三分统计相）⟹ |σ² − 1| = √3 ≈ 1.732 ≠ 0
  S3 SU(2) 双覆盖（SFS5）：四个 2×2 生成元的 e^{iπσ} = −I（2π 变号）、e^{2iπσ} = I（4π 复原）
  S4 ★ 自旋-统计配对：2π 旋转在自旋 j 的表示上的标量 = (−1)^{2j}
       j = 0, 1, 2 ⟹ +1（玻色型）； j = 1/2, 3/2 ⟹ −1（费米型）
  S5 ★ 接口（VSS8）：闭包相因子 σ = 旋转角色在 2π 的取值 g(2π)；
       只有 α ∈ ℤ/2 时 σ² = 1——「整数/半整数绕数」与「玻色/费米」是同一件事

产物：artifacts/spinstatisticsconnection/{report.json, summary.txt, fig_two_values.png, fig_spin_matching.png}
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

OUT = os.path.join(os.path.dirname(__file__), "..", "artifacts", "spinstatisticsconnection")
os.makedirs(OUT, exist_ok=True)

I2 = np.eye(2, dtype=complex)
SIG = [np.array([[0, 1], [1, 0]], dtype=complex),
       np.array([[0, -1j], [1j, 0]], dtype=complex),
       np.array([[1, 0], [0, -1]], dtype=complex)]


def expm(A):
    """矩阵指数（本脚本只对可对角化矩阵用）。"""
    w, V = np.linalg.eig(A)
    return V @ np.diag(np.exp(w)) @ np.linalg.inv(V)


def main():
    report = {"model": "spin-statistics algebraic core: sigma in {+1,-1} (VSS1-VSS8)",
              "date": str(date.today()), "results": {}}

    # ------------------------------------------------------------------ S1 ★★
    alphas = np.linspace(0.0, 2 * np.pi, 200001)
    sigma = np.exp(1j * alphas)
    dev = np.abs(sigma ** 2 - 1.0)
    # 找局部极小（就是零点）
    mask = np.abs(dev) < 1e-6
    zero_alpha = alphas[mask]
    # 去掉连续性重复
    groups = []
    for a in zero_alpha:
        if not groups or a - groups[-1][-1] > 0.01:
            groups.append([a])
        else:
            groups[-1].append(a)
    zeros_raw = [float(np.mean(g)) for g in groups]
    # 去重：α 与 α+2π 是同一点（把 2π 折回 0）
    zeros = sorted({round(z % (2 * np.pi), 9) for z in zeros_raw})
    report["results"]["S1_two_values_only"] = {
        "公式": "σ = e^{iα}，角色性 + 4π 复原 ⟹ σ² = 1 ⟹ σ = ±1",
        "扫描 α 范围": "[0, 2π)，200001 点",
        "|σ²−1| < 1e−6 的零点位置（rad）": zeros,
        "零点个数（模 2π 去重）": len(zeros),
        "结论": "单位圆上只有两个解：α = 0（σ = +1 玻色型）与 α = π（σ = −1 费米型）",
    }

    # ------------------------------------------------------------------ S2 ❌
    anyon = 2 * np.pi / 3.0
    sg_anyon = np.exp(1j * anyon)
    sg = sg_anyon
    report["results"]["S2_anyon_excluded"] = {
        "任意子相 α": float(anyon),
        "σ": [float(sg.real), float(sg.imag)],
        "σ²": [float((sg ** 2).real), float((sg ** 2).imag)],
        "|σ² − 1|": float(abs(sg ** 2 - 1)),
        "应等于（√3）": float(np.sqrt(3)),
        "判据": "4π 复原要求 σ² = g(4π) = 1；任意子相给出 √3 ⟹ 违反 ⟹ 被排除",
        "结论": "★ σ ∈ {±1} 是**穷尽**的 —— 在 3D（三方向）+ SU(2) 双覆盖下没有第三种统计",
    }

    # ------------------------------------------------------------------ S3
    rows3 = []
    worst_2pi = 0.0
    worst_4pi = 0.0
    for k, s in enumerate(SIG):
        a2 = expm(1j * np.pi * s)
        a4 = expm(1j * 2 * np.pi * s)
        worst_2pi = max(worst_2pi, float(np.max(np.abs(a2 + I2))))
        worst_4pi = max(worst_4pi, float(np.max(np.abs(a4 - I2))))
        rows3.append({"生成元": f"σ_{k+1}",
                      "max|e^{iπσ} + I|（2π 变号）": float(np.max(np.abs(a2 + I2))),
                      "max|e^{2iπσ} − I|（4π 复原）": float(np.max(np.abs(a4 - I2)))})
    report["results"]["S3_double_cover"] = {
        "内容": "SU(2) 双覆盖（SFS5）：2π 旋转 = −I，4π 旋转 = +I",
        "三个生成元": rows3,
        "2π 变号最大偏差": float(worst_2pi),
        "4π 复原最大偏差": float(worst_4pi),
        "结论": "g(4π) = 1 不是假设，是 SU(2)（Cℓ(3) 最小表示）的表示论事实",
    }

    # ------------------------------------------------------------------ S4 ★
    def R2pi_spin_j(j):
        """绕 z 轴转 2π 的自旋 j 表示：R = exp(-i·2π·Jz)，R(2π) = (−1)^{2j} I（数值看标量）。"""
        if j == 0.5:
            Jz = np.diag([0.5, -0.5]).astype(complex)
        elif j == 1.0:
            Jz = np.diag([1.0, 0.0, -1.0]).astype(complex)
        elif j == 1.5:
            Jz = np.diag([1.5, 0.5, -0.5, -1.5]).astype(complex)
        elif j == 2.0:
            Jz = np.diag([2.0, 1.0, 0.0, -1.0, -2.0]).astype(complex)
        else:
            raise ValueError(j)
        R = expm(-1j * 2 * np.pi * Jz)
        n = R.shape[0]
        scalar = R[0, 0]
        is_scalar = np.max(np.abs(R - scalar * np.eye(n))) < 1e-9
        return float(np.real(scalar)), bool(is_scalar), n

    rows4 = []
    ok_pairing = True
    for j in [0.0, 0.5, 1.0, 1.5, 2.0]:
        if j == 0.0:
            scalar, is_scalar, n = 1.0, True, 1
        else:
            scalar, is_scalar, n = R2pi_spin_j(j)
        expected = (-1.0) ** int(round(2 * j))
        rows4.append({"自旋 j": j, "表示的维数 2j+1": n,
                      "R(2π) 的标量": scalar, "是否纯量（中心）": is_scalar,
                      "(−1)^{2j}": expected,
                      "统计": "玻色型" if expected > 0 else "费米型"})
        if abs(scalar - expected) > 1e-9 or not is_scalar:
            ok_pairing = False
    report["results"]["S4_spin_matching"] = {
        "内容": "2π 旋转在自旋 j 的不可约表示上是纯量 (−1)^{2j}（SU(2) 的中心 {±I}）",
        "表": rows4,
        "整数自旋 ⟹ +1（玻色型）/ 半整数自旋 ⟹ −1（费米型）": bool(ok_pairing),
        "结论": "★ 自旋-统计的配对不是事后的约定：它是 SU(2) 中心的表示论事实",
    }

    # ------------------------------------------------------------------ S5 ★
    def closure_factor_from_role(alpha):
        """f(θ) = g(θ) f(0)，g(θ) = e^{iαθ} ⟹ 闭包相因子 σ = g(2π) = e^{2πiα}。"""
        return np.exp(2j * np.pi * alpha)

    rows5 = []
    for alpha, name in [(1.0, "整数绕数（玻色）"), (0.5, "半整数绕数（费米）"),
                        (1.0 / 3.0, "三分绕数（任意子）"), (1.7, "一般实数绕数")]:
        sg = closure_factor_from_role(alpha)
        rows5.append({"绕数 α": alpha, "名字": name,
                      "σ = g(2π)": [float(sg.real), float(sg.imag)],
                      "|σ² − 1|": float(abs(sg ** 2 - 1)),
                      "满足 4π 复原": bool(abs(sg ** 2 - 1) < 1e-9)})
    report["results"]["S5_interface_VBS"] = {
        "内容": "闭包相因子 = 旋转角色在 2π 的取值（VSS8 的数值版）",
        "表": rows5,
        "结论": "「绕数整数/半整数」与「玻色/费米」是同一件事；一般绕数（任意子）不满足 4π 复原",
    }

    # ------------------------------------------------------------------ 图 1
    fig, ax = plt.subplots(figsize=(10, 5))
    ax.plot(alphas, dev, "C0-", lw=1.8)
    ax.axhline(0, color="k", lw=0.8)
    for a, lab, col in [(0.0, "σ = +1\n玻色型", "C0"),
                        (np.pi, "σ = −1\n费米型", "C3")]:
        ax.plot([a], [0.0], "o", color=col, ms=11)
    ax.plot([anyon], [abs(sg ** 2 - 1)], "X", color="C1", ms=13)
    ax.annotate("任意子 α = 2π/3\n|σ²−1| = √3 ≈ 1.732\n⟹ 违反 4π 复原，被排除",
                xy=(anyon, abs(sg ** 2 - 1)), xytext=(anyon + 0.35, 1.45),
                fontsize=10, arrowprops=dict(arrowstyle="->", lw=1.2))
    ax.set_xlabel("α（σ = e^{iα} 的相位）")
    ax.set_ylabel("|σ² − 1|")
    ax.set_xticks([0, np.pi / 2, np.pi, 3 * np.pi / 2, 2 * np.pi])
    ax.set_xticklabels(["0", "π/2", "π", "3π/2", "2π"])
    ax.set_title("σ² = 1 在单位圆上只有两个解（α = 0 与 α = π）\n"
                 "角色性 + SU(2) 双覆盖（4π 复原）⟹ σ ∈ {+1, −1}，任意子被排除")
    ax.grid(alpha=0.3)
    fig.tight_layout()
    fig.savefig(os.path.join(OUT, "fig_two_values.png"), dpi=150)
    plt.close(fig)

    # ------------------------------------------------------------------ 图 2
    fig, ax = plt.subplots(figsize=(9, 5))
    js = [r["自旋 j"] for r in rows4]
    sc = [r["R(2π) 的标量"] for r in rows4]
    colors = ["C0" if v > 0 else "C3" for v in sc]
    ax.bar([str(j) for j in js], sc, color=colors, alpha=0.85, width=0.55)
    ax.axhline(0, color="k", lw=1)
    ax.set_ylim(-1.3, 1.3)
    ax.set_xlabel("自旋 j")
    ax.set_ylabel("R(2π) 的标量（SU(2) 中心 ±I 上的特征值）")
    ax.set_title("2π 旋转在自旋 j 的表示上 = (−1)^{2j}\n"
                 "整数自旋 ⟹ +1（玻色型）；半整数自旋 ⟹ −1（费米型）")
    ax.grid(alpha=0.3, axis="y")
    for x, v in zip(range(len(js)), sc):
        ax.text(x, v + 0.06 if v > 0 else v - 0.14, f"{v:+.0f}",
                ha="center", fontsize=11)
    fig.tight_layout()
    fig.savefig(os.path.join(OUT, "fig_spin_matching.png"), dpi=150)
    plt.close(fig)

    report["conclusion"] = (
        "把 σ ∈ {±1} 从「定义」升级成「定理」（4 层口径）：① 两个前提都不是新公设——"
        "角色性（相位在旋转复合下相乘）是「相位」概念本身的要求；4π 复原是 SU(2) 双覆盖"
        "（SFS5 / Cℓ(3) 最小表示 2 维）；② ★★ 二者联立 ⟹ σ² = g(4π) = 1 ⟹ **σ = +1 或 −1**；"
        "③ ★ **任意子被排除**：σ² = 1 在 ℂ 中只有 ±1 两解（数值 S2：α=2π/3 给出 √3 ≠ 0）；"
        "④ ★ 配对是表示论事实而非约定：2π 旋转在自旋 j 的不可约表示上 = 纯量 (−1)^{2j} "
        "（S4 数值 j=0,1/2,1,3/2,2 全中）——整数自旋玻色、半整数自旋费米。"
        "诚实边界：拓扑前提 π₁(SO(3)) = ℤ₂ 未形式化（用等价的「4π 复原」代替）；"
        "标准 Pauli 定理的另一半「相因子 ⟹ 场算符反对易」需要场算符语言，仓库没有，**未闭合**；"
        "GQC2 的角色是许可性的（保证闭包相位是态自身的角色），不是本定理的前提——"
        "真正的第三块碎料是**三方向（P3，3D）**，不是 GQC2（更正上一轮的说法）。"
        "无新公设、无新标度、无新可检验预言。"
    )
    report["files"] = {"fig_two_values": "fig_two_values.png",
                       "fig_spin_matching": "fig_spin_matching.png"}

    with open(os.path.join(OUT, "report.json"), "w", encoding="utf-8") as f:
        json.dump(report, f, ensure_ascii=False, indent=2)

    lines = [
        "把 σ ∈ {±1} 从定义升级成定理（VSS1–VSS8）",
        "=" * 66,
        f"S1 |σ²−1| 的零点位置（rad）      = {['%.6f' % z for z in zeros]}（共 {len(zeros)} 个）",
        f"S2 任意子 α=2π/3 的 |σ²−1|       = {abs(sg_anyon**2 - 1):.6f}（应 = √3 = {np.sqrt(3):.6f}）",
        f"S3 2π 变号最大偏差                = {worst_2pi:.3e}",
        f"S3 4π 复原最大偏差                = {worst_4pi:.3e}",
        f"S4 自旋-统计配对全中              = {ok_pairing}",
        f"S5 一般绕数 α=1.7 的 |σ²−1|      = {abs(closure_factor_from_role(1.7)**2 - 1):.4f}（不满足）",
        "=" * 66,
        "结论：角色性 + 4π 复原 ⟹ σ ∈ {+1,−1}；任意子被排除；配对 = (−1)^{2j}。",
    ]
    with open(os.path.join(OUT, "summary.txt"), "w", encoding="utf-8") as f:
        f.write("\n".join(lines) + "\n")

    print(json.dumps(report["results"], ensure_ascii=False, indent=2))
    print("\n-> 产物:", os.path.abspath(OUT))


if __name__ == "__main__":
    main()
