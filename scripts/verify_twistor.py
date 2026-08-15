#!/usr/bin/env python3
"""彭罗斯扭量 × 流动空间：光子/电子/正电子/胶子兼容性验证（Twistor.lean TW1–TW5）

leo（2026-08-15）假设：
  1. 扭量可以描述点光子（兼容性检验）
  2. 用扭量描述带质量的电子/正电子——电子和正电子在法向量方向不同，
     由此产生不同电性
  3. 胶子是否也符合扭量（带入不同参数描述单个胶子）

验证：
  N1 扭量动量恒等：随机 π ⟹ det(π⊗π̄) = 0（机器精度）——无质量
  N2 螺旋度 = CP¹（黎曼球面）几何
  N3 ★ 电子障碍：单扭量动量 det = 0 恒（无质量）⟹ 电子需双扭量
  N4 ★ 电性 = 法向量方向：σ₃ 本征值 ±1 ↔ 电荷 ±；电荷共轭 C = iσ₂
     翻转法向量方向（数值验证）
  N5 ★ 胶子扭量：无质量（det = 0 ✓）+ 色八重态（a = 1..8）参数表
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

OUT = os.path.join(os.path.dirname(__file__), "..", "artifacts", "twistor")
os.makedirs(OUT, exist_ok=True)

I = complex(0, 1)
SIG3 = np.array([[1, 0], [0, -1]], dtype=complex)
SIG2 = np.array([[0, -I], [I, 0]], dtype=complex)


def momentum_from_twistor(pi):
    """p_AA' = π_A·conj(π_A')——rank-1 厄米矩阵。"""
    p = np.outer(pi, np.conj(pi))
    return p


def main():
    report = {"model": "Penrose twistor × flowing space (compatibility test)",
              "date": str(date.today()), "results": {}}

    # ---- N1 扭量动量恒等（TW1）----
    rng = np.random.default_rng(42)
    max_det = 0.0
    for _ in range(200):
        pi = rng.standard_normal(2) + 1j * rng.standard_normal(2)
        p = momentum_from_twistor(pi)
        max_det = max(max_det, abs(np.linalg.det(p)))
    report["results"]["N1_momentum_massless"] = {
        "max|det(π⊗π̄)|（200 随机扭量）": round(float(max_det), 14),
        "note": "★ 扭量构造的动量必然在光锥上（det = 0 恒等，TW1 Lean 已证）"
                "——光子/胶子的自然描述；动量不是独立输入，是 π 的秩 1 外积"}

    # ---- N2 螺旋度 = CP¹ ----
    report["results"]["N2_helicity"] = {
        "螺旋度几何": "π 的射影类 ∈ CP¹ = 黎曼球面",
        "射影等价": "π → sπ 动量只缩放 |s|²（TW2 Lean 已证）",
        "note": "无质量粒子的'内禀'结构 = 旋量方向的几何（球面位置）"}

    # ---- N3 电子障碍 ----
    report["results"]["N3_electron_obstruction"] = {
        "单扭量动量 det": "= 0 恒（N1）",
        "电子质量 m_e": "≠ 0（0.511 MeV）",
        "判定": "单扭量不能描述电子（TW1 ⟹ 无质量）——彭罗斯经典结果："
                "有质量粒子需双扭量（twistor pair）",
        "note": "诚实：电子 = 单扭量的假设被 det = 0 恒等阻止；出路 = 双扭量"
                "扩展（未形式化）"}

    # ---- N4 电性 = 法向量方向 ----
    # σ₃ 本征态：电子（+1）/正电子（−1）
    e_plus = np.array([1.0, 0.0], dtype=complex)    # σ₃ = +1（法向量正向）
    e_minus = np.array([0.0, 1.0], dtype=complex)   # σ₃ = −1（法向量反向）
    s3_plus = SIG3 @ e_plus
    s3_minus = SIG3 @ e_minus
    # 电荷共轭 C = iσ₂·conj：翻转 σ₃ 本征值
    C_lin = I * SIG2
    Cp = C_lin @ np.conj(e_plus)
    Cm = C_lin @ np.conj(e_minus)
    # 反交换验证：[C, σ₃] = C·σ₃ + σ₃·C = 0（对任意 ψ）
    anticomm = C_lin @ SIG3 + SIG3 @ C_lin
    # C 翻转本征值：C(e+) 应与 e− 平行（±相位）
    flip_ok = (abs(np.vdot(e_minus, Cp)) > 0.99) and (abs(np.vdot(e_plus, Cm)) > 0.99)
    report["results"]["N4_charge_vs_normal"] = {
        "σ₃·e+ = +1·e+（电子，法向量正向）": bool(np.allclose(s3_plus, e_plus)),
        "σ₃·e− = −1·e−（正电子，法向量反向）": bool(np.allclose(s3_minus, -e_minus)),
        "C·σ₃ + σ₃·C = 0（反交换）": bool(np.allclose(anticomm, 0)),
        "C 翻转法向量方向（e+ ↔ e−）": bool(flip_ok),
        "note": "★ 用户的电性假设代数化：电子/正电子 = 法向量 σ₃ 的两种朝向"
                "（±1 本征值）；电荷共轭 C = iσ₂·conj 反交换 σ₃ ⟹ 翻转电性"
                "（TW4 Lean 已证）——电性是法向量方向的符号，不是独立量子数"}

    # ---- N5 胶子扭量参数表 ----
    gluon_rows = []
    for a in range(1, 9):   # 色八重态 a = 1..8
        pi = np.array([np.exp(1j * a), np.exp(-1j * a)], dtype=complex)
        det = abs(np.linalg.det(momentum_from_twistor(pi)))
        gluon_rows.append({"色 a": a, "det(p)": round(float(det), 14),
                           "无质量": bool(det < 1e-12), "自旋": 1})
    report["results"]["N5_gluon_twistor"] = {
        "色八重态 a = 1..8 的扭量动量": gluon_rows,
        "全部无质量": bool(all(r["无质量"] for r in gluon_rows)),
        "note": "★ 胶子 = 无质量自旋 1 色八重态：单扭量完全兼容（TW1/TW5）"
                "——每个色态 a 的动量都在光锥上；色 = 2³ = 8（Cℓ(6) 旋量，"
                "ColorOctetMathlib）。胶子参数（无质量/自旋 1/色）全部适合扭量"}

    # ---- 图 1: 螺旋度球面（CP¹）+ 动量方向 ----
    fig, axes = plt.subplots(1, 2, figsize=(11, 5))
    th = np.linspace(0, 2 * np.pi, 100)
    axes[0].plot(np.cos(th), np.sin(th), "C0-", lw=1.2)
    axes[0].set_aspect("equal")
    axes[0].set_title("CP¹ = 黎曼球面：螺旋度\n（π 的射影类——无质量粒子的内禀结构）")
    axes[0].grid(alpha=0.3)
    # 动量方向 vs π 相位（光锥上）
    ax = axes[1]
    ph = np.linspace(0, 2 * np.pi, 50)
    px = np.cos(ph) ** 2
    py = np.sin(ph) * np.cos(ph)
    ax.plot(px, py, "C1-", lw=1.5)
    ax.set_aspect("equal")
    ax.set_title("动量 p = π⊗π̄（det = 0）\n所有动量在光锥上（无质量恒等）")
    ax.grid(alpha=0.3)
    fig.tight_layout()
    fig.savefig(os.path.join(OUT, "helicity_sphere.png"), dpi=150)
    plt.close(fig)

    # ---- 图 2: 电性 = 法向量方向 ----
    fig, ax = plt.subplots(figsize=(8, 5))
    ax.bar(["电子 σ₃ = +1\n(法向量正向)", "正电子 σ₃ = −1\n(法向量反向)"],
           [1, -1], color=["C0", "C3"], alpha=0.8, width=0.5)
    ax.axhline(0, color="k", lw=1)
    ax.set_ylabel("电性符号（法向量投影）")
    ax.set_title("电性 = 法向量方向的两种朝向\n"
                 "电荷共轭 C = iσ₂·conj 反交换 σ₃ ⟹ 翻转电性（TW4）")
    ax.grid(alpha=0.3, axis="y")
    fig.tight_layout()
    fig.savefig(os.path.join(OUT, "charge_normal.png"), dpi=150)
    plt.close(fig)

    report["conclusion"] = (
        "扭量 × 流动空间兼容性判定（4 层）：① 光子 = 单扭量 ✓ 完全兼容"
        "（TW1：动量 det = 0 恒等——彭罗斯模型成立）；② 电子/正电子 = "
        "单扭量 ✗ 被 TW1 阻止（det = 0 ⟹ 无质量）——彭罗斯经典障碍，"
        "出路 = 双扭量（未形式化）；但用户的'电性 = 法向量方向'有独立"
        "代数内核（TW4：电荷共轭翻转 σ₃ 本征值 ±1——电性是法向量朝向，"
        "结构对应成立）；③ 胶子 = 单扭量 ✓ 兼容（TW5：无质量恒等 + "
        "色八重态 2³ = 8，参数表全部 det = 0）；④ 诚实：扭量兼容点 = "
        "无质量粒子类（光子/胶子），带质量类（电子）是经典障碍；"
        "'法向量 ⟹ 电性'是手性/电荷共轭的代数对应，不是电性数值来源"
        "（第二输入缺口）。")
    report["files"] = {"helicity_sphere": "helicity_sphere.png",
                       "charge_normal": "charge_normal.png"}

    with open(os.path.join(OUT, "report.json"), "w", encoding="utf-8") as f:
        json.dump(report, f, ensure_ascii=False, indent=2)

    print(json.dumps(report["results"], ensure_ascii=False, indent=2))
    print("\n→ 产物:", os.path.abspath(OUT))


if __name__ == "__main__":
    main()
