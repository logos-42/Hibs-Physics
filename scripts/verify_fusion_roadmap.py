#!/usr/bin/env python3
"""可控核聚变五年计划——判决漏斗数值支撑（路线图的可检验化）

对应 docs/wiki/fusion-program-roadmap.md。

leo（2026-09-15）：五年计划不该写成日历表，应写成判决漏斗——先用最便宜的实验
决定"反引力约束"是否成立，再按门增加投入。本脚本把计划里所有可量化的东西算出来：

  R1  判决量 D1：回旋共振频移签名（FC9 ω_ci ∝ 1/m_eff）
      R_ci(μ) = 1/(1−μ) − 1；诊断相对精度 δ ⟹ 可探测 μ_min = δ/(1+δ)
  R2  判决量 D2：锁定比 Λ = τ_E 增益 / S* 惩罚
      FC5 预言 Λ=1（不可绕开）；本设计主张几何捕获（AMC7）⟹ Λ>1 —— 分歧点
  R3  判决量 D3：μ 的功率标度指数 k（μ ∝ P^k）
      到聚变级 μ 需要多少倍输入功率：10^(Δdecade/k)
  R4  μ 数量级阶梯（每年推进一个数量级才够）+ 人·月预算曲线
  R5  阶段门表（月起止 / 交付 / 人数 / 人·月 / 失败处置）

输出：artifacts/fusionroadmap/report.json + summary.txt + 两张图
"""
import json
import math
import os

import numpy as np

OUT = os.path.join(os.path.dirname(__file__), "..", "artifacts", "fusionroadmap")
os.makedirs(OUT, exist_ok=True)

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
import matplotlib.font_manager as fm

# —— 中文字体探测（优先单 face 的 Arial Unicode MS；PingFang.ttc 是 TTC，
#    matplotlib 解析其 cmap 不完整会误报字符缺失）——
for _fp in ("/Library/Fonts/Arial Unicode.ttf",
            "/System/Library/Fonts/STHeiti Light.ttc",
            "/System/Library/Fonts/PingFang.ttc",
            "/System/Library/Fonts/Hiragino Sans GB.ttc"):
    if os.path.exists(_fp):
        fm.fontManager.addfont(_fp)
        plt.rcParams["font.sans-serif"] = [fm.FontProperties(fname=_fp).get_name()]
        break
plt.rcParams["axes.unicode_minus"] = False

# ---------------------------------------------------------------------------
# 常数（真实值，SI）
E_CHARGE = 1.602176634e-19
M_U = 1.66053906660e-27          # 原子质量单位
M_DT = 2.5 * M_U                 # D-T 平均离子质量（D:T = 1:1）
M_P = 1.007276466621 * M_U       # 质子（H 快流环 / 示踪离子）
M_CU63 = 62.9295975 * M_U        # ⁶³Cu（Cu 慢流环）

# 仓库已证条目引用的门槛（不重新推导，直接取）
MU_FC11 = 1.0 - 9.1093837015e-31 / M_DT   # FC11 RMF 天花板 μ < 1 − m_e/m_i
MU_FUSION = 0.999                 # FrcCompact 轮：紧凑 FRC 级所需 μ（≈0.999）
MU_BENCH = 1.0e-4                 # 桌面判据台量级（≈1e-4）

PALETTE = dict(bg="#faf8f5", gate="#c0392b", ok="#27ae60", warn="#e67e22",
               mu="#8e44ad", bar="#2e86de", grey="#95a5a6")


def mu_signature_cyclotron(mu):
    """D1 签名：R_ci = 1/(1−μ) − 1（FC9 ω_ci ∝ 1/m_eff，m_eff = s(1−μ)）。"""
    return 1.0 / (1.0 - mu) - 1.0


def mu_min_detectable(delta):
    """诊断相对精度 δ（= R_ci）对应的可探测 μ 下限：μ = δ/(1+δ)。"""
    return delta / (1.0 + delta)


def tau_gain(mu):
    """FC4：τ_E 增益 = 1/√(1−μ)。"""
    return 1.0 / math.sqrt(1.0 - mu)


def s_penalty(mu):
    """FC5 锁定：S* 惩罚 = 1/√(1−μ)（与 τ_E 增益同因子）。"""
    return 1.0 / math.sqrt(1.0 - mu)


def locking_ratio(mu, geometry_capture=False):
    """D2 锁定比 Λ = τ_E 增益 / S* 惩罚。FC5 ⟹ Λ≡1；几何捕获（AMC7）⟹ Λ>1。"""
    if not geometry_capture:
        return tau_gain(mu) / s_penalty(mu)
    # 若几何捕获成立：输运获益保留 1/√(1−μ)，稳定性惩罚仅剩磁通道（退化为 1）
    return tau_gain(mu)


def power_ratio_for_decades(decades, k):
    """μ ∝ P^k ⟹ 提升 10^decades 倍 μ 所需输入功率倍数 = 10^(decades/k)。"""
    return 10.0 ** (decades / k)


def cyclotron_mhz(B_T, m_kg):
    """f_ci = eB/(2πm)。"""
    return E_CHARGE * B_T / (2.0 * math.pi * m_kg) / 1e6


# ---------------------------------------------------------------------------
# R1 判决量 D1（回旋频移签名）
# ---------------------------------------------------------------------------
DIAG_PRECISIONS = [1e-3, 1e-4, 1e-5, 1e-6]
R1_signature = {
    "判决量": "D1 回旋共振频移 R_ci = f_ci(μ)/f_ci(0) − 1 = 1/(1−μ) − 1（FC9）",
    "零假设（标准 MHD）": "R_ci = 0",
    "诊断精度 → 可探测 μ 下限": {
        f"δ={d:.0e}": {"μ_min": mu_min_detectable(d),
                       "R_ci(μ_min)": mu_signature_cyclotron(mu_min_detectable(d))}
        for d in DIAG_PRECISIONS},
    "μ → 签名对照": {f"μ={m:g}": {"R_ci": mu_signature_cyclotron(m),
                                  "τ_E 增益=1/√(1−μ)": tau_gain(m)}
                     for m in (1e-4, 1e-3, 1e-2, 0.1, 0.5, 0.9, 0.99, 0.999)},
    "示踪离子回旋频率 @B=1T [MHz]": {
        "¹H": cyclotron_mhz(1.0, M_P),
        "⁶³Cu": cyclotron_mhz(1.0, M_CU63),
        "D-T 平均": cyclotron_mhz(1.0, M_DT)},
}

# ---------------------------------------------------------------------------
# R2 判决量 D2（锁定比）
# ---------------------------------------------------------------------------
R2_lock = {
    "判决量": "D2 锁定比 Λ = τ_E 增益 / S* 惩罚",
    "FC5 预言（μ 不可绕开）": "Λ ≡ 1（改善输运 ⟹ 稳定性同因子恶化）",
    "本设计主张（几何捕获 AMC7）": "Λ > 1（未证——本设计与 FC 轮的分歧点）",
    "Λ 数值（两条假说）": {
        f"μ={m:g}": {"FC5：Λ=1": locking_ratio(m, False),
                     "几何捕获：Λ=1/√(1−μ)": locking_ratio(m, True)}
        for m in (0.1, 0.5, 0.9, 0.99, 0.999)},
    "判决方式": "同一装置同一 μ 下同时测 τ_E 与 s 参数：Λ 实测 = τ_E 增益 / s 惩罚",
}

# ---------------------------------------------------------------------------
# R3 判决量 D3（功率标度指数）
# ---------------------------------------------------------------------------
K_VALUES = [1.0, 0.5, 0.25, 0.1]
R3_scaling = {
    "判决量": "D3 μ 的功率标度指数 k（μ ∝ P^k），由 μ(P) 标定曲线对数斜率给出",
    "从桌面 μ≈1e-4 到聚变级 μ≈0.999（Δ≈4 个数量级）所需输入功率倍数": {
        f"k={k:g}": power_ratio_for_decades(4.0, k) for k in K_VALUES},
    "每推进一个数量级 μ 所需功率倍数": {
        f"k={k:g}": power_ratio_for_decades(1.0, k) for k in K_VALUES},
    "预写判据": {
        "k ≥ 1": "可行（每数量级 μ 需 ≤10× 功率，装置功率量级可覆盖）",
        "k ≈ 0.5": "需 1e8 倍功率 ⟹ 五年计划内不可行",
        "k ≤ 0.25": "需 ≥1e16 倍功率 ⟹ 判死刑",
    },
}

# ---------------------------------------------------------------------------
# R4 μ 阶梯 + 人·月
# ---------------------------------------------------------------------------
MU_LADDER = [
    # (阶段, 月起点, 月终点, μ 目标, 装置尺度, 人·月)
    ("G0 判据规范", 0, 3, MU_BENCH, "桌面（无装置）", 6),
    ("G1 D1 判决", 3, 6, 1e-3, "桌面判据台", 9),
    ("G2 D3 标度初值", 6, 12, 1e-2, "中型测试台", 30),
    ("G3 独立复现", 12, 18, 1e-2, "中型测试台 ×2", 48),
    ("G4 D2 锁定判决", 18, 24, 1e-1, "FRC 级约束装置", 144),
    ("G5 D-D 产额标度", 24, 36, 0.5, "FRC 级 + 中子诊断", 240),
    ("G6 D-T 燃烧", 36, 48, 0.99, "燃烧装置 + 氚设施", 336),
    ("G7 稳态 + 净电", 48, 60, MU_FUSION, "全系统集成", 420),
]
total_pm = sum(row[5] for row in MU_LADDER)
R4_ladder = {
    "每年推进一个数量级（判据）": "5 年 5 个数量级：1e-4 → 1e-3 → 1e-2 → 1e-1 → 0.5 → 0.999",
    "阶梯表": [{"阶段": r[0], "月区间": f"{r[1]}–{r[2]}", "μ 目标": r[3],
                "装置尺度": r[4], "人·月": r[5],
                "累计人·月占比 [%]": round(sum(x[5] for x in MU_LADDER[:i + 1])
                                          / total_pm * 100, 2)}
               for i, r in enumerate(MU_LADDER)],
    "总人·月": total_pm,
    "判决期成本占比 [%]": round((MU_LADDER[0][5] + MU_LADDER[1][5]) / total_pm * 100, 2),
    "两年门（M24）前累计占比 [%]": round(sum(r[5] for r in MU_LADDER[:5]) / total_pm * 100, 2),
    "峰值人数": MU_LADDER[-1][5] // 12,
}

# ---------------------------------------------------------------------------
# R5 阶段门表
# ---------------------------------------------------------------------------
GATES = [
    ("G0", 3, "判据规范 + 零假设基准 + 预注册协议（论文 1）",
     "无实验：标准 MHD 预测值 R_ci=0 的解析/数值基准 + 诊断方案定标", "2", "继续"),
    ("G1", 6, "D1 判决实验 v1（桌面判据台）",
     "R_ci 实测 > 3σ 且零假设预测 < 分辨率 ⟹ 通过", "3", "R_ci=0 ⟹ 停装置线，转纯理论（可发负结果）"),
    ("G2", 12, "D3 标度初值 k + μ(B,f,配比) 标定曲线",
     "对数斜率 k 拟合 + 置信区间；μ 达 1e-2", "5", "k<0.5 ⟹ 转 B 计划（μ 降级为辅助输运层）"),
    ("G3", 18, "外部实验室独立复现（≥2 装置/≥3 批次）",
     "复现包：装置参数 + 原始数据 + 分析脚本；第三方数据同号同量级", "8", "复现失败 ⟹ 回 G1 重设诊断"),
    ("G4", 24, "D2 锁定判决（Λ）+ τ_E 标度律（FC4）",
     "同 μ 下 τ_E 增益与 s 惩罚实测比；标度律 1/√(1−μ) 拟合", "12", "Λ=1 ⟹ 反引力不可作主约束，并入 FRC/CFR2"),
    ("G5", 36, "D-D 产额标度 + μ–⟨σv⟩ 耦合闭合",
     "中子产额 vs 约束参数标度律；反应率随 μ 的实测修正（未建模缺口闭合）", "20", "产额不随约束提升 ⟹ 回 G4"),
    ("G6", 48, "D-T 燃烧 Q>1",
     "秒级 Q>1；（氚许可 + 中子屏蔽 + 远程维护为硬前置）", "28", "未点火 ⟹ 降级为 D-D 演示装置"),
    ("G7", 60, "稳态长脉冲 + 热电转换 + 路线裁决",
     "分钟级稳态 + 净电输出演示；与 CFR2 分段压缩路线对照裁决报告", "35", "—"),
]
R5_gates = {"门表": [{"门": g[0], "月": g[1], "交付": g[2], "通过条件": g[3],
                     "人数": g[4], "失败处置": g[5]} for g in GATES],
            "三判决量": [
                "D1（M6）R_ci = 1/(1−μ) − 1 ≠ 0 —— μ 可被主动产生",
                "D2（M24）Λ = τ_E 增益/S* 惩罚 —— 反引力能否作主约束",
                "D3（M12 起）k = dlnμ/dlnP ≥ 1 —— μ 能否外推到聚变级"],
            "节律": {"最小步长": "季度（3 月）一个证据包",
                     "裁决节律": "半年 Go / Pivot / Stop",
                     "对外节律": "年（论文 + 预注册更新 + 独立复现）",
                     "全周期": "60 月"}}


# ---------------------------------------------------------------------------
# 图 1：门漏斗（μ 阶梯 + 人力条）
# ---------------------------------------------------------------------------
def fig_gate_funnel():
    fig, (ax1, ax2) = plt.subplots(2, 1, figsize=(12.2, 8.4), sharex=True,
                                   gridspec_kw={"height_ratios": [1.35, 1.0],
                                                "hspace": 0.12})
    fig.patch.set_facecolor(PALETTE["bg"])

    months = np.linspace(0, 60, 601)
    mu_curve = np.empty_like(months)
    for i, m in enumerate(months):
        for j, row in enumerate(MU_LADDER):
            if row[1] <= m <= row[2]:
                lo = MU_BENCH if j == 0 else MU_LADDER[j - 1][3]
                frac = (m - row[1]) / (row[2] - row[1])
                # 对数插值（每阶段推进若干数量级）
                lo_safe, hi_safe = max(lo, 1e-5), max(row[3], 1e-5)
                mu_curve[i] = 10 ** (math.log10(lo_safe) +
                                     frac * (math.log10(hi_safe) - math.log10(lo_safe)))
                break
        else:
            mu_curve[i] = MU_LADDER[-1][3]
    ax1.set_facecolor(PALETTE["bg"])
    ax1.semilogy(months, mu_curve, color=PALETTE["mu"], lw=2.6, zorder=4,
                 label="μ 数量级阶梯（每年推进一个数量级）")
    ax1.axhline(MU_FUSION, color=PALETTE["ok"], ls="--", lw=1.6,
                label="聚变级门槛 μ≈0.999（FrcCompact 轮）")
    ax1.axhline(MU_FC11, color=PALETTE["gate"], ls="-", lw=1.6,
                label="FC11 硬天花板 μ<0.99978（RMF 窗口）")
    ax1.fill_between(months, MU_FUSION, MU_FC11, color=PALETTE["ok"], alpha=0.10)
    ax1.text(1.0, MU_FC11 * 1.06, "聚变级工作带（0.999 → 0.99978，窄窗 = 设计红线）",
             fontsize=9, color="#1e6b45")

    for name, end, mu, dev, pm in [(r[0], r[2], r[3], r[4], r[5]) for r in MU_LADDER]:
        ax1.plot([end], [mu], "o", color=PALETTE["gate"], ms=6, zorder=5)
        ax1.annotate(f"{name}\nμ≈{mu:g}\n{dev}", xy=(end, mu),
                     xytext=(end, mu * 12), fontsize=8, ha="center", va="bottom",
                     color="#333333",
                     bbox=dict(boxstyle="round,pad=0.22", fc="white",
                               ec=PALETTE["gate"], alpha=0.9),
                     arrowprops=dict(arrowstyle="-", color=PALETTE["gate"], lw=0.9))
    ax1.set_ylim(5e-5, 3e3)
    ax1.set_ylabel("μ（对数轴）", fontsize=11)
    ax1.set_title("可控核聚变五年计划 = 判决漏斗：三判决量 + 八道门（每门预写失败处置）",
                  fontsize=13, pad=14)
    ax1.legend(loc="lower right", fontsize=8.5, framealpha=0.95)
    ax1.grid(alpha=0.25, which="both")

    ax2.set_facecolor(PALETTE["bg"])
    bars = [(r[0], r[1], r[2] - r[1], r[5]) for r in MU_LADDER]
    for name, start, width, pm in bars:
        ax2.bar(start + width / 2, pm, width=width * 0.82, color=PALETTE["bar"],
                alpha=0.85, edgecolor="white")
        ax2.text(start + width / 2, pm + 8, f"{pm}", ha="center", fontsize=8.5)
    cum = np.cumsum([r[5] for r in MU_LADDER])
    ax2b = ax2.twinx()
    ends = [r[2] for r in MU_LADDER]
    ax2b.plot(ends, cum / cum[-1] * 100, color=PALETTE["warn"], lw=2.0, marker="s",
              ms=4.5, label="累计人·月占比 [%]")
    ax2b.set_ylabel("累计人·月占比 [%]", color=PALETTE["warn"], fontsize=10)
    ax2b.tick_params(axis="y", colors=PALETTE["warn"])
    ax2b.set_ylim(0, 105)
    ax2.set_ylabel("阶段人·月", fontsize=11)
    ax2.set_xlabel("月（M0 = 2026-09 起算）", fontsize=11)
    ax2.set_xlim(0, 60)
    ax2.set_ylim(0, 470)
    ax2.grid(alpha=0.25, axis="y")
    ax2.text(3.5, 430, f"判决期（G0+G1）只占全周期 {R4_ladder['判决期成本占比 [%]']}% 人力；"
                       f"两年门（M24）前 {R4_ladder['两年门（M24）前累计占比 [%]']}%",
             fontsize=9.5, color="#333333",
             bbox=dict(boxstyle="round,pad=0.25", fc="white", ec=PALETTE["warn"]))
    ax2b.legend(loc="center right", fontsize=9, framealpha=0.95)

    fig.subplots_adjust(left=0.075, right=0.925, top=0.90, bottom=0.09)
    p = os.path.join(OUT, "fig_gate_funnel.png")
    fig.savefig(p, dpi=140, facecolor=PALETTE["bg"])
    plt.close(fig)
    return p


# ---------------------------------------------------------------------------
# 图 2：μ 的功率标度（D3）
# ---------------------------------------------------------------------------
def fig_mu_power_scaling():
    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(12.4, 5.2))
    fig.patch.set_facecolor(PALETTE["bg"])

    decades = np.linspace(0, 4.2, 200)
    for k, col in zip(K_VALUES, ["#27ae60", "#e67e22", "#c0392b", "#6c3483"]):
        ax1.set_facecolor(PALETTE["bg"])
        ax1.semilogy(decades, [power_ratio_for_decades(d, k) for d in decades],
                     color=col, lw=2.2, label=f"k={k:g}（每数量级 μ 需 "
                                              f"{power_ratio_for_decades(1, k):.0e}× 功率）")
    ax1.axhline(1e4, color=PALETTE["grey"], ls=":", lw=1.4)
    ax1.text(0.05, 1.6e4, "装置功率量级上限 ≈1e4×（桌面 kW → 装置 300 kW 级）",
             fontsize=8.5, color="#555555")
    ax1.axvline(4.0, color=PALETTE["mu"], ls="--", lw=1.6)
    ax1.text(3.75, 3e-1, "桌面 μ≈1e-4 → 聚变级 μ≈0.999（Δ=4 数量级）",
             fontsize=9, rotation=90, va="bottom", ha="right", color=PALETTE["mu"])
    ax1.set_xlabel("μ 提升的（十进位）数量级 Δlog₁₀μ", fontsize=11)
    ax1.set_ylabel("所需输入功率倍数（相对桌面台）", fontsize=11)
    ax1.set_title("D3 判决量：μ ∝ P^k —— 只有 k ≥ 1 才够用五年爬完 4 个数量级",
                  fontsize=12.5, pad=12)
    ax1.legend(fontsize=8.5, loc="lower right", framealpha=0.95)
    ax1.grid(alpha=0.25, which="both")
    ax1.set_ylim(1, 1e17)
    ax2.set_facecolor(PALETTE["bg"])
    mus = np.array([1e-4, 1e-3, 1e-2, 1e-1, 0.5, 0.9, 0.99, 0.999])
    ax2.plot(mus, [mu_signature_cyclotron(m) for m in mus], "o-",
             color=PALETTE["mu"], lw=2.2, label="D1 签名 R_ci = 1/(1−μ) − 1")
    ax2.plot(mus, [tau_gain(m) - 1 for m in mus], "s--",
             color=PALETTE["bar"], lw=2.0, label="FC4 输运增益 1/√(1−μ) − 1")
    for d in DIAG_PRECISIONS[:3]:
        ax2.axhline(d, color=PALETTE["gate"], ls=":", lw=1.1)
        ax2.text(1.5e-4, d * 1.15, f"诊断精度 δ={d:.0e} → μ_min≈{mu_min_detectable(d):.1e}",
                 fontsize=8, color=PALETTE["gate"])
    ax2.axvline(MU_FC11, color=PALETTE["ok"], ls="-", lw=1.4)
    ax2.set_xscale("log")
    ax2.set_yscale("log")
    ax2.set_xlabel("μ", fontsize=11)
    ax2.set_ylabel("可测量相对偏移", fontsize=11)
    ax2.set_title("D1/D2 判决量的灵敏度：桌面台在 μ≳1e-4 处就有 3σ 判别力",
                  fontsize=12.5, pad=12)
    ax2.legend(fontsize=8.5, loc="upper left", framealpha=0.95)
    ax2.grid(alpha=0.25, which="both")

    fig.subplots_adjust(left=0.065, right=0.975, top=0.86, bottom=0.13, wspace=0.26)
    p = os.path.join(OUT, "fig_mu_sensitivity_scaling.png")
    fig.savefig(p, dpi=140, facecolor=PALETTE["bg"])
    plt.close(fig)
    return p


def main():
    f1 = fig_gate_funnel()
    f2 = fig_mu_power_scaling()

    report = {
        "title": "可控核聚变五年计划——判决漏斗数值支撑",
        "date": "2026-09-15",
        "R1_D1_cyclotron_signature": R1_signature,
        "R2_D2_locking_ratio": R2_lock,
        "R3_D3_power_scaling": R3_scaling,
        "R4_mu_ladder_and_person_months": R4_ladder,
        "R5_gate_table": R5_gates,
        "figures": [os.path.basename(f1), os.path.basename(f2)],
        "诚实边界": [
            "本报告是计划文档的数值支撑，不是物理证据：所有门槛取自仓库已证条目"
            "（FC2/FC4/FC5/FC9/FC11/AMC1/AMC7），未新增物理。",
            "μ 主动产生机制仍是第二输入缺口——D1 判决实验正是为了判决它。",
            "人·月与占比是排程假设（非实测），人员成本数字按 leo 规则不入 wiki。",
            "未含：氚/中子设施、μ 主动产生若需微波/激光/额外磁体（Y2 门后重估）。",
        ],
    }
    with open(os.path.join(OUT, "report.json"), "w", encoding="utf-8") as fh:
        json.dump(report, fh, ensure_ascii=False, indent=2)

    lines = [
        "可控核聚变五年计划——判决漏斗（2026-09-15）",
        "=" * 62,
        f"D1 判决量（M6）：R_ci = 1/(1−μ) − 1（FC9）",
        f"  诊断 δ=1e-4 ⟹ 可探测 μ_min = {mu_min_detectable(1e-4):.3e}",
        f"  FC11 硬天花板 μ_max = {MU_FC11:.6f}（D-T）",
        f"D2 判决量（M24）：Λ = τ_E 增益 / S* 惩罚（FC5 预言 ≡1）",
        f"D3 判决量（M12 起）：k = dlnμ/dlnP，4 数量级所需功率倍数：",
    ]
    for k in K_VALUES:
        lines.append(f"  k={k:g}: {power_ratio_for_decades(4.0, k):.3e}×")
    lines += [
        f"μ 阶梯：{R4_ladder['每年推进一个数量级（判据）']}",
        f"总人·月 {total_pm}；判决期占 {R4_ladder['判决期成本占比 [%]']}%；"
        f"M24 前累计 {R4_ladder['两年门（M24）前累计占比 [%]']}%",
        f"峰值人数 {R4_ladder['峰值人数']} 人；节律 "
        f"季度证据包 / 半年裁决 / 年度对外",
        "图：fig_gate_funnel.png, fig_mu_sensitivity_scaling.png",
    ]
    with open(os.path.join(OUT, "summary.txt"), "w", encoding="utf-8") as fh:
        fh.write("\n".join(lines) + "\n")

    print("\n".join(lines))
    print("\n产物：", OUT)


if __name__ == "__main__":
    main()
