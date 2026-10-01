#!/usr/bin/env python3
"""标度类缺口的账本更正：单位类 vs 比值类（SC1–SC8）

leo：「先做第二条」——核「ħ 是单位不是缺口」+「标度类缺口 = 缺第二个标度」。

规则（本脚本要数值演示的那一条）：
    单个量纲常数的数值 = 单位（可被单位制吸收）
    两个同类量之比       = 真缺口（无量纲）

S1  三种单位制下 c / ħ / M₀ 的**数值**（变），vs 无量纲比（不变）
S2 ★ 尺度协变性：M₀ 扫 10 个量级 —— 谱等比缩放、一切比值恒定（相对变化 ~1e-16）
S3 ★★ 自由度计数：框架的量纲常数 {c, ħ, M₀} 恰好够定义 M/L/T 三个基本单位
        → 3 − 3 = 0 → 它们**全部**是单位 → 框架本身零标度内容
S4 ★★ 缺口重排：九张脸逐条分类为单位类 / 比值类 / 未定类
S5 ★★ ħ 的出现位置审查：逐个检查能否被单位吸收
S6 ★★ 层级问题数值：v/M₀、M₀/m_e、G 的无量纲组合

产物：artifacts/scaleaccounting/{report.json, summary.txt, fig_unit_vs_ratio.png,
      fig_scale_covariance.png, fig_gap_ledger.png}
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

OUT = os.path.join(os.path.dirname(__file__), "..", "artifacts", "scaleaccounting")
os.makedirs(OUT, exist_ok=True)

# ---------------------------------------------------------------------------
# 基准常数（SI 与粒子物理两套）
# ---------------------------------------------------------------------------
HBAR_SI = 1.054571817e-34          # J·s
C_SI = 2.99792458e8                # m/s
EV_IN_J = 1.602176634e-19
HBAR_EV = HBAR_SI / EV_IN_J        # eV·s
M0_GEV = 0.977                     # 胶球阶梯标定（RT-E，五态 ±1.64%）
ME_GEV = 0.510998950e-3
V_EW_GEV = 246.2196                # Higgs 真空期望值
ALPHA = 1 / 137.035999084
ALPHA_S_MZ = 0.1179
M_PLANCK_GEV = 1.220890e19
MP_GEV = 0.93827208816             # 质子
N_LADDER = [3, 6, 7, 9, 10]        # RT-E 阶梯（格点最轻五态）


def main():
    report = {"model": "标度类缺口账本：单位类（可溶解）vs 比值类（真缺口）",
              "date": str(date.today()), "results": {}}

    # ---------------------------------------------------------------- S1
    def hbar_in(unit_action):
        """ħ 在「作用量单位 = unit_action（J·s）」下的数值。"""
        return HBAR_SI / unit_action

    unit_rows = []
    for name, ua, uc, um in [
        ("SI", 1.0, 1.0, 1.0),
        ("自然（eV, c=ħ=1）", HBAR_SI, C_SI, EV_IN_J / 1e9),      # 能量用 GeV
        ("普朗克（ħ=c=M_Pl=1）", HBAR_SI, C_SI, EV_IN_J * M_PLANCK_GEV * 1e9),
    ]:
        m0_coord = M0_GEV * 1e9 * EV_IN_J / um
        me_coord = ME_GEV * 1e9 * EV_IN_J / um
        unit_rows.append({
            "单位制": name,
            "ħ 的数值": hbar_in(ua),
            "c 的数值": C_SI / uc,
            "M₀ 的数值": m0_coord,
            "m_e 的数值": me_coord,
            # 两个坐标在**同一单位制内**相除 ⟹ 比值（应当与单位制无关）
            "m_e/M₀ 的数值": me_coord / m0_coord,
        })
    ratios_here = {
        "α（精细结构）": ALPHA,
        "m_e/M₀": ME_GEV / M0_GEV,
        "M₀/m_e": M0_GEV / ME_GEV,
        "v/M₀（层级比）": V_EW_GEV / M0_GEV,
        "√(6/3) = √2（2++/0++）": float(np.sqrt(6 / 3)),
        "√(7/3)（0-+/0++）": float(np.sqrt(7 / 3)),
    }
    report["results"]["S1_unit_vs_ratio"] = {
        "内容": "量纲常数的数值随单位制变（坐标）；无量纲比不变（物理）",
        "单位制表": unit_rows,
        "无量纲比（与单位制无关）": ratios_here,
        "ħ 三种单位制下的数值": [r["ħ 的数值"] for r in unit_rows],
        "M₀ 三种单位制下的数值": [r["M₀ 的数值"] for r in unit_rows],
        "m_e/M₀ 三种单位制下的数值（应完全相同）": [r["m_e/M₀ 的数值"] for r in unit_rows],
        "m_e/M₀ 的跨单位制最大相对差": float(max(
            abs(r["m_e/M₀ 的数值"] / unit_rows[0]["m_e/M₀ 的数值"] - 1) for r in unit_rows)),
        "结论": "ħ 的数值是**单位坐标**：SI 1.055e−34、自然单位 1、普朗克单位 1 —— "
                "三个都是「同一个 ħ」；α、M₀/m_e 在三种单位制下**完全相同**",
    }

    # ---------------------------------------------------------------- S2
    M0_grid = 10.0 ** np.arange(-3, 8)                       # 7 个量级
    spec = np.array([[float(np.sqrt(N)) * m0 for N in N_LADDER] for m0 in M0_grid])
    ratios = spec / spec[:, [0]]
    ratio_worst = float(np.max(np.abs(ratios - ratios[0])))
    exp_ratios = np.array([float(np.sqrt(N / N_LADDER[0])) for N in N_LADDER])
    report["results"]["S2_scale_covariance"] = {
        "内容": "M₀ 扫 7 个量级：全谱等比缩放；一切比值恒定",
        "M₀ 网格": [float(x) for x in M0_grid],
        "比值残差最大（应 ~1e−16）": ratio_worst,
        "解析比值 √(N_i/N_1)": [float(x) for x in exp_ratios],
        "结论": "**SC1/SC2/SC4 的数值版**：谱随 M₀ 线性、一切比值与 M₀ 无关 → "
                "这一形状**原理上**读不出 M₀（SC6）",
    }

    # ---------------------------------------------------------------- S3
    constants = ["c（SLS1）", "ħ（GQR 关系层）", "M₀（胶球阶梯标定）"]
    report["results"]["S3_degrees_of_freedom"] = {
        "内容": "框架的量纲常数 vs 基本单位数",
        "框架显式使用的量纲常数": constants,
        "基本单位数": ["质量 M", "长度 L", "时间 T"],
        "计数": f"{len(constants)} − 3 = {len(constants) - 3}",
        "结论": "3 个量纲常数**恰好够**定义 M/L/T 三个基本单位 → 可以把它们全部置 1 "
                "→ **它们全部是单位** → 框架本身**零标度内容**。"
                "（若把 G、e 也计入：N 个量纲常数最多给出 N−3 个独立无量纲比，结论不变，清单多两项。）",
    }

    # ---------------------------------------------------------------- S4
    ledger = [
        ("c 的数值", "2.998e8 m/s", "单位类", "已溶解（§8 字典轮）", 0),
        ("ħ 的数值", "1.055e−34 J·s", "单位类", "**本条提出溶解**", 0),
        ("M₀ 的数值", "0.977 GeV", "单位类", "**本条提出溶解**（标定动作仍是记账项）", 0),
        ("e 的数值", "1.602e−19 C", "单位类", "真内容 = α；e 可被单位吸收", 0),
        ("966× = M₀/(2m_e)", "≈ 9.66e2", "比值类", "**真缺口**（M₀≈0.987 GeV 那一版）", 1),
        ("v/M₀（层级比）", "≈ 2.52e2", "比值类", "**真缺口**；标准理论也没解决", 1),
        ("α", "7.297e−3", "比值类", "真缺口；标准里是自由输入", 1),
        ("α_s(M_Z)", "0.1179", "比值类", "真缺口；有跑动但值仍是输入", 1),
        ("G·m_p²/(ħc)", "≈ 5.9e−39", "比值类", "真缺口（层级）", 1),
        ("ρ·α·k·κ·ν 等内部系数", "未定", "未定类", "需动力学方程；**不属标度类**", 2),
    ]
    report["results"]["S4_gap_ledger"] = {
        "内容": "九张脸（原缺口清单）逐条重分类",
        "表": [{"缺口": g, "值": v, "类": k, "状态": s} for g, v, k, s, _ in ledger],
        "计数": {"单位类（可溶解）": sum(1 for r in ledger if r[2] == "单位类"),
                 "比值类（真缺口）": sum(1 for r in ledger if r[2] == "比值类"),
                 "未定类": sum(1 for r in ledger if r[2] == "未定类")},
        "结论": "**标度类缺口 = 单位类（自动消掉）+ 比值类（真难）**。"
                "把单位类拆出去之后，真缺口只剩**无量纲比**，而干净的名字是"
                "「**框架只有一个标度 M₀，缺第二个标度 v**」= 层级问题。",
    }

    # ---------------------------------------------------------------- S5
    hbar_uses = [
        {"位置": "GQR4–G6 关系层（ħ = h/2π、p = h/λ、E = hf）", "类型": "纯关系",
         "能被单位吸收": True},
        {"位置": "VBC 修正式 ƛ = ħ/(m c)（约化康普顿波长）", "类型": "与 m 搭配",
         "能被单位吸收": True, "说明": "m 的单位和 ħ 的单位互相吸收"},
        {"位置": "C5 数值代入（ħ、m_e、c 代真实常数验 ħω₀ = mc²）", "类型": "数值校验",
         "能被单位吸收": True, "说明": "验的是恒等式，不是导出 ħ 的数值"},
    ]
    report["results"]["S5_hbar_audit"] = {
        "内容": "框架里 ħ 的全部出现位置，逐个判定能否被单位吸收",
        "表": hbar_uses,
        "全部可吸收": all(u["能被单位吸收"] for u in hbar_uses),
        "结论": "现有出现**全部**可被单位吸收 → 没有「不可归约的无量纲组合」→ "
                "**ħ 的数值不是物理缺口**（**死法**：若将来出现一个不可归约的组合，本条死）",
    }

    # ---------------------------------------------------------------- S6
    hierarchy = {
        "v/M₀": V_EW_GEV / M0_GEV,
        "M₀/m_e（当前 M₀=0.977）": M0_GEV / ME_GEV,
        "M₀/(2 m_e)（记作 966× 的那个量）": M0_GEV / (2 * ME_GEV),
        "M₀/(2 m_e)（旧版 M₀=0.987）": 0.987 / (2 * ME_GEV),
        "α²×10": 10 * ALPHA ** 2,
        "m_e/M₀": ME_GEV / M0_GEV,
        "M₀/m_P": M0_GEV / M_PLANCK_GEV,
        "v/m_P": V_EW_GEV / M_PLANCK_GEV,
    }
    report["results"]["S6_hierarchy"] = {
        "内容": "真缺口的具体值（全部无量纲）",
        "值": hierarchy,
        "α²×10 与 m_e/M₀ 的相对差": abs(hierarchy["α²×10"] / hierarchy["m_e/M₀"] - 1),
        "结论": "`966×` 的确切定义 = M₀/(2m_e)（旧版 M₀≈0.987 GeV 给 965.8）→ "
                "它是**比值**。标准模型把 v/M₀ ≈ 252 这个数叫**层级问题**，也没有解决。",
    }

    # ---------------------------------------------------------------- 图 1
    fig, axes = plt.subplots(1, 2, figsize=(13.5, 5.6))
    ax = axes[0]
    labels = [r["单位制"] for r in unit_rows]
    vals = [r["ħ 的数值"] for r in unit_rows]
    ax.bar(range(3), vals, color=["C0", "C1", "C2"], alpha=0.85, width=0.6)
    ax.set_yscale("log")
    for xi, v in zip(range(3), vals):
        ax.text(xi, v * 3, f"{v:.3e}", ha="center", fontsize=9)
    ax.set_xticks(range(3))
    ax.set_xticklabels([l.replace("（", "\n（") for l in labels], fontsize=10)
    ax.set_ylabel("ħ 的数值（作用量单位下）")
    ax.set_title("ħ 的数值随单位制变\nS1：SI 1.055e−34 / 自然 1 / 普朗克 1\n→ 它是坐标，不是不变量", fontsize=11)
    ax.grid(alpha=0.3, axis="y")

    ax = axes[1]
    rnames = list(ratios_here.keys())
    rvals = [ratios_here[k] for k in rnames]
    ax.barh(range(len(rnames)), rvals, color="C3", alpha=0.85, height=0.6)
    ax.set_xscale("log")
    ax.set_yticks(range(len(rnames)))
    ax.set_yticklabels(rnames, fontsize=9)
    ax.set_xlabel("数值（三种单位制下完全相同）")
    ax.set_title("无量纲比不随单位制变\nS1：α、M₀/m_e、v/M₀、√2、√(7/3)\n→ 物理住在这里", fontsize=11)
    ax.grid(alpha=0.3, axis="x")
    fig.tight_layout()
    fig.savefig(os.path.join(OUT, "fig_unit_vs_ratio.png"), dpi=150)
    plt.close(fig)

    # ---------------------------------------------------------------- 图 2
    fig, axes = plt.subplots(1, 2, figsize=(13.5, 5.4))
    ax = axes[0]
    m0_bars = [0.5, 1.0, 2.0]
    w = 0.15
    for i, N in enumerate(N_LADDER):
        ys_b = [float(np.sqrt(N)) * m0 for m0 in m0_bars]
        xs_b = [k + (i - 2) * w for k in range(len(m0_bars))]
        ax.bar(xs_b, ys_b, width=w, alpha=0.85, label=f"N={N}")
    ax.set_xticks(range(len(m0_bars)))
    ax.set_xticklabels([f"M₀ = {m}" for m in m0_bars])
    ax.set_ylabel("m = √N·M₀")
    ax.set_title("S2 左：M₀ 翻倍 → 全谱每一档都翻倍\n（5 档等比缩放，形状不变）", fontsize=11)
    ax.grid(alpha=0.3, axis="y")
    ax.legend(fontsize=9, ncol=2)

    ax = axes[1]
    for i, N in enumerate(N_LADDER):
        ax.semilogx(M0_grid, ratios[:, i], "o-", ms=4,
                    label=f"√({N}/{N_LADDER[0]})")
    ax.set_xlabel("M₀（任意单位）")
    ax.set_ylabel("m_i / m_1")
    ax.set_title(f"S2 右：一切比值与 M₀ 无关\n残差 {ratio_worst:.1e} → 这一形状读不出标度（SC6）", fontsize=11)
    ax.grid(alpha=0.3)
    ax.legend(fontsize=9)
    fig.tight_layout()
    fig.savefig(os.path.join(OUT, "fig_scale_covariance.png"), dpi=150)
    plt.close(fig)

    # ---------------------------------------------------------------- 图 3
    fig, ax = plt.subplots(figsize=(11, 6.2))
    colors = {"单位类": "C0", "比值类": "C3", "未定类": "0.6"}
    ys = np.arange(len(ledger))[::-1]
    for (g, v, k, s, _), y in zip(ledger, ys):
        ax.barh(y, 1.0, color=colors[k], alpha=0.8, height=0.62)
        ax.text(1.03, y, f"{k}   |   {s.replace('**', '')}", va="center", fontsize=9.5)
    ax.set_yticks(ys)
    ax.set_yticklabels([f"{g}\n（{v}）" for g, v, k, s, _ in ledger], fontsize=9)
    ax.set_xlim(0, 3.1)
    ax.set_xticks([])
    ax.set_title("S4 缺口重排：单位类（蓝，可溶解）/ 比值类（红，真缺口）/ 未定类（灰）\n"
                 "→ 标度类缺口 = 单位 + 比值 两样混在一起；拆开后真缺口只剩无量纲比", fontsize=11)
    fig.tight_layout()
    fig.savefig(os.path.join(OUT, "fig_gap_ledger.png"), dpi=150)
    plt.close(fig)

    report["conclusion"] = (
        "① S1/S3：框架的量纲常数 {c, ħ, M₀} 恰好够定义 M/L/T 三个基本单位 → 它们**全部是单位** "
        "（数值随单位制变，见 S1 的三行）→ 框架本身零标度内容。"
        "② S2/S6：一切**比值**与 M₀ 无关（残差 ~1e−16）→ SC6：这一形状**原理上**读不出 M₀。"
        "③ S4/S5：ħ 的数值与 966× **不是同一张脸**——ħ 是单位类（可溶解，与 c 同款动作），"
        "966× = M₀/(2m_e) 是比值类（真缺口）。"
        "④ 干净陈述：**标度类缺口 = 「框架只有一个标度 M₀，缺第二个标度 v」= 层级问题**"
        "（v/M₀ ≈ 252）——标准理论也没解决它。"
        "**死法**：若出现一个不能被 M₀ ↦ lam·M₀ 吸收的量纲量，本划分死；现框架全部可证伪预言都是比值形（√2、√(7/3)…）→ 相容。"
        "**诚实**：本脚本零新预言、零新物理；它只把缺口的分类改对，**不给出第二个标度**。"
    )
    report["files"] = {"fig_unit_vs_ratio": "fig_unit_vs_ratio.png",
                       "fig_scale_covariance": "fig_scale_covariance.png",
                       "fig_gap_ledger": "fig_gap_ledger.png"}

    with open(os.path.join(OUT, "report.json"), "w", encoding="utf-8") as f:
        json.dump(report, f, ensure_ascii=False, indent=2)

    lines = [
        "标度类缺口账本更正：单位类（可溶解）vs 比值类（真缺口）（SC1–SC8）",
        "=" * 74,
        "S1 ħ 三种单位制下的数值        = " + ", ".join(f"{v:.3e}" for v in
                                                    [r["ħ 的数值"] for r in unit_rows]),
        f"S1 M₀ 三种制下的数值          = " + ", ".join(f"{r['M₀ 的数值']:.3e}" for r in unit_rows),
        f"S1 m_e/M₀ 跨三制最大相对差     = "
        f"{max(abs(r['m_e/M₀ 的数值'] / unit_rows[0]['m_e/M₀ 的数值'] - 1) for r in unit_rows):.2e}（应 0）",
        f"S1 不变量 α                    = {ALPHA:.6e}（三制相同）",
        f"S1 不变量 m_e/M₀               = {ratios_here['m_e/M₀']:.4e}（三制相同）",
        f"S2 比值残差（扫 7 个量级）      = {ratio_worst:.2e}",
        f"S3 量纲常数数 − 基本单位数      = {len(constants)} − 3 = {len(constants) - 3}",
        "S4 单位类 / 比值类 / 未定类     = "
        f"{report['results']['S4_gap_ledger']['计数']['单位类（可溶解）']} / "
        f"{report['results']['S4_gap_ledger']['计数']['比值类（真缺口）']} / "
        f"{report['results']['S4_gap_ledger']['计数']['未定类']}",
        f"S5 ħ 出现位置全部可被单位吸收   = {report['results']['S5_hbar_audit']['全部可吸收']}",
        f"S6 v/M₀（层级比）              = {hierarchy['v/M₀']:.2f}",
        f"S6 M₀/(2m_e)（= 966× 的量）    = {hierarchy['M₀/(2 m_e)（记作 966× 的那个量）']:.1f}"
        f"（旧 M₀=0.987 给 {hierarchy['M₀/(2 m_e)（旧版 M₀=0.987）']:.1f}）",
        "=" * 74,
        "结论：ħ 的数值 = 单位（溶解）；966× = 比值（真缺口）。",
        "      干净名字：标度类缺口 = 缺第二个标度（层级问题 v/M₀ ≈ 252）。",
    ]
    with open(os.path.join(OUT, "summary.txt"), "w", encoding="utf-8") as f:
        f.write("\n".join(lines) + "\n")

    print(json.dumps({k: v for k, v in report["results"].items()
                      if k in ("S1_unit_vs_ratio", "S2_scale_covariance",
                               "S3_degrees_of_freedom", "S5_hbar_audit")},
                     ensure_ascii=False, indent=2)[:2200])
    print("\n-> 产物:", os.path.abspath(OUT))


if __name__ == "__main__":
    main()
