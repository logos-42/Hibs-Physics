#!/usr/bin/env python3
"""硬件第二轴·诊断——δ → μ_min 阶梯与生死门 G0/G1 的定量依据

对应 docs/wiki/fusion-program-roadmap.md（§1 判决量 D1 的判别力 + §2 八道门 +
§2.5 前 18 个月逐季度落位）。

【本脚本的纪律】不发明物理与仪器参数。全部数字只有两个来源：
  (a) 仓库已写下的判决量关系式：R_ci = 1/(1−μ) − 1（FC9 + AMC1），
      μ_min = δ/(1+δ)（roadmap §1）——本脚本重算并与其产物逐位对齐；
  (b) roadmap 表里已写下的门/人·月/阶梯目标值——只做原文搬运校验。
桌面判据台的**绝对规格**（腔体/磁体/RF 功率/离子源）在任何页里都没有 ⟹ 只写
[缺口]，禁止填默认值。

产物：artifacts/diagnostics/report.json + summary.txt + fig_diagnostics_ladder.png
"""
import hashlib
import json
import math
import os

import numpy as np

REPO = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
OUT = os.path.join(REPO, "artifacts", "diagnostics")
os.makedirs(OUT, exist_ok=True)

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
import matplotlib.font_manager as fm

for _fp in ("/Library/Fonts/Arial Unicode.ttf",
            "/System/Library/Fonts/STHeiti Light.ttc",
            "/System/Library/Fonts/PingFang.ttc",
            "/System/Library/Fonts/Hiragino Sans GB.ttc"):
    if os.path.exists(_fp):
        fm.fontManager.addfont(_fp)
        plt.rcParams["font.sans-serif"] = [fm.FontProperties(fname=_fp).get_name()]
        break
plt.rcParams["axes.unicode_minus"] = False

M_E = 9.1093837015e-31
U = 1.66053906660e-27
M_DT = 2.5 * U

FIG_LABELS = []


def figtext(s):
    FIG_LABELS.append(str(s))
    return s


def sha16(path):
    h = hashlib.sha256()
    with open(path, "rb") as fh:
        for chunk in iter(lambda: fh.read(8192), b""):
            h.update(chunk)
    return h.hexdigest()[:16]


def read_wiki(name):
    with open(os.path.join(REPO, "docs", "wiki", name), encoding="utf-8") as fh:
        return fh.read()


def load_report(rel):
    with open(os.path.join(REPO, rel), encoding="utf-8") as fh:
        return json.load(fh)


# 判决量关系式（roadmap §1 + FC9/FC4）
def r_ci(mu):
    """D1 签名：回旋共振相对频移 R_ci = 1/(1−μ) − 1（FC9 ω_ci ∝ 1/m_eff）。"""
    return 1.0 / (1.0 - mu) - 1.0


def mu_min_from_delta(delta, n_sigma=1.0):
    """分辨率 δ（相对）⟹ 可探测 μ 下限：R_ci = n·δ ⟺ μ = nδ/(1+nδ)。

    n=1 是 roadmap §1 的口径（μ_min = δ/(1+δ)）；n=3 是生死门 G1 的通过条件
    口径（『R_ci 实测 > 3σ』）——两个口径都来自页面原文，不新设。
    """
    x = n_sigma * delta
    return x / (1.0 + x)


def tau_gain(mu):
    """FC4：τ_E 增益 = 1/√(1−μ)（与 FC5 锁定同因子）。"""
    return 1.0 / math.sqrt(1.0 - mu)


MU_CEIL = 1.0 - M_E / M_DT          # FC11 天花板 μ < 1 − m_e/m_i（D-T）
MU_FUSION = 0.999                   # FrcCompact 轮：紧凑 FRC 级所需 μ

ROAD = load_report("artifacts/fusionroadmap/report.json")
R1 = ROAD["R1_D1_cyclotron_signature"]
R4 = ROAD["R4_mu_ladder_and_person_months"]
FCR = load_report("artifacts/frccompact/report.json")["results"]
WIKI_RM = read_wiki("fusion-program-roadmap.md")

CHECKS = []


def chk(name, cond, detail=""):
    CHECKS.append({"检查": name, "通过": bool(cond), "细节": str(detail)})
    print(("PASS " if cond else "FAIL ") + name + (f"  [{detail}]" if detail else ""))
    return bool(cond)


def relerr(a, b):
    return abs(a - b) / max(abs(b), 1e-300)


# ---------------------------------------------------------------------------
# G1 δ → μ_min 阶梯（1e-3 / 1e-4 / 1e-5）+ 3σ 口径
# ---------------------------------------------------------------------------
DELTAS = [1e-3, 1e-4, 1e-5]
LADDER = {d: {"μ_min（1σ，roadmap §1 口径）": mu_min_from_delta(d, 1.0),
              "μ_min（3σ，G1 通过条件口径）": mu_min_from_delta(d, 3.0),
              "R_ci(μ_min,1σ)": r_ci(mu_min_from_delta(d, 1.0)),
              "到 FC11 天花板的量级差 [decade]": math.log10(MU_CEIL /
                                                       mu_min_from_delta(d, 1.0)),
              "到聚变级 μ=0.999 的量级差 [decade]": math.log10(MU_FUSION /
                                                          mu_min_from_delta(d, 1.0)),
              "该 δ 下 τ_E 增益上限 1/√(1−μ_min)": tau_gain(mu_min_from_delta(d, 1.0))}
          for d in DELTAS}

for d in DELTAS:
    ref = R1["诊断精度 → 可探测 μ 下限"][f"δ={d:.0e}"]["μ_min"]
    chk(f"DG1 δ={d:.0e} 重算 μ_min = δ/(1+δ) 与 fusionroadmap 产物一致",
        relerr(LADDER[d]["μ_min（1σ，roadmap §1 口径）"], ref) < 1e-15,
        f"{LADDER[d]['μ_min（1σ，roadmap §1 口径）']:.6e}")

chk("DG2 3σ 口径把下限抬高约 3×（严格大于 1σ 下限，且比值 < 3）",
    all(LADDER[d]["μ_min（3σ，G1 通过条件口径）"] > LADDER[d]["μ_min（1σ，roadmap §1 口径）"]
        and LADDER[d]["μ_min（3σ，G1 通过条件口径）"]
        / LADDER[d]["μ_min（1σ，roadmap §1 口径）"] < 3.0 for d in DELTAS),
    f"δ=1e-4: {LADDER[1e-4]['μ_min（1σ，roadmap §1 口径）']:.3e} → "
    f"{LADDER[1e-4]['μ_min（3σ，G1 通过条件口径）']:.3e}")

chk("DG3 阶梯三档原文在库（δ ⟹ μ_min≈1.0e-3 / 1.0e-4 / 1.0e-5）",
    all(s in WIKI_RM for s in ("δ=1e-3 ⟹ μ_min≈1.0e-3", "δ=1e-4 ⟹ μ_min≈1.0e-4",
                                "δ=1e-5 ⟹ μ_min≈1.0e-5")), "3/3")

chk("DG4 判别力条件原文在库（R_ci > 3σ 且零假设预测 < 分辨率）",
    "R_ci 实测 > 3σ 且零假设预测 < 分辨率" in WIKI_RM
    and "R_ci 实测 > 3σ 且零假设预测 < 分辨率" in read_wiki(
        "fusion-program-roadmap.md"), "G1 通过条件")

# ---------------------------------------------------------------------------
# 与聚变级的量级差（FC11 天花板 0.999781）
# ---------------------------------------------------------------------------
chk("DG5 FC11 天花板重算 1 − m_e/m_i 与 frccompact 产物一致（D-T）",
    relerr(MU_CEIL, FCR["G3_three_gates"]["mu_crit_rmf"]) < 1e-12,
    f"{MU_CEIL:.9f}")
chk("DG6 天花板原文在库（0.99978 / 0.999781 两处口径）",
    "0.99978" in WIKI_RM and "0.999781" in WIKI_RM
    and "0.99978" in read_wiki("theory-antigravity-confinement.md"),
    "0.99978（FC11 硬天花板）/ 0.999781（D1 判别力段）")
chk("DG7 δ=1e-4 到聚变级的量级差 ≈ 4 个数量级（页面原文『差 4 个数量级』）",
    abs(LADDER[1e-4]["到 FC11 天花板的量级差 [decade]"] - 4.0) < 0.01
    and "差 4 个数量级" in WIKI_RM,
    f"{LADDER[1e-4]['到 FC11 天花板的量级差 [decade]']:.3f} decade")
chk("DG8 聚变级门槛原文在库（μ≈0.999，FrcCompact 轮）",
    "μ≈0.999（FC11 天花板 0.999781）" in WIKI_RM, "roadmap §1")

# ---------------------------------------------------------------------------
# μ 数量级阶梯（roadmap §3 表：目标值 + 月区间 + 人·月，只做搬运校验）
# ---------------------------------------------------------------------------
MU_LADDER_WIKI = [
    ("G0 判据规范", "0–3", "~1e-4（可探测定义）", "桌面（无装置）", 6, 0.52),
    ("G1 D1 判决", "3–6", "1e-3", "桌面判据台", 9, 1.29),
    ("G2 D3 标度初值", "6–12", "1e-2", "中型测试台", 30, 3.88),
    ("G3 独立复现", "12–18", "1e-2（复现）", "中型测试台 ×2", 48, 8.01),
    ("G4 D2 锁定判决", "18–24", "1e-1", "FRC 级约束装置", 72, 14.21),
    ("G5 D-D 产额标度", "24–36", "0.5", "FRC 级 + 中子诊断", 240, 34.89),
    ("G6 燃烧工程门", "36–48", "0.99（若实验证据支持）",
     "D-D/替代实验 + 屏蔽/许可方案；D-T 设施需另立项目", 336, 63.82),
    ("G7 系统级复核", "48–60", "0.999（若实验证据支持）",
     "可重复装置 + 能量账本 + 独立复核", 420, 100),
]
TOTAL_PM = sum(r[4] for r in MU_LADDER_WIKI)
chk("DG9 阶梯人·月合计 1161（roadmap §7 口径）",
    TOTAL_PM == 1161 and R4["总人·月"] == 1161, f"{TOTAL_PM} 人·月")
chk("DG10 阶梯累计占比逐行与 fusionroadmap 产物一致（8 行）",
    all(abs(round(sum(x[4] for x in MU_LADDER_WIKI[:i + 1]) / TOTAL_PM * 100, 2)
            - R4["阶梯表"][i]["累计人·月占比 [%]"]) < 1e-9 for i in range(8)),
    f"末行 {R4['阶梯表'][-1]['累计人·月占比 [%]']}%")
# μ 目标：从页面单元格文本解析（不新造；「1e-2（复现）」按 1e-2 计）
def parse_mu(cell):
    import re as _re
    m = _re.search(r"~?([0-9]+(?:\.[0-9]+)?e-?[0-9]+|[0-9]*\.?[0-9]+)", cell)
    return float(m.group(1))


chk("DG11 μ 目标单元格 8 行原文在库 + 解析值单调不减",
    all(r[2] in WIKI_RM for r in MU_LADDER_WIKI)
    and all(parse_mu(MU_LADDER_WIKI[i][2]) <= parse_mu(MU_LADDER_WIKI[i + 1][2])
            for i in range(7)),
    " / ".join(r[2] for r in MU_LADDER_WIKI))
TARGETS = [parse_mu(r[2]) for r in MU_LADDER_WIKI]
DECADES = [math.log10(TARGETS[i + 1] / TARGETS[i]) for i in range(7)]
chk("DG12 阶梯步长：1e-4→1e-3→1e-2→1e-1 各 1 个数量级；复现阶段重复 1e-2、"
    "末两步（0.99/0.999）<1——按页面原样搬运",
    abs(DECADES[0] - 1.0) < 1e-9 and abs(DECADES[1] - 1.0) < 1e-9
    and abs(DECADES[3] - 1.0) < 1e-9 and abs(DECADES[2]) < 1e-9
    and DECADES[4] < 1.0 and DECADES[5] < 1.0 and DECADES[6] < 1.0,
    "decade 步长 = " + ", ".join(f"{d:.3f}" for d in DECADES))
chk("DG12b 阶梯口径原文在库（『每年推进一个数量级』判据 + 5 年 5 个数量级）",
    "每 12 个月一个数量级" in WIKI_RM
    and "5 年 5 个数量级" in R4["每年推进一个数量级（判据）"], "roadmap §3")

# ---------------------------------------------------------------------------
# 生死门 G0/G1 的定量依据
# ---------------------------------------------------------------------------
G0_PM, G1_PM = 6, 9
chk("DG13 生死门 G0+G1 = 15 人·月 = 全周期 1.29%（roadmap §7）",
    G0_PM + G1_PM == 15 and abs((G0_PM + G1_PM) / TOTAL_PM * 100 - 1.29) < 0.005
    and abs(R4["判决期成本占比 [%]"] - 1.29) < 1e-9, f"{(G0_PM+G1_PM)/TOTAL_PM*100:.2f}%")
chk("DG14 前 18 个月（G0–G3）93 人·月 = 8.01%（不是 1.29% —— 页面已修正的口径）",
    sum(r[4] for r in MU_LADDER_WIKI[:4]) == 93
    and abs(93 / TOTAL_PM * 100 - 8.01) < 0.005,
    f"{93/TOTAL_PM*100:.2f}%")
chk("DG15 G0 交付判据原文在库（δ 实际可达值 → μ_min=δ/(1+δ)）",
    "δ 实际可达值 → μ_min=δ/(1+δ)" in WIKI_RM, "roadmap §2.5 Q1 本季判据")
chk("DG16 G0 的预写失败处置原文在库（δ 只到 1e-3 ⟹ 阶梯起点抬高一个数量级）",
    "δ 只到 1e-3 ⟹ 判决仍可做，但阶梯起点抬高一个数量级" in WIKI_RM, "roadmap §2.5 Q1")
chk("DG17 D1 与 FC4 两条通道函数形式不同（1/(1−μ) vs 1/√(1−μ)）——一致性检验原文在库",
    "函数形式不同" in WIKI_RM and "1/(1−μ) 线性通道 vs 1/√(1−μ) 输运通道" in WIKI_RM,
    "roadmap §1")

TAU_CHANNEL = {f"μ={m:g}": {"D1 线性通道 R_ci": r_ci(m),
                            "FC4 输运通道 1/√(1−μ)−1": tau_gain(m) - 1.0,
                            "比值 R_ci/(1/√(1−μ)−1)": r_ci(m) / (tau_gain(m) - 1.0)}
               for m in (1e-3, 1e-2, 0.1, 0.5, 0.9, 0.99, 0.999)}
_K_SMALL = f"μ={1e-3:g}"
_K_BIG = f"μ={0.999:g}"
chk("DG18 两条通道在小 μ 处比值 →2、在大 μ 处发散（同 μ 双测量 = 互相检验）",
    abs(TAU_CHANNEL[_K_SMALL]["比值 R_ci/(1/√(1−μ)−1)"] - 2.0) < 0.01
    and TAU_CHANNEL[_K_BIG]["比值 R_ci/(1/√(1−μ)−1)"] > 10.0,
    f"{_K_SMALL} → {TAU_CHANNEL[_K_SMALL]['比值 R_ci/(1/√(1−μ)−1)']:.4f}；"
    f"{_K_BIG} → {TAU_CHANNEL[_K_BIG]['比值 R_ci/(1/√(1−μ)−1)']:.2f}")

# ---------------------------------------------------------------------------
# 缺口（诚实：判据台的绝对规格与 δ 预算在任何页里都没有）
# ---------------------------------------------------------------------------
GAPS = [
    "桌面判据台的绝对规格（真空腔尺寸、磁体场强、RF 功率、离子源型式）——"
    "wiki 只有『中型测试台功率量级』的定性表述，无数字",
    "δ 的实际可达值与误差预算（Q1 交付物之一，尚未产出）",
    "『3σ』的统计口径细节（统计量定义、批次合并方式、系统误差分解）——"
    "页面只写通过条件，未给实现",
    "零假设（标准 MHD 预测 R_ci=0）的解析/数值基准实现（Q1 交付物，尚未产出）",
    "回旋共振测量的探针/光谱诊断配置与频率分辨率（Q3 才升级）",
]

# ---------------------------------------------------------------------------
# 图：δ → μ_min 阶梯 + R_ci 灵敏度
# ---------------------------------------------------------------------------
BG = "#faf8f5"


def fig_ladder():
    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(13.2, 5.4))
    fig.patch.set_facecolor(BG)
    ax1.set_facecolor(BG)
    ax2.set_facecolor(BG)

    # 左：μ 阶梯（对数轴）+ 可探测下限 + FC11 天花板
    ends = [3, 6, 12, 18, 24, 36, 48, 60]
    offs = [1.9, 0.42, 2.1, 0.42, 2.2, 2.3, 2.3, 0.34]   # 交替上下，避免相邻标注相撞
    lv = [TARGETS[i] for i in range(8)]
    ax1.set_yscale("log")
    ax1.plot(ends, lv, "o-", color="#8e44ad", lw=2.2, ms=6,
             label=figtext("μ 数量级阶梯（目标曲线，roadmap §3）"))
    for e, v, name, o in zip(ends, lv, ["G0", "G1", "G2", "G3", "G4", "G5", "G6", "G7"],
                             offs):
        ax1.annotate(figtext(f"{name} {v:g}"), xy=(e, v),
                     xytext=(e + (0.5 if name not in ("G5", "G6", "G7") else -1.4),
                             v * o),
                     ha="left" if name not in ("G5", "G6", "G7") else "right",
                     fontsize=7.4, color="#333333",
                     bbox=dict(boxstyle="round,pad=0.15", fc="white", ec="#8e44ad",
                               alpha=0.85, lw=0.7))
    for d, c in ((1e-3, "#e67e22"), (1e-4, "#2e86de"), (1e-5, "#27ae60")):
        ax1.axhline(LADDER[d]["μ_min（1σ，roadmap §1 口径）"], color=c, ls=":", lw=1.6,
                    label=figtext(f"δ={d:.0e} ⟹ μ_min={mu_min_from_delta(d):.1e}（1σ）"))
    ax1.axhline(MU_CEIL, color="#c0392b", ls="-", lw=1.8,
                label=figtext(f"FC11 硬天花板 μ<{MU_CEIL:.6f}"))
    ax1.fill_between([0, 60], MU_FUSION, MU_CEIL, color="#27ae60", alpha=0.16)
    ax1.text(0.8, 1.45e-5, figtext(
        f"聚变级工作带 0.999–{MU_CEIL:.6f}；桌面判据台（μ≈1e-4）到此处 "
        f"差 {math.log10(MU_CEIL/1e-4):.1f} 个数量级"),
        fontsize=7.6, color="#1e6b45")
    ax1.set_xlim(0, 60)
    ax1.set_ylim(3e-6, 20.0)
    ax1.set_xlabel(figtext("月（M0 起算）"), fontsize=10.5)
    ax1.set_ylabel(figtext("μ（对数轴）"), fontsize=10.5)
    ax1.set_title(figtext("δ → μ_min 阶梯：生死门 G0/G1 与聚变级的量级差"),
                  fontsize=11.5, pad=10)
    ax1.grid(alpha=0.25, which="both", ls="--")
    ax1.legend(loc="lower right", fontsize=7.2, framealpha=0.94)

    # 右：R_ci(μ) 灵敏度 + 分辨率线
    mus = np.logspace(-5, -0.0009, 400)
    ax2.set_facecolor(BG)
    ax2.loglog(mus, [r_ci(m) for m in mus], color="#8e44ad", lw=2.4,
               label=figtext("D1 签名 R_ci = 1/(1−μ) − 1（FC9+AMC1）"))
    ax2.loglog(mus, [tau_gain(m) - 1.0 for m in mus], color="#2e86de", lw=2.0, ls="--",
               label=figtext("FC4 输运通道 1/√(1−μ) − 1（同一 μ 双测量互检）"))
    for d, c, k in ((1e-3, "#e67e22", 3.4), (1e-4, "#2e86de", 8.0), (1e-5, "#27ae60", 3.4)):
        ax2.axhline(d, color=c, ls=":", lw=1.4)
        ax2.axhline(3 * d, color=c, ls="-.", lw=1.0, alpha=0.75)
        ax2.text(1.4e-5, 3 * d * k, figtext(f"δ={d:.0e}：1σ 门(细虚线)/3σ 门(点划)"),
                 fontsize=6.6, color=c)
    ax2.axvline(MU_CEIL, color="#c0392b", lw=1.6)
    ax2.text(MU_CEIL * 0.12, 3e3, figtext(f"FC11 天花板\nμ={MU_CEIL:.6f}"),
             fontsize=7.6, color="#c0392b")
    ax2.set_xlabel(figtext("μ（对数轴）"), fontsize=10.5)
    ax2.set_ylabel(figtext("可测相对频移（对数轴）"), fontsize=10.5)
    ax2.set_title(figtext("判别力：R_ci 与分辨率门（δ=1e-3/1e-4/1e-5）"),
                  fontsize=11.5, pad=10)
    ax2.grid(alpha=0.25, which="both", ls="--")
    ax2.legend(loc="lower right", fontsize=7.2, framealpha=0.94)
    ax2.set_xlim(1e-5, 1.0)
    ax2.set_ylim(1e-6, 1e7)

    fig.subplots_adjust(left=0.06, right=0.985, top=0.90, bottom=0.105, wspace=0.20)
    p = os.path.join(OUT, "fig_diagnostics_ladder.png")
    fig.savefig(p, dpi=140, facecolor=BG)
    plt.close(fig)
    return p


def main():
    fig = fig_ladder()
    chk("DG19 图纸文字保持干净（无 缺口/未给出/第二输入 字样）",
        not any(w in lbl for lbl in FIG_LABELS for w in ("缺口", "未给出", "第二输入")),
        f"{len(FIG_LABELS)} 条图注")

    sources = ["docs/wiki/fusion-program-roadmap.md",
               "docs/wiki/theory-frc-compact.md",
               "artifacts/fusionroadmap/report.json",
               "artifacts/frccompact/report.json"]
    report = {
        "title": "硬件轴②诊断——δ → μ_min 阶梯与生死门 G0/G1 定量依据",
        "date": "2026-09-27",
        "对应 wiki": ["docs/wiki/fusion-program-roadmap.md",
                       "docs/wiki/theory-frc-compact.md"],
        "纪律": [
            "数字只有两个来源：仓库已写下的判决量关系式（重算 + 与产物逐位对齐）"
            "或页面已写下的表格值（原文搬运校验）。",
            "桌面判据台的绝对规格与 δ 预算在任何页里都没有 ⟹ 只列 [缺口]。",
            "金额不入库：只用 人·月 / 工期 / 人 / 比例。",
        ],
        "G1_δ_到_μ_min_阶梯": {
            "关系式": "R_ci = 1/(1−μ) − 1（FC9 ω_ci∝1/m_eff + AMC1 m_eff=s(1−μ)）⟹ "
                      "μ_min = nδ/(1+nδ)，nσ 门取 n=1（roadmap §1）或 n=3（G1 通过条件）",
            "1e-3/1e-4/1e-5": {f"δ={d:.0e}": LADDER[d] for d in DELTAS},
            "生死门口径": "G0（M3）交付 δ 实际可达值；G1（M6）通过 ⟺ R_ci 实测 > 3σ "
                          "且零假设预测 < 分辨率",
        },
        "G2_两条通道一致性检验": {
            "说明": "D1（1/(1−μ) 线性）与 FC4（1/√(1−μ) 输运）函数形式不同 ⟹ "
                    "同一 μ 双测量互为一致性检验（roadmap §1）",
            "数值": TAU_CHANNEL,
        },
        "G3_与聚变级的量级差": {
            "FC11 天花板 μ_max": MU_CEIL,
            "聚变级门槛 μ≈": MU_FUSION,
            "δ=1e-4 ⟹ 量级差 [decade]": LADDER[1e-4]["到 FC11 天花板的量级差 [decade]"],
            "阶梯目标（roadmap §3）": "1e-4 → 1e-3 → 1e-2 → 1e-1 → 0.5 → 0.999",
            "派生：相邻目标的对数步长 [decade]": DECADES,
            "派生：阶段月数": [3, 3, 6, 6, 6, 12, 12, 12],
        },
        "G4_生死门人·月依据": {
            "G0": G0_PM, "G1": G1_PM, "G0+G1": G0_PM + G1_PM,
            "全周期人·月": TOTAL_PM,
            "判决期占比 [%]": round((G0_PM + G1_PM) / TOTAL_PM * 100, 2),
            "前 18 个月（G0–G3）人·月": 93,
            "前 18 个月占比 [%]": round(93 / TOTAL_PM * 100, 2),
        },
        "G5_缺口清单": GAPS,
        "图": os.path.basename(fig),
        "来源文件 hash（16 位）": {f: sha16(os.path.join(REPO, f)) for f in sources},
        "checks": CHECKS,
    }
    with open(os.path.join(OUT, "report.json"), "w", encoding="utf-8") as fh:
        json.dump(report, fh, ensure_ascii=False, indent=2)

    lines = [
        "硬件轴②诊断——δ → μ_min 阶梯（2026-09-27）",
        "=" * 62,
        "D1 签名 R_ci = 1/(1−μ) − 1（FC9 + AMC1）；μ_min = nδ/(1+nδ)",
    ]
    for d in DELTAS:
        lines.append(f"  δ={d:.0e}：μ_min(1σ)={LADDER[d]['μ_min（1σ，roadmap §1 口径）']:.4e}"
                     f" / μ_min(3σ)={LADDER[d]['μ_min（3σ，G1 通过条件口径）']:.4e}"
                     f" / 到 FC11 天花板差 {LADDER[d]['到 FC11 天花板的量级差 [decade]']:.2f} decade")
    lines += [
        f"FC11 硬天花板 μ_max = {MU_CEIL:.6f}（1 − m_e/m_i，D-T）；聚变级 μ≈{MU_FUSION}",
        f"生死门：G0={G0_PM} + G1={G1_PM} = {G0_PM+G1_PM} 人·月 = "
        f"{(G0_PM+G1_PM)/TOTAL_PM*100:.2f}%（全周期 {TOTAL_PM} 人·月）；"
        f"前 18 个月 93 人·月 = {93/TOTAL_PM*100:.2f}%",
        "阶梯步长 [decade]：" + ", ".join(f"{d:.3f}" for d in DECADES)
        + "（1e-4→1e-1 各 1 个数量级；复现阶段重复 1e-2、末两步 <1——按页面表原样搬运）",
        f"缺口 {len(GAPS)} 条（判据台绝对规格/δ 预算/3σ 统计口径/零假设基准/诊断配置）",
        f"图：{os.path.basename(fig)}",
        f"检查：{sum(1 for c in CHECKS if c['通过'])}/{len(CHECKS)} 通过",
    ]
    with open(os.path.join(OUT, "summary.txt"), "w", encoding="utf-8") as fh:
        fh.write("\n".join(lines) + "\n")

    print("\n".join(lines))
    failed = [c for c in CHECKS if not c["通过"]]
    print("\n产物：", OUT)
    if failed:
        raise SystemExit(f"诊断轴检查失败 {len(failed)} 条：{[c['检查'] for c in failed]}")


if __name__ == "__main__":
    main()
