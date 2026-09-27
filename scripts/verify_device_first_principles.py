#!/usr/bin/env python3
"""硬件第一轴·装置——把「写在 wiki 正文里的装置论述」变成可锚定量

对应 docs/wiki/theory-antigravity-confinement.md（反引力约束稳态聚变环装置设计）
+ docs/wiki/theory-frc-compact.md（FC8/FC12/CFR2 现实锚点）
+ docs/wiki/theory-plasma-fusion.md（PF5/PF7 环几何与应力）。

【本脚本的纪律】不发明设计参数。每一条可锚定量必须满足二选一：
  (a) 由仓库已证定理（PF3/PF5/PF7/FC8/FC9/FC12/FC11）**重算**，且算出的值
      与仓库已有产物（artifacts/*/report.json）**逐位一致**；或
  (b) 是仓库某页**已经写下的**锚点值——脚本只做「原文出现即通过」的搬运校验。
反引力约束环**自身**的几何尺寸（环半径/厚度/间距/线圈匝数）在任何页里都没有
给出 ⟹ 只写 [缺口]，禁止填默认值（缺口清单见 report.json 与 wiki 正文）。

产物：artifacts/device/report.json + summary.txt + fig_device_anchors.png
"""
import hashlib
import json
import math
import os
import re

import numpy as np

REPO = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
OUT = os.path.join(REPO, "artifacts", "device")
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

# ---------------------------------------------------------------------------
# 常数（真实值，SI）——与仓库其它 verify 脚本同源
# ---------------------------------------------------------------------------
MU0 = 4 * math.pi * 1e-7
E_CH = 1.602176634e-19
U = 1.66053906660e-27
M_DT = 2.5 * U                     # D-T 平均离子质量（D:T = 1:1）
C_LIGHT = 2.99792458e8             # m/s

# 装置长（FC12 上界 c/L 用）——**出处：scripts/plot_artificial_field.py 的 L = 0.5**，
# 不是本脚本新设的参数；L 变化的影响单独给灵敏度表，不另选默认值。
L_DEVICE = 0.5

# RMF 选频倍数区间（FC12：k ∈ [2,5]）——出处 ProjectionPhysics/FrcCompact.lean
K_BAND = (2.0, 5.0)

FIG_LABELS = []          # 图纸文字登记（用于「图纸保持干净」门禁）


def figtext(s):
    FIG_LABELS.append(str(s))
    return s


def sha16(path):
    """16 位 SHA-256 前缀（与 wiki v2 source_hash 同口径）。"""
    h = hashlib.sha256()
    with open(path, "rb") as fh:
        for chunk in iter(lambda: fh.read(8192), b""):
            h.update(chunk)
    return h.hexdigest()[:16]


def read_wiki(name):
    p = os.path.join(REPO, "docs", "wiki", name)
    with open(p, encoding="utf-8") as fh:
        return fh.read()


def load_report(rel):
    p = os.path.join(REPO, rel)
    with open(p, encoding="utf-8") as fh:
        return json.load(fh)


def f_ci(B_T, m_kg):
    """FC9：离子回旋频率 f_ci = eB/(2πm_eff)（μ=0 时 m_eff = m_i）。"""
    return E_CH * B_T / (2.0 * math.pi * m_kg)


def b_cap(r_s, sigma_y, t):
    """FC8/PF7 反解：B² ≤ 2μ₀σ_y·t/R_c ⟹ B_cap = √(2μ₀σ_yt/r_s)。"""
    return math.sqrt(2.0 * MU0 * sigma_y * t / r_s)


def r_max(B, sigma_y, t):
    """PF7：σ ≤ σ_y ⟺ R ≤ 2μ₀σ_y·t/B²。"""
    return 2.0 * MU0 * sigma_y * t / (B * B)


# ---------------------------------------------------------------------------
# 载入仓库已有产物（重算后必须与它们逐位一致——这就是门禁的「锚」）
# ---------------------------------------------------------------------------
WIKI_CONF = read_wiki("theory-antigravity-confinement.md")
WIKI_FRC = read_wiki("theory-frc-compact.md")
WIKI_PF = read_wiki("theory-plasma-fusion.md")
WIKI_MZ = read_wiki("masstozero.md")
PF = load_report("artifacts/plasmafusion/report.json")["results"]
FCR = load_report("artifacts/frccompact/report.json")["results"]

CHECKS = []


def chk(name, cond, detail=""):
    CHECKS.append({"检查": name, "通过": bool(cond), "细节": str(detail)})
    print(("PASS " if cond else "FAIL ") + name + (f"  [{detail}]" if detail else ""))
    return bool(cond)


def relerr(a, b):
    return abs(a - b) / max(abs(b), 1e-300)


# ---------------------------------------------------------------------------
# D3 线圈峰场与环几何（全部由 PF7/FC8 重算 + CFR2 锚点原文）
# ---------------------------------------------------------------------------
# 机械门上界：与 scripts/verify_frc_compact.py 的 B_cap(r_s, σ_y=2e9, t=0.0135)
# 同参数（该脚本注释：σ_y=2GPa, t=1.35cm ⟹ B_cap(10cm)=26T）
SIGMA_Y_FC = 2.0e9
T_FC = 0.0135
B_CAP_10CM = b_cap(0.10, SIGMA_Y_FC, T_FC)
# wiki 页里的另一组独立口径：R=10cm、t=1cm、σ_y=1GPa ⟹ B_cap ≈ 15.8T
B_CAP_10CM_WIKI = b_cap(0.10, 1.0e9, 0.01)
# PF7 环几何：冷加工铜 σ_y=250MPa、壁厚 0.5m（wiki F4/F5 口径）
SIGMA_Y_CU = 250e6
T_CU = 0.5
R_MAX_12_2 = r_max(12.2, SIGMA_Y_CU, T_CU)

fc_rows = {r["r_s_m"]: r for r in FCR["G3_three_gates"]["rows"]}
fc_g6 = {r["mu"]: r for r in FCR["G6_rmf_window"]["rows"]}

chk("DV1 PF7 重算 R_max(12.2T, 冷加工铜 250MPa, t=0.5m) 与 plasmafusion 产物一致",
    relerr(R_MAX_12_2, PF["F5_min_ring"]["stress_limit_Rmax_12.2T_m"]) < 1e-12,
    f"{R_MAX_12_2:.6f} m")
chk("DV2 FC8 重算 B_cap(10cm, σ_y=2GPa, t=1.35cm) 与 frccompact 产物一致",
    relerr(B_CAP_10CM, fc_rows[0.10]["B_cap_T"]) < 1e-12, f"{B_CAP_10CM:.4f} T")
chk("DV3 wiki 口径 B_cap(R=10cm, t=1cm, σ_y=1GPa) ≈ 15.8T（PF7 反解）",
    abs(B_CAP_10CM_WIKI - 15.8) < 0.1, f"{B_CAP_10CM_WIKI:.2f} T")

F_CI_9T = f_ci(9.0, M_DT)
chk("DV4 FC9 重算 f_ci(B=9T, D-T) 与 frccompact RMF 窗口表一致",
    relerr(F_CI_9T, fc_g6[0.0]["f_ci_MHz"] * 1e6) < 1e-12, f"{F_CI_9T/1e6:.3f} MHz")

BAND = (K_BAND[0] * F_CI_9T, K_BAND[1] * F_CI_9T)
LIGHT_LIMIT = C_LIGHT / L_DEVICE
B_MAX_BAND = C_LIGHT * 2.0 * math.pi * M_DT / (K_BAND[1] * E_CH * L_DEVICE)
chk("DV5 FC12 选频带 [2,5]·f_ci(B=9T) 完全落在 c/L 上限之下（L=0.5m）",
    BAND[1] < LIGHT_LIMIT, f"{BAND[1]/1e6:.1f} < {LIGHT_LIMIT/1e6:.1f} MHz")
chk("DV6 FC12 上界条件反解 B（k=5, L=0.5m）——带内即低于 c/L 的场强上限",
    15.0 < B_MAX_BAND < 25.0, f"B < {B_MAX_BAND:.3f} T")

# CFR2 现实锚点原文（wiki 已写下的值，只做搬运校验）
CFR2_ANCHORS = [
    ("末级燃烧室直径", "12cm 直径燃烧室", 0.12, "m", "theory-frc-compact.md §现实锚点"),
    ("真空场下界", "真空场 7-9T", 7.0, "T", "theory-frc-compact.md §现实锚点"),
    ("真空场上界", "真空场 7-9T", 9.0, "T", "theory-frc-compact.md §现实锚点"),
    ("压缩峰场", "压缩到 **35T**", 35.0, "T", "theory-frc-compact.md §现实锚点"),
    ("脉冲长度下界", "2-5ms 脉冲", 0.002, "s", "theory-frc-compact.md §现实锚点"),
    ("脉冲长度上界", "2-5ms 脉冲", 0.005, "s", "theory-frc-compact.md §现实锚点"),
    ("单脉冲产额下界", "20-40 MJ/脉冲", 20.0, "MJ", "theory-frc-compact.md §现实锚点"),
    ("单脉冲产额上界", "20-40 MJ/脉冲", 40.0, "MJ", "theory-frc-compact.md §现实锚点"),
    ("能量增益", "**增益 G~10**", 10.0, "—", "theory-frc-compact.md §现实锚点"),
    ("形成室长度", "~0.8m 形成室", 0.8, "m", "theory-frc-compact.md §现实锚点"),
    ("压缩线圈级数", "10 级压缩", 10.0, "级", "theory-frc-compact.md §现实锚点"),
    ("燃烧室长度下界", "3-6m 燃烧室", 3.0, "m", "theory-frc-compact.md §现实锚点"),
    ("燃烧室长度上界", "3-6m 燃烧室", 6.0, "m", "theory-frc-compact.md §现实锚点"),
    ("wiki 口径 B_cap", "B_cap ≈ 15.8T", 15.8, "T", "theory-frc-compact.md §机械门"),
]
for name, text, val, unit, src in CFR2_ANCHORS:
    chk(f"DV7 锚点原文在库 {name}（{text!r}）", text in WIKI_FRC, src)

# 反引力约束环自身的几何量：任何页都没给 ⟹ [缺口]（禁止填默认值）
ANTIGRAVITY_GEOM_GAP = [
    "双流环（Cu 慢流环 / H 快流环）的半径、厚度、环间距、环流速度与配比数值",
    "RMF 线圈的型式、匝数、线材、冷却与导体截面",
    "反引力约束环整机的径向/轴向包络（该页只有同心三层示意，无尺寸）",
    "顶部/底部端部结构与真空腔尺寸",
]
HOLLOW_NOT_GIVEN = re.search(r"\d+(\.\d+)?\s*(cm|m|mm|T)\b", WIKI_CONF) is None
chk("DV8 装置设计页确实未给出自身几何尺寸（grep 无尺寸数字 ⟹ [缺口] 成立）",
    HOLLOW_NOT_GIVEN, "theory-antigravity-confinement.md 全文无 cm/m/mm/T 量纲数字")

# ---------------------------------------------------------------------------
# D1 关键件（三层架构原文 + 双流环配比锚点）
# ---------------------------------------------------------------------------
KEY_PARTS = [
    ("① 内", "聚变燃料区", "D-T 等离子体，反引力约束作用对象", "FC 轮燃料层"),
    ("② 中", "双流环", "Cu 慢流环（重离子惯性锚定）+ H 快流环（轻离子快速响应）",
     "DR1–DR5 / PA1–PA8"),
    ("③ 外", "RMF 时变场源", "旋转磁场线圈，持续变化的电磁场 = 引力场发生器",
     "PA4 / FC9–FC11"),
]
chk("DV9 三层架构三条原文在库（装置设计页 §2 系统架构表）",
    all(p[1] in WIKI_CONF and p[2] in WIKI_CONF for p in KEY_PARTS),
    " / ".join(p[1] for p in KEY_PARTS))
chk("DV10 Cu:H 锚定权重比 106:1 在库（装置设计页 + plasma-antigravity 页）",
    "106:1" in WIKI_CONF and "106:1" in read_wiki("theory-plasma-antigravity.md"),
    "Cu:H = 106:1")

# FRC 现实技术的保留/砍掉清单（装置设计页 §5）
FRC_KEEP = [("θ-pinch 形成（一次）", "保留"), ("RMF 旋转磁场维持", "保留并强化"),
            ("分段压缩（10 级递减线圈）", "砍掉"), ("自然偏滤器（开磁力线）", "AMC7 切向流捕获"),
            ("NBI 大轨道离子", "双流环快流")]
chk("DV11 FRC 技术映射五条在库（保留/砍掉清单）",
    all(k in WIKI_CONF for k, _v in FRC_KEEP) and "砍掉" in WIKI_CONF,
    "5 条映射")

# ---------------------------------------------------------------------------
# D4 工期（排期锚点：装置线逐季度里程碑——取自 roadmap §2.5，不新造）
# ---------------------------------------------------------------------------
MILESTONES = [
    # (里程碑, 季度, 月区间, 人·月, 门, 校验文件, wiki/脚本 原文片段)
    ("桌面判据台规格书 + 询价单（只问不买）", "Q1", "M1–3", 1.0, "G0（M3）",
     "wiki", "桌面判据台规格书与询价单（只问不买）"),
    ("桌面判据台建成（腔体/离子源/RF/探针）", "Q2", "M4–6", 2.5, "G1（M6）生死门",
     "script", "桌面判据台建成（腔体/离子源/RF/探针）"),
    ("诊断升级（探针阵列 + 光谱）", "Q3", "M7–9", 3.0, "—",
     "wiki", "诊断升级（探针阵列+光谱）"),
    ("中型测试台建成", "Q4", "M10–12", 7.5, "G2（M12）",
     "wiki", "中型测试台建成"),
    ("复现装置 #2 建成（独立场地/独立团队）", "Q5", "M13–15", 9.0, "—",
     "wiki", "复现装置 #2（独立场地、独立团队）"),
    ("两装置重复性统计 + FRC 级装置参数表（M24 门前置设计）", "Q6", "M16–18", 7.5,
     "G3（M18）", "wiki", "公共数据集 + FRC 级装置参数表"),
]
WIKI_RM = read_wiki("fusion-program-roadmap.md")
RM_SCRIPT = open(os.path.join(REPO, "scripts", "verify_fusion_roadmap.py"),
                 encoding="utf-8").read()
SRC_TEXT = {"wiki": WIKI_RM, "script": RM_SCRIPT}
chk("DV12 装置线六个里程碑原文在库（roadmap §2.5 + verify_fusion_roadmap 季度交付）",
    all(m[6] in SRC_TEXT[m[5]] for m in MILESTONES),
    "；".join(m[6] for m in MILESTONES if m[6] not in SRC_TEXT[m[5]]) or "6/6")
LANE_PM_DEVICE = 30.5
chk("DV13 装置线 18 个月人·月 = 30.5（roadmap §2.5 工作流分解，脚本 assert 口径）",
    abs(sum(m[3] for m in MILESTONES) - LANE_PM_DEVICE) < 1e-9,
    f"Σ = {sum(m[3] for m in MILESTONES)}")
chk("DV14 装置线人·月与 fusionroadmap 产物一致（同一张表两个脚本不同算法）",
    relerr(json.load(open(os.path.join(REPO, "artifacts/fusionroadmap/report.json"),
                          encoding="utf-8"))["R6_first_18_months_quarterly"]
           ["工作流人·月分解"]["装置线"], LANE_PM_DEVICE) < 1e-12, LANE_PM_DEVICE)

# ---------------------------------------------------------------------------
# 图：装置可锚定量（环几何/场强标尺 + FC12 选频带）
# ---------------------------------------------------------------------------
BG = "#faf8f5"


def fig_device_anchors():
    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(13.2, 5.9))
    fig.patch.set_facecolor(BG)
    ax1.set_facecolor(BG)
    ax2.set_facecolor(BG)

    # 左：环几何/场强标尺（log-log）
    #   点旁只放短数值标签（无箭头、无边框 ⟹ 不会互相遮挡）；完整名称统一进图例
    anchors = [
        ("CFR2 末级燃烧室 12cm｜压缩 35T（脉冲，theory-frc-compact.md §现实锚点）",
         "35T（脉冲）", 0.12, 35.0, "#c0392b", (1.30, 1.10)),
        ("r_s=10cm 机械上限 B_cap=26.0T（FC8 反解）",
         "26.0T", 0.10, B_CAP_10CM, "#e67e22", (1.22, 1.10)),
        ("wiki 口径 B_cap=15.85T（t=1cm, σ_y=1GPa，PF7）",
         "15.85T", 0.10, B_CAP_10CM_WIKI, "#8e44ad", (1.32, 1.06)),
        ("CFR2 真空场 7–9T（脉冲）", "7–9T", 0.12, 8.0, "#2e86de", (1.30, 1.08)),
        ("微型环 R=0.6m / a=0.2m，B=15T（PF 工程表）",
         "15T", 0.6, 15.0, "#27ae60", (1.12, 1.12)),
        ("SPARC R=1.85m，B=12.2T（现实基准）",
         "12.2T", 1.85, 12.2, "#16a085", (1.10, 1.12)),
        ("ITER R=6.2m，B=5.3T（对照）", "5.3T", 6.2, 5.3, "#95a5a6", (0.30, 1.10)),
    ]
    ax_handles = []
    for full, short, r, b, c, (mx, my) in anchors:
        ax1.plot([r], [b], "o", color=c, ms=8, zorder=5)
        ax1.text(r * mx, b * my, figtext(short), fontsize=7.6, color="#333333",
                 ha="left", va="bottom", zorder=6)
        ax_handles.append(plt.Line2D([], [], marker="o", ls="none", color=c, ms=7,
                                     label=figtext(full)))
    rr = np.logspace(-2.1, 1.0, 200)
    for s, t, c, lab in ((SIGMA_Y_CU, T_CU, "#2e86de", "PF7 冷加工铜 250MPa, t=0.5m"),
                         (2e9, 0.0135, "#e67e22", "FC8 σ_y=2GPa, t=1.35cm")):
        ax1.loglog(rr, [b_cap(x, s, t) for x in rr], lw=1.8, color=c,
                   label=figtext(lab))
    ax1.set_xscale("log")
    ax1.set_yscale("log")
    ax1.set_xlim(0.06, 10)
    ax1.set_ylim(3, 130)
    ax1.set_xlabel(figtext("装置半径 R / r_s（m，对数）"), fontsize=10.5)
    ax1.set_ylabel(figtext("线圈峰场 B（T，对数）"), fontsize=10.5)
    ax1.set_title(figtext("装置可锚定量：环几何 × 线圈峰场（全部来自已证条目/现实锚点）"),
                  fontsize=11.5, pad=10)
    ax1.grid(alpha=0.25, which="both", ls="--")
    ax1.legend(loc="upper right", fontsize=7.0, framealpha=0.94)

    # 右：FC12 选频带 vs B
    B = np.linspace(0.5, 20, 400)
    fci = np.array([f_ci(b, M_DT) for b in B])
    ax2.set_facecolor(BG)
    ax2.fill_between(B, fci, 4557.22 * fci, color="#b8d4e3", alpha=0.30,
                     label=figtext("FC11 RMF 窗口 [f_ci, f_ce]（D-T，比值 4557）"))
    ax2.fill_between(B, 2 * fci, 5 * fci, color="#f5b041", alpha=0.55,
                     label=figtext("FC12 最优选频带 k·f_ci，k∈[2,5]"))
    ax2.axhline(LIGHT_LIMIT, color="#8e44ad", ls=":", lw=2.0,
                label=figtext(f"装置光速响应上限 c/L = {LIGHT_LIMIT/1e6:.0f} MHz（L=0.5m）"))
    ax2.axvline(B_MAX_BAND, color="#c0392b", ls="--", lw=1.8,
                label=figtext(f"带内不越 c/L 的场强上限 B < {B_MAX_BAND:.1f}T"))
    ax2.plot([9.0], [F_CI_9T], "o", color="#2e86de", ms=7, zorder=6)
    ax2.annotate(figtext(f"B=9T：f_ci={F_CI_9T/1e6:.1f}MHz\n选频带 {BAND[0]/1e6:.0f}–{BAND[1]/1e6:.0f}MHz"),
                 xy=(9.0, F_CI_9T), xytext=(3.2, 2.2 * F_CI_9T), fontsize=8,
                 color="#333333", bbox=dict(boxstyle="round,pad=0.25", fc="white",
                                            ec="#2e86de", alpha=0.94),
                 arrowprops=dict(arrowstyle="->", color="#2e86de", lw=0.9))
    ax2.set_xscale("log")
    ax2.set_yscale("log")
    ax2.set_xlim(0.5, 20)
    ax2.set_ylim(1e7, 1e11)
    ax2.set_xlabel(figtext("磁场 B（T，对数）"), fontsize=10.5)
    ax2.set_ylabel(figtext("频率（Hz，对数）"), fontsize=10.5)
    ax2.set_title(figtext("FC12 人工场选频：ω = k·ω_ci（k∈[2,5]）与其光速响应上界"),
                  fontsize=11.5, pad=10)
    ax2.grid(alpha=0.25, which="both", ls="--")
    ax2.legend(loc="upper left", fontsize=7.4, framealpha=0.94)

    fig.legend(handles=ax_handles, loc="upper center", bbox_to_anchor=(0.5, 0.075),
               ncol=2, fontsize=7.0, framealpha=0.95, facecolor=BG,
               title=figtext("装置锚点（逐条带出处，见 artifacts/device/report.json）"),
               title_fontsize=7.6)
    fig.subplots_adjust(left=0.06, right=0.985, top=0.90, bottom=0.245, wspace=0.20)
    p = os.path.join(OUT, "fig_device_anchors.png")
    fig.savefig(p, dpi=140, facecolor=BG)
    plt.close(fig)
    return p


# ---------------------------------------------------------------------------
def main():
    fig = fig_device_anchors()

    chk("DV15 图纸文字保持干净（无 缺口/未给出/第二输入 字样）",
        not any(w in lbl for lbl in FIG_LABELS for w in ("缺口", "未给出", "第二输入")),
        f"{len(FIG_LABELS)} 条图注")

    anchors = [
        {"轴": "装置", "量": "稳态环半径上限（冷加工铜 σ_y=250MPa, t=0.5m, B=12.2T）",
         "值": R_MAX_12_2, "单位": "m", "原文": "R_max(B=12.2T) = 2.1m",
         "出处": "PF7（σ ≤ σ_y ⟺ R ≤ 2μ₀σ_yt/B²）+ theory-plasma-fusion.md §F5",
         "来源文件": ["docs/wiki/theory-plasma-fusion.md",
                      "artifacts/plasmafusion/report.json"]},
        {"轴": "装置", "量": "紧凑装置机械门上限 B_cap（FC8 反解，σ_y=2GPa, t=1.35cm, r_s=10cm）",
         "值": B_CAP_10CM, "单位": "T", "原文": "B_cap = √(2μ₀σ_yt/r_s)（σ_y=2GPa, t=1.35cm）",
         "出处": "FC8（B² ≤ 2μ₀σ_y t/R_c ⟺ PF7）+ scripts/verify_frc_compact.py B_cap()",
         "来源文件": ["ProjectionPhysics/FrcCompact.lean",
                      "artifacts/frccompact/report.json",
                      "scripts/verify_frc_compact.py"]},
        {"轴": "装置", "量": "wiki 独立口径机械门（R=10cm, t=1cm, σ_y=1GPa）",
         "值": B_CAP_10CM_WIKI, "单位": "T", "原文": "B_cap ≈ 15.8T",
         "出处": "theory-frc-compact.md §机械门（FC8）",
         "来源文件": ["docs/wiki/theory-frc-compact.md"]},
        {"轴": "装置", "量": "RMF 离子回旋频率（B=9T, D-T, μ=0）",
         "值": F_CI_9T / 1e6, "单位": "MHz",
         "原文": "{\"mu\": 0.0, \"f_ci_MHz\": 55.28202317494117",
         "出处": "FC9 ω_ci ∝ 1/m_eff + FrcCompact.lean ionCyclotron",
         "来源文件": ["artifacts/frccompact/report.json", "ProjectionPhysics/FrcCompact.lean"]},
        {"轴": "装置", "量": "FC12 选频带下沿 2·f_ci（B=9T）",
         "值": BAND[0] / 1e6, "单位": "MHz", "原文": "RMF 驱动频率 ω=k·ω_ci, k∈[2,5] 最优",
         "出处": "FC12 rmf_selection_band_nonempty + rmf_selection_above_ci",
         "来源文件": ["ProjectionPhysics/FrcCompact.lean"]},
        {"轴": "装置", "量": "FC12 选频带上沿 5·f_ci（B=9T）",
         "值": BAND[1] / 1e6, "单位": "MHz", "原文": "最优≈138-276MHz（VHF）",
         "出处": "FC12（FrcCompact.lean 定理注释的数值层）",
         "来源文件": ["ProjectionPhysics/FrcCompact.lean"]},
        {"轴": "装置", "量": "装置光速响应上限 c/L（L=0.5m，脚本既有取值）",
         "值": LIGHT_LIMIT / 1e6, "单位": "MHz", "原文": "L = 0.5",
         "出处": "FC12 lightLimit（ω_max = c/L，MS3 空间场波速 = c）",
         "来源文件": ["scripts/plot_artificial_field.py",
                      "ProjectionPhysics/FrcCompact.lean"]},
        {"轴": "装置", "量": "带内低于 c/L 的场强上限（k=5, L=0.5m，FC12 反解）",
         "值": B_MAX_BAND, "单位": "T",
         "原文": "rmf_selection_band_nonempty（2×ω_ci < 5×ω_ci）",
         "出处": "FC12 上界条件 k·f_ci < c/L 对 B 反解（代数代入，非新设计值）",
         "来源文件": ["ProjectionPhysics/FrcCompact.lean"]},
    ]
    for a in anchors:
        a["来源文件 hash（16 位）"] = {f: sha16(os.path.join(REPO, f))
                                       for f in a["来源文件"]}

    report = {
        "title": "硬件轴①装置——可锚定量（第一性原理核算的可机读形式）",
        "date": "2026-09-27",
        "对应 wiki": ["docs/wiki/theory-antigravity-confinement.md",
                       "docs/wiki/theory-frc-compact.md",
                       "docs/wiki/theory-plasma-fusion.md",
                       "docs/wiki/fusion-program-roadmap.md"],
        "纪律": [
            "不发明设计参数：每条量或由已证定理重算并与既有产物逐位一致，"
            "或为仓库某页已写下的锚点值（原文搬运校验）。",
            "反引力约束环自身的几何尺寸在任何页里都没有 ⟹ 只列 [缺口]。",
            "金额不入库：只用 人·月 / 工期 / 人 / 比例。",
        ],
        "D1_关键件": [
            {"层": a, "名称": n, "内容": s, "仓库对应": r} for a, n, s, r in KEY_PARTS],
        "D2_FRC_技术取舍": [{"FRC 现实技术": k, "本设计处理": v} for k, v in FRC_KEEP],
        "D3_可锚定量": anchors,
        "D4_工期锚点（装置线）": [
            {"里程碑": m[0], "季度": m[1], "月区间": m[2], "人·月": m[3], "门": m[4],
             "出处": f"docs/wiki/fusion-program-roadmap.md §2.5（Q{m[1][1]} 装置线交付）"
                     + (f" + scripts/verify_fusion_roadmap.py QUARTERS" if m[5] == "script" else "")}
            for m in MILESTONES],
        "D4_装置线人·月合计": LANE_PM_DEVICE,
        "D5_缺口清单": ANTIGRAVITY_GEOM_GAP + [
            "关键件逐件交期/工期（何件先到、何件外协）——仓库只给了季度里程碑与人·月",
            "前 18 个月设备清单逐项（roadmap 只写了『已按第一性原理逐项核算』，条目未入库）",
        ],
        "图": os.path.basename(fig),
        "checks": CHECKS,
    }
    with open(os.path.join(OUT, "report.json"), "w", encoding="utf-8") as fh:
        json.dump(report, fh, ensure_ascii=False, indent=2)

    lines = [
        "硬件轴①装置——可锚定量（2026-09-27）",
        "=" * 62,
        f"环几何：R_max(12.2T, 冷加工铜, t=0.5m) = {R_MAX_12_2:.3f} m（PF7）",
        f"        紧凑装置 r_s=10cm：B_cap = {B_CAP_10CM:.2f} T（FC8，σ_y=2GPa t=1.35cm）"
        f" / {B_CAP_10CM_WIKI:.2f} T（wiki 口径 t=1cm σ_y=1GPa）",
        "        现实基准：SPARC R=1.85m B=12.2T；CFR2 末级燃烧室 12cm（7–9T → 35T 脉冲）",
        f"FC12 选频：f_ci(9T) = {F_CI_9T/1e6:.2f} MHz；带 [2,5]·f_ci = "
        f"{BAND[0]/1e6:.1f}–{BAND[1]/1e6:.1f} MHz；c/L(L=0.5m) = {LIGHT_LIMIT/1e6:.1f} MHz",
        f"        带内不越 c/L 的场强上限 B < {B_MAX_BAND:.2f} T（k=5）",
        f"关键件：三层架构（D-T 燃料区 / 双流环 Cu:H=106:1 / RMF 时变场源）+ "
        f"FRC 五条技术取舍（保留 θ-pinch 与 RMF，砍掉 10 级分段压缩）",
        f"工期：装置线 18 个月 = {LANE_PM_DEVICE} 人·月；首件 = 桌面判据台（M6，G1 生死门）",
        f"缺口 {len(ANTIGRAVITY_GEOM_GAP) + 2} 条（自身几何/关键件交期/设备清单逐项）——见 report.json",
        f"图：{os.path.basename(fig)}",
        f"检查：{sum(1 for c in CHECKS if c['通过'])}/{len(CHECKS)} 通过",
    ]
    with open(os.path.join(OUT, "summary.txt"), "w", encoding="utf-8") as fh:
        fh.write("\n".join(lines) + "\n")

    print("\n".join(lines))
    failed = [c for c in CHECKS if not c["通过"]]
    print("\n产物：", OUT)
    if failed:
        raise SystemExit(f"装置轴检查失败 {len(failed)} 条：{[c['检查'] for c in failed]}")


if __name__ == "__main__":
    main()
