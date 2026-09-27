#!/usr/bin/env python3
"""硬件第三轴·建造-可造性——工序 / 关键路径 / 首件 / 自有 vs 外协

对应 docs/wiki/fusion-program-roadmap.md（§2 八道门 + §2.5 前 18 个月逐季度落位 +
§4 找人找团队）与 docs/wiki/theory-antigravity-confinement.md（关键件三层架构）。

【本脚本的纪律】
  (a) 工序、门、人·月、自有/外协全部取自页面已写下的表与段落——只做原文搬运校验，
      关键路径是**派生量**（口径写死在 report.json 里：门链上有实物产出的工序），
      不是页面原话，脚本显式标注「派生」；
  (b) 设备清单逐项（哪件自制/哪件外购、单件工期与交期）在任何页里都没有 ⟹ [缺口]；
  (c) 金额不入库：本脚本对产物做**货币字样扫描**（¥/$/万元/元），扫到即报红。

产物：artifacts/buildability/report.json + summary.txt + fig_buildability_gantt.png
"""
import hashlib
import json
import os
import re

import numpy as np

REPO = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
OUT = os.path.join(REPO, "artifacts", "buildability")
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


WIKI_RM = read_wiki("fusion-program-roadmap.md")
WIKI_CONF = read_wiki("theory-antigravity-confinement.md")
ROAD = load_report("artifacts/fusionroadmap/report.json")
R6 = ROAD["R6_first_18_months_quarterly"]
LANE_PM = R6["工作流逐季度人·月"]

CHECKS = []


def chk(name, cond, detail=""):
    CHECKS.append({"检查": name, "通过": bool(cond), "细节": str(detail)})
    print(("PASS " if cond else "FAIL ") + name + (f"  [{detail}]" if detail else ""))
    return bool(cond)


def relerr(a, b):
    return abs(a - b) / max(abs(b), 1e-300)


# ---------------------------------------------------------------------------
# B1 工序链（页面原文：装置线「规格书/询价 → 桌面台建造 → 中型台 → 复现装置 #2」）
# ---------------------------------------------------------------------------
CHAIN_WIKI = "规格书/询价 → 桌面台建造 → 中型台 → 复现装置 #2"
chk("BD1 装置线工序链原文在库（roadmap §2.5 工作流分解表）",
    CHAIN_WIKI in WIKI_RM, CHAIN_WIKI)
chk("BD2 装置线人·月原文在库（30.5 / 32.8%）",
    "| 装置线 | 30.5 | 32.8% |" in WIKI_RM, "装置线 30.5 人·月")

# (工序, 季度, 月区间, 人·月, 门, 关键路径, 自有/外协, 页面原文片段)
STEPS = [
    ("① 规格书 + 询价单（只设计不采购）", "Q1", "M1–3", 1.0, "G0（M3）", True,
     "自有（自建）", "桌面判据台规格书与询价单（只问不买）"),
    ("② 首件：桌面判据台建成", "Q2", "M4–6", 2.5, "G1（M6）生死门", True,
     "自有（自建）", "桌面判据台建成"),
    ("③ 诊断升级（探针阵列 + 光谱）——并行支撑", "Q3", "M7–9", 3.0, "—", False,
     "自有（自建）", "诊断升级（探针阵列+光谱）"),
    ("④ 中型测试台建成", "Q4", "M10–12", 7.5, "G2（M12）", True,
     "自有（自建）", "中型测试台建成"),
    ("⑤ 复现装置 #2 建成（独立场地/独立团队）", "Q5", "M13–15", 9.0, "—", True,
     "自有场地 + 外部介入", "复现装置 #2（独立场地、独立团队）"),
    ("⑥ 两装置重复性统计 + FRC 级装置参数表", "Q6", "M16–18", 7.5, "G3（M18）", True,
     "自有 + 第三方分析", "公共数据集 + FRC 级装置参数表"),
]
chk("BD3 六道工序的月区间与人·月：Σ = 30.5，且与 fusionroadmap 产物一致",
    abs(sum(s[3] for s in STEPS) - 30.5) < 1e-9
    and relerr(R6["工作流人·月分解"]["装置线"], 30.5) < 1e-12
    and sum(s[3] for s in STEPS) == sum(LANE_PM[q]["装置线"]
                                       for q in ("Q1", "Q2", "Q3", "Q4", "Q5", "Q6")),
    f"{sum(s[3] for s in STEPS)} 人·月")
chk("BD4 六道工序原文在库（roadmap §2.5 / verify_fusion_roadmap QUARTERS）",
    all(s[7] in WIKI_RM or s[7] in open(os.path.join(REPO, "scripts",
                                                     "verify_fusion_roadmap.py"),
                                        encoding="utf-8").read() for s in STEPS),
    "6/6")

# ---------------------------------------------------------------------------
# B2 关键路径（派生量，口径显式）
# ---------------------------------------------------------------------------
CRITICAL = [s for s in STEPS if s[5]]
CRITICAL_INDEX = [i for i, s in enumerate(STEPS) if s[5]]
chk("BD5 关键路径口径可核验：= 装置线工序中除『诊断升级（并行支撑）』外的五道，"
    "且每道都对应判决门的实物产出/前置（G0 规格书 / G1 首件 / G2 中型台 / "
    "G3 的实物前置 = 复现装置 #2 与参数表）",
    CRITICAL_INDEX == [0, 1, 3, 4, 5] and len(CRITICAL) == 5
    and STEPS[2][5] is False,
    " / ".join(f"{s[1]}{s[2]}→{s[4]}" for s in CRITICAL))
chk("BD6 关键路径上首件排在最前（M4–6），之后才是中型台（M10–12）与装置 #2（M13–15）",
    [s[2] for s in CRITICAL] == ["M1–3", "M4–6", "M10–12", "M13–15", "M16–18"],
    "→".join(s[1] for s in CRITICAL))
chk("BD7 关键路径首尾贯通判决期（M1 起、M18 止）⟹ 长度 18 个月",
    CRITICAL[0][2].startswith("M1") and CRITICAL[-1][2].endswith("18")
    and sum(s[3] for s in CRITICAL) < 30.5,
    f"M1–M18，{sum(s[3] for s in CRITICAL)} 人·月")

# ---------------------------------------------------------------------------
# B3 首件（桌面判据台）
# ---------------------------------------------------------------------------
chk("BD8 首件判据原文在库（R_ci 实测 > 3σ 且零假设预测 < 分辨率）",
    "R_ci 实测 > 3σ 且零假设预测 < 分辨率" in WIKI_RM, "G1 通过条件")
chk("BD9 首件失败处置原文在库（R_ci=0 ⟹ 停装置线）",
    "R_ci=0 ⟹ 停装置线" in WIKI_RM, "G1 预写失败处置")
chk("BD10 首件过之前不放大型装置：Q1 只设计不采购 + G1 过才加人",
    "只设计不采购" in WIKI_RM and "G1 判决通过才加" in WIKI_RM,
    "roadmap §2.5 Q1 主题 + §4 招人触发条件")

# ---------------------------------------------------------------------------
# B4 自有 vs 外协
# ---------------------------------------------------------------------------
chk("BD11 外部化原文在库（G3 起找 1–2 个外部实验室做独立复现）",
    "G3（M18）起找 1–2 个外部实验室做独立复现" in WIKI_RM, "roadmap §4 外部化")
chk("BD12 整机不全部自造原文在库（G7：系统集成 + 外部合作，不自己造全部部件）",
    "不自己造全部部件" in WIKI_RM, "roadmap §4 团队表 G7 行")
chk("BD13 询价即外购路径原文在库（规格书 → 询价单 → 建造；Q1 只问不买）",
    "询价单" in WIKI_RM and "只问不买" in WIKI_RM, "roadmap §2.5")
chk("BD14 关键件三层架构原文在库（D-T 燃料区 / 双流环 / RMF 时变场源）",
    all(k in WIKI_CONF for k in ("聚变燃料区", "双流环", "RMF 时变场源")), "3/3")

# 自有/外协的**逐件**归属 = [缺口]（页面没有设备清单）
GAPS = [
    "设备清单逐项（条目、单件工期、交期）——roadmap §8 只写『已按第一性原理逐项核算』，"
    "条目未入库；Q1 交付物『询价单』就是用来把这些估列值替换成报价的",
    "自有 vs 外协的逐件归属（哪件自制、哪件外购、哪件找外部实验室）——"
    "页面只有层级归属（G3 外部复现、G7 不自己造全部部件），没有工件级清单",
    "关键件的制造前置周期（长周期采购件/真空腔/磁体线圈的 lead time）",
    "十级分段压缩线圈被砍掉后，剩余外购件清单的变化量（装置设计页只说『砍掉』，未列替代清单）",
]

# ---------------------------------------------------------------------------
# B5 金额不入库（扫描产物 + 新 wiki 页）
# ---------------------------------------------------------------------------
CURRENCY_RE = re.compile(r"[¥$€£]|\d+\s*(万元|亿元|万元人民币|USD|美元|人民币|元整)")


def scan_currency(paths):
    hits = []
    for p in paths:
        if not os.path.exists(p):
            continue
        txt = open(p, encoding="utf-8").read()
        for m in CURRENCY_RE.finditer(txt):
            hits.append(f"{os.path.relpath(p, REPO)}: {m.group(0)}")
    return hits


FIG_LABELS_AT_END = None

# ---------------------------------------------------------------------------
# 图：工序甘特（关键路径高亮 + 首件 + 门 + 自有/外协）+ 四工作流人·月
# ---------------------------------------------------------------------------
BG = "#faf8f5"


def fig_gantt():
    fig, (ax, ax2) = plt.subplots(2, 1, figsize=(13.0, 8.2),
                                  gridspec_kw={"height_ratios": [2.0, 1.0],
                                               "hspace": 0.32})
    fig.patch.set_facecolor(BG)
    ax.set_facecolor(BG)
    ax2.set_facecolor(BG)

    span = {"M1–3": (1, 3), "M4–6": (4, 6), "M7–9": (7, 9), "M10–12": (10, 12),
            "M13–15": (13, 15), "M16–18": (16, 18)}
    for i, (name, q, months, pm, gate, critical, own, _src) in enumerate(STEPS):
        y = len(STEPS) - 1 - i
        x0, x1 = span[months]
        color = "#2e86de" if critical else "#95a5a6"
        hatch = "" if own.startswith("自有") and "外部" not in own else "//"
        ax.broken_barh([(x0, x1 - x0 + 1)], (y + 0.18, 0.64), facecolors=color,
                       alpha=0.85 if critical else 0.55, edgecolor="white",
                       hatch=hatch)
        ax.text((x0 + x1 + 1) / 2, y + 0.5, figtext(f"{pm} 人·月"), ha="center",
                va="center", fontsize=8.4, color="white", fontweight="bold")
        ax.text(0.35, y + 0.5, figtext(name), ha="right", va="center", fontsize=8.6)
        ax.text(18.9, y + 0.5, figtext(f"{months}｜{gate}｜{own}"), ha="left",
                va="center", fontsize=7.6, color="#555555")
    # 首件/外协标记统一放到图底注（避免与条形内的人·月文字相撞）
    # 门标记
    for m, g in ((3, "G0"), (6, "G1 生死门"), (12, "G2"), (18, "G3")):
        ax.axvline(m, color="#c0392b", ls="--", lw=1.1, alpha=0.7)
        ax.text(m, len(STEPS) + 0.35, figtext(g), ha="center", fontsize=8.2,
                color="#c0392b")
    # 外协/外部介入标记统一放到图底注
    ax.set_xlim(0, 27)
    ax.set_ylim(-0.15, len(STEPS) + 0.95)
    ax.set_yticks([])
    ax.set_xticks(range(1, 19, 3))
    ax.set_xticklabels([f"M{i}" for i in range(1, 19, 3)], fontsize=8.4)
    ax.set_title(figtext("建造工序 / 关键路径 / 首件（实心=关键路径，斜纹=含外部介入；"
                         "人·月为排程假设）"), fontsize=12, pad=14)
    for s in ax.spines.values():
        s.set_visible(False)

    # 下：四工作流逐季度人·月（来自 fusionroadmap 产物）
    lanes = ["诊断线", "装置线", "理论数值线", "对外线"]
    colors = {"诊断线": "#2e86de", "装置线": "#e67e22", "理论数值线": "#8e44ad",
              "对外线": "#27ae60"}
    quarters = ["Q1", "Q2", "Q3", "Q4", "Q5", "Q6"]
    bottom = np.zeros(6)
    for lane in lanes:
        vals = np.array([LANE_PM[q][lane] for q in quarters])
        ax2.bar(range(6), vals, 0.56, bottom=bottom, color=colors[lane],
                alpha=0.88, edgecolor="white", label=figtext(
                    f"{lane}（18 月合计 {sum(vals):g} 人·月）"))
        bottom += vals
    for i, tot in enumerate(bottom):
        ax2.text(i, tot + 0.7, figtext(f"{tot:g}"), ha="center", fontsize=8.6)
    ax2.set_xticks(range(6))
    ax2.set_xticklabels([figtext(f"{q}\n{R6['季度表'][i]['月区间']}") for i, q in
                         enumerate(quarters)], fontsize=8.6)
    ax2.set_ylabel(figtext("季度人·月（人·月 = 人 × 3 月）"), fontsize=10)
    ax2.set_ylim(0, 30)
    ax2.grid(alpha=0.25, axis="y")
    ax2.legend(fontsize=7.8, ncol=4, loc="upper left", framealpha=0.95)
    ax2.set_title(figtext("四工作流逐季度人·月分解（前 18 个月 93 人·月；装置线 30.5）"),
                  fontsize=11.5, pad=10)

    fig.subplots_adjust(left=0.245, right=0.905, top=0.925, bottom=0.135)
    fig.text(0.245, 0.055, figtext("★ 首件 = 桌面判据台（M6 建成，G1 生死门，判据 "
                                   "R_ci > 3σ；失败 → 停装置线）"), fontsize=8.4,
             color="#c0392b")
    fig.text(0.245, 0.022, figtext("外部介入：G3 起 1–2 个外部实验室独立复现（M18 起）"
                                   "｜实心 = 关键路径，斜纹 = 含外部介入"),
             fontsize=8.4, color="#555555")
    p = os.path.join(OUT, "fig_buildability_gantt.png")
    fig.savefig(p, dpi=140, facecolor=BG)
    plt.close(fig)
    return p


def main():
    fig = fig_gantt()

    chk("BD15 图纸文字保持干净（无 缺口/未给出/第二输入 字样）",
        not any(w in lbl for lbl in FIG_LABELS for w in ("缺口", "未给出", "第二输入")),
        f"{len(FIG_LABELS)} 条图注")

    report = {
        "title": "硬件轴③建造-可造性——工序 / 关键路径 / 首件 / 自有 vs 外协",
        "date": "2026-09-27",
        "对应 wiki": ["docs/wiki/fusion-program-roadmap.md",
                       "docs/wiki/theory-antigravity-confinement.md"],
        "纪律": [
            "工序/门/人·月/自有-外协归属取自页面已写下的表与段落（原文搬运校验）。",
            "关键路径是派生量：口径 = 门链（G0/G1/G2/G3）上有实物产出的工序，"
            "本报告显式标注「派生」，不冒充页面原话。",
            "设备清单逐项与工件级自制/外购归属在任何页里都没有 ⟹ 只列 [缺口]。",
            "金额不入库：产物做货币字样扫描（扫到即报红），只用 人·月 / 工期 / 人 / 比例。",
        ],
        "B1_工序链（页面原文）": CHAIN_WIKI,
        "B2_工序表": [
            {"工序": s[0], "季度": s[1], "月区间": s[2], "人·月": s[3], "门": s[4],
             "关键路径": s[5], "自有 vs 外协": s[6],
             "出处": f"docs/wiki/fusion-program-roadmap.md §2.5（{s[1]} 装置线/诊断线交付）"}
            for s in STEPS],
        "B3_关键路径（派生）": {
            "口径": "装置线工序中除『诊断升级（并行支撑）』外的五道——每道都对应判决门的"
                    "实物产出/前置：G0 规格书 / G1 首件桌面判据台 / G2 中型测试台 / "
                    "G3 的实物前置（复现装置 #2 + 参数表）",
            "序列": " → ".join(f"{s[1]}({s[2]})" for s in CRITICAL),
            "长度 [月]": 18,
            "关键路径人·月": sum(s[3] for s in CRITICAL),
            "装置线合计人·月": 30.5,
        },
        "B4_首件": {
            "首件": "桌面判据台（Q2 末 M6 建成；腔体/离子源/RF/探针）",
            "首件判据": "R_ci 实测 > 3σ 且零假设预测 < 分辨率（G1 生死门）",
            "首件失败处置（预写）": "R_ci=0 ⟹ 停装置线，写负结果论文",
            "首件之前的纪律": "Q1 只设计不采购（只问不买）；G1 判决通过才加人（加人闸门）",
        },
        "B5_自有 vs 外协": {
            "自有（自建/自担）": [
                "桌面判据台（首件）与中型测试台的建造（装置线 Q2–Q4）",
                "诊断升级：磁探针阵列 + 光谱（诊断线 Q3）",
                "复现装置 #2 的场地与运行（Q5，独立场地/独立团队——自有体系内）",
                "判据规范、预注册协议、理论/数值线（1 FTE × 18 月 = 18 人·月）",
            ],
            "外部（外协/外部复现）": [
                "G3（M18）起 1–2 个外部实验室做独立复现（把『leo 的装置』变成可复现现象）",
                "G7（M60）系统集成 + 外部合作，不自己造全部部件",
                "Q5 对外线：外部实验室合作协议 + 数据共享条款",
                "Q1 询价单：外购件先询价（只问不买）",
            ],
            "工件级归属": "[缺口] —— 页面没有设备清单，无法给出逐件自制/外购（见缺口清单）",
        },
        "B6_人·月与工期": {
            "装置线 18 个月": 30.5,
            "四条工作流 18 个月": R6["工作流人·月分解"],
            "逐季度人·月": LANE_PM,
            "60 个月逐工作流分解": "[缺口] —— 仓库只分解了前 18 个月（Q1–Q6）",
        },
        "B7_缺口清单": GAPS,
        "图": os.path.basename(fig),
        "来源文件 hash（16 位）": {
            f: sha16(os.path.join(REPO, f)) for f in
            ["docs/wiki/fusion-program-roadmap.md",
             "docs/wiki/theory-antigravity-confinement.md",
             "artifacts/fusionroadmap/report.json"]},
        "checks": CHECKS,
    }
    rp = os.path.join(OUT, "report.json")
    with open(rp, "w", encoding="utf-8") as fh:
        json.dump(report, fh, ensure_ascii=False, indent=2)

    lines = [
        "硬件轴③建造-可造性（2026-09-27）",
        "=" * 62,
        f"工序链（页面原文）：{CHAIN_WIKI}",
        "工序表（月区间｜人·月｜门｜关键路径｜自有-外协）：",
    ]
    for s in STEPS:
        lines.append(f"  {s[0]}｜{s[2]}｜{s[3]} 人·月｜{s[4]}｜"
                     f"{'关键路径' if s[5] else '并行支撑'}｜{s[6]}")
    lines += [
        f"关键路径（派生口径）：{' → '.join(s[1] for s in CRITICAL)}，18 个月，"
        f"{sum(s[3] for s in CRITICAL)} 人·月（装置线合计 30.5 人·月）",
        "首件 = 桌面判据台（M6，G1 生死门）；判据 R_ci > 3σ；失败 ⟹ 停装置线",
        "自有：判据台/中型台/诊断升级/复现装置 #2/理论数值线；"
        "外部：G3 起外部实验室独立复现、G7 不自己造全部部件",
        f"缺口 {len(GAPS)} 条（设备清单逐项/工件级自制-外购/长周期 lead time/砍掉压缩线圈后的替代清单）",
        f"图：{os.path.basename(fig)}",
    ]
    sp = os.path.join(OUT, "summary.txt")
    with open(sp, "w", encoding="utf-8") as fh:
        fh.write("\n".join(lines) + "\n")

    # 金额不入库（扫本轴产物 + 新 wiki 页）
    hits = scan_currency([rp, sp, os.path.join(REPO, "docs", "wiki", "hardware-axes.md")])
    chk("BD16 金额不入库（产物 + hardware-axes.md 无 ¥/$/万元/元 字样）",
        not hits, "；".join(hits) or "无货币字样")

    print("\n".join(lines))
    failed = [c for c in CHECKS if not c["通过"]]
    print("\n产物：", OUT)
    if failed:
        raise SystemExit(f"建造轴检查失败 {len(failed)} 条：{[c['检查'] for c in failed]}")


if __name__ == "__main__":
    main()
