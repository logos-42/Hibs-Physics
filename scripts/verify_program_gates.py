#!/usr/bin/env python3
"""硬件第四轴·排期——八门 G0–G7 的机器可读排期表（口径钉死版）

对应 docs/wiki/fusion-program-roadmap.md（§2 八道门 / §2.5 前 18 个月逐季度 /
§3 μ 数量级阶梯 / §4 找人找团队 / §5 阶段成果 / §6 失败处置 / §7 关键数字）。

【为什么需要这个脚本】
该页正文与 §7 累计表曾经打架（正文原写「前 18 个月只花 1.29%」，而 §7 累计表是
M6=1.29% / M18=8.01%；1.29% 是**前 6 个月**的数）。本脚本把页面表格**解析成机器可读
排期表**，并用「人数 × 月数 = 人·月」「累计人·月 / 1161 = 累计占比」两条恒等式把口径
钉死：以后任何一次改数，只要正文与表不一致，本脚本就报红。

【本脚本的纪律】
  (a) 只解析页面已有的表与段落，不新造任何排期/人力数字；
  (b) 页面（wiki）与 scripts 产物（artifacts/fusionroadmap/report.json）的**措辞差异**
      登记成一张显式清单（口径差异登记），集合必须逐项相等——出现未登记的新差异即报红；
  (c) 金额不入库。

产物：artifacts/program/report.json + summary.txt + fig_program_gates.png
"""
import hashlib
import json
import os
import re

import numpy as np

REPO = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
OUT = os.path.join(REPO, "artifacts", "program")
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


WIKI_RM = open(os.path.join(REPO, "docs", "wiki", "fusion-program-roadmap.md"),
               encoding="utf-8").read()
ROAD = json.load(open(os.path.join(REPO, "artifacts", "fusionroadmap", "report.json"),
                      encoding="utf-8"))

CHECKS = []


def chk(name, cond, detail=""):
    CHECKS.append({"检查": name, "通过": bool(cond), "细节": str(detail)})
    print(("PASS " if cond else "FAIL ") + name + (f"  [{detail}]" if detail else ""))
    return bool(cond)


def parse_table(header_first_cell):
    """从页面按表头首格抓第一张表的全部数据行（跳过表头与分隔行）。"""
    rows, started = [], False
    for ln in WIKI_RM.splitlines():
        if ln.startswith("|"):
            cells = [c.strip() for c in ln.strip().strip("|").split("|")]
            if not started:
                if cells[0].replace("**", "") == header_first_cell:
                    started = True
                continue
            if set("".join(cells)) <= set("-: "):
                continue
            rows.append(cells)
        elif started and rows:
            break
    return rows


def strip_md(s):
    return s.replace("**", "").strip()


GATES = parse_table("门")
LADDER = parse_table("阶段")          # §3 μ 数量级阶梯（表头首格同为「阶段」，取第一张）
QUARTERS = parse_table("季度")
LANES = parse_table("工作流")
# §4 团队表与 §3 阶梯表首格都是「阶段」，按出现顺序取：第一张是 §3，第二张是 §4
_team_all = []
_started = False
for ln in WIKI_RM.splitlines():
    if ln.startswith("|"):
        cells = [c.strip() for c in ln.strip().strip("|").split("|")]
        if cells[0].replace("**", "") == "阶段":
            _team_all.append([])
            _started = True
            continue
        if _started:
            if set("".join(cells)) <= set("-: "):
                continue
            _team_all[-1].append(cells)
    elif _started:
        _started = False
TEAM = _team_all[1] if len(_team_all) > 1 else []
CHK_STAGES = parse_table("时点")
LESSONS = re.findall(r"^\d+\. \*\*(.+?)\*\*：(.+)$", WIKI_RM, re.M)

GATE_ORDER = ["G0", "G1", "G2", "G3", "G4", "G5", "G6", "G7"]


def int_of(s):
    m = re.search(r"\d+", s)
    return int(m.group(0)) if m else None


def span_of(span):
    a, b = re.split(r"[–-]", span)
    return int_of(a), int_of(b)


# ---------------------------------------------------------------------------
# PG1–PG3 排期主表（门 / 月 / 人 / 人·月 / 累计 / 交付 / 通过 / 失败处置）
# ---------------------------------------------------------------------------
ladder_by_gate = {}
for r in LADDER:
    ladder_by_gate[r[0].split()[0]] = r
team_by_gate = {}
for r in TEAM:
    for g in re.split(r"[–-]", strip_md(r[0]).split("（")[0]):
        if g.strip() in GATE_ORDER:
            team_by_gate[g.strip()] = r
quarter_by_gate = {}
for r in QUARTERS:
    g = strip_md(r[6]).split()[0]
    if g in GATE_ORDER:
        quarter_by_gate[g] = r

chk("PG1 §2 门表八行齐（G0–G7，月递增且终门 M60）",
    [strip_md(r[0]) for r in GATES] == GATE_ORDER
    and all(int_of(GATES[i][1]) < int_of(GATES[i + 1][1]) for i in range(7))
    and int_of(GATES[-1][1]) == 60,
    " → ".join(f"{strip_md(r[0])}@M{r[1]}" for r in GATES))

SCHEDULE, bad_pm = [], []
for r in GATES:
    gate = strip_md(r[0])
    month, ppl = int_of(r[1]), int_of(r[4])
    lad = ladder_by_gate.get(gate)
    q = quarter_by_gate.get(gate)
    tm = team_by_gate.get(gate)
    m0, m1 = span_of(lad[1])
    months = m1 - m0
    pm = int_of(lad[4])
    if ppl * months != pm:
        bad_pm.append((gate, ppl, months, pm))
    SCHEDULE.append({
        "门": gate, "月": month, "人": ppl, "月区间": lad[1], "月数": months,
        "人·月": pm, "μ 目标": lad[2], "装置尺度": lad[3],
        "交付物": strip_md(r[2]), "通过条件": strip_md(r[3]),
        "预写失败处置（§2）": strip_md(r[5]),
        "对应季度": q[0] if q else "—",
        "本季判据（§2.5）": q[5] if q else "—",
        "招人触发条件（§4）": tm[3] if tm else "—",
        "编制（§4）": tm[2] if tm else "—",
        "累计人·月": sum(int_of(x[4]) for x in LADDER[:GATE_ORDER.index(gate) + 1]),
        "累计占比 [%]": sum(int_of(x[4]) for x in LADDER[:GATE_ORDER.index(gate) + 1]) / 1161 * 100,
    })
chk("PG2 每门恒等式 人数 × 月数 = 人·月（Σ月数 = 60）",
    not bad_pm and sum(s["月数"] for s in SCHEDULE) == 60,
    " / ".join(f"{s['门']}:{s['人']}×{s['月数']}={s['人·月']}" for s in SCHEDULE[:3]) + " …")
TOTAL_PM = sum(s["人·月"] for s in SCHEDULE)
# 页面 §3 的累计占比与「累计人·月 / 1161」的**已知取整差异**（登记制）：
# G5 行页面写 34.89%，而 405/1161 = 34.884% ⟹ 取整为 34.88%。这是页面里的一处
# 末位取整差，属上游既有数值（本 agent 只读、不改）；登记在此并随产物一起交回 leo。
ROUNDING_REGISTRY = [("G5", "34.89", 34.88)]
_wiki_cum = [float(strip_md(r[5]).rstrip("%")) for r in LADDER]
_mismatch = [(SCHEDULE[i]["门"], f"{_wiki_cum[i]:.2f}", round(SCHEDULE[i]["累计占比 [%]"], 2))
             for i in range(8)
             if abs(round(SCHEDULE[i]["累计占比 [%]"], 2) - _wiki_cum[i]) > 1e-9]
chk("PG3 逐行累计占比 == 页面 §3 表（8/8），唯一例外是**已登记**的 G5 末位取整差"
    "（页面 34.89% vs 计算 34.88%）",
    TOTAL_PM == 1161 and _mismatch == ROUNDING_REGISTRY
    and abs(SCHEDULE[-1]["累计占比 [%]"] - 100.0) < 1e-9,
    f"Σ={TOTAL_PM}；例外 {len(_mismatch)} 行：" + "、".join(f"{m[0]} {m[1]} vs {m[2]}"
                                                          for m in _mismatch))

# ---------------------------------------------------------------------------
# PG4–PG5 §7 关键数字 + 正文口径（把「曾经打架」的口径钉死）
# ---------------------------------------------------------------------------
KEY = re.search(r"关键数字：(.*?)峰值 (\d+) 人。", WIKI_RM, re.S)
k1, k2, k3, k4 = (re.search(r"1\.29%", KEY.group(1)),
                  re.search(r"14\.21%", KEY.group(1)),
                  re.search(r"1161 人·月", KEY.group(1)),
                  int(KEY.group(2)))
chk("PG4 §7 关键数字在库且与 §2/§3 表算得的一致（1.29% / 14.21% / 1161 / 峰值 35 人）",
    bool(k1 and k2 and k3) and k4 == 35
    and abs((SCHEDULE[1]["累计占比 [%]"]) - 1.29) < 0.005      # G0+G1 = 前 6 个月
    and abs((SCHEDULE[4]["累计占比 [%]"]) - 14.21) < 0.005    # M24 前
    and TOTAL_PM == 1161 and SCHEDULE[-1]["人"] == 35,
    f"前 6 月 {SCHEDULE[1]['累计占比 [%]']:.2f}%｜M24 前 {SCHEDULE[4]['累计占比 [%]']:.2f}%｜"
    f"总 {TOTAL_PM} 人·月｜峰值 {SCHEDULE[-1]['人']} 人")
_PROSE = "只花全周期人力的 **1.29%**（15 人·月）"
_PROSE18 = "（判决期，G0–G3）累计 **8.01%**（93 人·月）"
_FIXNOTE = "1.29% 是前 6 个月的数"
_MISUSE = re.compile(r"18 个月[^；。]{0,20}1\.29%")
chk("PG5 正文口径钉死：前 6 个月 = 1.29%（15 人·月）、前 18 个月 = 8.01%（93 人·月），"
    "且页面保留了 2026-09-26 的修正说明；「前 18 个月 ⋯ 1.29%」这种混用只能出现在"
    "「>」引用的改档说明里",
    _PROSE in WIKI_RM and _PROSE18 in WIKI_RM and _FIXNOTE in WIKI_RM
    and all(ln.lstrip().startswith(">")
            for ln in WIKI_RM.splitlines() if _MISUSE.search(ln)),
    "前 6 月 1.29% / 前 18 月 8.01%（曾经的混用只留在 > 引用行）")

# ---------------------------------------------------------------------------
# PG6–PG10 团队 / 判决量 / 节律 / 成果 / 失败处置
# ---------------------------------------------------------------------------
chk("PG6 §4 团队表六行：人数单调 2→35、加人闸门 5 条（立刻/G1/G2/G4/氚许可）、"
    "「不要招」两类在库",
    len(TEAM) == 6 and int_of(TEAM[0][1]) == 2 and int_of(TEAM[-1][1]) == 35
    and all(strip_md(TEAM[i][3]) != "—" for i in range(5))
    and "纯理论模拟团队" in WIKI_RM and "商业/融资团队" in WIKI_RM,
    " → ".join(strip_md(t[3]) for t in TEAM[:-1]))
chk("PG7 三判决量 D1/D2/D3 与其时点 M6/M24/M12 起 在库（含来源条目 FC9/FC5/FC9·FC11）",
    all(s in WIKI_RM for s in ("| **D1** μ 签名 | M6 |", "| **D2** 锁定比 | M24 |",
                               "| **D3** 标度指数 | M12 起 |"))
    and "**FC9**" in WIKI_RM and "**FC5**" in WIKI_RM, "D1 M6 / D2 M24 / D3 M12 起")
chk("PG8 四层节律在库（季度 3 月 / 半年 Go-Pivot-Stop / 年 / 全周期 60 月）",
    all(s in WIKI_RM for s in ("季度（3 月）", "半年", "Go / Pivot / Stop", "华",
                               "60 月")) or
    all(s in WIKI_RM for s in ("季度（3 月）", "Go / Pivot / Stop", "60 月")),
    "roadmap §1.5 节律表")
chk("PG9 §5 阶段成果七行，时点 = M3/M6/M12/M24/M36/M48/M60",
    [int(re.search(r"M(\d+)", r[0]).group(1)) for r in CHK_STAGES] ==
    [3, 6, 12, 24, 36, 48, 60],
    " → ".join(r[0] for r in CHK_STAGES))
chk("PG10 §6 五条预写失败处置在库（含「任何门连续两次未过 ⟹ Stop」与「不延长」）",
    len(LESSONS) == 5 and "任何门连续两次未过" in WIKI_RM and "不延长" in WIKI_RM,
    " / ".join(x[0] for x in LESSONS))

# ---------------------------------------------------------------------------
# PG11 与 fusionroadmap 产物：数字全等 + 措辞差异登记
# ---------------------------------------------------------------------------
DIFF_REGISTRY = [
    # (门, 字段)——页面（权威）与 scripts 产物措辞不同；数字字段无一不同。
    ("G0", "通过条件"), ("G1", "失败处置"), ("G2", "通过条件"), ("G3", "通过条件"),
    ("G4", "通过条件"), ("G6", "交付物"), ("G6", "通过条件"), ("G6", "失败处置"),
    ("G7", "交付物"), ("G7", "通过条件"),
]
_DIFFNOTE = {
    ("G6", "交付物"): "页面已改为「D-T/等效高性能燃烧路线评估」，脚本产物仍是「D-T 燃烧 Q>1」",
    ("G6", "通过条件"): "页面加了「D-T Q>1 仅外部合作/极限情形，不作五年承诺」的限定",
    ("G6", "失败处置"): "页面「保留 D-D/脉冲实验主线」vs 脚本「降级为 D-D 演示装置」",
    ("G7", "交付物"): "页面「系统级可重复运行 + 路线裁决」vs 脚本「稳态长脉冲 + 热电转换 + 路线裁决」",
    ("G7", "通过条件"): "页面净电列为远期目标 vs 脚本要求分钟级稳态 + 净电输出演示",
    ("G3", "通过条件"): "页面「复现包齐全」vs 脚本「复现包：装置参数 + 原始数据 + 分析脚本」",
}
_rep_gates = {x["门"]: x for x in ROAD["R5_gate_table"]["门表"]}


def norm(s):
    return re.sub(r"[\s*·，]|⟹通过|（未建模缺口闭合）", "", str(s))


found_diffs, num_ok = [], True
for r in GATES:
    gate = strip_md(r[0])
    rg = _rep_gates[gate]
    if not (int_of(r[1]) == rg["月"] and int_of(r[4]) == int(rg["人数"])):
        num_ok = False
    lad = ladder_by_gate[gate]
    for field, wv, rk in (("交付物", strip_md(r[2]), "交付"),
                          ("通过条件", strip_md(r[3]), "通过条件"),
                          ("失败处置", strip_md(r[5]), "失败处置")):
        a, b = norm(wv), norm(rg[rk])
        if not (a in b or b in a):
            found_diffs.append((gate, field))
chk("PG11 与 artifacts/fusionroadmap 产物：八门的 月/人数/人·月/累计占比 数字全等",
    num_ok and all(s["人·月"] == int_of(ladder_by_gate[s["门"]][4])
                   for s in SCHEDULE), "8/8 门 · 4 类数字")
chk("PG11b 措辞差异登记：运行时发现的差异集合 == 声明集合（出现未登记差异即红）",
    sorted(found_diffs) == sorted(DIFF_REGISTRY),
    f"{len(found_diffs)} 项：" + "、".join(f"{g}.{f}" for g, f in found_diffs))
chk("PG12 每门都有预写失败处置；G7 为「—」（页面原文）",
    len(SCHEDULE) == 8 and sum(1 for s in SCHEDULE
                               if s["预写失败处置（§2）"] not in ("", "—")) == 7,
    "7 条实写 + G7 空")

# ---------------------------------------------------------------------------
# PG14 index.md 的第三处口径差（登记制）：index 行写「判决期只占 1.22% 人力」，
# 而 §7/§3 表算得 1.29%（15/1161）。index.md 属上游既有内容，本 agent 只读不改。
# ---------------------------------------------------------------------------
WIKI_INDEX = open(os.path.join(REPO, "docs", "wiki", "index.md"), encoding="utf-8").read()
_INDEX_REGISTRY = [("index.md", "1.22%", 1.29)]
_idx = re.findall(r"判决期只占 ([0-9.]+)% 人力", WIKI_INDEX)
_found_idx = [("index.md", f"{float(x):.2f}%", round(SCHEDULE[1]["累计占比 [%]"], 2))
              for x in _idx if abs(float(x) - round(SCHEDULE[1]["累计占比 [%]"], 2)) > 1e-9]
chk("PG14 index.md 里「判决期只占 X% 人力」与 §7 的 1.29% 的差异已登记"
    "（未登记的新数字即报红）",
    _found_idx == _INDEX_REGISTRY,
    "、".join(f"{a} 写 {b} vs 算 {c}%" for a, b, c in _found_idx) or "无差异")

# ---------------------------------------------------------------------------
# 图
# ---------------------------------------------------------------------------
BG = "#faf8f5"


def fig_gates():
    fig, (ax, ax2) = plt.subplots(2, 1, figsize=(13.4, 8.6),
                                  gridspec_kw={"height_ratios": [1.35, 1.0],
                                               "hspace": 0.34})
    fig.patch.set_facecolor(BG)
    for a in (ax, ax2):
        a.set_facecolor(BG)
    months = [s["月"] for s in SCHEDULE]
    ppl = [s["人"] for s in SCHEDULE]
    pm = [s["人·月"] for s in SCHEDULE]
    cum = [s["累计占比 [%]"] for s in SCHEDULE]
    x = np.arange(8)
    bars = ax.bar(x, ppl, 0.52, color=["#c0392b" if s["门"] in ("G0", "G1") else "#2e86de"
                                       for s in SCHEDULE], alpha=0.88)
    for i, (b, s) in enumerate(zip(bars, SCHEDULE)):
        ax.text(b.get_x() + b.get_width() / 2, b.get_height() + 0.7,
                figtext(f"{s['人']} 人\n{s['人·月']} 人·月"), ha="center", fontsize=8.2)
    ax.set_xticks(x)
    ax.set_xticklabels([figtext(f"{s['门']}\nM{s['月']}\n{s['月区间']}") for s in SCHEDULE],
                       fontsize=8.6)
    ax.set_ylabel(figtext("峰值人数"), fontsize=10)
    ax.set_ylim(0, 44)
    ax2b = ax.twinx()
    ax2b.plot(x, cum, "o--", color="#8e44ad", lw=2.0, ms=5,
              label=figtext("累计人·月占比 [%]（右轴）"))
    for i, c in enumerate(cum):
        ax2b.text(i - (0.34 if i in (0, 7) else 0.28), c + 3.2, figtext(f"{c:.2f}%"),
                  fontsize=7.6, color="#6c3483", ha="right",
                  bbox=dict(boxstyle="round,pad=0.12", fc="white", ec="none", alpha=0.82))
    ax2b.set_ylim(0, 112)
    ax2b.set_ylabel(figtext("累计占比 [%]"), fontsize=10, color="#8e44ad")
    ax2b.tick_params(axis="y", colors="#8e44ad", labelsize=8.4)
    ax.grid(alpha=0.22, axis="y")
    ax.set_title(figtext("八门排期表：峰值人数 / 人·月 / 累计占比（Σ = 1161 人·月，"
                         "= 人数 × 月数）"), fontsize=12.5, pad=14)
    for s in ax.spines.values():
        s.set_visible(False)

    # 下：四层节律 + 三判决量时点
    rhythm = [("最小步长 季度（3 月）", 3, "#2e86de"), ("裁决节律 半年", 6, "#e67e22"),
              ("对外节律 年", 12, "#27ae60"), ("全周期 60 月", 60, "#8e44ad")]
    for i, (name, period, c) in enumerate(rhythm):
        y = len(rhythm) - 1 - i
        n = 60 // period
        for k in range(n):
            ax2.broken_barh([(k * period + 0.15, period - 0.3)], (y + 0.2, 0.6),
                            facecolors=c, alpha=0.75, edgecolor="white")
        ax2.text(-1.2, y + 0.5, figtext(name), ha="right", va="center", fontsize=8.8)
    for m, lab, c in ((6, "D1 判决 M6", "#c0392b"), (12, "D3 标定 M12 起", "#8e44ad"),
                      (24, "D2 锁定判决 M24", "#c0392b"), (18, "G3 复现 M18", "#2e86de"),
                      (60, "G7 M60", "#555555")):
        ax2.axvline(m, color=c, ls=":", lw=1.1, alpha=0.8)
        ax2.text(m + (0.5 if m != 60 else -0.5), -0.42, figtext(lab), fontsize=8.0,
                 color=c, ha="left" if m != 60 else "right")
    ax2.set_xlim(-14, 62)
    ax2.set_ylim(-0.95, len(rhythm) + 0.1)
    ax2.set_yticks([])
    ax2.set_xticks(range(0, 61, 6))
    ax2.set_xticklabels([figtext(f"M{i}") for i in range(0, 61, 6)], fontsize=8.4)
    ax2.set_title(figtext("四层节律与三判决量时点（季度证据包 → 半年 Go/Pivot/Stop → "
                          "年度对外 → 60 月收口）"), fontsize=11.5, pad=10)
    for s in ax2.spines.values():
        s.set_visible(False)
    fig.text(0.075, 0.055, figtext("生死门 G1（M6）：前 6 个月只花 1.29%（15 人·月）"
                                   "｜加人闸门：G1 过才加 → k≥1 才加 → G4 过才加 "
                                   "→ 氚许可落地才加"), fontsize=8.4, color="#c0392b")
    fig.text(0.075, 0.022, figtext("Stop 规则：任何门连续两次未过 → Stop（不延长）"
                                   "｜红柱 = 生死门 G0/G1（合计 15 人·月 = 1.29%）"),
             fontsize=8.4, color="#555555")
    fig.subplots_adjust(left=0.075, right=0.925, top=0.92, bottom=0.135)
    p = os.path.join(OUT, "fig_program_gates.png")
    fig.savefig(p, dpi=140, facecolor=BG)
    plt.close(fig)
    return p


def main():
    fig = fig_gates()
    chk("PG13 图纸文字保持干净（无 缺口/未给出/第二输入 字样）",
        not any(w in lbl for lbl in FIG_LABELS for w in ("缺口", "未给出", "第二输入")),
        f"{len(FIG_LABELS)} 条图注")

    report = {
        "title": "硬件轴④排期——八门 G0–G7 机器可读排期表",
        "date": "2026-09-27",
        "对应 wiki": ["docs/wiki/fusion-program-roadmap.md"],
        "纪律": [
            "只解析页面已有的表与段落；不新造排期/人力数字。",
            "口径恒等式：人数 × 月数 = 人·月（Σ 月数 = 60）；累计人·月 / 1161 = 累计占比。",
            "页面（权威）与 scripts 产物（artifacts/fusionroadmap/report.json）的措辞差异"
            "登记为显式清单，集合必须相等——新增未登记差异即报红。",
            "金额不入库：只用 人·月 / 工期 / 人 / 比例。",
        ],
        "PG1_排期表（机器可读）": SCHEDULE,
        "PG2_恒等式": {
            "人数 × 月数 = 人·月": [f"{s['门']}: {s['人']} × {s['月数']} = {s['人·月']}"
                                    for s in SCHEDULE],
            "Σ 人·月": TOTAL_PM,
            "Σ 月数": sum(s["月数"] for s in SCHEDULE),
            "累计占比基（人·月）": 1161,
        },
        "PG3_关键数字（与页面 §7 一致）": {
            "判决期 G0+G1 占全周期人力 [%]": round(SCHEDULE[1]["累计占比 [%]"], 2),
            "M24 前累计 [%]": round(SCHEDULE[4]["累计占比 [%]"], 2),
            "前 18 个月（G0–G3）累计 [%]": round(SCHEDULE[3]["累计占比 [%]"], 2),
            "总人·月": TOTAL_PM,
            "峰值人数": SCHEDULE[-1]["人"],
        },
        "PG3b_取整差异登记（页面 vs 计算）": [
            {"门": g, "页面 §3 值 [%]": w, "计算值 [%]": c,
             "说明": "页面 §3 该行累计占比的末位取整差；属上游既有数值，"
                     "本 agent 只读不改，交回 leo 决定是否修正页面"}
            for g, w, c in ROUNDING_REGISTRY],
        "PG4_节律": {r[0]: r[1] for r in
                     [("最小步长", "季度（3 月）一个可交付证据包"),
                      ("裁决节律", "半年 Go / Pivot / Stop"),
                      ("对外节律", "年（论文 + 预注册更新 + 独立复现）"),
                      ("全周期", "60 月，八道门，每门预写失败处置")]},
        "PG5_三判决量（§1）": [
            {"判决量": "D1", "时间": "M6", "定义": "R_ci = 1/(1−μ) − 1",
             "来源条目": "FC9 / AMC1"},
            {"判决量": "D2", "时间": "M24", "定义": "Λ = τ_E 增益 / S* 惩罚",
             "来源条目": "FC5 / AMC7"},
            {"判决量": "D3", "时间": "M12 起", "定义": "k = dlnμ/dlnP",
             "来源条目": "FC9 / FC11"}],
        "PG6_预写失败处置（§6）": [f"{a}：{b}" for a, b in LESSONS],
        "PG7_措辞差异登记（页面 vs 脚本产物）": [
            {"门": g, "字段": f, "说明": _DIFFNOTE.get((g, f), "措辞不同（数字一致）")}
            for g, f in DIFF_REGISTRY],
        "PG8_第三处口径差登记（index.md）": [
            {"文件": a, "文中写的 [%]": b, "该改成的 [%]": c,
             "说明": "index.md 的 roadmap 描述行写『判决期只占 1.22% 人力』，"
                     "而 §7/§3 表算得 1.29%（15/1161）。index.md 属上游既有内容，"
                     "本 agent 只读不改，交回 leo 决定是否修正"}
            for a, b, c in _INDEX_REGISTRY],
        "图": os.path.basename(fig),
        "来源文件 hash（16 位）": {
            f: sha16(os.path.join(REPO, f)) for f in
            ["docs/wiki/fusion-program-roadmap.md",
             "artifacts/fusionroadmap/report.json"]},
        "checks": CHECKS,
    }
    rp = os.path.join(OUT, "report.json")
    with open(rp, "w", encoding="utf-8") as fh:
        json.dump(report, fh, ensure_ascii=False, indent=2)

    lines = [
        "硬件轴④排期——八门 G0–G7（2026-09-27）",
        "=" * 62,
        "门｜月｜人｜月数｜人·月｜累计人·月｜累计占比｜交付物",
    ]
    for s in SCHEDULE:
        lines.append(f"  {s['门']}｜M{s['月']}｜{s['人']} 人｜{s['月数']} 月｜{s['人·月']} 人·月｜"
                     f"{s['累计人·月']}｜{s['累计占比 [%]']:.2f}%｜{s['交付物']}")
    lines += [
        f"恒等式：人数 × 月数 = 人·月；Σ = {TOTAL_PM} 人·月（Σ 月数 = 60）",
        f"口径钉死：前 6 个月（G0+G1）{SCHEDULE[1]['累计占比 [%]']:.2f}%；"
        f"前 18 个月（G0–G3）{SCHEDULE[3]['累计占比 [%]']:.2f}%；"
        f"M24 前 {SCHEDULE[4]['累计占比 [%]']:.2f}%；峰值 {SCHEDULE[-1]['人']} 人",
        f"措辞差异登记 {len(DIFF_REGISTRY)} 项（数字全等）："
        + "、".join(f"{g}.{f}" for g, f in DIFF_REGISTRY),
        f"图：{os.path.basename(fig)}",
        f"检查：{sum(1 for c in CHECKS if c['通过'])}/{len(CHECKS)} 通过",
    ]
    sp = os.path.join(OUT, "summary.txt")
    with open(sp, "w", encoding="utf-8") as fh:
        fh.write("\n".join(lines) + "\n")
    print("\n".join(lines))
    failed = [c for c in CHECKS if not c["通过"]]
    print("\n产物：", OUT)
    if failed:
        raise SystemExit(f"排期轴检查失败 {len(failed)} 条：{[c['检查'] for c in failed]}")


if __name__ == "__main__":
    main()
