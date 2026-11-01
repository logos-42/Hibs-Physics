#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""胶球质量阶梯：把 M₀ 定死成一个数，产出 ≥4 GeV 的可判死预言 + 死法（LAD1–LAD6）

leo（2026-11-01）：审计第一刀 ——「M₀ 从每文一个拟合改成单一定值」。

病因（审计登记）：仓库此前每个脚本各用各的 M₀（0.93 / 0.977 / 0.987 / 0.99 GeV），
于是「√N·M₀ 命中格点」永远成立 —— 每个态都能吃到一个私人标定 ⟹ 零预言力。
本脚本把三件事定死，此后不再调整：

  ① **M₀ 唯一来源**：单一锚点态 0++，单次除法 M₀ := m(0++)/√3。
     两个标度约定各算一次（TABLE XXI：r₀⁻¹ = 410 MeV；Athenodorou–Teper 2020：
     √σ = 475.6 MeV），但**每个约定内部只有一个数**，绝不逐态重标定。
  ② **阶梯规则（定死，不含整数选择自由）**：
     N = Σᵢ nᵢ² + |μ̄₃|，nᵢ ∈ ℤ\\{0}，μ̄₃ ∈ {0,1} 且仅当 max|nᵢ| ≥ 2（变体 II），R = 6。
     变体 II 有据：变体 I（μ̄₃ 任意）会多出 √4·M₀ ≈ 1.87 GeV 的奇宇称态，
     而格点最轻奇宇称态在 2.3–2.6 GeV ⟹ 变体 I 被数据否掉（RT-B 已登记）。
  ③ **对位两口径各报**（模型现状的诚实登记，不是自由度）：
     严格版 = 质量升序↔阶梯升序一一对应；简并版 = 落最近一阶（多态可共享 N）。

产出：
  LAD1 阶梯算术（可达集 / 缺口 / 覆盖率）+ 算术断言
  LAD2 单一 M₀（两个标度约定各一个数）
  LAD3 残差账本（严格版 vs 简并版，失败项照登）
  LAD4 ≥4 GeV 阶梯位置 + 禁区窗口 + 所需格点精度
  LAD5 饱和性：≥4 GeV 处 ±2% 判据的随机基线
  LAD6 死法 D1–D6（带数值阈值）

Lean 端同一批事实：`ProjectionPhysics/Explorations/GlueballLadder.lean`（LAD1–LAD7，零 sorry）
  —— 4/5/8/16 不可达（无条件）、窗口定理 `window_empty_sq`、间距 <2%（N ≥ 25）均已证。

诚实边界（写死）：不产生 J^PC（RT-F 已证线性规则给不出）、不碰宽度/衰变/产生率、
M₀ 仍是输入（SC6）、禁区判决力受格点误差限制（本脚本给出需要的阈值，不声称已判决）。
"""

import json
import math
import os
from datetime import date

import numpy as np

REPO = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
OUT = os.path.join(REPO, "artifacts", "glueball_ladder")
os.makedirs(OUT, exist_ok=True)

FAILS = []


def check(label, ok, detail=""):
    print(f"  [{'PASS' if ok else 'FAIL'}] {label}" + (f"  ({detail})" if detail else ""))
    if not ok:
        FAILS.append(label)


# ───────────────────────── LAD1 阶梯规则（定死） ─────────────────────────
print("=" * 78)
print("LAD1 阶梯规则：N = Σᵢ nᵢ² + |μ̄₃|（变体 II，R = 6）—— 无整数选择自由")
print("=" * 78)


def ladder(R=6, variant=2):
    """可达 N 集合。nᵢ ∈ ℤ\\{0}（三方向都要在），μ̄₃ ∈ {0,1}（变体 II 需 max|nᵢ| ≥ 2）。"""
    reach = {}
    for a in range(-R, R + 1):
        for b in range(-R, R + 1):
            for c in range(-R, R + 1):
                if a == 0 or b == 0 or c == 0:
                    continue
                base = a * a + b * b + c * c
                reach.setdefault(base, (a, b, c, 0))
                if variant == 2 and max(abs(a), abs(b), abs(c)) < 2:
                    continue
                reach.setdefault(base + 1, (a, b, c, 1))
    return sorted(reach), reach


LADDER, IMPL = ladder()
LAD_SET = set(LADDER)
print(f"  可达 N（R=6）共 {len(LADDER)} 个，最大 N = {LADDER[-1]}")
print(f"  前 20 阶：{LADDER[:20]}")
MISSING = [n for n in range(3, 61) if n not in LAD_SET]
print(f"  3–60 的缺口 N（= 禁区）：{MISSING}")
COVER = len([n for n in LADDER if 3 <= n <= 60])
print(f"  覆盖率（3–60）：{COVER}/{58} = {COVER / 58:.1%}")

check("LAD1a 前四阶 = 3,6,7,9（复现仓库 N 序列 3,6,7）", LADDER[:4] == [3, 6, 7, 9], str(LADDER[:4]))
check("LAD1b 7 可达但不在对角型（Legendre 三平方定理：7 不可表）",
      7 in LAD_SET and all(a * a + b * b + c * c != 7
                           for a in range(-3, 4) for b in range(-3, 4) for c in range(-3, 4)))
check("LAD1c 变体 I 多给出 N=4（√4·M₀ ≈ 1.87 GeV 的奇宇称态，格点无）",
      4 in set(ladder(variant=1)[0]) and 4 not in LAD_SET)
check("LAD1d 缺口 N=16 存在（√15–√17 之间 6% 宽空档）",
      16 not in LAD_SET and 15 in LAD_SET and 17 in LAD_SET)

# ───────────────────── LAD2 单一 M₀（单锚点态，单次除法） ─────────────────────
print()
print("=" * 78)
print("LAD2 定死 M₀：M₀ := m(0++)/√3（单一锚点态，此后不再调整）")
print("=" * 78)

# TABLE XXI of "Glueball masses from the lattice: a (partial) review of recent results"
DATA_21 = [("0++", 1710, 50, 80), ("2++", 2390, 30, 120), ("0-+", 2560, 35, 120),
           ("1+-", 2980, 30, 140), ("2-+", 3040, 40, 150),
           ("3+-", 3600, 40, 170), ("3++", 3670, 50, 180)]
# Athenodorou–Teper 2020 (JHEP 11 (2020) 172, Table 17)，M_G/√σ，√σ = 475.6 MeV
DATA_AT = [("0++", 1619, 10), ("2++", 2328, 10), ("0-+", 2509, 21),
           ("1+-", 2885, 19), ("2-+", 3006, 43)]

SETS = []
for name, rows, split in (("TABLE XXI", DATA_21, True), ("AT2020", DATA_AT, False)):
    M0 = rows[0][1] / math.sqrt(3)
    SETS.append({"name": name, "rows": rows, "split": split, "M0": M0})
    print(f"  {name}: m(0++) = {rows[0][1]} MeV ⟹ M₀ = {rows[0][1]}/√3 = {M0:.2f} MeV（唯一标定）")

# ────────────────── LAD3 对位 + 残差账本 ──────────────────
print()
print("=" * 78)
print("LAD3 对位与残差账本（严格版 vs 简并版；失败项照登）")
print("=" * 78)

report = {"model": "glueball ladder with M₀ fixed by a single anchor state",
          "date": str(date.today()), "rule": "N = Σnᵢ² + |μ̄₃| (variant II, R=6)",
          "ladder_N": LADDER, "missing_N_3_60": MISSING,
          "coverage_3_60": round(COVER / 58.0, 4), "results": {}}


def nearest_rung(m, M0):
    return min(LADDER, key=lambda n: abs(math.sqrt(n) * M0 - m))


for S in SETS:
    M0, rows, name = S["M0"], S["rows"], S["name"]
    strict, degen = [], []
    for i, row in enumerate(rows):
        st, m = row[0], row[1]
        err = (row[2] + row[3]) if S["split"] else row[2]
        n_s, n_d = LADDER[i], nearest_rung(m, M0)
        p_s, p_d = math.sqrt(n_s) * M0, math.sqrt(n_d) * M0
        strict.append({"J^PC": st, "obs": m, "err": err, "N": n_s, "pred": round(p_s, 1),
                       "dev_pct": round((p_s - m) / m * 100, 2),
                       "pass_err": bool(abs(p_s - m) <= err),
                       "pass_3pct": bool(abs(p_s - m) / m <= 0.03)})
        degen.append({"J^PC": st, "obs": m, "err": err, "N": n_d, "pred": round(p_d, 1),
                      "dev_pct": round((p_d - m) / m * 100, 2),
                      "pass_3pct": bool(abs(p_d - m) / m <= 0.03)})
    ns_ok = sum(r["pass_3pct"] for r in strict)
    nd_ok = sum(r["pass_3pct"] for r in degen)
    shared = {}
    for r in degen:
        shared.setdefault(r["N"], []).append(r["J^PC"])
    pairs = []
    for i in range(len(rows) - 1):
        m1, m2 = rows[i][1], rows[i + 1][1]
        if m2 / m1 - 1 < 0.03:
            n1, n2 = strict[i]["N"], strict[i + 1]["N"]
            pairs.append({"态对": [rows[i][0], rows[i + 1][0]],
                          "格点劈裂%": round((m2 / m1 - 1) * 100, 2),
                          "阶梯劈裂%": round((math.sqrt(n2) / math.sqrt(n1) - 1) * 100, 2)})
    print(f"\n  【{name}】M₀ = {M0:.2f} MeV")
    for r in strict:
        print(f"   严格 {r['J^PC']:5s} obs {r['obs']:6d}±{r['err']:<4d} N={r['N']:2d} "
              f"pred {r['pred']:7.1f} ({r['dev_pct']:+6.2f}%)"
              f"{'  ✓' if r['pass_3pct'] else '  ✗ 失败'}")
    print(f"   ⟹ 严格版通过 {ns_ok}/{len(strict)}；简并版 ±3% 通过 {nd_ok}/{len(degen)}；"
          f"共享阶 {dict((k, v) for k, v in shared.items() if len(v) > 1)}")
    for p in pairs:
        print(f"   近简并 {p['态对'][0]}/{p['态对'][1]}：格点 {p['格点劈裂%']:.2f}% "
              f"vs 阶梯 {p['阶梯劈裂%']:.2f}%")
    report["results"][name] = {"M0_MeV": round(M0, 2), "strict": strict, "degen": degen,
                               "strict_pass": ns_ok, "degen_pass": nd_ok,
                               "n_states": len(rows), "near_degenerate_pairs": pairs}

# ─────────────────── LAD4 ≥4 GeV 预言 + 禁区窗口 ───────────────────
print()
print("=" * 78)
print("LAD4 ≥4 GeV 预言（阶梯位置 + 禁区窗口 + 所需格点精度）")
print("=" * 78)

pred_block = {}
for S in SETS:
    M0 = S["M0"]
    rungs = [(n, math.sqrt(n) * M0) for n in LADDER if 4000.0 <= math.sqrt(n) * M0 <= 6500.0]
    wins = []
    for n_miss in MISSING:
        lo_n, hi_n = n_miss - 1, n_miss + 1
        if lo_n not in LAD_SET or hi_n not in LAD_SET:
            continue
        lo_m, hi_m = math.sqrt(lo_n) * M0, math.sqrt(hi_n) * M0
        if hi_m < 4000.0 or lo_m > 6500.0:
            continue
        wins.append({"缺口 N": n_miss, "禁区 [MeV]": [round(lo_m), round(hi_m)],
                     "宽度 [MeV]": round(hi_m - lo_m),
                     "相对宽度 %": round((hi_m / lo_m - 1) * 100, 2)})
    spacing = [(rungs[i + 1][1] / rungs[i][1] - 1) * 100 for i in range(len(rungs) - 1)]
    print(f"\n  【{S['name']}】M₀ = {M0:.2f} MeV：{len(rungs)} 阶，"
          f"{rungs[0][1]:.0f}–{rungs[-1][1]:.0f} MeV，平均间距 {np.mean(spacing):.2f}%")
    for w in wins:
        print(f"   ★ 禁区 N={w['缺口 N']}：{w['禁区 [MeV]'][0]}–{w['禁区 [MeV]'][1]} MeV "
              f"（宽 {w['宽度 [MeV]']} MeV，{w['相对宽度 %']}%）")
    need_err = min((w["宽度 [MeV]"] / 2 for w in wins), default=float("nan"))
    print(f"   ⟹ 判掉任一禁区所需格点误差 ≤ ±{need_err:.0f} MeV（现 3.6 GeV 处 ±210–230 MeV）")
    pred_block[S["name"]] = {"M0_MeV": round(M0, 2),
                             "rungs_4_65GeV": [(n, round(m, 1)) for n, m in rungs],
                             "mean_spacing_pct": round(float(np.mean(spacing)), 2),
                             "min_spacing_pct": round(float(min(spacing)), 2),
                             "forbidden_windows": wins,
                             "needed_lattice_err_MeV": round(need_err)}
report["results"]["predictions_ge_4GeV"] = pred_block

check("LAD4a ≥4 GeV 处阶梯间距 < 4%（逐阶判据饱和）",
      all(p["min_spacing_pct"] < 4.0 for p in pred_block.values()))
check("LAD4b 每个约定在 4–6.5 GeV 内至少一个禁区窗口",
      all(len(p["forbidden_windows"]) >= 1 for p in pred_block.values()))

# ─────────────── LAD5 饱和性：±2% 判据的随机基线 ───────────────
print()
print("=" * 78)
print("LAD5 可区分度（随机基线：随便一个质量落在某阶 ±2% 内的概率）")
print("=" * 78)

rng = np.random.default_rng(20261101)
sat = {}
for S in SETS:
    for lo, hi, tag in ((1000.0, 4000.0, "1–4 GeV"), (4000.0, 6500.0, "4–6.5 GeV")):
        ms = rng.uniform(lo, hi, 200000)
        rung_m = np.array([math.sqrt(n) * S["M0"] for n in LADDER])
        hit = np.min(np.abs(ms[:, None] - rung_m[None, :]) / ms[:, None], axis=1) <= 0.02
        sat[f"{S['name']} {tag}"] = round(float(hit.mean()), 4)
        print(f"  {S['name']:9s} {tag:9s} ±2% 命中率 = {hit.mean():.1%}")
report["results"]["saturation_random_baseline"] = sat

check("LAD5a 4–6.5 GeV 的 ±2% 命中率 ≥ 90%（该区间只能用禁区判死）",
      all(v >= 0.90 for k, v in sat.items() if "4–6.5" in k))

# ───────────────────────── LAD6 死法与产物 ─────────────────────────
print()
print("=" * 78)
print("LAD6 死法（带数值阈值；任一条成立 ⟹ 定死 M₀ 的阶梯模型死）")
print("=" * 78)

w16 = [w for w in pred_block["TABLE XXI"]["forbidden_windows"] if w["缺口 N"] == 16][0]
death = [
    {"编号": "D1", "条件": f"N=16 禁区（{w16['禁区 [MeV]'][0]}–{w16['禁区 [MeV]'][1]} MeV）内"
                       f"确认存在纯规范胶球态（误差 ≤ ±{round(w16['宽度 [MeV]'] / 2)} MeV）",
     "含义": "阶梯可达集错了（Σnᵢ²+|μ̄₃| 不是质量谱）"},
    {"编号": "D2", "条件": "任一新态相对最近阶偏离 > 5%（误差 ≤ 2%）",
     "含义": "M₀ 单一定值不成立 ⟹ 回到私人标定 = 零预言力"},
    {"编号": "D3", "条件": "同一 M₀ 下严格版通过率 < 4/7（TABLE XXI）或 < 3/5（AT2020）",
     "含义": "阶梯与谱的排序结构不符（当前 5/7、5/5，已贴边界）"},
    {"编号": "D4", "条件": "出现劈裂 < 2% 而阶梯最小劈裂 > 4% 的近简并对（当前已有 2 例）",
     "含义": "阶梯缺简并结构 ⟹ √N 间距不是谱的真实间距"},
    {"编号": "D5", "条件": "变体 I 的 N=4 态（≈1.87 GeV 奇宇称）被格点确认",
     "含义": "变体 II 的模型选择被推翻"},
    {"编号": "D6", "条件": "跨标度约定无法用同一 M₀ 复现（残差 > 5%）",
     "含义": "「单一 M₀」只是某约定的巧合"},
]
for d in death:
    print(f"  {d['编号']}  {d['条件']}\n      ⟹ {d['含义']}")
report["death_conditions"] = death

d3_now = {k: f"{v['strict_pass']}/{v['n_states']}" for k, v in report["results"].items()
          if "strict_pass" in v}
print(f"\n  现状照登：D3 通过率 = {d3_now}")
report["results"]["current_status_D3"] = d3_now

report["conclusion"] = (
    "定死 M₀（单锚点态）后：① 严格版 5/7（TABLE XXI，3+- −9.0%、3++ −6.8%）与 5/5（AT2020，"
    "全部 ≤2.8%）；② ≥4 GeV 处阶梯间距 1.1–2.0% < 格点误差 ⟹ 「落阶」判据饱和（随机基线 100%），"
    "唯一硬判据是禁区窗口（N=16：3.82–4.07 GeV；N=32/40 更高）；③ 结构性缺陷：阶梯最小劈裂 > 4% "
    "而格点谱存在 2% 近简并对（2 例）⟹ √N 间距不是谱的真实间距。"
    "本脚本只交付「定死 + 可判死」，不交付 J^PC、宽度、产生率。")
report["honest"] = [
    "M₀ 仍是输入（SC6：框架零标度内容，比值不可能输出 M₀ 的数值）",
    "J^PC 仍不可导出（RT-F 已穷举 256 条线性规则，全中 7 项者 = 0）",
    "禁区窗口宽度 ≈ 格点误差量级 ⟹ 目前只能算「待判」，不算「已判」",
    "两种对位口径判决不同（5/7 vs 7/7）本身说明模型尚未锐化到唯一预言",
]

with open(os.path.join(OUT, "report.json"), "w", encoding="utf-8") as f:
    json.dump(report, f, ensure_ascii=False, indent=2)

print(f"\n报告 → {os.path.join(OUT, 'report.json')}")
print()
if FAILS:
    print(f"✗ 算术断言失败 {len(FAILS)} 项：{FAILS}")
    raise SystemExit(1)
print("✓ 全部算术断言通过（残差账本见 report.json；失败项照登，不做断言）")
print("  Lean 端同一批事实：ProjectionPhysics/Explorations/GlueballLadder.lean（LAD1–LAD7，零 sorry）")
