#!/usr/bin/env python3
"""μ 反馈控制律的闭环时域验证（MAC7–MAC10 数值同位体）

═════ 动机（leo 2026-10-19 续轮）═════
S5（verify_mu_axiom_chain.py）发现：恒定 η 的最后一步会跳过 FC11 天花板，
正确进窗 = 末步调小增益 + 关断。本轮把这条工程经验**一般化成显式反馈律**，
并做闭环时域验证：

    η_control(μ) = 0                          if μ ≥ μT   （关断，TD19）
                 = min(η_inj, (μT−μ)/(1−μ))   if μ < μT   （钳制到精确落窗）

Lean：ProjectionPhysics/MuAxiomChain.lean MAC7–MAC10（零 sorry）——
  MAC7a 单步不越目标 / MAC7b 控制律单步不越
  MAC8  归纳不变量 ∀n μ_n ≤ μT（μT < 天花板 ⟹ 永不越界）
  MAC9  钳制未激活段与开环一致 ⟹ 进窗步数相同
  MAC10 到目标即冻结 ⟹ 停留任意久

═════ 断言（每条对位既有锚点）═════
  C1  闭环 10000 步不越 μT（MAC8 数值同位体；开环 μ(162) 越界 S6a）
  C2  轨道单调、进窗后冻结（MAC10）
  C3  进窗步数与开环一致（MAC9；开环 S4 {2,2,4,12,36}）
  C4  劳森持续：μT 冻结点 τ_E ≥ 2s 可任意久（MAC6b/TD19）
  C5  目标带宽：μT ∈ [μT_min(劳森), 天花板] 非空且有裕度
  C6  控制轨迹形状：η 序列 = 注入 → 末步钳制 η_final → 0（对位 S5 的 0.277176）
  C7  窗口内扫描：μT 在窗口内多个取值都冻结于窗内、劳森达标

═════ 诚实边界（写死）═════
  · 控制律是模型选择（TD18/19 语义的一般化），不是物理定律；
    η_inj 数值仍待 G1/D1 标定（H1 只承诺 η>0 有限）。
  · 本脚本是闭环时域的独立验证（同锚点数字），sim_two_flow_ring.py
    保持开环口径（18 断言不动）。
  · 全部数字 = 既有闭式代入；无新物理预言。

产物：artifacts/mucontrol/{report.json, summary.txt, fig_control_loop.png}
"""
import json
import math
import os

import numpy as np
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
import matplotlib.font_manager as fm

for _fp in ("/Library/Fonts/Arial Unicode.ttf", "/System/Library/Fonts/StHeiti Light.ttc",
            "/System/Library/Fonts/PingFang.ttc"):
    if os.path.exists(_fp):
        fm.fontManager.addfont(_fp)
        plt.rcParams["font.sans-serif"] = [fm.FontProperties(fname=_fp).get_name()]
        break
plt.rcParams["axes.unicode_minus"] = False

REPO = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
OUT = os.path.join(REPO, "artifacts", "mucontrol")
os.makedirs(OUT, exist_ok=True)

CHECKS = []

# ── 仓库锚点（与 verify_mu_axiom_chain.py 同口径）────────────────────────
MU0 = 0.15
MU_T = 0.9997                      # 输运解锁门槛（箍定目标下界）
MU_CEIL = 1.0 - 2.19432e-4         # 0.999780568036375（FC11 天花板）
TAU0 = 0.036                       # 0.2m 环基线约束时间 [s]
TAU_LAWSON = 2.0
ETA_INJ = 0.5                      # 注入增益（容差内档位，S4 同族）
ETA_TABLE = [0.999, 0.99, 0.9, 0.5, 0.2]
HORIZON = 10000


def eta_control(muT, eta_inj, mu):
    """反馈控制律：μ ≥ μT 关断；否则 min(η_inj, 精确落窗增益)。"""
    if mu >= muT:
        return 0.0
    return min(eta_inj, (muT - mu) / (1.0 - mu))


def mu_step(mu, eta):
    return mu + eta * (1.0 - mu)


def closed_loop(mu0, muT, eta_inj, n):
    """闭环轨道：返回 (μ_list, η_list)。"""
    mus, etas = [mu0], []
    mu = mu0
    for _ in range(n):
        eta = eta_control(muT, eta_inj, mu)
        etas.append(eta)
        mu = mu_step(mu, eta)
        mus.append(mu)
    return mus, etas


def open_entry_steps(mu0, eta, target):
    """开环进窗步数（TD7 反解，η<1）。"""
    if eta >= 1.0:
        return 1
    num = math.log((1.0 - mu0) / (1.0 - target))
    den = math.log(1.0 / (1.0 - eta))
    return max(math.ceil(num / den - 1e-12), 1)


def check(name, cond, detail=""):
    CHECKS.append({"检查": name, "通过": bool(cond), "细节": str(detail)})


# ── C1：闭环永不越目标（MAC8 数值同位体；对比开环 S6a 越界）──────────────
mus, etas = closed_loop(MU0, MU_T, ETA_INJ, HORIZON)
max_mu = max(mus)
over = [m for m in mus if m > MU_T + 1e-12]
check("C1 闭环 10000 步 μ ≤ μT 恒成立（MAC8；μT < 天花板 ⟹ 永不越界）",
      max_mu <= MU_T + 1e-12 and len(over) == 0,
      f"max μ = {max_mu:.10f} ≤ μT = {MU_T}；越界点数 = {len(over)}（开环对比：μ(162) = 0.999790761 越天花板 1.019e-5）")

# ── C2：单调 + 进窗冻结（MAC10）──────────────────────────────────────────
diffs = [mus[k + 1] - mus[k] for k in range(len(mus) - 1)]
mono = all(d >= -1e-15 for d in diffs)
strict_before_freeze = all(d > 1e-15 for d in diffs[:12])   # 前 12 步严格增
mu_closed_target = mus[12] if len(mus) > 12 else MU_T
frozen_after = all(abs(mus[k] - mu_closed_target) < 1e-9 for k in range(12, len(mus)))
check("C2 轨道单调递增、进窗后冻结（MAC10 关断语义）",
      mono and strict_before_freeze and frozen_after,
      f"前 12 步严格增；μ_12 起 ≡ {mu_closed_target:.10f}（冻结 9988 步不变）")

# ── C3：进窗步数与开环一致（MAC9）────────────────────────────────────────
open_entries = {e: open_entry_steps(MU0, e, MU_T) for e in ETA_TABLE}
closed_entries = {}
for e in ETA_TABLE:
    m_c, _ = closed_loop(MU0, MU_T, e, 200)
    first = next(k for k, v in enumerate(m_c) if v >= MU_T - 1e-12)
    closed_entries[e] = first
same = all(closed_entries[e] == open_entries[e] for e in ETA_TABLE)
check("C3 进窗步数与开环一致（MAC9：钳制只激活在末步）",
      same,
      f"开环 {open_entries} vs 闭环 {closed_entries}（钳制 ≤1 步，进窗不因控制变慢）")

# ── C4：劳森持续（冻结点 τ_E ≥ 2s，可任意久）─────────────────────────────
tau_frozen = TAU0 / math.sqrt(1.0 - MU_T)
check("C4 劳森持续：μT=0.9997 冻结 ⟹ τ_E=2.078s ≥ 2s（MAC6b：停留任意久）",
      tau_frozen >= TAU_LAWSON,
      f"τ_E = {tau_frozen:.3f} s（冻结即持续；天花板处 2.430 s）")

# ── C5：目标带宽（μT 可行区间非空且有裕度）───────────────────────────────
muT_min = 1.0 - (TAU0 / TAU_LAWSON) ** 2        # τ_E(μT_min) = 劳森 ⇒ 下界
band = MU_CEIL - muT_min
check("C5 目标带宽：μT ∈ [劳森下界, 天花板] 非空且有裕度",
      band > 0 and muT_min < MU_T < MU_CEIL,
      f"μT_min(τ_E=2s) = {muT_min:.6f}；带宽 {band:.3e}；μT=0.9997 在带内且天花板余量 {(MU_CEIL - MU_T):.3e}")

# ── C6：控制轨迹形状（η 序列 = 注入 → 末步钳制 → 0）──────────────────────
muT = MU_T
eta_series = []
m = MU0
for _ in range(16):
    eta_series.append(eta_control(muT, ETA_INJ, m))
    m = mu_step(m, eta_series[-1])
eta_final = eta_series[11]                       # 第 12 步（进窗步）
eta_after = eta_series[12]
check("C6 控制轨迹形状：11 步注入 0.5，第 12 步钳制 η_final，此后 0（对位 S5）",
      abs(eta_series[0] - 0.5) < 1e-12 and 0 < eta_final < 0.5 and eta_after == 0.0,
      f"η₀..₁₀ = 0.5；η₁₁ = {eta_final:.6f}（S5 锚点 0.277176）；η₁₂.. = 0（关断）")

# ── C7：目标扫描（μT 在窗口内多点都冻结于窗内、劳森达标）─────────────────
scan = [0.99970, 0.99972, 0.99974, 0.99976, 0.99978]
scan_ok = []
for t in scan:
    m_s, _ = closed_loop(MU0, t, ETA_INJ, 500)
    mf = m_s[-1]
    tau_s = TAU0 / math.sqrt(1.0 - mf)
    ok = mf >= t - 1e-12 and mf <= t + 1e-12 and mf < MU_CEIL and tau_s >= TAU_LAWSON
    scan_ok.append(ok)
check("C7 目标扫描：μT ∈ {0.99970..0.99978} 全部冻结于目标、窗内、劳森达标",
      all(scan_ok),
      f"{[round(t, 5) for t in scan]} 全部冻结于窗内（τ_E ∈ [{2.078:.3f}, {TAU0 / math.sqrt(1 - 0.99978):.3f}]s）")

# ── 图：闭环 μ 轨道 + η 控制轨迹（双面板），窗口带 + 开环越界对比 ────────
fig, (ax1, ax2) = plt.subplots(2, 1, figsize=(9, 7), sharex=True)
ns = np.arange(0, 40)
mu_open = MU0
open_ser = [MU0]
for _ in range(39):
    mu_open = mu_step(mu_open, 0.5)
    open_ser.append(mu_open)
ax1.plot(ns, open_ser, "C3--", lw=1.5, label="开环恒定 η=0.5（第 12 步跳过天花板）")
ax1.plot(ns, mus[:40], "C0-", lw=2.5, label="闭环反馈律（进窗即冻结）")
ax1.axhline(MU_T, color="C2", ls=":", lw=1.2, label=f"目标 μT={MU_T}")
ax1.axhspan(MU_T, MU_CEIL, color="gray", alpha=0.15, label="工作窗口 [0.9997, 0.999780568]")
ax1.axhline(MU_CEIL, color="red", ls="--", lw=1)
ax1.annotate("FC11 天花板", (30, MU_CEIL), textcoords="offset points", xytext=(0, 6), fontsize=9, color="red")
ax1.set_ylabel("μ")
ax1.legend(loc="lower right", fontsize=9)
ax1.grid(alpha=0.3)
ax2.bar(range(len(etas[:20])), etas[:20], color="C1", alpha=0.8)
ax2.axhline(0, color="k", lw=0.8)
ax2.annotate(f"末步钳制 η_final={eta_final:.4f}", (11, eta_final),
             textcoords="offset points", xytext=(6, 4), fontsize=9, color="C1")
ax2.set_xlabel("递推步 n")
ax2.set_ylabel("η_control")
ax2.grid(alpha=0.3)
fig.tight_layout()
fig.savefig(os.path.join(OUT, "fig_control_loop.png"), dpi=150)

passed = sum(1 for c in CHECKS if c["通过"])
report = {
    "控制律": "η_control(μ) = 0 if μ≥μT else min(η_inj, (μT−μ)/(1−μ))（TD19 关断 + 末步钳制一般化）",
    "Lean": "MAC7a/MAC7b/MAC8/MAC9/MAC10（零 sorry）",
    "checks": CHECKS,
    "锚点": {
        "mu0": MU0, "muT": MU_T, "mu_ceil": MU_CEIL,
        "muT_min_劳森": muT_min, "目标带宽": band,
        "进窗步数_开环": open_entries, "进窗步数_闭环": closed_entries,
        "冻结点_tau_E": round(tau_frozen, 4),
        "eta_final_第12步": eta_final,
        "开环越界对比_μ162": 0.999790760833,
    },
    "诚实边界": [
        "控制律是模型选择（TD18/19 语义一般化），非物理定律；η_inj 数值待 G1/D1 标定",
        "闭环为独立时域验证（同锚点）；sim_two_flow_ring.py 保持开环口径（18 断言不动）",
        "全部数字 = 既有闭式代入；无新物理预言",
    ],
    "conclusion": "闭环反馈律验证成立：10000 步永不越目标（MAC8），进窗步数与开环一致（MAC9），到目标即冻结（MAC10）⟹ 劳森 τ_E=2.078s 持续任意久；目标带宽 [0.999676, 0.999781] 非空。"
    if passed == len(CHECKS) else f"FAIL: {passed}/{len(CHECKS)} 通过",
}
with open(os.path.join(OUT, "report.json"), "w", encoding="utf-8") as f:
    json.dump(report, f, ensure_ascii=False, indent=2)
with open(os.path.join(OUT, "summary.txt"), "w", encoding="utf-8") as f:
    f.write(f"μ 反馈控制律闭环时域验证：{passed}/{len(CHECKS)} 断言通过\n")
    for c in CHECKS:
        f.write(f"  {'PASS' if c['通过'] else 'FAIL'}  {c['检查']}  {c['细节']}\n")

print(f"RESULT: {passed}/{len(CHECKS)} passed")
for c in CHECKS:
    print(f"  {'PASS' if c['通过'] else 'FAIL'}  {c['检查']}")
    print(f"         {c['细节']}")
print(f"产物: {OUT}/{{report.json, summary.txt, fig_control_loop.png}}")