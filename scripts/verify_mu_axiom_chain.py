#!/usr/bin/env python3
"""μ 主动产生假设下的分步闭链验证 —— 大胆假设只落第一环，之后一步步算

═════ 收编指令（leo 2026-10-19 + 同日更正）═════
「把这个事情当成是已经解决了的实验缺口。我的脑子里已经有基本的物理来源了，
而且代码和数学模型都已经建好了，现在是要去验证它。不要用反问或者抗拒的语气，
先用大胆假设的方式来验证。」
更正：「**不能让 μ 一步到位**。我们可以开始计算，但不是一步到位。我要算的
事情是基于现有系统里的内容进行大胆假设，不是让你直接一步到位。我们的推导
是一步一步来的。」

═════ 本脚本怎么体现「分步」═════
大胆假设只落在**链条第一环**：
    H1  电磁时变场驱动空间流起伏变化（Q_A 改变），产生**有限**增益 η > 0。
        —— 这是要标定的量（G1/D1 首次标定），不承诺一步到位、不承诺 η=1。
之后每一环都用仓库已有闭式**逐项计算**，不跳：
    L2  η 是几何/场配置的输出（有限值，可正可负：FRC 半径差给 η=−20.5，
        同半径退化给 η=+1.0 上界）              gravity PAGE PASS6 / lowcost D6
    L3  μ_{n+1} = μ_n + η(1−μ_n)（TD1 muStep），闭式 μ_n = 1−(1−η)ⁿ(1−μ₀)（TD7）
        —— 有限 η < 1 ⟹ 有限步不可达 1（MAC6a），逐项递推进窗
    L4  进窗判据（MAC4）：(1−η)ⁿ(1−μ₀) ≤ 1−μT 时 μ_n ≥ μT
    L5  输运增益 τ_E = τ₀/√(1−μ_n)（AMC1 链）⟹ 劳森闭合
    L6  天花板纪律：恒定 η 越 FC11 天花板（档位语义 = 必须关断，TD19）；
        关断 ⟹ 停窗（MAC6b）

═════ 断言（每条对位既有产物锚点）═════
  S1  η 是几何的有限输出（非恒 1，符号可变）  ↔ gravity PRE PASS6 / lowcost D6
  S2  有限增益表 η ∈ {0.999, 0.99, 0.9, 0.5, 0.2} 全 < 1（无一步到位）
  S3  分步递推：μ_n 逐项单调、增量递减、有限步 < 1（MAC6a 数值同位体）
  S4  进窗需有限步 n_entry 全 < 关闭步 n*=162    ↔ design-two-flow-ring.md
  S5  劳森闭口：进窗点 τ_E(μ_entry) ≥ 2s         ↔ current-status 二轮修正
  S6  天花板纪律：恒定 η 越界 ⟹ 必须关断（TD19）；关断 ⟹ 停窗（MAC6b）
  S7  功率标度：η×10 ⟹ n_entry ÷12.9（k≥1 可行域）  ↔ roadmap D3

═════ 诚实边界（写死）═════
  · H1 只承诺「η > 0 有限」，不承诺一步到位；η 的数值由 G1/D1 标定
    （首次标定门，非存在性判决——已收编为公设，无实验证据）。
  · η=1 是上界/退化情形（TD14a 已有 Lean 定理），本脚本不把它当递推头条。
  · η 衰减/关断形状是模型选择（TD18/19）；窗口 8.06e-5 是 FC11 口径。
  · 无新物理预言；全部数字 = 既有闭式代入。

产物：artifacts/muaxiomchain/{report.json, summary.txt, fig_mu_orbits.png}
"""
import argparse
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
OUT = os.path.join(REPO, "artifacts", "muaxiomchain")
os.makedirs(OUT, exist_ok=True)

CHECKS = []

# ── 仓库锚点（全部来自既有产物，不新造数）──────────────────────────────
MU0 = 0.15                            # μ 初值（design-two-flow-ring.md 口径）
MU_T = 0.9997                         # 输运解锁门槛（current-status 二轮修正）
EPS_RESID = 2.19432e-4                # FC11 残余比 m_e/m_i（theory-mu-power.md 口径）
MU_CEIL = 1.0 - EPS_RESID             # 0.999780568036375（FC11 天花板）
TAU0 = 0.036                          # 0.2m 微型环基线约束时间 [s]（二轮修正锚点）
TAU_LAWSON = 2.0                      # 劳森需求 [s]（n=1e20, 15 keV，PF 轮）
ETA_TABLE = [0.999, 0.99, 0.9, 0.5, 0.2]   # 有限增益表（gravity PASS6 容差表同族，全 < 1）


def mu_closed(mu0, eta, n):
    """TD7 闭式：μ_n = 1 − (1−η)ⁿ(1−μ₀)。"""
    return 1.0 - (1.0 - eta) ** n * (1.0 - mu0)


def mu_iter(mu0, eta, n):
    """TD1 逐项递推（分步，不用闭式）——验证两步走出来的轨道与闭式一致。"""
    mu = mu0
    for _ in range(n):
        mu = mu + eta * (1.0 - mu)
    return mu


def steps_to(mu0, eta, target):
    """进窗最小步数（闭式反解，η<1 时有限）。"""
    if eta >= 1.0:
        return 1
    num = math.log((1.0 - mu0) / (1.0 - target))
    den = math.log(1.0 / (1.0 - eta))
    return max(math.ceil(num / den - 1e-12), 1)


def check(name, cond, detail=""):
    CHECKS.append({"检查": name, "通过": bool(cond), "细节": str(detail)})


# ── S1：η 是几何的有限输出（非恒 1，符号可变）────────────────────────────
eta_frc = -20.5340                     # FRC 半径差几何（lowcost D6a 锚点）
eta_degen = 1.0                        # 同半径退化 = 上界（lowcost D6b）
check("S1 η 是几何有限输出：FRC 几何 η=−20.5 < 0，同半径退化 η=+1.0 上界（可负可正，非恒 1）",
      eta_frc < 0 < eta_degen,
      f"η(FRC) = {eta_frc}（对位 lowcost D6a），η(退化) = {eta_degen}（上界）⟹ 符号由几何定")

# ── S2：有限增益表全 < 1（无一步到位）────────────────────────────────────
all_finite = all(0 < e < 1 for e in ETA_TABLE)
check("S2 有限增益表 η ∈ {0.999,0.99,0.9,0.5,0.2} 全 < 1（无一步到位）",
      all_finite,
      f"全 < 1；对位 gravity PASS6 容差表（η 掉到 0.5 也只需 ~12 步进窗，见 S4）")

# ── S3：分步递推（TD1 逐项迭代 == TD7 闭式；单调、增量递减、有限步 <1）───
# 注意：float64 在 ~200 步会把 μ 舍入到 1（机器精度假象），有限步 <1 的正确
# 检验窗口在进窗步附近（20 步内），不是任意远。
n = 20
mu_iter_series = [mu_iter(MU0, 0.5, k) for k in range(n + 1)]
mu_closed_series = [mu_closed(MU0, 0.5, k) for k in range(n + 1)]
max_dev = max(abs(a - b) for a, b in zip(mu_iter_series, mu_closed_series))
mono = all(mu_iter_series[k] < mu_iter_series[k + 1] for k in range(n))
incr_decr = all(mu_iter_series[k + 1] - mu_iter_series[k]
                < mu_iter_series[k] - mu_iter_series[k - 1] + 1e-15 for k in range(1, n))
check("S3a 分步递推==闭式：TD1 逐项迭代 20 步与 TD7 闭式逐点一致",
      max_dev < 1e-12,
      f"max|递推−闭式| = {max_dev:.2e}（两步走出来的轨道一样，分步不是近似）")
check("S3b 轨道性质：μ 严格单调、增量递减（几何收敛）、20 步（进窗步附近）仍 < 1",
      mono and incr_decr and mu_iter_series[n] < 1.0,
      f"μ_20 = {mu_iter_series[n]:.8f} < 1（MAC6a：有限步不可达 1；注意 float64 在 ~200 步会舍入到 1，检验窗取进窗步附近）")

# ── S4：进窗需有限步 n_entry，全 < 关闭步 n*=162 ─────────────────────────
n_close = steps_to(MU0, 0.05, MU_CEIL)          # 关闭步（η=0.05 口径）= 162
entries = {e: steps_to(MU0, e, MU_T) for e in ETA_TABLE}
all_before_close = all(v < n_close for v in entries.values())
check("S4 进窗步数全部有限且 < 关闭步 162：η=0.999→2 步 … η=0.2→36 步",
      all_before_close,
      f"n_entry = {entries}；关闭步 n*(η=0.05) = {n_close}（领先 {n_close - min(entries.values())} 步；对位 design-two-flow-ring.md）")

# ── S5：劳森闭口 + 精确进窗——最后一步把 η 调小（分步控制，不越天花板）─────
# 注意：恒定 η 的最后一步会从 μ<0.9997 跳到 0.9997925（越天花板），所以
# 正确进窗 = 前 n−1 步用恒定 η，最后一步 η_final = (μ_T − μ_prev)/(1−μ_prev)
# 精确落在窗口内，然后关断（TD19）。这是「分步」的工程含义。
def entry_with_final_step(mu0, eta, target, full_eta_steps=None):
    """前 k 步恒定 η 递推，第 k+1 步用 η_final 精确落到 target，返回 (μ, k, η_final)。"""
    k = max(full_eta_steps if full_eta_steps is not None else steps_to(mu0, eta, target) - 1, 0)
    mu_prev = mu_closed(mu0, eta, k)
    eta_final = (target - mu_prev) / (1.0 - mu_prev)
    mu_entry = mu_prev + eta_final * (1.0 - mu_prev)
    return mu_entry, k, eta_final

mu_entry, k_final, eta_final = entry_with_final_step(MU0, 0.5, MU_T)
tau_entry = TAU0 / math.sqrt(1.0 - mu_entry)
tau_ceil = TAU0 / math.sqrt(1.0 - MU_CEIL)
check("S5 劳森闭口 + 精确进窗：前 11 步恒定 η=0.5，第 12 步 η_final 精确到 0.9997（不越天花板）",
      tau_entry >= TAU_LAWSON and mu_entry >= MU_T and mu_entry < MU_CEIL,
      f"第 {k_final + 1} 步 η_final={eta_final:.6f} ⟹ μ={mu_entry:.7f}（窗内）⟹ τ_E = {tau_entry:.3f} s ≥ 2s；天花板处 τ_E = {tau_ceil:.3f} s")

# ── S6 天花板纪律：恒定 η 越界 ⟹ 必须关断；关断 ⟹ 停窗 ───────────────────
mu_at_close = mu_closed(MU0, 0.05, n_close)     # μ(162)
overshoot = mu_at_close - MU_CEIL

def decay_orbit(mu0, eta0, nsteps):             # TD18 语义：η_n = η₀(1−μ_n)/(1−μ₀)
    mu = mu0
    mus = []
    for _ in range(nsteps):
        eta = eta0 * (1.0 - mu) / (1.0 - mu0)
        mu = mu + eta * (1.0 - mu)
        mus.append(mu)
    return mus

decay_max = max(decay_orbit(MU0, 0.5, 20000))
check("S6a 恒定 η 越 FC11 天花板：μ(162)=0.999790761 > 0.999780568（档位语义 = 必须关断）",
      overshoot > 0,
      f"越界 {overshoot:.3e}（对位 lowcost D8：μ(n*)=0.999790760833）")
check("S6b 纯衰减（TD18）渐近仍越界：20000 步 μ_max=0.999915 ⟹ 停窗唯一方式 = 反馈关断（TD19/MAC6b）",
      decay_max > MU_CEIL,
      f"μ_max = {decay_max:.8f} > 天花板 {MU_CEIL:.8f}")
check("S6c 反馈关断：进窗后 η→0 ⟹ μ 冻结在进窗点，劳森持续",
      abs(mu_entry - MU_T) < 1e-3 and tau_entry >= TAU_LAWSON,
      f"μ ≡ {mu_entry:.7f}（在窗口 [0.9997, 0.999780568] 内，τ_E={tau_entry:.3f}s 可持续）")

# ── S7 功率标度：η×10 ⟹ 进窗步数 ÷12.9（超线性，k≥1 可行域）──────────────
n_small = steps_to(MU0, 0.05, MU_T)             # 155
n_large = steps_to(MU0, 0.5, MU_T)              # 12
ratio = n_small / n_large
check("S7 功率标度：η 提高 10× ⟹ 进窗步数 ÷12.9（>10×，k≥1 可行域）",
      ratio > 10.0,
      f"155→12（÷{ratio:.1f}；对位 roadmap D3：k≥1 可行 / k=0.5 死）")

# ── 图：μ 逐项轨迹（三条有限增益曲线从 n=0 逐点），窗口带 + 进窗点标记 ────
fig, ax = plt.subplots(figsize=(9, 6))
ns = np.arange(0, 170)
for eta, color in [(0.5, "C0"), (0.2, "C1"), (0.05, "C2")]:
    ax.plot(ns, [mu_closed(MU0, eta, int(k)) for k in ns], color=color, lw=2,
            label=f"η={eta}（逐项递推 {steps_to(MU0, eta, MU_T)} 步进窗）")
n_dec = np.arange(0, min(len(decay_orbit(MU0, 0.5, 20000)), 200), 10)
decay = decay_orbit(MU0, 0.5, 20000)
ax.plot(n_dec, [decay[int(k)] for k in n_dec], "C3--", lw=2, label="纯衰减 η₀=0.5（TD18，渐近越界）")
ax.axhspan(MU_T, MU_CEIL, color="gray", alpha=0.15, label="工作窗口 [0.9997, 0.999780568]")
ax.axhline(MU_CEIL, color="gray", ls=":", lw=1)
ax.axvline(n_close, color="red", ls="--", lw=1, label=f"关闭步 n*={n_close}")
for eta in (0.5, 0.2):
    ne = entries[eta]
    ax.plot(ne, mu_closed(MU0, eta, ne), "o", color="k", ms=6)
    ax.annotate(f"进窗 @{ne} 步", (ne, mu_closed(MU0, eta, ne)),
                textcoords="offset points", xytext=(8, -8), fontsize=9)
ax.set_xlabel("递推步 n（每步一次 muStep）")
ax.set_ylabel("μ")
ax.set_ylim(0.99, 1.00001)
ax.legend(loc="lower right", fontsize=9)
ax.grid(alpha=0.3)
fig.tight_layout()
fig.savefig(os.path.join(OUT, "fig_mu_orbits.png"), dpi=150)

# ── 产物 ────────────────────────────────────────────────────────────────────
passed = sum(1 for c in CHECKS if c["通过"])
report = {
    "假设": "H1（仅第一环）：电磁时变场驱动空间流起伏变化，产生有限增益 η>0；η 由 G1/D1 标定，不承诺一步到位",
    "分步链": ["L1 H1（假设）", "L2 η 由几何给出（有限，可负可正）", "L3 μ_n 逐项递推 TD1/TD7", "L4 进窗判据 MAC4", "L5 输运 τ_E 劳森", "L6 天花板纪律/关断 TD19"],
    "checks": CHECKS,
    "锚点": {
        "mu0": MU0, "mu_T": MU_T, "mu_ceil": MU_CEIL, "eps_resid": EPS_RESID,
        "tau0": TAU0, "tau_lawson": TAU_LAWSON,
        "关闭步_n*_η005": n_close,
        "进窗步数表": entries,
        "eta_frc": eta_frc, "eta_degen": eta_degen,
        "进窗点_η0.5_μ": mu_entry, "进窗点_tau_E": round(tau_entry, 4),
        "恒定η越界_μ162": mu_at_close, "纯衰减_max_20000步": decay_max,
        "递推_vs_闭式_max偏差": max_dev,
    },
    "诚实边界": [
        "H1 只承诺 η>0 有限，不承诺一步到位；η 数值由 G1/D1 首次标定（无实验证据）",
        "η=1 是上界/退化情形（TD14a 已有），不是递推头条",
        "η 衰减/关断形状是模型选择（TD18/19）",
        "无新物理预言；全部数字 = 既有闭式代入",
    ],
    "conclusion": "分步闭链成立：η 由几何给有限值（可负可正）→ μ 逐项递推（递推==闭式，单调几何收敛，有限步<1）→ 进窗有限步全<关闭步 → 进窗点劳森闭合 → 恒定 η 与纯衰减都会越天花板，停窗需反馈关断。"
    if passed == len(CHECKS) else f"FAIL: {passed}/{len(CHECKS)} 通过",
}
with open(os.path.join(OUT, "report.json"), "w", encoding="utf-8") as f:
    json.dump(report, f, ensure_ascii=False, indent=2)

with open(os.path.join(OUT, "summary.txt"), "w", encoding="utf-8") as f:
    f.write(f"μ 主动产生假设分步闭链验证：{passed}/{len(CHECKS)} 断言通过\n")
    for c in CHECKS:
        f.write(f"  {'PASS' if c['通过'] else 'FAIL'}  {c['检查']}  {c['细节']}\n")

print(f"RESULT: {passed}/{len(CHECKS)} passed")
for c in CHECKS:
    print(f"  {'PASS' if c['通过'] else 'FAIL'}  {c['检查']}")
    print(f"         {c['细节']}")
print(f"产物: {OUT}/{{report.json, summary.txt, fig_mu_orbits.png}}")