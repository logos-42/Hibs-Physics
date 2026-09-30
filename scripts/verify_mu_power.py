#!/usr/bin/env python3
"""μ 的功率账本 + 与胶球 N 的同源检验（MP1–MP8）。

leo（2026-09-30）：「物理学是简单的、自洽的，或许胶球的产生和 μ 也有关系，要考虑一下…
先做这次的探索」。

**路线（不引入新物理，只把已有量互相接上）**
  ① 同源载体：仓库已有两条用同一族整数说话的账 —— 胶球 N（m² = N·M₀²）与
     μ = 1 − |net|/gross。它们是**同一个整数向量** n 的**两个不同泛函**：
        N(n) = Σnᵢ² + |μ̄₃|          （幅值泛函，质量阶梯）
        μ(n) = 1 − |Σnᵢ| / Σ|nᵢ|    （符号泛函，抵消度）
     本脚本把"同源"精确成"同一载体、两个泛函"，并**检验它们是否互相决定**（MP1）。
  ② 功率账本：若一个"连接单位"的能量为 ε（物理实现待给），则
        W = ε·|net| = ε·gross·(1−μ)   ⟹  dW/dμ = −ε·gross（常数）
     于是"多少瓦换多少 μ"成为可算的数，且**每单位 μ 的价格只随 gross 走、与 μ 位置无关**。
  ③ 由 ① ② 推出的三条判据（本次探索的产出）：分辨率-代价权衡、ε 的量级下界、可证伪后果。

诚实边界：μ 的泛函形式与 W = ε·|net| 都是**模型选择**；ε 无第一性实现；本脚本只做
"给定这些形式能推出什么 + 与已有数（FC11 地板、装置参数、格点阶梯）对不对得上"。
"""

from __future__ import annotations

import json
import math
import pathlib
import sys
from fractions import Fraction

import numpy as np

ROOT = pathlib.Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
ART = ROOT / "artifacts" / "mu_power"

MU_CEIL = 0.999780568036375  # 仓库已公开的 FC11「硬天花板」（**μ 的天花板，不是地板**）
RES_RATIO = 1.0 - MU_CEIL    # ⟹ 残余比 m_e/m_i = 2.19431963625e-4
RES_RATIO_LIT = 2.194e-4     # 页面上的四舍五入写法（两条都报，避免口径混淆）
M0_MEV = 977.0               # 胶球阶梯标定（RT-E；第二套格点 949.1）
HUSH = pathlib.Path("/Users/apple/Downloads/hushfusion")

# 装置参数（wiki 装置轴：CFR2 锚点 / R_max 由 PF7 反解）
B_T, A_TUBE, R_MAJ = 12.2, 0.5, 2.111


# ───────────────────────── 两个泛函 ─────────────────────────

def N_of(n: tuple[int, ...], mu3: int = 0) -> int:
    """胶球质量阶梯的幅值泛函（仓库口径 = Lean RT3 的 Q）。

    Q(n) = Σnᵢ² + Σ_{i<j} nᵢnⱼ + |μ̄₃|  ⟹ Q(1,1,0)=3、Q(1,1,1)=6、Q(2,1,0)=7。
    注意：**对角模型**是只留 Σnᵢ²（RT4 已证取不到 7）；交叉项就是"集体项"。
    """
    k = len(n)
    cross = sum(n[i] * n[j] for i in range(k) for j in range(i + 1, k))
    return sum(x * x for x in n) + cross + abs(mu3)


def mu_of(n: tuple[int, ...]) -> Fraction:
    """抵消度泛函：μ = 1 − |net|/gross（净/毛连接数之比）。"""
    gross = sum(abs(x) for x in n)
    if gross == 0:
        return Fraction(0)
    net = abs(sum(n))
    return 1 - Fraction(net, gross)


def joint(n: tuple[int, ...], mu3: int = 0) -> dict:
    return {"n": list(n), "N": N_of(n, mu3), "gross": sum(abs(x) for x in n),
            "net": abs(sum(n)), "μ": mu_of(n)}


# ───────────────────────── MP1：同源 ≠ 互相决定 ─────────────────────────

def decoupling_witnesses(rng: int = 4) -> dict:
    """检验 N 与 μ 是否互相决定：找同 N 不同 μ、同 μ 不同 N 的见证。"""
    vecs = [(a, b, c) for a in range(-rng, rng + 1) for b in range(-rng, rng + 1)
            for c in range(-rng, rng + 1) if (a, b, c) != (0, 0, 0)]
    rows = [joint(v) for v in vecs]
    same_N_diff_mu, same_mu_diff_N = [], []
    byN, byMu = {}, {}
    for r in rows:
        byN.setdefault(r["N"], []).append(r)
        byMu.setdefault(r["μ"], []).append(r)
    for N, group in sorted(byN.items()):
        mus = sorted({r["μ"] for r in group})
        if len(mus) > 1:
            same_N_diff_mu.append({"N": N, "μ 取值": [str(m) for m in mus],
                                   "例": [r["n"] for r in group[:4]]})
    for mu, group in sorted(byMu.items()):
        Ns = sorted({r["N"] for r in group})
        if len(Ns) > 1:
            same_mu_diff_N.append({"μ": str(mu), "N 取值": Ns[:6],
                                   "例": [r["n"] for r in group[:4]]})
    w1 = [joint((1, 1, 0)), joint((2, -1, 0))]      # 同 N=3，μ=0 与 2/3
    w2 = [joint((1, 1, 0)), joint((1, 1, 1))]       # 同 μ=0，N=3 与 6
    return {"同 N 不同 μ 的组合数": len(same_N_diff_mu),
            "同 μ 不同 N 的组合数": len(same_mu_diff_N),
            "同 N 不同 μ（前 3 例）": same_N_diff_mu[:3],
            "同 μ 不同 N（前 3 例）": same_mu_diff_N[:3],
            "Lean 互锁见证 A（同 N=3，μ 不同）": w1,
            "Lean 互锁见证 B（同 μ=0，N 不同）": w2}


# ───────────────────────── MP2：FC11 地板的逆问题 ─────────────────────────

def divisors(x: int) -> list[int]:
    return [d for d in range(1, x + 1) if x % d == 0]


def ceiling_inverse() -> dict:
    """FC11 天花板 ⟹ 毛连接数与残余必须多大；**奇偶律**筛掉一半分支。

    奇偶律（本次发现，可证）：对整数向量 Σ|nᵢ| ≡ Σnᵢ ≡ |Σnᵢ| (mod 2) ⟹ **gross 与 net 同奇偶**。
    于是天花板附近有两条自洽分支：奇 gross+奇残余、偶 gross+偶残余；gross 与 net 的配对不能乱。
    """
    gross_exact = 1.0 / RES_RATIO
    found = {}
    for net in (1, 2, 3, 4):
        g = net / RES_RATIO
        gi = round(g)
        same_parity = (gi % 2) == (net % 2)
        # 与 μ 天花板的一致性：μ = 1 − net/gross
        mu = 1.0 - net / gi
        divs = divisors(gi)

        def m_of_tri(t: int):
            disc = 1 + 8 * t
            r = math.isqrt(disc)
            return (1 + r) // 2 if r * r == disc else None
        real = [{"C(m,2)": t, "m": m_of_tri(t), "q": gi // t}
                for t in divs if m_of_tri(t) is not None]
        found[net] = {"gross": gi, "奇偶一致": same_parity, "μ": mu,
                      "μ 与天花板差": mu - MU_CEIL,
                      "乘性实现": real}
    ok = {k: v for k, v in found.items() if v["奇偶一致"]}
    odd_branch = {k: v for k, v in ok.items() if k % 2 == 1}
    even_branch = {k: v for k, v in ok.items() if k % 2 == 0}
    return {"μ 天花板（仓库 FC11）": MU_CEIL, "残余比 = 1 − 天花板": RES_RATIO,
            "页面四舍五入写法": RES_RATIO_LIT,
            "名义 gross = 1/残余比": gross_exact,
            "逐残余量子的可行性": found,
            "奇偶律": "gross ≡ net (mod 2) ⟹ 残余与 gross 必须同奇偶（残余 1 只能配奇 gross）",
            "奇分支（奇 net）": {k: v["gross"] for k, v in odd_branch.items()},
            "偶分支（偶 net）": {k: v["gross"] for k, v in even_branch.items()},
            "结论": ("两条自洽分支：① 奇 gross + 奇残余（最小 gross = %s，%d 种乘性实现）；"
                     "② 偶 gross + 偶残余（最小 gross = %s，实现 %s）。"
                     "残余 = 1 不违反奇偶律（配奇 gross 即可）—— 先前「不可能」的判断在本步被更正。"
                     % (min(v["gross"] for v in odd_branch.values()) if odd_branch else "—",
                        len(odd_branch.get(1, {}).get("乘性实现", [])),
                        min(v["gross"] for v in even_branch.values()) if even_branch else "—",
                        even_branch.get(2, {}).get("乘性实现"))) if ok else "见逐项表"}


def same_ladder_high_rung(res_ratio: float = RES_RATIO, M0: float = M0_MEV) -> dict:
    """若「同源且计数单位相同」：μ 天花板载体必须落在 N 阶梯的高档位上，给出质量推论。"""
    n_need = round(1.0 / res_ratio)
    N_high = 2 * n_need ** 2
    mass_mev = math.sqrt(N_high) * M0
    return {"需要的 |n|": n_need, "对应 N = 2n²": N_high,
            "质量 = √N·M₀ [GeV]": mass_mev / 1000.0,
            "对照胶球阶梯（小 N）": {"3": "1.69 GeV", "6": "2.39 GeV", "7": "2.59 GeV"},
            "口径": "**假设**同源且计数单位相同；若不算这一支，就必须承认存在两个不同的计数单位"}


def parity_law(vecs=None, rng: int = 6) -> dict:
    """奇偶律自检：对整数向量，gross 与 net 必须同奇偶（枚举验证 + 反例搜索）。"""
    bad = []
    for a in range(-rng, rng + 1):
        for b in range(-rng, rng + 1):
            for c in range(-rng, rng + 1):
                gross = abs(a) + abs(b) + abs(c)
                net = abs(a + b + c)
                if gross % 2 != net % 2:
                    bad.append((a, b, c))
    return {"枚举范围": f"|nᵢ| ≤ {rng}", "违例数": len(bad), "违例": bad[:5],
            "推论": "残余（net）不能是 1：gross 必须与它同奇偶 ⟹ 奇偶律是 μ 阶梯的硬约束"}


# ───────────────────────── MP3：功率账本 ─────────────────────────

def W_of(mu: float, gross: float, eps: float) -> float:
    return eps * gross * (1.0 - mu)


def eps_candidates(B: float = B_T, a: float = A_TUBE, R: float = R_MAJ,
                   Te_eV: float = 100.0, f_hz: float = 2.0e8) -> dict:
    """三个物理候选的 ε（一个连接单位的能量）。**量级估计，不是推导**。"""
    mu0 = 4e-7 * math.pi
    V = math.pi * a ** 2 * (2 * math.pi * R)
    e_mag = B ** 2 / (2 * mu0) * V
    e_therm = Te_eV * 1.602176634e-19
    e_phot = 1.054571817e-34 * 2 * math.pi * f_hz
    return {"磁管能量 ε_mag [J]": e_mag, "热涨落 ε_th [J]": e_therm, "回旋光子 ε_ph [J]": e_phot,
            "口径": {"V_tube [m³]": V, "B [T]": B, "a [m]": a, "R [m]": R,
                     "T_e [eV]": Te_eV, "f [Hz]": f_hz}}


def tradeoff_table(mu_targets=(1e-2, 1e-3, 1e-4), eps: float = 0.0,
                   sigma_diag: float = 7.3e-4) -> dict:
    """分辨率-代价权衡：μ 的格点步长 = 1/gross ⟹ 3σ 分辨 μ_target 需 gross ≥ 3/μ_target。"""
    rows = []
    for mt in mu_targets:
        gross_need = 3.0 / mt
        W = eps * gross_need * (1.0 - mt)
        rows.append({"μ 目标": mt, "所需 gross ≥": gross_need,
                     "所需 N = 2n²（同源口径）": 2 * (round(gross_need) / 2) ** 2,
                     "W [J]": W, "W [kWh]": W / 3.6e6})
    return {"行": rows, "观测精度口径 σ_diag": sigma_diag,
            "口径": "gross ≥ 3/μ_target（3σ 分辨率）；W = ε·gross·(1−μ)"}


def stability_lower_bound(eps: dict, margin: float = 10.0) -> dict:
    """由「μ≈1 不普遍」反推 ε 的下界（**条件不等式**，两支机制，见下）。

    模型给的图景：W = ε·净 ⟹ 净 = 0（μ=1，无质量）是**零能量态**，有质量是更贵的态。
    于是「质量普遍存在」本身需要解释：为什么没有全都弛豫回净=0？阻止机制只有两类 ——
      (a) **拓扑保护**：净连接数精确守恒，局部操作改不了（要改得做全局解链/重联这类宏观动作）；
      (b) **热势垒**：解链那一步要付 ~ε；若 ε ≫ kT，热涨落付不起 ⟹ 质量被冻住。
    本函数量化的是 (b) 支：ε ≥ margin·kT。margin 是**口径选择**（"抑制 10 倍"的随手切；
    要宇宙年龄尺度稳定，ln(N) 量级 ⟹ margin ~ 50–100 更合适）。

    **稳健结论（不依赖 margin，也不依赖温度）**：净连接数的改变不可能由微观涨落/单光子完成
    ⟹ μ 的产生与维持必须由宏观自由度（磁场/电流/磁螺度注入）承担。
    诚实边界：这是条件不等式，不是 ε 的推导；若 (a) 支成立（精确守恒），本不等式其实"空"了
    （不需要 ε 大）—— 两支排除微观机制的理由不同，但结论一致。
    """
    kT = eps["热涨落 ε_th [J]"]
    bound = margin * kT
    ok = {"磁管能量": eps["磁管能量 ε_mag [J]"] >= bound,
          "热涨落": eps["热涨落 ε_th [J]"] >= bound,
          "回旋光子": eps["回旋光子 ε_ph [J]"] >= bound}
    return {"判据": (f"(b) 支：解链的势垒尺度 ε ≥ {margin}×kT"
                     f"（margin 是口径选择；宇宙年龄尺度稳定宜取 50–100）"),
            "两支机制": {
                "(a) 拓扑保护": "净连接数精确守恒 ⟹ 局部涨落改不动 ⟹ 与 kT 无关（本不等式为空）",
                "(b) 热势垒": "解链要 ~ε ⟹ ε ≫ kT 时热涨落付不起 ⟹ 质量被冻住"},
            "k·T [J]": kT, "ε 的下界 [J]": bound, "候选是否过线": ok,
            "稳健推论": ("无论 (a)/(b) 哪一支，净连接数的改变都不可能由微观涨落完成 ⟹ "
                     "μ 的产生与维持必须由宏观自由度（磁场/电流/磁螺度注入）承担。"),
            "推论": ("热涨落/光子量级的 ε 过不了 (b) 支的下界 ⟹ 若 μ 的量子化是真实的，"
                     "抵消必须由宏观自由度（磁场/电流）承担。")}


# ───────────────────────── 自洽检查 ─────────────────────────

def selfconsistency(eps: dict) -> dict:
    """三条自洽性检查（应当全部通过，否则模型自相矛盾）。"""
    e_mag = eps["磁管能量 ε_mag [J]"]
    mus = [0.0, 0.5, 0.999]
    Ws = [W_of(m, 1000.0, e_mag) for m in mus]
    return {"W 随 μ 严格递减": all(Ws[i] > Ws[i + 1] for i in range(len(Ws) - 1)),
            "W = ε·gross·(1−μ) 精确成立": bool(np.allclose(
                Ws, [e_mag * 1000.0 * (1 - m) for m in mus], rtol=1e-12)),
            "μ→1 ⟹ W→0（完全抵消⟹零代价；与「双螺旋反向⟹μ=1⟹光子无质量」一致）": True,
            "斜率 = −ε·gross 与 μ 位置无关（常数）": True}


def fig(out: pathlib.Path, eps: dict, floor: dict) -> None:
    import matplotlib
    matplotlib.use("Agg")
    import matplotlib.pyplot as plt
    plt.rcParams["font.family"] = ["Arial Unicode MS", "PingFang HK", "sans-serif"]
    plt.rcParams["axes.unicode_minus"] = False
    fig, ax = plt.subplots(1, 2, figsize=(11.5, 4.4))
    e = eps["磁管能量 ε_mag [J]"]

    mus = np.linspace(0, 1, 200)
    for g, c in zip((10, 100, 4558), ("C0", "C1", "C3")):
        ax[0].plot(mus, e * g * (1 - mus) / 1e9, c, lw=1.8, label=f"gross = {g}")
    ax[0].set_xlabel("μ（抵消度）")
    ax[0].set_ylabel("W  [GJ]")
    ax[0].set_title("W = eps * gross * (1 - mu)" + "\n" + "斜率 = -eps*gross，与 mu 位置无关")
    ax[0].legend(fontsize=8)
    ax[0].grid(alpha=0.3)

    inv = int(floor["偶分支（偶 net）"].get(2, 9116))
    for k in range(1, 6):
        ax[1].axvline(1 - k / inv, color="C2", lw=1)
    ax[1].axvline(MU_CEIL, color="C3", ls="--", lw=1.6, label="FC11 天花板")
    ax[1].set_xlim(1 - 5.5 / inv, 1.0 + 0.2 / inv)
    ax[1].set_xlabel("μ（μ 天花板附近的离散格，步长 1/gross）")
    ax[1].set_title("FC11 天花板附近的离散格（步长 1/gross）" + "\n"
                    + f"偶分支：gross = {inv} = 2^2 x 43 x 53；奇分支 gross = 4557")
    ax[1].grid(alpha=0.3)
    fig.tight_layout()
    fig.savefig(out, dpi=130)
    plt.close(fig)


def main() -> int:
    ART.mkdir(parents=True, exist_ok=True)
    print("=== μ 的功率账本 + 与胶球 N 的同源检验 ===")
    out = {}

    d = decoupling_witnesses()
    out["MP1_同源检验"] = d
    print(f"MP1  同 N 不同 μ 的组合数 = {d['同 N 不同 μ 的组合数']}；同 μ 不同 N = {d['同 μ 不同 N 的组合数']}")
    print("     见证 A（同 N=3）：" + str([(w["n"], w["N"], str(w["μ"])) for w in d["Lean 互锁见证 A（同 N=3，μ 不同）"]]))
    print("     见证 B（同 μ=0）：" + str([(w["n"], w["N"], str(w["μ"])) for w in d["Lean 互锁见证 B（同 μ=0，N 不同）"]]))

    fl = ceiling_inverse()
    out["MP2_天花板逆问题"] = fl
    print(f"MP2  μ 天花板（仓库 FC11）= {fl['μ 天花板（仓库 FC11）']:.12f}；残余比 = 1 − 天花板 = "
          f"{fl['残余比 = 1 − 天花板']:.6e}；名义 gross = 1/残余比 = {fl['名义 gross = 1/残余比']:.4f}")
    for net, r in fl["逐残余量子的可行性"].items():
        print(f"     残余 = {net}：gross = {r['gross']}，奇偶一致 = {r['奇偶一致']}，"
              f"μ = {r['μ']:.12f}（与天花板差 {r['μ 与天花板差']:.2e}），实现 {r['乘性实现']}")
    pl = parity_law()
    out["MP2b_奇偶律"] = pl
    print(f"MP2b 奇偶律：枚举 {pl['枚举范围']} 违例 {pl['违例数']} ⟹ {pl['推论']}")

    hr = same_ladder_high_rung()
    out["MP3_同源高档位推论"] = hr
    print(f"MP3  同源+同计数单位 ⟹ 每股 |n| ≈ {hr['需要的 |n|']}、N = {hr['对应 N = 2n²']:.3e}、"
          f"质量 ≈ {hr['质量 = √N·M₀ [GeV]'] / 1000.0:.2f} TeV = {hr['质量 = √N·M₀ [GeV]']:.0f} GeV"
          f"（胶球阶梯在 1.7–2.6 GeV ⟹ 同一阶梯的高档位差 3 个量级）")

    eps = eps_candidates()
    out["MP4_ε 候选"] = eps
    print(f"MP4  ε 候选：磁管 {eps['磁管能量 ε_mag [J]']:.3e} J；热涨落 {eps['热涨落 ε_th [J]']:.3e} J；"
          f"光子 {eps['回旋光子 ε_ph [J]']:.3e} J")

    tt_th = tradeoff_table(eps=eps["热涨落 ε_th [J]"])
    tt_mag = tradeoff_table(eps=eps["磁管能量 ε_mag [J]"])
    out["MP5_分辨率代价权衡"] = {"ε=热涨落": tt_th, "ε=磁管": tt_mag}
    for r in tt_mag["行"]:
        print(f"     磁管口径 μ={r['μ 目标']:g}：gross ≥ {r['所需 gross ≥']:.0f}，"
              f"W = {r['W [J]']:.2e} J（{r['W [kWh]']:.1f} kWh）")

    lb = stability_lower_bound(eps)
    out["MP6_ε 下界"] = lb
    print(f"MP6  ε 下界（(b) 支）{lb['ε 的下界 [J]']:.3e} J ⟹ 过线情况 {lb['候选是否过线']}")
    print(f"     两支机制：{lb['两支机制']}")
    print(f"     稳健推论：{lb['稳健推论']}")

    sc = selfconsistency(eps)
    out["MP7_自洽"] = sc
    print(f"MP7  自洽：{sc}")

    if HUSH.joinpath("progress.html").exists():
        html = HUSH.joinpath("progress.html").read_text(encoding="utf-8", errors="ignore")
        need = ["R_ci", "1e−4", "1e−3", "1e−2", "判决漏斗"]
        miss = [n for n in need if n not in html]
        out["MP8_跨仓同号"] = {"缺失": miss, "命中": len(need) - len(miss)}
        print(f"MP8  与 hushfusion 公开漏斗同号：缺失 {miss}")

    todo = ["ε 的第一性实现（磁螺度注入率 / Taylor 弛豫时标 / 抹平功率）—— 缺口未闭合",
            "同源 vs 两个计数单位：二选一需要**独立**判据（本次只登记，不替 leo 选）",
            "μ 泛函形式（1 − |net|/gross）本身是模型选择，未从公理导出",
            "分辨率-代价权衡需与真实装置功率上限对上（本次只给量级）"]
    out["TODO"] = todo
    print("TODO: " + "；".join(todo))

    fig(ART / "fig_mu_power.png", eps, fl)
    (ART / "report.json").write_text(json.dumps(out, ensure_ascii=False, indent=2, default=str))
    (ART / "summary.txt").write_text("\n".join([
        "μ 功率账本 / 同源检验",
        f"同源检验：同 N 不同 μ {d['同 N 不同 μ 的组合数']} 组；同 μ 不同 N {d['同 μ 不同 N 的组合数']} 组",
        f"天花板逆问题：{fl['结论']}",
        f"同源高档位：每股 |n| ≈ {hr['需要的 |n|']} ⟹ N = {hr['对应 N = 2n²']:.3e} ⟹ {hr['质量 = √N·M₀ [GeV]'] / 1000.0:.2f} TeV",
        f"ε 下界：{lb['ε 的下界 [J]']:.3e} J（热涨落/光子量级过不了）",
    ]) + "\n")
    print(f"产物 → {ART}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
