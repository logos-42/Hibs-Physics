#!/usr/bin/env python3
"""「以太」层级：集体频率带 / 瞬时相关 / 两种超光速（AetherBand AB1–AB18 数值同位体）

═════ 动机（leo 2026-10-29 原话）═════
「宇宙的本身是振动频率和维度的超广阔的集体，在局域频率较低且不一致的时候，
 会有波动现象，比如光速和空间涟漪，超广意场是范围更大的，所以可以瞬时影响彼此，
 远比光速要快，因为光速是空间流动速度的等效，实际上，超广意场观下，有更快的方式。」

形式化落点（Lean: ProjectionPhysics/Explorations/AetherBand.lean，零 sorry）：
  AB1/AB2  相位速度 v_ph = ω/k 随 k→0 无界（「越广越快」的代数内核）
  AB3      相位滞后 k·d 可任意小（「瞬时影响」= 共相位，不是信号）
  AB4/AB5  同步（共相位）是等价关系；k=0 集体模 ⟹ 处处同步
  AB6      k>0 且 d>0 ⟹ 有相位梯度 = 有波（局域频率不一致 ⟹ 波动）
  AB7/AB8  零带宽 ⟺ 常数 ⟹ 不可传信
  AB9/AB10 容量 C = d·B·log2(1+SNR) 在 B=0 处为 0；对维度线性、单模速率不变
  AB11     拖曳型超光速 1+v（GQC3 已有）· AB12–AB14 层级型 c2 = ratio·c 的生死线
  AB15     两机制在单点等效速度上不可区分（死法）
  AB17/AB18 k=0 ⟹ ω=0（瞬时 ⟹ 静态）；范围×更新率 (L·ω < c·ε)

═════ 断言（N1–N7，每条对位一条 Lean 定理）═════
  N1 ★★ 相位速度无界（AB1/AB2）
  N2 ★★ 「广」的代价：瞬时覆盖 L 需 k ≤ ε/L（AB3）
  N3 ★★★ 范围×更新率上界：L·ω_max = c·ε 为常数（AB18）——「更快」的价格表
  N4 ★★ 零带宽⟹零容量 + 维度只增容量（AB9/AB10）
  N5 ★★★ 两锥生死线：ratio=1 ⟹ 差 0（无新速度）；ratio≠1 ⟹ 差>0（AB12–AB14）
  N6-AB ★★ 两机制不可区分（沿流），各向异性才是唯一分辨通道（AB15）
  N7 ★★ 瞬时⟹静态：v_ph 发散而 ω→0，乘积恒为常数（AB17）

═════ 诚实边界（写死）═════
  · 全部数字 = 初等代数/傅里叶关系代入；本脚本**不**证明宇宙是振动的，也不证明
    存在快于 c 的影响 —— 它只给两条互斥分支各自的判据。
  · 分支Ⅰ（同一场的 k→0 模）：瞬时成立、传信不成立、**零新物理**。
  · 分支Ⅱ（独立层，c2 = ratio·c）：需要一条新公设 + 一个新的无量纲比 ratio
    （与 M₀/λ 同款输入缺口）；ratio 若能由 P1–P4 导出，则缺口关闭。
  · 「瞬时」一律读作共相位/同时面，不读作传比特（paper3 死法 (c)）。
  · 无新可检验预言：N3/N6 是**判据形状**，不是新数值预言。

产物：artifacts/aetherband/{report.json, summary.txt, fig_*.png}
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
OUT = os.path.join(REPO, "artifacts", "aetherband")
os.makedirs(OUT, exist_ok=True)

CHECKS = []


def check(name, ok, detail):
    CHECKS.append({"检查": name, "通过": bool(ok), "细节": detail})


C_MED = 1.0        # 介质等效速度（c = 1 单位）
EPS = 1e-3         # 相位分辨率口径（ε）

# ── N1 ★★ 相位速度无界（AB1/AB2）───────────────────────────────────────────
omega = 1.0
ks = np.array([1.0, 1e-1, 1e-2, 1e-3, 1e-4, 1e-5, 1e-6])
v_ph = omega / ks
mono = bool(np.all(np.diff(v_ph) > 0))
check("N1 ★★ 相位速度 v_ph=ω/k 随 k→0 严格增且无界（AB1/AB2）",
      mono and v_ph[-1] >= 1e6 - 1e-6,
      f"k={ks[-1]:.0e} ⟹ v_ph={v_ph[-1]:.3e}（单调={mono}）")

# ── N2 ★★ 「广」的代价：k ≤ ε/L（AB3）──────────────────────────────────────
Ls = np.array([1.0, 1e3, 1e6, 1e9])
k_max = EPS / Ls
lag = k_max * Ls
check("N2 ★★ 瞬时覆盖距离 L 需 k ≤ ε/L（相位滞后 = ε，机器精度）（AB3）",
      bool(np.all(np.abs(lag - EPS) <= 1e-18 + 1e-12 * EPS)),
      "L=" + ", ".join(f"{L:.0e}→k_max={k:.2e}" for L, k in zip(Ls, k_max)))

# ── N3 ★★★ 范围 × 更新率上界（AB18）────────────────────────────────────────
omega_max = C_MED * EPS / Ls
prod = omega_max * Ls
check("N3 ★★★ 范围×更新率：L·ω_max = c·ε 恒定（AB18，「更快」的价格表）",
      bool(np.all(np.abs(prod - C_MED * EPS) <= 1e-15 * max(C_MED * EPS, 1e-30))),
      "L·ω_max = " + ", ".join(f"{p:.6e}" for p in prod) + f"（c·ε = {C_MED*EPS:.6e}）")

# ── N4 ★★ 零带宽⟹零容量；维度只增容量（AB9/AB10）──────────────────────────
def capacity(dim, B, snr):
    return dim * B * (math.log(1.0 + snr) / math.log(2.0))


snr = 10.0
Bs = [0.0, 0.1, 1.0, 10.0]
caps = [capacity(1, B, snr) for B in Bs]
cap_d3 = capacity(3, Bs[2], snr)
cap_d1 = capacity(1, Bs[2], snr)
per_mode = [cap / d for cap, d in ((cap_d1, 1), (cap_d3, 3))]
check("N4 ★★ 带宽 0 ⟹ 容量 0；容量对维度线性、单模速率不变（AB9/AB10）",
      caps[0] == 0.0 and abs(cap_d3 - 3 * cap_d1) <= 1e-15 * cap_d3
      and abs(per_mode[0] - per_mode[1]) <= 1e-15 * per_mode[0],
      f"C(B=0)={caps[0]:.1f}；C(d=3)={cap_d3:.4f}=3×C(d=1)={3*cap_d1:.4f}；"
      f"单模速率 {per_mode[0]:.4f} vs {per_mode[1]:.4f}")

# ── N5 ★★★ 两锥生死线（AB12–AB14）─────────────────────────────────────────
ratios = [1.0, 1.5, 3.0]
c2 = [r * C_MED for r in ratios]
delta = [x - C_MED for x in c2]
check("N5 ★★★ ratio=1 ⟹ 两锥重合（差 0，无新速度）；ratio≠1 ⟹ 差>0（AB12–AB14）",
      delta[0] == 0.0 and all(d > 0 for d in delta[1:]),
      "ratio=" + ", ".join(f"{r}→c2={x:.2f}（Δ={d:+.2f}）" for r, x, d in zip(ratios, c2, delta)))

# ── N6-AB ★★ 两机制不可区分（沿流）；各向异性是唯一分辨通道（AB15）───────────────
v_drag = 0.5
along_drag = 1.0 + v_drag     # 拖曳：沿流
perp_drag = 1.0               # 拖曳：垂直
ratio_coarse = 1.5
along_coarse = ratio_coarse * C_MED
perp_coarse = ratio_coarse * C_MED
check("N6-AB ★★ 单点等效速度两机制不可区分；各向异性才分辨（AB15）",
      abs(along_drag - along_coarse) == 0.0 and abs(perp_drag - perp_coarse) == 0.5,
      f"沿流 拖曳={along_drag:.2f} vs 层级={along_coarse:.2f}（差 0）；"
      f"垂直 拖曳={perp_drag:.2f} vs 层级={perp_coarse:.2f}（差 {abs(perp_drag-perp_coarse):.2f}）")

# ── N7 ★★ 瞬时 ⟹ 静态（AB17）──────────────────────────────────────────────
k_sweep = np.array([1e-1, 1e-2, 1e-3, 1e-4, 1e-5, 1e-6])
vph_fixed_omega = 1.0 / k_sweep            # 固定 ω = 1：相位速度发散
omega_disp = C_MED * k_sweep               # 线性色散 ω = c·k：频率趋于 0
prod7 = vph_fixed_omega * omega_disp
check("N7 ★★ 瞬时 ⟹ 静态：v_ph→∞ 而 ω→0，v_ph·ω 恒为常数（AB17）",
      bool(np.all(np.diff(vph_fixed_omega) > 0)) and bool(np.all(np.diff(omega_disp) < 0))
      and bool(np.all(np.abs(prod7 - 1.0) <= 1e-15)),
      f"k=1e-6：v_ph={vph_fixed_omega[-1]:.1e}，ω={omega_disp[-1]:.1e}，v_ph·ω={prod7[-1]:.15f}")

# ═════════════════════ 图 ═════════════════════
# 图 1：相位速度 vs 波矢（无界） + 瞬时⟹静态的双轴
fig, ax1 = plt.subplots(figsize=(7.2, 4.6))
ax1.loglog(ks, v_ph, "o-", color="C0", label="v_ph = ω/k（ω=1）")
for i, L in enumerate((1.0, 1e3, 1e6)):
    ax1.axvline(EPS / L, ls=":", color="0.6", lw=0.9)
    ax1.annotate(f"覆盖 L={L:.0e}\n需 k≤{EPS/L:.0e}", (EPS / L, 0.33), fontsize=7,
                 color="0.35", ha="left" if L > 1e5 else "center", va="bottom")
ax1.set_xlim(1.2e-10, 2.0)
ax1.set_ylim(0.3, 3e6)
ax1.set_xlabel("波矢 k（越小 = 越「广」）")
ax1.set_ylabel("相位速度 v_ph", color="C0")
ax1.tick_params(axis="y", labelcolor="C0")
ax1.grid(alpha=0.3, which="both")
ax2 = ax1.twinx()
ax2.loglog(k_sweep, omega_disp, "s--", color="C3", label="ω = c·k（色散）")
ax2.set_ylabel("角频率 ω", color="C3")
ax2.tick_params(axis="y", labelcolor="C3")
ax1.set_title("「越广越快」与「越广越静」是同一件事的两面（AB1/AB2 与 AB17）")
fig.tight_layout()
fig.savefig(os.path.join(OUT, "fig_speed_unbounded.png"), dpi=150)
plt.close(fig)

# 图 2：范围 × 更新率上界
fig, ax = plt.subplots(figsize=(7.2, 4.4))
ax.loglog(Ls, omega_max, "o-", color="C2")
for i, (L, w) in enumerate(zip(Ls, omega_max)):
    left_side = i == len(Ls) - 1
    ax.annotate(f"ω_max={w:.1e}", (L, w), textcoords="offset points",
                xytext=(-8, 10) if left_side else (6, -12), fontsize=8,
                ha="right" if left_side else "left")
ax.set_xlabel("同步覆盖距离 L")
ax.set_ylabel("可承载的最大角频率 ω_max")
ax.set_title(f"范围 × 更新率封顶：L·ω_max = c·ε（ε={EPS:g}, c=1）（AB18）")
ax.grid(alpha=0.3, which="both")
fig.tight_layout()
fig.savefig(os.path.join(OUT, "fig_reach_rate.png"), dpi=150)
plt.close(fig)

# 图 3：容量 vs 带宽（维度只改斜率）
fig, ax = plt.subplots(figsize=(7.2, 4.4))
Bgrid = np.linspace(0, 10, 101)
for d, st in ((1, "-"), (2, "--"), (3, ":")):
    ax.plot(Bgrid, [capacity(d, B, snr) for B in Bgrid], st, label=f"维度 d={d}")
ax.axvline(0, color="k", lw=0.8)
ax.plot([0], [0], "o", color="C3", ms=7)
ax.annotate("B = 0 → C = 0（瞬时通道没有容量）", (0, 0), textcoords="offset points",
            xytext=(10, 12), fontsize=9, color="C3")
ax.set_xlabel("带宽 B")
ax.set_ylabel("信道容量 C")
ax.set_title(f"维度只增容量、不改单模速度（SNR={snr:g}）（AB9/AB10）")
ax.legend()
ax.grid(alpha=0.3)
fig.tight_layout()
fig.savefig(os.path.join(OUT, "fig_capacity_dim.png"), dpi=150)
plt.close(fig)

# 图 4：两种「超光速」的数值不可区分 / 各向异性可分辨
fig, ax = plt.subplots(figsize=(7.0, 4.4))
labels = ["沿流方向", "垂直方向"]
drag_vals = [along_drag, perp_drag]
coarse_vals = [along_coarse, perp_coarse]
x = np.arange(2)
ax.bar(x - 0.18, drag_vals, 0.36, label=f"拖曳型 1+v（v={v_drag}）", color="C0")
ax.bar(x + 0.18, coarse_vals, 0.36, label=f"层级型 ratio（ratio={ratio_coarse}）", color="C1")
for i in range(2):
    ax.annotate(f"{drag_vals[i]:.2f}", (i - 0.18, drag_vals[i]), ha="center", va="bottom", fontsize=9)
    ax.annotate(f"{coarse_vals[i]:.2f}", (i + 0.18, coarse_vals[i]), ha="center", va="bottom", fontsize=9)
ax.set_xticks(x)
ax.set_xticklabels(labels)
ax.set_ylabel("静止系等效速度（c=1）")
ax.set_ylim(0, 2.1)
ax.set_title("单点测速不可分辨两机制；各向异性是唯一分辨通道（AB15）")
ax.legend(loc="upper center", ncol=2, fontsize=9, framealpha=0.9)
ax.grid(alpha=0.3, axis="y")
fig.tight_layout()
fig.savefig(os.path.join(OUT, "fig_two_cones_directional.png"), dpi=150)
plt.close(fig)

passed = sum(1 for c in CHECKS if c["通过"])
report = {
    "假设（leo 2026-10-29）": "宇宙是振动频率与维度的超广阔集体；局域频率低且不一致 ⟹ 波动（光速、空间涟漪）；"
                            "超广意场范围更大 ⟹ 可瞬时彼此影响，快于光速；光速 = 空间流动速度的等效",
    "Lean": "ProjectionPhysics/Explorations/AetherBand.lean AB1–AB18（零 sorry）",
    "checks": CHECKS,
    "结果": {
        "相位速度_表": {f"{k:.0e}": float(v) for k, v in zip(ks, v_ph)},
        "覆盖距离与所需波矢": {f"{L:.0e}": float(k) for L, k in zip(Ls, k_max)},
        "范围×更新率_omega_max": {f"{L:.0e}": float(w) for L, w in zip(Ls, omega_max)},
        "L·omega_max_常数": float(prod[0]),
        "容量_表": {"B=" + str(B): float(c) for B, c in zip(Bs, caps)},
        "两锥": {"ratio": ratios, "c2": c2, "Δ": delta},
        "各向异性": {"沿流_拖曳": along_drag, "沿流_层级": along_coarse,
                     "垂直_拖曳": perp_drag, "垂直_层级": perp_coarse},
        "瞬时⟹静态": {"k": k_sweep.tolist(), "v_ph": vph_fixed_omega.tolist(),
                       "omega": omega_disp.tolist()},
    },
    "锚点": {
        "v_ph_在 k=1e-6（ω=1）": float(v_ph[-1]),
        "L·ω_max 常数（= c·ε）": float(prod[0]),
        "容量 C(B=0)": float(caps[0]),
        "容量 C(d=3)/C(d=1)": float(cap_d3 / cap_d1),
        "两锥 Δ（ratio=1,1.5,3）": [float(d) for d in delta],
        "各向异性 垂直差 |拖曳−层级|": float(abs(perp_drag - perp_coarse)),
        "v_ph·ω 常数（AB17）": float(prod7[-1]),
    },
    "判据（可判死）": {
        "分支Ⅰ（同一场的 k→0 模）": "瞬时成立、传信不成立、零新物理；若某集体模能在 k=0 携带"
                                     "随时间变化的可分辨符号 ⟹ AB7/AB8 死",
        "分支Ⅱ（独立层 c2=ratio·c）": "需要新公设 + 新的无量纲比 ratio；若 ratio 能由 P1–P4 导出 ⟹ 缺口关闭；"
                                       "若观测到的「快」既非 1+v 也非 ratio ⟹ 两分支皆死",
        "实验分辨": "AB15：单点等效速度两机制同值（1.5），只有各向异性（拖曳 {1.5,1.0} vs 层级 {1.5,1.5}）可分辨",
    },
    "诚实边界": [
        "全部数字 = 初等代数/傅里叶关系代入；不证明宇宙是振动的，也不证明存在快于 c 的影响",
        "「瞬时」一律读作共相位/同时面，不读作传比特（paper3 死法 (c)）",
        "分支Ⅱ的 ratio 是新的无量纲输入（与 M₀/λ 同款），未闭合",
        "无新可检验预言：N3/N6-AB 是判据形状，不是新数值预言",
    ],
    "conclusion": "「越广越快」在相位速度层成立且无界（AB2），但同一条路把频率带到 0（AB17）⟹ "
                  "瞬时相关没有信道容量（AB9）；真正「更快」只能是独立的一层（c2=ratio·c，AB13/AB14），"
                  "其价格是一个新的无量纲比 ratio，其分辨通道是各向异性（AB15）。"
    if passed == len(CHECKS) else f"FAIL: {passed}/{len(CHECKS)} 通过",
}
with open(os.path.join(OUT, "report.json"), "w", encoding="utf-8") as f:
    json.dump(report, f, ensure_ascii=False, indent=2)
with open(os.path.join(OUT, "summary.txt"), "w", encoding="utf-8") as f:
    f.write(f"「以太」层级 AetherBand 数值验证：{passed}/{len(CHECKS)} 断言通过\n")
    for c in CHECKS:
        f.write(f"  {'PASS' if c['通过'] else 'FAIL'}  {c['检查']}  {c['细节']}\n")

print(f"RESULT: {passed}/{len(CHECKS)} passed")
for c in CHECKS:
    print(f"  {'PASS' if c['通过'] else 'FAIL'}  {c['检查']}")
    print(f"         {c['细节']}")
print(f"产物: {OUT}/{{report.json, summary.txt, fig_*.png}}")
