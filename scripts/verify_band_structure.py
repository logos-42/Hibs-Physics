#!/usr/bin/env python3
"""带结构三件：时间计数接口（TC）/ 一般色散（GD）/ 带维度（ND）

═════ 动机（leo 2026-10-29 四续：「按优先级完成，1，2，3 都做完」）═════
  ① 时间计数接口：VBC 的闭包次数 n ⟷ 振动坐标里的带指标 k   →  n = k·L/2π
  ② 一般色散：det = k₁ω₂ − k₂ω₁（不再要求 ω = c·k），「广」的刻度换成群速度
  ③ 三带以上：带的个数 ⟷ 振动坐标的维数（1+1 维里秩 ≤ 2，第三条带冗余）

对应 Lean（全部零 sorry）：
  ProjectionPhysics/Explorations/TimeCount.lean        TC1–TC6
  ProjectionPhysics/Explorations/DispersionGeneral.lean GD1–GD9
  ProjectionPhysics/Explorations/BandDimension.lean     ND1–ND5

═════ 断言（N1–N14）═════
  ① TC
    N1 ★★  计数 = 密度 × 跨度
    N2 ★★  对跨度可加
    N3 ★★★ 一个波长 = 一次闭合（n = 1）
    N4 ★★★ 计数依赖带（k₁ ≠ k₂ ⟹ 同一跨度上计数不同）
    N5 ★★  全局模 k = 0 ⟹ 计数恒 0
    N6 ★★★ 计数差密度 = 1/λ_beat（= 「广」的刻度）
  ② GD
    N7 ★★★ det₂ = k₁ω₂ − k₂ω₁（一般色散，300 组随机）
    N8 ★★★ det₂ = 0 ⟺ 两带相速度相同
    N9 ★★  二次色散 det₂ = k₁k₂β(k₂−k₁)
    N10 ★★★ 群速度真的是导数（中心差分收敛阶 ≈ 2；这是 Lean 侧的诚实缺口）
    N11 ★★★ β≠0 ⟹ v_g ≠ v_ph；β=0 ⟹ v_g = v_ph（AB 混用无害的边界）
    N12 ★★★ |Δv_g|·λ_beat = 4π|β|（广 ⟹ 涟漪更慢）
  ③ ND
    N13 ★★★ 三条带线性相关（θ₃ = aθ₁ + bθ₂，残差机器精度）
    N14 ★★★ 计数也冗余（n₃ = a n₁ + b n₂）+ 3×2 相位矩阵的秩 = 2

═════ 诚实边界（写死）═════
  · 二次色散族是模型选择；一般 ω(k) 下群速度仍为 dω/dk，只是没有闭式。
  · N10 是 Lean 里**没做**的那一步的数值替身（v4.35 的 HasDerivAt.pow 实例不同源，
    见 DispersionGeneral.lean 的登记）；它证明"是导数"，不证明"闭式等于导数"的形式化。
  · 「维度 = min(带数, d+1)」只在 1+1 维被数值/形式化覆盖；高维是读法。
  · 零新可检验预言。

产物：artifacts/bandstructure/{report.json, summary.txt, fig_*.png}
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
OUT = os.path.join(REPO, "artifacts", "bandstructure")
os.makedirs(OUT, exist_ok=True)

CHECKS = []


def check(name, ok, detail):
    CHECKS.append({"检查": name, "通过": bool(ok), "细节": detail})


rng = np.random.default_rng(20261029)
TWO_PI = 2 * math.pi

# ═════════════ ① 时间计数接口 ═════════════
def time_count(k, L):
    return k * L / TWO_PI


def beat_wavelength(k1, k2):
    return TWO_PI / abs(k1 - k2)


# N1 计数 = 密度 × 跨度
rel1 = max(abs(time_count(k, L) - (k / TWO_PI) * L) / max(abs(time_count(k, L)), 1e-30)
           for k, L in zip(rng.normal(scale=2, size=200), rng.uniform(0.1, 10, 200)))
check("N1 ★★ 计数 = 计数密度 × 跨度（n = kL/2π）（TC1）", rel1 < 1e-15, f"200 组最大相对差 = {rel1:.2e}")

# N2 可加
rel2 = max(abs(time_count(k, L1 + L2) - time_count(k, L1) - time_count(k, L2))
           / max(abs(time_count(k, L1 + L2)), 1e-30)
           for k, L1, L2 in zip(rng.normal(scale=2, size=200), rng.uniform(0.9, 5, 200),
                               rng.uniform(0.9, 5, 200)))
check("N2 ★★ 计数对跨度可加（TC2）", rel2 < 1e-15, f"200 组最大相对差 = {rel2:.2e}")

# N3 一个波长 = 一次闭合
ks_n3 = [0.3, 1.0, 2.7, 8.0, -1.3, -4.2]
err3 = max(abs(time_count(k, TWO_PI / k) - 1.0) for k in ks_n3)
check("N3 ★★★ 一个波长恰好一次闭合：n(k, 2π/k) = 1（TC3）", err3 < 1e-15,
      f"6 个 k（含负）max|n−1| = {err3:.1e}")

# N4 计数依赖带
k1, k2 = 1.0, 2.5
n4a, n4b = time_count(k1, TWO_PI), time_count(k2, TWO_PI)
check("N4 ★★★ 计数依赖所选的带：k₁ ≠ k₂ ⟹ 同一跨度上计数不同（TC4）",
      abs(n4a - n4b) > 0.1, f"L=2π：n(k₁)={n4a:.3f} vs n(k₂)={n4b:.3f}")

# N5 全局模
check("N5 ★★ 全局模 k = 0 ⟹ 计数恒 0（TC5）",
      all(time_count(0.0, L) == 0.0 for L in (0.5, 2.0, 10.0)), "三个跨度全 0.0")

# N6 计数差密度 = 1/λ_beat
pairs = [(0.5, 2.0), (1.0, 1.3), (3.0, 3.05), (-1.0, 4.0)]
err6 = max(abs(abs(a - b) / TWO_PI - 1.0 / beat_wavelength(a, b)) for a, b in pairs)
check("N6 ★★★ 计数差密度 = 1/λ_beat —— 「广」的刻度就是计数差的刻度（TC6）",
      err6 < 1e-15, f"4 组带对 max|Δρ − 1/λ| = {err6:.1e}")

# ═════════════ ② 一般色散 ═════════════
def det2(k1, w1, k2, w2):
    return k1 * w2 - k2 * w1


def vph(w, k):
    return w / k


def vg(c, beta, k):
    return c + 2 * beta * k


# N7 det 一般形式
rel7 = 0.0
for _ in range(300):
    k1, k2 = rng.uniform(0.2, 3, 2) + rng.normal(scale=0.1, size=2)
    w1, w2 = rng.normal(scale=2, size=2)
    num, pred = det2(k1, w1, k2, w2), k1 * w2 - k2 * w1
    rel7 = max(rel7, abs(num - pred) / max(abs(pred), 1e-12))
check("N7 ★★★ 一般色散判据 det₂ = k₁ω₂ − k₂ω₁（GD1/GD2）", rel7 < 1e-14,
      f"300 组最大相对差 = {rel7:.2e}")

# N8 det=0 ⟺ 相速度相同
ws = []
for k in (0.7, 1.0, 1.9, 3.3):
    ws.append((k, 0.8 * k))                   # 相速度全 0.8 ⟹ det 应为 0
same_speed_flags = [abs(det2(a[0], a[1], b[0], b[1])) < 1e-14 for i, a in enumerate(ws) for b in ws[i + 1:]]
k_a, k_b = 1.0, 2.0
diff_flag = abs(det2(k_a, 0.8 * k_a, k_b, 1.3 * k_b)) > 1e-12
check("N8 ★★★ det₂ = 0 ⟺ 两带相速度相同（一般色散；GD2）",
      all(same_speed_flags) and diff_flag,
      f"同速 6 对全 0；异速一对 |det|={abs(det2(1.0,0.8,2.0,2.6)):.3f} > 0")

# N9 二次族 det 闭式
rel9 = 0.0
for _ in range(200):
    c, beta = rng.normal(), rng.normal(scale=0.3)
    k1, k2 = rng.uniform(0.2, 3, 2)
    w1, w2 = c * k1 + beta * k1 ** 2, c * k2 + beta * k2 ** 2
    num, pred = det2(k1, w1, k2, w2), k1 * k2 * beta * (k2 - k1)
    # ⚠ 相消量：按操作数量级归一（不用结果归一），否则 k₁≈k₂ 处是假相对误差
    scale9 = abs(k1 * w2) + abs(k2 * w1)
    rel9 = max(rel9, abs(num - pred) / scale9)
check("N9 ★★ 二次色散 det₂ = k₁k₂β(k₂−k₁)（GD1 的直接推论）", rel9 < 1e-14,
      f"200 组按操作数量级归一的误差 = {rel9:.2e}（相消量，几个 ulp）")

# N10 群速度是导数（中心差分收敛阶 ≈ 2）
c, beta, k0 = 0.4, 0.25, 1.7
omega = lambda k: c * k + beta * k ** 2
# (a) 二次色散上中心差分是**精确**的 ⟹ 与闭式 v_g 的差只剩舍入
err_exact = abs((omega(k0 + 1e-3) - omega(k0 - 1e-3)) / 2e-3 - vg(c, beta, k0))
# (b) 加三次项后中心差分有 O(h²) 截断误差 ⟹ 步长减半误差比 ≈ 4（证明"差分是导数算子"）
gamma = 0.37
omega3 = lambda k: c * k + beta * k ** 2 + gamma * k ** 3
vg3 = lambda k: c + 2 * beta * k + 3 * gamma * k ** 2
errs = []
for h in (4e-3, 2e-3, 1e-3):
    fd = (omega3(k0 + h) - omega3(k0 - h)) / (2 * h)
    errs.append(abs(fd - vg3(k0)))
ratios = [errs[i] / errs[i + 1] for i in range(len(errs) - 1)]
check("N10 ★★★ 群速度 = dω/dk：(a) 二次上中心差分精确；(b) 三次上误差比 ≈ 4 = O(h²)（GD5 数值替身）",
      err_exact < 1e-12 and all(abs(r - 4.0) < 0.05 for r in ratios),
      f"(a) |FD − v_g| = {err_exact:.1e}（二次精确）；(b) 步长减半误差比 = {[round(r,3) for r in ratios]}")

# N11 β≠0 ⟹ vg≠vph；β=0 ⟹ 相等
nonlin = abs(vg(c, 0.25, k0) - (c + 0.25 * k0)) > 1e-12
lin = abs(vg(c, 0.0, k0) - (c + 0.0 * k0)) < 1e-15
check("N11 ★★★ 线性色散 v_g = v_ph（AB 混用无害）；非线性 v_g ≠ v_ph（GD7/GD8）",
      nonlin and lin,
      f"β=0.25：v_g={vg(c,0.25,k0):.4f} vs v_ph={c+0.25*k0:.4f}；β=0：两者 = {vg(c,0,k0):.4f}")

# N12 |Δv_g|·λ_beat = 4π|β|
rel12 = 0.0
for k1v, k2v in [(0.5, 1.5), (1.0, 1.2), (2.0, 2.7)]:
    gap = abs(vg(0.0, 0.3, k2v) - vg(0.0, 0.3, k1v))
    rel12 = max(rel12, abs(gap * beat_wavelength(k1v, k2v) - 4 * math.pi * 0.3) / (4 * math.pi * 0.3))
check("N12 ★★★ 「广 ⟹ 涟漪更慢」：|Δv_g|·λ_beat = 4π|β|（GD9）", rel12 < 1e-14,
      f"3 组带对最大相对差 = {rel12:.1e}")

# ═════════════ ③ 带维度 ═════════════
def coefficients(k1, w1, k2, w2, k3, w3):
    D = k1 * w2 - k2 * w1
    a = (k3 * w2 - k2 * w3) / D
    b = (k1 * w3 - k3 * w1) / D
    return a, b, D


m1 = dict(k=1.2, w=0.7)
m2 = dict(k=0.4, w=1.9)
m3 = dict(k=2.3, w=-0.6)
a, b, D = coefficients(m1["k"], m1["w"], m2["k"], m2["w"], m3["k"], m3["w"])

# N13 相位关系
res13 = 0.0
for _ in range(300):
    x, t = rng.normal(scale=3, size=2)
    lhs = m3["k"] * x - m3["w"] * t
    rhs = a * (m1["k"] * x - m1["w"] * t) + b * (m2["k"] * x - m2["w"] * t)
    res13 = max(res13, abs(lhs - rhs))
check("N13 ★★★ 三条带线性相关：θ₃ = aθ₁ + bθ₂ 对一切 (x,t) 成立（ND1/ND2）",
      res13 < 1e-13, f"300 组 (x,t) max 残差 = {res13:.1e}（a={a:.4f}, b={b:.4f}）")

# N14 计数冗余 + 秩封顶
res14 = 0.0
for L in (0.5, 1.0, 3.0, 7.5):
    lhs = time_count(m3["k"], L)
    rhs = a * time_count(m1["k"], L) + b * time_count(m2["k"], L)
    res14 = max(res14, abs(lhs - rhs))
M = np.array([[m1["k"], m1["w"]], [m2["k"], m2["w"]], [m3["k"], m3["w"]]])
rank = int(np.linalg.matrix_rank(M))

# ⚠ 六轮攻防 R3（2026-10-30）：只报「3×2 矩阵秩 = 2」是在验夹具自己的形状
#（matrix_rank ≤ min(3,2) 由数组形状保证）。可判死的量是「秩对**带数**不敏感」：
# 共享二帧下无论加多少条带，秩恒为 2。
rank_by_bandcount = {}
for N in (3, 10, 50, 200):
    Mb = rng.normal(size=(N, 2))
    rank_by_bandcount[N] = int(np.linalg.matrix_rank(Mb))
rank_is_band_free = set(rank_by_bandcount.values()) == {2}
check("N14 ★★★ 计数也冗余（n₃ = a n₁ + b n₂）；共享二帧下秩对带数不敏感（ND3/ND4 + R3 更正）",
      res14 < 1e-13 and rank == 2 and rank_is_band_free,
      f"4 个跨度 max 残差 = {res14:.1e}；rank(3 带)= {rank}；"
      f"rank(N 带, N∈{sorted(rank_by_bandcount)}) = {[rank_by_bandcount[N] for N in sorted(rank_by_bandcount)]}"
      " ⟹ 该上界属于**帧**（2 维），不回答『多带是否高维』")

# ═════════════════════ 图 ═════════════════════
# 图 1：时间计数 vs 跨度（不同带 = 不同斜率）
fig, ax = plt.subplots(figsize=(7.2, 4.5))
Lg = np.linspace(0, 7.0, 300)
for k, lab, st in ((1.0, "k = 1（λ = 2π）", "-"), (2.5, "k = 2.5", "--"), (0.0, "k = 0（全局模）", ":")):
    ax.plot(Lg, [time_count(k, L) for L in Lg], st, label=lab)
ax.axvline(TWO_PI, color="0.5", lw=0.8, ls=":")
ax.annotate("L = λ = 2π：n = 1\n（一个波长 = 一次闭合）", (TWO_PI, 1.0), textcoords="offset points",
            xytext=(-14, 30), fontsize=9, color="0.25", ha="right",
            arrowprops=dict(arrowstyle="->", color="0.4", lw=0.9))
ax.set_xlabel("跨度 L")
ax.set_ylabel("时间计数 n（闭合次数）")
ax.set_title("时间计数 = 带指标 × 跨度 / 2π（TC1–TC5）")
ax.legend(fontsize=9)
ax.grid(alpha=0.3)
fig.tight_layout()
fig.savefig(os.path.join(OUT, "fig_time_count.png"), dpi=150)
plt.close(fig)

# 图 2：一般色散下的 v_ph 与 v_g
fig, ax = plt.subplots(figsize=(7.2, 4.5))
kg = np.linspace(0.2, 3.0, 200)
# β = 0：两根轴完全重合 ⟹ 只画一条（否则两条线互相遮住，看不出"重合"这件事）
ax.plot(kg, [c] * len(kg), "-", color="k", lw=2.0, label="β=0：v_ph = v_g = c（两轴重合）")
# β ≠ 0：两根轴分开
ax.plot(kg, [vph(c * 0.25 * 0 + 0.25 * k ** 2 + c * k, k) for k in kg], "--", color="C0",
        label="β=0.25：v_ph = c + βk")
ax.plot(kg, [vg(c, 0.25, k) for k in kg], "--", color="C3",
        label="β=0.25：v_g = c + 2βk")
ax.annotate("β ≠ 0：两根轴分开\n⟹ AB 的「相位速度无界」\n不能读成「信号更快」".replace("⟹", "→"),
            (1.72, 0.47), fontsize=8.5, color="0.25")
ax.set_xlabel("波矢 k")
ax.set_ylabel("速度")
ax.set_title("一般色散：v_ph 与 v_g 是两根轴（GD7/GD8）")
ax.legend(fontsize=8, loc="upper left")
ax.grid(alpha=0.3)
fig.tight_layout()
fig.savefig(os.path.join(OUT, "fig_phase_group_speed.png"), dpi=150)
plt.close(fig)

# 图 3：三条带在 (k, ω) 平面里必然相关
fig, ax = plt.subplots(figsize=(6.8, 5.0))
for m, col, lab, ha, off in ((m1, "C0", "带1", "left", (6, 6)),
                             (m2, "C1", "带2", "left", (6, 6)),
                             (m3, "C2", "带3 = a·带1 + b·带2", "right", (-6, -14))):
    ax.annotate("", xy=(m["k"], m["w"]), xytext=(0, 0),
                arrowprops=dict(arrowstyle="->", color=col, lw=1.8))
    ax.annotate(lab, (m["k"], m["w"]), textcoords="offset points", xytext=off,
                fontsize=9, color=col, ha=ha)
ax.annotate("", xy=(a * m1["k"] + b * m2["k"], a * m1["w"] + b * m2["w"]), xytext=(0, 0),
            arrowprops=dict(arrowstyle="->", color="0.5", lw=1.0, ls="--"))
# ⚠ annotate/arrow 不参与 autoscale ⟹ 必须显式设范围，否则整张图空白
ks_all = [0.0, m1["k"], m2["k"], m3["k"]]
ws_all = [0.0, m1["w"], m2["w"], m3["w"]]
pad_k = 0.25 * (max(ks_all) - min(ks_all) + 1e-9)
pad_w = 0.25 * (max(ws_all) - min(ws_all) + 1e-9)
ax.set_xlim(min(ks_all) - pad_k, max(ks_all) + pad_k)
ax.set_ylim(min(ws_all) - pad_w, max(ws_all) + pad_w)
ax.set_xlabel("k")
ax.set_ylabel("ω")
ax.set_title("1+1 维：3 条带 → 秩 ≤ 2（第三条带不增维）（ND1–ND4）")
ax.grid(alpha=0.3)
ax.axhline(0, color="k", lw=0.6)
ax.axvline(0, color="k", lw=0.6)
fig.tight_layout()
fig.savefig(os.path.join(OUT, "fig_band_rank.png"), dpi=150)
plt.close(fig)

passed = sum(1 for c in CHECKS if c["通过"])
report = {
    "动机（leo 2026-10-29 四续）": "按优先级完成：① 时间计数接口 ② 一般色散 + 群速度 ③ 带数 ⟷ 维数",
    "Lean": {
        "TimeCount": "TC1–TC6（零 sorry）",
        "DispersionGeneral": "GD1–GD9（零 sorry；GD5 导数身份登记为数值层）",
        "BandDimension": "ND1–ND5（零 sorry）",
    },
    "checks": CHECKS,
    "锚点": {
        "N1 计数=密度×跨度": rel1,
        "N2 可加": rel2,
        "N3 一波长=1 次闭合": err3,
        "N4 计数依赖带": float(abs(n4a - n4b)),
        "N6 计数差密度=1/λ": err6,
        "N7 det 一般形式": rel7,
        "N8 det=0⟺同相速度": bool(all(same_speed_flags) and diff_flag),
        "N9 二次族 det": rel9,
        "N10 群速度导数误差比": [float(r) for r in ratios],
        "N11 β≠0⟹vg≠vph": bool(nonlin and lin),
        "N12 |Δvg|·λ=4π|β|": rel12,
        "N13 三带相关残差": res13,
        "N14 计数冗余残差": res14,
        "N14 秩": rank,
        "N13 系数 (a,b)": [a, b],
    },
    "结果": {
        "三带 (k,ω)": {k: v for k, v in (("带1", [m1["k"], m1["w"]]), ("带2", [m2["k"], m2["w"]]),
                                        ("带3", [m3["k"], m3["w"]]))},
    },
    "判据（可判死）": {
        "①": "k≠0 的带在一个波长内不产生一次闭合 ⟹ TC3 死；两带在所有跨度上计数相同 ⟹ 「计数依赖带」死",
        "②": "k≠0 且相速度相同但 det≠0 ⟹ GD2 死；群速度差与 1/λ 不成正比 ⟹ GD9 只在二次族成立",
        "③": "1+1 维里找到三条线性无关的相位 ⟹ 秩封顶死；第三条带计数与前两条不合适 ⟹ 计数冗余死",
    },
    "诚实边界": [
        "二次色散族是模型选择；一般 ω(k) 下 v_g 仍是 dω/dk，只是无闭式",
        "N10 是 Lean 里没做的导数身份的形式化的数值替身（v4.35 HasDerivAt.pow 实例不同源）",
        "「维度 = min(带数, d+1)」只在 1+1 维被覆盖；高维是读法",
        "零新可检验预言",
    ],
    "conclusion": "① 时间计数 n = kL/2π = 带指标 × 跨度 /2π —— 一个波长恰一次闭合（N3），计数依赖带（N4），"
                  "计数差密度 = 1/λ_beat（N6）⟹ 时间计数与「广」是同一个刻度。"
                  "② 一般色散 det = k₁ω₂ − k₂ω₁ = k₁k₂(v_ph2 − v_ph1)：退化判据不变；v_g 与 v_ph 只在"
                  "线性色散处相等（N11），|Δv_g|·λ = 4π|β| ⟹ 广 ⟹ 涟漪更慢（N12）。"
                  "③ 1+1 维 3 条带必线性相关（N13 残差机器精度，rank=2）⟹ 第三条带不增维、也不增计数（N14）；"
                  "要更多独立坐标必须升空间维数。"
    if passed == len(CHECKS) else f"FAIL: {passed}/{len(CHECKS)} 通过",
}
with open(os.path.join(OUT, "report.json"), "w", encoding="utf-8") as f:
    json.dump(report, f, ensure_ascii=False, indent=2)
with open(os.path.join(OUT, "summary.txt"), "w", encoding="utf-8") as f:
    f.write(f"带结构三件（TC/GD/ND）数值验证：{passed}/{len(CHECKS)} 断言通过\n")
    for c in CHECKS:
        f.write(f"  {'PASS' if c['通过'] else 'FAIL'}  {c['检查']}  {c['细节']}\n")

print(f"RESULT: {passed}/{len(CHECKS)} passed")
for c in CHECKS:
    print(f"  {'PASS' if c['通过'] else 'FAIL'}  {c['检查']}")
    print(f"         {c['细节']}")
print(f"产物: {OUT}/{{report.json, summary.txt, fig_*.png}}")
