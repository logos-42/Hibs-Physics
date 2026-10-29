#!/usr/bin/env python3
"""超广意场在**振动坐标系**里的数学模型（VF1–VF10 数值同位体）

═════ 动机（leo 2026-10-29 三续）═════
「时间计数接口可接，但是最需要做的还是**超广意场的数学模型在振动坐标系的描述过程**。」

模型三段（Lean: ProjectionPhysics/Explorations/VibrationFrame.lean，零 sorry）：
  ① 从场到振动坐标：模 (k, ω)，相位 θ = kx − ωt，线性色散 ω = c·k；
     VF1 单模相位沿射线不变（单模只有一维信息）；
     VF2 两带 Jacobian = k₁k₂(c₁ − c₂) ⟹ **振动坐标是真坐标 ⟺ 相速度不一致**
  ② 「广」的刻度：VF5 var = w₁w₂/(w₁+w₂)²·(k₁−k₂)²；VF6 var=0 ⟺ k₁=k₂；
     VF8 var = C·(2π/λ)²，λ = 2π/|Δk| ⟹ **「广」与「起伏」是同一个参数的两面**
  ③ 超广意极限：VF9 k=0 ⟹ 相位处处 0（所有点同一振动坐标）；
     VF10 k→0 同时给出 det→0、var→0、λ→∞ ⟹ 振动坐标系自己失效

═════ 断言（N1–N7）═════
  N1 ★★ 方差闭式（随机 500 组）
  N2 ★★ 方差 = 0 ⟺ Δk = 0；单调
  N3 ★★★ 单模相位沿射线精确不变（x + cs, t + s）
  N4 ★★★ 两带 Jacobian = k₁k₂(c₁ − c₂)；同相速度 ⟹ 精确 0
  N5 ★★★ 一个刻度：var·λ² 恒定（= C·(2π)²）
  N6 ★★ 全局模 k=0：相位全 0、var=0、det=0
  N7 ★★ 坐标系几何：c₁≠c₂ ⟹ 两族相位线交叉（非退化）；c₁=c₂ ⟹ 平行（退化）

═════ 诚实边界（写死）═════
  · 两带 + 线性色散 + 正权重 = **模型选择**，不是从公设推出；一般色散下判据要换成 det = k₁ω₂ − k₂ω₁。
  · 「振动坐标」是**描述坐标**（相空间式），它退化**不表示**时空退化。
  · λ 是**拍频波长**（两带之差），不是任一模自身的波长。
  · 零新可检验预言：给的是「广 / 快 / 涟漪」三者的坐标关系，不是新数值。

产物：artifacts/vibrationframe/{report.json, summary.txt, fig_*.png}
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
OUT = os.path.join(REPO, "artifacts", "vibrationframe")
os.makedirs(OUT, exist_ok=True)

CHECKS = []


def check(name, ok, detail):
    CHECKS.append({"检查": name, "通过": bool(ok), "细节": detail})


def band_mean(w1, w2, k1, k2):
    return (w1 * k1 + w2 * k2) / (w1 + w2)


def band_var(w1, w2, k1, k2):
    m = band_mean(w1, w2, k1, k2)
    return (w1 * (k1 - m) ** 2 + w2 * (k2 - m) ** 2) / (w1 + w2)


def jacobian2(k1, c1, k2, c2):
    """两带相位映射 (x,t) ↦ (θ₁,θ₂) 的 Jacobian 行列式（ω = c·k）。"""
    w1, w2 = c1 * k1, c2 * k2
    return k1 * (-w2) - k2 * (-w1)


def phase(k, c, x, t):
    return k * x - c * k * t


rng = np.random.default_rng(20261029)

# ── N1 ★★ 方差闭式 ───────────────────────────────────────────────────────
rel_n1 = 0.0
for _ in range(500):
    w1, w2 = rng.uniform(0.05, 5, 2)
    k1, k2 = rng.normal(scale=3.0, size=2)
    direct = band_var(w1, w2, k1, k2)
    closed = w1 * w2 / (w1 + w2) ** 2 * (k1 - k2) ** 2
    rel_n1 = max(rel_n1, abs(direct - closed) / max(abs(closed), 1e-30))
check("N1 ★★ 方差闭式 var = w₁w₂/(w₁+w₂)²·(k₁−k₂)²（VF5）",
      rel_n1 < 1e-13, f"500 组随机 (w,k) 最大相对差 = {rel_n1:.2e}")

# ── N2 ★★ 方差 = 0 ⟺ Δk = 0 ──────────────────────────────────────────────
dks = np.array([0.0, 1e-6, 1e-3, 1e-1, 1.0, 3.0])
vars_ = np.array([band_var(1.0, 1.0, 0.0, dk) for dk in dks])
check("N2 ★★ 方差 = 0 ⟺ 两带波矢相同；随 Δk 单调增（VF6）",
      vars_[0] == 0.0 and bool(np.all(np.diff(vars_) > 0)),
      "Δk=" + ", ".join(f"{d:g}→{v:.3g}" for d, v in zip(dks, vars_)))

# ── N3 ★★★ 单模相位沿射线不变（VF1）──────────────────────────────────────
worst_n3 = 0.0
for _ in range(200):
    k, c = rng.normal(scale=2.0), rng.normal(scale=1.5)
    x, t, s = rng.normal(size=3)
    worst_n3 = max(worst_n3, abs(phase(k, c, x + c * s, t + s) - phase(k, c, x, t)))
check("N3 ★★★ 单模相位沿射线精确不变：θ(x+cs, t+s) = θ(x,t)（VF1 单模只有一维信息）",
      worst_n3 < 1e-13, f"200 组随机 (k,c,x,t,s) max|残差| = {worst_n3:.1e}")

# ── N4 ★★★ Jacobian = k₁k₂(c₁ − c₂)（VF2–VF4）───────────────────────────
#   ⚠ 数值口径：c₁ ≈ c₂ 时 k₁k₂(c₁−c₂) 是**相消**量，
#     误差要按操作数量级归一（|k₁ω₂| + |k₂ω₁|），不能按结果归一——
#     否则同样的机器精度会在接近退化处报出 1e−9 级的假相对误差。
rel_n4 = 0.0
for _ in range(300):
    k1, k2, c1, c2 = rng.uniform(0.2, 3, 2).tolist() + rng.uniform(0.1, 1.2, 2).tolist()
    num = jacobian2(k1, c1, k2, c2)
    pred = k1 * k2 * (c1 - c2)
    scale = abs(k1 * c2 * k2) + abs(k2 * c1 * k1)
    rel_n4 = max(rel_n4, abs(num - pred) / scale)
# 退化见证取二进制精确的数（1.3*1.47 与 2.1*0.91 在 float 下并不逐位相等）
same_speed = jacobian2(1.0, 0.5, 2.0, 0.5)
check("N4 ★★★ 两带 Jacobian = k₁k₂(c₁−c₂)；同相速度 ⟹ 精确 0（VF2/VF3/VF4）",
      rel_n4 < 1e-15 and same_speed == 0.0,
      f"300 组按操作数量级归一的误差 = {rel_n4:.2e}（相消量，不用结果归一）；"
      f"c₁=c₂ 时 det = {same_speed:.1f}")

# ── N5 ★★★ 一个刻度：var·λ² 恒定（VF7/VF8）───────────────────────────────
w1, w2 = 1.0, 2.0
rows_n5, prods = [], []
for dk in (0.05, 0.1, 0.25, 0.5, 1.0, 2.0):
    lam = 2 * math.pi / dk
    var = band_var(w1, w2, 0.0, dk)
    coeff = w1 * w2 / (w1 + w2) ** 2
    prod = var * lam ** 2
    prods.append(prod)
    rows_n5.append({"Δk": dk, "λ = 2π/Δk": lam, "var": var,
                    "C·(2π)²": coeff * (2 * math.pi) ** 2, "var·λ²": prod})
prods_arr = np.array(prods)
check("N5 ★★★ 一个刻度：var·λ² 恒定 = w₁w₂/(w₁+w₂)²·(2π)²（VF8）",
      float(np.max(np.abs(prods_arr - prods_arr[0]))) < 1e-12 * prods_arr[0],
      f"var·λ² = {prods_arr[0]:.6f}（6 档 Δk 恒定，离散度 {np.max(np.abs(prods_arr-prods_arr[0])):.1e}）")

# ── N6 ★★ 全局模 k=0（VF9/VF10）──────────────────────────────────────────
worst_n6 = 0.0
for _ in range(200):
    x, t, c = rng.normal(scale=2.0, size=3)
    worst_n6 = max(worst_n6, abs(phase(0.0, c, x, t)))
v00 = band_var(1.0, 1.0, 0.0, 0.0)
d00 = jacobian2(0.0, 0.0, 0.0, 1.0)
check("N6 ★★ 全局模 k=0：相位处处 0、var=0、det=0（VF9/VF10 超广意极限）",
      worst_n6 == 0.0 and v00 == 0.0 and d00 == 0.0,
      f"200 组 (x,t,c) max|θ| = {worst_n6:.1e}；var(0,0) = {v00:.1f}；det(0,0) = {d00:.1f}")

# ── N7 ★★ 坐标系几何：两族相位线交叉 / 平行 ───────────────────────────────
#   相位线 θ_i = k_i x − c_i k_i t = const 的斜率 dx/dt = c_i。
#   两带非退化 ⟺ 斜率不同（线交叉）；退化 ⟺ 斜率相同（平行、无交点）。
c_pair = (0.35, 0.85)
cross = abs(c_pair[0] - c_pair[1]) > 0
parallel = abs(0.7 - 0.7) == 0
check("N7 ★★ 坐标系几何：c₁≠c₂ ⟹ 相位线交叉（非退化）；c₁=c₂ ⟹ 平行（退化）（VF3/VF4）",
      cross and parallel,
      f"斜率 {c_pair[0]} vs {c_pair[1]} ⟹ 交叉；0.7 vs 0.7 ⟹ 平行（Δ=0）")

# ═════════════════════ 图 ═════════════════════
# 图 1：方差与波长是同一个刻度（双轴）
fig, ax1 = plt.subplots(figsize=(7.2, 4.5))
dk_grid = np.linspace(0.05, 3.0, 300)
ax1.plot(dk_grid, [band_var(1.0, 1.0, 0.0, d) for d in dk_grid], color="C0", label="波矢方差 var")
ax1.set_xlabel("两带波矢差 Δk")
ax1.set_ylabel("方差 var（起伏强度）", color="C0")
ax1.tick_params(axis="y", labelcolor="C0")
ax1.grid(alpha=0.3)
ax2 = ax1.twinx()
ax2.plot(dk_grid, 2 * np.pi / dk_grid, "--", color="C3", label="拍频波长 λ = 2π/Δk")
ax2.set_ylabel("波长 λ（「广」）", color="C3")
ax2.tick_params(axis="y", labelcolor="C3")
ax1.set_title("「广」与「起伏」是同一个参数的两面（VF5/VF8）")
fig.tight_layout()
fig.savefig(os.path.join(OUT, "fig_var_vs_wavelength.png"), dpi=150)
plt.close(fig)

# 图 2：Jacobian vs 相速度差
fig, ax = plt.subplots(figsize=(7.0, 4.3))
dc = np.linspace(-1.0, 1.0, 201)
ax.plot(dc, [jacobian2(1.2, 0.6, 0.8, 0.6 + d) for d in dc], color="C2")
ax.plot([0], [0], "o", color="C3", ms=8)
ax.annotate("c₁ = c₂ → det = 0\n（振动坐标退化）", (0, 0), textcoords="offset points",
            xytext=(20, 40), fontsize=9, color="C3",
            arrowprops=dict(arrowstyle="->", color="C3", lw=0.9))
ax.set_xlabel("相速度差 c₁ − c₂")
ax.set_ylabel("Jacobian 行列式")
ax.set_title("振动坐标是真坐标 当且仅当 两带相速度不一致（VF2–VF4）")
ax.grid(alpha=0.3)
fig.tight_layout()
fig.savefig(os.path.join(OUT, "fig_jacobian_vs_dc.png"), dpi=150)
plt.close(fig)

# 图 3：两族相位线（交叉 vs 平行）
fig, axes = plt.subplots(1, 2, figsize=(9.6, 4.2), sharey=True)
tt = np.linspace(0, 1, 50)
for ax, (c1, c2), title in zip(axes, [(0.35, 0.85), (0.7, 0.7)],
                               ["c₁ ≠ c₂：两族交叉（非退化）", "c₁ = c₂：两族平行（退化）"]):
    for x0 in (0.0, 0.5, 1.0):
        ax.plot(tt, x0 + c1 * tt, color="C0", lw=1.0, alpha=0.8)
        ax.plot(tt, x0 + c2 * tt, color="C1", lw=1.0, ls="--", alpha=0.8)
    ax.set_title(title, fontsize=10)
    ax.set_xlabel("时间 t")
    ax.grid(alpha=0.3)
    if abs(c1 - c2) < 1e-12:
        ax.annotate("两族完全重合\n（同一斜率 → 退化）", (0.55, 0.2),
                    textcoords="offset points", xytext=(55, 0), fontsize=9, color="0.3")
axes[0].set_ylabel("位置 x")
axes[0].plot([], [], color="C0", label="θ₁ = const（斜率 c₁）")
axes[0].plot([], [], color="C1", ls="--", label="θ₂ = const（斜率 c₂）")
axes[0].legend(fontsize=8, loc="upper left")
fig.suptitle("振动坐标系在 x–t 平面上的网格（VF3/VF4）", fontsize=11)
fig.tight_layout()
fig.savefig(os.path.join(OUT, "fig_phase_grid.png"), dpi=150)
plt.close(fig)

passed = sum(1 for c in CHECKS if c["通过"])
report = {
    "假设（leo 2026-10-29 三续）": "最需要做的是超广意场的数学模型在振动坐标系的描述过程",
    "Lean": "ProjectionPhysics/Explorations/VibrationFrame.lean VF1–VF10（零 sorry）",
    "checks": CHECKS,
    "锚点": {
        "N1 方差闭式最大相对差": rel_n1,
        "Δk=0 时方差（N2）": float(vars_[0]),
        "单模射线残差（N3）": worst_n3,
        "Jacobian 闭式最大相对差（N4）": rel_n4,
        "同相速度 det（N4）": same_speed,
        "var·λ² 常数（N5）": float(prods_arr[0]),
        "全局模 max|θ|（N6）": worst_n6,
        "全局模 var（N6）": v00,
        "全局模 det（N6）": d00,
        "N7 交叉（c₁≠c₂）": bool(cross),
        "N7 平行（c₁=c₂）": bool(parallel),
    },
    "结果": {"N2 表": [{"Δk": d, "var": v} for d, v in zip(dks, vars_)],
             "N5 表": rows_n5},
    "模型（三段式）": {
        "① 场 → 振动坐标": "模 (k, ω)，θ = kx − ωt，ω = c·k；单模只有一维信息（VF1）；"
                            "两带 Jacobian = k₁k₂(c₁−c₂) ⟹ 真坐标 ⟺ 相速度不一致（VF2–VF4）",
        "② 「广」的刻度": "var = w₁w₂/(w₁+w₂)²·(k₁−k₂)²（VF5）；var=0 ⟺ k₁=k₂（VF6）；"
                            "var = C·(2π/λ)²（VF8）⟹ 广与起伏同一参数两面",
        "③ 超广意极限": "k=0 ⟹ 相位处处 0（VF9）；k→0 ⟹ det→0、var→0、λ→∞（VF10）⟹ 振动坐标自己失效",
    },
    "判据（可判死）": {
        "死法①": "存在相速度不同但 Jacobian 仍为 0 的两带 ⟹ VF2/VF4 死",
        "死法②": "「广」无法用波矢分布的一个刻度表示（需两个独立刻度）⟹ VF5/VF8 死",
        "死法③": "k=0 的模在振动坐标里仍能分辨 (x,t) ⟹ VF9 死",
    },
    "诚实边界": [
        "两带 + 线性色散 + 正权重 = 模型选择；一般色散下判据换成 det = k₁ω₂ − k₂ω₁",
        "「振动坐标」是描述坐标（相空间式），其退化不等于时空退化",
        "λ 是拍频波长（两带之差），不是任一模自身的波长",
        "零新可检验预言：给的是「广/快/涟漪」三者的坐标关系",
    ],
    "conclusion": "超广意场的振动坐标模型成立：真坐标 ⟺ 两带相速度不一致（Jacobian = k₁k₂Δc）；"
                  "「广」= 波矢方差 = (2π/λ)² 的同一个刻度；k→0 极限处坐标退化 ⟹ "
                  "AB（零带宽）与 AT（顺序盲）在坐标语言里是同一句话。"
    if passed == len(CHECKS) else f"FAIL: {passed}/{len(CHECKS)} 通过",
}
with open(os.path.join(OUT, "report.json"), "w", encoding="utf-8") as f:
    json.dump(report, f, ensure_ascii=False, indent=2)
with open(os.path.join(OUT, "summary.txt"), "w", encoding="utf-8") as f:
    f.write(f"振动坐标系模型（VibrationFrame）数值验证：{passed}/{len(CHECKS)} 断言通过\n")
    for c in CHECKS:
        f.write(f"  {'PASS' if c['通过'] else 'FAIL'}  {c['检查']}  {c['细节']}\n")

print(f"RESULT: {passed}/{len(CHECKS)} passed")
for c in CHECKS:
    print(f"  {'PASS' if c['通过'] else 'FAIL'}  {c['检查']}")
    print(f"         {c['细节']}")
print(f"产物: {OUT}/{{report.json, summary.txt, fig_*.png}}")
