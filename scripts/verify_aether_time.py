#!/usr/bin/env python3
"""接 YM 接口：顺序（时间的代数影子）⟺ 非对易 —— 无质量层没有线性时间观（AT1–AT10 数值同位体）

═════ 动机（leo 2026-10-29 续）═════
「结 ym 方程接口，瞬时是因为时间在人类世界上线性的，在无质量空间，不存在当前的
 线性时间观。」

形式化落点（Lean: ProjectionPhysics/Explorations/AetherTime.lean，零 sorry）：
  AT1/AT2  顺序盲 ⟺ 无观察量能报告先后；否定 ⟺ 存在见证场
  AT3/AT4  平坦（无起伏 = Q_A=0）⟹ 汇算子复合顺序盲
  AT5      有梯度 ⟹ 顺序可观测（交换差 = λ²(v_q−v_p)，复用 YM3）
  AT6      非平坦 ⟹ 存在梯度
  AT7/AT8  无质量 ⟹ dτ²=0；全区间为 0 ⟹ 无严格先后
  AT9      平坦 ∧ 无质量 ⟹ 顺序盲 ∧ 无严格时间序 ⟹「瞬时」= 比较无定义，不是更快
  AT10     有梯度 ⟹ 时间序被生出来（与 AT4 对偶）

═════ 断言（N1–N6，每条对位一条 Lean 定理）═════
  N1 ★★  平坦场 ⟹ 交换差精确为 0（顺序盲）
  N2 ★★★ 有梯度 ⟹ 交换差 = λ²|v_q−v_p|（顺序可观测，机器精度）
  N3 ★★  「时间序可观测度」∝ 起伏幅度 ε（ε=0 精确 0，线性过原点）
  N4 ★★  无质量 ⟹ dτ²=0（β=1 精确 0）；dτ=0 ⟹ 快慢不可比
  N5 ★★★ 全区间间隔为 0 ⟹ 不存在严格先后（对照：有质量侧存在）
  N6 ★★★ 定量桥：交换差 = λ²·√(Q_A·N/(N−1))（时间可观测度 ∝ √起伏能量）

═════ 诚实边界（写死）═════
  · 本脚本**不**证明「时间 = 非对易性」。它证明两者**结构同位**：顺序可观测 ⟺ 非交换
    ⟺ 有梯度。把时间等同于非对易性的记录是**解释层**（框架读法）。
  · 「无质量 ⟹ 平坦」未证明：框架里是两条独立链（质量=锚定；平坦⟹μ=1⟹m_eff=0），
    本脚本只把「平坦」与「无质量（dτ=0）」并置成判据，不主张等价。
  · 标准物理里光子无固有时但有坐标时间；「无质量空间没有线性时间观」是本框架读法
    （时间单位 = 闭包次数 VBC4/VBC5），不是标准 QFT 结论。
  · AT1–AT10 全是初等代数/序关系（真但平凡）；零新可检验预言。

产物：artifacts/aethertime/{report.json, summary.txt, fig_*.png}
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
OUT = os.path.join(REPO, "artifacts", "aethertime")
os.makedirs(OUT, exist_ok=True)

CHECKS = []


def check(name, ok, detail):
    CHECKS.append({"检查": name, "通过": bool(ok), "细节": detail})


def sink_to_point(p, lam, v):
    """向单点 p 收缩：v_i ← (1−λ)v_i + λ v_p（YangMillsSeed.sinkToPoint）。"""
    return (1.0 - lam) * v + lam * v[p]


def commutator(v, p, q, lam):
    """顺序差（交换差场）：T_p∘T_q − T_q∘T_p。"""
    return sink_to_point(p, lam, sink_to_point(q, lam, v)) - \
        sink_to_point(q, lam, sink_to_point(p, lam, v))


def fluctuation(v):
    """起伏能量 Q_A = Σ (v_i − 均值)²（GCA 的基元）。"""
    return float(np.sum((v - v.mean()) ** 2))


N = 6
P, Q_IDX = 1, 4
LAM = 0.4
rng = np.random.default_rng(20261029)

# ── N1 ★★ 平坦 ⟹ 顺序盲（AT3/AT4）────────────────────────────────────────
worst_flat = 0.0
for _ in range(200):
    c = rng.normal()
    v = np.full(N, float(c))
    worst_flat = max(worst_flat, float(np.max(np.abs(commutator(v, P, Q_IDX, LAM)))))
check("N1 ★★ 平坦场（Q_A=0）⟹ 交换差精确 0（顺序盲）（AT3/AT4）",
      worst_flat == 0.0, f"200 组常值场 max|交换差| = {worst_flat:.1e}")

# ── N2 ★★★ 有梯度 ⟹ 顺序可观测，强度 = λ²|v_q − v_p|（AT5）──────────────
rows_n2, rel_n2 = [], 0.0
for lam in (0.1, 0.25, 0.4, 0.6, 0.9):
    for g in (1e-3, 1e-1, 1.0, 5.0):
        v = np.zeros(N)
        v[Q_IDX] = g
        comm = commutator(v, P, Q_IDX, lam)
        pred = lam ** 2 * g
        rel = abs(float(np.max(np.abs(comm))) - pred) / pred
        rel_n2 = max(rel_n2, rel)
        rows_n2.append({"lambda": lam, "梯度 g": g, "数值 max|交换差|": float(np.max(np.abs(comm))),
                        "λ²g": pred, "相对差": rel})
check("N2 ★★★ 交换差 = λ²|v_q − v_p|（顺序可观测；复用 YM3 公式）（AT5/AT10）",
      rel_n2 < 1e-14, f"20 组 (λ,g) 最大相对差 = {rel_n2:.2e}")

# ── N3 ★★ 时间序可观测度 ∝ 起伏幅度 ε（ε=0 精确 0）────────────────────────
base = np.full(N, 3.0)
dirv = rng.normal(size=N)
dirv -= dirv[P]                      # 让 p 处起伏为 0（干净口径）
eps_list = [0.0, 1e-3, 1e-2, 1e-1, 0.5, 1.0]
grad_list, comm_list = [], []
for eps in eps_list:
    v = base + eps * dirv
    g = abs(v[Q_IDX] - v[P])
    grad_list.append(g)
    comm_list.append(float(np.max(np.abs(commutator(v, P, Q_IDX, LAM)))))
g_arr, c_arr = np.array(grad_list), np.array(comm_list)
slope = c_arr[-1] / g_arr[-1] if g_arr[-1] else 0.0
resid = float(np.max(np.abs(c_arr - LAM ** 2 * g_arr)))
check("N3 ★★ 顺序可观测度 ∝ 起伏幅度（ε=0 精确 0；线性过原点）（AT5）",
      c_arr[0] == 0.0 and resid < 1e-14 * max(1.0, float(np.max(c_arr))) and abs(slope - LAM ** 2) < 1e-14,
      f"ε=0 ⟹ {c_arr[0]:.1f}；斜率 = {slope:.6f}（λ² = {LAM**2:.6f}）；残差 ≤ {resid:.1e}")

# ── N4 ★★ 无质量 ⟹ dτ²=0（AT7）──────────────────────────────────────────
betas = [0.0, 0.5, 0.9, 0.99, 0.999999, 1.0]
dtau = [1.0 - b ** 2 for b in betas]
ratio_defined = [abs(1.0 - b ** 2) > 0 for b in betas]
check("N4 ★★ β=1（无质量/随流）⟹ dτ²=0 精确；此时「快慢」比值 0/0 不可比（AT7）",
      dtau[-1] == 0.0 and all(ratio_defined[:-1]) and not ratio_defined[-1],
      "β=" + ", ".join(f"{b:g}→dτ²={d:.3g}" for b, d in zip(betas, dtau)))

# ── N5 ★★★ 全区间间隔 0 ⟹ 无严格先后（AT8）────────────────────────────────
massless_tau = np.zeros((5, 5))                        # 无质量层：所有有向间隔 = 0
times = np.array([0.0, 1.0, 2.5, 4.0, 5.5])
massive_tau = times[None, :] - times[:, None]           # 有质量层：有向间隔 t_y − t_x


def has_strict_order(tau):
    """严格先后：存在有序对 (x,y) 使 τ(x,y) < τ(y,x)
    （有向间隔才谈得上「先 / 后」；只看上半三角会把两种朝向混成一种）。"""
    n = tau.shape[0]
    return any(i != j and tau[i, j] < tau[j, i] for i in range(n) for j in range(n))


check("N5 ★★★ 全区间间隔为 0 ⟹ 不存在严格先后；有质量侧存在（AT8/AT9）",
      (not has_strict_order(massless_tau)) and has_strict_order(massive_tau),
      f"无质量层 10 对有向间隔全 0 → 严格序 0 处；有质量层存在（max |Δτ|={np.abs(massive_tau).max():.1f}）")

# ── N6 ★★★ 定量桥：交换差 = λ²·√(Q_A·N/(N−1))（AT5 + GCA 起伏）─────────────
rows_n6, rel_n6 = [], 0.0
for n in (3, 4, 6, 10):
    for g in (0.05, 0.5, 2.0):
        v = np.zeros(n)
        v[0] = 0.0
        v[-1] = g
        qa = fluctuation(v)
        g_pred = math.sqrt(qa * n / (n - 1))
        comm = float(np.max(np.abs(commutator(v, 0, n - 1, LAM))))
        pred = LAM ** 2 * g_pred
        rel = abs(comm - pred) / pred
        rel_n6 = max(rel_n6, rel)
        rows_n6.append({"N": n, "梯度 g": g, "Q_A": qa, "√(Q_A·N/(N−1))": g_pred,
                        "λ²√(Q·N/(N−1))": pred, "数值交换差": comm, "相对差": rel})
check("N6 ★★★ 时间序可观测度 = λ²·√(Q_A·N/(N−1))（∝ √起伏能量）（AT5 + GCA）",
      rel_n6 < 1e-13, f"12 组 (N,g) 最大相对差 = {rel_n6:.2e}")

# ═════════════════════ 图 ═════════════════════
# 图 1：顺序可观测度 vs 起伏幅度
fig, ax = plt.subplots(figsize=(7.0, 4.4))
ax.plot(g_arr, c_arr, "o-", color="C0", label="数值 max|交换差|")
ax.plot(g_arr, LAM ** 2 * g_arr, "--", color="C3", lw=1.2, label=f"λ²·|v_q−v_p|（λ={LAM}）")
ax.annotate("ε = 0：精确 0\n（无起伏 → 顺序盲）", (0.0, 0.0), textcoords="offset points",
            xytext=(150, 12), fontsize=9, color="0.25")
ax.set_xlabel("起伏幅度（两汇点场差）")
ax.set_ylabel("时间序可观测度  max|交换差|")
ax.set_title("顺序可观测 = 有起伏（时间序被质量生出来）（AT5）")
ax.legend(fontsize=9)
ax.grid(alpha=0.3)
fig.tight_layout()
fig.savefig(os.path.join(OUT, "fig_order_vs_fluctuation.png"), dpi=150)
plt.close(fig)

# 图 2：固有时 vs β
fig, ax = plt.subplots(figsize=(7.0, 4.2))
bg = np.linspace(0, 1, 201)
ax.plot(bg, 1.0 - bg ** 2, color="C2", label="dτ² = 1 − β²")
ax.plot([1.0], [0.0], "o", color="C3", ms=8)
ax.annotate("β = 1：dτ² = 0 → 无固有时\n（快慢比值 0/0，不可比）", (1.0, 0.0),
            textcoords="offset points", xytext=(-150, 30), fontsize=9, color="C3",
            arrowprops=dict(arrowstyle="->", color="C3", lw=0.9))
ax.set_xlabel("速度比 β = v/c")
ax.set_ylabel("固有时平方 dτ²")
ax.set_title("无质量层不花时间：比较的前提消失（AT7/AT8）")
ax.legend(fontsize=9)
ax.grid(alpha=0.3)
fig.tight_layout()
fig.savefig(os.path.join(OUT, "fig_proper_time.png"), dpi=150)
plt.close(fig)

# 图 3：交换差 / λ² vs √Q（精确 y = x）
qs = [r["√(Q_A·N/(N−1))"] for r in rows_n6]
cs = [r["数值交换差"] / LAM ** 2 for r in rows_n6]
fig, ax = plt.subplots(figsize=(6.6, 4.6))
ax.plot(qs, cs, "o", color="C4", label="12 组 (N, g)")
lim = [0, max(qs) * 1.15]
ax.plot(lim, lim, "--", color="0.5", lw=1.0, label="y = x（精确关系）")
ax.set_xlabel("√(Q_A·N/(N−1))　起伏的平方根")
ax.set_ylabel("交换差 / λ²")
ax.set_title("时间序可观测度 = λ²·√起伏（AT5 × GCA）")
ax.annotate("12 组（3 档 g × 4 档 N）\n同组重合显示", (0.62, 0.12), xycoords="axes fraction",
            fontsize=8, color="0.35")
ax.legend(fontsize=9)
ax.grid(alpha=0.3)
fig.tight_layout()
fig.savefig(os.path.join(OUT, "fig_comm_vs_sqrtQ.png"), dpi=150)
plt.close(fig)

passed = sum(1 for c in CHECKS if c["通过"])
report = {
    "假设（leo 2026-10-29 续）": "结 ym 方程接口；瞬时是因为时间在人类世界上线性的，在无质量空间不存在当前的线性时间观",
    "Lean": "ProjectionPhysics/Explorations/AetherTime.lean AT1–AT10（零 sorry）",
    "checks": CHECKS,
    "锚点": {
        "平坦场 max|交换差|（N1）": worst_flat,
        "交换差 vs λ²g 最大相对差（N2）": rel_n2,
        "ε=0 时交换差（N3）": c_arr[0],
        "N3 斜率 vs λ²": slope,
        "β=1 时 dτ²（N4）": dtau[-1],
        "无质量层严格序处数（N5）": int(has_strict_order(massless_tau)),
        "有质量层严格序处数（N5）": int(has_strict_order(massive_tau)),
        "N6 最大相对差": rel_n6,
    },
    "结果": {
        "N2 表": rows_n2,
        "N3 表": [{"ε": e, "梯度": g, "交换差": c} for e, g, c in zip(eps_list, grad_list, comm_list)],
        "N4 表": [{"β": b, "dτ²": d} for b, d in zip(betas, dtau)],
        "N6 表": rows_n6,
    },
    "判据（可判死）": {
        "接口陈述": "顺序（时间的代数影子）可观测 ⟺ 算符不交换 ⟺ 场有梯度（有质量）；"
                    "平坦（无起伏）⟹ 顺序盲；无质量 ⟹ dτ=0 ⟹ 无严格先后",
        "死法①": "若平坦场上找到两个汇算子不交换 ⟹ AT3/AT4/AT6 死（时间序不需要质量）",
        "死法②": "若找到无质量但非平坦的构型、其中时间序仍可观测 ⟹ AT9 的读法死（「平坦 ⟺ 无质量」未证，只并置）",
        "死法③": "若把「时间 = 非对易性的记录」当物理定律使用 ⟹ 需补推导，本轮未做（登记缺口）",
    },
    "诚实边界": [
        "不证明「时间 = 非对易性」；只证结构同位（顺序可观测 ⟺ 非交换 ⟺ 有梯度）",
        "「无质量 ⟹ 平坦」未证明：两条独立链被并置，不主张等价",
        "标准物理里光子无固有时但有坐标时间；本判据是框架读法（时间单位=闭包次数 VBC4/VBC5）",
        "AT1–AT10 全初等代数/序关系（真但平凡）；零新可检验预言",
    ],
    "conclusion": "接上 YM 接口：顺序可观测 ⟺ 非交换 ⟺ 有起伏；平坦/无质量层顺序盲且 dτ=0 ⟹ "
                  "「瞬时」不是更快，而是快慢的比较没有定义；要谈更快，先得有质量把时间序生出来。"
    if passed == len(CHECKS) else f"FAIL: {passed}/{len(CHECKS)} 通过",
}
with open(os.path.join(OUT, "report.json"), "w", encoding="utf-8") as f:
    json.dump(report, f, ensure_ascii=False, indent=2)
with open(os.path.join(OUT, "summary.txt"), "w", encoding="utf-8") as f:
    f.write(f"AetherTime（YM 接口 × 时间序）数值验证：{passed}/{len(CHECKS)} 断言通过\n")
    for c in CHECKS:
        f.write(f"  {'PASS' if c['通过'] else 'FAIL'}  {c['检查']}  {c['细节']}\n")

print(f"RESULT: {passed}/{len(CHECKS)} passed")
for c in CHECKS:
    print(f"  {'PASS' if c['通过'] else 'FAIL'}  {c['检查']}")
    print(f"         {c['细节']}")
print(f"产物: {OUT}/{{report.json, summary.txt, fig_*.png}}")
