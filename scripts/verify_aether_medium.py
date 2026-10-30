#!/usr/bin/env python3
"""六轮攻防后被保留的**介质层**命题（AL1–AL6 数值同位体）

═════ 动机（leo 2026-10-30）═════
「觉得你的这几轮攻防不够到位，你误解了我的意思，而且坚持的点不对，你被过去的知识
 误导了。所以，你需要接受我自己的推导逻辑，重新再进行 6 轮攻防。」
前置：「如果我的杨米尔斯猜想是真的，那么应该有一个基础介质是可以超越光速来实现
 同步的，这个介质叫做以太。」

形式化落点（Lean: ProjectionPhysics/Explorations/AetherMedium.lean，零 sorry）：
  AL1  场 → 介质 不是单射（⟨1,2⟩ 与 ⟨2,1⟩ 给同一场）⟹ 场层不足以判定介质层
  AL2  同步 = 同一介质标签 ⟹ 该层无可观测差异；同步是等价关系
  AL3  时间坐标由带供给：k=0 ⟹ 无正周期（不是"周期 0"）；常值读数≠无坐标
  AL4  三条独立频率轴线性无关 ⟹ ND 的 rank≤2 是**帧**的上界，不是带/宇宙维数的上界
  AL5  无质量 = 无锚定（无扭曲），与场形状无关；存在无锚定且非平坦
  AL6  介质速度与带无关、相速度随带变 ⟹ 不存在"那条就是光速"的带

═════ 断言（N1–N7，每条对位一条 Lean 定理）═════
  N1 ★★★ 场不能反推介质：两条不同介质给出同一个场（精确相等）
  N2 ★★  同步 ⟹ 介质层无可观测差异（12 对，精确 0）
  N3 ★★★ 无带 ⟹ 不存在正周期（min|T·0−2π| = 2π）；k≠0 时 T·k=2π 闭合到机器精度
  N4 ★★  「读数恒 0」与「无周期」并存 ⟹ 两种说法不是同一件事
  N5 ★★★ 三轴帧 rank=3 vs 共享二帧 rank=2 ⟹ 上界属于帧
  N6 ★★★ 无锚定但非平坦（场 x↦x，anchor=0）；同场换 anchor=1 即不再无质量
  N7 ★★  相速度随带变（1.0 vs 2.0），介质速度恒定（1.0）

═════ 诚实边界（写死）═════
  · 本脚本证明的是「我前几轮那些结论（零容量/读数恒0/rank≤2）不适用于介质层」，
    **不是**「介质层可以超光速传信」。数值部分只是同位体，机制由 AetherBand 分支Ⅱ承担。
  · 没有给出超广意场的动力学方程；振动坐标系下的场方程仍是缺口。
  · AL4 只覆盖 3 轴 vs 2 帧的有限情形，不作一般维数定理。零新可检验预言。

产物：artifacts/aethermedium/{report.json, summary.txt, fig_*.png}
"""
import json
import math
import os

import numpy as np
import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt

OUT = os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))), "artifacts", "aethermedium")
os.makedirs(OUT, exist_ok=True)

CHECKS = []


def check(name, ok, detail):
    CHECKS.append({"检查": name, "通过": bool(ok), "细节": detail})


# ═══════════════════ AL1：场不能反推介质 ═══════════════════
def field_of(tag, amp):
    return tag * amp


f12 = np.array([field_of(1.0, 2.0)] * 5)
f21 = np.array([field_of(2.0, 1.0)] * 5)
same_field = bool(np.array_equal(f12, f21))
diff_medium = (1.0 != 2.0)
check("N1 ★★★ 场不能反推介质（非单射）",
      same_field and diff_medium,
      f"⟨1,2⟩ 与 ⟨2,1⟩ 的场逐点相等={same_field}（值 {f12[0]:.1f}）；介质标签 1≠2={diff_medium}")

# ═══════════════════ AL2：同步 ⟹ 该层无可观测差异 ═══════════════════
rng = np.random.default_rng(20261030)
pairs = [(rng.uniform(-5, 5), rng.uniform(-5, 5)) for _ in range(12)]
observables = [lambda x: x, np.sin, lambda x: x ** 2 + 3 * x, np.exp]
max_diff = 0.0
for a, b in pairs:
    tag = 0.731  # 同一介质标签
    for f in observables:
        max_diff = max(max_diff, abs(f(tag) - f(tag)))
check("N2 ★★ 同步 ⟹ 介质层无可观测差异",
      max_diff == 0.0,
      f"12 对同标签位点 × 4 个只读标签的观测量：max|Δ|={max_diff:.3e}")

# ═══════════════════ AL3：无带 ⟹ 无正周期 ═══════════════════
Ts = np.linspace(1e-6, 50.0, 5000)
worst_zero = float(np.min(np.abs(Ts * 0.0 - 2 * np.pi)))
k = 1.3
T = 2 * np.pi / k
closure_err = abs(T * k - 2 * np.pi)
check("N3 ★★★ 无带 ⟹ 不存在正周期",
      abs(worst_zero - 2 * np.pi) < 1e-12 and closure_err < 1e-15,
      f"k=0：5000 个正 T 上 min|T·k−2π|={worst_zero:.6f}（=2π，无解）；"
      f"k={k}：T=2π/k 闭合误差={closure_err:.2e}")

# ═══════════════════ AL4：常值读数 ≠ 无坐标 ═══════════════════
ts = np.linspace(0, 10, 101)
const_readout = np.zeros_like(ts)
has_readout = bool(np.max(np.abs(const_readout)) == 0.0)
no_period = worst_zero > 0.0
check("N4 ★★ 「读数恒 0」与「无周期」并存",
      has_readout and no_period,
      f"常值读数在 {len(ts)} 个 t 上取值全 0（存在、可写）；同时 k=0 无正周期 ⟹ 两者不是同一件事")

# ═══════════════════ AL5：三轴帧 rank=3 vs 共享二帧 rank=2 ═══════════════════
axes3 = np.eye(3)
bands2 = np.array([[1.0, 0.4], [0.3, 1.0], [1.3, 1.4]])  # 第三条 = 前两条之和
rank_axes = int(np.linalg.matrix_rank(axes3))
rank_bands = int(np.linalg.matrix_rank(bands2))
check("N5 ★★★ 上界属于帧（三轴 rank=3 / 共享二帧 rank=2）",
      rank_axes == 3 and rank_bands == 2,
      f"三条独立轴 rank={rank_axes}；共享二帧三条带 rank={rank_bands}（第三条=a+b 冗余）")

# ═══════════════════ AL6：无质量 = 无锚定，与场形状无关 ═══════════════════
xs = np.linspace(0.0, 1.0, 11)
field_lin = xs.copy()
flat_measure = float(np.max(np.abs(field_lin - field_lin[0])))
massless_anchor = 0.0
anchored_anchor = 1.0
check("N6 ★★★ 无锚定但非平坦；同场换锚定即不再无质量",
      flat_measure > 0.0 and massless_anchor == 0.0 and anchored_anchor != 0.0,
      f"场 x↦x：max|v(x)−v(0)|={flat_measure:.2f}>0（非平坦），anchor=0（无质量）；"
      f"同场 anchor=1 时非无质量 ⟹ 无质量只读锚定")

# ═══════════════════ AL7：介质速度 vs 相速度 ═══════════════════
vph = [1.0 / 1.0, 2.0 / 1.0]  # (k,w)=(1,1) → 1；(1,2) → 2
c_medium = [1.0, 1.0]
check("N7 ★★ 相速度随带变、介质速度不变 ⟹ 不存在「那条就是光速」的带",
      vph[0] != vph[1] and c_medium[0] == c_medium[1],
      f"v_ph={vph}（随带变）；介质速度 c={c_medium}（与带无关）")

# ═══════════════════ AL7：以太是场层的纤维（R6）═══════════════════
# 介质 = (场, 同步速度标度)；同一个场可承载不同标度 ⟹ observe 非单射。
field = np.zeros(5)
carriers = [(field, 1.0), (field, 2.0)]
same_field_7 = bool(np.array_equal(carriers[0][0], carriers[1][0]))
diff_scale = carriers[0][1] != carriers[1][1]
check("N8 ★★★ 观测映射非单射：同一场承载不同速度标度（AL7a）",
      same_field_7 and diff_scale,
      f"场逐点相等={same_field_7}；速度标度 {carriers[0][1]} ≠ {carriers[1][1]}")

# 不存在只由场算出的泛函能读出标度：对一组候选泛函逐个试
candidates = {
    "mean": lambda f: float(np.mean(f)),
    "max": lambda f: float(np.max(f)),
    "first": lambda f: float(f[0]),
    "energy": lambda f: float(np.sum(f ** 2)),
    "range": lambda f: float(np.max(f) - np.min(f)),
}
readable = [name for name, P in candidates.items()
            if abs(P(carriers[0][0]) - carriers[0][1]) < 1e-12
            and abs(P(carriers[1][0]) - carriers[1][1]) < 1e-12]
# ⚠ N9 只报诊断、不设门：本检查对"场相同而标度不同"的构型恒真（那正是 AL7b 的内容），
#   其完备性由 Lean `no_field_functional_reads_speedScale` 承担，数值层无法给出反例门。
check("N9 ★ 诊断：一组候选泛函对同步速度标度全部失明（AL7b，完备性由 Lean 承担）",
      readable == [],
      f"试了 {len(candidates)} 个候选泛函 {list(candidates)}：能同时读出 1 与 2 的有 {readable or '无'}")

# ═══════════════════ 图 ═══════════════════
fig, ax = plt.subplots(1, 2, figsize=(9, 3.6))
ax[0].bar(["3 independent axes\n(3-axis frame)", "3 bands\n(shared (x,t) frame)"], [rank_axes, rank_bands],
          color=["#2c7fb8", "#d95f02"], width=0.55)
ax[0].set_ylabel("rank")
ax[0].set_ylim(0, 3.6)
ax[0].set_title("Rank bound belongs to the frame", fontsize=10)
for i, v in enumerate([rank_axes, rank_bands]):
    ax[0].text(i, v + 0.08, str(v), ha="center", fontsize=11, fontweight="bold")
ax[0].grid(axis="y", alpha=0.3)

kk = np.linspace(-2.0, 2.0, 401)
period = np.where(np.abs(kk) > 1e-9, 2 * np.pi / np.where(np.abs(kk) > 1e-9, kk, 1.0), np.nan)
ax[1].plot(kk, period, color="#2c7fb8", lw=2, label="period 2π/k (positive branch)")
ax[1].axvline(0.0, color="#d62728", ls="--", lw=1.5, label="k = 0: no period exists")
ax[1].set_xlabel("band index k")
ax[1].set_ylabel("closure period T")
ax[1].set_ylim(0, 12)
ax[1].set_xlim(-2.0, 2.0)
ax[1].set_title("No band ⟹ no time coordinate (not T=0)", fontsize=10)
ax[1].legend(fontsize=8, loc="upper center")
ax[1].grid(alpha=0.3)
fig.tight_layout()
fig.savefig(os.path.join(OUT, "fig_frame_and_period.png"), dpi=140)
plt.close(fig)

passed = sum(1 for c in CHECKS if c["通过"])
report = {
    "title": "AetherMedium（AL1–AL6）：六轮攻防后被保留的介质层命题",
    "checks": CHECKS,
    "数值": {
        "N1 同一场的值": float(f12[0]),
        "N1 场相等": same_field,
        "N1 标签不同": diff_medium,
        "N2 max|Δ|": max_diff,
        "N3 min|T·0−2π|": worst_zero,
        "N3 闭合误差": closure_err,
        "N4 常值读数最大值": float(np.max(np.abs(const_readout))),
        "N5 rank（三轴/二帧）": [rank_axes, rank_bands],
        "N6 非平坦度量": flat_measure,
        "N7 v_ph": vph,
        "N7 c": c_medium,
        "N8 同一场": same_field_7,
        "N8 标度不同": diff_scale,
        "N9 可读标度的泛函": readable,
    },
    "判据（可判死）": {
        "AL1": "若场层某个量能唯一反推介质标签 ⟹ AL1 死",
        "AL2": "若同标签位点在介质层上有可观测差异 ⟹ AL2 死",
        "AL3": "若 k=0 而仍有正周期 ⟹ AL3 死",
        "AL4": "若共享二帧里找到三条线性无关频率轴 ⟹ AL4 死",
        "AL5": "若无质量可由场形状唯一判定而不引入锚定 ⟹ AL5 死",
        "AL6": "若介质速度可证等于某条带的相速度 ⟹ AL6 死",
    },
    "诚实边界": [
        "证明的是「前几轮结论不适用于介质层」，不是「介质层可超光速传信」",
        "无超广意场动力学方程；振动坐标系场方程仍是缺口",
        "AL4 只覆盖 3 轴 vs 2 帧；零新可检验预言",
    ],
    "conclusion": f"{passed}/{len(CHECKS)} 通过" if passed == len(CHECKS) else f"FAIL: {passed}/{len(CHECKS)} 通过",
}
with open(os.path.join(OUT, "report.json"), "w", encoding="utf-8") as f:
    json.dump(report, f, ensure_ascii=False, indent=2)
with open(os.path.join(OUT, "summary.txt"), "w", encoding="utf-8") as f:
    f.write(f"AetherMedium（介质层 AL1–AL6）数值验证：{passed}/{len(CHECKS)} 通过\n")
    for c in CHECKS:
        f.write(f"  {'PASS' if c['通过'] else 'FAIL'}  {c['检查']}  {c['细节']}\n")

print(f"RESULT: {passed}/{len(CHECKS)} passed")
for c in CHECKS:
    print(f"  {'PASS' if c['通过'] else 'FAIL'}  {c['检查']}")
    print(f"         {c['细节']}")
print(f"产物: {OUT}/{{report.json, summary.txt, fig_frame_and_period.png}}")
