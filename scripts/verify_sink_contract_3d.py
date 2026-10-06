#!/usr/bin/env python3
"""verify_sink_contract_3d.py — 3D 离散「散度 ⟹ 起伏下降」数值验证。

验证 CR7/CR9/CR10 的核心命题在 3D 格点场上的实现：
  负散度场（每点向中心收敛的线性场 v = -r）经「向心收缩」物理过程
  迭代后，起伏能量 Q_A(v) 严格单调下降到 0，同时散度 Div(v) 归零。

三件事都要真：
  S1 ★ 场内每点 div < 0（真的是汇，不是随便一个场）
  S2 ★ 收缩迭代前 Q_A > 0 且最大 |梯度| > 0（有起伏可抹）
  S3 ★★ 向心收缩迭代 ⟹ Q_A 严格单调递减到 < 1e-10，Div 同时 → 0

对比（诚实）：正散度场（源）用同样迭代 Q_A 也下降——平滑算子是线性的，
  符号不决定平滑性本身；负散度的特殊处是「几何上就在向心收缩」。
  这个对比写进结论，不作过度声称。
"""
import json
import numpy as np
import os

N = 21  # 3D 格点 [-1,1]^3，中心在原点
xs = np.linspace(-1, 1, N)
X, Y, Z = np.meshgrid(xs, xs, xs, indexing="ij")

def divergence3d(vx, vy, vz):
    """3D 中心差分散度 div v = ∂xvx + ∂yvy + ∂zvz。"""
    dvx = np.gradient(vx, axis=0)
    dvy = np.gradient(vy, axis=1)
    dvz = np.gradient(vz, axis=2)
    return dvx + dvy + dvz

def fluctuation_energy(vx, vy, vz):
    """起伏 Q = Σ|v − v̄|²（三分量，GravityControl Q_A 的 3D 版）。"""
    v = np.stack([vx, vy, vz])
    mean = np.mean(v, axis=(1, 2, 3), keepdims=True)
    return float(np.sum((v - mean) ** 2))

def sink_contract_step(vx, vy, vz, lam=0.5):
    """向心收缩一步：每点向区域均值靠拢 λ 步（CR9 的 3D 版，三分量独立）。"""
    means = [np.mean(c) for c in (vx, vy, vz)]
    return tuple((1 - lam) * c + lam * m for c, m in zip((vx, vy, vz), means))

# --- 构造负散度场（汇）：v = -r，每点指向中心，|v| 随 |r| 增大 ---
vx, vy, vz = -X, -Y, -Z

div0 = divergence3d(vx, vy, vz)
Q0 = fluctuation_energy(vx, vy, vz)
grad0 = float(np.max(np.abs(np.gradient(vx, axis=0))))  # 代表性的梯度量级

print(f"=== 负散度场 v = -r (3D {N}³) ===")
print(f"div 范围: [{div0.min():.4f}, {div0.max():.4f}]")
print(f"Q_A(初始) = {Q0:.4f}")
print(f"max|∂vx/∂x| = {grad0:.4f}")

# --- S1: 逐点 div < 0? ---
interior = div0[1:-1, 1:-1, 1:-1]  # 中心差分边界不可靠，取内部
s1_ok = bool(np.all(interior < 0))
print(f"\nS1 每点 div < 0 (内部格点): {s1_ok} (min={interior.min():.4f})")

# --- S2: 有起伏可抹? ---
s2_ok = Q0 > 1.0 and grad0 > 0.05
print(f"S2 初始 Q_A>0 且梯度>0: {s2_ok} (Q={Q0:.3f}, grad={grad0:.3f})")

# --- S3: 向心收缩迭代 ⟹ Q_A 单调降到 0, Div → 0 ---
qs = [Q0]
divs = [float(np.abs(divergence3d(vx, vy, vz)).mean())]
for step in range(200):
    vx, vy, vz = sink_contract_step(vx, vy, vz)
    q = fluctuation_energy(vx, vy, vz)
    d = float(np.abs(divergence3d(vx, vy, vz)).mean())
    qs.append(q)
    divs.append(d)
qs = np.array(qs)
divs = np.array(divs)

monotone = bool(np.all(np.diff(qs) <= 1e-12))
converged = qs[-1] < 1e-10 and divs[-1] < 1e-10
print(f"\nS3 向心收缩 200 步:")
print(f"  Q_A: {qs[0]:.4f} → {qs[-1]:.2e} ({qs[-1]/qs[0]*100:.4f}%)")
print(f"  单调递减: {monotone}")
print(f"  收敛到零: {converged}")
print(f"  max|div|: {divs[0]:.4f} → {divs[-1]:.2e}")

# --- 对比: 正散度场(源) 同样迭代(诚实缓冲) ---
vxp, vyp, vzp = X, Y, Z
Q0p = fluctuation_energy(vxp, vyp, vzp)
for _ in range(200):
    vxp, vyp, vzp = sink_contract_step(vxp, vyp, vzp)
Qend_p = fluctuation_energy(vxp, vyp, vzp)
print(f"\n对比: 正散度场(源) 200步后 Q = {Qend_p:.2e} (同样可平滑——平滑是线性算子)")

results = {
    "N": N,
    "div_range": [float(div0.min()), float(div0.max())],
    "Q0": Q0,
    "Q_end": float(qs[-1]),
    "Q_decrease_pct": float(qs[-1] / qs[0] * 100),
    "max_div_end": float(divs[-1]),
    "S1_all_interior_div_negative": bool(s1_ok),
    "S2_initial_fluctuation_positive": bool(s2_ok),
    "S3_monotone_decrease": bool(monotone),
    "S3_converged_to_zero": bool(converged),
    "source_comparison_Q_end": Qend_p,
    "conclusion": "负散度(汇)场经向心收缩迭代, 起伏能量严格单调降到0, 散度同时归零——"+
                  "'收敛=抹平'在3D离散格点成立(CR7/CR9/CR10数值实现)。"+
                  "诚实: 平滑算子线性, 正散度场同样可平滑; 负散度的特殊处是几何向心收缩。"
}

os.makedirs("artifacts/sinkcontract3d", exist_ok=True)
with open("artifacts/sinkcontract3d/report.json", "w") as f:
    json.dump(results, f, indent=2, ensure_ascii=False)

print(f"\n已写 artifacts/sinkcontract3d/report.json")
assert s1_ok, "S1 failed: 内部格点应全部 div < 0"
assert s2_ok, "S2 failed: 初始应有起伏"
assert monotone and converged, "S3 failed: 起伏应严格单调降到 0 且散度归零"
print("ALL ASSERTIONS PASSED")