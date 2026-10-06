#!/usr/bin/env python3
"""verify_phase_winding_anchor.py — 相位绕数能否固定 PW3 的锚定归一化？

测试闭合相位 θ=2π n x/L 与脱流包络残差 R=(1-v²) A'' 的接口。
若同一绕数 n 下归一化系数仍随包络尺度 c 变化，则绕数本身不能给出 MC1 的质量尺度。
"""
import json, math, os
import numpy as np

ART = "artifacts/phasewindinganchor"
os.makedirs(ART, exist_ok=True)
L = 2.0 * math.pi
x = np.linspace(0.0, L, 4097)

def envelope(x, c):
    # 周期化的平滑包络：1 + a cos(nx)，避免边界不闭合
    return 1.0 + 0.25 * np.cos(math.sqrt(c) * x)

def winding(n):
    theta = 2.0 * math.pi * n * x / L
    return (theta[-1] - theta[0]) / (2.0 * math.pi)

def curvature_scale(c):
    A = envelope(x, c)
    dx = x[1] - x[0]
    Axx = np.gradient(np.gradient(A, dx, edge_order=2), dx, edge_order=2)
    return float(np.max(np.abs(Axx)) / np.max(np.abs(A)))

ns = [1, 2, 3, 5]
cs = [1.0, 4.0, 9.0, 16.0]
windings = {str(n): winding(n) for n in ns}
scales = {str(c): curvature_scale(c) for c in cs}
# 对固定绕数，拓扑项 n²/L²；比较 K_shape / phase_gradient²
normalized = {
    str(n): {str(c): scales[str(c)] / ((2.0 * math.pi * n / L) ** 2) for c in cs}
    for n in ns
}
spread_by_n = {
    str(n): max(vals.values()) - min(vals.values())
    for n, vals in normalized.items()
}
result = {
    "L": L,
    "winding_numbers": windings,
    "curvature_scale_by_c": scales,
    "normalized_shape_over_phase_gradient_sq": normalized,
    "spread_by_winding": spread_by_n,
    "conclusion": "绕数闭合本身不固定 K；同一绕数下，包络曲率随 c 变化。需要额外动力学或归一化输入。"
}
with open(f"{ART}/report.json", "w", encoding="utf-8") as f:
    json.dump(result, f, ensure_ascii=False, indent=2)
with open(f"{ART}/summary.txt", "w", encoding="utf-8") as f:
    f.write(f"绕数 = {windings}\n")
    f.write(f"曲率尺度 = {scales}\n")
    f.write(f"同绕数归一化离散度 = {spread_by_n}\n")
    f.write(result["conclusion"] + "\n")
print(json.dumps(result, ensure_ascii=False, indent=2))
assert all(abs(v - round(v)) < 1e-10 for v in windings.values())
assert all(v > 1e-3 for v in spread_by_n.values())
