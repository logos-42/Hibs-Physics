#!/usr/bin/env python3
"""verify_phase_anchor_interface.py — PW 残差与 MC1 锚定强度的对位诊断

目标不是把残差直接命名为质量，而是测试最后一跳：
  PW3 residual(v) = K * (1-v²/c²)
  MC1 anchorMassSq(s) = s²

如果残差要等于锚定质量平方，必须额外指定 s(v)=sqrt(K)*sqrt(1-v²/c²)。
这会把“相等”拆成：形状比例已知、归一化 K 未知、s 的定义未闭合。
"""
import json, math, os

ART = "artifacts/phaseanchor"
os.makedirs(ART, exist_ok=True)
velocities = [0.0, 0.25, 0.5, 0.65, 0.8, 0.95]
K = 0.24993334844133586  # PW5 c=1 包络的曲率归一化
residual = [K * (1.0 - v*v) for v in velocities]

# 三种口径：
# 1) s=1-v：MC1 锚定平方不匹配；
# 2) s=1-v²：仍不匹配；
# 3) s=sqrt(residual)：逐点匹配，但这是反向定义，不是推导。
candidates = {
    "s=1-v": [ (1-v)**2 for v in velocities ],
    "s=1-v²": [ (1-v*v)**2 for v in velocities ],
    "s=sqrt(PW3)": residual[:],
}
errors = {}
for name, values in candidates.items():
    errors[name] = max(abs(a-b) for a,b in zip(values, residual))

result = {
    "K": K,
    "velocities": velocities,
    "PW3_residual": residual,
    "candidate_anchorMassSq": candidates,
    "max_abs_error": errors,
    "required_strength": [math.sqrt(x) for x in residual],
    "conclusion": "PW3 与 1-v² 的形状已对齐，但 MC1 的 s 及归一化 K 仍是输入；s=sqrt(PW3) 是定义匹配，不是推导。",
}
with open(f"{ART}/report.json", "w", encoding="utf-8") as f:
    json.dump(result, f, ensure_ascii=False, indent=2)
with open(f"{ART}/summary.txt", "w", encoding="utf-8") as f:
    f.write(f"K = {K:.15g}\n")
    f.write(f"候选最大误差 = {errors}\n")
    f.write(f"所需 s(v) = sqrt(PW3) = {result['required_strength']}\n")
    f.write(result["conclusion"] + "\n")
print(json.dumps(result, ensure_ascii=False, indent=2))
assert errors["s=1-v"] > 1e-3
assert errors["s=1-v²"] > 1e-3
assert errors["s=sqrt(PW3)"] == 0.0
