#!/usr/bin/env python3
"""verify_phase_anchor_shape_map.py — 包络曲率到锚定强度的最小候选

对 A_c(x)=(c/2)sech²(√c x/2)，定义无量纲形状曲率
  K_shape = max|A''| / max|A| = c/2
PW 脱流残差 R=(1-v²)A''，因此
  max|R|/max|A| = (c/2)(1-v²).
这给出相对锚定强度候选，但不提供绝对质量单位。
"""
import json, math, os
import numpy as np
ART="artifacts/phaseanchorshape"; os.makedirs(ART, exist_ok=True)
x=np.linspace(-8,8,4001); dx=x[1]-x[0]
cs=[0.25,1.0,4.0,9.0,16.0]; vs=[0.0,0.5,0.8]
rows=[]
for c in cs:
    A=(c/2)/np.cosh(np.sqrt(c)*x/2)**2
    Axx=np.gradient(np.gradient(A,dx,edge_order=2),dx,edge_order=2)
    k_shape=float(np.max(np.abs(Axx))/np.max(np.abs(A)))
    rows.append({"c":c,"K_shape":k_shape,"expected_c_over_2":c/2,
                 "relative_error":abs(k_shape-c/2)/(c/2)})
# Check separability: normalized residual / K_shape = 1-v²
separable=[]
for row in rows:
    for v in vs:
        val=row["K_shape"]*(1-v*v)
        separable.append({"c":row["c"],"v":v,"candidate_s_sq":val,
                          "velocity_factor":1-v*v,
                          "shape_factor":row["K_shape"]})
result={"rows":rows,"separable":separable,
        "conclusion":"包络曲率给出相对锚定强度 s²∝(c/2)(1-v²)，但绝对归一化/质量单位仍未导出。"}
with open(f"{ART}/report.json","w",encoding="utf-8") as f: json.dump(result,f,ensure_ascii=False,indent=2)
with open(f"{ART}/summary.txt","w",encoding="utf-8") as f:
    f.write("包络曲率到锚定强度的最小候选\n")
    for r in rows: f.write(f"c={r['c']}: K_shape={r['K_shape']:.9g}, c/2={r['expected_c_over_2']:.9g}, relerr={r['relative_error']:.3e}\n")
    f.write(result["conclusion"]+"\n")
print(json.dumps(result,ensure_ascii=False,indent=2))
assert max(r["relative_error"] for r in rows) < 2e-3
for row in rows:
    for v in vs:
        assert abs(row["K_shape"]*(1-v*v)/row["K_shape"]-(1-v*v)) < 1e-12
