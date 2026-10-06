#!/usr/bin/env python3
"""verify_phase_norm_feedback.py — 固定模长空间场的相位反馈审计

取二维相位嵌入 C=c(cos θ, sin θ)。对 Box=∂t²−∂x²：
  Box C = c*n_perp*Box θ - c*n*((θt)^2-(θx)^2)
因此若同时要求 Box C=0 且 c≠0：
  n·Box C=0 => (θt)^2-(θx)^2=0（相位梯度必须光锥）
  n_perp·Box C=0 => Box θ=0
结论：固定模长 + 线性无源波动不会产生局域包络；非线性反馈只能来自
放松模长约束、源项或新增动力学。
"""
import json, math, os
import numpy as np
ART="artifacts/phasenormfeedback"; os.makedirs(ART,exist_ok=True)
x=np.linspace(-5,5,2001); t=0.37
# 相位一：光锥 traveling wave，theta=k(x-t)
k=1.7
theta_null=k*(x-t)
theta_t_null=-k; theta_x_null=k
radial_null=theta_t_null**2-theta_x_null**2
# 相位二：非光锥 travelling wave theta=k(x-vt), v=0.65
v=0.65
theta_t_off=-k*v; theta_x_off=k
radial_off=theta_t_off**2-theta_x_off**2
# amplitude localization impossible at fixed c: |C| constant by construction
out={
 "fixed_norm": "|C|=c",
 "null_phase": {"radial_BoxC_component": radial_null, "Box_theta": 0.0},
 "off_lightcone_phase": {"radial_BoxC_component": radial_off, "Box_theta": 0.0},
 "conclusion": "固定模长 C=c(cosθ,sinθ) 与无源线性波动结合时，只允许光锥相位；不会自动产生局域包络。"
}
with open(f"{ART}/report.json","w",encoding="utf-8") as f: json.dump(out,f,ensure_ascii=False,indent=2)
with open(f"{ART}/summary.txt","w",encoding="utf-8") as f: f.write(out["conclusion"]+"\n")
print(json.dumps(out,ensure_ascii=False,indent=2))
assert abs(radial_null)<1e-12
assert abs(radial_off)>1e-3
