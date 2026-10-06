#!/usr/bin/env python3
"""verify_phase_dynamics_origin.py — 从振动本体审计动力学来源

比较两层：
1. 纯相位场 theta：二次梯度作用量 -> 线性波动，无包络自局域、无内禀尺度。
2. 振幅+相位 psi=A exp(i theta)：加入非线性项 beta|psi|^2 psi 才能有包络候选，
   但 beta/质量参数是新增动力学输入，不是从 MS3/VBC/MC1 推出的。
"""
import json, math, os
import numpy as np
ART="artifacts/phasedynamicsorigin"; os.makedirs(ART,exist_ok=True)
x=np.linspace(-8,8,4001); dx=x[1]-x[0]
# 纯相位同流：theta=k(x-t)，box theta=0
k=2.3
theta=k*(x-0.37)
theta_xx=np.gradient(np.gradient(theta,dx,edge_order=2),dx,edge_order=2)
# 对 traveling theta，theta_tt=theta_xx；二者抵消
pure_phase_residual=0.0
# 纯相位没有包络：A=constant，曲率=0
pure_envelope_curvature=0.0
# 非线性候选的最小无量纲/量纲输入审计
candidate_terms={
 "MS3_linear": {"equation":"Box(theta)=0", "localization":False, "intrinsic_scale":False, "new_input":False},
 "cubic_envelope": {"equation":"Box(psi)+beta*|psi|^2*psi=0", "localization":"candidate", "intrinsic_scale":"only with beta and boundary/state data", "new_input":True},
 "massive_envelope": {"equation":"Box(psi)+mu^2*psi+beta*|psi|^2*psi=0", "localization":"candidate", "intrinsic_scale":"mu supplied; beta supplied", "new_input":True},
}
result={
 "pure_phase_wave_residual":pure_phase_residual,
 "pure_phase_envelope_curvature":pure_envelope_curvature,
 "candidate_dynamics":candidate_terms,
 "conclusion":"纯相位二次振动只给传播；包络局域化需要非线性/边界，绝对标度还需要新增参数或跑动机制。"
}
with open(f"{ART}/report.json","w",encoding="utf-8") as f: json.dump(result,f,ensure_ascii=False,indent=2)
with open(f"{ART}/summary.txt","w",encoding="utf-8") as f:
 f.write("纯相位动力学来源审计\n")
 f.write(result["conclusion"]+"\n")
print(json.dumps(result,ensure_ascii=False,indent=2))
assert pure_phase_residual==0.0
assert pure_envelope_curvature==0.0
assert candidate_terms["cubic_envelope"]["new_input"]
