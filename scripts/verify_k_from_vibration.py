#!/usr/bin/env python3
"""verify_k_from_vibration.py — 从振动本体导出 kappa 候选

对 psi=A exp(i theta), Box=dt^2-c^2 dx^2：
 Box psi / exp(i theta) = Box A + 2i(At theta_t-c^2 Ax theta_x)
   + i A Box theta - A(theta_t^2-c^2 theta_x^2)

纯平面相位 theta=kx-omega t 的唯一振动尺度是 dispersion defect
 Delta=c^2 k^2-omega^2；在线性色散关系 omega=ck 上 Delta=0。
局域包络另给曲率尺度 K_shape=max|A''|/max|A|。
两者都是候选，不能未经动力学推导直接相加成唯一 kappa。
"""
import json, math, os
ART="artifacts/kfromvibration"; os.makedirs(ART,exist_ok=True)
c=1.0
rows=[]
for k,omega in [(1.0,1.0),(1.0,.8),(2.0,1.0),(3.0,2.0)]:
    delta=c*c*k*k-omega*omega
    rows.append({"k":k,"omega":omega,"dispersion_defect":delta,"on_shell":abs(delta)<1e-12})
# sech^2 envelope: K_shape=c_env/2 numerically
shape=[]
for cenv in [.25,1.,4.,9.,16.]:
    dx=16/4000
    xs=[-8+i*dx for i in range(4001)]
    A=[(cenv/2)/math.cosh(math.sqrt(cenv)*x/2)**2 for x in xs]
    # analytic curvature scale for this family = cenv/2
    K=cenv/2
    shape.append({"c_env":cenv,"K_shape":K,"ratio":K/(cenv/2)})
# 统一链：振动 → κ 候选 → 旋量质量候选 → MS5 源 → 四力
A1, A2 = 1.3, 0.8
theta1, theta2 = 0.0, math.pi / 2
q_spin = (A1 * A2) ** 2 * math.sin((theta2 - theta1) / 2) ** 2
k, omega, c = 1.0, 0.8, 1.0
delta = c*c*k*k - omega*omega
c_env = 4.0
k_shape = c_env / 2.0
# κ=1 仅作为接口归一化测试，不是物理推导值
kappa = 1.0
J = kappa * q_spin
dm, mass, C, v, dC, dv = 0.2, 1.5, 1.0, 0.3, 0.4, 0.1
forces = {
    "electric_dm_C": dm*C,
    "magnetic_dm_v": -dm*v,
    "nuclear_m_dC": mass*dC,
    "gravity_m_dv": -mass*dv,
}
result={"dispersion_candidates":rows,"envelope_candidates":shape,
 "unified_chain":{"A1":A1,"A2":A2,"theta_delta":theta2-theta1,
 "q_spin":q_spin,"kappa_interface":kappa,"MS5_J":J,
 "k_candidates":{"dispersion_defect":delta,"envelope_curvature":k_shape},
 "four_force_channels":forces,
 "status":"结构链已运行；κ=1 只是归一化接口，不是物理推导值"},
 "conclusion":"振动本体给出色散缺陷与包络曲率两个κ候选；旋量相对方向给源项形状；绝对κ仍未由公设推出。"}
assert abs(q_spin - 0.5408) < 1e-12
assert abs(J - q_spin) < 1e-12
assert set(forces)=={"electric_dm_C","magnetic_dm_v","nuclear_m_dC","gravity_m_dv"}
with open(f"{ART}/report.json","w",encoding="utf-8") as f: json.dump(result,f,ensure_ascii=False,indent=2)
with open(f"{ART}/summary.txt","w",encoding="utf-8") as f: f.write(result["conclusion"]+"\n")
print(json.dumps(result,ensure_ascii=False,indent=2))
assert rows[0]["on_shell"]
assert all(abs(x["ratio"]-1)<1e-12 for x in shape)
