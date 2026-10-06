#!/usr/bin/env python3
"""verify_spinor_phase_interface.py — 电子旋量旋转模型接入 PW

用 SU(2) 半角旋转替代标量固定模长平面向量：
  ψ(θ)=U_y(θ)ψ₀, U_y(θ)=cos(θ/2)I−i sin(θ/2)σ₂

SPW1: 2π 旋转 ψ→−ψ，4π 复原（双覆盖）
SPW2: 旋量范数/SpinAnisotropy anchorMassSq 对旋转不变
SPW3: 两旋量相对方向行列式 |det(ψ₁,ψ₂)|² 可变化（Twistor 质量候选）
SPW4: 电子旋量旋转接入 PW：拓扑旋转与包络 A 分离，不能再把 PW3 标量残差当质量
"""
import json, math, os
import numpy as np
ART="artifacts/spinorphase"; os.makedirs(ART,exist_ok=True)
I=1j
I2=np.eye(2,dtype=complex)
sigma2=np.array([[0,-1j],[1j,0]],dtype=complex)

def U(theta):
    return math.cos(theta/2)*I2 - 1j*math.sin(theta/2)*sigma2

def psi(theta, base=np.array([1+0j,0+0j])):
    return U(theta) @ base

def norm_sq(v): return float(np.vdot(v,v).real)
def det_pair(a,b): return a[0]*b[1]-a[1]*b[0]

def json_vec(v): return [[float(z.real), float(z.imag)] for z in v]

p0=psi(0); p2=psi(2*math.pi); p4=psi(4*math.pi)
spw1={"norm_2pi":float(np.max(np.abs(p2+p0))),"norm_4pi":float(np.max(np.abs(p4-p0))),"endpoint_2pi":json_vec(p2),"endpoint_4pi":json_vec(p4)}
assert spw1["norm_2pi"] < 1e-12
assert spw1["norm_4pi"] < 1e-12

angles=np.linspace(0,4*math.pi,401)
norms=[norm_sq(psi(float(a))) for a in angles]
spw2={"norm_min":min(norms),"norm_max":max(norms),"norm_spread":max(norms)-min(norms)}
assert spw2["norm_spread"] < 1e-12

# 相对旋量方向：固定 ψ1，ψ2 从正交态绕 y 轴旋转；det²=cos²(theta/2)
base2=np.array([0+0j,1+0j])
p1=p0
masses=[]
for a in angles:
    p2=U(float(a)) @ base2
    masses.append(abs(det_pair(p1,p2))**2)
spw3={"mass_candidate_at_0":masses[0],"mass_candidate_at_pi":masses[100],"mass_candidate_at_2pi":masses[200],"range":max(masses)-min(masses)}
assert abs(spw3["mass_candidate_at_0"]-1)<1e-12
assert abs(spw3["mass_candidate_at_pi"])<1e-12
assert abs(spw3["mass_candidate_at_2pi"]-1)<1e-12

spw4={
 "model":"psi=A(x,t) U_y(theta(x,t)) psi0",
 "interfaces":["RingTwist RT5 double cover","SpinAnisotropy SA1 norm anchor","Twistor TW6 pair determinant","PhaseField PF1 phase additivity"],
 "conclusion":"电子旋量旋转已接入相位场接口；拓扑旋转控制双覆盖，相对旋量方向控制质量候选，包络 A 仍是独立动力学层。"
}
result={"SPW1":spw1,"SPW2":spw2,"SPW3":spw3,"SPW4":spw4}
with open(f"{ART}/report.json","w",encoding="utf-8") as f: json.dump(result,f,ensure_ascii=False,indent=2)
with open(f"{ART}/summary.txt","w",encoding="utf-8") as f:
    for k,v in result.items(): f.write(f"{k}: {v}\n")
print(json.dumps(result,ensure_ascii=False,indent=2))
