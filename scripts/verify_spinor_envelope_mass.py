#!/usr/bin/env python3
"""verify_spinor_envelope_mass.py — 包络 A 与电子旋量相对方向的统一候选

psi_i = A_i U_y(theta_i) psi0
TW6 mass candidate = |det(psi1, psi2)|^2
对于同一基础旋量，解析候选应为 |A1*A2|^2 sin^2((theta2-theta1)/2)。
这只是 TW6 接口的统一候选，不是质量定理。
"""
import json, math, os
import numpy as np
ART="artifacts/spinorenvelope"; os.makedirs(ART,exist_ok=True)
I=1j; I2=np.eye(2,dtype=complex)
sigma2=np.array([[0,-1j],[1j,0]],dtype=complex)

def U(t): return math.cos(t/2)*I2 - 1j*math.sin(t/2)*sigma2
def det(a,b): return a[0]*b[1]-a[1]*b[0]
def calc(A1,A2,t1,t2):
    p=np.array([1+0j,0+0j])
    q1=A1*(U(t1)@p); q2=A2*(U(t2)@p)
    actual=abs(det(q1,q2))**2
    predicted=(A1*A2)**2*math.sin((t2-t1)/2)**2
    return actual,predicted
rows=[]
for A1,A2,t1,t2 in [(1,.7,0,.4),(2,1.3,0,math.pi),(1.1,.9,.2,4.7),(3,.4,2*math.pi,3*math.pi)]:
    a,b=calc(A1,A2,t1,t2)
    rows.append({"A1":A1,"A2":A2,"theta1":t1,"theta2":t2,"actual":a,"predicted":b,"error":abs(a-b)})
maxerr=max(r["error"] for r in rows)
result={"rows":rows,"max_error":maxerr,"conclusion":"TW6 双旋量质量候选可分解为包络幅值因子×相对旋转方向因子；仍未给出包络动力学或绝对归一化。"}
with open(f"{ART}/report.json","w",encoding="utf-8") as f: json.dump(result,f,ensure_ascii=False,indent=2)
with open(f"{ART}/summary.txt","w",encoding="utf-8") as f: f.write(result["conclusion"]+f"\n最大误差={maxerr:.3e}\n")
print(json.dumps(result,ensure_ascii=False,indent=2))
assert maxerr<1e-12
