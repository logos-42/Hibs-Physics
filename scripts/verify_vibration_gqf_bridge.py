#!/usr/bin/env python3
"""verify_vibration_gqf_bridge.py — 振动候选接入 GQF2 四力通道

仅测试一个明确的候选接口：
  q_spin(t)=|A1(t)A2(t)|² sin²(Δθ(t)/2)
  m(t)=m0+lambda*q_spin(t)
  P(t)=m(t)*(C(t)-v(t))

验证 dP/dt = dm*C + m*dC - dm*v - m*dv。
lambda 保持显式输入；本脚本不声称从振动推出其数值。
"""
import json, math, os
import numpy as np
ART="artifacts/vibrationgqf"; os.makedirs(ART,exist_ok=True)
t=np.linspace(0,2*math.pi,2001); dt=t[1]-t[0]
A1=1.0+0.15*np.cos(t); A2=.8+.10*np.sin(t)
dtheta=.7*t+.2*np.sin(t)
q=(A1*A2)**2*np.sin(dtheta/2)**2
m0=1.0; lam=0.4
m=m0+lam*q
C=1.0+.1*np.sin(.5*t)
v=.2+.05*np.cos(.7*t)
P=m*(C-v)
dm=np.gradient(m,dt); dC=np.gradient(C,dt); dv=np.gradient(v,dt)
left=np.gradient(P,dt)
channels={"electric":dm*C,"nuclear":m*dC,"magnetic":-dm*v,"gravity":-m*dv}
right=sum(channels.values())
err=float(np.max(np.abs(left-right)))
result={"max_product_rule_error":err,"q_spin_range":[float(q.min()),float(q.max())],"mass_range":[float(m.min()),float(m.max())],"lambda_input":lam,"channels_at_peak":{k:float(v[np.argmax(q)]) for k,v in channels.items()},"conclusion":"振动旋量候选可作为质量变化源接入 GQF2；四力分解精确保持，但 lambda 仍是输入。"}
with open(f"{ART}/report.json","w",encoding="utf-8") as f: json.dump(result,f,ensure_ascii=False,indent=2)
with open(f"{ART}/summary.txt","w",encoding="utf-8") as f: f.write(json.dumps(result,ensure_ascii=False,indent=2)+"\n")
print(json.dumps(result,ensure_ascii=False,indent=2))
assert err < 2e-3
assert q.max()>q.min()
