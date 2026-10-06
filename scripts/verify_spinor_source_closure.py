#!/usr/bin/env python3
"""SPC: audit whether the existing source slot J can close through the spinor model.

The existing MS5 has Box(C)=J but no J(C,psi) constitutive law.  Use the already
verified SEM candidate q=|A1*A2|^2 sin^2(dtheta/2), then test the only natural
closure form J=kappa*q.  The result deliberately exposes kappa as an input.
"""
import json, math, os
ART="artifacts/spinorsourceclosure"; os.makedirs(ART,exist_ok=True)
rows=[]
for A1,A2,dt in [(1,.7,.4),(2,1.3,math.pi),(1.1,.9,4.5)]:
    q=(A1*A2)**2*math.sin(dt/2)**2
    rows.append({"A1":A1,"A2":A2,"delta_theta":dt,"spinor_q":q,
                 "J_kappa_1":q,"J_kappa_2":2*q})
result={"rows":rows,"closure":"J=kappa*|det(psi1,psi2)|^2",
        "kappa_is_input":True,
        "conclusion":"旋量质量候选可作为 MS5 源项形状，但绝对耦合 kappa 未由现有公设推出；源闭合仍未完成。"}
with open(f"{ART}/report.json","w",encoding="utf-8") as f: json.dump(result,f,ensure_ascii=False,indent=2)
with open(f"{ART}/summary.txt","w",encoding="utf-8") as f: f.write(result["conclusion"]+"\n")
print(json.dumps(result,ensure_ascii=False,indent=2))
assert result["kappa_is_input"]
