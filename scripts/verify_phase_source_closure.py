#!/usr/bin/env python3
"""verify_phase_source_closure.py — MS5 源项闭合审计

固定模长 C=c(cos θ,sin θ) 时，MS5 要求 J=Box(C)。
本脚本计算光锥与脱光锥相位下的径向/切向 J，验证：
- 光锥相位 J=0；
- 脱光锥相位需要非零 J；
- J 的形状由 θ 给出，但 J 的物理来源仍未由框架推出。
"""
import json, math, os
import numpy as np
ART="artifacts/phasesourceclosure"; os.makedirs(ART,exist_ok=True)
x=np.linspace(-5,5,2001); k=1.7; c=1.0

def audit(v):
    # theta=k(x-vt), theta_tt=0, theta_xx=0；固定模长的 Box(C) 只剩径向项
    radial = -c * (0.0 - k*k) * 0.0  # placeholder replaced below
    # Box C radial coefficient = -c*(theta_t^2-theta_x^2)
    radial = -c*((-k*v)**2-k*k)
    tangent = 0.0
    return {"v":v,"radial_J_coefficient":radial,"tangent_J_coefficient":tangent,
            "J_zero":abs(radial)<1e-12}
rows=[audit(v) for v in (1.0,0.8,0.65,0.0)]
result={"rows":rows,"conclusion":"MS5 可接受由相位运动计算出的 J，但现有框架没有 J(C,theta) 的闭合本构关系；因此脱光锥源项是接口输入，不是自发推导。"}
with open(f"{ART}/report.json","w",encoding="utf-8") as f: json.dump(result,f,ensure_ascii=False,indent=2)
with open(f"{ART}/summary.txt","w",encoding="utf-8") as f: f.write(result["conclusion"]+"\n")
print(json.dumps(result,ensure_ascii=False,indent=2))
assert rows[0]["J_zero"]
assert all(not r["J_zero"] for r in rows[1:])
