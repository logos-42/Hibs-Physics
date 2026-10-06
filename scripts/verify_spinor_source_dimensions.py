#!/usr/bin/env python3
"""Audit dimensions of the SEM -> MS5 source closure.

q_spin=|det(psi1,psi2)|^2 is dimensionless after normalized spinors.
MS5's J has the dimensions of Box(C), so J=kappa*q_spin requires kappa
with the dimensions of Box(C). This is an input unless derived elsewhere.
"""
import json, os
ART="artifacts/spinorsourcedim"
os.makedirs(ART, exist_ok=True)
result={
 "q_spin": {"dimension":"1", "origin":"normalized spinor relative direction"},
 "MS5_J": {"dimension":"[Box(C)]", "origin":"space-field source term"},
 "kappa": {"required_dimension":"[Box(C)]", "derived":False},
 "conclusion":"SEM supplies a dimensionless source shape; MS5 requires kappa with Box(C) dimensions. The closure is structural, not parameter-free."
}
with open(f"{ART}/report.json","w",encoding="utf-8") as f: json.dump(result,f,ensure_ascii=False,indent=2)
with open(f"{ART}/summary.txt","w",encoding="utf-8") as f: f.write(result["conclusion"]+"\n")
print(json.dumps(result,ensure_ascii=False,indent=2))
assert result["q_spin"]["dimension"] == "1"
assert result["kappa"]["derived"] is False
