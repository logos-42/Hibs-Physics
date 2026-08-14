#!/usr/bin/env python3
"""ProjectionPhysics 统一验证门禁（canonical test command）。

用法：  python3 scripts/verify_all.py        # 全量（lake build + 全部数值脚本 + 断言）
        python3 scripts/verify_all.py --fast # 只 lake build + 零 sorry/admit + 已有报告断言

内容：
  0. lake build 全绿（仓库 canonical 门禁，lefthook 提交钩子同款）
  1. 零 sorry/admit（全部 .lean 文件扫描）
  2. 数值脚本重跑（MaxwellSpace / SpaceField3D / MaxwellFlow / Entanglement / BlackHole）
  3. 关键物理断言（各脚本 report.json 的回归锚点——数字基准不可改）
  4. 产物完整性（artifacts/ 关键文件存在且非空）

注意：这是仓库自己的门禁（AGENTS.md 惯例），不是外部测试套件。
"""

import json
import os
import subprocess
import sys

REPO = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
FAILS = []


def check(name, cond, detail: object = ""):
    tag = "PASS" if cond else "FAIL"
    print(f"{tag} {name}" + (f"  [{detail}]" if detail else ""))
    if not cond:
        FAILS.append(name)


def run(cmd, cwd=REPO, timeout=420):
    return subprocess.run(cmd, cwd=cwd, capture_output=True, text=True, timeout=timeout)


def load_report(rel):
    p = os.path.join(REPO, rel)
    return json.load(open(p, encoding="utf-8")) if os.path.exists(p) else None


def main():
    fast = "--fast" in sys.argv

    # 0. lake build（canonical 门禁）
    r = run(["lake", "build"])
    check("lake build 全绿", r.returncode == 0 and
          "Build completed successfully" in r.stdout + r.stderr,
          r.returncode)

    # 1. 零 sorry/admit（排除注释：/-! 块注释 + -- 行注释）
    import re
    lean_files = []
    for root, _dirs, files in os.walk(os.path.join(REPO, "ProjectionPhysics")):
        for f in files:
            if f.endswith(".lean"):
                lean_files.append(os.path.join(root, f))
    bad = []
    for p in lean_files:
        src = open(p, encoding="utf-8").read()
        src_nc = re.sub(r"/-!.*?-/", "", src, flags=re.S)  # 删块注释
        for line in src_nc.splitlines():
            if line.lstrip().startswith("--"):
                continue
            for kw in ("sorry", "admit"):
                if kw in line:
                    bad.append(f"{os.path.relpath(p, REPO)}:{kw}")
    check(f"零 sorry/admit（{len(lean_files)} 个 Lean 文件，注释排除）", not bad, "; ".join(bad[:3]))

    # 2. 数值脚本重跑（--fast 跳过重跑，用已有报告）
    if not fast:
        for script in ["scripts/verify_maxwell_space.py",
                       "scripts/verify_spacefield3d.py",
                       "scripts/verify_spin_from_space.py",
                       "scripts/verify_maxwell_flow.py",
                       "scripts/verify_entanglement_helix.py",
                       "scripts/verify_blackhole_wormhole.py"]:
            r = run(["python3", script], timeout=420)
            check(f"{os.path.basename(script)} exit 0", r.returncode == 0, r.returncode)

    # 3. 关键物理断言（回归锚点，数字基准不可改）
    ms = load_report("artifacts/maxwellspace/report.json")
    if ms:
        res = ms["results"]
        check("MS: C 波包 v = c", abs(res["space_field_wave"]["C 波包速度"] - 1.0) < 0.01,
              res["space_field_wave"]["C 波包速度"])
        ma = res["maxwell_automatic"]
        check("MS: 法拉第残差 = 0（解析+数值）",
              ma["法拉第残差（解析行波，应 ≈ 0）"] == 0.0 and ma["法拉第残差（数值 leapfrog）"] == 0.0)
        check("MS: 安培残差 = 0（解析+数值）",
              ma["安培残差（解析行波，应 ≈ 0）"] == 0.0 and ma["安培残差（数值 leapfrog）"] == 0.0)

    s3 = load_report("artifacts/spacefield3d/report.json")
    if s3:
        res = s3["results"]
        dc = res["div_curl_zero_SF1"]["max|div(curl C)| (3 随机种子)"]
        check("SF3D: div(curl C) 机器精度 0（3 seeds）", all(abs(v) < 1e-12 for v in dc), dc)
        check("SF3D: curl(grad f) 机器精度 0",
              abs(res["curl_grad_zero_SF2"]["max|curl(grad f)|"]) < 1e-12)
        check("SF3D: 涡旋场 div B = 0",
              res["vortex_curl_SF5"]["涡旋场 max|div(B = curl C)|"] == 0.0)

    sp = load_report("artifacts/spinspace/report.json")
    if sp:
        res = sp["results"]
        ca = res["clifford_algebra"]
        check("SFS: Clifford 代数 7 项全 true", all(ca[k] is True for k in ca if k != "note"))
        check("SFS: e^{iπσ₁} = −I（旋转 π 变号）",
              res["double_cover"]["e^{iπσ₁} = −I（旋转 π）"])
        check("SFS: 2π 复原 / 4π 还原",
              res["double_cover"]["e^{2iπσ₁} = +I（旋转 2π 复原）"] and
              res["double_cover"]["旋量旋转 π 变号（费米子 2π 不还原，4π 还原）"])

    mf = load_report("artifacts/maxwell/report.json")
    if mf:
        res = mf["results"]
        check("MF: 波包 v = c", abs(res["base_maxwell"]["wavepacket_speed (FDTD)"] - 1.0) < 0.01,
              res["base_maxwell"]["wavepacket_speed (FDTD)"])
        bh = res["blackhole_flow"]
        check("MF: |C| = c 恒", bh["|C| = c max deviation"] == 0.0 and
              bh["|C| = c max deviation (inside)"] == 0.0)
        check("MF: dτ² = 0 恒", bh["max |dτ²| along flowline"] == 0.0)
        check("MF: P1 内部流线入奇点", bh["inside flowline reaches singularity"])
        check("MF: P2 红移方向（ω₂ < ω₁）", res["redshift_P2"]["ω₂/ω₁ (flow, MF5)"] < 1.0)
        check("MF: P3 视界横向模消失", res["transverse_mode_P3"]["v_t(r<r_h)"] == 0.0)
        iso = res["isotropy_P4"]
        check("MF: P4 各向同性", iso["max |v_photon| over directions"] == 1.0 and
              iso["min |v_photon| over directions"] == 1.0)

    eh = load_report("artifacts/entanglement/report.json")
    if eh:
        res = eh["results"]
        chsh = res["CHSH"]
        check("EH: E(π/8) 螺旋解析 = −0.5",
              abs(res["E_delta_checks"]["Δ=22.5°"]["helix_analytic"] + 0.5) < 0.01,
              res["E_delta_checks"]["Δ=22.5°"]["helix_analytic"])
        check("EH: |S_螺旋| ≈ 2（饱和局域界）",
              abs(chsh["helix_model"] - 2.0) < 0.05, chsh["helix_model"])
        check("EH: 量子 |S| ≈ 2√2",
              abs(chsh["quantum"] - 2.8284) < 0.05, chsh["quantum"])
        check("EH: LHV 界 = 2", chsh["lhv_bound"] == 2.0)

    # 4. 产物完整性
    artifacts = {
        "artifacts/maxwellspace/three_fields.png": 30_000,
        "artifacts/maxwellspace/maxwell_residuals.png": 30_000,
        "artifacts/spacefield3d/vortex_curl.png": 30_000,
        "artifacts/maxwell/fig_blackhole_flow.png": 30_000,
        "artifacts/maxwell/photon_infall.gif": 500_000,
        "artifacts/entanglement/helix_3d.png": 30_000,
        "artifacts/blackhole/fig_flow_structures.png": 30_000,
    }
    for rel, mb in artifacts.items():
        p = os.path.join(REPO, rel)
        check("产物 " + os.path.basename(rel),
              os.path.exists(p) and os.path.getsize(p) > mb,
              os.path.getsize(p) if os.path.exists(p) else "missing")

    print("\nRESULT:", "ALL PASS" if not FAILS else f"{len(FAILS)} FAILURES: {FAILS}")
    sys.exit(0 if not FAILS else 1)


if __name__ == "__main__":
    main()
