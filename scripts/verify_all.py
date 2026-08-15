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
                       "scripts/verify_fractal_flow.py",
                       "scripts/verify_double_slit.py",
                       "scripts/verify_glueball_coupling.py",
                       "scripts/verify_twistor.py",
                       "scripts/verify_qft_flow.py",
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

    fr = load_report("artifacts/fractal/report.json")
    if fr:
        res = fr["results"]
        check("FR: 谱域散度恒等 ∇²Φ = δ 精确",
              res["V2_flow_consistency"]["max|∇·C + δ|（谱域，精确）"] == 0.0)
        check("FR: δ* 落在 KBC 观测范围",
              res["V4_hubble_tension"]["δ* 在观测范围"])
        check("FR: 空洞内 H 提升（tension 量级）",
              0.05 < res["V5_hubble_boost"]["空洞提升 ΔH/H"] < 0.15)

    ds = load_report("artifacts/doubleslit/report.json")
    if ds:
        res = ds["results"]
        check("DS: 螺旋投影圆误差 0", res["N1_helix_projection"]["max|x²+y² − R²|（xy 投影是圆）"] == 0.0)
        check("DS: 双缝产生干涉条纹",
              res["N2_double_slit"]["解析条纹数（I > 0.5）"] > 50)
        check("DS: 观察后 = 2 道条纹",
              res["N3_observation"]["观察后亮带数"] == 2)

    gb = load_report("artifacts/glueball/report.json")
    if gb:
        res = gb["results"]
        scan = res["V2_coupling_scan"]
        check("GB: 耦合增强 ⟹ 束缚更紧（质量单调）",
              all(scan["束缚态质量"][i] < scan["束缚态质量"][i + 1]
                  for i in range(len(scan["束缚态质量"]) - 1)), scan["束缚态质量"])
        check("GB: 质量化梯度 Φ = ½v²",
              abs(res["V3_massification_gradient"]["梯度势 Φ = ½v²（SG11）"] - 0.045) < 1e-6)
        fit = res["V4_lattice_comparison"]["√N·M₀ 序列（M₀=0.93 GeV 中值）"]
        check("GB: 0++ 模型落入格点范围",
              fit["0++"][1] <= fit["0++"][0] <= fit["0++"][2], fit["0++"])
        check("GB: 2++ 模型落入格点范围（N=6=d(2)）",
              fit["2++"][1] <= fit["2++"][0] <= fit["2++"][2], fit["2++"])
        check("GB: 0-+ 模型落入格点范围",
              fit["0-+"][1] <= fit["0-+"][0] <= fit["0-+"][2], fit["0-+"])

    tw = load_report("artifacts/twistor/report.json")
    if tw:
        res = tw["results"]
        check("TW: 扭量动量无质量恒等（机器精度）",
              res["N1_momentum_massless"]["max|det(π⊗π̄)|（200 随机扭量）"] < 1e-10)
        n4 = res["N4_charge_vs_normal"]
        check("TW: 电性 = 法向量（σ₃ 本征 ±1）",
              n4["σ₃·e+ = +1·e+（电子，法向量正向）"] and
              n4["σ₃·e− = −1·e−（正电子，法向量反向）"])
        check("TW: 电荷共轭反交换 + 翻转法向量",
              n4["C·σ₃ + σ₃·C = 0（反交换）"] and n4["C 翻转法向量方向（e+ ↔ e−）"])
        check("TW: 胶子色八重态全部无质量",
              res["N5_gluon_twistor"]["全部无质量"])
        n6 = res["N6_twistor_pair_electron"]
        check("TW6: 双扭量 det = |⟨π₁,π₂⟩|²（机器精度）",
              n6["max|det(p₁+p₂) − |⟨π₁,π₂⟩|²|（200 随机对）"] < 1e-10)
        check("TW7: 电荷共轭保持双扭量质量",
              n6["电荷共轭保持质量 m²(Cπ) = m²(π)"])

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

    qf = load_report("artifacts/qftflow/report.json")
    if qf:
        res = qf["results"]
        n1 = res["N1_excitation_flow"]
        check("QFT1: 非激发 dτ² = 0（随流）", n1["非激发 = 0（机器精度）"] and
              abs(n1["非激发 dτ²（dx = c·dt，随流）"]) < 1e-12)
        check("QFT2: 激发 dτ² > 0（偏离流动）", n1["激发 > 0"] and n1["激发 dτ²（dx = 0.6c·dt，偏离）"] > 0)
        n2 = res["N2_excitation_mass"]
        check("QFT3: 激发质量 = 锚定范数（机器精度）", n2["max|m² − (|ψ₁|²+|ψ₀|²)|（200 随机旋量）"] < 1e-10)
        n4 = res["N4_global_antiphase"]
        check("QFT5: 反相恒等全域（机器精度）", n4["反相恒等 max|E − (−cos²φ)|（所有距离/位置）"] < 1e-10)
        check("QFT5: E(Δ=π) = −1 精确", n4["E(Δ=π) 精确反关联"] == 1.0)
        check("QFT5: 关联形状与距离无关（全域无衰减）", n4["形状与距离无关（max≈0, min≈−1, mean≈−½）"])
        n5 = res["N5_ghz_reduced"]
        check("QFT7: GHZ 单体约化混合（Tr ρ² = ½ < 1）",
              n5["ρ² ≠ ρ（混合态）"] and abs(n5["Tr(ρ_A²)"] - 0.5) < 1e-6 and n5["纯度 < 1（三体纠缠判据）"])
        n6 = res["N6_rank_entanglement"]
        check("QFT8: 单扭量秩 1（det = 0 机器精度）", n6["单扭量 max|det|（秩 1，非激发）"] < 1e-10)
        check("QFT8: 双扭量 det = |⟨π₁,π₂⟩|²（机器精度）",
              n6["双扭量 max|det − |⟨π₁,π₂⟩|²|（秩 2，激发）"] < 1e-10)
        check("QFT8: 平行 ⟹ m² = 0 / 正交 ⟹ m² 最大",
              n6["平行（α=0）⟹ m² = 0（无质量/可分）"] and
              n6["正交（α=π/2）⟹ m² = 最大（有质量/纠缠）"])
        n7 = res["N7_three_direction_basis"]
        check("QFT6: (σ₁+σ₂+σ₃)² = 3I（机器精度）", n7["max|(σ₁+σ₂+σ₃)² − 3I|"] == 0.0)
        check("QFT6: 三方向可逆（det = −3）", abs(n7["det(σ₁+σ₂+σ₃)"] + 3.0) < 1e-6)
        n9 = res["N9_triple_twistor_det"]
        check("GQ2: 三扭量 det₃ = |det₃[π₁π₂π₃]|²（机器精度）",
              n9["max|det₃(P) − |det₃[π₁π₂π₃]|²|（200 随机三扭量）"] < 1e-10)
        check("GQ2: Hadamard |det₃| ≤ |π₁||π₂||π₃|", n9["Hadamard: max |det₃|/(|π₁||π₂||π₃|) ≤ 1"])
        n10 = res["N10_rank_criterion"]
        check("GQ3–5: 独立 ⟹ m² = 1 / 退化 ⟹ m² = 0 / 共面 ⟹ m² = 0",
              n10["三扭量独立（单位基）⟹ m² = 1（激发）"] and
              n10["退化（π₃ = π₂）⟹ m² = 0（非激发）"] and
              n10["共面（π₃ 线性相关）⟹ m² = 0（非激发）"])
        n11 = res["N11_rank_unified"]
        check("GQ6: 统一链 N=1,2,3（质量² = |det_N|²）",
              n11["N=1 光子: det₁ = |π₁|²"] and n11["N=2 电子: det₂ = |⟨π₁,π₂⟩|²（= |det 2×2|²）"] and
              n11["N=3 胶球: det₃ = |det₃[π₁π₂π₃]|²"])
        n12 = res["N12_w_type_triplet"]
        check("GQ4b: W 型两两纠缠 ≠ 全域激发（共面 det₃ = 0）",
              n12["随机独立三扭量：三对 Plücker 全非零（W 型，200/200）"] and
              n12["共面三扭量：两两不平行但 det₃ = 0（局部纠缠 ≠ 激发）"])

    # 4. 产物完整性
    artifacts = {
        "artifacts/maxwellspace/three_fields.png": 30_000,
        "artifacts/maxwellspace/maxwell_residuals.png": 30_000,
        "artifacts/spacefield3d/vortex_curl.png": 30_000,
        "artifacts/maxwell/fig_blackhole_flow.png": 30_000,
        "artifacts/maxwell/photon_infall.gif": 500_000,
        "artifacts/entanglement/helix_3d.png": 30_000,
        "artifacts/qftflow/fig_antiphase_global.png": 30_000,
        "artifacts/qftflow/fig_triple_rank.png": 30_000,
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
