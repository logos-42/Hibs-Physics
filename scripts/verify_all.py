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
import math
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
                       "scripts/verify_blackhole_wormhole.py",
                       "scripts/verify_space_extensibility.py",
                       "scripts/verify_space_fold.py",
                       "scripts/measure_fold_topology.py",
                       "scripts/verify_mass_cancellation.py",
                       "scripts/verify_space_modulation.py",
                       "scripts/verify_time_freeze.py",
                       "scripts/verify_plasma_antigravity.py",
                       "scripts/verify_plasma_dynamics.py",
                       "scripts/verify_plasma_fusion.py",
                       "scripts/verify_frc_compact.py",
                       "scripts/verify_hidden_qft.py",
                       "scripts/verify_fusion_roadmap.py",
                       "scripts/verify_gravity_control.py",
                       "scripts/verify_mu_dynamics.py",
                       "scripts/verify_moire_field.py",
                       "scripts/verify_device_first_principles.py",
                       "scripts/verify_diagnostics_ladder.py",
                       "scripts/verify_buildability.py",
                       "scripts/verify_program_gates.py",
                       "scripts/verify_glueball_ring_twist.py",
                       "scripts/verify_tl3_jones.py",
                       "scripts/fig_ring_twist_understanding.py",
                       "scripts/fig_twisted_ring_math.py",
                       "scripts/fig_braid_ring_spacetime.py",
                       "scripts/world_feed.py"]:
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
        n13 = res["N13_general_N_identity"]
        check("GQN2: 一般 N 恒等 det = |detₙ|²（N=2..8）",
              n13["max|det_N(P) − |detₙ[π₁...π_N]|²|（N=2..8 × 100 随机）"] < 1e-5)
        check("GQN2: Hadamard（所有 N）", n13["Hadamard |det| ≤ Π|πᵢ|（所有 N）"])
        check("GQN3–4: 满秩 ⟹ 激发 / 退化 ⟹ 非激发（N=2..7）",
              res["N14_general_N_rank"]["满秩 ⟹ det > 0 / 退化 ⟹ det = 0（N=2..7）"])
        n15 = res["N15_general_N_chain"]
        check("GQN5: 统一链 N=1..6（m² = |det_N|²）", n15["全部 m² = |det_N|²（机器精度）"])
        n16 = res["N16_cauchy_binet_2d"]
        check("GQM1: n=2, m=3..8 Cauchy-Binet（Σ|⟨πᵢ,πⱼ⟩|²）",
              n16["max|det(P) − Σ_{i<j}|⟨πᵢ,πⱼ⟩|²|（n=2, m=3..8）"] < 1e-8)
        n17 = res["N17_cauchy_binet_3d"]
        check("GQM3: n=3, m=4..7 Cauchy-Binet（Σ|det₃[π_S]|²）",
              n17["max|det(P) − Σ|det₃[π_S]|²|（n=3, m=4..7）"] < 1e-8)
        n18 = res["N18_cauchy_binet_general"]
        check("GQM: 一般 n×m 完整 Cauchy-Binet（360 样本）",
              n18["max|det(AA†) − Σ_S|det(A[:,S])|²|（n=2..4, m=n+1..n+4 × 30）"] < 1e-6)
        n19 = res["N19_gqs1_finset_2d_any_m"]
        check("GQS1: n=2 任意 m Finset 版（Σ_{i<j}|⟨πᵢ,πⱼ⟩|²，210 样本）",
              n19["max|det(P) − Σ_{i<j}|⟨πᵢ,πⱼ⟩|²|（m=3..12 × 30）"] < 1e-8)
        n20 = res["N20_gqs3_expansion_core"]
        check("GQS3: 一般 n 展开核（Σ_{r 单射}(∏A)·star(det M_r)）",
              n20["max|det(AA†) − Σ_{r 单射}(∏A)·star(det M_r)|（n=2..3, m=3..5 × 20）"] < 1e-8)
        n21 = res["N21_lattice_N_vs_Cmn"]
        check("N21: 格点 N 序列命中检测（3=C(3,2), 6=C(4,2) 命中；7 仅平凡 C(7,1)）",
              "C(3,2)=3" in n21["格点 N 序列命中检测"]["0++"]
              and "C(4,2)=6" in n21["格点 N 序列命中检测"]["2++"]
              and n21["格点 N 序列命中检测"]["0-+"] == ["C(7,1)=7"])
        check("N21: 等幅均匀 n=2 恒等（det(P) = Σ_{i<j}sin²）",
              all(abs(v["det(P)"] - v["Σsin²"]) < 1e-8 for v in n21["等幅均匀 n=2 det(P)（纠缠加法）"].values()))
        n22 = res["N22_unitary_transport_info"]
        check("GQC1: 流动传播信息守恒 det((UA)(UA)†) = det(AA†)（酉传输）",
              n22["det((UA)(UA)†) = det(AA†) 最大误差（方阵 n=2..4 × 25）"] < 1e-8
              and n22["传输公式 (UA)(UA)† = U(AA†)U† 最大误差（n=2..4 × 25）"] < 1e-8)
        check("GQC1: 子式逐项守恒（每个子纠缠体积 |det(U·A[:,S])|² 随流不变）",
              all(v["max|子式|det|² 差|"] < 1e-8 for v in n22["矩形版（m>n 叠加）det 守恒 + 子式逐项守恒"].values())
              and n22["双扭量辛内积逐对 |⟨Uπᵢ,Uπⱼ⟩|² 守恒最大误差（100 样本）"] < 1e-8)
        n23 = res["N23_causal_lightcone"]
        check("GQC2: 光锥（带宽≤1 ⟹ t 步带宽≤t，光锥外传播核为零）",
              all(v["最大带宽违规元数"] == 0 for v in n23["链跳跃光锥（带宽≤1 ⟹ t 步带宽≤t，违规元数全 0）"].values())
              and all(v["带宽-1 随机矩阵 t≤5 步光锥外最大|传播核|"] == 0.0
                      for v in n23["随机带宽-1 矩阵光锥外传播核（全 0）"].values()))
        check("GQC2: 酉多步信息守恒 det((U^t A)(U^t A)†) = det(AA†)",
              n23["酉多步信息守恒 det((U^t A)(U^t A)†) = det(AA†) 最大误差（t=2,3,5）"] < 1e-8)
        n24 = res["N24_equivalent_superluminal"]
        check("GQC3: 等效超光速 = 几何描述（均匀流动等效速度 = 1+v，信号相对流动仍 ≤ 1）",
              all(abs(u["等效速度（最快信号，=1+v）"] - u["理论 1+v"]) < 1e-6
                  and u["扩散速度对照（随机游走）"] < u["等效速度（最快信号，=1+v）"]
                  for u in n24["均匀流动：等效速度 = 1 + v（模拟 vs 理论）"].values())
              and n24["非均匀流动（黑洞雨速类比）"]["信号相对流动速度保持 ≤ 1（局部因果）"])
        check("GQC3: 黑洞雨速类比（视界处 v=1，等效速度 = 1+v_local 超光速区域）",
              n24["非均匀流动（黑洞雨速类比）"]["等效速度 > 1 的格点数（等效超光速区域）"] > 0
              and n24["非均匀流动（黑洞雨速类比）"]["等效速度 1+v_local 最大"] > 1.0)
        n25 = res["N25_flow_momentum_four_forces"]
        check("GQF: 四力分解 dP/dt = (dm)C + m(dC) − (dm)v − m(dv)（product rule 四项）",
              n25["四力分解 dP/dt = (dm)C + m(dC) − (dm)v − m(dv) 最大误差（30 序列 × 99 步）"] < 1e-8)
        check("GQF: 质量 = 位移条数（锚定加法 m = √N·M₀ 命中格点 N 序列 3,6,7）",
              all("✓" in v["格点 N 序列命中"] for k, v in
                  n25["质量 = 位移条数（m² = |det_N|² vs 条数加法）"].items() if k in ("3", "6", "7")))
        n26 = res["N26_photon_structure"]
        check("GQP: 光子模型 B 环向抵消 + 无质量（类光）+ 随流",
              n26["模型 B 环向动量抵消（y 叠加最大幅度）"] == 0.0
              and n26["无质量判据 E² = |p|²（轴向光速，c=1）"]
              and n26["光子随流（位移 = 流动位移，v_flow = c）"])
        n27 = res["N27_photon_energy_matching"]
        check("GQR: 光子能量匹配 E = ħω = h·f = 每圈角动量 × 每秒圈数",
              n27["E = ħω 数值匹配相对误差"] < 1e-10
              and abs(n27["E = 每圈角动量 h × 每秒圈数 f（螺旋解释）"] - n27["E = h·f（普朗克-爱因斯坦，f = 5e14 Hz）"]) < 1e-30)
        n28 = res["N28_glueball_quark_matching"]
        check("N28: 胶球条数匹配（三方向锚定 m = √3·M₀）+ 统一三链条（3→3→3，8=2³）",
              n28["三方向锚定 det₃（正交单位）"] == 1.0
              and n28["锚定加法 m² = 3·M₀² ⟹ m = √3·M₀（0++ 命中）"] == 1.732051
              and n28["统一三链条匹配表"]["胶子数（色八重态 adjoint 表示）"] == 8
              and n28["统一三链条匹配表"]["Cℓ(6) 旋量维数 2³"] == 8)
        n29 = res["N29_circumference_wavelength"]
        check("GQR4-6: 圆周 = 波长（ħ = r·p 复现真实 ħ，德布罗意 + 普朗克-爱因斯坦从螺旋几何涌现）",
              abs(n29["h/ħ（= 2π = 单位圆周长）"] - 2 * math.pi) < 1e-6
              and float(n29["真实 ħ 相对误差"]) < 1e-6
              and float(n29["E = pc = hf 相对误差"]) < 1e-6)
        n30 = res["N30_G_and_e_structural"]
        check("N30: G 结构性存在（雨速视界处 v = c）+ e 结构性存在（α = e²/4πε₀ħc = 1/137.036）",
              "0.00e+00" in n30["G 的存在位置（雨速 v=√(2GM/r)，太阳）"]["视界雨速 v(r_s)"]
              and float(n30["e 的存在位置（条数流率，精细结构常数）"]["α 相对误差（vs 137.035999）"]) < 1e-6)
        n31 = res["N31_heisenberg_pauli"]
        check("N31: 海森堡不确定性从螺旋几何涌现（Δx·Δp = ħ ≥ ħ/2）+ 泡利排斥几何判据（平行扭量 det=0）",
              all(v["Δx·Δp = ħ（精确）"] and v["≥ ħ/2 满足"]
                  for v in n31["海森堡：Δx·Δp = (λ/2π)(h/λ) = ħ ≥ ħ/2（螺旋几何）"].values())
              and n31["泡利：平行扭量（相同态）det"] == 0.0
              and n31["泡利：不同扭量（不同态）det ≠ 0"] > 0)
        n32 = res["N32_mercury_precession"]
        check("N32: 水星近日点进动（GR 公式 Δφ = 6πGM/(c²a(1−e²))，落入观测 43.1±0.5）",
              "43.1 ± 0.5 arcsec/century" in n32["观测值（GR 经典验证）"]
              and 42.0 < float(n32["每世纪进动（计算）"].split(" ")[0]) < 44.0)

    se = load_report("artifacts/spaceextensibility/report.json")
    if se:
        res = se["results"]
        check("SE1: 压缩能密度非负 + δ>0 单调增",
              res["SE1_compress_nonneg"]["正（δ>0）且随 δ 单调增"])
        check("SE2: 内部空间更大 ⟺ 域差 δ>0",
              res["SE2_domain_difference"]["内部空间更大 ⟺ δ>0（同坐标体积装更多空间）"])
        check("SE3-4: 边界能 ≥ 0 + 总能恒等 + 压缩能单调",
              res["SE3_SE4_energy_budget"]["E_bdry（弥散边界梯度层）≥ 0"]
              and res["SE3_SE4_energy_budget"]["E_comp 随 δ 单调增"])
        s5 = res["SE5_spiral_balance"]
        check("SE5: 螺旋场自维持上限 δ_max（δ≤δ_max 外补=0 / δ>δ_max 外补>0）",
              s5["δ ≤ δ_max → 外补能量 = 0（螺旋场内建维持）"]
              and s5["δ > δ_max → 外补能量 > 0（需外能撑边界）"])

    sf = load_report("artifacts/spacefold/report.json")
    if sf:
        res = sf["results"]
        check("SF1: 密度度规行列式 = −ρ²/c² + v²(ρ²−1)/c⁴（机器精度）",
              res["SF1_det_formula"]["机器精度（< 1e-12）"])
        check("SF1s: 静态折叠 det = −ρ²/c²",
              res["SF1s_static_det"]["静态折叠 = 纯密度贡献"])
        check("SF1: ρ=1 退化保体积 −1/c²（SG2 接轨）+ 耦合项非零",
              res["SF1_coupling"]["耦合项 v²(ρ²−1)/c⁴ 在 ρ≠1 时非零"])
        check("SF2: 延拓性（内部密度更大 ⟹ |det| 更大）",
              res["SF2_interior_larger"]["内部空间更大（|det_in| > |det_out|）"])
        check("SF3: 空间域差值 ΔΦ = ½(v_in²−v_out²) 为正",
              res["SF3_potential_difference"]["内部流动更快 ⟹ 势差为正"])
        check("SF7: 边界维持能 = 压缩能（密度比同源）",
              res["SF7_unified"]["E_bdry = E_compress（密度比同源）"])
        check("SF8: 内部继续折叠（褶皱更多 ⟹ 内部空间更大，Q1）",
              res["SF8_more_folds_more_space"]["N=1..20 层 |det| 严格递增"]
              and res["SF8_more_folds_more_space"]["褶皱数可加 ρ₀N₁ + ρ₀N₂ = ρ₀(N₁+N₂)（SF8a）"])
        check("SF9: 势差-密度耦合（ΔΦ 随 ρ_in 单调，α=1）",
              res["SF9_potential_density_coupling"]["ΔΦ = ½α(ρ_in²−ρ_out²) 随 ρ_in 单调递增（α=1）"])
        check("SF10: 边界势差越大 ⟹ 内部空间越大（链条，Q2）",
              res["SF10_larger_potential_larger_space"]["|det g(ρ_in)| 随 ρ_in 单调递增"]
              and res["SF10_larger_potential_larger_space"]["ΔΦ 大 ⟹ |det| 大（势差大 ⟹ 内部空间大，链条成对样本）"])
        check("SF10b: 总势差 ΔΦ·S 随 ΔΦ 单调",
              res["SF10b_total_potential"]["总势差 ΔΦ·S 随 ΔΦ 单调递增（S=10）"])
        check("SF11: 自维持上限 ∝ B（δ_max² = νB²V/(κg2) 机器精度）",
              res["SF11_sustain_limit_vs_B"]["δ_max 随 B 严格递增（1..8）"]
              and res["SF11_sustain_limit_vs_B"]["δ_max² = νB²V/(κg2) 机器精度"])

    ft = load_report("artifacts/fold_topology/report.json")
    if ft:
        res_ft = ft["results"]
        q1b = res_ft["Q1_b_delta_at_fixed_energy_budget"]["反解可达 δ"]
        space_tot = [v["内部空间总量 δ·∫g²dV"] for v in q1b.values()]
        check("FOLD-Q1: 固定能量预算下多褶皱内部空间更多（N=5 > N=1）",
              space_tot[2] > space_tot[0], space_tot)
        q2b = res_ft["Q2_b_potential_difference_drive"]["边界势差驱动强度 B（≪ΔΦ 放大）放大"]
        dmaxs = [v["δ_max（自维持上限）"] for v in q2b.values()]
        check("FOLD-Q2: 势差驱动 B 放大 ⟹ δ_max 单调增（内部更大）",
              all(dmaxs[i] < dmaxs[i + 1] for i in range(len(dmaxs) - 1)), dmaxs)
        q2a = res_ft["Q2_a_boundary_stiffness_gamma"]["在 δ=1 固定时，γ（边界势差刚度）放大"]
        check("FOLD-Q2a: 加硬边界层 γ 不改变 δ_max（需放大驱动强度而非刚度）",
              len({v["δ_max（自维持上限）"] for v in q2a.values()}) == 1)

    mc = load_report("artifacts/masscancellation/report.json")
    if mc:
        res = mc["results"]
        n1 = res["N1_universal_mass_cancellation"]
        check("AMC1: 通用质量取消（电子/质子/原子同一曲线，μ=1 全归零）",
              n1["归一化曲线 m_eff²/s² = (1−μ)² 对全部锚定强度一致"]
              and n1["电子/质子/原子全部在 μ=1 归零"])
        n2 = res["N2_gradient_cost"]
        check("AMC3: 抹平成本 ∝ 梯度²（减半⟹¼）+ 均匀区零成本",
              n2["成本 ∝ 梯度²（梯度减半 ⟹ 成本¼，全扫描）"]
              and n2["均匀区 g=0 成本=0（本无褶皱可磨）"])
        check("AMC4: 无源区零维持成本（源强²成本，Q=0 免费）",
              res["N3_source_cost"]["无源区 Q=0 维持成本=0（源不再重新制造褶皱）"])
        n4 = res["N4_pair_flat_zone"]
        check("AMC5: 正/反电子相反源抵消（重叠带 ∇·C≈0、|C|≈0 ⟹ 测试物质偏离≈0）",
              n4["重叠带 ∇·C ≈ 0（无净源，两相反源抵消）"]
              and n4["平坦带 |C| ≈ 0 ⟹ 测试物质偏离 u≈0 ⟹ m_eff≈0"]
              and n4["源旁对照 u 明显更大（仍有质量）"])
        n5 = res["N5_ring_capture"]
        check("AMC7: 切向流无径向逃逸（恒等机器精度 + 精确旋转流 100 圈误差 0 + 欧拉二次收敛）",
              n5["AMC7 恒等 |p+v|²−|p|² = |v|²（200 随机切向流，机器精度）"]
              and n5["精确旋转流 100 圈半径误差 = 0.0（几何捕获精确）"]
              and n5["欧拉随流漂移二次收敛（步长减半 ⟹ 漂移≈¼，无线性项）"])
        check("AMC2/AMC6/AMC8: 环无质量产生（dτ²=0、∇·C=0、B=curl C≠0、静态无辐射）",
              n5["dτ² = 0 沿环（无质量，|C|=c 恒）"]
              and n5["∇·C = 0（无源 ⟹ 环不制造质量）"]
              and n5["∇×C = 2ω ≠ 0（B = curl C ≠ 0 磁场标记）"]
              and n5["∂C/∂t = 0（静态环 ⟹ E=0 无辐射）"])
        n6 = res["N6_loop_potential_zero"]
        check("AMC6: 保守势闭合回绕和 = 0（机器精度）+ 接缝对照 ≠ 0",
              n6["保守势闭合回绕和 = 0（机器精度，AMC6）"]
              and n6["非保守（接缝不闭合）开口净积累 ≠ 0"])
        n7 = res["N7_control_anchored_escapes"]
        check("AMC8b: 锚定物质直线逃逸（环只捕获无质量物质，须整体覆盖反引力场）",
              n7["锚定物质（v≠C）径向位移线性增长 ⟹ 逃逸"]
              and n7["平均径向速度 ≈ 踢出速度 v_radial（线性）"])

    pf = load_report("artifacts/plasmafusion/report.json")
    if pf:
        res = pf["results"]
        f2 = res["F2_beta_scan"]
        check("PF-F2: ITER 5.3T β≈4.3% / SPARC 12.2T β<1%（高场宽松）",
              abs(f2["beta_pct"][2] - 4.3) < 0.5 and f2["beta_pct"][4] < 1.0)
        f3 = res["F3_confining_force"]
        check("PF-F3: 约束力随 B²×面积（ITER 总力 ~5.5e9 N = GN 量级）",
              f3[0]["F_total_MN"] > 1e3 and f3[1]["F_total_MN"] < f3[0]["F_total_MN"])
        f4 = res["F4_hoop_stress"]
        rows = f4["rows"]
        check("PF-F4: ITER/SPARC 环向应力均在冷加工铜（250MPa）内",
              rows[0]["safe_cold"] and rows[1]["safe_cold"])
        f5 = res["F5_min_ring"]
        check("PF-F5: 应力极限 12.2T R_max≈2.1m（高场必须小环，SPARC 逻辑）",
              1.8 < f5["stress_limit_Rmax_12.2T_m"] < 2.4)
        f6 = res["F6_space_compression"]
        check("PF-F6: 空间压缩 G=(ρ_in/ρ_out)²，密度比 10 ⟹ 尺寸 ×0.215",
              abs(f6["size_shrink_factor"][-1] - 100 ** (-1 / 3)) < 1e-9)
        f7 = res["F7_modulation_control"]
        check("PF-F7: δB/B=1% ⟹ 调制控制力占比 2.01%（PF9c 代数）",
              abs(f7["mod_force_ratio_dF_over_F"][2] - 0.0201) < 1e-9)

    fc = load_report("artifacts/frccompact/report.json")
    if fc:
        res = fc["results"]
        g1 = res["G1_beta_advantage"]["rows"]
        check("FC-G1: FRC β=0.875 的 nT 是托卡马克 β=2% 的 ~44×（紧凑性来源）",
              abs(g1[0]["nT_keVm3"] / g1[1]["nT_keVm3"] - 43.75) < 0.5)
        g2 = res["G2_sstar_lock"]["rows"]
        check("FC-FC2: S*²ρ_i² = β r_s²/2 对全部 μ 机器精度成立",
              all(r["rel_err"] < 1e-12 for r in g2))
        check("FC-FC5★: μ=0.999 ⟹ τ_E 与 S* 同放大 31.6×（锁定定理）",
              abs(g2[3]["tau_E_s"] / g2[0]["tau_E_s"] - 31.62) < 0.2
              and abs(g2[3]["S_star"] / g2[0]["S_star"] - 31.62) < 0.2)
        g3 = res["G3_three_gates"]["rows"]
        r10 = [r for r in g3 if abs(r["r_s_m"] - 0.10) < 1e-9][0]
        check("FC-门①: r_s=10cm、μ=0、B=B_cap ⟹ 不点火（gain<1，需 B≈70T）",
              r10["gain_mu0"] < 1.0 and r10["B_needed_T_mu0"] > 60.0)
        check("FC-门②: r_s=10cm 应力上限 B≈26T（σ_y=2GPa, t=2cm，PF7 反解）",
              24.0 < r10["B_cap_T"] < 28.0)
        check("FC-门③: r_s=10cm、μ=0 的 S*≈75 在脉冲 FRC 已演示区（<100）",
              r10["S_star_mu0"] < 100.0)
        mu_crit = res["G3_three_gates"]["mu_crit_rmf"]
        check("FC-门④★: RMF 硬天花板 μ<1−m_e/m_i≈0.99978（FC11）",
              abs(mu_crit - 0.99978) < 1e-4)
        check("FC-门④: r_s=10cm 所需 μ=0.9975 仍在 RMF 窗口内；r_s=3cm 已被排除",
              r10["mu_needed_at_Bcap"] < mu_crit
              and [r for r in g3 if abs(r["r_s_m"] - 0.03) < 1e-9][0]["mu_needed_at_Bcap"] > mu_crit)
        g5 = res["G5_mu_tradeoff"]["rows"]
        check("FC-FC5: τ_E 增益 = S* 惩罚 = 1/√(1−μ)（逐行）",
              all(abs(r["tau_gain_x"] - r["S_penalty_x"]) < 1e-9 for r in g5))
        g6 = res["G6_rmf_window"]["rows"]
        check("FC-FC9: RMF 窗口比 = m_i/m_e，且 μ↑ ⟹ f_ci 上移",
              all(g6[i]["f_ci_MHz"] < g6[i + 1]["f_ci_MHz"] for i in range(len(g6) - 1)))
        g7 = res["G7_pulsed_no_ignition"]["rows"]
        p10 = [r for r in g7 if abs(r["r_s_m"] - 0.10) < 1e-9 and r["mu"] == 0.0][0]
        check("FC-G7: 脉冲非点火路线 r_s=10cm、μ=0 ⟹ 净出需 回收×注入 ≥80%",
              0.78 < p10["eta_min_required"] < 0.82)

    hq = load_report("artifacts/hiddenqft/report.json")
    if hq:
        res = hq["results"]
        check("HQ-H1: 临界叶 √e≈1.6487>1（绝对/条件收敛分界）",
              res["H1_critical_sheet"]["gt_one"])
        check("HQ-H2: 相干度有界（随机<1, 全对齐=1, HQ2/HQ3）",
              res["H2_coherence_bound"]["bound_ok"])
        check("HQ-H3: 极化相变（涨落超临界 ⟹ 相位对齐, Ising 型）",
              res["H3_polarization_phase_transition"]["phase_transition_observed"])
        check("HQ-H4: 全对齐能量 = −JN（HQ5 最小能量态）",
              res["H4_energy_emergence"]["hq5_ok"])
        check("HQ-H5: 释放 ≈ 耦合减少（守恒, 非净产出, HQ6）",
              res["H5_energy_balance"]["release_eq_coupling_approx"]
              and not res["H5_energy_balance"]["net_production"])
        h6 = res["H6_fractal_vibration"]
        check("HQ-H6: 分形振动能量累积 + A3 开方不可逆（HQ7/HQ8）",
              h6["energy_accumulates"] and h6["sqrt_irreversible"]
              and h6["mul_sqrt_asymmetric"])
        h7 = res["H7_tag_flow_engine"]
        check("HQ-H7: Tag 流发动机——单循环净产出 δ（开方释放−泵回，HQ10）"
              " + 分形自生成 g>0 超守恒（HQ11）",
              abs(h7["cycle_net_output_delta"] - 1.0) < 1e-12
              and h7["fractal_gen"][-1]["total_100_cycles"] > 100
              and h7["conservative_without_postulate"])

    gc = load_report("artifacts/gravitycontrol/report.json")
    if gc:
        res = gc["results"]
        check("GCA1: P_A 幂等（P²=P）", res["N1_idempotent"]["P² = P（幂等）"])
        n2 = res["N2_decision_functional"]
        check("GCA2: Q ≥ 0 且 Q=0 ⟺ 区域常值，抹平后 Q=0",
              n2["Q ≥ 0"] and n2["Q = 0 ⟺ 区域常值（200/200 常值场 vs 200/200 非常值场）"] and n2["抹平 ⟹ Q = 0"])
        check("GCA2d: 抹平 ⟹ A 内部 ∇Φ 归零（边界跳变保留）",
              res["N2b_gravity_interface"]["抹平 ⟹ 区域内部引力关闭（边界保留）"])
        check("GCA3: 极化恒等式（二次型 → 内积）", res["N3_polarization"]["极化恒等式成立"])
        check("GCA4: 起伏 ⟂ 常值", res["N4_orthogonal"]["起伏 ⟂ 常值"])
        check("GCA5: (P, I−P) 互补投影对", res["N5_complementary_projection"]["互补投影对成立"])
        check("GCA6: 层状族 ⟹ 可交换，部分重叠 ⟹ 不可交换",
              res["N6_commutator_scan"]["层状族（不交或嵌套）⟹ 交换子 = 0"]
              and res["N6_commutator_scan"]["部分重叠 ⟹ 交换子 > 0（全部）"])
        check("GCA6a: 不交族分配律 + 格并幂等（布尔子代数）",
              res["N7_boolean_vs_not"]["不交族 = 布尔子代数（分配律 + 格并幂等成立）"])
        check("GCA6c: 交叠族布尔运算失效（交换子≠0 + 非投影）",
              res["N7_boolean_vs_not"]["交叠族：布尔运算失效（交换子≠0 + 格并非投影）"])
        check("GCA7: 基元是二次型（Q(t·v) = t²Q(v)）", res["N8_quadratic_signature"]["基元是二次型（2 次齐次）"])
        n9 = res["N9_commute_absorb_witnesses"]
        check("GCA6b/c 见证：部分重叠不可交换 / 嵌套吸收",
              n9["部分重叠 ⟹ 次序不同结果不同"] and n9["嵌套 ⟹ 吸收（次序无关，同结果）"])

    mud = load_report("artifacts/mudynamics/report.json")
    if mud:
        res = mud["results"]
        check("TD1a: μ,η ∈ [0,1] ⟹ 更新后仍在 [0,1]（不超调）", res["N1_bounded"]["有界不超调"])
        check("TD2: μ<1 且 η>0 ⟹ 严格推进（μ 增大）", res["N2_strict_mono"]["严格递增"])
        check("TD3/TD3b: μ=1 一步不可达 / η>1 超调（稳定区 η≤1）",
              res["N3_N4_reachable_overshoot"]["稳定区 = η ≤ 1"])
        check("TD7: 闭式解 μ_n = 1 − (1−η)^n(1−μ₀) 与递推一致", res["N5_closed_form"]["闭式解成立"])
        n678 = res["N6_N7_N8_never_reach"]
        check("TD8: 有限步不可达（μ_n < 1）", n678["轨道最大值 < 1"], n678["严格性检查步数"])
        check("TD9: 轨道单调递增", n678["单调递增"])
        check("TD10: 质量永不归零（m_eff² > 0 始终）", n678["质量永不归零"])
        check("TD5: 满增益 η=1 一步到 1", res["N9_full_gain"]["η=1 ⟹ μ'=1（100 点）"])
        check("TD6: 无超调 η≤1 / 超调收敛 1<η<2 / 发散 η≥2（两临界值）",
              res["N10_convergence_scan"]["两个临界值（1 = 无超调上界；2 = 收敛上界）"])
        n11 = res["N11_N12_bridge"]
        check("TD12: 抹平一次 ⟹ 增益 = 1（flatten 接入 μ 更新）", n11["抹平 ⟹ η = 1"])
        check("TD13: 增益对起伏单调反向（Q 小 ⟹ η 大）", n11["Q 小 ⟹ η 大（单调反向，200 对）"])
        check("TD17: 顺序不可交换（先抹平 μ'=1 vs 先更新 μ'=0）",
              res["N13_order_witness"]["顺序改变 μ 演化"])
        n14 = res["N14_gap_and_cost"]
        check("TD15/TD16: 顺序差 = (1−μ)(1−η_before)", n14["顺序差 = (1−μ)(1−η_before)"])
        check("TD18: 满增益 ⟺ 零代价 ⟺ 区域已平坦（缺口移动不消失）",
              n14["满增益 ⟺ 零代价（200 场）"])
        n15 = res["N15_frc_interface"]
        check("TD19: RMF 窗口余量沿轨道严格收窄（不自行恢复）",
              n15["窗口余量 m_i(1−μ_n) 严格递减"])
        check("TD20: 锁定因子良定义 + 单调递增（逼近但不达发散点）",
              n15["锁定因子 1/√(1−μ_n) 分母恒正（良定义）"] and n15["锁定因子严格递增（逼近发散点）"])
        check("TD21: 窗口关闭步判据（闭式解 ⟺ FC11b 阈值）",
              n15["阈值判据等价（逐点，闭式 ⟺ FC11b 阈值）"],
              n15["D-T 窗口关闭步 n*（阈值 μ ≥ 0.99978）"])

    mf = load_report("artifacts/moirefield/report.json")
    if mf:
        res = mf["results"]
        m2 = res["M2_field_density"]
        m2r = {r["key"]: r for r in m2["rows"]}
        check("MF-M2: β≤1 撑住 n=1e20 需 B_min≈1.099 T（PF3/FC1 反解）",
              abs(m2["B_min_design_T"] - 1.0991) < 5e-3)
        check("MF-M2: 场源天花板 ⟹ 密度天花板 n_max(0.12T)=1.19e18 / (1.6T)=2.12e20",
              abs(m2r["MATBG_N2_perp"]["n_max_perm3"] / 1.194e18 - 1) < 5e-3
              and abs(m2r["MATBG_N2_par"]["n_max_perm3"] / 2.12e20 - 1) < 5e-3)
        check("MF-M2: MATBG 面外 0.12T 下连 β≤1 都不可能（面内 1.6T 可以）",
              m2r["MATBG_N2_perp"]["beta_impossible"]
              and not m2r["MATBG_N2_par"]["beta_impossible"])
        m3r = {r["key"]: r for r in res["M3_power"]["rows"]}
        check("MF-M3: 功率 ∝ B⁴ —— MATBG 面内 1.6T ⟹ P×1e-3（体积×1000）",
              abs(m3r["MATBG_N2_par"]["p_rel"] / 9.99e-4 - 1) < 0.02
              and abs(m3r["MATBG_N2_par"]["V_rel_for_same_power"] / 1001.0 - 1) < 0.02)
        check("MF-M3: MATBG 面外 0.12T ⟹ P×3.2e-8（同功率体积×3.2e7）；35T 压缩 ⟹ P×229",
              abs(m3r["MATBG_N2_perp"]["p_rel"] / 3.16e-8 - 1) < 0.03
              and abs(m3r["CFR2_comp"]["p_rel"] / 229.0 - 1) < 0.02)
        m4 = res["M4_mu_window"]
        m4r = {r["key"]: r for r in m4["rows"]}
        check("MF-M4: FC11 地板 m_e/m_i = 2.194e-4（D-T 2.5u）",
              abs(m4["floor_FC11"] - 2.1943e-4) < 1e-7)
        check("MF-M4★: MATBG 面外 0.12T ⟹ X_req=4.6e-8 < 地板 ⟹ μ 窗口关闭（无解）",
              not m4r["MATBG_N2_perp"]["feasible"]
              and m4r["MATBG_N2_perp"]["chi_mu"] < 1e-3)
        check("MF-M4: 面内 1.6T / MATTG 10T ⟹ 可行性裕度 1.48×（设计密度分支）",
              m4r["MATBG_N2_par"]["feasible"] and m4r["MATTG_N3_par"]["feasible"]
              and abs(m4["chi_mu_at_design"] - 1.476) < 0.03)
        m5 = res["M5_death_threshold"]
        check("MF-M5★: 死活判据 B_death(a=0.2m)=0.997 T（低于它 μ 窗口关闭）",
              abs(m5["B_death_ref_T"] - 0.9966) < 3e-3)
        sc = {r["a_m"]: r for r in m5["scan"]}
        check("MF-M5: B_death ∝ 1/a（0.1m→1.99T、0.05m→3.99T ⟹ 紧凑化抬高场门槛）",
              abs(sc[0.1]["B_death_T"] / m5["B_death_ref_T"] - 2.0) < 0.02
              and abs(sc[0.05]["B_death_T"] / m5["B_death_ref_T"] - 4.0) < 0.03)
        m6 = res["M6_current_gate"]
        check("MF-M6: 载流门——REBCO 片超流密度 vs MATBG 满填充 ⟹ 1.31e4×",
              abs(m6["ns_gap_full"] / 1.31e4 - 1) < 0.05)
        check("MF-M6: 片电流 MATBG 2.5e-3 A/cm vs REBCO 1000 A/cm ⟹ 4.0e5×",
              abs(m6["K_gap"] / 4.0e5 - 1) < 0.05)
        m7 = res["M7_cryo_gate"]
        check("MF-M7: 制冷门——ITER 冷量 75kW@4.5K vs 稀释制冷机 20mW@0.5K ⟹ 3.75e6×",
              abs(m7["capacity_gap_05K"] / 3.75e6 - 1) < 0.02)
        check("MF-M7: Carnot 因子 4.5K→0.5K 恶化 9.1×",
              abs(m7["carnot_ratio"] - 9.1) < 0.2)
        check("MF-M8: 数据变化总表 7 行（面外死/面内与 N≥3 活）",
              len(res["M8_summary"]["rows"]) == 7)

    # 4a. 硬件四轴（装置/诊断/建造-可造性/排期）+ 下游 feed 的回归锚点
    dev = load_report("artifacts/device/report.json")
    if dev:
        a = {x["量"]: x for x in dev["D3_可锚定量"]}
        q = a["稳态环半径上限（冷加工铜 σ_y=250MPa, t=0.5m, B=12.2T）"]
        check("DV: 应力层最小环 R_max(12.2T, 冷加工铜, t=0.5m) = 2.111 m（PF7 反解）",
              abs(q["值"] - 2.1107179881683646) < 1e-12 and q["原文"] == "R_max(B=12.2T) = 2.1m")
        cap = a["紧凑装置机械门上限 B_cap（FC8 反解，σ_y=2GPa, t=1.35cm, r_s=10cm）"]
        check("DV: FC8 机械上限 r_s=10cm（σ_y=2GPa, t=1.35cm）≈ 26.05 T",
              abs(cap["值"] - 26.049645164097633) < 1e-9)
        lo = a["FC12 选频带下沿 2·f_ci（B=9T）"]
        hi = a["FC12 选频带上沿 5·f_ci（B=9T）"]
        cl = a["装置光速响应上限 c/L（L=0.5m，脚本既有取值）"]
        check("DV: FC12 选频带 [2,5]·f_ci(B=9T) = 110.56–276.41 MHz，完全落在 c/L = 599.58 MHz 之下",
              abs(lo["值"] - 110.56404634988235) < 1e-9
              and abs(hi["值"] - 276.41011587470587) < 1e-9
              and abs(cl["值"] - 599.584916) < 1e-5 and hi["值"] < cl["值"])
        check("DV: FC12 f_ci(B=9T) = 55.282 MHz 与 frccompact G6 行一致",
              abs(a["RMF 离子回旋频率（B=9T, D-T, μ=0）"]["值"] - 55.28202317494117) < 1e-9)
        check("DV: 装置线 18 个月 = 30.5 人·月、六道工序（roadmap §2.5）",
              abs(dev["D4_装置线人·月合计"] - 30.5) < 1e-9
              and len(dev["D4_工期锚点（装置线）"]) == 6)
        check("DV: 反引力约束环自身几何为 [缺口]（清单非数字、不填默认值）",
              len(dev["D5_缺口清单"]) >= 4
              and all(isinstance(x, str) and x.strip() for x in dev["D5_缺口清单"])
              and any("整机" in x or "包络" in x or "几何" in x
                      for x in dev["D5_缺口清单"]))

    dg = load_report("artifacts/diagnostics/report.json")
    if dg:
        lad = dg["G1_δ_到_μ_min_阶梯"]["1e-3/1e-4/1e-5"]
        check("DG: δ=1e-4 ⟹ μ_min(1σ) = 9.9990e-05（R_ci 反解 μ_min = δ/(1+δ)）",
              abs(lad["δ=1e-04"]["μ_min（1σ，roadmap §1 口径）"]
                  - 9.999000099990002e-05) < 1e-18)
        check("DG: 3σ 门 μ_min = 3δ/(1+3δ) = 2.9991e-04 > 1σ 门（生死门 G1 用 3σ）",
              abs(lad["δ=1e-04"]["μ_min（3σ，G1 通过条件口径）"]
                  - 0.00029991002699190244) < 1e-18
              and lad["δ=1e-04"]["μ_min（3σ，G1 通过条件口径）"]
              > lad["δ=1e-04"]["μ_min（1σ，roadmap §1 口径）"])
        check("DG: FC11 硬天花板 μ = 1 − m_e/m_i = 0.999780568036375",
              abs(dg["G3_与聚变级的量级差"]["FC11 天花板 μ_max"]
                  - 0.999780568036375) < 1e-15)
        check("DG: δ=1e-4 到 FC11 天花板差 4.00 个数量级（roadmap『差 4 个数量级』）",
              abs(dg["G3_与聚变级的量级差"]["δ=1e-4 ⟹ 量级差 [decade]"] - 4.0) < 0.005)
        check("DG: 生死门 G0+G1 = 15 人·月 = 1.29%（全周期 1161 人·月）",
              dg["G4_生死门人·月依据"]["G0+G1"] == 15
              and dg["G4_生死门人·月依据"]["判决期占比 [%]"] == 1.29
              and dg["G4_生死门人·月依据"]["全周期人·月"] == 1161)

    bd = load_report("artifacts/buildability/report.json")
    if bd:
        check("BD: 六道工序人·月合计 = 30.5（装置线）",
              abs(sum(s["人·月"] for s in bd["B2_工序表"]) - 30.5) < 1e-9)
        check("BD: 关键路径 = 除『诊断升级』外的五道，长度 18 个月（派生口径已显式）",
              len(bd["B3_关键路径（派生）"]["序列"].split("→")) == 5
              and bd["B3_关键路径（派生）"]["长度 [月]"] == 18)
        check("BD: 首件 = 桌面判据台（M6, G1 生死门）；失败处置 = 停装置线",
              "桌面判据台" in bd["B4_首件"]["首件"]
              and "停装置线" in bd["B4_首件"]["首件失败处置（预写）"])
        check("BD: 工件级自制/外购归属记为 [缺口]（页面无设备清单）",
              "[缺口]" in bd["B5_自有 vs 外协"]["工件级归属"])

    pg = load_report("artifacts/program/report.json")
    if pg:
        sch = pg["PG1_排期表（机器可读）"]
        check("PG: 八门 Σ 人·月 = 1161 且 Σ 月数 = 60（人数 × 月数 = 人·月）",
              sum(s["人·月"] for s in sch) == 1161
              and sum(s["月数"] for s in sch) == 60
              and all(s["人"] * s["月数"] == s["人·月"] for s in sch))
        check("PG: 口径钉死——前 6 个月 1.29%（G0+G1）、前 18 个月 8.01%、M24 前 14.21%",
              abs(pg["PG3_关键数字（与页面 §7 一致）"]["判决期 G0+G1 占全周期人力 [%]"] - 1.29) < 0.005
              and abs(pg["PG3_关键数字（与页面 §7 一致）"]["前 18 个月（G0–G3）累计 [%]"] - 8.01) < 0.005
              and abs(pg["PG3_关键数字（与页面 §7 一致）"]["M24 前累计 [%]"] - 14.21) < 0.005
              and pg["PG3_关键数字（与页面 §7 一致）"]["峰值人数"] == 35)
        check("PG: 已知取整差 1 处已登记（§3 G5 行 34.89% vs 计算 34.88%）",
              len(pg["PG3b_取整差异登记（页面 vs 计算）"]) == 1)
        check("PG: 措辞差异登记 10 项（页面为权威，数字全等）",
              len(pg["PG7_措辞差异登记（页面 vs 脚本产物）"]) == 10)
        check("PG: index.md 的 1.22% 口径差已登记",
              len(pg["PG8_第三处口径差登记（index.md）"]) == 1)

    wf = load_report("artifacts/world_feed/world_feed.json")
    if wf:
        check("WF: 47 条锚点、四段（状态/动作/目标/终止）齐、7 条缺口槽位",
              len(wf["锚点"]) == 47
              and all(wf["结论"]["按段计数"][s] > 0 for s in ("状态", "动作", "目标", "终止"))
              and len(wf["缺口槽位"]) == 7)
        check("WF: 每条锚点带来源文件 + 16 位 sha256（下游按 hash 去锚）",
              all(len(x["来源文件 sha256_16"]) == 16 and x["来源文件"] for x in wf["锚点"]))
        check("WF: 不引用本次新建的四轴产物（无循环引用）+ 缺口槽位不填默认值",
              not any(x["来源文件"].startswith(
                  ("artifacts/device/", "artifacts/diagnostics/",
                   "artifacts/buildability/", "artifacts/program/"))
                  for x in wf["锚点"])
              and all("需要 leo 给什么" in g for g in wf["缺口槽位"]))
        _k = {x["键名"]: x for x in wf["锚点"]}
        _r = _k["target.device.应力层最小环上限（B=12.2T）"]
        check("WF: 多数字引句必须显式声明取值锚（应力层最小环=2.1107m 而非引句里的 12.2）",
              abs(float(_r["取值"]) - 2.110710) < 1e-5 and _r["单位"] == "m"
              and _k["target.device.真空场（RMF 选频用 B，下限）"]["取值"] == "7"
              and _k["terminate.gate.D1=0 ⟹ 停装置线"]["取值"] == "D1 = 0（M6）")

    # 3b. 胶球环扭转（RT 系列：环扭转 → 条数 N 与 μ 的连接数写法）
    rt = load_report("artifacts/glueball_ring_twist/report.json")
    if rt:
        res = rt["results"]
        pa = res["RT_A_identity_planar"]
        check("RT-A1: 扭环恒等式 Lk = Tw + Wr（平面圆,Wr=0 ⟹ Lk = 扭转圈数）",
              pa["max|残差|"] < 0.05, pa["max|残差|"])
        pt = res["RT_A_identity_trefoil"]
        dlk = pt["ΔLk 每加一圈扭转"]
        check("RT-A2: 加一圈扭转 ⟹ ΔLk = +1（非平面,与 Wr 无关）",
              all(abs(d - 1.0) < 0.05 for d in dlk), dlk)
        check("RT-A3: 非平面自拧 Wr ≠ 0（三叶结 |Wr| ≈ 3）",
              abs(abs(pt["trefoil_Wr (N=2401)"]) - 3.0) < 0.4, pt["trefoil_Wr (N=2401)"])
        pm = res["RT_A_double_helix_mu"]
        mus = {tuple(r["扭转对"]): r["μ = 1 − |Lk_net|/|Lk_gross|"] for r in pm["rows"]}
        check("RT-A4: 双螺旋反向对 ⟹ μ = 1（光子情形）/ 同向对 ⟹ μ = 0",
              mus.get((1, -1)) == 1.0 and mus.get((2, -2)) == 1.0 and mus.get((1, 1)) == 0.0, mus)
        pb = res["RT_B_reachability"]
        check("RT-B1: 对角型（三个独立绕数）取不到 N = 7",
              pb["7 在对角型"] is False and 7 not in pb["对角型可达（≤20）"])
        check("RT-B2: 集体型（Σnᵢ²+|μ̄₃|）能取到 N = 7", pb["7 在集体型"] is True)
        check("RT-B3: 变体 II 的最小三个 N = {3,6,7}（与仓库胶球账本一致）",
              pb["变体 II（μ̄₃ 需 max|nᵢ|≥2）前三个 N"] == [3, 6, 7],
              pb["变体 II（μ̄₃ 需 max|nᵢ|≥2）前三个 N"])
        check("RT-B4: 变体 I 会多出多余态（记录:选择规则尚未导出）",
              pb["变体 I（μ̄₃ 任意）前三个 N"] != [3, 6, 7],
              pb["变体 I（μ̄₃ 任意）前三个 N"])
        pl = res["RT_B_ladder"]
        check("RT-B5: 3/6/7 三个态都落在格点观测区间内（只比比值）",
              all(v["落区间内"] for v in pl.values()),
              {k: v["m = √N·M₀ (GeV)"] for k, v in pl.items()})
        pc = res["RT_C_ratios"]
        check("RT-C1: √(6/3) 与 √(7/3) 落在格点比值区间内",
              pc["格点 2++/0++ 区间"][0] <= pc["√(6/3)"] <= pc["格点 2++/0++ 区间"][1] and
              pc["格点 0-+/0++ 区间"][0] <= pc["√(7/3)"] <= pc["格点 0-+/0++ 区间"][1],
              [pc["√(6/3)"], pc["√(7/3)"]])
        pf = res["RT_C_mu_floor_linkage"]
        check("RT-C2: FC11 地板的连接数读法（1/(m_e/m_i) ≈ 4558）",
              4550 < pf["1/(m_e/m_i)"] < 4570, pf["1/(m_e/m_i)"])
        pe = res["RT_E_lattice"]
        rws = pe["对位（按质量升序，两边都排序 ⟹ 无选择自由度）"]
        check("RT-E1: 最轻五个格点态全部落在格点误差带内（单一 M₀ 回算）",
              all(v["落在格点误差内"] for v in rws[:5]),
              [(v["J^PC"], v["偏差 %"]) for v in rws[:5]])
        sc = pe["单一常数"]["反推散布 ±%"]
        ctrl = pe["拟合非空转对照（反推 M₀ 离散）"]
        check("RT-E2: 单一常数的散布 ≤3%，且比「连续整数 3..7」的对照好 3 倍以上（拟合非空转）",
              sc <= 3.0 and ctrl["连续整数 3..7"] / sc > 3.0,
              {"我们": sc, "连续整数": ctrl["连续整数 3..7"], "最朴素": ctrl["最朴素 1..5"]})
        rt = pe["只比比值"]
        check("RT-E3: 只比比值（不依赖 M₀）前四条偏差 ≤3%",
              all(abs(v["偏差 %"]) <= 3.0 for v in rt[:4]), [(v["J^PC/0++"], v["偏差 %"]) for v in rt[:4]])
        gap0 = pe["不符"]["0*++"]["反推 N（非整数）"]
        gap_x = pe["张力"]["X(2370)"]["反推 N"]
        check("RT-E4: 不符与张力都被如实登记（0*++ 反推 N 远离整数；X(2370) 反推 N ≈ 6 撞我们的 2++ 槽）",
              abs(gap0 - round(gap0)) >= 0.3 and abs(gap_x - 6.0) <= 0.1, {"0*++ N": gap0, "X(2370) N": gap_x})
        at = pe["第二套格点（Athenodorou–Teper 2020, M_G/√σ）"]
        check("RT-E6: 换第二套独立格点数据（M_G/√σ）同一阶梯仍自洽，且 M₀ 随标度约定一起平移",
              at["散布 ±%"] <= 2.0 and abs(at["单一 M₀"] - pe["单一常数"]["M₀（前五态反推均值）"]) / at["单一 M₀"] <= 0.06,
              {"AT M₀": at["单一 M₀"], "散布": at["散布 ±%"], "TABLE XXI M₀": pe["单一常数"]["M₀（前五态反推均值）"]})
        check("RT-E7: 被跳过的 N=11 在第二套数据里找到对应态（3.2–3.4 GeV 空隙有态）",
              abs(at["被跳过的 N=11 的对位"]["偏差 %"]) <= 3.0, at["被跳过的 N=11 的对位"])
        check("RT-E5: 3.2–3.4 GeV 的空隙不被掩盖（3+- / 3++ 两条明确记为超出误差）",
              not rws[5]["落在格点误差内"] and not rws[6]["落在格点误差内"],
              [(rws[5]["J^PC"], rws[5]["偏差 %"]), (rws[6]["J^PC"], rws[6]["偏差 %"])])
        pf_ = res["RT_F_jpc_and_fullspectrum"]
        jp = pf_["① J^PC 导出性（穷举）"]
        check("RT-F1: ① J^PC 导出的穷举**否定**结果（256 条规则里 0 条全中）",
              jp["穷举条数"] == 256 and jp["全中条数"] == 0,
              {"穷举条数": jp["穷举条数"], "全中": jp["全中条数"], "最好": jp["最好命中"]})
        fs = pf_["② 全谱命中率"]
        h1 = int(fs["1σ 命中"].split("/")[0]) / int(fs["1σ 命中"].split("/")[1]) * 100
        base = fs["随机基线（误差与数据同分布）%"]
        check("RT-F2: ② 全谱 1σ 命中率 ≥1.5× 随机基线（误差同分布口径）",
              h1 / base >= 1.5, {"我们 %": round(h1), "随机 %": base, "比值": round(h1 / base, 2)})
        fl = pf_["③ 旗标相关性"]
        check("RT-F3: ③ 漏掉的态**不集中在**格点标星的态（干净态命中率 ≤ 标星态）",
              fl["格点标「好拟合」的态"]["命中 1σ"] / fl["格点标「好拟合」的态"]["个数"] <=
              fl["格点标星（拟合一般/不确定）的态"]["命中 1σ"] / fl["格点标星（拟合一般/不确定）的态"]["个数"],
              fl)
        e7 = res["RT_E_lattice"]["第二套格点（Athenodorou–Teper 2020, M_G/√σ）"]["被跳过的 N=11 的对位"]
        check("RT-F4: ③ 两个具体点都被如实判为**未命中**（0*++ 远离整数 N；2++ ex1 落在两档之间）",
              abs(e7["反推 N"] - 11) > 0.3 and abs(e7["反推 N"] - 12) > 0.3 and e7["σ 数"] > 3.0,
              {"2++ ex1 反推 N": e7["反推 N"], "σ": e7["σ 数"]})
        pg = res["RT_G_braid_three"]
        g1 = pg["① 中心元是纯量（数值）"]
        check("RT-G1: B₃ 既约 Burau：braid 关系 + (σ₁σ₂)³ = t³·I 在 9 个单位根上全成立",
              g1["braid 关系在 9 个根上成立"] and g1["(σ1σ2)³ = t³·I 全成立"] and g1["最大偏差"] < 1e-12,
              {"最大偏差": g1["最大偏差"], "Lean": g1["Lean"]})
        g2 = pg["② 相位阶梯（λ = e^(2πi·3/m) ⟹ h = 3/m mod 1，J = 2h）"]
        check("RT-G2: 2 维既约 Burau 的中心元相位给不出 J = 2, 3（本条是否定结果门）",
              g2["可达自旋（整数/半整数）"] == [0.0, 0.5, 1.0, 1.5] and set(g2["不可达"]) == {2, 3},
              {"可达": g2["可达自旋（整数/半整数）"], "不可达": g2["不可达"]})
        g3 = pg["③ 辫词字典（几何 → 辫词）"]["行"]
        check("RT-G3: 三股几何 ⟹ 辫词 (σ₁σ₂)^{3q}（Σ = 3q ⟹ e = 6q 自洽）",
              all(r["⟹ 指数和 e = 2Σ"] == 6 * r["q（两两连接数，RT-D 实测）"] for r in g3), g3)
        tj = load_report("artifacts/glueball_ring_twist/tl3_jones.json")
        if tj:
            h1 = tj["1) TL₃(δ) 5 维左正则表示"]
            check("RT-H1: TL₃ 定义关系成立且结合律 0 违例（125 组全过）",
                  h1["定义关系成立"] and h1["结合律违例数"] == 0, h1["结合律违例数"])
            h2 = tj["2) 中心"]
            check("RT-H2: TL₃ 中心维数 = 2 且有**显式非纯量中心元**（对照 BT3 的纯量局面）",
                  h2["维数"] == 2 and h2["Z 是中心元"] and not h2["Z 是纯量"],
                  {"维数": h2["维数"], "Z 中心": h2["Z 是中心元"], "Z 纯量": h2["Z 是纯量"]})
            h3 = tj["3) 骨架形式 σ = A + A⁻¹e（δ = −(A²+A⁻²)）"]
            check("RT-H3: 骨架 braid 关系 + Δ 中心但**非纯量**（两个标量、多重度 1 与 4）",
                  h3["braid 关系成立"] and h3["Δ 是中心元"] and not h3["Δ 是纯量"]
                  and sorted(m for _, m in h3["Δ 的特征值（多重度）"]) == [1, 4],
                  {"braid": h3["braid 关系成立"], "Δ 中心": h3["Δ 是中心元"],
                   "Δ 纯量": h3["Δ 是纯量"], "多重度": [m for _, m in h3["Δ 的特征值（多重度）"]]})
            h4 = tj["4) 融合奇偶规则（导出，独立于 TL）"]
            fus = h4["n 股融合的 J 集合"]
            parity = all(all(round(2 * j) % 2 == int(n) % 2 for j in fus[n]) for n in fus)
            check("RT-H4: 融合奇偶规则 2J ≡ n (mod 2) 成立 ⟹ \"永远三股\"被否证（0++/2++ 的 J 是偶数）",
                  parity and h4["奇偶规则自洽"], {"J 集合": fus, "股数分配": h4["自洽股数分配"]})
        pd = res["RT_D_braid"]
        check("RT-D1: m 股麻花辫的每对连接数 = q（m = 2/3/4，q = 1/2/3）",
              all(r["max|Lk − q|"] < 0.05 for r in pd["rows"]),
              [(r["股数 m"], r["扭转 q"], r["max|Lk − q|"]) for r in pd["rows"]])
        check("RT-D2: 加密一倍 ⟹ 偏差下降（离散误差不是模型误差）",
              pd["收敛性 (4 股 q=2)"]["N=2801"] < pd["收敛性 (4 股 q=2)"]["N=1401"],
              pd["收敛性 (4 股 q=2)"])
        check("RT-D3: 成对连接总数 = C(m,2)·q",
              pd["成对连接总数 Σ_{i<j} Lk"]["m=3, q=2"] == 6 and
              pd["成对连接总数 Σ_{i<j} Lk"]["m=4, q=2"] == 12,
              pd["成对连接总数 Σ_{i<j} Lk"])

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
        "artifacts/spaceextensibility/space_extensibility.png": 30_000,
        "artifacts/fold_topology/fold_topology.png": 30_000,
        "artifacts/masscancellation/fig_feasibility_capture.png": 30_000,
        "artifacts/masscancellation/fig_pair_flat_zone.png": 30_000,
        "artifacts/plasmafusion/report.json": 5_000,
        "artifacts/plasmafusion/summary.txt": 1_000,
        "artifacts/plasmafusion/fig_hoop_stress.png": 30_000,
        "artifacts/plasmafusion/fig_space_compression.png": 30_000,
        "artifacts/plasmafusion/fig_mod_control.png": 30_000,
        "artifacts/frccompact/report.json": 5_000,
        "artifacts/frccompact/summary.txt": 1_000,
        "artifacts/frccompact/fig_frc_gates.png": 30_000,
        "artifacts/hiddenqft/report.json": 2_500,
        "artifacts/hiddenqft/fig_polarization.png": 30_000,
        "artifacts/hiddenqft/fig_fractal_energy.png": 30_000,
        "artifacts/hiddenqft/fig_tag_flow_engine.png": 30_000,
        "artifacts/fusionroadmap/report.json": 2_000,
        "artifacts/fusionroadmap/summary.txt": 500,
        "artifacts/fusionroadmap/fig_gate_funnel.png": 30_000,
        "artifacts/fusionroadmap/fig_mu_sensitivity_scaling.png": 30_000,
        "artifacts/fusionroadmap/fig_18m_quarterly.png": 30_000,
        "artifacts/gravitycontrol/report.json": 2_000,
        "artifacts/gravitycontrol/summary.txt": 500,
        "artifacts/gravitycontrol/fig_gravity_control.png": 30_000,
        "artifacts/mudynamics/report.json": 2_000,
        "artifacts/mudynamics/summary.txt": 800,
        "artifacts/mudynamics/fig_mu_dynamics.png": 30_000,
        "artifacts/glueball_ring_twist/report.json": 4_000,
        "artifacts/glueball_ring_twist/tl3_jones.json": 3_000,
        "artifacts/glueball_ring_twist/fig_ring_twist.png": 30_000,
        "artifacts/glueball_ring_twist/fig_understanding_ring_twist.png": 30_000,
        "artifacts/glueball_ring_twist/fig_twisted_ring_math.png": 30_000,
        "artifacts/glueball_ring_twist/fig_braid_ring_spacetime.png": 30_000,
        "artifacts/moirefield/report.json": 4_000,
        "artifacts/moirefield/summary.txt": 800,
        "artifacts/moirefield/fig_field_ceiling_scaling.png": 30_000,
        "artifacts/moirefield/fig_mu_window_verdict.png": 30_000,
        "artifacts/moirefield/fig_Bdeath_vs_size.png": 30_000,
        "artifacts/moirefield/fig_gate_gaps.png": 30_000,
        "artifacts/device/report.json": 6_000,
        "artifacts/device/summary.txt": 800,
        "artifacts/device/fig_device_anchors.png": 30_000,
        "artifacts/diagnostics/report.json": 6_000,
        "artifacts/diagnostics/summary.txt": 800,
        "artifacts/diagnostics/fig_diagnostics_ladder.png": 30_000,
        "artifacts/buildability/report.json": 6_000,
        "artifacts/buildability/summary.txt": 800,
        "artifacts/buildability/fig_buildability_gantt.png": 30_000,
        "artifacts/program/report.json": 8_000,
        "artifacts/program/summary.txt": 800,
        "artifacts/program/fig_program_gates.png": 30_000,
        "artifacts/world_feed/world_feed.json": 8_000,
        "artifacts/world_feed/summary.txt": 1_000,
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
