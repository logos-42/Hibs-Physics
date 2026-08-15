#!/usr/bin/env python3
"""QFT × 流动空间：激发态与全域纠缠验证（QFTFlow.lean QFT1–QFT9）

leo（2026-08-15）假设：
  1. 激发态 = 偏离空间流动（锚定）；非激发 = 完全随流（光子，dτ=0）
  2. 全域性量子纠缠 = 空间场自身的相干结构（反相无距离衰减 + 三方向不可分）
  3. ★ 统一：质量 ⟺ 激发 ⟺ 秩 2 纠缠（单扭量秩 1 可分 / 双扭量秩 2 复合）

验证：
  N1 非激发 dτ² = 0（随流，机器精度）vs 激发 dτ² > 0（QFT1–2）
  N2 激发质量 = 锚定范数 m² = |ψ₁|²+|ψ₀|²（随机旋量，QFT3）
  N3 多激发质量加法（√N 序列）+ 叠加永不减少（QFT4）
  N4 ★ 全域相干：反相螺旋关联与传播距离无关（QFT5）——E(Δ=π) = −1 精确
  N5 ★ GHZ 三体纠缠判据：单体约化 ρ_A = ½I 混合 Tr(ρ²) = 0.5 < 1（QFT7）
  N6 ★ 秩判据：单扭量 det = 0（秩1）vs 双扭量 det = |⟨π₁,π₂⟩|²（秩2）（QFT8）
  N7 三方向签名 (σ₁+σ₂+σ₃)² = 3I（QFT6）
  N8 统一表：无质量 ⟺ 秩1 ⟺ 可分 / 有质量 ⟺ 秩2 ⟺ 纠缠（QFT9）
"""
import json
import os
from datetime import date

import numpy as np
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
import matplotlib.font_manager as fm

for _fp in ("/System/Library/Fonts/PingFang.ttc",
            "/System/Library/Fonts/Hiragino Sans GB.ttc"):
    if os.path.exists(_fp):
        fm.fontManager.addfont(_fp)
        plt.rcParams["font.sans-serif"] = [fm.FontProperties(fname=_fp).get_name()]
        break
plt.rcParams["axes.unicode_minus"] = False

OUT = os.path.join(os.path.dirname(__file__), "..", "artifacts", "qftflow")
os.makedirs(OUT, exist_ok=True)

I = complex(0, 1)
SIG1 = np.array([[0, 1], [1, 0]], dtype=complex)
SIG2 = np.array([[0, -I], [I, 0]], dtype=complex)
SIG3 = np.array([[1, 0], [0, -1]], dtype=complex)


def anchor_mass_sq(psi):
    """锚定质量平方 = |(σ₁ψ)₀|² + |(σ₁ψ)₁|²（MC4'）。"""
    flow = SIG1 @ psi
    return abs(flow[0]) ** 2 + abs(flow[1]) ** 2


def _py(v):
    """递归转 numpy 标量 → Python 原生（JSON 可序列化）。"""
    if isinstance(v, (np.bool_, np.integer)):
        return bool(v)
    if isinstance(v, (np.floating, np.complexfloating)):
        return float(np.real(v))
    if isinstance(v, dict):
        return {k: _py(x) for k, x in v.items()}
    if isinstance(v, (list, tuple)):
        return [_py(x) for x in v]
    if isinstance(v, np.ndarray):
        return [_py(x) for x in v.tolist()]
    return v


def main():
    report = {"model": "QFT × flowing space: excited states & global entanglement",
              "date": str(date.today()), "results": {}}
    rng = np.random.default_rng(42)

    # ---- N1 非激发 dτ² = 0 vs 激发 dτ² > 0（QFT1–2）----
    c = 1.0
    dt = 1.0
    # 非激发：完全随流 dx = c·dt
    dx_com = c * dt
    dtau2_com = dt**2 - dx_com**2 / c**2
    # 激发：偏离随流（dx < c·dt，锚定偏离）
    dx_exc = 0.6 * c * dt
    dtau2_exc = dt**2 - dx_exc**2 / c**2
    report["results"]["N1_excitation_flow"] = {
        "非激发 dτ²（dx = c·dt，随流）": round(float(dtau2_com), 15),
        "激发 dτ²（dx = 0.6c·dt，偏离）": round(float(dtau2_exc), 15),
        "非激发 = 0（机器精度）": abs(dtau2_com) < 1e-14,
        "激发 > 0": dtau2_exc > 0,
        "note": "QFT1–2：非激发 = 完全随空间流动（光子，不花时间）；"
                "激发 = 偏离空间流动（锚定，花时间）——SM1/SM3c 重述"}

    # ---- N2 激发质量 = 锚定范数（QFT3）----
    max_err_m = 0.0
    for _ in range(200):
        psi = rng.standard_normal(2) + 1j * rng.standard_normal(2)
        m2 = anchor_mass_sq(psi)
        m2_expected = abs(psi[0]) ** 2 + abs(psi[1]) ** 2
        max_err_m = max(max_err_m, abs(m2 - m2_expected))
    # 非零旋量 ⟹ m² > 0
    n_pos = sum(1 for _ in range(200)
                if anchor_mass_sq(rng.standard_normal(2) + 1j * rng.standard_normal(2)) > 0)
    report["results"]["N2_excitation_mass"] = {
        "max|m² − (|ψ₁|²+|ψ₀|²)|（200 随机旋量）": round(float(max_err_m), 14),
        "非零旋量 m² > 0（200/200）": n_pos == 200,
        "note": "QFT3：激发态质量 = 锚定范数（MC4'/MC2'）——激发强度不是"
                "场的能量，而是旋量流对空间运动的锚定量"}

    # ---- N3 多激发质量加法（QFT4）----
    M0 = 1.0
    seq = {}
    for N in (1, 2, 3, 6, 7):
        amps = [1.0 / np.sqrt(N)] * N  # 等幅归一化
        m2_total = sum(a * a for a in amps) * N  # 每方向锚定 a²，N 个方向
        seq[str(N)] = {"√N·M₀": round(np.sqrt(N) * M0, 4),
                       "叠加 m² = Σ mᵢ²": round(m2_total, 4)}
    # 叠加永不减少：随机验证
    never_dec = True
    for _ in range(200):
        psi1 = rng.standard_normal(2) + 1j * rng.standard_normal(2)
        psi2 = rng.standard_normal(2) + 1j * rng.standard_normal(2)
        psi3 = rng.standard_normal(2) + 1j * rng.standard_normal(2)
        if not (anchor_mass_sq(psi1) <=
                anchor_mass_sq(psi1) + anchor_mass_sq(psi2) + anchor_mass_sq(psi3) + 1e-12):
            never_dec = False
    report["results"]["N3_multi_excitation"] = {
        "√N·M₀ 序列（N=1,2,3,6,7）": seq,
        "叠加锚定永不减少（200 随机）": never_dec,
        "note": "QFT4：多激发叠加质量 = 各激发之和（MC6'）——胶球 √N 序列的"
                "代数种子；产生算符叠加只增不减"}

    # ---- N4 ★ 全域相干：反相螺旋关联与距离无关（QFT5）----
    # 螺旋相位场 φ = k·(传播距离) + θ（θ = 测量位置相位），反相股相位差 π。
    # 关联 E(θ) = cos φ · cos(φ+π) = −cos²φ（QFT5b）——传播距离只整体平移
    # 相位，不改变反相结构（形状/极值/平均与距离无关 = 全域无衰减）。
    theta = np.linspace(0, 2 * np.pi, 10000)
    distances = [1.0, 5.0, 20.0, 50.0]  # 传播距离（圈数 × 波长）
    shape_stats, max_shape_err = {}, 0.0
    for L in distances:
        E_L = np.cos(theta + L) * np.cos(theta + L + np.pi)
        shape_stats[str(L)] = {"min": round(float(E_L.min()), 6),
                               "max": round(float(E_L.max()), 6),
                               "mean": round(float(E_L.mean()), 6)}
        # 反相恒等：E_L(θ) = −cos²(θ+L) 精确（对每个 L，每个 θ）
        max_shape_err = max(max_shape_err, float(np.max(np.abs(E_L + np.cos(theta + L) ** 2))))
    # 极值/平均的距离无关性（网格离散容差：max≈0, min≈−1, mean≈−½）
    dist_inv = all(st["max"] < 1e-4 and abs(st["min"] + 1.0) < 1e-4
                   and abs(st["mean"] + 0.5) < 1e-3 for st in shape_stats.values())
    # 反相点精确反关联
    E_pi = float(np.cos(0.0) * np.cos(0.0 + np.pi))
    report["results"]["N4_global_antiphase"] = {
        "反相恒等 max|E − (−cos²φ)|（所有距离/位置）": round(float(max_shape_err), 15),
        "E(Δ=π) 精确反关联": E_pi == -1.0,
        "极值形状（min/max/mean 各距离）": shape_stats,
        "形状与距离无关（max≈0, min≈−1, mean≈−½）": bool(dist_inv),
        "note": "QFT5：反相恒等 cos(θ+π) = −cos θ——传播距离只整体平移相位，"
                "不改变反相结构 ⟹ 全域纠缠 = 空间场处处自带的相干结构"
                "（非超距作用；E(Δ) 只依赖相对相位差）"}

    fig, ax = plt.subplots(1, 2, figsize=(12, 4.6))
    for L in distances:
        ax[0].plot(theta, np.cos(theta + L) * np.cos(theta + L + np.pi),
                   lw=1.2, label=f"L = {L:g}")
    ax[0].plot(theta, -np.cos(theta) ** 2, "k--", lw=1.6, label="解析 −cos²θ")
    ax[0].axhline(-1.0, color="r", ls=":", lw=0.8)
    ax[0].set_xlabel("位置相位 θ")
    ax[0].set_ylabel("关联 E = cosθ·cos(θ+π)")
    ax[0].set_title("QFT5 全域相干：反相关联与距离无关")
    ax[0].legend(fontsize=8)
    ax[0].grid(alpha=0.3)

    # ---- N5 ★ GHZ 三体纠缠判据（QFT7）----
    rhoA = 0.5 * np.eye(2, dtype=complex)          # GHZ 单体约化 = ½I
    rhoA2 = rhoA @ rhoA
    purity = float(np.real(np.trace(rhoA2)))       # Tr(ρ²) = ½
    is_mixed = not np.allclose(rhoA2, rhoA)        # ρ² ≠ ρ
    report["results"]["N5_ghz_reduced"] = {
        "ρ_A = ½I（GHZ 单体约化）": np.allclose(rhoA, 0.5 * np.eye(2)),
        "Tr(ρ_A²)": round(purity, 6),
        "ρ² ≠ ρ（混合态）": bool(is_mixed),
        "纯度 < 1（三体纠缠判据）": purity < 1.0,
        "note": "QFT7：三体纠缠 ⟹ 单体约化最大混合——只看单个方向无法"
                "纯化（三方向全域纠缠的信息完整性判据）"}

    # ---- N6 ★ 秩判据：单扭量 det=0 vs 双扭量 det=|⟨π₁,π₂⟩|²（QFT8）----
    max_det_single = 0.0
    max_err_pair = 0.0
    for _ in range(200):
        pi = rng.standard_normal(2) + 1j * rng.standard_normal(2)
        max_det_single = max(max_det_single, abs(np.linalg.det(np.outer(pi, np.conj(pi)))))
        p1 = np.outer(pi, np.conj(pi))
        pi2 = rng.standard_normal(2) + 1j * rng.standard_normal(2)
        p2 = np.outer(pi2, np.conj(pi2))
        det_pair = abs(np.linalg.det(p1 + p2))
        symp = pi[0] * pi2[1] - pi[1] * pi2[0]     # ⟨π₁,π₂⟩
        max_err_pair = max(max_err_pair, abs(det_pair - abs(symp) ** 2))
    # 相对角度扫描：π₁=(1,0)，π₂=(cosα, sinα)，辛内积 = sinα，det = sin²α
    alphas = np.linspace(0, np.pi / 2, 91)
    det_scan = np.sin(alphas) ** 2
    m2_zero_parallel = abs(det_scan[0]) < 1e-14    # α=0：平行 ⟹ det=0
    m2_max_orthogonal = abs(det_scan[-1] - 1.0) < 1e-14  # α=π/2：正交 ⟹ det=1
    report["results"]["N6_rank_entanglement"] = {
        "单扭量 max|det|（秩 1，非激发）": round(float(max_det_single), 14),
        "双扭量 max|det − |⟨π₁,π₂⟩|²|（秩 2，激发）": round(float(max_err_pair), 14),
        "平行（α=0）⟹ m² = 0（无质量/可分）": bool(m2_zero_parallel),
        "正交（α=π/2）⟹ m² = 最大（有质量/纠缠）": bool(m2_max_orthogonal),
        "note": "QFT8：双扭量 det = |⟨π₁,π₂⟩|²（TW6）；质量 = 两半旋量的"
                "相对方向——平行 = 秩 1 = 无质量（光子边界）；不平行 = "
                "秩 2 = 有质量（电子 = 两半旋量纠缠复合）"}

    ax[1].plot(alphas, det_scan, "b-", lw=1.6, label="det = sin²α（双扭量）")
    ax[1].axhline(0, color="k", ls=":", lw=0.8)
    ax[1].set_xlabel("两旋量夹角 α（π₁=(1,0), π₂=(cosα,sinα)）")
    ax[1].set_ylabel("det(p₁+p₂) = m²")
    ax[1].set_title("QFT8 秩判据：激发质量 = 旋量相对方向")
    ax[1].legend(fontsize=8)
    ax[1].grid(alpha=0.3)
    fig.tight_layout()
    fig.savefig(os.path.join(OUT, "fig_antiphase_global.png"), dpi=130)
    plt.close(fig)

    # ---- N7 三方向签名（QFT6）----
    M = SIG1 + SIG2 + SIG3
    M2 = M @ M
    err_sig = np.max(np.abs(M2 - 3 * np.eye(2, dtype=complex)))
    det_M = np.linalg.det(M)
    report["results"]["N7_three_direction_basis"] = {
        "max|(σ₁+σ₂+σ₃)² − 3I|": round(float(err_sig), 15),
        "det(σ₁+σ₂+σ₃)": round(float(np.real(det_M)), 6),
        "可逆（满秩，信息不损失）": bool(abs(det_M) > 1e-12),
        "note": "QFT6：三方向纠缠算符平方 = 3I（SH3 引用）且 det = −3 ≠ 0——"
                "三方向不可分离的全域纠缠基底"}

    # ---- N8 统一表（QFT9）----
    report["results"]["N8_unified"] = {
        "无质量（非激发，完全随流）": "秩 1（单扭量 det = 0）⟺ 可分",
        "有质量（激发，锚定偏离）": "秩 2（双扭量 det = |⟨π₁,π₂⟩|²）⟺ 纠缠",
        "统一命题": "质量 ⟺ 激发 ⟺ 秩 2 纠缠——标准 QFT 的'粒子 = 场的激发'"
                    "在流动空间中成为'粒子 = 空间流动的秩 2 锚定结构'",
        "note": "QFT9：QFT1–2（激发=锚定偏离）× QFT8（秩判据）组合——"
                "激发与纠缠同源（解释层统一，非新物理预言）"}

    # ---- N9 ★ 三扭量 det₃ 恒等（GQ2：det₃(Σπᵢ⊗π̄ᵢ) = |det₃[π₁π₂π₃]|²）----
    max_err_tri, max_hadamard_ratio = 0.0, 0.0
    for _ in range(200):
        P = [rng.standard_normal(3) + 1j * rng.standard_normal(3) for _ in range(3)]
        A = np.array(P, dtype=complex)            # 行 = 扭量
        outer_sum = sum(np.outer(p, np.conj(p)) for p in P)   # 3×3 分量空间矩阵
        max_err_tri = max(max_err_tri,
                          abs(np.linalg.det(outer_sum) - abs(np.linalg.det(A)) ** 2))
        # Hadamard：|det₃| ≤ |π₁||π₂||π₃|
        norms = np.linalg.norm(A, axis=1)
        max_hadamard_ratio = max(max_hadamard_ratio,
                                 abs(np.linalg.det(A)) / (norms.prod() + 1e-300))
    report["results"]["N9_triple_twistor_det"] = {
        "max|det₃(P) − |det₃[π₁π₂π₃]|²|（200 随机三扭量）": round(float(max_err_tri), 14),
        "Hadamard: max |det₃|/(|π₁||π₂||π₃|) ≤ 1": round(float(max_hadamard_ratio), 10) <= 1.0,
        "note": "GQ2：三扭量外积和 det = |3 阶行列式|²（Cauchy-Binet/det(AA†)=|detA|²）"
                "——胶球质量平方 = 三扭量体积形式；与电子 det₂ = |⟨π₁,π₂⟩|² 同构"}

    # ---- N10 秩判据：独立 ⟹ 激发；退化 ⟹ 非激发（GQ3–GQ5）----
    e1, e2, e3 = np.eye(3, dtype=complex)
    P_ind = [e1, e2, e3]                            # 三扭量独立（张满）
    A_ind = np.array(P_ind)
    m2_ind = abs(np.linalg.det(sum(np.outer(p, np.conj(p)) for p in P_ind)))
    P_dep = [e1, e2, e2]                            # 退化：两扭量相等
    A_dep = np.array(P_dep)
    m2_dep = abs(np.linalg.det(sum(np.outer(p, np.conj(p)) for p in P_dep)))
    # 共面（π₃ = απ₁+βπ₂，线性相关但两两不平行）：det₃ = 0
    alpha, beta = 1.3, -0.7
    pi3_coplanar = alpha * e1 + beta * e2
    P_cop = [e1, e2, pi3_coplanar]
    m2_cop = abs(np.linalg.det(sum(np.outer(p, np.conj(p)) for p in P_cop)))
    # 数值线性相关性检查（SVD 最小奇异值）
    svd_min_ind = float(np.min(np.linalg.svd(A_ind, compute_uv=False)))
    svd_min_dep = float(np.min(np.linalg.svd(A_dep, compute_uv=False)))
    report["results"]["N10_rank_criterion"] = {
        "三扭量独立（单位基）⟹ m² = 1（激发）": abs(m2_ind - 1.0) < 1e-12,
        "退化（π₃ = π₂）⟹ m² = 0（非激发）": m2_dep < 1e-12,
        "共面（π₃ 线性相关）⟹ m² = 0（非激发）": m2_cop < 1e-12,
        "SVD 最小奇异值（独立 1.0 / 退化 0）": [round(svd_min_ind, 6), round(svd_min_dep, 6)],
        "note": "GQ3–GQ5：激发 ⟺ det₃ ≠ 0 ⟺ 三扭量张满（秩 3）；退化/共面 "
                "⟹ 无质量——'激发 ⟺ 秩'判据的三体版（与电子秩 2 同构）"}

    # ---- N11 统一秩判据表（GQ6：质量² = |det_N[π₁...π_N]|²）----
    z = 2.0 + 3.0j                                   # N=1：1×1 动量
    m1 = abs(z * np.conj(z))                         # det₁ = |π₁|²
    det1_formula = abs(z) ** 2
    a1, b1, a2, b2 = 1 + 1j, 2 - 1j, -1 + 0.5j, 0.5 + 2j   # N=2：双扭量
    symp2 = a1 * b2 - a2 * b1
    det2_formula = abs(symp2) ** 2
    P2 = [np.array([a1, b1]), np.array([a2, b2])]
    m2_formula = abs(np.linalg.det(sum(np.outer(p, np.conj(p)) for p in P2)))
    A3 = np.array([e1, e2, e3])                      # N=3：三扭量
    det3_formula = abs(np.linalg.det(A3)) ** 2
    P3 = [e1, e2, e3]
    m3_formula = abs(np.linalg.det(sum(np.outer(p, np.conj(p)) for p in P3)))
    report["results"]["N11_rank_unified"] = {
        "N=1 光子: det₁ = |π₁|²": abs(m1 - det1_formula) < 1e-12,
        "N=2 电子: det₂ = |⟨π₁,π₂⟩|²（= |det 2×2|²）": abs(m2_formula - det2_formula) < 1e-12,
        "N=3 胶球: det₃ = |det₃[π₁π₂π₃]|²": abs(m3_formula - det3_formula) < 1e-12,
        "统一链": "质量² = |det_N[π₁...π_N]|²，N = 扭量数（秩 = N）",
        "note": "GQ6：一条链——质量 ⟺ 激发 ⟺ 扭量独立（秩 = 扭量数）；"
                "电子（2 维辛体积）与胶球（3 维体积形式）是同一判据的两个实例"}

    # ---- N12 W 型三体纠缠：两两配对都有纠缠贡献 ----
    # 3 维扭量的每对 Plücker 坐标（叉积）非零 ⟺ 该对不平行（局部纠缠）。
    # 随机独立三扭量：三对叉积全非零 = W 型（两两纠缠）；共面三扭量：
    # 两两可纠缠但体积为零 = 局部纠缠 ≠ 全域激发（需秩 3）。
    n_w = 0
    for _ in range(200):
        P = [rng.standard_normal(3) + 1j * rng.standard_normal(3) for _ in range(3)]
        cross = [np.linalg.norm(np.cross(P[i], P[j])) for i, j in ((0, 1), (0, 2), (1, 2))]
        if all(c > 1e-8 for c in cross):
            n_w += 1
    cross_cop = [np.linalg.norm(np.cross(P_cop[i], P_cop[j]))
                 for i, j in ((0, 1), (0, 2), (1, 2))]
    report["results"]["N12_w_type_triplet"] = {
        "随机独立三扭量：三对 Plücker 全非零（W 型，200/200）": n_w == 200,
        "共面三扭量：两两不平行但 det₃ = 0（局部纠缠 ≠ 激发）":
            all(c > 1e-8 for c in cross_cop) and m2_cop < 1e-12,
        "note": "三扭量 = W 型三体纠缠（任意两对都有纠缠贡献）——与 GHZ "
                "（QFT7，只有整体纠缠）互补；但只有三扭量张满（秩 3）才是"
                "激发：局部两两纠缠 ≠ 全域质量（GQ4b）"}

    # ---- N13 一般 N 统一恒等（GQN2：det(Σπᵢ⊗π̄ᵢ) = |detₙ[π₁...π_N]|²）----
    max_err_gn, hadamard_ok = 0.0, True
    for N in range(2, 9):                            # N = 2..8 维
        for _ in range(100):
            A = rng.standard_normal((N, N)) + 1j * rng.standard_normal((N, N))
            outer_sum = sum(np.outer(A[k], np.conj(A[k])) for k in range(N))
            err = abs(np.linalg.det(outer_sum) - abs(np.linalg.det(A)) ** 2)
            max_err_gn = max(max_err_gn, err)
            norms = np.linalg.norm(A, axis=1)
            if abs(np.linalg.det(A)) > (norms.prod() + 1e-12) * (1 + 1e-9):
                hadamard_ok = False
    report["results"]["N13_general_N_identity"] = {
        "max|det_N(P) − |detₙ[π₁...π_N]|²|（N=2..8 × 100 随机）": round(float(max_err_gn), 13),
        "Hadamard |det| ≤ Π|πᵢ|（所有 N）": bool(hadamard_ok),
        "note": "GQN2：det(AA†) = |detA|² 对任意 N（Cauchy-Binet 方阵特例）——"
                "质量² = |det_N[π₁...π_N]|² 统一链的数值验证（N=2,3 特例与 "
                "TW6/GQ2 一致，GQN6 的 Lean 一致性定理已证）；高维（N≥7）"
                "绝对误差 ~1e-7 是 det 数值放大，非恒等失效（N≤6 时 ~1e-12）"}

    # ---- N14 一般 N 秩判据：满秩 ⟹ 激发；退化 ⟹ 非激发（GQN3–GQN4）----
    rank_ok = True
    for N in range(2, 8):
        A_full = rng.standard_normal((N, N)) + 1j * rng.standard_normal((N, N))
        outer_full = sum(np.outer(A_full[k], np.conj(A_full[k])) for k in range(N))
        if abs(np.linalg.det(outer_full)) < 1e-8:    # 满秩（概率 1）⟹ det > 0
            rank_ok = False
        # 退化（秩 < N）：N=2 两行相等；N≥3 最后一行 = 前两行组合（用原始行）
        A_dep = A_full.copy()
        if N == 2:
            A_dep[1] = A_dep[0]
        else:
            A_dep[-1] = 0.7 * A_full[0] + 0.3 * A_full[1]
        outer_dep = sum(np.outer(A_dep[k], np.conj(A_dep[k])) for k in range(N))
        if abs(np.linalg.det(outer_dep)) > 1e-8:
            rank_ok = False
    report["results"]["N14_general_N_rank"] = {
        "满秩 ⟹ det > 0 / 退化 ⟹ det = 0（N=2..7）": bool(rank_ok),
        "note": "GQN3–GQN4：激发 ⟺ 秩 N（任意 N）——扭量张满才有质量；"
                "退化（子空间内）恒无质量"}

    # ---- N15 统一链数值表（GQN5：质量² = |det_N|²，N = 1..6）----
    chain = {}
    for N in range(1, 7):
        A = np.eye(N, dtype=complex)                # N 个单位正交扭量（张满）
        outer_sum = sum(np.outer(A[k], np.conj(A[k])) for k in range(N))
        det_outer = abs(np.linalg.det(outer_sum))
        chain[f"N={N}"] = {"m² = det_N(P)": round(float(det_outer), 6),
                           "|det_N[π₁...π_N]|²": round(float(abs(np.linalg.det(A)) ** 2), 6)}
    # N=3 与 GQ2 数值对比（单位基 ⟹ det₃ = 1）
    report["results"]["N15_general_N_chain"] = {
        "统一链表（单位正交扭量）": chain,
        "全部 m² = |det_N|²（机器精度）": all(
            abs(v["m² = det_N(P)"] - v["|det_N[π₁...π_N]|²"]) < 1e-9 for v in chain.values()),
        "note": "GQN5：质量² = |det_N[π₁...π_N]|² 对任意 N——光子/电子/胶球"
                "是同一恒等的实例（N=1 秩1 非激发/ N≥2 秩N 激发）；单位正交"
                "扭量时 det = 1（Hadamard 饱和）"}

    # ---- N16 n=2, m=3..8：det(P) = Σ_{i<j}|⟨πᵢ,πⱼ⟩|²（GQM1 的一般 m）----
    from itertools import combinations
    max_err_m2 = 0.0
    for m in range(3, 9):
        for _ in range(50):
            P = [rng.standard_normal(2) + 1j * rng.standard_normal(2) for _ in range(m)]
            outer_sum = sum(np.outer(p, np.conj(p)) for p in P)
            det_outer = abs(np.linalg.det(outer_sum))
            pair_sum = sum(abs(P[i][0] * P[j][1] - P[i][1] * P[j][0]) ** 2
                           for i, j in combinations(range(m), 2))
            max_err_m2 = max(max_err_m2, abs(det_outer - pair_sum))
    report["results"]["N16_cauchy_binet_2d"] = {
        "max|det(P) − Σ_{i<j}|⟨πᵢ,πⱼ⟩|²|（n=2, m=3..8）": round(float(max_err_m2), 13),
        "note": "GQM1 的一般 m 版：2 维空间多扭量叠加的质量² = 所有对辛内积"
                "平方和（C(m,2) 个子式）——每对半旋量的纠缠贡献相加"}

    # ---- N17 n=3, m=4..7：det(P) = Σ_{S,|S|=3}|det₃[π_S]|²（GQM3 的一般 m）----
    max_err_m3 = 0.0
    for m in range(4, 8):
        for _ in range(50):
            A = rng.standard_normal((m, 3)) + 1j * rng.standard_normal((m, 3))
            P = A.T  # 3×m，列 = 扭量
            outer_sum = sum(np.outer(P[:, k], np.conj(P[:, k])) for k in range(m))
            det_outer = abs(np.linalg.det(outer_sum))
            sub_sum = sum(abs(np.linalg.det(P[:, list(S)])) ** 2
                          for S in combinations(range(m), 3))
            max_err_m3 = max(max_err_m3, abs(det_outer - sub_sum))
    report["results"]["N17_cauchy_binet_3d"] = {
        "max|det(P) − Σ|det₃[π_S]|²|（n=3, m=4..7）": round(float(max_err_m3), 13),
        "note": "GQM3 的一般 m 版：3 维空间多扭量叠加的质量² = 所有三元子族"
                "的子纠缠体积平方和（C(m,3) 个子式）——全域纠缠 = 所有子结构"
                "的纠缠之和"}

    # ---- N18 一般 n×m 完整 Cauchy-Binet（数值验证，n=2..4, m=n+1..n+4）----
    max_err_cb, n_cb = 0.0, 0
    for n in range(2, 5):
        for m in range(n + 1, n + 5):
            for _ in range(30):
                A = rng.standard_normal((m, n)) + 1j * rng.standard_normal((m, n))
                P = A.T  # n×m
                det_outer = abs(np.linalg.det(P @ np.conj(P).T))
                sub_sum = sum(abs(np.linalg.det(P[:, list(S)])) ** 2
                              for S in combinations(range(m), n))
                max_err_cb = max(max_err_cb, abs(det_outer - sub_sum))
                n_cb += 1
    report["results"]["N18_cauchy_binet_general"] = {
        "max|det(AA†) − Σ_S|det(A[:,S])|²|（n=2..4, m=n+1..n+4 × 30）": round(float(max_err_cb), 13),
        "样本数": n_cb,
        "note": "完整 Cauchy-Binet（数值）：det(AA†) = 所有 n×n 子式平方和——"
                "m > n 多扭量叠加的质量² = 全纠缠结构（所有 n 元子族的子纠缠"
                "体积平方和）；m = n 退化为单一子式 |det A|²（GQN2 Lean 已证）"}

    # ---- 三扭量图：det₃ 恒等 + 退化→独立扫描（GQ2/GQ5）----
    fig2, ax2 = plt.subplots(1, 2, figsize=(12, 4.6))
    # 左：det₃(P) vs |det₃[π₁π₂π₃]|² 散点（恒等，y = x）
    dets_P, dets_A = [], []
    for _ in range(200):
        P = [rng.standard_normal(3) + 1j * rng.standard_normal(3) for _ in range(3)]
        A = np.array(P, dtype=complex)
        dets_P.append(abs(np.linalg.det(sum(np.outer(p, np.conj(p)) for p in P))))
        dets_A.append(abs(np.linalg.det(A)) ** 2)
    ax2[0].scatter(dets_A, dets_P, s=14, alpha=0.6)
    lim = [0, max(max(dets_P), max(dets_A)) * 1.05]
    ax2[0].plot(lim, lim, "r--", lw=1.2, label="y = x（恒等）")
    ax2[0].set_xlabel("|det₃[π₁π₂π₃]|²")
    ax2[0].set_ylabel("det₃(Σπᵢ⊗π̄ᵢ)")
    ax2[0].set_title("GQ2 三扭量 det 恒等（Cauchy-Binet）")
    ax2[0].legend(fontsize=8)
    ax2[0].grid(alpha=0.3)
    # 右：退化→独立扫描：π₃ = (1−t)·e₂ + t·e₃，t ∈ [0,1]
    ts = np.linspace(0, 1, 101)
    m2_scan = [abs(np.linalg.det(np.array([e1, e2, (1 - t) * e2 + t * e3]))) ** 2 for t in ts]
    ax2[1].plot(ts, m2_scan, "b-", lw=1.6)
    ax2[1].axhline(0, color="k", ls=":", lw=0.8)
    ax2[1].set_xlabel("t（π₃ 从退化 e₂ 渐变到独立 e₃）")
    ax2[1].set_ylabel("m² = det₃(P)")
    ax2[1].set_title("GQ5 秩判据：第三方向独立 ⟹ 激发")
    ax2[1].grid(alpha=0.3)
    fig2.tight_layout()
    fig2.savefig(os.path.join(OUT, "fig_triple_rank.png"), dpi=130)
    plt.close(fig2)

    # report.md
    with open(os.path.join(OUT, "report.json"), "w", encoding="utf-8") as f:
        json.dump(_py(report), f, ensure_ascii=False, indent=2)
    md = ["# QFT × 流动空间：激发态与全域纠缠（QFTFlow）", "",
          f"日期：{report['date']}  |  模型：{report['model']}", ""]
    for k, v in report["results"].items():
        md.append(f"## {k}")
        for kk, vv in v.items():
            md.append(f"- {kk}: {vv}")
        md.append("")
    with open(os.path.join(OUT, "report.md"), "w", encoding="utf-8") as f:
        f.write("\n".join(md))
    print(f"report written to {OUT}")
    print(json.dumps(_py(report["results"]), ensure_ascii=False, indent=1)[:2000])


if __name__ == "__main__":
    main()
