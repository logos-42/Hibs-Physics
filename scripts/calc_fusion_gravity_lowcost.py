#!/usr/bin/env python3
"""可控核聚变 × 引力场：**零 GPU / 零离散化参数**的闭式计算器

═════ 动机（leo 2026-10-19）═════
「现在的代码里面计算可控核聚变、使用引力场来实现，有没有低成本的法子？」

现状成本（实测，artifacts/twoflowring_gpu/report*.json）：
  · sim_two_flow_ring_gpu.py --scale mps   → 墙钟 96.63 s（本机 MPS / torch float32）
  · sim_two_flow_ring_gpu.py --scale full  → 墙钟  6.89 s（远端 A100，nseg=2048、
                                              96³=884,736 点全场 + 1e6 流元 × 4000 步 RK4）
  两类重活都来自同一个根源：**Biot–Savart 直接求和** O(点数 × nseg) + **流元逐步推演**。

═════ 本脚本的低成本路线（三条，全部标准数学、不新设物理）═════
  R1 **圆电流环的椭圆积分闭式**（标准电磁学，K/E 完全椭圆积分）：
       同轴圆环在 (ρ,z) 的场有闭式 —— 把 O(N·nseg) 的直接求和换成 O(N) 的精确求值，
       **nseg 离散化参数整个消失**（仓库里「数值 vs 解析 < 2e-3」这类断言的存在本身
       就是因为离散化；闭式下数值即解析，机器精度）。
  R2 **捕获率的解析反演**：push_rk4 的径向方程径向分量恒等 ṙ = ξ
       （ṙ = (x·vx+y·vy)/r = ξ(x²+y²)/r² = ξ，对任意积分器精确成立）
       ⟹ r(t) = r₀ + ξt 精确 ⟹ 捕获率 = r₀ 的均匀分布的一行闭式，
       1e6 流元 × 4000 步的 GPU 扫描换成算术；且容差可**连续反解**
       （GPU 扫描网格 {1e-4,1e-3,1e-2} 只能报 ≤1e-3，闭式给 5.875e-3）。
  R3 **μ / 温度 / 关闭步本来就是闭式**（MUFC/TD）：μ_n = 1−(1−η)ⁿ(1−μ₀)、
       n* = ⌈ln((1−μ₀)/(1−μ_ceil))/ln(1/(1−η))⌉ —— 仓库已在用，零成本。

═════ 本脚本算什么（每个量都对位既有实测产物，见断言）═════
  D1 轴上 B_z(0)（λ=1.5 / 0.4）            ↔ A100 report：−1.6455962657928467 / +0.3291192303760737
  D2 场反判据 λ_crit = R_H/R_Cu = 0.583333
  D3 中平面零点（λ=0.4 → 干净零点 r*=0.242937368 m；λ=1.5 → 只有环上伪零点）
                                            ↔ A100 report：clean=[0.242937368321263] / clean=[]
  D4 轴向分离设计点 d*(λ=1.5) = 1.090526 m  ↔ design-two-flow-ring-axial.md
  D5 捕获率闭式 + ξ 容差连续反解             ↔ A100/MPS report 捕获率_vs_xi
  D6 引力场 Q_A → η（FRC 几何 η≈−20.5；同半径对 η=1 精确）
                                            ↔ artifacts/twoflowring_gravity/report.json
  D7 96³ 全场在笔记本 CPU 上的闭式耗时       ↔ A100 6.89 s

═════ 诚实边界（写死）═════
  · 闭式是**标准电磁学**（圆环场的椭圆积分解），不新设物理、不是新预言；
    它消除的是**离散化误差与算力成本**，不消除任何物理假设
    （点丝模型 / ξ 参化 / μ 主动产生仍是档 3，与上游脚本同一口径）。
  · 点丝模型在环上的近场奇异性保留（闭式在那里正确地发散）⟹ 与仓库既有处理一致。
  · 本脚本不替代 GPU 脚本的**可视化网格**用途，只证明判决量全部可闭式获得。

产物：artifacts/lowcost_calc/{report.json, summary.txt}
"""
import argparse
import json
import math
import os
import time

import numpy as np
from scipy.optimize import brentq
from scipy.special import ellipe, ellipk

REPO = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
OUT = os.path.join(REPO, "artifacts", "lowcost_calc")
os.makedirs(OUT, exist_ok=True)

CHECKS = []
TIMES = {}


def check(name, cond, detail=""):
    CHECKS.append({"检查": name, "通过": bool(cond), "细节": str(detail)})


# ────────────────────────────────────────────────────────────────────────────
# R1：同轴圆电流环的椭圆积分闭式（标准电磁学；u = (Γ/μ₀I)·B 即涡丝流场）
# ────────────────────────────────────────────────────────────────────────────
MU0 = 4.0e-7 * math.pi
R_CU, R_H = 0.60, 0.35            # 外(Cu)/内(H) 环半径 [m]（沿用已定设计）
I_CU = 1.0e6                      # 外环电流 [A]（与 GPU 脚本同口径）


def loop_field_closed(rho, z, a, I):
    """圆环（半径 a、电流 I、位于 z=0 平面）在圆柱坐标 (ρ,z) 的 (B_ρ, B_z)。

    m = k² = 4aρ/((a+ρ)²+z²) ≤ 1（AM-GM，等号仅在丝上）；
      B_z = μ₀I/(2π√((a+ρ)²+z²)) · [K(m) + (a²−ρ²−z²)/((a−ρ)²+z²)·E(m)]
      B_ρ = μ₀I·z/(2πρ√((a+ρ)²+z²)) · [−K(m) + (a²+ρ²+z²)/((a−ρ)²+z²)·E(m)]
    自检：ρ=0 ⟹ B_z = μ₀Ia²/(2(a²+z²)^{3/2})（轴上环公式）；z=0 ⟹ B_ρ = 0（对称性）。
    """
    rho = np.atleast_1d(np.asarray(rho, dtype=float))
    z = np.atleast_1d(np.asarray(z, dtype=float))
    rho, z = np.broadcast_arrays(rho, z)
    den = (a + rho) ** 2 + z ** 2
    sq = np.sqrt(den)
    m = np.clip(4.0 * a * rho / den, 0.0, 1.0 - 1e-16)   # 丝上奇异性保留（m→1 对数发散）
    K, E = ellipk(m), ellipe(m)
    d2 = (a - rho) ** 2 + z ** 2                            # →0 只在丝上
    Bz = MU0 * I / (2.0 * math.pi * sq) * (K + (a * a - rho * rho - z * z) / d2 * E)
    Brho = np.zeros_like(rho)
    nz = z != 0.0
    rho_safe = np.where(rho > 0.0, rho, 1.0)     # 轴上 B_rho ≡ 0（对称性），避开 1/rho
    Brho[nz] = (MU0 * I * z[nz] / (2.0 * math.pi * rho_safe[nz] * sq[nz])
                * (-K[nz] + (a * a + rho[nz] ** 2 + z[nz] ** 2) / d2[nz] * E[nz]))
    return Brho, Bz


def ring_flow_closed(pts, a, gamma, z0):
    """涡丝环流空间流（Γ/4π 版 Biot–Savart）的闭式：u = (Γ/μ₀)·B(I=1)。"""
    x, y, z = pts[:, 0], pts[:, 1], pts[:, 2]
    rho = np.hypot(x, y)
    Brho, Bz = loop_field_closed(rho, z - z0, a, 1.0)
    s = gamma / MU0
    dirx = np.where(rho > 0.0, x / np.maximum(rho, 1e-300), 0.0)
    diry = np.where(rho > 0.0, y / np.maximum(rho, 1e-300), 0.0)
    return np.stack([s * Brho * dirx, s * Brho * diry, s * Bz], axis=1)


def ring_flow_discrete(pts, a, gamma, z0, nseg=512):
    """仓库口径的直接求和（逐字镜像 scripts/verify_two_flow_ring_gravity.py 的 ring_flow），
    仅用于「离散 ⟶ 闭式」的收敛对照与耗时对照。"""
    phi = np.linspace(0.0, 2 * np.pi, nseg, endpoint=False)
    lx, ly = a * np.cos(phi), a * np.sin(phi)
    dl = a * (2 * np.pi / nseg)
    dlx, dly = -np.sin(phi) * dl, np.cos(phi) * dl
    rx = pts[:, None, 0] - lx[None, :]
    ry = pts[:, None, 1] - ly[None, :]
    rz = pts[:, None, 2] - float(z0)
    inv = (gamma / (4 * math.pi)) / np.maximum(rx * rx + ry * ry + rz * rz, 1e-18) ** 1.5
    cx = np.einsum("ns,ns->n", dly[None, :] * rz, inv)
    cy = np.einsum("ns,ns->n", -dlx[None, :] * rz, inv)
    cz = np.einsum("ns,ns->n", dlx[None, :] * ry - dly[None, :] * rx, inv)
    return np.stack([cx, cy, cz], axis=1)


# ────────────────────────────────────────────────────────────────────────────
# D1/D3：轴上场 + 中平面零点（brentq 作用于闭式，无离散化参数）
# ────────────────────────────────────────────────────────────────────────────
def b_axis(lam):
    """B_z(0) = (μ₀I_Cu/2)(1/R_Cu − λ/R_H)（解析；与 GPU 脚本同式）。"""
    return MU0 * I_CU / 2.0 * (1.0 / R_CU - lam / R_H)


def bz_midplane(lam, rho):
    _, b1 = loop_field_closed(rho, np.zeros_like(np.atleast_1d(rho)), R_CU, I_CU)
    _, b2 = loop_field_closed(rho, np.zeros_like(np.atleast_1d(rho)), R_H, -lam * I_CU)
    return b1 + b2


def midplane_zeros(lam, hi=1.15, n=4000, ring_tol=0.02):
    """中平面 z=0 全部零点，按「离导体远近」分类（与 GPU 版同口径：环附近 = 模型近场伪零点）。"""
    rs = np.linspace(1e-4, hi, n)
    bz = bz_midplane(lam, rs)
    sgn = np.sign(bz)
    idx = np.nonzero(sgn[:-1] * sgn[1:] < 0)[0]
    clean, at_ring = [], []
    for k in idx:
        z0 = brentq(lambda r: float(bz_midplane(lam, np.array([r]))[0]),
                    float(rs[k]), float(rs[k + 1]), xtol=1e-14, rtol=1e-14)
        (at_ring if min(abs(z0 - R_H), abs(z0 - R_CU)) < ring_tol else clean).append(z0)
    return sorted(clean), sorted(at_ring)


# ────────────────────────────────────────────────────────────────────────────
# D4：轴向分离（轴上闭式核 f(a,d)=a²/(a²+(d/2)²)^{3/2}，design-two-flow-ring-axial 同式）
# ────────────────────────────────────────────────────────────────────────────
def f_axis(a, d):
    return a * a / (a * a + (d / 2.0) ** 2) ** 1.5


def lambda_of_d(d):
    """两环轴向分离 d 时，使轴上 B_z(0)=0 的电流比 λ（d→∞ ⟶ (R_Cu/R_H)²）。"""
    return f_axis(R_CU, d) / f_axis(R_H, d)


def d_of_lambda(lam):
    """给定 λ，解 f(R_Cu,d) = λ·f(R_H,d) 的分离距离（一对一，见 axial 设计页）。"""
    return brentq(lambda d: f_axis(R_CU, d) - lam * f_axis(R_H, d),
                  1e-9, 50.0, xtol=1e-14, rtol=1e-14)


# ────────────────────────────────────────────────────────────────────────────
# R2/D5：捕获率闭式（ṙ = ξ 精确 ⟹ r(t)=r₀+ξt）+ 容差连续反解
# ────────────────────────────────────────────────────────────────────────────
R_THRESH_FRAC = 0.05      # 偏离自身半径 >5% 视为逃逸（与 push_rk4 同口径）


def capture_closed(xi, t_total, r_lo=R_H, r_hi=R_CU, frac=R_THRESH_FRAC):
    """捕获率 = P(r₀ ≥ |ξ|·t/frac)，r₀ ~ U[r_lo, r_hi] ⟹ 一行闭式。"""
    bound = abs(xi) * t_total / frac
    return float(np.clip((r_hi - max(r_lo, bound)) / (r_hi - r_lo), 0.0, 1.0))


def xi_for_capture(target, t_total, r_lo=R_H, r_hi=R_CU, frac=R_THRESH_FRAC):
    """把「99% 捕获」反解成 ξ 容差（GPU 扫描网格做不到的连续值）。"""
    bound = r_hi - target * (r_hi - r_lo)          # = max(r_lo, |ξ|t/frac)
    if bound < r_lo:                               # 目标低于任何 ξ 能达到的水平
        return 0.0
    return bound * frac / t_total


def push_rk4_np(n_part, n_steps, dt, omega, xi, seed=2):
    """小规模 RK4 复核（numpy CPU）：验证闭式捕获率与积分器实测一致（一次性、廉价）。"""
    g = np.random.default_rng(seed)
    th = g.random(n_part) * 2 * np.pi
    r0 = R_H + (R_CU - R_H) * g.random(n_part)
    x, y = r0 * np.cos(th), r0 * np.sin(th)

    def f(x, y):
        r = np.maximum(np.hypot(x, y), 1e-12)
        return -omega * y + xi * x / r, omega * x + xi * y / r

    for _ in range(n_steps):
        k1x, k1y = f(x, y)
        k2x, k2y = f(x + 0.5 * dt * k1x, y + 0.5 * dt * k1y)
        k3x, k3y = f(x + 0.5 * dt * k2x, y + 0.5 * dt * k2y)
        k4x, k4y = f(x + dt * k3x, y + dt * k3y)
        x = x + dt / 6 * (k1x + 2 * k2x + 2 * k3x + k4x)
        y = y + dt / 6 * (k1y + 2 * k2y + 2 * k3y + k4y)
    drift = np.abs(np.hypot(x, y) - r0)
    return float((drift <= R_THRESH_FRAC * r0).mean())


# ────────────────────────────────────────────────────────────────────────────
# D6：引力场 Q_A → η（目标区口径与 verify_two_flow_ring_gravity.py 逐字一致）
# ────────────────────────────────────────────────────────────────────────────
R_A, Z_A = 0.30, 0.26       # 目标区 A：r ≤ 0.30 m、|z| ≤ 0.26 m（口径）


def qa(flow):
    m = flow.mean(axis=0)
    d = flow - m
    return float((d * d).sum())


def target_zone(n):
    rgr = R_A * np.sqrt((np.arange(n) + 0.5) / n)
    thg = 2 * np.pi * (np.arange(n) + 0.5) / n
    zg = Z_A * (2 * (np.arange(n) + 0.5) / n - 1.0)
    RR, TH, ZZ = np.meshgrid(rgr, thg, zg, indexing="ij")
    return np.stack([(RR * np.cos(TH)).ravel(), (RR * np.sin(TH)).ravel(), ZZ.ravel()], axis=1)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--n", type=int, default=26, help="目标区每轴采样数（n³ 点；与仓库脚本同口径）")
    ap.add_argument("--nseg", type=int, default=512, help="离散对照的段数（仓库默认 512）")
    ap.add_argument("--grid", type=int, default=96, help="三维全场网格每轴点数（A100 full 用 96）")
    a = ap.parse_args()
    t_start = time.time()

    # ── D1 轴上 B_z(0)：闭式 = 解析式，且对位 A100 实测 ────────────────────
    lam, lam_lo = 1.5, 0.40
    b15_closed = float(loop_field_closed(np.array([0.0]), np.array([0.0]), R_CU, I_CU)[1][0]
                       + loop_field_closed(np.array([0.0]), np.array([0.0]), R_H, -lam * I_CU)[1][0])
    b04_closed = float(loop_field_closed(np.array([0.0]), np.array([0.0]), R_CU, I_CU)[1][0]
                       + loop_field_closed(np.array([0.0]), np.array([0.0]), R_H, -lam_lo * I_CU)[1][0])
    A100_F32 = -1.6455962657928467   # A100 report 的轴上探针值是 float32（其自报残差 6.92e-08）
    check("D1 轴上 B_z(0)：椭圆闭式 = 解析式（机器精度）；λ=0.4 与 A100 float64 值逐位一致；"
          "λ=1.5 与 A100 float32 值差 6.92e-08 = float32 ε（闭式消掉它）",
          abs(b15_closed - b_axis(lam)) < 1e-12
          and abs(b15_closed - A100_F32) < 2e-7   # float32 ε = 1.19e-7
          and abs(b04_closed - 0.3291192303760737) < 1e-12,
          f"λ=1.5：闭式 {b15_closed:.16f} = 解析 {b_axis(lam):.16f}；"
          f"A100 float32 参考差 {abs(b15_closed - A100_F32):.2e}（即 GPU 脚本自报的 6.92e-08 残差）；"
          f"λ=0.4：闭式 vs A100 float64 差 {abs(b04_closed - 0.3291192303760737):.1e}")

    # ── D2 场反判据 ───────────────────────────────────────────────────────
    lam_crit = R_H / R_CU
    check("D2 场反位形判据 λ_crit = R_H/R_Cu = 0.583333（轴上闭式的根）",
          abs(lam_crit - 0.5833333333) < 1e-9
          and abs(b_axis(lam_crit)) < 1e-9
          and b_axis(lam) < 0 and b_axis(lam_lo) > 0,
          f"λ_crit = {lam_crit:.10f}；λ=1.5 ⟹ B_z(0)={b_axis(lam):.4f}<0（核心反向）；"
          f"λ=0.4 ⟹ B_z(0)={b_axis(lam_lo):.4f}>0（未反向）")

    # ── D3 中平面零点（闭式 brentq，无 nseg） ──────────────────────────────
    t0 = time.time()
    clean_lo, ring_lo = midplane_zeros(lam_lo)
    clean_hi, ring_hi = midplane_zeros(lam)
    TIMES["D3_中平面零点_秒"] = round(time.time() - t0, 4)
    check("D3a λ=0.4：干净内层零点 r* = 0.242937368 m（A100 0.242937368321263，无离散化误差）",
          len(clean_lo) == 1 and abs(clean_lo[0] - 0.242937368321263) < 1e-9
          and all(abs(z - R_H) < 0.01 or abs(z - R_CU) < 0.01 for z in ring_lo),
          f"clean = {[round(z, 9) for z in clean_lo]}；环附近伪零点 = {[round(z, 6) for z in ring_lo]}")
    check("D3b λ=1.5：除导体近场外**没有**干净零点 ⟹ 共面双环给不出离开导体的中性面"
          "（GPU 版同一结论，闭式零成本重得）",
          clean_hi == [] and len(ring_hi) >= 1
          and min(abs(z - R_H) for z in ring_hi) < 0.01,
          f"clean = {clean_hi}；变号点 = {[round(z, 6) for z in ring_hi]}（内环 R_H={R_H}）"
          f"⟹ 要真中性面必须轴向分离（见 D4）")

    # ── D4 轴向分离设计点 ─────────────────────────────────────────────────
    t0 = time.time()
    d_star = d_of_lambda(lam)
    lam_inf = lambda_of_d(1e6)
    TIMES["D4_轴向分离_秒"] = round(time.time() - t0, 4)
    check("D4 轴向分离：λ=1.5 ⟹ d* = 1.090526 m（对位 design-two-flow-ring-axial.md），"
          "且 d→∞ 时 λ→(R_Cu/R_H)² = 2.938775",
          abs(d_star - 1.090526) < 1e-6 and abs(lam_inf - (R_CU / R_H) ** 2) < 1e-6,
          f"d*(λ=1.5) = {d_star:.6f} m；λ(d→∞) = {lam_inf:.6f} = (R_Cu/R_H)²")
    # 闭式自洽：代回全场（含离轴）确认轴上零点
    bz_after = float(loop_field_closed(np.array([0.0]), np.array([0.0]), R_CU, I_CU)[1][0]
                     + loop_field_closed(np.array([0.0]), np.array([0.0]), R_H, -lam * I_CU)[1][0])
    bz_sep = float(loop_field_closed(np.array([0.0]), np.array([d_star / 2]), R_CU, I_CU)[1][0]
                   + loop_field_closed(np.array([0.0]), np.array([-d_star / 2]), R_H, -lam * I_CU)[1][0])
    check("D4b 共版对照：同一 λ=1.5，共面轴上 {:.4f} T ≠ 0，轴向分离 d* 后轴上 {:.2e} T = 0".format(bz_after, bz_sep),
          abs(bz_after) > 1.0 and abs(bz_sep) < 1e-9,
          f"共面 B_z(0) = {bz_after:.6f} T（整体反向）；分离 d* 后 B_z(0) = {bz_sep:.2e} T")

    # ── D5 捕获率闭式 + 容差连续反解 ──────────────────────────────────────
    t_total = 300 * 0.01          # MPS/A100 扫描口径：nsteps//4 × dt = 300 × 0.01 = 3.0 s
    xi_grid = [0.0, 1e-4, 1e-3, 1e-2, 0.1]
    cap_closed = {x: capture_closed(x, t_total) for x in xi_grid}
    xi_99 = xi_for_capture(0.99, t_total)
    check("D5a 捕获率闭式逐点复现 GPU 扫描（A100：{1.0, 1.0, 1.0, 0.0, 0.0}；MPS 的 2e-5 是采样噪声）",
          abs(cap_closed[0.0] - 1.0) < 1e-15 and abs(cap_closed[1e-4] - 1.0) < 1e-15
          and abs(cap_closed[1e-3] - 1.0) < 1e-15 and cap_closed[1e-2] < 1e-3
          and cap_closed[0.1] == 0.0,
          "；".join(f"ξ={x:g}→闭式 {cap_closed[x]:.4f}" for x in xi_grid)
          + f"（t_total={t_total} s，ṙ=ξ 精确 ⟹ r(t)=r₀+ξt）")
    check("D5b ★ 容差连续反解：99% 捕获允许 ξ ≤ {:.6f}（GPU 扫描网格只能报 ≤1e-3，"
          "闭式细 5.9×）".format(xi_99),
          0 < xi_99 < 1e-2 and abs(xi_99 - 0.005875) < 1e-9,
          f"ξ_99 = (R_Cu − 0.99(R_Cu−R_H))·0.05/t = {xi_99:.6f}；"
          f"100% 捕获 ξ ≤ {xi_for_capture(1.0, t_total):.6f}（= 0.05·R_H/t）")
    # 小规模 RK4 复核（一次性、廉价）：闭式 vs 积分器
    t0 = time.time()
    n_part, n_steps, dt, omega = 20000, 300, 0.01, 2.0
    cap_rk4 = {x: push_rk4_np(n_part, n_steps, dt, omega, x, seed=2) for x in (0.0, 1e-3, 1e-2)}
    TIMES["D5_RK4复核_秒"] = round(time.time() - t0, 3)
    tol_samp = 3.0 / math.sqrt(n_part)
    check("D5c 小 RK4 复核（2e4 流元 × 300 步，CPU）：捕获率与闭式一致到采样误差内",
          all(abs(cap_rk4[x] - capture_closed(x, t_total)) <= max(tol_samp, 1e-3)
              for x in cap_rk4),
          "；".join(f"ξ={x:g}→RK4 {cap_rk4[x]:.4f} vs 闭式 {capture_closed(x, t_total):.4f}"
                    for x in cap_rk4) + f"（采样 tolerance {tol_samp:.4f}）")

    # ── D6 引力场 Q_A → η：闭式 vs 仓库离散口径 ───────────────────────────
    pts = target_zone(a.n)
    t0 = time.time()
    c_cu_c = ring_flow_closed(pts, R_CU, +1.0, 0.0)
    c_h_c = ring_flow_closed(pts, R_H, -1.0, 0.0)
    q_cu_c, q_h_c, q_both_c = qa(c_cu_c), qa(c_h_c), qa(c_cu_c + c_h_c)
    eta_c = 1.0 - q_both_c / max(q_cu_c, 1e-300)
    q_same_c = qa(c_cu_c + ring_flow_closed(pts, R_CU, -1.0, 0.0))
    TIMES["D6_闭式Q_A_秒"] = round(time.time() - t0, 4)
    t0 = time.time()
    c_cu_d = ring_flow_discrete(pts, R_CU, +1.0, 0.0, a.nseg)
    c_h_d = ring_flow_discrete(pts, R_H, -1.0, 0.0, a.nseg)
    q_cu_d, q_both_d = qa(c_cu_d), qa(c_cu_d + c_h_d)
    eta_d = 1.0 - q_both_d / max(q_cu_d, 1e-300)
    TIMES["D6_离散Q_A_秒"] = round(time.time() - t0, 4)
    rel_q = abs(q_cu_c - q_cu_d) / q_cu_d
    rel_eta = abs(eta_c - eta_d) / abs(eta_d)
    check("D6a FRC 几何（R_Cu=0.60 / R_H=0.35）给不出引力关闭：η < 0，闭式与仓库 nseg=512 口径一致",
          eta_c < 0 and rel_eta < 1e-6,
          f"闭式 Q_A：单Cu {q_cu_c:.4e} / 单H {q_h_c:.4e} / 双环 {q_both_c:.4e} ⟹ η = {eta_c:+.4f}；"
          f"仓库口径（report.json）η ≈ −20.53；相对差 {rel_eta:.2e}")
    check("D6b 地基自检：同半径 + 反环量 ⟹ Q_A(抵消对) = 0（机器精度）⟹ η = 1 精确（一步 μ=1）",
          q_same_c / max(q_cu_c, 1e-300) < 1e-12,
          f"Q_A(抵消对) = {q_same_c:.3e} vs Q_A(单环) = {q_cu_c:.3e}（比值 {q_same_c / max(q_cu_c, 1e-300):.2e}）")
    speedup = TIMES["D6_离散Q_A_秒"] / max(TIMES["D6_闭式Q_A_秒"], 1e-9)
    check("D6c 成本：闭式在 n={} 目标区（{} 点）上算 Q_A 比 nseg={} 直接求和快 ≥10×"
          "且无离散化参数".format(a.n, pts.shape[0], a.nseg),
          speedup >= 10.0 and rel_q < 1e-6,
          f"闭式 {TIMES['D6_闭式Q_A_秒']} s vs 离散 {TIMES['D6_离散Q_A_秒']} s（×{speedup:.1f}）；"
          f"Q_A 相对差 {rel_q:.2e}（周期梯形的指数收敛 ⟹ nseg=512 已近精确，闭式是其极限）")
    # 离散收敛对照：加大 nseg 应收敛到闭式（闭式 = nseg→∞ 极限）
    t0 = time.time()
    c_cu_d4 = ring_flow_discrete(pts, R_CU, +1.0, 0.0, 2048)
    rel_q4 = abs(qa(c_cu_d4) - q_cu_c) / q_cu_c
    TIMES["D6_离散Q_A_nseg2048_秒"] = round(time.time() - t0, 3)
    check("D6d 离散→闭式收敛：nseg=2048 与闭式的 Q_A 相对差 < 1e-9（闭式 = nseg→∞ 极限）",
          rel_q4 < 1e-9,
          f"nseg=2048 vs 闭式：相对差 {rel_q4:.2e}（耗时 {TIMES['D6_离散Q_A_nseg2048_秒']} s）")

    # ── D7 96³ 全场：笔记本 CPU 闭式耗时（对位 A100 full 的 6.89 s） ─────
    t0 = time.time()
    axg = np.linspace(-1.20, 1.20, a.grid)
    X, Y, Z = np.meshgrid(axg, axg, axg, indexing="ij")
    gpts = np.stack([X.ravel(), Y.ravel(), Z.ravel()], axis=1)
    del X, Y, Z
    Bg = np.zeros((gpts.shape[0], 3))
    for (rad, cur) in ((R_CU, I_CU), (R_H, -lam * I_CU)):
        Brho, Bz = loop_field_closed(np.hypot(gpts[:, 0], gpts[:, 1]), gpts[:, 2], rad, cur)
        rho = np.hypot(gpts[:, 0], gpts[:, 1])
        Bg[:, 0] += Brho * np.where(rho > 0, gpts[:, 0] / np.maximum(rho, 1e-300), 0.0)
        Bg[:, 1] += Brho * np.where(rho > 0, gpts[:, 1] / np.maximum(rho, 1e-300), 0.0)
        Bg[:, 2] += Bz
    grid_ok = bool(np.isfinite(Bg).all()) and float(np.abs(Bg).max()) > 0
    TIMES["D7_全场网格_秒"] = round(time.time() - t0, 3)
    check("D7 {}³ = {:,} 点全场（CPU 闭式，无 torch/GPU）：有限且非零，耗时 {:.2f} s"
          "（A100 full 同类全场 6.89 s，且本机无 CUDA）".format(a.grid, gpts.shape[0], TIMES["D7_全场网格_秒"]),
          grid_ok and TIMES["D7_全场网格_秒"] < 60.0,
          f"max|B| = {float(np.abs(Bg).max()):.4e} T；墙钟 {TIMES['D7_全场网格_秒']} s；"
          f"flops ≈ {gpts.shape[0] * 40:.2e}（vs 直接求和 ×nseg=2048 ⟹ ~1.8e9）")

    # ── D8 μ 动力学闭式（FC11 天花板 + 关闭步，对位仓库锚点） ─────────────
    mu0, eta = 0.15, 0.05
    ME_OVER_MI = 1.0 / (2.5 * 1822.888486209)
    MU_CEIL = 1.0 - ME_OVER_MI
    n_star = int(math.ceil(math.log((1 - mu0) / (1 - MU_CEIL)) / math.log(1.0 / (1.0 - eta))))
    mu_n = lambda n: 1.0 - (1.0 - eta) ** n * (1.0 - mu0)
    check("D8 μ 闭式：n*(η=0.05, μ₀=0.15) = 162（对位 design-two-flow-ring.md 锚点）；"
          "FC11 天花板 μ < 0.999780568036375",
          n_star == 162 and abs(MU_CEIL - 0.999780568036375) < 1e-12
          and mu_n(n_star) >= MU_CEIL > mu_n(n_star - 1),
          f"n* = {n_star}；μ(n*) = {mu_n(n_star):.12f} ≥ {MU_CEIL:.12f} > μ(n*−1) = {mu_n(n_star - 1):.12f}；"
          f"η=1（同半径对）⟹ μ₁ = {1.0 - (1.0 - 1.0) ** 1 * (1.0 - mu0):.1f} 一步到 1（TD12）")

    # ── 汇总 ──────────────────────────────────────────────────────────────
    total = round(time.time() - t_start, 3)
    out = {
        "产物": "可控核聚变 × 引力场：闭式计算器（零 GPU / 零离散化参数）",
        "路线": {
            "R1 椭圆积分闭式（圆环场）": "O(N·nseg) 直接求和 → O(N) 精确求值，nseg 参数消失",
            "R2 捕获率解析反演": "ṙ=ξ 精确 ⟹ r(t)=r₀+ξt ⟹ 捕获率/容差一行闭式",
            "R3 μ/温度闭式": "μ_n=1−(1−η)ⁿ(1−μ₀)、n*=⌈ln((1−μ₀)/(1−μ_ceil))/ln(1/(1−η))⌉",
        },
        "对位实测": {
            "轴上_Bz0_lam1.5": b15_closed, "A100_实测": -1.6455962657928467,
            "轴上_Bz0_lam0.4": b04_closed, "A100_实测_lam0.4": 0.3291192303760737,
            "中平面干净零点_lam0.4": clean_lo, "A100_实测": 0.242937368321263,
            "轴向分离_d_star_m": d_star, "design页锚点": 1.090526,
            "eta_FRC几何": eta_c, "仓库report锚点": -20.53,
            "n_star": n_star, "仓库锚点": 162,
        },
        "捕获率闭式_vs_xi": {str(k): v for k, v in cap_closed.items()},
        "xi容差_99pct": xi_99,
        "xi容差_100pct": xi_for_capture(1.0, t_total),
        "RK4复核": {str(k): v for k, v in cap_rk4.items()},
        "成本账本": {
            "现状_GPU_mps_秒": 96.63, "现状_GPU_A100_full_秒": 6.89,
            "本脚本各项_秒": TIMES,
            "本脚本总计_秒": total,
            "96³全场_flops比": "闭式 ≈ N×40 vs 直接求和 ≈ N×2048×2（≈ 100×）",
        },
        "诚实边界": [
            "闭式是标准电磁学（圆环场椭圆积分解），不新设物理、不是新预言",
            "消除的是离散化误差与算力成本，不消除物理假设（点丝模型 / ξ 参化 / μ 主动产生仍档 3）",
            "点丝近场奇异性在闭式中正确保留（m→1 对数发散），与仓库既有处理一致",
            "不替代 GPU 脚本的可视化网格用途；本脚本证明判决量全部可闭式获得",
        ],
        "checks": CHECKS,
    }
    with open(os.path.join(OUT, "report.json"), "w", encoding="utf-8") as fh:
        json.dump(out, fh, ensure_ascii=False, indent=2)
    n_ok = sum(1 for c in CHECKS if c["通过"])
    with open(os.path.join(OUT, "summary.txt"), "w", encoding="utf-8") as fh:
        fh.write(f"聚变×引力场闭式计算器：{n_ok}/{len(CHECKS)} 通过；总计 {total} s（零 GPU）；"
                 f"B_z(0)λ=1.5={b15_closed:.10f}（A100 一致）；r*={clean_lo[0]:.9f}；"
                 f"d*={d_star:.6f} m；η(FRC)={eta_c:+.4f}；ξ_99={xi_99:.6f}；n*={n_star}\n")
    print(f"聚变×引力场闭式计算器：{n_ok}/{len(CHECKS)} 通过 | 总计 {total} s（零 GPU、零离散化参数）")
    for c in CHECKS:
        print(("  PASS  " if c["通过"] else "  FAIL  ") + c["检查"])
        if c["细节"]:
            print("         " + c["细节"])
    return 0 if n_ok == len(CHECKS) else 1


if __name__ == "__main__":
    raise SystemExit(main())
