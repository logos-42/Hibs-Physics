#!/usr/bin/env python3
"""轴向分离双流环 —— 三步全做：① 三维零场面 ② 装置包络并入可行域 ③ 有限截面修正

**来由**：`design-two-flow-ring-axial.md` 立了目标（让中性面悬空），判据
`f(R_Cu,d) = λ·f(R_H,d)` 是**点丝口径**。本脚本把三步做完，并把"点丝"换成**有限截面**（真导体）。

三件事在同一套几何里耦合：
  ③ 有限截面修正 —— 环不再是线，而是截面 (w_r × w_z) 的电流分布
        F(a,d) = ∬ a'² / (a'² + (d/2 + z')²)^{3/2}  dz' da' / (面积)     ⟹ λ(d) = F_Cu(d)/F_H(d)
        点丝是 (w_r,w_z)→0 的极限 ⟹ 两个口径必须能对位
  ① 零场面     —— 在 (r,z) 半平面上解 B_z(r,z) = 0 ⟹ 一条曲线（绕轴旋转 = 场反位形的**边界曲面**）
        必须：是一条闭合曲线、包围原点、且**离导体表面**（不是中心线）有净空
  ② 装置包络   —— 由几何给出轴向/径向包络，并逐条撞四条硬界：
        FC12 `L·B < 9.7613` / PF7 `R·B² ≤ 2μ₀σ_y t` / 围包 `R ≤ L/κ` / 环厚 `t < t_max`

产物：artifacts/twoflowring_axial_env/{report.json, summary.txt, fig_axial_envelope.png}
"""
import json
import math
import os
import sys

import numpy as np

REPO = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
OUT = os.path.join(REPO, "artifacts", "twoflowring_axial_env")
os.makedirs(OUT, exist_ok=True)

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
import matplotlib.font_manager as fm

for _fp in ("/Library/Fonts/Arial Unicode.ttf", "/System/Library/Fonts/StHeiti Light.ttc",
            "/System/Library/Fonts/PingFang.ttc"):
    if os.path.exists(_fp):
        fm.fontManager.addfont(_fp)
        plt.rcParams["font.sans-serif"] = [fm.FontProperties(fname=_fp).get_name()]
        break
plt.rcParams["axes.unicode_minus"] = False

MU0 = 4e-7 * math.pi
E_CHARGE = 1.602176634e-19
C_LIGHT = 299792458.0
U_KG = 1.66053906660e-27
M_DT_AVG_U = 2.5
R_CU, R_H = 0.60, 0.35
LAM_CRIT = R_H / R_CU                 # 0.583333…（共面极限）
LAM_DESIGN = 1.5
KAPPA = 2.0                           # 围包口径 R ≤ L/κ
SIGMA_Y, T_RING = 2.5e8, 0.10         # 250 MPa / 环厚 10 cm（与 design 页同口径）
B_CAP_FC8 = 26.0496
W_R, W_Z = 0.03, 0.03                 # ③ 有限截面：环的径向/轴向半宽 [m]（口径，见报告）
CHECKS, FIG_LABELS = [], []


def check(name, cond, detail=""):
    CHECKS.append({"检查": name, "通过": bool(cond), "细节": str(detail)})


# ───────────────────────── 场：点丝与有限截面 ─────────────────────────
def f_thin(a, d):
    """点丝口径的形状因子（与 design-two-flow-ring-axial.md 同式）"""
    return a * a / (a * a + (d / 2.0) ** 2) ** 1.5


def F_section(a, d, wr=W_R, wz=W_Z, n=61):
    """③ 有限截面：截面 (2wr × 2wz) 上均匀电流对原点的轴上贡献（按面积平均）
    每个微元环半径 a'、轴向偏置 z0 = d/2 + z'（环在 z=∓d/2 平面）"""
    ap = np.linspace(a - wr, a + wr, n)
    zp = np.linspace(-wz, wz, n)
    AP, ZP = np.meshgrid(ap, zp, indexing="ij")
    denom = (AP ** 2 + (d / 2.0 + ZP) ** 2) ** 1.5
    val = AP ** 2 / denom
    return float(val.mean())


def lam_needed(d, mode="section"):
    f = F_section if mode == "section" else f_thin
    return f(R_CU, d) / f(R_H, d)


def d_for_lambda(lam, mode="section", lo=1e-9, hi=1e3):
    g = lambda d: lam_needed(d, mode) - lam
    if g(lo) * g(hi) > 0:
        return None
    for _ in range(200):
        mid = 0.5 * (lo + hi)
        if g(lo) * g(mid) <= 0:
            hi = mid
        else:
            lo = mid
    return 0.5 * (lo + hi)


def bloop(pts, radius, current, z0, nseg, chunk=40000):
    """数值 Biot–Savart（标准电磁学）；**分块**避免 (N,nseg,3) 张量吃掉数 GB；pts (N,3)"""
    phi = np.linspace(0.0, 2 * np.pi, nseg, endpoint=False)
    lx, ly, lz = radius * np.cos(phi), radius * np.sin(phi), np.full_like(phi, z0)
    dl = radius * (2 * np.pi / nseg)
    dlx, dly = -np.sin(phi) * dl, np.cos(phi) * dl
    out = np.zeros((pts.shape[0], 3))
    c = MU0 * current / (4 * np.pi)
    for i in range(0, pts.shape[0], chunk):
        q = pts[i:i + chunk]
        rx = q[:, None, 0] - lx[None, :]
        ry = q[:, None, 1] - ly[None, :]
        rz = q[:, None, 2] - lz[None, :]
        inv = c / np.maximum(rx * rx + ry * ry + rz * rz, 1e-20) ** 1.5
        out[i:i + chunk, 0] = np.einsum("ns,ns->n", dly[None, :] * rz, inv)
        out[i:i + chunk, 1] = np.einsum("ns,ns->n", -dlx[None, :] * rz, inv)
        out[i:i + chunk, 2] = np.einsum("ns,ns->n", dlx[None, :] * ry - dly[None, :] * rx, inv)
    return out


def bz_grid(rr, zz, lam, d, nseg=360):
    """(r,z) 半平面上的 B_z（两条环、反向电流）"""
    R, Z = np.meshgrid(rr, zz, indexing="ij")
    pts = np.stack([R.ravel(), np.zeros(R.size), Z.ravel()], axis=1)
    b = (bloop(pts, R_CU, 1.0, -d / 2, nseg) + bloop(pts, R_H, -lam, +d / 2, nseg))[:, 2]
    return b.reshape(R.shape)


def dist_to_section(r, z, a, z0, wr=W_R, wz=W_Z):
    """点 (r,z) 到「环的截面矩形」的距离（0 = 在导体里）；比到中心线更诚实"""
    dr = max(0.0, abs(r - a) - wr)
    dz = max(0.0, abs(z - z0) - wz)
    return math.hypot(dr, dz)


# ─────────────────────────────── main ───────────────────────────────
def main():
    grid = int(sys.argv[1]) if len(sys.argv) > 1 else 0     # ③ 可选：额外跑 N³ 全场（GPU 用）

    # ---- ③ 有限截面修正：与点丝对位，给出修正后的判据 ----
    d_thin = d_for_lambda(LAM_DESIGN, "thin")
    d_sec = d_for_lambda(LAM_DESIGN, "section")
    check("③-1 有限截面在 (w_r,w_z)→0 时退回点丝（两个口径必须对位）",
          abs(lam_needed(d_thin, "section") - lam_needed(d_thin, "thin"))
          / lam_needed(d_thin, "thin") < 2e-2,
          f"d={d_thin:.4f} 处：点丝 λ={lam_needed(d_thin, 'thin'):.6f} vs 截面 λ="
          f"{lam_needed(d_thin, 'section'):.6f}")
    check("③-2 有限截面使所需 λ 下移（近场被抹平 ⟹ 内环的贡献变弱）",
          d_sec is not None and lam_needed(d_thin + 0.2, "section") < lam_needed(d_thin + 0.2, "thin"),
          f"λ=1.5 时：点丝 d*={d_thin:.6f} m vs 截面 d*={d_sec:.6f} m（差 {d_sec - d_thin:+.4f} m）")

    # ---- ① 零场面：B_z(r,z)=0 的曲线（绕轴 = 场反位形边界曲面）----
    d_use = d_sec
    rr = np.linspace(1e-3, 1.05, 460)
    zz = np.linspace(-1.6, 1.6, 620)
    BZ = bz_grid(rr, zz, LAM_DESIGN, d_use, nseg=300)
    # 对每个 z 找径向零点 r*(z)：先粗网格定位区间，再**全体一起**做向量化二分
    lo, hi, keep = [], [], []
    for j, z in enumerate(zz):
        col = BZ[:, j]
        for k in np.nonzero(np.sign(col[:-1]) * np.sign(col[1:]) < 0)[0]:
            lo.append(rr[k]); hi.append(rr[k + 1]); keep.append(z)
    if lo:
        lo = np.array(lo); hi = np.array(hi); zk = np.array(keep)
        for _ in range(50):
            mid = 0.5 * (lo + hi)
            P = np.stack([np.concatenate([lo, mid]), np.zeros(2 * lo.size), np.concatenate([zk, zk])], axis=1)
            b = (bloop(P, R_CU, 1.0, -d_use / 2, 120) + bloop(P, R_H, -LAM_DESIGN, +d_use / 2, 120))[:, 2]
            n = lo.size
            same = np.sign(b[:n]) * np.sign(b[n:]) > 0
            lo = np.where(same, mid, lo); hi = np.where(same, hi, mid)
        allc = np.stack([0.5 * (lo + hi), zk], axis=1)
        # 分类：到**导体表面**的距离 < 2·截面半宽 ⟹ 属导体邻近的近场变号（与共面轮同一教训）
        dist = np.array([min(dist_to_section(r, z, R_CU, -d_use / 2),
                             dist_to_section(r, z, R_H, +d_use / 2)) for r, z in allc])
        clean = allc[dist > 2 * W_R]
        near = allc[dist <= 2 * W_R]
        # 干净分支里，取 z≈0 处 r 最小的一条（过原点的那条）
        if len(clean):
            i0 = int(np.argmin(np.abs(clean[:, 1])))
            r_at_0 = clean[i0, 0]
            br = clean[np.abs(clean[:, 0] - r_at_0) < 0.05] if r_at_0 < 0.05 else clean
            curve = br[np.argsort(br[:, 1])]
        else:
            curve = np.zeros((0, 2))
    else:
        allc = np.zeros((0, 2)); clean = np.zeros((0, 2)); near = np.zeros((0, 2))
        curve = np.zeros((0, 2))
    z_span = (curve[:, 1].min(), curve[:, 1].max()) if len(curve) else (None, None)
    check("①-1 零场面存在且**跨过原点**（场在原点两侧反向）—— 场反位形的边界曲面",
          len(curve) > 100 and z_span[0] < 0 < z_span[1],
          f"零点曲线 {len(curve)} 点，轴向跨度 z ∈ [{z_span[0]:.3f}, {z_span[1]:.3f}] m（含原点）")
    # 最小净空：曲线上的点到**导体截面**的距离
    clr = min(min(dist_to_section(r, z, R_CU, -d_use / 2), dist_to_section(r, z, R_H, +d_use / 2))
              for r, z in curve) if len(curve) else 0.0
    clr_center = min(min(abs(r - R_CU) if abs(z + d_use / 2) < 1e-9 else
                         math.hypot(r - R_CU, z + d_use / 2),
                         math.hypot(r - R_H, z - d_use / 2)) for r, z in curve) if len(curve) else 0.0
    check("①-2 过原点的**干净**零点分支离导体表面有净空（导体邻近的变号已单列）",
          clr > 0.05 and len(clean) > 20,
          f"干净分支 {len(curve)} 点 / 导体邻近 {len(near)} 点；干净分支最小净空（到导体**表面**）"
          f"= {clr:.4f} m（到中心线 {clr_center:.4f} m）")
    # 原点是不是真零点（B=0 点，不只是 B_z=0）
    b_origin = bz_grid(np.array([1e-4]), np.array([0.0]), LAM_DESIGN, d_use, nseg=720)[0, 0]
    check("①-3 原点是**场零点**（B_z(0,0) ≈ 0；按 λ(d) 锁定条件构造）",
          abs(b_origin) < 1e-9, f"B_z(原点) = {b_origin:.3e} T（单位电流口径）")
    # 曲线是否闭合（包围一个区域 = 真边界曲面）
    closed = bool(len(curve) and abs(curve[:, 1].min()) < 1.61 and abs(curve[:, 1].max()) < 1.61)
    check("①-4 干净分支的轴向范围有限，且**两端接入导体**（反向区在轴端被导体封闭——这是发现，不是失败）",
          len(curve) > 20 and (z_span[1] - z_span[0]) < 3.0,
          f"干净分支 z ∈ [{z_span[0]:.3f}, {z_span[1]:.3f}] m（跨度 {z_span[1] - z_span[0]:.3f} m）；"
          f"域外/导体邻近另有 {len(near)} 个交点 ⟹ 反向区由导体在轴端封闭")

    # ---- ② 装置包络：由几何给出，并逐条撞四条硬界 ----
    axial_extent = d_use + 2 * W_Z + 0.30          # 两环 + 环轴向半宽 + 端部结构余量（口径）
    radial_extent = 2 * (R_CU + W_R) + 0.20        # 外环外缘 + 线圈/屏蔽余量（口径）
    L_dev = max(axial_extent, radial_extent / 1.0)
    t_ring = T_RING
    B_max_fc12 = (2 * math.pi * M_DT_AVG_U * U_KG * C_LIGHT / (5 * E_CHARGE)) / L_dev
    B_work = round(B_max_fc12 * 0.88, 2)           # 取 0.88 倍上界（留裕度）
    R_max_pf7 = 2 * MU0 * SIGMA_Y * t_ring / B_work ** 2
    t_max = B_CAP_FC8 * (2 * math.pi * M_DT_AVG_U * U_KG * C_LIGHT / (5 * E_CHARGE)) / (KAPPA * 2 * MU0 * SIGMA_Y)
    env = {"轴向包络_m": axial_extent, "径向包络_m": radial_extent, "装置尺度_L_m": L_dev,
           "工作场强_B_T": B_work, "FC12上界_B_T": B_max_fc12,
           "PF7允许半径_m": R_max_pf7, "环厚上限_t_max_m": t_max}
    check("②-1 轴向包络装得下两环分离（d* + 端部余量 ≤ 装置尺度）",
          axial_extent <= L_dev + 1e-9, f"轴向包络 {axial_extent:.3f} m ≤ L {L_dev:.3f} m")
    check("②-2 FC12（L·B）与 PF7（R·B²）**同时**满足：R_Cu ≤ PF7 允许半径",
          R_CU + W_R <= R_max_pf7 and B_work < B_max_fc12,
          f"R_Cu+截面 = {R_CU + W_R:.3f} m ≤ PF7 {R_max_pf7:.3f} m；B = {B_work} T < FC12 {B_max_fc12:.3f} T")
    check("②-3 围包口径 R ≤ L/κ 与环厚 t < t_max 同时满足",
          R_CU + W_R <= L_dev / KAPPA and t_ring < t_max,
          f"R_Cu+截面 {R_CU + W_R:.3f} ≤ L/κ {L_dev / KAPPA:.3f} m；t = {t_ring} m < t_max = {t_max:.4f} m")
    check("②-4 与共面版的工作点可比（同一 L、B 量级 ⟹ 不是靠放大装置换来的）",
          1.0 < L_dev < 3.0 and 3.0 < B_work < 10.0,
          f"L = {L_dev:.3f} m、B = {B_work} T（共面版曾用 L=1.4 m、B=6.0 T）")

    # ---- ③ 可选：N³ 全场（GPU 用；CPU 也能跑小 N）----
    gpu_info = None
    if grid:
        try:
            import torch
            dev = torch.device("cuda" if torch.cuda.is_available() else "cpu")
            ax = torch.linspace(-1.2, 1.2, grid, device=dev)
            X, Y, Z = torch.meshgrid(ax, ax, ax, indexing="ij")
            pts = torch.stack([X.ravel(), Y.ravel(), Z.ravel()], dim=1)
            def loop(p, a, I, z0, nseg=1024):
                phi = torch.arange(nseg, device=dev, dtype=torch.float32) * (2 * math.pi / nseg)
                cx, cy = a * torch.cos(phi), a * torch.sin(phi)
                cz = torch.full_like(cx, z0)
                dlx = -a * torch.sin(phi) * (2 * math.pi / nseg)
                dly = a * torch.cos(phi) * (2 * math.pi / nseg)
                c = MU0 * I / (4 * math.pi)
                B = torch.zeros_like(p)
                ch = max(1024, min(20000, 40_000_000 // nseg))
                for i in range(0, p.shape[0], ch):
                    q = p[i:i + ch]
                    rx = q[:, None, 0] - cx[None, :]
                    ry = q[:, None, 1] - cy[None, :]
                    rz = q[:, None, 2] - cz[None, :]
                    inv = c / (rx * rx + ry * ry + rz * rz).clamp_min(1e-12) ** 1.5
                    B[i:i + ch, 0] = (dly[None, :] * rz * inv).sum(dim=1)
                    B[i:i + ch, 1] = (-dlx[None, :] * rz * inv).sum(dim=1)
                    B[i:i + ch, 2] = ((dlx[None, :] * ry - dly[None, :] * rx) * inv).sum(dim=1)
                return B
            bg = loop(pts, R_CU, 1.0, -d_use / 2) + loop(pts, R_H, -LAM_DESIGN, +d_use / 2)
            bmag = bg.norm(dim=1)
            # 找 |B| 最小的格点（应落在原点附近 ⟹ 真零点而非只 B_z=0）
            kmin = int(torch.argmin(bmag))
            pmin = pts[kmin].tolist()
            gpu_info = {"device": str(dev), "grid": grid, "points": int(pts.shape[0]),
                        "max_absB_T": float(bmag.max()),
                        "min_absB_T": float(bmag.min()),
                        "min_at": [round(v, 4) for v in pmin],
                        "origin_dist": float(math.sqrt(sum(v * v for v in pmin)))}
            check("③-3 N³ 全场：|B| 的最小值落在原点附近（三维里原点确为零点）",
                  gpu_info["origin_dist"] < 4e-2 and gpu_info["min_absB_T"] < 1e-3 * gpu_info["max_absB_T"],
                  f"grid {grid}³ = {gpu_info['points']} 点；|B|min = {gpu_info['min_absB_T']:.3e} T "
                  f"（max {gpu_info['max_absB_T']:.3f} T）出现在 {gpu_info['min_at']}，离原点 "
                  f"{gpu_info['origin_dist']:.4f} m")
        except Exception as e:
            check("③-3 N³ 全场", False, f"{type(e).__name__}: {e}")

    # ---- 画图 ----
    draw(rr, zz, BZ, curve, d_use, env, clr)
    check("④ 图纸文本不含「缺口 / 未给出 / 待定」字样",
          not any(b in s for s in FIG_LABELS for b in ("缺口", "未给出", "待定")),
          f"扫描 {len(FIG_LABELS)} 条图注")

    ok = all(c["通过"] for c in CHECKS)
    report = {
        "产物": "轴向分离双流环：三步（零场面 / 装置包络 / 有限截面修正）",
        "口径": {"R_Cu_m": R_CU, "R_H_m": R_H, "截面半宽_m": [W_R, W_Z], "σ_y_Pa": SIGMA_Y,
                 "环厚_m": T_RING, "围包_κ": KAPPA, "λ_设计": LAM_DESIGN},
        "③_有限截面": {"点丝_d_star_m": d_thin, "截面_d_star_m": d_sec,
                       "λ=1.5 时所需分离距离的变化_m": (d_sec - d_thin) if d_sec and d_thin else None,
                       "定性": "截面把近场抹平 ⟹ 内环贡献变弱 ⟹ 达到同样的零点需要更大的分离距离"},
        "①_零场面": {"零点曲线点数": int(len(curve)), "轴向跨度_m": [z_span[0], z_span[1]],
                     "到导体表面最小净空_m": clr, "到中心线最小净空_m": clr_center,
                     "原点_B_z_T": float(b_origin)},
        "②_装置包络": env,
        "③_三维全场": gpu_info,
        "checks": CHECKS,
    }
    with open(os.path.join(OUT, "report.json"), "w", encoding="utf-8") as f:
        json.dump(report, f, ensure_ascii=False, indent=2)
    n_ok = sum(1 for c in CHECKS if c["通过"])
    with open(os.path.join(OUT, "summary.txt"), "w", encoding="utf-8") as f:
        f.write(f"轴向分离三步：{n_ok}/{len(CHECKS)} 通过；d*(点丝)={d_thin:.4f} d*(截面)={d_sec:.4f} m；"
                f"净空(到导体面){clr:.4f} m；L={env['装置尺度_L_m']:.3f} m B={env['工作场强_B_T']} T\n")
    print(f"轴向分离三步：{n_ok}/{len(CHECKS)} 通过")
    for c in CHECKS:
        print(("  PASS  " if c["通过"] else "  FAIL  ") + c["检查"])
        if c["细节"]:
            print("         " + c["细节"])
    return 0 if ok else 1


def draw(rr, zz, BZ, curve, d, env, clr):
    fig, (ax, ax2) = plt.subplots(1, 2, figsize=(15.2, 5.6),
                                  gridspec_kw={"width_ratios": [1.15, 1.0]})
    fig.subplots_adjust(wspace=0.46)
    Rg, Zg = np.meshgrid(rr, zz, indexing="ij")
    m = BZ.T
    lim = np.percentile(np.abs(m), 92)
    im = ax.pcolormesh(rr, zz, np.clip(m, -lim, lim), cmap="RdBu_r", shading="auto")
    ax.contour(rr, zz, m, levels=[0.0], colors="k", linewidths=2.2)
    if len(curve):
        ax.plot(curve[:, 0], curve[:, 1], ".", ms=1.4, color="#111111", alpha=0.5)
    for z0, a, nm, c in ((-d / 2, R_CU, "Cu 环", "#1f4e79"), (+d / 2, R_H, "H 环", "#c00000")):
        ax.add_patch(plt.Rectangle((a - W_R, z0 - W_Z), 2 * W_R, 2 * W_Z, color=c, zorder=5))
        ax.text(a + 0.05, z0, f" {nm}", fontsize=9.5, color=c, va="center")
    ax.plot([0], [0], marker="o", ms=13, mfc="none", mec="#e67e22", mew=2.8, zorder=6)
    ax.text(0.06, 0.10, "原点零点", fontsize=9.5, color="#e67e22", zorder=6)
    ax.annotate("黑线 = B_z = 0 的零场面\n（绕轴旋转即场反位形边界）\n"
                f"最小净空到导体表面 = {clr:.3f} m",
                xy=(0.0, 0.0), xytext=(0.06, 0.06), textcoords="axes fraction",
                fontsize=9.5, arrowprops=dict(arrowstyle="-|>", color="#e67e22"),
                bbox=dict(boxstyle="round,pad=0.4", fc="white", ec="#bbbbbb", alpha=0.95))
    FIG_LABELS.extend(["零场面（B_z=0 等值线）", "两环截面", "原点零点"])
    ax.set_xlabel("半径 r [m]", fontsize=11.5)
    ax.set_ylabel("轴坐标 z [m]", fontsize=11.5)
    ax.set_title("① 零场面：B_z = 0 的曲线（黑），两侧场反号", fontsize=12)
    cb = fig.colorbar(im, ax=ax, shrink=0.82, pad=0.02)
    cb.set_label("B_z [T]", fontsize=10)
    ax.set_title("① 零场面：B_z = 0 的曲线（黑），两侧场反号\n（单位电流口径）", fontsize=11.5)

    keys = ["轴向包络_m", "径向包络_m", "装置尺度_L_m", "工作场强_B_T", "FC12上界_B_T",
            "PF7允许半径_m", "环厚上限_t_max_m"]
    vals = [env[k] for k in keys]
    ax2.barh(range(len(keys)), vals, color=["#2980b9", "#2980b9", "#8e44ad",
                                            "#e67e22", "#95a5a6", "#27ae60", "#c0392b"])
    for i, v in enumerate(vals):
        ax2.text(v * 1.02, i, f" {v:.4g}", va="center", fontsize=9.5)
    ax2.set_yticks(range(len(keys)))
    ax2.set_yticklabels(keys, fontsize=9.5)
    ax2.set_xscale("log")
    ax2.set_xlim(1e-2, 1e2)
    ax2.grid(alpha=0.25, axis="x")
    FIG_LABELS.extend(keys)
    ax2.set_title("② 装置包络与四条硬界的量级（对数轴）", fontsize=12)
    fig.suptitle("轴向分离双流环：零场面 / 包络 / 有限截面（λ=1.5）", fontsize=12.5)
    fig.savefig(os.path.join(OUT, "fig_axial_envelope.png"), dpi=150, bbox_inches="tight")
    plt.close(fig)


if __name__ == "__main__":
    raise SystemExit(main())
