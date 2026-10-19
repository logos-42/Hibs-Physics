#!/usr/bin/env python3
"""双流环 —— **GPU 三维版**（与笔记本版 scripts/sim_two_flow_ring.py 同一物理，独立实现）

跑在远端 A100 上（torch + CUDA）。三件事：

  G1  三维全场：把两条反向环流的 Biot–Savart 场算到三维网格上（分块累加，显存安全）
      · 轴上值与解析式 (μ₀I_Cu/2)(1/R_Cu − λ/R_H) 对位
      · PA3 叠加线性 B(C1+C2) = B(C1)+B(C2)
      · ★ **中性点半径 r***：中平面上 B_z 变号的位置 —— 场反位形判据 λ > R_H/R_Cu 的**三维版**
        （笔记本版只在轴上验过；这里在全场里定位它）
  G2  流元捕获：10⁶ 个流元，RK4，切向运动 + **_参量化**的径向项 ξ**（DR4/AMC7 说 ξ=0）
      · 径向漂移随 dt 的收敛阶（RK4 应 ~dt⁴，比笔记本版的一阶 Euler 严格得多）
      · ★ **捕获率(ξ, N)** 反解出**容差**：要 N 步内 99% 捕获，ξ 必须小于多少 —— 一个器件级数字
  G3  交叉核对与提速：同一场公式，GPU 与笔记本实现逐点比；记录墙钟与显存

诚实边界（写死在 report.json）
  · 场用**标准电磁学**的电流环（结构对应层）；本框架要求的是 PA3 线性叠加与 DR2b 反向抵消
  · ξ 是**参量化**的破坏项，不是新物理：DR4/AMC7 主张 ξ=0，本作业量的是「ξ 能容忍多大」
  · 不涉及 μ 的主动产生（仍是档 3）

场有两条实现（--field，默认 auto；低成本路线，leo 2026-10-19）：
  sum     分段 Biot–Savart 直接求和 O(N*nseg)（GPU 友好，原实现）
  closed  圆环场**椭圆积分闭式** O(N)（scipy，CPU/float64 求值后回填设备；
          nseg 离散化参数整个消失；轴上即解析式、机器精度）
  auto    有 scipy 用 closed，否则回落 sum（远端容器缺 scipy 时自动降级，report 如实登记）
配套：捕获率也有解析闭式（径向方程恒等 rdot = xi ⟹ r(t) = r0 + xi*t 精确），G2c 把两者对挂；
判决量全闭式版见 scripts/calc_fusion_gravity_lowcost.py（15 断言，零 GPU）。

用法：
  python3 twoflowring_gpu.py                 # 正式（需 CUDA；auto 场模式）
  python3 twoflowring_gpu.py --smoke         # 冒烟（CPU 也能跑，尺寸极小，只验逻辑与断言链）
  python3 twoflowring_gpu.py --field closed  # 强制闭式场（mps/full 档重活从 96.63 s 到秒级）
"""
import argparse
import json
import math
import os
import time

import torch

try:                                    # 闭式场需要 scipy；远端容器可能没有（同 matplotlib 缺失）
    import numpy as np
    from scipy.special import ellipe, ellipk
    _HAVE_SCIPY = True
except Exception:                       # pragma: no cover - 环境相关
    _HAVE_SCIPY = False

FIELD_MODE = "sum"                      # 由 main() 按 --field {auto,closed,sum} 设定

MU0 = 4e-7 * math.pi
R_CU, R_H = 0.60, 0.35          # 外/内环半径 [m]
I_CU = 1.0e6                    # 外环电流 [A]
LAM_CRIT = R_H / R_CU           # 场反位形判据（解析）


def loop_field_closed_np(pts_np, radius, current):
    """圆环场**椭圆积分闭式**（标准电磁学；numpy/scipy，CPU/float64，O(N)）。

    m = k^2 = 4a*rho/((a+rho)^2+z^2) <= 1（AM-GM，等号仅在丝上，奇异性正确保留）：
      B_z = mu0*I/(2*pi*sqrt((a+rho)^2+z^2)) * [K(m) + (a^2-rho^2-z^2)/((a-rho)^2+z^2)*E(m)]
      B_rho = mu0*I*z/(2*pi*rho*sqrt((a+rho)^2+z^2)) * [-K(m) + (a^2+rho^2+z^2)/((a-rho)^2+z^2)*E(m)]
    自检：轴上 ⟹ mu0*I*a^2/(2*(a^2+z^2)^1.5)；z=0 ⟹ B_rho=0（对称性）。
    """
    x, y, z = pts_np[:, 0], pts_np[:, 1], pts_np[:, 2]
    rho = np.hypot(x, y)
    den = (radius + rho) ** 2 + z ** 2
    sq = np.sqrt(den)
    m = np.clip(4.0 * radius * rho / den, 0.0, 1.0 - 1e-16)
    K, E = ellipk(m), ellipe(m)
    d2 = (radius - rho) ** 2 + z ** 2
    Bz = (MU0 * current / (2.0 * math.pi * sq)
          * (K + (radius * radius - rho * rho - z * z) / d2 * E))
    Brho = np.zeros_like(rho)
    nz = z != 0.0
    rho_safe = np.where(rho > 0.0, rho, 1.0)          # 轴上 B_rho 恒 0，避开 1/rho
    Brho[nz] = (MU0 * current * z[nz] / (2.0 * math.pi * rho_safe[nz] * sq[nz])
                * (-K[nz] + (radius * radius + rho[nz] ** 2 + z[nz] ** 2) / d2[nz] * E[nz]))
    dirx = np.where(rho > 0.0, x / rho_safe, 0.0)
    diry = np.where(rho > 0.0, y / rho_safe, 0.0)
    return np.stack([Brho * dirx, Brho * diry, Bz], axis=1)


def loop_field(points, radius, current, nseg, chunk=None, field_mode=None):
    """共面/三维点上的环电流 Biot–Savart 场（分块累加，显存安全）。
    points: (N,3) float32/float64 on device。返回 (N,3)。
    field_mode=None 用全局 FIELD_MODE；"closed" 走椭圆积分闭式（O(N)、无 nseg）。"""
    if (field_mode or FIELD_MODE) == "closed":
        if not _HAVE_SCIPY:
            raise RuntimeError("--field closed 需要 scipy（当前环境没有）")
        out_np = loop_field_closed_np(points.detach().cpu().numpy().astype(np.float64),
                                      radius, current)
        return torch.tensor(out_np, device=points.device, dtype=points.dtype)
    dev, dt = points.device, points.dtype
    if chunk is None:                      # 自适应：每块临时张量 ~4e7 元素（float32 ≈ 160 MB/个）
        chunk = max(1024, min(200_000, 40_000_000 // max(nseg, 1)))
    phi = torch.arange(nseg, device=dev, dtype=dt) * (2 * math.pi / nseg)
    cx, cy = radius * torch.cos(phi), radius * torch.sin(phi)
    cz = torch.zeros_like(cx)
    dlx = -radius * torch.sin(phi) * (2 * math.pi / nseg)
    dly = radius * torch.cos(phi) * (2 * math.pi / nseg)
    c = MU0 * current / (4 * math.pi)
    B = torch.zeros_like(points)
    for i in range(0, points.shape[0], chunk):
        p = points[i:i + chunk]
        rx = p[:, None, 0] - cx[None, :]
        ry = p[:, None, 1] - cy[None, :]
        rz = p[:, None, 2] - cz[None, :]
        inv = c / (rx * rx + ry * ry + rz * rz).clamp_min(1e-12) ** 1.5   # (n, nseg)
        # dl × R 的三个分量，**先对 segment 轴求和**再累加（这就是冒烟抓到的那处）
        #   dl = (dlx, dly, 0), R = (rx, ry, rz)
        #   x: dly·rz       y: −dlx·rz       z: dlx·ry − dly·rx
        B[i:i + chunk, 0] += (dly[None, :] * rz * inv).sum(dim=1)
        B[i:i + chunk, 1] += (-dlx[None, :] * rz * inv).sum(dim=1)
        B[i:i + chunk, 2] += ((dlx[None, :] * ry - dly[None, :] * rx) * inv).sum(dim=1)
    return B


def b_axis_analytic(lam, I_CU=I_CU, R_CU=R_CU, R_H=R_H):
    """轴上 B_z(0) = (μ₀I_Cu/2)(1/R_Cu − λ/R_H)（解析，用于对位）。"""
    return MU0 * I_CU / 2 * (1.0 / R_CU - lam / R_H)


def bz_midplane(rs, lam, nseg):
    """中平面 z=0 上一串半径处的 B_z（两条环叠加）。"""
    pts = torch.stack([rs, torch.zeros_like(rs), torch.zeros_like(rs)], dim=1)
    return (loop_field(pts, R_CU, I_CU, nseg) + loop_field(pts, R_H, -lam * I_CU, nseg))[:, 2]


RING_EPS = 0.03        # 排除环附近的半径窗：点丝模型在环上发散，那是模型的近场，不是物理零点


def midplane_structure(lam, nseg, hi=1.15, n=6000, ring_tol=0.02):
    """中平面 z=0 上 B_z 的全部零点，**按是否落在导体（环）附近分类**。

    为什么必须分类：点丝模型在环上有近场奇异性，单个环的共面 B_z 跨过环本身就会变号
    （场点在环内 vs 环外的 z 分量反号）。所以「落在环附近的零点」是**模型的近场**，
    不是物理中性面；只有落在离导体较远处的零点才是真正的中性面（clean）。
    """
    rs = torch.linspace(1e-4, hi, n, device=DEV, dtype=FDT)
    bz = bz_midplane(rs, lam, nseg)
    sign = torch.sign(bz)
    idx = torch.nonzero(sign[:-1] * sign[1:] < 0).flatten().tolist()
    clean, at_ring = [], []
    for k in idx:
        lo, hi2, vlo = float(rs[k]), float(rs[k + 1]), float(bz[k])
        for _ in range(70):
            mid = 0.5 * (lo + hi2)
            v = float(bz_midplane(torch.tensor([mid], device=DEV, dtype=FDT), lam, nseg)[0])
            if vlo * v <= 0:
                hi2 = mid
            else:
                lo, vlo = mid, v
        z = 0.5 * (lo + hi2)
        (at_ring if min(abs(z - R_H), abs(z - R_CU)) < ring_tol else clean).append(z)
    return {"clean": sorted(clean), "at_ring": sorted(at_ring)}


def push_rk4(n_part, n_steps, dt, omega, xi, seed=0, dev=None, fdt=None):
    """流元推演：切向刚体旋转 + **参量化径向项** ξ·r̂。
    解析上（ξ=0）轨道半径恒定 ⟹ 只剩积分器误差。返回 (径向漂移统计, 捕获率)。"""
    dev = DEV if dev is None else dev
    fdt = FDT if fdt is None else fdt
    g = torch.Generator(device="cpu").manual_seed(seed)
    th = torch.rand(n_part, generator=g, dtype=fdt) * 2 * math.pi
    r0 = R_H + (R_CU - R_H) * torch.rand(n_part, generator=g, dtype=fdt)
    x, y = r0 * torch.cos(th), r0 * torch.sin(th)
    rr0 = torch.hypot(x, y)
    x, y = x.to(dev), y.to(dev)
    rr0 = rr0.to(dev)
    r_thresh = rr0 * 0.05                       # 偏离自身半径 >5% 视为逃逸

    def f(x, y):
        r = torch.hypot(x, y).clamp_min(1e-12)
        vx = -omega * y + xi * (x / r)          # 切向 + ξ·r̂（ξ=0 即 DR4/AMC7 的主张）
        vy = omega * x + xi * (y / r)
        return vx, vy

    for _ in range(n_steps):
        k1x, k1y = f(x, y)
        k2x, k2y = f(x + 0.5 * dt * k1x, y + 0.5 * dt * k1y)
        k3x, k3y = f(x + 0.5 * dt * k2x, y + 0.5 * dt * k2y)
        k4x, k4y = f(x + dt * k3x, y + dt * k3y)
        x = x + dt / 6 * (k1x + 2 * k2x + 2 * k3x + k4x)
        y = y + dt / 6 * (k1y + 2 * k2y + 2 * k3y + k4y)
    rr = torch.hypot(x, y)
    drift = torch.abs(rr - rr0)
    captured = (drift <= r_thresh).float().mean().item()
    return {
        "max_rel_drift": float((drift / rr0).max()),
        "median_rel_drift": float((drift / rr0).median()),
        "captured_fraction": captured,
    }


def capture_analytic(xi_v, t_total, r_lo=R_H, r_hi=R_CU, frac=0.05):
    """捕获率解析闭式：径向方程 rdot = xi 对任意积分器精确 ⟹ r(t) = r0 + xi*t；
    r0 ~ U[r_lo, r_hi] ⟹ 捕获率 = P(r0 >= |xi|*t/frac)，一行算术（无流元、无步进）。"""
    bound = abs(xi_v) * t_total / frac
    return float(min(max((r_hi - max(r_lo, bound)) / (r_hi - r_lo), 0.0), 1.0))


def xi_for_capture(target, t_total, r_lo=R_H, r_hi=R_CU, frac=0.05):
    """把「target 捕获率」反解成 xi 容差（GPU 扫描网格做不到的连续值）。"""
    bound = r_hi - target * (r_hi - r_lo)          # = max(r_lo, |xi|*t/frac)
    return 0.0 if bound < r_lo else bound * frac / t_total


def draw_structure(nseg, lam_hi, lam_lo, st_hi, st_lo, scan, outdir, fname="fig_gpu_structure.png"):
    """中平面场结构（零点按是否落在导体附近分类）+ 捕获率 vs ξ。"""
    import matplotlib
    matplotlib.use("Agg")
    import matplotlib.pyplot as plt
    import matplotlib.font_manager as fm
    for fp in ("/Library/Fonts/Arial Unicode.ttf", "/System/Library/Fonts/STHeiti Light.ttc",
               "/System/Library/Fonts/PingFang.ttc"):
        if os.path.exists(fp):
            fm.fontManager.addfont(fp)
            plt.rcParams["font.sans-serif"] = [fm.FontProperties(fname=fp).get_name()]
            break
    plt.rcParams["axes.unicode_minus"] = False

    fig, (ax, ax2) = plt.subplots(1, 2, figsize=(13.0, 5.4))
    rs = torch.linspace(1e-4, 1.10, 1500, device=torch.device("cpu"), dtype=torch.float64)
    for lam_v, col, lab in ((lam_hi, "#c0392b", f"λ = {lam_hi}（> λ_crit，场反位形）"),
                            (lam_lo, "#2980b9", f"λ = {lam_lo}（< λ_crit，核心未反向）")):
        bz = bz_midplane(rs, lam_v, nseg).cpu().numpy()
        bz = torch.clamp(torch.tensor(bz), -8.0, 8.0).numpy()
        ax.plot(rs.numpy(), bz, lw=2.4, color=col, label=lab)
    ax.axhline(0.0, color="#999999", lw=1.0)
    for R, nm, c in ((R_H, "H 环", "#c0392b"), (R_CU, "Cu 环", "#1f4e79")):
        ax.axvline(R, ls="--", lw=1.4, color=c)
        ax.text(R, 7.2, f" {nm}", fontsize=9.5, color=c)
    for z in st_hi["at_ring"] + st_lo["at_ring"]:
        ax.plot([z], [0], marker="x", ms=9, color="#7f8c8d")
    for z in st_lo["clean"]:
        ax.plot([z], [0], marker="o", ms=10, mfc="none", mec="#e67e22", mew=2.2)
        ax.annotate(f"干净零点 r = {z:.4f} m\n（内层反向环带边界）", xy=(z, 0),
                    xytext=(0.06, -6.9), fontsize=9.5,
                    arrowprops=dict(arrowstyle="-|>", color="#e67e22"),
                    bbox=dict(boxstyle="round,pad=0.35", fc="white", ec="#bbbbbb"))
    ax.annotate("变号落在内环自身上\n（点丝近场奇异性，非物理中性面）\n"
                "→ 共面双环给不出离开导体的中性面",
                xy=(R_H, 0.5), xytext=(0.70, -4.6), fontsize=9.5,
                arrowprops=dict(arrowstyle="-|>", color="#7f8c8d"),
                bbox=dict(boxstyle="round,pad=0.4", fc="white", ec="#bbbbbb"))
    ax.set_xlabel("半径 r [m]", fontsize=11.5)
    ax.set_ylabel("中平面轴向场 B_z [T]（截断 ±8）", fontsize=11.5)
    ax.set_title("中平面场结构：两类零点必须分开看", fontsize=12)
    ax.grid(alpha=0.25)
    ax.legend(fontsize=9.5, loc="upper right")

    ks = sorted(scan.keys())
    pos = [max(k, 3e-5) for k in ks]          # ξ=0 无法落在对数轴上：画在左端并单独标注
    ax2.semilogx(pos, [scan[k] for k in ks], "o-", lw=2.2, color="#27ae60")
    ax2.axhline(0.99, ls="--", lw=1.6, color="#c0392b")
    if ks and ks[0] == 0.0:
        ax2.annotate("ξ = 0（DR4/AMC7 的主张值）\n捕获率 1.0000", xy=(pos[0], scan[0.0]),
                     xytext=(1.2e-4, 0.72), fontsize=9.5,
                     arrowprops=dict(arrowstyle="-|>", color="#27ae60"),
                     bbox=dict(boxstyle="round,pad=0.35", fc="white", ec="#bbbbbb"))
    ax2.text(4e-5, 0.955, "99% 捕获线", fontsize=9.5, color="#c0392b")
    ax2.set_xlabel("径向破坏项强度 ξ（对数轴；ξ = 0 画在左端）", fontsize=11.5)
    ax2.set_ylabel("捕获率", fontsize=11.5)
    ax2.set_ylim(-0.05, 1.05)
    ax2.grid(alpha=0.25)
    ax2.set_title("捕获率 vs ξ：反解出器件容差", fontsize=12)
    fig.suptitle("双流环 GPU 运行（本机 MPS / 远端 A100 同一脚本）", fontsize=12.5)
    fig.savefig(os.path.join(outdir, fname), dpi=150, bbox_inches="tight")
    plt.close(fig)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--smoke", action="store_true", help="极小尺寸（CPU 也能跑）")
    ap.add_argument("--device", default="auto", choices=["auto", "cuda", "mps", "cpu"])
    ap.add_argument("--scale", default="smoke", choices=["auto", "smoke", "mps", "full"],
                    help="裸跑默认 smoke（快，可进门禁）；正式跑显式给 mps/full")
    ap.add_argument("--field", default="auto", choices=["auto", "closed", "sum"],
                    help="场实现：closed=椭圆积分闭式(O(N)，无 nseg) / sum=直接求和(O(N*nseg))"
                         " / auto=有 scipy 用 closed 否则 sum")
    a = ap.parse_args()
    global DEV, FDT, FIELD_MODE
    FIELD_MODE = "closed" if (a.field == "auto" and _HAVE_SCIPY) or a.field == "closed" else "sum"
    if a.field == "closed" and not _HAVE_SCIPY:
        raise SystemExit("--field closed 需要 scipy，当前环境没有；用 --field sum 或 auto")
    scale0 = "smoke" if a.smoke else a.scale
    dev = a.device
    if dev == "auto":
        if scale0 == "smoke":
            dev = "cpu"            # smoke 的意义是快+可移植；MPS 上小 kernel 启动开销反而慢 ~50×（实测 51 s vs ~1 s）
        else:
            dev = ("cuda" if torch.cuda.is_available()
                   else "mps" if getattr(torch.backends, "mps", None) and torch.backends.mps.is_available()
                   else "cpu")
    DEV = torch.device(dev)
    # Metal 不支持 float64 ⟹ MPS 上用 float32（精度敏感的收敛阶测试另钉在 CPU/float64）
    FDT = torch.float64 if DEV.type in ("cuda", "cpu") else torch.float32
    scale = scale0
    if scale == "auto":
        scale = "smoke" if DEV.type == "cpu" else ("mps" if DEV.type == "mps" else "full")
    SC = {"smoke": dict(nseg=64, ngrid=3, npart=2000, nsteps=200),
          "mps":   dict(nseg=512, ngrid=48, npart=200_000, nsteps=1200),
          "full":  dict(nseg=2048, ngrid=96, npart=1_000_000, nsteps=4000)}[scale]
    nseg, ngrid, npart, nsteps = SC["nseg"], SC["ngrid"], SC["npart"], SC["nsteps"]
    cfg = {"规模档": scale, "nseg": nseg, "ngrid": ngrid, "npart": npart, "nsteps": nsteps,
           "场模式": FIELD_MODE}
    # 产物目录：在仓库里跑（脚本在 scripts/）→ artifacts/twoflowring_gpu/；在远端作业目录里跑 → 就地
    here = os.path.dirname(os.path.abspath(__file__))
    in_repo = os.path.basename(here) == "scripts"
    outdir = os.path.join(os.path.dirname(here), "artifacts", "twoflowring_gpu") if in_repo else here
    os.makedirs(outdir, exist_ok=True)
    TAG = "" if scale != "smoke" else "_smoke"      # smoke 档不覆盖正式 GPU 跑的产物

    t0 = time.time()
    out = {"设备": str(DEV), "精度": str(FDT).replace("torch.", ""), "配置": cfg, "断言": []}

    def chk(name, cond, detail=""):
        out["断言"].append({"检查": name, "通过": bool(cond), "细节": str(detail)})

    if DEV.type == "cuda":
        out["GPU"] = torch.cuda.get_device_name(0)
        out["显存_GB"] = round(torch.cuda.get_device_properties(0).total_memory / 1e9, 1)

    lam = 1.5
    # ---------- G1 三维场 ----------
    # 1) 轴上对位
    pts = torch.zeros((1, 3), device=DEV, dtype=torch.float32)
    b_num = float((loop_field(pts, R_CU, I_CU, nseg)
                   + loop_field(pts, R_H, -lam * I_CU, nseg))[0, 2])
    b_ana = b_axis_analytic(lam)
    chk("G1 轴上 B_z(0) 数值 = 解析 (μ₀I_Cu/2)(1/R_Cu − λ/R_H)",
        abs(b_num - b_ana) / abs(b_ana) < 2e-3,
        f"数值 {b_num:.6e} T vs 解析 {b_ana:.6e} T（相对差 {abs(b_num - b_ana) / abs(b_ana):.2e}）")

    # 2) PA3 线性
    p_test = torch.rand((500, 3), device=DEV, dtype=torch.float32) - 0.5
    B1 = loop_field(p_test, R_CU, I_CU, nseg)
    B2 = loop_field(p_test, R_H, -lam * I_CU, nseg)
    B12 = loop_field(p_test, R_CU, I_CU, nseg) + loop_field(p_test, R_H, -lam * I_CU, nseg)
    lin = float((B12 - (B1 + B2)).abs().max())
    chk("G1b PA3 叠加线性 B(C1+C2)=B(C1)+B(C2)（三维、机器精度）", lin < 1e-6,
        f"max|残差| = {lin:.2e}")

    # 3) 中性点半径（三维版判据）
    st_hi = midplane_structure(lam, nseg)
    out["中平面_lam1.5"] = st_hi
    out["轴上_Bz0_lam1.5"] = b_num
    chk("G1c 场反位形（λ>λ_crit）：轴上 B_z(0) < 0 且**除导体处外没有其它中性面**（核心整体反向）",
        b_num < 0 and st_hi["clean"] == [],
        f"B_z(0) = {b_num:.4f} T < 0；离导体较远的零点 {st_hi['clean']}；"
        f"落在导体附近的 {[round(z, 4) for z in st_hi['at_ring']]}")

    lam_lo = 0.40
    st_lo = midplane_structure(lam_lo, nseg)
    b_lo = float(bz_midplane(torch.tensor([0.0], device=DEV, dtype=FDT), lam_lo, nseg)[0])
    out["中平面_lam0.4"] = st_lo
    out["轴上_Bz0_lam0.4"] = b_lo
    out["内层环带边界_lam0.4_m"] = st_lo["clean"][0] if st_lo["clean"] else None
    chk("G1d 判据可判死：λ<λ_crit 时轴上不反向，但出现**一个干净的内层零点**（可测量的中间量）",
        b_lo > 0 and len(st_lo["clean"]) == 1 and st_lo["clean"][0] < R_H - 0.05,
        f"λ={lam_lo} < λ_crit={LAM_CRIT:.4f} ⟹ B_z(0) = {b_lo:.4f} T > 0（核心未反向）；"
        f"内层反向环带边界 r = {out['内层环带边界_lam0.4_m']:.6f} m（离两环都 >0.05 m ⟹ 非奇异性伪影）")

    chk("G1e ★共面模型的极限：λ>λ_crit 时变号点被内环自身的近场吃掉 ⟹ 中性面无法离开导体",
        len(st_hi["at_ring"]) >= 1 and abs(st_hi["at_ring"][0] - R_H) < 0.01,
        f"变号点 = {[round(z, 5) for z in st_hi['at_ring'][:2]]}（内环 R_H={R_H}）；"
        "⟹ 要真正的中性面（离开导体）必须让两环**轴向分离**，共面不行 —— 这是本作业的"
        "设计结论，笔记本版只验轴上、看不到这一点")

    # 4) 三维网格化的场（后续插值/可视化用；验尺寸与有限性）
    if DEV.type == "cuda":
        ax = torch.linspace(-1.20, 1.20, ngrid, device=DEV)
        X, Y, Z = torch.meshgrid(ax, ax, ax, indexing="ij")
        gpts = torch.stack([X.flatten(), Y.flatten(), Z.flatten()], dim=1)
        Bg = loop_field(gpts, R_CU, I_CU, nseg) + loop_field(gpts, R_H, -lam * I_CU, nseg)
        chk("G1e 三维网格全场有限且非零",
            bool(torch.isfinite(Bg).all()) and float(Bg.abs().max()) > 0,
            f"网格 {ngrid}³ = {Bg.shape[0]} 点，max|B| = {float(Bg.abs().max()):.3e} T")
        del Bg, gpts, X, Y, Z
        torch.cuda.empty_cache()

    # ---------- G2 流元捕获 ----------
    omega = 2.0
    xi = 0.0
    # 收敛阶要在 float64 + 足够大的 dt 下量（float32/小 dt 时量到的是舍入，不是截断误差）
    # 收敛阶：float64 + 三档 dt（同总时长）。dt 越小越接近渐近阶 4。
    # 精度敏感 ⟹ 固定 CPU + float64（与设备无关地量「积分器阶」，MPS 的 float32 量不到）
    d = {}
    npart_order = min(npart, 20_000)
    for k, dt_v in enumerate((0.4, 0.2, 0.1)):
        d[dt_v] = push_rk4(npart_order, (nsteps // 20) * (2 ** k), dt_v, omega, xi,
                           seed=1, dev=torch.device("cpu"), fdt=torch.float64)
    order = math.log(d[0.4]["max_rel_drift"] / max(d[0.2]["max_rel_drift"], 1e-300)) / math.log(2)
    order2 = math.log(d[0.2]["max_rel_drift"] / max(d[0.1]["max_rel_drift"], 1e-300)) / math.log(2)
    out["测得收敛阶"] = [round(order, 2), round(order2, 2)]
    chk("G2 DR4/AMC7：ξ=0 时径向漂移纯为积分器误差（RK4 测得阶 → 4）且捕获率 = 1",
        3.0 < order2 < 6.5 and d[0.1]["captured_fraction"] > 0.999,
        f"测得阶（dt 0.4/0.2/0.1，CPU/float64，n={npart_order}）= {order:.2f} / {order2:.2f}（RK4 渐近 4；粗 dt 偏高）；"
        f"ξ=0 捕获率 {d[0.1]['captured_fraction']:.6f}，最大相对漂移 {d[0.1]['max_rel_drift']:.2e}")

    # 容差反解：要 99% 捕获，ξ 能有多大（扫 ξ）
    scan = {}
    for xi_v in (0.0, 1e-4, 1e-3, 1e-2, 1e-1):
        r = push_rk4(max(npart // 20, 1000) if a.smoke else npart // 4,
                     max(nsteps // 20, 50) if a.smoke else nsteps // 4, 0.01, omega, xi_v, seed=2)
        scan[xi_v] = r["captured_fraction"]
    out["捕获率_vs_xi"] = scan
    xi_ok = [k for k, v in scan.items() if v >= 0.99]
    out["容差_xi_max_99pct"] = max(xi_ok) if xi_ok else None
    chk("G2b 捕获率随 ξ 单调下降 ⟹ 反解出容差（器件级数字）",
        scan[0.0] >= 0.99 and scan[0.1] < scan[0.0],
        f"ξ=0 捕获率 {scan[0.0]:.4f}；ξ=0.1 掉到 {scan[0.1]:.4f}；"
        f"99% 捕获可容忍 ξ ≤ {out['容差_xi_max_99pct']}")
    # 解析闭式对挂（ṙ=ξ 精确 ⟹ r(t)=r₀+ξt）：RK4 实测 vs 一行算术
    t_total = 0.01 * (max(nsteps // 20, 50) if a.smoke else nsteps // 4)
    n_scan = max(npart // 20, 1000) if a.smoke else npart // 4
    scan_closed = {xi_v: capture_analytic(xi_v, t_total) for xi_v in scan}
    out["捕获率_vs_xi_解析"] = scan_closed
    out["容差_xi_99pct_解析"] = xi_for_capture(0.99, t_total)
    tol_s = 3.0 / math.sqrt(n_scan)
    xi99 = xi_for_capture(0.99, t_total)
    chk("G2c 捕获率解析闭式与 RK4 实测一致（ṙ=ξ 精确 ⟹ r(t)=r₀+ξt；差 ≤ 3/√n 采样误差）",
        all(abs(scan[xi_v] - scan_closed[xi_v]) <= max(tol_s, 5e-3) for xi_v in scan),
        "；".join(f"ξ={xi_v:g}→RK4 {scan[xi_v]:.4f}/闭式 {scan_closed[xi_v]:.4f}" for xi_v in scan)
        + f"（n={n_scan}，容差 {tol_s:.4f}）；★99% 捕获的**连续**容差 ξ_99 = {xi99:.6f}"
        f"（扫描网格只报到 {out['容差_xi_max_99pct']}，闭式细 "
        f"{xi99 / max(out['容差_xi_max_99pct'] or 1e-300, 1e-300):.1f}×）")

    # ---------- G3 交叉核对 + 计时 ----------
    # sum 模式：同一公式的两条实现（CPU 路径 vs GPU 路径）逐点对位（原口径）
    # closed 模式：两条**独立**实现对挂 —— 椭圆积分闭式 vs 分段直接求和
    #   （与 calc_fusion_gravity_lowcost.py 的 D6d/D7 同口径；nseg 参考值取大以排除离散化）
    pts_cpu = torch.tensor([[0.0, 0.0, 0.0], [0.30, 0.0, 0.0], [0.80, 0.0, 0.0]], dtype=torch.float32)
    if FIELD_MODE == "closed":
        nseg_ref = max(nseg, 512)
        b_cpu = (loop_field(pts_cpu, R_CU, I_CU, nseg_ref, field_mode="sum")
                 + loop_field(pts_cpu, R_H, -lam * I_CU, nseg_ref, field_mode="sum"))
        b_gpu = (loop_field(pts_cpu.to(DEV), R_CU, I_CU, nseg, field_mode="closed")
                 + loop_field(pts_cpu.to(DEV), R_H, -lam * I_CU, nseg, field_mode="closed")).cpu()
        g3_name = f"G3 闭式 vs 直接求和（nseg={nseg_ref}）逐点一致 —— 两条独立实现对挂"
        g3_tol = 1e-4
    else:
        b_cpu = (loop_field(pts_cpu, R_CU, I_CU, nseg) + loop_field(pts_cpu, R_H, -lam * I_CU, nseg))
        b_gpu = (loop_field(pts_cpu.to(DEV), R_CU, I_CU, nseg)
                 + loop_field(pts_cpu.to(DEV), R_H, -lam * I_CU, nseg)).cpu()
        g3_name = "G3 同一公式的两条实现（CPU 路径 vs GPU 路径）逐点一致"
        g3_tol = 1e-6
    cross = float((b_cpu - b_gpu).abs().max())
    chk(g3_name, cross < g3_tol, f"max|差| = {cross:.2e}（阈值 {g3_tol:g}）")

    try:
        fname = f"fig_gpu_structure{TAG}.png"
        draw_structure(nseg, lam, lam_lo, st_hi, st_lo, scan, outdir, fname)
        out["图"] = fname
    except Exception as e:                      # 出图失败不影响断言判定，但如实登记
        out["图_失败"] = f"{type(e).__name__}: {e}"

    out["墙钟_秒"] = round(time.time() - t0, 2)
    ok = all(c["通过"] for c in out["断言"])
    out["全通过"] = ok
    # （产物目录已在 main 开头推导）
    with open(os.path.join(outdir, f"report{TAG}.json"), "w", encoding="utf-8") as fh:
        json.dump(out, fh, ensure_ascii=False, indent=2)
    n_ok = sum(1 for c in out["断言"] if c["通过"])
    with open(os.path.join(outdir, f"summary{TAG}.txt"), "w", encoding="utf-8") as fh:
        fh.write(f"双流环 GPU：{n_ok}/{len(out['断言'])} 通过；设备 {out['设备']}；"
                 f"场模式 {FIELD_MODE}；"
                 f"r*={out.get('中性点半径_r*_m')}；ξ 容差={out.get('容差_xi_max_99pct')}；"
                 f"墙钟 {out['墙钟_秒']}s\n")
    print(f"双流环 GPU：{n_ok}/{len(out['断言'])} 通过 | 设备 {out['设备']} | "
          f"场模式 {FIELD_MODE} | 墙钟 {out['墙钟_秒']}s")
    for c in out["断言"]:
        print(("  PASS  " if c["通过"] else "  FAIL  ") + c["检查"])
        if c["细节"]:
            print("         " + c["细节"])
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
