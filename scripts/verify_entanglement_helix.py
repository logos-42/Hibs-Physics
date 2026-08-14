#!/usr/bin/env python3
"""双螺旋纠缠模型的贝尔检验（流动空间假设）

模型（leo, 2026-08-14）：
  光子 = 完全随空间流动（SLS2, dτ=0）：世界线 = 空间流动线。
  纠缠光子对 = 同一流动管内的双螺旋：
    光子 1（相位 λ）  在检偏角 a 的结果  A(λ,a) = sign(cos 2(λ−a))
    光子 2（相位 λ+π）在检偏角 b 的结果  B(λ,b) = −sign(cos 2(λ−b))  （反相）
    λ ~ Uniform[0, π)   （螺旋相位均匀，周期 π）

检验内容：
  1. E(Δ) 关联曲线：螺旋（线性 −1+4Δ/π）vs 量子（−cos 2Δ）
  2. CHSH：S_螺旋 = 2.0（饱和局域界）vs S_量子 = 2√2 ≈ 2.828
  3. 蒙特卡洛贝尔实验（随机设置 + 有限样本误差）
  4. 流旋转不变性：相位被流动旋转 δ 后 S 仍 ≤ 2（CHSH 定理的数值确认）
  5. 量子统计读出（Born 规则，流携带联合单态）：S = 2.828 ——
     同样的双螺旋几何，换读出规则即达量子界

诚实边界：
  - 本脚本是数值模拟，不是实验；结论以 CHSH 定理（Lean 已证，
    Explorations/EntanglementHelix.lean EH2）+ 已知实验为准。
  - sign(cos) 模型的 E(Δ) 解析为 −1+4Δ/π（Δ∈[0,π/2]），本脚本同时
    用解析式与蒙特卡洛两种方式给出，互相验证。
"""
import json
import os
from datetime import date

import numpy as np
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
import matplotlib.font_manager as fm

# macOS CJK 字体（图内中文标题）
for _fp in ("/System/Library/Fonts/PingFang.ttc",
            "/System/Library/Fonts/Hiragino Sans GB.ttc"):
    if os.path.exists(_fp):
        fm.fontManager.addfont(_fp)
        plt.rcParams["font.sans-serif"] = [fm.FontProperties(fname=_fp).get_name()]
        break
plt.rcParams["axes.unicode_minus"] = False

OUT = os.path.join(os.path.dirname(__file__), "..", "artifacts", "entanglement")
os.makedirs(OUT, exist_ok=True)

PI = np.pi
RNG = np.random.default_rng(20260814)


# ---------- 模型 ----------

def A_helix(lam, a):
    """光子 1：相位 λ 在检偏角 a 的 ±1 结果（Malus 型确定性读出）。"""
    return np.sign(np.cos(2.0 * (lam - a)))


def B_helix(lam, b):
    """光子 2：反相股（相位 λ+π ⟹ 结果符号相反）。"""
    return -np.sign(np.cos(2.0 * (lam - b)))


def E_helix_mc(a, b, n=2_000_000):
    """双螺旋模型的关联函数（蒙特卡洛）。"""
    lam = RNG.uniform(0.0, PI, n)
    return float(np.mean(A_helix(lam, a) * B_helix(lam, b)))


def E_helix_analytic(delta):
    """双螺旋模型 E(Δ) 解析式：−1 + 4Δ/π（Δ∈[0, π/2]）。"""
    return -1.0 + 4.0 * delta / PI


def E_quantum(a, b):
    """量子力学单态预言：E(a,b) = −cos 2(a−b)。"""
    return -np.cos(2.0 * (a - b))


def chsh(E):
    """从关联函数算 CHSH 值（标准角度 a=0, a'=π/4, b=π/8, b'=3π/8）。"""
    a, a2 = 0.0, PI / 4
    b, b2 = PI / 8, 3 * PI / 8
    return E(a, b) - E(a, b2) + E(a2, b) + E(a2, b2)


# ---------- 1. E(Δ) 曲线 ----------

def e_curve():
    deltas = np.linspace(0.0, PI / 2, 129)
    e_q = -np.cos(2.0 * deltas)
    e_h = E_helix_analytic(deltas)
    e_h_mc = np.array([E_helix_mc(d, 0.0, n=400_000) for d in deltas[::8]])
    return deltas, e_q, e_h, e_h_mc


# ---------- 2. 蒙特卡洛贝尔实验 ----------

def bell_experiment(n_events=1_000_000):
    """类真实贝尔实验：每个事件随机选设置，估计 |S|。"""
    a_choices = np.array([0.0, PI / 4])
    b_choices = np.array([PI / 8, 3 * PI / 8])
    lam = RNG.uniform(0.0, PI, n_events)
    a_idx = RNG.integers(0, 2, n_events)
    b_idx = RNG.integers(0, 2, n_events)
    a = a_choices[a_idx]
    b = b_choices[b_idx]
    A = A_helix(lam, a)
    B = B_helix(lam, b)
    prod = A * B
    # S = E(a,b) − E(a,b') + E(a',b) + E(a',b')，系数表 (ai,bi)
    coeff = {(0, 0): +1.0, (0, 1): -1.0, (1, 0): +1.0, (1, 1): +1.0}
    S_est = 0.0
    for ai in (0, 1):
        for bi in (0, 1):
            m = (a_idx == ai) & (b_idx == bi)
            S_est += coeff[(ai, bi)] * prod[m].mean()
    # 统计误差（4 个子集，每项 ~ ±1/√(n/4)）
    err = 4.0 / np.sqrt(n_events / 4.0)
    return float(S_est), float(err)


# ---------- 3. 流旋转不变性 ----------

def flow_rotation_scan():
    """相位被流动旋转 δ（如介质/引力旋转）后 CHSH 值的扫描。"""
    lam = RNG.uniform(0.0, PI, 1_000_000)
    a, a2 = 0.0, PI / 4
    b, b2 = PI / 8, 3 * PI / 8
    results = []
    for delta in np.linspace(0.0, PI, 25):
        A1 = np.sign(np.cos(2.0 * (lam - a)))
        A2 = np.sign(np.cos(2.0 * (lam - a2)))
        B1 = -np.sign(np.cos(2.0 * (lam + delta - b)))
        B2 = -np.sign(np.cos(2.0 * (lam + delta - b2)))
        S = np.mean(A1 * B1) - np.mean(A1 * B2) + np.mean(A2 * B1) + np.mean(A2 * B2)
        results.append(S)
    return np.linspace(0.0, PI, 25), np.array(results)


# ---------- 4. 量子统计读出（同一几何，Born 规则） ----------

def quantum_mc(n=2_000_000):
    """单态 |ψ⟩=(|HV⟩−|VH⟩)/√2 的量子统计：
    P(+,−)=P(−,+)=½cos²(a−b), P(+,+)=P(−,−)=½sin²(a−b)。"""
    a, a2 = 0.0, PI / 4
    b, b2 = PI / 8, 3 * PI / 8
    pairs = [(a, b), (a, b2), (a2, b), (a2, b2)]
    Es = []
    for ai, bi in pairs:
        # P(相同符号) = ½sin²(a−b)·2 = sin²(a−b)；P(相反) = cos²(a−b)
        same = RNG.uniform(0, 1, n) < np.sin(ai - bi) ** 2
        A = np.where(RNG.uniform(0, 1, n) < 0.5, 1.0, -1.0)   # P(A=+1)=½
        B = np.where(same, A, -A)                              # 相同→同号，相反→异号
        Es.append(np.mean(A * B))
    S_q = Es[0] - Es[1] + Es[2] + Es[3]
    return float(S_q), float(np.std(Es))


# ---------- 绘图 ----------

def plot_e_delta(deltas, e_q, e_h, e_h_mc, path):
    fig, ax = plt.subplots(figsize=(8, 5))
    ax.plot(deltas / PI * 180, e_q, "k-", lw=2, label="量子力学 $E=-\\cos 2\\Delta$")
    ax.plot(deltas / PI * 180, e_h, "C0--", lw=2,
            label="双螺旋（经典读出）$E=-1+4\\Delta/\\pi$")
    ax.plot((deltas[::8] / PI * 180)[1:], e_h_mc[1:], "C0o", ms=4,
            label="双螺旋蒙特卡洛")
    for x in (22.5, 67.5):
        ax.axvline(x, color="gray", ls=":", lw=1)
    ax.text(22.5, 0.55, "CHSH 角 π/8", ha="center", fontsize=8, color="gray")
    ax.text(67.5, 0.55, "3π/8", ha="center", fontsize=8, color="gray")
    ax.axhline(0, color="gray", lw=0.8)
    ax.set_xlabel("检偏角差 Δ（度）")
    ax.set_ylabel("关联 E(Δ)")
    ax.set_title("双螺旋纠缠模型 vs 量子力学：关联函数")
    ax.set_ylim(-1.15, 1.15)
    ax.legend(loc="lower left", fontsize=9)
    ax.grid(alpha=0.3)
    fig.tight_layout()
    fig.savefig(path, dpi=150)
    plt.close(fig)


def plot_chsh(s_helix, s_quantum, s_aspect, err_helix, path):
    fig, ax = plt.subplots(figsize=(7.5, 5))
    labels = ["局域界\n(CHSH 定理)", "双螺旋模型\n(蒙特卡洛)", "量子力学\n2√2", "实验\n(Aspect 1982)"]
    vals = [2.0, s_helix, 2.0 * np.sqrt(2), 2.697]
    errs = [0, err_helix, 0, 0.015]
    colors = ["#888888", "#1f77b4", "#2ca02c", "#d62728"]
    ax.bar(labels, vals, yerr=errs, color=colors, capsize=4, alpha=0.85)
    ax.axhline(2.0, color="#888888", ls="--", lw=1)
    ax.axhline(2.0 * np.sqrt(2), color="#2ca02c", ls="--", lw=1)
    ax.set_ylabel("CHSH 值 S")
    ax.set_ylim(0, 3.3)
    ax.set_title("贝尔检验：双螺旋（经典）无法达到量子界")
    for i, v in enumerate(vals):
        ax.text(i, v + 0.06, f"{v:.3f}", ha="center", fontsize=10, fontweight="bold")
    ax.grid(axis="y", alpha=0.3)
    fig.tight_layout()
    fig.savefig(path, dpi=150)
    plt.close(fig)


def plot_flow_rotation(deltas, ss, path):
    fig, ax = plt.subplots(figsize=(7.5, 4.5))
    ax.plot(deltas / PI * 180, ss, "C2o-", ms=4)
    ax.axhline(2.0, color="#888888", ls="--", lw=1, label="局域界 2")
    ax.axhline(2.0 * np.sqrt(2), color="#2ca02c", ls="--", lw=1, label="量子界 2√2")
    ax.set_xlabel("流动相位旋转 δ（度）")
    ax.set_ylabel("CHSH 值 S")
    ax.set_title("流旋转不变性：δ 任意，双螺旋 S ≤ 2（CHSH 定理数值确认）")
    ax.set_ylim(0, 3.2)
    ax.legend()
    ax.grid(alpha=0.3)
    fig.tight_layout()
    fig.savefig(path, dpi=150)
    plt.close(fig)


def plot_heatmap(path):
    aa = np.linspace(0, PI, 91)
    bb = np.linspace(0, PI, 91)
    A, Bv = np.meshgrid(aa, bb, indexing="ij")
    diff = E_helix_analytic(np.abs(A - Bv) % PI) - E_quantum(A, Bv)
    fig, ax = plt.subplots(figsize=(7, 5.5))
    im = ax.pcolormesh(A / PI * 180, Bv / PI * 180, diff, cmap="RdBu_r",
                       vmin=-0.5, vmax=0.5, shading="auto")
    fig.colorbar(im, ax=ax, label="E_螺旋 − E_量子")
    ax.set_xlabel("检偏角 a（度）")
    ax.set_ylabel("检偏角 b（度）")
    ax.set_title("双螺旋与量子关联的差值（只有反关联轴吻合）")
    fig.tight_layout()
    fig.savefig(path, dpi=150)
    plt.close(fig)


# ---------- 主流程 ----------

def main():
    report = {"model": "double-helix in flowing space",
              "date": str(date.today()),
              "results": {}}

    # 1. E(Δ)
    deltas, e_q, e_h, e_h_mc = e_curve()
    plot_e_delta(deltas, e_q, e_h, e_h_mc, os.path.join(OUT, "fig_e_delta.png"))
    # 解析 vs 蒙特卡洛 对照（Δ = π/8, 3π/8）
    check = {}
    for d in (PI / 8, 3 * PI / 8):
        mc = E_helix_mc(d, 0.0)
        an = E_helix_analytic(d)
        qu = E_quantum(d, 0.0)
        check[f"Δ={d/PI*180:.1f}°"] = {"helix_mc": round(mc, 4),
                                        "helix_analytic": round(an, 4),
                                        "quantum": round(qu, 4)}
    report["results"]["E_delta_checks"] = check

    # 2. CHSH（|S|：定理与实验都以绝对值报）
    s_helix = abs(chsh(lambda a, b: E_helix_mc(a, b, n=4_000_000)))
    s_quantum = 2.0 * np.sqrt(2)
    s_helix_err = 4.0 / np.sqrt(4_000_000 / 4.0)
    plot_chsh(s_helix, s_quantum, 2.697, s_helix_err, os.path.join(OUT, "fig_chsh.png"))
    report["results"]["CHSH"] = {
        "helix_model": round(s_helix, 4),
        "helix_err": round(s_helix_err, 4),
        "quantum": round(s_quantum, 4),
        "lhv_bound": 2.0,
        "aspect1982_exp": 2.697,
        "conclusion": "双螺旋模型饱和局域界 2，无法达到量子界 2.828 ⟹ 经典读出被贝尔实验排除"}

    # 3. 贝尔实验蒙特卡洛
    s_bell, err_bell = bell_experiment()
    report["results"]["bell_experiment_mc"] = {
        "S_est": round(s_bell, 4), "err": round(err_bell, 4),
        "within_LHV_bound": bool(abs(s_bell) <= 2.0 + 3 * err_bell)}

    # 4. 流旋转
    deltas_r, ss = flow_rotation_scan()
    plot_flow_rotation(deltas_r, ss, os.path.join(OUT, "fig_flow_rotation.png"))
    report["results"]["flow_rotation"] = {
        "S_max_over_delta": round(float(ss.max()), 4),
        "S_min_over_delta": round(float(ss.min()), 4),
        "conclusion": "流动相位旋转不改变结论：S ≤ 2（局域界）"}

    # 5. 量子统计读出
    s_q, _ = quantum_mc()
    report["results"]["quantum_readout"] = {
        "S_quantum_mc": round(s_q, 4),
        "expectation": round(2.0 * np.sqrt(2), 4),
        "conclusion": "同一双螺旋几何 + Born 规则读出（流携带联合单态）⟹ S = 2√2，与实验一致"}

    # 热图
    plot_heatmap(os.path.join(OUT, "fig_heatmap.png"))

    # 结论
    report["conclusion"] = (
        "双螺旋几何精确给出：① 对齐设置完全反关联 E(0)=−1（与量子一致）；"
        "② 经典相位读出时 E(Δ)=−1+4Δ/π 为线性，CHSH S=2.0 饱和局域界，"
        "被贝尔实验（Aspect 1982: 2.697；2015 无漏洞实验）排除；"
        "③ 达到 2.828 的唯一路径是流携带联合量子态（Born 规则读出），"
        "即纠缠活在流场携带的波函数层面，双螺旋只是真实空间的几何投影。"
        "可检验预言：流动非均匀（引力）⟹ 两股相位差变化 ⟹ E(Δ) 出现引力依赖相移。")
    report["files"] = {
        "e_delta": "fig_e_delta.png", "chsh": "fig_chsh.png",
        "flow_rotation": "fig_flow_rotation.png", "heatmap": "fig_heatmap.png"}

    json_path = os.path.join(OUT, "report.json")
    with open(json_path, "w", encoding="utf-8") as f:
        json.dump(report, f, ensure_ascii=False, indent=2)

    # Markdown 报告
    md = f"""# 双螺旋纠缠模型：贝尔检验报告

> 流动空间假设下：光子 = 完全随空间流动（dτ=0）；纠缠对 = 同一流动管内的双螺旋（两股反相 λ 与 λ+π）。

## 结果

| 检验 | 双螺旋（经典读出） | 量子力学 | 实验 |
|---|---|---|---|
| E(0) 对齐反关联 | −1.000 ✓ | −1.000 ✓ | −1 ✓ |
| E(π/8) | {check['Δ=22.5°']['helix_mc']:.4f} | {check['Δ=22.5°']['quantum']:.4f} | — |
| E(3π/8) | {check['Δ=67.5°']['helix_mc']:.4f} | {check['Δ=67.5°']['quantum']:.4f} | — |
| CHSH S | {s_helix:.3f} ± {s_helix_err:.3f} | {s_quantum:.3f} | 2.697 ± 0.015 (Aspect 1982) |

## 结论（诚实评估）

1. **双螺旋给出"纠缠的一半"**：几何锁相（反相股）⟹ 对齐设置完全反关联，与量子一致。
2. **经典读出无法证明量子纠缠**：E(Δ) 是线性 −1+4Δ/π，CHSH S=2.0 恰好饱和局域界——它是"经典能做到的最像量子"的模型，但仍被贝尔实验（S 实测 2.697–2.828）排除。CHSH 定理（|S|≤2）已在 `ProjectionPhysics/Explorations/EntanglementHelix.lean` 用 Lean 证明（EH2）。
3. **流旋转改变不了结论**：相位被流动旋转任意 δ，S 仍 ≤ 2（数值扫描确认定理）。
4. **要 2.828 必须换读出规则**：同一几何 + Born 规则（流携带联合单态）⟹ S = 2√2 与实验一致。
   ⟹ 纠缠不在螺旋轨迹的几何里，在流场携带的波函数（联合量子态）里；双螺旋 = 纠缠的几何投影，不是机制。

## 可检验预言

空间流动非均匀（引力，仓库主线"引力=流动非均匀"）⟹ 双螺旋两股相位差随路径改变 ⟹ 纠缠关联 E(Δ) 出现引力依赖的相移（对应实验上"引力对纠缠相位的效应"，当前精度未测）。

## 文件

- 模拟: `scripts/verify_entanglement_helix.py`、`scripts/entanglement_helix_3d.py`
- Lean: `ProjectionPhysics/Explorations/EntanglementHelix.lean`（EH1–EH4）
- 图: `artifacts/entanglement/fig_*.png`、`helix_3d.gif`
"""
    with open(os.path.join(OUT, "report.md"), "w", encoding="utf-8") as f:
        f.write(md)

    print(json.dumps(report["results"], ensure_ascii=False, indent=2))
    print("\n→ 产物目录:", os.path.abspath(OUT))


if __name__ == "__main__":
    main()
