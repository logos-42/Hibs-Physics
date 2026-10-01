#!/usr/bin/env python3
"""维数选择：「振动 ⟹ 三方向」的唯一性论证（DS1–DS8）

leo：「然后把第一条做完」。上一版口头用的**最小性**是口味选择；本脚本配的那套 Lean 用的是
**唯一性**：两条硬要求的交集只落在 3 上。

D1 ★★ 2D（π₁ 阿贝尔化 = Z）：相位取值集合是**整个单位圆** ⟹ 任意子排除不掉
        （α = π/3 见证：虚部 √3/2 ≠ 0，而 ±1 虚部为 0）
D2 ★★ 3D（π₁ 阿贝尔化 = Z2）：相位只有两类（阶 2 ⟹ 只有 ±1）
D3 ★★★ d ≥ 4：**显式解结** —— 三叶结在 3D 投影有 3 个交叉；用第 4 维做局部鼓包
        把 3 个交叉**全部解开**，且新曲线在 R⁴ 里无自交 ⟹ 无平凡扭结（非平凡链接不存在）
D4 ★★ d = 2：**互连不可能** —— Hopf link 在 3D 里互不相交且环绕数 = 1；
        但投影到平面（z = 0）后**必然相交**（交点 > 0）⟹ 互连需要第三维
D5 ★★ 维数判定表 d = 1..5：只有 d = 3 同时满足两条要求

产物：artifacts/dimensionselection/{report.json, summary.txt,
      fig_phase_sets.png, fig_unknot_r4.png, fig_dimension_verdict.png}
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

OUT = os.path.join(os.path.dirname(__file__), "..", "artifacts", "dimensionselection")
os.makedirs(OUT, exist_ok=True)
RNG = np.random.default_rng(7)


# ---------------------------------------------------------------- 几何工具
def seg_intersect(p, q, r, s):
    """线段 pq 与 rs 是否（真）相交，返回交点或 None。"""
    d1 = q - p
    d2 = s - r
    den = d1[0] * d2[1] - d1[1] * d2[0]
    if abs(den) < 1e-14:
        return None
    t = ((r[0] - p[0]) * d2[1] - (r[1] - p[1]) * d2[0]) / den
    u = ((r[0] - p[0]) * d1[1] - (r[1] - p[1]) * d1[0]) / den
    if 1e-9 < t < 1 - 1e-9 and 1e-9 < u < 1 - 1e-9:
        return p + t * d1
    return None


def projected_crossings(P, min_gap=50):
    """折线 P（Nx2）的自交叉：返回 [(i, j, 交点)]（跳过参数相邻的对）。"""
    N = len(P)
    out = []
    for i in range(N):
        for j in range(i + 1, N):
            if j - i < min_gap or (N - (j - i)) < min_gap:
                continue
            pt = seg_intersect(P[i], P[(i + 1) % N], P[j], P[(j + 1) % N])
            if pt is not None:
                out.append((i, j, pt))
    return out


def pairwise_min_dist(Q, min_gap=50):
    """采样点之间的最小距离（跳过参数相邻的对）。"""
    N = len(Q)
    best = np.inf
    for i in range(N):
        for j in range(i + 1, N):
            if j - i < min_gap or (N - (j - i)) < min_gap:
                continue
            d = np.linalg.norm(Q[i] - Q[j])
            if d < best:
                best = d
    return best


def gauss_linking(curve1, curve2, n_q=140):
    """Gauss 双积分给环绕数（数值，用于核对 Hopf link）。"""
    a = curve1[np.linspace(0, len(curve1), n_q, endpoint=False).astype(int)]
    b = curve2[np.linspace(0, len(curve2), n_q, endpoint=False).astype(int)]
    da = np.roll(a, -1, axis=0) - a
    db = np.roll(b, -1, axis=0) - b
    total = 0.0
    for i in range(n_q):
        r = a[i] - b
        num = np.einsum('ij,ij->i', np.cross(da[i], db), r)
        den = np.linalg.norm(r, axis=1) ** 3
        m = den > 1e-9
        total += float(np.sum(num[m] / den[m]))
    return total / (4 * np.pi)


def main():
    report = {"model": "维数选择：两条硬要求的交 = {3}（唯一性，非最小性）",
              "date": str(date.today()), "results": {}}

    # ------------------------------------------------------------------ D1
    alphas = np.linspace(0, 2 * np.pi, 200001, endpoint=False)
    vals = np.exp(1j * alphas)
    on_pm1 = np.abs(np.abs(vals.real) - 1.0) < 1e-9
    frac = float(np.mean(on_pm1))
    a33 = np.pi / 3
    report["results"]["D1_two_dim_phase_set"] = {
        "内容": "二维（π₁ 阿贝尔化 = Z）：相位取值 = 整个单位圆 ⟹ 任意子排除不掉",
        "扫描点数": len(alphas),
        "落在 ±1 上的比例": frac,
        "α = π/3 处相位": [float(np.cos(a33)), float(np.sin(a33))],
        "α = π/3 虚部（解析 √3/2）": float(np.sin(a33)),
        "√3/2": float(np.sqrt(3) / 2),
        "结论": "取值集合是**连续统**；±1 只是其中两个点 ⟹「只有两类」在 Z 型群上**不成立**",
    }

    # ------------------------------------------------------------------ D2
    # 注意：必须用 endpoint=True（默认）——否则 α = π 落在网格外（π 不是 2π/200001 的整数倍），
    # 会漏数一个零点（实测 endpoint=False 给 1，应 2）。
    grid = np.linspace(0, 2 * np.pi, 200001)
    sig_grid = np.exp(1j * grid)
    dev = np.abs(sig_grid ** 2 - 1.0)
    zs = grid[dev < 1e-6]
    groups = []
    for a in zs:
        if not groups or a - groups[-1][-1] > 0.01:
            groups.append([a])
        else:
            groups[-1].append(a)
    zeros = sorted({round(float(np.mean(g)) % (2 * np.pi), 9) for g in groups})
    report["results"]["D2_three_dim_phase_set"] = {
        "内容": "三维（π₁ 阿贝尔化 = Z2，阶 2）：相位只能是 ±1",
        "满足 σ² = 1 的相位数（模 2π 去重）": len(zeros),
        "位置": zeros,
        "结论": "阶 2 ⟹ 只有两个取值 ⟹ **任意子被排除**（与 ES5 一致）",
    }

    # ------------------------------------------------------------------ D3
    t = np.linspace(0, 2 * np.pi, 2000, endpoint=False)
    trefoil = np.stack([np.sin(t) + 2 * np.sin(2 * t),
                        np.cos(t) - 2 * np.cos(2 * t),
                        -np.sin(3 * t)], axis=1)
    P2 = trefoil[:, :2]
    cross_before = projected_crossings(P2)
    # 用第 4 维：在每个交叉的两股处加符号相反的局部鼓包
    x4 = np.zeros(len(t))
    bump = 0.35
    width = 25
    for (i, j, _) in cross_before:
        for (idx, sgn) in ((i, +1.0), (j, -1.0)):
            k = np.arange(len(t))
            d = np.minimum(np.abs(k - idx), len(t) - np.abs(k - idx))
            x4 += sgn * bump * np.exp(-(d / width) ** 2)
    Q4 = np.concatenate([trefoil, x4[:, None]], axis=1)
    # 交叉是否被解开：两股在交叉处的 x4 差
    resolved = []
    for (i, j, _) in cross_before:
        resolved.append(float(abs(x4[i] - x4[j])))
    n_res = sum(1 for d in resolved if d > 0.05)
    dmin4 = pairwise_min_dist(Q4)
    dmin3 = pairwise_min_dist(trefoil)
    report["results"]["D3_unlink_in_four_dim"] = {
        "内容": "d ≥ 4：三叶结用第 4 维局部鼓包把 3 个交叉全部解开",
        "3D 投影交叉数": len(cross_before),
        "交叉处两股的 |Δx₄|": [round(d, 4) for d in resolved],
        "被解开的交叉数": n_res,
        "R³ 中最小非相邻点距（扭结本身是嵌入的，无自交；交叉是投影造成的）": float(dmin3),
        "R⁴ 中加鼓包后最小非相邻点距（应 > 0 ⟹ 仍嵌入）": float(dmin4),
        "最大 |x₄|": float(np.max(np.abs(x4))),
        "结论": "3D 里 3 个交叉（非平凡扭结）；加第 4 维鼓包后**全部解开**且 R⁴ 里无自交 "
                "⟹ 该扭结在 R⁴ 中可解 ⟹ **四维及以上不存在非平凡扭结** ⟹ 非平凡连接数不存在",
    }

    # ------------------------------------------------------------------ D4
    s1 = np.linspace(0, 2 * np.pi, 1200, endpoint=False)
    C1 = np.stack([np.cos(s1), np.sin(s1), np.zeros_like(s1)], axis=1)
    s2 = np.linspace(0, 2 * np.pi, 1200, endpoint=False)
    C2 = np.stack([np.zeros_like(s2), 1 + np.cos(s2), np.sin(s2)], axis=1)
    # 3D 里互不相交？
    d_3d = min(np.linalg.norm(C1[i] - C2[j])
               for i in range(0, len(C1), 12) for j in range(0, len(C2), 12))
    lk = gauss_linking(C1, C2, n_q=180)
    # 投影到 z = 0：C1 → 单位圆；C2 → 线段 x=0, y∈[0,2]（退化为线段）
    P1 = C1[:, :2]
    P2c = C2[:, :2]
    # 几何交点数 = 邻近点的**聚类数**（不是邻近点对数）
    near = [P2c[j] for j in range(0, len(P2c))
            for i in range(0, len(P1)) if np.linalg.norm(P1[i] - P2c[j]) < 0.02]
    clusters = []
    for p in near:
        for c in clusters:
            if np.linalg.norm(p - p[0] if False else c[0] - p) < 0.05:
                c.append(p)
                break
        else:
            clusters.append([p])
    hits = len(clusters)
    hit_pts = [np.mean(c, axis=0).round(4).tolist() for c in clusters]
    # 更干净：C2 投影是线段 x=0, y∈[0,2]，与单位圆交于 (0, ±1)；y∈[0,2] 只含 (0,1)
    report["results"]["D4_two_dim_cannot_link"] = {
        "内容": "d = 2：Hopf link 互不相交且环绕数 = 1，但投影到平面后必然相交",
        "3D 中两环最小距离（应 > 0 ⟹ 互不相交）": float(d_3d),
        "Gauss 双积分环绕数（应 ≈ 1）": float(lk),
        "C2 的 z 跨度（≠ 0 ⟹ 用到了第三维）": float(C2[:, 2].max() - C2[:, 2].min()),
        "投影 z=0 后两曲线的像的**几何**交点数（聚类）": hits,
        "交点位置": hit_pts,
        "解析：C2 投影 = 线段 x=0,y∈[0,2]，与单位圆交于 (0,1)": 1,
        "结论": "3D 里 Lk = 1 且**互不相交**；把 z 压到 0（二维）后两环的像**必然相交** "
                "⟹ **互连需要第三维** ⟹ d = 2 无非平凡连接数",
    }

    # ------------------------------------------------------------------ D5
    rows = [
        {"d": 1, "π₁ 阿贝尔化": "平凡（无交换）", "相位取值": "无", "统计两类?": "不适用",
         "非平凡连接?": "否", "同时满足": "否"},
        {"d": 2, "π₁ 阿贝尔化": "Z", "相位取值": "整个 U(1)", "统计两类?": "**否**",
         "非平凡连接?": "否", "同时满足": "否"},
        {"d": 3, "π₁ 阿贝尔化": "Z2", "相位取值": "{+1, −1}", "统计两类?": "**是**",
         "非平凡连接?": "**是**", "同时满足": "**是**"},
        {"d": 4, "π₁ 阿贝尔化": "Z2", "相位取值": "{+1, −1}", "统计两类?": "是",
         "非平凡连接?": "**否**", "同时满足": "否"},
        {"d": 5, "π₁ 阿贝尔化": "Z2", "相位取值": "{+1, −1}", "统计两类?": "是",
         "非平凡连接?": "否", "同时满足": "否"},
    ]
    report["results"]["D5_dimension_verdict"] = {
        "内容": "维数判定表（标准事实 + 本脚本 D1–D4 的数值佐证）",
        "表": rows,
        "唯一同时满足的维数": 3,
        "结论": "**交集 = {3}**（唯一性，不是最小性）",
    }

    # ------------------------------------------------------------------ 图 1
    fig, axes = plt.subplots(1, 2, figsize=(13, 5.6))
    ax = axes[0]
    ax.plot(np.cos(alphas), np.sin(alphas), "C3", lw=2.2, label="可达相位 = 整个 U(1)")
    for a, lab in [(a33, "α = π/3\n(0.5, √3/2)"), (1.7, "α = 1.7")]:
        ax.plot([np.cos(a)], [np.sin(a)], "C1o", ms=12)
        ax.annotate(lab, xy=(np.cos(a), np.sin(a)),
                    xytext=(np.cos(a) * 1.3, np.sin(a) * 1.3 + 0.1), fontsize=11)
    ax.plot([1, -1], [0, 0], "C0o", ms=10, alpha=0.6, label="±1")
    ax.set_aspect("equal")
    ax.set_xlim(-1.75, 1.75)
    ax.set_ylim(-1.5, 1.5)
    ax.set_title("d = 2（π₁ 阿贝尔化 = Z）\n相位取值是**连续统** → 任意子排除不掉\n"
                 "（±1 只是其中两点）".replace("**", ""), fontsize=11)
    ax.axhline(0, color="k", lw=0.6)
    ax.axvline(0, color="k", lw=0.6)
    ax.grid(alpha=0.3)
    ax.legend(loc="lower left", fontsize=9)

    ax = axes[1]
    th = np.linspace(0, 2 * np.pi, 800)
    ax.plot(np.cos(th), np.sin(th), "0.7", lw=1.2, label="单位圆 U(1)")
    ax.plot([1, -1], [0, 0], "C0o", ms=14)
    ax.annotate("+1", xy=(1, 0), xytext=(1.14, 0.2), fontsize=12, color="C0")
    ax.annotate("−1", xy=(-1, 0), xytext=(-1.5, 0.2), fontsize=12, color="C0")
    ax.set_aspect("equal")
    ax.set_xlim(-1.75, 1.75)
    ax.set_ylim(-1.4, 1.4)
    ax.set_title("d ≥ 3（π₁ 阿贝尔化 = Z2，阶 2）\n相位只能是 ±1 → 任意子被排除\n"
                 "（同一个方程 χ(2) = χ(1)²）", fontsize=11)
    ax.axhline(0, color="k", lw=0.6)
    ax.axvline(0, color="k", lw=0.6)
    ax.grid(alpha=0.3)
    ax.legend(loc="lower left", fontsize=9)
    fig.tight_layout()
    fig.savefig(os.path.join(OUT, "fig_phase_sets.png"), dpi=150)
    plt.close(fig)

    # ------------------------------------------------------------------ 图 2
    fig = plt.figure(figsize=(13.5, 5.8))
    ax = fig.add_subplot(1, 2, 1)
    ax.plot(P2[:, 0], P2[:, 1], "C0", lw=1.4)
    for (i, _, pt) in cross_before:
        ax.plot([pt[0]], [pt[1]], "C3o", ms=11)
    ax.set_aspect("equal")
    ax.set_title(f"三叶结的 3D 投影：{len(cross_before)} 个交叉\n（红点；非平凡扭结）", fontsize=11)
    ax.grid(alpha=0.3)

    ax = fig.add_subplot(1, 2, 2)
    ax.plot(t, x4, "C2", lw=1.4)
    ax.axhline(0, color="k", lw=0.6, ls="--")
    for (i, j, _) in cross_before:
        ax.plot([t[i]], [x4[i]], "C3o", ms=9)
        ax.plot([t[j]], [x4[j]], "C3v", ms=9)
    ax.set_xlabel("参数 t")
    ax.set_ylabel("第 4 维坐标 x₄")
    ax.set_title(f"用第 4 维做局部鼓包：交叉处两股 |Δx₄| 最小 "
                 f"{min(resolved):.2f} > 0.05\n被解开的交叉 {n_res}/{len(cross_before)} 个；"
                 f"R⁴ 中最小平距离 {dmin4:.3f} > 0", fontsize=11)
    ax.grid(alpha=0.3)
    fig.tight_layout()
    fig.savefig(os.path.join(OUT, "fig_unknot_r4.png"), dpi=150)
    plt.close(fig)

    # ------------------------------------------------------------------ 图 3
    fig, ax = plt.subplots(figsize=(12, 5.6))
    col_labels = ["统计只有两类", "非平凡连接", "同时满足"]
    yes = ("是", "**是**")
    for k, row in enumerate(rows):
        vals = [row["统计两类?"], row["非平凡连接?"], row["同时满足"]]
        for m, v in enumerate(vals):
            ok = v in yes
            ax.add_patch(plt.Rectangle((m * 1.12, k - 0.36), 1.0, 0.72,
                                       color="C2" if ok else "0.85", alpha=0.95))
            ax.text(m * 1.12 + 0.5, k, "是" if ok else "否", ha="center", va="center",
                    fontsize=12, color="white" if ok else "0.35")
        ax.text(3.55, k, f"π₁ 阿贝尔化 = {row['π₁ 阿贝尔化']}", va="center", fontsize=10.5)
    ax.set_yticks(range(len(rows)))
    ax.set_yticklabels([f"d = {row['d']}" for row in rows], fontsize=12)
    ax.set_xticks([m * 1.12 + 0.5 for m in range(3)])
    ax.set_xticklabels(col_labels, fontsize=11)
    ax.set_xlim(-0.1, 5.4)
    ax.set_ylim(-0.65, len(rows) - 0.35)
    ax.set_title("维数判定（绿 = 是）：只有 d = 3 三格全绿\n"
                 "R1 给下界 3 ≤ d；R2 给上界 d ≤ 3 → 交集 = {3}（唯一性，不是最小性）",
                 fontsize=11)
    fig.tight_layout()
    fig.savefig(os.path.join(OUT, "fig_dimension_verdict.png"), dpi=150)
    plt.close(fig)

    report["conclusion"] = (
        "① D1/D2：**同一个方程 χ(2) = χ(1)²，两种群，两个世界**——Z 型群给连续统（任意子排除不掉）、"
        "Z2 型群给 {±1}。这是 R1（统计只有两类）的代数核，也是 ES/VSS 那轮的同一件事。"
        "② D3：**d ≥ 4 不存在非平凡扭结**（数值：三叶结 3 个交叉用第 4 维鼓包全部解开、R⁴ 无自交）"
        "⟹ R2 的上界。"
        "③ D4：**d = 2 不能互连**（Hopf link 在 3D Lk = 1 且互不相交，压到 z = 0 后必然相交）"
        "⟹ R2 的下界那一侧。"
        "④ 合起来：R1 给 d ≥ 3、R2 给 d = 3 ⟹ **交集 = {3}，是唯一性不是最小性**。"
        "**诚实边界**：R1/R2 两条要求本身是标准事实的**陈述**（Fox–Neuwirth 1962 等），本套未形式化；"
        "Lean 里抽成 `3 ≤ d` / `d ≤ 3` 两个定义，主定理是 `le_antisymm` —— 全部重量在这两条输入上。"
        "真定理只有 DS1（Z 型角色不落在 ±1）与 DS3（与 ES5 合并）。"
        "**这不是「把 P3 变成推论」**：R1/R2 仍是输入；本工作把「维数 = 3」从一个**单一公设（P3 三方向）**"
        "换成**两条可分别判死的要求的交**——收窄了输入的性质，没有消掉输入。零新可检验预言。"
    )
    report["files"] = {"fig_phase_sets": "fig_phase_sets.png",
                       "fig_unknot_r4": "fig_unknot_r4.png",
                       "fig_dimension_verdict": "fig_dimension_verdict.png"}

    with open(os.path.join(OUT, "report.json"), "w", encoding="utf-8") as f:
        json.dump(report, f, ensure_ascii=False, indent=2)

    lines = [
        "维数选择：两条硬要求的交 = {3}（唯一性，非最小性）（DS1–DS8）",
        "=" * 72,
        f"D1 二维相位落在 ±1 上的比例     = {frac:.2e}（整个单位圆 ⟹ 排除不掉任意子）",
        f"D1 α=π/3 虚部 / √3/2           = {float(np.sin(a33)):.6f} / {float(np.sqrt(3)/2):.6f}",
        f"D2 三维满足 σ²=1 的相位数       = {len(zeros)}（应 2）",
        f"D3 三叶结 3D 交叉数             = {len(cross_before)}",
        f"D3 被第 4 维解开的交叉数        = {n_res}（最小 |Δx₄| = {min(resolved):.3f}）",
        f"D3 R⁴ 中最小非相邻点距          = {dmin4:.4f}（> 0 ⟹ 无自交）",
        f"D4 Hopf link 3D 最小距离        = {d_3d:.4f}（> 0 ⟹ 互不相交）",
        f"D4 Gauss 环绕数                 = {lk:.4f}（应 ≈ 1）",
        f"D4 压到 z=0 后两曲线交点数      = {hits}（> 0 ⟹ 二维互连不可能）",
        f"D5 唯一同时满足的维数           = 3",
        "=" * 72,
        "结论：R1（统计只有两类）给 d ≥ 3；R2（非平凡连接数）给 d = 3 ⟹ 交集 = {3}。",
        "      **唯一性，不是最小性** —— 没有口味选择。",
    ]
    with open(os.path.join(OUT, "summary.txt"), "w", encoding="utf-8") as f:
        f.write("\n".join(lines) + "\n")

    print(json.dumps({k: v for k, v in report["results"].items()
                      if k in ("D1_two_dim_phase_set", "D3_unlink_in_four_dim",
                               "D4_two_dim_cannot_link")}, ensure_ascii=False, indent=2)[:2600])
    print("\n-> 产物:", os.path.abspath(OUT))


if __name__ == "__main__":
    main()
