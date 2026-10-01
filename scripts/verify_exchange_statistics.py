#!/usr/bin/env python3
"""交换回路 ≅ 2π 旋转回路：把「统计性 = 闭包相因子」从定义升级成条件定理（ES1–ES8）

leo：「交换回路与 2π 旋转回路同伦」后续。

E1 ★  Z₂ 角色只有两个（⟹ 三维相位只能 ±1）
E2 ★★ 二维：全扭转(2π 旋转) = 交换²；同一个方程 χ(2) = χ(1)²
       在 Z 里 2 ≠ 0（自由）／在 Z₂ 里 2 = 0（被迫 ±1）——**任意子为什么只在二维**
E3    可达相位集对比：三维 {±1}（2 点）vs 二维 U(1)（整圆）
E4 ★★ SU(2)/SO(3) 提升检验：「2π 旋转回路非平凡」的严格核
       θ∈[0,2π] 的旋转回路在 SU(2) 里从 I 走到 −I（非闭合 ⟹ 不可缩）；
       θ∈[0,4π] 回到 +I（可缩，给出显式收缩族）
E5 ★★ 皮带诡计（Dirac belt）：不变量 = 扭转数的**奇偶** = Z₂
       2π ⟹ 奇（不可解）；4π ⟹ 偶（可解到零）
E6    接口：交换相因子 = 闭包相因子（同一 Z₂ 上取值一致）

产物：artifacts/exchangestatistics/{report.json, summary.txt, fig_phase_space.png, fig_belt_parity.png}
"""
import json
import os
from collections import deque
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

OUT = os.path.join(os.path.dirname(__file__), "..", "artifacts", "exchangestatistics")
os.makedirs(OUT, exist_ok=True)

I2 = np.eye(2, dtype=complex)
SIG = {"σ₁": np.array([[0, 1], [1, 0]], dtype=complex),
       "σ₂": np.array([[0, -1j], [1j, 0]], dtype=complex),
       "σ₃": np.array([[1, 0], [0, -1]], dtype=complex)}


def main():
    rng = np.random.default_rng(11)
    report = {"model": "exchange loop = 2π rotation loop (upgrades VBS definition to a conditional theorem)",
              "date": str(date.today()), "results": {}}

    # ------------------------------------------------------------------ E1 ★
    alphas = np.linspace(0, 2 * np.pi, 200001)
    dev = np.abs(np.exp(1j * alphas) ** 2 - 1.0)
    mask = dev < 1e-6
    zs = alphas[mask]
    groups = []
    for a in zs:
        if not groups or a - groups[-1][-1] > 0.01:
            groups.append([a])
        else:
            groups[-1].append(a)
    zeros = sorted({round(float(np.mean(g)) % (2 * np.pi), 9) for g in groups})
    report["results"]["E1_two_class_phases"] = {
        "内容": "Z₂ 角色：χ(2)=1 且 χ(2)=χ(1)² → χ(1)²=1 → 只有两个值",
        "扫描 |χ(1)²−1| < 1e−6 的零点（rad，模 2π 去重）": zeros,
        "零点个数": len(zeros),
        "结论": "三维相位只能 +1 / −1 ⟹ **任意子被排除**（与 ES5 一致）",
    }

    # ------------------------------------------------------------------ E2 ★★
    def chi(alpha, n):        # 二维辫群 Z 的角色 χ(n) = exp(iαn)
        return np.exp(1j * alpha * n)

    rows2 = []
    worst2 = 0.0
    for alpha in [0.0, np.pi / 3, np.pi / 2, np.pi, 1.7, 2 * np.pi / 3]:
        exch = chi(alpha, 1)              # 交换 = 生成元 1
        rot = chi(alpha, 2)               # 2π 旋转（全扭转）= 生成元 2
        worst2 = max(worst2, abs(rot - exch ** 2))
        rows2.append({"α": float(alpha), "交换 χ(1)": [float(exch.real), float(exch.imag)],
                      "2π 旋转 χ(2)": [float(rot.real), float(rot.imag)],
                      "χ(2) − χ(1)²": float(abs(rot - exch ** 2)),
                      "|χ(1)|": float(abs(exch)),
                      "χ(1) 不是 ±1（任意子相位）": bool(abs(exch - 1) > 1e-9
                                                   and abs(exch + 1) > 1e-9)})
    report["results"]["E2_double_exchange"] = {
        "内容": "二维：χ(2) = χ(1)²（两次交换 = 一次 2π 旋转），且 χ(1) 自由",
        "最大偏差": float(worst2),
        "抽样表": rows2,
        "结论": "**同一个方程**：在 Z（二维辫群）里 2 ≠ 0 → χ(1) 自由（任意子）；"
                "在 Z₂（三维类群）里 2 = 0 → χ(1)² = 1 → 被迫 ±1",
    }

    # ------------------------------------------------------------------ E3
    n3d = len(zeros)
    report["results"]["E3_reachable_phases"] = {
        "三维（π₁ 的阿贝尔化 = Z₂）": {"可达相位个数": n3d, "集合": ["+1", "−1"]},
        "二维（π₁ 的阿贝尔化 = Z）": {"可达相位": "整个 U(1)", "参数": "α ∈ [0, 2π) 连续"},
        "结论": "任意子只在二维存在；三维被阿贝尔化 Z₂ 压成两个值",
    }

    # ------------------------------------------------------------------ E4 ★★
    # 把旋转回路提升到 SU(2) ≅ S³（单位四元数）。U(θ) = cos(θ/2) − i sin(θ/2)σ₃ 对应
    # 四元数 (cos(θ/2), −sin(θ/2), 0, 0)；θ ∈ [0,4π] 走完整个大圆一次。
    def lift_q(theta, M):
        """把 U(θ)=cos(θ/2)I − i sin(θ/2)M 映成单位四元数。"""
        c, s = np.cos(theta / 2), np.sin(theta / 2)
        cands = []
        for v in [(1, 0, 0), (0, 1, 0), (0, 0, 1)]:
            q = np.array([c, -s * v[0], -s * v[1], -s * v[2]])
            U = c * I2 - 1j * s * M
            # 校验：由 q 重建的 SU(2) 矩阵应等于 U（差一个无关的相位约定）
            a, b, cc, d = q
            Mq = np.array([[a - 1j * d, -b - 1j * cc],
                           [b - 1j * cc, a + 1j * d]], dtype=complex)
            cands.append((float(np.max(np.abs(Mq - U))), q))
        _, q = min(cands, key=lambda t: t[0])
        return q, min(c[0] for c in cands)

    lift_rows, qerr = [], 0.0
    for name, M in SIG.items():
        q2, e2 = lift_q(2 * np.pi, M)
        q4, e4 = lift_q(4 * np.pi, M)
        qerr = max(qerr, e2, e4)
        lift_rows.append({"轴": name,
                          "2π 提升的端点（四元数）": [round(float(x), 12) for x in q2],
                          "4π 提升的端点（四元数）": [round(float(x), 12) for x in q4],
                          "2π 端点距 +1": float(np.linalg.norm(q2 - np.array([1.0, 0, 0, 0]))),
                          "4π 端点距 +1": float(np.linalg.norm(q4 - np.array([1.0, 0, 0, 0])))})
    w2 = max(r["2π 端点距 +1"] for r in lift_rows)
    w4 = max(r["4π 端点距 +1"] for r in lift_rows)

    # 4π 回路的**显式收缩族**：H(u,φ) = cosφ·(cos u, sin u, 0, 0) + sinφ·(0,0,1,0)
    # φ=0 是大圆（= 4π 提升，走一遍）；φ=π/2 是常值；每个固定 φ 都是**闭曲线**。
    def H(u, phi):
        return np.array([np.cos(phi) * np.cos(u), np.cos(phi) * np.sin(u), np.sin(phi), 0.0])
    phis = np.linspace(0, np.pi / 2, 41)
    us = np.linspace(0, 2 * np.pi, 721)
    unit_dev = max(abs(np.linalg.norm(H(u, ph)) - 1.0) for ph in phis for u in us[::20])
    clos_dev = max(float(np.linalg.norm(H(0.0, ph) - H(2 * np.pi, ph))) for ph in phis)
    const_dev = max(float(np.linalg.norm(H(u, np.pi / 2) - H(0.0, np.pi / 2))) for u in us)
    report["results"]["E4_double_cover_lift"] = {
        "内容": "旋转回路提升到 SU(2) ≅ S³（单位四元数）：2π 从 +1 走到 −1（非闭合 ⟹ 不可缩）；"
                "4π 回到 +1（闭合 ⟹ 可缩，给出显式收缩族）",
        "四元数重建 SU(2) 矩阵的最大偏差": float(qerr),
        "表": lift_rows,
        "2π 提升端点距 +1（应为 2）": float(w2),
        "4π 提升端点距 +1（应为 0）": float(w4),
        "收缩族 H(u,φ)：|q|−1 最大偏差": float(unit_dev),
        "收缩族 H(u,φ)：每条曲线闭合性 max|H(0,φ)−H(2π,φ)|": float(clos_dev),
        "收缩族 H(u,π/2) 距常值最大偏差": float(const_dev),
        "结论": "同一个收缩族：φ=0 是 4π 回路、φ=π/2 退化为常值，**每个中间 φ 都是闭曲线** ⟹ "
                "4π 回路可缩。2π 回路的提升端点停在 −1（≠ +1）—— 端点在同伦下不变（相对基点），"
                "故 2π 回路**不可缩**。这正是「交换 = 2π 旋转」非平凡的严格核。",
    }

    # ------------------------------------------------------------------ E5 ★★
    # 皮带模型：扭转总量 T ∈ Z。允许的操作：
    #   R1 局部分配（保守：Σ 不变）——数值验证
    #   R2 绕过端点一次（皮带诡计的标准动作）：T → T − 2
    def redistribute(T, N=8, steps=2000):
        seg = [0] * N
        seg[0] = T
        for _ in range(steps):
            i = int(rng.integers(0, N))
            if seg[i] != 0:
                j = int(rng.integers(0, N))
                if j != i:
                    seg[i] -= 1
                    seg[j] += 1
        return sum(seg), seg
    sums_ok = all(redistribute(T)[0] == T for T in range(-4, 5))

    def reachable(T, bound=40):
        seen = {T}
        dq = deque([T])
        out = {T}
        while dq:
            v = dq.popleft()
            for nv in (v - 2, v + 2):
                if abs(nv) <= bound and nv not in seen:
                    seen.add(nv)
                    out.add(nv)
                    dq.append(nv)
        return out
    reach = {T: sorted(reachable(T)) for T in [-2, -1, 0, 1, 2, 3]}
    report["results"]["E5_belt_parity"] = {
        "内容": "皮带诡计：不变量 = 扭转数的**奇偶**（= Z₂，与 E1 同一个群）",
        "局部分配保持 Σ 扭转（数值验证）": bool(sums_ok),
        "模型输入：绕过端点一次使 T → T − 2（皮带诡计的标准动作）": True,
        "从 T=1（2π 旋转）可达的 T（前 6 个）": reach[1][:6],
        "从 T=2（4π 旋转）可达的 T（前 6 个）": reach[2][:6],
        "T=1 能否归零": bool(0 in reach[1]),
        "T=2 能否归零": bool(0 in reach[2]),
        "结论": "2π ⟹ 奇 ⟹ **不可解**；4π ⟹ 偶 ⟹ **可解到零**。不变量就是奇偶 = Z₂",
    }

    # ------------------------------------------------------------------ E6
    rows6 = []
    for lab, s in [("玻色型", 1.0), ("费米型", -1.0)]:
        rows6.append({"类型": lab, "交换相因子": s, "闭包相因子（2π 旋转）": s,
                      "差": 0.0})
    report["results"]["E6_interface_VBS_VSS"] = {
        "内容": "交换相因子与闭包相因子落在同一个 Z₂ 上，取值一致（ES8）",
        "表": rows6,
        "结论": "「统计性 = 闭包相因子」从 **定义**（VBS）升级为 **条件定理**："
                "条件是拓扑输入『交换回路与 2π 旋转回路同类』",
    }

    # ------------------------------------------------------------------ 图 1
    fig, axes = plt.subplots(1, 2, figsize=(13, 5.6))
    ax = axes[0]
    th = np.linspace(0, 2 * np.pi, 800)
    ax.plot(np.cos(th), np.sin(th), "0.7", lw=1.2, label="单位圆 U(1)")
    ax.plot([1, -1], [0, 0], "C0o", ms=13)
    ax.annotate("χ = +1", xy=(1, 0), xytext=(1.12, 0.22), fontsize=12, color="C0")
    ax.annotate("χ = −1", xy=(-1, 0), xytext=(-1.5, 0.22), fontsize=12, color="C0")
    ax.set_aspect("equal")
    ax.set_xlim(-1.75, 1.75)
    ax.set_ylim(-1.35, 1.35)
    ax.set_title("三维：π₁ 的阿贝尔化 = Z₂\nχ(2)=χ(1)² 且 2 ≡ 0 → χ(1)² = 1 → 只能 ±1\n"
                 "（任意子被排除）", fontsize=11)
    ax.axhline(0, color="k", lw=0.6)
    ax.axvline(0, color="k", lw=0.6)
    ax.grid(alpha=0.3)
    ax.legend(loc="lower left", fontsize=9)

    ax = axes[1]
    ax.plot(np.cos(th), np.sin(th), "C3", lw=2.2, label="可达相位 = 整个 U(1)")
    for a, lab in [(np.pi / 3, "α = π/3\n（任意子）"), (1.7, "α = 1.7")]:
        ax.plot([np.cos(a)], [np.sin(a)], "C1o", ms=12)
        ax.annotate(lab, xy=(np.cos(a), np.sin(a)),
                    xytext=(np.cos(a) * 1.25, np.sin(a) * 1.25 + 0.12), fontsize=11)
    ax.plot([1, -1], [0, 0], "C0o", ms=10, alpha=0.5)
    ax.set_aspect("equal")
    ax.set_xlim(-1.75, 1.75)
    ax.set_ylim(-1.45, 1.45)
    ax.set_title("二维：π₁ 的阿贝尔化 = Z\nχ(2)=χ(1)² 且 2 ≠ 0 → χ(1) 自由（参数 α ∈ [0,2π)）\n"
                 "（任意子合法）", fontsize=11)
    ax.axhline(0, color="k", lw=0.6)
    ax.axvline(0, color="k", lw=0.6)
    ax.grid(alpha=0.3)
    ax.legend(loc="lower left", fontsize=9)
    fig.tight_layout()
    fig.savefig(os.path.join(OUT, "fig_phase_space.png"), dpi=150)
    plt.close(fig)

    # ------------------------------------------------------------------ 图 2
    fig, ax = plt.subplots(figsize=(10.5, 5.5))
    Ts = list(range(-5, 6))
    cols = ["C3" if T % 2 else "C0" for T in Ts]
    ax.bar(Ts, [1] * len(Ts), color=cols, alpha=0.85, width=0.7)
    ax.axvline(0.5, color="k", lw=1.4, ls="--")
    ax.annotate("2π 旋转 → T = 1（奇）：只能在此集合内活动，到不了 0",
                xy=(0, 1.30), fontsize=10.5, ha="center", color="C3")
    ax.annotate("4π 旋转 → T = 2（偶）：绕过端点两次 → 回到 0",
                xy=(0, 1.13), fontsize=10.5, ha="center", color="C0")
    ax.set_yticks([])
    ax.set_ylim(0, 1.50)
    ax.set_xlabel("皮带的扭转总量 T（绕过端点一次使 T → T − 2，故奇偶是守恒量）")
    ax.set_title("皮带诡计（Dirac belt）：不变量 = 扭转数的奇偶 = Z₂\n"
                 "红 = 奇数（不可归零）/ 蓝 = 偶数（可归零到 0）⟹ 与三维相位同一个 Z₂")
    ax.grid(alpha=0.3, axis="x")
    fig.tight_layout()
    fig.savefig(os.path.join(OUT, "fig_belt_parity.png"), dpi=150)
    plt.close(fig)

    report["conclusion"] = (
        "① E1/E5：三维的相位只取 ±1，理由是 π₁ 的阿贝尔化是 Z₂（阶 2）——任意子被排除；"
        "皮带诡计的不变量（扭转数奇偶）就是同一个 Z₂。"
        "② E2/E3：**同一个方程** χ(2) = χ(1)²，在 Z（二维辫群）里 2 ≠ 0 ⟹ χ(1) 自由 ⟹ 任意子合法；"
        "在 Z₂（三维类群）里 2 ≡ 0 ⟹ χ(1)² = 1 ⟹ 被迫 ±1。**「任意子为什么需要二维」的答案就是这一行。**"
        "③ E4：SU(2) 提升检验——2π 旋转回路从 I 走到 −I（非闭合、不可缩），4π 回到 +I（同一收缩族全程闭合）。"
        "这是「交换 = 2π 旋转」非平凡的严格核。"
        "④ E6：**把 VBS 的『统计性 = 闭包相因子』从定义升级成条件定理**——"
        "条件是拓扑输入『交换回路与 2π 旋转回路落在同一类』（Fadell 1962 / Finkelstein–Rubinstein 1968）。"
        "诚实边界：**代数部分是平凡的**（Lean 里一行 rw），全部重量在拓扑输入上；"
        "拓扑输入本身（配置空间的 π₁ = S_N / B_N、Fox–Neuwirth）**未形式化**；"
        "算子那一半（相位 ⟹ 场算符反对易）仍缺 ⟹ 仍不是完整自旋-统计定理。"
    )
    report["files"] = {"fig_phase_space": "fig_phase_space.png",
                       "fig_belt_parity": "fig_belt_parity.png"}

    with open(os.path.join(OUT, "report.json"), "w", encoding="utf-8") as f:
        json.dump(report, f, ensure_ascii=False, indent=2)

    lines = [
        "交换回路 ≅ 2π 旋转回路：把「统计性 = 闭包相因子」从定义升级成条件定理（ES1–ES8）",
        "=" * 72,
        f"E1 Z₂ 相位零点个数（模 2π 去重）= {len(zeros)}（应 2）  位置 = {zeros}",
        f"E2 χ(2) = χ(1)² 最大偏差          = {worst2:.3e}（二维自由）",
        f"E3 三维可达相位 {n3d} 个 / 二维可达相位 = 整个 U(1)",
        f"E4 2π 提升端点距 +1（四元数）      = {w2:.3f}（= 2，即停在 −1 ⟹ 非闭合）",
        f"E4 4π 提升端点距 +1（四元数）      = {w4:.3e}（闭合）",
        f"E4 收缩族 |q|−1 最大偏差           = {unit_dev:.3e}",
        f"E4 收缩族每条曲线闭合性偏差        = {clos_dev:.3e}；φ=π/2 距常值 = {const_dev:.3e}",
        f"E5 局部分配保持 ΣT                = {sums_ok}",
        f"E5 T=1（2π）可达集合 → 含 0?      = {0 in reach[1]}   （奇偶守恒 ⟹ 不可归零）",
        f"E5 T=2（4π）可达集合 → 含 0?      = {0 in reach[2]}   （可归零）",
        "=" * 72,
        "结论：同一个方程 χ(2)=χ(1)²，2≡0 mod 2 就只给 ±1（三维），2≠0 就给 U(1)（二维）；",
        "      交换与 2π 旋转同类 ⟹ 相位相同 ⟹ VBS 那条定义变成条件定理。",
    ]
    with open(os.path.join(OUT, "summary.txt"), "w", encoding="utf-8") as f:
        f.write("\n".join(lines) + "\n")

    print(json.dumps({k: v for k, v in report["results"].items()
                      if k in ("E1_two_class_phases", "E4_double_cover_lift",
                               "E5_belt_parity")}, ensure_ascii=False, indent=2)[:2400])
    print("\n-> 产物:", os.path.abspath(OUT))


if __name__ == "__main__":
    main()
