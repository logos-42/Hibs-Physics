#!/usr/bin/env python3
"""黑洞与虫洞的流动结构：数值验证（空间流动假设）

主线公设（SLS/SM/SG）：引力 = 空间流动非均匀（Φ = ½v²，SG11）；
光子 = 随空间流动（dτ = 0）。Gordon 度规 g_tt = 1 − v²/c²。

物理图像（与 Hamilton–Lisle 河流模型 2008 精确同构）：
  黑洞 = 空间径向内向流动 v(r) = c·√(r_s/r)（Schwarzschild 精确 river 场）
    视界 r_s = 2GM/c² = v 首次达到 c 的面（BH1，Lean 已证）
    向外光子坐标速度 dx/dt = v − c：视界处 = 0（冻结，BH3），内部 < 0（仍向内）
    向内光子 dx/dt = −(v + c)：恒内向
    时间膨胀 √(1 − v²/c²) = √(1 − r_s/r) → 0 在视界
  白洞 = 流反转（v ↦ −v，BH5–BH6）：光子被喷出，视界同位
  虫洞 = 亚光速流管通道：v(s) 在喉部有峰值但 |v| < c 处处
    （vs 黑洞单调趋 c——结构差异：黑洞有视界，虫洞没有）
    光子随流穿过全程 dτ = 0（零时通道）

检验：
  1. 视界位置：v(r_s) = c ⟺ r_s = 2GM/c²（与 GR 精确一致）
  2. 光子速度符号表：视界/内外的向外光子坐标速度
  3. 时间膨胀曲线：视界处 → 0
  4. 外部观测者：向外光子 t(r) 在 r → r_s⁺ 发散（看不到光进视界）
  5. 虫洞 vs 黑洞：v 场结构对比（单调过 c vs 峰值 < c）
  6. 虫洞穿越：光子随流 dτ = 0 全程

诚实边界：与 GR/河流模型数值全同——结构无变化，变化只在解释层
（视界 = 光速面、内部 = 超光速流、虫洞 = 流管通道）。见 4 层判定。
"""
import json
import os
from datetime import date

import numpy as np
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
import matplotlib.font_manager as fm
from scipy.integrate import quad

for _fp in ("/System/Library/Fonts/PingFang.ttc",
            "/System/Library/Fonts/Hiragino Sans GB.ttc"):
    if os.path.exists(_fp):
        fm.fontManager.addfont(_fp)
        plt.rcParams["font.sans-serif"] = [fm.FontProperties(fname=_fp).get_name()]
        break
plt.rcParams["axes.unicode_minus"] = False

OUT = os.path.join(os.path.dirname(__file__), "..", "artifacts", "blackhole")
os.makedirs(OUT, exist_ok=True)

C = 1.0      # c = 1（几何单位）
RS = 1.0     # 视界半径 r_s = 2GM/c²


def v_blackhole(r):
    """黑洞 river 场：v(r) = c·√(r_s/r)（内向，Schwarzschild 精确）。"""
    return C * np.sqrt(RS / np.maximum(r, 1e-9))


def v_wormhole(s, v0=0.8 * C, w=0.5, s0=0.0):
    """虫洞通道流场：喉部（s=s0）处 v 峰值 v0 < c，两侧趋于 0。"""
    return v0 / np.cosh((s - s0) / w)


def photon_velocities(v):
    """Gordon 度规中光子的两个坐标速度：dx/dt = v ± c。"""
    return v + C, v - C


def report_4layer():
    """诚实 4 层判定（仓库标准，防过度声称）。"""
    return [
        {"layer": "① 数学恒等式", "verdict": "真但平凡",
         "why": ("视界 v=c⟺g_tt=0（BH1 Lean 已证）是 Gordon 度规的直接代数；"
                 "向外光子 dx=(v−c)dt 代入 dτ²=0 是恒等（BH2）——"
                 "河流模型（Hamilton–Lisle 2008, Am. J. Phys. 76, 519）的全部内容")},
        {"layer": "② 结构对应", "verdict": "已知物理",
         "why": ("黑洞 = 内向流动 + 视界 = 光速面 + 内部超光速流 = "
                 "Schwarzschild 解的精确重述；虫洞 = 亚光速流管"
                 "（Morris–Thorne 喉部的流线版）")},
        {"layer": "③ 数值匹配", "verdict": "一致但非新",
         "why": ("r_s = 2GM/c² 与 GR 精确同；时间膨胀 √(1−r_s/r) 同；"
                 "光子冻结在视界 = GR 坐标奇点（史瓦西坐标 "
                 "dr/dt = ±c(1−r_s/r) 的另一种写法）")},
        {"layer": "④ 概念重构", "verdict": "不可证伪",
         "why": ("解释层全变（视界=光速面、内部=超光速流、虫洞=流管）"
                 "但公式与数值全同；唯一可检验出口 = 空间流动非均匀 ⟹ "
                 "洛伦兹破缺（仓库既有诚实结论，此处无新增）")},
    ]


def main():
    report = {"model": "black hole & wormhole as space-flow structures",
              "date": str(date.today()), "results": {}}

    # ---- 1. 视界位置 ----
    rs_num = float(RS)
    gtt = 1.0 - v_blackhole(rs_num) ** 2 / C ** 2
    report["results"]["horizon"] = {
        "r_s = 2GM/c^2": rs_num,
        "v(r_s)/c": round(float(v_blackhole(rs_num)), 6),
        "g_tt(r_s)": round(float(gtt), 9),
        "note": "v(r_s)=c ⟺ g_tt=0（BH1 数值确认，与 GR 精确一致）"}

    # ---- 2. 光子速度符号表 ----
    r_test = [0.25, 0.5, 1.0, 2.0, 4.0]  # 内部×2, 视界, 外部×2
    table = []
    for r in r_test:
        v = float(v_blackhole(r))
        v_in, v_out = photon_velocities(v)
        table.append({"r/r_s": r, "v/c": round(v, 4),
                      "向内光子 dx/dt": round(v_in, 4),
                      "向外光子 dx/dt": round(v_out, 4),
                      "向外光子方向": "仍向内" if v_out >= 0 else "向外"})
    report["results"]["photon_velocity_table"] = table

    # ---- 3. 时间膨胀 ----
    rr = np.linspace(1.0, 8.0, 400)
    dt_over_tau = np.sqrt(np.maximum(1.0 - RS / rr, 0.0))
    report["results"]["time_dilation_at_horizon"] = round(float(dt_over_tau[0]), 6)

    # ---- 4. 外部观测者：向外光子 t(r) 在视界发散 ----
    # dr/dt = v − c = c(√(r_s/r) − 1)；t = ∫ dr/(c−v) 从 r 到 ∞
    def t_infall(r0):
        integrand = lambda r: 1.0 / (C - v_blackhole(r))
        return quad(integrand, r0, 50.0, points=[rs_num])[0]
    t_at_1_1 = t_infall(1.1)
    t_at_1_01 = t_infall(1.01)
    t_at_1_001 = t_infall(1.001)
    report["results"]["external_observer_photon_time"] = {
        "t(r=1.1 r_s)": round(t_at_1_1, 3),
        "t(r=1.01 r_s)": round(t_at_1_01, 3),
        "t(r=1.001 r_s)": round(t_at_1_001, 3),
        "note": "外部（静止）观测者看到向外光子在 r → r_s⁺ 时 t → ∞：光永远到不了视界（GR 坐标奇点）"}

    # ---- 5. 虫洞 vs 黑洞 ----
    s = np.linspace(-4, 4, 500)
    vw = v_wormhole(s)
    vr = v_blackhole(np.linspace(0.25, 8, 500))
    report["results"]["wormhole_vs_blackhole"] = {
        "wormhole_v_peak/c": round(float(vw.max()), 4),
        "wormhole_has_horizon": bool(np.any(vw >= C)),
        "blackhole_v_exceeds_c_at": "r < r_s（内部）",
        "wormhole_photons_cross": "随流 dτ=0 全程，无冻结点"}

    # ---- 6. 虫洞穿越：光子 dτ = 0 ----
    s_pts = np.linspace(-4, 4, 2001)
    vv = v_wormhole(s_pts)
    ds = s_pts[1] - s_pts[0]
    # 光子随流（dx = (v+c)dt 解），坐标时间 dt = ds/(v+c)
    dt_coord = np.sum(ds / (vv + C))
    # dτ² = dt² − dx²/c² 每步：dτ² = ds²(1 − (v+c)²/c²)/(v+c)² —— 应恒 0？
    # 更直接：用 gordonProperTimeSq 每步验证
    proper_sq = (ds ** 2) * (1.0 - ((vv + C) - vv) ** 2 / C ** 2) / (vv + C) ** 2
    report["results"]["wormhole_crossing"] = {
        "coordinate_time (sum ds/(v+c))": round(float(dt_coord), 4),
        "max |dτ²| per step": round(float(np.max(np.abs(proper_sq))), 15),
        "note": "光子随流穿过虫洞 dτ² ≡ 0（零时通道，SM1/BH2 每点成立）"}

    # ---- 图 ----
    # 图1: v 场对比（黑洞单调过 c / 虫洞峰值 < c）
    fig, ax = plt.subplots(figsize=(8, 5))
    ax.plot(rr, v_blackhole(rr) / C, "k-", lw=2, label="黑洞 v(r)/c = √(r_s/r)")
    ax.plot(s, vw / C, "C0-", lw=2, label="虫洞 v(s)/c = v₀·sech((s−s₀)/w)")
    ax.axhline(1.0, color="red", ls="--", lw=1.2, label="光速面 v = c（视界）")
    ax.axvline(1.0, color="gray", ls=":", lw=1)
    ax.text(1.0, 1.06, "视界 r_s", ha="center", fontsize=9, color="gray")
    ax.text(0.28, 0.28, "黑洞内部\nv > c", fontsize=9, color="red", ha="center")
    ax.text(2.3, 0.35, "虫洞喉部\nv_peak < c（可穿越）", fontsize=9, color="C0")
    ax.set_xlabel("r / r_s  （虫洞用通道坐标 s）")
    ax.set_ylabel("空间流动速度 v / c")
    ax.set_title("黑洞 vs 虫洞：流动结构的本质差异（视界 vs 亚光速喉部）")
    ax.set_ylim(-0.1, 2.2)
    ax.legend(loc="upper right", fontsize=9)
    ax.grid(alpha=0.3)
    fig.tight_layout()
    fig.savefig(os.path.join(OUT, "fig_flow_structures.png"), dpi=150)
    plt.close(fig)

    # 图2: 黑洞光子速度 + 冻结
    fig, ax = plt.subplots(figsize=(8, 5))
    r2 = np.linspace(0.25, 4.0, 400)
    v2 = v_blackhole(r2)
    vin, vout = photon_velocities(v2)
    ax.plot(r2, vin, "C1-", lw=2, label="向内光子 dx/dt = −(v+c)")
    ax.plot(r2, vout, "C2-", lw=2, label="向外光子 dx/dt = v−c")
    ax.axhline(0, color="gray", lw=0.8)
    ax.axvline(1.0, color="red", ls="--", lw=1.2)
    ax.text(1.05, -2.1, "视界 r_s：向外光子冻结 dx/dt=0", fontsize=9, color="red")
    ax.text(0.35, 1.2, "内部：向外光子 dx/dt > 0\n（坐标上仍向内！）", fontsize=9, color="C2")
    ax.set_xlabel("r / r_s")
    ax.set_ylabel("光子坐标速度 dx/dt（c=1）")
    ax.set_title("黑洞光锥的流动表述：视界处向外光锥关闭")
    ax.legend(loc="lower left", fontsize=9)
    ax.grid(alpha=0.3)
    fig.tight_layout()
    fig.savefig(os.path.join(OUT, "fig_photon_freeze.png"), dpi=150)
    plt.close(fig)

    # 图3: 时间膨胀
    fig, ax = plt.subplots(figsize=(8, 5))
    ax.plot(rr, dt_over_tau, "C3-", lw=2)
    ax.axvline(1.0, color="red", ls="--", lw=1.2)
    ax.text(1.05, 0.5, "视界：dτ/dt → 0", fontsize=9, color="red")
    ax.set_xlabel("r / r_s")
    ax.set_ylabel("dτ / dt = √(1 − v²/c²) = √(1 − r_s/r)")
    ax.set_title("时间膨胀：偏离空间流动（SM2）在视界处归零")
    ax.grid(alpha=0.3)
    fig.tight_layout()
    fig.savefig(os.path.join(OUT, "fig_time_dilation.png"), dpi=150)
    plt.close(fig)

    report["conclusion"] = (
        "黑洞/虫洞结构在流动假设下与 GR 完全一致（数值同、公式同）——"
        "变化只在解释层：黑洞 = 空间内向流动 v≥c 的区域（视界 = 光速面，"
        "向外光子冻结；内部超光速流把光拖向奇点）；白洞 = 流反转；"
        "虫洞 = 亚光速流管通道（喉部 v 峰值 < c，光子随流零时穿过）。"
        "需要的额外几何描述：① 3+1 维流场 v(x,t)（目前只有 1+1 维 Gordon 骨架）"
        "② 流场动力学方程（目前只有动量守恒 D5 离散版）"
        "③ 流源项（虫洞喉部负能量 = GR NEC 违背的流动语言）"
        "④ 流线拓扑（汇/源/通道分类）⑤ 喉部嵌入几何（双漏斗，Morris–Thorne）。"
        "4 层判定：①②③④ 全为已知物理的重述——无新物理（诚实结论，写死）。")
    report["files"] = {
        "fig_flow_structures": "fig_flow_structures.png",
        "fig_photon_freeze": "fig_photon_freeze.png",
        "fig_time_dilation": "fig_time_dilation.png"}

    with open(os.path.join(OUT, "report.json"), "w", encoding="utf-8") as f:
        json.dump(report, f, ensure_ascii=False, indent=2)

    md = f"""# 黑洞与虫洞的流动结构：数值验证报告

> 空间流动假设：引力 = 流动非均匀（Φ=½v²）；光子 = 随空间流动（dτ=0）。
> 黑洞 = v ≥ c 区域；虫洞 = 亚光速流管通道。与 Hamilton–Lisle 河流模型（2008）同构。

## 结果

| 检验 | 数值 | 与 GR |
|---|---|---|
| 视界 | v(r_s) = c ⟺ g_tt = 0（r_s = 2GM/c²） | 精确一致 |
| 向外光子 @ 视界 | dx/dt = v − c = 0（冻结） | 坐标奇点同 |
| 向外光子 @ 内部 | dx/dt = v − c > 0（仍向内） | 内部 r 类时同 |
| 时间膨胀 @ 视界 | dτ/dt = √(1−r_s/r) → 0 | 精确一致 |
| 外部观测者 | t(r→r_s⁺) → ∞（光到不了视界） | 精确一致 |
| 虫洞喉部 | v_peak = 0.8c < c（可穿越） | MT 喉部同 |
| 虫洞穿越 | 光子随流 dτ² ≡ 0 全程 | 零测地线同 |

## 光子速度（c=1，v(r) = √(r_s/r)）

| r/r_s | v/c | 向内光子 | 向外光子 | 方向 |
|---|---|---|---|---|
{chr(10).join(f"| {t['r/r_s']} | {t['v/c']} | {t['向内光子 dx/dt']} | {t['向外光子 dx/dt']} | {t['向外光子方向']} |" for t in table)}

## 4 层判定（诚实，写死）

{chr(10).join(f"{e['layer']}：**{e['verdict']}** — {e['why']}" for e in report_4layer())}

## 结论

黑洞/虫洞结构在流动假设下**与 GR 完全一致**（数值同、公式同）——变化只在解释层。
**还需要什么几何描述**：
1. 3+1 维流场 v(x,t)（目前只有 1+1 维 Gordon 骨架）
2. 流场动力学方程（目前只有动量守恒 D5 离散版）
3. 流源项（虫洞喉部负能量 = GR NEC 违背的流动语言）
4. 流线拓扑（汇/源/通道分类）
5. 喉部嵌入几何（双漏斗，Morris–Thorne）

## 文件

- Lean: `ProjectionPhysics/Explorations/BlackHoleWormhole.lean`（BH1–BH7, WH1）
- 模拟: `scripts/verify_blackhole_wormhole.py`
- 图: `artifacts/blackhole/fig_*.png`
"""
    with open(os.path.join(OUT, "report.md"), "w", encoding="utf-8") as f:
        f.write(md)

    print(json.dumps(report["results"], ensure_ascii=False, indent=2))
    print("\n→ 产物目录:", os.path.abspath(OUT))


if __name__ == "__main__":
    main()
