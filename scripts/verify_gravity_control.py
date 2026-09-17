#!/usr/bin/env python3
"""控制引力场的代数系统 —— 数值验证（GravityControl.lean GCA0–GCA7 的数值同位体）

leo（2026-09-17）：能不能根据现在的物理学设计一种控制引力场的代数系统？
AI 要做的是"怎么定义基本逻辑——根据数学的什么量化属性来定义计算"。

本脚本验证的答案：
  基元 = 起伏能量（非负二次型）Q_A(v) = Σ_{i∈A}(v_i − v̄_A)²
  命题 p_A := "A 内引力关闭" ⟺ Q_A = 0（GCA2）
  二次型 --极化--> 内积 --正交--> 投影 --投影族--> 逻辑运算
  布尔代数 = 控制区域层状（两两不交或嵌套）的子族（GCA6a/b）；部分重叠 ⟹ 不可交换 ⟹ 非布尔

数值检验（对应 verify_all.py 断言区 GCA-N1..N9）：
  N1  P_A 幂等（P²=P，控制是设定不是累加）
  N2  Q ≥ 0，Q = 0 ⟺ 区域常值，且抹平后 Q = 0
  N2b 与引力接缝：抹平 ⟹ A 内部 Φ=½v² 梯度归零（边界跳变保留 = 诚实残留）
  N3  极化恒等式 Q(u+v) = Q(u) + Q(v) + 2⟨u,v⟩（机器精度）
  N4  正交分解：⟨起伏, 常值⟩ = 0（抹平是正交投影）
  N5  互补投影对：(P, I−P) 幂等/正交/完备（复用 PA2 结构）
  N6  交换律扫描：层状（重叠度 0 或 1）⟹ 交换子 = 0；部分重叠 ⟹ > 0
  N7  布尔子代数：不交族 ⟹ 分配律成立 + 格并幂等；交叠族 ⟹ 双双失效
  N8  二次型签名：Q(t·v) = t²Q(v)（基元是二次型的直接数值证据）
  N9  交换/吸收见证：部分重叠 ⟹ 次序不同；嵌套 ⟹ 吸收（同结果）
"""
import json
import os
from datetime import date

import numpy as np

OUT = os.path.join(os.path.dirname(__file__), "..", "artifacts", "gravitycontrol")
os.makedirs(OUT, exist_ok=True)

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

RNG = np.random.default_rng(20260917)


# ───────────────────────── 代数层（与 Lean 定义逐字对应） ─────────────────────────

def region_mean(A, v):
    """A 上的平均流动（Lean: regionMean）"""
    return v[A].sum() / len(A)


def flatten(A, v):
    """控制操作 P_A：A 内替换为区域平均，A 外不动（Lean: flatten）"""
    w = v.copy()
    w[A] = region_mean(A, v)
    return w


def fluctuation(A, v):
    """起伏 = 被控制拿走的部分（Lean: fluctuation）"""
    w = np.zeros_like(v)
    w[A] = v[A] - region_mean(A, v)
    return w


def fluctuation_energy(A, v):
    """★ 逻辑基元：起伏能量（非负二次型，Lean: fluctuationEnergy）"""
    d = v[A] - region_mean(A, v)
    return float(np.dot(d, d))


def region_inner(A, u, v):
    """区域内积（Lean: regionInner，由极化恒等式给出）"""
    du = u[A] - region_mean(A, u)
    dv = v[A] - region_mean(A, v)
    return float(np.dot(du, dv))


def comm(A, B, v):
    return flatten(A, flatten(B, v)) - flatten(B, flatten(A, v))


def overlap_fraction(A, B, n):
    """重叠度：|A∩B| / min(|A|,|B|)"""
    inter = len(set(A.tolist()) & set(B.tolist()))
    return inter / min(len(A), len(B))


CHECKS = []


def check(name, cond, detail: object = ""):
    CHECKS.append((name, bool(cond)))
    print(("PASS " if cond else "FAIL ") + name + (f"  [{detail}]" if detail != "" else ""))


def main():
    n = 64
    results = {}
    A = np.arange(0, 32)

    # ── N1 P_A 幂等（P² = P） ────────────────────────────────────────────────
    idem = []
    for _ in range(200):
        v = RNG.normal(size=n)
        idem.append(np.max(np.abs(flatten(A, flatten(A, v)) - flatten(A, v))))
    N1 = {"max|P_A(P_A v) − P_A v| (200 随机场)": float(max(idem)),
          "P² = P（幂等）": bool(max(idem) < 1e-12)}
    results["N1_idempotent"] = N1
    check("GCA1: P_A 幂等（P²=P，控制是设定不是累加）", N1["P² = P（幂等）"], N1["max|P_A(P_A v) − P_A v| (200 随机场)"])

    # ── N2 判定泛函：Q ≥ 0 且 Q = 0 ⟺ 常值 ──────────────────────────────────
    qmin = min(fluctuation_energy(A, RNG.normal(size=n)) for _ in range(500))
    const_ok, nonconst_ok = True, True
    for _ in range(200):
        v = RNG.normal(size=n)
        c = float(RNG.normal())
        w = v.copy(); w[A] = c                       # 区域上常值
        const_ok &= abs(fluctuation_energy(A, w)) < 1e-24
        nonconst_ok &= fluctuation_energy(A, v) > 1e-12
    flat_after = max(fluctuation_energy(A, flatten(A, RNG.normal(size=n))) for _ in range(200))
    N2 = {"min Q_A(v) over 500 随机场": float(qmin),
          "Q ≥ 0": bool(qmin >= 0.0),
          "Q = 0 ⟺ 区域常值（200/200 常值场 vs 200/200 非常值场）": bool(const_ok and nonconst_ok),
          "抹平后 Q_A(P_A v) 最大残差": float(flat_after),
          "抹平 ⟹ Q = 0": bool(flat_after < 1e-24)}
    results["N2_decision_functional"] = N2
    check("GCA2a/b: Q ≥ 0 且 Q = 0 ⟺ 区域常值（命题 p_A 的判据）",
          N2["Q ≥ 0"] and N2["Q = 0 ⟺ 区域常值（200/200 常值场 vs 200/200 非常值场）"], N2["min Q_A(v) over 500 随机场"])
    check("GCA2c: 一次抹平让 Q 归零（控制达成目标）", N2["抹平 ⟹ Q = 0"], flat_after)

    # ── N2b 与引力的接缝：Φ = ½v² 的梯度（内部归零，边界跳变诚实保留） ──────
    v = RNG.normal(size=n) * 0.5 + 1.0
    phi = lambda x: 0.5 * x ** 2
    grad_interior = lambda x: np.abs(np.diff(phi(x)[0:31])).max()  # A=[0,32) 内部梯度（0..30）
    before = float(grad_interior(v))
    after = float(grad_interior(flatten(A, v)))
    boundary_jump = float(abs(phi(flatten(A, v))[32] - phi(flatten(A, v))[31]))
    N2b = {"max|∇Φ| A 内部 抹平前": before, "max|∇Φ| A 内部 抹平后": after,
           "边界跳变（区域外未处理，诚实残留）": boundary_jump,
           "抹平 ⟹ 区域内部引力关闭（边界保留）": bool(after < 1e-15 and before > 1e-3 and boundary_jump > 1e-3)}
    results["N2b_gravity_interface"] = N2b
    check("GCA2d: 抹平 ⟹ A 内部 Φ=½v² 梯度归零（引力关闭）", N2b["抹平 ⟹ 区域内部引力关闭（边界保留）"],
          f"内部 {before:.4f} → {after:.2e} / 边界跳变 {boundary_jump:.3f}")

    # ── N3 极化恒等式 ───────────────────────────────────────────────────────
    pol = []
    for _ in range(200):
        u, w = RNG.normal(size=n), RNG.normal(size=n)
        lhs = fluctuation_energy(A, u + w)
        rhs = fluctuation_energy(A, u) + fluctuation_energy(A, w) + 2 * region_inner(A, u, w)
        pol.append(abs(lhs - rhs) / max(1.0, abs(lhs)))
    N3 = {"max 相对误差 Q_A(u+v) = Q_A(u)+Q_A(v)+2⟨u,v⟩（200 对）": float(max(pol)),
          "极化恒等式成立": bool(max(pol) < 1e-12)}
    results["N3_polarization"] = N3
    check("GCA3: 极化恒等式（二次型 → 内积）", N3["极化恒等式成立"], N3["max 相对误差 Q_A(u+v) = Q_A(u)+Q_A(v)+2⟨u,v⟩（200 对）"])

    # ── N4 正交分解 ─────────────────────────────────────────────────────────
    orth = []
    for _ in range(200):
        v = RNG.normal(size=n); c = float(RNG.normal())
        orth.append(abs(region_inner(A, v, np.full(n, c))))
    N4 = {"max|⟨起伏, 常值⟩_A|（200 随机场 × 随机常数）": float(max(orth)),
          "起伏 ⟂ 常值": bool(max(orth) < 1e-12)}
    results["N4_orthogonal"] = N4
    check("GCA4: 起伏 ⟂ 常值（抹平是正交投影）", N4["起伏 ⟂ 常值"], N4["max|⟨起伏, 常值⟩_A|（200 随机场 × 随机常数）"])

    # ── N5 互补投影对 (P, I−P) ──────────────────────────────────────────────
    idP, idQ, ortho, complete = [], [], [], []
    for _ in range(200):
        v = RNG.normal(size=n)
        P = flatten(A, v); Q = v - P
        idP.append(np.max(np.abs(flatten(A, P) - P)))
        idQ.append(np.max(np.abs((P + Q - flatten(A, P + Q)) - Q)))
        ortho.append(np.max(np.abs(flatten(A, Q))))
        complete.append(np.max(np.abs(P + Q - v)))
    N5 = {"幂等 P²=P": float(max(idP)), "幂等 (I−P)²=I−P": float(max(idQ)),
          "正交 P(I−P)=0": float(max(ortho)), "完备 P+(I−P)=I": float(max(complete))}
    N5["互补投影对成立"] = bool(max(idP + idQ + ortho + complete) < 1e-12)
    results["N5_complementary_projection"] = N5
    check("GCA5: (P_A, I−P_A) 是互补投影对（复用 PA2 结构）", N5["互补投影对成立"],
          f"idem {max(idP):.1e} / ortho {max(ortho):.1e} / complete {max(complete):.1e}")

    # ── N6 交换律扫描：层状 ⟹ 交换子 0，部分重叠 ⟹ > 0 ──────────────────────
    vv = RNG.normal(size=n)
    scan = []
    for shift in [0, 2, 4, 8, 12, 16, 20, 24, 28, 32]:
        B = np.arange(16 + shift, 32 + shift) % n
        B = np.unique(B)
        com = np.max(np.abs(comm(A, B, vv)))
        scan.append({"区域 B 起点": int(16 + shift), "重叠度": round(overlap_fraction(A, B, n), 4),
                     "‖[P_A,P_B]v‖": float(com)})
    laminar_cases = [s for s in scan if s["重叠度"] == 0.0 or s["重叠度"] == 1.0]
    partial_cases = [s for s in scan if 0.0 < s["重叠度"] < 1.0]
    N6 = {"扫描": scan,
          "层状族（不交或嵌套）⟹ 交换子 = 0": bool(laminar_cases and all(s["‖[P_A,P_B]v‖"] < 1e-12 for s in laminar_cases)),
          "部分重叠 ⟹ 交换子 > 0（全部）": bool(partial_cases and all(s["‖[P_A,P_B]v‖"] > 1e-6 for s in partial_cases))}
    results["N6_commutator_scan"] = N6
    check("GCA6a/b: 层状族（不交或嵌套）⟹ 可交换（布尔子代数）", N6["层状族（不交或嵌套）⟹ 交换子 = 0"],
          [s["‖[P_A,P_B]v‖"] for s in laminar_cases])
    check("GCA6c: 部分重叠 ⟹ 不可交换（非布尔）", N6["部分重叠 ⟹ 交换子 > 0（全部）"],
          [round(s["‖[P_A,P_B]v‖"], 4) for s in partial_cases])

    # ── N7 布尔子代数：不交族 vs 交叠族（∧ = 复合，∨ = P+Q−P∘Q） ───────────
    def meet(P, Q):
        return lambda w: P(Q(w))

    def join(P, Q):
        return lambda w: P(w) + Q(w) - P(Q(w))

    v2 = RNG.normal(size=n)
    # 不交族（层状，两两不交）
    A1 = np.arange(0, 16); A2 = np.arange(16, 32); A3 = np.arange(32, 48)
    PA, PB, PC = (lambda w: flatten(A1, w)), (lambda w: flatten(A2, w)), (lambda w: flatten(A3, w))
    # 分配律：P ∧ (Q ∨ R) = (P ∧ Q) ∨ (P ∧ R)
    dist_disjoint = np.max(np.abs(
        meet(PA, join(PB, PC))(v2) - join(meet(PA, PB), meet(PA, PC))(v2)))
    idem_disjoint = np.max(np.abs(join(PA, PB)(join(PA, PB)(v2)) - join(PA, PB)(v2)))
    # 交叠族（非层状）：A=[0,32) 与 B=[24,56) 部分重叠
    A_overlap = np.arange(0, 32); B_overlap = np.arange(24, 56)
    PAo = lambda w: flatten(A_overlap, w); PBo = lambda w: flatten(B_overlap, w)
    comm_overlap = np.max(np.abs(PAo(PBo(v2)) - PBo(PAo(v2))))
    idem_overlap = np.max(np.abs(join(PAo, PBo)(join(PAo, PBo)(v2)) - join(PAo, PBo)(v2)))
    N7 = {"不交族: P∧(Q∨R) − (P∧Q)∨(P∧R)": float(dist_disjoint),
          "不交族: (P∨Q)² − (P∨Q)（幂等）": float(idem_disjoint),
          "交叠族: 交换子 ‖[P_A,P_B]v‖": float(comm_overlap),
          "交叠族: (P∨Q)² − (P∨Q)（幂等）": float(idem_overlap),
          "不交族 = 布尔子代数（分配律 + 格并幂等成立）": bool(dist_disjoint < 1e-12 and idem_disjoint < 1e-12),
          "交叠族：布尔运算失效（交换子≠0 + 格并非投影）": bool(comm_overlap > 1e-3 and idem_overlap > 1e-3)}
    results["N7_boolean_vs_not"] = N7
    check("GCA6a: 不交族满足分配律 + 格并幂等（可像集合一样化简）", N7["不交族 = 布尔子代数（分配律 + 格并幂等成立）"],
          f"分配律残差 {dist_disjoint:.1e}")
    check("GCA6c: 交叠族布尔运算失效（交换子≠0 + P+Q−PQ 不是投影）", N7["交叠族：布尔运算失效（交换子≠0 + 格并非投影）"],
          f"交换子 {comm_overlap:.4f} / 幂等残差 {idem_overlap:.4f}")

    # ── N8 二次型签名：Q(t·v) = t²Q(v) ──────────────────────────────────────
    quad = []
    for _ in range(200):
        v = RNG.normal(size=n); t = float(RNG.uniform(0.1, 10.0))
        quad.append(abs(fluctuation_energy(A, t * v) - t * t * fluctuation_energy(A, v))
                    / max(1e-12, abs(t * t * fluctuation_energy(A, v))))
    N8 = {"max 相对误差 Q(t·v) = t²Q(v)（200 随机 (t,v)）": float(max(quad)),
          "基元是二次型（2 次齐次）": bool(max(quad) < 1e-12)}
    results["N8_quadratic_signature"] = N8
    check("GCA7: 基元是二次型（Q(t·v) = t²Q(v)，2 次齐次）", N8["基元是二次型（2 次齐次）"],
          N8["max 相对误差 Q(t·v) = t²Q(v)（200 随机 (t,v)）"])

    # ── N9 交换/吸收见证（与 Lean GCA6b/c 同一组数） ─────────────────────────
    v3 = np.array([1.0, 0.0, 0.0])
    A31 = np.array([0, 1]); B31 = np.array([1, 2])
    lap = (flatten(A31, flatten(B31, v3)), flatten(B31, flatten(A31, v3)))
    v2b = np.array([1.0, 1.0])
    A_nest = np.array([0]); B_nest = np.array([0, 1])
    nest = (flatten(A_nest, flatten(B_nest, v2b)), flatten(B_nest, flatten(A_nest, v2b)))
    N9 = {"部分重叠 A={0,1},B={1,2} v=[1,0,0]：先A后B": lap[0].tolist(),
          "部分重叠：先B后A": lap[1].tolist(),
          "部分重叠 ⟹ 次序不同结果不同": bool(not np.allclose(lap[0], lap[1])),
          "嵌套 A={0}⊂B={0,1} v=[1,1]：先A后B": nest[0].tolist(),
          "嵌套：先B后A": nest[1].tolist(),
          "嵌套 ⟹ 吸收（次序无关，同结果）": bool(np.allclose(nest[0], nest[1]))}
    results["N9_commute_absorb_witnesses"] = N9
    check("GCA6c: 部分重叠不可交换（Fin 3 见证，与 Lean 同组数）", N9["部分重叠 ⟹ 次序不同结果不同"],
          f"{N9['部分重叠 A={0,1},B={1,2} v=[1,0,0]：先A后B']} vs {N9['部分重叠：先B后A']}")
    check("GCA6b: 嵌套可交换（吸收律，Fin 2 见证，与 Lean 同组数）", N9["嵌套 ⟹ 吸收（次序无关，同结果）"],
          f"{N9['嵌套 A={0}⊂B={0,1} v=[1,1]：先A后B']} vs {N9['嵌套：先B后A']}")

    # ── 图 ──────────────────────────────────────────────────────────────────
    fig, axes = plt.subplots(2, 2, figsize=(13, 9))
    fig.suptitle("控制引力场的代数系统：基元 = 起伏能量（二次型）／布尔边界 = 层状区域族",
                 fontsize=13)

    ax = axes[0][0]
    v = RNG.normal(size=n)
    ax.plot(v, "o-", ms=3, label="原始流动 v")
    ax.plot(flatten(A, v), "s-", ms=3, label="抹平 P_A v（A 内取均值）")
    ax.axvspan(A[0], A[-1], alpha=0.12, color="orange")
    ax.set_title("GCA1/GCA2：一次抹平让 A 内起伏归零（引力关闭）\n"
                 f"Q_A(v)={fluctuation_energy(A, v):.3f} -> Q_A(P_A v)={fluctuation_energy(A, flatten(A, v)):.1e}")
    ax.set_xlabel("空间样本 i"); ax.set_ylabel("流动 v"); ax.legend(fontsize=8)

    ax = axes[0][1]
    shifts = [s["重叠度"] for s in scan]
    coms = [max(s["‖[P_A,P_B]v‖"], 1e-18) for s in scan]
    ax.semilogy(shifts, coms, "o-", color="crimson")
    ax.axhline(1e-12, ls="--", c="gray", lw=1, label="机器精度（= 交换子为零）")
    ax.set_title("GCA6：布尔性的边界\n重叠度 0/1（层状）⟹ 交换子 = 0；部分重叠 ⟹ 顺序进入语义")
    ax.set_xlabel("区域重叠度 |A∩B|/min(|A|,|B|)"); ax.set_ylabel("‖[P_A,P_B]v‖（顺序差）")
    ax.legend(fontsize=8)

    ax = axes[1][0]
    labels = ["不交族\n分配律", "不交族\n格并幂等", "交叠族\n交换子", "交叠族\n格并幂等"]
    vals = [max(dist_disjoint, 1e-18), max(idem_disjoint, 1e-18),
            max(comm_overlap, 1e-18), max(idem_overlap, 1e-18)]
    colors = ["steelblue", "steelblue", "crimson", "crimson"]
    ax.bar(labels, vals, color=colors)
    ax.set_yscale("log")
    ax.axhline(1e-12, ls="--", c="gray", lw=1)
    ax.set_title("N7：布尔子代数 vs 布尔运算失效\n（∧ = 复合，∨ = P+Q−P∘Q）")
    ax.set_ylabel("残差（对数）")
    for i, val in enumerate(vals):
        ax.text(i, val * 1.5, f"{val:.1e}", ha="center", fontsize=8)

    ax = axes[1][1]
    xs = np.arange(3)
    ax.plot(xs, lap[0], "o-", label="先抹 A={0,1} 再抹 B={1,2}")
    ax.plot(xs, lap[1], "s--", label="先抹 B 再抹 A")
    ax.set_xticks(xs)
    ax.set_title(f"GCA6c 见证（v=[1,0,0]，i=1 处 {lap[0][1]:.2f} vs {lap[1][1]:.2f}）\n"
                 "交叠控制：施加次序改变最终引力分布")
    ax.set_xlabel("空间样本 i"); ax.set_ylabel("抹平后的流动"); ax.legend(fontsize=8)

    fig.tight_layout()
    fig.savefig(os.path.join(OUT, "fig_gravity_control.png"), dpi=130)
    plt.close(fig)

    # ── 落盘 ────────────────────────────────────────────────────────────────
    report = {"title": "控制引力场的代数系统（GCA0–GCA7）数值验证",
              "date": str(date.today()),
              "primitive": "起伏能量 Q_A(v) = Σ_{i∈A}(v_i − v̄_A)²（非负二次型）",
              "derivation": "二次型 --极化--> 内积 --正交--> 正交投影 --投影族--> 逻辑；布尔 = 层状区域族（不交或嵌套）",
              "results": results,
              "honest": ["全部为代数恒等/序关系/有限维见证（真但平凡）",
                         "抹平 = 引力关闭属解释层（与弱场 GR 数值不可区分），且只关内部、边界跳变保留",
                         "基元选择由四条判据支撑，不是从公理推出",
                         "控制器的物理实现（μ 主动产生）= 第二输入缺口未变",
                         "无新物理预言"]}
    with open(os.path.join(OUT, "report.json"), "w", encoding="utf-8") as f:
        json.dump(report, f, ensure_ascii=False, indent=2, default=float)

    lines = ["=" * 66,
             "控制引力场的代数系统 —— 数值验证摘要（GCA0–GCA7）",
             "=" * 66,
             "逻辑基元 = 起伏能量（非负二次型）：命题 p_A ⟺ Q_A(v) = 0",
             "推导链：二次型 ->(极化) 内积 ->(正交) 正交投影 ->(投影族) 逻辑运算",
             f"N1 P² = P（幂等，200 场）              : {N1['max|P_A(P_A v) − P_A v| (200 随机场)']:.2e}",
             f"N2 Q ≥ 0 / Q=0 ⟺ 常值 / 抹平后 Q=0     : {N2['min Q_A(v) over 500 随机场']:.3f} / ✓ / {flat_after:.1e}",
             f"N2b 抹平 ⟹ A 内部 ∇Φ 归零（边界保留）   : {before:.4f} -> {after:.2e} / 边界 {boundary_jump:.3f}",
             f"N3 极化恒等式（相对误差）               : {N3['max 相对误差 Q_A(u+v) = Q_A(u)+Q_A(v)+2⟨u,v⟩（200 对）']:.2e}",
             f"N4 起伏 ⟂ 常值                          : {N4['max|⟨起伏, 常值⟩_A|（200 随机场 × 随机常数）']:.2e}",
             f"N5 互补投影对（幂等/正交/完备）         : {max(idP+idQ+ortho+complete):.2e}",
             f"N6 层状 ⟹ 交换子 = 0 / 部分重叠 ⟹ > 0   : {N6['层状族（不交或嵌套）⟹ 交换子 = 0']} / {N6['部分重叠 ⟹ 交换子 > 0（全部）']}",
             f"N7 不交族布尔可化简 / 交叠族失效         : {N7['不交族 = 布尔子代数（分配律 + 格并幂等成立）']} / {N7['交叠族：布尔运算失效（交换子≠0 + 格并非投影）']}",
             f"N8 二次型签名 Q(t·v) = t²Q(v)           : {N8['max 相对误差 Q(t·v) = t²Q(v)（200 随机 (t,v)）']:.2e}",
             f"N9 部分重叠次序不同 / 嵌套吸收           : {lap[0].tolist()} vs {lap[1].tolist()} / {nest[0].tolist()} vs {nest[1].tolist()}",
             "-" * 66,
             "工程含义：控制区域层状（两两不交或嵌套）⟹ 控制程序可像布尔式一样化简与综合；",
             "          区域部分重叠 ⟹ 控制词变成有序词，执行次序进入语义（逐步验证）。",
             "诚实：代数恒等层（真但平凡）；抹平=引力关闭属解释层且只关内部；μ 主动产生=第二输入缺口；无新物理预言。"]
    summary = "\n".join(lines)
    print(summary)
    with open(os.path.join(OUT, "summary.txt"), "w", encoding="utf-8") as f:
        f.write(summary + "\n")

    ok = all(c for _, c in CHECKS)
    print("\nALL CHECKS PASS" if ok else "\nSOME CHECKS FAILED")
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
