#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
胶球质量来源 = 扭量螺旋环（环扭转）验证 —— RT 系列

leo (2026-09-29): 在原来的扭量数学上做**环扭转**,形成比普通螺旋线圈更扭转的
"扭量螺旋环";环本身也带时空的变化 ⟹ 或许可以解释质量来源（胶球的 N 序列）。

这一本账要回答仓库里两个**已标明的缺口**:
  * `theory-twistor.md` TW6:质量 m = |⟨π₁,π₂⟩|（两扭量的相对方向）——缺"谁定这个方向"
  * `artifacts/glueball/report.json`:m² = N·M₀²,N ∈ {3,6,7} 命中格点,但
    "N 序列(3,6,7)与 M₀ 标定是假设/拟合,非第一性预言(第二输入缺口)"

本脚本做三件事（都可核对,不含新物理）:
  RT-A 扭环恒等式实测:环 + 标架 ⟹ **Lk = Tw + Wr**（Călugăreanu–White–Fuller）
       用 Gauss 双积分直接算 Lk 与 Wr,再与给定扭转 Tw 对照。
       顺带实测"双螺旋反向抵消"（+q 与 −q 两条 ⟹ 净 Lk = 0 ⟹ μ = 1 的光子情形）
  RT-B 计数可达性（★ 核心）:N 若是"三个方向的独立绕数"的平方和（对角型 Σnᵢ²),
       **7 取不到**（Legendre 三平方定理:7 = 4⁰(8·0+7) 不可表）⟹
       要给出 N = 7 就必须有**非对角的(集体的)项** ⟹ "环扭转"不是可选项,是必需项。
       给出最小集体规则与它给出的 {3,6,7} 实现,并列出**它同时给出的其它 N**(风险清单)。
  RT-C 与格点/μ 的对接:比值 √3:√6:√7（只比比值,不用绝对标定）；
       以及 μ 的连接数写法 μ = 1 − |Lk_net|/|Lk_gross| 与 FC11 地板 m_e/m_i 的
       数量关系（把"残余连接数"变成一个可数目标）。

诚实边界（与结果同时引用）:
  - 质量 = |⟨π₁,π₂⟩| 是 Penrose 标准结果（仓库 TW6 已标注"复述"）;
  - "扭转 → N" 是**模型选择**:本脚本只**否掉**对角模型、并给出最小集体实现,
    **没有**导出选择规则;M₀ 仍需外部标定;
  - Lk = Tw + Wr 是**经典定理**,本脚本是数值复核,不是新证明;
  - 与格点只比比值（量级校验）,不构成预言。
"""
import json
import math
import os

import numpy as np

REPO = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
OUT = os.path.join(REPO, "artifacts", "glueball_ring_twist")
os.makedirs(OUT, exist_ok=True)

ME_MI_DT = 2.194e-4          # FC11 地板（D-T）
M0_GEV = 0.93                # 仓库口径的标定中值
LATTICE = {"0++": (1.475, 1.75), "2++": (2.15, 2.40), "0-+": (2.30, 2.60)}

report = {
    "title": "胶球质量来源 = 扭量螺旋环（环扭转）",
    "date": "2026-09-29",
    "honest": ["质量=|⟨π₁,π₂⟩| 是 Penrose 标准结果（复述）",
               "扭转→N 是模型选择:只否掉对角模型,未导出选择规则",
               "Lk=Tw+Wr 是经典定理,本脚本是数值复核",
               "与格点只比比值,是量级校验不是预言"],
    "results": {},
}

print("=" * 74)
print("胶球质量来源 = 扭量螺旋环（环扭转）· RT 系列")
print("=" * 74)


# ────────────────────────────── 数值工具 ──────────────────────────────
def gauss_link(c1, c2, eps=1e-9):
    """Gauss 双积分 = 两条闭合曲线的连接数（离散求和近似）。

    Lk = 1/(4π) ∮∮ (r1−r2)·(dr1×dr2)/|r1−r2|³
    """
    r1, r2 = c1, c2
    d1 = np.roll(r1, -1, axis=0) - r1
    d2 = np.roll(r2, -1, axis=0) - r2
    R1 = 0.5 * (r1 + np.roll(r1, -1, axis=0))
    R2 = 0.5 * (r2 + np.roll(r2, -1, axis=0))
    diff = R1[:, None, :] - R2[None, :, :]
    dist = np.linalg.norm(diff, axis=2)
    np.fill_diagonal(dist, np.inf)          # 自项去掉（离散近似惯用）
    dist = np.maximum(dist, eps)
    cross = np.cross(d1[:, None, :], d2[None, :, :])
    # 符号约定:本仓取 cross(d1,d2) 并整体取负,使 q>0 的扭转给出 Lk>0
    # (离散 Gauss 积分的定向与教科书相反,这里显式定死,免得两处互相抵消看不出来)
    num = np.einsum("ijk,ijk->ij", diff, cross)
    return float(np.sum(num / dist ** 3) / (4.0 * math.pi))


def circle(n=721, R=1.0):
    t = np.linspace(0.0, 2.0 * math.pi, n)
    return np.stack([R * np.cos(t), R * np.sin(t), np.zeros_like(t)], axis=1)


def ribbon_from_planar_circle(twist, n=721, R=1.0, w=1.0):
    """平面圆 + 绕环扭转 q 圈（Tw = q）⟹ 两条边;Wr（平面）= 0 ⟹ Lk 应 ≈ q。"""
    t = np.linspace(0.0, 2.0 * math.pi, n)
    base = np.stack([R * np.cos(t), R * np.sin(t), np.zeros_like(t)], axis=1)
    e_r = np.stack([np.cos(t), np.sin(t), np.zeros_like(t)], axis=1)      # 径向
    e_z = np.stack([np.zeros_like(t), np.zeros_like(t), np.ones_like(t)], axis=1)
    ang = twist * t
    m = np.cos(ang)[:, None] * e_r + np.sin(ang)[:, None] * e_z          # 标架
    edge1 = base + 0.5 * w * m
    edge2 = base - 0.5 * w * m
    return base, edge1, edge2


def torus_knot(p, q, n=1201, R1=1.0, R2=0.35):
    t = np.linspace(0.0, 2.0 * math.pi, n)
    r = R1 + R2 * np.cos(q * t)
    return np.stack([r * np.cos(p * t), r * np.sin(p * t), R2 * np.sin(q * t)], axis=1)


def parallel_normal_frame(curve):
    """沿曲线的近似平行标架（避免 Frenet 在拐点翻转）。"""
    T = np.roll(curve, -1, axis=0) - np.roll(curve, 1, axis=0)
    T /= np.linalg.norm(T, axis=1)[:, None]
    ref = np.array([0.0, 0.0, 1.0])
    n0 = np.cross(T[0], ref)
    n0 /= np.linalg.norm(n0)
    N = np.zeros_like(curve)
    N[0] = n0
    for i in range(1, len(curve)):
        v = N[i - 1] - T[i] * np.dot(N[i - 1], T[i])
        nv = np.linalg.norm(v)
        N[i] = v / nv if nv > 1e-12 else N[i - 1]
    B = np.cross(T, N)
    return T, N, B


# ─────────────────────── RT-A 扭环恒等式 Lk = Tw + Wr ───────────────────────
print("\n【RT-A】环 + 标架:Lk = Tw + Wr（Gauss 双积分实测）")

def ribbon_edges_trefoil(p, q, tw_add, n=2401, w=0.15):
    """(p,q) 环面结 + 平行标架 + 额外扭转 tw_add 圈 ⟹ 两条边的曲线。"""
    tk = torus_knot(p, q, n=n)
    _T, N_, B_ = parallel_normal_frame(tk)
    ang = tw_add * np.linspace(0.0, 2.0 * math.pi, n)
    m = np.cos(ang)[:, None] * N_ + np.sin(ang)[:, None] * B_
    return tk, tk + 0.5 * w * m, tk - 0.5 * w * m


SIGN = -1.0     # Gauss 积分定向修正（见 gauss_link 里的注释）
rows_a = []
for q in (1, 2, 3, -2):
    base, e1, e2 = ribbon_from_planar_circle(q)
    Lk = SIGN * gauss_link(e1, e2)
    Wr = SIGN * gauss_link(base, base)   # 平面圆:自拧 = 0
    Tw = Lk - Wr
    _, e1h, e2h = ribbon_from_planar_circle(q, n=1441)      # 收敛性:加密一倍
    Lk_h = SIGN * gauss_link(e1h, e2h)
    rows_a.append({"扭圈数 q": q, "Lk（两边 Gauss）": round(Lk, 4), "拐点加密后 Lk": round(Lk_h, 4),
                   "Wr（曲线自拧）": round(Wr, 4), "Tw = Lk − Wr": round(Tw, 4),
                   "恒等式残差": round(Tw - q, 4)})
    print(f"   平面圆 + 扭转 q={q:+d}:Lk={Lk:+.3f}（加密 {Lk_h:+.3f}） Wr={Wr:+.3f} "
          f"Tw=Lk−Wr={Tw:+.3f}（应 = {q:+d},残差 {Tw - q:+.2e}）")
report["results"]["RT_A_identity_planar"] = {
    "identity": "Lk = Tw + Wr（Călugăreanu–White–Fuller）",
    "rows": rows_a,
    "max|残差|": max(abs(r["恒等式残差"]) for r in rows_a),
    "note": "平面圆 Wr = 0 ⟹ Lk 应等于给定扭转圈数;残差 ~1e-3–1e-2 来自离散化"
            "（N=721 与 1441 两档对照,加密后残差下降 ⟹ 是离散误差不是模型误差）",
}

# 非平面:三叶结（trefoil = (2,3) 环面结）Wr ≠ 0
tk = torus_knot(2, 3, n=2401)
tk_h = torus_knot(2, 3, n=4801)
Wr_tk = SIGN * gauss_link(tk, tk)
T, N_, B_ = parallel_normal_frame(tk)
rows_b = []
lk_list = []
for tw_add in (0.0, -1.0, -2.0):     # 取负 = 与本仓 Lk 定向一致的手性（⟹ ΔLk = +1/圈）
    m = np.zeros_like(tk)
    ang = tw_add * np.linspace(0.0, 2.0 * math.pi, len(tk))
    m = np.cos(ang)[:, None] * N_ + np.sin(ang)[:, None] * B_
    e1 = tk + 0.5 * 0.15 * m
    e2 = tk - 0.5 * 0.15 * m
    Lk = SIGN * gauss_link(e1, e2)
    lk_list.append(Lk)
    rows_b.append({"额外扭转（圈）": tw_add, "Lk（两边 Gauss）": round(Lk, 4),
                   "Tw = Lk − Wr": round(Lk - Wr_tk, 4)})
    print(f"   三叶结（2,3, N=2401）Wr={Wr_tk:+.3f} + 额外扭转 {tw_add:.0f} 圈:"
          f"Lk={Lk:+.3f} ⟹ Tw=Lk−Wr={Lk - Wr_tk:+.3f}")
d1 = lk_list[1] - lk_list[0]
d2 = lk_list[2] - lk_list[1]
print(f"   ★ 干净判据:加一圈扭转 ⟹ ΔLk = {d1:+.4f} / 再加一圈 ⟹ {d2:+.4f}（应 = +1.000,"
      f"与 Wr 无关）")
_, e1h, e2h = ribbon_edges_trefoil(2, 3, 0.0, n=4801, w=0.15)
Lk_h0 = SIGN * gauss_link(e1h, e2h)
Wr_h = SIGN * gauss_link(tk_h, tk_h)
_, e1h1, e2h1 = ribbon_edges_trefoil(2, 3, -1.0, n=4801, w=0.15)
Lk_h1 = SIGN * gauss_link(e1h1, e2h1)
print(f"   （分辨率对照 N=2401 vs 4801:Wr {Wr_tk:+.3f} vs {Wr_h:+.3f};"
      f"Lk(0 圈) {lk_list[0]:+.4f} vs {Lk_h0:+.4f};ΔLk {d1:+.4f} vs {Lk_h1 - Lk_h0:+.4f}）")
report["results"]["RT_A_identity_trefoil"] = {
    "trefoil_Wr (N=2401)": round(Wr_tk, 4), "rows": rows_b,
    "ΔLk 每加一圈扭转": [round(d1, 4), round(d2, 4)],
    "分辨率对照": {"Wr N=2401": round(Wr_tk, 4), "Wr N=4801": round(Wr_h, 4),
                   "Lk(0圈) N=2401": round(lk_list[0], 4), "Lk(0圈) N=4801": round(Lk_h0, 4),
                   "ΔLk N=2401": round(d1, 4), "ΔLk N=4801": round(Lk_h1 - Lk_h0, 4)},
    "note": "非平面曲线 Wr ≠ 0（三叶结 |Wr|≈3）;最干净的判据是 ΔLk:每加一圈扭转 Lk 恰好 +1，"
            "与 Wr 的取值无关 ⟹ 恒等式 Lk = Tw + Wr 在非平面情形同样成立。"
            "**手性约定**:扭转方向相对曲线定向取负号时 ΔLk 才为 +1（⟹ Lk 的符号由手性决定,"
            "这与 μ = 1 − |Lk_net|/|Lk_gross| 取绝对值是自洽的）",
}

# 双螺旋反向抵消 ⟹ μ = 1（光子情形）;同向 ⟹ μ = 0
rows_c = []
for qa, qb in ((1, -1), (2, -2), (1, 1)):
    _, a1, a2 = ribbon_from_planar_circle(qa)
    _, b1, b2 = ribbon_from_planar_circle(qb)
    Lk_a, Lk_b = gauss_link(a1, a2), gauss_link(b1, b2)
    gross = abs(Lk_a) + abs(Lk_b)
    net = abs(Lk_a + Lk_b)
    mu = 1.0 - (net / gross if gross else 0.0)
    rows_c.append({"扭转对": [qa, qb], "Lk_a": round(Lk_a, 3), "Lk_b": round(Lk_b, 3),
                   "μ = 1 − |Lk_net|/|Lk_gross|": round(mu, 4)})
    print(f"   双螺旋对 ({qa:+d},{qb:+d}):Lk={Lk_a:+.3f},{Lk_b:+.3f} ⟹ μ={mu:.4f}")
report["results"]["RT_A_double_helix_mu"] = {
    "definition": "μ = 1 − |Lk_net| / |Lk_gross|",
    "rows": rows_c,
    "note": "反向对 ⟹ 净连接 0 ⟹ μ=1（仓库『双螺旋环向抵消 ⟹ 无质量』的光子情形）;"
            "同向对 ⟹ μ=0。μ=1 需要精确抵消,而精确抵消不是连续可达的",
}


# ─────────────────── RT-B 计数可达性:7 逼出"集体项" ───────────────────
print("\n【RT-B】N 的可达性:对角型（三独立绕数）拿不到 7")


def diagonal_vals(R=6):
    vs = {}
    for a in range(-R, R + 1):
        for b in range(-R, R + 1):
            for c in range(-R, R + 1):
                v = a * a + b * b + c * c
                vs.setdefault(v, (a, b, c))
    return vs


def collective_vals(R=6, allow_triple_anywhere=True):
    """N = Σnᵢ² + |μ̄₃|（三环集体不变量;两两连接为 0 的 Borromean 型）。

    allow_triple_anywhere=True  → 变体 I:μ̄₃ 任何三元组都能取 1
    allow_triple_anywhere=False → 变体 II:μ̄₃ 只在 max|nᵢ| ≥ 2 时允许取 1
                                  （"要出现整体连接,必须有环被扭过两圈以上"）
    """
    vs = {}
    for a in range(-R, R + 1):
        for b in range(-R, R + 1):
            for c in range(-R, R + 1):
                if a == 0 or b == 0 or c == 0:
                    continue                      # 三个方向都要在
                base = a * a + b * b + c * c
                allowed = (0, 1) if (allow_triple_anywhere or max(abs(a), abs(b), abs(c)) >= 2) else (0,)
                for tri in allowed:
                    vs.setdefault(base + tri, (a, b, c, tri))
    return vs


dv, cv = diagonal_vals(), collective_vals()          # cv = 变体 I
cv2 = collective_vals(allow_triple_anywhere=False)   # 变体 II


def first_n(d, k=3):
    """可达值里最小的 k 个（用于对照仓库的 N 序列）。"""
    return sorted(d)[:k]
diag_small = sorted(v for v in dv if v <= 20)
coll_small = sorted(cv)
print(f"   对角型 Σnᵢ² 的可达值（≤20）:{diag_small}")
print(f"   集体型 Σnᵢ²+|μ̄₃| 的可达值（|nᵢ|≥1, ≤20）:{[v for v in coll_small if v <= 20]}")
print(f"   变体 II 可达值（≤20）:{[v for v in sorted(cv2) if v <= 20]}")
print(f"   7 ∈ 对角型?{7 in dv}    7 ∈ 集体型?{7 in cv}")
print(f"   ★ 变体 I  （μ̄₃ 任意）   前三个 N:{first_n(cv)}"
      f"{'  ← 与仓库 {3,6,7} 一致' if first_n(cv) == [3, 6, 7] else '  ✗ 不一致'}")
print(f"   ★ 变体 II （μ̄₃ 需被扭过两圈）前三个 N:{first_n(cv2)}"
      f"{'  ← 与仓库 {3,6,7} 一致' if first_n(cv2) == [3, 6, 7] else '  ✗ 不一致'}")
print(f"   变体 I 多出来的第一个态:N={first_n(cv, 6)[3] if len(first_n(cv, 6)) > 3 else None}"
      f" ⟹ {math.sqrt(first_n(cv, 6)[3]) * M0_GEV:.3f} GeV（格点最轻的奇宇称态在 2.3–2.6 ⟹ 无此态）")
report["results"]["RT_B_reachability"] = {
    "对角型可达（≤20）": diag_small,
    "变体 I（μ̄₃ 任意）前三个 N": first_n(cv),
    "变体 II（μ̄₃ 需 max|nᵢ|≥2）前三个 N": first_n(cv2),
    "仓库观测到的 N 序列": [3, 6, 7],
    "集体型可达（≤20）": [v for v in coll_small if v <= 20],
    "7 在对角型": bool(7 in dv),
    "7 在集体型": bool(7 in cv),
    "选中的变体": "II（μ̄₃ 需要 max|nᵢ| ≥ 2）—— 变体 I 会多出一个 1.86 GeV 的奇宇称态,"
                  "而格点最轻的奇宇称态在 2.3–2.6 GeV ⟹ 数据选 II",
    "对角型最小实现": {str(v): dv[v] for v in [1, 3, 6] if v in dv},
    "集体型最小实现（变体 II）": {str(v): cv2[v] for v in [3, 6, 7] if v in cv2},
    "定理": "Legendre 三平方定理:n 可表为三平方和 ⟺ n ≠ 4^a(8b+7);7 = 4⁰(8·0+7) ⟹ 7 不可表",
    "note": "仓库的 0-+ 态 N=7 ⟹ 只要保留它,任何『三个独立绕数』的模型都被自己的数据否掉 "
            "⟹ 必须引入非对角(集体/Borromean)项 —— 这正是『环扭转』的数学位置",
}

print("\n   最小集体实现（Σnᵢ²+|μ̄₃|）:")
assign = {"0++": 3, "2++": 6, "0-+": 7}
ladder = {}
for state, N in assign.items():
    impl = cv2.get(N) or cv.get(N)
    m = math.sqrt(N) * M0_GEV
    lo, hi = LATTICE[state]
    ladder[state] = {"N": N, "实现 (n₁,n₂,n₃,μ̄₃)": impl, "m = √N·M₀ (GeV)": round(m, 3),
                     "格点区间": [lo, hi], "落区间内": bool(lo <= m <= hi)}
    print(f"     {state}: N={N} 实现={impl} ⟹ m={m:.3f} GeV  格点 {lo}–{hi}  ⟹ {lo <= m <= hi}")
report["results"]["RT_B_ladder"] = ladder


# ───────── RT-C 比值对接 + 集体规则的"多余态"风险清单 ─────────
print("\n【RT-C】与格点只比比值 + 集体规则给出的其它态（风险清单）")
r63 = math.sqrt(6 / 3)
r73 = math.sqrt(7 / 3)
lat_21 = (LATTICE["2++"][0] / LATTICE["0++"][1], LATTICE["2++"][1] / LATTICE["0++"][0])
lat_31 = (LATTICE["0-+"][0] / LATTICE["0++"][1], LATTICE["0-+"][1] / LATTICE["0++"][0])
print(f"   √(6/3) = {r63:.4f}（格点 2++/0++ 区间 {lat_21[0]:.3f}–{lat_21[1]:.3f}）")
print(f"   √(7/3) = {r73:.4f}（格点 0-+/0++ 区间 {lat_31[0]:.3f}–{lat_31[1]:.3f}）")

extra = []
for N in [v for v in sorted(cv2) if 3 < v <= 19]:
    impl = cv2[N]
    extra.append({"N": N, "实现": impl, "m = √N·M₀": round(math.sqrt(N) * M0_GEV, 3),
                  "状态": "已被仓库占用" if N in assign.values() else "未指定 J^PC"})
    print(f"   N={N:2d} 实现={impl} ⟹ {math.sqrt(N) * M0_GEV:.3f} GeV")
report["results"]["RT_C_ratios"] = {
    "√(6/3)": round(r63, 4), "格点 2++/0++ 区间": [round(x, 3) for x in lat_21],
    "√(7/3)": round(r73, 4), "格点 0-+/0++ 区间": [round(x, 3) for x in lat_31],
    "多余态清单（风险：规则过宽）": extra,
    "note": "集体规则能给出 3/6/7 ✓,但也给出 4/5/9/11… ⟹ 选择规则尚未导出;"
            "把多余的 N 当作可证伪的预言,而不是当噪声滤掉",
}

# μ 与 FC11 地板的连接数读法
G_floor = 1.0 / ME_MI_DT
report["results"]["RT_C_mu_floor_linkage"] = {
    "FC11 地板 m_e/m_i": ME_MI_DT,
    "1/(m_e/m_i)": round(G_floor, 2),
    "读法": "若净残余连接数 = 1,则毛连接数 G ≈ 1/(m_e/m_i) ≈ 4558",
    "note": "μ = 1 − |Lk_net|/|Lk_gross| ⟹ 地板 m_e/m_i 等价于『残余/毛 ≈ 2.19e-4』;"
            "这是一个可数目标(不是新物理结论),也是 μ 与 N 用同一个扭转角时的过度决定检验点",
}
print(f"\n   FC11 地板 {ME_MI_DT:.3e} ⟹ 若净残余 = 1 个连接单位,毛连接数 ≈ {G_floor:.0f}")

# ─────── RT-D 多股麻花辫（三股以上）:两两连接数 = q,m 股第一次出现不可交换编织 ───────
def braid_strands(n_strands, twist, n=1401, R=1.0, a=0.19):
    """m 股麻花环:第 k 股 = 核心圆 + 相位错开 2πk/m 的标架偏移。

    每股 s_k(θ) = c(θ) + a[cos(qθ + 2πk/m) e_r + sin(qθ + 2πk/m) e_z]
    ⟹ 相邻股保持固定相位差、互不相交;自连接数（framing）口径下每对连接 q 次。
    """
    th = np.linspace(0.0, 2.0 * math.pi, n)
    base = np.stack([R * np.cos(th), R * np.sin(th), np.zeros_like(th)], axis=1)
    e_r = np.stack([np.cos(th), np.sin(th), np.zeros_like(th)], axis=1)
    e_z = np.stack([np.zeros_like(th), np.zeros_like(th), np.ones_like(th)], axis=1)
    out = []
    for k in range(n_strands):
        ph = twist * th + 2.0 * math.pi * k / n_strands
        out.append(base + a * (np.cos(ph)[:, None] * e_r + np.sin(ph)[:, None] * e_z))
    return base, out


print("\n   RT-D 多股麻花辫:两两连接数（Gauss 双积分,自连接口径）")
rows_d = []
for m, q in ((2, 1), (2, 2), (2, 3), (3, 1), (3, 2), (4, 1), (4, 2)):
    _b, st = braid_strands(m, q)
    lks = [SIGN * gauss_link(st[i], st[j]) for i in range(m) for j in range(i + 1, m)]
    dev = max(abs(v - q) for v in lks)
    rows_d.append({"股数 m": m, "扭转 q": q,
                   "两两连接数": [round(v, 4) for v in lks],
                   "max|Lk − q|": round(dev, 4), "对数": len(lks)})
    print(f"    m={m} 股 × q={q}:Lk(每对) = {[round(v, 3) for v in lks]}"
          f"（应 = {q},max|偏差| = {dev:.4f}）")

# 收敛性:对最密的 (m,q) = (4,2) 加密一倍复核
_b2, st2 = braid_strands(4, 2, n=2801)
lk_fine = [SIGN * gauss_link(st2[i], st2[j]) for i in range(4) for j in range(i + 1, 4)]
dev_fine = max(abs(v - 2) for v in lk_fine)
print(f"    收敛性 (4 股, q=2):N=1401 max|偏差| = {rows_d[-1]['max|Lk − q|']:.4f} ⟹ "
      f"N=2801 = {dev_fine:.4f}")

# 三股第一次出现**不可交换**的编织生成元:σ1σ2 ≠ σ2σ1（与 TD15–TD17「顺序不可交换」同源）
report["results"]["RT_D_braid"] = {
    "公式": "s_k(θ) = c(θ) + a[cos(qθ + 2πk/m) e_r + sin(qθ + 2πk/m) e_z]",
    "rows": rows_d,
    "收敛性 (4 股 q=2)": {"N=1401": rows_d[-1]["max|Lk − q|"], "N=2801": round(dev_fine, 4)},
    "成对连接总数 Σ_{i<j} Lk": {f"m={r['股数 m']}, q={r['扭转 q']}": round(r["对数"] * r["扭转 q"], 3)
                                for r in rows_d},
    "note": "m 股(每条都带同一 q 扭转)⟹ 两两连接数都 = q(实测,偏差 ~1e-3–1e-2 为离散误差);"
            "m ≥ 3 第一次出现**不可交换**的编织生成元 σ1σ2 ≠ σ2σ1 ⟹ 与仓库 TD15–TD17"
            "「顺序不可交换」同源。**诚实缺口**:这里量的是两两(二阶)部分;真正的三阶集体量"
            "（Massey 三重积 / Milnor μ̄₃）本脚本**没有数值算法**,只在上界口径下用 μ̄₃ ∈ {0,1} 记账。",
}

# ─────── RT-E 与真实胶球谱逐条对位（格点数 + 实验候选；**我们这边零 QCD 输入**）───────
# 来源：TABLE XXI of "Glueball masses from the lattice: a (partial) review of recent results"
#       （物理单位，标度 r₀⁻¹ = 410(20) MeV；误差 = 统计(连续外推) + 各向异性 ~1%）
LATTICE_SPECTRUM = [("0++", 1710, 50, 80), ("2++", 2390, 30, 120), ("0-+", 2560, 35, 120),
           ("1+-", 2980, 30, 140), ("2-+", 3040, 40, 150), ("3+-", 3600, 40, 170),
           ("3++", 3670, 50, 180)]
LATTICE_0s = ("0*++", 2670, 180, 130)   # Morningstar–Peardon PRD 60, 034509 (1999)
X2370 = {"源": "BESIII, PRL 132, 181901 (2024)（11.7σ）", "M": 2395, "M_err": (11, 26, -94),
         "Γ": 188, "Γ_err": (18, 17, 124, -33), "JPC": "0-+"}
SQRT_SIGMA = 445.0      # MeV，格点弦张力（√σ ≈ 440–445 MeV）

# 可达集（变体 II）按升序取，与格点态按质量升序一一对位（**无选择自由度**：两边都排序）
order_e = [v for v in sorted(cv2)]
pairs = list(zip(LATTICE_SPECTRUM, order_e))
implied_m0 = [m / math.sqrt(N) for (_st, m, _e1, _e2), N in pairs]
mean_m0 = sum(implied_m0) / len(implied_m0)
scatter_pct = (max(implied_m0) - min(implied_m0)) / 2.0 / mean_m0 * 100.0
m0_5 = implied_m0[:5]
mean5 = sum(m0_5) / 5.0
scatter5 = (max(m0_5) - min(m0_5)) / 2.0 / mean5 * 100.0

print("\n   RT-E 与格点胶球谱对位（我们：N = Σnᵢ² + |μ̄₃| 的升序阶梯；格点：TABLE XXI）")
rows_e = []
for (st, m, e1, e2), N in pairs:
    M0_impl = m / math.sqrt(N)
    pred = math.sqrt(N) * mean5
    rows_e.append({"J^PC": st, "格点 M (MeV)": m, "格点误差 ±(统计+系统)": e1 + e2, "指派 N": N,
                   "反推 M₀ = M/√N": round(M0_impl, 1),
                   "用 M₀=%.1f 回算" % mean5: round(pred, 1),
                   "偏差 %": round((pred - m) / m * 100, 2),
                   "落在格点误差内": bool(abs(pred - m) <= e1 + e2)})
    print(f"    {st:5s} 格点 {m}±{e1+e2:<3d} ⟹ N = {N:2d} ⟹ 反推 M₀ = {M0_impl:6.1f} MeV；"
          f"M₀={mean5:.1f} 回算 {pred:6.1f}（{(pred-m)/m*100:+5.2f}%）"
          f"{' ✓' if abs(pred-m) <= e1+e2 else ' ✗'}")

# 只比比值（完全不依赖 M₀）
ratios_e = []
for (st, m, _e1, _e2), N in pairs[1:]:
    ours, lat = math.sqrt(N / 3.0), m / LATTICE_SPECTRUM[0][1]
    ratios_e.append({"J^PC/0++": st, "我们 √(N/3)": round(ours, 4), "格点": round(lat, 4),
                     "偏差 %": round((ours / lat - 1.0) * 100, 2)})
    print(f"    {st:5s}/0++：我们 {ours:.4f} vs 格点 {lat:.4f}（{(ours/lat-1)*100:+.2f}%）")

# 拟合不是空转：换成「连续整数」或「最朴素的 1..5」做同样的反推，离散要大得多
def scatter_of(nums):
    m0s = [m / math.sqrt(n) for (_st, m, _e1, _e2), n in zip(LATTICE_SPECTRUM[:5], nums)]
    mu = sum(m0s) / 5.0
    return (max(m0s) - min(m0s)) / 2.0 / mu * 100.0, m0s


base_cont, _ = scatter_of([3, 4, 5, 6, 7])
base_naive, _ = scatter_of([1, 2, 3, 4, 5])
print(f"    拟合不是空转：我们集(3,6,7,9,10) 反推 M₀ 离散 ±{scatter5:.2f}%；"
      f"连续整数(3..7) ±{base_cont:.2f}%；最朴素(1..5) ±{base_naive:.2f}%")

# 不符的那一个
st0, m0v, e1_0, e2_0 = LATTICE_0s
n_impl = (m0v / mean5) ** 2
near_n = min(sorted(cv2), key=lambda v: abs(v - n_impl))
print(f"    ✗ {st0} 格点 {m0v}±{e1_0+e2_0} ⟹ 反推 N = {n_impl:.2f}（非整数）；"
      f"最近阶梯 N={near_n} → {math.sqrt(near_n)*mean5:.0f} MeV ⟹ 阶梯在 2.59–2.93 GeV 之间没有态")

# 与最新实验候选的张力
n_x = (X2370["M"] / mean5) ** 2
print(f"    ⚠ X(2370)（{X2370['JPC']}, {X2370['M']} MeV, Γ = {X2370['Γ']} MeV, BESIII 2024）"
      f"⟹ 反推 N = {n_x:.2f} ⟹ 落在 N=6（我们的 2++ 槽）；我们的 0-+ 预言 = "
      f"{math.sqrt(7)*mean5:.0f} MeV（高 {math.sqrt(7)*mean5 - X2370['M']:.0f} MeV）")

# 尺度锚点：弦张力
ratio_sigma = LATTICE_SPECTRUM[0][1] / SQRT_SIGMA
print(f"    尺度锚点：m(0++)/√σ = {ratio_sigma:.2f}（√σ = {SQRT_SIGMA} MeV）⟹ "
      f"M₀ ≈ {LATTICE_SPECTRUM[0][1]/math.sqrt(3)/SQRT_SIGMA:.2f}·√σ = {LATTICE_SPECTRUM[0][1]/math.sqrt(3):.0f} MeV")

# ── 第二套独立格点数据（Athenodorou–Teper, JHEP 11 (2020) 172, Table 17：M_G/√σ 的连续极限）──
# 目的：TABLE XXI（r₀⁻¹ = 410 MeV 约定）与这套（r₀√σ = 1.160(6)）的绝对标度差 ~3%，
#       两套各自内部一致 ⟹ 用两套分别拟合，看 M₀ 是否随标度约定一起平移（稳健性检验）。
R0SQRT_SIGMA = (1.160, 0.006)          # r₀√σ
R0_INV_MEV = 410.0                     # MeV（与 TABLE XXI 同一约定）
SQRT_SIGMA_AT = R0SQRT_SIGMA[0] * R0_INV_MEV
AT = [("0++", 3.405, 0.021), ("2++", 4.894, 0.022), ("0-+", 5.276, 0.045),
      ("1+-", 6.065, 0.040), ("2-+", 6.32, 0.09), ("(2++ ex1)", 6.788, 0.040),
      ("3+-", 7.27, 0.12), ("3++", 7.71, 0.09)]
at_M = [(st, v * SQRT_SIGMA_AT, e * SQRT_SIGMA_AT) for st, v, e in AT]
at5 = [m for (_st, m, _e) in at_M[:5]]
at_ns = [3, 6, 7, 9, 10]
at_m0 = [m / math.sqrt(n) for m, n in zip(at5, at_ns)]
at_mean = sum(at_m0) / 5.0
at_scatter = (max(at_m0) - min(at_m0)) / 2.0 / at_mean * 100.0
print(f"\n   RT-E6 第二套数据（Athenodorou–Teper 2020, M_G/√σ；√σ = {SQRT_SIGMA_AT:.1f} MeV）：")
for (st, m, e), n, m0 in zip(at_M[:5], at_ns, at_m0):
    print(f"    {st:5s} {m:6.0f}±{e:4.0f} MeV ⟹ N = {n:2d} ⟹ 反推 M₀ = {m0:6.1f} MeV")
print(f"    ⟹ 单一 M₀ = {at_mean:.1f} MeV，五态散布 ±{at_scatter:.2f}%"
      f"（与 TABLE XXI 的 {mean5:.1f} MeV / ±{scatter5:.2f}% 相比：M₀ 随格点标度约定一起平移）")
st_ex, m_ex, e_ex = at_M[5]
n_ex = (m_ex / at_mean) ** 2
print(f"    ★ 阶梯被跳过的 N=11：我们 → {math.sqrt(11)*at_mean:.0f} MeV；"
      f"({st_ex}) 格点 {m_ex:.0f}±{e_ex:.0f} MeV ⟹ 反推 N = {n_ex:.2f}"
      f"（Δ = {(math.sqrt(11)*at_mean - m_ex)/m_ex*100:+.2f}%）⟹ 3.2–3.4 GeV 的空隙在这套数据里有对应态")

report["results"]["RT_E_lattice"] = {
    "格点来源": "TABLE XXI, 'Glueball masses from the lattice: a (partial) review of recent results'"
                "（r₀⁻¹ = 410(20) MeV）；0*++ 另取 Morningstar–Peardon PRD 60, 034509 (1999)",
    "实验候选": X2370,
    "对位（按质量升序，两边都排序 ⟹ 无选择自由度）": rows_e,
    "只比比值": ratios_e,
    "单一常数": {"M₀（前五态反推均值）": round(mean5, 1),
                 "反推散布 ±%": round(scatter5, 2),
                 "五态各自反推 M₀": [round(x, 1) for x in implied_m0[:5]]},
    "拟合非空转对照（反推 M₀ 离散）": {"我们的 3,6,7,9,10": round(scatter5, 2),
                                        "连续整数 3..7": round(base_cont, 2),
                                        "最朴素 1..5": round(base_naive, 2)},
    "不符": {st0: {"格点 M": m0v, "反推 N（非整数）": round(n_impl, 2),
                   "最近阶梯": near_n, "note": "阶梯在 2.59–2.93 GeV 之间没有态；"
                   "要么我们的规则漏了一个态，要么该态不是单胶球（原论文自己提醒要区分 two-glueball/torelon）"}},
    "张力": {"X(2370)": {"M": X2370["M"], "反推 N": round(n_x, 2),
                         "落在哪": "N = 6（我们的 2++ 槽）",
                         "我们的 0-+ 预言": round(math.sqrt(7) * mean5, 0),
                         "note": "X(2370) 比我们的 0-+ 低 ~190 MeV；要么它不是那个 0-+ 胶球"
                                 "（或含混合成分），要么我们按质量序的 J^PC 指配是错的"}},
    "尺度锚点": {"m(0++)/√σ（格点）": round(ratio_sigma, 2), "√σ (MeV)": SQRT_SIGMA,
                 "M₀/√σ": round(LATTICE_SPECTRUM[0][1] / math.sqrt(3) / SQRT_SIGMA, 2)},
    "第二套格点（Athenodorou–Teper 2020, M_G/√σ）": {
        "源": "JHEP 11 (2020) 172, Table 17（连续极限，M_G/√σ；r₀√σ = 1.160(6)，取 r₀⁻¹ = 410 MeV ⟹ √σ = %.1f MeV）" % SQRT_SIGMA_AT,
        "五态反推 M₀": [round(x, 1) for x in at_m0],
        "单一 M₀": round(at_mean, 1), "散布 ±%": round(at_scatter, 2),
        "与 TABLE XXI 对比": {"TABLE XXI M₀": round(mean5, 1), "散布": round(scatter5, 2)},
        "被跳过的 N=11 的对位": {"我们": round(math.sqrt(11) * at_mean), "格点态": st_ex,
                                 "格点 M (MeV)": round(m_ex), "反推 N": round(n_ex, 2),
                                 "偏差 %": round((math.sqrt(11) * at_mean - m_ex) / m_ex * 100, 2),
                                 "σ 数": round((m_ex - math.sqrt(11) * at_mean) / (0.040 * SQRT_SIGMA_AT), 1),
                                 "判读": "该态落在阶梯两档（N=11 → %.0f、N=12 → %.0f）**之间**："
                                         "与低档差 %+.2f%%、与高档差 %+.2f%% ⟹ 既非命中也不在格点上"
                                         "（19 MeV 的格点误差下这是 %.1fσ 的偏离）⟹ 空隙**没有被填上**，"
                                         "RT-E7 只记录『这里确实有激发态』，不算命中" % (
                                             math.sqrt(11) * at_mean, math.sqrt(12) * at_mean,
                                             (math.sqrt(11) * at_mean - m_ex) / m_ex * 100,
                                             (math.sqrt(12) * at_mean - m_ex) / m_ex * 100,
                                             abs(m_ex - math.sqrt(11) * at_mean) / (0.040 * SQRT_SIGMA_AT))},
    },
    "诚实边界": "我们这边零 QCD 输入：N 阶梯与 M₀ 都是本仓自己的模型选择；格点误差 ±(50–180) MeV 量级，"
                "所以「偏差 ≤1.6%」不等于「精度 1.6%」——只能说**全部落在格点误差带内**；"
                "自旋/宇称不是算出来的（J^PC 是按质量序指派的）；宽度/衰变/产生率完全没碰；"
                "比的是淬火（纯规范）格点，对「纯胶」对象是合适的参照，但真实世界有夸克混合。",
}

# ─────── RT-F ① J^PC 能不能从几何**导出**（穷举否定）+ ② 全谱命中率 + ③ 两个具体点 ───────
# 数据：Athenodorou–Teper, JHEP 11 (2020) 172, Table 17（连续极限，M_G/√σ），
#       = 该文能识别 J^PC 的全部 20 个态；星号为其自己的拟合质量旗标（* 一般，** 显著不确定）。
AT_ALL = [  # (J^PC, M/√σ, 误差, 旗标)
    ("0++",   3.405, 0.021, ""), ("0-+",   5.276, 0.045, ""),
    ("0*++",  5.855, 0.041, ""), ("0*-+",  7.29,  0.13,  ""),
    ("2++",   4.894, 0.022, ""), ("2-+",   6.32,  0.09,  ""),
    ("2+-",   8.74,  0.12,  "*"), ("2--",  8.08,  0.15,  ""),
    ("2*++",  6.788, 0.040, ""), ("2*-+",  8.18,  0.08,  ""),
    ("1-+",   8.48,  0.12,  ""), ("1+-",   6.065, 0.040, ""), ("1--", 8.31, 0.10, ""),
    ("1*-+",  8.57,  0.13,  "*"), ("1*+-", 7.82,  0.06,  ""),
    ("1**-+", 8.66,  0.15,  "*"),
    ("3++",   7.71,  0.09,  "*"), ("3+-",  7.27,  0.12,  ""),
    ("4++",   7.60,  0.12,  "*"), ("4+-",  9.02,  0.10,  "**"),
]
SQ_AT = R0SQRT_SIGMA[0] * R0_INV_MEV            # 475.6 MeV
M0_AT = at_mean                                  # 949.1 MeV（RT-E6 拟出）

# ── ① J^PC 导出性：穷举「两个自然 ℤ₂ 不变量」的所有线性规则 ──
# 几何能给的不变量只有两个：a = Σ|nᵢ| mod 2（总绕数奇偶）、b = μ̄₃（集体连接）
# 候选规则族：P = (−1)^(a·e1 + b·e2 + d1)，C = (−1)^(a·z1 + b·z2 + d2)，e,z,d ∈ {0,1} ⟹ 64 种
# 判定：按质量升序把阶梯前 7 项与格点最轻 7 个态对位，要求**J 由规则给出且 P,C 全中**
ladder7 = [(3, (1, 1, 1, 0)), (6, (2, 1, 1, 0)), (7, (2, 1, 1, 1)), (9, (2, 2, 1, 0)),
           (10, (2, 2, 1, 1)), (13, (2, 2, 2, 1)), (14, (3, 2, 1, 0))]
lat7_pc = [("0", "+", "+"), ("2", "+", "+"), ("0", "-", "+"), ("1", "+", "-"),
           ("2", "-", "+"), ("3", "+", "-"), ("3", "+", "+")]
J_RULES = {
    "J=Σ(|nᵢ|−1)": lambda n: sum(abs(x) - 1 for x in n[:3]),
    "J=max|nᵢ|−1": lambda n: max(abs(x) for x in n[:3]) - 1,
    "J=|n₁|+|n₂|−|n₃|−1": lambda n: abs(n[0]) + abs(n[1]) - abs(n[2]) - 1,
    "J=Σ|nᵢ|−3+|μ̄₃|": lambda n: sum(abs(x) for x in n[:3]) - 3 + n[3],
}
best = None
hits_table = []
for jname, jf in J_RULES.items():
    for e1 in (0, 1):
        for e2 in (0, 1):
            for d1 in (0, 1):
                for z1 in (0, 1):
                    for z2 in (0, 1):
                        for d2 in (0, 1):
                            ok = 0
                            for (_N, impl), (Jlat, Plat, Clat) in zip(ladder7, lat7_pc):
                                n = impl
                                a = sum(abs(x) for x in n[:3]) % 2
                                b = n[3]
                                P = -1 if (a * e1 + b * e2 + d1) % 2 else 1
                                C = -1 if (a * z1 + b * z2 + d2) % 2 else 1
                                J = jf(n)
                                good = (str(abs(J)) == Jlat) and (("+" if P > 0 else "-") == Plat) \
                                       and (("+" if C > 0 else "-") == Clat)
                                ok += int(good)
                            hits_table.append((jname, (e1, e2, d1), (z1, z2, d2), ok))
                            if best is None or ok > best[-1]:
                                best = (jname, (e1, e2, d1), (z1, z2, d2), ok)
tot_rules = len(hits_table)
print(f"\n   RT-F ① J^PC 导出性:穷举 {tot_rules} 条「两个 ℤ₂ 不变量的线性规则」（4 个 J 候选 × 64 个奇偶指配）")
print(f"    最好的一条命中 {best[3]}/7 项（J 规则 = {best[0]}；P 用 (e1,e2,d1) = {best[1]}；"
      f"C 用 (z1,z2,d2) = {best[2]}）")
full = [h for h in hits_table if h[3] == 7]
print(f"    能全中 7 项的规则数 = {len(full)} ⟹ "
      f"{'存在' if full else '**不存在**（在这个规则族里 J^PC 无法从 (Σ|nᵢ| mod 2, μ̄₃) 线性导出）'}")
# 结构性理由：格点出现的 (P,C) 组合有 4 种
combos = sorted({(p, c) for (_J, p, c) in lat7_pc})
print(f"    格点最轻 7 态出现 {len(combos)} 种 (P,C) 组合：{combos}；"
      f"而两个 ℤ₂ 不变量的线性规则最多也只能给 4 种 ⟹ 局限不在「组合数不够」而在**指配不上**")

# ── ② 全谱命中率 + 随机基线 ──
import random
random.seed(20260929)
rows_f = []
for st, v, e, star in AT_ALL:
    M = v * SQ_AT
    err = e * SQ_AT
    n_impl = (M / M0_AT) ** 2
    near = min(sorted(cv2), key=lambda x: abs(x - n_impl))
    pred = math.sqrt(near) * M0_AT
    rows_f.append({"J^PC": st, "M (MeV)": round(M), "±": round(err), "旗标": star,
                   "反推 N": round(n_impl, 2), "最近阶梯 N": near, "阶梯预言 (MeV)": round(pred),
                   "偏差 (MeV)": round(pred - M), "命中 1σ": bool(abs(pred - M) <= err),
                   "命中 2σ": bool(abs(pred - M) <= 2 * err)})
n1 = sum(r["命中 1σ"] for r in rows_f)
n2 = sum(r["命中 2σ"] for r in rows_f)
print(f"\n   RT-F ② 全谱（{len(rows_f)} 个可识别 J^PC 态）命中率：1σ 内 {n1}/{len(rows_f)} = "
      f"{n1/len(rows_f)*100:.0f}%；2σ 内 {n2}/{len(rows_f)} = {n2/len(rows_f)*100:.0f}%")

# 随机基线：同样的阶梯，拿 20 个随机质量（落在数据跨度内）比
lo, hi = min(r["M (MeV)"] for r in rows_f), max(r["M (MeV)"] for r in rows_f)
rel_errs = [e * SQ_AT / (v * SQ_AT) for (_st, v, e, _s) in AT_ALL]      # 与数据同分布的相对误差
trials, base1, base1w = 20000, 0, 0
for _ in range(trials):
    c = cw = 0
    for _k in range(len(rows_f)):
        M = random.uniform(lo, hi)
        err = random.choice(rel_errs) * M
        n_imp = (M / M0_AT) ** 2
        nr = min(sorted(cv2), key=lambda x: abs(x - n_imp))
        if abs(math.sqrt(nr) * M0_AT - M) <= err:
            c += 1
        if abs(math.sqrt(nr) * M0_AT - M) <= 0.03 * M:      # 3% 宽口径（对照）
            cw += 1
    base1 += c
    base1w += cw
base_pct = base1 / trials / len(rows_f) * 100
base_pct_w = base1w / trials / len(rows_f) * 100
print(f"    随机基线（{trials} 次 × {len(rows_f)} 个随机质量，**误差与数据同分布**）：{base_pct:.1f}%"
      f"；宽口径（3% 误差）{base_pct_w:.1f}% ⟹ 我们 {n1/len(rows_f)*100:.0f}% vs 随机 {base_pct:.1f}%"
      f"（宽口径 {base_pct_w:.1f}%）")
# 旗标相关性（③）
clean = [r for r in rows_f if r["旗标"] == ""]
star = [r for r in rows_f if r["旗标"] != ""]
print(f"    ③ 旗标相关性：格点自己标「好拟合」的 {len(clean)} 个态命中 {sum(r['命中 1σ'] for r in clean)} 个"
      f"（{sum(r['命中 1σ'] for r in clean)/len(clean)*100:.0f}%）；标了星的 {len(star)} 个态命中 "
      f"{sum(r['命中 1σ'] for r in star)} 个（{sum(r['命中 1σ'] for r in star)/len(star)*100:.0f}%）")
for st in ("0*++", "2*++"):
    r = [x for x in rows_f if x["J^PC"] == st][0]
    print("    ③ {st}：格点 {m}±{e} MeV，反推 N = {n}（最近阶梯 N={nn} → {p} MeV，偏差 {d:+d} MeV，旗标 [{f}]）"
          .format(st=st, m=r["M (MeV)"], e=r["±"], n=r["反推 N"], nn=r["最近阶梯 N"],
                  p=r["阶梯预言 (MeV)"], d=r["偏差 (MeV)"], f=r["旗标"] or "无"))

report["results"]["RT_F_jpc_and_fullspectrum"] = {
    "① J^PC 导出性（穷举）": {
        "规则族": "P = (−1)^(a·e1+b·e2+d1)、C = (−1)^(a·z1+b·z2+d2)，其中 a = Σ|nᵢ| mod 2、b = μ̄₃；"
                  "J 取 4 个几何候选（Σ(|nᵢ|−1) / max|nᵢ|−1 / |n₁|+|n₂|−|n₃|−1 / Σ|nᵢ|−3+μ̄₃）",
        "穷举条数": tot_rules,
        "最好命中": f"{best[3]}/7（{best[0]}）",
        "全中条数": len(full),
        "结论": "**不存在**能复现格点最轻 7 态 J^PC 的规则 ⟹ J^PC 仍**不可从 (Σ|nᵢ| mod 2, μ̄₃) 导出**；"
                "格点谱里 4 种 (P,C) 组合都出现，而几何只提供两个 ℤ₂ ⟹ 指配上无解（不是组合数不够）",
    },
    "② 全谱命中率": {
        "数据": "Athenodorou–Teper JHEP 11 (2020) 172, Table 17（20 个可识别 J^PC 态）",
        "1σ 命中": f"{n1}/{len(rows_f)}", "2σ 命中": f"{n2}/{len(rows_f)}",
        "随机基线（误差与数据同分布）%": round(base_pct, 1),
        "随机基线（宽口径 3% 误差）%": round(base_pct_w, 1),
        "行": rows_f,
    },
    "③ 旗标相关性": {
        "格点标「好拟合」的态": {"个数": len(clean), "命中 1σ": sum(r["命中 1σ"] for r in clean)},
        "格点标星（拟合一般/不确定）的态": {"个数": len(star), "命中 1σ": sum(r["命中 1σ"] for r in star)},
        "读法": "若漏掉的态集中在标星者 ⟹ 可用格点自身的不确定性解释；若集中在干净态 ⟹ 是真实的否证点",
    },
    "诚实边界": "命中率只说明「阶梯的格子密度与格点谱的分布是否相容」，不等于物理吻合；"
                "对位用的是**质量升序**（因为 J^PC 不可导出，见 ①），所以 ② 的命中率仍带对位自由度；"
                "随机基线用的是均匀分布而不是真实谱的先验分布，只作量级参照。",
}

# ────────────────────────────── 图 ──────────────────────────────
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
import matplotlib.font_manager as fm

# 中文字体（与仓库其它绘图脚本同一套:先 PingFang 再 Hiragino）
for _fp in ("/System/Library/Fonts/PingFang.ttc",
            "/System/Library/Fonts/Hiragino Sans GB.ttc"):
    if os.path.exists(_fp):
        fm.fontManager.addfont(_fp)
        plt.rcParams["font.sans-serif"] = [fm.FontProperties(fname=_fp).get_name()]
        break
plt.rcParams["axes.unicode_minus"] = False

fig = plt.figure(figsize=(15, 4.6))
ax1 = fig.add_subplot(1, 3, 1, projection="3d")
base, e1, e2 = ribbon_from_planar_circle(3, n=361)
ax1.plot(base[:, 0], base[:, 1], base[:, 2], "k--", lw=1, label="环轴（基础曲线）")
ax1.plot(e1[:, 0], e1[:, 1], e1[:, 2], "#c0392b", lw=1.6, label="边 1（螺旋）")
ax1.plot(e2[:, 0], e2[:, 1], e2[:, 2], "#2471a3", lw=1.6, label="边 2（反向螺旋）")
ax1.set_title("RT-A:环 + 标架 → Lk = Tw + Wr\n(Tw=3, Wr=0 → Lk=3)", fontsize=10)
ax1.legend(fontsize=7, loc="upper right")
ax1.set_axis_off()

ax2 = fig.add_subplot(1, 3, 2)
vals = sorted(set(list(dv.keys()) + list(cv.keys())))
ax2.scatter([v for v in diag_small], [1.0] * len(diag_small), c="#2471a3", s=28,
            label="对角型 Σn_i²（三独立绕数）")
ax2.scatter([v for v in coll_small if v <= 20], [0.0] * len([v for v in coll_small if v <= 20]),
            c="#c0392b", s=28, label="集体型 Σn_i²+|μ̄₃|（三环整体）")
ax2.axvline(7, color="k", ls=":", lw=1)
ax2.annotate("N=7 对角型拿不到\n(Legendre 三平方定理)", xy=(7, 0.5), xytext=(8.5, 0.55),
             fontsize=8, arrowprops=dict(arrowstyle="->", lw=0.8))
ax2.set_yticks([0, 1])
ax2.set_yticklabels(["集体", "对角"], fontsize=9)
ax2.set_xlabel("N（质量² 的条数因子）")
ax2.set_title("RT-B:N 的可达值\n(仓库 0-+ 的 N=7 逼出集体项)", fontsize=10)
ax2.legend(fontsize=7, loc="lower right")
ax2.grid(alpha=0.25)

ax3 = fig.add_subplot(1, 3, 3)
Ns = [3, 6, 7]
ms = [math.sqrt(N) * M0_GEV for N in Ns]
for i, st in enumerate(["0++", "2++", "0-+"]):
    lo, hi = LATTICE[st]
    ax3.fill_betweenx([i - 0.3, i + 0.3], lo, hi, color="#95a5a6", alpha=0.45)
    ax3.plot([ms[i]], [i], "o", color="#c0392b", ms=8)
    ax3.text(ms[i] + 0.03, i, f"{st}\nN={Ns[i]}", fontsize=8, va="center")
ax3.set_yticks([])
ax3.set_xlabel("m = √N·M₀ (GeV),M₀=0.93")
ax3.set_title("RT-C:与格点只比比值\n(灰带 = 格点观测区间)", fontsize=10)
ax3.grid(alpha=0.25, axis="x")

plt.tight_layout()
fig_path = os.path.join(OUT, "fig_ring_twist.png")
plt.savefig(fig_path, dpi=130)
plt.close()

with open(os.path.join(OUT, "report.json"), "w", encoding="utf-8") as f:
    json.dump(report, f, ensure_ascii=False, indent=2)

print("\n" + "-" * 74)
print(f"图 → {fig_path}")
print(f"报告 → {os.path.join(OUT, 'report.json')}")
print("RT 结论:① Lk = Tw + Wr 数值复核成立（平面残差 ~1e-3–1e-2,加密后下降 ⟹ 离散误差;"
      "非平面用 ΔLk=+1/圈 这条与 Wr 无关的判据）;"
      "② 7 ∉ 三平方和 ⟹ 对角模型被仓库自己的 N=7 否掉 ⟹ 必须集体项;"
      "③ 比值 √3:√6:√7 落在格点区间（量级校验）;"
      "④ 变体 II 仍给出 9/10/11/12… 这些多余态 ⟹ 选择规则仍未导出（诚实缺口）;"
      "⑤ m 股麻花辫:m ≥ 3 才出现不可交换编织（σ1σ2 ≠ σ2σ1）；"
      "⑥ 与格点胶球谱对位（RT-E）：最轻五个态按质量序对上 N = 3,6,7,9,10，单一 M₀ 散布 ±%.2f%%，"
      "全部落在格点误差内；0*++ 反推 N = %.2f（非整数）⟹ 登记为不符；X(2370) 反推 N ≈ %.2f ⟹ 登记张力。"
      % (report["results"]["RT_E_lattice"]["单一常数"]["反推散布 ±%"],
         report["results"]["RT_E_lattice"]["不符"]["0*++"]["反推 N（非整数）"],
         report["results"]["RT_E_lattice"]["张力"]["X(2370)"]["反推 N"]))
