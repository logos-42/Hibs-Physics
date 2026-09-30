#!/usr/bin/env python3
"""把「改变净连接数是**非局部**的」落成可算的东西（MT-N1…MT-N6）。

leo（2026-09-30）：承认「改变必须是非局部的」这一支。于是要把口头前提变成
可算、可证、可否证的三件东西：

  ① 载体（组合 ↔ 几何对齐）：闭辫的链接数由辫词的**指数和** e 承载 ——
     e = 2·Σ_{i<j}Lk（RT-D 实测的几何数），脚本读 RT-D 的报告来复核这条对齐。
  ② **局部 vs 非局部**（精确整数）：
       局部变形（braid 关系式、共轭、循环置换）⟹ e 不变；
       改变计数（加/减股 = Markov 稳定化、改幂次）⟹ e 变 ±1。
     ⟹ 「非局部」的可算定义 = **改指数和**。
  ③ 代价语义变更：局部不可达 ⟹ 代价不是"微分价格"，而是**拓扑事件的阈值能量**
     （装置级场能量级），并把它与 RT-H4「股数随态变」交叉核对。

诚实边界：e = 2ΣLk 来自数值（Gauss 双积分，有离散误差）；阈值代价是**量级估计**
（层厚假设跨度 500×）；物理学侧"非局部 = 重联这类拓扑事件"是标准读法，本脚本不证它。
"""

from __future__ import annotations

import itertools
import json
import math
import pathlib
import sys

ROOT = pathlib.Path(__file__).resolve().parents[1]
ART = ROOT / "artifacts" / "mu_topology"
RING = ROOT / "artifacts" / "glueball_ring_twist"
B_T, A_TUBE, R_MAJ = 12.2, 0.5, 2.111      # 装置参数（wiki 装置轴）


# ───────── 组合侧：指数和（与 Lean MuTopology.e 同一件事） ─────────

def e(word: list[tuple[int, int]]) -> int:
    """辫词指数和；word = [(股号, ±1)]。"""
    return sum(s for _, s in word)


def word_twist(m: int, q: int) -> list[tuple[int, int]]:
    """m 股、每对 q 次连接的自然辫词：把 (σ₁…σ_{m-1}) 重复 2q 次的一半等价物。

    口径：纯扭辫 (σ₁⋯σ_{m−1})^{2q·? }；本脚本只用到它的**指数和**
    e = m(m−1)q（= 2Σ_{i<j}Lk，与 RT-D 实测对齐）。
    """
    per = 2 * (m - 1) * q          # (σ₁…σ_{m−1}) 一轮的指数和 = m−1；需要 e = m(m−1)q
    rounds = per // (m - 1)
    w: list[tuple[int, int]] = []
    for _ in range(rounds):
        for i in range(m - 1):
            w.append((i, +1))
    assert e(w) == m * (m - 1) * q, (e(w), m * (m - 1) * q)
    return w


def find_lk_table(obj) -> dict:
    """在报告里找含 (m=…, q=…) 键的连接数表。"""
    if isinstance(obj, dict):
        if any(str(k).startswith("m=") and "q=" in str(k) for k in obj):
            return obj
        for v in obj.values():
            r = find_lk_table(v)
            if r:
                return r
    elif isinstance(obj, list):
        for v in obj:
            r = find_lk_table(v)
            if r:
                return r
    return {}


def load_rtd() -> dict:
    f = RING / "report.json"
    if not f.exists():
        return {}
    d = json.loads(f.read_text())
    return find_lk_table(d)


# ───────── MT-N2 / MT-N3：局部 vs 非局部（精确整数枚举） ─────────

def local_invariance(rng: int = 3) -> dict:
    """枚举小辫词，检验：关系式/共轭/循环都不改 e；加股改 e。"""
    # (a) braid 关系 σᵢσᵢ₊₁σᵢ = σᵢ₊₁σᵢσᵢ₊₁（同股号集合 ⟹ 同计数 ⟹ 同 e）
    rel = []
    for i in range(rng):
        lhs = [(i, +1), (i + 1, +1), (i, +1)]
        rhs = [(i + 1, +1), (i, +1), (i + 1, +1)]
        rel.append({"i": i, "e(lhs)": e(lhs), "e(rhs)": e(rhs), "相等": e(lhs) == e(rhs)})
    # (b) 共轭 v·w·v⁻¹
    conj = []
    pool = [[(0, +1)], [(1, -1)], [(0, +1), (1, +1)], [(1, +1), (0, -1)]]
    for v in pool:
        for w in pool:
            vinv = [(i, -s) for i, s in reversed(v)]
            conj.append({"v": v, "w": w, "e(vwv⁻¹)": e(v + w + vinv), "e(w)": e(w),
                         "相等": e(v + w + vinv) == e(w)})
    # (c) 循环置换（闭辫口径）
    cyc = []
    for w in pool[:3]:
        for k in range(len(w)):
            cyc.append({"w": w, "k": k, "e(轮换)": e(w[k:] + w[:k]), "e(w)": e(w),
                        "相等": e(w[k:] + w[:k]) == e(w)})
    # (d) 加股（稳定化）：把词塞进多一股的辫群 ⟹ e 加一个新生成元的 ±1
    stab = []
    for w in pool[:3]:
        for s in (+1, -1):
            stab.append({"w": w, "加股符号": s, "e": e(w) + s})
    return {"(a) braid 关系": rel, "a 违例": sum(1 for r in rel if not r["相等"]),
            "(b) 共轭": conj, "b 违例": sum(1 for r in conj if not r["相等"]),
            "(c) 循环置换": cyc, "c 违例": sum(1 for r in cyc if not r["相等"]),
            "(d) 加股改 e（见证）": stab,
            "结论": ("局部变形（关系式/共轭/循环）**全不改 e**；只有改计数（加股/改幂次）才改 e "
                     "⟹ 「非局部」的可算定义 = 改指数和")}


# ───────── MT-N4：代价语义从"微分价格"变"阈值能量" ─────────

def threshold_cost() -> dict:
    """一次拓扑事件（加一股 / 重联）要付的场能量级 —— 层厚假设给区间。"""
    mu0 = 4e-7 * math.pi
    u = B_T ** 2 / (2 * mu0)                       # 磁能密度 [J/m³]
    rows = []
    for name, delta in (("电阻层 δ=L/√S（S=1e6）", 0.5 / 1e3), ("离子惯性长 d_i ~ 2 mm", 2e-3),
                        ("整管 a=0.5 m（上界）", A_TUBE)):
        V = 2 * math.pi * R_MAJ * (2 * math.pi * A_TUBE) * delta   # 环向层体积
        rows.append({"层厚口径": name, "δ [m]": delta, "体积 [m³]": V, "能量 [J]": u * V})
    whole = u * math.pi * A_TUBE ** 2 * (2 * math.pi * R_MAJ)      # 整管（原 ε_mag 口径）
    return {"磁能密度 [J/m³]": u, "逐口径": rows, "整管（ε_mag 口径）[J]": whole,
            "结论": ("局部操作不可达 ⟹ 代价不是 ε·Δnet 的微分价格，而是**一次拓扑事件的阈值**；"
                     "口径跨度 500×（δ 从 2 mm 到 0.5 m）⟹ 阈值在 1e6–1e9 J，"
                     "整管口径 ≈ 装置级场能（0.6 GJ）⟹ 跳变要动全装置的场，不是局部小额支付")}


def device_scale(note: str = "") -> dict:
    mu0 = 4e-7 * math.pi
    E = B_T ** 2 / (2 * mu0) * (math.pi * A_TUBE ** 2 * 2 * math.pi * R_MAJ)
    return {"装置储磁场能（整管口径）[J]": E, "口径": note or "B=12.2T, a=0.5m, R=2.111m"}


def main() -> int:
    ART.mkdir(parents=True, exist_ok=True)
    print("=== 非局部性：把「改变净连接数」落成指数和与阈值代价 ===")
    out = {}

    # ── MT-N1：组合 ↔ 几何对齐（e = 2·ΣLk，用 RT-D 的实测数）──
    lk = load_rtd()
    rows = []
    for k, v in sorted(lk.items()):
        if not (str(k).startswith("m=") and "q=" in str(k)):
            continue
        m = int(str(k).split("m=")[1].split(",")[0])
        q = int(str(k).split("q=")[1])
        e_need = m * (m - 1) * q
        rows.append({"m": m, "q": q, "ΣLk(实测)": v, "2·ΣLk": 2 * v,
                     "e(辫词)": e_need, "相对偏差": abs(2 * v - e_need) / e_need})
    out["MT-N1_载体对齐"] = {"行": rows,
                            "最大相对偏差": max((r["相对偏差"] for r in rows), default=None),
                            "口径": ("与 RT-D 报告的 ΣLk **表**对齐（表内是取整后的派生值 ⟹ 本项偏差 0）；"
                                     "底层 Gauss 双积分实测偏差 ~0.006–0.018（见 RT-D1），"
                                     "所以这是**记账对齐**，不是把几何验到机器精度")}
    print(f"MT-N1 载体对齐：{len(rows)} 个 (m,q) 点，2ΣLk vs e=m(m−1)q 最大相对偏差 = "
          f"{out['MT-N1_载体对齐']['最大相对偏差']:.2e}")

    # ── MT-N2/N3：局部不变 vs 非局部改变 ──
    li = local_invariance()
    out["MT-N2_局部不变性"] = li
    print(f"MT-N2 局部不变：关系式违例 {li['a 违例']}、共轭违例 {li['b 违例']}、"
          f"循环违例 {li['c 违例']}（都是 0 ⟹ 局部变形不改 e）")
    print(f"MT-N3 非局部见证：加股 ⟹ e 变 ±1（{len(li['(d) 加股改 e（见证）'])} 例）；"
          "几何侧见 MT-N1 表（m=3→4 同 q 时 ΣLk 翻倍以上）")

    # ── MT-N4：阈值代价 ──
    tc = threshold_cost()
    ds = device_scale()
    out["MT-N4_阈值代价"] = {**tc, "装置尺度": ds}
    for r in tc["逐口径"]:
        print(f"MT-N4 代价口径 {r['层厚口径']:26s} δ={r['δ [m]']:.4g} m ⟹ {r['能量 [J]']:.3e} J")
    print(f"      整管口径 {tc['整管（ε_mag 口径）[J]']:.3e} J（与装置储磁场能同量级）")

    # ── MT-N5：与 RT-H4 交叉核对（股数随态变）──
    cb = RING / "conformal_blocks.json"
    strands = []
    if cb.exists():
        d = json.loads(cb.read_text())
        for k in d:
            if "股数" in str(d[k]):
                strands = [row.get("股数 n") for row in d[k].get("指配", [])]
                break
    out["MT-N5_与 RT-H4 交叉核对"] = {
        "格点最轻 7 态的股数": strands,
        "股数取值集合": sorted(set(x for x in strands if x is not None)),
        "口径": ("若改 μ 必须改股数（本脚本的结论），则「永远三股」本来就被 RT-H4 否掉；"
                  "两条独立结论指同一件事。"),
        "一致": len(set(x for x in strands if x is not None)) > 1}
    print(f"MT-N5 交叉核对：格点 7 态股数取值 = {out['MT-N5_与 RT-H4 交叉核对']['股数取值集合']} "
          f"（>1 种 ⟹ 与「改 μ 要改股数」一致）")

    # ── MT-N6：口径影响 + S3 实验设计（登记，不混进 PASS）──
    todo = [
        "口径变更：若「改变非局部」成立，μ 不再是连续可调量，S2 的「分辨率 σ ≤ 7.3e−4」判据要重读为"
        "「**配置枚举**」（每个配置一个离散 μ 值）；两者并存的口径说明待写，本步只登记",
        "S3 实验设计（未跑）：在 2-D 求解器里定义『局部操作』（局部 E 驱动/局部压缩/局部加热，不改股数）"
        "与『全局操作』（重联式：反向场引入/拓扑事件），预测**前者不改变 μ 的量子、后者能改变**；"
        "若局部操作显著改变 ⟹ 本支被证伪。协议与阈值待定",
        "阈值代价的层厚口径需要真装置诊断量（电流片厚度）才能收窄（当前 500× 跨度）",
    ]
    for t in todo:
        print("TODO: " + t)
    out["TODO_S3"] = todo

    (ART / "report.json").write_text(json.dumps(out, ensure_ascii=False, indent=2, default=str))
    (ART / "summary.txt").write_text("\n".join([
        "非局部性：把「改变净连接数非局部」落成指数和与阈值代价",
        f"① 载体对齐：e = 2·Σ_(i<j)Lk（RT-D 报告表，{len(rows)} 个 (m,q) 点），最大相对偏差 "
        f"{out['MT-N1_载体对齐']['最大相对偏差']:.2e}（记账对齐；底层 Gauss 实测偏差 0.006–0.018）",
        f"② 局部不变：braid 关系式/共轭/循环置换违例 = {li['a 违例']}/{li['b 违例']}/{li['c 违例']}（全 0）",
        f"③ 非局部见证：加股（Markov 稳定化）⟹ e 变 ±1（{len(li['(d) 加股改 e（见证）'])} 例）",
        f"④ 代价 = 阈值能量：δ=0.5mm {tc['逐口径'][0]['能量 [J]']:.2e} J → 整管 "
        f"{tc['整管（ε_mag 口径）[J]']:.2e} J（与装置储磁场能同量级）",
        f"⑤ 交叉核对 RT-H4：格点 7 态股数取值 {out['MT-N5_与 RT-H4 交叉核对']['股数取值集合']}（随态变 ✓）",
        "⑥ 判决实验（S3，未跑）：局部操作不该改 μ 的量子、全局重联式能改；局部能改即证伪本支",
    ]) + "\n")
    print(f"产物 → {ART}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
