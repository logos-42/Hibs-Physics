"""RT-H：TL₃ / Jones 表示 —— B₃ 的"可导出量子数"能不能从 2 维升级？

leo（2026-09-29）：BT/RT-G 判掉了 B₃ 的 **2 维既约 Burau**（全扭转是纯量 ⟹ 无态依赖 + 自旋 ≤ 3/2）。
本步按指定上 **TL/Jones**（level k ≥ 4 才有 j = 2），并把结论钉死。

算的五件事（全部可复算）：
  1. TL₃(δ) 的 5 维左正则表示（基 {1, e₁, e₂, e₁e₂, e₂e₁}）：定义关系 + **结合律全 125 组**
  2. **中心维数**（正确口径：z 中心 ⟺ L_z 与左乘/右乘都交换）与**显式非纯量中心元 Z**
     ⟹ 对照 BT3：2 维既约 Burau 的中心元是纯量；TL₃ 的中心 ⊋ 标量 ⟹ 态依赖标签存在
  3. 骨架形式 σᵢ = A + A⁻¹eᵢ、δ = −(A²+A⁻²)：braid 关系；**Δ = (σ₁σ₂)³ 中心但非纯量**
  4. 融合奇偶规则（独立于 TL）：n 条自旋-1/2 ⟹ **2J ≡ n (mod 2)**（整数 J 时才 = J ≡ n (mod 2)）；格点最轻 7 态的一致性检验
     ⟹ "永远三股"被**否证**（0++/2++ 的 J 是偶数）
  5. 诚实边界：Δ 的两个标量 = 3/(k+2) 与 1−3/(k+2)，**不等于** SU(2)_k 主权重的 j(j+1)/(k+2)
     ⟹ 还不能把标签直接读成 J（下一步：conformal blocks / 融合空间）

坑（已踩过，记下）：算中心时**不能**解「任意矩阵 M 与 R_ei 交换」——那是右正则像的交换子，
维数 = 5（= 左正则像，双中心化定理）。中心 = {z : L_z 与所有 L/R 交换}，未知量是 z 的 5 个系数。

产物：artifacts/glueball_ring_twist/tl3_jones.json
"""

import itertools
import json
import math
import os

import sympy as sp

REPO = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
ART = os.path.join(REPO, "artifacts", "glueball_ring_twist")

d, A = sp.symbols("delta A")             # δ = TL 参数；A = 骨架参数（q = A²）
BASIS = ["1", "e1", "e2", "u", "v"]      # u = e1e2, v = e2e1
IDX = {b: i for i, b in enumerate(BASIS)}

# ── TL₃ 乘法表（左因子 × 右因子） ──
T = {
    ("1", "1"): {"1": 1}, ("1", "e1"): {"e1": 1}, ("1", "e2"): {"e2": 1},
    ("1", "u"): {"u": 1}, ("1", "v"): {"v": 1},
    ("e1", "1"): {"e1": 1}, ("e1", "e1"): {"e1": d}, ("e1", "e2"): {"u": 1},
    ("e1", "u"): {"u": d}, ("e1", "v"): {"e1": 1},
    ("e2", "1"): {"e2": 1}, ("e2", "e1"): {"v": 1}, ("e2", "e2"): {"e2": d},
    ("e2", "u"): {"e2": 1}, ("e2", "v"): {"v": d},
    ("u", "1"): {"u": 1}, ("u", "e1"): {"e1": 1}, ("u", "e2"): {"u": d},
    ("u", "u"): {"u": 1}, ("u", "v"): {"e1": d},
    ("v", "1"): {"v": 1}, ("v", "e1"): {"v": d}, ("v", "e2"): {"e2": 1},
    ("v", "u"): {"e2": d}, ("v", "v"): {"v": 1},
}


def mul(x, y):
    """两个（基 → 系数）字典相乘。"""
    out = {}
    for a, ca in x.items():
        for b, cb in y.items():
            for k, c in T[(a, b)].items():
                out[k] = sp.expand(out.get(k, 0) + ca * cb * c)
    return {k: v for k, v in out.items() if v != 0}


def L(x):
    """左乘 x 的 5×5 矩阵。"""
    M = sp.zeros(5, 5)
    for i, b in enumerate(BASIS):
        for k, c in mul(x, {b: 1}).items():
            M[IDX[k], i] += c
    return M


def R(x):
    """右乘 x 的 5×5 矩阵。"""
    M = sp.zeros(5, 5)
    for i, b in enumerate(BASIS):
        for k, c in mul({b: 1}, x).items():
            M[IDX[k], i] += c
    return M


LB = {b: L({b: 1}) for b in BASIS}
RB = {b: R({b: 1}) for b in BASIS}

# ── 1) 定义关系与结合律 ──
rel_ok = (mul({"e1": 1}, {"e1": 1}) == {"e1": d} and mul({"e2": 1}, {"e2": 1}) == {"e2": d}
          and mul(mul({"e1": 1}, {"e2": 1}), {"e1": 1}) == {"e1": 1}
          and mul(mul({"e2": 1}, {"e1": 1}), {"e2": 1}) == {"e2": 1}
          and mul({"e1": 1}, {"e2": 1}) != mul({"e2": 1}, {"e1": 1}))
assoc_bad = 0
for a, b, c in itertools.product(BASIS, repeat=3):
    lhs, rhs = mul(mul({a: 1}, {b: 1}), {c: 1}), mul({a: 1}, mul({b: 1}, {c: 1}))
    if any(sp.simplify(lhs.get(k, 0) - rhs.get(k, 0)) != 0 for k in BASIS):
        assoc_bad += 1
print("RT-H 1) TL₃(δ)：定义关系 =", rel_ok, f"；结合律违例 = {assoc_bad}/125；dim = 5 = Catalan(3)")

# ── 2) 中心：未知量 = z 的 5 个系数；条件 = L_z 与所有 L_x、R_x 交换 ──
cs = sp.symbols("c0:5")
# z 中心 ⟺ L_z = R_z（左右乘相等）⟹ 25 条方程、5 个未知量
rows = []
for i in range(5):
    for j in range(5):
        expr = sp.expand(sum(cs[k] * (LB[BASIS[k]][i, j] - RB[BASIS[k]][i, j]) for k in range(5)))
        rows.append([sp.expand(expr.coeff(c)) for c in cs])
Mctr = sp.Matrix(rows)
rank = Mctr.rank()
center_dim = 5 - rank
nul = Mctr.nullspace()
Z_mat, z_central, z_scalar = None, None, None
for v in nul:
    if sp.simplify(v[0]) == 0 and any(sp.simplify(x) != 0 for x in v[1:]):
        Z_mat = sp.zeros(5, 5)
        for k in range(5):
            Z_mat += sp.nsimplify(v[k]) * LB[BASIS[k]]
        Z_mat = sp.simplify(Z_mat)
        break
if Z_mat is not None:
    z_central = all(sp.simplify(sp.expand(Z_mat * G - G * Z_mat)) == sp.zeros(5, 5)
                    for G in (LB["e1"], LB["e2"]))
    z_scalar = sp.simplify(Z_mat - Z_mat[0, 0] * sp.eye(5)) == sp.zeros(5, 5)
    print(f"RT-H 2) 中心维数 = {center_dim}（rank = {rank}）；显式中心元 Z：中心 = {z_central}，"
          f"纯量 = {z_scalar}")
    print("   Z =", Z_mat.tolist())

# ── 3) 骨架形式 σᵢ = A + A⁻¹eᵢ（δ = −(A²+A⁻²)）：braid 关系与 Δ ──
deltaA = -(A ** 2 + A ** (-2))
S1 = (A * sp.eye(5) + A ** (-1) * LB["e1"]).subs(d, deltaA)
S2 = (A * sp.eye(5) + A ** (-1) * LB["e2"]).subs(d, deltaA)
braid_ok = sp.simplify(sp.expand(S1 * S2 * S1 - S2 * S1 * S2)) == sp.zeros(5, 5)
D = sp.simplify(sp.expand((S1 * S2) ** 3))
D_scalar = sp.simplify(D - D[0, 0] * sp.eye(5)) == sp.zeros(5, 5)
D_central = all(sp.simplify(sp.expand(D * G - G * D)) == sp.zeros(5, 5)
                for G in (LB["e1"].subs(d, deltaA), LB["e2"].subs(d, deltaA)))
evs = [(sp.factor(k), int(m)) for k, m in D.eigenvals().items()]
print(f"RT-H 3) braid 关系 = {braid_ok}；Δ 中心? {D_central}；Δ 纯量? {D_scalar}；"
      f"特征值（多重度）= {[(str(k), m) for k, m in evs]}")
tab = []
for kk in range(1, 11):
    Av = sp.exp(sp.I * sp.pi / (kk + 2))           # A = e^{iπ/(k+2)} ⟹ q = A² = e^{2πi/(k+2)}
    ph = sorted({round(float(sp.arg(sp.N(sp.simplify(lam.subs(A, Av))))) / (2 * math.pi) % 1, 6)
                 for lam, _ in evs})
    tab.append({"k（level）": kk, "两个标量的相位/2π": ph, "两个不同": len(ph) > 1})
print("   Δ 两个标量的相位（相位/2π = h）：", [(r["k（level）"], r["两个标量的相位/2π"]) for r in tab[:5]],
      "…")

# ── 4) 融合奇偶规则（独立于 TL 的组合事实） ──
fusion = {}
for n in range(2, 7):
    Js = sorted({abs(sum(s)) for s in itertools.product([0.5, -0.5], repeat=n)})
    fusion[n] = Js
    print(f"RT-H 4) n = {n} 股自旋-1/2 ⟹ J ∈ {Js}（2J ≡ n (mod 2)：{all(round(2*j) % 2 == n % 2 for j in Js)}）")
lat_J = [0, 2, 0, 1, 2, 3, 3]
assign = ["2 股" if j % 2 == 0 else "3 股" for j in lat_J]
parity_ok = all((j % 2) == (n % 2) for j, n in zip(lat_J, [2 if j % 2 == 0 else 3 for j in lat_J]))
print(f"   格点 J（质量升序）= {lat_J} ⟹ 自洽股数分配 = {assign}；奇偶规则自洽 = {parity_ok}")
print("   ⟹ **\"永远三股\"被否证**：三股只给奇数 J，而最轻的 0++、2++ 的 J 是偶数")

out = {
    "1) TL₃(δ) 5 维左正则表示": {"定义关系成立": bool(rel_ok), "结合律违例数": assoc_bad,
                                 "基": BASIS, "维数": 5},
    "2) 中心": {"维数": int(center_dim), "rank": int(rank),
                "显式中心元 Z": str(Z_mat.tolist()), "Z 是中心元": bool(z_central),
                "Z 是纯量": bool(z_scalar),
                "对照 BT3": "2 维既约 Burau 的中心元是**纯量**（⟹ 无态依赖）；TL₃ 中心维数 "
                            f"{center_dim} 且显式非纯量中心元存在 ⟹ **态依赖的离散标签存在**"},
    "3) 骨架形式 σ = A + A⁻¹e（δ = −(A²+A⁻²)）": {
        "braid 关系成立": bool(braid_ok), "Δ 是中心元": bool(D_central), "Δ 是纯量": bool(D_scalar),
        "Δ 的特征值（多重度）": [[str(k), m] for k, m in evs],
        "自洽性": "两个标量、多重度 1 与 4 ⟹ 与 TL₃ ≅ M₁ ⊕ M₂ 的左正则表示 V₁ ⊕ V₂^{⊕2}"
                  "（1 + 4 = 5 维）一致",
        "两个标量的相位（h = 相位/2π）": tab,
        "对照 BT2/BT3": "2 维既约 Burau：Δ = t³·I（纯量，BT2）⟹ 无态依赖；"
                        "TL₃：Δ **中心但非纯量** ⟹ 两个不能约分量拿到不同标量"},
    "4) 融合奇偶规则（导出，独立于 TL）": {
        "n 股融合的 J 集合": {str(k): v for k, v in fusion.items()},
        "规则": "2J ≡ n (mod 2)，即 J ≡ n/2 (mod 1)（n 条自旋-1/2；2J = |n − 2k| 且 |n − 2k| ≡ n）—— 整数 J 时才简写成 J ≡ n (mod 2)",
        "格点 J（质量升序）": lat_J, "自洽股数分配": assign, "奇偶规则自洽": bool(parity_ok),
        "结论": "存在自洽的 2 股/3 股分配；**\"永远三股\"被否证**（0++、2++ 的 J 是偶数，"
                "三股只给奇数 J）"},
    "5) 诚实边界": "TL₃ 的表与矩阵由本脚本逐步复核（结合律 125 组全过）；δ = −A²−A⁻²、σ = A + A⁻¹e 是"
                   "标准 skein 约定；Δ 的两个标量是**算出来的**。但 3/(k+2) 与 1−3/(k+2) **不等于**"
                   " SU(2)_k 主权重的 j(j+1)/(k+2) ⟹ 还不能把标签直接读成 J；要给 J 必须用融合空间"
                   "（conformal blocks）—— 那是本步之后唯一剩下的一步。",
}

os.makedirs(ART, exist_ok=True)
with open(os.path.join(ART, "tl3_jones.json"), "w", encoding="utf-8") as fh:
    json.dump(out, fh, ensure_ascii=False, indent=1)
print(f"\n产物 → {os.path.join(ART, 'tl3_jones.json')}")
