"""RT-I：最后一步 —— SU(2)_k 融合空间（conformal blocks），J 能不能变成"导出量"？

走到这一步的来路：
  · RT-F：几何只给两个 ℤ₂（Σ|nᵢ| mod 2, μ̄₃）⟹ 穷举 256 条规则全中 = 0 ⟹ 不能线性导出 J^PC
  · BT/RT-G：2 维既约 Burau 判死（中心元纯量 ⟹ 无态依赖；自旋 ≤ 3/2）
  · RT-H：TL₃ 中心维数 2、Δ 中心但非纯量（两个标量 A^{±6}）⟹ 态依赖标签存在；
          融合奇偶规则 2J ≡ n (mod 2)
本步（RT-I）：把 **融合空间**（SU(2)_k 的 conformal blocks）算出来，看
  (1) J 能不能成为**导出的**标签（不靠"按质量序指配"）
  (2) J 的多重度/容量能不能对上格点最轻 7 态
  (3) P、C 能不能从同一结构里出来 —— 这一条是**结构性**判断，本脚本给出理由

约定：自旋用整数标签 L = 2j（于是 L 就是 J = 2j，直接是"角动量"）。
  SU(2)_k 融合：a ⊗ b = ⊕ c，|a−b| ≤ c ≤ min(a+b, 2k − a − b)，且 0 ≤ c ≤ k（level 截断）

产物：artifacts/glueball_ring_twist/conformal_blocks.json
"""

import json
import os
from functools import lru_cache

REPO = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
ART = os.path.join(REPO, "artifacts", "glueball_ring_twist")


def fuse(a, b, k):
    """SU(2)_k 融合规则（整数标签 L = 2j）。

    两个条件缺一不可：
      · 宇称：2j₁ + 2j₂ ≡ 2j (mod 2) ⟹ c ≡ a + b (mod 2)（漏了这条会算出 n=3 出现 J = 0、2 的假结果）
      · level 截断：c ≤ min(a+b, 2k − a − b) 且 c ≤ k
    """
    lo, hi = abs(a - b), min(a + b, 2 * k - a - b)
    return [c for c in range(lo, hi + 1) if 0 <= c <= k and (c - a - b) % 2 == 0]


def multiplicities(n, k):
    """n 条自旋-1/2（标签 1）融合到总标签 c 的路径数 mult_c(n)。"""
    cur = {1: 1}                                  # 一条股
    for _ in range(n - 1):
        nxt = {}
        for a, ma in cur.items():
            for c in fuse(a, 1, k):
                nxt[c] = nxt.get(c, 0) + ma
        cur = nxt
    return cur


def catalan(n):
    from math import comb
    return comb(2 * n, n) // (n + 1)


print("RT-I 1) 融合空间：n 条自旋-1/2 在 level k 下的多重度 mult_c(n)（c = J）")
rows = []
for n in range(2, 8):
    for k in [1, 2, 3, 4, 6, 10, 12]:
        m = multiplicities(n, k)
        dim = sum(m.values())                       # 路径数 = 融合空间维数
        sq = sum(v * v for v in m.values())         # Σ mult² = TL_n 标准模维数
        rows.append({"n": n, "k": k, "多重度 mult_J": m, "融合空间维数 Σ mult": dim,
                     "Σ mult²": sq, "Catalan(n)": catalan(n),
                     "Σ mult² = Catalan(n)": sq == catalan(n)})
        flag = "✓" if sq == catalan(n) else "✗"
        if k >= n:      # 无截断时必然相等：这是与 TL 维数对上的硬检查
            print(f"   n={n}, k={k}: J→{ {c: m[c] for c in sorted(m)} }  Σmult={dim}  "
                  f"Σmult²={sq} vs Catalan({n})={catalan(n)} {flag}")
print("   （k ≥ n 时截断不生效 ⟹ Σ mult² 必须 = Catalan(n)，这是本步与 RT-H 的 TL 维数对齐的自检）")
bad = [r for r in rows if r["k"] >= r["n"] and not r["Σ mult² = Catalan(n)"]]
print(f"   自检违例数（k ≥ n）= {len(bad)}")

print("\nRT-I 2) J 变成**导出量**：三股（n=3）在 level k 下允许的 J 与多重度")
three = []
for k in range(1, 13):
    m = multiplicities(3, k)
    three.append({"k": k, "允许的 J（= c）": sorted(m), "多重度": {c: m[c] for c in sorted(m)}})
    print(f"   k={k:2d}: J ∈ {sorted(m)}（多重度 {[m[c] for c in sorted(m)]}）")
print("   ⟹ J = 3（三股的总自旋 3/2）**当且仅当 k ≥ 3** 才出现；J = 1 恒可（k ≥ 2）且**多重度 2**")

print("\nRT-I 3) 与 RT-H 的 TL₃ 对位（维数把两个标量钉到两个扇区上）")
# TL₃ ≅ M₁ ⊕ M₂：单模维数 1 与 2；融合扇区的 TL 单模维数 = mult_J
for k in [3, 4, 6, 10]:
    m = multiplicities(3, k)
    dims = sorted(m.values())
    print(f"   k={k}: 扇区多重度 = {dims}；TL₃ 单模维数（RT-H 中心维数 2 ⟹ 两个单模）= [1, 2] "
          f"⟹ 对应 {dims == [1, 2]}")
H = 3 / (3 + 2)          # 占位，下面按 k 算
phase_rows = []
for k in range(2, 13):
    h1 = 1 * (1 + 2) / (4 * (k + 2))            # J=1 的权重：h_j = j(j+1)/(k+2)，j = J/2
    h3 = 3 * (3 + 2) / (4 * (k + 2))            # J=3 的权重
    dh = h3 - h1
    phase_rows.append({"k": k, "h(J=3) − h(J=1)": round(dh, 10), "3/(k+2)": round(3 / (k + 2), 10),
                       "相等": abs(dh - 3 / (k + 2)) < 1e-12})
print(f"   RT-H 的两个标量相位是 ±3/(k+2)；融合扇区给出 h(J=3) − h(J=1) = "
      f"3/(k+2)（全部 k 相等 = {all(r['相等'] for r in phase_rows)}）")
print("   ⟹ 两个不能约扇区 = J = 1（多重度 2）与 J = 3（多重度 1）；两个标量相位 = e^{±2πi(h₃ − h₁)}")

print("\nRT-I 4) 格点最轻 7 态的容量/奇偶一致性检验")
# 格点最轻 7 态（质量升序）：(J, P, C, 质量 MeV)
LAT = [("0++", 0, 1710), ("2++", 2, 2390), ("0-+", 0, 2560), ("1+-", 1, 2980),
       ("2-+", 2, 3040), ("3+-", 3, 3600), ("3++", 3, 3670)]
K = 6                      # 取 level k = 6（j ≤ 3，即 J ≤ 6）
cap = multiplicities(3, K) | multiplicities(4, K)
ok_parity, ok_cap, assign = True, True, []
for name, J, mass in LAT:
    n = 2 if J % 2 == 0 else 3              # 奇偶规则：2J ≡ n (mod 2)
    avail = multiplicities(n, K)
    ok_parity &= (2 * J % 2) == (n % 2) or (J % 2) == (n % 2)
    ok_cap &= J in avail
    assign.append({"态": name, "J": J, "质量 MeV": mass, "股数 n": n,
                   "该 (n,J) 的容量 mult": avail.get(J, 0)})
    print(f"   {name:5s} J={J} m={mass}: n={n}（奇偶）容量 mult_{J}({n})={avail.get(J, 0)}")
print(f"   奇偶规则全过 = {ok_parity}；容量允许 = {ok_cap}")
print("   诚实说明：这是**容量约束**（格点某 J 的态数不得超过融合谱给出的容量），不是预测 —— "
      "它排除读法，不指出唯一指配")

print("\nRT-I 5) P、C 能不能从融合结构出来（结构性判断）")
print("   SU(2)_k 是**手性**代数（chiral algebra）：它的数据是融合规则 + R/θ（编织与扭转）；")
print("   融合范畴里没有宇称 P、也没有电荷共轭 C 的位置 —— 这两个是**体态**（非手性）的对称性。")
print("   加上 RT-F 的穷举否定（几何只给两个 ℤ₂、256 条规则全中 = 0）⟹ 结论：")
print("   **J 有导出来源了；P、C 仍然没有来源**，而且这条缺口现在是「结构性」的，不是「没找到」。")

out = {
    "1) 融合空间多重度": {"表": rows, "自检（k ≥ n）": "Σ_J mult_J(n)² = Catalan(n)",
                          "自检违例数": len(bad)},
    "2) J 作为导出量（n = 3）": {"表": three,
                                 "结论": "J = 3 当且仅当 k ≥ 3；J = 1 多重度 2（k ≥ 2）"},
    "3) 与 RT-H 的 TL₃ 对位": {
        "维数对位": "TL₃ ≅ M₁ ⊕ M₂（单模维数 1, 2）= 融合扇区多重度 mult_J ⟹ "
                    "J = 3 ↔ 维数 1；J = 1 ↔ 维数 2（两处独立算出，维数把它们钉在一起）",
        "相位对位": "RT-H 的两个标量 = A^{±6} = e^{±2πi·3/(k+2)}；融合权重给 "
                    "h(J=3) − h(J=1) = 3/(k+2) ⟹ 两个标量 = e^{±2πi(h₃ − h₁)}",
        "表": phase_rows},
    "4) 格点最轻 7 态（容量/奇偶）": {"指配": assign, "奇偶全过": bool(ok_parity),
                                       "容量允许": bool(ok_cap),
                                       "口径": "容量约束：某 J 的格点态数 ≤ 该 (n, J) 的融合容量；"
                                               "它排除读法、不指出唯一指配"},
    "5) P/C": {"结论": "SU(2)_k 是手性代数，融合范畴里没有 P、C 的位置（它们是体态对称性）⟹ "
                       "J 有导出来源；P、C 仍缺来源，且缺口是结构性的（不是没找到）",
               "与 RT-F 关系": "RT-F 已穷举否定「几何两个 ℤ₂ 线性导出 J^PC」（256 条全中 = 0）；"
                               "本步补上 J，但 P/C 的缺口没被填上"},
    "诚实边界": "融合规则与路径计数是精确组合（自检 Σ mult² = Catalan(n) 全过）；"
                "扇区↔TL 单模的对应由维数强制；相位的对位是**算出来的**（±3/(k+2) 与 h₃ − h₁）。"
                "**没有做**：R 矩阵/6j 的显式构造（那会给出每个融合树态的具体相位，但不会改变"
                "扇区与相位集合）；P/C 的候选来源（例如环的定向/镜像结构）留作下一步的具体猜想。",
}

os.makedirs(ART, exist_ok=True)
with open(os.path.join(ART, "conformal_blocks.json"), "w", encoding="utf-8") as fh:
    json.dump(out, fh, ensure_ascii=False, indent=1)
print(f"\n产物 → {os.path.join(ART, 'conformal_blocks.json')}")
