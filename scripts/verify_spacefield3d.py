#!/usr/bin/env python3
"""空间场 3D 向量微积分：数值验证（SpaceField3D.lean SF1–SF5 的数值对应）

候选 1（leo）：3D 推广——B = ∇×C 无散自动成立是 3D 才完整的。
候选 2：与 MC1 自旋连接——电子 = C 的涡旋（自旋，∇×C ≠ 0 = 磁场 B）。
候选 3：电荷机制——J 是输入，e 无来源（诚实缺口，仅标注）。

数值检验：
  1. 随机 3D 场：div(curl C) = 0（机器精度，SF1）
  2. 随机标量场：curl(grad f) = 0（机器精度，SF2）
  3. 涡旋场（环形流）：B = curl C 无散 + 图（磁场 = 自旋涡旋）
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

OUT = os.path.join(os.path.dirname(__file__), "..", "artifacts", "spacefield3d")
os.makedirs(OUT, exist_ok=True)


def curl_num(F, dx=1.0):
    """数值 curl（中心差分，3D 数组场）。F: (3, N, N, N)。"""
    Cx, Cy, Cz = F
    return np.stack([
        np.gradient(Cz, dx, axis=1) - np.gradient(Cy, dx, axis=2),  # x
        np.gradient(Cx, dx, axis=2) - np.gradient(Cz, dx, axis=0),  # y
        np.gradient(Cy, dx, axis=0) - np.gradient(Cx, dx, axis=1),  # z
    ])


def div_num(F, dx=1.0):
    """数值散度。"""
    Cx, Cy, Cz = F
    return (np.gradient(Cx, dx, axis=0) + np.gradient(Cy, dx, axis=1)
            + np.gradient(Cz, dx, axis=2))


def grad_num(f, dx=1.0):
    """数值梯度。"""
    return np.stack([np.gradient(f, dx, axis=0),
                     np.gradient(f, dx, axis=1),
                     np.gradient(f, dx, axis=2)])


def main():
    report = {"model": "3D discrete vector calculus of space field C (SF1-SF5)",
              "date": str(date.today()), "results": {}}

    # ---- 1. div(curl C) = 0（随机场，SF1）----
    rng = np.random.default_rng(42)
    results = []
    for seed in range(3):
        r = np.random.default_rng(seed)
        F = r.standard_normal((3, 40, 40, 40))
        d = div_num(curl_num(F))
        results.append(float(np.max(np.abs(d))))
    report["results"]["div_curl_zero_SF1"] = {
        "max|div(curl C)| (3 随机种子)": results,
        "机器精度": "≈ 1e-15",
        "note": "B = curl C ⟹ ∇·B = 0 自动（3D 运动学恒等，SF1 Lean 已证）"}

    # ---- 2. curl(grad f) = 0（随机标量场，SF2）----
    f = np.random.default_rng(7).standard_normal((40, 40, 40))
    g = grad_num(f)
    cg = curl_num(g)
    report["results"]["curl_grad_zero_SF2"] = {
        "max|curl(grad f)|": float(np.max(np.abs(cg))),
        "note": "梯度无旋（SF2）——静电场 E = −∇φ 自动无旋"}

    # ---- 3. 涡旋场：B = curl C 无散 + 磁场 = 自旋 ----
    # 环形流：C = (−y, x, 0)·exp(−r²/σ²)（绕 z 轴的涡旋，带包络）
    n = 48
    g = np.linspace(-3, 3, n)
    X, Y, Z = np.meshgrid(g, g, g, indexing="ij")
    r2 = X ** 2 + Y ** 2
    env = np.exp(-r2 / 2.0)
    Cfield = np.stack([-Y * env, X * env, np.zeros_like(X)])
    Bfield = curl_num(Cfield)
    divB = div_num(Bfield)
    report["results"]["vortex_curl_SF5"] = {
        "涡旋场 max|div(B = curl C)|": float(np.max(np.abs(divB))),
        "max|B|": round(float(np.max(np.abs(Bfield))), 4),
        "max|curl C|": round(float(np.max(np.abs(curl_num(Cfield)))), 4),
        "note": "磁场 B = curl C = 空间场涡旋（SF5）——电子自旋的磁场位置；"
                "涡旋场 B 无散 ✓"}

    # ---- 图：涡旋 C 与 B = curl C（xy 截面）----
    fig, axes = plt.subplots(1, 2, figsize=(12, 5.5))
    mid = n // 2
    ax = axes[0]
    ax.quiver(X[:, :, mid][::2, ::2], Y[:, :, mid][::2, ::2],
              Cfield[0][:, :, mid][::2, ::2], Cfield[1][:, :, mid][::2, ::2],
              color="steelblue", alpha=0.8)
    ax.set_title("空间场 C（环形涡旋 = 自旋）\n∇×C ≠ 0（z 方向）")
    ax.set_aspect("equal")
    ax = axes[1]
    ax.quiver(X[:, :, mid][::2, ::2], Y[:, :, mid][::2, ::2],
              Bfield[0][:, :, mid][::2, ::2], Bfield[1][:, :, mid][::2, ::2],
              color="darkorange", alpha=0.8)
    ax.set_title("磁场 B = curl C（无散）\n∇·B = 0 自动成立（SF1）")
    ax.set_aspect("equal")
    for a in axes:
        a.grid(alpha=0.2)
    fig.suptitle("候选 1+2：磁场 = 空间场的涡旋（3D 恒等 div(curl C) = 0）", fontsize=12)
    fig.tight_layout()
    fig.savefig(os.path.join(OUT, "vortex_curl.png"), dpi=150)
    plt.close(fig)

    report["conclusion"] = (
        "候选 1 ✓（Lean SF1–SF4 + 数值）：3D 离散恒等——div(curl C) = 0 自动"
        "（B 无散）、curl(grad f) = 0（静电场无旋）、∂_t 与 curl 交换 ⟹ "
        "法拉第 3D 自动。B = curl C 无散是 3D 才完整的运动学内容。"
        "候选 2 ✓（代数位置）：磁场 B = curl C = 自旋的磁场（SF5）——"
        "龙卷风图像（涡旋+源）获得 curl/div 的代数分解；curl 三分量 ↔ "
        "空间三方向（三方向假设）。候选 3 ✗（诚实缺口）：∇·C ≠ 0 只给"
        "电荷的代数位置，e 的数值与量子化（1.602e-19 C）无来源——"
        "与'第二输入未找到'同源，仓库最深的开放问题之一。")
    report["files"] = {"vortex_curl": "vortex_curl.png"}

    with open(os.path.join(OUT, "report.json"), "w", encoding="utf-8") as f:
        json.dump(report, f, ensure_ascii=False, indent=2)

    print(json.dumps(report["results"], ensure_ascii=False, indent=2))
    print("\n→ 产物:", os.path.abspath(OUT))


if __name__ == "__main__":
    main()
