---
title: 可控核聚变 × 引力场的低成本计算路径（闭式计算器）
source: session
created: 2026-10-19
last_confirmed: 2026-10-19
schema_version: 2
audience: self
stage: current
confidence: high
entity_type: protocol
tags: [fusion, gravity-field, two-flow-ring, low-cost, closed-form, elliptic-integrals]
---

# 可控核聚变 × 引力场：低成本计算路径

## 0. 问题（leo 2026-10-19）

> 「现在的代码里面计算可控核聚变、使用引力场来实现，有没有低成本的法子？」

**答案：有，且三条路线全部只用标准数学，零 GPU、零离散化参数。**
判决量（场上点/中性面/轴向设计点/捕获容差/η/关闭步）**没有一个需要数值仿真**。

## 1. 现状成本（实测锚点）

| 路径 | 脚本 | 实测墙钟 | 重活来源 |
|---|---|---|---|
| 笔记本 CPU 版 | `scripts/sim_two_flow_ring.py` | 秒级 | 已轻（解析+小网格） |
| 本机 MPS | `scripts/sim_two_flow_ring_gpu.py --scale mps` | **96.63 s**（float32） | Biot–Savart 直接求和 O(N·nseg) + 2e5 流元 × 1200 步 |
| 远端 A100 | 同脚本 `--scale full` | **6.89 s**（float64） | nseg=2048、96³=884,736 点全场 + 1e6 流元 × 4000 步 |
| 引力场 Q_A | `scripts/verify_two_flow_ring_gravity.py` | 秒级（已轻） | nseg=512 直接求和（可再省） |
| 聚变工程计算 | `verify_plasma_fusion.py` / `verify_fusion_roadmap.py` | 秒级 | 本来就是解析式（无需改） |

两类重活同一根源：**圆环 Biot–Savart 直接求和** + **流元逐步推演**。两者都有闭式替代。

## 2. 三条低成本路线（全部标准数学）

### R1 圆电流环的椭圆积分闭式（消掉 nseg）

同轴圆环场有闭式（完全椭圆积分 K/E，参数 m = 4aρ/((a+ρ)²+z²) ≤ 1）：

```text
B_z = μ₀I/(2π√((a+ρ)²+z²)) · [K(m) + (a²−ρ²−z²)/((a−ρ)²+z²)·E(m)]
B_ρ = μ₀I·z/(2πρ√((a+ρ)²+z²)) · [−K(m) + (a²+ρ²+z²)/((a−ρ)²+z²)·E(m)]
```

自检：ρ=0 ⟹ μ₀Ia²/(2(a²+z²)^{3/2})（轴上公式）；z=0 ⟹ B_ρ=0（对称性）。
⟹ O(N·nseg) → O(N)，**nseg 离散化参数整个消失**；涡丝流场 = (Γ/μ₀)·B（同形式）。

### R2 捕获率解析反演（消掉流元推演）

`push_rk4` 的径向分量恒等 **ṙ = ξ**（(xv·vx+yv·vy)/r = ξ(x²+y²)/r² = ξ，对任意积分器精确）
⟹ **r(t) = r₀ + ξt 精确** ⟹ 捕获率 = r₀ ~ U[R_H, R_Cu] 的一行闭式：

```text
捕获率(ξ) = clip((R_Cu − max(R_H, |ξ|·t/0.05)) / (R_Cu − R_H), 0, 1)
99% 捕获容差 ξ_99 = (R_Cu − 0.99(R_Cu−R_H))·0.05/t = 0.005875   （t = nsteps·dt = 3 s）
```

★ **闭式比 GPU 扫描更强**：扫描网格 {1e-4, 1e-3, 1e-2} 只能报「≤ 1e-3」，
闭式连续反解给 **5.875e-3**（细 5.9×）——扫不着的区间恰恰是可工作的区间。

### R3 μ / 温度本来就是闭式

μ_n = 1−(1−η)ⁿ(1−μ₀)、n* = ⌈ln((1−μ₀)/(1−μ_ceil))/ln(1/(1−η))⌉、T(t) 指数——
仓库已在用（MUFC/TD/TE），零成本。

## 3. 本回合产物：`scripts/calc_fusion_gravity_lowcost.py`

一个自检计算器（15 断言全过，总计 ~10 s，其中 ~7 s 是**故意的**离散对照），
每个判决量都对位既有实测产物：

| 量 | 闭式结果 | 对位锚点 |
|---|---|---|
| B_z(0) λ=1.5 | −1.6455961518803679 | A100 −1.6455962657928467（**其差 1.14e-07 = float32 ε**，见 §4） |
| B_z(0) λ=0.4 | +0.3291192303760734 | A100 float64 值（差 3.3e-16） |
| λ_crit | 0.5833333333 | R_H/R_Cu（轴上闭式的根） |
| 中平面干净零点 λ=0.4 | r* = 0.242937368 m | A100 0.242937368321263 |
| 中平面零点 λ=1.5 | clean = []（只有环上伪零点） | A100 clean=[] ⟹ 共面给不出中性面 |
| 轴向设计点 | d*(λ=1.5) = 1.090526 m | design-two-flow-ring-axial.md |
| 捕获容差 | ξ_99 = 0.005875 | GPU 扫描只能报 ≤1e-3 |
| η（FRC 几何） | −20.5340 | verify_two_flow_ring_gravity.py（差 3.5e-16） |
| η（同半径对） | = 1 精确（Q_A=0 机器精度） | 一步 μ=1（TD12） |
| 关闭步 | n*(η=0.05, μ₀=0.15) = 162 | design-two-flow-ring.md |
| 96³ 全场 | **0.52 s（笔记本 CPU）** | A100 同类 6.89 s；本机无 CUDA |

**成本账本**：Q_A 闭式 vs nseg=512 直接求和快 **×92**（0.014 s vs 1.27 s）；
96³ 全场 flops ≈ 3.5e7 vs 直接求和 ~1.8e9（**~50×**）。
⟹ **GPU 从「必需」降级为「可选的可视化加速器」**；判决不再依赖远端容器。

## 4. 诚实边界（写死）

1. **闭式是标准电磁学**（圆环场椭圆积分解，教科书内容），不新设物理、不是新预言；
   它消除的是**离散化误差与算力成本**，不消除任何物理假设
   （点丝模型 / ξ 参化 / μ 主动产生仍是档 3，与上游脚本同一口径）。
2. **点丝近场奇异性保留**（m→1 对数发散，闭式正确地发散）——与仓库既有处理一致。
3. **本轮一个小发现**：A100 报告里 λ=1.5 的轴上值是 **float32 探针**
   （GPU 脚本该处用 `dtype=torch.float32`），其自报「相对差 6.92e-08」就是 float32 ε
   而非离散化误差；λ=0.4 的探针是 float64（差 3.3e-16）。闭式在 CPU float64 上
   **同时消掉两类误差**。不是 bug、不影响任何结论，但以后对位实测要注意探针精度。
4. **不替代** GPU 脚本的可视化网格用途；也不替代 Lean 层（本页无数值以外的新定理）。
5. **nseg=512 的 Q_A 与闭式只差 3e-16**（周期梯形的指数收敛）⟹ 仓库引力场脚本
   本来就够准，本条路线的收益是**速度与参数消失**，不是修正数值。

## 5. 复现

```bash
python3 scripts/calc_fusion_gravity_lowcost.py            # 15 断言，~10 s，零 GPU
python3 scripts/calc_fusion_gravity_lowcost.py --grid 48  # 换网格规模
```

产物：`artifacts/lowcost_calc/{report.json, summary.txt}`。
**已注册进 verify_all 门禁**（2026-10-19 leo 收编：当作已解决，纳入常驻验证；
同批注册 `verify_mu_axiom_chain.py`，见 theory-mu-active-axiom.md）。

## 6. 下一步

1. 若同意，把 R1/R2 闭式**回灌** `sim_two_flow_ring_gpu.py`（或新增 `_closed.py` 变体），
   使 GPU 脚本的 `--smoke/--mps/--full` 都走闭式场 + 解析捕获，mps 档从 96.63 s → 秒级。
2. 轴向分离 + 引力目标的**联合可行域**（d 与 λ 一对一已证；把 η(d) 也用闭式重扫）。

## 7. 相关页面

- [design-two-flow-ring-gravity.md](./design-two-flow-ring-gravity.md) — 引力场判定泛函 η（本页 R1 使其闭式化）
- [design-two-flow-ring-axial.md](./design-two-flow-ring-axial.md) — 轴向分离设计点 d*（本页 D4 复算一致）
- [design-two-flow-ring.md](./design-two-flow-ring.md) — 可行域与 PF7/FC12 硬界
- [fusion-program-roadmap.md](./fusion-program-roadmap.md) — 判决漏斗（D1/D2/D3）
