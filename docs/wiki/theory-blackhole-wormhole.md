---
title: 黑洞与虫洞的流动结构（探索）
source: session
created: 2026-08-14
last_confirmed: 2026-08-14
audience: self
stage: draft
schema_version: 2
confidence: medium
entity_type: theorem
tags: [blackhole, wormhole, space-flow, horizon, gordon-metric, exploration]
status: current
---

# 黑洞与虫洞的流动结构（探索）

> leo（2026-08-14）：在这个空间流动假设里面，黑洞和虫洞的结构会发生
> 什么变化，还需要什么几何描述？

## 1. 结论（先给答案）

**黑洞/虫洞结构在流动假设下与 GR 完全一致（公式同、数值同）——变化只在
解释层。** 具体：

```text
黑洞 = 空间内向流动 v(r) = c·√(r_s/r) 的区域（Schwarzschild 精确 river 场）
  视界 r_s = 2GM/c² = v 首次达到 c 的光速面（★ BH1）
  向外光子坐标速度 dx/dt = v − c：视界处 = 0（冻结），内部 > 0（仍向内）
  ⟹ 光子（随空间流动）永远无法逃出 v ≥ c 区域（★ BH3）
  白洞 = 流反转 v ↦ −v（视界同位，BH5–BH6）

虫洞 = 亚光速流管通道：v(s) 在喉部有峰值但 |v| < c 处处
  光子随流穿过全程 dτ = 0（零时通道）
  喉部恢复光锥（v = 0 ⟹ g_tt = 1，WH1）
```

与 Hamilton–Lisle 河流模型（2008, "The river model of black holes",
Am. J. Phys. 76, 519）**精确同构**——Schwarzschild 解 = 空间向内流动 +
平直空间度规，是已知 GR 的重新表述。

## 2. Lean 形式化（`ProjectionPhysics/Explorations/BlackHoleWormhole.lean`）

| 定理 | 内容 |
|---|---|
| BH1 `horizon_iff_light_speed_flow` | ★ 视界 = 光速面：g_tt = 1 − v²/c² = 0 ⟺ \|v\| = c |
| BH1b `horizon_region_gtt_nonpos` | 黑洞区域 v ≥ c ⟹ g_tt ≤ 0 |
| BH2 `gordon_outward_photon_proper_time_zero` | 向外光子世界线 dx = (v−c)dt 类光（代数恒等） |
| BH3 `outward_photon_cannot_escape` | ★ 逃逸不可能：v ≥ c ⟹ 向外光子位移 ≥ 0（仍向内）；`outward_photon_frozen_at_horizon` v=c ⟹ dx=0 |
| BH4 `escape_requires_sublight_flow` | 逃逸 ⟺ 流动亚光速（BH3 逆否） |
| BH5–6 `white_hole_gtt_invariant`/`white_hole_gtx_flips` | 白洞 = 流反转：g_tt 不变（只依赖 v²），g_tx 变号 |
| BH7 `gordonGtt_negative_inside_horizon` | 内部 v > c ⟹ g_tt < 0（类时/类空角色互换种子） |
| WH1 `wormhole_throat_restores_light_cone` | 喉部 v = 0 ⟹ g_tt = 1（平直，光锥恢复） |

`lake build` 全绿（4128 jobs）。

## 3. 数值验证（`scripts/verify_blackhole_wormhole.py`）

| 检验 | 数值（c=1, r_s=1） | 与 GR |
|---|---|---|
| 视界 | v(r_s) = 1.0 = c，g_tt = 0 | 精确一致 |
| 向外光子 @ r=0.25r_s（内部） | dx/dt = +1.0（坐标仍向内） | 内部 r 类时同 |
| 向外光子 @ 视界 | dx/dt = 0（冻结） | 坐标奇点同 |
| 向外光子 @ r=2r_s（外部） | dx/dt = −0.293（真向外） | 同 |
| 时间膨胀 @ 视界 | dτ/dt → 0 | 同 |
| 外部观测者 | t(r→r_s⁺) → ∞ | 同 |
| 虫洞喉部 | v_peak = 0.8c < c，无视界 | MT 喉部同 |
| 虫洞穿越 | 光子随流 dτ² ≡ 0 全程 | 零测地线同 |

## 4. 还需要什么几何描述（正面回答）

1. **3+1 维流场 v(x,t)**：目前只有 1+1 维 Gordon 骨架（SG 诚实边界）；
   完整的黑洞/虫洞需要完整空间流场。
2. **流场动力学方程**：目前只有动量守恒 D5 离散版（Flow 组合律）；
   需要连续版（欧拉型方程，流动梯度 = 等效引力的动力学）。
3. **流源项**：可穿越虫洞喉部需要负能量（GR 的 NEC 违背在流动语言 =
   流源，∇·v ≠ 0）；无源流动禁止内部源/汇 ⟹ 无虫洞（拓扑论证）。
4. **流线拓扑**：汇（黑洞奇点）/源（白洞）/通道（虫洞）的分类——离散
   骨架是 FlowConservation.lean（D5）。
5. **喉部嵌入几何**：Morris–Thorne 双漏斗嵌入（z(r) = 2√r₀·√(r−r₀)），
   需要第二类几何（嵌入到高维平直空间）。
6. **曲率张量/场方程**：仓库诚实标注的大工程（需 mathlib Riemannian
   Geometry），黑洞内部奇点的完整描述依赖它。

## 5. 诚实评估（4 层判定，写死防过度声称）

| 层 | 判定 | 理由 |
|---|---|---|
| ① 数学恒等式 | 真但平凡 | 视界=v=c⟺g_tt=0、向外光子 dτ²=0 是 Gordon 度规直接代数（河流模型全部内容） |
| ② 结构对应 | 已知物理 | 黑洞=内向流+光速面、虫洞=亚光速流管 = Schwarzschild/MT 的流线版 |
| ③ 数值匹配 | 一致但非新 | r_s、时间膨胀、光子冻结全部与 GR 数值同 |
| ④ 概念重构 | 不可证伪 | 解释层全变但公式数值全同；唯一出口 = 流动非均匀⟹洛伦兹破缺（仓库既有） |

**真实发现判据全未满足**——本模块是主线（空间流动假设）在强场区域的
应用与几何需求清单，不是新物理。价值 = 把"引力=流动非均匀"推进到
视界/喉部尺度（解释层自洽性检查：光子=随空间 ⟹ 视界冻结、内部拖拽，
与 GR 一致），并给出下一步几何工具的明确清单。

## 6. 文件与产物

- Lean: `ProjectionPhysics/Explorations/BlackHoleWormhole.lean`（BH1–BH7, WH1）
- 模拟: `scripts/verify_blackhole_wormhole.py`（报告 JSON+MD）、
  `scripts/blackhole_wormhole_3d.py`
- 图: `artifacts/blackhole/fig_flow_structures.png`（黑洞 vs 虫洞流场）、
  `fig_photon_freeze.png`（光锥关闭）、`fig_time_dilation.png`、
  `blackhole_3d.png`（漏斗+视界球）、`wormhole_3d.png`（双漏斗）、
  `wormhole_traverse.gif`（光子穿越动画）
