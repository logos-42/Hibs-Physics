---
title: 麦克斯韦方程 × 空间流动假设（探索）
source: session
created: 2026-08-14
last_confirmed: 2026-08-14
audience: self
stage: draft
schema_version: 2
confidence: medium
entity_type: theorem
tags: [maxwell, electromagnetism, light-speed, space-flow, blackhole, prediction]
status: current
---

# 麦克斯韦方程 × 空间流动假设（探索）

> leo（2026-08-14）：把麦克斯韦方程和现有的数学进行组合，先写基础的
> 麦克斯韦方程，之后更新我的假设后写出麦克斯韦方程，应该有预言会出现。

## 0. 基础假设修正（leo 指出，本页起点）

**上一轮黑洞模块（BH2/BH3）没有完整安装 SLS2 公设**：它把光子当作
"相对空间以 c 传播的波"（Gordon 光锥 = Hamilton–Lisle 河流模型）——
那是 SG 弱场工具的套用。按公设重写：

```text
SLS1: 空间速度矢量 C(x)，|C| = c 处处（矢量光速普适）
SLS2: 光子 = 完全随空间（IsComoving，相对运动 = 0）
SM1:  光子随流 ⟹ |dx/dt| = |C| = c ⟹ dτ² = 0（不花时间）

⟹ 黑洞 = 矢量流场 C 的汇（流线全部终止于奇点）
  光子 = 流线本身；逃逸 = 逆流 = 违背 SLS2
  ⟹ 逃逸不可能是公设的直接推论（PH2 Lean 已证），不借用 GR
```

## 1. 基础麦克斯韦方程（标准）

```text
真空（1+1 维种子，MF1–MF2）：
  ∂_t²E = c²∂_x²E（波动方程）
  色散：ω² = c²k² ⟺ (ω−ck)(ω+ck) = 0 ⟺ ω = ±ck（双向光速）
  c = 1/√(μ₀ε₀) ⟹ c²·μ₀ε₀ = 1（MF2 Lean 已证）
```

数值：leapfrog FDTD（CFL=1 精确），高斯行波速度 = 1.000c ✓。

## 2. 更新后的麦克斯韦方程（leo 假设）

**方程形式不变；c 的身份改变**（MF3–MF4，Lean 已证）：

```text
MF3 ★ 光速 = 空间属性 = 麦克斯韦速度：
     1/√(μ₀ε₀) = c ⟹ c²μ₀ε₀ = 1（c 是空间等效速度，不是电磁参数）
MF4 电磁波 = 空间流动的波动；光子 = 完全随空间（SLS2）
     ⟹ |v_photon| = |C| = c 恒 ⟹ dτ² = 0 恒（自洽）
     色散双向模 ω = ±ck 保持（局域光速不变 = 流动普适，SLS6）
```

## 3. 黑洞（公设版）

| 项 | 内容 |
|---|---|
| 黑洞 | 内向流区域（r < r_h：C = −c·r̂，流线全部入奇点） |
| 视界 | 流线不可逃逸面（内部全内向 + 逆流 = 违背 SLS2） |
| 逃逸不可能 | **公设直接推论**（PH2：IsComoving + 内向流 ⟹ 不逃逸） |
| |C| = c | 数值验证：偏差 < 1e-12 ✓ |
| dτ² = 0 | 沿流线 < 1e-12 ✓ |
| 内部流线 | 全部终止于奇点（数值 ✓） |

## 4. 预言（P1–P4）

| 预言 | 内容 | 状态 |
|---|---|---|
| P1 | 视界内光必入奇点（随流公设） | 数值 ✓ + PH2 Lean |
| P2 | 引力红移：ω₂/ω₁ = (c−v₂)/(c−v₁)（MF5） | 方向 ✓；数值匹配 GR 需流场形状自由参数 |
| P3 | 视界横向模消失（黑洞内电磁波纯径向，MF6） | 数值 ✓ |
| P4 | 光速各向同性保持（|C|=c ⟹ 任意方向 \|v\|=c） | 结构上不可测（诚实） |

## 5. 诚实 4 层判定

| 层 | 判定 | 理由 |
|---|---|---|
| ① 数学恒等式 | 真但平凡 | 色散因子分解/红移代数/流线积分 |
| ② 结构对应 | 已知物理 | 流场汇 = 黑洞的拓扑图像（GR 几何重述） |
| ③ 数值匹配 | 需额外输入 | 红移与 GR 一致 ⟺ 流场 v_r(r) 取 GR 形状——仓库无第一性来源 |
| ④ 概念重构 | 不可证伪 | 解释层变化；P4 结构上不可测 |

**真实发现判据未满足**。黑洞半径 r_h 是流场参数（未锚定到质量）——
与"第二输入未找到"同源。本模块价值：SLS2 公设的自洽推导路径
（逃逸不可能从公设直接推出，不再借用 GR），以及预言形式的完整清单。

## 6. 文件与产物

- Lean: `ProjectionPhysics/Explorations/MaxwellFlow.lean`（MF1–MF6, PH1–PH2）
- 模拟: `scripts/verify_maxwell_flow.py`
- 图: `artifacts/maxwell/fig_wavepacket.png`（基础波包）、
  `fig_blackhole_flow.png`（|C|=c 流场黑洞）、`fig_redshift.png`（P2）、
  `photon_infall.gif`（光子随流入黑洞动画）
