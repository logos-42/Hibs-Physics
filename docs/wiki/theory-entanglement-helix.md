---
title: 双螺旋纠缠：流动空间中的量子纠缠几何（探索）
source: session
created: 2026-08-14
last_confirmed: 2026-08-14
audience: self
stage: draft
schema_version: 2
confidence: medium
entity_type: theorem
tags: [entanglement, bell, chsh, double-helix, space-flow, photon, exploration]
status: current
---

# 双螺旋纠缠：流动空间中的量子纠缠几何（探索）

> leo（2026-08-14）：用流动空间构造三维光线模型——光的纠缠是双螺旋
> 轨迹，光随着空间流动。本页记录模型、贝尔检验结果与诚实结论。

## 1. 模型

```text
流动空间假设（主线，SLS2）: 光子 = 完全随空间流动（dτ = 0）
  ⟹ 光子的世界线就是空间流动线

纠缠光子对 = 同一流动管内的双螺旋：
  光子 1（相位 λ）   在检偏角 a 的结果  A(λ,a) = sign(cos 2(λ−a))
  光子 2（相位 λ+π） 在检偏角 b 的结果  B(λ,b) = −sign(cos 2(λ−b))   （反相股）
  λ ~ Uniform[0, π)   （螺旋相位均匀，周期 π）

几何图像：
  两股螺旋线沿公共轴（空间流动方向）展开，相位差 π；
  源点（z=0）产生纠缠对 → 两股随流动反向传播 → 两端检偏器测量。
  3D 模型：artifacts/entanglement/helix_3d.png / helix_3d.gif
```

## 2. 检验结果（数值，蒙特卡洛 N≥4×10⁶）

| 检验 | 双螺旋（经典读出） | 量子力学 | 实验 |
|---|---|---|---|
| E(0) 对齐反关联 | −1.000 ✓ | −1.000 ✓ | −1 ✓ |
| E(π/8) | −0.500 | −0.707 | — |
| E(3π/8) | +0.500 | +0.707 | — |
| **CHSH \|S\|** | **2.0005 ± 0.004** | **2.8284** | 2.697 ± 0.015（Aspect 1982） |

- 关联函数形状：螺旋 E(Δ) = −1 + 4Δ/π（**线性**）；量子 E(Δ) = −cos 2Δ。
  两条曲线在 Δ = 0、π/4、π/2 三点相交，π/8 与 3π/8 处分叉——这正是
  CHSH 检验所探测的区域。
- 流旋转不变性：相位被流动旋转任意 δ（介质/引力旋转），扫描全部 δ，
  |S| 最大恰为 2.0——**流动旋转改变不了结论**（CHSH 定理的数值确认）。
- 量子统计读出：同一双螺旋几何 + Born 规则（流携带联合单态）
  ⟹ S = −2.8283 ≈ 2√2，与实验一致。

## 3. Lean 形式化（`ProjectionPhysics/Explorations/EntanglementHelix.lean`）

| 定理 | 内容 |
|---|---|
| EH1 `chsh_core` | 四个 ±1 结果的 CHSH 组合 ∈ {−2, 2}（纯代数，omega） |
| EH2 `chsh_expectation_bound` | ★ **贝尔不等式（CHSH）代数形式：任何局域确定性 ±1 模型（结果只依赖本地设置与共享隐变量，分布任意）⟹ \|S\| ≤ 2** |
| EH3 `helix_strand_anticorrelation` | 反相股 B = −A ⟹ A·B = −1（符号必然相反） |
| EH4 `helix_aligned_correlation` | 对齐设置关联恒为 −1：E(a,a) = −1（任意分布取平均） |

`lake build` 全绿（4126 jobs）。EH2 是贝尔定理的代数内核——双螺旋作为
局域模型是其特例，因此无论 λ 分布多强关联（含"两股相位完全锁死"的
最大关联），|S| 都无法超过 2。

## 4. 诚实结论（4 条，写死的防过度声称）

1. **双螺旋给出"纠缠的一半"**：几何锁相（反相股）⟹ 对齐设置完全反
   关联 E(0) = −1，与量子一致。这是"纠缠"最直观可感的部分。
2. **经典读出无法证明量子纠缠**：E(Δ) 是线性 −1+4Δ/π，CHSH |S| = 2.0
   恰好饱和局域界——**双螺旋是"经典能做到的最像量子"的模型**（达到
   经典最优），但仍被贝尔实验（Aspect 1982: 2.697；2015 无漏洞实验
   ≈2.83）排除。CHSH 定理（|S| ≤ 2）已在 Lean 证明。
3. **流旋转、更强的关联分布都救不了它**：局域界是硬的（EH2）。
4. **要 2.828 必须换读出规则**：同一几何 + Born 规则（流携带联合单态
   ψ = (|HV⟩−|VH⟩)/√2）⟹ 精确复现量子统计。
   ⟹ **纠缠不在螺旋轨迹的几何里，在流场携带的波函数（联合量子态）里；
   双螺旋 = 纠缠的真实空间几何投影，不是纠缠的机制。**

## 5. 与主线的连接 + 可检验预言

- **连接**：本模型是矢量光速（SLS1–SLS2，光子=完全随空间流动）的
  直接延伸——纠缠对 = 两条共享同一流动管的流线。不新增公理。
- **可检验预言（仓库唯一出口）**：空间流动非均匀（引力 = 流动非均匀，
  SG/SM 主线）⟹ 双螺旋两股相位差随路径积分改变 ⟹ 纠缠关联 E(Δ)
  出现**引力依赖的相移**。对应真实物理中"引力对纠缠相位"的实验设想
  （光子对通过不同引力势），当前实验精度未测——这是本模型的
  第一个可证伪出口。
- **后续候选**：Tsirelson 界 2√2 的 Lean 形式化（需 Pauli 矩阵自旋
  期望，本模块诚实边界）；玻姆型引导场（构型空间流动）的数值版。

## 6. 文件与产物

- Lean: `ProjectionPhysics/Explorations/EntanglementHelix.lean`（EH1–EH4）
- 模拟: `scripts/verify_entanglement_helix.py`（报告 JSON+MD 在
  `artifacts/entanglement/`）、`scripts/entanglement_helix_3d.py`
- 图: `artifacts/entanglement/fig_e_delta.png`（E(Δ)）、`fig_chsh.png`（CHSH）、
  `fig_flow_rotation.png`（流旋转扫描）、`fig_heatmap.png`（差值热图）、
  `helix_3d.png`/`helix_3d.gif`（三维模型）
