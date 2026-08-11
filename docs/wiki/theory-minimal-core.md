---
title: 最小核心命题：质量 = 内部运动状态对空间运动的锚定
source: session
created: 2026-08-11
last_confirmed: 2026-08-11
audience: self
stage: draft
schema_version: 2
confidence: high
entity_type: concept
tags: [minimal-core, mass, spin, anchoring, space-motion, glueball]
status: current
---

# 最小核心命题（锚定版本）

> 整个 ProjectionPhysics 项目最简单、最可靠的核心结果。质量默认有**量的
> 结构**：它不是从场与激发态来描述的（不是激发能量），而是物质为抵抗
> **空间本身的运动**产生的**锚定效果**。

## 1. 方向修正（2026-08-11）

旧版把质量写成场的二次型 `m² = Q(h) = h²`（激发态语言）。这默认质量是
"场的一种激发量"。修正为：

- 质量 = 物质抵抗空间本身运动的**锚定效果**；
- 来源是**内部运动状态**（自旋 / 内部关系），不是场的激发；
- 夸克自己的内部关系组成质子质量，用运动状态来描述；
- 电子有电荷（"电"），但质量来自**自旋抵御空间运动**；
- 正反电子碰撞激发的光子，是**一瞬间摆脱了空间运动锚定**的激发场粒子
  ⟹ 零锚定 ⟹ 无质量。

## 2. 最小命题（旋量流版，2026-08-11 v2）

自旋本身就是运动状态——不需要空间位移差来描述：

```text
内部运动状态 s（自旋：Clifford 生成元 σ 作用在旋量 ψ 上的流 σψ）
→ 空间运动 F（空间本身的运动）
→ 质量 m := 锚定效果（旋量流的分量范数：对空间运动的抵抗）
→ 自旋非零 ⟹ m ≠ 0
```

对应代码：[`ProjectionPhysics/MinimalCore.lean`](../../ProjectionPhysics/MinimalCore.lean)（MC1）

- `spinFlow σ ψ`：自旋算子作用在旋量上 = 内部运动状态（旋量流）
- `spinFlowAnchorMass`：锚定质量候选 = 旋量流四分量范数之和
- `spin_flow_anchor_mass_pos_of_spinor_nonzero`：非零旋量 ⟹ 锚定质量 > 0
- `spin_flow_anchor_mass_zero_of_zero_spinor`：零旋量 ⟹ m = 0（光子边界）

**隐数实现**（MC1h，核方向表达）：

- `hiddenSpinAnchorMassSquared h = h²`：自旋状态编码为核方向（隐数 h ∈ ker Re）
- `hidden_spin_anchor_mass_squared_nonzero`：非零隐数 ⟹ 锚定质量平方 ≠ 0
- `hidden_spin_anchor_mass_squared_zero_of_zero`：零隐数 ⟹ 0

Lean #eval 落地：σ₁·(1,0)→1、σ₁·(0,1)→1、σ₁·(1,1)→2；隐数版 3→9、−4→16。

## 3. 胶球最小版本

保留最少的色单态条件：三个胶子的内部运动状态 (a, b, c) 组成色单态。

```text
G = (a, b, c)，color profile = (1, 1, 1)
m_G² = |a|² + |b|² + |c|²
只要 a, b, c 中至少一个非零 ⟹ m_G² > 0
```

对应代码：[`ProjectionPhysics/MinimalCore.lean`](../../ProjectionPhysics/MinimalCore.lean)（MC2）

- `minimalTripletGlueball`：三色占据相等的色单态胶球
- `triplet_glueball_mass_squared_formula`：m_G² = |a|²+|b|²+|c|²
- `triplet_glueball_mass_squared_positive_of_any_nonzero`：∃ 非零分量 ⟹ m_G² > 0

## 4. 物理边界（必须明确）

这一步证明的是：

> **非零内部运动状态产生非零锚定质量候选。**

**不是**：

- ❌ 实验质量（无 MeV 数值）
- ❌ QCD 质量（无色规范场动力学）
- ❌ 胶球谱（无禁闭能量、无 J^PC 连续谱）
- ❌ 时空本身弯曲的广义相对论锚定

## 5. 后续扩展（不进最小核心）

| 扩展项 | 当前状态 | 说明 |
|---|---|---|
| SU(3) | `SU3Bridge.lean` 只有离散 C₃ 子群 | 连续八维 Lie 代数未支持 |
| Higgs 门户 | `GlueballBridge.lean` 0++ 解耦定理 | 混合本征值、连续归一化未支持 |
| 时间 | `HiddenEventClocks.lean` 离散时钟 | 连续时间未支持 |
| 连续场 | 全程整数系数 | 需系数环升级 ℤ→ℚ/ℝ |
| 禁闭 | 无 | 需 Yang–Mills 动力学 |

## 6. 与现有文件的关系

- [`HiddenSpacePhysics.lean`](../../ProjectionPhysics/HiddenSpacePhysics.lean)：HSP3 "自旋 = 对空间运动的旋量阻抗"（锚定语言的现成结构，MC1 的源）
- [`HiddenOnlyHiggs.lean`](../../ProjectionPhysics/HiddenOnlyHiggs.lean)：m² = (yv)²（Yukawa 型，保留为扩展比较对象）
- [`GlueballBridge.lean`](../../ProjectionPhysics/GlueballBridge.lean)：纯胶子质量候选非零且非负（MC2 的源）
- [`theory-glueball-bridge.md`](./theory-glueball-bridge.md)：胶球物理边界详细评估

## 7. 数值验证结果（2026-08-11，诚实报告 v2）

对"质量 = 自旋 × 空间阻抗"代入 CODATA/PDG 数值后（详见
[`theory-mass-anchoring-validation.md`](./theory-mass-anchoring-validation.md)）：

- **电子**：m_cand = S/(λ_c·c)、S/(r_e·c)、ℏ/(c·a₀) 全部是**恒等式重排**，
  无独立预言力（这些长度本身由 m_e 定义）。
- **胶球谱（v2 最有价值的结果）**：格点 m(2++)/m(0++) = 1.4035 ≈ √2，
  **m² = N·M₀²（N 整数模式数）与格点 0++(N=2)/2++(N=4) 相容**，
  M₀ ≈ 1.21 GeV；0-+(N=5) 偏差 ~6%。谱形 √N 是结构预言。
- **0++ 矛盾已修正**：J=0 是总角动量，内部是两个自旋-1 胶子 ⟹
  内部运动非零，与"质量=内部运动锚定"**不矛盾**（v1 论证错误）。
- **失败点**：异常磁矩 a_e 需 QED 圈图；m_p/m_e=1836 需内部结构。
- **结论**：当前是**自洽的序关系框架**（非零 ⟹ 非零）+ 胶球谱比 √N
  这个接近数值预言的唯一方向；MC1/MC2 代数定理不受影响。
