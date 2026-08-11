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

## 2. 最小命题

```text
内部运动状态 s（自旋 / 内部关系：隐数内部流）
→ 空间运动 F（空间本身的运动：space flow）
→ 质量 m := 锚定效果（旋量阻抗：对空间运动的抵抗）
→ 内部运动非零 ⟹ m ≠ 0
```

对应代码：[`ProjectionPhysics/MinimalCore.lean`](../../ProjectionPhysics/MinimalCore.lean)（MC1）

- `anchorMassOf`：锚定质量候选 = 空间流产生的旋量阻抗
- `anchor_mass_formula`：m = |隐流差| + |横向差|（旋量阻抗范数）
- `anchor_mass_nonzero_of_internal_motion`：内部运动非零 ⟹ m ≠ 0
- `anchor_mass_zero_of_no_internal_motion`：静止流 ⟹ m = 0（光子边界）

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
