---
title: 最小核心命题：非零内部不变量 ⟹ 非零质量平方候选
source: session
created: 2026-08-11
last_confirmed: 2026-08-11
audience: self
stage: draft
schema_version: 2
confidence: high
entity_type: concept
tags: [minimal-core, mass, kernel, glueball, quadratic-form]
status: current
---

# 最小核心命题

> 这是整个 ProjectionPhysics 项目最简单、最可靠的核心结果。其余一切
> （SU(3)、Higgs 门户、时间、连续场、禁闭）都是后续扩展，不属于最小核心。

## 1. 最小命题（隐数/核版本）

```text
h ∈ K，Q(h) = h²，m²(h) := Q(h)
⟹ h ≠ 0 ⟹ m²(h) ≠ 0
```

最简推导只有四步：

```text
内部自由度 h
→ 二次型 Q(h) = h²
→ 定义质量平方 m² = Q(h)
→ h ≠ 0 ⇒ m² ≠ 0
```

对应代码：[`ProjectionPhysics/MinimalCore.lean`](../../ProjectionPhysics/MinimalCore.lean)（MC1）

- `minimalKernelElement`：h ∈ K（经 `hiddenKernelEmbedding` 进入 `ker(Re)`）
- `minimal_quadratic_formula`：Q(h) = h²
- `minimalMassSquared`：m²(h) := Q(h)
- `minimal_mass_squared_nonzero_of_nonzero`：h ≠ 0 ⟹ m²(h) ≠ 0

## 2. 胶球最小版本

保留最少的色单态条件：

```text
G = (a, b, c)，color profile = (1, 1, 1)
m_G² = |a|² + |b|² + |c|²
只要 a, b, c 中至少一个非零 ⟹ m_G² > 0
```

对应代码：[`ProjectionPhysics/MinimalCore.lean`](../../ProjectionPhysics/MinimalCore.lean)（MC2）

- `minimalTripletGlueball`：三色占据相等的色单态胶球
- `triplet_glueball_mass_squared_formula`：m_G² = |a|²+|b|²+|c|²
- `triplet_glueball_mass_squared_positive_of_any_nonzero`：∃ 非零分量 ⟹ m_G² > 0

## 3. 物理边界（必须明确）

这一步证明的是：

> **非零内部不变量产生非零质量平方候选。**

**不是**：

- ❌ 实验质量（无 MeV 数值）
- ❌ QCD 质量（无色规范场动力学）
- ❌ 胶球谱（无禁闭能量、无 J^PC 连续谱）

## 4. 后续扩展（不进最小核心）

| 扩展项 | 当前状态 | 说明 |
|---|---|---|
| SU(3) | `SU3Bridge.lean` 只有离散 C₃ 子群 | 连续八维 Lie 代数未支持 |
| Higgs 门户 | `GlueballBridge.lean` 0++ 解耦定理 | 混合本征值、连续归一化未支持 |
| 时间 | `HiddenEventClocks.lean` 离散时钟 | 连续时间未支持 |
| 连续场 | 全程整数系数 | 需系数环升级 ℤ→ℚ/ℝ |
| 禁闭 | 无 | 需 Yang–Mills 动力学 |

## 5. 与现有文件的关系

- [`HiddenOnlyHiggs.lean`](../../ProjectionPhysics/HiddenOnlyHiggs.lean)：m² = (yv)²（Yukawa 型，MC1 的实例化）
- [`GlueballBridge.lean`](../../ProjectionPhysics/GlueballBridge.lean)：纯胶子质量候选非零且非负（MC2 的源）
- [`theory-glueball-bridge.md`](./theory-glueball-bridge.md)：胶球物理边界详细评估
