---
title: 相对论重构：矢量光速假设下的公式变化
source: session
created: 2026-08-11
last_confirmed: 2026-08-11
audience: self
stage: draft
schema_version: 2
confidence: medium
entity_type: concept
tags: [relativity, light-speed, inertia, lorentz, dirac, space-flow]
status: current
---

# 相对论重构：矢量光速假设下的公式变化

> leo（2026-08-11）：狄拉克方程根据相对论推导，而我的矢量空间运动
> 等效速度改变了相对论的前提假设。需要重新考虑：在这种情况下，
> 相对论的公式会怎么变？推导出的狄拉克方程怎么变化？

## 1. 核心结论

**相对论公式形式不变，解释层全部改变**：

```text
公式不变 (光速不变保持 ⟹ 洛伦兹不变性保持):
  洛伦兹变换 / E² = p²c² + m²c⁴ / 狄拉克方程 (γ^μ p_μ − m)ψ = 0

解释改变:
  c: 物质速度极限 → ★ 空间本身的流动速度 (矢量光速)
  m: 裸参数 (输入) → ★ 锚定 = 手征耦合 (DB4)
  惯性系: 任意匀速系 → ★ 随空间流动的参考系 (SLS6)
  引力: 时空弯曲 → 空间流动的非均匀性 (GR 重构方向)
```

## 2. 推导路径（SLS6，Lean 已证）

对应代码：[`ProjectionPhysics/SpaceLightSpeed.lean`](../../ProjectionPhysics/SpaceLightSpeed.lean)（SLS6）

```text
新公设:
  空间以恒定速度 C 流动, |C| = c (SLS1: 光速 = 空间属性)
  物质运动 = 相对空间的运动 (SLS2)
  光子 = 空间流动的波动表现 (完全随空间运动)

推论:
  惯性系 = 随空间流动的系 (IsInertialFrame, SLS6)
  光速不变 = 空间流动普适 (light_speed_invariance_comoving_observer, SLS6)
  洛伦兹不变性 = 空间流动均匀 (IsUniformSpaceFlow, SLS6)
  引力 = 空间流动非均匀性 (GR 重构种子)
```

- `IsInertialFrame`：惯性系 = 完全随空间运动的参考系
  （惯性 = 随空间，非惯性 = 偏离空间）
- `light_speed_invariance_comoving_observer`：★ 任何随空间观测者
  测到的光速恒定（= 空间流动速度），观测者无关性内建
- `non_inertial_observer_sees_photon_motion`：偏离空间的观测者
  看到光子相对运动非零（锚定质量 = 偏离程度，SLS3 呼应）
- `IsUniformSpaceFlow` + `uniform_flow_iff_light_speed_universal`：
  均匀空间流动 ⟺ 光速普适

## 3. 狄拉克方程的变化（DB4 呼应）

```text
形式不变: (γ^μ p_μ − m)ψ = 0 保持 (DB3-DB6: γ 代数已证)
质量项变化:
  传统: m = 裸参数 (输入)
  新假设: m = 锚定 = 手征耦合强度
  DB4: (γ⁰−1)ψ = 0 ⟺ ψ_L = ψ_R — 质量解要求左右手耦合
  DB5: m = 0 ⟹ 手征对称 (Weyl) = 光子 = 零锚定
```

## 4. 数值验证（诚实）

脚本：[`scripts/verify_relativity_rebuild.py`](../../scripts/verify_relativity_rebuild.py)

- **公式保持**：E² = p²c² + m²c⁴ 在 m=0（光子）时 E = pc，
  无质量色散与实验一致 ✓
- **m 的来源**：m_e = 0.511 MeV vs 锚定候选 M₀ ≈ 0.987 GeV，
  差 966 倍——数值未确立（与"第二输入未找到"一致）
- **光速不变**：随空间观测者测光速恒定（SLS6 ✓，实验 ✓）

## 5. 诚实边界

- 这是**解释层的重构**，不是新公式：所有标准相对论公式
  在新假设下依然成立（这是与实验相容的关键）
- 未形式化：时空度规、测地线方程、爱因斯坦场方程——
  GR 完整重构是后续方向，当前只有概念种子
- 空间流动是否均匀是经验问题：若不均匀（如星系尺度），
  洛伦兹不变性应被修正——这是可检验预言（需未来工作）
- 质量数值缺口未解决：公式结构 ✓，数值来源 ✗
