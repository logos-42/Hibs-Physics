---
title: 矢量光速：空间本身的等效速度（新概念）
source: session
created: 2026-08-11
last_confirmed: 2026-08-11
audience: self
stage: draft
schema_version: 2
confidence: medium
entity_type: concept
tags: [light-speed, space-motion, photon, electron, new-concept, anchoring]
status: current
---

# 矢量光速：空间本身的等效速度（新概念）

> leo 提出的新概念（2026-08-11）：光速不是"物质/信号在空间中的最大
> 速度"（物质属性），而是**空间本身的等效速度**——空间自身以 c 运动，
> 物质在其中运动是相对空间运动而言的。

## 1. 概念

```text
传统: 光速 c = 物质/信号在空间中的最大速度 (物质属性)
新概念: 光速 c = 空间本身的等效速度 (空间属性)

空间自身在三个方向运动 (三方向假设: 平面内圆周/椭圆 + 法向量)
⟹ 矢量光速 = 空间运动在三方向的等效速度矢量
```

与三方向假设的连接：空间在三个方向运动，矢量光速就是这个运动在
三方向的等效速度。**c 是空间的运动属性，不是物质的运动极限。**

## 2. 代数种子（SpaceLightSpeed.lean）

对应代码：[`ProjectionPhysics/SpaceLightSpeed.lean`](../../ProjectionPhysics/SpaceLightSpeed.lean)（SLS1–SLS3）

### SLS1. 矢量光速结构

- `SpaceVelocity c2`：空间速度矢量（三方向），模 = c² 普适常数
- `light_speed_is_universal_space_property`：**任何空间点的等效速度模相同**
  ——c 是空间属性，不是物质速度极限（核心定理）
- `xDirectionalSpace`：空间沿 x 方向运动的实例
- `triDirectionalSpace`：三方向空间运动（平面 + 法向量）

### SLS2. 光子 = 完全随空间运动

- `RelativeMotion`：物质相对空间的运动（物质速度 − 空间运动）
- `IsComoving`：完全随空间运动（相对运动为零）
- `anchor_mass_zero_of_photon`：**无内部运动 + 完全随空间 ⟹ 零锚定 ⟹ 零质量**
- #eval：光子锚定质量 = 0

### SLS3. 电子 = 自旋偏离空间运动

- `anchor_mass_positive_of_internal_motion`：**自旋非零 ⟹ 锚定质量为正**
- `anchor_mass_positive_of_relative_motion`：偏离空间运动也产生锚定
- #eval：电子锚定质量 = 1；偏离 + 自旋 = 9

## 3. 与最小核心的关系

| 概念 | 最小核心 (MC1) | 矢量光速 (SLS) |
|---|---|---|
| 内部运动 | 自旋 = Clifford σψ 旋量流 | 自旋 = MatterState.spin |
| 锚定质量 | 旋量流分量范数 | 自旋 + 相对空间运动范数 |
| 光子 | 零旋量 ⟹ 零锚定 | 零自旋 + 完全随空间 ⟹ 零锚定 |
| 新增 | — | **相对空间运动也是锚定来源** |

## 4. 诚实边界

- 这是**新概念的代数种子**（结构 + 序关系定理），不是连续时空形式化。
- 没有狭义/广义相对论：无洛伦兹变换、无度规、无场方程。
- 光速普适性是**结构内建**（SpaceVelocity 携带 speed_squared 证明），
  不是从更基本原理推出的——与标准"光速不变"同样是公设级别。
- 矢量光速如何与 GR 结合（思路 A：加入运动空间的矢量光速）是后续扩展。
