---
title: 自旋 = 空间三方向结构的涌现（行动探索）
source: session
created: 2026-08-14
last_confirmed: 2026-08-14
audience: self
stage: draft
schema_version: 2
confidence: medium
entity_type: theorem
tags: [spin, clifford, three-directions, su2, double-cover, thomas-precession]
status: current
---

# 自旋 = 空间三方向结构的涌现（行动探索）

> leo（2026-08-14）：电子的自旋在狄拉克看来是复数的内禀属性（方程
> 结构副产品，方程本身是假设）；托马斯进动基于狭义相对论（预设自旋）。
> 都不是基于我们的假设（空间流动）。需要完整安装假设重新推导，看会
> 不会产生电子的自旋内禀属性。前人有误区——这是行动探索，不是原有
> 的数学经验。

## 1. 推导路径（`SpinFromSpace.lean` SFS1–SFS5 全证，零 sorry）

```text
SLS1: 空间速度矢量三方向 C = (C₁, C₂, C₃)，|C| = c
  ⟹ 三方向流动的旋转结构 ⟹ Clifford 代数（σᵢσⱼ = −σⱼσᵢ）
SFS1 ★ 复数 = 空间三方向的体积元：i := σ₁σ₂σ₃（三方向定向）
      ——狄拉克的"复数内禀属性"从空间三方向结构涌现，不是公设
SFS2 σ₁σ₂ = iσ₃（平面涌现法向量：两方向乘积 = 法向量定向）
SFS3 ★ 自旋算符 = 空间旋转生成元：[σ₁,σ₂] = 2iσ₃（so(3)/su(2) 生成元）
SFS4 σ₁²+σ₂²+σ₃² = 3I（三方向签名 = 3 = 单位球面半径平方）
SFS5 ★ 自旋 1/2 的 Casimir：S² = ¾I = s(s+1)I，s = ½
      ——Cℓ(3) 最小忠实表示是 2 维 ⟹ 自旋 1/2（SU(2) 双重覆盖）
```

## 2. 数值验证（`scripts/verify_spin_from_space.py`）

| 检验 | 结果 |
|---|---|
| Clifford 代数（反交换/i 涌现/对易/S²=¾） | 7 项全 true ✓ |
| e^{iπσ₁} = −I（旋转 π 变号） | true ✓ |
| e^{2iπσ₁} = +I（2π 复原）/ e^{4iπσ₁}（4π） | true ✓ |
| 标准托马斯 ω_Th = (γ²−1)v/r | 0.167 |
| 流动版 ω_flow = γ·\|∇×C\| | 0.289（比值恰 √3，呼应三方向主题——数值巧合候选） |

图：`artifacts/spinspace/double_cover.png`（SU(2) 双重覆盖：2π 变号）、
`three_directions.png`（三方向 ⟹ σ）。

## 3. 行动探索判定（诚实）

| 项 | 判定 |
|---|---|
| 自旋的代数结构从空间三方向涌现 | ✓ 完整（i/法向量/对易/Casimir/2 维表示，Lean 全证） |
| "复数内禀"的根源 | ✓ i = 三方向体积元（比狄拉克更深：自旋不是方程副产物，是 SLS1 的代数必然） |
| 旋转 2π 变号（费米子拓扑属性） | ✓ SU(2) 双重覆盖（数值） |
| 托马斯进动的流动版 | 结构对应（∇×C = 磁场 = 自旋的场，SF5 连接）；数值未锚定 |
| "为什么电子用 2 维表示" | ✗ 仍输入：Cℓ(3) 表示论保证 2 维是最小忠实表示（必然），但选中它是实验事实 |
| ℏ 的数值 | ✗ 仍输入（与"第二输入未找到"同源） |

**结论**：自旋内禀属性的**代数结构**（i、对易、s=½、2 维、2π 变号）从
空间三方向完整涌现——比狄拉克/托马斯更深的第一性层次；自旋的**取值**
（2 维 vs 其他表示）与 ℏ 数值仍是输入。前人误区（用户观点）的方向
得到部分支持：自旋不需要作为量子力学公设（其代数结构来自空间结构），
但完整推导仍需"第二输入"。

## 4. 文件与产物

- Lean: `ProjectionPhysics/Explorations/SpinFromSpace.lean`（SFS1–SFS5）
- 模拟: `scripts/verify_spin_from_space.py`
- 图: `artifacts/spinspace/double_cover.png`、`three_directions.png`
