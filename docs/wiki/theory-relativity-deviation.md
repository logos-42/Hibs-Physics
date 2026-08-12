---
title: 相对论公式的差值项：矢量光速 − 质量物体速度
source: session
created: 2026-08-11
last_confirmed: 2026-08-11
audience: self
stage: draft
schema_version: 2
confidence: medium
entity_type: theorem
tags: [relativity, deviation, lightspeed, gamma, velocity-addition, vector-lightspeed]
status: current
---

# 相对论公式的差值项：矢量光速 − 质量物体速度

> leo（2026-08-11）：总结下来我们构造的相对论公式里面应该多了一个
> 矢量光速和质量物体速度的差值？

## 1. 核心答案

**是的——差值 (c − v) 确实出现在公式里，但被相对论精确消灭。**

对应代码：
- [`ProjectionPhysics/RelativityDeviation.lean`](../../ProjectionPhysics/RelativityDeviation.lean)（RD1–RD7，mathlib）
- [`scripts/verify_relativity_deviation.py`](../../scripts/verify_relativity_deviation.py)（数值）

```text
经典速度合成（伽利略）:   w = c − v      ← 差值显式出现（光速依赖观测者）
相对论速度加法:           w = (c−v)/(1−cv/c²)  ← 差值在分子
                          ⟹ 恒等于 c     ← 差值被分母 (1−v/c) 精确抵消
★ 光速不变的代数根源 = 分母抵消分子差值
```

## 2. 定理（Lean 已证）

| 定理 | 内容 | 物理意义 |
|---|---|---|
| RD1 | (c−v)/(1−cv/c²) = c | ★ 光速不变 = 差值被分母抵消 |
| RD2 | 经典 w=c−v ≠ 相对论 w=c（v≠0 时） | 差值在经典极限的产物，相对论消除 |
| RD3 | γ²(c, c−u) = γ²_dev(c, u) | 差值参数化 = 同一公式重写 |
| RD4 | u=0 ⟹ 1−(c−u)²/c² = 0 | 光子 γ=∞ ⟹ dτ=0（不花时间） |
| RD5 | u=c ⟹ 1−(c−u)²/c² = 1 | 静止物质 γ=1（正常时间） |
| RD6 | 1−(c−u)²/c² = (2cu−u²)/c² | 分母恒等式 |
| RD7 | 0<u<c ⟹ 0<2cu−u² | 质量物体分母为正（γ 有限） |

## 3. 洛伦兹因子的差值参数化

```text
标准:   γ²(v) = 1/(1−v²/c²)          v = 物质速度
差值:   γ²(u) = 1/(2u/c − u²/c²)     u = c − v = 偏离空间流动的程度

u=0（光子完全随空间）⟹ 分母 0 ⟹ γ=∞ ⟹ dτ=0（不花时间）
u=c（物质静止）      ⟹ γ=1（正常时间）
0<u<c（质量物体）    ⟹ 0<γ<∞（时间膨胀, 偏离越大越慢）
```

能量动量（差值形式）：
```text
E(u) = mc²/√(2u/c − u²/c²)
p(u) = m(c−u)/√(2u/c − u²/c²)
静止 (u=c): E=mc², p=0 ✓
```

## 4. 诚实边界

- **差值参数化不是新公式**——与标准相对论数值完全一致（RD3 保证）
- 新在**解释层**：u = 矢量光速 − 物质速度 = 偏离空间流动的程度
- 与 SM 系列一致：光子 u=0（完全随空间）⟹ 时间冻结；质量 = 偏离
- 无新数值预言；差值项的价值 = 让"质量=偏离空间"机制显式进入
  相对论公式的推导

## 5. 与已有模块的连接

- SLS6：observedPhotonVelocity = relativeMotionZero − o.relative
  （观测者测光子 = 零参考 − 观测者相对空间——同样的差值结构）
- SM3：deviationFromSpaceFlow = dx/dt − c（物质相对空间流动）
- LR：β = tanh θ（快度 = 偏离空间流动的程度）
- SM6：时间膨胀 1−tanh²θ = 1/cosh²θ（偏离越大时间越慢）
- ★ 本模块把差值显式写进速度加法与洛伦兹因子——"公式里的差值项"
