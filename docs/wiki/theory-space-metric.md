---
title: 空间流动度规：GR 重构种子（矢量光速假设下的度规推导）
source: session
created: 2026-08-11
last_confirmed: 2026-08-11
audience: self
stage: draft
schema_version: 2
confidence: medium
entity_type: theorem
tags: [metric, general-relativity, space-flow, proper-time, photon, massless, mathlib]
status: current
---

# 空间流动度规：GR 重构种子

> leo（2026-08-11）：广义相对论也要变一下推导公式。因为在我的假设下，
> 空间的等效速度是光速，所以空间的速度需要一个矢量光速来描述物质视角
> 的运动。在无质量视角下，是空间本身在运动，所以不花时间。

## 1. 核心命题

对应代码：[`ProjectionPhysics/SpaceMetric.lean`](../../ProjectionPhysics/SpaceMetric.lean)

```text
新假设:
  空间以速度 v = c 流动（矢量光速 = 空间本身的等效速度）
  光子 = 完全随空间流动（dx = c·dt）

推导:
  固有时间 dτ² = dt² − dx²/c²（标准，绝对框架）
  SM1 ★ 光子（dx = c·dt）⟹ dτ² = 0（不花时间）
  SM2 质量粒子（|dx| < |c·dt|）⟹ dτ² > 0（花时间）
  SM3 物质视角：相对空间流动 u = dx/dt − c；光子 u=0 ⟹ dτ²=0
  SM3c 质量 ⟹ 偏离空间流动：dτ²>0 ⟹ dx ≠ c·dt（★ "无法随空间以 c 运动"）
  SM3d 偏离空间流动 ⟹ 质量：|dx| < |c·dt| ⟹ dτ²>0
  SM4 度规一致性：dτ² = g_μν Δx^μ Δx^ν（g = diag(1, −1/c²)）
  SM5 det(g) = −1/c²（时空体积不随流动改变）
  SM6 时间膨胀：1 − tanh²θ = 1/cosh²θ（偏离越大时间越慢）
```

## 2. 物理意义（leo 的洞察形式化）

**"无质量视角下，是空间本身在运动，所以不花时间"**：
- 光子完全随空间流动（dx = c·dt）——它的世界线就是空间流动线
- dτ² = dt² − (c·dt)²/c² = 0 ⟹ **光子的固有时间恒为零**（SM1）
- 这正是相对论的已知事实（光沿零测地线），但现在有了新解释：
  不是"光速不可达"的极限，而是**光子 = 空间流动本身**

**"空间的速度需要一个矢量光速来描述物质视角的运动"**：
- 物质视角的运动 = 相对空间流动的运动 u = dx/dt − c（SM3）
- 光子：u = 0（与空间流动同步）⟹ 零固有时间
- 质量粒子：u ≠ 0（偏离空间流动）⟹ 正固有时间
- **时间流逝 = 偏离空间流动的程度**（SM2 + SM6）

## 3. GR 重构方向（诚实边界）

本模块是 **GR 重构的种子**，不是完整 GR：
- ✅ 已形式化：度规（1+1 维）、固有时间、光子零固有时间、
  质量正固有时间、时间膨胀、保体积
- ❌ 未形式化：时空曲率、测地线方程、爱因斯坦场方程、
  引力 = 空间流动非均匀性的完整推导
- 诚实标注：SM1–SM6 的代数内容与标准相对论一致
  （dτ² = dt² − dx²/c² 是闵可夫斯基度规）——
  **新的是解释层**：c 是空间流动速度、光子是空间流动本身、
  时间 = 偏离空间流动的程度
- 下一步候选：非均匀流动（v(x) 随位置变化）⟹ 有效度规
  g = diag(1−v²/c², v/c², ..., −1/c²)（Gordon 度规形式），
  这是真正"GR 变公式"的入口（流动的梯度 = 等效引力场）

## 5. 电子质量机制连接（leo：自旋的法向量运动轨迹）

对应代码：[`MinimalCoreMathlib.lean`](../../ProjectionPhysics/MinimalCoreMathlib.lean) MC5'

```text
机制链（Lean 全证）:
  自旋非零 (ψ ≠ 0)
  ⟹ σ₃ψ ≠ 0（自旋的法向量运动轨迹, spin_normal_flow_nonzero）
  ⟹ 法向量锚定 > 0（|(σ₃ψ)₀|² + |(σ₃ψ)₁|² > 0）
  ⟹ 质量 ⟹ 偏离空间流动（dx ≠ c·dt, SM3c）
  ⟹ dτ² > 0（花时间, 有质量, SM3d）
```

- `normal_direction_emerges`：σ₃ = −i·σ₁σ₂——法向量从平面内运动涌现
  （第三个方向不是独立假设）
- 光子：无法向量分量（平面内）⟹ 完全随空间 ⟹ m = 0
- 电子：自旋的法向量运动轨迹 ⟹ 偏离空间流动 ⟹ m > 0
- 胶球：三方向全参与（m_G² = |a|²+|b|²+|c|²）

数值（诚实）：`scripts/verify_electron_normal_spin.py`——法向量方向的
量级与平面内相同（ℏ/r₀ 量级），966 倍缺口未改变（量级由 r₀ 决定，
与方向无关；候选公式全是恒等式 m ≡ M₀/2）。机制方向正确，
数值缺口仍开放——需不在 ℏ/r₀ 量级内的独立输入。

## 6. mathlib 证明要点

| 定理 | 证明方法 |
|---|---|
| `photon_proper_time_zero` | rw [h] + field_simp + ring |
| `massive_proper_time_positive` | sq_lt_sq.mpr + field_simp + div_pos |
| `photon_comoving_zero_deviation` | field_simp（u=0 ⟹ dx=c·dt） |
| `mass_implies_deviation_from_flow` | 反证 + SM1 + linarith（质量⟹偏离） |
| `deviation_implies_mass` | = SM2（偏离但低于光速⟹质量） |
| `proper_time_eq_metric` | simp + ring |
| `metric_det` | simp（分量直算） |
| `proper_time_dilation` | tanh 定义 + cosh_sq_sub_sinh_sq |
