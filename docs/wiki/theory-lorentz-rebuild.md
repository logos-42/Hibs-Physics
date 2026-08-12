---
title: 洛伦兹重构：新假设下的洛伦兹变换（mathlib 推导）
source: session
created: 2026-08-11
last_confirmed: 2026-08-11
audience: self
stage: draft
schema_version: 2
confidence: medium
entity_type: theorem
tags: [lorentz, rapidity, boost, mathlib, relativity, space-flow]
status: current
---

# 洛伦兹重构：新假设下的洛伦兹变换（mathlib 推导）

> leo（2026-08-11）：在"空间流动/矢量光速"假设下，证明推导新的
> 洛伦兹变换，利用 mathlib。

## 1. 新假设 → 洛伦兹变换的推导路径

```text
新假设 (SLS1, SLS6):
  光速 c = 空间本身的等效速度，空间以 c 流动
  惯性系 = 随空间流动的参考系
  观测者偏离空间流动的速度 v = 快度参数化 θ，tanh θ = v/c

推导 (LorentzRebuild.lean, mathlib):
  LR1  boost(θ) = [[cosh θ, -sinh θ], [-sinh θ, cosh θ]]
       保持闵可夫斯基度规 η = diag(-1, 1)  ⟹ 洛伦兹变换
  LR2  γ² − γ²β² = 1（γ = cosh θ, β = tanh θ ⟹ γ = 1/√(1−β²)）
  LR3  boost(θ₁)·boost(θ₂) = boost(θ₁+θ₂)（快度加法，洛伦兹群）
  LR3b tanh(θ₁+θ₂) = (tanh θ₁ + tanh θ₂)/(1 + tanh θ₁·tanh θ₂)
       （相对论速度加法定理）
  LR4  |tanh θ| < 1（有限快度永不达光速，β < 1）
  LR5  t' = γ(t − βx), x' = γ(x − βt)（标准洛伦兹坐标变换）
```

## 2. 证明（mathlib 版）

对应代码：[`ProjectionPhysics/LorentzRebuild.lean`](../../ProjectionPhysics/LorentzRebuild.lean)

使用 mathlib 的 ℝ、2×2 矩阵、双曲函数：

| 定理 | 内容 | mathlib API |
|---|---|---|
| `boost_is_lorentz` | ΛᵀηΛ = η（度规保持） | `Real.cosh_sq_sub_sinh_sq` + ring |
| `gamma_sq_minus_beta_sq` | γ²(1−β²) = 1 | `Real.tanh_eq_sinh_div_cosh` + field_simp |
| `boost_mul_boost` | 快度加法 | `Real.sinh_add`/`Real.cosh_add` |
| `rapidity_add_velocity_add` | 速度加法定理 | sinh/cosh 展开 + field_simp |
| `finite_rapidity_never_reaches_light` | β < 1 | `Real.tanh_lt_one` |
| `boost_time_component` | t' = γ(t−βx) | 显式分量 |
| `boost_space_component` | x' = γ(x−βt) | 显式分量 |

## 3. 与 SLS6 的衔接

SLS6（core Lean）证明了概念层：惯性系 = 随空间流动、光速不变 =
空间流动普适、洛伦兹不变性 = 空间流动均匀。

LorentzRebuild（mathlib）证明了计算层：具体 boost 矩阵、度规保持、
快度加法、速度加法、光速边界。

两层衔接：**新假设下的洛伦兹变换形式与标准洛伦兹变换完全相同**
（boost 矩阵、γ 因子、速度加法），但解释层改变——β 是"偏离空间
流动的程度"，γ 是随空间系与偏离空间系的坐标变换因子。

## 4. mathlib 化的收益（对照 core Lean）

| 方面 | core Lean（Clifford.lean） | mathlib（PauliMathlib.lean） |
|---|---|---|
| 复数 | 手写 ℂ（Int 分量） | mathlib 内建 ℂ |
| 矩阵 | 手写 Mat2 + 分量展开 | `Matrix (Fin 2) (Fin 2) ℂ` |
| 证明 | 展开 re/im 到 Int + omega | `ext` + `fin_cases` + `ring` |
| 双曲函数 | 无 | `Real.cosh_sq_sub_sinh_sq` 等现成 |

mathlib 将"逐分量展开再 omega"的繁琐证明简化为 `ring`/`field_simp`。

## 5. 诚实边界

- 1+1 维（时间 + 一维空间）已完整推导；3+1 维需 4×4 矩阵，
  mathlib 支持（`Matrix (Fin 4) (Fin 4) ℝ`），留作后续
- 度规符号约定 (−,+)；换 (+,−,−,−) 需重做符号
- 推导从"空间流动假设"出发的形式与标准洛伦兹变换一致——
  这不是新公式，而是同一公式的新解释（与 SLS6 结论一致）
- 未证明洛伦兹变换的唯一性（群论分类），只证明 boost 形式成立
