---
title: 从动量守恒推导广义相对论（流动空间假设下的重构）
source: session
created: 2026-08-11
last_confirmed: 2026-08-11
audience: self
stage: draft
schema_version: 2
confidence: medium
entity_type: theorem
tags: [GR, momentum-conservation, gordon-metric, christoffel, geodesic, newtonian-limit]
status: current
---

# 从动量守恒推导广义相对论

> leo（2026-08-11）：能不能根据我的时空假设重新从动量守恒推导一次广义相对论？

## 1. 推导路线

对应代码：
- [`ProjectionPhysics/SpaceGravity.lean`](../../ProjectionPhysics/SpaceGravity.lean)（SG1–SG6，mathlib 骨架）
- [`scripts/verify_gravity_from_conservation.py`](../../scripts/verify_gravity_from_conservation.py)（数值完整链）

```text
① 动量守恒（平直空间）: ∂_μ T^μν = 0
② 空间流动非均匀 v(x) ⟹ 度规弯曲（Gordon 度规）
③ 协变守恒: ∇_μ T^μν = 0（Christoffel 符号）
④ 动量守恒 + 等效原理 ⟹ 测地线方程
⑤ 场方程: G_μν = κT_μν（弱场 ⟹ 牛顿引力）
```

## 2. ★ 关键新结果

**引力势 = 空间流动速度平方的一半：Φ = ½v²**

```text
Gordon 度规 g_tt = 1 − v²/c²        （空间流动假设, SG1）
弱场 GR  g_tt   = 1 − 2Φ/c²         （标准结果）

对照: 1 − v²/c² = 1 − 2Φ/c²  ⟹  Φ = ½v²  精确一致 ✓

牛顿极限: a = −∇(½v²) = −v·∇v（流动的非均匀性 = 引力加速度）
```

## 3. 定理（Lean 已证）

| 定理 | 内容 | 物理意义 |
|---|---|---|
| SG1 | gordonMetric v c = [[1−v²/c², v/c²], [v/c², −1/c²]] | 空间流动⟹度规 |
| SG1b | v=0 ⟹ 闵可夫斯基度规 | 平直空间=无流动 |
| SG2 | det(g) = −1/c² | 流动保体积 |
| SG4 | g⁻¹·g = I | 度规升降良定义 |
| SG6 | g_tt + g_xx·c² = 0（光子） | 零质量条件（dτ=0，v=0 平直） |
| SG8 | gordonProperTimeSq = dt² − (dx−v·dt)²/c² | Gordon 固有时间（v=0 退化 SM） |
| SG9 | dτ²_gordon = g_μνΔx^μΔx^ν | ★ 度规一致性（SM4 的非零流动版） |
| SG10 | 光子相对流动以 c 运动（dx−v·dt=±c·dt）⟹ dτ²=0 | ★ SM1 在非均匀流动 v≠0 下的对应 |
| SG11 | g_tt = 1 − 2Φ/c²，Φ=½v² | ★ 弱场匹配定理化（引力势=½流动速度平方） |

> 2026-08-14 验证补充（SG8–SG11，mathlib）：Gordon 度规 = SpaceMetric.lean 的
> 下一步候选（非均匀流动 v(x)）已 Lean 验证——`gordon_photon_proper_time_zero(_rev)`
> 是 SM1 光子 dτ=0 在非零流动下的对应，建模坑（skill 记录）：光子条件是相对流动
> |dx − v·dt| = c·dt，不是随流动静止 dx = v·dt（那会得 dτ² = dt² ≠ 0 的错误物理）。
> 6 个 example 组合验证（正向/反向光子、弱场 g_tt=91/100、度规一致性、质量偏离 dτ²>0、
> 坑确认）全部通过；`lake build` 4118 jobs 零 sorry 零 warning。

## 4. 数值推导链（验证）

```text
v(x) = v₀·e^(−x/L) 非均匀流动（= 引力场）
  ⟹ Gordon 度规 g(x) 随位置弯曲
  ⟹ Christoffel Γ^x_tt = −(1−v²)·v·v' 非零
  ⟹ 测地线: d²x/dt² ≈ −Γ^x_tt ≈ −v·v' = −d(½v²)/dx
  ⟹ 牛顿极限: a = −∇Φ, Φ = ½v²  ✓ 与弱场 GR 精确一致
```

> 2026-08-14 验证修正：旧版 Christoffel 是手算的，σ=x 项误用 ∂_x g_tx
> （正确是 ∂_t g_xx = 0），Γ^t_tx/Γ^x_tx 两个分量算错（+0.0083/+0.0470，
> 正确 +0.0166/+0.0030）。测地线关键分量 Γ^x_tt 正确，牛顿极限结论不受影响。
> 已改为通用公式 Γ^λ_μν = ½g^λσ(∂_μ g_σν + ∂_ν g_σμ − ∂_σ g_μν) 一次算出全部
> 8 个分量 + 4 项手算自动对照（全 ✓），删除死代码（Gamma() 空循环/sigma_help）。

## 5. 诚实边界

- **2026-08-14 评估（无新物理）**：本模块全部内容是数学恒等式层——Gordon 度规是经典结果（1923），弱场匹配/牛顿极限是教科书标准；"引力=流动非均匀"是概念重构（与标准 GR 数值不可区分）。价值在形式化严谨性（零 sorry 全链）与假设体系自洽性（SLS→SM→SG 闭环），不在新物理。任何后续声称前先过 current-status.md 的 4 层评估表。
- **完整曲率张量/Bianchi/场方程推导**需 mathlib RiemannianGeometry
  （大工程；当前 Lean 是代数骨架 SG1–SG6 + 数值验证弱场极限）
- **1+1 维**（单方向流动）；3+1 维推广是后续
- **牛顿极限已验证**；强场（黑洞/引力波）未验证
- 数值验证推导链，非数学证明
- 光子零质量（SG6）⟹ 光偏折由度规弯曲决定（GR 预言方向正确）

## 6. 与已有模块连接

- SLS6：引力=流动非均匀（种子）⟹ 本模块落地为 Φ=½v²
- SM1–SM6：光子 dτ=0（=SG6 零质量条件）
- RD1–RD7：γ² 差值形式（=SG7 质量动量）
- Gordon 度规 = SpaceMetric.lean 的下一步候选（非均匀流动 v(x)）
