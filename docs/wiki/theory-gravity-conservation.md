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
| SG6 | g_tt + g_xx·c² = 0（光子） | 零质量条件（dτ=0） |

## 4. 数值推导链（验证）

```text
v(x) = v₀·e^(−x/L) 非均匀流动（= 引力场）
  ⟹ Gordon 度规 g(x) 随位置弯曲
  ⟹ Christoffel Γ^x_tt = (1−v²)·v·v' 非零
  ⟹ 测地线: d²x/dt² ≈ −Γ^x_tt ≈ −v·v' = −d(½v²)/dx
  ⟹ 牛顿极限: a = −∇Φ, Φ = ½v²  ✓ 与弱场 GR 精确一致
```

## 5. 诚实边界

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
