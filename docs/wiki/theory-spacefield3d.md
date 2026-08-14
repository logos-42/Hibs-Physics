---
title: 空间场 3D 向量微积分（三场接缝，探索）
source: session
created: 2026-08-14
last_confirmed: 2026-08-14
audience: self
stage: draft
schema_version: 2
confidence: medium
entity_type: theorem
tags: [space-field, 3d, curl, divergence, spin, charge, maxwell]
status: current
---

# 空间场 3D 向量微积分（三场接缝，探索）

> leo（2026-08-14）下一步候选：
> 1. 3D 推广：B = ∇×C 无散自动成立是 3D 才完整的（1+1 维只是种子）
> 2. 与 MC1 自旋连接：电子 = C 的涡旋（∇×C ≠ 0 = 磁场 B）+ 源
>    （∇·C ≠ 0 = 电场 E）——龙卷风图像获得代数位置
> 3. 电荷机制：MS5 里 J 是输入，e 的数值/量子化无来源（诚实缺口）

## 1. 数学内容（`SpaceField3D.lean` SF1–SF5 全证，零 sorry）

3D 差分离散向量微积分（ℤ⁴：t, x, y, z）：

```text
SF1 ★ div(curl C) = 0 自动成立（3D 离散恒等）
    —— B = curl C ⟹ ∇·B = 0；麦克斯韦第一条方程（无磁单极）不是
    独立定律，是"磁场 = 空间场旋度"的运动学恒等。1+1 维没有 curl，
    这是 3D 才完整的数学内容。
SF2 curl(grad f) = 0 自动（梯度无旋）
    —— 静电场 E = −∇φ 自动无旋（φ = 标量势层，与 curl 层互补）
SF3 ∂_t 与 curl 交换（时间差分与空间差分交换）
SF4 ★ 法拉第定律 3D 自动：∂_t B = −curl E（E = −∂_tC, B = curl C）
SF5 磁场 = 自旋的代数位置：B = curl C ⟹ B ≠ 0 ⟺ curl C ≠ 0
    （curl 三分量 ↔ 空间三方向——三方向假设）
```

## 2. 三个候选的接缝判定

| 候选 | 状态 | 内容 |
|---|---|---|
| 1. 3D 推广 | ✓ 完成 | div(curl C)=0（SF1）、法拉第 3D（SF4）、梯度无旋（SF2）——B 无散是 3D 运动学恒等 |
| 2. 与 MC1 连接 | ✓ 代数位置 | B = curl C = 自旋的磁场（SF5）；∇·C ≠ 0 = 源（电荷散度层）；龙卷风（涡旋+源）= curl/div 代数分解 |
| 3. 电荷机制 | ✗ 诚实缺口 | ∇·C ≠ 0 只给电荷代数位置；e 数值（1.602e-19 C）与量子化无来源——与"第二输入未找到"同源 |

## 3. 数值验证（`scripts/verify_spacefield3d.py`）

| 检验 | 结果 |
|---|---|
| div(curl C)（3 随机种子） | 1.8e-15 / 9.4e-16 / 1.8e-15（机器精度 0）✓ |
| curl(grad f)（随机标量场） | 8.9e-16 ✓ |
| 涡旋场 div(B = curl C) | 0.0（精确）✓ |
| max\|B\| = max\|curl C\| | 0.2512（B = curl C 一致）✓ |

图：`artifacts/spacefield3d/vortex_curl.png`——空间场环形涡旋（自旋）
与其磁场 B = curl C（无散）。

## 4. 诚实 4 层判定

| 层 | 判定 | 理由 |
|---|---|---|
| ① 数学恒等式 | 真（3D 才完整） | div∘curl = 0、curl∘grad = 0 是标准向量分析恒等；仓库价值 = 在"空间场 = 一切"框架里给它们物理位置 |
| ② 结构对应 | 已知物理 | 矢量势表述的 3D 完整化（B = ∇×A 无散是标准内容） |
| ③ 数值匹配 | — | 恒等层无新数值 |
| ④ 概念重构 | 不可证伪 | C = A 物理化（|C| = c）；自旋 = 涡旋在解释层 |

价值：候选 1（3D 推广）完成——"麦克斯韦 = 空间场运动学"在 3D 的
完整恒等骨架（B 无散 + 法拉第 + 梯度无旋）；候选 2 获得代数位置
（龙卷风 = curl + div 分解）；候选 3 诚实标注为最深的开放问题。

## 5. 文件与产物

- Lean: `ProjectionPhysics/Explorations/SpaceField3D.lean`（SF1–SF5）
- 模拟: `scripts/verify_spacefield3d.py`
- 图: `artifacts/spacefield3d/vortex_curl.png`
